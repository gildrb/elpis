#!/usr/bin/env python3
"""Regression tests for the PQ2_0 GGUF reading / dequant / transform package.

Plain-python runner (no pytest): every test runs in order, results are
written to tests/report.json, and the process exits nonzero on any failure.

Run inside the pinned container:
  docker run --rm -v <pkg>:/work -w /work --entrypoint python3 \
    -v /mnt/ssd/storage/ai/qwen3.8-27b/models:/models:ro \
    lmsysorg/sglang@sha256:d6e7288627be8b02be88e4bba38e73f6d50e2826869f753c13a4c4385ab3eda9 \
    tests/test_pq2.py
"""

from __future__ import annotations

import json
import os
import struct
import sys
import tempfile
import time
import traceback
from datetime import datetime, timezone
from pathlib import Path
from typing import Callable, Dict, List, Tuple

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import numpy as np

import artifact
import hadamard
import pq2
from gguf_reader import (
    GGMLType,
    GgufBoundsError,
    GgufError,
    GgufFormatError,
    GgufMetadataType,
    GgufReader,
    GgufUnsupportedError,
    bf16_bytes_to_f32,
    ggml_geometry,
)

_ARTIFACT_CANDIDATES = (
    os.environ.get("PQ2_ARTIFACT_PATH", ""),
    "/models/Ternary-Bonsai-2-27B-PQ2_0.gguf",
    "/mnt/ssd/storage/ai/qwen3.8-27b/models/Ternary-Bonsai-2-27B-PQ2_0.gguf",
)

_U32 = struct.Struct("<I")
_U64 = struct.Struct("<Q")


class SkipTest(Exception):
    """Raised when an environment-dependent test cannot run."""


def _artifact_path() -> str:
    for candidate in (
        os.environ.get("PQ2_ARTIFACT_PATH", ""),
        "/models/Ternary-Bonsai-2-27B-PQ2_0.gguf",
        "/mnt/ssd/storage/ai/qwen3.8-27b/models/Ternary-Bonsai-2-27B-PQ2_0.gguf",
    ):
        if candidate and os.path.exists(candidate):
            return candidate
    raise SkipTest("Bonsai PQ2_0 GGUF artifact not available in this environment")


def _u32(value: int) -> bytes:
    return _U32.pack(value)


def _u64(value: int) -> bytes:
    return _U64.pack(value)


def _enc_str(value: str) -> bytes:
    raw = value.encode("utf-8")
    return _u64(len(raw)) + raw


def _header(n_tensors: int, n_kv: int, version: int = 3, magic: bytes = b"GGUF") -> bytes:
    return magic + _u32(version) + _u64(n_tensors) + _u64(n_kv)


def _tensor_info(name: str, dims: Tuple[int, ...], type_id: int, offset: int) -> bytes:
    return (
        _enc_str(name)
        + _u32(len(dims))
        + b"".join(_u64(d) for d in dims)
        + _u32(type_id)
        + _u64(offset)
    )


_SCALAR_FMT = {
    GgufMetadataType.UINT8.value: "<B",
    GgufMetadataType.INT8.value: "<b",
    GgufMetadataType.UINT16.value: "<H",
    GgufMetadataType.INT16.value: "<h",
    GgufMetadataType.UINT32.value: "<I",
    GgufMetadataType.INT32.value: "<i",
    GgufMetadataType.FLOAT32.value: "<f",
    GgufMetadataType.UINT64.value: "<Q",
    GgufMetadataType.INT64.value: "<q",
    GgufMetadataType.FLOAT64.value: "<d",
}


def _encode_scalar(value_type: int, value: object) -> bytes:
    if value_type == GgufMetadataType.STRING.value:
        return _enc_str(str(value))
    if value_type == GgufMetadataType.BOOL.value:
        if not isinstance(value, bool):
            raise TypeError(f"bool kv needs a bool, got {value!r}")
        return bytes([1 if value else 0])
    fmt = _SCALAR_FMT.get(value_type)
    if fmt is None:
        raise TypeError(f"not a scalar metadata type: {value_type}")
    return struct.pack(fmt, value)


def _infer_elem_type(items: List[object]) -> int:
    if not items:
        raise TypeError("cannot infer element type of an empty array")
    first = items[0]
    if isinstance(first, str):
        return GgufMetadataType.STRING.value
    if isinstance(first, bool):
        return GgufMetadataType.BOOL.value
    if isinstance(first, int):
        return GgufMetadataType.INT32.value
    if isinstance(first, float):
        return GgufMetadataType.FLOAT32.value
    if isinstance(first, list):
        return GgufMetadataType.ARRAY.value
    raise TypeError(f"unsupported array element {first!r}")


def _encode_value(value_type: int, value: object) -> bytes:
    if value_type == GgufMetadataType.ARRAY.value:
        if isinstance(value, tuple) and len(value) == 2 and isinstance(value[0], list):
            items, elem_type = value
        else:
            items = list(value)
            elem_type = _infer_elem_type(items)
        out = _u32(elem_type) + _u64(len(items))
        for item in items:
            out += _encode_value(elem_type, item)
        return out
    return _encode_scalar(value_type, value)


def _kv(key: str, value_type: int, value: object) -> bytes:
    return _enc_str(key) + _u32(value_type) + _encode_value(value_type, value)


def build_gguf(
    path: str,
    kvs: List[bytes],
    tensors: List[Tuple[str, Tuple[int, ...], int, bytes]],
    alignment: int = 32,
) -> int:
    """Write a well-formed GGUF v3 file; return the data section offset."""
    header = _header(len(tensors), len(kvs))
    body = b"".join(kvs)

    rel_offsets: List[int] = []
    payload_total = 0
    for _name, _dims, _type_id, payload in tensors:
        rel = ((payload_total + alignment - 1) // alignment) * alignment
        rel_offsets.append(rel)
        payload_total = rel + len(payload)

    infos = b"".join(
        _tensor_info(name, dims, type_id, rel)
        for (name, dims, type_id, _payload), rel in zip(tensors, rel_offsets)
    )
    end_of_meta = len(header) + len(body) + len(infos)
    data_offset = ((end_of_meta + alignment - 1) // alignment) * alignment

    with open(path, "wb") as f:
        f.write(header)
        f.write(body)
        f.write(infos)
        f.write(b"\x00" * (data_offset - end_of_meta))
        for (_name, _dims, _type_id, payload), rel in zip(tensors, rel_offsets):
            f.seek(data_offset + rel)
            f.write(payload)
    return data_offset


def encode_tensor_rows(rows: "np.ndarray[tuple[int, int], np.dtype[np.float32]]") -> "np.ndarray[tuple[int, int], np.dtype[np.uint8]]":
    """Encode (ne1, ne0) float32 rows into the (ne1, row_bytes) GGUF layout."""
    packed_rows = [pq2.encode_pq2_row_ref(row) for row in rows]
    row_bytes = (rows.shape[1] // pq2.QK_PQ2_0) * pq2.BLOCK_BYTES
    return np.concatenate(packed_rows, axis=0).reshape(rows.shape[0], row_bytes)


def _read_file_bytes(path: str) -> bytes:
    with open(path, "rb") as f:
        return f.read()


def _write_file_bytes(path: str, data: bytes) -> None:
    with open(path, "wb") as f:
        f.write(data)


# ---------------------------------------------------------------------------
# (a) synthetic GGUF: alignment padding, relative offsets, F32/BF16 values

def _synthetic_file(path: str, alignment: int = 32) -> int:
    pq2_rows = np.array(
        [[3.0, -1.0] + [0.0] * 254, [0.5, 2.0] + [0.25] * 254], dtype=np.float32
    )
    assert pq2_rows.shape == (2, 256)
    pq2_payload = encode_tensor_rows(pq2_rows).tobytes()
    f32_payload = np.array(
        [1.0, -2.5, 3.25, 0.0, 1e-8, -7.0], dtype=np.float32
    ).tobytes()
    bf16_payload = struct.pack("<3H", 0x3F80, 0x4000, 0xBF80)
    f16_payload = np.array([1.0, -2.0], dtype=np.float16).astype("<f2").tobytes()
    kvs = [
        _kv("general.alignment", GgufMetadataType.UINT32.value, alignment),
        _kv("test.str", GgufMetadataType.STRING.value, "h\xc3\xa9llo"),
        _kv("test.f64", GgufMetadataType.FLOAT64.value, 2.5),
        _kv("test.flag", GgufMetadataType.BOOL.value, True),
        _kv("test.i64", GgufMetadataType.INT64.value, -7),
        _kv("test.u64", GgufMetadataType.UINT64.value, 2**63),
        _kv("test.arr_str", GgufMetadataType.ARRAY.value, ["a", "bb", "ccc"]),
        _kv("test.arr_i", GgufMetadataType.ARRAY.value, [1, -2, 3]),
        _kv("test.nested", GgufMetadataType.ARRAY.value, [[1, 2], [3, 4, 5]]),
        _kv("test.empty", GgufMetadataType.ARRAY.value, ([], GgufMetadataType.STRING.value)),
    ]
    tensors = [
        ("t.f32", (6,), GGMLType.F32.value, f32_payload),
        ("t.bf16", (3,), GGMLType.BF16.value, bf16_payload),
        ("t.f16", (2,), GGMLType.F16.value, f16_payload),
        ("t.pq2", (256, 2), GGMLType.PQ2_0.value, pq2_payload),
    ]
    return build_gguf(path, kvs, tensors, alignment=alignment)


def test_synthetic_gguf_roundtrip() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        path = os.path.join(tmp, "synthetic.gguf")
        data_offset = _synthetic_file(path)
        with GgufReader(path) as r:
            assert r.version == 3
            assert r.alignment == 32
            assert r.data_offset == data_offset
            assert r.data_offset % 32 == 0
            assert r.metadata["test.str"] == "h\xc3\xa9llo"
            assert r.metadata["test.f64"] == 2.5
            assert r.metadata["test.flag"] is True
            assert r.metadata["test.i64"] == -7
            assert r.metadata["test.u64"] == 2**63
            assert r.metadata["test.arr_str"] == ["a", "bb", "ccc"]
            assert r.metadata["test.arr_i"] == [1, -2, 3]
            assert r.metadata["test.nested"] == [[1, 2], [3, 4, 5]]
            assert r.metadata["test.empty"] == []
            assert r.kv_types["test.flag"] == GgufMetadataType.BOOL
            assert r.kv_types["test.arr_str"] == GgufMetadataType.ARRAY
            assert r.kv_types["test.i64"] == GgufMetadataType.INT64

            assert r.tensor_order == ["t.f32", "t.bf16", "t.f16", "t.pq2"]
            f32_info = r.tensors["t.f32"]
            bf16_info = r.tensors["t.bf16"]
            f16_info = r.tensors["t.f16"]
            pq2_info = r.tensors["t.pq2"]
            # 24-byte F32 tensor is followed by an aligned next tensor: the
            # gap is the alignment padding exercised here
            assert f32_info.nbytes == 24
            assert bf16_info.offset == 32
            assert bf16_info.absolute_offset == data_offset + 32
            assert pq2_info.dims == (256, 2)
            assert pq2_info.type == GGMLType.PQ2_0
            assert pq2_info.nbytes == 2 * 2 * pq2.BLOCK_BYTES
            # relative offsets are relative to the data section base
            for info in r.tensors.values():
                assert info.absolute_offset == r.data_offset + info.offset

            f32_vals = np.frombuffer(r.read_tensor_bytes("t.f32"), dtype="<f4")
            assert np.array_equal(f32_vals, np.array([1.0, -2.5, 3.25, 0.0, 1e-8, -7.0], dtype=np.float32))

            # BF16 must be bit-reinterpreted, never int-cast
            bf16_raw = np.frombuffer(r.read_tensor_bytes("t.bf16"), dtype=np.uint8)
            assert np.array_equal(
                bf16_bytes_to_f32(bf16_raw),
                np.array([1.0, 2.0, -1.0], dtype=np.float32),
            )
            # historical defect: int-casting the raw bytes yields these values
            int_cast = np.frombuffer(r.read_tensor_bytes("t.bf16"), dtype="<i2")
            assert int_cast.tolist() == [16256, 16384, -16512]

            f16_vals = np.frombuffer(r.read_tensor_bytes("t.f16"), dtype="<f2")
            assert np.array_equal(f16_vals, np.array([1.0, -2.0], dtype=np.float16))

            pq2_raw = r.read_tensor_bytes("t.pq2")
            assert len(pq2_raw) == 2 * 2 * pq2.BLOCK_BYTES
            packed = np.frombuffer(pq2_raw, dtype=np.uint8).reshape(2, 2 * pq2.BLOCK_BYTES)
            decoded = pq2.decode_pq2_tensor(packed, (256, 2), np.float32)
            source = np.array(
                [[3.0, -1.0] + [0.0] * 254, [0.5, 2.0] + [0.25] * 254], dtype=np.float32
            )
            expected, _ = _c_reference_roundtrip(source)
            assert decoded.shape == (2, 256)
            assert np.array_equal(decoded, expected), "decode != C reference"
            # the amax element (3.0) survives quantization exactly
            assert decoded[0, 0] == 3.0

        try:
            with GgufReader(path) as r:
                r.read_tensor_bytes("nope.weight")
            raise AssertionError("expected GgufFormatError for unknown tensor name")
        except GgufFormatError:
            pass


# ---------------------------------------------------------------------------
# (a) malformed / truncated GGUF rejections

def _minimal_wellformed_bytes() -> bytes:
    """Header + one kv + one 128-element PQ2 tensor info + payload."""
    payload = pq2.encode_pq2_row_ref(np.full(128, 0.5, dtype=np.float32)).tobytes()
    head = _header(1, 1)
    kv = _kv("general.alignment", GgufMetadataType.UINT32.value, 32)
    info = _tensor_info("w.weight", (128,), GGMLType.PQ2_0.value, 0)
    meta_end = len(head) + len(kv) + len(info)
    data_offset = ((meta_end + 31) // 32) * 32
    return head + kv + info + b"\x00" * (data_offset - meta_end) + payload


def _expect_gguf_error(data: bytes, exc_type: type, label: str) -> None:
    with tempfile.TemporaryDirectory() as tmp:
        path = os.path.join(tmp, "bad.gguf")
        _write_file_bytes(path, data)
        try:
            GgufReader(path)
        except exc_type:
            return
        except GgufError as exc:
            raise AssertionError(
                f"{label}: raised {type(exc).__name__}, expected {exc_type.__name__}: {exc}"
            )
        raise AssertionError(f"{label}: no error raised, expected {exc_type.__name__}")


def test_gguf_malformed_rejections() -> None:
    good = _minimal_wellformed_bytes()

    # truncated header
    _expect_gguf_error(good[:10], GgufBoundsError, "truncated header")
    # bad magic
    _expect_gguf_error(b"XGUF" + good[4:], GgufFormatError, "bad magic")
    # unsupported version
    _expect_gguf_error(good[:4] + _u32(2) + good[8:], GgufFormatError, "version 2")
    # kv key length beyond EOF
    bad_kv_len = good[:24] + _u64(1 << 40) + good[32:]
    _expect_gguf_error(bad_kv_len, GgufBoundsError, "kv key length beyond EOF")
    # unknown metadata value type
    i = good.find(_u32(GgufMetadataType.UINT32.value))
    _expect_gguf_error(good[:i] + _u32(200) + good[i + 4:], GgufUnsupportedError, "unknown kv type")
    # unknown tensor type id
    j = good.find(_u32(GGMLType.PQ2_0.value), good.find(b"w.weight"))
    _expect_gguf_error(good[:j] + _u32(999) + good[j + 4:], GgufFormatError, "unknown tensor type")
    # zero dimension
    j = good.find(b"w.weight")
    dim_pos = j + len(b"w.weight") + 4  # past name bytes, past n_dims u32
    _expect_gguf_error(good[:dim_pos] + _u64(0) + good[dim_pos + 8:], GgufFormatError, "zero dim")
    # n_dims = 5
    ndim_pos = good.find(b"w.weight") + len(b"w.weight")
    _expect_gguf_error(good[:ndim_pos] + _u32(5) + good[ndim_pos + 4:] + _u64(128) * 2, GgufFormatError, "n_dims 5")
    # empty tensor name: replace name with zero-length string
    head0 = _header(1, 0)
    info0 = _u64(0) + _u32(1) + _u64(128) + _u32(GGMLType.PQ2_0.value) + _u64(0)
    _expect_gguf_error(head0 + info0, GgufFormatError, "empty tensor name")
    # invalid utf-8 key
    kv_bad = _u64(2) + b"\xff\xfe" + _u32(GgufMetadataType.UINT32.value) + _u32(32)
    _expect_gguf_error(_header(1, 1) + kv_bad, GgufFormatError, "invalid utf-8 key")
    # duplicate metadata key
    one_kv = _kv("dup.key", GgufMetadataType.UINT32.value, 32)
    _expect_gguf_error(_header(0, 2) + one_kv + one_kv, GgufFormatError, "duplicate kv")
    # duplicate tensor name
    info_dup = _tensor_info("same.weight", (128,), GGMLType.PQ2_0.value, 0)
    meta_end = len(_header(2, 0)) + 2 * len(info_dup)
    data_off = ((meta_end + 31) // 32) * 32
    payload = b"\x00" * (data_off - meta_end) + pq2.encode_pq2_row_ref(np.zeros(128, dtype=np.float32)).tobytes() * 2
    _expect_gguf_error(_header(2, 0) + info_dup + info_dup + payload, GgufFormatError, "duplicate tensor name")
    # unaligned tensor offset
    info_unaligned = _tensor_info("w.weight", (128,), GGMLType.PQ2_0.value, 3)
    meta_end = len(_header(1, 0)) + len(info_unaligned)
    data_off = ((meta_end + 31) // 32) * 32
    blob = _header(1, 0) + info_unaligned + b"\x00" * (data_off - meta_end) + b"\x00" * 64
    _expect_gguf_error(blob, GgufFormatError, "unaligned tensor offset")
    # tensor data beyond EOF
    info_far = _tensor_info("w.weight", (128,), GGMLType.PQ2_0.value, 1 << 20)
    _expect_gguf_error(_header(1, 0) + info_far, GgufBoundsError, "tensor beyond EOF")
    # alignment not a power of two
    kv_align_bad = _kv("general.alignment", GgufMetadataType.UINT32.value, 24)
    _expect_gguf_error(_header(0, 1) + kv_align_bad, GgufFormatError, "alignment 24")
    # alignment wrong value type (string)
    kv_align_str = _enc_str("general.alignment") + _u32(GgufMetadataType.STRING.value) + _enc_str("32")
    _expect_gguf_error(_header(0, 1) + kv_align_str, GgufFormatError, "alignment as string")
    # unknown array element type
    arr_bad = _enc_str("a") + _u32(GgufMetadataType.ARRAY.value) + _u32(200) + _u64(1)
    _expect_gguf_error(_header(0, 1) + arr_bad, GgufUnsupportedError, "array elem type 200")
    # bool byte out of domain
    bool_bad = _enc_str("b") + _u32(GgufMetadataType.BOOL.value) + bytes([2])
    _expect_gguf_error(_header(0, 1) + bool_bad, GgufFormatError, "bool byte 2")
    # trailing truncation mid payload
    _expect_gguf_error(good[:-10], GgufBoundsError, "truncated payload")

    # well-formed control parses and exposes the tensor
    with tempfile.TemporaryDirectory() as tmp:
        path = os.path.join(tmp, "ok.gguf")
        _write_file_bytes(path, good)
        with GgufReader(path) as r:
            info = r.tensors["w.weight"]
            assert info.type == GGMLType.PQ2_0
            assert info.nbytes == pq2.BLOCK_BYTES
            assert len(r.read_tensor_bytes("w.weight")) == pq2.BLOCK_BYTES


# ---------------------------------------------------------------------------
# (b) PQ2 round-trip on random and structured fixtures

def _c_reference_roundtrip(rows: "np.ndarray[tuple[int, int], np.dtype[np.float32]]"):
    """Expected decode per the C reference, quantizing per 128-block:
    q = roundf(w * (1/amax_block)) + 1, scale stored as fp16."""
    ne0 = rows.shape[1]
    blocks = rows.reshape(-1, pq2.QK_PQ2_0)
    amax = np.abs(blocks).max(axis=1, keepdims=True)
    d16 = amax.astype(np.float16).astype(np.float32)  # stored scale
    inv = np.where(amax > 0, np.float32(1.0) / np.where(amax > 0, amax, 1.0), np.float32(0.0))
    t = blocks * inv
    q = np.where(t >= 0, np.floor(t + np.float32(0.5)), np.ceil(t - np.float32(0.5)))
    q = np.clip(q.astype(np.int64) + 1, 0, 3)
    decoded = ((q - 1) * d16).reshape(rows.shape)
    d_per_element = np.repeat(d16, pq2.QK_PQ2_0, axis=0).reshape(rows.shape)
    return decoded, d_per_element


def _assert_roundtrip(rows: "np.ndarray[tuple[int, int], np.dtype[np.float32]]", label: str) -> None:
    packed = encode_tensor_rows(rows)
    ne0, ne1 = rows.shape[1], rows.shape[0]
    decoded = pq2.decode_pq2_tensor(packed, (ne0, ne1), np.float32)
    expected, d16 = _c_reference_roundtrip(rows)
    assert decoded.shape == (ne1, ne0), f"{label}: shape {decoded.shape}"
    assert np.array_equal(decoded, expected), f"{label}: decode != C reference"
    bound = float((0.5 * d16 * (1 + 2**-11) + d16 * 2**-12).max())
    assert np.abs(decoded - rows).max() <= bound, f"{label}: error bound"
    # the reference quantizer only emits codes 0..2 -> values in {-d, 0, +d}
    dmat = d16
    assert np.all(
        (decoded == 0)
        | (np.abs(decoded - dmat) <= dmat * 1e-6)
        | (np.abs(decoded + dmat) <= dmat * 1e-6)
    ), f"{label}: decoded value outside {{-d, 0, +d}}"


def test_pq2_roundtrip_fixtures() -> None:
    rng = np.random.default_rng(20260214)
    _assert_roundtrip((rng.standard_normal((5, 128)) * 0.02).astype(np.float32), "normal 5x128")
    _assert_roundtrip((rng.standard_normal((3, 384)) * 0.02).astype(np.float32), "normal 3x384")
    _assert_roundtrip((rng.standard_normal((9, 128))).astype(np.float32), "multirow 9x128")
    _assert_roundtrip((rng.standard_normal((4, 256))).astype(np.float32), "nonsquare 4x256")
    _assert_roundtrip(np.zeros((2, 128), dtype=np.float32), "zeros")
    halves = np.tile(np.array([0.5, -0.5, 1.5, -1.5, 0.25, 1.0, -1.0, 0.0], dtype=np.float32), 16)
    _assert_roundtrip(halves.reshape(1, 128), "exact halves")
    mixed = np.array([[1e-3, 10.0, -10.0, 0.5, -0.5, 3.0, -3.0, 0.0]], dtype=np.float32)
    mixed = np.tile(mixed, (2, 16))
    _assert_roundtrip(mixed, "mixed magnitudes")
    large = (rng.standard_normal((1, 128)) * 1000).astype(np.float32)
    _assert_roundtrip(large, "large fp16-safe")

    # constants vs the pinned reference geometry
    assert (pq2.QK_PQ2_0, pq2.BLOCK_BYTES) == (128, 34)

    # misaligned / wrong-shape rejections
    packed_ok = encode_tensor_rows(np.ones((2, 128), dtype=np.float32))
    for bad_call, why in (
        (lambda: pq2.decode_pq2_tensor(packed_ok.reshape(-1), (128, 2), np.float32), "flat packed"),
        (lambda: pq2.decode_pq2_tensor(packed_ok, (2, 128), np.float32), "ne0 not multiple of 128"),
        (lambda: pq2.decode_pq2_tensor(packed_ok, (128, 3), np.float32), "wrong row count"),
        (lambda: pq2.decode_pq2_tensor(packed_ok.astype(np.int32), (128, 2), np.float32), "non-uint8 packed"),
        (lambda: pq2.decode_pq2_tensor(packed_ok, (128, 2), np.int32), "int out_dtype"),
        (lambda: pq2.decode_pq2_tensor(packed_ok, (128,), np.float32), "1-D logical shape"),
        (lambda: pq2.decode_pq2_tensor(packed_ok, (128, 0), np.float32), "zero rows"),
        (lambda: pq2.decode_pq2_tensor(packed_ok, (128, 2.0), np.float32), "non-int dim"),
    ):
        try:
            bad_call()
            raise AssertionError(f"expected Pq2ShapeError for {why}")
        except pq2.Pq2ShapeError:
            pass

    # encoder rejections
    for bad_call, why in (
        (lambda: pq2.encode_pq2_row_ref(np.ones(128, dtype=np.float64)), "float64 input"),
        (lambda: pq2.encode_pq2_row_ref(np.ones((1, 128), dtype=np.float32)), "2-D input"),
        (lambda: pq2.encode_pq2_row_ref(np.ones(100, dtype=np.float32)), "length 100"),
        (lambda: pq2.encode_pq2_row_ref(np.zeros(0, dtype=np.float32)), "empty"),
        (lambda: pq2.encode_pq2_row_ref(np.array([np.inf, 0.0], dtype=np.float32)), "non-finite"),
        (lambda: pq2.encode_pq2_row_ref(np.full(128, 1e5, dtype=np.float32)), "fp16 overflow scale"),
    ):
        try:
            bad_call()
            raise AssertionError(f"expected error for {why}")
        except (pq2.Pq2ShapeError, pq2.Pq2Error):
            pass


# ---------------------------------------------------------------------------
# (c) Example A: the butterfly alias trap

def test_example_a_butterfly_alias_trap() -> None:
    # H2 (unnormalized butterfly) applied to [1, 2] must give [3, -1].
    # The historical trap: a sequential IN-PLACE butterfly overwrites x0
    # before computing x1, producing [3, x0-x1] -> [3, 1]. A functional
    # (out-of-place) apply cannot alias, so overwriting cannot occur.
    x = np.array([1.0, 2.0])
    h2_unnorm = np.array([[1.0, 1.0], [1.0, -1.0]])
    out_unnorm = h2_unnorm @ x
    assert out_unnorm.tolist() == [3.0, -1.0], out_unnorm
    # the buggy in-place result, for documentation of the trap only
    alias = x.copy()
    alias[0] = alias[0] + alias[1]
    alias[1] = alias[0] - alias[1]
    assert alias.tolist() == [3.0, 1.0], "expected the historical aliased result here"

    # normalized H2 from the package gives [3/sqrt(2), -1/sqrt(2)]
    h2 = hadamard.hadamard_matrix(2)
    out = h2 @ x
    assert np.allclose(out, np.array([3.0 / np.sqrt(2.0), -1.0 / np.sqrt(2.0)]), atol=1e-15)
    assert np.allclose(h2, h2_unnorm / np.sqrt(2.0), atol=1e-15)

    # functional apply does not mutate its input
    before = x.copy()
    signs2 = np.array([1.0, 1.0])
    hadamard.forward_apply(x, 2, signs2)
    assert np.array_equal(x, before), "forward_apply must not mutate its input"


# ---------------------------------------------------------------------------
# (c) Example B: the signed transform T = H @ D is not involutive

def test_example_b_signed_transform() -> None:
    path = _artifact_path()
    with GgufReader(path) as r:
        meta = hadamard.parse_hadamard_metadata(r.metadata)
        assert meta.sign_mode == "explicit"
        signs = meta.signs_for_width(5120).copy()
        assert meta.block_size == 1024

    block = 1024
    h = hadamard.hadamard_matrix(block)
    d0 = signs[:block]
    big_d = np.sign(signs).astype(np.float64)
    t = h * d0.reshape(1, -1)  # T = H @ diag(D)

    rng = np.random.default_rng(42)
    x = rng.standard_normal(block)
    # T @ T @ x != x: the sign vector makes one application non-involutive
    assert np.abs(t @ t @ x - x).max() > 0.1
    # T.T @ T @ x == x: (H D)^T (H D) = D H^T H D = D D = I
    assert np.allclose(t.T @ t @ x, x, atol=1e-9)

    # forward/inverse round trip on a random 5120-vector with the real signs
    x5120 = rng.standard_normal(5120)
    fwd = hadamard.forward_apply(x5120, block, signs)
    back = hadamard.inverse_apply(fwd, block, signs)
    assert np.allclose(back, x5120, atol=1e-9), np.abs(back - x5120).max()

    # forward must equal per-block H @ (D_block . x_block) with each block's
    # own sign slice (regression: a single first-block sign slice everywhere)
    for b in range(5120 // block):
        block_x = x5120[b * block:(b + 1) * block]
        want = h @ (signs[b * block:(b + 1) * block] * block_x)
        assert np.allclose(fwd[b * block:(b + 1) * block], want, atol=1e-9), f"block {b}"
        back_want = signs[b * block:(b + 1) * block] * (h @ fwd[b * block:(b + 1) * block])
        assert np.allclose(back[b * block:(b + 1) * block], back_want, atol=1e-9), f"inv block {b}"

    # inverse is H first, then signs (llama-graph.cpp: h = s * (H z))
    z = rng.standard_normal(5120)
    manual = np.concatenate([
        signs[b * block:(b + 1) * block] * (h @ z[b * block:(b + 1) * block])
        for b in range(5120 // block)
    ])
    assert np.allclose(hadamard.inverse_apply(z, block, signs), manual, atol=1e-9)

    # big_d referenced to keep the full sign vector explicit for the transforms
    assert big_d.shape == (5120,)


# ---------------------------------------------------------------------------
# (c) Example F: 2-D shape preservation, ones-matrix times ones-vector

def test_example_f_shape_preservation() -> None:
    # A ones matrix with stored dims [in, out] = [128, 2] (two 128-wide rows)
    # decodes to the matmul-ready (2, 128) array -- never a flat (256,) vector.
    packed = encode_tensor_rows(np.ones((2, 128), dtype=np.float32))
    decoded = pq2.decode_pq2_tensor(packed, (128, 2), np.float32)
    assert decoded.shape == (2, 128)
    assert decoded.min() == 1.0 and decoded.max() == 1.0
    y = decoded @ np.ones(128, dtype=np.float32)
    assert np.array_equal(y, np.array([128.0, 128.0], dtype=np.float32)), y

    # scaled variant: every weight 0.5 -> row sums 64
    packed_half = encode_tensor_rows(np.full((2, 128), 0.5, dtype=np.float32))
    decoded_half = pq2.decode_pq2_tensor(packed_half, (128, 2), np.float32)
    y_half = decoded_half @ np.ones(128, dtype=np.float32)
    assert np.array_equal(y_half, np.array([64.0, 64.0], dtype=np.float32)), y_half

    # shape preservation for a wider nonsquare tensor
    packed3 = encode_tensor_rows(np.full((3, 256), 2.0, dtype=np.float32))
    decoded3 = pq2.decode_pq2_tensor(packed3, (256, 3), np.float32)
    assert decoded3.shape == (3, 256)
    y3 = decoded3 @ np.ones(256, dtype=np.float32)
    assert np.array_equal(y3, np.array([512.0, 512.0, 512.0], dtype=np.float32))


# ---------------------------------------------------------------------------
# Hadamard: parity/doubling agreement, orthogonality, metadata parser

def test_hadamard_agreement_and_properties() -> None:
    for n in (2, 4, 8, 16, 64, 256, 1024):
        parity = hadamard.hadamard_matrix_parity(n)
        doubling = hadamard.hadamard_matrix_doubling(n)
        assert np.array_equal(parity, doubling), f"parity != doubling at n={n}"
        eye = parity @ parity
        assert np.allclose(eye, np.eye(n), atol=1e-12), f"H@H != I at n={n}"

    rng = np.random.default_rng(11)
    signs = rng.choice([-1.0, 1.0], size=4096)
    x = rng.standard_normal(4096)
    fwd = hadamard.forward_apply(x, 1024, signs)
    back = hadamard.inverse_apply(fwd, 1024, signs)
    assert np.allclose(back, x, atol=1e-9), "forward then inverse must be identity"
    # orthogonality preserves norms exactly up to rounding
    assert np.allclose(np.linalg.norm(fwd), np.linalg.norm(x), atol=1e-9)

    for bad in (0, 3, 1000, -4, True):
        try:
            hadamard.hadamard_matrix(bad)
            raise AssertionError(f"expected HadamardError for n={bad!r}")
        except hadamard.HadamardError:
            pass
    try:
        hadamard.forward_apply(np.ones(100), 1024, np.ones(100))
        raise AssertionError("expected HadamardError for width not multiple of block")
    except hadamard.HadamardError:
        pass


def _valid_explicit_md() -> Dict[str, object]:
    values = [1 if (i // 64) % 2 == 0 else -1 for i in range(2048)]
    return {
        "prism.hadamard.version": 1,
        "prism.hadamard.block_size": 1024,
        "prism.hadamard.transform": "normalized-sylvester-walsh-hadamard",
        "prism.hadamard.axis": "input-last-dimension",
        "prism.hadamard.sign_mode": "explicit",
        "prism.hadamard.weight_names": ["blk.0.attn_q.weight"],
        "prism.hadamard.sign_widths": [2048],
        "prism.hadamard.sign_values": values,
    }


def test_hadamard_metadata_parser() -> None:
    md = _valid_explicit_md()
    meta = hadamard.parse_hadamard_metadata(md)
    assert meta.block_size == 1024
    assert meta.sign_widths == (2048,)
    assert meta.sign_values[0] == 1 and meta.sign_values[-1] == -1
    assert meta.gdn_v_grouped is None
    vec = meta.signs_for_width(2048)
    assert vec.shape == (2048,) and set(np.unique(vec)).issubset({1.0, -1.0})
    try:
        meta.signs_for_width(1024)
        raise AssertionError("expected HadamardError for missing width")
    except hadamard.HadamardError:
        pass

    # valid identity mode (no sign keys)
    identity = dict(_valid_explicit_md())
    del identity["prism.hadamard.sign_mode"]
    del identity["prism.hadamard.sign_widths"]
    del identity["prism.hadamard.sign_values"]
    identity["prism.hadamard.sign_mode"] = "identity"
    meta_id = hadamard.parse_hadamard_metadata(identity)
    assert meta_id.sign_widths == () and meta_id.signs_by_width == {}

    # valid with optional keys
    full = dict(_valid_explicit_md())
    full["prism.hadamard.inverse_weight_names"] = ["token_embd.weight"]
    full["prism.hadamard.gdn_v_grouped"] = True
    meta_full = hadamard.parse_hadamard_metadata(full)
    assert meta_full.inverse_weight_names == ("token_embd.weight",)
    assert meta_full.gdn_v_grouped is True

    rejections: List[Tuple[Dict[str, object], str]] = []
    for key, bad_value in (
        ("prism.hadamard.version", 2),
        ("prism.hadamard.version", True),
        ("prism.hadamard.version", "1"),
        ("prism.hadamard.block_size", 0),
        ("prism.hadamard.block_size", 1000),
        ("prism.hadamard.block_size", 1024.0),
        ("prism.hadamard.transform", "butterfly"),
        ("prism.hadamard.axis", "input-first-dimension"),
        ("prism.hadamard.sign_mode", "signed"),
        ("prism.hadamard.weight_names", []),
        ("prism.hadamard.weight_names", "blk.0.attn_q.weight"),
        ("prism.hadamard.sign_widths", []),
        ("prism.hadamard.sign_widths", [999]),
        ("prism.hadamard.sign_widths", [0]),
        ("prism.hadamard.sign_widths", [-2048]),
        ("prism.hadamard.sign_values", [0] * 2047),
        ("prism.hadamard.sign_values", [2] + [1] * 2047),
        ("prism.hadamard.gdn_v_grouped", 1),
    ):
        bad = dict(_valid_explicit_md())
        bad[key] = bad_value
        rejections.append((bad, f"{key}={bad_value!r}"))
    # missing required keys
    for key in (
        "prism.hadamard.version",
        "prism.hadamard.block_size",
        "prism.hadamard.transform",
        "prism.hadamard.axis",
        "prism.hadamard.sign_mode",
        "prism.hadamard.weight_names",
        "prism.hadamard.sign_widths",
        "prism.hadamard.sign_values",
    ):
        bad = dict(_valid_explicit_md())
        del bad[key]
        rejections.append((bad, f"missing {key}"))
    # explicit mode with empty widths (would read as identity)
    bad = dict(_valid_explicit_md())
    bad["prism.hadamard.sign_widths"] = []
    rejections.append((bad, "explicit with empty widths"))
    # sign_values length mismatch
    bad = dict(_valid_explicit_md())
    bad["prism.hadamard.sign_values"] = [1] * 2047
    rejections.append((bad, "sign_values length mismatch"))
    # identity mode carrying explicit-only keys must be rejected, not ignored
    bad = dict(identity)
    bad["prism.hadamard.sign_widths"] = [2048]
    rejections.append((bad, "identity with sign_widths"))
    # inverse names must be the verified lookup table only
    bad = dict(_valid_explicit_md())
    bad["prism.hadamard.inverse_weight_names"] = ["blk.0.attn_q.weight"]
    rejections.append((bad, "inverse name not token_embd"))
    bad = dict(_valid_explicit_md())
    bad["prism.hadamard.inverse_weight_names"] = ["token_embd.weight", "token_embd.weight"]
    rejections.append((bad, "duplicate inverse name"))

    for bad_md, why in rejections:
        try:
            hadamard.parse_hadamard_metadata(bad_md)
            raise AssertionError(f"expected HadamardError for {why}")
        except hadamard.HadamardError:
            pass


# ---------------------------------------------------------------------------
# (e) enum identity: type 142 is PQ2_0, never an alias of TQ2_0

def test_enum_identity_regression() -> None:
    # Historical counterexample: a reader that aliased PQ2_0 (142) onto
    # TQ2_0 (35) would use geometry (256, 66) with the scale stored AFTER the
    # codes. PQ2_0 is its own type: (128, 34), scale stored FIRST.
    assert int(GGMLType.PQ2_0) == 142
    assert int(GGMLType.TQ2_0) == 35
    assert ggml_geometry(GGMLType.PQ2_0) == (128, 34)
    assert ggml_geometry(GGMLType.TQ2_0) == (256, 66)
    assert GGMLType.PQ2_0 != GGMLType.TQ2_0

    # A TQ2_0-geometry alias cannot even tile a 128-element tensor.
    try:
        from gguf_reader import ggml_nbytes
        ggml_nbytes(GGMLType.TQ2_0, (128,))
        raise AssertionError("TQ2_0 geometry must not consume a 128-element tensor")
    except GgufFormatError:
        pass

    with tempfile.TemporaryDirectory() as tmp:
        path = os.path.join(tmp, "pq2_only.gguf")
        weights = np.concatenate([[3.0, -3.0], np.zeros(126)]).astype(np.float32)
        payload = pq2.encode_pq2_row_ref(weights).tobytes()
        assert len(payload) == pq2.BLOCK_BYTES
        # the block's last two bytes are 2-bit codes, not a scale: a
        # scale-at-end (TQ2_0 style) interpretation would read garbage here
        assert payload[32:34] != payload[0:2]
        build_gguf(
            path,
            [_kv("general.alignment", GgufMetadataType.UINT32.value, 32)],
            [("w.weight", (128,), GGMLType.PQ2_0.value, payload)],
        )
        with GgufReader(path) as r:
            info = r.tensors["w.weight"]
            assert info.type is GGMLType.PQ2_0
            assert info.type is not GGMLType.TQ2_0
            assert info.dims == (128,)
            assert info.nbytes == 34
            raw = r.read_tensor_bytes("w.weight")
            assert len(raw) == 34
            packed = np.frombuffer(raw, dtype=np.uint8).reshape(1, 34)
            scale_bits = int(packed[0, 0]) | (int(packed[0, 1]) << 8)
            scale = float(np.frombuffer(struct.pack("<H", scale_bits), dtype="<f2")[0])
            assert scale == 3.0, f"scale-first fp16 scale must be 3.0, got {scale}"
            decoded = pq2.decode_pq2_tensor(packed, (128, 1), np.float32)
            assert np.array_equal(decoded.reshape(-1)[:3], np.array([3.0, -3.0, 0.0], dtype=np.float32))


# ---------------------------------------------------------------------------
# (d) real artifact checks

def test_real_artifact_inventory() -> None:
    path = _artifact_path()
    with GgufReader(path) as r:
        assert r.version == 3
        assert r.alignment == 32
        assert len(r.tensors) == 851
        expected = artifact.expected_inventory()
        assert set(r.tensors) == set(expected), "tensor name set mismatch"
        for name, info in r.tensors.items():
            want_type, want_dims = expected[name]
            assert info.type == want_type, f"{name}: {info.type.name} != {want_type.name}"
            assert info.dims == want_dims, f"{name}: {info.dims} != {want_dims}"
        counts: Dict[str, int] = {}
        for info in r.tensors.values():
            counts[info.type.name] = counts.get(info.type.name, 0) + 1
        assert counts == {"PQ2_0": 402, "F32": 353, "BF16": 96}

        token_embd = r.tensors["token_embd.weight"]
        output = r.tensors["output.weight"]
        assert token_embd.type == GGMLType.PQ2_0 and token_embd.dims == (5120, 248320)
        assert output.type == GGMLType.PQ2_0 and output.dims == (5120, 248320)

        full_layers = sorted(
            int(n.split(".")[1]) for n in r.tensors if n.startswith("blk.") and n.endswith(".attn_q.weight")
        )
        assert full_layers == [3 + 4 * k for k in range(16)]
        linear_layers = [i for i in range(64) if i % 4 != 3]
        assert len(linear_layers) == 48
        for i in linear_layers:
            assert f"blk.{i}.attn_qkv.weight" in r.tensors
            assert f"blk.{i}.ssm_out.weight" in r.tensors
            assert f"blk.{i}.attn_q.weight" not in r.tensors

        meta = hadamard.parse_hadamard_metadata(r.metadata)
        assert meta.block_size == 1024
        assert meta.sign_widths == (5120, 6144, 17408)
        assert len(meta.sign_values) == 28672
        assert meta.inverse_weight_names == ("token_embd.weight",)
        assert meta.gdn_v_grouped is True
        assert meta.signs_for_width(5120).shape == (5120,)

        # reader-level BF16 spot check on one small tensor
        alpha_raw = r.read_tensor_bytes("blk.0.ssm_alpha.weight")
        alpha = bf16_bytes_to_f32(np.frombuffer(alpha_raw, dtype=np.uint8))
        assert alpha.shape == (5120 * 48,)


def test_real_artifact_full_validation() -> None:
    path = _artifact_path()
    report = artifact.validate_bonsai_artifact(
        path, artifact.PINNED_SHA256, artifact.PINNED_SIZE
    )
    assert report.sha256 == artifact.PINNED_SHA256
    assert report.file_size == artifact.PINNED_SIZE
    assert report.tensor_count == 851
    assert report.dtype_counts == {"PQ2_0": 402, "F32": 353, "BF16": 96}
    assert report.alignment == 32
    assert report.full_attention_layers == tuple(3 + 4 * k for k in range(16))
    assert report.linear_layer_count == 48

    row0 = report.token_embd_row0
    assert row0.dims == (5120, 1)
    assert row0.element_count == 5120
    assert row0.block_count == 40
    assert row0.scales_positive_and_finite is True
    assert row0.values_in_code_domain is True
    assert row0.code3_count >= 0  # counted, not assumed

    blk0 = report.output_block0
    assert blk0.dims == (128, 1)
    assert blk0.element_count == 128
    assert blk0.block_count == 1
    assert blk0.scales_positive_and_finite is True
    assert blk0.values_in_code_domain is True


# ---------------------------------------------------------------------------
# pinned block geometry

def test_pq2_block_geometry_constants() -> None:
    # ggml-common.h at prism-b10683-d8f26ee:
    #   #define QK_PQ2_0 128
    #   typedef struct { ggml_half d; uint8_t qs[QK_PQ2_0/4]; } block_pq2_0;
    #   static_assert(sizeof(block_pq2_0) == sizeof(ggml_half) + QK_PQ2_0/4, ...)
    assert pq2.QK_PQ2_0 == 128
    assert pq2.BLOCK_BYTES == 34
    assert pq2.SCALE_BYTES == 2
    assert pq2.CODES_PER_BYTE == 4
    assert ggml_geometry(GGMLType.PQ2_0) == (128, 34)
    # the historical alias target, for contrast
    assert ggml_geometry(GGMLType.TQ2_0) == (256, 66)
    assert pq2.row_bytes(5120) == 40 * 34
    assert pq2.row_bytes(128) == 34
    try:
        pq2.row_bytes(130)
        raise AssertionError("expected Pq2ShapeError for row_bytes(130)")
    except pq2.Pq2ShapeError:
        pass
    try:
        pq2.row_bytes(0)
        raise AssertionError("expected Pq2ShapeError for row_bytes(0)")
    except pq2.Pq2ShapeError:
        pass


# ---------------------------------------------------------------------------
# runner

TESTS: List[Tuple[str, Callable[[], None]]] = [
    ("pq2_block_geometry_constants", test_pq2_block_geometry_constants),
    ("synthetic_gguf_roundtrip", test_synthetic_gguf_roundtrip),
    ("gguf_malformed_rejections", test_gguf_malformed_rejections),
    ("pq2_roundtrip_fixtures", test_pq2_roundtrip_fixtures),
    ("example_a_butterfly_alias_trap", test_example_a_butterfly_alias_trap),
    ("example_b_signed_transform", test_example_b_signed_transform),
    ("example_f_shape_preservation", test_example_f_shape_preservation),
    ("hadamard_agreement_and_properties", test_hadamard_agreement_and_properties),
    ("hadamard_metadata_parser", test_hadamard_metadata_parser),
    ("enum_identity_regression", test_enum_identity_regression),
    ("real_artifact_inventory", test_real_artifact_inventory),
    ("real_artifact_full_validation", test_real_artifact_full_validation),
]


def main() -> int:
    results = []
    for name, fn in TESTS:
        start = time.perf_counter()
        try:
            fn()
            status, error = "pass", None
        except SkipTest as exc:
            status, error = "skipped", str(exc)
        except Exception:
            status, error = "fail", traceback.format_exc()
        duration = time.perf_counter() - start
        results.append(
            {
                "name": name,
                "status": status,
                "duration_s": round(duration, 4),
                "error": error,
            }
        )
        print(f"[{status.upper():7s}] {name} ({duration:.2f}s)", flush=True)
        if error and status == "fail":
            for line in error.rstrip().splitlines():
                print(f"    {line}", flush=True)

    passed = sum(1 for x in results if x["status"] == "pass")
    failed = sum(1 for x in results if x["status"] == "fail")
    skipped = sum(1 for x in results if x["status"] == "skipped")
    report = {
        "generated_utc": datetime.now(timezone.utc).isoformat(),
        "python_version": sys.version.split()[0],
        "numpy_version": np.__version__,
        "summary": {
            "total": len(results),
            "pass": passed,
            "fail": failed,
            "skipped": skipped,
        },
        "results": results,
    }
    report_path = Path(__file__).resolve().parent / "report.json"
    report_path.write_text(json.dumps(report, indent=2) + "\n")
    print(f"summary: {passed} pass, {failed} fail, {skipped} skipped", flush=True)
    print(f"report: {report_path}", flush=True)
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
