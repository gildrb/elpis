"""Validation of the pinned Bonsai PQ2_0 artifact.

Artifact: Ternary-Bonsai-2-27B-PQ2_0.gguf
sha256 3907dc1658db1f78a9826bf8d5bcb8dc65db0d466388937af57f2294fae62ec1
size 7206168928 bytes, arch qwen35, 851 tensors (402 PQ2_0, 353 F32, 96 BF16).

The inventory below is pinned from the artifact itself at the reference
release prism-b10683-d8f26ee: 64 decoder layers, full-attention layers every
4th index (qwen35.full_attention_interval), linear (GDN) layers elsewhere.
"""

from __future__ import annotations

import hashlib
import os
from dataclasses import dataclass
from typing import Dict, List, Tuple

import numpy as np
from numpy.typing import NDArray

import hadamard
import pq2
from gguf_reader import GGMLType, GgufError, GgufReader, TensorInfo

PINNED_SHA256 = "3907dc1658db1f78a9826bf8d5bcb8dc65db0d466388937af57f2294fae62ec1"
PINNED_SIZE = 7206168928

_ARCH = "qwen35"
_N_LAYERS = 64
_FULL_INTERVAL = 4
_N_EMBD = 5120
_N_VOCAB = 248320
_FFN = 17408
_N_SSM_OUT = 6144
_DT_RANK = 48

_PQ2 = GGMLType.PQ2_0
_F32 = GGMLType.F32
_BF16 = GGMLType.BF16

_HASH_CHUNK = 4 * 1024 * 1024


class ArtifactError(Exception):
    """One or more artifact contract violations (all violations reported)."""


@dataclass(frozen=True)
class Pq2SampleCheck:
    """Result of decoding one sample row/block of the real artifact."""

    name: str
    dims: Tuple[int, ...]
    block_count: int
    scale_min: float
    scale_max: float
    scales_positive_and_finite: bool
    element_count: int
    code3_count: int
    values_in_code_domain: bool


@dataclass(frozen=True)
class ArtifactReport:
    path: str
    file_size: int
    sha256: str
    tensor_count: int
    dtype_counts: Dict[str, int]
    alignment: int
    data_offset: int
    full_attention_layers: Tuple[int, ...]
    linear_layer_count: int
    token_embd_row0: Pq2SampleCheck
    output_block0: Pq2SampleCheck


def expected_inventory() -> Dict[str, Tuple[GGMLType, Tuple[int, ...]]]:
    """Name -> (type, stored dims [in, out]) for all 851 tensors."""
    expected: Dict[str, Tuple[GGMLType, Tuple[int, ...]]] = {
        "token_embd.weight": (_PQ2, (_N_EMBD, _N_VOCAB)),
        "output.weight": (_PQ2, (_N_EMBD, _N_VOCAB)),
        "output_norm.weight": (_F32, (_N_EMBD,)),
    }
    for i in range(_N_LAYERS):
        full = i % _FULL_INTERVAL == _FULL_INTERVAL - 1
        expected[f"blk.{i}.attn_norm.weight"] = (_F32, (_N_EMBD,))
        expected[f"blk.{i}.post_attention_norm.weight"] = (_F32, (_N_EMBD,))
        expected[f"blk.{i}.ffn_gate.weight"] = (_PQ2, (_N_EMBD, _FFN))
        expected[f"blk.{i}.ffn_up.weight"] = (_PQ2, (_N_EMBD, _FFN))
        expected[f"blk.{i}.ffn_down.weight"] = (_PQ2, (_FFN, _N_EMBD))
        if full:
            expected[f"blk.{i}.attn_q.weight"] = (_PQ2, (_N_EMBD, 12288))
            expected[f"blk.{i}.attn_k.weight"] = (_PQ2, (_N_EMBD, 1024))
            expected[f"blk.{i}.attn_v.weight"] = (_PQ2, (_N_EMBD, 1024))
            expected[f"blk.{i}.attn_output.weight"] = (_PQ2, (_N_SSM_OUT, _N_EMBD))
            expected[f"blk.{i}.attn_q_norm.weight"] = (_F32, (256,))
            expected[f"blk.{i}.attn_k_norm.weight"] = (_F32, (256,))
        else:
            expected[f"blk.{i}.attn_qkv.weight"] = (_PQ2, (_N_EMBD, 10240))
            expected[f"blk.{i}.attn_gate.weight"] = (_PQ2, (_N_EMBD, _N_SSM_OUT))
            expected[f"blk.{i}.ssm_out.weight"] = (_PQ2, (_N_SSM_OUT, _N_EMBD))
            expected[f"blk.{i}.ssm_a"] = (_F32, (_DT_RANK,))
            expected[f"blk.{i}.ssm_alpha.weight"] = (_BF16, (_N_EMBD, _DT_RANK))
            expected[f"blk.{i}.ssm_beta.weight"] = (_BF16, (_N_EMBD, _DT_RANK))
            expected[f"blk.{i}.ssm_conv1d.weight"] = (_F32, (4, 10240))
            expected[f"blk.{i}.ssm_dt.bias"] = (_F32, (_DT_RANK,))
            expected[f"blk.{i}.ssm_norm.weight"] = (_F32, (128,))
    return expected



def _sha256_file(path: str) -> str:
    digest = hashlib.sha256()
    with open(path, "rb") as f:
        while True:
            chunk = f.read(_HASH_CHUNK)
            if not chunk:
                break
            digest.update(chunk)
    return digest.hexdigest()


def _check_int_metadata(
    reader: GgufReader, violations: List[str], checks: Dict[str, int]
) -> None:
    for key, expected_value in checks.items():
        value = reader.metadata.get(key)
        if type(value) is not int:
            violations.append(f"metadata {key} must be a UINT32 int, got {value!r}")
        elif value != expected_value:
            violations.append(f"metadata {key} = {value}, expected {expected_value}")


def _check_float_metadata(
    reader: GgufReader, violations: List[str], checks: Dict[str, float]
) -> None:
    for key, expected_value in checks.items():
        value = reader.metadata.get(key)
        if not isinstance(value, float):
            violations.append(f"metadata {key} must be a FLOAT32, got {value!r}")
        elif not np.isclose(value, expected_value, rtol=1e-6, atol=0.0):
            violations.append(f"metadata {key} = {value}, expected {expected_value}")


def _validate_inventory(reader: GgufReader, violations: List[str]) -> None:
    expected = expected_inventory()
    actual: Dict[str, TensorInfo] = reader.tensors
    if len(actual) != 851:
        violations.append(f"tensor count {len(actual)}, expected 851")
    for name, info in actual.items():
        want = expected.get(name)
        if want is None:
            violations.append(f"unexpected tensor {name!r}")
            continue
        want_type, want_dims = want
        if info.type != want_type:
            violations.append(
                f"tensor {name!r} type {info.type.name}, expected {want_type.name}"
            )
        if info.dims != want_dims:
            violations.append(
                f"tensor {name!r} dims {info.dims}, expected {want_dims}"
            )
    for name in expected:
        if name not in actual:
            violations.append(f"missing tensor {name!r}")
    counts: Dict[str, int] = {}
    for info in actual.values():
        counts[info.type.name] = counts.get(info.type.name, 0) + 1
    for type_name, want in (("PQ2_0", 402), ("F32", 353), ("BF16", 96)):
        got = counts.get(type_name, 0)
        if got != want:
            violations.append(f"{type_name} tensor count {got}, expected {want}")
    if set(counts) - {"PQ2_0", "F32", "BF16"}:
        violations.append(f"unexpected dtypes present: {sorted(set(counts) - {'PQ2_0', 'F32', 'BF16'})}")


def _validate_metadata(reader: GgufReader, violations: List[str]) -> hadamard.HadamardMetadata:
    _check_int_metadata(reader, violations, {
        "general.quantization_version": 2,
        "general.file_type": 141,
        "qwen35.block_count": _N_LAYERS,
        "qwen35.context_length": 262144,
        "qwen35.embedding_length": _N_EMBD,
        "qwen35.feed_forward_length": _FFN,
        "qwen35.full_attention_interval": _FULL_INTERVAL,
        "qwen35.attention.head_count": 24,
        "qwen35.attention.head_count_kv": 4,
        "qwen35.attention.key_length": 256,
        "qwen35.attention.value_length": 256,
        "qwen35.ssm.conv_kernel": 4,
        "qwen35.ssm.group_count": 16,
        "qwen35.ssm.inner_size": _N_SSM_OUT,
        "qwen35.ssm.state_size": 128,
        "qwen35.ssm.time_step_rank": _DT_RANK,
    })
    _check_float_metadata(reader, violations, {
        "qwen35.attention.layer_norm_rms_epsilon": 1e-6,
        "qwen35.rope.freq_base": 10000000.0,
    })
    arch = reader.metadata.get("general.architecture")
    if arch != _ARCH:
        violations.append(f"general.architecture = {arch!r}, expected {_ARCH!r}")

    try:
        meta = hadamard.parse_hadamard_metadata(reader.metadata)
    except hadamard.HadamardError as exc:
        violations.append(f"hadamard metadata: {exc}")
        raise ArtifactError("\n".join(violations)) from exc

    if meta.sign_widths != (5120, 6144, 17408):
        violations.append(
            f"prism.hadamard.sign_widths = {list(meta.sign_widths)}, "
            "expected [5120, 6144, 17408]"
        )
    if len(meta.sign_values) != 28672:
        violations.append(
            f"prism.hadamard.sign_values length {len(meta.sign_values)}, expected 28672"
        )
    if meta.inverse_weight_names != ("token_embd.weight",):
        violations.append(
            f"prism.hadamard.inverse_weight_names = {list(meta.inverse_weight_names)}, "
            "expected ['token_embd.weight']"
        )
    if meta.gdn_v_grouped is not True:
        violations.append(
            f"prism.hadamard.gdn_v_grouped = {meta.gdn_v_grouped!r}, expected True"
        )
    pq2_names = {
        name for name, info in reader.tensors.items() if info.type == _PQ2
    }
    want_folded = pq2_names - {"token_embd.weight"}
    if set(meta.weight_names) != want_folded:
        missing = sorted(want_folded - set(meta.weight_names))[:5]
        extra = sorted(set(meta.weight_names) - want_folded)[:5]
        violations.append(
            "prism.hadamard.weight_names does not match the folded PQ2 weight set; "
            f"missing sample {missing}, unexpected sample {extra}"
        )
    return meta


def _sample_check(
    packed: NDArray[np.uint8],
    logical_shape: Tuple[int, int],
    label: str,
    violations: List[str],
) -> Pq2SampleCheck:
    if packed.ndim != 2 or packed.dtype != np.uint8:
        raise ArtifactError(f"{label}: packed sample must be a 2-D uint8 array")
    n_rows, row_bytes = packed.shape
    if row_bytes % pq2.BLOCK_BYTES != 0:
        raise ArtifactError(f"{label}: row_bytes {row_bytes} is not a block multiple")
    blocks_per_row = row_bytes // pq2.BLOCK_BYTES
    n_blocks = n_rows * blocks_per_row
    blocks = packed.reshape(n_rows, blocks_per_row, pq2.BLOCK_BYTES)
    scales_f32 = np.frombuffer(
        np.ascontiguousarray(blocks[:, :, :2]).tobytes(), dtype="<f2"
    ).reshape(n_rows, blocks_per_row).astype(np.float32)
    values = pq2.decode_pq2_tensor(packed, logical_shape, np.float32)
    positive_finite = bool(np.isfinite(scales_f32).all() and (scales_f32 > 0).all())
    if not positive_finite:
        violations.append(f"{label}: fp16 scales must be positive and finite")
    # per-block code domain {-d, 0, +d, +2d}; (q-1)*d is exact in fp32 for
    # q-1 in {0, 1, 2}, so a small relative tolerance only absorbs denormals
    dmat = np.abs(scales_f32).reshape(n_rows, blocks_per_row, 1)
    vm = values.reshape(n_rows, blocks_per_row, pq2.QK_PQ2_0)
    tol = dmat * 1e-6
    in_domain = bool(
        np.all(
            (vm >= -dmat - tol)
            & (vm <= 2 * dmat + tol)
            & (
                (vm == 0)
                | (np.abs(np.abs(vm) - dmat) <= tol)
                | (np.abs(vm - 2 * dmat) <= tol)
            )
        )
    )
    # a code-3 (+2d) occurrence is any nonzero value that is not +/-d
    code3 = int(np.sum((vm != 0) & (np.abs(np.abs(vm) - dmat) > tol)))
    if not in_domain:
        violations.append(
            f"{label}: decoded values leave the PQ2 code domain {{-d, 0, +d, +2d}}"
        )
    return Pq2SampleCheck(
        name=label,
        dims=logical_shape,
        block_count=int(n_blocks),
        scale_min=float(scales_f32.min()),
        scale_max=float(scales_f32.max()),
        scales_positive_and_finite=positive_finite,
        element_count=int(values.size),
        code3_count=code3,
        values_in_code_domain=bool(in_domain),
    )


def validate_bonsai_artifact(
    path: str,
    expected_sha256: str = PINNED_SHA256,
    expected_size: int = PINNED_SIZE,
) -> ArtifactReport:
    """Full artifact validation; raises ArtifactError listing every violation."""
    violations: List[str] = []

    path = os.fspath(path)
    if not os.path.exists(path):
        raise ArtifactError(f"artifact not found: {path}")
    size = os.path.getsize(path)
    if size != expected_size:
        violations.append(f"file size {size}, expected {expected_size}")

    sha = _sha256_file(path)
    if sha != expected_sha256:
        violations.append(f"sha256 {sha}, expected {expected_sha256}")

    try:
        reader = GgufReader(path)
    except GgufError as exc:
        raise ArtifactError(f"GGUF parse failed: {exc}") from exc
    try:
        _validate_inventory(reader, violations)
        _validate_metadata(reader, violations)

        token_row_bytes = pq2.row_bytes(_N_EMBD)
        raw = reader.read_tensor_bytes("token_embd.weight")
        packed_row0 = np.frombuffer(raw[:token_row_bytes], dtype=np.uint8).reshape(
            1, token_row_bytes
        ).copy()
        token_embd_row0 = _sample_check(
            packed_row0, (_N_EMBD, 1), "token_embd.weight row 0", violations,
        )

        out_raw = reader.read_tensor_bytes("output.weight")
        packed_blk0 = np.frombuffer(out_raw[: pq2.BLOCK_BYTES], dtype=np.uint8).reshape(
            1, pq2.BLOCK_BYTES
        ).copy()
        output_block0 = _sample_check(
            packed_blk0, (128, 1), "output.weight block 0", violations,
        )
    finally:
        reader.close()

    if violations:
        raise ArtifactError(
            f"{len(violations)} artifact violation(s):\n" + "\n".join(violations)
        )
    full_layers = tuple(i for i in range(_N_LAYERS) if i % _FULL_INTERVAL == _FULL_INTERVAL - 1)
    return ArtifactReport(
        path=path,
        file_size=size,
        sha256=sha,
        tensor_count=851,
        dtype_counts={"PQ2_0": 402, "F32": 353, "BF16": 96},
        alignment=reader.alignment,
        data_offset=reader.data_offset,
        full_attention_layers=full_layers,
        linear_layer_count=_N_LAYERS - len(full_layers),
        token_embd_row0=token_embd_row0,
        output_block0=output_block0,
    )

