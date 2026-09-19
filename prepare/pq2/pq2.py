"""PQ2_0 (ggml type 142) codec, pinned to the PrismML fork prism-b10683-d8f26ee.

Block layout (ggml-common.h ``block_pq2_0``, 34 bytes per 128 weights):

- byte 0..1: fp16 scale ``d``, little-endian, stored FIRST
- byte 2..33: 32 bytes of 2-bit codes, four codes per byte, code j of a
  block lives in byte ``j // 4`` at bit offset ``(j % 4) * 2`` (little-endian
  bit order inside the byte)

Code map (ggml-quants.c ``dequantize_row_pq2_0``): value = (q - 1) * d, so
00 -> -d, 01 -> 0, 10 -> +d, 11 -> +2d. The reference quantizer only emits
codes 0..2; code 3 is decodable but countable in validation.

Reference encoder (ggml-quants.c ``quantize_row_pq2_0_ref``): d = amax of
the block stored as fp16, q = round(w / d) + 1 clamped to [0, 3] with C
``roundf`` semantics (half away from zero).

Tensor geometry: GGUF stores ne[0] (the input/column dim) contiguous, so a
weight tensor with stored dims [in, out] is a byte stream of ``out`` rows of
``(in / 128) * 34`` bytes. Decoding preserves that 2-D structure: the output
is the matmul-ready (out, in) array, never a flat vector.
"""

from __future__ import annotations

from typing import Tuple, Union

import numpy as np
from numpy.typing import NDArray

#: elements per PQ2_0 block (ggml-common.h ``QK_PQ2_0``)
QK_PQ2_0 = 128
#: bytes per PQ2_0 block: 2-byte fp16 scale + 32 code bytes
BLOCK_BYTES = 34
#: bytes of the fp16 scale at the start of each block
SCALE_BYTES = 2
#: 2-bit codes packed per byte
CODES_PER_BYTE = 4

_DTYPE_HINT = Union[str, np.dtype, type]


class Pq2Error(Exception):
    """Base class for PQ2_0 codec failures."""


class Pq2ShapeError(Pq2Error):
    """Shape, geometry or dtype of an input does not tile into PQ2_0 blocks."""


def _as_int(value: object, what: str) -> int:
    if type(value) is not int:
        raise Pq2ShapeError(f"{what} must be an int, got {type(value).__name__}")
    return value


def row_bytes(ne0: int) -> int:
    """Packed bytes of one tensor row with ne[0] contiguous elements."""
    if type(ne0) is not int or ne0 <= 0:
        raise Pq2ShapeError(f"ne0 must be a positive int, got {ne0!r}")
    if ne0 % QK_PQ2_0 != 0:
        raise Pq2ShapeError(
            f"ne0 {ne0} is not a multiple of the PQ2_0 block size {QK_PQ2_0}"
        )
    return (ne0 // QK_PQ2_0) * BLOCK_BYTES


def decode_pq2_tensor(
    packed: NDArray[np.uint8],
    logical_shape: Tuple[int, int],
    out_dtype: _DTYPE_HINT,
) -> NDArray[np.floating]:
    """Decode packed PQ2_0 blocks exactly per ``dequantize_row_pq2_0``.

    ``packed`` is a 2-D uint8 array of shape (rows, row_bytes) where rows is
    ``logical_shape[1]`` and row_bytes is ``(logical_shape[0] // 128) * 34``.
    ``logical_shape`` is the stored GGUF dims [in, out] with ne[0] contiguous.

    Returns a 2-D array of shape (out, in): row i holds the ne[0]-contiguous
    elements of byte-row i, so ``decoded @ x`` computes the layer output for
    an activation x of length in. A flat vector is never returned.
    """
    if not isinstance(packed, np.ndarray) or packed.dtype != np.dtype(np.uint8):
        raise Pq2ShapeError(
            f"packed bytes must be a uint8 ndarray, got {type(packed).__name__} "
            f"with dtype {getattr(packed, 'dtype', None)}"
        )
    if packed.ndim != 2:
        raise Pq2ShapeError(
            f"packed bytes must be 2-D (rows, row_bytes), got ndim {packed.ndim}"
        )
    if not isinstance(logical_shape, tuple) or len(logical_shape) != 2:
        raise Pq2ShapeError(
            f"logical_shape must be a 2-tuple [in, out], got {logical_shape!r}"
        )
    ne0 = _as_int(logical_shape[0], "logical_shape[0]")
    ne1 = _as_int(logical_shape[1], "logical_shape[1]")
    if ne0 <= 0 or ne1 <= 0:
        raise Pq2ShapeError(f"logical dims must be positive, got {logical_shape!r}")
    dtype = np.dtype(out_dtype)
    if dtype.kind != "f":
        raise Pq2ShapeError(
            f"out_dtype must be floating point, got {dtype} (no silent int casting)"
        )
    expected_rows = ne1
    expected_row_bytes = row_bytes(ne0)
    if packed.shape != (expected_rows, expected_row_bytes):
        raise Pq2ShapeError(
            f"packed shape {packed.shape} does not match logical shape "
            f"{logical_shape!r}: expected ({expected_rows}, {expected_row_bytes})"
        )

    # A row of ne[0] elements is (ne0 // 128) consecutive 34-byte blocks; the
    # fp16 scale sits at the start of every block.
    blocks = packed.reshape(expected_rows, ne0 // QK_PQ2_0, BLOCK_BYTES)

    # fp16 scale bits, assembled little-endian, then reinterpreted as fp16.
    # (fp16 -> fp32 widening is exponent-bias arithmetic, NOT a bit shift;
    # the shift trick only applies to bf16.)
    scale_bits = blocks[:, :, 0].astype(np.uint16) | (
        blocks[:, :, 1].astype(np.uint16) << 8
    )
    d = np.frombuffer(
        scale_bits.astype("<u2").tobytes(), dtype="<f2"
    ).reshape(scale_bits.shape).astype(dtype)

    qs = np.ascontiguousarray(blocks[:, :, SCALE_BYTES:BLOCK_BYTES])
    bits = np.unpackbits(qs, axis=-1, bitorder="little").reshape(
        expected_rows, ne0 // QK_PQ2_0, QK_PQ2_0, 2
    )
    codes = bits[..., 0] | (bits[..., 1].astype(np.uint8) << 1)
    values = (codes.astype(dtype) - dtype.type(1)) * d.reshape(
        expected_rows, ne0 // QK_PQ2_0, 1
    )
    return values.reshape(expected_rows, ne0)


def encode_pq2_row_ref(weights: NDArray[np.float32]) -> NDArray[np.uint8]:
    """Encode float32 rows per ``quantize_row_pq2_0_ref`` for round-trip fixtures.

    ``weights`` must be a 1-D float32 array whose length is a multiple of 128.
    Returns a (n_blocks, 34) uint8 array. The block scale is amax stored as
    fp16; blocks whose amax is not exactly representable in fp16 raise rather
    than silently quantizing through inf or zero.
    """
    if not isinstance(weights, np.ndarray) or weights.dtype != np.dtype(np.float32):
        raise Pq2ShapeError(
            f"weights must be a float32 ndarray, got {type(weights).__name__} "
            f"with dtype {getattr(weights, 'dtype', None)}"
        )
    if weights.ndim != 1:
        raise Pq2ShapeError(f"weights must be 1-D, got ndim {weights.ndim}")
    if weights.size == 0 or weights.size % QK_PQ2_0 != 0:
        raise Pq2ShapeError(
            f"weights length {weights.size} is not a nonzero multiple of {QK_PQ2_0}"
        )
    if not np.isfinite(weights).all():
        raise Pq2ShapeError("weights contain non-finite values")
    blocks = weights.reshape(-1, QK_PQ2_0)
    n_blocks = blocks.shape[0]

    amax = np.abs(blocks).max(axis=1)  # float32, matches C float amax
    fp16_max = float(np.finfo(np.float16).max)
    if float(amax.max()) > fp16_max:
        raise Pq2Error(
            f"block amax {amax.max()!r} exceeds the fp16 scale range ({fp16_max})"
        )
    with np.errstate(over="ignore", under="ignore"):
        d16 = amax.astype(np.float16)
    d16_f32 = d16.astype(np.float32)
    if np.any((amax > 0) & (d16_f32 == 0)):
        raise Pq2Error("block amax underflows the fp16 scale range")

    # id = 1/d in float32, exactly 0 for an all-zero block (matches the C ref)
    inv = np.where(amax > 0, np.float32(1.0) / np.where(amax > 0, amax, 1.0), np.float32(0.0))
    scaled = blocks * inv.reshape(n_blocks, 1)
    # roundf: round half away from zero (numpy.round would round half to even)
    rounded = np.where(
        scaled >= 0, np.floor(scaled + np.float32(0.5)), np.ceil(scaled - np.float32(0.5))
    )
    q = np.clip(rounded.astype(np.int64) + 1, 0, 3).astype(np.uint8)
    # repack: 4 consecutive codes per byte, code j at bit offset 2*(j%4)
    codes = q.reshape(n_blocks, BLOCK_BYTES - SCALE_BYTES, CODES_PER_BYTE)
    qs_bytes = np.zeros((n_blocks, BLOCK_BYTES - SCALE_BYTES), dtype=np.uint8)
    for lane in range(CODES_PER_BYTE):
        qs_bytes |= codes[:, :, lane] << np.uint8(2 * lane)

    scale_bits16 = np.frombuffer(
        d16.astype("<f2").tobytes(), dtype="<u2"
    )
    scale_lo = (scale_bits16 & 0xFF).astype(np.uint8)
    scale_hi = (scale_bits16 >> 8).astype(np.uint8)
    out = np.empty((n_blocks, BLOCK_BYTES), dtype=np.uint8)
    out[:, 0] = scale_lo
    out[:, 1] = scale_hi
    out[:, SCALE_BYTES:BLOCK_BYTES] = qs_bytes
    return out
