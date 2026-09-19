"""Normalized Sylvester Walsh-Hadamard transform, pinned to the PrismML fork
prism-b10683-d8f26ee.

Contract (llama-model.cpp ~1194-1340, llama-impl.h ``llama_mul_mat_hadamard``,
llama-graph.cpp ``build_lora_mm`` / token-embedding path):

- H is the natural-order normalized Walsh-Hadamard matrix:
  H[i][j] = (-1)^popcount(i & j) / sqrt(block_size). It is involutive
  (H @ H = I) and orthonormal. The fork builds it with the quadrant-doubling
  construction in llama-kv-cache.cpp ``ggml_gen_hadamard``; the doubling
  construction and the parity formula produce identical matrices.
- Forward (activations, per 1024 block): x' = H @ (D . x), where D is the
  per-width sign vector applied elementwise first (ggml_mul by the sign
  tensor) and H multiplies each contiguous block_size slice.
- Inverse (token embedding lookup; rows are stored latents z): x = D . (H @ z):
  H first, then the sign multiply (llama-graph.cpp: "h = s * (H z)").
- The GDN ssm_out exception (perm_hd/perm_nk/perm_rep head regrouping) exists
  in the fork but is NOT implemented here; this package documents it as
  unsupported.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Dict, Optional, Tuple

import numpy as np
from numpy.typing import NDArray

#: metadata key namespace
_KEY_VERSION = "prism.hadamard.version"
_KEY_BLOCK_SIZE = "prism.hadamard.block_size"
_KEY_TRANSFORM = "prism.hadamard.transform"
_KEY_AXIS = "prism.hadamard.axis"
_KEY_SIGN_MODE = "prism.hadamard.sign_mode"
_KEY_WEIGHT_NAMES = "prism.hadamard.weight_names"
_KEY_SIGN_WIDTHS = "prism.hadamard.sign_widths"
_KEY_SIGN_VALUES = "prism.hadamard.sign_values"
_KEY_INVERSE_NAMES = "prism.hadamard.inverse_weight_names"
_KEY_GDN_V_GROUPED = "prism.hadamard.gdn_v_grouped"

_TRANSFORM = "normalized-sylvester-walsh-hadamard"
_AXIS = "input-last-dimension"
_SIGN_MODES = ("identity", "explicit")

_HADAMARD_CACHE: Dict[int, NDArray[np.float64]] = {}


class HadamardError(Exception):
    """Hadamard metadata or transform contract violation."""


def _require_power_of_two(block_size: int, what: str) -> None:
    if type(block_size) is not int or block_size <= 0:
        raise HadamardError(f"{what} must be a positive int, got {block_size!r}")
    if block_size & (block_size - 1) != 0:
        raise HadamardError(f"{what} {block_size} is not a power of two")


def hadamard_matrix_parity(n: int) -> NDArray[np.float64]:
    """Natural-order normalized WHT via H[i][j] = (-1)^popcount(i & j)/sqrt(n)."""
    _require_power_of_two(n, "n")
    i = np.arange(n, dtype=np.int64).reshape(n, 1)
    j = np.arange(n, dtype=np.int64).reshape(1, n)
    overlap = i & j
    parity = np.zeros((n, n), dtype=np.int64)
    shift = 0
    while (n - 1) >> shift:
        parity += (overlap >> shift) & 1
        shift += 1
    signs = 1 - 2 * (parity & 1)
    return signs.astype(np.float64) / np.sqrt(np.float64(n))


def hadamard_matrix_doubling(n: int) -> NDArray[np.float64]:
    """The ggml_gen_hadamard quadrant-doubling construction (llama-kv-cache.cpp)."""
    _require_power_of_two(n, "n")
    m = np.zeros((n, n), dtype=np.float64)
    m[0, 0] = 1.0 / np.sqrt(np.float64(n))
    s = 1
    while s < n:
        m[s:2 * s, :s] = m[:s, :s]
        m[:s, s:2 * s] = m[:s, :s]
        m[s:2 * s, s:2 * s] = -m[:s, :s]
        s *= 2
    return m


def hadamard_matrix(n: int) -> NDArray[np.float64]:
    """Cached, read-only normalized WHT of size n (parity construction)."""
    cached = _HADAMARD_CACHE.get(n)
    if cached is not None:
        return cached
    m = hadamard_matrix_parity(n)
    m.setflags(write=False)
    _HADAMARD_CACHE[n] = m
    return m


def _validate_signs(signs: NDArray, n: int) -> NDArray[np.float64]:
    if not isinstance(signs, np.ndarray):
        raise HadamardError(f"signs must be an ndarray, got {type(signs).__name__}")
    if signs.shape != (n,):
        raise HadamardError(f"signs shape {signs.shape} must be ({n},)")
    if signs.dtype != np.dtype(np.float64):
        signs = signs.astype(np.float64)
    if not np.all((signs == 1.0) | (signs == -1.0)):
        raise HadamardError("signs must contain only +1 and -1")
    return signs


def forward_apply(
    x: NDArray[np.floating],
    block_size: int,
    signs: NDArray,
) -> NDArray[np.float64]:
    """Runtime forward transform: per block_size block, H @ (signs * x).

    x is any float array transformed along its last dimension; the last
    dimension must be a multiple of block_size and signs must span it.
    """
    _require_power_of_two(block_size, "block_size")
    if not isinstance(x, np.ndarray) or x.dtype.kind != "f":
        raise HadamardError(f"x must be a floating ndarray, got {type(x).__name__}")
    n = x.shape[-1]
    if n == 0 or n % block_size != 0:
        raise HadamardError(
            f"last dimension {n} is not a nonzero multiple of block_size {block_size}"
        )
    d = _validate_signs(signs, n)
    h = hadamard_matrix(block_size)
    flat = x.reshape(-1, n).astype(np.float64)
    # mirrors the graph: full-width sign multiply first (ggml_mul), then the
    # per-block H matmul (llama_mul_mat_hadamard reshapes to (bs, n/bs))
    signed = flat * d.reshape(1, n)
    transformed = (signed.reshape(-1, block_size) @ h.T).reshape(flat.shape)
    return transformed.reshape(x.shape)


def inverse_apply(
    z: NDArray[np.floating],
    block_size: int,
    signs: NDArray,
) -> NDArray[np.float64]:
    """Runtime inverse transform: x = signs * (H @ z), per block_size block."""
    _require_power_of_two(block_size, "block_size")
    if not isinstance(z, np.ndarray) or z.dtype.kind != "f":
        raise HadamardError(f"z must be a floating ndarray, got {type(z).__name__}")
    n = z.shape[-1]
    if n == 0 or n % block_size != 0:
        raise HadamardError(
            f"last dimension {n} is not a nonzero multiple of block_size {block_size}"
        )
    d = _validate_signs(signs, n)
    h = hadamard_matrix(block_size)
    flat = z.reshape(-1, n).astype(np.float64)
    # mirrors the graph: per-block H matmul first, then the sign multiply
    rotated = (flat.reshape(-1, block_size) @ h.T).reshape(flat.shape)
    restored = rotated * d.reshape(1, n)
    return restored.reshape(z.shape)


@dataclass(frozen=True)
class HadamardMetadata:
    """Validated prism.hadamard.* metadata."""

    block_size: int
    sign_mode: str
    weight_names: Tuple[str, ...]
    sign_widths: Tuple[int, ...]
    sign_values: Tuple[int, ...]
    inverse_weight_names: Tuple[str, ...]
    gdn_v_grouped: Optional[bool]
    signs_by_width: Dict[int, NDArray[np.float64]] = field(default_factory=dict)

    def signs_for_width(self, width: int) -> NDArray[np.float64]:
        """Sign vector for one weight width; fails loudly when absent."""
        vec = self.signs_by_width.get(width)
        if vec is None:
            raise HadamardError(
                f"prism.hadamard has no sign vector for width {width}"
            )
        return vec


def _get_int(md: dict, key: str) -> int:
    value = md.get(key)
    if type(value) is not int:
        raise HadamardError(f"{key} must be a UINT32 int, got {value!r}")
    return value


def _get_str(md: dict, key: str) -> str:
    value = md.get(key)
    if not isinstance(value, str):
        raise HadamardError(f"{key} must be a string, got {value!r}")
    return value


def _get_str_list(md: dict, key: str) -> Tuple[str, ...]:
    value = md.get(key)
    if not isinstance(value, list) or not all(isinstance(v, str) for v in value):
        raise HadamardError(f"{key} must be an array of strings, got {value!r}")
    return tuple(value)


def _get_int_list(md: dict, key: str) -> Tuple[int, ...]:
    value = md.get(key)
    if not isinstance(value, list) or not all(type(v) is int for v in value):
        raise HadamardError(f"{key} must be an array of ints, got {value!r}")
    return tuple(value)


def parse_hadamard_metadata(md: dict) -> HadamardMetadata:
    """Strictly validate prism.hadamard.* metadata per the fork's loader.

    Deviation from the fork (stricter here): sign_widths/sign_values present
    while sign_mode is "identity" are rejected instead of silently ignored,
    because ignoring them can silently change the model function.
    """
    if not isinstance(md, dict):
        raise HadamardError(f"metadata must be a dict, got {type(md).__name__}")
    version = _get_int(md, _KEY_VERSION)
    if version != 1:
        raise HadamardError(f"unsupported prism.hadamard.version: {version}")
    block_size = _get_int(md, _KEY_BLOCK_SIZE)
    _require_power_of_two(block_size, _KEY_BLOCK_SIZE)
    transform = _get_str(md, _KEY_TRANSFORM)
    if transform != _TRANSFORM:
        raise HadamardError(f"unsupported prism.hadamard.transform: {transform}")
    axis = _get_str(md, _KEY_AXIS)
    if axis != _AXIS:
        raise HadamardError(f"unsupported prism.hadamard.axis: {axis}")
    sign_mode = _get_str(md, _KEY_SIGN_MODE)
    if sign_mode not in _SIGN_MODES:
        raise HadamardError(f"unsupported prism.hadamard.sign_mode: {sign_mode}")
    weight_names = _get_str_list(md, _KEY_WEIGHT_NAMES)
    if not weight_names:
        raise HadamardError("prism.hadamard.weight_names is empty")

    sign_widths: Tuple[int, ...] = ()
    sign_values: Tuple[int, ...] = ()
    signs_by_width: Dict[int, NDArray[np.float64]] = {}
    if sign_mode == "explicit":
        sign_widths = _get_int_list(md, _KEY_SIGN_WIDTHS)
        sign_values = _get_int_list(md, _KEY_SIGN_VALUES)
        # explicit mode with no widths would read as identity and silently
        # change the model function (mirrors the fork's loader)
        if not sign_widths:
            raise HadamardError("prism.hadamard.sign_mode is explicit but sign_widths is empty")
        offset = 0
        for width in sign_widths:
            if width <= 0 or width % block_size != 0 or offset + width > len(sign_values):
                raise HadamardError(f"invalid prism.hadamard sign width: {width}")
            segment = sign_values[offset:offset + width]
            if any(v not in (1, -1) for v in segment):
                raise HadamardError("prism.hadamard sign values must be +/-1")
            signs_by_width[width] = np.asarray(segment, dtype=np.float64)
            offset += width
        if offset != len(sign_values):
            raise HadamardError("prism.hadamard.sign_values length mismatch")
    else:
        for key in (_KEY_SIGN_WIDTHS, _KEY_SIGN_VALUES):
            if key in md:
                raise HadamardError(
                    f"{key} present but sign_mode is 'identity'; refusing to ignore it"
                )

    inverse_names: Tuple[str, ...] = ()
    if _KEY_INVERSE_NAMES in md:
        inverse_names = _get_str_list(md, _KEY_INVERSE_NAMES)
        seen_inverse: set[str] = set()
        for name in inverse_names:
            # the graph applies the inverse only to the token-embedding lookup
            if name != "token_embd.weight":
                raise HadamardError(
                    f"prism.hadamard: weight {name!r} is not a verified "
                    "inverse-after-lookup table"
                )
            if name in weight_names or name in seen_inverse:
                raise HadamardError(f"duplicate prism.hadamard inverse weight: {name}")
            seen_inverse.add(name)

    gdn_v_grouped: Optional[bool] = None
    if _KEY_GDN_V_GROUPED in md:
        value = md[_KEY_GDN_V_GROUPED]
        if type(value) is not bool:
            raise HadamardError(f"{_KEY_GDN_V_GROUPED} must be a bool, got {value!r}")
        gdn_v_grouped = value

    return HadamardMetadata(
        block_size=block_size,
        sign_mode=sign_mode,
        weight_names=weight_names,
        sign_widths=sign_widths,
        sign_values=sign_values,
        inverse_weight_names=inverse_names,
        gdn_v_grouped=gdn_v_grouped,
        signs_by_width=signs_by_width,
    )
