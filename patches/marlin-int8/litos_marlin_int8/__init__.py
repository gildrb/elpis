# SPDX-License-Identifier: Apache-2.0
# Scale/permutation helpers derived from vLLM; see source-manifest.json.
"""SM86 uint4b8/group128 W4A8. No W4A16 or framework fallback exists here."""
from enum import IntEnum

import torch

from . import _litos_marlin_int8  # Loads only this extension, not sgl-kernel/vLLM.
from .quantization import per_token_quant_int8

__all__ = [
    "WeightType", "validate_metadata", "gptq_marlin_repack", "gptq_marlin_gemm",
    "per_token_quant_int8", "marlin_permute_scales", "marlin_permute_bias",
    "marlin_act_int8_process_scales", "marlin_make_workspace_new",
]


class WeightType(IntEnum):
    """The exact upstream ScalarType ID, obtained from its C++ definition."""
    uint4b8 = torch.ops._litos_marlin_int8.uint4b8_id()


def validate_metadata(
    weight_type: WeightType,
    group_size: int,
    input_dtype: torch.dtype,
    output_dtype: torch.dtype,
    *,
    has_zp: bool = False,
    act_order: bool = False,
    is_k_full: bool = True,
) -> None:
    """Load-time admission; metadata never implies a packed tensor's provenance."""
    if not isinstance(weight_type, WeightType) or weight_type != WeightType.uint4b8:
        raise ValueError("weight_type must be WeightType.uint4b8")
    if type(group_size) is not int or group_size != 128:
        raise ValueError("only symmetric group128 weights are supported")
    if input_dtype != torch.int8 or output_dtype not in (torch.float16, torch.bfloat16):
        raise ValueError("requires explicit int8 input and float16/bfloat16 output")
    if has_zp is not False or act_order is not False or is_k_full is not True:
        raise ValueError("requires has_zp=False, act_order=False, is_k_full=True")


def _nk(size_k: int, size_n: int) -> None:
    if type(size_k) is not int or size_k < 256 or size_k % 128:
        raise ValueError("K must be >=256 and divisible by 128")
    if type(size_n) is not int or size_n <= 0 or size_n % 64:
        raise ValueError("N must be positive and divisible by 64")
    if size_k * size_n > 2**31 - 1:
        raise ValueError("N*K exceeds upstream 32-bit indexing range")


def _scales_tensor(s: torch.Tensor) -> None:
    if s.dtype not in (torch.float16, torch.bfloat16) or s.ndim != 2 or not s.is_contiguous():
        raise ValueError("scales must be contiguous float16/bfloat16 rank-2 tensors")
    if s.device.type != "cuda" or torch.cuda.get_device_capability(s.device) != (8, 6):
        raise ValueError("scale preparation requires SM86 CUDA")
    if s.requires_grad:
        raise ValueError("scale preparation is inference-only")


# This is upstream's scale_perm_single, also used for group scales with A8.
_SCALE_PERM_SINGLE = tuple(2 * i + j for i in range(4) for j in (0, 1, 8, 9, 16, 17, 24, 25))


def marlin_permute_scales(
    s: torch.Tensor, size_k: int, size_n: int, group_size: int,
    is_a_8bit: bool = True,
) -> torch.Tensor:
    """One-time load operation on UNPACKED [K/128,N] scales; never W4A16 layout."""
    _nk(size_k, size_n)
    _scales_tensor(s)
    if type(group_size) is not int or group_size != 128 or is_a_8bit is not True:
        raise ValueError("requires group_size=128 and is_a_8bit=True")
    if s.shape != (size_k // 128, size_n):
        raise ValueError("s must have shape [K/128,N]")
    return s.reshape(-1, 32)[:, list(_SCALE_PERM_SINGLE)].reshape(-1, size_n).contiguous()


def marlin_permute_bias(s: torch.Tensor) -> torch.Tensor:
    """One-time load operation on the bias; pass the permuted result to GEMM."""
    if s.ndim != 1 or s.numel() <= 0 or s.numel() % 64:
        raise ValueError("bias must have positive shape [N], N divisible by 64")
    _scales_tensor(s.view(1, -1))
    return s.reshape(-1, 32)[:, list(_SCALE_PERM_SINGLE)].reshape(s.shape).contiguous()


def marlin_act_int8_process_scales(s: torch.Tensor) -> tuple[torch.Tensor, torch.Tensor]:
    """Pack permuted group scales as signed-int16 BITS in the original dtype.

    Returns (packed_scales, input_global_scale). Apply input_global_scale to the
    per-token FP32 activation scales before GEMM, NOT to its NVFP4 global_scale.
    Arithmetic and rounding match upstream, including the FP16/BF16 intermediate.
    This load-only validation synchronizes; it must not run during graph capture.
    """
    _scales_tensor(s)
    if s.numel() == 0 or s.shape[0] < 2 or s.shape[1] % 64:
        raise ValueError("scales must describe K>=256, group128, N divisible by 64")
    maximum = s.max()
    if not bool(torch.isfinite(s).all()) or bool(maximum == 0):
        raise ValueError("scales must be finite with nonzero maximum")
    a_scales_scale_factor = 1 / 4096 * maximum.float()
    rounded = (s / maximum * 4096).round()
    # Avoid undefined/out-of-range float-to-int conversion; do not silently
    # replace upstream s.max() with absmax or clamp negative scales.
    if not bool(torch.isfinite(rounded).all()) or not bool(
        ((rounded.float() >= -32768) & (rounded.float() <= 32767)).all()
    ):
        raise ValueError("upstream scale quantization exceeds signed-int16 range")
    return rounded.to(torch.int16).view(s.dtype), a_scales_scale_factor


def marlin_make_workspace_new(
    device: torch.device, max_blocks_per_sm: int = 1,
) -> torch.Tensor:
    """Allocate zeroed INT32 locks outside capture. One workspace per concurrent stream.

    Locks are reset by successful GEMM completion. Do not share across overlapping
    kernels/graphs, or reuse after an aborted/failed launch without zeroing safely.
    Keep this tensor alive and its address stable while any captured graph uses it.
    """
    device = torch.device(device)
    if device.type != "cuda" or torch.cuda.get_device_capability(device) != (8, 6):
        raise ValueError("workspace requires SM86 CUDA")
    if type(max_blocks_per_sm) is not int or max_blocks_per_sm < 1:
        raise ValueError("max_blocks_per_sm must be a positive integer")
    sms = torch.cuda.get_device_properties(device).multi_processor_count
    return torch.zeros(sms * max_blocks_per_sm, dtype=torch.int32, device=device)


def gptq_marlin_repack(
    b_q_weight: torch.Tensor, perm: torch.Tensor, size_k: int, size_n: int,
    num_bits: int = 4, is_a_8bit: bool = True,
) -> torch.Tensor:
    """GPTQ int32 [K/8,N] -> A8-Marlin int32 [K/16,2*N]; perm must be empty.

    Do not pass already-Marlin/W4A16 packed storage. Replace the original weight
    after repacking; this package never retains a second full-model weight copy.
    """
    _nk(size_k, size_n)
    if type(num_bits) is not int or num_bits != 4 or is_a_8bit is not True:
        raise ValueError("only num_bits=4 and is_a_8bit=True are supported")
    return torch.ops._litos_marlin_int8.gptq_marlin_repack(
        b_q_weight, perm, size_k, size_n, num_bits, is_a_8bit,
    )


def gptq_marlin_gemm(
    a: torch.Tensor,
    c: torch.Tensor | None,
    b_q_weight: torch.Tensor,
    b_bias: torch.Tensor | None,
    b_scales: torch.Tensor,
    a_scales: torch.Tensor,
    global_scale: torch.Tensor | None,
    b_zeros: torch.Tensor | None,
    g_idx: torch.Tensor | None,
    perm: torch.Tensor | None,
    workspace: torch.Tensor,
    b_type_id: int,
    size_m: int,
    size_n: int,
    size_k: int,
    is_k_full: bool = True,
    use_atomic_add: bool = False,
    use_fp32_reduce: bool = True,
    is_zp_float: bool = False,
) -> torch.Tensor:
    """Upstream argument order; A8 packed weights/scales required, no dtype fallback.

    a is [M,K] INT8; a_scales is [M] or [M,1] FP32 already multiplied by
    input_global_scale. global_scale must be None. zeros/g_idx/perm are None or
    empty INT32. The output dtype equals the packed b_scales carrier dtype.
    c=None allocates output; c supplied is mutated/returned. Upstream allocates
    FP32 reduction scratch (SMs*min(ceil(M/16)*16,64)*256 elements) per invocation
    when use_fp32_reduce=True. CUDA graph private pools own captured allocations;
    warm up first and keep all captured buffers/locks alive. The native schemas
    declare mutations; consumers must provide their own compile/fake boundary.
    Group-weighted accumulation is locally widened to signed int64 before the
    final FP32 conversion; unlike the pinned upstream int32 sum, it cannot wrap
    within this package's admitted indexing bounds. This precision/safety change
    and its register cost are experimental, not numerically or speed qualified.
    """
    if isinstance(b_type_id, bool) or not isinstance(b_type_id, int) or b_type_id != int(WeightType.uint4b8):
        raise ValueError("b_type_id must equal int(WeightType.uint4b8)")
    if any(type(flag) is not bool for flag in (is_k_full, use_atomic_add, use_fp32_reduce, is_zp_float)):
        raise ValueError("GEMM flags must be bool")
    if any(type(dim) is not int for dim in (size_m, size_n, size_k)):
        raise ValueError("M/N/K must be integers")
    return torch.ops._litos_marlin_int8.gptq_marlin_gemm(
        a, c, b_q_weight, b_bias, b_scales, a_scales, global_scale, b_zeros,
        g_idx, perm, workspace, b_type_id, size_m, size_n, size_k, is_k_full,
        use_atomic_add, use_fp32_reduce, is_zp_float,
    )
