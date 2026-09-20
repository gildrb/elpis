# SPDX-License-Identifier: Apache-2.0
# SPDX-FileCopyrightText: Copyright contributors to the vLLM project
# CUDA-only extraction from vLLM int8_utils.py at the source-manifest pin.
# Upstream adaptation: sgl-project/sglang at 4cb53ecd0cffceb6dee5c011a58f65997a86f151.
import torch
import triton
import triton.language as tl


@triton.jit
def round_int8(x):
    return tl.extra.cuda.libdevice.round(x).to(tl.int8)


@triton.jit
def _per_token_quant_int8(
    x_ptr,
    xq_ptr,
    scale_ptr,
    stride_x,
    stride_xq,
    N,
    BLOCK: tl.constexpr,
):
    # Adapted from https://github.com/InternLM/lmdeploy/blob/086481ed84b59bee3b8e4274e5fc69620040c048/lmdeploy/pytorch/kernels/cuda/w8a8_triton_kernels.py#L282
    row_id = tl.program_id(0)
    cols = tl.arange(0, BLOCK)
    mask = cols < N
    x = tl.load(x_ptr + row_id * stride_x + cols, mask=mask, other=0.0).to(tl.float32)
    absmax = tl.maximum(tl.max(tl.abs(x)), 1e-10)
    scale_x = absmax / 127
    x_q = x * (127 / absmax)
    x_q = round_int8(x_q)
    tl.store(xq_ptr + row_id * stride_xq + cols, x_q, mask=mask)
    tl.store(scale_ptr + row_id, scale_x)


def _tensor(t: torch.Tensor, dtype: torch.dtype, device: torch.device, name: str) -> None:
    if t.device != device or t.dtype != dtype or not t.is_contiguous():
        raise ValueError(f"{name} must be contiguous {dtype} on {device}")
    if t.requires_grad:
        raise ValueError(f"{name} is inference-only")
    if t.numel() and t.data_ptr() % 16:
        raise ValueError(f"{name} must be 16-byte aligned")


def per_token_quant_int8(
    x: torch.Tensor,
    *,
    out: torch.Tensor | None = None,
    scales: torch.Tensor | None = None,
) -> tuple[torch.Tensor, torch.Tensor]:
    """Upstream per-token quantization, with optional caller-owned capture buffers.

    Finite FP16/BF16 contiguous input, rank >=2. Round halfway away from zero,
    absmax floor 1e-10, symmetric /127. Returned scales do NOT yet include the
    weight's input_global_scale. Warm the Triton specialization before capture.
    """
    if x.device.type != "cuda" or torch.cuda.get_device_capability(x.device) != (8, 6):
        raise ValueError("per_token_quant_int8 requires SM86 CUDA")
    if x.dtype not in (torch.float16, torch.bfloat16) or x.ndim < 2:
        raise ValueError("x must have rank >=2 and dtype float16 or bfloat16")
    _tensor(x, x.dtype, x.device, "x")
    n = x.shape[-1]
    if n <= 0:
        raise ValueError("x's token width must be positive")
    m = x.numel() // n
    if out is None:
        out = torch.empty_like(x, dtype=torch.int8)
    if scales is None:
        scales = torch.empty(x.shape[:-1] + (1,), device=x.device, dtype=torch.float32)
    _tensor(out, torch.int8, x.device, "out")
    _tensor(scales, torch.float32, x.device, "scales")
    if out.shape != x.shape or scales.shape != x.shape[:-1] + (1,):
        raise ValueError("out must match x.shape; scales must have shape x.shape[:-1]+(1,)")
    # No writable buffer may alias an input or another writable buffer.
    for lhs, rhs in ((out, x), (scales, x), (out, scales)):
        if lhs.untyped_storage().data_ptr() == rhs.untyped_storage().data_ptr() and lhs.numel():
            raise ValueError("quantization buffers must use distinct storage")
    if m:
        block = triton.next_power_of_2(n)
        num_warps = min(max(block // 256, 1), 8)
        _per_token_quant_int8[(m,)](
            x, out, scales, stride_x=x.stride(-2), stride_xq=out.stride(-2),
            N=n, BLOCK=block, num_warps=num_warps, num_stages=1,
        )
    return out, scales
