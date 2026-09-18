"""
Bootstrap script for Bonsai PQ2_0 GGUF support in SGLang.

Patches the gguf library and SGLang's quantization module at runtime
to support the PQ2_0 (type 142) ternary quantization format used by
PrismML Bonsai 2 models.

Called from the entrypoint before launching the serving process.
Must run before any model loading occurs.
"""

import logging
import functools
import torch

logger = logging.getLogger(__name__)


def bootstrap_gguf_pq2():
    """Apply all patches needed for Bonsai PQ2_0 GGUF model loading."""
    _patch_gguf_library()
    _patch_sglang_gguf()
    logger.info("Bonsai PQ2_0 bootstrap complete")


def _patch_gguf_library():
    """Add PQ2_0 (type 142) as a recognized quantization type."""
    import gguf
    from gguf import GGMLQuantizationType

    if 142 not in GGMLQuantizationType._value2member_map_:
        # Map 142 to TQ2_0 (same 2-bit ternary packing, different block size)
        GGMLQuantizationType._value2member_map_[142] = GGMLQuantizationType.TQ2_0
        # PQ2_0: block_size=128, type_size=34 (2 bytes fp16 + 32 bytes qs)
        # Override the default TQ2_0 size (256, 66) for this type
        gguf.GGML_QUANT_SIZES[142] = (128, 34)
        logger.info("Added PQ2_0 (type 142) to gguf.GGMLQuantizationType")


def _patch_sglang_gguf():
    """Patch SGLang's GGUF quantization to handle PQ2_0."""
    from sglang.srt.layers.quantization import gguf as gguf_mod
    from gguf import GGMLQuantizationType as WT

    # Add TQ types to the dequant set
    gguf_mod.DEQUANT_TYPES.add(WT.TQ2_0)
    gguf_mod.DEQUANT_TYPES.add(WT.TQ1_0)
    gguf_mod.MMVQ_QUANT_TYPES.add(WT.TQ2_0)
    gguf_mod.MMQ_QUANT_TYPES.add(WT.TQ2_0)

    # Patch the fused_mul_mat_gguf function
    original_mul_mat = gguf_mod.fused_mul_mat_gguf

    @functools.wraps(original_mul_mat)
    def patched_mul_mat(x, qweight, qweight_type):
        if qweight_type in (WT.TQ2_0, WT.TQ1_0, 142):
            # Dequant to FP16 using torch
            weight = dequant_pq2_weight(qweight)
            # Move to correct device and dtype
            weight = weight.to(device=x.device, dtype=x.dtype)
            # Standard matmul
            return x @ weight.T
        return original_mul_mat(x, qweight, qweight_type)

    gguf_mod.fused_mul_mat_gguf = patched_mul_mat

    # Patch dequantize function
    original_dequant = gguf_mod.dequantize_gguf_weight

    @functools.wraps(original_dequant)
    def patched_dequant(qweight, qweight_type, dtype):
        if qweight_type in (WT.TQ2_0, WT.TQ1_0, 142):
            return dequant_pq2_weight(qweight).to(dtype)
        return original_dequant(qweight, qweight_type, dtype)

    gguf_mod.dequantize_gguf_weight = patched_dequant

    logger.info("Patched SGLang gguf module for PQ2_0")


def dequant_pq2_weight(packed: "torch.Tensor") -> "torch.Tensor":
    """
    Dequant a PQ2_0 (type 142) packed tensor to FP16.
    
    PQ2_0: 128 weights packed as 32 bytes of 2-bit ternary values + 2 bytes fp16 scale.
    Total 34 bytes per block.
    
    Shape handling: the packed weight may be a 1D byte array or shaped with some
    logical dimensions. We flatten to bytes, process blocks, then reshape.
    """

    import math

    # Flatten to 1D bytes
    flat = packed.contiguous().view(-1)
    total_bytes = flat.shape[0]
    
    block_size = 128
    block_bytes = 34
    
    n_blocks = total_bytes // block_bytes
    if n_blocks * block_bytes != total_bytes:
        raise ValueError(f"Packed data size {total_bytes} not divisible by block size {block_bytes}")
    
    # Reshape to blocks
    blocks = flat[:n_blocks * block_bytes].view(n_blocks, block_bytes)
    
    # First 32 bytes: packed 2-bit values
    qs = blocks[:, :32]  # (N, 32) uint8
    # Last 2 bytes: fp16 scale
    d_raw = blocks[:, 32:34]  # (N, 2) uint8
    
    # Convert fp16 to float32
    d = d_raw.view(torch.float16).to(torch.float32).view(-1, 1)  # (N, 1)
    
    # Decode 2-bit values (4 per byte)
    qs = qs.view(n_blocks, -1, 32)
    shifts = torch.tensor([0, 2, 4, 6], dtype=torch.uint8, device=packed.device).view(1, 1, 4, 1)
    qs_vals = (qs >> shifts) & 0x03
    qs_vals = qs_vals.view(n_blocks, block_size).to(torch.int8)
    
    # Ternary: 0 -> -1, 1 -> 0, 2 -> +1
    qs_vals = qs_vals - 1
    
    # Dequantize
    result = (d * qs_vals.to(torch.float32)).to(torch.float16)
    
    # Flatten to 1D
    result = result.view(-1)
    
    return result


if __name__ == '__main__':
    logging.basicConfig(level=logging.INFO)
    bootstrap_gguf_pq2()
    print("Bonsai bootstrap complete")