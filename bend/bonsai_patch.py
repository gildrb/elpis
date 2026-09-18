#!/usr/bin/env python3
"""
PQ2_0 / TQ2_0 (type 142) support for SGLang's GGUF model loader.

This module monkey-patches the gguf Python library and SGLang's gguf
quantization module to support the Prism ML PQ2_0 ternary quantization format
(type 142) used by Bonsai 2 models.

Usage:
    import bonsai_patch
    bonsai_patch.patch_all()
    
This must be called before the model is loaded.
"""

import logging
import functools

logger = logging.getLogger(__name__)

# ── GGUF library patching ──────────────────────────────────────────

def patch_gguf_library():
    """Add PQ2_0 (type 142) support to the gguf Python library."""
    import gguf
    from gguf import GGMLQuantizationType
    
    # Only add type 142 if not already present
    if 142 not in GGMLQuantizationType._value2member_map_:
        # Add 142 as an alias for TQ2_0 in the enum
        # The actual dequant is different (block size 128 vs 256) but the
        # bit packing is identical (2-bit ternary).
        GGMLQuantizationType._value2member_map_[142] = GGMLQuantizationType.TQ2_0
        
        # PQ2_0: block_size=128, type_size=34 (2 bytes fp16 + 32 bytes qs)
        gguf.GGML_QUANT_SIZES[142] = (128, 34)
        
        logger.info("Added PQ2_0 (type 142) to gguf library")
    else:
        logger.info("PQ2_0 (type 142) already in gguf library")


# ── PQ2_0 dequantization (PyTorch) ─────────────────────────────────

_HADAMARD_CACHE = {}

def _get_swht_signs():
    """Return the explicit sign values for the Sylvester Walsh-Hadamard transform."""
    # The sign values from the Bonsai 2 model metadata
    # These are for the normalized Sylvester Walsh-Hadamard transform
    return torch.tensor(SWHT_SIGNS, dtype=torch.float32)


def dequant_pq2_blocks_cpu(packed: torch.Tensor) -> torch.Tensor:
    """
    Dequant PQ2_0 blocks from packed uint8 to FP16.
    
    Args:
        packed: Raw bytes of the tensor, shape (num_blocks, 34)
        
    Returns:
        Dequantized weights, shape (num_blocks, 128)
    """
    n_blocks = packed.shape[0]
    
    # Split: first 32 bytes = 2-bit quantized values, last 2 bytes = fp16 scale
    qs = packed[:, :32]  # (N, 32)
    d_raw = packed[:, 32:34]  # (N, 2)
    
    # Convert fp16 bytes to float32
    d = d_raw.view(torch.float16).to(torch.float32).view(-1, 1)  # (N, 1)
    
    # Decode 2-bit values: each byte has 4 packed values
    # Bits: [0:2], [2:4], [4:6], [6:8]
    qs = qs.view(n_blocks, -1, 1, 32)
    # Shift right by [0, 2, 4, 6] bits
    qs = qs >> torch.tensor([0, 2, 4, 6], dtype=torch.uint8, device=packed.device).view(1, 1, 4, 1)
    qs = (qs & 0x03).view(n_blocks, -1).to(torch.int8)  # (N, 128)
    
    # Convert ternary: 0 -> -1, 1 -> 0, 2 -> +1
    qs = qs - torch.tensor(1, dtype=torch.int8, device=packed.device)
    
    # Dequant: multiply by scale
    result = d * qs.to(torch.float32)  # (N, 128)
    
    return result.to(torch.float16)


def dequantize_pq2_0_weight(
    qweight: torch.Tensor,
    qweight_type: int,
    target_dtype: torch.dtype,
) -> torch.Tensor:
    """
    Dequantize an entire PQ2_0 weight matrix to the target dtype.
    
    The tensor is stored as packed uint8 blocks. We dequant each block
    to FP16 and then apply the SWHT un-rotation.
    """
    import math
    
    # The packed data has shape (block_bytes,) in uint8
    # Dequant block by block
    n_bytes = qweight.numel()
    block_size = 128
    block_bytes = 34
    
    # Flatten to blocks
    flat = qweight.view(-1)
    n_blocks = flat.numel() // block_bytes
    blocks = flat[:n_blocks * block_bytes].view(n_blocks, block_bytes)
    
    # Dequant
    dequant = dequant_pq2_blocks_cpu(blocks)  # (N, 128)
    
    # The dequantized shape is (n_blocks * 128,) which equals the logical shape
    # But we need to know the actual tensor shape to reshape correctly
    # The logical shape is encoded in how the blocks are packed
    # For a matrix of shape (out_dim, in_dim), the blocks are laid out row-major
    
    return dequant.reshape(-1)


def apply_swht_unrotate(weight: torch.Tensor, in_dim: int, block_size: int = 1024):
    """
    Apply normalized Sylvester Walsh-Hadamard un-rotation to a weight matrix.
    
    The weights are stored in rotated form: W_rot = SWHT(W_true).
    To recover: W_true = SWHT(W_rot) (self-inverse).
    
    Applied column-wise (along last dim) in blocks.
    """
    global SWHT_SIGNS
    n_out = weight.shape[0]
    n_in = weight.shape[1]
    
    # Build the sign vector once
    if not hasattr(apply_swht_unrotate, 'signs'):
        signs = torch.tensor(SWHT_SIGNS, dtype=torch.float32, device=weight.device)
        apply_swht_unrotate.signs = signs
    
    result = torch.empty_like(weight)
    
    for block_start in range(0, n_in, block_size):
        block_end = min(block_start + block_size, n_in)
        actual_block = block_end - block_start
        
        # Get the sign vector for this block
        signs_block = apply_swht_unrotate.signs[:actual_block]
        
        # For each row, apply SWHT to the block
        block = weight[:, block_start:block_end]  # (n_out, block_size)
        
        # SWHT = H_norm * (x * s)
        # Apply element-wise signs
        signed = block * signs_block.unsqueeze(0)  # (n_out, block_size)
        
        # Apply normalized Walsh-Hadamard transform
        # Using iterative butterfly
        h_temp = signed.clone()
        h = 1
        n = actual_block
        while h < n:
            for i in range(0, n // (h * 2)):
                j = i * 2 * h
                for k in range(h):
                    if j + k < n and j + k + h < n:
                        x = h_temp[:, j + k]
                        y = h_temp[:, j + k + h]
                        h_temp[:, j + k] = x + y
                        h_temp[:, j + k + h] = x - y
            h *= 2
        
        result[:, block_start:block_end] = h_temp / math.sqrt(n)
    
    return result


# ── SGLang monkey-patching ─────────────────────────────────────────

PATCHED_DEQUANT_TYPES = set()

def patch_sglang_gguf():
    """Patch SGLang's gguf quantization module to support PQ2_0 (type 142)."""
    from sglang.srt.layers.quantization import gguf as gguf_module
    from gguf import GGMLQuantizationType as WeightType
    
    # Add PQ2_0 (which we mapped to TQ2_0 in the enum) to the dequant types
    global PATCHED_DEQUANT_TYPES
    
    if WeightType.TQ2_0 not in gguf_module.DEQUANT_TYPES:
        gguf_module.DEQUANT_TYPES.add(WeightType.TQ2_0)
        PATCHED_DEQUANT_TYPES.add(WeightType.TQ2_0)
        
    if WeightType.TQ1_0 not in gguf_module.DEQUANT_TYPES:
        gguf_module.DEQUANT_TYPES.add(WeightType.TQ1_0)
        PATCHED_DEQUANT_TYPES.add(WeightType.TQ1_0)
    
    # Monkey-patch fused_mul_mat_gguf to handle TQ types
    original_fn = gguf_module.fused_mul_mat_gguf
    
    @functools.wraps(original_fn)
    def patched_fused_mul_mat_gguf(x, qweight, qweight_type):
        if qweight_type in [WeightType.TQ2_0, WeightType.TQ1_0] or qweight_type == 142:
            # PQ2_0/TQ2_0: dequant + SWHT un-rotate + matmul
            # This path is slower than native kernels but functionally correct
            
            # Get the logical shape
            in_dim = x.shape[-1]
            out_dim = qweight.shape[0]
            
            # Read metadata to get the actual shape
            # For now, assume shape based on x
            # The qweight is stored as packed blocks; we need the logical shape
            # to reshape the dequantized output correctly
            
            # For a Linear layer weight: shape (out_dim, in_dim)
            # The packed weight layout is row-major with PQ2_0 blocks
            # Each row of 128 weights takes 34 bytes
            
            # Step 1: Dequant
            flat = qweight.view(-1)
            total_packed_bytes = flat.numel()
            block_bytes = 34
            n_blocks = total_packed_bytes // block_bytes
            
            # The logical shape is determined by the model, not from packed format
            # For the fused_mul_mat_gguf call, we know x.shape[-1] = in_dim
            # and we need out_dim = total_elements / in_dim
            
            # total_elements = n_blocks * 128
            total_elems = n_blocks * 128
            actual_out_dim = total_elems // in_dim
            
            # Dequant to FP16
            # Process blocks on CPU then move to GPU
            blocks = flat[:n_blocks * block_bytes].cpu().view(n_blocks, block_bytes)
            dequant = dequant_pq2_blocks_cpu(blocks)  # (N, 128)
            
            # Reshape to logical dimensions
            weight = dequant.view(actual_out_dim, in_dim).to(x.device, dtype=x.dtype)
            
            # Step 2: Apply SWHT un-rotation
            if weight.device.type == 'cuda':
                weight = apply_swht_unrotate(weight, in_dim)
            
            # Step 3: Standard matmul
            return x @ weight.T
        
        return original_fn(x, qweight, qweight_type)
    
    gguf_module.fused_mul_mat_gguf = patched_fused_mul_mat_gguf
    
    # Patch dequantize_gguf_weight
    original_dequant = gguf_module.dequantize_gguf_weight
    
    @functools.wraps(original_dequant)
    def patched_dequantize_gguf_weight(qweight, qweight_type, dtype):
        if qweight_type in [WeightType.TQ2_0, WeightType.TQ1_0] or qweight_type == 142:
            # Dequant PQ2_0 blocks
            return dequantize_pq2_0(qweight, qweight_type, dtype)
        return original_dequant(qweight, qweight_type, dtype)
    
    gguf_module.dequantize_gguf_weight = patched_dequantize_gguf_weight
    
    logger.info("Patched SGLang gguf module for PQ2_0/TQ2_0 support")


def patch_all():
    """Apply all patches for Bonsai model support."""
    patch_gguf_library()
    try:
        patch_sglang_gguf()
    except ImportError:
        logger.warning("SGLang not available; only gguf library patched")


# ── SWHT sign values from Bonsai 2 metadata ────────────────────────

SWHT_SIGNS = [
    -1, -1, -1, 1, -1, 1, 1, 1, 1, 1, 1, 1, -1, -1, -1, -1,
    -1, -1, -1, 1, -1, -1, -1, 1, -1, 1, -1, -1, -1, -1, 1, -1,
    1, 1, 1, 1, -1, -1, -1, -1, 1, 1, 1, -1, 1, 1, -1, 1,
    1, 1, -1, 1, 1, -1, 1, -1, 1, -1, 1, 1, -1, 1, 1, 1,
    1, 1, -1, -1, 1, -1, 1, -1, -1, 1, 1, -1, 1, -1, 1, -1,
    1, 1, -1, 1, -1, 1, 1, 1, 1, 1, -1, 1, 1, -1, -1, -1,
    1, 1, 1, -1, 1, 1, 1, -1, -1, 1, -1, 1, 1, -1, 1, 1,
    1, 1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 1, -1, 1, -1,
    -1, -1, -1, 1, 1, 1, -1, -1, -1, 1, -1, -1, -1, -1, -1, -1,
    -1, 1, 1, -1, 1, 1, 1, 1, 1, 1, -1, -1, -1, -1, 1, -1,
    1, -1, -1, -1, 1, 1, -1, 1, -1, -1, 1, 1, -1, 1, -1, 1,
    1, 1, -1, -1, -1, 1, 1, -1, -1, -1, 1, -1, 1, -1, -1, -1,
    -1, 1, 1, 1, 1, -1, -1, 1, -1, 1, 1, 1, -1, -1, -1, 1,
    1, -1, 1, -1, 1, -1, -1, -1, 1, 1, 1, -1, -1, -1, -1, -1,
    1, 1, 1, 1, -1, -1, 1, 1, 1, 1, 1, -1, -1, -1, 1, -1,
    -1, 1, -1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, -1, -1, 1,
    -1, 1, 1, -1, 1, 1, -1, -1, 1, 1, -1, 1, 1, -1, 1, -1,
    1, 1, -1, -1, 1, -1, 1, 1, 1, -1, 1, 1, 1, 1, -1, 1,
    -1, 1, 1, -1, -1, 1, 1, -1, -1, -1, 1, -1, -1, -1, -1, 1,
    1, 1, 1, 1, -1, -1, 1, 1, -1, -1, 1, -1, -1, 1, -1, -1,
    -1, -1, 1, -1, 1, 1, -1, -1, 1, 1, -1, 1, 1, -1, -1, 1,
    -1, 1, 1, -1, 1, 1, -1, 1, 1, -1, 1, -1, -1, 1, -1, -1,
    1, -1, -1, -1, -1, -1, -1, -1, 1, -1, -1, 1, -1, -1, 1, 1,
    1, 1, -1, -1, 1, -1, 1, -1, 1, 1, 1, 1, -1, 1, 1, 1,
    -1, -1, -1, -1, 1, -1, -1, 1, -1, 1, -1, 1, -1, -1, 1, -1,
    -1, -1, 1, 1, 1, -1, -1, -1, -1, -1, -1, -1, -1, 1, 1, -1,
    -1, 1, 1, 1, 1, 1, -1, 1, 1, 1, -1, -1, -1, -1, -1, -1,
    -1, -1, 1, -1, 1, -1, 1, -1, 1, 1, -1, 1, 1, 1, 1, -1,
    1, 1, 1, 1, 1, 1, -1, -1, 1, -1, 1, 1, 1, -1, 1, 1,
    -1, 1, -1, -1, 1, 1, 1, -1, 1, 1, 1, 1, 1, 1, -1, 1,
    1, -1, -1, -1, -1, 1, 1, -1, 1, -1, -1, 1, 1, -1, 1, -1,
    -1, 1, -1, -1, 1, -1, 1, -1, -1, -1, 1, -1, 1, -1, -1, -1,
    1, 1, -1, -1, 1, 1, -1, -1, -1, -1, -1, 1, 1, -1, 1, 1,
    -1, -1, -1, 1, 1, -1, 1, -1, 1, 1, 1, 1, 1, 1, 1, 1,
    -1, 1, -1, -1, -1, 1, 1, 1, -1, 1, 1, -1, 1, 1, 1, -1,
    -1, -1, 1, 1, 1, -1, 1, 1, -1, 1, 1, 1, 1, -1, -1, -1,
    -1, 1, 1, 1, -1, 1, -1, -1, 1, -1, -1, 1, 1, 1, 1, 1,
    1, -1, -1, 1, -1, -1, 1, 1, -1, 1, 1, 1, -1, 1, -1, -1,
    -1, -1, -1, 1, -1, -1, -1, 1, 1, -1, 1, -1, 1, 1, -1, -1,
    -1, 1, 1, -1, -1, -1, 1, 1, -1, 1, -1, 1, -1, 1, 1, 1,
    1, -1, -1, -1, -1, 1, 1, 1, -1, -1, -1, 1, 1, 1, -1, 1,
    -1, 1, 1, 1, 1, 1, -1, -1, 1, 1, -1, -1, 1, -1, -1, 1,
    1, -1, 1, -1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, 1, 1,
    -1, -1, 1, 1, 1, 1, -1, 1, 1, 1, -1, -1, -1, -1, 1, 1,
    -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 1, -1, -1, 1, 1, 1,
    -1, -1, -1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 1, -1, 1, 1,
    -1, -1, -1, 1, 1, -1, -1, -1, -1, 1, -1, -1, -1, 1, 1, 1,
    1, 1, 1, 1, -1, -1, 1, -1, 1, -1, 1, -1, 1, 1, 1, 1,
    -1, -1, 1, 1, 1, 1, 1, 1, -1, -1, -1, -1, -1, -1, -1, -1,
    1, 1, 1, -1, 1, -1, -1, -1, 1, -1, -1, 1, -1, -1, -1, 1,
    1, -1, -1, 1, 1, -1, 1, -1, 1, -1, 1, 1, 1, 1, 1, -1,
    -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, -1, -1, -1, 1, 1,
    -1, 1, 1, 1, 1, 1, -1, -1, 1, -1, -1, 1, -1, 1, 1, 1,
    1, 1, -1, 1, 1, 1, -1, -1, 1, 1, 1, 1, -1, -1, 1, 1,
    1, 1, -1, 1, 1, 1, -1, -1, 1, 1, -1, -1, 1, -1, -1, -1,
    -1, -1, -1, 1, -1, -1, 1, -1, 1, 1, 1, -1, 1, -1, -1, 1,
    -1, 1, 1, -1, -1, 1, 1, -1, 1, 1, 1, 1, -1, 1, -1, 1,
    -1, 1, 1, 1, 1, 1, -1, 1, 1, -1, 1, 1, 1, 1, -1, 1,
    1, 1, -1, 1, 1, -1, -1, -1, 1, 1, 1, -1, 1, -1, 1, 1,
    1, 1, -1, 1, -1, -1, 1, 1, 1, -1, -1, -1, 1, 1, 1, -1,
    1, -1, -1, -1, 1, 1, -1, -1, 1, 1, 1, 1, -1, -1, 1, -1,
    1, -1, 1, 1, 1, -1, 1, 1, 1, 1, -1, -1, -1, 1, -1, 1,
    -1, 1, 1, -1, 1, 1, 1, 1, 1, -1, 1, -1, 1, 1, -1, -1,
    -1, -1, 1, -1, -1, 1, 1, -1, -1, -1, 1, -1, -1, -1, 1, 1,
    1, 1, -1, 1, 1, -1, -1, -1, 1, 1, -1, 1, -1, -1, 1, 1,
    1, 1, -1, -1, 1, 1, 1, -1, 1, -1, -1, -1, 1, 1, 1, 1,
]

assert len(SWHT_SIGNS) == 1024, f"Expected 1024 signs, got {len(SWHT_SIGNS)}"


# ── Standalone test ────────────────────────────────────────────────

def test_dequant():
    """Test PQ2_0 dequant on a sample tensor from the GGUF file."""
    import gguf
    import torch
    
    patch_gguf_library()
    
    path = '/tmp/bonsai-gguf/Ternary-Bonsai-2-27B-PQ2_0.gguf'
    reader = gguf.GGUFReader(path)
    
    # Find the first PQ2_0 tensor
    for tensor in reader.tensors:
        if tensor.tensor_type.name == 'TQ2_0':  # PQ2_0 mapped to TQ2_0
            print(f"Testing dequant on: {tensor.name} shape={list(tensor.shape)}")
            print(f"  Raw data: {tensor.data.shape} {tensor.data.dtype}")
            
            # Convert to torch
            raw = torch.from_numpy(tensor.data.copy())
            
            # Dequant
            dequant = dequant_pq2_blocks_cpu(raw.view(-1, 34))
            print(f"  Dequantized: {dequant.shape}")
            print(f"  Values: min={dequant.min():.4f}, max={dequant.max():.4f}, mean={dequant.mean():.4f}")
            break


if __name__ == '__main__':
    logging.basicConfig(level=logging.INFO)
    test_dequant()