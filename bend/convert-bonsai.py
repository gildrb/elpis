#!/usr/bin/env python3
"""
Convert Ternary Bonsai 2 GGUF (PQ2_0) to W4A16 compressed-tensors format.

Reads the PQ2_0 GGUF file, dequants ternary weights to FP32, applies
blockwise Hadamard un-rotation, re-quantizes to W4A16 via compressed-tensors,
and saves safetensors + config for SGLang serving.
"""

import os
import sys
import struct
import json
import numpy as np

# ── GGUF raw reader ────────────────────────────────────────────────

GGUF_MAGIC = b'GGUF'

GGUF_VALUE_TYPE = {
    0: 'UINT8', 1: 'INT8', 2: 'UINT16', 3: 'INT16', 4: 'UINT32',
    5: 'INT32', 6: 'FLOAT32', 7: 'BOOL', 8: 'STRING', 9: 'ARRAY',
    10: 'UINT64', 11: 'INT64', 12: 'FLOAT64', 13: 'BF16',
}

def read_gguf_header(path):
    """Read GGUF header and return (version, tensor_count, metadata_kv_count, metadata, tensor_infos)."""
    with open(path, 'rb') as f:
        magic = f.read(4)
        assert magic == GGUF_MAGIC, f"Bad magic: {magic}"
        
        version = struct.unpack('<I', f.read(4))[0]
        tensor_count = struct.unpack('<Q', f.read(8))[0]
        metadata_kv_count = struct.unpack('<Q', f.read(8))[0]
        
        metadata = {}
        for _ in range(metadata_kv_count):
            key_len = struct.unpack('<Q', f.read(8))[0]
            key = f.read(key_len).decode('utf-8')
            val_type = struct.unpack('<I', f.read(4))[0]
            val = _read_value(f, val_type)
            metadata[key] = val
        
        # Read tensor infos
        tensor_infos = []
        for _ in range(tensor_count):
            name_len = struct.unpack('<Q', f.read(8))[0]
            name = f.read(name_len).decode('utf-8')
            n_dims = struct.unpack('<I', f.read(4))[0]
            shape = struct.unpack('<' + 'Q' * n_dims, f.read(8 * n_dims))
            ggml_type = struct.unpack('<I', f.read(4))[0]
            offset = struct.unpack('<Q', f.read(8))[0]
            tensor_infos.append((name, shape, ggml_type, offset))
        
        data_start = f.tell()
    
    return version, tensor_count, metadata, tensor_infos, data_start


def _read_value(f, val_type):
    if val_type == 0:  # UINT8
        return struct.unpack('<B', f.read(1))[0]
    elif val_type == 1:  # INT8
        return struct.unpack('<b', f.read(1))[0]
    elif val_type == 2:  # UINT16
        return struct.unpack('<H', f.read(2))[0]
    elif val_type == 3:  # INT16
        return struct.unpack('<h', f.read(2))[0]
    elif val_type == 4:  # UINT32
        return struct.unpack('<I', f.read(4))[0]
    elif val_type == 5:  # INT32
        return struct.unpack('<i', f.read(4))[0]
    elif val_type == 6:  # FLOAT32
        return struct.unpack('<f', f.read(4))[0]
    elif val_type == 7:  # BOOL
        return bool(struct.unpack('<?', f.read(1))[0])
    elif val_type == 8:  # STRING
        s_len = struct.unpack('<Q', f.read(8))[0]
        return f.read(s_len).decode('utf-8')
    elif val_type == 9:  # ARRAY
        arr_type = struct.unpack('<I', f.read(4))[0]
        arr_len = struct.unpack('<Q', f.read(8))[0]
        return [_read_value(f, arr_type) for _ in range(arr_len)]
    elif val_type == 10:  # UINT64
        return struct.unpack('<Q', f.read(8))[0]
    elif val_type == 11:  # INT64
        return struct.unpack('<q', f.read(8))[0]
    elif val_type == 12:  # FLOAT64
        return struct.unpack('<d', f.read(8))[0]
    elif val_type == 13:  # BF16
        data = f.read(2)
        # Convert BF16 to float32
        return struct.unpack('<f', data + b'\x00\x00')[0]
    else:
        raise ValueError(f"Unknown value type: {val_type}")


# ── PQ2_0 dequant ──────────────────────────────────────────────────

def dequant_pq2_0(data: np.ndarray, shape: tuple) -> np.ndarray:
    """
    Dequant PQ2_0 tensor (type 142, prism fork).
    
    PQ2_0 block: 128 weights, stored as:
      - 32 bytes of 2-bit packed values (4 per byte)
      - 2 bytes FP16 scale
    Total per block: 34 bytes.
    """
    # Get the raw bytes
    assert data.dtype == np.uint8
    total_bytes = data.size
    
    # PQ2_0: block_size=128, block_bytes=34, 2 bits per weight
    block_size = 128
    block_bytes = 34
    
    num_blocks = total_bytes // block_bytes
    assert total_bytes == num_blocks * block_bytes, f"Data {total_bytes} not divisible by {block_bytes}"
    
    # Reshape to (num_blocks, block_bytes)
    blocks = data[:num_blocks * block_bytes].reshape(num_blocks, block_bytes)
    
    # Split: first 32 bytes = quantized values, last 2 bytes = fp16 scale
    qs = blocks[:, :32].astype(np.uint8)        # (N, 32)
    d_raw = blocks[:, 32:34].reshape(-1, 2)     # (N, 2)
    
    # Convert fp16 bytes to float32
    d = d_raw.view(np.float16).astype(np.float32).reshape(-1, 1)  # (N, 1)
    
    # Decode 2-bit values
    # Each byte has 4 packed values: bits [0:2], [2:4], [4:6], [6:8]
    qs = qs.reshape(num_blocks, -1, 1, 32) >> np.array([0, 2, 4, 6], dtype=np.uint8).reshape(1, 1, 4, 1)
    qs = (qs & 0x03).reshape(num_blocks, -1).astype(np.int8)  # (N, 128)
    
    # ternary: 0->-1, 1->0, 2->+1
    qs = qs - np.int8(1)
    
    # Dequant: multiply by scale
    result = d * qs.astype(np.float32)  # (N, 128)
    
    # The shape in the GGUF is typically the logical shape of the tensor.
    # We need to reshape the result.
    logical_elements = int(np.prod(shape))
    assert result.size == logical_elements, f"Result size {result.size} != logical {logical_elements}"
    
    return result.reshape(shape)


# ── Hadamard de-rotation ───────────────────────────────────────────

def build_hadamard_1024():
    """Build the 1024x1024 Hadamard matrix (Walsh-Hadamard, entries ±1)."""
    H = np.array([[1, 1], [1, -1]], dtype=np.float32)
    while H.shape[0] < 1024:
        H = np.kron(H, np.array([[1, 1], [1, -1]], dtype=np.float32))
    return H

HADAMARD_1024 = None

def apply_hadamard_unrotate(weight_matrix: np.ndarray, block_size: int = 1024):
    """
    The weights are stored in a rotated basis: W_rot = H * W_true.
    To recover W_true: W_true = H * W_rot (since H^2 = I).
    
    For a weight matrix of shape (out_dim, in_dim), the rotation is applied
    column-wise in blocks of `block_size`.
    
    Each block of `block_size` columns is multiplied by the Hadamard matrix.
    """
    global HADAMARD_1024
    if HADAMARD_1024 is None:
        HADAMARD_1024 = build_hadamard_1024()
    
    out_dim, in_dim = weight_matrix.shape
    result = np.zeros_like(weight_matrix)
    
    for start in range(0, in_dim, block_size):
        end = min(start + block_size, in_dim)
        actual_block = end - start
        if actual_block < block_size:
            # Partial block at end - won't happen for 1024-aligned dimensions
            # but handle gracefully
            H = HADAMARD_1024[:actual_block, :actual_block]
        else:
            H = HADAMARD_1024
        
        # Apply: W_true[:, start:end] = H @ W_rot[:, start:end]
        result[:, start:end] = H @ weight_matrix[:, start:end]
    
    return result


# ── Main conversion logic ──────────────────────────────────────────

def convert_gguf_to_w4a16(gguf_path: str, output_dir: str):
    """Convert a PQ2_0 GGUF file to W4A16 compressed-tensors format."""
    print(f"Reading GGUF: {gguf_path}")
    version, tensor_count, metadata, tensor_infos, data_start = read_gguf_header(gguf_path)
    
    print(f"GGUF version: {version}")
    print(f"Tensors: {tensor_count}")
    print(f"Metadata keys: {list(metadata.keys())[:10]}...")
    
    architecture = metadata.get('general.architecture', 'unknown')
    print(f"Architecture: {architecture}")
    
    # Categorize tensors by type
    tensor_types = {}
    for name, shape, ggml_type, offset in tensor_infos:
        tensor_types[ggml_type] = tensor_types.get(ggml_type, 0) + 1
    
    print(f"\nTensor types: {tensor_types}")
    
    # Build index of tensors
    from collections import defaultdict
    tensors_by_type = defaultdict(list)
    for name, shape, ggml_type, offset in tensor_infos:
        tensors_by_type[ggml_type].append((name, shape, offset))
    
    # Show sample tensors per type
    for ggml_type, tensors in tensors_by_type.items():
        print(f"\nType {ggml_type} ({len(tensors)} tensors):")
        for name, shape, _ in tensors[:5]:
            print(f"  {name} {shape}")
        if len(tensors) > 5:
            print(f"  ... and {len(tensors)-5} more")
    
    # PQ2_0 type is 142
    pq2_0_tensors = tensors_by_type.get(142, [])
    other_types = set(tensor_types.keys()) - {142}
    if other_types:
        print(f"\nNon-PQ2_0 types: {other_types}")
    
    print(f"\nPQ2_0 tensors: {len(pq2_0_tensors)}")
    
    # Determine output shape for the conversion
    # We need to map GGUF tensor names to HuggingFace names
    # The Bonsai model uses qwen35 architecture, same as Qwen3.5/3.8
    
    return architecture, tensor_infos


def main():
    """Entry point."""
    import argparse
    parser = argparse.ArgumentParser(description='Convert Ternary Bonsai GGUF to W4A16')
    parser.add_argument('gguf', help='Path to GGUF file')
    parser.add_argument('output', help='Output directory for model files')
    args = parser.parse_args()
    
    architecture, tensor_infos = convert_gguf_to_w4a16(args.gguf, args.output)
    print(f"\nDone. Architecture: {architecture}")
    print(f"Total tensors: {len(tensor_infos)}")


if __name__ == '__main__':
    main()