#!/usr/bin/env python3
"""
Convert Ternary Bonsai 2 (PQ2_0 GGUF) to W4A16 compressed-tensors format.

Runs inside the Docker container with PyTorch + CUDA for fast GPU conversion.

Usage:
    python3 /opt/qwen/serve/convert-bonsai-to-w4a16.py \
        /models/Ternary-Bonsai-2-27B-PQ2_0.gguf \
        /models/bonsai-w4a16/

Output: safetensors + config.json + tokenizer files in output_dir,
ready to serve with SGLang's default model loader.
"""

import os
import sys
import json
import math
import struct
import logging
import shutil
from pathlib import Path
from typing import Optional

import numpy as np
import torch

logging.basicConfig(level=logging.INFO, format='%(asctime)s %(levelname)s %(message)s')
logger = logging.getLogger(__name__)


# ── GGUF raw reader (handles type 142 PQ2_0) ───────────────────────

GGUF_MAGIC = b'GGUF'

def read_gguf_header(path):
    """Read GGUF file header, tensor info, and metadata."""
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
            val = _read_gguf_value(f, val_type)
            metadata[key] = val
        
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


def _read_gguf_value(f, val_type):
    if val_type == 0: return struct.unpack('<B', f.read(1))[0]
    elif val_type == 1: return struct.unpack('<b', f.read(1))[0]
    elif val_type == 2: return struct.unpack('<H', f.read(2))[0]
    elif val_type == 3: return struct.unpack('<h', f.read(2))[0]
    elif val_type == 4: return struct.unpack('<I', f.read(4))[0]
    elif val_type == 5: return struct.unpack('<i', f.read(4))[0]
    elif val_type == 6: return struct.unpack('<f', f.read(4))[0]
    elif val_type == 7: return bool(struct.unpack('<?', f.read(1))[0])
    elif val_type == 8:
        s_len = struct.unpack('<Q', f.read(8))[0]
        return f.read(s_len).decode('utf-8')
    elif val_type == 9:
        arr_type = struct.unpack('<I', f.read(4))[0]
        arr_len = struct.unpack('<Q', f.read(8))[0]
        return [_read_gguf_value(f, arr_type) for _ in range(arr_len)]
    elif val_type == 10: return struct.unpack('<Q', f.read(8))[0]
    elif val_type == 11: return struct.unpack('<q', f.read(8))[0]
    elif val_type == 12: return struct.unpack('<d', f.read(8))[0]
    elif val_type == 13:
        data = f.read(2)
        return struct.unpack('<f', data + b'\x00\x00')[0]
    else:
        raise ValueError(f"Unknown value type: {val_type}")


# ── PQ2_0 dequant (GPU via PyTorch) ────────────────────────────────

def dequant_pq2_gpu(packed: torch.Tensor) -> torch.Tensor:
    """
    Dequant PQ2_0 (type 142) packed blocks to FP16 on GPU.
    
    PQ2_0 block: 128 weights = 32 bytes qs (2-bit packed) + 2 bytes fp16 scale = 34 bytes
    """
    n_blocks = packed.shape[0]
    n_weights = n_blocks * 128
    
    # Extract quantized values (32 bytes) and scale (last 2 bytes)
    qs = packed[:, :32].contiguous()          # (N, 32) uint8
    d_raw = packed[:, 32:34].contiguous()     # (N, 2) uint8
    
    # Convert fp16 bytes to float32
    d = d_raw.view(torch.float16).to(torch.float32).view(-1, 1)  # (N, 1)
    
    # Decode 2-bit ternary values from packed bytes
    # Each byte has 4 vals at positions [0:2], [2:4], [4:6], [6:8]
    qs = qs.view(n_blocks, -1, 1, 32)
    shifts = torch.tensor([0, 2, 4, 6], dtype=torch.uint8, device=packed.device).view(1, 1, 4, 1)
    qs = (qs >> shifts) & 0x03
    qs = qs.view(n_blocks, n_weights // n_blocks).to(torch.int8)  # (N, 128)
    
    # Convert packed ternary (0→-1, 1→0, 2→+1)
    qs = qs - 1
    
    # Dequant: multiply by scale, promote to FP16
    result = (d * qs.to(torch.float32)).to(torch.float16)
    
    return result.view(-1)


# ── Hadamard un-rotation (GPU) ─────────────────────────────────────

_SWHT_SIGNS: Optional[torch.Tensor] = None

def _get_signs():
    """Load the SWHT sign values from the extracted metadata."""
    global _SWHT_SIGNS
    if _SWHT_SIGNS is not None:
        return _SWHT_SIGNS
    
    # The sign values from Bonsai 2 model metadata (prism.hadamard.sign_values)
    # This is a fixed ±1 pattern for the normalized Sylvester Walsh-Hadamard transform
    signs = [
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
    _SWHT_SIGNS = torch.tensor(signs, dtype=torch.float32)
    return _SWHT_SIGNS


def swht_butterfly(x: torch.Tensor, dim: int = -1, signs: torch.Tensor = None) -> torch.Tensor:
    """
    Apply normalized Sylvester Walsh-Hadamard transform along given dimension.
    
    The transform is: SWHT(x) = H_norm * (x * signs)
    where H_norm is the normalized Hadamard matrix (H/sqrt(n)).
    
    Applied butterfly-style in O(n log n).
    """
    if signs is not None:
        x = x * signs.view([-1 if i == dim % x.ndim else 1 for i in range(x.ndim)])
    
    n = x.shape[dim]
    h = 1
    while h < n:
        # Split along dim, compute butterfly
        step = h
        x1 = x.narrow(dim, 0, n // 2).clone()
        x2 = x.narrow(dim, n // 2, n // 2).clone()
        
        # Apply butterfly
        x1_part = x1.chunk(2, dim=dim)
        x2_part = x2.chunk(2, dim=dim)
        
        # This needs to be done more carefully for arbitrary dimensions
        # For simplicity, reshape to 2D and apply
        orig_shape = x.shape
        x_2d = x.reshape(-1, n)
        
        h_temp = x_2d.clone()
        step2 = 1
        while step2 < n:
            for i in range(0, n, step2 * 2):
                j_end = min(i + step2, n)
                if i + step2 < n:
                    a = h_temp[:, i:i+step2].clone()
                    b = h_temp[:, i+step2:j_end].clone()
                    h_temp[:, i:i+step2] = a + b
                    h_temp[:, i+step2:j_end] = a - b
                else:
                    # Odd tail - copy as-is
                    pass
            step2 *= 2
        
        x_2d = h_temp / math.sqrt(n)
        x = x_2d.reshape(orig_shape)
        break  # Already did full transform
    
    return x


def apply_swht_unrotate_weight(weight: torch.Tensor, in_dim: int, block_size: int = 1024):
    """
    Un-rotate weight matrix stored with SWHT along last dimension.
    
    W_rotated = SWHT(W_true) along axis=1 (input dimension).
    W_true = SWHT(W_rotated) (self-inverse).
    """
    signs = _get_signs()
    out_dim, n_in = weight.shape
    
    result = torch.empty_like(weight)
    
    for start in range(0, n_in, block_size):
        end = min(start + block_size, n_in)
        block = weight[:, start:end]  # (out_dim, block_size)
        
        # Apply SWHT: element-wise sign then butterfly
        block_signs = signs[:end-start]
        signed = block * block_signs.unsqueeze(0)
        
        # Walsh-Hadamard butterfly
        n = block.shape[1]
        h_temp = signed.clone()
        step = 1
        while step < n:
            stride = step * 2
            for i in range(0, n, stride):
                j_end = min(i + step, n)
                if i + step < n:
                    a = h_temp[:, i:i+step].clone()
                    b = h_temp[:, i+step:i+stride].clone()
                    h_temp[:, i:i+step] = a + b
                    h_temp[:, i+step:i+stride] = a - b
            step *= 2
        
        h_temp = h_temp / math.sqrt(n)
        result[:, start:end] = h_temp
    
    return result


# ── Compression-tensors W4A16 helper ───────────────────────────────

def quantize_w4a16(weight: torch.Tensor, group_size: int = 128) -> dict:
    """
    Quantize a weight tensor to W4A16 (4-bit weights, FP16 scales).
    
    Returns dict with 'qweight' (packed int4, shape [out, in//2]),
    'scales' (fp16, shape [out, in//group_size]).
    """
    out_dim, in_dim = weight.shape
    
    # Reshape for group quantization
    w_reshaped = weight.view(out_dim, -1, group_size)  # (out, n_groups, group_size)
    
    # Find min/max per group for symmetric quantization
    w_max = w_reshaped.abs().amax(dim=-1)  # (out, n_groups)
    
    # 4-bit symmetric: scale = max / 7.0 (since int4 range is [-8, 7])
    # We use symmetric quantization to match the W4A16 format
    scales = w_max / 7.0  # (out, n_groups)
    scales = scales.to(torch.float16)
    scales = scales.clamp(min=1e-10)  # Avoid division by zero
    
    # Quantize
    q = w_reshaped / scales.unsqueeze(-1)
    q = q.round().to(torch.int8).clamp(-8, 7)
    
    # Pack as uint4: two int4 per byte
    q = q.view(out_dim, -1, 2)  # Pair up adjacent values
    # Shift second value to high nibble
    packed = (q[:, :, 0].to(torch.uint8) & 0x0F) | ((q[:, :, 1].to(torch.uint8) & 0x0F) << 4)
    packed = packed.reshape(out_dim, -1)
    
    return {
        'qweight': packed,
        'scales': scales,
        'qweight_type': torch.tensor(0, dtype=torch.int32),  # W4A16 type marker
    }


# ── Main conversion ────────────────────────────────────────────────

def convert_model(gguf_path: str, output_dir: str, device: str = 'cuda'):
    """Convert Bonsai GGUF to W4A16 format."""
    device = torch.device(device)
    output_dir = Path(output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)
    
    logger.info(f"Reading GGUF: {gguf_path}")
    version, tensor_count, metadata, tensor_infos, data_start = read_gguf_header(gguf_path)
    
    architecture = metadata.get('general.architecture', 'qwen35')
    logger.info(f"Architecture: {architecture}, {tensor_count} tensors")
    
    # Categorize tensors
    pq2_0_infos = [(n, s, o) for n, s, g, o in tensor_infos if g == 142]
    f32_infos = [(n, s, o) for n, s, g, o in tensor_infos if g == 0]
    bf16_infos = [(n, s, o) for n, s, g, o in tensor_infos if g == 30]
    
    logger.info(f"PQ2_0: {len(pq2_0_infos)}, F32: {len(f32_infos)}, BF16: {len(bf16_infos)}")
    
    # Build HuggingFace config from local reference
    import json
    from transformers import AutoConfig
    
    ref_config_path = "/models/compact-target-rholsc8k/artifact/config.json"
    with open(ref_config_path) as f:
        config_dict = json.load(f)
    config = AutoConfig.from_dict(config_dict)
    
    # Convert tensor name from GGUF to HF format
    # GGUF names: blk.N.attn_qkv.weight, blk.N.ffn_gate.weight, etc.
    # HF names: model.layers.N.self_attn.qkv_proj.weight, etc.
    def gguf_to_hf_name(name: str) -> str:
        """Map GGUF qwen35 tensor name to HuggingFace name."""
        # Common mappings
        mapping = {
            'token_embd.weight': 'model.embed_tokens.weight',
            'output.weight': 'lm_head.weight',
            'output_norm.weight': 'model.norm.weight',
        }
        if name in mapping:
            return mapping[name]
        
        # Layer names: blk.N.NAME.weight
        if name.startswith('blk.'):
            parts = name.split('.')
            layer_id = int(parts[1])
            tensor_name = parts[2]
            suffix = parts[3] if len(parts) > 3 else 'weight'
            
            prefix = f'model.layers.{layer_id}.'
            
            sub_mapping = {
                'attn_norm': 'input_layernorm',
                'post_attention_norm': 'post_attention_layernorm',
                'ssm_norm': 'ssm.layernorm',
                'attn_qkv': 'self_attn.qkv_proj',
                'attn_q': 'self_attn.q_proj',
                'attn_k': 'self_attn.k_proj',
                'attn_v': 'self_attn.v_proj',
                'attn_output': 'self_attn.o_proj',
                'attn_gate': 'self_attn.gate_proj',
                'ffn_gate': 'mlp.gate_proj',
                'ffn_up': 'mlp.up_proj',
                'ffn_down': 'mlp.down_proj',
                'ssm_conv1d': 'ssm.conv1d',
                'ssm_dt': 'ssm.dt',
                'ssm_a': 'ssm.a',
                'ssm_alpha': 'ssm.alpha',
                'ssm_beta': 'ssm.beta',
                'ssm_out': 'ssm.out_proj',
                'attn_k_norm': 'self_attn.k_norm',
                'attn_q_norm': 'self_attn.q_norm',
            }
            
            if tensor_name in sub_mapping:
                return prefix + sub_mapping[tensor_name] + '.' + suffix
        
        return name  # Fallback
    
    # Read and process tensors
    safetensors_metadata = {}
    tensor_files = []
    tensors_per_file = 100  # Max tensors per safetensors file
    file_idx = 0
    tensor_count_in_file = 0
    current_file_data = {}
    
    def flush_file():
        nonlocal file_idx, tensor_count_in_file, current_file_data
        if not current_file_data:
            return
        
        from safetensors.torch import save_file as sf_save
        fname = f'model-{file_idx:05d}-of-{len(tensor_infos) // tensors_per_file + 1:05d}.safetensors'
        fpath = output_dir / fname
        sf_save(current_file_data, str(fpath))
        logger.info(f"  Saved {fpath.name} with {len(current_file_data)} tensors")
        
        for key in current_file_data:
            safetensors_metadata[key] = {'dtype': 'bfloat16', 'shape': list(current_file_data[key].shape)}
        
        file_idx += 1
        tensor_count_in_file = 0
        current_file_data = {}
    
    logger.info("Processing F32 tensors...")
    # Process F32 tensors first (simple copy)
    for info in f32_infos:
        name, shape, offset = info
        hf_name = gguf_to_hf_name(name)
        
        with open(gguf_path, 'rb') as f:
            f.seek(offset)
            n_bytes = int(np.prod(shape)) * 4  # F32 = 4 bytes per element
            data = np.frombuffer(f.read(n_bytes), dtype=np.float32).reshape(shape).copy()
        
        tensor = torch.from_numpy(data).bfloat16()
        current_file_data[hf_name] = tensor.contiguous()
        tensor_count_in_file += 1
        
        if tensor_count_in_file >= tensors_per_file:
            flush_file()
    
    flush_file()
    
    logger.info("Processing BF16 tensors...")
    # Process BF16 tensors
    for info in bf16_infos:
        name, shape, offset = info
        hf_name = gguf_to_hf_name(name)
        
        with open(gguf_path, 'rb') as f:
            f.seek(offset)
            n_bytes = int(np.prod(shape)) * 2  # BF16 = 2 bytes per element
            # Read as uint16 then convert to BF16
            raw = np.frombuffer(f.read(n_bytes), dtype=np.uint16).reshape(shape).copy()
        
        # Convert uint16 bits to bfloat16
        import ctypes
        tensor = torch.tensor(raw.view(np.int16).copy(), dtype=torch.bfloat16)
        current_file_data[hf_name] = tensor.contiguous()
        tensor_count_in_file += 1
        
        if tensor_count_in_file >= tensors_per_file:
            flush_file()
    
    flush_file()
    
    logger.info("Processing PQ2_0 tensors (dequant + un-rotate + W4A16)...")
    # Process PQ2_0 tensors
    pq2_tensors = [(name, shape, offset) for name, shape, ggml_type, offset in tensor_infos if ggml_type == 142]
    
    # Check if inverse_weight_names need special handling
    inverse_weight_names = set(metadata.get('prism.hadamard.inverse_weight_names', []))
    rotated_weight_names = set(metadata.get('prism.hadamard.weight_names', []))
    
    rotated_hf_names = set()
    for name, _, _ in pq2_tensors:
        hf_name = gguf_to_hf_name(name)
        if name in rotated_weight_names:
            rotated_hf_names.add(hf_name)
    
    for idx, (name, shape, offset) in enumerate(pq2_tensors):
        hf_name = gguf_to_hf_name(name)
        logger.info(f"  [{idx+1}/{len(pq2_tensors)}] {name} -> {hf_name} {shape}")
        
        with open(gguf_path, 'rb') as f:
            f.seek(offset)
            # Read raw PQ2_0 blocks
            # Shape is the logical shape, but data is PQ2_0 packed
            n_logical_elements = int(np.prod(shape))
            n_blocks = (n_logical_elements + 127) // 128
            n_bytes = n_blocks * 34  # 34 bytes per PQ2_0 block
            raw = np.frombuffer(f.read(n_bytes), dtype=np.uint8).copy()
        
        # Dequant on GPU
        packed = torch.from_numpy(raw).to(device)
        dequant_fp16 = dequant_pq2_gpu(packed.view(-1, 34))
        
        # Reshape to logical dimensions
        actual_elements = dequant_fp16.numel()
        n_out = shape[0]
        n_in = actual_elements // n_out
        weight = dequant_fp16.view(n_out, n_in)
        
        # Apply SWHT un-rotation if this tensor is rotated
        if name in rotated_weight_names or True:  # All PQ2_0 tensors are rotated
            weight = apply_swht_unrotate_weight(weight, n_in)
        
        # Quantize to W4A16
        quantized = quantize_w4a16(weight.to(torch.float32))
        
        current_file_data[f'{hf_name}.qweight'] = quantized['qweight'].contiguous()
        current_file_data[f'{hf_name}.scales'] = quantized['scales'].contiguous()
        current_file_data[f'{hf_name}.qweight_type'] = quantized['qweight_type']
        
        # Also store the original weight type info
        current_file_data[f'{hf_name}.weight'] = weight.bfloat16().contiguous()
        
        tensor_count_in_file += 1
        if tensor_count_in_file >= tensors_per_file:
            flush_file()
        
        # Clear GPU cache periodically
        if idx % 10 == 9:
            torch.cuda.empty_cache()
    
    flush_file()
    
    # Save config
    logger.info("Saving model config...")
    config.save_pretrained(str(output_dir))
    
    # Save tokenizer files (copy from original Qwen)
    logger.info("Copying tokenizer files...")
    try:
        from transformers import AutoTokenizer
        tokenizer = AutoTokenizer.from_pretrained("Qwen/Qwen3.8-27B", trust_remote_code=True)
        tokenizer.save_pretrained(str(output_dir))
    except Exception as e:
        logger.warning(f"Could not save tokenizer: {e}")
        # Copy from existing model if available
        for tokenizer_file in ['tokenizer.json', 'tokenizer_config.json', 'vocab.json', 'merges.txt', 'added_tokens.json']:
            src = Path('/models/Qwen3.8-27B') / tokenizer_file
            if src.exists():
                shutil.copy2(src, output_dir / tokenizer_file)
    
    logger.info(f"Conversion complete. Model saved to {output_dir}")
    logger.info(f"Use SGLang with: --model-path {output_dir}")


def main():
    import argparse
    parser = argparse.ArgumentParser(description='Convert Bonsai GGUF to W4A16')
    parser.add_argument('gguf', help='Path to PQ2_0 GGUF file')
    parser.add_argument('output', help='Output directory')
    parser.add_argument('--device', default='cuda', choices=['cuda', 'cpu'])
    args = parser.parse_args()
    
    convert_model(args.gguf, args.output, args.device)


if __name__ == '__main__':
    main()