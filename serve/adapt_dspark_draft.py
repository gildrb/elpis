#!/usr/bin/env python3
"""
Adapt a DeepSpec DSpark draft model for Qwen3.8-27B vocabulary.

DeepSpec's DSpark drafts (deepseek-ai/dspark_qwen3_14b_block7) use
Qwen3's vocabulary (151,936 tokens). Qwen3.8-27B extends this to
248,320 tokens. This script adapts the draft by extending the
embedding/lm_head layers and setting a valid mask token.

Qwen3.8-27B vocab: first ~152K = Qwen3 base vocab, last ~96K = new
tokens and padding. The adapted draft will only propose tokens from
the shared base, which is sufficient for speculative decoding.
"""

import json
import logging
import sys
from pathlib import Path

import torch

logging.basicConfig(level=logging.INFO, format='%(asctime)s %(levelname)s %(message)s')
logger = logging.getLogger(__name__)

# Qwen3.8-27B target vocab size
TARGET_VOCAB_SIZE = 248320
# Qwen3 base vocab size  
QWEN3_VOCAB_SIZE = 151936

def adapt_dspark_draft(draft_path: str, output_path: str):
    """Adapt DSpark draft from Qwen3 vocab to Qwen3.8 vocab."""
    output_dir = Path(output_path)
    output_dir.mkdir(parents=True, exist_ok=True)
    
    logger.info(f"Loading DSpark draft from {draft_path}")
    
    # Load the draft model
    from transformers import AutoModelForCausalLM, AutoConfig, AutoTokenizer
    
    config = AutoConfig.from_pretrained(draft_path, trust_remote_code=True)
    logger.info(f"Original vocab_size: {config.vocab_size}")
    logger.info(f"Original hidden_size: {config.hidden_size}")
    
    # Save original DSpark-specific config
    dspark_config_attrs = {}
    for key in ['dspark_block_size', 'dspark_markov_rank', 'dspark_markov_head_type',
                'dspark_noise_token_id', 'dspark_target_layer_ids']:
        val = getattr(config, key, None)
        if val is not None:
            dspark_config_attrs[key] = val
            logger.info(f"  {key}: {val}")
    
    # Load model on CPU with meta device first to check architecture
    from transformers import AutoModelForCausalLM
    try:
        model = AutoModelForCausalLM.from_pretrained(
            draft_path, 
            torch_dtype=torch.float16,
            device_map='cpu',
            trust_remote_code=True
        )
    except Exception as e:
        logger.warning(f"Could not load full model: {e}")
        logger.info("Falling back to config-only adaptation...")
        model = None
    
    # Extend config
    logger.info(f"Extending vocab from {config.vocab_size} to {TARGET_VOCAB_SIZE}")
    old_vocab = config.vocab_size
    config.vocab_size = TARGET_VOCAB_SIZE
    
    # Set mask token ID to a valid value in the new vocab
    # Use BOS token (248044 for Qwen3.8) or EOS (248046)
    if 'dspark_noise_token_id' not in dspark_config_attrs:
        # For Qwen3.8, use a safe token ID
        config.dspark_noise_token_id = TARGET_VOCAB_SIZE - 1
        dspark_config_attrs['dspark_noise_token_id'] = TARGET_VOCAB_SIZE - 1
    
    target_layer_ids = dspark_config_attrs.get('dspark_target_layer_ids', None)
    if target_layer_ids:
        config.dspark_target_layer_ids = target_layer_ids
    
    # Save config
    config.save_pretrained(str(output_dir))
    logger.info(f"Saved extended config to {output_dir}")
    
    if model is not None:
        # Extend embedding layer
        embed = model.get_input_embeddings()
        if embed is not None:
            old_weight = embed.weight.data  # (old_vocab, hidden_size)
            new_weight = torch.zeros(TARGET_VOCAB_SIZE, old_weight.shape[1], dtype=old_weight.dtype)
            new_weight[:old_vocab] = old_weight
            embed.weight = torch.nn.Parameter(new_weight)
            embed.num_embeddings = TARGET_VOCAB_SIZE
            logger.info(f"Extended embeddings: {old_weight.shape} -> {new_weight.shape}")
        
        # Extend LM head
        if hasattr(model, 'lm_head') and model.lm_head is not None:
            lm = model.lm_head
            old_weight = lm.weight.data  # (old_vocab, hidden_size)
            new_weight = torch.zeros(TARGET_VOCAB_SIZE, old_weight.shape[1], dtype=old_weight.dtype)
            new_weight[:old_vocab] = old_weight
            lm.weight = torch.nn.Parameter(new_weight)
            if lm.bias is not None:
                old_bias = lm.bias.data
                new_bias = torch.zeros(TARGET_VOCAB_SIZE, dtype=old_bias.dtype)
                new_bias[:old_vocab] = old_bias
                lm.bias = torch.nn.Parameter(new_bias)
            logger.info(f"Extended LM head: {old_weight.shape} -> {new_weight.shape}")
        
        # Also extend any dense/linear output layers that reference vocab size
        for name, module in model.named_modules():
            if hasattr(module, 'out_features') and module.out_features == old_vocab:
                if module is not model.lm_head:  # Skip LM head already handled
                    old_w = module.weight.data
                    new_w = torch.zeros(TARGET_VOCAB_SIZE, old_w.shape[1], dtype=old_w.dtype)
                    new_w[:old_vocab] = old_w
                    module.weight = torch.nn.Parameter(new_w)
                    if module.bias is not None:
                        old_b = module.bias.data
                        new_b = torch.zeros(TARGET_VOCAB_SIZE, dtype=old_b.dtype)
                        new_b[:old_vocab] = old_b
                        module.bias = torch.nn.Parameter(new_b)
                    module.out_features = TARGET_VOCAB_SIZE
                    logger.info(f"Extended {name}: {old_w.shape} -> {new_w.shape}")
        
        # Save model weights
        logger.info(f"Saving adapted model to {output_dir}")
        model.save_pretrained(str(output_dir), safe_serialization=True)
    
    # Save tokenizer
    try:
        tokenizer = AutoTokenizer.from_pretrained(draft_path, trust_remote_code=True)
        tokenizer.save_pretrained(str(output_dir))
    except Exception:
        logger.warning("Could not save tokenizer")
    
    logger.info(f"DSpark draft adaptation complete!")
    logger.info(f"  Original vocab: {old_vocab}")
    logger.info(f"  Target vocab: {TARGET_VOCAB_SIZE}")
    logger.info(f"  DSpark config preserved: {dspark_config_attrs}")
    logger.info(f"\nTo use with SGLang:")
    logger.info(f"  --speculative-algorithm DSPARK")
    logger.info(f"  --speculative-draft-model-path {output_dir}")


def main():
    import argparse
    parser = argparse.ArgumentParser(description='Adapt DSpark draft for Qwen3.8 vocab')
    parser.add_argument('draft', help='Path to DSpark draft (HF model ID or local path)')
    parser.add_argument('output', help='Output path for adapted model')
    args = parser.parse_args()
    
    adapt_dspark_draft(args.draft, args.output)


if __name__ == '__main__':
    main()