#!/usr/bin/env python3
"""Build the serving wrapper directory for the Bonsai PQ2_0 target.

The wrapper is the ONLY model path the production entrypoint accepts: it pins
the text-only Qwen3.5 config, the verified tokenizer files and exactly one
GGUF payload behind an artifact manifest. This script runs offline during
preparation; serving only verifies.

Everything is fail-loud: the GGUF identity, its metadata contract and the
tokenizer identity are checked against this repository's pins before any
output is written. An existing non-empty output directory is never replaced.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import stat
import sys
from pathlib import Path
from typing import Dict, List

sys.path.insert(0, str(Path(__file__).resolve().parent))
from pq2.gguf_reader import GgufReader, ggml_type  # noqa: E402
from pq2.gguf_reader import GGMLType  # noqa: E402
from pq2 import hadamard as hadamard_mod  # noqa: E402

CHUNK = 8 * 1024 * 1024
PQ2_TYPE_ID = int(GGMLType.PQ2_0)
BOS_ID = 248044
EOS_ID = 248046
PAD_ID = 248044
EXPECTED_ARCH = "qwen35"
EXPECTED_CONTEXT = 262144


def sha256_of(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        while True:
            block = stream.read(CHUNK)
            if not block:
                break
            digest.update(block)
    return digest.hexdigest()


def require(condition: object, message: str) -> None:
    if not condition:
        raise ValueError(message)


def metadata_int(metadata: Dict[str, object], key: str) -> int:
    value = metadata.get(key)
    require(isinstance(value, int), f"GGUF metadata {key} missing or not an integer: {value!r}")
    return int(value)


def metadata_float(metadata: Dict[str, object], key: str) -> float:
    value = metadata.get(key)
    require(isinstance(value, (int, float)), f"GGUF metadata {key} missing or not numeric: {value!r}")
    return float(value)


def metadata_str(metadata: Dict[str, object], key: str) -> str:
    value = metadata.get(key)
    require(isinstance(value, str), f"GGUF metadata {key} missing or not a string: {value!r}")
    return value


REQUIRED_TOKENIZER_FILES = (
    "tokenizer.json",
    "tokenizer_config.json",
    "chat_template.jinja",
)
OPTIONAL_TOKENIZER_FILES = (
    "special_tokens_map.json",
    "generation_config.json",
)


def verify_tokenizer_identity(source: Path, tokens: List[str], metadata: Dict[str, object]) -> None:
    """The serving tokenizer must be the exact vocabulary the GGUF carries."""
    tokenizer_json = json.loads((source / "tokenizer.json").read_text(encoding="utf-8"))
    vocab = tokenizer_json["model"]["vocab"]
    require(tokenizer_json["model"]["type"] == "BPE", "tokenizer.json model type must be BPE")
    hf_tokens = [token for token, _ in sorted(vocab.items(), key=lambda item: item[1])]
    gguf_count = len(tokens)
    require(gguf_count == 248320, f"unexpected GGUF vocabulary size {gguf_count}")
    overlap = len(hf_tokens)
    require(overlap == 248044, f"unexpected tokenizer.json vocabulary size {overlap}")
    mismatches = [i for i in range(overlap) if hf_tokens[i] != tokens[i]]
    require(not mismatches, f"tokenizer.json vocabulary diverges from GGUF at {mismatches[:3]}")
    tail = tokens[overlap:]
    tokenizer_document = json.loads((source / "tokenizer.json").read_text(encoding="utf-8"))
    special_contents = {entry["id"]: entry["content"] for entry in tokenizer_document["added_tokens"]}
    require(len(special_contents) == 33, f"unexpected added-token count {len(special_contents)}")
    non_pad = [(i + overlap, token) for i, token in enumerate(tail) if not token.startswith("[PAD")]
    for token_id, token in non_pad:
        require(special_contents.get(token_id) == token,
                f"GGUF special token {token_id} {token!r} not in tokenizer_config.json")
    require(metadata_int(metadata, "tokenizer.ggml.bos_token_id") == BOS_ID, "bos id mismatch")
    require(metadata_int(metadata, "tokenizer.ggml.eos_token_id") == EOS_ID, "eos id mismatch")
    require(metadata_int(metadata, "tokenizer.ggml.padding_token_id") == PAD_ID, "pad id mismatch")


def validate_metadata(metadata: Dict[str, object]) -> None:
    require(metadata_str(metadata, "general.architecture") == EXPECTED_ARCH,
            f"unexpected GGUF architecture {metadata.get('general.architecture')!r}")
    checks = {
        "qwen35.context_length": EXPECTED_CONTEXT,
        "qwen35.block_count": 64,
        "qwen35.embedding_length": 5120,
        "qwen35.feed_forward_length": 17408,
        "qwen35.attention.head_count": 24,
        "qwen35.attention.head_count_kv": 4,
        "qwen35.attention.key_length": 256,
        "qwen35.attention.value_length": 256,
        "qwen35.ssm.conv_kernel": 4,
        "qwen35.ssm.state_size": 128,
        "qwen35.ssm.group_count": 16,
        "qwen35.ssm.time_step_rank": 48,
        "qwen35.ssm.inner_size": 6144,
        "qwen35.full_attention_interval": 4,
    }
    for key, expected in checks.items():
        require(metadata_int(metadata, key) == expected,
                f"GGUF {key} = {metadata.get(key)!r}, expected {expected}")
    require(abs(metadata_float(metadata, "qwen35.rope.freq_base") - 1e7) < 1e-3,
            "GGUF rope.freq_base mismatch")
    sections = metadata.get("qwen35.rope.dimension_sections")
    require(sections == [11, 11, 10, 0], f"unexpected rope dimension sections {sections!r}")
    require(metadata.get("general.quantization_version") == 2, "unexpected quantization version")


def wrapper_config() -> Dict[str, object]:
    """Text-only Qwen3.5 config; rope_parameters mirror the retained checkpoint."""
    return {
        "architectures": ["Qwen3_5ForCausalLM"],
        # Flat text-only config: Qwen3_5TextConfig. A composite qwen3_5 config
        # would auto-default an unused text sub-config and hide these fields.
        "model_type": "qwen3_5_text",
        "torch_dtype": "bfloat16",
        "vocab_size": 248320,
        "hidden_size": 5120,
        "intermediate_size": 17408,
        "num_hidden_layers": 64,
        "num_attention_heads": 24,
        "num_key_value_heads": 4,
        "head_dim": 256,
        "hidden_act": "silu",
        "max_position_embeddings": 262144,
        "rms_norm_eps": 1e-06,
        "rope_theta": 10000000.0,
        # Text-only mrope with identical position rows is exactly 1-D partial
        # NeoX rotary (rotary_dim = 0.25 * head_dim = 64); the fork's
        # rope.dimension_sections [11, 11, 10, 0] partition the same pairs.
        # rope_type "default" selects the unscaled rotary embedding, matching
        # the retained checkpoint's rope_parameters.rope_type.
        "rope_scaling": {"rope_type": "default"},
        "partial_rotary_factor": 0.25,
        "attn_output_gate": True,
        "output_gate_type": "swish",
        "attention_bias": False,
        "attention_dropout": 0.0,
        "linear_conv_kernel_dim": 4,
        "linear_key_head_dim": 128,
        "linear_value_head_dim": 128,
        "linear_num_key_heads": 16,
        "linear_num_value_heads": 48,
        "full_attention_interval": 4,
        "tie_word_embeddings": False,
        "bos_token_id": BOS_ID,
        "eos_token_id": EOS_ID,
        "pad_token_id": PAD_ID,
        "use_cache": True,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--gguf", type=Path, required=True,
                        help="Ternary-Bonsai-2-27B-PQ2_0.gguf payload")
    parser.add_argument("--tokenizer-source", type=Path, required=True,
                        help="Retained Qwen3.8 checkpoint directory with the verified tokenizer")
    parser.add_argument("--output", type=Path, required=True,
                        help="Wrapper directory to create (must not exist)")
    args = parser.parse_args()

    gguf_path = args.gguf.resolve()
    source = args.tokenizer_source.resolve()
    output = args.output

    require(gguf_path.is_file(), f"GGUF payload not found: {gguf_path}")
    require(source.is_dir(), f"Tokenizer source not found: {source}")
    require(not output.exists(), f"Output directory already exists: {output}")
    require(stat.S_ISDIR(source.lstat().st_mode), "Tokenizer source must be a real directory")

    digest = sha256_of(gguf_path)
    size = gguf_path.stat().st_size

    with GgufReader(str(gguf_path)) as reader:
        metadata = reader.metadata
        validate_metadata(metadata)
        tokens = metadata.get("tokenizer.ggml.tokens")
        require(isinstance(tokens, list) and tokens, "GGUF tokenizer tokens missing")
        verify_tokenizer_identity(source, list(tokens), metadata)

        # Hadamard contract must be present and well-formed before serving.
        parsed = hadamard_mod.parse_hadamard_metadata(metadata)
        pq2_names = {
            info.name for info in reader.tensors.values()
            if info.type is ggml_type(PQ2_TYPE_ID)
        }
        require("token_embd.weight" in pq2_names, "token_embd.weight must be PQ2_0")
        expected_folded = pq2_names - {"token_embd.weight"}
        require(set(parsed.weight_names) == expected_folded,
                "fold metadata must cover exactly the PQ2 matmul weights")
        print(f"hadamard contract ok: block_size={parsed.block_size}, "
              f"{len(parsed.weight_names)} folded weights, widths={sorted(parsed.signs_by_width)}")

    output.mkdir(mode=0o755)
    config = wrapper_config()
    (output / "config.json").write_text(json.dumps(config, indent=2) + "\n", encoding="utf-8")

    copied: List[str] = []
    for name in REQUIRED_TOKENIZER_FILES:
        candidate = source / name
        require(candidate.is_file(), f"tokenizer source missing {name}")
        (output / name).write_bytes(candidate.read_bytes())
        copied.append(name)
    for name in OPTIONAL_TOKENIZER_FILES:
        candidate = source / name
        if candidate.is_file():
            (output / name).write_bytes(candidate.read_bytes())
            copied.append(name)

    payload_name = gguf_path.name
    os.symlink(os.path.relpath(gguf_path, output), output / payload_name)
    resolved = (output / payload_name).resolve(strict=True)
    require(resolved == gguf_path, "payload symlink must resolve to the source GGUF")

    manifest = {
        "schema_version": 1,
        "wrapper_for": "Ternary-Bonsai-2-27B (PQ2_0 native) on SGLang + DFlash2",
        "payload": {"file": payload_name, "sha256": digest, "size_bytes": size},
        "config_sha256": sha256_of(output / "config.json"),
        "files": {
            name: {"sha256": sha256_of(output / name), "size_bytes": (output / name).stat().st_size}
            for name in (*copied, "config.json")
        },
        "tokenizer_source": str(source),
    }
    (output / "MANIFEST.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print(f"wrapper ready: {output}")
    print(f"payload {payload_name}: {size} bytes sha256 {digest}")


if __name__ == "__main__":
    main()
