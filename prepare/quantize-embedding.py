#!/usr/bin/env python3
"""Reproduce only the pinned int8 embedding shard from authenticated BF16 input.

Run inside the manifest-pinned image. Inputs are read-only; output must be absent.
The adjacent upstream recipe is provenance only and is never executed.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib
import sys
from pathlib import Path

import torch
from compressed_tensors.compressors.pack_quantized.base import pack_to_int32
from safetensors import safe_open
from safetensors.torch import save_file

guard = importlib.import_module("verify-models")
ROOT = Path(__file__).resolve().parent
NAME = "model-00006-of-00007.safetensors"
KEY = "model.language_model.embed_tokens.weight"
NORM = "model.language_model.norm.weight"


def quantize(work: Path, shard_only: bool = False) -> None:
    """Reproduce and authenticate the pinned embedding shard offline."""
    guard.directory(work)
    source = work / "source"
    if shard_only is False:
        guard.directory(source)
    guard.directory(work / "input")
    provenance = guard.document(guard.read_bytes(ROOT / "source-provenance.json"))
    recipe = guard.obj(provenance["embedding_recipe"])
    guard.require(
        guard.digest(ROOT / guard.filename(recipe["file"]))
        == guard.sha256(recipe["sha256"]),
        "Upstream recipe hash mismatch",
    )
    raw = guard.obj(provenance["embedding_input"])
    incoming = work / "input" / NAME
    guard.require(
        guard.digest(incoming) == guard.sha256(raw["sha256"]),
        "Raw embedding input hash mismatch",
    )
    expected = guard.inventory(
        guard.read_bytes(ROOT / "source.sha256"), guard.TARGET_NAMES
    )
    if shard_only is False:
        guard.layout(source, guard.TARGET_NAMES - {NAME})
        for name in sorted(guard.TARGET_NAMES - {NAME}):
            guard.require(
                guard.digest(source / name) == expected[name],
                f"Source mismatch: {name}",
            )
    # A private exclusive directory owns the intermediate, including on failure.
    temporary = work / "embedding-quantization"
    temporary.mkdir(mode=0o700)
    output = temporary / NAME
    torch.set_num_threads(4)
    tensors: dict[str, torch.Tensor] = {}
    with safe_open(incoming, framework="pt", device="cpu") as handle:
        guard.require(set(handle.keys()) == {KEY, NORM}, "Unexpected raw shard tensors")
        weight = handle.get_tensor(KEY)
        norm = handle.get_tensor(NORM)
        guard.require(
            list(weight.shape) == [248320, 5120] and weight.dtype == torch.bfloat16,
            "Wrong embedding shape/dtype",
        )
        guard.require(
            list(norm.shape) == [5120] and norm.dtype == torch.bfloat16,
            "Wrong norm shape/dtype",
        )
        metadata = handle.metadata()
        guard.require(
            metadata is None or metadata == {"format": "pt"}, "Unexpected metadata"
        )
        tensors[NORM] = norm.clone()
        packed = torch.empty((248320, 1280), dtype=torch.int32)
        scales = torch.empty((248320, 40), dtype=torch.bfloat16)
        error_squared = 0.0
        weight_squared = 0.0
        # Groupwise operations are identical to upstream; chunking bounds RAM.
        for start in range(0, 248320, 1024):
            stop = min(start + 1024, 248320)
            dense = weight[start:stop].to(torch.float32)
            grouped = dense.reshape(stop - start, 40, 128)
            scale = torch.clamp(
                grouped.abs().amax(dim=-1, keepdim=True) / 127, min=1e-10
            )
            quantized = torch.clamp(torch.round(grouped / scale), -128, 127).to(
                torch.int8
            )
            dequantized = quantized.to(torch.float32) * scale
            error_squared += (dequantized - grouped).double().square().sum().item()
            weight_squared += grouped.double().square().sum().item()
            packed[start:stop] = pack_to_int32(
                quantized.reshape(stop - start, 5120), 8, packed_dim=1
            ).contiguous()
            scales[start:stop] = scale.squeeze(-1).to(torch.bfloat16)
        guard.require(
            weight_squared > 0 and error_squared / weight_squared < 0.0001,
            "Quantization error exceeds upstream 1 percent limit",
        )
        tensors[KEY.replace(".weight", ".weight_packed")] = packed
        tensors[KEY.replace(".weight", ".weight_scale")] = scales
        tensors[KEY.replace(".weight", ".weight_shape")] = torch.tensor(
            [248320, 5120], dtype=torch.int64
        )
        save_file(tensors, output, metadata={"format": "pt"})
    guard.require(
        guard.digest(output) == expected[NAME],
        "Quantized shard differs from pinned bytes; intermediate retained, source unpublished",
    )
    if shard_only is True:
        output.chmod(0o444)
        print(f"Isolated shard reproduction verified: {expected[NAME]}", flush=True)
        print("No source assembly or artifact publication performed.", flush=True)
        return
    # Independent copy with exclusive creation; no overwrite, hardlink or fallback.
    checksum = hashlib.sha256()
    with output.open("rb") as incoming_stream, (source / NAME).open("xb") as outgoing:
        while True:
            block = incoming_stream.read(8 * 1024 * 1024)
            if len(block) == 0:
                break
            checksum.update(block)
            outgoing.write(block)
    guard.require(checksum.hexdigest() == expected[NAME], "Publication hash mismatch")
    (source / NAME).chmod(0o444)
    guard.layout(source, guard.TARGET_NAMES)
    source.chmod(0o555)
    print(f"All 17 source files authenticated; embedding SHA256 {expected[NAME]}")
    print("Run the separate original conversion and final model verification next.")


def main() -> int:
    """Run the command and report validation failures."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", type=Path, required=True)
    parser.add_argument(
        "--shard-only",
        action="store_true",
        help="Verify only the derived shard; do not assemble or publish source",
    )
    args = parser.parse_args()
    try:
        quantize(args.work, args.shard_only)
    except (OSError, ValueError, KeyError, TypeError, RuntimeError) as error:
        print(f"Embedding preparation failed: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
