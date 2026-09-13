#!/usr/bin/env python3
"""Read-only, CPU-only authentication of the approved local model pair.

The adjacent manifest, inventories and proof are the trust root. Mount them and
both model directories read-only. This checks bytes, not runtime quality.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
import re
import stat
import sys
from pathlib import Path
from typing import TypeAlias

JSON: TypeAlias = "bool | int | float | str | list[JSON] | dict[str, JSON] | None"
METADATA_LIMIT = 16 * 1024 * 1024
CHUNK_SIZE = 8 * 1024 * 1024
DRAFT_REVISION = "4d30ec736ffc6b8688dc2ae2b502d9b48bdec279"
TARGET_NAMES = frozenset(
    {
        "chat_template.jinja",
        "config.json",
        "generation_config.json",
        "model.safetensors.index.json",
        "model_extra_tensors.safetensors",
        "mtp_draft_vocab_ids.pt",
        "processor_config.json",
        "quantization_config.json",
        "tokenizer.json",
        "tokenizer_config.json",
    }
    | {f"model-{number:05d}-of-00007.safetensors" for number in range(1, 8)}
)
DRAFT_NAMES = frozenset({"config.json", "model.safetensors"})


def require(condition: bool, message: str) -> None:
    """Reject a condition unless it is exactly true."""
    if condition is not True:
        raise ValueError(message)


def regular(path: Path) -> None:
    """Require a regular file without following a symlink."""
    require(stat.S_ISREG(path.lstat().st_mode), f"Not a regular file: {path}")


def directory(path: Path) -> None:
    """Require an absolute directory with no symlink components."""
    require(path.is_absolute(), f"Expected absolute directory: {path}")
    require(".." not in path.parts, f"Parent traversal forbidden: {path}")
    for component in (*reversed(path.parents), path):
        require(
            stat.S_ISDIR(component.lstat().st_mode),
            f"Not a real directory (symlinks forbidden): {component}",
        )


def read_bytes(path: Path, limit: int = METADATA_LIMIT) -> bytes:
    """Read bounded metadata from a regular file."""
    regular(path)
    descriptor = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    with os.fdopen(descriptor, "rb") as stream:
        require(stat.S_ISREG(os.fstat(stream.fileno()).st_mode), f"Not regular: {path}")
        data = stream.read(limit + 1)
    require(len(data) <= limit, f"Metadata too large: {path}")
    return data


def digest(path: Path) -> str:
    """Hash a regular file and reject changes during verification."""
    regular(path)
    value = hashlib.sha256()
    descriptor = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    with os.fdopen(descriptor, "rb") as stream:
        before = os.fstat(stream.fileno())
        require(stat.S_ISREG(before.st_mode), f"Not regular: {path}")
        while True:
            block = stream.read(CHUNK_SIZE)
            if len(block) == 0:
                break
            value.update(block)
        after = os.fstat(stream.fileno())
    current = path.lstat()
    for snapshot in (after, current):
        require(
            (
                before.st_dev,
                before.st_ino,
                before.st_size,
                before.st_mtime_ns,
                before.st_ctime_ns,
            )
            == (
                snapshot.st_dev,
                snapshot.st_ino,
                snapshot.st_size,
                snapshot.st_mtime_ns,
                snapshot.st_ctime_ns,
            ),
            f"File changed during verification: {path}",
        )
    return value.hexdigest()


def json_value(value: object) -> JSON:
    """Validate and rebuild a finite JSON value."""
    if value is None or isinstance(value, (str, bool, int)):
        return value
    if isinstance(value, float):
        require(math.isfinite(value), "Nonfinite JSON number")
        return value
    if isinstance(value, list):
        return [json_value(item) for item in value]
    if isinstance(value, dict):
        result: dict[str, JSON] = {}
        for key, item in value.items():
            require(isinstance(key, str), "Non-string JSON key")
            if not isinstance(key, str):
                message = "Non-string JSON key"
                raise ValueError(message)
            result[key] = json_value(item)
        return result
    message = "Unsupported JSON value"
    raise ValueError(message)


def unique_object(pairs: list[tuple[str, object]]) -> dict[str, JSON]:
    """Build a JSON object while rejecting duplicate keys."""
    result: dict[str, JSON] = {}
    for key, value in pairs:
        require(key not in result, f"Duplicate JSON key: {key}")
        result[key] = json_value(value)
    return result


def obj(value: JSON) -> dict[str, JSON]:
    """Require a JSON object."""
    if not isinstance(value, dict):
        message = "Expected JSON object"
        raise ValueError(message)
    return value


def document(data: bytes) -> dict[str, JSON]:
    """Decode a strict JSON object from UTF-8 bytes."""
    value: object = json.loads(data.decode("utf-8"), object_pairs_hook=unique_object)
    return obj(json_value(value))


def integer(value: object) -> int:
    """Require an integer other than a boolean."""
    if not isinstance(value, int) or isinstance(value, bool):
        message = "Expected integer"
        raise ValueError(message)
    return value


def filename(value: object) -> str:
    """Require a safe inventory filename."""
    if (
        not isinstance(value, str)
        or re.fullmatch(r"[A-Za-z0-9_][A-Za-z0-9_.-]*", value) is None
    ):
        message = "Invalid inventory filename"
        raise ValueError(message)
    return value


def sha256(value: object) -> str:
    """Require a lowercase SHA256 digest."""
    if not isinstance(value, str) or re.fullmatch(r"[0-9a-f]{64}", value) is None:
        message = "Invalid SHA256"
        raise ValueError(message)
    return value


def inventory(data: bytes, names: frozenset[str]) -> dict[str, str]:
    """Parse an inventory with the exact approved filenames."""
    result: dict[str, str] = {}
    for line in data.decode("ascii").splitlines():
        require(
            len(line) >= 67 and line[64:66] == "  ", "Invalid SHA256 inventory line"
        )
        checksum = sha256(line[:64])
        name = filename(line[66:])
        require(name not in result, f"Duplicate inventory entry: {name}")
        result[name] = checksum
    require(
        set(result) == names, "Inventory filenames differ from approved model layout"
    )
    return result


def layout(path: Path, names: frozenset[str], draft: bool = False) -> None:
    """Verify the model directory layout without reading weights."""
    directory(path)
    entries = {entry.name: entry for entry in path.iterdir()}
    extras = set(entries) - names
    require(names <= set(entries), f"Missing model files: {path}")
    require(
        extras <= {"README.md", ".cache"} if draft else len(extras) == 0,
        f"Unexpected model files: {path}: {sorted(extras)}",
    )
    for name in names:
        regular(entries[name])
    if "README.md" in extras:
        regular(entries["README.md"])
    if ".cache" in extras:
        directory(entries[".cache"])


def quantization(config: dict[str, JSON], draft: bool, *, packed: bool = False) -> None:
    """Verify the approved packed quantization configuration."""
    quant = obj(config["quantization_config"])
    require(quant["quant_method"] == "compressed-tensors", "Wrong quantization method")
    require(quant["format"] == "pack-quantized", "Wrong quantization format")
    require(quant["quantization_status"] == "compressed", "Weights are not compressed")
    groups = obj(quant["config_groups"])
    expected = (
        {"group_0": ["Linear"]}
        if draft
        else {
            "group_0": ["Linear"],
            "group_1": ["re:.*lm_head$"],
            "group_3": [r"re:^mtp\..*"],
            **({"group_2": ["re:.*embed_tokens$"]} if packed else {}),
        }
    )
    require(set(groups) == set(expected), "Unexpected quantization groups")
    for name, targets in expected.items():
        group = obj(groups[name])
        require(group["targets"] == targets, f"Unexpected quantization targets: {name}")
        require(group["format"] == "pack-quantized", "Unexpected group format")
        require(
            group["input_activations"] is None and group["output_activations"] is None,
            "Expected unquantized activations",
        )
        weights = obj(group["weights"])
        bits = 8 if name == "group_2" else 4
        require(
            integer(weights["num_bits"]) == bits
            and integer(weights["group_size"]) == 128,
            f"Expected W{bits} group128 weights",
        )
        require(
            weights["symmetric"] is True and weights["dynamic"] is False,
            "Unexpected weight quantization",
        )
        require(
            weights["strategy"] == "group"
            and weights["type"] == "int"
            and weights["actorder"] is None,
            "Unexpected weight scheme",
        )


def verify(target: Path, draft: Path, representation: str = "dense") -> None:
    # Do not resolve(): individual Nix mounts must share this container directory.
    """Authenticate the approved model pair and its provenance."""
    require(representation in {"dense", "packed"}, "Unknown target representation")
    packed = representation == "packed"
    preparation = Path(__file__).absolute().parent
    manifest = document(read_bytes(preparation / "manifest.json"))
    require(integer(manifest["schema_version"]) == 1, "Unsupported manifest schema")
    require(
        manifest["validation_file"] == "embedding-validation.json"
        and manifest["output_inventory"] == "artifact.sha256"
        and manifest["source_inventory"] == "source.sha256"
        and manifest["draft_inventory"] == "draft.sha256",
        "Unexpected provenance paths",
    )
    require(
        obj(manifest["source_revisions"])["draft"] == DRAFT_REVISION,
        "Unexpected draft ancestry revision",
    )
    proof_data = read_bytes(preparation / "embedding-validation.json")
    require(
        hashlib.sha256(proof_data).hexdigest() == sha256(manifest["validation_sha256"]),
        "Embedding proof authentication failed",
    )
    proof = document(proof_data)
    target_hashes = inventory(
        read_bytes(preparation / ("source.sha256" if packed else "artifact.sha256")),
        TARGET_NAMES,
    )
    proof_hashes = {
        filename(name): sha256(value)
        for name, value in obj(
            proof["source_hashes" if packed else "output_hashes"]
        ).items()
    }
    require(
        target_hashes == proof_hashes,
        "Target inventory differs from authenticated proof",
    )
    draft_data = read_bytes(preparation / "draft.sha256")
    require(
        hashlib.sha256(draft_data).hexdigest()
        == sha256(manifest["draft_inventory_sha256"]),
        "Draft inventory authentication failed",
    )
    draft_hashes = inventory(draft_data, DRAFT_NAMES)
    layout(target, TARGET_NAMES)
    layout(draft, DRAFT_NAMES, draft=True)
    # Small configuration checks precede the large, bounded streaming reads.
    for path, hashes in ((target, target_hashes), (draft, draft_hashes)):
        require(
            digest(path / "config.json") == hashes["config.json"],
            f"Configuration SHA256 mismatch: {path}",
        )
    config = document(read_bytes(target / "config.json"))
    require(
        config["architectures"] == ["Qwen3_5ForConditionalGeneration"]
        and config["model_type"] == "qwen3_5",
        "Unexpected target architecture",
    )
    text = obj(config["text_config"])
    require(
        config["tie_word_embeddings"] is False and text["tie_word_embeddings"] is False,
        "Target embeddings must be untied",
    )
    rows = integer(text["vocab_size"])
    columns = integer(text["hidden_size"])
    require(rows == 248320 and columns == 5120, "Unexpected embedding dimensions")
    require(
        integer(proof["rows_checked"]) == rows
        and integer(proof["values_checked"]) == rows * columns
        and integer(proof["dense_bytes"]) == rows * columns * 2,
        "Embedding proof dimensions mismatch",
    )
    quantization(config, draft=False, packed=packed)
    index_data = read_bytes(target / "model.safetensors.index.json")
    require(
        hashlib.sha256(index_data).hexdigest()
        == target_hashes["model.safetensors.index.json"],
        "Index SHA256 mismatch",
    )
    index = document(index_data)
    require(
        integer(obj(index["metadata"])["total_size"])
        == integer(proof["source_index_total_size" if packed else "index_total_size"]),
        "Index byte count differs from proof",
    )
    mapping = obj(index["weight_map"])
    embedding_keys = (
        {
            "model.language_model.embed_tokens.weight_packed",
            "model.language_model.embed_tokens.weight_scale",
            "model.language_model.embed_tokens.weight_shape",
        }
        if packed
        else {"model.language_model.embed_tokens.weight"}
    )
    require(
        {key for key in mapping if "embed_tokens" in key} == embedding_keys,
        "Embedding keys differ from explicit representation",
    )
    for key in embedding_keys:
        require(
            mapping[key] == "model-00006-of-00007.safetensors",
            "Unexpected embedding shard",
        )
    shards = {filename(value) for value in mapping.values()}
    require(
        shards == {name for name in TARGET_NAMES if name.endswith(".safetensors")},
        "Index references unexpected shards",
    )
    draft_config = document(read_bytes(draft / "config.json"))
    require(
        draft_config["architectures"] == ["DFlash2DraftModel"],
        "Wrong draft architecture",
    )
    require(
        integer(obj(draft_config["dflash_config"])["block_size"]) == 8
        and integer(draft_config["sliding_window"]) == 2048
        and draft_config["use_sliding_window"] is True,
        "Wrong draft block/window configuration",
    )
    quantization(draft_config, draft=True)
    for path, hashes in ((target, target_hashes), (draft, draft_hashes)):
        for name, expected in sorted(hashes.items()):
            require(digest(path / name) == expected, f"SHA256 mismatch: {path / name}")
        print(f"Verified {len(hashes)} model files: {path}", flush=True)
    layout(target, TARGET_NAMES)
    layout(draft, DRAFT_NAMES, draft=True)
    print(
        "Model bytes verified; runtime qualification and activation are separate.",
        flush=True,
    )


def main() -> int:
    """Run the command and report validation failures."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--target", required=True, type=Path)
    parser.add_argument("--draft", required=True, type=Path)
    parser.add_argument(
        "--representation",
        choices=("dense", "packed"),
        default="dense",
        help="Authenticate only this target representation; never detect or fall back",
    )
    args = parser.parse_args()
    try:
        verify(args.target, args.draft, args.representation)
    except (OSError, ValueError, KeyError, TypeError, RecursionError) as error:
        print(f"Model verification failed: {error}", file=sys.stderr, flush=True)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
