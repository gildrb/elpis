#!/usr/bin/env python3
"""Verify the reviewed opt-in source overlay without importing SGLang."""

import argparse
import hashlib
import json
from pathlib import Path
import re


def unique_object(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate manifest key: {key}")
        result[key] = value
    return result


def object_fields(value: object, label: str) -> dict[str, object]:
    if not isinstance(value, dict):
        raise ValueError(f"{label} must be an object")
    result: dict[str, object] = {}
    for key, item in value.items():
        if not isinstance(key, str):
            raise ValueError(f"{label} keys must be strings")
        result[key] = item
    return result


def text(value: object, label: str) -> str:
    if not isinstance(value, str) or len(value) == 0:
        raise ValueError(f"{label} must be a nonempty string")
    return value


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--phase", choices=("original", "replacement"), required=True)
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--image", required=True)
    args = parser.parse_args()
    decoded: object = json.loads(
        args.manifest.read_text(), object_pairs_hook=unique_object
    )
    manifest = object_fields(decoded, "manifest")
    if set(manifest) != {
        "schema_version", "status", "quality_status", "base_image", "source_root",
        "runtime", "modules", "qualification", "source",
    }:
        raise ValueError("unexpected manifest schema")
    source = object_fields(manifest["source"], "source")
    if set(source) != {"repository", "revision", "base_revision", "nar_hash"}:
        raise ValueError("unexpected source provenance schema")
    if source["repository"] != "https://github.com/gildrb/sglang":
        raise ValueError("unexpected source repository")
    for key in ("revision", "base_revision"):
        if re.fullmatch(r"[0-9a-f]{40}", text(source[key], key)) is None:
            raise ValueError(f"invalid source revision: {key}")
    if re.fullmatch(r"sha256-[A-Za-z0-9+/]{43}=", text(source["nar_hash"], "nar_hash")) is None:
        raise ValueError("invalid source NAR hash")
    if type(manifest.get("schema_version")) is not int or manifest["schema_version"] != 1:
        raise ValueError("unsupported manifest schema")
    if manifest.get("status") != "reviewed_opt_in_runtime":
        raise ValueError("unexpected reviewed opt-in runtime status")
    source_root = text(manifest.get("source_root"), "source_root")
    if source_root != "/sgl-workspace/sglang/python/sglang/srt":
        raise ValueError("unexpected installed source root")
    base_image = text(manifest.get("base_image"), "base_image")
    if re.fullmatch(r"lmsysorg/sglang@sha256:[0-9a-f]{64}", base_image) is None:
        raise ValueError("invalid immutable base image")
    image_match = re.fullmatch(
        r"(lmsysorg/sglang)(?::[a-zA-Z0-9_.-]+)?@(sha256:[0-9a-f]{64})",
        args.image,
    )
    if image_match is None or "@".join(image_match.groups()) != base_image:
        raise ValueError("configured image does not match qualified image")
    root: Path = args.root
    if not root.is_absolute() or not root.is_dir() or root.resolve() != root:
        raise ValueError("source root must be an existing canonical absolute directory")
    modules = manifest.get("modules")
    if not isinstance(modules, list) or len(modules) != 3:
        raise ValueError("manifest must contain exactly three reviewed modules")
    expected_paths = {
        "layers/logits_processor.py", "models/dflash.py",
        "speculative/dflash_worker_v2.py",
    }
    seen: set[str] = set()
    for value in modules:
        module = object_fields(value, "module")
        if set(module) != {
            "file", "installed_path", "original_sha256", "replacement_sha256",
            "patch", "patch_sha256", "purpose",
        }:
            raise ValueError("unexpected module schema")
        fields = {key: text(item, key) for key, item in module.items()}
        relative = fields["installed_path"]
        if relative not in expected_paths or relative in seen:
            raise ValueError(f"unexpected or repeated module path: {relative}")
        seen.add(relative)
        if fields["file"] != Path(relative).name:
            raise ValueError("module filename does not match installed path")
        if re.fullmatch(r"[a-z0-9-]+\.patch", fields["patch"]) is None:
            raise ValueError("invalid patch filename")
        for key in ("original_sha256", "replacement_sha256", "patch_sha256"):
            if re.fullmatch(r"[0-9a-f]{64}", fields[key]) is None:
                raise ValueError(f"invalid module digest: {key}")
        path = root / relative
        if not path.is_file() or path.resolve() != path:
            raise ValueError(f"missing or symlinked module: {relative}")
        with path.open("rb") as stream:
            digest = hashlib.file_digest(stream, "sha256").hexdigest()
        if digest != fields[f"{args.phase}_sha256"]:
            raise ValueError(f"{args.phase} source digest mismatch: {relative}")
    print(f"[sglang-compat] verified {args.phase} source; reviewed opt-in runtime")


if __name__ == "__main__":
    main()
