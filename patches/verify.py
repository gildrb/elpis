#!/usr/bin/env python3
"""Verify the required reviewed runtime sources without importing SGLang."""

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

REVIEWED_MODULE_COUNT = 3


def unique_object(pairs: list[tuple[str, object]]) -> dict[str, object]:
    """Decode an object without accepting duplicate keys.

    Returns:
        The decoded fields.

    Raises:
        ValueError: If a manifest key is repeated.

    """
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            message = f"duplicate manifest key: {key}"
            raise ValueError(message)
        result[key] = value
    return result


def object_fields(value: object, label: str) -> dict[str, object]:
    """Return manifest object fields with string keys.

    Returns:
        The validated object fields.

    Raises:
        ValueError: If the value is not an object with string keys.

    """
    if isinstance(value, dict):
        result: dict[str, object] = {}
        for key, item in value.items():
            if isinstance(key, str):
                result[key] = item
                continue
            message = f"{label} keys must be strings"
            raise ValueError(message)
        return result
    message = f"{label} must be an object"
    raise ValueError(message)


def text(value: object, label: str) -> str:
    """Return a nonempty manifest string.

    Returns:
        The validated string.

    Raises:
        ValueError: If the value is not a nonempty string.

    """
    if not isinstance(value, str) or len(value) == 0:
        message = f"{label} must be a nonempty string"
        raise ValueError(message)
    return value


def _verify_provenance(value: object) -> None:
    """Check the exact source provenance fields and digest syntax.

    Raises:
        ValueError: If a reviewed baseline guard fails.

    """
    source = object_fields(value, "source")
    if set(source) != {"repository", "revision", "base_revision", "nar_hash"}:
        message = "unexpected source provenance schema"
        raise ValueError(message)
    if source["repository"] != "https://github.com/gildrb/sglang":
        message = "unexpected source repository"
        raise ValueError(message)
    for key in ("revision", "base_revision"):
        if re.fullmatch(r"[0-9a-f]{40}", text(source[key], key)) is None:
            message = f"invalid source revision: {key}"
            raise ValueError(message)
    if (
        re.fullmatch(r"sha256-[A-Za-z0-9+/]{43}=", text(source["nar_hash"], "nar_hash"))
        is None
    ):
        message = "invalid source NAR hash"
        raise ValueError(message)


def _verify_manifest(manifest: dict[str, object], image: str) -> None:
    """Check the baseline manifest schema, provenance and image identity.

    Raises:
        ValueError: If a reviewed baseline guard fails.

    """
    if set(manifest) != {
        "schema_version",
        "status",
        "quality_status",
        "base_image",
        "source_root",
        "runtime",
        "modules",
        "qualification",
        "source",
    }:
        message = "unexpected manifest schema"
        raise ValueError(message)
    _verify_provenance(manifest["source"])
    if (
        type(manifest.get("schema_version")) is not int
        or manifest["schema_version"] != 1
    ):
        message = "unsupported manifest schema"
        raise ValueError(message)
    if manifest.get("status") != "reviewed_runtime":
        message = "unexpected reviewed runtime status"
        raise ValueError(message)
    source_root = text(manifest.get("source_root"), "source_root")
    if source_root != "/sgl-workspace/sglang/python/sglang/srt":
        message = "unexpected installed source root"
        raise ValueError(message)
    base_image = text(manifest.get("base_image"), "base_image")
    if re.fullmatch(r"lmsysorg/sglang@sha256:[0-9a-f]{64}", base_image) is None:
        message = "invalid immutable base image"
        raise ValueError(message)
    image_match = re.fullmatch(
        r"(lmsysorg/sglang)(?::[a-zA-Z0-9_.-]+)?@(sha256:[0-9a-f]{64})",
        image,
    )
    if image_match is None or "@".join(image_match.groups()) != base_image:
        message = "configured image does not match qualified image"
        raise ValueError(message)


def _verify_module_bytes(fields: dict[str, str], root: Path, phase: str) -> None:
    """Check the installed file identity and phase digest.

    Raises:
        ValueError: If the file is missing, symlinked or has the wrong digest.

    """
    relative = fields["installed_path"]
    path = root / relative
    if not path.is_file() or path.resolve() != path:
        message = f"missing or symlinked module: {relative}"
        raise ValueError(message)
    with path.open("rb") as stream:
        digest = hashlib.file_digest(stream, "sha256").hexdigest()
    if digest != fields[f"{phase}_sha256"]:
        message = f"{phase} source digest mismatch: {relative}"
        raise ValueError(message)


def _verify_modules(manifest: dict[str, object], root: Path, phase: str) -> None:
    """Verify the three reviewed module records and their installed bytes.

    Raises:
        ValueError: If a reviewed baseline guard fails.

    """
    modules = manifest.get("modules")
    if not isinstance(modules, list) or len(modules) != REVIEWED_MODULE_COUNT:
        message = "manifest must contain exactly three reviewed modules"
        raise ValueError(message)
    expected_paths = {
        "layers/logits_processor.py",
        "models/dflash.py",
        "speculative/dflash_worker_v2.py",
    }
    seen: set[str] = set()
    for value in modules:
        module = object_fields(value, "module")
        if set(module) != {
            "file",
            "installed_path",
            "original_sha256",
            "replacement_sha256",
            "patch",
            "patch_sha256",
            "purpose",
        }:
            message = "unexpected module schema"
            raise ValueError(message)
        fields = {key: text(item, key) for key, item in module.items()}
        relative = fields["installed_path"]
        if relative not in expected_paths or relative in seen:
            message = f"unexpected or repeated module path: {relative}"
            raise ValueError(message)
        seen.add(relative)
        if fields["file"] != Path(relative).name:
            message = "module filename does not match installed path"
            raise ValueError(message)
        if re.fullmatch(r"[a-z0-9-]+\.patch", fields["patch"]) is None:
            message = "invalid patch filename"
            raise ValueError(message)
        for key in ("original_sha256", "replacement_sha256", "patch_sha256"):
            if re.fullmatch(r"[0-9a-f]{64}", fields[key]) is None:
                message = f"invalid module digest: {key}"
                raise ValueError(message)
        _verify_module_bytes(fields, root, phase)


def main() -> None:
    """Verify reviewed sources using the required command-line arguments.

    Raises:
        TypeError: If the parsed root is not a path.
        ValueError: If the source root is not a canonical absolute directory.

    """
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
    _verify_manifest(manifest, args.image)
    root = args.root
    if not isinstance(root, Path):
        message = "source root must be a path"
        raise TypeError(message)
    if not root.is_absolute() or not root.is_dir() or root.resolve() != root:
        message = "source root must be an existing canonical absolute directory"
        raise ValueError(message)
    _verify_modules(manifest, root, args.phase)
    sys.stdout.write(
        f"[sglang-compat] verified {args.phase} source; reviewed runtime\n"
    )


if __name__ == "__main__":
    main()
