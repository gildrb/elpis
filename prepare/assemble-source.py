#!/usr/bin/env python3
"""Assemble supplied, pinned model files in a new private directory; no network."""

from __future__ import annotations

import argparse
import hashlib
import importlib
import os
import sys
from pathlib import Path

# Reuse the serving verifier's strict boundary and inventory checks.
guard = importlib.import_module("verify-models")
ROOT = Path(__file__).resolve().parent


def copy_checked(source: Path, destination: Path, expected: str, size: int) -> None:
    """Copy an input exclusively and authenticate its size and digest."""
    guard.regular(source)
    checksum = hashlib.sha256()
    count = 0
    descriptor = os.open(source, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    with os.fdopen(descriptor, "rb") as incoming, destination.open("xb") as outgoing:
        while True:
            block = incoming.read(8 * 1024 * 1024)
            if len(block) == 0:
                break
            count += len(block)
            guard.require(count <= size, f"Oversized input: {source}")
            checksum.update(block)
            outgoing.write(block)
        outgoing.flush()
        os.fsync(outgoing.fileno())
    guard.require(
        count == size and checksum.hexdigest() == expected,
        f"Input SHA256/size mismatch: {source}; partial attempt retained",
    )
    destination.chmod(0o444)


def assemble(
    base: Path, fast: Path, draft: Path, embedding: Path, destination: Path
) -> None:
    """Authenticate supplied files and copy them into a new attempt."""
    for directory in (base, fast, draft, embedding.parent, destination.parent):
        guard.directory(directory)
    guard.require(
        destination.is_absolute() and ".." not in destination.parts,
        "Destination must be absolute without parent traversal",
    )
    provenance = guard.document(guard.read_bytes(ROOT / "source-provenance.json"))
    manifest = guard.document(guard.read_bytes(ROOT / "manifest.json"))
    repositories = guard.obj(provenance["repositories"])
    revisions = guard.obj(manifest["source_revisions"])
    for label, value in repositories.items():
        guard.require(
            guard.obj(value)["revision"] == revisions[label], "Revision mismatch"
        )
    files = guard.obj(provenance["files"])
    plans: list[tuple[Path, str, str, str, int]] = []
    roots = {"base": base, "fast": fast, "draft": draft}
    for group, names, inventory_file in (
        ("source", guard.TARGET_NAMES, "source.sha256"),
        ("draft", guard.DRAFT_NAMES, "draft.sha256"),
    ):
        inventory = guard.inventory(guard.read_bytes(ROOT / inventory_file), names)
        entries = guard.obj(files[group])
        guard.require(set(entries) == names, "Provenance inventory mismatch")
        for name, value in entries.items():
            entry = guard.obj(value)
            checksum = guard.sha256(entry["sha256"])
            guard.require(checksum == inventory[name], "Provenance SHA256 mismatch")
            origin = guard.filename(entry["origin"])
            size = guard.integer(entry["size"])
            guard.require(size > 0, "Invalid input size")
            if origin == "quantized-embedding":
                guard.require(
                    group == "source" and name == "model-00006-of-00007.safetensors",
                    "Unexpected derived file",
                )
                continue
            guard.require(origin in roots, "Unknown origin")
            plans.append((roots[origin] / name, group, name, checksum, size))
    raw = guard.obj(provenance["embedding_input"])
    plans.append((
        embedding,
        "input",
        guard.filename(raw["filename"]),
        guard.sha256(raw["sha256"]),
        guard.integer(raw["size"]),
    ))
    for source, _, _, _, size in plans:
        guard.regular(source)
        guard.require(source.stat().st_size == size, f"Input size mismatch: {source}")
    # Ownership is established before any writes. Existing paths always fail.
    destination.mkdir(mode=0o700)
    for group in ("source", "draft", "input"):
        (destination / group).mkdir(mode=0o700)
    for source, group, name, checksum, size in plans:
        copy_checked(source, destination / group / name, checksum, size)
        print(f"Copied and authenticated {group}/{name}", flush=True)
    (destination / "draft").chmod(0o555)
    (destination / "input").chmod(0o555)
    print(
        "Offline inputs authenticated. Source is incomplete until quantize-embedding.py succeeds."
    )


def main() -> int:
    """Run the command and report validation failures."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base", type=Path, required=True)
    parser.add_argument("--fast", type=Path, required=True)
    parser.add_argument("--draft", type=Path, required=True)
    parser.add_argument("--embedding-input", type=Path, required=True)
    parser.add_argument("--destination", type=Path, required=True)
    args = parser.parse_args()
    try:
        assemble(
            args.base, args.fast, args.draft, args.embedding_input, args.destination
        )
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"Offline assembly failed: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
