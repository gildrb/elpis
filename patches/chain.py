#!/usr/bin/env python3
"""Authenticate and apply the non-serving qualification source chain."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import secrets
import stat
from contextlib import contextmanager
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from collections.abc import Iterator

SGLANG_PREFIX_COMPONENTS = 3
MAX_FILE_BYTES = 2 * 1024 * 1024


class ChainError(ValueError):
    """Reject an invalid source bundle or source tree."""


def require(*, condition: bool, message: str) -> None:
    """Reject a failed explicit validation condition.

    Raises:
        ChainError: If a required validation condition fails.

    """
    if not condition:
        raise ChainError(message)


def relative_path(value: object) -> str:
    """Validate a portable relative path with no traversal components.

    Returns:
        The validated portable path.

    Raises:
        TypeError: If a narrowed value has an unexpected type.

    """
    require(condition=isinstance(value, str), message="Path must be text")
    if not isinstance(value, str):
        raise TypeError
    require(
        condition=re.fullmatch(r"[A-Za-z0-9_./-]+", value) is not None,
        message="Invalid path text",
    )
    parts = value.split("/")
    require(
        condition=all(part not in {"", ".", ".."} for part in parts),
        message="Invalid path component",
    )
    require(
        condition=not PurePosixPath(value).is_absolute(),
        message="Absolute path forbidden",
    )
    return value


def digest(value: object, *, absent: bool = False) -> str | None:
    """Validate a SHA256 digest or an explicitly permitted absence.

    Returns:
        The validated digest, or permitted absence.

    Raises:
        TypeError: If a narrowed value has an unexpected type.

    """
    if value is None and absent:
        return None
    require(condition=isinstance(value, str), message="Digest must be text")
    if not isinstance(value, str):
        raise TypeError
    require(
        condition=re.fullmatch(r"[0-9a-f]{64}", value) is not None,
        message="Invalid SHA256",
    )
    return value


def object_fields(value: object, fields: set[str]) -> dict[str, object]:
    """Validate exact object fields without accepting unknown keys.

    Returns:
        The exact validated fields.

    Raises:
        ChainError: If a required validation condition fails.
        TypeError: If a narrowed value has an unexpected type.

    """
    if not isinstance(value, dict):
        message = "Expected JSON object"
        raise ChainError(message)
    result: dict[str, object] = {}
    for key, item in value.items():
        require(condition=isinstance(key, str), message="Object key must be text")
        if not isinstance(key, str):
            raise TypeError
        result[key] = item
    require(condition=set(result) == fields, message="Unexpected object fields")
    return result


def unique_object(pairs: list[tuple[str, object]]) -> dict[str, object]:
    """Reject duplicate JSON keys before schema validation.

    Returns:
        The decoded object with unique keys.

    """
    result: dict[str, object] = {}
    for key, value in pairs:
        require(condition=key not in result, message="Duplicate JSON key")
        result[key] = value
    return result


def entries(value: object) -> list[object]:
    """Validate a nonempty JSON array.

    Returns:
        The nonempty array items.

    Raises:
        ChainError: If a required validation condition fails.

    """
    if not isinstance(value, list):
        message = "Expected JSON array"
        raise ChainError(message)
    require(condition=len(value) > 0, message="Empty array")
    return list(value)


@dataclass(frozen=True)
class Transition:
    """One authenticated source-file transition."""

    path: str
    before: str | None
    after: str

    @classmethod
    def parse(cls, value: object) -> Transition:
        """Validate a transition record.

        Returns:
            The validated record.

        Raises:
            TypeError: If a narrowed value has an unexpected type.

        """
        obj = object_fields(value, {"path", "before_sha256", "after_sha256"})
        after = digest(obj["after_sha256"])
        require(condition=after is not None, message="Missing replacement digest")
        if after is None:
            raise TypeError
        return cls(
            relative_path(obj["path"]), digest(obj["before_sha256"], absent=True), after
        )


@dataclass(frozen=True)
class SourceFile:
    """One original and final inventory entry."""

    path: str
    original: str | None
    final: str
    original_file: str | None

    @classmethod
    def parse(cls, value: object) -> SourceFile:
        """Validate the original-file presence contract.

        Returns:
            The validated record.

        Raises:
            ChainError: If a required validation condition fails.

        """
        obj = object_fields(
            value, {"path", "original_sha256", "final_sha256", "original_file"}
        )
        original = digest(obj["original_sha256"], absent=True)
        final = digest(obj["final_sha256"])
        if final is None:
            message = "Missing final digest"
            raise ChainError(message)
        original_file = (
            None
            if obj["original_file"] is None
            else relative_path(obj["original_file"])
        )
        require(
            condition=(original is None) == (original_file is None),
            message="Original presence mismatch",
        )
        return cls(relative_path(obj["path"]), original, final, original_file)


@dataclass(frozen=True)
class Stage:
    """One ordered patch with exact input and output files."""

    name: str
    patch: str
    patch_sha256: str
    strip_components: int
    files: tuple[Transition, ...]

    @classmethod
    def parse(cls, value: object) -> Stage:
        """Validate patch metadata and unique paths.

        Returns:
            The validated record.

        Raises:
            TypeError: If a narrowed value has an unexpected type.

        """
        obj = object_fields(
            value, {"name", "patch", "patch_sha256", "strip_components", "files"}
        )
        name = relative_path(obj["name"])
        patch_hash = digest(obj["patch_sha256"])
        strip = obj["strip_components"]
        require(
            condition=type(strip) is int and strip in {1, 3},
            message="Unsupported patch path prefix",
        )
        if not isinstance(strip, int) or patch_hash is None:
            raise TypeError
        files = tuple(Transition.parse(item) for item in entries(obj["files"]))
        require(
            condition=len({item.path for item in files}) == len(files),
            message="Repeated stage path",
        )
        return cls(name, relative_path(obj["patch"]), patch_hash, strip, files)


@dataclass(frozen=True)
class Plan:
    """Validated image binding and complete source chain."""

    image: str
    stages: tuple[Stage, ...]
    files: tuple[SourceFile, ...]

    @classmethod
    def parse(cls, raw: bytes) -> Plan:
        """Validate the schema and connect every intermediate digest.

        Returns:
            The validated record.

        Raises:
            ChainError: If a required validation condition fails.

        """
        decoded: object = json.loads(raw, object_pairs_hook=unique_object)
        obj = object_fields(
            decoded,
            {
                "schema_version",
                "status",
                "base_image",
                "source_root",
                "stages",
                "files",
            },
        )
        require(
            condition=type(obj["schema_version"]) is int and obj["schema_version"] == 1,
            message="Unsupported schema",
        )
        require(
            condition=obj["status"] == "source-only-unqualified-not-for-serving",
            message="Invalid qualification status",
        )
        require(
            condition=obj["source_root"] == "/sgl-workspace/sglang/python/sglang",
            message="Unexpected installed root",
        )
        image = obj["base_image"]
        if not isinstance(image, str):
            message = "Image must be text"
            raise ChainError(message)
        require(
            condition=re.fullmatch(r"lmsysorg/sglang@sha256:[0-9a-f]{64}", image)
            is not None,
            message="Image must be digest-pinned",
        )
        stages = tuple(Stage.parse(item) for item in entries(obj["stages"]))
        files = tuple(SourceFile.parse(item) for item in entries(obj["files"]))
        require(
            condition=len({stage.name for stage in stages}) == len(stages),
            message="Repeated stage name",
        )
        require(
            condition=len({stage.patch for stage in stages}) == len(stages),
            message="Repeated patch",
        )
        require(
            condition=len({item.path for item in files}) == len(files),
            message="Repeated inventory path",
        )
        state = {item.path: item.original for item in files}
        covered: set[str] = set()
        for stage in stages:
            for change in stage.files:
                require(condition=change.path in state, message="Unlisted stage path")
                require(
                    condition=state[change.path] == change.before,
                    message="Broken intermediate digest chain",
                )
                require(
                    condition=change.before != change.after,
                    message="Unchanged patch transition",
                )
                state[change.path] = change.after
                covered.add(change.path)
        require(condition=covered == set(state), message="Unpatched inventory path")
        require(
            condition=state == {item.path: item.final for item in files},
            message="Final inventory mismatch",
        )
        return cls(image, stages, files)


@contextmanager
def parent_fd(
    root: Path, relative: str, *, create: bool = False
) -> Iterator[tuple[int, str]]:
    """Open each directory without following symlinks, optionally creating it.

    Yields:
        The secured parent descriptor and final filename.

    """
    parts = relative_path(relative).split("/")
    require(condition=root.is_absolute(), message="Source root must be absolute")
    descriptor = os.open("/", os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    try:
        for component in root.parts[1:]:
            child = os.open(
                component,
                os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW,
                dir_fd=descriptor,
            )
            os.close(descriptor)
            descriptor = child
        for part in parts[:-1]:
            if create:
                try:
                    os.mkdir(part, dir_fd=descriptor)
                except FileExistsError:
                    require(
                        condition=stat.S_ISDIR(
                            os.stat(
                                part, dir_fd=descriptor, follow_symlinks=False
                            ).st_mode
                        ),
                        message="Existing parent is not a directory",
                    )
            child = os.open(
                part, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=descriptor
            )
            os.close(descriptor)
            descriptor = child
        yield descriptor, parts[-1]
    finally:
        os.close(descriptor)


def read_at(descriptor: int, name: str) -> bytes | None:
    """Read a regular file through an already secured parent directory.

    Returns:
        The file bytes, or None when absent.

    """
    try:
        source = os.open(
            name, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK, dir_fd=descriptor
        )
    except FileNotFoundError:
        return None
    with os.fdopen(source, "rb") as stream:
        metadata = os.fstat(stream.fileno())
        require(
            condition=stat.S_ISREG(metadata.st_mode),
            message="Source is not a regular file",
        )
        require(
            condition=metadata.st_size <= MAX_FILE_BYTES,
            message="Source exceeds file size limit",
        )
        raw = stream.read(MAX_FILE_BYTES + 1)
        require(
            condition=len(raw) <= MAX_FILE_BYTES,
            message="Source grew beyond file size limit",
        )
        return raw


def read_source(root: Path, relative: str) -> bytes | None:
    """Read bytes or report absence without following any source symlink.

    Returns:
        The file bytes, or None when absent.

    """
    try:
        with parent_fd(root, relative) as (descriptor, name):
            return read_at(descriptor, name)
    except FileNotFoundError:
        return None


def check_bytes(raw: bytes | None, expected: str | None, label: str) -> None:
    """Verify exact bytes or required absence."""
    actual = None if raw is None else hashlib.sha256(raw).hexdigest()
    require(
        condition=actual == expected,
        message="Source digest or absence mismatch: " + label,
    )


def write_source(root: Path, change: Transition, raw: bytes) -> None:
    """Recheck the destination and atomically publish an owned temporary file.

    The disposable build root must be exclusively owned without concurrent
    writers. Only absent paths are accepted. A no-clobber link ensures
    concurrent creation cannot be overwritten.

    Raises:
        TypeError: If the temporary file identity was not established.

    """
    require(
        condition=change.before is None, message="Only absent paths may be published"
    )
    with parent_fd(root, change.path, create=True) as (descriptor, name):
        check_bytes(read_at(descriptor, name), change.before, change.path)
        temporary = ".qwen-chain-" + secrets.token_hex(16)
        output = os.open(
            temporary,
            os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW,
            0o644,
            dir_fd=descriptor,
        )
        owned: os.stat_result | None = None
        try:
            with os.fdopen(output, "wb") as stream:
                owned = os.fstat(stream.fileno())
                stream.write(raw)
            check_bytes(read_at(descriptor, name), change.before, change.path)
            os.link(
                temporary,
                name,
                src_dir_fd=descriptor,
                dst_dir_fd=descriptor,
                follow_symlinks=False,
            )
        finally:
            try:
                current = os.stat(temporary, dir_fd=descriptor, follow_symlinks=False)
            except FileNotFoundError:
                current = None
            if current is not None:
                require(
                    condition=owned is not None,
                    message="Temporary file identity was not established",
                )
                if owned is None:
                    raise TypeError
                require(
                    condition=(current.st_dev, current.st_ino)
                    == (owned.st_dev, owned.st_ino),
                    message="Temporary file ownership changed",
                )
                os.unlink(temporary, dir_fd=descriptor)


def patch_path(line: str, prefix: str, strip: int) -> str | None:
    """Accept only the declared unified-diff header convention.

    Returns:
        The stripped path, or None for /dev/null.

    """
    require(
        condition=line.startswith(prefix) and line.endswith("\n"),
        message="Malformed patch header",
    )
    value = line[len(prefix) : -1]
    if value == "/dev/null":
        return None
    path = relative_path(value)
    parts = path.split("/")
    expected = ["a" if prefix == "--- " else "b"]
    if strip == SGLANG_PREFIX_COMPONENTS:
        expected.extend(["python", "sglang"])
    require(
        condition=parts[:strip] == expected and len(parts) > strip,
        message="Unexpected patch prefix",
    )
    return relative_path("/".join(parts[strip:]))


def apply_hunk(
    lines: list[str], index: int, source: list[str], cursor: int, output: list[str]
) -> tuple[int, int]:
    """Apply one exact-position hunk with validated old and new line counts.

    Returns:
        The next patch index and source cursor.

    Raises:
        TypeError: If a narrowed value has an unexpected type.

    """
    match = re.fullmatch(
        r"@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@[^\n]*\n", lines[index]
    )
    require(condition=match is not None, message="Malformed hunk header")
    if match is None:
        raise TypeError
    old_start, old_count, new_start, new_count = (
        int(value) if value is not None else 1 for value in match.groups()
    )
    at = old_start - 1 if old_count > 0 else old_start
    require(condition=cursor <= at <= len(source), message="Invalid hunk position")
    output.extend(source[cursor:at])
    require(
        condition=len(output) == (new_start - 1 if new_count > 0 else new_start),
        message="Invalid output position",
    )
    cursor = at
    consumed = produced = 0
    index += 1
    while consumed < old_count or produced < new_count:
        require(condition=index < len(lines), message="Truncated hunk")
        line = lines[index]
        require(
            condition=line[:1] in {" ", "+", "-"} and line.endswith("\n"),
            message="Invalid hunk line",
        )
        if line[0] in {" ", "-"}:
            require(
                condition=cursor < len(source) and source[cursor] == line[1:],
                message="Hunk context mismatch",
            )
            cursor += 1
            consumed += 1
        if line[0] in {" ", "+"}:
            output.append(line[1:])
            produced += 1
        require(
            condition=consumed <= old_count and produced <= new_count,
            message="Hunk count overflow",
        )
        index += 1
    return index, cursor


def transform(
    raw: bytes, stage: Stage, sources: dict[str, bytes | None]
) -> dict[str, bytes]:
    """Apply authenticated unified diffs in memory with no fuzz or extra paths.

    Returns:
        The authenticated replacement bytes by path.

    Raises:
        TypeError: If a narrowed value has an unexpected type.

    """
    check_bytes(raw, stage.patch_sha256, stage.patch)
    lines = raw.decode("utf-8").splitlines(keepends=True)
    changes = {item.path: item for item in stage.files}
    result: dict[str, bytes] = {}
    index = 0
    while index < len(lines):
        require(condition=index + 1 < len(lines), message="Truncated patch header")
        old = patch_path(lines[index], "--- ", stage.strip_components)
        new = patch_path(lines[index + 1], "+++ ", stage.strip_components)
        require(
            condition=new is not None and new in changes and new not in result,
            message="Unexpected patched path",
        )
        if new is None:
            raise TypeError
        change = changes[new]
        require(
            condition=old == (None if change.before is None else new),
            message="Unexpected original path",
        )
        original = sources[new]
        check_bytes(original, change.before, new)
        source = (
            []
            if original is None
            else original.decode("utf-8").splitlines(keepends=True)
        )
        output: list[str] = []
        cursor = 0
        index += 2
        hunks = 0
        while index < len(lines) and lines[index].startswith("@@ "):
            index, cursor = apply_hunk(lines, index, source, cursor, output)
            hunks += 1
        require(condition=hunks > 0, message="Patch has no hunks")
        output.extend(source[cursor:])
        replacement = "".join(output).encode("utf-8")
        check_bytes(replacement, change.after, new)
        result[new] = replacement
    require(
        condition=set(result) == set(changes),
        message="Patch does not cover declared stage",
    )
    return result


def bundle_sources(bundle: Path, plan: Plan) -> dict[str, bytes | None]:
    """Authenticate vendored originals and reconstruct the full chain in memory.

    Returns:
        The reconstructed final sources by path.

    Raises:
        TypeError: If a narrowed value has an unexpected type.

    """
    sources: dict[str, bytes | None] = {}
    for item in plan.files:
        raw = (
            None
            if item.original_file is None
            else read_source(bundle, item.original_file)
        )
        check_bytes(raw, item.original, item.path)
        sources[item.path] = raw
    for stage in plan.stages:
        patch = read_source(bundle, stage.patch)
        require(condition=patch is not None, message="Missing patch")
        if patch is None:
            raise TypeError
        sources.update(transform(patch, stage, sources))
    for item in plan.files:
        check_bytes(sources[item.path], item.final, item.path)
    return sources


def verify_tree(root: Path, plan: Plan, *, final: bool) -> None:
    """Verify every declared source path, including required original absence."""
    for item in plan.files:
        check_bytes(
            read_source(root, item.path),
            item.final if final else item.original,
            item.path,
        )


def canonical_directory(value: str) -> Path:
    """Require an existing absolute canonical directory.

    Returns:
        The validated directory path.

    """
    path = Path(value)
    require(
        condition=path.is_absolute() and path.resolve() == path and path.is_dir(),
        message="Directory must be absolute, canonical and existing",
    )
    return path


def main() -> None:
    """Check the bundle, create a source overlay or verify installed sources.

    Overlay mode exclusively creates a new destination directory. Failed
    publication leaves the owned partial tree in place for disposal.

    Raises:
        ChainError: If a required validation condition fails.
        TypeError: If a narrowed value has an unexpected type.

    """
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bundle", required=True, type=canonical_directory)
    parser.add_argument("--manifest-sha256", required=True)
    parser.add_argument("--image", required=True)
    parser.add_argument(
        "--mode",
        required=True,
        choices=("audit", "overlay", "original", "final"),
    )
    parser.add_argument("--root", type=Path)
    parser.add_argument(
        "--exclusive-build-tree",
        action="store_true",
        help="acknowledge exclusive ownership of a disposable build tree",
    )
    args = parser.parse_args()
    require(
        condition=args.exclusive_build_tree == (args.mode == "overlay"),
        message="Exclusive build tree acknowledgement required only for overlay",
    )
    bundle = args.bundle
    root = args.root
    if not isinstance(bundle, Path):
        message = "Bundle must be a path"
        raise TypeError(message)
    if root is not None and not isinstance(root, Path):
        message = "Root must be a path"
        raise TypeError(message)
    raw = read_source(bundle, "qualification/manifest.json")
    expected = digest(args.manifest_sha256)
    check_bytes(raw, expected, "qualification manifest")
    if raw is None:
        message = "Missing qualification manifest"
        raise ChainError(message)
    plan = Plan.parse(raw)
    require(
        condition=args.image == plan.image,
        message="Configured image does not match source image",
    )
    final_sources = bundle_sources(bundle, plan)
    if args.mode == "audit":
        require(condition=root is None, message="Audit does not accept a destination")
        return
    require(condition=root is not None, message="Destination root required")
    if root is None:
        raise TypeError
    if args.mode == "overlay":
        require(condition=root.is_absolute(), message="Overlay root must be absolute")
        canonical_directory(str(root.parent))
        relative_path(root.name)
    else:
        canonical_directory(str(root))
    require(
        condition=root != bundle
        and bundle not in root.parents
        and root not in bundle.parents,
        message="Source and bundle roots must be disjoint",
    )
    if args.mode == "overlay":
        with parent_fd(root.parent, root.name) as (descriptor, name):
            os.mkdir(name, dir_fd=descriptor)
        for item in plan.files:
            replacement = final_sources[item.path]
            if replacement is None:
                message = "Missing final source"
                raise ChainError(message)
            write_source(root, Transition(item.path, None, item.final), replacement)
        verify_tree(root, plan, final=True)
    else:
        verify_tree(root, plan, final=args.mode == "final")


if __name__ == "__main__":
    main()
