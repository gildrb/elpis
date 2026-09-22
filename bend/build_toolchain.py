#!/usr/bin/env python3
"""Package the pinned Bend 2.0.20 checker for source-mode execution.

The original release ELF executes the immutable upstream TypeScript entry
through Bun's documented BUN_BE_BUN CLI mode. One reviewed stack-safe
comparator patch (an iterative rewrite of term_compare) is applied to
bend2/bend.ts; Base, effects, guides and the other compiler modules stay
byte-identical to the pinned sources.
"""

import argparse
import hashlib
import json
import os
import shutil
import subprocess
import tarfile
import tempfile
from pathlib import Path
from typing import Literal


VERSION = "bend 2.0.20\n"
RELEASE_URL = "https://github.com/bendlang/bend/releases/download/v2.0.20/bend-2.0.20-linux-x64.tar.gz"
RELEASE_SHA256 = "dca589832e1645500ad258d27171ed6b5a30812bcc3088c9aedf437059be41e1"
RUNTIME_SHA256 = "fab9e564c578a0a15880d5fea561ac1612dba01265a5a219906b5888f3381d8c"
BASE_SHA256 = "b8c2734d45ec6b4ce70fee70ff06ef35e08fce885af8852d8eb77dbff020e946"
SOURCE_COMMIT = "a5269a6b2c5ccd6752b66df4bc6f60678b4f49bc"
SOURCE_URL = f"https://codeload.github.com/bendlang/bend/tar.gz/{SOURCE_COMMIT}"
SOURCE_SHA256 = "f2949ac7a1fc83ccdb7e42801c74f00481207026aef8667b3c8539d358b8b13f"
UNMODIFIED_CHECKER_SHA256 = (
    "baf326d77e81c2ebe80c2bdd016c08732071a56ff951da0a67f68c26ac99e9d4"
)
PATCHED_CHECKER_SHA256 = (
    "180676f885557a6faf38acce10d48872ea3c01594f49af9139bafea2d3152ad9"
)
SOURCE_MAIN_SHA256 = "9db2123696fd8c40d0455dbf43730f51c03f1be73b02acaa570ee138be65309e"
SOURCE_COMP_SHA256 = "1cf3b5ffea86697656f8ef4d6c26040f16ac512fd92485d164f8a14425871bd0"
WRAPPER_SHA256 = "99a3a8c80a5b2906c398e2d5b7a10db3721ca745d20059042d7efe450d7cc82f"
COMPILER_NAMES = (
    "bin/bend",
    "bin/bend-runtime",
    "bend2/main.ts",
    "bend2/comp.ts",
    "bend2/bend.ts",
)
LAUNCHER = """#!/bin/sh
# Pinned source-mode launcher: the hash-pinned release ELF executes the
# retained upstream TS entry (Base, compiler sources and the reviewed
# comparator patch are pinned byte-for-byte).
set -eu
root=$(CDPATH='' cd -- "$(dirname -- "$0")/.." && pwd -P)
export BEND_NO_TELEMETRY=1 BUN_BE_BUN=1
exec "$root/bin/bend-runtime" run "$root/bend2/main.ts" "$@"
"""


class Arguments(argparse.Namespace):
    """Typed command arguments; each command reads only its own fields."""

    command: str = ""
    release: Path = Path()
    source: Path = Path()
    patch: Path = Path()
    output: Path = Path()
    provenance: Path = Path()
    recipe: Path = Path()
    nix_relocation: bool = False


def digest(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def check(path: Path, expected: str) -> None:
    require(digest(path) == expected, f"SHA256 mismatch: {path}")


def inventory(root: Path) -> dict[str, str]:
    files: dict[str, str] = {}
    for path in sorted(root.rglob("*")):
        require(not path.is_symlink(), f"Unexpected symlink: {path}")
        if path.is_file():
            files[path.relative_to(root).as_posix()] = digest(path)
    return files


def write_json(path: Path, value: dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("x", encoding="utf-8") as stream:
        _ = stream.write(json.dumps(value, indent=2, sort_keys=True) + "\n")


def release_tree(archive_path: Path, work: Path) -> Path:
    """Authenticate the complete distribution before extracting any member."""
    check(archive_path, RELEASE_SHA256)
    with tarfile.open(archive_path) as archive:
        archive.extractall(work, filter="data")
    root = work / "bend"
    check(root / "bin/bend", RUNTIME_SHA256)
    check(root / "bend2/base.bend", BASE_SHA256)
    return root


def source_tree(archive_path: Path, work: Path) -> Path:
    """Authenticate the immutable upstream source before reading any module."""
    check(archive_path, SOURCE_SHA256)
    with tarfile.open(archive_path) as archive:
        archive.extractall(work, filter="data")
    root = work / f"bend-{SOURCE_COMMIT}"
    check(root / "bend2/main.ts", SOURCE_MAIN_SHA256)
    check(root / "bend2/comp.ts", SOURCE_COMP_SHA256)
    check(root / "bend2/bend.ts", UNMODIFIED_CHECKER_SHA256)
    return root


def apply_checker_patch(source: Path, patch: Path, target: Path) -> None:
    """Apply the reviewed comparator patch and pin the exact patched bytes."""
    check(patch, "3d7b1aee163eb2fd3023be42e5a526c8eb48f1de4a5495d11950de8cd9627240")
    _ = shutil.copytree(source, target, ignore=shutil.ignore_patterns(".git"))
    result = subprocess.run(
        ["patch", "-p1", "--fuzz=3", "-i", str(patch.resolve())],
        cwd=target,
        stdin=subprocess.DEVNULL,
        capture_output=True,
        text=True,
        check=True,
        timeout=60,
    )
    require(
        "succeeded" in result.stdout and result.stderr == "",
        "Comparator patch did not apply cleanly",
    )
    check(target / "bend2/bend.ts", PATCHED_CHECKER_SHA256)


def version(runner: Path) -> None:
    """Require the packaged launcher's documented version command to succeed."""
    require(
        "BUN_BE_BUN" not in os.environ,
        "Ambient BUN_BE_BUN changes release executable semantics",
    )
    environment = dict(os.environ, BEND_NO_TELEMETRY="1")
    result = subprocess.run(
        [str(runner), "version"],
        env=environment,
        stdin=subprocess.DEVNULL,
        capture_output=True,
        check=True,
        timeout=60,
    )
    require(
        result.stdout == VERSION.encode("utf-8") and result.stderr == b"",
        "Packaged Bend is not the selected 2.0.20 source-mode checker",
    )


def assemble(release: Path, patched: Path, output: Path) -> None:
    """Lay out the source-mode toolchain; preserve release resources exactly."""
    _ = shutil.copytree(release, output)
    resources = {
        name: value
        for name, value in inventory(output).items()
        if not name.startswith("bin/")
    }
    (output / "bin/bend-runtime").write_bytes((release / "bin/bend").read_bytes())
    (output / "bin/bend").unlink()
    for name in ("main.ts", "comp.ts", "bend.ts"):
        _ = shutil.copy2(patched / "bend2" / name, output / "bend2" / name)
    (output / "bin/bend").write_text(LAUNCHER, encoding="utf-8")
    (output / "bin/bend").chmod(0o755)
    (output / "bin/bend-runtime").chmod(0o755)
    installed = inventory(output)
    require(
        all(installed.get(name) == value for name, value in resources.items()),
        "Release resources changed while assembling the toolchain",
    )


def record(
    release: Path,
    patched: Path,
    toolchain: Path,
    provenance: Path,
    *,
    patch_sha256: str,
    transport: Literal["release", "nix-patchelf"],
    recipe: Path | None = None,
) -> None:
    """Record assembled bytes; consumers admit only observed, pinned hashes."""
    original = inventory(release)
    installed = inventory(toolchain)
    require(
        set(installed) == set(original) | set(COMPILER_NAMES),
        "Installed toolchain file set is not the pinned source-mode layout",
    )
    resources = {name: value for name, value in original.items() if name != "bin/bend"}
    require(
        all(installed[name] == value for name, value in resources.items()),
        "Installed Base/effects/guides differ from the selected release",
    )
    runner = toolchain / "bin/bend"
    require(
        (recipe is not None) == (transport == "nix-patchelf"),
        "Relocation recipe is only valid for the reproducible Nix build",
    )
    version(runner)
    require(
        inventory(toolchain) == installed,
        "Installed toolchain changed while recording identity",
    )
    write_json(
        provenance,
        {
            "schema": 5,
            "claim": (
                "Pinned Bend 2.0.20 release ELF executes the pinned upstream "
                "source through BUN_BE_BUN source mode; one reviewed stack-safe "
                "comparator patch replaces term_compare; Base and effects are "
                "unmodified release bytes"
            ),
            "release": {
                "url": RELEASE_URL,
                "sha256": RELEASE_SHA256,
                "version": VERSION.rstrip("\n"),
            },
            "source": {
                "url": SOURCE_URL,
                "sha256": SOURCE_SHA256,
                "commit": SOURCE_COMMIT,
            },
            "checker": {
                "unmodified_bend_ts_sha256": UNMODIFIED_CHECKER_SHA256,
                "patch_sha256": patch_sha256,
                "patched_bend_ts_sha256": PATCHED_CHECKER_SHA256,
                "main_ts_sha256": SOURCE_MAIN_SHA256,
                "comp_ts_sha256": SOURCE_COMP_SHA256,
                "launcher_sha256": WRAPPER_SHA256,
            },
            "base_bend_sha256": BASE_SHA256,
            "build_helper_sha256": digest(Path(__file__)),
            "release_resources_sha256": resources,
            "runtime": {
                "release_executable_sha256": RUNTIME_SHA256,
                "packaged_executable_sha256": installed["bin/bend-runtime"],
                "transport": transport,
                "relocation_recipe_sha256": digest(recipe)
                if recipe is not None
                else None,
            },
            "execution": {
                "mode": "source",
                "command_prefix": ["bin/bend"],
                "interpreter": "bin/bend-runtime",
                "environment": {"BEND_NO_TELEMETRY": "1", "BUN_BE_BUN": "1"},
            },
            "installed_compiler_sha256": {
                name: installed[name] for name in COMPILER_NAMES
            },
        },
    )


def build(args: Arguments) -> None:
    output = args.output.resolve()
    provenance = args.provenance.resolve()
    require(not output.exists(), f"Output already exists: {output}")
    require(not provenance.exists(), f"Provenance already exists: {provenance}")
    require(
        not provenance.is_relative_to(output),
        "Keep provenance outside the compiler tree",
    )
    with tempfile.TemporaryDirectory(prefix="bend-source-mode-") as temporary:
        work = Path(temporary)
        release = release_tree(args.release.resolve(), work / "release")
        source = source_tree(args.source.resolve(), work / "source")
        patched = work / "patched"
        apply_checker_patch(source, args.patch.resolve(), patched)
        assemble(release, patched, output)
        if not args.nix_relocation:
            record(
                release,
                patched,
                output,
                provenance,
                patch_sha256=digest(args.patch.resolve()),
                transport="release",
            )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    builder = commands.add_parser("build")
    for name in ("release", "source", "patch", "output", "provenance"):
        _ = builder.add_argument(name, type=Path)
    _ = builder.add_argument(
        "--nix-relocation",
        action="store_true",
        help="Defer native version/provenance until Nix has relocated the ELF",
    )
    relocated = commands.add_parser(
        "record-relocated", help="Record the frozen Nix build's native output"
    )
    for name in ("release", "source", "patch", "toolchain", "provenance", "recipe"):
        _ = relocated.add_argument(name, type=Path)
    args = parser.parse_args(namespace=Arguments())
    if args.command == "build":
        build(args)
    else:
        with tempfile.TemporaryDirectory(prefix="bend-source-mode-") as temporary:
            work = Path(temporary)
            release = release_tree(args.release.resolve(), work / "release")
            source = source_tree(args.source.resolve(), work / "source")
            patched = work / "patched"
            apply_checker_patch(source, args.patch.resolve(), patched)
            record(
                release,
                patched,
                args.toolchain.resolve(),
                args.provenance.resolve(),
                patch_sha256=digest(args.patch.resolve()),
                transport="nix-patchelf",
                recipe=args.recipe.resolve(),
            )


if __name__ == "__main__":
    main()
