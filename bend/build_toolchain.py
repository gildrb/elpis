#!/usr/bin/env python3
"""Package the unmodified, pinned Bend 2.0.29 release checker and compiler.

The release ELF and resources stay byte-identical to upstream except for
Nix ELF relocation. A small launcher supplies the OS and JavaScriptCore
stack limits required by the project proofs; it never changes the checker.
The matching immutable source archive is authenticated for provenance.
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


VERSION = "bend 2.0.29\n"
RELEASE_URL = "https://github.com/bendlang/bend/releases/download/v2.0.29/bend-2.0.29-linux-x64.tar.gz"
RELEASE_SHA256 = "e0ff4fa44581b42f6024d2a1128e7e518219a502cb726030c714a5c23d61726e"
RUNTIME_SHA256 = "2aabe5cc340203fe3f873a41f2c67445c6734d24456cfa174e9efe2ee13dcea6"
BASE_SHA256 = "22eea83911e2395f63594fea7c10ac0c1e5b548251681fc97cd7667e0eb7031b"
SOURCE_COMMIT = "c8691aa93b0b1bb2fda277d9fc88c5aa797e88de"
SOURCE_URL = f"https://codeload.github.com/bendlang/bend/tar.gz/{SOURCE_COMMIT}"
SOURCE_SHA256 = "1e5006bff6cdf9f03b2e60f33c45ed1d91fa9dbbd633466c9f22e48880f9351a"
UNMODIFIED_CHECKER_SHA256 = (
    "09d2cc5c5d757f1a694dd126ccbac72ef2374cfe948d9d51c2b08247c5d2581e"
)
SOURCE_MAIN_SHA256 = "0a6c19ee942ec4fadcf7daaa69ca1cfd395a5ee8ef130df72b548291def93884"
SOURCE_COMP_SHA256 = "0cf866b28ff273d47970b3c16e82288e9676ce9f0ea3fce49877a82ce4a6301b"
WRAPPER_SHA256 = "437f2f10c027d4b1a68d86b08d372a0bc32786b2304b658b5d07eefb79de437d"
COMPILER_NAMES = ("bin/bend", "bin/bend-runtime")
LAUNCHER = """#!/bin/sh
# The unmodified release checker needs explicit OS and JavaScriptCore stacks.
set -eu
if [ -n "${BUN_BE_BUN:-}" ]; then
  echo 'BUN_BE_BUN changes release executable semantics' >&2
  exit 1
fi
root=$(CDPATH='' cd -- "$(dirname -- "$0")/.." && pwd -P)
ulimit -s 1048576
export BEND_NO_TELEMETRY=1 BUN_JSC_maxPerThreadStackUsage=536870912
exec "$root/bin/bend-runtime" "$@"
"""


class Arguments(argparse.Namespace):
    """Typed command arguments; each command reads only its own fields."""

    command: str = ""
    release: Path = Path()
    source: Path = Path()
    output: Path = Path()
    provenance: Path = Path()
    recipe: Path = Path()
    toolchain: Path = Path()
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


def version(runner: Path) -> None:
    """Require the packaged launcher's documented version command to succeed."""
    require(
        not os.environ.get("BUN_BE_BUN"),
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
        "Packaged Bend is not the selected 2.0.29 release checker",
    )


def assemble(release: Path, output: Path) -> None:
    """Wrap the release runtime without modifying its checker or resources."""
    _ = shutil.copytree(release, output)
    _ = (output / "bin/bend").rename(output / "bin/bend-runtime")
    _ = (output / "bin/bend").write_text(LAUNCHER, encoding="utf-8")
    (output / "bin/bend").chmod(0o755)
    (output / "bin/bend-runtime").chmod(0o755)


def record(
    release: Path,
    toolchain: Path,
    provenance: Path,
    *,
    transport: Literal["release", "nix-patchelf"],
    recipe: Path | None = None,
) -> None:
    """Record assembled bytes; consumers admit only observed, pinned hashes."""
    original = inventory(release)
    installed = inventory(toolchain)
    require(
        set(installed) == set(original) | set(COMPILER_NAMES),
        "Installed toolchain file set is not the pinned release layout",
    )
    resources = {name: value for name, value in original.items() if name != "bin/bend"}
    require(
        all(installed[name] == value for name, value in resources.items()),
        "Installed Base/effects/guides differ from the selected release",
    )
    check(toolchain / "bin/bend", WRAPPER_SHA256)
    if transport == "release":
        check(toolchain / "bin/bend-runtime", RUNTIME_SHA256)
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
            "schema": 6,
            "claim": (
                "Pinned, unmodified Bend 2.0.29 release checker/compiler and "
                "Base; launcher configures OS and JavaScriptCore stack limits; "
                "matching upstream source is authenticated without patching"
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
                "mode": "release",
                "command_prefix": ["bin/bend"],
                "interpreter": "bin/bend-runtime",
                "environment": {
                    "BEND_NO_TELEMETRY": "1",
                    "BUN_JSC_maxPerThreadStackUsage": "536870912",
                },
                "stack_limit_bytes": 1073741824,
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
    with tempfile.TemporaryDirectory(prefix="bend-release-") as temporary:
        work = Path(temporary)
        release = release_tree(args.release.resolve(), work / "release")
        _ = source_tree(args.source.resolve(), work / "source")
        assemble(release, output)
        if not args.nix_relocation:
            record(
                release,
                output,
                provenance,
                transport="release",
            )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    builder = commands.add_parser("build")
    for name in ("release", "source", "output", "provenance"):
        _ = builder.add_argument(name, type=Path)
    _ = builder.add_argument(
        "--nix-relocation",
        action="store_true",
        help="Defer native version/provenance until Nix has relocated the ELF",
    )
    relocated = commands.add_parser(
        "record-relocated", help="Record the frozen Nix build's native output"
    )
    for name in ("release", "source", "toolchain", "provenance", "recipe"):
        _ = relocated.add_argument(name, type=Path)
    args = parser.parse_args(namespace=Arguments())
    if args.command == "build":
        build(args)
    else:
        with tempfile.TemporaryDirectory(prefix="bend-release-") as temporary:
            work = Path(temporary)
            release = release_tree(args.release.resolve(), work / "release")
            _ = source_tree(args.source.resolve(), work / "source")
            record(
                release,
                args.toolchain.resolve(),
                args.provenance.resolve(),
                transport="nix-patchelf",
                recipe=args.recipe.resolve(),
            )


if __name__ == "__main__":
    main()
