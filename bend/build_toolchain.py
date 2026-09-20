#!/usr/bin/env python3
"""Package the selected Bend 2.0.20 release without rebuilding its compiler."""

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
SELECTED_PACKAGE = "/nix/store/sd7wczd0pn674v1pxg24mgqis9z3h9ph-bend-2.0.20"
SELECTED_DERIVATION = "/nix/store/699gw2b69g9vqgfipqrx0gab5mcg5d61-bend-2.0.20.drv"
SELECTED_DERIVATION_SHA256 = (
    "5475f2e6878b80df60638fc9a8467c05e09517f0c99893fd51f47fd154e2338f"
)
SELECTED_RELEASE = (
    "/nix/store/06y8gnr26gv10skb71knmir3ijz6p20i-bend-2.0.20-linux-x64.tar.gz"
)
SELECTED_RUNTIME_SHA256 = (
    "2736371e69c65e0e519491a8165dec2de577c752e1d8779290e59c1d0781a95c"
)
COMPILER_NAMES = ("bin/bend",)


class Arguments(argparse.Namespace):
    """Typed command arguments; each command reads only its own fields."""

    command: str = ""
    release: Path = Path()
    output: Path = Path()
    provenance: Path = Path()
    toolchain: Path = Path()
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


def version(runner: Path) -> None:
    """Require the installed executable's documented version command to succeed."""
    environment = dict(os.environ, BEND_NO_TELEMETRY="1")
    require(
        "BUN_BE_BUN" not in environment,
        "BUN_BE_BUN changes release executable semantics",
    )
    result = subprocess.run(
        [str(runner), "version"],
        env=environment,
        stdin=subprocess.DEVNULL,
        capture_output=True,
        check=True,
        timeout=30,
    )
    require(
        result.stdout == VERSION.encode("utf-8") and result.stderr == b"",
        "Installed Bend is not the selected 2.0.20 release",
    )


def record(
    release: Path,
    toolchain: Path,
    provenance: Path,
    *,
    transport: Literal["release", "selected-installed", "nix-patchelf"],
    recipe: Path | None = None,
) -> None:
    """Record actual relocation output; consumers admit only observed, pinned ELF hashes."""
    original = inventory(release)
    installed = inventory(toolchain)
    require(set(installed) == set(original), "Installed release file set changed")
    resources = {
        name: value for name, value in original.items() if name not in COMPILER_NAMES
    }
    require(
        all(installed[name] == value for name, value in resources.items()),
        "Installed Base/effects/guides differ from the selected release",
    )
    runner = toolchain / "bin/bend"
    selected = transport == "selected-installed"
    if selected:
        require(
            toolchain == Path(SELECTED_PACKAGE) / "libexec/bend",
            "Only the exact selected installed Nix package is supported",
        )
        check(Path(SELECTED_DERIVATION), SELECTED_DERIVATION_SHA256)
        check(runner, SELECTED_RUNTIME_SHA256)
    elif transport == "release":
        check(runner, RUNTIME_SHA256)
    else:
        require(
            str(toolchain).startswith("/nix/store/") and recipe is not None,
            "Nix relocation requires a store output and the exact package recipe",
        )
        with runner.open("rb") as stream:
            require(
                stream.read(4) == b"\x7fELF", "Relocated Bend must remain a native ELF"
            )
    require(
        (recipe is not None) == (transport == "nix-patchelf"),
        "Relocation recipe is only valid for the reproducible Nix build",
    )
    version(runner)
    require(
        inventory(toolchain) == installed,
        "Installed release changed while recording identity",
    )
    write_json(
        provenance,
        {
            "schema": 4,
            "claim": "Selected Bend release; no compiler reconstruction, rebundling, or checker patches",
            "release": {
                "url": RELEASE_URL,
                "sha256": RELEASE_SHA256,
                "version": VERSION.rstrip("\n"),
            },
            "build_helper_sha256": digest(Path(__file__)),
            "release_resources_sha256": resources,
            "runtime": {
                "release_executable_sha256": RUNTIME_SHA256,
                "packaged_executable_sha256": installed["bin/bend"],
                "transport": transport,
                "relocation_recipe_sha256": digest(recipe)
                if recipe is not None
                else None,
                "selected_package": SELECTED_PACKAGE if selected else None,
                "selected_derivation": SELECTED_DERIVATION if selected else None,
                "selected_derivation_sha256": SELECTED_DERIVATION_SHA256
                if selected
                else None,
                "selected_release": SELECTED_RELEASE if selected else None,
            },
            "execution": {
                "mode": "release",
                "command_prefix": ["bin/bend"],
                "environment": {"BEND_NO_TELEMETRY": "1"},
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
        release = release_tree(args.release.resolve(), Path(temporary))
        _ = shutil.copytree(release, output)
        require(
            inventory(output) == inventory(release),
            "Packaging changed the release bytes",
        )
        if not args.nix_relocation:
            record(release, output, provenance, transport="release")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    builder = commands.add_parser("build")
    for name in ("release", "output", "provenance"):
        _ = builder.add_argument(name, type=Path)
    _ = builder.add_argument(
        "--nix-relocation",
        action="store_true",
        help="Defer native version/provenance until Nix has relocated the ELF",
    )
    installed = commands.add_parser(
        "record-installed", help="Record only the exact selected package"
    )
    _ = installed.add_argument("provenance", type=Path)
    relocated = commands.add_parser(
        "record-relocated", help="Record the frozen Nix build's native output"
    )
    for name in ("release", "toolchain", "provenance", "recipe"):
        _ = relocated.add_argument(name, type=Path)
    args = parser.parse_args(namespace=Arguments())
    if args.command == "build":
        build(args)
    else:
        with tempfile.TemporaryDirectory(prefix="bend-release-") as temporary:
            selected = args.command == "record-installed"
            release = release_tree(
                Path(SELECTED_RELEASE) if selected else args.release.resolve(),
                Path(temporary),
            )
            if selected:
                record(
                    release,
                    Path(SELECTED_PACKAGE) / "libexec/bend",
                    args.provenance.resolve(),
                    transport="selected-installed",
                )
            else:
                record(
                    release,
                    args.toolchain.resolve(),
                    args.provenance.resolve(),
                    transport="nix-patchelf",
                    recipe=args.recipe.resolve(),
                )


if __name__ == "__main__":
    main()
