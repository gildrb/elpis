"""Rebuild the pinned exllamav3_ext CUDA extension and record it, fail closed.

Run at image build time by Dockerfile.exl3 from a copy of the repository's
patches/ directory (this tool imports the strict patch rules of
patches/exl3/apply.py):

    python -I -B ext.py prepare <rebuilt|patched> <build-root>
    python -I -B ext.py compose <rebuilt|patched> <shared-object>
    python -I -B ext.py record <rebuilt|patched> <engine-manifest>

prepare checks the installed engine against exl3-ext.json: the package root, the
SHA-256 listing of the whole compiled source tree, and the vendored upstream
setup.py. For `patched` it then checks the series, every patch and every pre-image,
applies the series in place with the strict hunk rules of patches/exl3/apply.py,
and requires every post-image. Finally it lays out <build-root> like the upstream
checkout (setup.py plus exllamav3/exllamav3_ext) for the compiler.

compose prints the image's engine manifest: the patches/exl3 manifest with its
per-file closure extended by the extension's patched files, schema 2, plus an
`extension` record naming the variant, source and toolchain pins, the series and
the SHA-256 of the built shared object.

record recomposes that manifest from the installed shared object, requires the
installed manifest to be patches/exl3's, rehashes every recorded file and the
acceptance artifact, and replaces <engine-manifest>.
"""

from __future__ import annotations

import hashlib
import importlib.util
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from patches.exl3.apply import (
    MANIFEST_KEYS,
    SERIES_LINE,
    apply_file,
    check_acceptor,
    check_files,
    digest,
    fail,
    parse_patch,
    pinned,
    require,
    safe_relative,
    text_value,
)

EXT_DIR = Path(__file__).resolve().parent
EXL3_DIR = EXT_DIR.parent / "exl3"
KEYS = {
    "schema",
    "source",
    "toolchain",
    "extension",
    "series_sha256",
    "patches",
    "files",
}
SOURCE_KEYS = {"revision", "root", "tree", "tree_sha256", "setup_py", "setup_py_sha256"}
VARIANTS = ("rebuilt", "patched")


def mapping(value: object, label: str) -> dict[str, object]:
    """Require a JSON object with string keys.

    Returns:
        The validated object.
    """
    if not isinstance(value, dict) or not all(isinstance(key, str) for key in value):
        fail(f"{label} is not an object")
    return {str(key): item for key, item in value.items()}


def load() -> dict[str, object]:
    """Read and shape-check the extension manifest.

    Returns:
        The manifest.
    """
    manifest = mapping(json.loads((EXT_DIR / "exl3-ext.json").read_bytes()), "manifest")
    require(set(manifest) == KEYS, "bad extension manifest keys")
    require(manifest["schema"] == 1, "unsupported extension manifest schema")
    require(
        set(mapping(manifest["source"], "source")) == SOURCE_KEYS,
        "bad extension source record",
    )
    return manifest


def tree_digest(root: Path) -> str:
    """Hash a source tree as sorted `<sha256>  <relative path>` lines.

    Returns:
        The lowercase hex SHA-256 of the listing.
    """
    lines: list[str] = []
    for path in sorted(root.rglob("*")):
        relative = path.relative_to(root)
        if "__pycache__" in relative.parts:
            continue
        require(not path.is_symlink(), f"symlink in source tree: {relative}")
        if path.is_file():
            lines.append(f"{digest(path)}  {relative.as_posix()}\n")
    require(bool(lines), f"empty source tree {root}")
    return hashlib.sha256("".join(lines).encode()).hexdigest()


def engine_root(source: dict[str, object]) -> Path:
    """Match the installed engine package to the manifest.

    Returns:
        The engine package root.
    """
    root = Path(text_value(source["root"], "source root"))
    spec = importlib.util.find_spec("exllamav3")
    require(
        spec is not None
        and spec.origin is not None
        and Path(spec.origin).parent == root,
        "installed engine root differs from the extension manifest",
    )
    return root


def series(manifest: dict[str, object]) -> list[tuple[str, str]]:
    """Match the series file to the manifest's pinned patch list.

    Returns:
        (patch name, sha256) in application order.
    """
    path = EXT_DIR / "series"
    require(
        digest(path) == pinned(manifest["series_sha256"], "series_sha256"),
        "extension series hash mismatch",
    )
    entries: list[tuple[str, str]] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        match = SERIES_LINE.match(line)
        if match is None:
            fail(f"malformed extension series line {line!r}")
        entries.append((match.group(2), match.group(1)))
    require(
        manifest["patches"] == [{"name": n, "sha256": s} for n, s in entries],
        "extension series differs from the manifest",
    )
    return entries


def apply_series(manifest: dict[str, object], root: Path) -> None:
    """Apply the pinned series in place between pre- and post-image checks."""
    entries = series(manifest)
    require(bool(entries), "patched variant needs a nonempty series")
    pins = check_files(manifest)
    for relative, (pre, _) in pins.items():
        if pre is None:
            require(not (root / relative).exists(), f"{relative} exists before its patch")
        else:
            require(digest(root / relative) == pre, f"pre-image mismatch: {relative}")
    touched: set[str] = set()
    for name, sha in entries:
        path = EXT_DIR / name
        require(digest(path) == sha, f"patch hash mismatch: {name}")
        for relative, creates, hunks in parse_patch(path.read_text(encoding="utf-8")):
            require(relative in pins, f"patch touches unpinned file {relative}")
            require(
                creates == (pins[relative][0] is None and relative not in touched),
                f"file creation disagrees with the manifest: {relative}",
            )
            apply_file(root / relative, creates=creates, hunks=hunks)
            touched.add(relative)
    require(touched == set(pins), "manifest pins files no patch touches")
    for relative, (_, post) in pins.items():
        require(digest(root / relative) == post, f"post-image mismatch: {relative}")


def prepare(variant: str, build: Path) -> None:
    """Verify the compiled sources, apply the series if patched, lay out the build."""
    manifest = load()
    source = mapping(manifest["source"], "source")
    root = engine_root(source)
    tree = safe_relative(text_value(source["tree"], "source tree"))
    require(
        tree_digest(root / tree) == pinned(source["tree_sha256"], "tree_sha256"),
        "installed extension sources differ from the pinned upstream tree",
    )
    setup_py = EXT_DIR / safe_relative(text_value(source["setup_py"], "setup.py"))
    require(
        digest(setup_py) == pinned(source["setup_py_sha256"], "setup_py_sha256"),
        "vendored setup.py differs from its pin",
    )
    extension = mapping(manifest["extension"], "extension")
    require(
        digest(Path(text_value(extension["path"], "extension path")))
        == pinned(extension["base_sha256"], "base_sha256"),
        "installed extension differs from the pinned base build",
    )
    if variant == "patched":
        apply_series(manifest, root)
    require(not build.exists(), f"{build} already exists")
    (build / "exllamav3" / tree).mkdir(parents=True)
    _ = (build / "setup.py").write_bytes(setup_py.read_bytes())
    for path in sorted((root / tree).rglob("*")):
        relative = path.relative_to(root)
        if "__pycache__" in relative.parts:
            continue
        destination = build / "exllamav3" / relative
        if path.is_dir():
            destination.mkdir()
        else:
            _ = destination.write_bytes(path.read_bytes())
    print(f"Prepared {variant} exllamav3_ext sources at {build}")


def compose(variant: str, so_sha256: str) -> bytes:
    """Build the image's engine manifest.

    Returns:
        The canonical JSON bytes.
    """
    manifest = load()
    source = mapping(manifest["source"], "source")
    engine = mapping(json.loads((EXL3_DIR / "exl3-patches.json").read_bytes()), "m")
    require(set(engine) == MANIFEST_KEYS, "bad patches/exl3 manifest keys")
    require(engine["schema"] == 1, "unsupported patches/exl3 manifest schema")
    require(
        mapping(engine["engine"], "engine")["root"] == source["root"],
        "extension and engine manifests name different package roots",
    )
    files = {
        name: mapping(record, name)
        for name, record in mapping(engine["files"], "files").items()
    }
    record: dict[str, object] = {
        "variant": variant,
        "source": source,
        "toolchain": mapping(manifest["toolchain"], "toolchain"),
        "shared_object": {
            **mapping(manifest["extension"], "extension"),
            "sha256": pinned(so_sha256, "built extension sha256"),
        },
        "series_sha256": None,
        "patches": [],
        "files": {},
    }
    if variant == "patched":
        _ = series(manifest)
        for name, (pre, post) in check_files(manifest).items():
            earlier = files.get(name)
            require(
                earlier is None or earlier["post"] == pre,
                f"extension pre-image of {name} is not the engine post-image",
            )
            files[name] = {
                "pre": pre if earlier is None else earlier["pre"],
                "post": post,
            }
        record["series_sha256"] = manifest["series_sha256"]
        record["patches"] = manifest["patches"]
        record["files"] = manifest["files"]
    document = {**engine, "schema": 2, "files": files, "extension": record}
    return (json.dumps(document, indent=2, sort_keys=True) + "\n").encode()


def record(variant: str, out: Path) -> None:
    """Replace the installed engine manifest after rehashing everything it names."""
    extension = mapping(load()["extension"], "extension")
    so = Path(text_value(extension["path"], "extension path"))
    document = compose(variant, digest(so))
    require(
        out.read_bytes() == (EXL3_DIR / "exl3-patches.json").read_bytes(),
        "installed engine manifest is not the patches/exl3 manifest",
    )
    parsed = mapping(json.loads(document), "document")
    root = Path(text_value(mapping(parsed["engine"], "engine")["root"], "root"))
    for name, value in mapping(parsed["files"], "files").items():
        require(
            digest(root / safe_relative(name)) == mapping(value, name)["post"],
            f"installed engine file differs from its post-image: {name}",
        )
    check_acceptor(parsed["acceptor"])
    out.unlink()
    _ = out.write_bytes(document)
    out.chmod(0o444)
    print(
        f"Recorded {variant} extension {digest(so)}; "
        f"manifest sha256 {hashlib.sha256(document).hexdigest()}"
    )


def main(argv: list[str]) -> None:
    """Dispatch one build-time step."""
    if len(argv) != 4 or argv[1] not in {"prepare", "compose", "record"}:
        fail("usage: ext.py <prepare|compose|record> <rebuilt|patched> <path>")
    command, variant, path = argv[1], argv[2], Path(argv[3])
    require(variant in VARIANTS, f"unknown extension variant {variant!r}")
    if command == "prepare":
        prepare(variant, path)
    elif command == "compose":
        _ = sys.stdout.buffer.write(compose(variant, digest(path)))
    else:
        record(variant, path)


if __name__ == "__main__":
    main(sys.argv)
