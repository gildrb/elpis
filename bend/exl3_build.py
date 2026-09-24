#!/usr/bin/env python3
"""Build the EXL3 Bend acceptance artifact directory on the host (CPU only).

  nix develop --offline --no-write-lock-file -c \\
    python3 bend/exl3_build.py --output build/bend-exl3

Uses the flake-pinned bend 2.0.27 and clang 19.1.7 from the dev shell PATH.
Steps, each fail-closed: proof gate of bend/exl3_accept_proof.bend; C
emission of the production program (bend/EXL3_ACCEPT.bend) and the reference
checker (bend/EXL3_ACCEPT_SPEC.bend); both compiled and run, their tables
byte-identical and equal to the pinned reference table; admission of the
emitted scalar leaf (unique signature, acyclic call closure, scalar-only
tokens, runtime polling/word ABI established); the UNCHANGED emitted C plus
bend/exl3_accept_glue.c compiled into libexl3_accept.so; identity.json; and
the complete ctypes differential admission of the resulting directory.
The output directory must not exist.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
BEND_VERSION = "bend 2.0.27\n"
CLANG_VERSION = "clang version 19.1.7"
PROOF = "bend/exl3_accept_proof.bend"
PRODUCTION = "bend/EXL3_ACCEPT.bend"
REFERENCE = "bend/EXL3_ACCEPT_SPEC.bend"
SOURCES = (
    "bend/exl3_accept.bend",
    "bend/exl3_accept_spec.bend",
    "bend/exl3_accept_laws.bend",
    "bend/exl3_accept_proof.bend",
    "bend/EXL3_ACCEPT.bend",
    "bend/EXL3_ACCEPT_SPEC.bend",
    "bend/exl3_accept_glue.c",
    "bend/exl3_bend_accept.py",
    "bend/exl3_build.py",
)
BEND_SOURCES = tuple(name for name in SOURCES if name.endswith(".bend"))
LOADER = "bend/exl3_bend_accept.py"
GLUE = "bend/exl3_accept_glue.c"
PROGRAM_FLAGS = ("-std=c11", "-O2")
LIBRARY_FLAGS = ("-std=c11", "-O2", "-fPIC", "-shared", "-fvisibility=hidden")
LINK_FLAGS = ("-lpthread", "-lm")
# The nix cc wrapper otherwise records build-shell paths as RUNPATH.
LIBRARY_ENVIRONMENT = {"NIX_DONT_SET_RPATH_x86_64_unknown_linux_gnu": "1"}
LEAF_ARGUMENTS = ("Term",) * 4 + ("u32",) * 19
RUNTIME_ABI = (
    "#define WL_SPIN     for (;;) { if (err_spun(e.mem, &wpoll)) { return 0; }",
    "#define err_seen(H)    (DEVICE && a32_load(a32_at(H, H_ERROR_CODE)) != 0)",
    "#define err_spun(H, n) ((++*(n) & 4095) == 0 && err_seen(H))",
    "#define U32_BIN(a, o, b) ((u64)((u32)(a) o (u32)(b)))",
    "#define DEVICE  0",
    "#define BANGS   0",
    "typedef u64 Term;",
    "typedef Term Nat;",
    "typedef struct {\n  Corpus   mem;\n  DEV u64* alc;\n} Env;",
)
SIGNATURE = re.compile(
    r"^INLINE Term (spin_[0-9]+)\(Env e, THR Term\* o((?:, (?:u32|Term) r[0-9]+)*)\) \{$",
    re.MULTILINE,
)
TOKEN = re.compile(
    r"\s*([A-Za-z_][A-Za-z0-9_]*|[0-9]+(?:ull)?|==|!=|>=|[-+*|=>;,()\[\]{}])"
)
KEYWORDS = frozenset(
    {"INLINE", "Term", "Env", "THR", "e", "o", "u32", "wpoll", "WL_SPIN", "U32_BIN"}
    | {"if", "else", "return", "break"}
)
LOCAL = re.compile(r"_[A-Za-z0-9_]*_(?:0|[1-9][0-9]*)|r(?:0|[1-9][0-9]*)")
UNIT = (
    "#define main litos_exl3_original_main\n"
    '#include "exl3_accept.c"\n'
    "#undef main\n"
    "#define LITOS_EXL3_LEAF {leaf}\n"
    '#include "exl3_accept_glue.c"\n'
)


def fail(message: str) -> SystemExit:
    return SystemExit(f"exl3_build: {message}")


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def run(command: list[str], cwd: Path, environment: dict[str, str]) -> str:
    result = subprocess.run(
        command, cwd=cwd, env=environment, capture_output=True, text=True, check=False
    )
    if result.returncode != 0:
        raise fail(f"{command} exited {result.returncode}: {result.stderr.strip()}")
    return result.stdout


def resolve(name: str) -> Path:
    found = shutil.which(name)
    if found is None:
        raise fail(f"{name} is not on PATH (run inside the pinned nix dev shell)")
    return Path(found)


def compile_environment(clang: Path, extra: dict[str, str]) -> dict[str, str]:
    return {"PATH": str(clang.parent), **extra}


def load_loader() -> object:
    spec = importlib.util.spec_from_file_location("exl3_bend_accept", REPO / LOADER)
    if spec is None or spec.loader is None:
        raise fail("cannot load the acceptance loader")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def functions(text: str) -> dict[str, tuple[tuple[str, ...], str]]:
    found: dict[str, tuple[tuple[str, ...], str]] = {}
    for match in SIGNATURE.finditer(text):
        closing = re.search(r"^}", text[match.end() :], re.MULTILINE)
        if closing is None:
            raise fail("incomplete emitted scalar function")
        arguments = tuple(re.findall(r", (u32|Term) r[0-9]+", match.group(2)))
        if match.group(1) in found:
            raise fail("duplicate emitted scalar function")
        body = text[match.start() : match.end() + closing.end()]
        found[match.group(1)] = (arguments, body)
    return found


def admit_leaf(text: str) -> dict[str, object]:
    """Admit the unique leaf and its acyclic scalar-only call closure."""
    for line in RUNTIME_ABI:
        if text.count(line) != 1:
            raise fail(f"emitted runtime ABI not established: {line!r}")
    table = functions(text)
    leaves = [
        name for name, (arguments, _) in table.items() if arguments == LEAF_ARGUMENTS
    ]
    if len(leaves) != 1:
        raise fail(f"expected one emitted leaf with the accept ABI, found {leaves}")
    admitted: dict[str, str] = {}
    active: set[str] = set()

    def visit(name: str) -> None:
        if name in active or name not in table:
            raise fail(f"recursive or unknown scalar callee {name}")
        if name in admitted:
            return
        active.add(name)
        body = table[name][1]
        position = 0
        while position < len(body):
            match = TOKEN.match(body, position)
            if match is None:
                if body[position:].strip():
                    raise fail(
                        f"unadmitted text in {name}: {body[position : position + 40]!r}"
                    )
                break
            token = match.group(1)
            position = match.end()
            if not (token[0].isalpha() or token[0] == "_"):
                continue
            if re.fullmatch(r"spin_(?:0|[1-9][0-9]*)", token):
                if token != name:
                    visit(token)
                continue
            if token not in KEYWORDS and LOCAL.fullmatch(token) is None:
                raise fail(f"unadmitted token {token!r} in {name}")
        active.remove(name)
        admitted[name] = digest(body.encode("utf-8"))

    visit(leaves[0])
    return {"name": leaves[0], "functions": dict(sorted(admitted.items()))}


def main(arguments: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    output = parser.parse_args(arguments).output.resolve()
    if output.exists():
        raise fail(f"{output} already exists")
    bend = resolve("bend")
    clang = resolve("clang")
    bend_environment = {**os.environ, "BEND_NO_TELEMETRY": "1"}
    if run([str(bend), "version"], REPO, bend_environment) != BEND_VERSION:
        raise fail("requires exactly bend 2.0.27")
    clang_version = run([str(clang), "--version"], REPO, compile_environment(clang, {}))
    if not clang_version.startswith(CLANG_VERSION + "\n"):
        raise fail("requires exactly clang 19.1.7")
    for name in BEND_SOURCES:
        text = (REPO / name).read_text(encoding="utf-8")
        if (
            "@unsafe" in text
            or "?TODO" in text
            or re.search(r"def [A-Za-z0-9_.]+\?\(", text)
        ):
            raise fail(f"{name} contains an unsafe definition or an open hole")
    if (
        run([str(bend), str(REPO / PROOF)], REPO, bend_environment)
        != "All terms check.\n"
    ):
        raise fail("proof gate did not report exactly 'All terms check.'")
    loader = load_loader()
    reference_sha256 = getattr(loader, "TABLE_SHA256")
    if not isinstance(reference_sha256, str):
        raise fail("loader does not pin a reference table")

    with tempfile.TemporaryDirectory(prefix="exl3-bend-build-") as scratch:
        work = Path(scratch)
        for program, source in (
            ("exl3_accept", PRODUCTION),
            ("exl3_accept_spec", REFERENCE),
        ):
            command = [str(bend), str(REPO / source), "-o", str(work / f"{program}.c")]
            run(command, REPO, bend_environment)
        tables: dict[str, str] = {}
        for program in ("exl3_accept", "exl3_accept_spec"):
            run(
                [
                    str(clang),
                    *PROGRAM_FLAGS,
                    f"{program}.c",
                    *LINK_FLAGS,
                    "-o",
                    program,
                ],
                work,
                compile_environment(clang, {}),
            )
            tables[program] = run([str(work / program), "--gpu", "off"], work, {})
        if tables["exl3_accept"] != tables["exl3_accept_spec"]:
            raise fail("production program table differs from the reference program")
        table = tables["exl3_accept_spec"].encode("ascii")
        if digest(table) != reference_sha256:
            raise fail("reference program table differs from the pinned table")
        leaf = admit_leaf((work / "exl3_accept.c").read_text(encoding="utf-8"))
        shutil.copyfile(REPO / GLUE, work / "exl3_accept_glue.c")
        (work / "unit.c").write_text(UNIT.format(leaf=leaf["name"]), encoding="utf-8")
        run(
            [
                str(clang),
                *LIBRARY_FLAGS,
                "unit.c",
                *LINK_FLAGS,
                "-o",
                "libexl3_accept.so",
            ],
            work,
            compile_environment(clang, LIBRARY_ENVIRONMENT),
        )
        staging = work / "artifact"
        staging.mkdir()
        shutil.copyfile(work / "libexl3_accept.so", staging / "libexl3_accept.so")
        (staging / "exl3_accept_table.txt").write_bytes(table)
        shutil.copyfile(REPO / LOADER, staging / "exl3_bend_accept.py")
        artifacts = {
            path.name: digest(path.read_bytes()) for path in sorted(staging.iterdir())
        }
        identity: dict[str, object] = {
            "schema": "litos-exl3-bend-accept/1",
            "bend_version": BEND_VERSION.strip(),
            "toolchain": {
                "bend": str(bend.resolve()),
                "bend_sha256": digest(bend.resolve().read_bytes()),
                "clang": str(clang.resolve()),
                "clang_sha256": digest(clang.resolve().read_bytes()),
                "clang_version": CLANG_VERSION,
                "program_flags": [*PROGRAM_FLAGS, *LINK_FLAGS],
                "library_flags": [*LIBRARY_FLAGS, *LINK_FLAGS],
                "library_environment": LIBRARY_ENVIRONMENT,
                "emitted_sha256": {
                    name: digest((work / name).read_bytes())
                    for name in ("exl3_accept.c", "exl3_accept_spec.c", "unit.c")
                },
            },
            "sources": {name: digest((REPO / name).read_bytes()) for name in SOURCES},
            "leaf": leaf,
            "artifacts": artifacts,
            "table_sha256": reference_sha256,
        }
        identity["identity_sha256"] = digest(
            json.dumps(identity, sort_keys=True, separators=(",", ":")).encode("utf-8")
        )
        (staging / "identity.json").write_text(
            json.dumps(identity, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
        admit = getattr(loader, "admit")
        admit(staging)
        shutil.copytree(staging, output)
    files = {path.name: digest(path.read_bytes()) for path in sorted(output.iterdir())}
    print(
        json.dumps({"output": str(output), "sha256": files}, indent=2, sort_keys=True)
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
