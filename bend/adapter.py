#!/usr/bin/env python3
"""Check Bend 2.0.20 proofs and retain four CPU serving-policy programs.

  python3 bend/adapter.py generate --output /tmp/qwen-bend --bend /path/to/bend
  python3 bend/adapter.py compile --directory /tmp/qwen-bend --cc clang-19
  python3 bend/adapter.py verify --directory /tmp/qwen-bend
  python3 bend/adapter.py check --directory /tmp/qwen-bend \
      --context 262144 --pool 263168 --page-size 128

Generation checks the actual root PROOF.bend, then emits C from bend/PLAN.bend,
bend/SELECT.bend, bend/SPECULATE.bend and bend/RUNTIME.bend. Compilation happens
in the target runtime. Serving loads the planner, greedy speculation table and
mirror action tables once per startup; qualification loads the objective table once.
Retained hashes bind artifacts, not their trustworthiness: Bend's checker/compiler,
Base intrinsics, foreign IO, clang and the host runtime remain trusted. The checker
runs the pinned upstream 2.0.20 TypeScript with one reviewed stack-safe comparator
patch through the release ELF's BUN_BE_BUN source mode. This
is not a CUDA/F32, capacity, quality, or compiler-correctness proof. Engine
allocation validators remain mandatory.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
from collections.abc import Iterable
from dataclasses import dataclass
from itertools import pairwise
from pathlib import Path
from typing import Literal, NoReturn, TypeAlias, TypeGuard

SOURCE_NAMES = (
    "LAWS.bend",
    "PROOF.bend",
    "bend/range.bend",
    "bend/spec.bend",
    "bend/control.bend",
    "bend/PLAN.bend",
    "bend/objectives.bend",
    "bend/selection.bend",
    "bend/selection_laws.bend",
    "bend/selection_proof.bend",
    "bend/SELECT.bend",
    "bend/speculation.bend",
    "bend/speculation_spec.bend",
    "bend/speculation_laws.bend",
    "bend/speculation_proof.bend",
    "bend/SPECULATE.bend",
    "bend/transaction_spec.bend",
    "bend/transaction.bend",
    "bend/transaction_laws.bend",
    "bend/transaction_proof.bend",
    "bend/ownership_spec.bend",
    "bend/ownership.bend",
    "bend/ownership_laws.bend",
    "bend/ownership_proof.bend",
    "bend/numerical_spec.bend",
    "bend/numerical.bend",
    "bend/numerical_laws.bend",
    "bend/numerical_proof.bend",
    "bend/abi_spec.bend",
    "bend/abi.bend",
    "bend/abi_laws.bend",
    "bend/abi_proof.bend",
    "bend/RUNTIME.bend",
    "bend/adapter.py",
    "bend/native_build.py",
    "bend/native.py",
    "bend/native.cu",
)
OFFSET_NAMES = (
    "k_packed",
    "k_scale",
    "k_zero",
    "k_token",
    "v_packed",
    "v_channel",
    "v_scale",
    "v_zero",
    "end",
)
FIELDS = (
    "context",
    "headroom",
    "pool",
    "page_size",
    "pages",
    "tail_slots",
    "write_tokens",
    "query_tokens",
    "commit_tokens",
    "write_span_pages",
    "admission_free_slots",
    "target_visible",
    "draft_window",
    "draft_visible",
    "target_dim",
    "target_kv_heads",
    "target_layers",
    "draft_dim",
    "draft_kv_heads",
    "draft_layers",
) + tuple(f"{role}_{name}" for role in ("target", "draft") for name in OFFSET_NAMES)
Plan: TypeAlias = dict[str, int | list[int]]
ObjectiveFamily: TypeAlias = Literal["quality", "throughput", "first_token", "energy"]
ObjectiveOrder: TypeAlias = Literal["better", "same", "worse", "missing"]
ObjectiveRelation: TypeAlias = Literal[
    "no_objectives",
    "equivalent",
    "dominates",
    "dominated",
    "tradeoff",
    "incomplete",
]
OBJECTIVE_FAMILIES: tuple[ObjectiveFamily, ...] = (
    "quality",
    "throughput",
    "first_token",
    "energy",
)
OBJECTIVE_ORDERS: tuple[ObjectiveOrder, ...] = ("better", "same", "worse", "missing")
OBJECTIVE_RELATIONS: tuple[ObjectiveRelation, ...] = (
    "no_objectives",
    "equivalent",
    "dominates",
    "dominated",
    "tradeoff",
    "incomplete",
)
POLICY_HEADER = "QWEN_OBJECTIVE_POLICY_V1\nROLES\n"
POLICY_END = "END_QWEN_OBJECTIVE_POLICY\n"
SPECULATION_HEADER = "QWEN_DFLASH_GREEDY_V1\n8\n128\n4\n"
SPECULATION_END = "END_QWEN_DFLASH_GREEDY\n"
RUNTIME_HEADER = "QWEN_RUNTIME_CONTROL_V1\nFREE_MIRROR\n8\n"
RUNTIME_END = "END_QWEN_RUNTIME_CONTROL\n"
U32_MAX = (1 << 32) - 1
HEADER = "QWEN_KVARN_PLAN_V2\n"
FREE = "FREE_PAGES\n"
END = "END_QWEN_KVARN_PLAN\n"
BEND_VERSION = "bend 2.0.20\n"
PROOF_DIAGNOSTIC = "All terms check.\n"
BEND_COMMAND = "./compiler/bin/bend"
COMPILER_FILES = {
    "bin/bend",
    "bin/bend-runtime",
    "bend2/main.ts",
    "bend2/comp.ts",
    "bend2/bend.ts",
}
BASE_SHA256 = "b8c2734d45ec6b4ce70fee70ff06ef35e08fce885af8852d8eb77dbff020e946"
RELEASE_RUNTIME_SHA256 = (
    "fab9e564c578a0a15880d5fea561ac1612dba01265a5a219906b5888f3381d8c"
)
SELECTED_RUNTIME_SHA256 = (
    "2736371e69c65e0e519491a8165dec2de577c752e1d8779290e59c1d0781a95c"
)
NATIVE_RUNTIME_SHA256 = (
    RELEASE_RUNTIME_SHA256,
    SELECTED_RUNTIME_SHA256,
    "e38cda9ed7c2066a9d3335dd599bb2bcf7d3e5871b8ed0f2a789fbea2e57eb0d",
)
# Source-mode checker identity: immutable upstream 2.0.20 TS plus the reviewed
# stack-safe comparator patch; the release ELF only interprets the entry.
WRAPPER_SHA256 = "99a3a8c80a5b2906c398e2d5b7a10db3721ca745d20059042d7efe450d7cc82f"
SOURCE_MAIN_SHA256 = "9db2123696fd8c40d0455dbf43730f51c03f1be73b02acaa570ee138be65309e"
SOURCE_COMP_SHA256 = "1cf3b5ffea86697656f8ef4d6c26040f16ac512fd92485d164f8a14425871bd0"
PATCHED_CHECKER_SHA256 = (
    "180676f885557a6faf38acce10d48872ea3c01594f49af9139bafea2d3152ad9"
)
# Resource limits for the full proof, not compiler/checker semantic overrides.
PROOF_COMMAND = [
    "prlimit",
    "--stack=1073741824:1073741824",
    "--core=0:0",
    "--",
    BEND_COMMAND,
    "sources/PROOF.bend",
]
EMIT_COMMAND = [BEND_COMMAND, "sources/bend/PLAN.bend", "-o", "plan.c"]
POLICY_EMIT_COMMAND = [BEND_COMMAND, "sources/bend/SELECT.bend", "-o", "select.c"]
SPECULATION_EMIT_COMMAND = [
    BEND_COMMAND,
    "sources/bend/SPECULATE.bend",
    "-o",
    "speculate.c",
]
RUNTIME_EMIT_COMMAND = [BEND_COMMAND, "sources/bend/RUNTIME.bend", "-o", "runtime.c"]
PLAN_COMMAND = ["./plan", "--gpu", "off"]
POLICY_COMMAND = ["./select", "--gpu", "off"]
SPECULATION_COMMAND = ["./speculate", "--gpu", "off"]
RUNTIME_COMMAND = ["./runtime", "--gpu", "off"]
PROGRAM_NAMES = ("plan", "select", "speculate", "runtime")
EMISSIONS = (
    (EMIT_COMMAND, "plan.c", "emit.json"),
    (POLICY_EMIT_COMMAND, "select.c", "emit-policy.json"),
    (SPECULATION_EMIT_COMMAND, "speculate.c", "emit-speculation.json"),
    (RUNTIME_EMIT_COMMAND, "runtime.c", "emit-runtime.json"),
)
COMPILATIONS = (
    ("plan", "compile.json"),
    ("select", "compile-policy.json"),
    ("speculate", "compile-speculation.json"),
    ("runtime", "compile-runtime.json"),
)
GENERATION_LOGS = ("version.json", "base.json", "proof.json") + tuple(
    log for _, _, log in EMISSIONS
)
BUILD_LOGS = ("compiler-version.json",) + tuple(log for _, log in COMPILATIONS)
SCOPE = (
    "Bend2 checks the filled root PROOF.bend and its transitive local laws; "
    "the CPU planner, objective policy, greedy block8 speculation decisions and "
    "host mirror action tables are compiled from bend/PLAN.bend, bend/SELECT.bend, "
    "bend/SPECULATE.bend and bend/RUNTIME.bend. Speculation acceptance and wire "
    "equivalence are proved against an independent Bend specification. Runtime "
    "tables select native host free-mirror and status-mirror actions only. "
    "Transaction, ownership, numerical and ABI laws are abstract contracts, not "
    "proofs of native events, epochs, ownership, machine arithmetic "
    "or device addressing. "
    "The checker is the pinned upstream 2.0.20 TypeScript with one reviewed "
    "stack-safe comparator patch (iterative term_compare); the patch changes "
    "evaluation strategy, not proof semantics, and is hash-bound. "
    "Base intrinsics, foreign IO, both compilers and the host runtime are trusted, "
    "not proved. GPU completion, consumption and execution remain trusted native "
    "facts. No CUDA/F32, compiler-correctness, capacity, performance or quality claim."
)
# String/comment masking preserves token separation, including @ #comment\n unsafe.
LEXEMES = re.compile(r'"(?:\\.|[^"\\])*"|#[^\n]*|[A-Za-z_][A-Za-z0-9_.]*|[^\s]')
IMPORT = re.compile(r"import\s+(\S+)(?:\s+as\s+([A-Za-z_][A-Za-z0-9_]*))?\s*(?:#.*)?")


def fail(message: str) -> NoReturn:
    """Reject malformed, changed, unsupported or failed control artifacts."""
    raise ValueError(message)


@dataclass(frozen=True, slots=True)
class ObjectivePolicy:
    """Immutable compiled roles and state-major transitions; no host decision algebra."""

    roles: tuple[int, ...]
    transitions: tuple[int, ...]

    def __post_init__(self) -> None:
        """Reject mutable tables, wrong dimensions and invalid wire codes."""
        for values, size, maximum in ((self.roles, 4, 1), (self.transitions, 24, 5)):
            if (
                type(values) is not tuple
                or len(values) != size
                or any(
                    type(value) is not int or not 0 <= value <= maximum
                    for value in values
                )
            ):
                fail("Malformed compiled objective policy table")

    def classify(
        self, rows: Iterable[tuple[ObjectiveFamily, ObjectiveOrder]]
    ) -> ObjectiveRelation:
        """Fold observed primary coordinates through the compiled transition table."""
        state: int = 0
        for family, order in rows:
            if type(family) is not str or family not in OBJECTIVE_FAMILIES:
                fail(f"Unknown objective family: {family!r}")
            if type(order) is not str or order not in OBJECTIVE_ORDERS:
                fail(f"Unknown objective order: {order!r}")
            if self.roles[OBJECTIVE_FAMILIES.index(family)] == 0:
                state = exact_int(
                    self.transitions[
                        state * len(OBJECTIVE_ORDERS) + OBJECTIVE_ORDERS.index(order)
                    ],
                    "compiled objective state",
                )
        return OBJECTIVE_RELATIONS[state]


@dataclass(frozen=True, slots=True)
class SpeculationPolicy:
    """Immutable compiled rows: accepted drafts, committed inputs, bonus index, advance."""

    block_size: int
    decisions: tuple[tuple[int, int, int, int], ...]

    def __post_init__(self) -> None:
        """Bound the complete wire without recomputing any Bend acceptance decision."""
        if type(self.block_size) is not int or self.block_size != 8:
            fail("Unsupported compiled speculation block size")
        if type(self.decisions) is not tuple or len(self.decisions) != 128:
            fail("Malformed compiled speculation table")
        for row in self.decisions:
            if (
                type(row) is not tuple
                or len(row) != 4
                or any(type(value) is not int for value in row)
                or not 0 <= row[0] <= 7
                or not 1 <= row[1] <= 8
                or not 0 <= row[2] <= 7
                or not 1 <= row[3] <= 8
            ):
                fail("Malformed compiled speculation row")


@dataclass(frozen=True, slots=True)
class RuntimePolicy:
    """Compiled host actions; event/epoch observations remain the caller's trust boundary."""

    free_mirror: tuple[int, ...]
    status: tuple[int, ...]

    def __post_init__(self) -> None:
        """Require immutable complete tables and the two bounded action alphabets."""
        for values, maximum in ((self.free_mirror, 1), (self.status, 2)):
            if (
                type(values) is not tuple
                or len(values) != 8
                or any(
                    type(value) is not int or not 0 <= value <= maximum
                    for value in values
                )
            ):
                fail("Malformed compiled runtime action table")

    def free_action(self, pending: bool, event_ready: bool, epoch_current: bool) -> int:
        """Index pending bit0, readiness bit1, current epoch bit2; no host policy algebra."""
        if (
            type(pending) is not bool
            or type(event_ready) is not bool
            or type(epoch_current) is not bool
        ):
            fail("Runtime free-mirror observations must be exact booleans")
        return self.free_mirror[pending | (event_ready << 1) | (epoch_current << 2)]

    def status_action(self, armed: bool, event_exists: bool, event_ready: bool) -> int:
        """Index armed bit0, event existence bit1, readiness bit2."""
        if (
            type(armed) is not bool
            or type(event_exists) is not bool
            or type(event_ready) is not bool
        ):
            fail("Runtime status-mirror observations must be exact booleans")
        return self.status[armed | (event_exists << 1) | (event_ready << 2)]


def digest(path: Path) -> str:
    """Hash the actual source, compiler, log, C or executable bytes."""
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def is_object(value: object) -> TypeGuard[dict[str, object]]:
    """Narrow JSON objects without an unchecked cast."""
    if not isinstance(value, dict):
        return False
    return all(isinstance(key, str) for key in value)


def write_json(path: Path, value: object) -> None:
    """Create an artifact exclusively; failed stages cannot silently be reused."""
    with path.open("x", encoding="utf-8") as stream:
        _ = stream.write(json.dumps(value, sort_keys=True, indent=2) + "\n")


def object_file(path: Path) -> dict[str, object]:
    """Read bounded JSON, rejecting duplicate keys and non-object roots."""

    def pairs(items: list[tuple[str, object]]) -> dict[str, object]:
        result: dict[str, object] = {}
        for key, value in items:
            if key in result:
                fail(f"Duplicate identity key: {key}")
            result[key] = value
        return result

    if path.stat().st_size > 4 * 1024 * 1024:
        fail(f"Identity file too large: {path}")

    def decoded(value: object) -> dict[str, object]:
        if not is_object(value):
            fail(f"Expected identity object: {path}")
        return value

    return decoded(
        json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=pairs)
    )


def exact_int(value: object, name: str) -> int:
    """Narrow exact Nat output to the adapter's bounded unsigned-32-bit wire."""
    if (
        not isinstance(value, int)
        or isinstance(value, bool)
        or not 0 <= value <= U32_MAX
    ):
        fail(f"Expected exact bounded integer: {name}")
    return value


def executable(name: str) -> Path:
    """Resolve an explicit tool, never substitute a different compiler."""
    found = shutil.which(name)
    if found is None:
        fail(f"Required executable not found: {name}")
    return Path(found).resolve(strict=True)


def command_environment(command: list[str]) -> dict[str, str]:
    """Record the approved proof-only VM stack setting and ordinary execution environment."""
    environment = {"BEND_NO_TELEMETRY": "1"}
    if command == PROOF_COMMAND:
        environment["BUN_JSC_maxPerThreadStackUsage"] = "536870912"
    return environment


def run(
    command: list[str], *, cwd: Path, record: Path | None = None
) -> dict[str, object]:
    """Run without a shell or stdin and preserve exact bytes as UTF-8, not CRLF translation."""
    for name in os.environ:
        if name.startswith("BUN_JSC_") or name in (
            "BUN_OPTIONS",
            "NODE_OPTIONS",
            "JSC_OPTIONS",
            "BUN_BE_BUN",
        ):
            fail(
                f"Unrecorded compiler execution override in ambient environment: {name}"
            )
    recorded_environment = command_environment(command)
    environment = dict(os.environ)
    environment.update(recorded_environment)
    result = subprocess.run(
        command,
        cwd=cwd,
        env=environment,
        stdin=subprocess.DEVNULL,
        check=False,
        capture_output=True,
        timeout=300,
    )
    stdout = result.stdout.decode("utf-8", errors="strict")
    stderr = result.stderr.decode("utf-8", errors="strict")
    evidence: dict[str, object] = {
        "command": command,
        "cwd": str(cwd),
        "environment": recorded_environment,
        "returncode": result.returncode,
        "stdout": stdout,
        "stderr": stderr,
    }
    if record is not None:
        write_json(record, evidence)
    if stderr:
        _ = sys.stderr.write(stderr)
    if result.returncode != 0:
        if stdout:
            _ = sys.stderr.write(stdout)
        result.check_returncode()
    return evidence


def successful_output(
    evidence: dict[str, object], command: list[str], *, quiet: bool = True
) -> str:
    """Require a successful recorded invocation with the exact expected command."""
    if (
        evidence.get("command") != command
        or type(evidence.get("returncode")) is not int
        or evidence.get("returncode") != 0
        or evidence.get("environment") != command_environment(command)
    ):
        fail("Missing or inconsistent compiler/execution evidence")
    stdout = evidence.get("stdout")
    stderr = evidence.get("stderr")
    if (
        not isinstance(stdout, str)
        or not isinstance(stderr, str)
        or (quiet and stderr != "")
    ):
        fail("Unexpected compiler/execution diagnostics")
    return stdout


def local_file(root: Path, path: Path) -> Path:
    """Keep the entire input closure inside its retained tree; never follow symlinks."""
    relative = Path(os.path.normpath(path)).relative_to(root)
    at = root
    for part in relative.parts:
        at /= part
        if at.is_symlink():
            fail(f"Symlink is not a retained input: {at}")
    if not at.is_file():
        fail(f"Missing retained input: {at}")
    return at


def source_closure(root: Path, base_root: Path) -> tuple[set[str], set[str]]:
    """Mirror Bend2's local import preamble; forbid packages and local foreign code.

    Only the installed Base is privileged by Bend2 (realpath equality, not its
    spelling). Scan it too: trusted intrinsic declarations are not permission
    to admit @unsafe. All its foreign .c/.js inputs are retained conservatively.
    """
    local: set[str] = set()
    trusted: set[str] = set()

    def visit(path: Path, *, base: bool) -> None:
        tree = base_root if base else root
        path = local_file(tree, path)
        names = trusted if base else local
        name = path.relative_to(tree).as_posix()
        if name in names:
            return  # Bend itself rejects import cycles and namespace collisions.
        names.add(name)
        text = path.read_text(encoding="utf-8")
        lines = text.split("\n")
        body_start = len(lines)
        for index, raw in enumerate(lines):
            line = raw.strip()
            if not line or line.startswith("#"):
                continue
            match = IMPORT.fullmatch(line)
            if match is None:
                body_start = index
                break
            target, alias = match.groups()
            if target == "Base" and alias is None:
                visit(base_root / "base.bend", base=True)
                continue
            if (
                alias is None
                or not target.endswith(".bend")
                or target.startswith("/")
                or re.match(r"0x[0-9a-f]+/", os.path.normpath(target)) is not None
            ):
                fail(
                    f"Only local .bend imports and installed Base are permitted: {path}"
                )
            visit(path.parent / target, base=base)
        previous = ""
        for match in LEXEMES.finditer("\n".join(lines[body_start:])):
            token = match.group()
            if (
                previous in ("def", "law")
                and token == "main"
                and (base or path == root / "PROOF.bend")
            ):
                fail(f"Proof entrypoint and trusted Base must be proof-only: {path}")
            if token.startswith("#"):
                continue
            if previous == "@" and token == "unsafe":
                fail(f"Unsafe annotation in proof/compiler inputs: {path}")
            if previous == "import":
                if not base or not token.startswith('"') or not token.endswith('"'):
                    fail(f"Foreign code is restricted to retained Base IO: {path}")
                foreign = token[1:-1]
                if (
                    "\\" in foreign
                    or "\n" in foreign
                    or foreign.startswith("/")
                    or Path(foreign).suffix not in (".c", ".js")
                ):
                    fail(f"Unsupported Base foreign path: {foreign}")
                dependency = local_file(base_root, path.parent / foreign)
                trusted.add(dependency.relative_to(base_root).as_posix())
            previous = token

    visit(root / "PROOF.bend", base=False)
    if local != {name for name in SOURCE_NAMES if name.endswith(".bend")}:
        fail(
            "Root PROOF must retain exactly the required PLAN/SELECT/SPECULATE/RUNTIME dependency closure"
        )
    if "base.bend" not in trusted:
        fail("Generated programs must use the installed Base IO boundary")
    for name in SOURCE_NAMES:
        if not name.endswith(".bend"):
            _ = local_file(root, root / name)
            local.add(name)
    return local, trusted


def snapshot(root: Path, target: Path, names: set[str]) -> dict[str, str]:
    """Copy the checked dependency closure and hash the bytes actually retained."""
    hashes: dict[str, str] = {}
    for name in sorted(names):
        source = local_file(root, root / name)
        destination = target / name
        destination.parent.mkdir(parents=True, exist_ok=True)
        _ = shutil.copyfile(source, destination)
        hashes[name] = digest(destination)
        if digest(source) != hashes[name]:
            fail(f"Input changed during snapshot: {source}")
    return hashes


def check_hashes(root: Path, value: object) -> set[str]:
    """Validate the exact retained file set as well as every digest."""
    if not is_object(value) or not value:
        fail(f"Invalid artifact manifest: {root}")
    for name, expected in value.items():
        if (
            Path(name).is_absolute()
            or ".." in Path(name).parts
            or Path(name).as_posix() != name
        ):
            fail(f"Invalid retained artifact path: {name}")
        if (
            not isinstance(expected, str)
            or re.fullmatch(r"[0-9a-f]{64}", expected) is None
        ):
            fail(f"Invalid digest for retained artifact: {name}")
        if digest(local_file(root, root / name)) != expected:
            fail(f"Changed retained artifact: {root / name}")
    return set(value)


def tree_files(root: Path) -> set[str]:
    """Disallow extra inputs and symlinks, including symlinked directories."""
    names: set[str] = set()
    for path in root.rglob("*"):
        if path.is_symlink():
            fail(f"Symlink in retained tree: {path}")
        if path.is_file():
            names.add(path.relative_to(root).as_posix())
    return names


def check_release_compiler(hashes: object) -> None:
    """Admit only the pinned source-mode 2.0.20 checker layout and bytes."""
    if not is_object(hashes) or not set(COMPILER_FILES) <= set(hashes):
        fail("Compiler layout is not the pinned source-mode Bend 2.0.20 closure")
    if hashes.get("bin/bend") != WRAPPER_SHA256:
        fail("Retained Bend launcher differs from the pinned source-mode wrapper")
    if hashes.get("bin/bend-runtime") not in NATIVE_RUNTIME_SHA256:
        fail("Bend runtime is not a pinned native 2.0.20 release executable")
    if (
        hashes.get("bend2/main.ts") != SOURCE_MAIN_SHA256
        or hashes.get("bend2/comp.ts") != SOURCE_COMP_SHA256
    ):
        fail("Retained compiler entry modules differ from the pinned upstream source")
    if hashes.get("bend2/bend.ts") != PATCHED_CHECKER_SHA256:
        fail("Retained checker differs from the reviewed stack-safe 2.0.20 comparator")


def generate(output: Path, bend: str) -> None:
    """Check the real proof with the retained release compiler, then emit standalone C."""
    compiler = executable(bend)
    if compiler.parent.name != "bin" or compiler.name != "bend":
        fail(
            "Bend must be the installed bin/bend executable with adjacent release resources"
        )
    compiler_root = compiler.parent.parent
    # Nix exposes a public makeWrapper script; retain the actual release ELF.
    # Only the selected package layout is recognized, never legacy source mode.
    nix_root = compiler_root / "libexec/bend"
    direct = (compiler_root / "bend2/base.bend").is_file()
    nix = (nix_root / "bin/bend").is_file() and (nix_root / "bend2/base.bend").is_file()
    if direct == nix:
        fail("Missing or ambiguous Bend release compiler closure")
    if nix:
        compiler = local_file(compiler_root, nix_root / "bin/bend")
        compiler_root = nix_root
    if digest(compiler_root / "bend2/base.bend") != BASE_SHA256:
        fail("Bend Base differs from the selected 2.0.20 release")
    base_root = compiler_root / "bend2"
    source_root = Path(__file__).resolve().parent.parent
    local, trusted = source_closure(source_root, base_root)
    output.mkdir(parents=False, exist_ok=False)
    (output / "logs").mkdir()
    sources = snapshot(source_root, output / "sources", local)
    compiler_names = COMPILER_FILES | {f"bend2/{name}" for name in trusted}
    compiler_hashes = snapshot(compiler_root, output / "compiler", compiler_names)
    check_release_compiler(compiler_hashes)
    (output / "compiler/bin/bend").chmod(0o755)
    # copyfile drops modes; the interpreter ELF must stay executable too.
    (output / "compiler/bin/bend-runtime").chmod(0o755)
    # Execute the copy so its realpath-selected Base is exactly the retained Base.
    version_command = [BEND_COMMAND, "version"]
    version = run(version_command, cwd=output, record=output / "logs/version.json")
    if successful_output(version, version_command) != BEND_VERSION:
        fail("Generation requires exactly bend 2.0.20")
    base_command = [BEND_COMMAND, "base"]
    base = run(base_command, cwd=output, record=output / "logs/base.json")
    if (
        successful_output(base, base_command).encode("utf-8")
        != (output / "compiler/bend2/base.bend").read_bytes()
    ):
        fail("Compiler supplied a different trusted Base")
    if source_closure(output / "sources", output / "compiler/bend2") != (
        local,
        trusted,
    ):
        fail("Dependency closure changed during snapshot")
    proof = run(PROOF_COMMAND, cwd=output, record=output / "logs/proof.json")
    if successful_output(proof, PROOF_COMMAND) != PROOF_DIAGNOSTIC:
        fail("Root PROOF.bend did not check every term without unsafe annotations")
    for command, name, log in EMISSIONS:
        emitted = run(command, cwd=output, record=output / "logs" / log)
        if (
            successful_output(emitted, command) != ""
            or (output / name).stat().st_size == 0
        ):
            fail(f"Bend did not silently emit a nonempty standalone program: {name}")
    _ = check_hashes(output / "sources", sources)
    _ = check_hashes(output / "compiler", compiler_hashes)
    write_json(
        output / "source.json",
        {
            "schema": 7,
            "bend_version": BEND_VERSION.rstrip("\n"),
            "bend_origin": str(compiler),
            "sources": sources,
            "compiler": compiler_hashes,
            "c": {f"{name}.c": digest(output / f"{name}.c") for name in PROGRAM_NAMES},
            "logs": {name: digest(output / "logs" / name) for name in GENERATION_LOGS},
            "scope": SCOPE,
        },
    )


def source_identity(directory: Path) -> dict[str, object]:
    """Check the complete proof/compiler/Base/source/C identity without rerunning proofs."""
    identity = object_file(directory / "source.json")
    if (
        set(identity)
        != {
            "schema",
            "bend_version",
            "bend_origin",
            "sources",
            "compiler",
            "c",
            "logs",
            "scope",
        }
        or type(identity.get("schema")) is not int
        or identity.get("schema") != 7
        or identity.get("bend_version") != BEND_VERSION.rstrip("\n")
        or identity.get("scope") != SCOPE
    ):
        fail("Unsupported Bend2 source identity")
    sources = check_hashes(directory / "sources", identity.get("sources"))
    compiler = check_hashes(directory / "compiler", identity.get("compiler"))
    if sources != tree_files(directory / "sources") or compiler != tree_files(
        directory / "compiler"
    ):
        fail("Retained source/compiler file set changed")
    for name in SOURCE_NAMES:
        if not name.endswith(".bend") and digest(
            directory / "sources" / name
        ) != digest(Path(__file__).resolve().parent.parent / name):
            fail(
                f"Running native/adapter source differs from proof-bound source: {name}"
            )
    local, trusted = source_closure(directory / "sources", directory / "compiler/bend2")
    check_release_compiler(identity.get("compiler"))
    if sources != local or compiler != COMPILER_FILES | {
        f"bend2/{name}" for name in trusted
    }:
        fail("Retained dependency closure differs from generation")
    if digest(directory / "compiler/bend2/base.bend") != BASE_SHA256:
        fail("Retained Base differs from the selected 2.0.20 release")
    if check_hashes(directory, identity.get("c")) != {
        f"{name}.c" for name in PROGRAM_NAMES
    }:
        fail("Unexpected generated C manifest")
    if check_hashes(directory / "logs", identity.get("logs")) != set(GENERATION_LOGS):
        fail("Incomplete compiler/proof invocation history")
    version = object_file(directory / "logs/version.json")
    if successful_output(version, [BEND_COMMAND, "version"]) != BEND_VERSION:
        fail("Retained compiler version evidence changed")
    base = object_file(directory / "logs/base.json")
    if (
        successful_output(base, [BEND_COMMAND, "base"]).encode("utf-8")
        != (directory / "compiler/bend2/base.bend").read_bytes()
    ):
        fail("Retained compiler Base evidence changed")
    proof = object_file(directory / "logs/proof.json")
    if successful_output(proof, PROOF_COMMAND) != PROOF_DIAGNOSTIC:
        fail("No complete, safe root PROOF.bend verdict")
    for command, _, log in EMISSIONS:
        if successful_output(object_file(directory / "logs" / log), command) != "":
            fail("Unexpected C generation diagnostics")
    return identity


def compile_programs(directory: Path, cc: str) -> None:
    """Build the genuine CPU-only generated C with the selected target clang."""
    _ = source_identity(directory)
    compiler = executable(cc)
    if any(
        path.exists() or path.is_symlink()
        for path in (
            *(directory / name for name in PROGRAM_NAMES),
            directory / "build.json",
            *(directory / "logs" / name for name in BUILD_LOGS),
        )
    ):
        fail("Refusing to overwrite an existing or partial CPU program build")
    compiler_sha256 = digest(compiler)
    command = [str(compiler), "--version"]
    evidence = run(
        command, cwd=directory, record=directory / "logs/compiler-version.json"
    )
    version = successful_output(evidence, command)
    match = re.search(
        r"^(?:Apple )?(?:\w+ )?clang version ([0-9]+)", version, re.MULTILINE
    )
    if match is None or int(match.group(1)) < 14:
        fail("Bend2 CPU compilation requires the selected clang 14 or newer")
    for name in PROGRAM_NAMES:
        c = (directory / f"{name}.c").read_text(encoding="utf-8")
        if re.search(r"^#define BANGS\s+0$", c, re.MULTILINE) is None:
            fail(f"CPU program must not require a GPU lane: {name}")
        if re.search(
            r"^\s*#\s*(?:import|include\s*[\"<](?:X11|alsa)/)", c, re.MULTILINE
        ):
            fail(
                f"CPU program must not require desktop/audio foreign libraries: {name}"
            )
    for name, log in COMPILATIONS:
        command = [
            str(compiler),
            "-std=c11",
            "-O3",
            f"{name}.c",
            "-lpthread",
            "-lm",
            "-o",
            name,
        ]
        compiled = run(command, cwd=directory, record=directory / "logs" / log)
        if successful_output(compiled, command, quiet=False) != "":
            fail("Unexpected C compiler stdout")
    if digest(compiler) != compiler_sha256:
        fail("Selected clang changed during compilation")
    _ = source_identity(directory)
    write_json(
        directory / "build.json",
        {
            "schema": 5,
            "source_sha256": digest(directory / "source.json"),
            "compiler": {
                "path": str(compiler),
                "sha256": compiler_sha256,
                "version": version,
            },
            "c": {
                f"{name}.c": digest(directory / f"{name}.c") for name in PROGRAM_NAMES
            },
            "binaries": {name: digest(directory / name) for name in PROGRAM_NAMES},
            "logs": {name: digest(directory / "logs" / name) for name in BUILD_LOGS},
        },
    )


def parse_plan(text: str) -> Plan:
    """Decode every byte: 38 fields, every ordered free ID, and one final newline."""
    if not text.startswith(HEADER) or not text.endswith(END):
        fail("Missing or malformed Bend2 plan protocol")
    rows = text[len(HEADER) : -len(END)].split("\n")
    if (
        len(rows) != len(FIELDS) + 1 + 2056 + 1
        or rows[-1] != ""
        or rows[len(FIELDS)] + "\n" != FREE
    ):
        fail("Bend2 plan field/free-page count or marker mismatch")
    numeric = rows[: len(FIELDS)] + rows[len(FIELDS) + 1 : -1]
    if any(re.fullmatch(r"0|[1-9][0-9]{0,9}", row) is None for row in numeric):
        fail("Bend2 plan contains noncanonical decimal integers")
    values = [exact_int(int(row), "wire value") for row in numeric]
    plan: Plan = dict(zip(FIELDS, values[: len(FIELDS)], strict=True))
    plan["schema"] = 2
    plan["free_pages"] = values[len(FIELDS) :]
    return plan


def read_plan(directory: Path, *, record: Path | None = None) -> Plan:
    """Execute the real CPU planner exactly once, with GPU execution disabled."""
    evidence = run(PLAN_COMMAND, cwd=directory, record=record)
    return parse_plan(successful_output(evidence, PLAN_COMMAND))


def parse_policy(text: str) -> ObjectivePolicy:
    """Decode the complete role/transition wire, including its sole final newline."""
    if not text.startswith(POLICY_HEADER) or not text.endswith(POLICY_END):
        fail("Missing or malformed Bend2 objective policy protocol")
    rows = text[len(POLICY_HEADER) : -len(POLICY_END)].split("\n")
    if len(rows) != 30 or rows[4] != "TRANSITIONS" or rows[-1] != "":
        fail("Bend2 objective role/transition count or marker mismatch")
    roles, transitions = rows[:4], rows[5:-1]
    if any(re.fullmatch(r"[01]", row) is None for row in roles) or any(
        re.fullmatch(r"[0-5]", row) is None for row in transitions
    ):
        fail("Bend2 objective policy contains invalid role or transition codes")
    return ObjectivePolicy(
        tuple(int(row) for row in roles), tuple(int(row) for row in transitions)
    )


def read_policy(directory: Path, *, record: Path | None = None) -> ObjectivePolicy:
    """Execute the compiled CPU objective program exactly once with GPU disabled."""
    evidence = run(POLICY_COMMAND, cwd=directory, record=record)
    return parse_policy(successful_output(evidence, POLICY_COMMAND))


def policy_record(policy: ObjectivePolicy) -> dict[str, object]:
    """Retain precisely the parsed generated table, not a host-computed replacement."""
    return {
        "schema": 1,
        "roles": list(policy.roles),
        "transitions": list(policy.transitions),
    }


def parse_speculation(text: str) -> SpeculationPolicy:
    """Decode all 128 four-column decisions and the protocol's sole final newline."""
    if not text.startswith(SPECULATION_HEADER) or not text.endswith(SPECULATION_END):
        fail("Missing or malformed Bend2 greedy speculation protocol")
    rows = text[len(SPECULATION_HEADER) : -len(SPECULATION_END)].split("\n")
    if len(rows) != 513 or rows[-1] != "":
        fail("Bend2 speculation decision count mismatch")
    if any(re.fullmatch(r"[0-8]", row) is None for row in rows[:-1]):
        fail("Bend2 speculation contains noncanonical or out-of-range decision values")
    return SpeculationPolicy(
        8,
        tuple(
            (
                int(rows[index]),
                int(rows[index + 1]),
                int(rows[index + 2]),
                int(rows[index + 3]),
            )
            for index in range(0, 512, 4)
        ),
    )


def read_speculation(
    directory: Path, *, record: Path | None = None
) -> SpeculationPolicy:
    """Execute the compiled CPU speculation program once, never once per token."""
    evidence = run(SPECULATION_COMMAND, cwd=directory, record=record)
    return parse_speculation(successful_output(evidence, SPECULATION_COMMAND))


def speculation_record(policy: SpeculationPolicy) -> dict[str, object]:
    """Retain exactly the compiled block size and decisions, without host decision algebra."""
    return {"schema": 1, "block_size": policy.block_size, "decisions": policy.decisions}


def parse_runtime(text: str) -> RuntimePolicy:
    """Decode the entire count-delimited action wire and its sole final newline."""
    if not text.startswith(RUNTIME_HEADER) or not text.endswith(RUNTIME_END):
        fail("Missing or malformed Bend2 runtime control protocol")
    rows = text[len(RUNTIME_HEADER) : -len(RUNTIME_END)].split("\n")
    if len(rows) != 19 or rows[8:10] != ["STATUS", "8"] or rows[-1] != "":
        fail("Bend2 runtime action count or marker mismatch")
    free_mirror, status = rows[:8], rows[10:-1]
    if any(re.fullmatch(r"[01]", row) is None for row in free_mirror) or any(
        re.fullmatch(r"[0-2]", row) is None for row in status
    ):
        fail("Bend2 runtime control contains invalid action codes")
    return RuntimePolicy(
        tuple(int(row) for row in free_mirror), tuple(int(row) for row in status)
    )


def read_runtime(directory: Path, *, record: Path | None = None) -> RuntimePolicy:
    """Execute the original compiled CPU runtime table once, never per mirror access."""
    evidence = run(RUNTIME_COMMAND, cwd=directory, record=record)
    return parse_runtime(successful_output(evidence, RUNTIME_COMMAND))


def runtime_record(policy: RuntimePolicy) -> dict[str, object]:
    """Retain compiled actions without recreating the decision algebra in Python."""
    return {
        "schema": 1,
        "free_mirror": list(policy.free_mirror),
        "status": list(policy.status),
    }


def validate_request(plan: Plan, context: int, pool: int, page_size: int) -> None:
    """Independently check geometry, every page ID, headroom and packed layouts."""
    if set(plan) != set(FIELDS) | {"schema", "free_pages"}:
        fail("Unexpected plan fields")
    for name in FIELDS:
        _ = exact_int(plan[name], name)
    if exact_int(plan["schema"], "schema") != 2:
        fail("Unsupported plan schema")

    def field(name: str) -> int:
        return exact_int(plan[name], name)

    for name, value in (("context", context), ("pool", pool), ("page_size", page_size)):
        if exact_int(value, name) != field(name):
            fail("Requested launch geometry differs from compiled Bend2 plan")
    if page_size != 128 or context != 262144 or field("headroom") != 1024:
        fail("Unsupported native Qwen KVarN plan")
    if pool != context + field("headroom") or pool % page_size:
        fail("Pool/headroom/page alignment relationship violated")
    pages = field("pages")
    if (pages - 1) * page_size != pool:
        fail("Reserved-zero physical page relationship violated")
    free_pages = plan["free_pages"]
    if not isinstance(free_pages, list) or len(free_pages) != pages - 1:
        fail("Free page IDs must cover the nonzero physical page domain")
    for expected, page in enumerate(free_pages, 1):
        if exact_int(page, "free page") != expected:
            fail("Free pages must be ordered, unique and exactly 1 through 2056")
        first = page * page_size
        last = first + page_size - 1
        if not page_size <= first <= last < pages * page_size:
            fail("Physical page extent exceeds the allocated token backing")
    if pages * page_size - 1 != 263295 or (pages - 1) * page_size - context != field(
        "headroom"
    ):
        fail("Final-page extent or reserved-page/headroom accounting violated")
    usable_tokens = (len(free_pages) - 1) * page_size
    if usable_tokens != context + 896 or usable_tokens != pool - page_size:
        fail("One native dummy reservation must leave context plus 896 headroom tokens")
    if (
        field("tail_slots"),
        field("write_tokens"),
        field("query_tokens"),
        field("commit_tokens"),
    ) != (8, 128, 32, 8):
        fail("Unsupported bounded tail/write/query/commit geometry")
    if (
        field("write_span_pages") != 2
        or field("admission_free_slots") != field("write_span_pages") + 2
    ):
        fail("Unaligned write and sink/COW reservation relationship violated")
    if field("admission_free_slots") * page_size + field("write_tokens") > field(
        "headroom"
    ):
        fail("Headroom cannot cover admission reservations and a full write")
    if field("target_visible") != page_size or field(
        "draft_window"
    ) != 2048 + page_size + field("commit_tokens"):
        fail("Visible window relationship violated")
    if field("draft_visible") != -(-field("draft_window") // page_size) * page_size:
        fail("Draft workspace must minimally page-cover its visible window")
    for role, dim, heads, layers in (("target", 256, 4, 16), ("draft", 128, 8, 5)):
        if (
            field(f"{role}_dim"),
            field(f"{role}_kv_heads"),
            field(f"{role}_layers"),
        ) != (dim, heads, layers):
            fail(f"Unsupported {role} Qwen layout")
        sizes = (
            dim * page_size // 2,
            2 * dim,
            2 * dim,
            2 * page_size,
            dim * page_size // 4,
            2 * dim,
            2 * page_size,
            2 * page_size,
        )
        boundaries = [field(f"{role}_{name}") for name in OFFSET_NAMES]
        if boundaries[0] != 0 or tuple(b - a for a, b in pairwise(boundaries)) != sizes:
            fail(f"Noncontiguous {role} packed tile segments")
        if boundaries[-1] != dim * page_size * 3 // 4 + 6 * (dim + page_size):
            fail(f"Incorrect {role} packed tile byte size")


def build_identity(directory: Path) -> dict[str, object]:
    """Check source/proof/C/binary provenance before any CPU program executes."""
    _ = source_identity(directory)
    build = object_file(directory / "build.json")
    if (
        set(build) != {"schema", "source_sha256", "compiler", "c", "binaries", "logs"}
        or type(build.get("schema")) is not int
        or build.get("schema") != 5
        or build.get("source_sha256") != digest(directory / "source.json")
    ):
        fail("Stale build identity")
    if check_hashes(directory, build.get("c")) != {
        f"{name}.c" for name in PROGRAM_NAMES
    }:
        fail("Unexpected compiled C manifest")
    if check_hashes(directory, build.get("binaries")) != set(PROGRAM_NAMES):
        fail("Unexpected CPU executable manifest")
    if check_hashes(directory / "logs", build.get("logs")) != set(BUILD_LOGS):
        fail("Incomplete target compiler invocation history")
    compiler = build.get("compiler")
    if not is_object(compiler):
        fail("Missing target compiler identity")
    path, sha256, version = (
        compiler.get("path"),
        compiler.get("sha256"),
        compiler.get("version"),
    )
    if (
        not isinstance(path, str)
        or not Path(path).is_absolute()
        or not isinstance(sha256, str)
        or re.fullmatch(r"[0-9a-f]{64}", sha256) is None
        or not isinstance(version, str)
    ):
        fail("Malformed target compiler identity")
    command = [path, "--version"]
    if (
        successful_output(
            object_file(directory / "logs/compiler-version.json"), command
        )
        != version
    ):
        fail("Changed target compiler version evidence")
    for name, log in COMPILATIONS:
        command = [path, "-std=c11", "-O3", f"{name}.c", "-lpthread", "-lm", "-o", name]
        if (
            successful_output(
                object_file(directory / "logs" / log), command, quiet=False
            )
            != ""
        ):
            fail("Changed target compilation evidence")
    return build


def verify(directory: Path) -> None:
    """Run all four generated CPU programs and retain their complete validated output."""
    _ = build_identity(directory)
    if any(
        path.exists() or path.is_symlink()
        for path in (
            directory / "plan.json",
            directory / "policy.json",
            directory / "speculation.json",
            directory / "runtime.json",
            directory / "verified.json",
            directory / "logs/verify.json",
            directory / "logs/verify-policy.json",
            directory / "logs/verify-speculation.json",
            directory / "logs/verify-runtime.json",
        )
    ):
        fail("Refusing to overwrite existing or partial CPU verification")
    plan = read_plan(directory, record=directory / "logs/verify.json")
    validate_request(plan, 262144, 263168, 128)
    policy = read_policy(directory, record=directory / "logs/verify-policy.json")
    speculation = read_speculation(
        directory, record=directory / "logs/verify-speculation.json"
    )
    runtime = read_runtime(directory, record=directory / "logs/verify-runtime.json")
    _ = build_identity(directory)
    write_json(directory / "plan.json", plan)
    write_json(directory / "policy.json", policy_record(policy))
    write_json(directory / "speculation.json", speculation_record(speculation))
    write_json(directory / "runtime.json", runtime_record(runtime))
    write_json(directory / "verified.json", verification_identity(directory))


def verification_identity(directory: Path) -> dict[str, object]:
    """Bind all four retained executions to the complete source, proof and build chain."""
    return {
        "schema": 5,
        "build_sha256": digest(directory / "build.json"),
        "source_sha256": digest(directory / "source.json"),
        "proof_sha256": digest(directory / "logs/proof.json"),
        "plan_sha256": digest(directory / "plan.json"),
        "policy_sha256": digest(directory / "policy.json"),
        "speculation_sha256": digest(directory / "speculation.json"),
        "runtime_sha256": digest(directory / "runtime.json"),
        "execution_sha256": digest(directory / "logs/verify.json"),
        "policy_execution_sha256": digest(directory / "logs/verify-policy.json"),
        "speculation_execution_sha256": digest(
            directory / "logs/verify-speculation.json"
        ),
        "runtime_execution_sha256": digest(directory / "logs/verify-runtime.json"),
        "scope": SCOPE,
    }


def retained_execution(
    directory: Path,
) -> tuple[Plan, ObjectivePolicy, SpeculationPolicy]:
    """Check all four retained executions; preserve the existing three-result API."""
    _ = build_identity(directory)
    verified = object_file(directory / "verified.json")
    if (
        verified != verification_identity(directory)
        or type(verified.get("schema")) is not int
    ):
        fail("Stale or absent Bend2 verification identity")
    plan = parse_plan(
        successful_output(object_file(directory / "logs/verify.json"), PLAN_COMMAND)
    )
    validate_request(plan, 262144, 263168, 128)
    if json.dumps(object_file(directory / "plan.json"), sort_keys=True) != json.dumps(
        plan, sort_keys=True
    ):
        fail("Retained plan differs from verified execution")
    policy = parse_policy(
        successful_output(
            object_file(directory / "logs/verify-policy.json"), POLICY_COMMAND
        )
    )
    if json.dumps(object_file(directory / "policy.json"), sort_keys=True) != json.dumps(
        policy_record(policy), sort_keys=True
    ):
        fail("Retained policy differs from verified execution")
    speculation = parse_speculation(
        successful_output(
            object_file(directory / "logs/verify-speculation.json"), SPECULATION_COMMAND
        )
    )
    if json.dumps(
        object_file(directory / "speculation.json"), sort_keys=True
    ) != json.dumps(speculation_record(speculation), sort_keys=True):
        fail("Retained speculation policy differs from verified execution")
    _ = _retained_runtime(directory)
    return plan, policy, speculation


def _retained_runtime(directory: Path) -> RuntimePolicy:
    """Decode and compare retained runtime output after shared identity admission."""
    policy = parse_runtime(
        successful_output(
            object_file(directory / "logs/verify-runtime.json"), RUNTIME_COMMAND
        )
    )
    if json.dumps(
        object_file(directory / "runtime.json"), sort_keys=True
    ) != json.dumps(runtime_record(policy), sort_keys=True):
        fail("Retained runtime policy differs from verified execution")
    return policy


def checked_plan(directory: Path, context: int, pool: int, page_size: int) -> Plan:
    """Validate retained proof/build/output identity, then execute one fresh startup plan."""
    directory = directory.resolve(strict=True)
    retained, _, _ = retained_execution(directory)
    validate_request(retained, context, pool, page_size)
    plan = read_plan(directory)
    validate_request(plan, context, pool, page_size)
    if plan != retained:
        fail("Compiled Bend2 plan changed since verification")
    return plan


def checked_policy(directory: Path) -> ObjectivePolicy:
    """Validate the full retained closure, then execute and compare one fresh policy."""
    directory = directory.resolve(strict=True)
    _, retained, _ = retained_execution(directory)
    policy = read_policy(directory)
    if policy != retained:
        fail("Compiled Bend2 objective policy changed since verification")
    return policy


def checked_speculation(directory: Path) -> SpeculationPolicy:
    """Validate the full retained closure, then execute and compare one fresh startup table."""
    directory = directory.resolve(strict=True)
    _, _, retained = retained_execution(directory)
    policy = read_speculation(directory)
    if policy != retained:
        fail("Compiled Bend2 speculation policy changed since verification")
    return policy


def checked_runtime(directory: Path) -> RuntimePolicy:
    """Validate all retained evidence, then compare one fresh CPU runtime execution."""
    directory = directory.resolve(strict=True)
    _ = retained_execution(directory)
    retained = _retained_runtime(directory)
    policy = read_runtime(directory)
    if policy != retained:
        fail("Compiled Bend2 runtime policy changed since verification")
    return policy


class Arguments(argparse.Namespace):
    """Typed argparse destination; only selected-command fields are accessed."""

    command: str = ""
    output: Path = Path()
    bend: str = "bend"
    directory: Path = Path()
    cc: str = "clang"
    context: int = 0
    pool: int = 0
    page_size: int = 0


def main() -> None:
    """Expose generation, target compilation, verification and startup validation."""
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    generator = commands.add_parser("generate")
    _ = generator.add_argument("--output", type=Path, required=True)
    _ = generator.add_argument("--bend", default="bend")
    compiler = commands.add_parser("compile")
    _ = compiler.add_argument("--directory", type=Path, required=True)
    _ = compiler.add_argument("--cc", default="clang")
    verifier = commands.add_parser("verify")
    _ = verifier.add_argument("--directory", type=Path, required=True)
    checker = commands.add_parser("check")
    _ = checker.add_argument("--directory", type=Path, required=True)
    _ = checker.add_argument("--context", type=int, required=True)
    _ = checker.add_argument("--pool", type=int, required=True)
    _ = checker.add_argument("--page-size", type=int, required=True)
    args = Arguments()
    _ = parser.parse_args(namespace=args)
    if args.command == "generate":
        generate(args.output.resolve(), args.bend)
    elif args.command == "compile":
        compile_programs(args.directory.resolve(), args.cc)
    elif args.command == "verify":
        verify(args.directory.resolve())
    else:
        plan = checked_plan(
            args.directory.resolve(), args.context, args.pool, args.page_size
        )
        _ = sys.stdout.write(
            json.dumps(plan, sort_keys=True, separators=(",", ":")) + "\n"
        )


if __name__ == "__main__":
    main()
