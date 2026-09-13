"""Fresh procedural quality measurement. No resume and no pass/fail gate."""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import re
import secrets
import signal
import sys
import time
import traceback
from contextlib import contextmanager
from dataclasses import dataclass, field
from pathlib import Path
from typing import TYPE_CHECKING, Literal, NoReturn
from urllib.parse import urlsplit

if TYPE_CHECKING:
    from collections.abc import Iterator
    from types import FrameType

import httpx
import reasoning_gym
from pydantic import BaseModel, ConfigDict, Field, JsonValue
from transport import (
    ApiFailure,
    ArtifactTarget,
    ChatMessage,
    RequestSettings,
    canonical,
    decode,
    digest,
    read_bounded,
    request_completion,
    write_private,
)

REVISION = "49b07130b3fcd12f2d064bba7c43869543a0e7e7"
INSTRUCTION = (
    "\nReturn your final answer inside exactly one <answer>...</answer> pair. "
    "Put no explanation inside that pair."
)
MAX_COUNT = 100
MAX_TOKENS = 65536
MAX_TIMEOUT = 3600
MAX_GENERATION_TIMEOUT = 600
MAX_PORT = 65535


class Strict(BaseModel):
    """Reject unknown fields and coercions at JSON boundaries."""

    model_config = ConfigDict(extra="forbid", strict=True)


class Stratum(Strict):
    """Describe one predeclared task distribution."""

    id: str = Field(pattern=r"^[a-z0-9-]+$")
    dataset: Literal[
        "knights_knaves", "zebra_puzzles", "shortest_path", "sokoban", "rearc"
    ]
    parameters: dict[str, JsonValue]
    acceptance: Literal["all", "feasible_min_side"]


class Plan(Strict):
    """Bind the exact reviewed upstream revision and strata."""

    schema_version: Literal[2]
    upstream_revision: Literal["49b07130b3fcd12f2d064bba7c43869543a0e7e7"]
    scoring: Literal["upstream-full-credit-only"]
    threshold: None
    strata: list[Stratum] = Field(min_length=9, max_length=9)


class Entry(Strict):
    """Validate a generated question, oracle answer, and metadata."""

    question: str = Field(min_length=1)
    answer: str = Field(min_length=1)
    metadata: dict[str, JsonValue]


class Frozen(Strict):
    """Validate committed prompt banks and rejection counts."""

    commitment_sha256: str = Field(pattern=r"^[0-9a-f]{64}$")
    prompt_digests: dict[Literal["pilot", "evaluation"], list[str]]
    duplicate_rejections: int = Field(ge=0)
    conditioning_rejections: dict[str, int]
    path_sampling: dict[str, dict[str, int]]
    selected_count: int = Field(ge=1)


class Roots(Strict):
    """Validate independent private seed roots."""

    pilot: str = Field(pattern=r"^[0-9a-f]{64}$")
    evaluation: str = Field(pattern=r"^[0-9a-f]{64}$")


class Item(Strict):
    """Bind one generated entry to its seed and prompt digest."""

    split: Literal["pilot", "evaluation"]
    stratum: str
    index: int = Field(ge=0, le=99)
    seed: str = Field(pattern=r"^[0-9]{1,78}$")
    attempt: int = Field(ge=0, le=999)
    entry: Entry
    prompt_sha256: str = Field(pattern=r"^[0-9a-f]{64}$")


def generation_timeout(_signum: int, _frame: FrameType | None) -> NoReturn:
    """Interrupt generator work in the Linux main thread.

    Raises:
        TimeoutError: The per-item generation deadline expired.

    """
    message = "Procedural item generation exceeded its deadline"
    raise TimeoutError(message)


@contextmanager
def generation_deadline(seconds: int, failure_path: Path) -> Iterator[None]:
    """Arm and restore an exclusive per-item generation alarm.

    Yields:
        Control to the protected generator work.

    Raises:
        RuntimeError: An existing alarm or non-Python handler prevents safe restoration.

    """
    remaining, interval = signal.getitimer(signal.ITIMER_REAL)
    if remaining > 0 or interval > 0:
        message = "Cannot replace a caller-owned generation alarm"
        raise RuntimeError(message)
    previous = signal.getsignal(signal.SIGALRM)
    if previous is None:
        message = "Cannot restore a non-Python caller alarm handler"
        raise RuntimeError(message)
    signal.signal(signal.SIGALRM, generation_timeout)
    try:
        signal.setitimer(signal.ITIMER_REAL, seconds)
        try:
            yield
        except Exception as error:
            write_private(
                failure_path,
                {
                    "generation_failures": 1,
                    "error_type": type(error).__name__,
                    "traceback": traceback.format_exc(),
                },
            )
            raise
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
        signal.signal(signal.SIGALRM, previous)


def native_entry(
    value: object, expected: Entry | None = None
) -> tuple[dict[str, object], Entry]:
    """Validate JSON without changing scorer-native tuples to lists.

    Returns:
        The original native mapping and its strict JSON representation.

    Raises:
        ValueError: The entry is malformed or differs from its frozen representation.

    """
    if not isinstance(value, dict):
        message = "Generator entry must be an object"
        raise ValueError(message)
    native: dict[str, object] = {}
    for key, item in value.items():
        if not isinstance(key, str):
            message = "Generator entry keys must be strings"
            raise ValueError(message)
        native[key] = item
    validated = Entry.model_validate(decode(canonical(native).decode()))
    if expected is not None and canonical(validated.model_dump()) != canonical(
        expected.model_dump()
    ):
        message = "Regenerated native entry differs from frozen entry"
        raise ValueError(message)
    return native, validated


def path_solution(entry: Entry) -> list[str]:
    """Validate the path directions against the oracle answer.

    Returns:
        The validated sequence of path directions.

    Raises:
        ValueError: The solution metadata or oracle answer is inconsistent.

    """
    raw = entry.metadata.get("solution")
    if not isinstance(raw, list):
        message = "Path solution must be a list"
        raise ValueError(message)
    directions: list[str] = []
    for direction in raw:
        if not isinstance(direction, str) or direction not in {
            "up",
            "down",
            "left",
            "right",
        }:
            message = "Invalid path solution direction"
            raise ValueError(message)
        directions.append(direction)
    if len(directions) == 0:
        if entry.answer != "infeasible":
            message = "Empty path solution requires infeasible answer"
            raise ValueError(message)
    elif entry.answer.split() != directions:
        message = "Path answer and solution metadata differ"
        raise ValueError(message)
    return directions


def validate_plan(plan: Plan) -> None:
    """Require the exact reviewed strata before collecting results.

    Raises:
        ValueError: The plan differs from the frozen design.

    """
    expected = [
        {
            "id": "knights-6-depth3",
            "dataset": "knights_knaves",
            "parameters": {"n_people": 6, "depth_constraint": 3, "width_constraint": 3},
            "acceptance": "all",
        },
        {
            "id": "knights-8-depth3",
            "dataset": "knights_knaves",
            "parameters": {"n_people": 8, "depth_constraint": 3, "width_constraint": 3},
            "acceptance": "all",
        },
        {
            "id": "knights-10-depth3",
            "dataset": "knights_knaves",
            "parameters": {
                "n_people": 10,
                "depth_constraint": 3,
                "width_constraint": 3,
            },
            "acceptance": "all",
        },
        {
            "id": "zebra-6x5",
            "dataset": "zebra_puzzles",
            "parameters": {"num_people": 6, "num_characteristics": 5},
            "acceptance": "all",
        },
        {
            "id": "zebra-7x6",
            "dataset": "zebra_puzzles",
            "parameters": {"num_people": 7, "num_characteristics": 6},
            "acceptance": "all",
        },
        {
            "id": "path-24-long",
            "dataset": "shortest_path",
            "parameters": {
                "min_rows": 24,
                "max_rows": 24,
                "min_cols": 24,
                "max_cols": 24,
                "p_blocked": 0.2,
            },
            "acceptance": "feasible_min_side",
        },
        {
            "id": "path-32-long",
            "dataset": "shortest_path",
            "parameters": {
                "min_rows": 32,
                "max_rows": 32,
                "min_cols": 32,
                "max_cols": 32,
                "p_blocked": 0.2,
            },
            "acceptance": "feasible_min_side",
        },
        {
            "id": "sokoban-9x9-boxes5",
            "dataset": "sokoban",
            "parameters": {
                "min_w": 9,
                "max_w": 9,
                "min_h": 9,
                "max_h": 9,
                "min_boxes": 5,
                "max_boxes": 5,
                "max_depth": 120,
            },
            "acceptance": "all",
        },
        {
            "id": "rearc-three-examples",
            "dataset": "rearc",
            "parameters": {
                "min_examples": 3,
                "max_examples": 3,
                "diff_lb": 0.3,
                "diff_ub": 0.7,
                "rng_difficulty_ranges": [[0.3, 0.7]],
                "rng_difficulty_weights": [1.0],
                "pso_difficulty_ranges": [[0.15, 0.6]],
                "pso_difficulty_weights": [1.0],
            },
            "acceptance": "all",
        },
    ]
    actual = [stratum.model_dump() for stratum in plan.strata]
    if canonical(actual) != canonical(expected):
        message = (
            "Unsupported plan: change and review runner with plan "
            "before collecting results"
        )
        raise ValueError(message)


def arguments() -> argparse.Namespace:
    """Parse and validate CLI settings before creating private output.

    Returns:
        Validated command-line settings.

    """
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output",
        type=Path,
        required=True,
        help="New private directory; must not exist",
    )
    parser.add_argument(
        "--plan", type=Path, default=Path(__file__).with_name("reasoning-plan.json")
    )
    parser.add_argument("--mode", choices=("pilot", "evaluation"), default="pilot")
    parser.add_argument(
        "--count", type=int, default=2, help="Items per stratum per split, 1..100"
    )
    parser.add_argument("--generate-only", action="store_true")
    imports = parser.add_mutually_exclusive_group()
    imports.add_argument(
        "--replay-from",
        type=Path,
        help="Replay frozen bank with identical plan/settings into a new output",
    )
    imports.add_argument(
        "--bank-from",
        type=Path,
        help="Controlled comparison on a frozen bank with explicit request changes",
    )
    parser.add_argument(
        "--producer-root",
        type=Path,
        help="Frozen producer source tree; required only with --bank-from",
    )
    parser.add_argument(
        "--pilot-run",
        type=Path,
        help="Prior private pilot directory; required for evaluation inference",
    )
    parser.add_argument("--endpoint", default="http://127.0.0.1:18020/v1")
    parser.add_argument("--key-file", type=Path)
    parser.add_argument("--model", default="qwen3.8-27b")
    parser.add_argument(
        "--model-identity",
        help="Reviewed immutable deployment/model provenance, e.g. inventory SHA256",
    )
    parser.add_argument(
        "--thinking", choices=("enabled", "disabled"), default="enabled"
    )
    parser.add_argument("--max-tokens", type=int, default=8192)
    parser.add_argument("--timeout", type=int, default=600)
    parser.add_argument(
        "--generation-timeout",
        type=int,
        default=120,
        help="Per-item generator wall deadline, 1..600 seconds",
    )
    args = parser.parse_args()
    request_flags = {
        "--endpoint": "endpoint_sha256",
        "--model": "model",
        "--model-identity": "model_identity",
        "--thinking": "thinking",
        "--max-tokens": "max_tokens",
        "--timeout": "timeout",
    }
    args.explicit_request_keys = {
        request_flags[token.split("=", 1)[0]]
        for token in sys.argv[1:]
        if token.split("=", 1)[0] in request_flags
    }
    if (args.bank_from is None) != (args.producer_root is None):
        parser.error("--bank-from and --producer-root must be supplied together")
    if (
        not 1 <= args.count <= MAX_COUNT
        or not 1 <= args.max_tokens <= MAX_TOKENS
        or not 1 <= args.timeout <= MAX_TIMEOUT
        or not 1 <= args.generation_timeout <= MAX_GENERATION_TIMEOUT
    ):
        parser.error("count, max-tokens or timeout out of bounds")
    endpoint = urlsplit(args.endpoint)
    try:
        port = endpoint.port
    except ValueError:
        parser.error("Invalid endpoint port")
    if port is not None and not 1 <= port <= MAX_PORT:
        parser.error("Invalid endpoint port")
    has_credentials = endpoint.username is not None or endpoint.password is not None
    has_suffix = len(endpoint.query) > 0 or len(endpoint.fragment) > 0
    if (
        endpoint.scheme not in {"http", "https"}
        or endpoint.hostname is None
        or has_credentials
        or has_suffix
        or endpoint.path.rstrip("/") != "/v1"
    ):
        parser.error(
            "endpoint must be an HTTP(S) /v1 URL without credentials, query or fragment"
        )
    if endpoint.scheme == "http" and endpoint.hostname not in {
        "127.0.0.1",
        "localhost",
        "::1",
    }:
        parser.error("Use HTTPS for non-loopback endpoints")
    if not args.generate_only and (
        args.key_file is None or args.model_identity is None
    ):
        parser.error("inference requires --key-file and --model-identity")
    if args.mode == "evaluation" and not args.generate_only and args.pilot_run is None:
        parser.error(
            "evaluation inference requires --pilot-run for cross-run prompt exclusion"
        )
    if len(args.model.strip()) == 0 or (
        args.model_identity is not None and len(args.model_identity.strip()) == 0
    ):
        parser.error("model and model identity must not be empty")
    return args


def run(args: argparse.Namespace) -> None:
    """Establish exclusive output ownership before writing failure evidence."""
    plan = Plan.model_validate(decode(read_bounded(args.plan)))
    validate_plan(plan)
    base = Path(__file__).resolve().parent.parent
    settings = {
        "mode": args.mode,
        "count_per_stratum": args.count,
        "model": args.model,
        "model_identity": args.model_identity,
        "endpoint_sha256": digest(args.endpoint),
        "thinking": args.thinking,
        "max_tokens": args.max_tokens,
        "timeout": args.timeout,
        "generation_timeout": args.generation_timeout,
        "temperature": 0,
        "concurrency": 1,
        "python_version": sys.version,
        "transport_sha256": hashlib.sha256(
            (base / "bench" / "transport.py").read_bytes()
        ).hexdigest(),
        "instruction": INSTRUCTION,
        "runner_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "lock_sha256": hashlib.sha256((base / "uv.lock").read_bytes()).hexdigest(),
    }
    # Ownership is established before entering the failure/checkpoint writer scope.
    args.output.mkdir(mode=0o700, parents=False, exist_ok=False)
    args.output.chmod(0o700)
    try:
        execute(args, plan, settings)
    except BaseException:
        write_private(
            args.output / "failure.json", {"traceback": traceback.format_exc()}
        )
        raise


def _changed_request_settings(
    args: argparse.Namespace,
    settings: dict[str, JsonValue],
    old_settings: dict[str, JsonValue],
) -> list[str]:
    """Validate explicit changes after producer schema and bytes match.

    Returns:
        Sorted request setting names explicitly changed by this invocation.

    Raises:
        ValueError: A changed setting is forbidden or lacks its explicit CLI flag.

    """
    request_keys = {
        "endpoint_sha256",
        "model",
        "model_identity",
        "thinking",
        "max_tokens",
        "timeout",
    }
    changed: list[str] = []
    for key in sorted(settings):
        if canonical(old_settings[key]) == canonical(settings[key]):
            continue
        if key == "runner_sha256":
            # The old runner was verified above; this runner is newly committed.
            continue
        if key not in request_keys:
            message = "Bank import cannot change " + key
            raise ValueError(message)
        if key not in args.explicit_request_keys:
            message = "Bank request change needs its explicit CLI flag: " + key
            raise ValueError(message)
        changed.append(key)
    return changed


def _validate_producer_request(old_settings: dict[str, JsonValue]) -> None:
    """Validate the committed producer identity and request bounds.

    Raises:
        ValueError: A producer request identity or bound is invalid.

    """
    for key in ("model", "endpoint_sha256"):
        old_value = old_settings.get(key)
        if not isinstance(old_value, str) or len(old_value.strip()) == 0:
            message = "Invalid producer request identity"
            raise ValueError(message)
        if (
            key == "endpoint_sha256"
            and re.fullmatch(r"[0-9a-f]{64}", old_value) is None
        ):
            message = "Invalid producer endpoint digest"
            raise ValueError(message)
    old_identity = old_settings.get("model_identity")
    if old_identity is not None and (
        not isinstance(old_identity, str) or len(old_identity.strip()) == 0
    ):
        message = "Invalid producer model identity"
        raise ValueError(message)
    thinking = old_settings.get("thinking")
    if not isinstance(thinking, str) or thinking not in {"enabled", "disabled"}:
        message = "Invalid producer thinking mode"
        raise ValueError(message)
    for key, limit in (("max_tokens", 65536), ("timeout", 3600)):
        value = old_settings.get(key)
        if (
            not isinstance(value, int)
            or isinstance(value, bool)
            or not 1 <= value <= limit
        ):
            message = "Invalid producer request limit"
            raise ValueError(message)


def verify_bank_producer(
    args: argparse.Namespace,
    plan: Plan,
    settings: dict[str, JsonValue],
    old_settings: dict[str, JsonValue],
) -> dict[str, JsonValue]:
    """Bind comparisons to actual frozen producer bytes.

    Returns:
        Verified source inventory, inventory digest, and changed request names.

    Raises:
        TypeError: The producer source root is not a filesystem path.
        ValueError: Producer bytes, plan, declaration, or settings do not match.

    """
    source_root: object = args.producer_root
    if not isinstance(source_root, Path):
        message = "Bank producer source root must be a path"
        raise TypeError(message)
    source_files = {
        "runner_sha256": "bench/reasoning.py",
        "transport_sha256": "bench/transport.py",
        "lock_sha256": "uv.lock",
    }
    inventory: dict[str, str] = {}
    for key, relative in source_files.items():
        content = read_bounded(source_root / relative).encode()
        actual_hash = hashlib.sha256(content).hexdigest()
        if old_settings.get(key) != actual_hash:
            message = "Bank producer source digest mismatch: " + key
            raise ValueError(message)
        inventory[relative] = actual_hash
    producer_plan = Plan.model_validate(
        decode(read_bounded(source_root / "bench/reasoning-plan.json"))
    )
    if canonical(producer_plan.model_dump()) != canonical(plan.model_dump()):
        message = "Bank producer plan does not match current reviewed plan"
        raise ValueError(message)
    inventory["bench/reasoning-plan.json"] = digest(producer_plan.model_dump())
    project_bytes = read_bounded(source_root / "pyproject.toml").encode()
    current_project = Path(__file__).resolve().parent.parent / "pyproject.toml"
    if project_bytes != current_project.read_bytes():
        message = "Bank producer project dependency declaration differs"
        raise ValueError(message)
    inventory["pyproject.toml"] = hashlib.sha256(project_bytes).hexdigest()
    if set(old_settings) != set(settings):
        message = "Bank settings schema differs from this producer contract"
        raise ValueError(message)
    changed = _changed_request_settings(args, settings, old_settings)
    _validate_producer_request(old_settings)
    return {
        "producer_inventory": inventory,
        "producer_inventory_sha256": digest(inventory),
        "changed_request_settings": changed,
    }


@dataclass(frozen=True)
class ExecutionInputs:
    """Hold invocation inputs without changing their public boundary."""

    args: argparse.Namespace
    plan: Plan
    settings: dict[str, JsonValue]


@dataclass
class BankState:
    """Hold invocation-local bank artifacts and selected native tasks."""

    commitment: dict[str, JsonValue]
    frozen: dict[str, JsonValue]
    selected: list[tuple[Stratum, int, Entry]] = field(default_factory=list)
    duplicates: int = 0
    conditioning_rejections: dict[str, int] = field(default_factory=dict)
    path_sampling: dict[str, dict[str, int]] = field(default_factory=dict)


@dataclass
class GenerationState:
    """Track rejection accounting and prompt identities for one invocation."""

    bank: BankState
    seen: set[str]
    prompt_digests: dict[str, list[str]]


@dataclass(frozen=True)
class ItemPosition:
    """Identify a task's position in a split and its derivation root."""

    split: Literal["pilot", "evaluation"]
    root: str
    stratum: Stratum
    index: int


@dataclass(frozen=True)
class AcceptedCandidate:
    """Hold an accepted native entry without adding another validation boundary."""

    seed: int
    attempt: int
    entry: Entry
    prompt_sha256: str


@dataclass(frozen=True)
class ImportedBank:
    """Hold validated import metadata before writing or regenerating items."""

    source: Path
    commitment: dict[str, JsonValue]
    manifest: Frozen
    roots: dict[str, str]
    expected_commitments: dict[str, str]
    comparison_provenance: dict[str, JsonValue] | None


@dataclass
class MeasurementTotals:
    """Accumulate only valid measurement fields in their original order."""

    counts: dict[str, dict[str, int]]
    elapsed_total: float = 0.0
    item_elapsed_total: float = 0.0
    completion_total: int = 0
    usage_count: int = 0


def pilot_exclusions(inputs: ExecutionInputs) -> set[str]:
    """Validate pilot provenance before choosing import or generation.

    Returns:
        Validated prompt hashes excluded from fresh generation.

    Raises:
        ValueError: Pilot commitment, mode, or prompt digests are invalid.

    """
    args, settings = inputs.args, inputs.settings
    excluded: set[str] = set()
    pilot_digest: str | None = None
    if args.pilot_run is not None:
        previous_value = decode(read_bounded(args.pilot_run / "frozen.json"))
        previous = Frozen.model_validate(previous_value)
        pilot_digest = digest(previous_value)
        previous_commitment = decode(read_bounded(args.pilot_run / "commitment.json"))
        if digest(previous_commitment) != previous.commitment_sha256:
            message = "Pilot commitment mismatch"
            raise ValueError(message)
        if not isinstance(previous_commitment, dict):
            message = "Pilot commitment must be an object"
            raise ValueError(message)
        previous_settings = previous_commitment.get("settings")
        if (
            not isinstance(previous_settings, dict)
            or previous_settings.get("mode") != "pilot"
        ):
            message = "Referenced run must be a pilot"
            raise ValueError(message)
        for hashes in previous.prompt_digests.values():
            for prompt_hash in hashes:
                if re.fullmatch(r"[0-9a-f]{64}", prompt_hash) is None:
                    message = "Invalid pilot prompt digest"
                    raise ValueError(message)
                excluded.add(prompt_hash)
    settings["pilot_frozen_sha256"] = pilot_digest
    return excluded


def inherit_pilot_provenance(
    inputs: ExecutionInputs, old_settings: dict[str, JsonValue]
) -> None:
    """Inherit absent pilot provenance and require it for live evaluation imports.

    Raises:
        ValueError: Live evaluation lacks valid committed pilot provenance.

    """
    args, settings = inputs.args, inputs.settings
    if args.pilot_run is None:
        settings["pilot_frozen_sha256"] = old_settings.get("pilot_frozen_sha256")
    if args.mode == "evaluation" and not args.generate_only:
        pilot_provenance = settings.get("pilot_frozen_sha256")
        if (
            not isinstance(pilot_provenance, str)
            or re.fullmatch(r"[0-9a-f]{64}", pilot_provenance) is None
        ):
            message = (
                "Evaluation replay requires a bank with committed pilot provenance"
            )
            raise ValueError(message)


def read_import(inputs: ExecutionInputs, imported_bank: Path) -> ImportedBank:
    """Verify import metadata before the first output seed write.

    Returns:
        Validated source paths, commitments, roots, and import provenance.

    Raises:
        ValueError: Imported metadata differs from the required plan or commitments.

    """
    args, plan, settings = inputs.args, inputs.plan, inputs.settings
    commitment_value = decode(read_bounded(imported_bank / "commitment.json"))
    if not isinstance(commitment_value, dict):
        message = "Replay commitment must be an object"
        raise ValueError(message)
    commitment = commitment_value
    old_settings = commitment.get("settings")
    if not isinstance(old_settings, dict):
        message = "Replay settings must be an object"
        raise ValueError(message)
    inherit_pilot_provenance(inputs, old_settings)
    if canonical(commitment.get("plan")) != canonical(plan.model_dump()):
        message = "Imported bank plan mismatch"
        raise ValueError(message)
    comparison_provenance: dict[str, JsonValue] | None = None
    if args.bank_from is not None:
        comparison_provenance = verify_bank_producer(args, plan, settings, old_settings)
    elif canonical(old_settings) != canonical(settings):
        message = "Replay plan/settings/model identity mismatch"
        raise ValueError(message)
    frozen_value = decode(read_bounded(imported_bank / "frozen.json"))
    manifest = Frozen.model_validate(frozen_value)
    if manifest.commitment_sha256 != digest(commitment):
        message = "Replay commitment digest mismatch"
        raise ValueError(message)
    replay_roots = Roots.model_validate(
        decode(read_bounded(imported_bank / "seeds.json"))
    ).model_dump()
    expected_commitments = {
        split: digest({
            "domain": "reasoning-bench-v1",
            "split": split,
            "seed": root,
        })
        for split, root in replay_roots.items()
    }
    if canonical(commitment.get("seed_commitments")) != canonical(expected_commitments):
        message = "Replay seed commitment mismatch"
        raise ValueError(message)
    return ImportedBank(
        imported_bank,
        commitment,
        manifest,
        replay_roots,
        expected_commitments,
        comparison_provenance,
    )


def replay_item(
    inputs: ExecutionInputs,
    imported: ImportedBank,
    position: ItemPosition,
    seen: set[str],
) -> Item:
    """Verify identity, conditioning and native oracle before accepting a replay.

    Returns:
        The validated frozen item after successful native oracle scoring.

    Raises:
        ValueError: Item identity, seed, conditioning, prompt, or native oracle differs.

    """
    args = inputs.args
    split, stratum, index = position.split, position.stratum, position.index
    name = f"{split}-{stratum.id}-{index:03d}-item.json"
    item = Item.model_validate(decode(read_bounded(imported.source / name)))
    if item.split != split or item.stratum != stratum.id or item.index != index:
        message = "Replay item identity mismatch"
        raise ValueError(message)
    expected_seed = int(
        digest({
            "domain": "reasoning-bench-item-v1",
            "root": imported.roots[split],
            "split": split,
            "stratum": stratum.id,
            "index": index,
            "attempt": item.attempt,
        }),
        16,
    )
    if int(item.seed) != expected_seed:
        message = "Replay item seed derivation mismatch"
        raise ValueError(message)
    if stratum.acceptance == "feasible_min_side":
        side = stratum.parameters.get("min_rows")
        if (
            not isinstance(side, int)
            or isinstance(side, bool)
            or len(path_solution(item.entry)) < side
        ):
            message = "Replay path violates frozen conditioning rule"
            raise ValueError(message)
    prompt_hash = digest(item.entry.question + INSTRUCTION)
    if item.prompt_sha256 != prompt_hash or prompt_hash in seen:
        message = "Replay prompt digest mismatch or duplicate"
        raise ValueError(message)
    dataset = reasoning_gym.create_dataset(
        stratum.dataset,
        seed=int(item.seed),
        size=1,
        **stratum.parameters,
    )
    with generation_deadline(
        args.generation_timeout, args.output / "generation-failure.json"
    ):
        regenerated: object = dataset[0]
    native, _regenerated_entry = native_entry(regenerated, item.entry)
    oracle_reward: object = dataset.score_answer(item.entry.answer, native)
    if (
        not isinstance(oracle_reward, (int, float))
        or isinstance(oracle_reward, bool)
        or not math.isfinite(oracle_reward)
        or not 1 <= oracle_reward <= 1
    ):
        message = "Replay oracle did not earn full credit"
        raise ValueError(message)
    if canonical(regenerated) != canonical(item.entry.model_dump()):
        message = "Replay entry does not match pinned generator"
        raise ValueError(message)
    return item


def replay_split(
    inputs: ExecutionInputs,
    imported: ImportedBank,
    bank: BankState,
    split: Literal["pilot", "evaluation"],
    seen: set[str],
) -> None:
    """Copy accepted items in stratum/index order, then verify the split manifest.

    Raises:
        ValueError: Copied prompt hashes differ from the split manifest.

    """
    actual_hashes: list[str] = []
    for stratum in inputs.plan.strata:
        for index in range(inputs.args.count):
            position = ItemPosition(split, imported.roots[split], stratum, index)
            item = replay_item(inputs, imported, position, seen)
            seen.add(item.prompt_sha256)
            actual_hashes.append(item.prompt_sha256)
            name = f"{split}-{stratum.id}-{index:03d}-item.json"
            write_private(inputs.args.output / name, item.model_dump())
            if split == inputs.args.mode:
                bank.selected.append((stratum, int(item.seed), item.entry))
    if imported.manifest.prompt_digests.get(split) != actual_hashes:
        message = "Replay bank manifest mismatch"
        raise ValueError(message)


def finish_import(
    inputs: ExecutionInputs, imported: ImportedBank, bank: BankState
) -> None:
    """Bind comparison provenance and publish frozen import artifacts.

    Raises:
        ValueError: Selected count or source summary binding differs.

    """
    args, plan, settings = inputs.args, inputs.plan, inputs.settings
    manifest, commitment = imported.manifest, imported.commitment
    comparison_provenance = imported.comparison_provenance
    imported_bank = imported.source
    expected_commitments = imported.expected_commitments
    selected = bank.selected
    if manifest.selected_count != len(selected):
        message = "Replay count mismatch"
        raise ValueError(message)
    source_frozen = manifest.model_dump()
    if comparison_provenance is not None:
        source_summary = decode(read_bounded(imported_bank / "summary.json"))
        if not isinstance(source_summary, dict) or source_summary.get(
            "frozen_sha256"
        ) != digest(source_frozen):
            message = "Bank source summary does not bind its frozen manifest"
            raise ValueError(message)
        comparison_provenance = {
            **comparison_provenance,
            "parent_frozen_sha256": digest(source_frozen),
            "parent_commitment_sha256": digest(commitment),
        }
        commitment = {
            "plan": plan.model_dump(),
            "settings": settings,
            "seed_commitments": expected_commitments,
            "bank_import": comparison_provenance,
        }
        frozen = {**source_frozen, "commitment_sha256": digest(commitment)}
    else:
        frozen = source_frozen
    bank.duplicates = manifest.duplicate_rejections
    bank.conditioning_rejections = manifest.conditioning_rejections
    bank.path_sampling = manifest.path_sampling
    write_private(args.output / "commitment.json", commitment)
    write_private(args.output / "frozen.json", frozen)
    if comparison_provenance is not None:
        write_private(args.output / "bank-import.json", comparison_provenance)
    else:
        write_private(
            args.output / "replay.json", {"source_frozen_sha256": digest(frozen)}
        )
    bank.commitment = commitment
    bank.frozen = frozen


def replay_bank(inputs: ExecutionInputs, source: Path) -> BankState:
    """Regenerate both committed splits before returning any inference tasks.

    Returns:
        The copied bank and its verified frozen artifacts.

    """
    imported = read_import(inputs, source)
    write_private(inputs.args.output / "seeds.json", imported.roots)
    bank = BankState(commitment=imported.commitment, frozen={})
    seen: set[str] = set()
    replay_split(inputs, imported, bank, "pilot", seen)
    replay_split(inputs, imported, bank, "evaluation", seen)
    finish_import(inputs, imported, bank)
    return bank


def generated_entry(inputs: ExecutionInputs, stratum: Stratum, seed: int) -> Entry:
    """Generate once and score the untouched native oracle before conditioning.

    Returns:
        The validated entry whose native oracle earns full credit.

    Raises:
        ValueError: The generated native oracle does not earn full credit.

    """
    args = inputs.args
    dataset = reasoning_gym.create_dataset(
        stratum.dataset, seed=seed, size=1, **stratum.parameters
    )
    # Always index zero: upstream Random(seed+idx) cannot overlap adjacent indices.
    with generation_deadline(
        args.generation_timeout,
        args.output / "generation-failure.json",
    ):
        upstream: object = dataset[0]
    native, entry = native_entry(upstream)
    oracle_reward: object = dataset.score_answer(entry.answer, native)
    if (
        not isinstance(oracle_reward, (int, float))
        or isinstance(oracle_reward, bool)
        or not math.isfinite(oracle_reward)
        or not 1 <= oracle_reward <= 1
    ):
        message = "Generated oracle did not earn full credit"
        raise ValueError(message)
    return entry


def reject_conditioned_path(stratum: Stratum, entry: Entry, bank: BankState) -> bool:
    """Count conditioned candidates before prompt deduplication.

    Returns:
        Whether the candidate is rejected by the frozen path condition.

    Raises:
        ValueError: The conditioned path side is not an integer.

    """
    if stratum.acceptance != "feasible_min_side":
        return False
    side = stratum.parameters.get("min_rows")
    if not isinstance(side, int) or isinstance(side, bool):
        message = "Conditioned path side must be an integer"
        raise ValueError(message)
    solution = path_solution(entry)
    if len(solution) == 0:
        bank.path_sampling[stratum.id]["candidate_infeasible"] += 1
        bank.conditioning_rejections[stratum.id] += 1
        return True
    bank.path_sampling[stratum.id]["candidate_feasible"] += 1
    if len(solution) < side:
        bank.path_sampling[stratum.id]["rejected_too_short"] += 1
        bank.conditioning_rejections[stratum.id] += 1
        return True
    return False


def generate_item(
    inputs: ExecutionInputs, state: GenerationState, position: ItemPosition
) -> AcceptedCandidate:
    """Try at most 1000 independently derived candidates in the original order.

    Returns:
        The first conditioned candidate with a previously unseen prompt.

    Raises:
        RuntimeError: All 1000 candidates fail conditioning or prompt deduplication.

    """
    for attempt in range(1000):
        seed = int(
            digest({
                "domain": "reasoning-bench-item-v1",
                "root": position.root,
                "split": position.split,
                "stratum": position.stratum.id,
                "index": position.index,
                "attempt": attempt,
            }),
            16,
        )
        entry = generated_entry(inputs, position.stratum, seed)
        if reject_conditioned_path(position.stratum, entry, state.bank):
            continue
        prompt_hash = digest(entry.question + INSTRUCTION)
        if prompt_hash not in state.seen:
            return AcceptedCandidate(seed, attempt, entry, prompt_hash)
        state.bank.duplicates += 1
        if position.stratum.dataset == "shortest_path":
            state.bank.path_sampling[position.stratum.id]["duplicate_rejections"] += 1
    message = "Conditioning/prompt deduplication retry limit reached"
    raise RuntimeError(message)


def generate_split(
    inputs: ExecutionInputs,
    state: GenerationState,
    split: Literal["pilot", "evaluation"],
    root: str,
) -> None:
    """Write each accepted task before adding it to the selected split."""
    for stratum in inputs.plan.strata:
        for index in range(inputs.args.count):
            item = generate_item(
                inputs, state, ItemPosition(split, root, stratum, index)
            )
            state.seen.add(item.prompt_sha256)
            state.prompt_digests[split].append(item.prompt_sha256)
            write_private(
                inputs.args.output / f"{split}-{stratum.id}-{index:03d}-item.json",
                {
                    "split": split,
                    "stratum": stratum.id,
                    "index": index,
                    "seed": str(item.seed),
                    "attempt": item.attempt,
                    "entry": item.entry.model_dump(),
                    "prompt_sha256": item.prompt_sha256,
                },
            )
            if split == inputs.args.mode:
                state.bank.selected.append((stratum, item.seed, item.entry))


def fresh_bank(inputs: ExecutionInputs, excluded: set[str]) -> BankState:
    """Commit roots and settings, generate both banks, and freeze prompt hashes.

    Returns:
        Both frozen splits and the selected tasks with rejection accounting.

    Raises:
        RuntimeError: Independent split root draws are identical.

    """
    args, plan, settings = inputs.args, inputs.plan, inputs.settings
    roots = {split: secrets.token_hex(32) for split in ("pilot", "evaluation")}
    if roots["pilot"] == roots["evaluation"]:
        message = "Split roots must be distinct"
        raise RuntimeError(message)
    write_private(args.output / "seeds.json", roots)
    commitment = {
        "plan": plan.model_dump(),
        "settings": settings,
        "seed_commitments": {
            split: digest({
                "domain": "reasoning-bench-v1",
                "split": split,
                "seed": seed,
            })
            for split, seed in roots.items()
        },
    }
    write_private(args.output / "commitment.json", commitment)
    bank = BankState(commitment=commitment, frozen={})
    bank.conditioning_rejections = {stratum.id: 0 for stratum in plan.strata}
    bank.path_sampling = {
        stratum.id: {
            "candidate_feasible": 0,
            "candidate_infeasible": 0,
            "rejected_too_short": 0,
            "duplicate_rejections": 0,
        }
        for stratum in plan.strata
        if stratum.dataset == "shortest_path"
    }
    state = GenerationState(bank, set(excluded), {"pilot": [], "evaluation": []})
    generate_split(inputs, state, "pilot", roots["pilot"])
    generate_split(inputs, state, "evaluation", roots["evaluation"])
    bank.frozen = {
        "commitment_sha256": digest(commitment),
        "prompt_digests": state.prompt_digests,
        "duplicate_rejections": bank.duplicates,
        "conditioning_rejections": bank.conditioning_rejections,
        "path_sampling": bank.path_sampling,
        "selected_count": len(bank.selected),
    }
    write_private(args.output / "frozen.json", bank.frozen)
    return bank


def accumulate_measurement(
    totals: MeasurementTotals, stratum: Stratum, result: dict[str, JsonValue]
) -> None:
    """Account timing and usage before validating and incrementing status.

    Raises:
        ValueError: The measurement status is not a declared outcome.

    """
    elapsed = result.get("elapsed_seconds")
    if isinstance(elapsed, float):
        totals.elapsed_total += elapsed
    item_elapsed = result.get("item_elapsed_seconds")
    if isinstance(item_elapsed, float):
        totals.item_elapsed_total += item_elapsed
    usage = result.get("usage")
    if isinstance(usage, dict):
        tokens = usage.get("completion_tokens")
        if isinstance(tokens, int) and not isinstance(tokens, bool):
            totals.completion_total += tokens
            totals.usage_count += 1
    status = result["status"]
    if not isinstance(status, str) or status not in totals.counts[stratum.id]:
        message = "Invalid measurement status"
        raise ValueError(message)
    totals.counts[stratum.id][status] += 1


def measure_bank(inputs: ExecutionInputs, bank: BankState) -> MeasurementTotals:
    """Measure only after all tasks and settings are frozen on disk.

    Returns:
        Per-stratum counts and timing and token totals.

    Raises:
        ValueError: The API key is empty or contains whitespace.

    """
    args = inputs.args
    totals = MeasurementTotals({
        stratum.id: {
            "correct": 0,
            "incorrect": 0,
            "parser_failure": 0,
            "truncation": 0,
            "api_failure": 0,
            "scorer_failure": 0,
        }
        for stratum in inputs.plan.strata
    })
    if args.generate_only:
        return totals
    key = read_bounded(args.key_file, 16384).strip()
    if len(key) == 0 or re.search(r"\s", key) is not None:
        message = "Invalid API key file"
        raise ValueError(message)
    with httpx.Client(
        timeout=args.timeout, follow_redirects=False, trust_env=False
    ) as client:
        for ordinal, (stratum, seed, entry) in enumerate(bank.selected):
            result = measure(client, args, key, (stratum, seed, entry), ordinal)
            accumulate_measurement(totals, stratum, result)
            write_private(args.output / f"{ordinal:04d}-result.json", result)
            write_private(
                args.output / f"checkpoint-{ordinal:04d}.json",
                {"completed": ordinal + 1, "counts": totals.counts},
            )
    return totals


def summarize_path_oracles(
    plan: Plan, selected: list[tuple[Stratum, int, Entry]]
) -> dict[str, dict[str, int | float]]:
    """Report the selected path oracle distribution without rescoring.

    Returns:
        Path feasibility counts, baseline accuracy, and solution lengths.

    """
    path_oracles: dict[str, dict[str, int | float]] = {}
    for stratum in plan.strata:
        if stratum.dataset == "shortest_path":
            answers = [
                entry.answer
                for selected_stratum, seed, entry in selected
                if selected_stratum.id == stratum.id
            ]
            infeasible = sum(answer == "infeasible" for answer in answers)
            path_oracles[stratum.id] = {
                "feasible": len(answers) - infeasible,
                "infeasible": infeasible,
                "always_infeasible_accuracy": infeasible / len(answers),
                "minimum_solution_steps": min(
                    len(answer.split()) for answer in answers
                ),
                "maximum_solution_steps": max(
                    len(answer.split()) for answer in answers
                ),
            }
    return path_oracles


def publish_summary(
    inputs: ExecutionInputs, bank: BankState, totals: MeasurementTotals
) -> None:
    """Publish the original summary schema after measurements complete."""
    args = inputs.args
    path_oracles = summarize_path_oracles(inputs.plan, bank.selected)
    total = sum(sum(row.values()) for row in totals.counts.values())
    correct = sum(row["correct"] for row in totals.counts.values())
    summary = {
        "schema_version": 1,
        "upstream_revision": REVISION,
        "mode": args.mode,
        "generate_only": args.generate_only,
        "planned": len(bank.selected),
        "completed": total,
        "thinking": args.thinking,
        "max_tokens": args.max_tokens,
        "concurrency": 1,
        "model_identity_sha256": digest(args.model_identity),
        "count_per_stratum": args.count,
        "full_credit": correct,
        "accuracy": correct / total if total > 0 else None,
        "bank_import": bank.commitment.get("bank_import"),
        "strata": totals.counts,
        "path_oracles": path_oracles,
        "commitment_sha256": digest(bank.commitment),
        "frozen_sha256": digest(bank.frozen),
        "duplicate_rejections": bank.duplicates,
        "conditioning_rejections": bank.conditioning_rejections,
        "path_sampling": bank.path_sampling,
        "generation_failures": 0,
        "threshold": None,
        "request_elapsed_seconds": totals.elapsed_total,
        "item_elapsed_seconds": totals.item_elapsed_total,
        "completion_tokens": totals.completion_total,
        "usage_available_count": totals.usage_count,
        "end_to_end_output_tokens_per_second": totals.completion_total
        / totals.elapsed_total
        if totals.elapsed_total > 0 and totals.usage_count == total
        else None,
    }
    write_private(args.output / "summary.json", summary)
    sys.stdout.write(json.dumps(summary, sort_keys=True) + "\n")


def execute(
    args: argparse.Namespace, plan: Plan, settings: dict[str, JsonValue]
) -> None:
    """Freeze both task banks before measuring and publishing results."""
    inputs = ExecutionInputs(args, plan, settings)
    excluded = pilot_exclusions(inputs)
    imported_bank = args.replay_from if args.replay_from is not None else args.bank_from
    bank = (
        fresh_bank(inputs, excluded)
        if imported_bank is None
        else replay_bank(inputs, imported_bank)
    )
    totals = measure_bank(inputs, bank)
    publish_summary(inputs, bank, totals)


def _score_answer(
    args: argparse.Namespace, task: tuple[Stratum, int, Entry], answer: str
) -> int | float:
    """Regenerate the native scorer entry and validate the reward.

    Returns:
        The finite upstream reward in the inclusive interval zero to one.

    Raises:
        ValueError: The upstream scorer returns an invalid reward.

    """
    stratum, seed, entry = task
    dataset = reasoning_gym.create_dataset(
        stratum.dataset, seed=seed, size=1, **stratum.parameters
    )
    with generation_deadline(
        args.generation_timeout, args.output / "generation-failure.json"
    ):
        upstream: object = dataset[0]
    native, _regenerated_entry = native_entry(upstream, entry)
    reward: object = dataset.score_answer(answer, native)
    if (
        not isinstance(reward, (int, float))
        or isinstance(reward, bool)
        or not math.isfinite(reward)
        or not 0 <= reward <= 1
    ):
        message = "Invalid upstream reward"
        raise ValueError(message)
    return reward


def measure(
    client: httpx.Client,
    args: argparse.Namespace,
    key: str,
    task: tuple[Stratum, int, Entry],
    ordinal: int,
) -> dict[str, JsonValue]:
    """Measure one request and retain its exclusive failure classification.

    Returns:
        Private result fields including status and measured elapsed times.

    """
    stratum, _seed, entry = task
    start = time.monotonic()
    request = RequestSettings(
        endpoint=args.endpoint,
        model=args.model,
        thinking=args.thinking,
        max_tokens=args.max_tokens,
        timeout=args.timeout,
    )
    messages = (ChatMessage(role="user", content=entry.question + INSTRUCTION),)
    result: dict[str, JsonValue] = {
        "ordinal": ordinal,
        "stratum": stratum.id,
        "status": "api_failure",
    }
    response = request_completion(
        client, request, key, messages, ArtifactTarget(args.output, f"{ordinal:04d}")
    )
    if isinstance(response, ApiFailure):
        result["elapsed_seconds"] = response.elapsed_seconds
        result["item_elapsed_seconds"] = time.monotonic() - start
        return result
    completion = response.completion
    if completion.usage is not None:
        result["usage"] = completion.usage.model_dump(exclude_none=True)
    choice = completion.choices[0]
    result["finish_reason"] = choice.finish_reason
    if choice.finish_reason == "length":
        result["status"] = "truncation"
    elif choice.finish_reason != "stop":
        result["status"] = "api_failure"
    else:
        content = choice.message.content
        matches = (
            []
            if content is None
            else re.findall(r"<answer>(.*?)</answer>", content, flags=re.DOTALL)
        )
        if (
            content is None
            or len(matches) != 1
            or content.count("<answer>") != 1
            or content.count("</answer>") != 1
            or len(matches[0].strip()) == 0
        ):
            result["status"] = "parser_failure"
        else:
            answer = matches[0].strip()
            result["answer"] = answer
            try:
                reward = _score_answer(args, task, answer)
                result["upstream_reward"] = reward
                result["status"] = "correct" if reward >= 1 else "incorrect"
            except (ValueError, TypeError, KeyError, IndexError, RuntimeError) as error:
                result["status"] = "scorer_failure"
                write_private(
                    args.output / f"{ordinal:04d}-scorer-error.json",
                    {"type": type(error).__name__, "traceback": traceback.format_exc()},
                )
    result["elapsed_seconds"] = response.elapsed_seconds
    result["item_elapsed_seconds"] = time.monotonic() - start
    return result


if __name__ == "__main__":
    try:
        run(arguments())
    except (Exception, KeyboardInterrupt):
        sys.stderr.write(
            "Benchmark stopped. Inspect the private output directory "
            "for failure evidence.\n"
        )
        sys.exit(1)
