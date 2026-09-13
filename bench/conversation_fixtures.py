"""Static synthetic grounding fixtures; no inference or native agent compaction.

Observations are explicitly user-supplied synthetic records, not executed tools.
The arms do not contain intermediate model answers and do not measure interactive
error accumulation. Supply a fresh secrets.token_hex(32) seed for a new run.
"""

from __future__ import annotations

import hashlib
import json
import random
import re
from dataclasses import dataclass
from typing import Literal

MAX_CASE_INDEX = 1_000_000
FIELD_COUNT = 6

FIELDS = ("engine", "model", "precision", "context", "draft", "power")
ArmName = Literal["full_history", "fixed_summary", "direct_control"]
ParseStatus = Literal["valid", "malformed_json", "invalid_schema"]


@dataclass(frozen=True)
class Message:
    """One synthetic chat message."""

    role: Literal["system", "user"]
    content: str


@dataclass(frozen=True)
class Observation:
    """One timestamped ledger observation."""

    observation_id: str
    entity_id: str
    timestamp: str
    field: str
    value: str


@dataclass(frozen=True)
class ExpectedField:
    """Authoritative value and evidence for one field."""

    field: str
    value: str
    observation_id: str
    stale_values: tuple[str, ...]


@dataclass(frozen=True)
class Arm:
    """One matched diagnostic prompt arm."""

    name: ArmName
    messages: tuple[Message, ...]


@dataclass(frozen=True)
class Fixture:
    """A synthetic ledger with three matched prompt arms."""

    case_id: str
    entity_id: str
    observations: tuple[Observation, ...]
    expected: tuple[ExpectedField, ...]
    arms: tuple[Arm, ...]
    scope: str = "static_synthetic_history_not_native_compaction"


@dataclass(frozen=True)
class Score:
    """Field and evidence scoring counts."""

    parse_status: ParseStatus
    all_fields_correct: bool
    exact_answer: bool
    field_correct: int
    evidence_correct: int
    stale_values: int
    unsupported_values: int
    field_total: int = 6


class InvalidJSON(ValueError):
    """JSON contains duplicate keys or non-finite literals."""


def _unique_object(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            message = "duplicate JSON key"
            raise InvalidJSON(message)
        result[key] = value
    return result


def _reject_constant(value: str) -> object:
    message = "non-finite JSON literal: " + value
    raise InvalidJSON(message)


def _record(observation: Observation) -> dict[str, str]:
    return {
        "observation_id": observation.observation_id,
        "entity_id": observation.entity_id,
        "timestamp": observation.timestamp,
        "field": observation.field,
        "value": observation.value,
    }


def generate_fixture(seed: str, case_index: int = 0) -> Fixture:
    """Generate three matched arms from a 64-hex-character external seed.

    A valid seed has 256-bit capacity; the caller must obtain actual entropy.
    Case index is domain-separated into deterministic generation. The fixture
    stores expected answers separately from submitted messages.

    Returns:
        The deterministic ledger and matched prompt arms.

    Raises:
        ValueError: The seed, index, or generated summary is invalid.

    """
    if not isinstance(seed, str) or re.fullmatch(r"[0-9a-fA-F]{64}", seed) is None:
        message = "seed must contain exactly 64 hexadecimal characters"
        raise ValueError(message)
    if isinstance(case_index, bool) or not isinstance(case_index, int):
        message = "case_index must be an integer"
        raise ValueError(message)
    if case_index < 0 or case_index > MAX_CASE_INDEX:
        message = "case_index must be between 0 and 1000000"
        raise ValueError(message)
    material = (
        bytes.fromhex(seed) + b"conversation-fixture-v1" + str(case_index).encode()
    )
    digest = hashlib.sha256(material).digest()
    rng = random.Random(int.from_bytes(digest, "big"))
    entity = "deployment-" + f"{rng.getrandbits(96):024x}"
    observations: list[Observation] = []
    # Distinct prefixes/counters guarantee uniqueness even if random suffixes collide.
    for index, field in enumerate(FIELDS):
        observations.append(
            Observation(
                f"obs-{index:02d}-{rng.getrandbits(96):024x}",
                entity,
                f"2031-04-05T10:{index:02d}:00Z",
                field,
                f"{field}-initial-{rng.getrandbits(64):016x}",
            )
        )
    updated = rng.sample(list(FIELDS), 3)
    for index, field in enumerate(updated, start=6):
        observations.append(
            Observation(
                f"obs-{index:02d}-{rng.getrandbits(96):024x}",
                entity,
                f"2031-04-05T11:{index:02d}:00Z",
                field,
                f"{field}-updated-{rng.getrandbits(64):016x}",
            )
        )
    # Older snapshots arrive last. Their arrival order is not authoritative.
    for index, field in enumerate(rng.sample(list(FIELDS), 3), start=9):
        observations.append(
            Observation(
                f"obs-{index:02d}-{rng.getrandbits(96):024x}",
                entity,
                f"2031-04-05T09:{index:02d}:00Z",
                field,
                f"{field}-archived-{rng.getrandbits(64):016x}",
            )
        )
    current: list[Observation] = []
    expected: list[ExpectedField] = []
    for field in FIELDS:
        candidates = [item for item in observations if item.field == field]
        latest = max(candidates, key=lambda item: item.timestamp)
        current.append(latest)
        expected.append(
            ExpectedField(
                field,
                latest.value,
                latest.observation_id,
                tuple(
                    item.value
                    for item in candidates
                    if item.observation_id != latest.observation_id
                ),
            )
        )
    summary = {
        item.field: {"value": item.value, "observation_id": item.observation_id}
        for item in current
    }
    # Validate all summary facts against the independently retained ledger selection.
    for item in expected:
        entry = summary.get(item.field)
        if (
            entry is None
            or entry["value"] != item.value
            or entry["observation_id"] != item.observation_id
        ):
            message = "generated summary does not match authoritative ledger"
            raise ValueError(message)
    return Fixture(
        "conversation-v1-" + digest.hex()[:24],
        entity,
        tuple(observations),
        tuple(expected),
        _prompt_arms(entity, observations, current, summary),
    )


def _prompt_arms(
    entity: str,
    observations: list[Observation],
    current: list[Observation],
    summary: dict[str, dict[str, str]],
) -> tuple[Arm, ...]:
    instruction = Message(
        "system",
        (
            "Track a fictitious deployment using only the supplied synthetic "
            "observations. "
            "These are user-supplied records, not real tool execution. All "
            "observations "
            "are authoritative for their recorded time. For each field use the "
            "greatest "
            "timestamp, not the last-arriving record. Values are opaque identifiers; "
            "do not infer real hardware facts. A supplied validated summary gives the "
            "current values and their original observation IDs. Return exactly one "
            "JSON "
            "object with exactly these six keys: engine, model, precision, "
            "context, draft, "
            "power. Each key must map to an object with exactly two string keys: value "
            "and observation_id. No Markdown, commentary, extra keys, or omitted "
            "fields."
        ),
    )
    question = Message(
        "user",
        f"Return the current six fields and supporting observation IDs for {entity}.",
    )
    history = tuple(
        Message(
            "user",
            "Synthetic observation: " + json.dumps(_record(item), sort_keys=True),
        )
        for item in observations
    )
    summary_message = Message(
        "user",
        (
            f"Programmatically validated synthetic current-state summary for {entity} "
            "(not native agent compaction): " + json.dumps(summary, sort_keys=True)
        ),
    )
    direct = Message(
        "user",
        "Current authoritative synthetic observations: "
        + json.dumps(
            [_record(item) for item in current],
            sort_keys=True,
        ),
    )
    return (
        Arm("full_history", (instruction, *history, question)),
        Arm("fixed_summary", (instruction, summary_message, question)),
        Arm("direct_control", (instruction, direct, question)),
    )


def score_answer(answer: str, fixture: Fixture) -> Score:
    """Score strict final JSON only; malformed/schema failures receive zero credit.

    Evidence correctness is scored independently from value correctness.
    A stale value appeared in an older observation for that same field. An
    unsupported value is neither the current nor a stale value for that field.

    Returns:
        Parse status and independent field and evidence counts.

    Raises:
        TypeError: The answer or fixture has an invalid type.
        ValueError: Expected fields do not match the ledger fields.

    """
    if not isinstance(answer, str):
        message = "answer must be a string"
        raise TypeError(message)
    if not isinstance(fixture, Fixture):
        message = "fixture must be a Fixture"
        raise TypeError(message)
    if len(fixture.expected) != len(FIELDS) or {
        item.field for item in fixture.expected
    } != set(FIELDS):
        message = "fixture expected fields must contain each ledger field exactly once"
        raise ValueError(message)
    try:
        parsed: object = json.loads(
            answer,
            object_pairs_hook=_unique_object,
            parse_constant=_reject_constant,
        )
    except (json.JSONDecodeError, InvalidJSON, RecursionError):
        return Score(
            "malformed_json",
            all_fields_correct=False,
            exact_answer=False,
            field_correct=0,
            evidence_correct=0,
            stale_values=0,
            unsupported_values=0,
        )
    if not isinstance(parsed, dict) or set(parsed) != set(FIELDS):
        return Score(
            "invalid_schema",
            all_fields_correct=False,
            exact_answer=False,
            field_correct=0,
            evidence_correct=0,
            stale_values=0,
            unsupported_values=0,
        )
    values: dict[str, tuple[str, str]] = {}
    for field in FIELDS:
        entry: object = parsed[field]
        if not isinstance(entry, dict) or set(entry) != {"value", "observation_id"}:
            return Score(
                "invalid_schema",
                all_fields_correct=False,
                exact_answer=False,
                field_correct=0,
                evidence_correct=0,
                stale_values=0,
                unsupported_values=0,
            )
        value: object = entry["value"]
        observation_id: object = entry["observation_id"]
        if not isinstance(value, str) or not isinstance(observation_id, str):
            return Score(
                "invalid_schema",
                all_fields_correct=False,
                exact_answer=False,
                field_correct=0,
                evidence_correct=0,
                stale_values=0,
                unsupported_values=0,
            )
        values[field] = (value, observation_id)
    return _score_values(values, fixture)


def _score_values(values: dict[str, tuple[str, str]], fixture: Fixture) -> Score:
    correct = evidence = stale = unsupported = 0
    for item in fixture.expected:
        value, observation_id = values[item.field]
        if value == item.value:
            correct += 1
        elif value in item.stale_values:
            stale += 1
        else:
            unsupported += 1
        if observation_id == item.observation_id:
            evidence += 1
    return Score(
        "valid",
        correct == FIELD_COUNT,
        correct == FIELD_COUNT and evidence == FIELD_COUNT,
        correct,
        evidence,
        stale,
        unsupported,
    )
