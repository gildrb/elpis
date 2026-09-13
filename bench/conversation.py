"""Static synthetic conversation grounding diagnostic; not native compaction."""

from __future__ import annotations

import argparse
import hashlib
import re
import secrets
import sys
import time
import traceback
from dataclasses import asdict, dataclass
from pathlib import Path

import httpx
from conversation_fixtures import Arm, Fixture, generate_fixture, score_answer
from pydantic import BaseModel, ConfigDict, Field, JsonValue
from transport import (
    ApiFailure,
    ArtifactTarget,
    ChatMessage,
    Choice,
    CompletedRequest,
    RequestSettings,
    canonical,
    decode,
    digest,
    read_bounded,
    request_completion,
    write_private,
)

MAX_CASE_COUNT = 100


class Frozen(BaseModel):
    """Source-bound settings and fixture commitments for exact replay."""

    model_config = ConfigDict(extra="forbid", strict=True)
    schema_version: int = Field(ge=1, le=1)
    settings: dict[str, JsonValue]
    seed_commitment: str = Field(pattern=r"^[0-9a-f]{64}$")
    fixture_digests: list[str] = Field(min_length=1, max_length=100)
    prompt_digests: list[str] = Field(min_length=3, max_length=300)


def arguments() -> argparse.Namespace:
    """Parse and validate diagnostic command-line settings.

    Returns:
        The validated command-line namespace.

    """
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument(
        "--count",
        type=int,
        default=12,
        help="Matched cases, each with three arms; 1..100",
    )
    parser.add_argument("--generate-only", action="store_true")
    parser.add_argument("--replay-from", type=Path)
    parser.add_argument("--endpoint", default="http://127.0.0.1:18020/v1")
    parser.add_argument("--key-file", type=Path)
    parser.add_argument("--model", default="qwen3.8-27b")
    parser.add_argument("--model-identity")
    parser.add_argument(
        "--thinking", choices=("enabled", "disabled"), default="enabled"
    )
    parser.add_argument("--max-tokens", type=int, default=8192)
    parser.add_argument("--timeout", type=int, default=600)
    args = parser.parse_args()
    if not 1 <= args.count <= MAX_CASE_COUNT:
        parser.error("count must be 1..100")
    if not args.generate_only and (
        args.key_file is None or args.model_identity is None
    ):
        parser.error("inference requires key-file and immutable model-identity")
    if args.model_identity is not None and len(args.model_identity.strip()) == 0:
        parser.error("model-identity must not be blank")
    return args


def run(args: argparse.Namespace) -> None:
    """Create an exclusive private output directory and run the diagnostic."""
    request = RequestSettings(
        endpoint=args.endpoint,
        model=args.model,
        thinking=args.thinking,
        max_tokens=args.max_tokens,
        timeout=args.timeout,
    )
    base = Path(__file__).resolve().parent
    settings = {
        "count": args.count,
        "endpoint_sha256": digest(request.endpoint),
        "model": request.model,
        "model_identity": args.model_identity,
        "thinking": request.thinking,
        "max_tokens": request.max_tokens,
        "timeout": request.timeout,
        "temperature": 0,
        "concurrency": 1,
        "scope": "static_synthetic_history_not_native_compaction",
        "arm_order": "rotate_full_history_fixed_summary_direct_control_by_case_index",
        "python_version": sys.version,
        "runner_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "fixture_source_sha256": hashlib.sha256(
            (base / "conversation_fixtures.py").read_bytes()
        ).hexdigest(),
        "transport_sha256": hashlib.sha256(
            (base / "transport.py").read_bytes()
        ).hexdigest(),
        "lock_sha256": hashlib.sha256(
            (base.parent / "uv.lock").read_bytes()
        ).hexdigest(),
    }
    args.output.mkdir(mode=0o700, parents=False, exist_ok=False)
    Path(args.output).chmod(0o700)
    try:
        execute(args, request, settings)
    except BaseException:
        write_private(
            args.output / "failure.json", {"traceback": traceback.format_exc()}
        )
        raise


def _prepare_seed(
    args: argparse.Namespace,
    settings: dict[str, JsonValue],
) -> tuple[str, str, Frozen | None]:
    previous: Frozen | None = None
    if args.replay_from is not None:
        previous = Frozen.model_validate(
            decode(read_bounded(args.replay_from / "frozen.json"))
        )
        if canonical(previous.settings) != canonical(settings):
            message = "Replay settings/model/source/lock mismatch"
            raise ValueError(message)
        seed_value = decode(read_bounded(args.replay_from / "seed.json"))
        if (
            not isinstance(seed_value, str)
            or re.fullmatch(r"[0-9a-f]{64}", seed_value) is None
        ):
            message = "Invalid replay seed"
            raise ValueError(message)
        seed = seed_value
    else:
        seed = secrets.token_hex(32)
    seed_commitment = digest({"domain": "conversation-benchmark-v1", "seed": seed})
    if previous is not None and previous.seed_commitment != seed_commitment:
        message = "Replay seed commitment mismatch"
        raise ValueError(message)
    write_private(args.output / "seed.json", seed)
    write_private(
        args.output / "commitment.json",
        {"settings": settings, "seed_commitment": seed_commitment},
    )
    return seed, seed_commitment, previous


def _prepare_fixtures(
    args: argparse.Namespace,
    settings: dict[str, JsonValue],
) -> tuple[list[Fixture], Frozen]:
    seed, seed_commitment, previous = _prepare_seed(args, settings)
    fixtures: list[Fixture] = []
    fixture_digests: list[str] = []
    prompt_digests: list[str] = []
    seen: set[str] = set()
    for index in range(args.count):
        fixture = generate_fixture(seed, index)
        fixture_value = asdict(fixture)
        oracle = {
            item.field: {"value": item.value, "observation_id": item.observation_id}
            for item in fixture.expected
        }
        oracle_score = score_answer(canonical(oracle).decode(), fixture)
        if not oracle_score.exact_answer:
            message = "Fixture oracle integrity failed"
            raise ValueError(message)
        fixture_digests.append(digest(fixture_value))
        if previous is not None:
            prior_fixture = decode(
                read_bounded(args.replay_from / f"{index:03d}-fixture.json")
            )
            if canonical(prior_fixture) != canonical(fixture_value):
                message = "Replay fixture mismatch"
                raise ValueError(message)
        for arm in fixture.arms:
            prompt_hash = digest([asdict(message) for message in arm.messages])
            if prompt_hash in seen:
                message = "Duplicate conversation prompt"
                raise ValueError(message)
            seen.add(prompt_hash)
            prompt_digests.append(prompt_hash)
        fixtures.append(fixture)
        write_private(args.output / f"{index:03d}-fixture.json", fixture_value)
    frozen = Frozen(
        schema_version=1,
        settings=settings,
        seed_commitment=seed_commitment,
        fixture_digests=fixture_digests,
        prompt_digests=prompt_digests,
    )
    if previous is not None and canonical(previous.model_dump()) != canonical(
        frozen.model_dump()
    ):
        message = "Replay frozen fixture/prompt digest mismatch"
        raise ValueError(message)
    write_private(args.output / "frozen.json", frozen.model_dump())
    return fixtures, frozen


@dataclass
class _Totals:
    elapsed_total: float = 0.0
    item_elapsed_total: float = 0.0
    output_total: int = 0
    usage_count: int = 0


def _score_choice(
    choice: Choice,
    fixture: Fixture,
    row: dict[str, int],
    result: dict[str, JsonValue],
) -> None:
    result["finish_reason"] = choice.finish_reason
    if choice.finish_reason == "length":
        row["truncation"] += 1
        result["status"] = "truncation"
    elif choice.finish_reason != "stop":
        row["api_failure"] += 1
        result["status"] = "api_failure"
    elif choice.message.content is None:
        row["parser_failure"] += 1
        result["status"] = "parser_failure"
    else:
        score = score_answer(choice.message.content, fixture)
        result["score"] = asdict(score)
        if score.parse_status != "valid":
            row["parser_failure"] += 1
            result["status"] = "parser_failure"
        else:
            result["status"] = "correct" if score.exact_answer else "incorrect"
            row["full_credit"] += int(score.exact_answer)
            row["all_values_correct"] += int(score.all_fields_correct)
            row["field_correct"] += score.field_correct
            row["evidence_correct"] += score.evidence_correct
            row["stale_values"] += score.stale_values
            row["unsupported_values"] += score.unsupported_values


def _record_response(
    response: ApiFailure | CompletedRequest,
    fixture: Fixture,
    row: dict[str, int],
    result: dict[str, JsonValue],
    totals: _Totals,
) -> None:
    if isinstance(response, ApiFailure):
        row["api_failure"] += 1
        result["status"] = "api_failure"
    else:
        completion = response.completion
        if completion.usage is not None:
            result["usage"] = completion.usage.model_dump(exclude_none=True)
            totals.output_total += completion.usage.completion_tokens
            totals.usage_count += 1
        _score_choice(completion.choices[0], fixture, row, result)


@dataclass
class _Inference:
    request: RequestSettings
    key: str
    output: Path
    counts: dict[str, dict[str, int]]
    totals: _Totals

    def record(
        self,
        client: httpx.Client,
        fixture: Fixture,
        arm: Arm,
        index: int,
        ordinal: int,
    ) -> None:
        start = time.monotonic()
        messages = tuple(
            ChatMessage(role=message.role, content=message.content)
            for message in arm.messages
        )
        response = request_completion(
            client,
            self.request,
            self.key,
            messages,
            ArtifactTarget(self.output, f"{ordinal:04d}"),
        )
        row = self.counts[arm.name]
        row["completed"] += 1
        result: dict[str, JsonValue] = {
            "case_index": index,
            "arm": arm.name,
            "ordinal": ordinal,
        }
        _record_response(response, fixture, row, result, self.totals)
        elapsed = time.monotonic() - start
        self.totals.item_elapsed_total += elapsed
        self.totals.elapsed_total += response.elapsed_seconds
        result["item_elapsed_seconds"] = elapsed
        result["elapsed_seconds"] = response.elapsed_seconds
        write_private(self.output / f"{ordinal:04d}-result.json", result)
        write_private(
            self.output / f"checkpoint-{ordinal:04d}.json",
            {"completed": ordinal + 1, "arms": self.counts},
        )

    def collect(self, fixtures: list[Fixture]) -> None:
        with httpx.Client(
            timeout=self.request.timeout,
            follow_redirects=False,
            trust_env=False,
        ) as client:
            ordinal = 0
            for index, fixture in enumerate(fixtures):
                offset = index % 3
                ordered = fixture.arms[offset:] + fixture.arms[:offset]
                for arm in ordered:
                    self.record(client, fixture, arm, index, ordinal)
                    ordinal += 1


def execute(
    args: argparse.Namespace,
    request: RequestSettings,
    settings: dict[str, JsonValue],
) -> None:
    """Freeze verified fixtures, collect selected requests, and write the summary."""
    fixtures, frozen = _prepare_fixtures(args, settings)
    arms = ("full_history", "fixed_summary", "direct_control")
    counts = {
        arm: {
            "completed": 0,
            "full_credit": 0,
            "all_values_correct": 0,
            "field_correct": 0,
            "evidence_correct": 0,
            "stale_values": 0,
            "unsupported_values": 0,
            "parser_failure": 0,
            "api_failure": 0,
            "truncation": 0,
        }
        for arm in arms
    }
    totals = _Totals()
    if not args.generate_only:
        inference = _Inference(
            request,
            read_bounded(args.key_file, 16384).strip(),
            args.output,
            counts,
            totals,
        )
        inference.collect(fixtures)
    completed = sum(row["completed"] for row in counts.values())
    summary = {
        "schema_version": 1,
        "scope": settings["scope"],
        "generate_only": args.generate_only,
        "cases": args.count,
        "planned_requests": args.count * 3,
        "completed_requests": completed,
        "arms": counts,
        "field_denominator_per_completed_request": 6,
        "threshold": None,
        "thinking": request.thinking,
        "max_tokens": request.max_tokens,
        "concurrency": 1,
        "model_identity_sha256": digest(args.model_identity),
        "frozen_sha256": digest(frozen.model_dump()),
        "request_elapsed_seconds": totals.elapsed_total,
        "item_elapsed_seconds": totals.item_elapsed_total,
        "completion_tokens": totals.output_total,
        "usage_available_count": totals.usage_count,
        "end_to_end_output_tokens_per_second": totals.output_total
        / totals.elapsed_total
        if totals.elapsed_total > 0 and totals.usage_count == completed
        else None,
    }
    write_private(args.output / "summary.json", summary)
    sys.stdout.write(canonical(summary).decode() + "\n")


if __name__ == "__main__":
    try:
        run(arguments())
    except (Exception, KeyboardInterrupt):
        sys.stderr.write(
            "Conversation diagnostic stopped. Inspect its private output "
            "for failure evidence.\n"
        )
        sys.exit(1)
