# Copyright (c) 2026 inference contributors.
"""Opt-in measurement around the unchanged native evaluator; never a scorer.

Run via eval/scripts/run --measure-power. The public summary contains only
numeric observations, counts and fixed labels. Native traces and detailed
measurement records stay in the private run directory.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
import re
import signal
import subprocess
import sys
import time
from dataclasses import dataclass
from itertools import pairwise
from pathlib import Path
from types import FrameType

from bench.power import NANOSECONDS, PowerSampler, clock_anchor, integrate_power

CLOCK_TOLERANCE_NS = 50_000_000
PHASES = ("boot", "setup", "agent", "finalize", "scoring")
VERIFIERS_REVISION = "ef47b2e96284a00bdcfc1012b9624b0c41ee6a0e"


def mapping(value: object) -> dict[str, object]:
    """Validate an object without trusting arbitrary JSON types."""
    if not isinstance(value, dict):
        raise ValueError("Expected JSON object")
    result: dict[str, object] = {}
    for key, item in value.items():
        if not isinstance(key, str):
            raise ValueError("Expected string JSON keys")
        result[key] = item
    return result


def sequence(value: object) -> list[object]:
    """Validate a JSON array."""
    if not isinstance(value, list):
        raise ValueError("Expected JSON array")
    return list(value)


def number(value: object) -> float:
    """Reject missing, boolean and nonfinite numeric data."""
    if isinstance(value, bool) or not isinstance(value, (float, int)):
        raise ValueError("Expected finite number")
    result = float(value)
    if not math.isfinite(result):
        raise ValueError("Expected finite number")
    return result


@dataclass
class EpisodeObservation:
    """Sanitized observations of one upstream episode, not a new score."""

    ordinal: int
    operational_ok: bool
    recorded_error_count: int
    trace_count: int
    trace_rewards: list[float | None]
    reward_components: list[list[dict[str, float | None]]]
    weighted_reward: float | None
    full_reward_success: bool | None
    truncated: bool
    start_unix_ns: int | None
    end_unix_ns: int | None
    timing_failure: str | None


def observe_episode(value: object, ordinal: int) -> EpisodeObservation:
    """Read pinned Episode/Trace fields; preserve fractional and missing rewards."""
    episode = mapping(value)
    ok = episode.get("ok")
    if not isinstance(ok, bool):
        raise ValueError("Missing episode operational status")
    traces = [mapping(trace) for trace in sequence(episode.get("traces"))]
    error_count = len(sequence(episode.get("errors", [])))
    rewards: list[float | None] = []
    components: list[list[dict[str, float | None]]] = []
    starts: list[int] = []
    ends: list[int] = []
    timing_failure = None if traces else "no_trace_timestamps"
    truncated = False
    for trace in traces:
        error_count += len(sequence(trace.get("errors", [])))
        parts: list[dict[str, float | None]] = []
        values: list[float] = []
        for reward in mapping(trace.get("rewards", {})).values():
            if reward is None:
                parts.append({"score": None, "weight": None, "value": None})
                continue
            record = mapping(reward)
            score = number(record.get("score"))
            weight = number(record.get("weight", 1.0))
            weighted = number(score * weight)
            parts.append({"score": score, "weight": weight, "value": weighted})
            values.append(weighted)
        components.append(parts)
        rewards.append(
            number(math.fsum(values)) if parts and len(parts) == len(values) else None
        )
        calls = [mapping(call) for call in sequence(trace.get("calls", []))]
        completed_calls = [call for call in calls if call.get("error") is None]
        truncated |= trace.get("stop_condition") in (
            "max_turns",
            "max_input_tokens",
            "max_output_tokens",
            "max_total_tokens",
        ) or bool(
            completed_calls and completed_calls[-1].get("finish_reason") == "length"
        )
        try:
            timing = mapping(trace.get("timing"))
            start = number(timing.get("start"))
            phase_ends: list[float] = []
            for phase in PHASES:
                span = mapping(timing.get(phase, {}))
                lo = number(span.get("start", 0))
                hi = number(span.get("end", 0))
                if lo == 0 and hi == 0:
                    continue
                # An unfinished phase is not a serialized episode end.
                if lo < start or hi < lo or lo <= 0:
                    raise ValueError("Incomplete or reversed trace phase")
                phase_ends.append(hi)
            if start <= 0 or not phase_ends:
                raise ValueError("No usable trace envelope")
            starts.append(round(start * NANOSECONDS))
            ends.append(round(max(phase_ends) * NANOSECONDS))
        except ValueError:
            timing_failure = "missing_or_invalid_trace_timestamps"
    # Existing profiles are single-agent. Do not invent a multi-agent reducer.
    weighted_reward = rewards[0] if len(rewards) == 1 else None
    success = False if not ok else None
    if weighted_reward is not None and 0 <= weighted_reward <= 1:
        success = ok and traces[0].get("ok") is True and weighted_reward == 1.0
    return EpisodeObservation(
        ordinal=ordinal,
        operational_ok=ok,
        recorded_error_count=error_count,
        trace_count=len(traces),
        trace_rewards=rewards,
        reward_components=components,
        weighted_reward=weighted_reward,
        full_reward_success=success,
        truncated=truncated,
        start_unix_ns=min(starts) if timing_failure is None else None,
        end_unix_ns=max(ends) if timing_failure is None else None,
        timing_failure=timing_failure,
    )


def load_episodes(
    root: Path,
) -> tuple[list[EpisodeObservation], dict[str, object], bool]:
    """Consume only one fresh native run, counting malformed/torn records."""
    paths = sorted(root.glob("*/traces.jsonl"))
    episodes: list[EpisodeObservation] = []
    evidence: dict[str, object] = {"failures": [], "malformed_records": 0}
    failures: list[str] = []
    evidence["failures"] = failures
    if len(paths) != 1:
        failures.append("no_unique_native_traces_file")
        return episodes, evidence, False
    digest = hashlib.sha256()
    malformed = 0
    try:
        with paths[0].open("rb") as stream:
            for ordinal, raw in enumerate(stream, 1):
                digest.update(raw)
                try:
                    decoded: object = json.loads(raw)
                    episodes.append(observe_episode(decoded, ordinal))
                except (ValueError, UnicodeError, OverflowError):
                    malformed += 1
    except OSError:
        failures.append("native_traces_read_failed")
    evidence["traces_sha256"] = digest.hexdigest()
    evidence["malformed_records"] = malformed
    if malformed:
        failures.append("malformed_native_records")
    if not episodes:
        failures.append("no_native_episodes")
    c1 = False
    try:
        config_value: object = json.loads(
            (paths[0].parent / "configs/resolved/eval.json").read_bytes()
        )
        config = mapping(config_value)
        serve = config.get("serve")
        c1 = config.get("max_concurrent") == 1
        if serve is not None:
            server = mapping(serve)
            pool = mapping(server.get("pool"))
            c1 = (
                c1
                and server.get("max_concurrent") == 1
                and pool.get("num_workers") == 1
            )
    except (OSError, ValueError, UnicodeError):
        failures.append("resolved_concurrency_unavailable")
    return episodes, evidence, c1


def efficiency_report(
    root: Path,
    environment: str,
    sampler: PowerSampler,
    start: dict[str, int],
    end: dict[str, int],
    native_exit_code: int,
    interrupted_signal: int | None,
) -> tuple[dict[str, object], list[dict[str, object]]]:
    """Attribute C1 trace envelopes only; all attempt costs remain in totals."""
    episodes, trace_evidence, c1 = load_episodes(root)
    power = sampler.summary(start["monotonic_ns"], end["monotonic_ns"])
    interval = mapping(power["interval"])
    offset = start["unix_time_ns"] - start["monotonic_ns"]
    offsets = [end["unix_time_ns"] - end["monotonic_ns"]]
    offsets.extend(
        sample.unix_time_ns - sample.monotonic_ns for sample in sampler.samples
    )
    drift = max((abs(value - offset) for value in offsets), default=0)
    clock_stable = drift <= CLOCK_TOLERANCE_NS
    spans: list[tuple[int, int]] = []
    for episode in episodes:
        if episode.start_unix_ns is not None and episode.end_unix_ns is not None:
            spans.append((episode.start_unix_ns - offset, episode.end_unix_ns - offset))
    spans.sort()
    overlap = any(right[0] < left[1] for left, right in pairwise(spans))
    details: list[dict[str, object]] = []
    attributed_ns = 0
    attributed_joules = 0.0
    observed_intervals = 0
    timing_failures: dict[str, int] = {}
    for episode in episodes:
        reason = episode.timing_failure
        if not c1:
            reason = "resolved_run_not_c1"
        elif not clock_stable:
            reason = "host_clock_discontinuity"
        elif overlap:
            reason = "overlapping_trace_envelopes"
        task_interval = None
        if (
            reason is None
            and episode.start_unix_ns is not None
            and episode.end_unix_ns is not None
        ):
            lo = episode.start_unix_ns - offset
            hi = episode.end_unix_ns - offset
            if lo < start["monotonic_ns"] or hi > end["monotonic_ns"] or hi <= lo:
                reason = "trace_envelope_outside_measured_run"
            else:
                task_interval = integrate_power(
                    sampler.samples, lo, hi, sampler.max_gap_ns
                )
                attributed_ns += hi - lo
                observed = task_interval["observed_joules"]
                if observed is not None:
                    attributed_joules += number(observed)
                    observed_intervals += 1
        if reason is not None:
            timing_failures[reason] = timing_failures.get(reason, 0) + 1
        details.append({
            "episode_ordinal": episode.ordinal,
            "operational_ok": episode.operational_ok,
            "recorded_error_count": episode.recorded_error_count,
            "trace_count": episode.trace_count,
            "trace_weighted_rewards": episode.trace_rewards,
            "reward_components": episode.reward_components,
            "full_reward_success": episode.full_reward_success,
            "truncated": episode.truncated,
            "interval_scope": "persisted_trace_envelope_not_complete_attempt",
            "interval": task_interval,
            "timing_failure": reason,
        })
    successes = sum(episode.full_reward_success is True for episode in episodes)
    unknown_success = sum(episode.full_reward_success is None for episode in episodes)
    denominator_complete = not trace_evidence["failures"] and not unknown_success
    ratio_valid = denominator_complete and successes > 0 and native_exit_code == 0
    rewards = [
        episode.weighted_reward
        for episode in episodes
        if episode.weighted_reward is not None
    ]
    joules = interval["joules"]
    wall = number(interval["wall_seconds"])
    ratio_reasons: list[str] = []
    if successes == 0:
        ratio_reasons.append("zero_successful_task_rollouts")
    if not denominator_complete:
        ratio_reasons.append("incomplete_success_denominator")
    if native_exit_code != 0:
        ratio_reasons.append("native_run_did_not_exit_successfully")
    summary: dict[str, object] = {
        "schema_version": 1,
        "environment": environment,
        "verifiers_revision": VERIFIERS_REVISION,
        "native_exit_code": native_exit_code,
        "interrupted_signal": interrupted_signal,
        "cost_scope": "whole_native_cli_including_startup_scoring_failures_retries_teardown",
        "energy_scope": "selected_gpu_board_not_system_no_idle_subtraction",
        "success_definition": "single_trace_weighted_reward_exactly_1_and_episode_and_trace_ok",
        "success_unit": "task_rollout_not_unique_question_or_operational_completion",
        "success_denominator_complete": denominator_complete,
        "successful_task_rollouts": successes,
        "unknown_success_task_rollouts": unknown_success,
        "recorded_task_rollouts": len(episodes),
        "operational_completions": sum(episode.operational_ok for episode in episodes),
        "operational_failures": sum(not episode.operational_ok for episode in episodes),
        "episodes_with_recorded_errors": sum(
            episode.recorded_error_count > 0 for episode in episodes
        ),
        "truncated_task_rollouts": sum(episode.truncated for episode in episodes),
        "fractional_reward_task_rollouts": sum(0 < value < 1 for value in rewards),
        "reward_observations": len(rewards),
        "weighted_reward_sum": math.fsum(rewards) if rewards else None,
        "weighted_reward_mean": math.fsum(rewards) / len(rewards) if rewards else None,
        "total_wall_seconds": wall,
        "total_joules": joules,
        "observed_joules": interval["observed_joules"],
        "seconds_per_successful_task_rollout": wall / successes
        if ratio_valid
        else None,
        "joules_per_successful_task_rollout": number(joules) / successes
        if ratio_valid and joules is not None
        else None,
        "time_ratio_available": ratio_valid,
        "energy_ratio_available": ratio_valid and joules is not None,
        "ratio_unavailable_reasons": ratio_reasons,
        "power_measurement_status": "complete" if joules is not None else "incomplete",
        "resolved_c1": c1,
        "clock_alignment": {
            "method": "host_unix_to_monotonic_offset_at_cli_start",
            "max_observed_drift_ns": drift,
            "tolerance_ns": CLOCK_TOLERANCE_NS,
            "boundary_uncertainty_ns": max(
                start["uncertainty_ns"], end["uncertainty_ns"]
            ),
            "stable": clock_stable,
        },
        "trace_attribution": {
            "scope": "persisted_trace_envelopes_only_not_discarded_retries_or_full_episodes",
            "attributed_wall_seconds": attributed_ns / NANOSECONDS,
            "unattributed_wall_seconds": wall - attributed_ns / NANOSECONDS,
            "attributed_observed_joules": attributed_joules
            if observed_intervals
            else None,
            "timing_failures": timing_failures,
        },
        "trace_evidence": trace_evidence,
        "power": {key: value for key, value in power.items() if key != "gpu"},
    }
    return summary, details


def save_json(path: Path, value: object) -> None:
    """Write private JSON, refusing to overwrite earlier evidence."""
    with path.open("x", encoding="utf-8") as stream:
        stream.write(json.dumps(value, indent=2, allow_nan=False) + "\n")


@dataclass
class Arguments:
    """Typed namespace for the existing eval wrapper's optional sidecar."""

    environment: str = ""
    output_dir: str = ""
    working_directory: str = ""
    gpu: str = "0"
    interval_seconds: float = 0.5
    max_seconds: float = 86400.0
    max_samples: int = 200_000
    command: list[str] | None = None


@dataclass
class Interruption:
    """Mutable signal state, including whether a forwarded signal raced exit."""

    signum: int | None = None
    delivery_races: int = 0

    def request(self, signum: int, _frame: FrameType | None) -> None:
        """Defer process control and evidence writing to the normal flow."""
        if self.signum is None:
            self.signum = signum

    def forward(self, pid: int, signum: int) -> None:
        """Signal only the native process group we started."""
        try:
            os.killpg(pid, signum)
        except ProcessLookupError:
            self.delivery_races += 1


def main() -> int:
    """Run exactly the supplied native command and report measurement separately."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--environment", required=True)
    parser.add_argument("--output-dir", required=True)
    parser.add_argument("--working-directory", required=True)
    parser.add_argument("--gpu", default="0")
    parser.add_argument("--interval-seconds", type=float, default=0.5)
    parser.add_argument("--max-seconds", type=float, default=86400.0)
    parser.add_argument("--max-samples", type=int, default=200_000)
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = Arguments()
    parser.parse_args(namespace=args)
    command = args.command or []
    if command[:1] == ["--"]:
        command = command[1:]
    if not command or re.fullmatch(r"[a-z0-9-]+", args.environment) is None:
        parser.error("A native command and a safe environment label are required")
    try:
        sampler = PowerSampler(
            args.gpu, args.interval_seconds, args.max_seconds, args.max_samples
        )
    except ValueError as error:
        parser.error(str(error))
    os.umask(0o077)
    root = Path(args.output_dir)
    root.mkdir(parents=True, exist_ok=True)
    evidence_dir = root / "measurement"
    evidence_dir.mkdir()  # Fresh invocation only; do not mix resumed attempt costs.
    interruption = Interruption()
    previous = {
        sig: signal.signal(sig, interruption.request)
        for sig in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP)
    }
    code = 127
    launch_failure = None
    try:
        with sampler:
            start = clock_anchor()
            try:
                with subprocess.Popen(
                    command, cwd=args.working_directory, start_new_session=True
                ) as child:
                    termination_deadline = None
                    killed = False
                    try:
                        while True:
                            if (
                                interruption.signum is not None
                                and termination_deadline is None
                            ):
                                interruption.forward(child.pid, interruption.signum)
                                termination_deadline = time.monotonic() + 10
                            if (
                                termination_deadline is not None
                                and time.monotonic() >= termination_deadline
                                and not killed
                            ):
                                interruption.forward(child.pid, signal.SIGKILL)
                                killed = True
                            try:
                                code = child.wait(timeout=0.2)
                                break
                            except subprocess.TimeoutExpired:
                                continue
                    finally:
                        # Also reap descendants if the parent exits on a signal.
                        if interruption.signum is not None or child.poll() is None:
                            interruption.forward(child.pid, signal.SIGKILL)
                            child.wait(timeout=5)
            except OSError:
                launch_failure = "native_process_launch_or_control_failed"
            finally:
                end = clock_anchor()
        # Persist collection first, even if native trace parsing later fails.
        save_json(
            evidence_dir / "power-samples.json",
            {
                "schema_version": 1,
                "gpu": sampler.gpu,
                "start": start,
                "end": end,
                "samples": sampler.records(),
            },
        )
        summary, details = efficiency_report(
            root, args.environment, sampler, start, end, code, interruption.signum
        )
        summary["launch_failure"] = launch_failure
        summary["signal_delivery_races"] = interruption.delivery_races
        save_json(evidence_dir / "task-intervals.json", details)
        save_json(evidence_dir / "efficiency.json", summary)
        if (
            summary["total_joules"] is None
            or sampler.limit_reached
            or any(sample.error for sample in sampler.samples)
        ):
            print(
                "Power measurement incomplete; inspect measurement/efficiency.json (native rewards unchanged).",
                file=sys.stderr,
            )
        if not summary["success_denominator_complete"]:
            print(
                "Task-success denominator incomplete; inspect native trace evidence (native rewards unchanged).",
                file=sys.stderr,
            )
        print(
            f"Per-environment efficiency evidence: {evidence_dir / 'efficiency.json'}",
            file=sys.stderr,
        )
    finally:
        for sig, handler in previous.items():
            signal.signal(sig, handler)
    if interruption.signum is not None:
        return 128 + interruption.signum
    return 128 - code if code < 0 else code


if __name__ == "__main__":
    raise SystemExit(main())
