# Copyright (c) 2026 inference contributors.
"""Finite EXL3 + Bend lane: one explicitly selected suite; see autoresearch.sh.

Suites: ``broad`` (native tasksets + C1 whole requests) and ``prefill`` (the
cold-prefill TTFT ladder in ``bench.prefill``). This supervisor never operates
Docker lifecycle, promotion, power policy or the maintenance guardian. The
latter must independently recover the owned candidate. Only the unchanged
native taskset producers, frozen requests and raw-evidence replays admit results.
"""

from __future__ import annotations

import ctypes
import hashlib
import json
import math
import os
import re
import select
import signal
import stat
import subprocess
import sys
import time
from collections.abc import Callable
from dataclasses import dataclass
from pathlib import Path
from types import FrameType

from bench import exl3, prefill
from bench.exl3 import mapping, number, sequence

ROOT = Path(__file__).resolve().parents[1]
ENDPOINT = exl3.ENDPOINT
OPERATOR = Path("/run/user/1000/eta-autoresearch-operator.json")
LIMIT_SECONDS = 2400
RECOVERY_HEADROOM_SECONDS = 120
TERMINATION_SECONDS = 20
LEASE = Path("/run/user/1000/qwen-packed64-docker-gpu0-maintenance.lock")
LAUNCH_LOCK = Path("/mnt/ssd/storage/ai/qwen3.8-27b/qwen-inference-launch.lock")
LAUNCH_IDENTITY = {
    "dev": 66305,
    "ino": 23726380,
    "uid": 1000,
    "mode": 0o600,
    "nlink": 1,
}
TASKSET_METRICS = ("output_tok_s", "reward", "truncated")
# Every rejected observation is recorded privately; nothing is retried.
FAILURES = (
    OSError,
    ValueError,
    KeyError,
    TypeError,
    RuntimeError,
    subprocess.SubprocessError,
)


def require(condition: bool, message: str) -> None:
    """Reject invalid boundary inputs and incomplete observations."""
    exl3.require(condition, message)


def file_identity(info: os.stat_result) -> dict[str, int]:
    """Match the guardian's inode/owner/private-mode identity contract."""
    return {
        "dev": info.st_dev,
        "ino": info.st_ino,
        "uid": info.st_uid,
        "mode": stat.S_IMODE(info.st_mode),
        "nlink": info.st_nlink,
    }


def private_read(path: Path, *, key: bool = False) -> tuple[bytes, dict[str, int]]:
    """Read one bounded private file, refusing symlinks and identity races."""
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_CLOEXEC | os.O_NONBLOCK)
    with os.fdopen(fd, "rb") as stream:
        info = os.fstat(stream.fileno())
        identity = file_identity(info)
        require(
            stat.S_ISREG(info.st_mode)
            and info.st_uid == os.getuid()
            and info.st_nlink == 1
            and stat.S_IMODE(info.st_mode) in ((0o400, 0o600) if key else (0o600,)),
            "Unsafe private file",
        )
        raw = stream.read(4097 if key else 65537)
        require(len(raw) <= (4096 if key else 65536), "Private file exceeds bound")
        require(
            identity == file_identity(path.stat(follow_symlinks=False)),
            "Private file changed while reading",
        )
    return raw, identity


def private_directory(path: Path) -> dict[str, int]:
    """Require the existing canonical private directory used by the guardian."""
    require(
        path.is_absolute() and path.resolve(strict=True) == path,
        "Maintenance directory must be canonical and absolute",
    )
    info = path.stat(follow_symlinks=False)
    require(
        stat.S_ISDIR(info.st_mode)
        and info.st_uid == os.getuid()
        and stat.S_IMODE(info.st_mode) == 0o700,
        "Unsafe maintenance directory",
    )
    return {"dev": info.st_dev, "ino": info.st_ino, "uid": info.st_uid, "mode": 0o700}


def process_start(pid: int) -> str:
    """Bind a live process to its Linux start-time tick, not just a reused PID."""
    fields = (Path("/proc") / str(pid) / "stat").read_text().rsplit(")", 1)[1].split()
    require(fields[0] not in ("Z", "X"), "Guardian process is not live")
    return fields[19]


def api_key(path: Path) -> str:
    """Load the validated private bearer key; it is never written to evidence."""
    raw, _ = private_read(path, key=True)
    key = raw.removesuffix(b"\n")
    require(
        bool(key) and all(33 <= char <= 126 for char in key),
        "Invalid private API key",
    )
    return key.decode("ascii")


@dataclass(frozen=True)
class Settings:
    """Explicit operator-owned inputs; workload/endpoint are not tunable knobs."""

    container: str
    key_file: Path
    maintenance: Path
    output: Path
    operator_raw: bytes
    operator_identity: dict[str, int]
    operator_sha256: str

    @classmethod
    def descriptor(cls) -> Settings:
        """Load the one private descriptor without inferring any operator input."""
        require(
            OPERATOR.resolve(strict=True) == OPERATOR, "Operator path is not canonical"
        )
        raw, identity = private_read(OPERATOR)
        value = mapping(exl3.loads(raw))
        require(
            set(value)
            == {
                "schema_version",
                "container_id",
                "api_key_file",
                "maintenance_directory",
                "output_directory",
            },
            "Unexpected operator descriptor keys",
        )
        require(
            exl3.integer(value.get("schema_version")) == 1,
            "Unsupported operator descriptor schema",
        )
        container = exl3.text(value.get("container_id"))
        require(
            re.fullmatch(r"[0-9a-f]{64}", container) is not None,
            "Owned container must be its full immutable ID",
        )
        values = [
            exl3.text(value.get(name))
            for name in ("api_key_file", "maintenance_directory", "output_directory")
        ]
        require(
            all(
                all(ord(char) >= 32 and ord(char) != 127 for char in value)
                for value in values
            ),
            "Invalid input path",
        )
        paths = [Path(value) for value in values]
        require(
            all(
                path.is_absolute() and str(path) == value
                for path, value in zip(paths, values)
            ),
            "Input paths must be canonical and absolute",
        )
        require(paths[0].resolve(strict=True) == paths[0], "Key path must be canonical")
        require(
            paths[2].parent.resolve(strict=True) == paths[2].parent,
            "Output parent must already exist and be canonical",
        )
        require(
            paths[2].resolve(strict=False) == paths[2],
            "Output path must be canonical",
        )
        _ = api_key(paths[0])
        return cls(
            container,
            paths[0],
            paths[1],
            paths[2],
            raw,
            identity,
            hashlib.sha256(raw).hexdigest(),
        )


def guard(settings: Settings) -> dict[str, object]:
    """Verify existing guardian ownership without acquiring or changing its locks."""
    require(
        os.getuid() == os.geteuid() == 1000, "Guardian contract requires owner uid1000"
    )
    require(OPERATOR.resolve(strict=True) == OPERATOR, "Operator path is not canonical")
    operator_raw, operator_identity = private_read(OPERATOR)
    require(
        operator_identity == settings.operator_identity
        and operator_raw == settings.operator_raw,
        "Operator descriptor changed during benchmark",
    )
    directory = private_directory(settings.maintenance)
    raw, _ = private_read(settings.maintenance / "status.json")
    state = mapping(exl3.loads(raw))
    _ = exl3.canonical(state)
    require(
        state.get("schema") == 1
        and state.get("state") == "armed"
        and state.get("phase") == "candidate_started",
        "Maintenance window is not armed on candidate",
    )
    require(
        state.get("directory_identity") == directory,
        "Maintenance directory identity changed",
    )
    require(
        state.get("boot_id")
        == Path("/proc/sys/kernel/random/boot_id").read_text().strip(),
        "Foreign maintenance boot",
    )
    require(
        not os.path.lexists(settings.maintenance / "control.json"),
        "Recovery/promotion already queued",
    )
    candidate = mapping(state.get("candidate"))
    require(
        candidate.get("id") == settings.container,
        "Candidate is not owned by this guardian",
    )
    require(state.get("lease_path") == str(LEASE), "Unexpected guardian lease")
    _, lease_identity = private_read(LEASE)
    _, launch_identity = private_read(LAUNCH_LOCK)
    _, mutex_identity = private_read(settings.maintenance / "operation.lock")
    require(
        lease_identity == state.get("lease_identity")
        and launch_identity == state.get("launch_lock_identity") == LAUNCH_IDENTITY
        and mutex_identity == state.get("operation_mutex_identity"),
        "Maintenance lock identity changed",
    )
    pid = exl3.integer(state.get("guardian_pid"))
    require(
        pid > 1 and process_start(pid) == state.get("guardian_start"),
        "Guardian process changed",
    )
    require(
        (Path("/proc") / str(pid)).stat().st_uid == os.getuid(),
        "Foreign guardian owner",
    )
    # flock ownership is read from the kernel, not inferred from an unlocked file.
    held = False
    for row in Path("/proc/locks").read_text().splitlines():
        fields = row.split()
        if (
            len(fields) < 6
            or fields[1:4] != ["FLOCK", "ADVISORY", "WRITE"]
            or fields[4] != str(pid)
        ):
            continue
        device = fields[5].split(":")
        if len(device) == 3 and (
            int(device[0], 16),
            int(device[1], 16),
            int(device[2]),
        ) == (
            os.major(lease_identity["dev"]),
            os.minor(lease_identity["dev"]),
            lease_identity["ino"],
        ):
            held = True
    require(held, "Guardian does not hold the maintenance lease")
    require(
        number(state.get("deadline_monotonic")) - time.monotonic()
        > RECOVERY_HEADROOM_SECONDS,
        "Insufficient recovery headroom",
    )
    return state


def verify_container(settings: Settings, state: dict[str, object]) -> None:
    """Check only public Docker identity fields before authenticated API probes."""
    template = (
        '{"id":{{json .Id}},"image":{{json .Image}},"name":{{json .Name}},'
        '"running":{{json .State.Running}},"ports":{{json .NetworkSettings.Ports}},'
        '"network":{{json .HostConfig.NetworkMode}}}'
    )
    value = mapping(
        json.loads(
            exl3.docker(
                "container",
                "inspect",
                "--format",
                template,
                settings.container,
            )
        )
    )
    candidate = mapping(state.get("candidate"))
    require(
        all(value.get(key) == candidate.get(key) for key in ("id", "image", "name"))
        and value.get("running") is True
        and value.get("network") != "host",
        "Owned serving instance differs from guardian candidate",
    )
    require(
        mapping(value.get("ports")).get("18020/tcp")
        == [
            {"HostIp": "127.0.0.1", "HostPort": "18020"},
        ],
        "Owned candidate must exclusively publish the fixed loopback endpoint",
    )


def run_producer(
    settings: Settings,
    name: str,
    command: list[str],
    cwd: Path,
    env: dict[str, str],
) -> None:
    """Run once, preserving private native output; no retries or score selection."""
    guard(settings)
    with (
        (settings.output / "logs" / f"{name}.stdout").open("xb") as stdout,
        (settings.output / "logs" / f"{name}.stderr").open("xb") as stderr,
    ):
        result = subprocess.run(
            command,
            cwd=cwd,
            env=env,
            stdin=subprocess.DEVNULL,
            stdout=stdout,
            stderr=stderr,
            check=False,
        )
    exl3.save(
        settings.output / name / "provenance/producer-exit.json",
        {"returncode": result.returncode},
    )
    require(
        result.returncode == 0,
        f"Native {name} command failed; retained artifacts are incomplete",
    )
    guard(settings)


def model_call_observations(
    evidence: exl3.Evidence,
    directory: Path,
    expected_episode_count: int,
) -> dict[str, object]:
    """Pool every native model call, including graded incorrect/truncated answers.

    Verifiers ModelCall.time is Unix wall time from request send through fully
    received response. Usage.completion_tokens already includes reasoning tokens.
    This is whole-model-call throughput, not SSE committed-decode/GPU timing.
    """
    require(
        type(expected_episode_count) is int and expected_episode_count > 0,
        "Expected a positive exact native episode count",
    )
    paths = list(directory.glob("*/traces.jsonl"))
    require(len(paths) == 1, "Missing unique native trace file")
    path = evidence.retain(paths[0])
    observations: list[dict[str, object]] = []
    durations: list[float] = []
    total_tokens = 0
    total_input_tokens = 0
    episodes = 0
    with path.open("rb") as stream:
        for ordinal, raw in enumerate(stream):
            episode_value: object = json.loads(raw, object_pairs_hook=exl3.pairs)
            episode = mapping(episode_value)
            task = mapping(episode.get("task"))
            require(
                episode.get("ok") is True and not sequence(episode.get("errors")),
                "Model-call metric cannot exclude an operationally failed episode",
            )
            traces = sequence(episode.get("traces"))
            require(len(traces) == 1, "Expected the native single-agent trace")
            trace = mapping(traces[0])
            require(
                trace.get("ok") is True and not sequence(trace.get("errors")),
                "Model-call metric cannot exclude a failed native trace",
            )
            calls = sequence(trace.get("calls"))
            require(bool(calls), "Missing native model-call observations")
            for index, value in enumerate(calls):
                call = mapping(value)
                # Native write_episode(exclude_none=True) omits a successful error.
                require(
                    call.get("error") is None,
                    "Failed or incomplete model call; no filtering or retries",
                )
                require(
                    call.get("finish_reason") in ("stop", "length"),
                    "Incomplete native model-call finish",
                )
                usage = mapping(call.get("usage"))
                tokens = exl3.integer(usage.get("completion_tokens"))
                require(tokens >= 0, "Negative model-call completion usage")
                prompt_tokens = exl3.integer(usage.get("prompt_tokens"))
                cached_value = usage.get("cached_input_tokens")
                cached_tokens = (
                    0 if cached_value is None else exl3.integer(cached_value)
                )
                require(
                    prompt_tokens >= 0 and cached_tokens >= 0,
                    "Negative native prompt/cache usage",
                )
                input_tokens = prompt_tokens + cached_tokens
                reasoning = usage.get("reasoning_tokens")
                if reasoning is not None:
                    require(
                        0 <= exl3.integer(reasoning) <= tokens,
                        "Reasoning usage must be a subset, never additional tokens",
                    )
                span = mapping(call.get("time"))
                start, end = number(span.get("start")), number(span.get("end"))
                duration = number(end - start)
                require(
                    0 < start < end and duration > 0,
                    "Missing, nonfinite or reversed native model-call wall clocks",
                )
                total_tokens += tokens
                total_input_tokens += input_tokens
                durations.append(duration)
                observations.append({
                    "episode": ordinal,
                    "task_key": exl3.text(task.get("key")),
                    "task_sha256": exl3.text(task.get("hash")),
                    "trace_id": trace.get("id"),
                    "call": index,
                    "completion_tokens": tokens,
                    "input_tokens": input_tokens,
                    "uncached_prompt_tokens": prompt_tokens,
                    "cached_input_tokens": cached_value,
                    "reasoning_tokens_subset": reasoning,
                    "start_unix_seconds": start,
                    "end_unix_seconds": end,
                    "duration_wall_seconds": duration,
                    "finish_reason": call["finish_reason"],
                })
            episodes += 1
    require(
        episodes == expected_episode_count,
        f"Model-call metric requires all {expected_episode_count} native episodes",
    )
    seconds = number(math.fsum(durations))
    require(seconds > 0, "No positive native model-call duration")
    return {
        "model_call_output_tok_s": number(total_tokens / seconds),
        "completion_tokens": total_tokens,
        "input_tokens": total_input_tokens,
        "model_call_wall_seconds": seconds,
        "call_count": len(observations),
        "episode_count": episodes,
        "length_truncated_calls": sum(
            call["finish_reason"] == "length" for call in observations
        ),
        "calls": observations,
        "scope": "whole native model-call wall time including prefill/decode/HTTP; not decode-only, monotonic or GPU time",
        "usage_semantics": "completion_tokens includes reasoning; optional reasoning_tokens is not added again",
        "input_usage_semantics": "native prompt_tokens excludes cache reads; input_tokens adds reported cached_input_tokens back, without claiming omitted cache telemetry is zero",
        "clock": "native Unix wall seconds, unmodified; positive finite end minus start per call",
    }


Window = tuple[int, int]
Metrics = dict[str, float]


@dataclass(frozen=True)
class Suite:
    """One frozen workload: protocol, metrics, sources and its three worker phases.

    ``freeze`` binds suite inputs before any generation and returns the suite's
    workload fields; ``collect`` sends the frozen workload once; ``admit``
    replays raw evidence into metrics plus the suite's admitted.json fields.
    """

    name: str
    protocol: str
    scope: str
    order: tuple[str, ...]
    primary_metric: str
    primary_scope: str
    metric_names: tuple[str, ...]
    optional_metrics: tuple[str, ...]
    sources: tuple[str, ...]
    record: dict[str, object]
    trees: tuple[str, ...]
    freeze: Callable[[Settings, exl3.Client, exl3.RawTokenizer], dict[str, object]]
    collect: Callable[[Settings, exl3.Client], None]
    admit: Callable[
        [Settings, exl3.Evidence, dict[str, object], Window],
        tuple[Metrics, dict[str, object]],
    ]


def _broad_freeze(
    settings: Settings, client: exl3.Client, tokenizer: exl3.RawTokenizer
) -> dict[str, object]:
    """Bind taskset inputs and C1 prompts/IDs before any generation."""
    tasksets: dict[str, object] = {}
    for taskset in exl3.TASKSETS:
        inputs = exl3.freeze_taskset(settings.output / taskset.name, taskset)
        tasksets[taskset.name] = {
            "profile": taskset.config,
            "tasks": taskset.tasks,
            "output_budget": taskset.output_tokens,
            "files_sha256": inputs["files_sha256"],
            "local_dataset": inputs["local_dataset"],
            "selection": inputs["selection"],
            "call_sampling": exl3.expected_call_sampling(taskset),
        }
    plan = exl3.plan_c1(settings.output / "c1", client, tokenizer)
    return {
        "tasksets": tasksets,
        "c1": {
            "plan_sha256": exl3.digest(settings.output / "c1/plan.json"),
            "rows": plan["rows"],
        },
    }


def _broad_collect(settings: Settings, client: exl3.Client) -> None:
    """Run every native taskset once, then the frozen C1 rows."""
    for taskset in exl3.TASKSETS:
        group = settings.output / taskset.name
        command, cwd = exl3.native_command(group, taskset)
        run_producer(
            settings,
            taskset.name,
            command,
            cwd,
            exl3.native_environment(group, client.key),
        )
        exl3.save(
            group / f"provenance/{taskset.name}.evaluation-inputs-after.json",
            exl3.taskset_inputs(group / "provenance", taskset),
        )
    exl3.run_c1(
        settings.output / "c1",
        client,
        exl3.document(settings.output / "c1/plan.json"),
        lambda: guard(settings),
    )


def _broad_admit(
    settings: Settings,
    evidence: exl3.Evidence,
    frozen_workload: dict[str, object],
    window: Window,
) -> tuple[Metrics, dict[str, object]]:
    """Replay every taskset, the pooled primary and C1 from raw evidence."""
    frozen_tasksets = mapping(frozen_workload["tasksets"])
    qualities: dict[str, object] = {}
    native_calls: dict[str, object] = {}
    metrics: Metrics = {}
    pooled_tokens = 0
    pooled_durations: list[float] = []
    for taskset in exl3.TASKSETS:
        group = settings.output / taskset.name
        quality = exl3.admit_taskset(evidence, group, taskset, window)
        calls = model_call_observations(evidence, group / taskset.name, taskset.tasks)
        require(
            calls["call_count"] == taskset.tasks
            and quality["rollouts"] == taskset.tasks
            and calls["length_truncated_calls"] == quality["truncated_rollouts"],
            f"{taskset.name} must retain all {taskset.tasks} graded one-call rollouts",
        )
        require(
            mapping(frozen_tasksets[taskset.name])["files_sha256"]
            == exl3.document(
                group / f"provenance/{taskset.name}.evaluation-inputs-before.json"
            )["files_sha256"],
            f"{taskset.name} inputs differ from the pre-suite frozen workload",
        )
        metrics[f"{taskset.metric}_output_tok_s"] = number(
            calls["model_call_output_tok_s"]
        )
        metrics[f"{taskset.metric}_reward"] = number(quality["weighted_reward_mean"])
        metrics[f"{taskset.metric}_truncated"] = float(
            exl3.integer(calls["length_truncated_calls"])
        )
        pooled_tokens += exl3.integer(calls["completion_tokens"])
        pooled_durations.extend(
            number(mapping(call)["duration_wall_seconds"])
            for call in sequence(calls["calls"])
        )
        qualities[taskset.name] = quality
        native_calls[taskset.name] = calls
    pooled_seconds = number(math.fsum(pooled_durations))
    require(pooled_seconds > 0, "No positive pooled native model-call duration")
    metrics["model_call_output_tok_s"] = number(pooled_tokens / pooled_seconds)
    native_calls["pooled"] = {
        "model_call_output_tok_s": metrics["model_call_output_tok_s"],
        "completion_tokens": pooled_tokens,
        "model_call_wall_seconds": pooled_seconds,
        "call_count": len(pooled_durations),
        "tasksets": [taskset.name for taskset in exl3.TASKSETS],
        "scope": "every native model call of all four tasksets pooled: sum of completion tokens / sum of model-call wall time",
    }
    c1 = exl3.admit_c1(evidence, settings.output / "c1")
    require(
        mapping(frozen_workload["c1"])["plan_sha256"]
        == exl3.digest(settings.output / "c1/plan.json"),
        "C1 plan differs from the pre-suite frozen workload",
    )
    guard(settings)
    metrics.update({
        name: number(value) for name, value in mapping(c1["metrics"]).items()
    })
    return metrics, {
        "quality_scope": "sampled native tasksets (3 AIME25, 20 MMLU-Pro, 6 I3 Logic, 3 LiveCodeBench); native rewards per taskset, no combined quality score",
        "tasksets": qualities,
        "native_model_calls": native_calls,
        "c1": c1,
        "not_measured": {
            "ttft": c1["ttft"],
            "committed_decode_tps": c1["committed_decode_tps"],
            "power_energy": "not sampled by this lane",
            "context_capacity": "/v1/models max_model_len is the reported limit, not a 262144-token capacity test",
        },
    }


def _prefill_freeze(
    settings: Settings, client: exl3.Client, tokenizer: exl3.RawTokenizer
) -> dict[str, object]:
    """Size, freeze and render every ladder row before any generation."""
    plan = prefill.plan(settings.output / "prefill", client, tokenizer, prefill.LADDER)
    return {
        "prefill": {
            "plan_sha256": exl3.digest(settings.output / "prefill/plan.json"),
            "rows": plan["rows"],
        },
    }


def _prefill_collect(settings: Settings, client: exl3.Client) -> None:
    """Send each frozen row's TTFT then continuation request once, in order."""
    prefill.run(
        settings.output / "prefill",
        client,
        exl3.document(settings.output / "prefill/plan.json"),
        lambda: guard(settings),
    )


def _prefill_admit(
    settings: Settings,
    evidence: exl3.Evidence,
    frozen_workload: dict[str, object],
    window: Window,
) -> tuple[Metrics, dict[str, object]]:
    """Replay every ladder row from raw evidence inside the identity window."""
    result = prefill.admit(evidence, settings.output / "prefill", prefill.LADDER)
    require(
        mapping(frozen_workload["prefill"])["plan_sha256"]
        == exl3.digest(settings.output / "prefill/plan.json"),
        "Prefill plan differs from the pre-suite frozen workload",
    )
    require(
        all(
            window[0]
            < exl3.integer(mapping(mapping(row)[kind])["request_started_unix_ns"])
            < window[1]
            for row in sequence(result["rows"])
            for kind in prefill.BUDGETS
        ),
        "Prefill requests fall outside the identity capture window",
    )
    guard(settings)
    metrics = {
        name: number(value) for name, value in mapping(result["metrics"]).items()
    }
    return metrics, {
        "prefill": result,
        "not_measured": {
            "streaming_ttft": prefill.TTFT_SCOPE,
            "committed_decode_tps": "unavailable: EXL3 exposes no incremental committed counters",
            "prefix_reuse": "the continuation is expected to reuse the TTFT prefix; usage carries no cache telemetry, so reuse is not observed",
            "quality": "this suite measures no task quality or reward",
            "power_energy": "not sampled by this lane",
        },
    }


BROAD = Suite(
    name="broad",
    protocol="exl3-native-broad-c1-request-v5",
    scope="exl3_bend_sampled_broad_tasksets_and_c1_whole_request_not_full_qualification",
    order=(*(taskset.name for taskset in exl3.TASKSETS), "c1"),
    primary_metric="model_call_output_tok_s",
    primary_scope="every native model call of all four tasksets pooled: sum of completion tokens / sum of model-call wall time",
    metric_names=(
        "model_call_output_tok_s",
        *(
            f"{taskset.metric}_{name}"
            for taskset in exl3.TASKSETS
            for name in TASKSET_METRICS
        ),
        *(f"c1_request_tok_s_{depth}" for depth in exl3.DEPTHS),
    ),
    optional_metrics=("spec_accept_length",),
    sources=(
        "autoresearch.sh",
        "bench/autoresearch.py",
        "bench/exl3.py",
        "bench/throughput-prompts.jsonl",
        "prepare/exl3-manifest.json",
    ),
    record={
        "tasksets": [
            {
                "taskset": taskset.name,
                "profile": taskset.config,
                "tasks": taskset.tasks,
                "rollouts": 1,
                "shuffle": True,
                "seed": 0,
                "output_budget": taskset.output_tokens,
                "sampling": "eval/configs/local.toml; greedy, thinking enabled; only max_tokens set per taskset",
            }
            for taskset in exl3.TASKSETS
        ],
        "c1": {
            "protocol": exl3.C1_PROTOCOL,
            "depths": list(exl3.DEPTHS),
            "repetitions": exl3.REPETITIONS,
            "output_budget": exl3.OUTPUT_TOKENS,
            "concurrency": 1,
            "order": "depth_then_repetition",
            "sampling": {"temperature": 0, "top_p": 1, "n": 1, "stream": False},
            "cache_policy": "deterministic_per_row_nonce_no_flush_no_warmup",
        },
    },
    trees=(
        *(
            f"{taskset.name}/{part}"
            for taskset in exl3.TASKSETS
            for part in ("provenance", taskset.name)
        ),
        "c1",
    ),
    freeze=_broad_freeze,
    collect=_broad_collect,
    admit=_broad_admit,
)
PREFILL = Suite(
    name="prefill",
    protocol="exl3-native-prefill-ttft-v1",
    scope="exl3_cold_prefill_ttft_ladder_nonstreaming_not_capacity_or_quality",
    order=("prefill",),
    primary_metric="prefill_tok_s",
    primary_scope=prefill.PRIMARY_SCOPE,
    metric_names=prefill.metric_names(prefill.LADDER),
    optional_metrics=(),
    sources=(
        "autoresearch.sh",
        "bench/autoresearch.py",
        "bench/exl3.py",
        "bench/prefill.py",
        "bench/throughput-prompts.jsonl",
        "prepare/exl3-manifest.json",
    ),
    record={
        "prefill": {
            "protocol": prefill.PROTOCOL,
            "ladder": [[depth, reps] for depth, reps in prefill.LADDER],
            "output_budgets": dict(prefill.BUDGETS),
            "concurrency": 1,
            "order": prefill.ORDER,
            "sampling": dict(prefill.SAMPLING),
            "cache_policy": prefill.CACHE_POLICY,
        },
    },
    trees=("prefill",),
    freeze=_prefill_freeze,
    collect=_prefill_collect,
    admit=_prefill_admit,
)
SUITES = {suite.name: suite for suite in (BROAD, PREFILL)}


def worker(settings: Settings, suite: Suite) -> int:
    """Collect the frozen workload once, then replay raw-evidence admission."""
    state = guard(settings)
    verify_container(settings, state)
    candidate = mapping(state.get("candidate"))
    client = exl3.Client(api_key(settings.key_file))
    before_path = settings.output / "identity-before.json"
    after_path = settings.output / "identity-after.json"
    before = exl3.capture_file(settings.container, client, before_path, None)
    identity = mapping(before["identity"])
    instance = mapping(identity["container"])
    require(
        instance.get("id") == settings.container
        and instance.get("image") == candidate.get("image"),
        "Captured identity selected another container or image",
    )
    tokenizer_record = mapping(identity["tokenizer"])
    tokenizer = exl3.RawTokenizer(
        Path(exl3.text(tokenizer_record["host_path"])),
        exl3.text(tokenizer_record["sha256"]),
    )
    identity_sha256 = exl3.digest(before_path)
    supervisor = exl3.document(settings.output / "supervisor.json")
    fields = suite.freeze(settings, client, tokenizer)
    sources = sequence(supervisor["sources"])
    for value in sources:
        item = mapping(value)
        name = exl3.text(item["path"]).removeprefix("sources/")
        require(
            item.get("sha256") == exl3.digest(ROOT / name),
            f"Benchmark source changed after its initial snapshot: {name}",
        )
    workload: dict[str, object] = {
        "protocol": suite.protocol,
        "order": list(suite.order),
        "primary_metric": suite.primary_metric,
        "primary_scope": suite.primary_scope,
        "identity_before_sha256": identity_sha256,
        **fields,
        "sources": sources,
    }
    benchmark = {
        **supervisor,
        "workload": workload,
        "workload_sha256": hashlib.sha256(exl3.canonical(workload)).hexdigest(),
    }
    exl3.save(settings.output / "benchmark.json", benchmark)
    suite.collect(settings, client)
    after = exl3.capture_file(settings.container, client, after_path, before_path)
    evidence = exl3.Evidence(settings.output / "admitted.json")
    for path in (before_path, after_path):
        evidence.retain(path)
    require(after["identity"] == identity, "Measurement changed serving instance")
    window = (
        exl3.integer(before["finished_unix_ns"]),
        exl3.integer(after["started_unix_ns"]),
    )
    metrics, admitted = suite.admit(settings, evidence, workload, window)
    for value in sources:
        item = mapping(value)
        path = settings.output / exl3.text(item["path"])
        require(
            exl3.digest(evidence.retain(path)) == item["sha256"],
            f"Snapshotted source changed: {path}",
        )
    for path in (
        settings.output / "benchmark.json",
        settings.output / "supervisor.json",
    ):
        evidence.retain(path)
    evidence.tree(settings.output / "sources")
    evidence.tree(settings.output / "logs")
    for tree in suite.trees:
        evidence.tree(settings.output / tree)
    exl3.save(
        settings.output / "admitted.json",
        {
            "schema_version": 1,
            "status": "complete_admitted_measurement",
            "protocol": suite.protocol,
            "scope": suite.scope,
            "order": list(suite.order),
            "workload_sha256": benchmark["workload_sha256"],
            "benchmark_sha256": exl3.digest(settings.output / "benchmark.json"),
            "identity": identity,
            "metrics": metrics,
            "primary_metric": suite.primary_metric,
            **admitted,
            "evidence_sha256": evidence.hashes,
        },
    )
    return 0


@dataclass
class Interruption:
    """Let the supervisor terminate only its own process family on interruption."""

    signum: int | None = None

    def request(self, signum: int, _frame: FrameType | None) -> None:
        """Defer shutdown to the supervised polling loop."""
        if self.signum is None:
            self.signum = signum


def _process_children(pid: int) -> list[int]:
    """Include children forked by any thread, regardless of their sessions."""
    children: list[int] = []
    try:
        for task in (Path("/proc") / str(pid) / "task").iterdir():
            try:
                children.extend(
                    int(child)
                    for child in (task / "children").read_text(encoding="ascii").split()
                )
            except (FileNotFoundError, ProcessLookupError):
                if pid == os.getpid() and task.name == str(pid):
                    raise
                continue
    except (FileNotFoundError, ProcessLookupError):
        if pid == os.getpid():
            raise
        return children
    return children


def _enable_subreaper() -> None:
    """Keep orphaned worker descendants under this dedicated Linux supervisor."""
    require(
        sys.platform == "linux"
        and hasattr(os, "pidfd_open")
        and hasattr(os, "P_PIDFD")
        and hasattr(signal, "pidfd_send_signal"),
        "Linux pidfd ownership is required before launching the worker",
    )
    require(
        not _process_children(os.getpid()),
        "Dedicated supervisor already owns children",
    )
    libc = ctypes.CDLL(None, use_errno=True)
    require(hasattr(libc, "prctl"), "Linux subreaper setup is unavailable")
    prctl = libc.prctl
    prctl.argtypes = [ctypes.c_int, *([ctypes.c_ulong] * 4)]
    prctl.restype = ctypes.c_int
    # PR_SET_CHILD_SUBREAPER and PR_GET_CHILD_SUBREAPER from linux/prctl.h.
    if prctl(36, 1, 0, 0, 0) != 0:
        raise OSError(ctypes.get_errno(), "PR_SET_CHILD_SUBREAPER failed")
    enabled = ctypes.c_int()
    if prctl(37, ctypes.addressof(enabled), 0, 0, 0) != 0:
        raise OSError(ctypes.get_errno(), "PR_GET_CHILD_SUBREAPER failed")
    require(enabled.value == 1, "Linux child subreaper was not enabled")


def _pidfd_pid(descriptor: int) -> int:
    """Read the kernel identity of a pidfd; reaped processes report minus one."""
    identity = dict(
        row.split(":", 1)
        for row in (Path("/proc/self/fdinfo") / str(descriptor))
        .read_text(encoding="ascii")
        .splitlines()
    )
    return int(identity.get("Pid", ""))


def owned_processes(deadline: float) -> dict[int, int]:
    """Pin verified descendants of this supervisor, including adopted orphans."""
    supervisor = os.getpid()
    pending = [(child, supervisor) for child in _process_children(supervisor)]
    descriptors: dict[int, int] = {}
    try:
        while pending and time.monotonic() < deadline:
            current, parent = pending.pop()
            if current in descriptors:
                continue
            descriptor: int | None = None
            try:
                descriptor = os.pidfd_open(current)
                process = Path("/proc") / str(current)
                fields = (
                    (process / "stat")
                    .read_text(encoding="ascii")
                    .rsplit(")", 1)[1]
                    .split()
                )
                owner = process.stat().st_uid
                if int(fields[1]) != parent:
                    continue
                children = _process_children(current)
                # A pidfd survives reaping/PID reuse; reject /proc data from a
                # replacement process before trusting its identity or children.
                pinned_pid = _pidfd_pid(descriptor)
                if pinned_pid == -1:
                    continue
                require(pinned_pid == current, "Unexpected pidfd process identity")
                if parent != supervisor and _pidfd_pid(descriptors[parent]) != parent:
                    continue
                require(owner == os.getuid(), "Worker descendant changed its owner uid")
                descriptors[current] = descriptor
                descriptor = None
                pending.extend((child, current) for child in children)
            except (FileNotFoundError, ProcessLookupError):
                continue
            finally:
                if descriptor is not None:
                    os.close(descriptor)
        return descriptors
    except BaseException:
        for descriptor in descriptors.values():
            os.close(descriptor)
        raise


def terminate(child: subprocess.Popen[bytes], deadline: float) -> bool:
    """Reap the owned family within the reserve; report any live processes seen."""
    cleanup_deadline = min(deadline, time.monotonic() + TERMINATION_SECONDS)
    term_deadline = cleanup_deadline - 1
    descriptors: dict[int, int] = {}
    poller = select.poll()
    saw_live = False
    try:
        while True:
            added: set[int] = set()
            for pid, descriptor in owned_processes(cleanup_deadline).items():
                if pid in descriptors:
                    os.close(descriptor)
                else:
                    descriptors[pid] = descriptor
                    poller.register(descriptor, select.POLLIN)
                    added.add(descriptor)
            # Only Popen may reap its root and update its cached return code.
            child.poll()
            exited = dict(poller.poll(0))
            finished: list[int] = []
            for pid, descriptor in descriptors.items():
                if descriptor in exited:
                    if pid == child.pid and child.returncode is None:
                        if child.poll() is None:
                            continue
                    else:
                        try:
                            os.waitid(os.P_PIDFD, descriptor, os.WEXITED | os.WNOHANG)
                        except ChildProcessError:
                            # Its parent still owns reaping, or already reaped it.
                            # Rediscovery will pin it again if it becomes adopted.
                            pass
                    finished.append(pid)
                    continue
                saw_live = True
                try:
                    if descriptor in added:
                        signal.pidfd_send_signal(descriptor, signal.SIGTERM)
                    if time.monotonic() >= term_deadline:
                        signal.pidfd_send_signal(descriptor, signal.SIGKILL)
                except ProcessLookupError:
                    continue
            for pid in finished:
                descriptor = descriptors.pop(pid)
                poller.unregister(descriptor)
                os.close(descriptor)
            # A traversal can race adoption. An empty direct-child list is the
            # final proof that no unvisited descendant can still fork or reparent.
            if (
                not descriptors
                and child.returncode is not None
                and not _process_children(os.getpid())
            ):
                return saw_live
            require(
                time.monotonic() < cleanup_deadline,
                "Worker family could not be terminated and reaped within its reserve",
            )
            time.sleep(min(0.05, max(0.0, cleanup_deadline - time.monotonic())))
    finally:
        for descriptor in descriptors.values():
            os.close(descriptor)


def supervise(settings: Settings, suite: Suite, started: float) -> int:
    """Enforce one deadline across capture, every frozen workload and admission."""
    require(not os.path.lexists(settings.output), "Output directory must be fresh")
    state = guard(settings)
    deadline = min(
        started + LIMIT_SECONDS,
        number(state.get("deadline_monotonic")) - RECOVERY_HEADROOM_SECONDS,
    )
    require(
        deadline - time.monotonic() > TERMINATION_SECONDS,
        "No guarded execution time remains",
    )
    settings.output.mkdir(mode=0o700)
    try:
        return supervise_created(settings, suite, started, state, deadline)
    except FAILURES as error:
        exl3.save(
            settings.output / "failure.json",
            {
                "status": "rejected",
                "error_type": type(error).__name__,
                "reason": str(error),
                "elapsed_seconds": time.monotonic() - started,
            },
        )
        raise


def supervise_created(
    settings: Settings,
    suite: Suite,
    started: float,
    state: dict[str, object],
    deadline: float,
) -> int:
    """Use only the fresh output directory exclusively created by this invocation."""
    _enable_subreaper()
    (settings.output / "logs").mkdir(mode=0o700)
    sources = exl3.snapshot_sources(settings.output, suite.sources)
    exl3.save(
        settings.output / "supervisor.json",
        {
            "schema_version": 1,
            "protocol": suite.protocol,
            "scope": suite.scope,
            "started_monotonic": started,
            "deadline_monotonic": deadline,
            "hard_limit_seconds": LIMIT_SECONDS,
            "recovery_headroom_seconds": RECOVERY_HEADROOM_SECONDS,
            "termination_reserve_seconds": TERMINATION_SECONDS,
            "owned_container_id": settings.container,
            "endpoint": ENDPOINT,
            "maintenance_directory": str(settings.maintenance),
            "operator_descriptor": {
                "path": str(OPERATOR),
                "identity": settings.operator_identity,
                "sha256": settings.operator_sha256,
            },
            "guardian_before": state,
            **suite.record,
            "order": list(suite.order),
            "sources": sources,
        },
    )
    interruption = Interruption()
    previous = {
        sig: signal.signal(sig, interruption.request)
        for sig in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP)
    }
    try:
        with (
            (settings.output / "logs/worker.stdout").open("xb") as stdout,
            (settings.output / "logs/worker.stderr").open("xb") as stderr,
        ):
            child = subprocess.Popen(
                [
                    "nix",
                    "develop",
                    "--offline",
                    "--no-write-lock-file",
                    "-c",
                    sys.executable,
                    "-m",
                    "bench.autoresearch",
                    "--suite",
                    suite.name,
                    "--worker",
                ],
                cwd=ROOT,
                stdin=subprocess.PIPE,
                stdout=stdout,
                stderr=stderr,
                start_new_session=True,
            )
            try:
                if child.stdin is None:
                    raise RuntimeError("Missing supervisor binding pipe")
                with child.stdin:
                    child.stdin.write(
                        exl3.canonical({
                            "identity": settings.operator_identity,
                            "sha256": settings.operator_sha256,
                        })
                    )
                while child.poll() is None:
                    require(
                        interruption.signum is None, "Canonical benchmark interrupted"
                    )
                    require(
                        time.monotonic() < deadline - TERMINATION_SECONDS,
                        "Canonical benchmark exceeded its guarded deadline; no partial metrics",
                    )
                    current = guard(settings)
                    require(
                        all(
                            current.get(key) == state.get(key)
                            for key in (
                                "candidate",
                                "guardian_pid",
                                "guardian_start",
                                "deadline_monotonic",
                                "lease_identity",
                            )
                        ),
                        "Maintenance ownership changed during benchmark",
                    )
                    time.sleep(
                        min(
                            0.5,
                            max(0.0, deadline - TERMINATION_SECONDS - time.monotonic()),
                        )
                    )
            except BaseException:
                terminate(child, deadline)
                raise
            descendants_survived = terminate(child, deadline)
            require(
                child.returncode == 0,
                "Canonical worker failed; inspect private evidence",
            )
            require(
                not descendants_survived,
                "Canonical worker left live descendants; no admitted metrics",
            )
        require(
            interruption.signum is None and time.monotonic() < deadline,
            "Canonical benchmark finished outside its guarded deadline",
        )
        guard(settings)
        admitted = exl3.document(settings.output / "admitted.json")
        require(
            admitted.get("status") == "complete_admitted_measurement"
            and admitted.get("schema_version") == 1
            and admitted.get("protocol") == suite.protocol
            and admitted.get("scope") == suite.scope
            and admitted.get("order") == list(suite.order)
            and admitted.get("primary_metric") == suite.primary_metric,
            "Missing complete frozen EXL3 admission",
        )
        benchmark = exl3.document(settings.output / "benchmark.json")
        require(
            admitted.get("benchmark_sha256")
            == exl3.digest(settings.output / "benchmark.json")
            and admitted.get("workload_sha256")
            == benchmark.get("workload_sha256")
            == hashlib.sha256(exl3.canonical(benchmark.get("workload"))).hexdigest(),
            "Admitted measurement is not bound to this complete frozen workload",
        )
        values = mapping(admitted.get("metrics"))
        names = set(suite.metric_names)
        require(
            names <= set(values) <= names | set(suite.optional_metrics),
            "Missing or unexpected admitted metrics",
        )
        ordered = [
            *suite.metric_names,
            *(name for name in suite.optional_metrics if name in values),
        ]
        metrics = {name: number(values[name]) for name in ordered}
        metrics["elapsed_seconds"] = time.monotonic() - started
        exl3.save(
            settings.output / "measurement.json",
            {
                "schema_version": 1,
                "status": "complete_admitted_measurement",
                "protocol": suite.protocol,
                "workload_sha256": admitted["workload_sha256"],
                "metrics": metrics,
                "admitted_sha256": exl3.digest(settings.output / "admitted.json"),
                "elapsed_scope": "entire canonical command through raw-evidence admission; not decode-only time",
                "finished_monotonic": time.monotonic(),
            },
        )
        require(
            time.monotonic() < deadline and interruption.signum is None,
            "Finalization exceeded deadline or was interrupted",
        )
        sys.stdout.write(
            "".join(f"METRIC {name}={value:.17g}\n" for name, value in metrics.items())
        )
        return 0
    finally:
        for sig, handler in previous.items():
            signal.signal(sig, handler)


def arguments(values: list[str]) -> tuple[Suite, bool]:
    """Parse the required suite choice (no default) and the internal worker flag."""
    require(bool(values), "A suite is required: --suite broad|prefill")
    require(
        values[0] == "--suite" and len(values) >= 2,
        "Expected --suite broad|prefill first",
    )
    suite = SUITES.get(values[1])
    if suite is None:
        raise ValueError(f"Unknown suite {values[1]!r}; expected broad or prefill")
    require(values[2:] in ([], ["--worker"]), "Unexpected arguments after the suite")
    return suite, values[2:] == ["--worker"]


def main() -> int:
    """Run the finite supervisor; preserve sanitized failure diagnostics privately."""
    started = time.monotonic()
    os.umask(0o077)
    try:
        suite, is_worker = arguments(sys.argv[1:])
    except ValueError as error:
        sys.stderr.write(f"{error}; use bash autoresearch.sh --help\n")
        return 2
    try:
        settings = Settings.descriptor()
        if is_worker:
            binding = mapping(exl3.loads(sys.stdin.buffer.read(4097)))
            require(
                binding
                == {
                    "identity": settings.operator_identity,
                    "sha256": settings.operator_sha256,
                },
                "Worker operator descriptor differs from supervisor startup",
            )
            try:
                return worker(settings, suite)
            except FAILURES as error:
                exl3.save(
                    settings.output / "worker-failure.json",
                    {
                        "status": "rejected",
                        "error_type": type(error).__name__,
                        "reason": str(error),
                    },
                )
                raise
        return supervise(settings, suite, started)
    except FAILURES:
        sys.stderr.write(
            "EXL3 autoresearch rejected; no admitted metrics. Inspect private artifacts.\n"
        )
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
