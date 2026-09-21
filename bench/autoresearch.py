# Copyright (c) 2026 inference contributors.
"""Finite native math/logic/direct-context/C1 measurements; see autoresearch.sh.

This supervisor never operates Docker lifecycle, promotion, power policy or the
maintenance guardian. The latter must independently recover the owned candidate.
Only the existing native producers and raw-evidence validators admit results.
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
from dataclasses import dataclass
from pathlib import Path
from types import FrameType

from bench import decode, direct_context
from eval.measure import mapping, number, sequence
from serve import qualification

ROOT = Path(__file__).resolve().parents[1]
ENDPOINT = "http://127.0.0.1:18020"
OPERATOR = Path("/run/user/1000/litos-autoresearch-operator.json")
LIMIT_SECONDS = 2400
RECOVERY_HEADROOM_SECONDS = 120
TERMINATION_SECONDS = 20
REPETITIONS = 5
LEASE = Path("/run/user/1000/qwen-packed64-docker-gpu0-maintenance.lock")
LAUNCH_LOCK = Path("/mnt/ssd/storage/ai/qwen3.8-27b/qwen-inference-launch.lock")
LAUNCH_IDENTITY = {
    "dev": 66305,
    "ino": 23726380,
    "uid": 1000,
    "mode": 0o600,
    "nlink": 1,
}
METRIC_NAMES = (
    "model_call_output_tok_s",
    "committed_tps_32768",
    "committed_tps_1024",
    "committed_tps_8192",
    "ttft_seconds_1024",
    "ttft_seconds_8192",
    "ttft_seconds_32768",
    "tiny_math_reward",
    "short_i3_model_call_output_tok_s",
    "short_i3_reward",
    "long_graphwalks_model_call_output_tok_s",
    "long_graphwalks_reward",
)
SUITE_PROTOCOL = "native-math3-logic1-graphwalks179k1-c1-v1"
SUITE_ORDER = ("tiny-math", "short-i3", "long-graphwalks", "decode")
SUITE_SCOPE = "sampled_math_logic_direct_graphwalks_and_C1_not_full_qualification"
SUITE_SOURCES = (
    "autoresearch.sh",
    "bench/autoresearch.py",
    "bench/direct_context.py",
    "bench/decode.py",
    "bench/cache.py",
    "bench/power.py",
    "bench/throughput-prompts.jsonl",
    "serve/qualification.py",
    "bend/adapter.py",
    "bend/build_toolchain.py",
)


def require(condition: bool, message: str) -> None:
    """Reject invalid boundary inputs and incomplete observations."""
    qualification.require(condition, message)


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
        value = mapping(json.loads(raw, object_pairs_hook=qualification.pairs))
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
            qualification.integer(value.get("schema_version")) == 1,
            "Unsupported operator descriptor schema",
        )
        container = qualification.text(value.get("container_id"))
        require(
            re.fullmatch(r"[0-9a-f]{64}", container) is not None,
            "Owned container must be its full immutable ID",
        )
        values = [
            qualification.text(value.get(name))
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
        key, _ = private_read(paths[0], key=True)
        key = key.removesuffix(b"\n")
        require(
            bool(key) and all(33 <= char <= 126 for char in key),
            "Invalid private API key",
        )
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
    state = mapping(json.loads(raw, object_pairs_hook=qualification.pairs))
    _ = qualification.canonical(state)
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
    pid = qualification.integer(state.get("guardian_pid"))
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
            qualification.docker(
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


def run_producer(settings: Settings, name: str, command: list[str]) -> None:
    """Run once, preserving private native output; no retries or score selection."""
    guard(settings)
    with (
        (settings.output / "logs" / f"{name}.stdout").open("xb") as stdout,
        (settings.output / "logs" / f"{name}.stderr").open("xb") as stderr,
    ):
        result = subprocess.run(
            command, cwd=ROOT, stdout=stdout, stderr=stderr, check=False
        )
    require(
        result.returncode == 0,
        f"Native {name} command failed; retained artifacts are incomplete",
    )
    guard(settings)


def model_call_observations(
    evidence: qualification.Evidence,
    directory: Path,
    expected_episode_count: int = 3,
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
            episode_value: object = json.loads(
                raw, object_pairs_hook=qualification.pairs
            )
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
                tokens = qualification.integer(usage.get("completion_tokens"))
                require(tokens >= 0, "Negative model-call completion usage")
                prompt_tokens = qualification.integer(usage.get("prompt_tokens"))
                cached_value = usage.get("cached_input_tokens")
                cached_tokens = (
                    0 if cached_value is None else qualification.integer(cached_value)
                )
                require(
                    prompt_tokens >= 0 and cached_tokens >= 0,
                    "Negative native prompt/cache usage",
                )
                input_tokens = prompt_tokens + cached_tokens
                reasoning = usage.get("reasoning_tokens")
                if reasoning is not None:
                    require(
                        0 <= qualification.integer(reasoning) <= tokens,
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
                    "task_key": qualification.text(task.get("key")),
                    "task_sha256": qualification.text(task.get("hash")),
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
        "calls": observations,
        "scope": "whole native model-call wall time including prefill/decode/HTTP; not decode-only, monotonic or GPU time",
        "usage_semantics": "completion_tokens includes reasoning; optional reasoning_tokens is not added again",
        "input_usage_semantics": "native prompt_tokens excludes cache reads; input_tokens adds reported cached_input_tokens back, without claiming omitted cache telemetry is zero",
        "clock": "native Unix wall seconds, unmodified; positive finite end minus start per call",
    }


def _native_workload(
    frozen: dict[str, object], provenance: Path, environment: str
) -> dict[str, object]:
    """Remove only the fresh launch path, not any frozen content identity."""
    files = mapping(frozen.get("files_sha256"))
    launch_hash = files.pop(str((provenance / f"{environment}.toml").resolve()))
    return {
        "profile": frozen["profile"],
        "environment": frozen["environment"],
        "selection": frozen["selection"],
        "files_sha256": files,
        "launch_config_sha256": launch_hash,
    }


def _freeze_suite(settings: Settings) -> dict[str, object]:
    """Bind all lanes before inference, inside the existing supervised deadline."""
    supervisor = qualification.document(settings.output / "supervisor.json")
    provenance_root = settings.output / "suite-provenance"
    provenance_root.mkdir(mode=0o700)
    native: dict[str, object] = {}
    files: dict[str, object] = {}
    image = (ROOT / "eval/.cache/sandbox-image").read_text(encoding="utf-8").strip()
    require(
        re.fullmatch(r"sha256:[a-f0-9]{64}", image) is not None,
        "Missing pinned native sandbox image",
    )
    for lane, profile, environment in (
        ("tiny-math", "tiny", "aime25"),
        ("short-i3", "diverse", "i3-logic"),
    ):
        provenance = provenance_root / lane
        provenance.mkdir(mode=0o700)
        config = ROOT / "eval/configs" / profile / f"{environment}.toml"
        launch, replacements = re.subn(
            r"^image = .*$",
            f'image = "{image}"',
            config.read_text(encoding="utf-8"),
            flags=re.MULTILINE,
        )
        require(replacements == 1, "Native profile must bind one sandbox image")
        with (provenance / f"{environment}.toml").open("xb") as stream:
            _ = stream.write(launch.encode())
        frozen = qualification.frozen_inputs(profile, environment, provenance)
        qualification.save(provenance / "evaluation-inputs.json", frozen)
        plan = _native_workload(frozen, provenance, environment)
        native[lane] = plan
        files.update(mapping(plan["files_sha256"]))
    direct_sources = {
        str(path.resolve()): qualification.digest(path)
        for path in direct_context.source_paths()
    }
    files.update(direct_sources)
    files.update({
        str((ROOT / name).resolve()): qualification.digest(ROOT / name)
        for name in SUITE_SOURCES
    })
    # Source/data hashes stay complete; copy repository producer/config bytes,
    # not large offline datasets or the prepared third-party source trees.
    names: set[str] = set()
    for value in files:
        path = Path(value)
        if path.is_relative_to(ROOT):
            relative = path.relative_to(ROOT)
            if not any(part.startswith(".") for part in relative.parts):
                names.add(relative.as_posix())
    sources = sequence(supervisor["sources"])
    already = {
        qualification.text(mapping(item)["path"]).removeprefix("sources/")
        for item in sources
    }
    sources.extend(
        decode.snapshot_sources(settings.output, tuple(sorted(names - already)))
    )
    for value in sources:
        item = mapping(value)
        name = qualification.text(item["path"]).removeprefix("sources/")
        require(
            item.get("sha256") == files.get(str((ROOT / name).resolve())),
            f"Benchmark source changed after its initial snapshot: {name}",
        )
    workload: dict[str, object] = {
        "protocol": SUITE_PROTOCOL,
        "order": list(SUITE_ORDER),
        "primary_metric": "model_call_output_tok_s",
        "primary_scope": "tiny-math native model calls only; unchanged numerator and wall-clock denominator",
        "native": native,
        "long-graphwalks": {
            "frozen_identity": direct_context.frozen_identity(),
            "source_closure": direct_sources,
        },
        "decode": supervisor["decode"],
        "files_sha256": files,
        "sources": sources,
    }
    benchmark = {
        **supervisor,
        "workload": workload,
        "workload_sha256": hashlib.sha256(
            qualification.canonical(workload)
        ).hexdigest(),
        "sources": sources,
    }
    qualification.save(settings.output / "benchmark.json", benchmark)
    return benchmark


def _admit_native_plan(
    evidence: qualification.Evidence,
    directory: Path,
    environment: str,
    expected: object,
) -> None:
    provenance = directory.parent / "provenance"
    path = evidence.retain(provenance / f"{environment}.evaluation-inputs-before.json")
    require(
        _native_workload(qualification.document(path), provenance, environment)
        == expected,
        f"{environment}: native run differs from the pre-suite frozen workload",
    )


def worker(settings: Settings) -> int:
    """Collect real producers, then replay existing independent admission gates."""
    state = guard(settings)
    verify_container(settings, state)
    before = settings.output / "identity-before.json"
    after = settings.output / "identity-after.json"
    qualification.capture_identity(
        settings.container, ENDPOINT, settings.key_file, before, None, None
    )
    identity = qualification.native_identity(
        qualification.document(before).get("identity")
    )
    require(
        identity.get("container_id") == settings.container,
        "Native identity selected another container",
    )
    os.environ.update(
        QWEN_SERVING_CONTAINER=settings.container,
        QWEN_API_KEY_FILE=str(settings.key_file),
        HF_HUB_OFFLINE="1",
        HF_DATASETS_OFFLINE="1",
        HF_HUB_DISABLE_TELEMETRY="1",
        UV_OFFLINE="1",
        UV_PYTHON_DOWNLOADS="never",
        QWEN_EVAL_ALLOW_REQUESTS="1",
        QWEN_EVAL_BASE_URL=f"{ENDPOINT}/v1",
    )
    benchmark = _freeze_suite(settings)
    frozen_workload = mapping(benchmark["workload"])
    run_producer(
        settings,
        "tiny-math",
        [
            "bash",
            str(ROOT / "eval/scripts/run"),
            "tiny",
            "aime25",
            "--measure-power",
            "--output",
            str(settings.output / "tiny-math"),
        ],
    )
    run_producer(
        settings,
        "short-i3",
        [
            "bash",
            str(ROOT / "eval/scripts/run"),
            "diverse",
            "i3-logic",
            "--measure-power",
            "--output",
            str(settings.output / "short-i3"),
        ],
    )
    run_producer(
        settings,
        "long-graphwalks",
        [
            sys.executable,
            "-m",
            "bench.direct_context",
            "collect",
            "--output",
            str(settings.output / "long-graphwalks"),
            "--key-file",
            str(settings.key_file),
            "--container",
            settings.container,
        ],
    )
    run_producer(
        settings,
        "decode",
        [
            sys.executable,
            "-m",
            "bench.decode",
            "--endpoint",
            ENDPOINT,
            "--key-file",
            str(settings.key_file),
            "--container",
            settings.container,
            "--repetitions",
            str(REPETITIONS),
            "--output",
            str(settings.output / "decode"),
        ],
    )
    qualification.capture_identity(
        settings.container, ENDPOINT, settings.key_file, after, before, 0
    )
    evidence = qualification.Evidence(settings.output / "admitted.json")
    require(
        qualification.captures(evidence, str(before), str(after)) == identity,
        "Canonical measurement changed serving instance",
    )
    math_directory = settings.output / "tiny-math/aime25"
    provenance = math_directory.parent / "provenance"
    require(
        qualification.captures(
            evidence,
            str(provenance / "aime25.serving-before.json"),
            str(provenance / "aime25.serving-after.json"),
        )
        == identity,
        "Math measurement changed serving instance",
    )
    quality = qualification.evaluation_gate(
        evidence, math_directory, identity, "tiny", "aime25"
    )
    model_calls = model_call_observations(evidence, math_directory)
    energy = qualification.energy_gate(evidence, math_directory, "aime25", identity)
    _admit_native_plan(
        evidence,
        math_directory,
        "aime25",
        mapping(frozen_workload["native"])["tiny-math"],
    )
    short_directory = settings.output / "short-i3/i3-logic"
    short_provenance = short_directory.parent / "provenance"
    require(
        qualification.captures(
            evidence,
            str(short_provenance / "i3-logic.serving-before.json"),
            str(short_provenance / "i3-logic.serving-after.json"),
        )
        == identity,
        "Short logic measurement changed serving instance",
    )
    short_quality = qualification.evaluation_gate(
        evidence, short_directory, identity, "diverse", "i3-logic"
    )
    short_calls = model_call_observations(
        evidence, short_directory, expected_episode_count=1
    )
    short_energy = qualification.energy_gate(
        evidence, short_directory, "i3-logic", identity
    )
    _admit_native_plan(
        evidence,
        short_directory,
        "i3-logic",
        mapping(frozen_workload["native"])["short-i3"],
    )
    require(short_quality.get("rollouts") == 1, "Missing graded logic sentinel")
    long_directory = settings.output / "long-graphwalks"
    long_result = direct_context.admit(long_directory, expected_identity=identity)
    long_plan = mapping(frozen_workload["long-graphwalks"])
    long_identity = mapping(long_plan["frozen_identity"])
    long_sources = mapping(long_plan["source_closure"])
    require(
        long_result.get("source_closure") == long_sources
        and direct_context.frozen_identity() == long_identity
        and long_result.get("frozen_identity") == long_identity
        and long_result.get("messages_sha256") == long_identity["messages_sha256"],
        "Direct context source or frozen identity differs from the pre-suite plan",
    )
    require(
        long_result.get("schema_version") == 1
        and long_result.get("producer") == "bench.direct_context.admit"
        and long_result.get("error") is None
        and type(long_result.get("is_truncated")) is bool
        and long_result.get("finish_reason") in ("stop", "length")
        and long_result["is_truncated"] == (long_result["finish_reason"] == "length"),
        "Incomplete direct-context native finish/error evidence",
    )
    long_tokens = qualification.integer(long_result.get("completion_tokens"))
    long_input = qualification.integer(long_result.get("input_tokens"))
    long_seconds = number(long_result.get("elapsed_seconds"))
    long_reward = number(long_result.get("reward"))
    long_scope = qualification.text(long_result.get("metric_scope"))
    require(
        long_input == 178769
        and 0 <= long_tokens <= 8192
        and long_seconds > 0
        and 0 <= long_reward <= 1,
        "Incomplete native direct-context usage, timing or reward",
    )
    long_rate = number(long_tokens / long_seconds)
    require(
        number(long_result.get("model_call_output_tok_s")) == long_rate,
        "Direct-context rate differs from its native model-call clock",
    )
    require(
        qualification.document(evidence.retain(long_directory / "report.json"))
        == long_result,
        "Direct-context producer report differs from independent raw admission",
    )
    paths = sequence(long_result.get("evidence_paths"))
    require(bool(paths), "Missing direct-context raw evidence paths")
    for value in paths:
        path = Path(qualification.text(value)).resolve(strict=True)
        require(
            path.is_relative_to(long_directory.resolve()) or str(path) in long_sources,
            "Direct-context evidence is outside its fresh root and frozen sources",
        )
        evidence.retain(path)
    report_path = settings.output / "decode/decode-depth-matrix.json"
    report = qualification.document(report_path)
    require(
        report.get("identity") == report.get("identity_after") == identity,
        "Decode measurement changed serving instance",
    )
    workload = qualification.document(report_path.parent / "workload.json")
    require(workload.get("repetitions") == REPETITIONS, "Canonical repetitions changed")
    timing = qualification.timing_gate(
        evidence, {"decode_report": str(report_path)}, identity
    )
    require(
        quality.get("rollouts") == 3, "Tiny math must retain all three graded rollouts"
    )
    rows = [mapping(row) for row in sequence(timing.get("rows"))]
    metrics: dict[str, float] = {
        "model_call_output_tok_s": number(model_calls.get("model_call_output_tok_s")),
        "tiny_math_reward": number(quality.get("weighted_reward_mean")),
        "short_i3_model_call_output_tok_s": number(
            short_calls.get("model_call_output_tok_s")
        ),
        "short_i3_reward": number(short_quality.get("weighted_reward_mean")),
        "long_graphwalks_model_call_output_tok_s": long_rate,
        "long_graphwalks_reward": long_reward,
    }
    pooled: dict[str, object] = {}
    for depth in decode.DEPTHS:
        selected = [row for row in rows if row.get("depth_target") == depth]
        require(len(selected) == REPETITIONS, "Incomplete canonical C1 matrix")
        tokens = sum(
            qualification.integer(row.get("counter_window_tokens")) for row in selected
        )
        nanoseconds = sum(
            qualification.integer(row.get("counter_window_ns")) for row in selected
        )
        ttft = sum(qualification.integer(row.get("ttft_ns")) for row in selected)
        require(
            tokens > 0 and nanoseconds > 0,
            "Missing positive committed counter interval",
        )
        metrics[f"committed_tps_{depth}"] = tokens * 1_000_000_000 / nanoseconds
        metrics[f"ttft_seconds_{depth}"] = ttft / (1_000_000_000 * REPETITIONS)
        pooled[str(depth)] = {
            "counter_window_tokens": tokens,
            "counter_window_ns": nanoseconds,
            "ttft_ns_sum": ttft,
            "repetitions": REPETITIONS,
        }
    guard(settings)
    for path_value, expected in mapping(frozen_workload["files_sha256"]).items():
        path = Path(path_value).resolve(strict=True)
        if str(path) not in evidence.hashes:
            evidence.retain(path)
        require(
            evidence.hashes[str(path)] == expected,
            f"Pre-suite source closure changed: {path}",
        )
    for path in (
        settings.output / "benchmark.json",
        settings.output / "supervisor.json",
    ):
        evidence.retain(path)
    evidence.tree(settings.output / "suite-provenance")
    evidence.tree(settings.output / "sources")
    evidence.tree(settings.output / "logs")
    evidence.tree(math_directory)
    evidence.tree(short_directory)
    qualification.save(
        settings.output / "admitted.json",
        {
            "schema_version": 2,
            "status": "complete_admitted_measurement",
            "protocol": SUITE_PROTOCOL,
            "scope": SUITE_SCOPE,
            "quality_scope": "three original AIME25 tasks, one original I3 logic task and one original direct BFS task; separate native rewards, no combined quality score",
            "order": list(SUITE_ORDER),
            "workload_sha256": benchmark["workload_sha256"],
            "benchmark_sha256": qualification.digest(
                settings.output / "benchmark.json"
            ),
            "identity": identity,
            "metrics": metrics,
            "pooled_counter_windows": pooled,
            "tiny_math": quality,
            "tiny_math_energy": energy,
            "short_i3": short_quality,
            "short_i3_energy": short_energy,
            "short_i3_model_calls": short_calls,
            "long_graphwalks": long_result,
            "long_graphwalks_metric_scope": long_scope,
            "timing": timing,
            "primary_metric": "model_call_output_tok_s",
            "native_model_calls": model_calls,
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


def supervise(settings: Settings, started: float) -> int:
    """Enforce one deadline across capture, all native workloads and admission."""
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
        return supervise_created(settings, started, state, deadline)
    except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as error:
        qualification.save(
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
    started: float,
    state: dict[str, object],
    deadline: float,
) -> int:
    """Use only the fresh output directory exclusively created by this invocation."""
    _enable_subreaper()
    (settings.output / "logs").mkdir(mode=0o700)
    sources = decode.snapshot_sources(
        settings.output, ("autoresearch.sh", "bench/autoresearch.py")
    )
    qualification.save(
        settings.output / "supervisor.json",
        {
            "schema_version": 2,
            "protocol": SUITE_PROTOCOL,
            "scope": SUITE_SCOPE,
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
            "math": {
                "profile": "tiny",
                "environment": "aime25",
                "tasks": 3,
                "rollouts": 1,
                "shuffle": True,
                "seed": 0,
                "output_budget": 32768,
                "sampling": "unchanged eval/configs/local.toml; greedy, thinking enabled",
            },
            "short": {
                "profile": "diverse",
                "environment": "i3-logic",
                "tasks": 1,
                "rollouts": 1,
                "shuffle": False,
                "output_budget": 8192,
                "selection": "first_native_eligible_source_order",
            },
            "long": {
                "profile": "diverse",
                "environment": "direct-graphwalks-bfs",
                "tasks": 1,
                "rollouts": 1,
                "input_tokens": 178769,
                "output_budget": 8192,
                "selection": "first_native_filtered_source_order",
            },
            "decode": {
                "depths": list(decode.DEPTHS),
                "repetitions": REPETITIONS,
                "output_budget": 1024,
                "protocol": decode.MEASUREMENT_PROTOCOL,
                "concurrency": 1,
                "order": "depth_then_repetition",
                "sampling": {
                    "temperature": 0,
                    "top_p": 1,
                    "n": 1,
                    "ignore_eos": False,
                },
                "cache_policy": "deterministic_per_row_nonce_no_flush_no_warmup",
            },
            "order": list(SUITE_ORDER),
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
                        qualification.canonical({
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
        admitted = qualification.document(settings.output / "admitted.json")
        require(
            admitted.get("status") == "complete_admitted_measurement"
            and admitted.get("schema_version") == 2
            and admitted.get("protocol") == SUITE_PROTOCOL
            and admitted.get("scope") == SUITE_SCOPE
            and admitted.get("order") == list(SUITE_ORDER),
            "Missing complete frozen diverse-suite admission",
        )
        benchmark = qualification.document(settings.output / "benchmark.json")
        require(
            admitted.get("benchmark_sha256")
            == qualification.digest(settings.output / "benchmark.json")
            and admitted.get("workload_sha256")
            == benchmark.get("workload_sha256")
            == hashlib.sha256(
                qualification.canonical(benchmark.get("workload"))
            ).hexdigest(),
            "Admitted measurement is not bound to this complete frozen workload",
        )
        values = mapping(admitted.get("metrics"))
        require(
            set(values) == set(METRIC_NAMES), "Missing or unexpected primary metrics"
        )
        metrics = {name: number(values[name]) for name in METRIC_NAMES}
        metrics["elapsed_seconds"] = time.monotonic() - started
        qualification.save(
            settings.output / "measurement.json",
            {
                "schema_version": 2,
                "status": "complete_admitted_measurement",
                "protocol": SUITE_PROTOCOL,
                "workload_sha256": admitted["workload_sha256"],
                "metrics": metrics,
                "admitted_sha256": qualification.digest(
                    settings.output / "admitted.json"
                ),
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


def main() -> int:
    """Run the finite supervisor; preserve sanitized failure diagnostics privately."""
    started = time.monotonic()
    os.umask(0o077)
    settings: Settings | None = None
    try:
        settings = Settings.descriptor()
        if sys.argv[1:] == ["--worker"]:
            binding = mapping(
                json.loads(
                    sys.stdin.buffer.read(4097), object_pairs_hook=qualification.pairs
                )
            )
            require(
                binding
                == {
                    "identity": settings.operator_identity,
                    "sha256": settings.operator_sha256,
                },
                "Worker operator descriptor differs from supervisor startup",
            )
            try:
                return worker(settings)
            except (
                OSError,
                ValueError,
                RuntimeError,
                subprocess.SubprocessError,
            ) as error:
                qualification.save(
                    settings.output / "worker-failure.json",
                    {
                        "status": "rejected",
                        "error_type": type(error).__name__,
                        "reason": str(error),
                    },
                )
                raise
        require(len(sys.argv) == 1, "Use bash autoresearch.sh --help")
        return supervise(settings, started)
    except (OSError, ValueError, RuntimeError, subprocess.SubprocessError):
        sys.stderr.write(
            "Canonical benchmark rejected; no admitted metrics. Inspect private artifacts.\n"
        )
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
