# Copyright (c) 2026 inference contributors.
"""One frozen native GraphWalks row; transport/admission, never a task or scorer.

The historical CLI does not expose HTTP retry configuration. The diverse lane
therefore constructs its native EvalConfig/ClientConfig and calls unchanged
run_evaluations, explicitly disabling both HTTP and rollout retries. Historical
smoke/quick/full CLI invocations are untouched. A successful sentinel is not
full benchmark qualification or a demonstration of the 262144-token boundary.
"""

from __future__ import annotations

import argparse
import asyncio
import hashlib
import importlib
import json
import os
import stat
import subprocess
import time
from collections.abc import Callable, Generator
from pathlib import Path
from typing import Protocol, runtime_checkable

from bench import cache, decode
from eval.measure import mapping, number, sequence
from serve import qualification as q

ROOT = Path(__file__).resolve().parents[1]
DIRECT = ROOT / "eval/direct"
CONFIG = DIRECT / "configs/diverse/graphwalks-bfs.toml"
BUDGET = DIRECT / "graphwalks-upper-current-token-budget.json"
INPUT_TOKENS = 178769
OUTPUT_TOKENS = 8192
CONTEXT_TOKENS = 262144
MESSAGES_SHA256 = "3ae0dc3fe105516e9e5644b36ea161331e72c91f881b060e9b8ae2c75d80cac7"
ENV_ARGS: dict[str, object] = {
    "split": "train",
    "scoring": "exact",
    "problem_type": "bfs",
    "prompt_chars_filter": "131073-262144",
    "shuffle": False,
    "seed": 0,
    "num_examples": -1,
}
SAMPLING: dict[str, object] = {
    "max_tokens": OUTPUT_TOKENS,
    "temperature": 0.6,
    "top_p": 0.95,
    "frequency_penalty": 0.0,
    "presence_penalty": 0.0,
    "extra_body": {
        "top_k": 20,
        "min_p": 0.0,
        "repetition_penalty": 1.0,
        "seed": 0,
        "chat_template_kwargs": {"enable_thinking": True},
    },
}
URLS = ("http://127.0.0.1:18020/v1", "http://127.0.0.1:18021/v1")
METRIC_SCOPE = (
    "one original GraphWalks exact-BFS row, first of 50 native eligible rows; "
    "178769 full templated input tokens, one rollout, 8192 output budget; "
    "native timing.model.spans get_model_response wall interval, including "
    "client/transport/prefill/decode, not decode-only or full-suite qualification"
)


def _hash(value: object) -> str:
    return hashlib.sha256(decode.canonical_bytes(value)).hexdigest()


def _messages_hash(value: object) -> str:
    # The retained upstream-tokenization proof used default JSON separators.
    return hashlib.sha256(json.dumps(value, sort_keys=True).encode()).hexdigest()


@runtime_checkable
class _Dataset(Protocol):
    def __len__(self) -> int: ...

    def __getitem__(self, index: int, /) -> object: ...


@runtime_checkable
class _Environment(Protocol):
    sampling_args: object

    def get_eval_dataset(self, n: int = -1) -> _Dataset: ...


@runtime_checkable
class _Serializable(Protocol):
    def model_dump(self, *, mode: str) -> dict[str, object]: ...


@runtime_checkable
class _Awaitable(Protocol):
    def __await__(self) -> Generator[object, None, object]: ...


def _native_function(module: str, name: str) -> Callable[..., object]:
    namespace = mapping(vars(importlib.import_module(module)))
    value = namespace.get(name)
    if not callable(value):
        raise ValueError("Pinned native API is not callable")
    return value


async def _native_evaluation(evaluation: object) -> None:
    run = _native_function("verifiers.types", "EvalRunConfig")(evals=[evaluation])
    result = _native_function("verifiers.utils.eval_utils", "run_evaluations")(run)
    if not isinstance(result, _Awaitable):
        raise ValueError("Pinned native runner did not return an awaitable")
    _ = await result


def frozen_identity() -> dict[str, object]:
    """Read the pre-existing token-fit proof, without native imports or inference."""
    measurement = mapping(q.document(BUDGET).get("sample_measurement"))
    records = [mapping(item) for item in sequence(measurement.get("records"))]
    selected = [
        row
        for row in records
        if row.get("problem_type") == "bfs" and row.get("selected_index") == 0
    ]
    q.require(len(selected) == 1, "Expected exactly one frozen BFS token-budget row")
    row = selected[0]
    q.require(
        row.get("native_args") == ENV_ARGS
        and row.get("example_id") == 0
        and row.get("messages_sha256") == MESSAGES_SHA256
        and row.get("templated_input_tokens") == INPUT_TOKENS
        and row.get("output_budget_tokens") == OUTPUT_TOKENS
        and row.get("engine_reserve_tokens") == 2
        and row.get("budget_total_tokens") == INPUT_TOKENS + OUTPUT_TOKENS + 2
        and INPUT_TOKENS + OUTPUT_TOKENS + 2 <= CONTEXT_TOKENS,
        "Frozen GraphWalks selection or token budget changed; no substitution",
    )
    return {
        "schema_version": 1,
        "environment": "graphwalks",
        "model": cache.MODEL,
        "native_args": ENV_ARGS,
        "sampling_args": SAMPLING,
        "request_seed_policy": "new-segment generation seed0; historical selector seed0 retained",
        "num_examples": 1,
        "rollouts_per_example": 1,
        "native_population_rows": 50,
        "native_context_tokens": CONTEXT_TOKENS,
        "input_tokens": INPUT_TOKENS,
        "output_budget_tokens": OUTPUT_TOKENS,
        "example_id": 0,
        "messages_sha256": MESSAGES_SHA256,
        "token_budget_row": row,
        "tokenizer_files_sha256": measurement["tokenizer_files_sha256"],
    }


def source_paths() -> list[Path]:
    """Exact local source/lock/raw-data closure; never exported task fixtures."""
    names = (
        "bench/direct_context.py",
        "bench/cache.py",
        "bench/decode.py",
        "bench/power.py",
        "bench/numerical.py",
        "eval/measure.py",
        "serve/qualification.py",
        "bend/adapter.py",
        "bend/build_toolchain.py",
        "eval/direct/run",
        "eval/direct/setup",
        "eval/direct/prepare_transport.py",
        "eval/direct/inspect_dataset.py",
        "eval/direct/sources.lock",
        "eval/direct/graphwalks/pyproject.toml",
        "eval/direct/graphwalks/uv.lock",
        "eval/direct/mrcr/pyproject.toml",
        "eval/direct/mrcr/uv.lock",
        "eval/direct/configs/diverse/graphwalks-bfs.toml",
        "eval/direct/graphwalks-upper-current-token-budget.json",
        "eval/scripts/data",
        "eval/datasets.lock",
    )
    paths = [ROOT / name for name in names]
    for checkout, subtree in (
        ("verifiers-graphwalks", "verifiers"),
        ("prime-envs", "environments/graphwalks"),
    ):
        base = DIRECT / ".sources" / checkout
        result = subprocess.run(
            ["git", "-C", str(base), "ls-files", "-z", "--", subtree, "pyproject.toml"],
            check=True,
            capture_output=True,
        )
        tracked = [name for name in result.stdout.decode().split("\0") if name]
        q.require(bool(tracked), "Missing pinned native source closure")
        paths.extend(base / name for name in tracked)
    dataset = mapping(
        mapping(q.document(ROOT / "eval/datasets.lock")["huggingface"])["graphwalks"]
    )
    revision = q.text(dataset.get("revision"))
    q.require(
        revision == "f338bb265735a56a79f4b0f5def722c9c3268ead",
        "GraphWalks revision changed",
    )
    snapshot = (
        ROOT
        / "eval/.cache/huggingface/hub/datasets--openai--graphwalks/snapshots"
        / revision
    )
    paths.extend(
        snapshot / q.text(mapping(item).get("path"))
        for item in sequence(dataset.get("files"))
    )
    return sorted({path.resolve(strict=True) for path in paths})


def _source_closure() -> dict[str, str]:
    return {str(path): q.digest(path) for path in source_paths()}


def _check_sources(value: object) -> dict[str, object]:
    closure = mapping(value)
    q.require(closure == _source_closure(), "Direct source/data closure changed")
    return closure


def _identity(
    output: Path, expected: dict[str, object] | None = None
) -> dict[str, object]:
    evidence = q.Evidence(output / "report.json")
    identity = q.captures(
        evidence,
        str(output / "identity-before.json"),
        str(output / "identity-after.json"),
    )
    if expected is not None:
        q.require(
            identity == expected,
            "Direct run belongs to another caller container/recipe",
        )
    _check_tokenizer(identity)
    return identity


def _check_tokenizer(identity: dict[str, object]) -> None:
    actual = mapping(identity.get("actual_server"))
    q.require(
        actual.get("context_length") == CONTEXT_TOKENS
        and actual.get("tokenizer_path") in (None, actual.get("model_path")),
        "Direct row requires the native prepared target tokenizer/context",
    )
    target = mapping(mapping(identity.get("model_inventory")).get("target"))
    expected = mapping(frozen_identity()["tokenizer_files_sha256"])
    q.require(
        all(
            target.get(name) == expected.get(name)
            for name in (
                "tokenizer.json",
                "tokenizer_config.json",
                "chat_template.jinja",
            )
        ),
        "Prepared tokenizer/template differs from the frozen long-input token proof",
    )


def _raw_config(path: Path) -> dict[str, object]:
    configs = sequence(
        _native_function("verifiers.utils.eval_utils", "load_toml_config")(path)
    )
    q.require(
        len(configs) == 1, "Diverse direct profile must contain exactly one evaluation"
    )
    config = mapping(configs[0])
    expected: dict[str, object] = {
        "model": cache.MODEL,
        "api_key_var": "QWEN_API_KEY",
        "api_client_type": "openai_chat_completions",
        "max_concurrent": 1,
        "independent_scoring": True,
        "num_workers": 1,
        "disable_env_server": True,
        "disable_tui": True,
        "save_results": True,
        "save_to_hf_hub": False,
        "output_dir": "results",
        "state_columns": ["trajectory"],
        "max_retries": 0,
        "num_examples": 1,
        "rollouts_per_example": 1,
        "sampling_args": SAMPLING,
        "env_id": "graphwalks",
        "name": "diverse-direct-graphwalks-bfs",
        "env_args": ENV_ARGS,
    }
    q.require(config.get("api_base_url") in URLS, "Unapproved direct endpoint")
    q.require(
        {key: value for key, value in config.items() if key != "api_base_url"}
        == expected,
        "Unexpected normalized native GraphWalks configuration",
    )
    return config


def _execute(config_path: Path, run: Path, *, dry: bool) -> None:
    """Load/score via original upstream APIs; freeze selection before native runner."""
    vf = importlib.import_module("verifiers")
    graphwalks = importlib.import_module("graphwalks")
    q.require(
        Path(q.text(vf.__file__)).resolve()
        == DIRECT / ".sources/verifiers-graphwalks/verifiers/__init__.py"
        and Path(q.text(graphwalks.__file__)).resolve()
        == DIRECT / ".sources/prime-envs/environments/graphwalks/graphwalks.py",
        "Native imports do not resolve to the pinned original source checkouts",
    )
    q.require(
        os.environ.get("HF_HUB_OFFLINE")
        == os.environ.get("HF_DATASETS_OFFLINE")
        == "1",
        "Direct native data loading must remain offline",
    )
    config = _raw_config(config_path)
    config_hash = q.digest(config_path)
    closure = _source_closure()
    os.chdir(run / "work")
    env = _native_function("graphwalks", "load_environment")(**ENV_ARGS)
    if not isinstance(env, _Environment):
        raise ValueError("Pinned native environment API changed")
    population = env.get_eval_dataset()
    selected = env.get_eval_dataset(n=1)
    q.require(
        type(env).__name__ == "SingleTurnEnv"
        and len(population) == 50
        and len(selected) == 1,
        "Native GraphWalks population/selection changed",
    )
    row = mapping(selected[0])
    q.require(
        row.get("example_id") == 0
        and _messages_hash(row.get("prompt")) == MESSAGES_SHA256,
        "Native selected full prompt differs from the frozen original row",
    )
    contract = frozen_identity()
    # This is the same native constructor used by the CLI, except its otherwise
    # hidden HTTP-retry default is explicitly zero. No global dispatch is patched.
    client = _native_function("verifiers.types", "ClientConfig")(
        client_type="openai_chat_completions",
        api_key_var="QWEN_API_KEY",
        api_base_url=config["api_base_url"],
        max_retries=0,
        extra_headers_from_state={"X-Session-ID": "trajectory_id"},
    )
    evaluation = _native_function("verifiers.types", "EvalConfig")(
        env_id="graphwalks",
        name=config["name"],
        env_args=ENV_ARGS,
        env_dir_path="./environments",
        model=cache.MODEL,
        client_config=client,
        sampling_args=SAMPLING,
        num_examples=1,
        rollouts_per_example=1,
        max_concurrent=1,
        num_workers=1,
        independent_scoring=True,
        max_retries=0,
        disable_env_server=True,
        disable_tui=True,
        output_dir="results",
        state_columns=["trajectory"],
        save_results=True,
        save_to_hf_hub=False,
    )
    if not isinstance(evaluation, _Serializable):
        raise ValueError("Pinned native configuration cannot be serialized")
    merged_sampling = {**mapping(env.sampling_args), **SAMPLING}
    manifest = {
        "schema_version": 1,
        "producer": "bench.direct_context.native-preflight",
        "frozen_at_unix": time.time(),
        "requests_sent": 0,
        "contract": contract,
        "config_sha256": config_hash,
        "normalized_config": config,
        "native_eval_config": evaluation.model_dump(mode="json"),
        "effective_sampling_args": merged_sampling,
        "native_row": row,
        "selected_row_sha256": _hash(row),
        "source_closure": closure,
    }
    q.save(run / "provenance/native-preflight.json", manifest)
    q.require(
        q.digest(config_path) == config_hash,
        "Effective config changed during native preflight",
    )
    _ = _check_sources(closure)
    if not dry:
        q.require(
            os.environ.get("QWEN_EVAL_ALLOW_REQUESTS") == "1"
            and bool(os.environ.get("QWEN_API_KEY")),
            "Explicit endpoint approval and private key transport are required",
        )
        asyncio.run(_native_evaluation(evaluation))


def _one(paths: list[Path], label: str) -> Path:
    q.require(len(paths) == 1, f"Expected exactly one native {label}")
    return paths[0]


def _count(value: object) -> int:
    count = number(value)
    q.require(count >= 0 and count.is_integer(), "Invalid native token count")
    return int(count)


def admit(
    output: Path, expected_identity: dict[str, object] | None = None
) -> dict[str, object]:
    """Independently admit saved native rows; never trust the collector's report."""
    output = output.resolve(strict=True)
    identity = _identity(output, expected_identity)
    launch = q.document(output / "launch.json")
    clock = q.document(output / "wrapper-clock.json")
    q.require(
        clock.get("exit_code") == 0,
        "Native direct wrapper failed; raw failure retained",
    )
    elapsed_wrapper = number(clock.get("elapsed_seconds"))
    q.require(elapsed_wrapper > 0, "Missing wrapper wall interval")
    run = output / "native"
    manifest_path = run / "provenance/native-preflight.json"
    manifest = q.document(manifest_path)
    q.require(
        manifest.get("producer") == "bench.direct_context.native-preflight"
        and manifest.get("requests_sent") == 0
        and manifest.get("contract") == frozen_identity(),
        "Invalid pre-result native freeze",
    )
    closure = _check_sources(manifest.get("source_closure"))
    q.require(
        closure == launch.get("source_closure"),
        "Direct source closure changed after launch freeze",
    )
    q.require(
        launch.get("contract") == frozen_identity()
        and launch.get("container_id") == identity.get("container_id"),
        "Launch does not match frozen row or caller container",
    )
    config = mapping(manifest.get("normalized_config"))
    native = mapping(manifest.get("native_eval_config"))
    client = mapping(native.get("client_config"))
    q.require(
        config.get("api_base_url") == launch.get("endpoint")
        and config.get("env_args") == native.get("env_args") == ENV_ARGS
        and config.get("sampling_args") == native.get("sampling_args") == SAMPLING
        and manifest.get("effective_sampling_args") == {"n": 1, **SAMPLING}
        and native.get("model") == cache.MODEL
        and native.get("env_id") == "graphwalks"
        and native.get("num_examples") == native.get("rollouts_per_example") == 1
        and native.get("max_concurrent") == native.get("num_workers") == 1
        and native.get("max_retries") == client.get("max_retries") == 0
        and native.get("independent_scoring") is True
        and native.get("disable_env_server") is True
        and native.get("state_columns") == ["trajectory"]
        and native.get("save_results") is True
        and native.get("save_to_hf_hub") is False
        and native.get("resume_path") is None
        and client.get("api_base_url") == config.get("api_base_url")
        and client.get("client_type") == "openai_chat_completions"
        and client.get("api_key_var") == "QWEN_API_KEY"
        and client.get("endpoint_configs") == [],
        "Native resolved runner/client differs from the frozen no-retry contract",
    )
    config_path = run / "provenance/effective-configs/graphwalks-bfs.toml"
    q.require(
        q.digest(config_path) == manifest.get("config_sha256"),
        "Effective direct config changed",
    )
    transport = q.document(config_path.with_suffix(".provenance.json"))
    q.require(
        transport.get("original_sha256") == q.digest(CONFIG)
        and transport.get("effective_sha256") == q.digest(config_path)
        and transport.get("native_normalized_nontransport_payload_identical") is True,
        "Missing transport-only config provenance",
    )
    original = mapping(manifest.get("native_row"))
    q.require(
        original.get("example_id") == 0
        and _messages_hash(original.get("prompt")) == MESSAGES_SHA256
        and _hash(original) == manifest.get("selected_row_sha256"),
        "Native row manifest changed",
    )
    results_path = _one(
        list((run / "work/results").rglob("results.jsonl")), "results.jsonl"
    )
    metadata_path = _one(
        list((run / "work/results").rglob("metadata.json")), "metadata.json"
    )
    q.require(
        results_path.parent == metadata_path.parent,
        "Mismatched native metadata/result directory",
    )
    rows: list[dict[str, object]] = []
    with results_path.open(encoding="utf-8") as stream:
        for line in stream:
            if line.strip():
                value: object = json.loads(line, object_pairs_hook=q.pairs)
                rows.append(mapping(value))
    q.require(
        len(rows) == 1, "Expected exactly one saved native rollout; no replacements"
    )
    row = rows[0]
    _ = q.canonical(row)
    q.require(
        row.get("example_id") == original.get("example_id")
        and row.get("prompt") == original.get("prompt")
        and row.get("answer") == original.get("answer"),
        "Saved result is not the preselected original task",
    )
    q.require(
        row.get("is_completed") is True
        and type(row.get("is_truncated")) is bool
        and row.get("error") is None
        and row.get("stop_condition") == "max_turns_reached",
        "Native rollout failed or is incomplete; raw outcome retained without reroll",
    )
    steps = sequence(row.get("trajectory"))
    q.require(len(steps) == 1, "Expected one native model call")
    step = mapping(steps[0])
    response = mapping(step.get("response"))
    message = mapping(response.get("message"))
    finish = message.get("finish_reason")
    truncated = finish == "length"
    q.require(
        step.get("prompt") == original.get("prompt")
        and step.get("completion") == row.get("completion")
        and response.get("model") == cache.MODEL
        and finish in ("stop", "length")
        and step.get("is_truncated") is truncated
        and message.get("is_truncated") is truncated
        and row.get("is_truncated") is truncated,
        "Original full prompt, native model, completion, or finish evidence mismatched",
    )
    usage = mapping(response.get("usage"))
    inputs, completions = (
        _count(usage.get("prompt_tokens")),
        _count(usage.get("completion_tokens")),
    )
    q.require(
        inputs == INPUT_TOKENS
        and 0 < completions <= OUTPUT_TOKENS
        and _count(usage.get("total_tokens")) == inputs + completions,
        "Actual native input/output usage violates frozen full-prompt budget",
    )
    metadata = q.document(metadata_path)
    for totals in (mapping(row.get("token_usage")), mapping(metadata.get("usage"))):
        q.require(
            _count(totals.get("input_tokens")) == inputs
            and _count(totals.get("output_tokens")) == completions,
            "Native usage aggregates disagree",
        )
    reward = number(row.get("reward"))
    q.require(
        reward in (0.0, 1.0)
        and number(mapping(row.get("metrics")).get("_exact_reward")) == reward,
        "Missing original exact-BFS rubric reward",
    )
    q.require(
        metadata.get("env_id") == "graphwalks"
        and metadata.get("env_args") == ENV_ARGS
        and metadata.get("name") == "diverse-direct-graphwalks-bfs"
        and metadata.get("model") == cache.MODEL
        and metadata.get("base_url") == config.get("api_base_url")
        and metadata.get("num_examples") == metadata.get("rollouts_per_example") == 1
        and metadata.get("sampling_args") == manifest.get("effective_sampling_args")
        and metadata.get("state_columns") == ["trajectory"]
        and number(metadata.get("avg_error")) == 0
        and number(metadata.get("avg_reward")) == reward
        and number(mapping(metadata.get("avg_metrics")).get("_exact_reward")) == reward,
        "Official native metadata/reward differs from the frozen run",
    )
    timing = mapping(row.get("timing"))
    model_clock = mapping(timing.get("model"))
    spans = sequence(model_clock.get("spans"))
    q.require(len(spans) == 1, "Missing native one-call wall timing")
    span = mapping(spans[0])
    start, end = number(span.get("start")), number(span.get("end"))
    seconds = end - start
    q.require(
        number(clock.get("started_at_unix"))
        <= number(manifest.get("frozen_at_unix"))
        <= start
        < end
        <= number(clock.get("ended_at_unix"))
        and abs(number(span.get("duration")) - seconds) < 1e-6
        and abs(number(model_clock.get("duration")) - seconds) < 1e-6,
        "Native model clock lies outside the observed wrapper interval",
    )
    native_wall = number(metadata.get("time"))
    q.require(
        seconds <= native_wall <= elapsed_wrapper + 1,
        "Invalid native whole-evaluation wall interval",
    )
    evidence = [
        path
        for path in output.rglob("*")
        if path.is_file()
        and not path.is_symlink()
        and "cache" not in path.relative_to(output).parts
        and path.name not in ("report.json", "failure.json")
    ]
    paths = sorted({str(path.resolve(strict=True)) for path in evidence} | set(closure))
    return {
        "schema_version": 1,
        "producer": "bench.direct_context.admit",
        "reward": reward,
        "input_tokens": inputs,
        "completion_tokens": completions,
        "elapsed_seconds": seconds,
        "metric_scope": METRIC_SCOPE,
        "model_call_output_tok_s": completions / seconds,
        "wrapper_wall_seconds": elapsed_wrapper,
        "native_eval_wall_seconds": native_wall,
        "model_call_started_at_unix": start,
        "model_call_ended_at_unix": end,
        "selected_row_sha256": manifest["selected_row_sha256"],
        "messages_sha256": MESSAGES_SHA256,
        "frozen_identity": frozen_identity(),
        "is_truncated": truncated,
        "finish_reason": finish,
        "error": None,
        "native_population_rows": 50,
        "source_closure": closure,
        "evidence_paths": paths,
        "evidence_sha256": {path: q.digest(Path(path)) for path in paths},
        "full_qualification": False,
    }


def collect(output: Path, key_file: Path, container: str) -> dict[str, object]:
    """Run once in a fresh directory, under the caller's external hard deadline."""
    q.require(
        os.environ.get("QWEN_EVAL_ALLOW_REQUESTS") == "1",
        "Explicit endpoint approval required",
    )
    endpoint = os.environ.get("QWEN_EVAL_BASE_URL", URLS[0])
    q.require(endpoint in URLS, "Unapproved direct endpoint")
    q.require(
        output.is_absolute() and output.resolve() == output and output.parent.is_dir(),
        "Direct output requires a canonical absolute fresh directory",
    )
    q.require(
        key_file.is_absolute() and not key_file.is_symlink(),
        "Expected absolute private key file",
    )
    info = key_file.stat()
    q.require(
        stat.S_ISREG(info.st_mode)
        and info.st_uid == os.getuid()
        and stat.S_IMODE(info.st_mode) in (0o400, 0o600)
        and 0 < info.st_size <= 4097,
        "Expected owned private serving key",
    )
    mask = os.umask(0o077)
    try:
        output.mkdir(mode=0o700)
        try:
            before = decode.capture_identity(
                output, container, endpoint.removesuffix("/v1"), str(key_file)
            )
            _check_tokenizer(before)
            closure = _source_closure()
            command = [
                str(DIRECT / "run"),
                "diverse",
                "graphwalks",
                "--output-dir",
                str(output / "native"),
            ]
            q.save(
                output / "launch.json",
                {
                    "command": command,
                    "container_id": before["container_id"],
                    "endpoint": endpoint,
                    "contract": frozen_identity(),
                    "source_closure": closure,
                },
            )
            environment = os.environ.copy()
            environment.pop("QWEN_API_KEY", None)
            environment.update({
                "QWEN_API_KEY_FILE": str(key_file),
                "QWEN_EVAL_BASE_URL": endpoint,
                "QWEN_RECIPE_ID": _hash(before),
            })
            start_wall, start = time.time(), time.monotonic()
            with (
                (output / "wrapper.stdout").open("xb") as stdout,
                (output / "wrapper.stderr").open("xb") as stderr,
            ):
                result = subprocess.run(
                    command,
                    cwd=ROOT,
                    env=environment,
                    stdout=stdout,
                    stderr=stderr,
                    check=False,
                )
            q.save(
                output / "wrapper-clock.json",
                {
                    "started_at_unix": start_wall,
                    "ended_at_unix": time.time(),
                    "elapsed_seconds": time.monotonic() - start,
                    "exit_code": result.returncode,
                    "scope": "complete direct wrapper: setup/data checks, native loading, generation, grading, persistence",
                },
            )
            decode.capture_identity(
                output,
                container,
                endpoint.removesuffix("/v1"),
                str(key_file),
                after=True,
                native_exit_code=result.returncode,
            )
            report = admit(output, before)
            q.save(output / "report.json", report)
            return report
        except Exception as error:
            q.save(
                output / "failure.json",
                {
                    "status": "rejected",
                    "error_type": type(error).__name__,
                    "raw_evidence_preserved": True,
                    "full_qualification": False,
                },
            )
            raise
    finally:
        os.umask(mask)


class _Arguments(argparse.Namespace):
    action: str = ""
    output: Path = Path()
    key_file: Path = Path()
    container: str = ""
    config: Path = Path()
    run: Path = Path()
    dry_run: bool = False


def main() -> None:
    """Separate host collection from the pinned native Python execution context."""
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="action", required=True)
    collect_parser = commands.add_parser("collect")
    collect_parser.add_argument("--output", type=Path, required=True)
    collect_parser.add_argument("--key-file", type=Path, required=True)
    collect_parser.add_argument("--container", required=True)
    execute_parser = commands.add_parser("execute")
    execute_parser.add_argument("--config", type=Path, required=True)
    execute_parser.add_argument("--run", type=Path, required=True)
    execute_parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args(namespace=_Arguments())
    if args.action == "collect":
        _ = collect(args.output, args.key_file, args.container)
    else:
        _execute(args.config, args.run, dry=args.dry_run)


if __name__ == "__main__":
    main()
