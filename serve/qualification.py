#!/usr/bin/env python3
"""Local, fail-closed evidence checking, not an independent trust boundary.

Run as ``python -m serve.qualification`` from the repository root. Qualification
never sends inference requests, changes a service, or supplies a quality scorer.
All outputs are exclusive-create canonical JSON; old evidence is never rebound.
"""

from __future__ import annotations

import argparse
import csv
from fractions import Fraction
import hashlib
import http.client
import inspect
import json
import math
import re
import subprocess
import sys
import time
import tomllib
from collections import Counter
from collections.abc import Callable
from pathlib import Path
from urllib.parse import urlsplit

from bend import adapter, build_toolchain
from bench import cache, decode
from bench.power import PowerSample, PowerSampler
from eval.measure import efficiency_report, load_episodes, mapping, number, sequence

ROOT = Path(__file__).resolve().parents[1]
ENVIRONMENTS = ("aime24", "aime25", "aime26", "i3-logic", "livecodebench")
PROTOCOL = "qwen-native-qualification-v2"


def profile_environments(profile: str) -> tuple[str, ...]:
    """Keep sampled math explicitly separate from the unchanged core suite."""
    require(
        profile in ("tiny", "quick", "full"),
        "Qualification requires a frozen tiny, quick or full profile, not smoke",
    )
    return ("aime25",) if profile == "tiny" else ENVIRONMENTS


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def integer(value: object) -> int:
    require(
        type(value) is int, "Expected an exact integer, not a flag or missing count"
    )
    if not isinstance(value, int):
        raise ValueError("Expected integer")
    return value


def text(value: object) -> str:
    require(isinstance(value, str) and bool(value), "Expected a nonempty string")
    if not isinstance(value, str):
        raise ValueError("Expected string")
    return value


def canonical(value: object) -> bytes:
    return (
        json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False) + "\n"
    ).encode()


def digest(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def pairs(items: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in items:
        require(key not in result, "Duplicate JSON object key")
        result[key] = value
    return result


def document(path: Path) -> dict[str, object]:
    value: object = json.loads(path.read_bytes(), object_pairs_hook=pairs)
    result = mapping(value)
    _ = canonical(result)  # Reject NaN/Infinity anywhere, including unused fields.
    return result


def save(path: Path, value: object) -> None:
    with path.open("xb") as stream:
        _ = stream.write(canonical(value))


class Evidence:
    """The explicit raw artifact closure, rehashed on every qualification/verification."""

    def __init__(self, manifest: Path) -> None:
        self.base: Path = manifest.resolve().parent
        self.hashes: dict[str, str] = {}

    def path(self, value: object) -> Path:
        path = Path(text(value))
        return (self.base / path).resolve(strict=True)

    def retain(self, path: Path) -> Path:
        path = path.resolve(strict=True)
        require(path.is_file(), f"Missing regular evidence file: {path}")
        value = digest(path)
        old = self.hashes.setdefault(str(path), value)
        require(old == value, f"Evidence changed during verification: {path}")
        return path

    def read(self, value: object) -> dict[str, object]:
        return document(self.retain(self.path(value)))

    def tree(self, root: Path) -> dict[str, str]:
        require(root.is_dir(), f"Missing evidence directory: {root}")
        result: dict[str, str] = {}
        for path in sorted(root.rglob("*")):
            if "__pycache__" in path.parts:
                continue
            require(not path.is_symlink(), f"Symlink in retained evidence: {path}")
            if path.is_file():
                retained = self.retain(path)
                result[path.relative_to(root).as_posix()] = self.hashes[str(retained)]
        require(bool(result), f"Empty evidence directory: {root}")
        return result


def native_identity(value: object) -> dict[str, object]:
    identity = mapping(value)
    require(
        re.fullmatch(r"[0-9a-f]{64}", text(identity.get("container_id"))) is not None,
        "Identity must contain the full running container ID",
    )
    require(
        re.fullmatch(r"sha256:[0-9a-f]{64}", text(identity.get("image_sha256")))
        is not None,
        "Identity must contain an immutable image SHA, not a tag",
    )
    _ = text(identity.get("container_started_at"))
    actual = mapping(identity.get("actual_server"))
    require(
        integer(actual.get("context_length")) == 262144,
        "Evaluation requires actual native context262144; fallback evaluation is forbidden",
    )
    require(
        integer(actual.get("max_total_num_tokens")) >= 263168,
        "Missing actually backed native token pool; configured size is not capacity",
    )
    require(
        bool(mapping(identity.get("model_inventory"))),
        "Missing verified prepared model inventories",
    )
    require(
        bool(mapping(identity.get("bend_artifacts"))),
        "Missing retained Bend artifact identity",
    )
    require(
        re.fullmatch(r"[0-9a-f]{64}", text(identity.get("server_config_sha256")))
        is not None,
        "Missing exact server configuration digest",
    )
    return identity


def recipe_identity(identity: dict[str, object]) -> dict[str, object]:
    """Restarts may change the observed instance, never the measured recipe."""
    return {
        key: value
        for key, value in identity.items()
        if key not in {"container_id", "container_started_at"}
    }


CONTAINER_ARTIFACTS = r"""
import contextlib, hashlib, importlib.util, io, json, sys
from pathlib import Path
from bend.adapter import checked_plan
target, draft = sys.argv[1:]
preparation = Path('/model-preparation')
spec = importlib.util.spec_from_file_location('prepared_model_verifier', preparation / 'verify-models.py')
verifier = importlib.util.module_from_spec(spec)
spec.loader.exec_module(verifier)
with contextlib.redirect_stdout(io.StringIO()):
    verifier.verify(Path(target), Path(draft), 'packed')
    checked_plan(Path('/opt/qwen/bend'), 262144, 263168, 128)
def sha(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()
root = Path('/opt/qwen/bend')
print(json.dumps({
    'model_inventory': {
        'target': verifier.inventory((preparation / 'source.sha256').read_bytes(), verifier.TARGET_NAMES),
        'draft': verifier.inventory((preparation / 'draft.sha256').read_bytes(), verifier.DRAFT_NAMES),
        'preparation': {p.name: sha(p) for p in preparation.iterdir() if p.is_file()},
    },
    'bend_artifacts': {p.relative_to(root).as_posix(): sha(p) for p in root.rglob('*') if p.is_file() and '__pycache__' not in p.parts},
    'bend_toolchain_sha256': sha(Path('/opt/qwen/bend-toolchain.json')),
    'bend_toolchain': json.loads(Path('/opt/qwen/bend-toolchain.json').read_bytes()),
    'draft_vocabulary_sha256': sha(Path('/state/draft_vocab_ids.json')),
}, sort_keys=True))
"""


def docker(*arguments: str, timeout: int = 30) -> str:
    try:
        result = subprocess.run(
            ["docker", *arguments],
            capture_output=True,
            text=True,
            timeout=timeout,
            check=True,
        )
    except (OSError, subprocess.SubprocessError) as error:
        raise ValueError(
            "Read-only container evidence capture failed; verify metadata access and prepared artifacts"
        ) from error
    return result.stdout.strip()


def toolchain_identity(identity: dict[str, object]) -> None:
    """Bind the selected release or exact installed package to retained compiler bytes."""
    record = mapping(identity.get("bend_toolchain"))
    release, runtime = (mapping(record.get(name)) for name in ("release", "runtime"))
    require(
        set(record)
        == {
            "schema",
            "claim",
            "release",
            "build_helper_sha256",
            "release_resources_sha256",
            "runtime",
            "execution",
            "installed_compiler_sha256",
        }
        and record.get("schema") == 4
        and release
        == {
            "url": build_toolchain.RELEASE_URL,
            "sha256": build_toolchain.RELEASE_SHA256,
            "version": build_toolchain.VERSION.rstrip("\n"),
        }
        and record.get("build_helper_sha256")
        == digest(ROOT / "bend/build_toolchain.py")
        and record.get("execution")
        == {
            "mode": "release",
            "command_prefix": ["bin/bend"],
            "environment": {"BEND_NO_TELEMETRY": "1"},
        },
        "Bend toolchain is not the pinned original 2.0.20 release",
    )
    require(
        set(runtime)
        == {
            "release_executable_sha256",
            "packaged_executable_sha256",
            "transport",
            "relocation_recipe_sha256",
            "selected_package",
            "selected_derivation",
            "selected_derivation_sha256",
            "selected_release",
        }
        and runtime.get("release_executable_sha256") == build_toolchain.RUNTIME_SHA256,
        "Unsupported Bend release transport identity",
    )
    compiler = mapping(record.get("installed_compiler_sha256"))
    names: set[str] = set(build_toolchain.COMPILER_NAMES)
    transport = runtime.get("transport")
    require(
        transport in ("release", "nix-patchelf", "selected-installed"),
        "Unsupported Bend compiler transport",
    )
    native_sha256 = text(runtime.get("packaged_executable_sha256"))
    if transport == "nix-patchelf":
        require(
            runtime.get("relocation_recipe_sha256") == digest(ROOT / "nix/bend.nix")
            and native_sha256 in adapter.NATIVE_RUNTIME_SHA256,
            "Nix Bend compiler differs from the observed frozen relocation recipe",
        )
    else:
        require(
            runtime.get("relocation_recipe_sha256") is None
            and native_sha256
            == (
                build_toolchain.SELECTED_RUNTIME_SHA256
                if transport == "selected-installed"
                else build_toolchain.RUNTIME_SHA256
            ),
            "Native Bend differs from the exact selected release or installation",
        )
    selected = transport == "selected-installed"
    selected_origin = {
        "selected_package": build_toolchain.SELECTED_PACKAGE,
        "selected_derivation": build_toolchain.SELECTED_DERIVATION,
        "selected_derivation_sha256": build_toolchain.SELECTED_DERIVATION_SHA256,
        "selected_release": build_toolchain.SELECTED_RELEASE,
    }
    require(
        all(
            runtime.get(name) == (value if selected else None)
            for name, value in selected_origin.items()
        ),
        "Selected installed Bend provenance differs from the inspected Nix derivation",
    )
    artifacts = mapping(identity.get("bend_artifacts"))
    require(
        set(compiler) == names
        and compiler.get("bin/bend") == native_sha256
        and all(
            artifacts.get("compiler/" + name) == value
            for name, value in compiler.items()
        ),
        "Bend retained compiler differs from the exact release or selected installation",
    )
    resources = mapping(record.get("release_resources_sha256"))
    require(
        resources.get("bend2/base.bend") == build_toolchain.BASE_SHA256
        and artifacts.get("compiler/bend2/base.bend") == build_toolchain.BASE_SHA256
        and all(
            resources.get(name.removeprefix("compiler/")) == value
            for name, value in artifacts.items()
            if name.startswith("compiler/")
            and name.removeprefix("compiler/") not in compiler
        ),
        "Bend retained Base dependency closure differs from original release resources",
    )


def runtime_identity(
    container: str, base_url: str, key_file: Path
) -> dict[str, object]:
    """Extend the existing container capture once; never persist raw server args."""
    identity = decode.container_identity(container)
    identifier = text(identity["container_id"])
    started = docker("inspect", "-f", "{{.State.StartedAt}}", identifier)
    endpoint = urlsplit(base_url)
    require(
        endpoint.scheme == "http"
        and endpoint.hostname in ("127.0.0.1", "localhost")
        and endpoint.path in ("", "/", "/v1", "/v1/")
        and not endpoint.username
        and not endpoint.password
        and not endpoint.query
        and not endpoint.fragment,
        "Serving metadata must use the local authenticated evaluation endpoint",
    )
    port = endpoint.port or 80
    ports_value: object = json.loads(
        docker("inspect", "-f", "{{json .NetworkSettings.Ports}}", identifier)
    )
    bindings = sequence(mapping(ports_value).get("18020/tcp"))
    require(
        any(
            mapping(binding).get("HostPort") == str(port)
            and mapping(binding).get("HostIp") in ("127.0.0.1", "0.0.0.0", "")
            for binding in bindings
        ),
        "Endpoint port is not published by the selected container",
    )
    require(
        key_file.is_file() and not key_file.is_symlink(),
        "Expected a regular private key file",
    )
    key = key_file.read_text(encoding="ascii").rstrip("\n")
    require(
        0 < len(key) <= 4096 and all(33 <= ord(char) <= 126 for char in key),
        "Invalid API key file",
    )

    def metadata(path: str) -> dict[str, object]:
        connection = http.client.HTTPConnection("127.0.0.1", port, timeout=30)
        try:
            connection.request("GET", path, headers={"Authorization": "Bearer " + key})
            response = connection.getresponse()
            require(response.status == 200, "Authenticated server metadata unavailable")
            body = response.read(16 * 1024 * 1024 + 1)
            require(len(body) <= 16 * 1024 * 1024, "Server metadata exceeds bound")
            value: object = json.loads(body, object_pairs_hook=pairs)
            return mapping(value)
        finally:
            connection.close()

    info, model = metadata("/server_info"), metadata("/model_info")
    require(info.get("status") == "ready", "Serving scheduler is not ready")
    require(
        integer(info.get("context_length")) == 262144,
        "Refusing evaluation: actual native context is not262144",
    )
    require(
        integer(info.get("max_total_num_tokens")) >= 263168,
        "Refusing evaluation: actual native pool is not backed",
    )
    states = sequence(info.get("internal_states"))
    require(len(states) == 1, "Exactly one native scheduler is required")
    state = mapping(states[0])
    fields = (
        "context_length",
        "max_total_tokens",
        "max_total_num_tokens",
        "model_path",
        "tokenizer_path",
        "speculative_draft_model_path",
        "speculative_algorithm",
        "speculative_dflash_block_size",
        "speculative_draft_window_size",
        "kv_cache_dtype",
        "page_size",
        "tp_size",
        "dtype",
        "load_format",
        "attention_backend",
        "speculative_draft_attention_backend",
        "max_running_requests",
        "chunked_prefill_size",
        "mem_fraction_static",
        "disable_cuda_graph",
        "kvarn_commit_graph",
    )
    actual = {name: state.get(name, info.get(name)) for name in fields}
    actual["max_total_num_tokens"] = info["max_total_num_tokens"]
    require(
        actual["model_path"] == "/models/compact-target-rholsc8k/packed"
        and actual["speculative_draft_model_path"]
        == "/models/Qwen3.8-27B-DFlash2-W4A16"
        and actual["speculative_algorithm"] == "DFLASH",
        "Only the prepared packed Qwen/DFlash2 pair is in scope",
    )
    require(
        model.get("model_path") == actual["model_path"],
        "Live model differs from startup model",
    )
    # Keep only a digest of complete resolved settings. Never serialize raw args,
    # Docker Cmd/Env, keys, or live throughput/cache/memory gauges.
    omitted = {
        "internal_states",
        "startup_time",
        "kv_events",
        "last_gen_throughput",
        "memory_usage",
        "avg_spec_accept_length",
        "step_time_dict",
        "env_vars",
        "dspark_info_record",
    }
    safe_keys = [
        name
        for name in info
        if name not in omitted
        and not any(
            secret in name.lower()
            for secret in ("api_key", "password", "secret", "credential")
        )
    ]
    settings = {name: state.get(name, info[name]) for name in safe_keys}
    safe_model = {
        name: model.get(name)
        for name in ("model_path", "tokenizer_path", "is_generation", "weight_version")
    }
    gpu_rows = list(
        csv.reader(
            docker(
                "exec",
                identifier,
                "nvidia-smi",
                "--query-gpu=uuid,name,pci.bus_id,power.limit,driver_version",
                "--format=csv,noheader,nounits",
            ).splitlines()
        )
    )
    require(
        len(gpu_rows) == 1 and len(gpu_rows[0]) == 5,
        "Expected exactly one visible RTX3090 board",
    )
    uuid, gpu_name, pci, power_limit, driver = (value.strip() for value in gpu_rows[0])
    require(
        gpu_name == "NVIDIA GeForce RTX 3090" and float(power_limit) == 280,
        "Qualification requires the actual RTX3090/280W policy, without changing it",
    )
    identity["hardware"] = {
        "uuid": uuid,
        "name": gpu_name,
        "pci_bus_id": pci,
        "power_limit_watts": float(power_limit),
        "driver_version": driver,
    }
    artifact_value: object = json.loads(
        docker(
            "exec",
            "-e",
            "PYTHONDONTWRITEBYTECODE=1",
            identifier,
            "python3",
            "-c",
            CONTAINER_ARTIFACTS,
            text(actual["model_path"]),
            text(actual["speculative_draft_model_path"]),
            timeout=600,
        )
    )
    identity.update(mapping(artifact_value))
    from bench.numerical import runtime_components

    component_source = (
        inspect.getsource(runtime_components)
        + "\nimport json\nprint(json.dumps(runtime_components(),sort_keys=True))"
    )
    component_value: object = json.loads(
        docker(
            "exec",
            "-e",
            "PYTHONDONTWRITEBYTECODE=1",
            identifier,
            "python3",
            "-c",
            component_source,
            timeout=600,
        )
    )
    identity["component_identity"] = mapping(component_value)
    identity.update({
        "container_started_at": started,
        "actual_server": actual,
        "server_config_sha256": hashlib.sha256(canonical(settings)).hexdigest(),
        "live_model_sha256": hashlib.sha256(canonical(safe_model)).hexdigest(),
    })
    toolchain_identity(identity)
    final_container = decode.container_identity(identifier)
    require(
        final_container == {key: identity[key] for key in final_container}
        and docker("inspect", "-f", "{{.State.StartedAt}}", identifier) == started,
        "Container changed during identity capture",
    )
    return native_identity(identity)


def capture_identity(
    container: str,
    base_url: str,
    key_file: Path,
    output: Path,
    match: Path | None,
    native_exit_code: int | None,
) -> None:
    identity = runtime_identity(container, base_url, key_file)
    result: dict[str, object] = {
        "schema_version": 1,
        "producer": "serve.qualification.capture",
        "producer_sha256": digest(Path(__file__)),
        "captured_unix_ns": time.time_ns(),
        "captured_monotonic_ns": time.monotonic_ns(),
        "identity": identity,
        "native_exit_code": native_exit_code,
    }
    if match is not None:
        before = document(match)
        require(
            before.get("producer") == result["producer"],
            "Not a new native identity capture",
        )
        require(
            before.get("producer_sha256") == result["producer_sha256"],
            "Capture producer changed during native execution",
        )
        require(
            before.get("identity") == identity,
            "Serving identity changed during native evaluation",
        )
        result["before_sha256"] = digest(match)
    save(output, result)


TINY_NATIVE_PLAN = r"""
import json
import os
from pathlib import Path
import sys
import tempfile
import tomllib

root, provenance, snapshot = map(Path, sys.argv[1:])
os.environ.update({
    "HOME": str(root / ".cache/home"),
    "HF_HOME": str(root / ".cache/huggingface"),
    "HF_HUB_CACHE": str(root / ".cache/huggingface/hub"),
    "HF_HUB_OFFLINE": "1", "HF_DATASETS_OFFLINE": "1",
    "HF_HUB_DISABLE_TELEMETRY": "1",
})
with tempfile.TemporaryDirectory(prefix=".tiny-selection.", dir=provenance.parent) as cache:
    os.environ["HF_DATASETS_CACHE"] = cache
    from verifiers.v1.configs.cli.eval import EvalConfig
    from verifiers.v1.taskset import SEED
    from verifiers.v1.utils.loaders import load_taskset

    with (root / "configs/local.toml").open("rb") as stream:
        settings = tomllib.load(stream)
    with (provenance / "aime25.toml").open("rb") as stream:
        settings.update(tomllib.load(stream))
    settings["env"]["taskset"]["dataset_name"] = str(snapshot)
    settings["rich"] = None
    config = EvalConfig.model_validate(settings)
    taskset = load_taskset(config.env.taskset)
    selected = taskset.shuffle() if config.shuffle else taskset
    if config.num_tasks is not None:
        selected = selected.head(config.num_tasks)
    tasks = [{"key": task.key, "hash": task.hash, "type": type(task).__name__}
             for task in selected]
    resolved = config.model_dump(mode="json")
    resolved.pop("run")
    resolved.pop("output_dir")
    print(json.dumps({"shuffle_seed": SEED, "tasks": tasks, "resolved_config": resolved}))
"""


def tiny_native_plan(provenance: Path) -> dict[str, object]:
    """Replay only the pinned native loader/selection, offline and without inference."""
    root = ROOT / "eval"
    with (root / "configs/tiny/aime25.toml").open("rb") as stream:
        settings_value: object = tomllib.load(stream)
    settings = mapping(settings_value)
    require(
        all(
            settings.get(key) == value
            for key, value in (
                ("num_tasks", 3),
                ("num_rollouts", 1),
                ("shuffle", True),
                ("max_concurrent", 1),
            )
        ),
        "Tiny requires exactly three native shuffled tasks and one C1 rollout per task",
    )
    with (provenance / "aime25.toml").open("rb") as stream:
        launch_value: object = tomllib.load(stream)
    launch = mapping(launch_value)
    expected_env = mapping(settings.get("env"))
    expected_runtime = mapping(expected_env.get("agent"))
    runtime = mapping(expected_runtime.get("runtime"))
    runtime["image"] = (
        (root / ".cache/sandbox-image").read_text(encoding="utf-8").strip()
    )
    expected_runtime["runtime"] = runtime
    expected_env["agent"] = expected_runtime
    settings["env"] = expected_env
    require(
        launch == settings,
        "Tiny launch differs from its frozen profile beyond the pinned sandbox image",
    )
    dataset = mapping(
        mapping(document(root / "datasets.lock")["huggingface"])["aime25"]
    )
    snapshot = (
        root
        / ".cache/huggingface/hub"
        / ("datasets--" + text(dataset["repo"]).replace("/", "--"))
        / "snapshots"
        / text(dataset["revision"])
    )
    try:
        result = subprocess.run(
            [
                str(root / ".venv/bin/python"),
                "-I",
                "-c",
                TINY_NATIVE_PLAN,
                str(root),
                str(provenance),
                str(snapshot),
            ],
            capture_output=True,
            text=True,
            timeout=120,
            check=False,
        )
    except subprocess.TimeoutExpired as error:
        raise ValueError(
            "Pinned offline tiny selection did not finish; no partial task plan is admissible"
        ) from error
    require(result.returncode == 0, "Pinned offline native tiny task selection failed")
    plan = mapping(json.loads(result.stdout))
    tasks = sequence(plan.get("tasks"))
    require(
        integer(plan.get("shuffle_seed")) == 0
        and len(tasks) == 3
        and len({text(mapping(task).get("hash")) for task in tasks}) == 3,
        "Tiny native selection requires seed zero and three distinct unchanged tasks",
    )
    return plan


DIVERSE_NATIVE_PLAN = r"""
import hashlib
import json
import os
from pathlib import Path
import sys
import tempfile

root, provenance, snapshot = map(Path, sys.argv[1:])
os.environ.update({
    "HOME": str(root / ".cache/home"),
    "HF_HOME": str(root / ".cache/huggingface"),
    "HF_HUB_CACHE": str(root / ".cache/huggingface/hub"),
    "HF_HUB_OFFLINE": "1", "HF_DATASETS_OFFLINE": "1",
    "HF_HUB_DISABLE_TELEMETRY": "1",
})
with tempfile.TemporaryDirectory(prefix=".logic-selection.", dir=provenance.parent) as cache:
    os.environ["HF_DATASETS_CACHE"] = cache
    from pydantic_config import cli
    from verifiers.v1.cli.resolve import narrow_config
    from verifiers.v1.configs.cli.eval import EvalConfig
    from verifiers.v1.utils.loaders import load_taskset

    # Use the actual native CLI merger, including nested sampling overrides.
    argv = ["@", str(root / "configs/local.toml"),
            "@", str(provenance / "i3-logic.toml"),
            "--no-rich", "--no-push",
            "--env.taskset.dataset.name", str(snapshot / "logic"),
            "--env.taskset.dataset.subset", "default"]
    config = cli(narrow_config(EvalConfig, argv), args=argv)
    taskset = load_taskset(config.env.taskset)
    selected = taskset.shuffle() if config.shuffle else taskset
    if config.num_tasks is not None:
        selected = selected.head(config.num_tasks)
    tasks, source_rows = [], []
    for task in selected:
        tasks.append({"key": task.key, "hash": task.hash, "type": type(task).__name__})
        source_rows.append({
            "idx": task.data.idx,
            "task_name": task.data.task_name,
            "prompt_sha256": hashlib.sha256(task.data.prompt.encode()).hexdigest(),
        })
    resolved = config.model_dump(mode="json")
    resolved.pop("run")
    resolved.pop("output_dir")
    print(json.dumps({"selection_rule": "first_native_eligible_source_order",
                      "tasks": tasks, "source_rows": source_rows,
                      "resolved_config": resolved}))
"""


def diverse_native_plan(provenance: Path) -> dict[str, object]:
    """Freeze the native logic row before results, without changing its grader."""
    root = ROOT / "eval"
    with (root / "configs/diverse/i3-logic.toml").open("rb") as stream:
        settings_value: object = tomllib.load(stream)
    settings = mapping(settings_value)
    require(
        all(
            settings.get(key) == value
            for key, value in (
                ("num_tasks", 1),
                ("num_rollouts", 1),
                ("shuffle", False),
                ("max_concurrent", 1),
            )
        )
        and mapping(settings.get("sampling")) == {"max_tokens": 8192},
        "Diverse logic requires one source-order C1 rollout and an 8192-token call budget",
    )
    env = mapping(settings.get("env"))
    agent = mapping(env.get("agent"))
    require(
        mapping(env.get("taskset")) == {"id": "i3-logic"}
        and agent.get("max_turns") == 1
        and agent.get("max_output_tokens") == 8192,
        "Diverse logic requires unchanged native task defaults and an 8192-token episode budget",
    )
    runtime = mapping(agent.get("runtime"))
    runtime["image"] = (
        (root / ".cache/sandbox-image").read_text(encoding="utf-8").strip()
    )
    agent["runtime"] = runtime
    env["agent"] = agent
    settings["env"] = env
    with (provenance / "i3-logic.toml").open("rb") as stream:
        launch_value: object = tomllib.load(stream)
    require(
        mapping(launch_value) == settings,
        "Diverse logic launch differs beyond the pinned sandbox image",
    )
    dataset = mapping(
        mapping(document(root / "datasets.lock")["huggingface"])["i3-logic"]
    )
    snapshot = (
        root
        / ".cache/huggingface/hub"
        / ("datasets--" + text(dataset["repo"]).replace("/", "--"))
        / "snapshots"
        / text(dataset["revision"])
    )
    try:
        result = subprocess.run(
            [
                str(root / ".venv/bin/python"),
                "-I",
                "-c",
                DIVERSE_NATIVE_PLAN,
                str(root),
                str(provenance),
                str(snapshot),
            ],
            capture_output=True,
            text=True,
            timeout=120,
            check=False,
        )
    except subprocess.TimeoutExpired as error:
        raise ValueError(
            "Pinned offline logic selection did not finish; no partial plan is admissible"
        ) from error
    require(result.returncode == 0, "Pinned offline native logic selection failed")
    plan = mapping(json.loads(result.stdout))
    require(
        plan.get("selection_rule") == "first_native_eligible_source_order"
        and len(sequence(plan.get("tasks"))) == 1
        and len(sequence(plan.get("source_rows"))) == 1,
        "Diverse logic requires exactly the first native eligible row",
    )
    return plan


def frozen_inputs(
    profile: str, environment: str, provenance: Path
) -> dict[str, object]:
    """Hash frozen inputs and retain sentinel profiles' native pre-result selection."""
    root = ROOT / "eval"
    files = [
        root / name
        for name in (
            "prime-envs.lock",
            "datasets.lock",
            "uv.lock",
            "pyproject.toml",
            "configs/local.toml",
        )
    ]
    files.extend([
        ROOT / "flake.lock",
        ROOT / "bench/power.py",
        ROOT / "serve/qualification.py",
        root / "measure.py",
        root / ".cache/sandbox-image",
        provenance / f"{environment}.toml",
        root / "configs" / profile / f"{environment}.toml",
    ])
    for path in files:
        require(path.is_file(), f"Missing frozen evaluator input: {path}")
    files.extend(path for path in (root / "runtime").rglob("*") if path.is_file())
    files.extend(path for path in (root / "scripts").iterdir() if path.is_file())
    for source in (
        root / ".sources/prime-envs/environments",
        root / ".sources/verifiers/verifiers",
    ):
        require(source.is_dir(), f"Missing pinned evaluator source: {source}")
        files.extend(
            path
            for path in source.rglob("*")
            if path.suffix in (".py", ".toml", ".lock")
        )
    hashes = {str(path.resolve()): digest(path) for path in files if path.is_file()}
    dataset = document(root / "datasets.lock")
    name = "mrcr-v2" if environment.startswith("mrcr-v2-") else environment
    raw_files: list[tuple[Path, str, str, int]] = []
    if name == "mrcr-v2":
        for item in mapping(dataset["mrcr-v2"]).values():
            entry = mapping(item)
            raw_files.append((
                root / ".cache/mrcr_v2" / text(entry["filename"]),
                "sha256",
                text(entry["sha256"]),
                integer(entry["size"]),
            ))
    else:
        entry = mapping(mapping(dataset["huggingface"])[name])
        snapshot = (
            root
            / ".cache/huggingface/hub"
            / ("datasets--" + text(entry["repo"]).replace("/", "--"))
            / "snapshots"
            / text(entry["revision"])
        )
        for item in sequence(entry["files"]):
            raw = mapping(item)
            raw_files.append((
                snapshot / text(raw["path"]),
                text(raw["algorithm"]),
                text(raw["hash"]),
                integer(raw["size"]),
            ))
    for path, algorithm, expected, size in raw_files:
        require(path.stat().st_size == size, f"Pinned dataset size differs: {path}")
        sha = digest(path)
        if algorithm == "sha256":
            actual = sha
        else:
            require(algorithm == "git-sha1", "Unknown pinned dataset hash algorithm")
            blob = hashlib.sha1(f"blob {size}\0".encode())
            with path.open("rb") as stream:
                while chunk := stream.read(1024 * 1024):
                    blob.update(chunk)
            actual = blob.hexdigest()
        require(actual == expected, f"Pinned dataset bytes differ: {path}")
        hashes[str(path.resolve())] = sha
    result: dict[str, object] = {
        "schema_version": 1,
        "producer": "serve.qualification.freeze-eval",
        "profile": profile,
        "environment": environment,
        "files_sha256": hashes,
    }
    if profile == "tiny":
        require(
            environment == "aime25", "Tiny is only the frozen three-task AIME25 sample"
        )
        result["selection"] = tiny_native_plan(provenance)
    if profile == "diverse":
        require(environment == "i3-logic", "Diverse is only the frozen logic sentinel")
        result["selection"] = diverse_native_plan(provenance)
    return result


def captures(
    evidence: Evidence, before_path: object, after_path: object
) -> dict[str, object]:
    before = evidence.read(before_path)
    after = evidence.read(after_path)
    require(
        before.get("producer")
        == after.get("producer")
        == "serve.qualification.capture",
        "Historical or caller-declared identity cannot qualify a new run",
    )
    require(
        integer(before.get("schema_version"))
        == integer(after.get("schema_version"))
        == 1,
        "Unsupported serving capture schema",
    )
    require(
        before.get("producer_sha256")
        == after.get("producer_sha256")
        == digest(Path(__file__)),
        "Serving captures do not belong to this retained verifier producer",
    )
    identity = native_identity(before.get("identity"))
    require(
        identity == native_identity(after.get("identity")),
        "Serving identity differs before/after",
    )
    require(
        after.get("before_sha256") == digest(evidence.path(before_path)),
        "After capture is not bound to before capture",
    )
    require(
        integer(after.get("captured_unix_ns"))
        > integer(before.get("captured_unix_ns")),
        "Reversed or reused capture interval",
    )
    require(
        integer(after.get("native_exit_code")) == 0,
        "Native command did not complete successfully",
    )
    return identity


def proof_gate(
    evidence: Evidence, arm: dict[str, object], identity: dict[str, object]
) -> dict[str, object]:
    directory = evidence.path(arm.get("bend_directory"))
    plan = adapter.checked_plan(directory, 262144, 263168, 128)
    hashes = evidence.tree(directory)
    require(
        hashes == identity.get("bend_artifacts"),
        "Bend proof/toolchain closure differs from the actual candidate",
    )
    source = adapter.source_identity(directory)
    sources = mapping(source.get("sources"))
    toolchain = evidence.retain(directory.parent / "bend-toolchain.json")
    require(
        digest(toolchain) == identity.get("bend_toolchain_sha256")
        and document(toolchain) == identity.get("bend_toolchain"),
        "Bend toolchain raw provenance differs",
    )
    toolchain_identity(identity)
    for name in adapter.SOURCE_NAMES:
        require(
            sources.get(name) == digest(evidence.retain(ROOT / name)),
            f"Original Bend source changed: {name}",
        )
    return {
        "plan": plan,
        "proof_sha256": hashes.get("logs/proof.json"),
        "scope": adapter.SCOPE,
    }


def close(actual: object, expected: float, label: str) -> None:
    require(
        math.isclose(number(actual), expected, rel_tol=1e-12, abs_tol=1e-12),
        f"Unreconstructible {label}",
    )


def timing_row(value: object) -> dict[str, object]:
    row = mapping(value)
    require(
        row.get("schema_version") == 2
        and row.get("measurement_protocol") == decode.MEASUREMENT_PROTOCOL,
        "Counter schema1 and v2 are incomparable; new protocol2 boundaries are required",
    )
    start = integer(row.get("request_started_ns"))
    content = integer(row.get("first_content_or_reasoning_observed_ns"))
    first_ns = integer(row.get("first_positive_counter_observed_ns"))
    terminal = integer(row.get("terminal_usage_observed_ns"))
    done = integer(row.get("done_observed_ns"))
    require(
        0 < start <= content <= terminal <= done and start <= first_ns < terminal,
        "Reversed C1 stream boundaries",
    )
    prompt = integer(row.get("prompt_tokens"))
    completed = integer(row.get("completion_tokens"))
    first = integer(row.get("first_positive_completion_tokens"))
    require(
        prompt > 0 and 0 < first < completed <= decode.OUTPUT_TOKENS,
        "Invalid committed counter delta",
    )
    require(
        row.get("finish_reason") in ("stop", "length"),
        "Failed or incomplete stream finish",
    )
    if row.get("finish_reason") == "length":
        require(
            completed == decode.OUTPUT_TOKENS,
            "Length finish did not reach the frozen budget",
        )
    samples = [mapping(sample) for sample in sequence(row.get("counter_samples"))]
    require(len(samples) >= 2, "Missing raw continuous-usage observations")
    previous_ns, previous_count = start, 0
    positive: tuple[int, int] | None = None
    for index, sample in enumerate(samples):
        observed = integer(sample.get("observed_ns"))
        count = integer(sample.get("completion_tokens"))
        require(
            previous_ns <= observed <= terminal
            and previous_count <= count <= completed,
            "Counter observations decrease or leave their stream interval",
        )
        require(
            integer(sample.get("prompt_tokens")) == prompt, "Prompt counter changed"
        )
        require(
            sample.get("terminal") is (index == len(samples) - 1),
            "Missing or repeated terminal counter",
        )
        if count > 0 and positive is None:
            positive = observed, count
        previous_ns, previous_count = observed, count
    require(
        positive == (first_ns, first),
        "First positive counter does not match raw observations",
    )
    require(
        (previous_ns, previous_count) == (terminal, completed),
        "Terminal counter does not match raw observations",
    )
    window, elapsed, delta = terminal - first_ns, done - start, completed - first
    require(
        integer(row.get("counter_window_tokens")) == delta
        and integer(row.get("counter_window_ns")) == window
        and integer(row.get("elapsed_ns")) == elapsed,
        "Reported timing/count deltas disagree with boundaries",
    )
    rate, ttft = delta * 1e9 / window, (content - start) / 1e9
    close(row.get("committed_tok_s"), rate, "committed counter throughput")
    close(
        row.get("whole_request_tok_s"),
        completed * 1e9 / elapsed,
        "whole-request throughput",
    )
    close(row.get("ttft_s"), ttft, "TTFT")
    close(row.get("elapsed_seconds"), elapsed / 1e9, "request duration")
    return {
        "depth_target": integer(row.get("depth_target")),
        "repetition": integer(row.get("repetition")),
        "prompt_tokens": prompt,
        "completion_tokens": completed,
        "committed_tok_s": rate,
        "ttft_s": ttft,
        "counter_window_tokens": delta,
        "counter_window_ns": window,
        "ttft_ns": content - start,
    }


def report_artifacts(
    evidence: Evidence,
    root: Path,
    report: dict[str, object],
    identity: dict[str, object],
) -> set[str]:
    require(
        report.get("evidence_schema_version") == 1,
        "Missing new producer-bound raw artifacts",
    )
    observed = native_identity(report.get("identity"))
    require(
        observed == report.get("identity_after")
        and recipe_identity(observed) == recipe_identity(identity),
        "Report instance changed or its immutable recipe differs from the candidate",
    )
    require(
        captures(
            evidence,
            str(root / "identity-before.json"),
            str(root / "identity-after.json"),
        )
        == observed,
        "Raw before/after instance captures differ from report",
    )
    names: set[str] = set()
    for value in sequence(report.get("artifacts")):
        item = mapping(value)
        name = text(item.get("path"))
        relative = Path(name)
        require(
            not relative.is_absolute()
            and ".." not in relative.parts
            and name not in names,
            "Unsafe or duplicate raw artifact path",
        )
        path = evidence.retain(root / relative)
        require(
            path.is_relative_to(root.resolve())
            and path.stat().st_size == integer(item.get("size_bytes"))
            and digest(path) == item.get("sha256"),
            f"Raw artifact changed: {name}",
        )
        names.add(name)
    require(bool(names), "Empty raw artifact manifest")
    return names


def replay_tokenization(
    directory: Path, name: str, expected: dict[str, object]
) -> tuple[int, int, int]:
    """Check a retained successful API receipt, not a tokenizer attestation."""
    receipt = document(directory / name)
    require(
        receipt.get("method") == "POST"
        and receipt.get("path") == "/v1/tokenize"
        and integer(receipt.get("status")) == 200,
        "C1 tokenization receipt is not a successful request",
    )
    require(
        decode.canonical_bytes(mapping(receipt.get("request")))
        == decode.canonical_bytes(expected),
        "C1 tokenization receipt belongs to different text, messages, model or special-token settings",
    )
    response = mapping(receipt.get("response"))
    require("error" not in response, "C1 tokenization response contains an error")
    count = integer(response.get("count"))
    tokens = sequence(response.get("tokens"))
    require(
        0 < count == len(tokens) <= cache.MAX_TOKEN_IDS
        and all(0 <= integer(token) <= cache.MAX_TOKEN_ID for token in tokens),
        "C1 tokenization count/IDs disagree or contain invalid token IDs",
    )
    started, received = (
        integer(receipt.get("request_started_ns")),
        integer(receipt.get("response_received_ns")),
    )
    require(0 < started <= received, "C1 tokenization receipt has reversed boundaries")
    return count, started, received


def replay_stream(
    root: Path,
    row: dict[str, object],
    names: set[str],
    corpus: str,
    repetitions: int,
    captured_ns: int,
) -> None:
    request_path = text(row.get("request_path"))
    stream_path = text(row.get("raw_stream_path"))
    times_path = text(row.get("raw_timestamps_path"))
    require(
        {request_path, stream_path, times_path, text(row.get("power_path"))} <= names,
        "C1 row lacks hashed request/stream/timestamp/power artifacts",
    )
    request = document(root / request_path)
    require(
        digest(root / request_path) == row.get("request_body_sha256"),
        "C1 request SHA mismatch",
    )
    depth, repetition = integer(row.get("depth_target")), integer(row.get("repetition"))
    require(
        depth in decode.DEPTHS and 0 <= repetition < repetitions,
        "C1 row is outside the frozen matrix",
    )
    nonce = f"[measurement run {repetition + 1} of {repetitions} at depth {depth}]"
    require(
        row.get("nonce") == nonce, "C1 nonce differs from its declared depth/repetition"
    )
    prefix_chars = integer(row.get("corpus_prefix_chars"))
    require(
        0 <= prefix_chars <= len(corpus),
        "C1 corpus prefix leaves the frozen natural document",
    )
    content = nonce + "\n" + corpus[:prefix_chars] + "\n\n" + decode.INSTRUCTION
    expected = {
        "model": cache.MODEL,
        "messages": [{"role": "user", "content": content}],
        "max_tokens": decode.OUTPUT_TOKENS,
        "temperature": 0,
        "top_p": 1,
        "n": 1,
        "stream": True,
        "stream_options": {"include_usage": True, "continuous_usage_stats": True},
    }
    require(
        decode.canonical_bytes(request) == decode.canonical_bytes(expected),
        "C1 request is not the frozen nonce/corpus-prefix/instruction and generation contract",
    )
    directory = (root / request_path).parent
    require(
        {
            (directory / name).relative_to(root).as_posix()
            for name in (
                "response-status.json",
                "request-timing.json",
                "row.json",
                "content-tokenization.json",
                "chat-tokenization.json",
            )
        }
        <= names,
        "C1 raw boundary/row files are absent from the hashed artifact closure",
    )
    require(
        document(directory / "row.json") == row, "C1 persisted row differs from summary"
    )
    require(
        document(directory / "response-status.json").get("status") == 200,
        "C1 HTTP failure",
    )
    require(
        document(directory / "request-timing.json").get("request_started_ns")
        == row.get("request_started_ns"),
        "C1 raw request start differs",
    )
    raw_count, raw_start, raw_received = replay_tokenization(
        directory,
        "content-tokenization.json",
        {
            "model": cache.MODEL,
            "prompt": content,
            "add_special_tokens": False,
        },
    )
    chat_count, chat_start, chat_received = replay_tokenization(
        directory,
        "chat-tokenization.json",
        {
            "model": cache.MODEL,
            "messages": expected["messages"],
        },
    )
    require(
        abs(raw_count - depth) <= 2,
        "C1 raw-content tokenization does not bind the nominal depth",
    )
    require(
        integer(row.get("prompt_tokens")) == chat_count,
        "C1 measured prompt count differs from independent chat-message tokenization",
    )
    require(
        captured_ns
        <= raw_start
        <= raw_received
        <= chat_start
        <= chat_received
        <= integer(row.get("request_started_ns")),
        "C1 sizing/chat tokenization lies outside its identity capture or timed request exclusion",
    )
    data = (root / stream_path).read_bytes()
    offset = 0
    previous = integer(row.get("request_started_ns"))
    samples: list[dict[str, object]] = []
    first_content: int | None = None
    done: int | None = None
    finish: str | None = None
    terminal = False
    with (root / times_path).open("rb") as stream:
        for raw in stream:
            decoded: object = json.loads(raw)
            stamp = mapping(decoded)
            length, observed = (
                integer(stamp.get("length")),
                integer(stamp.get("observed_ns")),
            )
            require(
                integer(stamp.get("offset")) == offset
                and length > 0
                and observed >= previous,
                "C1 raw timestamp coverage/order is invalid",
            )
            line = data[offset : offset + length].decode("utf-8").strip()
            offset += length
            previous = observed
            require(
                offset <= len(data) and done is None,
                "Raw SSE extends beyond DONE or timestamp coverage",
            )
            if not line.startswith("data:"):
                continue
            payload = line[5:].strip()
            if payload == "[DONE]":
                require(terminal, "DONE preceded terminal usage")
                done = observed
                continue
            require(not terminal, "Raw SSE data after terminal usage")
            event_value: object = json.loads(payload)
            event = mapping(event_value)
            _ = canonical(event)
            require("error" not in event, "Raw SSE contains model error")
            choices = sequence(event.get("choices"))
            require(len(choices) <= 1, "Raw SSE is not single-choice C1")
            if choices:
                choice = mapping(choices[0])
                require(
                    integer(choice.get("index")) == 0, "Wrong streamed choice index"
                )
                delta_value = choice.get("delta")
                delta = {} if delta_value is None else mapping(delta_value)
                for name in ("content", "reasoning_content"):
                    require(
                        delta.get(name) is None or isinstance(delta[name], str),
                        "Malformed streamed content",
                    )
                if first_content is None and (
                    delta.get("content") or delta.get("reasoning_content")
                ):
                    first_content = observed
                if choice.get("finish_reason") is not None:
                    require(
                        finish is None
                        and choice["finish_reason"] in ("stop", "length"),
                        "Invalid stream finish",
                    )
                    finish = text(choice["finish_reason"])
            if event.get("usage") is not None:
                usage = mapping(event["usage"])
                terminal = not choices
                require(
                    not terminal or finish is not None,
                    "Terminal usage lacks successful finish",
                )
                samples.append({
                    "observed_ns": observed,
                    "prompt_tokens": integer(usage.get("prompt_tokens")),
                    "completion_tokens": integer(usage.get("completion_tokens")),
                    "terminal": terminal,
                })
            elif not choices:
                require(bool(mapping(event.get("sglext"))), "Empty stream event")
    require(
        offset == len(data)
        and done == row.get("done_observed_ns")
        and finish == row.get("finish_reason")
        and first_content == row.get("first_content_or_reasoning_observed_ns")
        and samples == row.get("counter_samples"),
        "Raw SSE/timestamps cannot reconstruct reported committed counters and boundaries",
    )


def timing_gate(
    evidence: Evidence, arm: dict[str, object], identity: dict[str, object]
) -> dict[str, object]:
    report = evidence.read(arm.get("decode_report"))
    require(
        report.get("classification") == "C1_DECODE_DEPTH_MATRIX",
        "Synthetic/unrecognized report is not native C1 model evidence",
    )
    require(
        report.get("schema_version") == 2
        and report.get("measurement_protocol") == decode.MEASUREMENT_PROTOCOL,
        "Only schema2 continuous-usage-counter-delta-v2 is timing evidence",
    )
    root = evidence.path(arm.get("decode_report")).parent
    names = report_artifacts(evidence, root, report, identity)
    workload = document(evidence.retain(root / "workload.json"))
    require(
        "workload.json" in names
        and digest(root / "workload.json") == report.get("workload_sha256"),
        "C1 workload is missing from the raw artifact closure or its digest differs",
    )
    require(
        integer(workload.get("schema_version")) == decode.WORKLOAD_SCHEMA_VERSION,
        "C1 workload schema2 with content and chat-tokenization receipts is required",
    )
    require(
        integer(workload.get("concurrency")) == 1
        and workload.get("order") == "depth_then_repetition",
        "C1 concurrency or canonical matrix order changed",
    )
    require(
        [integer(depth) for depth in sequence(workload.get("depths"))]
        == list(decode.DEPTHS),
        "C1 declared depths differ from the source-frozen required matrix",
    )
    repetitions = integer(workload.get("repetitions"))
    require(repetitions > 0, "C1 repetition count must be a positive exact integer")
    require(
        workload.get("nonce_template")
        == "[measurement run {repetition + 1} of {repetitions} at depth {depth}]",
        "C1 frozen nonce template changed",
    )
    require(
        decode.canonical_bytes(workload.get("sampling"))
        == decode.canonical_bytes({
            "temperature": 0,
            "top_p": 1,
            "n": 1,
            "max_tokens": decode.OUTPUT_TOKENS,
            "ignore_eos": False,
        })
        and workload.get("cache")
        == {
            "policy": "deterministic_per_row_nonce_no_flush_no_warmup",
            "cache_salt": None,
        },
        "C1 frozen sampling/cache workload changed",
    )
    source_names = (
        "bench/decode.py",
        "bench/cache.py",
        "bench/power.py",
        "bench/throughput-prompts.jsonl",
    )
    sources = [mapping(value) for value in sequence(workload.get("sources"))]
    require(
        [source.get("path") for source in sources]
        == [f"sources/{name}" for name in source_names],
        "C1 frozen producer/corpus source closure is missing, duplicated or reordered",
    )
    for name, source in zip(source_names, sources, strict=True):
        relative = f"sources/{name}"
        require(
            relative in names,
            "C1 frozen source is absent from the raw artifact closure",
        )
        retained = root / relative
        require(
            digest(retained)
            == source.get("sha256")
            == digest(evidence.retain(ROOT / name))
            and retained.stat().st_size == integer(source.get("size_bytes")),
            f"C1 frozen source differs from the admitted producer/corpus: {name}",
        )
    corpus = decode.corpus_document(root / "sources/bench/throughput-prompts.jsonl")
    raw_rows = [mapping(row) for row in sequence(report.get("rows"))]
    require(
        len(raw_rows) == len(decode.DEPTHS) * repetitions
        and all(
            (integer(row.get("depth_target")), integer(row.get("repetition")))
            == (decode.DEPTHS[index // repetitions], index % repetitions)
            for index, row in enumerate(raw_rows)
        ),
        "C1 depth/repetition rows missing, skipped, duplicated or reordered",
    )
    rows: list[dict[str, object]] = []
    before, after = (
        document(root / "identity-before.json"),
        document(root / "identity-after.json"),
    )
    for row in raw_rows:
        replay_stream(
            root,
            row,
            names,
            corpus,
            repetitions,
            integer(before.get("captured_monotonic_ns")),
        )
        require(
            integer(before.get("captured_monotonic_ns"))
            <= integer(row.get("request_started_ns"))
            < integer(row.get("done_observed_ns"))
            <= integer(after.get("captured_monotonic_ns")),
            "C1 row lies outside its actual producer identity capture",
        )
        observed = timing_row(row)
        observed["request_body_sha256"] = row["request_body_sha256"]
        rows.append(observed)
    close(
        report.get("committed_tok_s_min"),
        min(number(row["committed_tok_s"]) for row in rows),
        "minimum rate",
    )
    close(
        report.get("committed_tok_s_max"),
        max(number(row["committed_tok_s"]) for row in rows),
        "maximum rate",
    )
    return {
        "rows": rows,
        "protocol": decode.MEASUREMENT_PROTOCOL,
        "workload_sha256": digest(root / "workload.json"),
    }


def capacity_gate(
    evidence: Evidence, arm: dict[str, object], identity: dict[str, object]
) -> dict[str, object]:
    from bench import capacity

    directory = evidence.path(arm.get("capacity_directory"))
    result = document(evidence.retain(directory / "result.json"))
    require(
        result.get("schema_version") == capacity.SCHEMA_VERSION,
        "Seeded capacity with retained native reset evidence is required",
    )
    names = report_artifacts(evidence, directory, result, identity)
    require(
        {
            "plan.json",
            "request.json",
            "input-ids.json",
            "fixture.json",
            "generation.json",
            "cache-reset.json",
        }
        <= names,
        "Capacity raw artifacts missing",
    )
    plan, request, generation = (
        document(directory / name)
        for name in ("plan.json", "request.json", "generation.json")
    )
    require(
        plan.get("schema_version") == capacity.SCHEMA_VERSION,
        "Unsupported capacity plan",
    )
    fixture, reset = (
        document(directory / name) for name in ("fixture.json", "cache-reset.json")
    )
    seed = integer(plan.get("seed"))
    nonce, salt = capacity.deterministic_parameters(seed)
    require(
        plan.get("workload_protocol")
        == fixture.get("workload_protocol")
        == result.get("workload_protocol")
        == capacity.WORKLOAD_PROTOCOL
        and fixture.get("seed") == result.get("seed") == seed
        and plan.get("fixture_nonce")
        == fixture.get("fixture_nonce")
        == result.get("fixture_nonce")
        == nonce
        and plan.get("cache_salt") == result.get("cache_salt") == salt,
        "Capacity seed, fixture nonce or cache namespace is inconsistent",
    )
    require(
        digest(directory / "fixture.json")
        == plan.get("fixture_sha256")
        == result.get("fixture_sha256"),
        "Capacity fixture hash differs",
    )
    source_names = ("bench/capacity.py", "bench/cache.py", "bench/decode.py")
    sources = [mapping(value) for value in sequence(result.get("sources"))]
    require(
        [source.get("path") for source in sources]
        == [f"sources/{name}" for name in source_names],
        "Capacity producer source closure is missing, duplicated or reordered",
    )
    for name, source in zip(source_names, sources, strict=True):
        relative = f"sources/{name}"
        require(
            relative in names
            and digest(directory / relative)
            == source.get("sha256")
            == digest(evidence.retain(ROOT / name))
            and (directory / relative).stat().st_size
            == integer(source.get("size_bytes")),
            f"Capacity frozen source differs from the admitted producer: {name}",
        )
    ids_value: object = json.loads((directory / "input-ids.json").read_bytes())
    ids = cache.token_ids(ids_value)
    seed_ids, instruction_ids = (
        cache.token_ids(fixture.get("seed_ids")),
        cache.token_ids(fixture.get("instruction_ids")),
    )
    require(
        len(seed_ids) > 0
        and 0 < len(instruction_ids) < len(ids)
        and fixture.get("synthetic_text") == cache.fixture_text(nonce)
        and fixture.get("instruction") == capacity.INSTRUCTION,
        "Capacity fixture or instruction changed",
    )
    ledger_count = len(ids) - len(instruction_ids)
    require(
        fixture.get("input_ids") == ids
        and ids
        == (seed_ids * ((ledger_count + len(seed_ids) - 1) // len(seed_ids)))[
            :ledger_count
        ]
        + instruction_ids
        and request == capacity.generation_request(ids, salt),
        "Capacity actual workload differs from its deterministic fixture",
    )
    require(
        len(ids) + 128 + 2 == integer(plan.get("total_budget_tokens")) == 262144
        and request.get("input_ids") == ids
        and plan.get("input_tokens") == len(ids),
        "Capacity probe is not near-native exact input",
    )
    require(
        digest(directory / "input-ids.json")
        == plan.get("input_ids_sha256")
        == result.get("input_ids_sha256")
        and digest(directory / "request.json")
        == plan.get("request_body_sha256")
        == generation.get("request_body_sha256")
        == result.get("request_body_sha256"),
        "Capacity request/input hashes differ",
    )
    for key in ("input_ids_sha256", "request_body_sha256"):
        require(
            plan.get("expected_" + key) is None
            or plan.get("expected_" + key) == plan.get(key),
            "Capacity supplied workload hash is inconsistent",
        )
    require(
        plan.get("requested_output_tokens") == 128
        and plan.get("engine_overhead_tokens") == 2,
        "Capacity fixed output/reserve budget changed",
    )
    prompt, completed = (
        integer(generation.get("prompt_tokens")),
        integer(generation.get("completion_tokens")),
    )
    require(
        0 <= prompt - len(ids) <= 2
        and completed == 128
        and 262142 <= prompt + completed <= 262144,
        "Capacity completion counts do not reach the real near-native boundary",
    )
    require(
        request.get("sampling_params")
        == {"temperature": 0, "ignore_eos": True, "max_new_tokens": 128}
        and generation.get("cached_tokens") == generation.get("num_retractions") == 0
        and mapping(generation.get("finish_reason")).get("type") == "length",
        "Capacity request failed, reused cache or retracted",
    )
    outputs = cache.token_ids(generation.get("output_ids"))
    require(
        len(outputs) == completed and bool(text(generation.get("output_text")).strip()),
        "Capacity output missing",
    )
    operations = sorted(directory.glob("http-*/operation.json"))
    expected_operations = (
        ("GET", "/v1/models"),
        ("POST", "/v1/tokenize"),
        ("POST", "/v1/tokenize"),
        ("GET", capacity.FLUSH_PATH),
        ("POST", "/generate"),
    )
    require(
        len(operations) == len(expected_operations),
        "Capacity requires exactly one ordered model/fixture/instruction/reset/generate sequence",
    )
    before, after = (
        document(directory / "identity-before.json"),
        document(directory / "identity-after.json"),
    )
    previous_finished = integer(before.get("captured_monotonic_ns"))
    responses: list[dict[str, object]] = []
    requests: list[dict[str, object] | None] = []
    for operation, (method, path) in zip(operations, expected_operations, strict=True):
        require(
            document(operation) == {"method": method, "path": path},
            "Capacity HTTP sequence changed",
        )
        required = [
            "operation.json",
            "status.json",
            "response.raw",
            "response.json",
            "timing.json",
        ]
        if method == "POST":
            required.append("request.json")
        require(
            {
                (operation.parent / name).relative_to(directory).as_posix()
                for name in required
            }
            <= names,
            "Capacity raw HTTP files are absent from the hashed artifact closure",
        )
        require(
            document(operation.parent / "status.json").get("status") == 200,
            "Capacity raw HTTP failure",
        )
        response = document(operation.parent / "response.json")
        if path == capacity.FLUSH_PATH:
            require(
                (operation.parent / "response.raw").read_bytes()
                == capacity.FLUSH_RESPONSE
                and response == {"message": capacity.FLUSH_RESPONSE.decode("ascii")},
                "Capacity reset lacks the pinned successful response",
            )
        else:
            require(
                document(operation.parent / "response.raw") == response,
                "Raw capacity response changed",
            )
        timing = document(operation.parent / "timing.json")
        require(
            previous_finished
            <= integer(timing.get("request_started_ns"))
            < integer(timing.get("response_finished_ns"))
            <= integer(after.get("captured_monotonic_ns")),
            "Capacity HTTP sequence overlaps, is reordered or lies outside its producer capture",
        )
        previous_finished = integer(timing.get("response_finished_ns"))
        requests.append(
            document(operation.parent / "request.json") if method == "POST" else None
        )
        responses.append(response)
    models = sequence(responses[0].get("data"))
    require(
        len(models) == 1 and mapping(models[0]).get("id") == cache.MODEL,
        "Capacity tokenizer model identity changed",
    )
    for index, prompt_text, tokens in (
        (1, fixture["synthetic_text"], seed_ids),
        (2, capacity.INSTRUCTION, instruction_ids),
    ):
        require(
            requests[index]
            == {
                "model": cache.MODEL,
                "prompt": prompt_text,
                "add_special_tokens": False,
            }
            and cache.token_ids(responses[index].get("tokens")) == tokens
            and integer(responses[index].get("count")) == len(tokens),
            "Capacity fixture IDs differ from their actual tokenizer receipts",
        )
    require(
        reset.get("schema_version") == 1
        and reset.get("policy") == "owned-native-flush-before-generate"
        and reset.get("owned_container_id")
        == mapping(result.get("identity")).get("container_id")
        and reset.get("identity_before_sha256")
        == digest(directory / "identity-before.json")
        and reset.get("response") == responses[3]
        and reset.get("response_sha256")
        == hashlib.sha256(capacity.FLUSH_RESPONSE).hexdigest()
        and digest(directory / "cache-reset.json") == result.get("cache_reset_sha256"),
        "Capacity cache reset is not bound to the owned admitted native instance",
    )
    require(
        requests[4] == request
        and digest(operations[4].parent / "request.json")
        == result.get("request_body_sha256"),
        "Raw capacity request differs",
    )
    response = responses[4]
    meta = mapping(response.get("meta_info"))
    require(
        cache.token_ids(response.get("output_ids")) == outputs
        and response.get("text") == generation.get("output_text"),
        "Raw capacity response differs from reported output",
    )
    for key in (
        "prompt_tokens",
        "completion_tokens",
        "cached_tokens",
        "num_retractions",
        "finish_reason",
    ):
        require(
            meta.get(key) == generation.get(key),
            f"Raw capacity response differs: {key}",
        )
    require(
        cache.logprobs(
            meta.get("output_token_logprobs"), outputs, allow_initial_null=False
        )
        == generation.get("logprobs"),
        "Capacity finite aligned logprobs differ from raw output",
    )
    require(
        all(result.get(key) == value for key, value in generation.items())
        and result.get("status") == "request_completed",
        "Capacity summary differs from real generation",
    )
    require(
        integer(generation.get("submitted_input_tokens")) == len(ids)
        and integer(generation.get("backend_prompt_overhead_tokens"))
        == prompt - len(ids)
        and integer(result.get("actual_total_tokens")) == prompt + completed
        and integer(result.get("native_context_tokens")) == 262144
        and result.get("near_native_completed") is True
        and result.get("near_native_rejection_reason") is None,
        "Capacity derived counts/status contradict raw completion",
    )
    close(
        result.get("native_coverage_fraction"),
        (prompt + completed) / 262144,
        "native capacity coverage",
    )
    return {
        "prompt_tokens": prompt,
        "completion_tokens": completed,
        "actual_total_tokens": prompt + completed,
        "workload_protocol": capacity.WORKLOAD_PROTOCOL,
        "seed": seed,
        "fixture_sha256": result["fixture_sha256"],
        "input_ids_sha256": result["input_ids_sha256"],
        "request_body_sha256": result["request_body_sha256"],
        "scope": "one completed near-native allocation/generation request; not sustained concurrency, cache correctness or model quality",
    }


def numerical_gate(
    evidence: Evidence, arm: dict[str, object], identity: dict[str, object]
) -> dict[str, object]:
    from bench.numerical import verify_report

    reports = sequence(arm.get("numerical_reports"))
    require(
        bool(reports),
        "Missing candidate-bound numerical reports; run bench.numerical on the exact image/components",
    )
    required = {
        "kvarn_attention",
        "kvarn_storage",
        "packed_embedding",
        "dflash_commit",
        "dflash_sampler",
    }
    if "QWEN_MARLIN_ACTIVATION_BITS=8" in sequence(identity.get("container_env", [])):
        required.add("marlin_a8")
    coverage: set[str] = set()
    observations: list[dict[str, object]] = []
    for value in reports:
        path = evidence.retain(evidence.path(value))
        replay = verify_report(path, identity)
        coverage.update(text(item) for item in sequence(replay.get("coverage")))
        observations.append(replay)
        evidence.tree(path.parent)
    require(
        required <= coverage,
        "Missing required numerical coverage: "
        + ", ".join(sorted(required - coverage)),
    )
    return {
        "coverage": sorted(coverage),
        "reports": observations,
        "scope": "replayed standalone numerical components for the exact frozen greedy recipe; model quality is a separate Prime gate",
    }


def energy_gate(
    evidence: Evidence, directory: Path, environment: str, identity: dict[str, object]
) -> dict[str, object]:
    measurement = directory / "measurement"
    recorded = document(evidence.retain(measurement / "efficiency.json"))
    raw = document(evidence.retain(measurement / "power-samples.json"))
    details_path = evidence.retain(measurement / "task-intervals.json")
    hardware = mapping(identity.get("hardware"))
    require(
        text(raw.get("gpu")).lower()
        in {
            "0",
            text(hardware.get("uuid")).lower(),
            text(hardware.get("pci_bus_id")).lower(),
        },
        "Measured board does not match captured serving GPU",
    )
    require(
        raw.get("schema_version") == recorded.get("schema_version") == 1,
        "Unsupported measurement sidecar",
    )
    require(
        recorded.get("native_exit_code") == 0
        and recorded.get("interrupted_signal") is None
        and recorded.get("launch_failure") is None,
        "Failed/interrupted measurement run",
    )
    power = mapping(recorded.get("power"))
    sampler = PowerSampler(
        text(raw.get("gpu")), number(power.get("sampling_interval_seconds"))
    )
    for value in sequence(raw.get("samples")):
        sample = mapping(value)
        watts = sample.get("watts")
        require(
            watts is not None and sample.get("error") is None,
            "Failed or missing board-power observation",
        )
        sampler.samples.append(
            PowerSample(
                integer(sample.get("monotonic_ns")),
                integer(sample.get("unix_time_ns")),
                integer(sample.get("query_started_ns")),
                integer(sample.get("query_finished_ns")),
                number(watts),
            )
        )
    start = {key: integer(value) for key, value in mapping(raw.get("start")).items()}
    end = {key: integer(value) for key, value in mapping(raw.get("end")).items()}
    sampler.started, sampler.ended = start, end
    require(power.get("limit_reached") is None, "Power collection limit reached")
    reconstructed, details = efficiency_report(
        directory, environment, sampler, start, end, 0, None
    )
    require(
        all(recorded.get(key) == value for key, value in reconstructed.items()),
        "Measurement summary differs from raw traces/power reconstruction",
    )
    require(
        json.loads(details_path.read_bytes()) == details,
        "Task interval sidecar differs from reconstruction",
    )
    require(
        reconstructed.get("success_denominator_complete") is True
        and reconstructed.get("power_measurement_status") == "complete",
        "Energy requires complete board coverage and the complete native success denominator",
    )
    successes = integer(reconstructed.get("successful_task_rollouts"))
    require(successes >= 0, "Negative native success count")
    if successes == 0:
        require(
            reconstructed.get("energy_ratio_available") is False
            and reconstructed.get("time_ratio_available") is False
            and reconstructed.get("joules_per_successful_task_rollout") is None
            and reconstructed.get("seconds_per_successful_task_rollout") is None,
            "Zero successes must retain undefined cost ratios, not zero cost",
        )
    else:
        require(
            reconstructed.get("energy_ratio_available") is True
            and reconstructed.get("time_ratio_available") is True,
            "Complete positive-success measurement lacks cost ratios",
        )
    return {
        key: reconstructed[key]
        for key in (
            "successful_task_rollouts",
            "total_wall_seconds",
            "total_joules",
            "seconds_per_successful_task_rollout",
            "joules_per_successful_task_rollout",
            "ratio_unavailable_reasons",
        )
    }


def evaluation_gate(
    evidence: Evidence,
    directory: Path,
    identity: dict[str, object],
    profile: str,
    environment: str,
) -> dict[str, object]:
    require(
        environment
        in (("i3-logic",) if profile == "diverse" else profile_environments(profile)),
        "Environment is outside the explicit evaluation profile",
    )
    provenance = directory.parent / "provenance"
    before_path = provenance / f"{environment}.serving-before.json"
    after_path = provenance / f"{environment}.serving-after.json"
    observed = captures(evidence, str(before_path), str(after_path))
    require(
        recipe_identity(observed) == recipe_identity(identity),
        f"{environment}: immutable serving recipe mismatch",
    )
    before, after = document(before_path), document(after_path)
    for name in (
        "prime-envs.lock",
        "datasets.lock",
        "uv.lock",
        "pyproject.toml",
        "configs/local.toml",
    ):
        copied = provenance / ("local.toml" if name == "configs/local.toml" else name)
        require(
            digest(evidence.retain(copied))
            == digest(evidence.retain(ROOT / "eval" / name)),
            f"{environment}: frozen evaluator/dataset/config pins differ: {name}",
        )
    frozen = document(
        evidence.retain(provenance / f"{environment}.evaluation-inputs-before.json")
    )
    require(
        frozen
        == document(
            evidence.retain(provenance / f"{environment}.evaluation-inputs-after.json")
        )
        and frozen.get("profile") == profile
        and frozen.get("environment") == environment
        and frozen.get("producer") == "serve.qualification.freeze-eval",
        f"{environment}: missing, mismatched or changed frozen inputs",
    )
    for path, expected in mapping(frozen.get("files_sha256")).items():
        require(
            digest(evidence.retain(Path(path))) == expected,
            f"{environment}: frozen input changed: {path}",
        )
    require(
        frozen == frozen_inputs(profile, environment, provenance),
        f"{environment}: frozen source/config/data closure differs",
    )
    evidence.tree(provenance / "runtime")
    episodes, trace_evidence, c1 = load_episodes(directory)
    require(
        not trace_evidence["failures"] and c1,
        f"{environment}: malformed, absent, or non-C1 native traces",
    )
    paths = list(directory.glob("*/traces.jsonl"))
    trace_path = evidence.retain(paths[0])
    config_path = evidence.retain(trace_path.parent / "configs/resolved/eval.json")
    config = document(config_path)
    require(config.get("model") == "qwen3.8-27b", f"{environment}: wrong model")
    taskset = mapping(mapping(config.get("env")).get("taskset"))
    require(taskset.get("id") == environment, f"{environment}: wrong upstream taskset")
    with (ROOT / "eval/configs/local.toml").open("rb") as stream:
        local: object = tomllib.load(stream)
    expected_sampling = mapping(mapping(local)["sampling"])
    if profile == "diverse":
        expected_sampling["max_tokens"] = 8192
    for key, expected in expected_sampling.items():
        require(
            mapping(config.get("sampling")).get(key) == expected,
            f"{environment}: changed sampling or output budget",
        )
    with (ROOT / "eval/configs" / profile / f"{environment}.toml").open("rb") as stream:
        profile_value: object = tomllib.load(stream)
    profile_config = mapping(profile_value)
    for key in ("num_tasks", "num_rollouts", "max_concurrent", "shuffle"):
        if key in profile_config:
            require(
                config.get(key) == profile_config[key],
                f"{environment}: changed frozen task/rollout selection",
            )
    require(
        config.get("num_tasks") == profile_config.get("num_tasks"),
        f"{environment}: changed frozen task count",
    )
    config.pop("run", None)
    config.pop("output_dir", None)
    if profile in ("tiny", "diverse"):
        selection = mapping(frozen.get("selection"))
        require(
            config == mapping(selection.get("resolved_config")),
            f"{profile}: resolved native taskset, harness, reasoning, budget or runtime differs from the frozen plan",
        )
    tasks: list[dict[str, object]] = []
    reward_components: list[object] = []
    with trace_path.open("rb") as stream:
        for raw in stream:
            episode_value: object = json.loads(raw)
            episode = mapping(episode_value)
            task = mapping(episode.get("task"))
            require(
                bool(task.get("key")) and bool(task.get("hash")),
                f"{environment}: missing native task identity",
            )
            require(
                task.get("hash")
                == hashlib.sha256(
                    json.dumps(task.get("data"), sort_keys=True).encode()
                ).hexdigest(),
                f"{environment}: task content hash mismatch",
            )
            tasks.append({key: task[key] for key in ("key", "hash", "type")})
            for trace_value in sequence(episode.get("traces")):
                trace = mapping(trace_value)
                require(trace.get("ok") is True, f"{environment}: failed trace")
                build = mapping(trace.get("verifiers"))
                require(
                    build.get("commit") == "ef47b2e96284a00bdcfc1012b9624b0c41ee6a0e",
                    f"{environment}: unpinned native scorer build",
                )
                reward_components.append(trace.get("rewards"))
    logs = list(trace_path.parent.glob("logs/attempt_*/eval.log"))
    require(len(logs) == 1, f"{environment}: missing unique native attempt log")
    log = evidence.retain(logs[0]).read_text(encoding="utf-8")
    planned = list(
        re.finditer(r"running ([0-9]+)x([0-9]+) rollouts on qwen3\.8-27b", log)
    )
    require(
        len(planned) == 1,
        f"{environment}: missing unambiguous upstream task/rollout plan",
    )
    planned_tasks, planned_rollouts = int(planned[0].group(1)), int(planned[0].group(2))
    counts = Counter(text(task["hash"]) for task in tasks)
    require(
        planned_tasks == len(counts)
        and planned_rollouts == integer(config.get("num_rollouts"))
        and len(episodes) == planned_tasks * planned_rollouts
        and all(value == planned_rollouts for value in counts.values()),
        f"{environment}: missing/skipped/duplicated task rollouts relative to upstream run plan",
    )
    if profile == "tiny":
        require(
            planned_tasks == 3
            and planned_rollouts == 1
            and len(episodes) == 3
            and tasks == sequence(mapping(frozen.get("selection")).get("tasks")),
            "Tiny requires the exact preselected seed-zero three-task, one-rollout native multiset",
        )
    if profile == "diverse":
        require(
            planned_tasks == 1
            and planned_rollouts == 1
            and len(episodes) == 1
            and tasks == sequence(mapping(frozen.get("selection")).get("tasks")),
            "Diverse logic requires the exact preselected first eligible native task and one rollout",
        )
    for episode in episodes:
        require(
            episode.operational_ok
            and episode.recorded_error_count == 0
            and episode.weighted_reward is not None
            and episode.trace_count == 1,
            f"{environment}: failed, skipped, multi-trace or unscored episode",
        )
        require(
            episode.start_unix_ns is not None
            and episode.end_unix_ns is not None
            and integer(before.get("captured_unix_ns"))
            <= episode.start_unix_ns
            <= episode.end_unix_ns
            <= integer(after.get("captured_unix_ns")),
            f"{environment}: trace does not lie inside its original serving capture",
        )
    rewards = [number(episode.weighted_reward) for episode in episodes]
    return {
        "config_sha256": hashlib.sha256(canonical(config)).hexdigest(),
        "tasks": tasks,
        "rollouts": len(episodes),
        "profile": profile,
        "scope": "sampled_math_only_not_full_qualification"
        if profile == "tiny"
        else "logic_sentinel_only_not_full_qualification"
        if profile == "diverse"
        else "core_suite",
        "weighted_reward_mean": math.fsum(rewards) / len(rewards),
        "reward_components": reward_components,
        "truncated_rollouts": sum(episode.truncated for episode in episodes),
    }


def objective_order(
    baseline: Fraction, candidate: Fraction, *, minimize: bool = False
) -> adapter.ObjectiveOrder:
    """Compare exact recorded rationals, not rounded display rates or a fitted epsilon."""
    if candidate > baseline:
        return "worse" if minimize else "better"
    if candidate < baseline:
        return "better" if minimize else "worse"
    return "same"


def exact_ratio(value: Fraction) -> dict[str, int]:
    """Keep exact observation arithmetic in the decision record."""
    return {"numerator": value.numerator, "denominator": value.denominator}


def compare_observations(
    baseline: dict[str, object],
    candidate: dict[str, object],
    policy: adapter.ObjectivePolicy,
    *,
    profile: str = "full",
) -> dict[str, object]:
    """Apply compiled Bend policy to already-verified, paired native observations."""
    environments = profile_environments(profile)
    for arm in (baseline, candidate):
        for name in (
            "bend_proof",
            "timing_validity",
            *("quality:" + environment for environment in environments),
        ):
            require(
                mapping(arm[name]).get("status") == "verified",
                "Comparable proved policy, native timing and per-environment quality evidence is incomplete",
            )
    orders: list[tuple[adapter.ObjectiveFamily, adapter.ObjectiveOrder]] = []
    axes: dict[str, object] = {}
    quality_preserved = True
    for environment in environments:
        left = mapping(mapping(baseline["quality:" + environment])["observations"])
        right = mapping(mapping(candidate["quality:" + environment])["observations"])
        require(
            left["config_sha256"] == right["config_sha256"]
            and left["tasks"] == right["tasks"],
            f"{environment}: changed workload/config/task IDs/sampling/budgets",
        )
        before, after = (
            Fraction(number(left["weighted_reward_mean"])),
            Fraction(number(right["weighted_reward_mean"])),
        )
        order = objective_order(before, after)
        orders.append(("quality", order))
        quality_preserved = quality_preserved and order != "worse"
        axes["quality:" + environment] = {
            "family": "quality",
            "role": "objective",
            "direction": "maximize",
            "baseline": exact_ratio(before),
            "candidate": exact_ratio(after),
            "order": order,
        }
    left_timing = mapping(mapping(baseline["timing_validity"])["observations"])
    right_timing = mapping(mapping(candidate["timing_validity"])["observations"])
    require(
        left_timing["workload_sha256"] == right_timing["workload_sha256"],
        "C1 workload/config/source/sampling/cache policy differs",
    )
    left_rows, right_rows = (
        sequence(left_timing["rows"]),
        sequence(right_timing["rows"]),
    )
    require(
        len(left_rows) == len(right_rows) and len(left_rows) > 0,
        "C1 paired rows absent or counts differ",
    )
    # Fresh per-depth totals: committed increments, interval ns, TTFT ns, repetitions.
    left_totals = {depth: [0, 0, 0, 0] for depth in decode.DEPTHS}
    right_totals = {depth: [0, 0, 0, 0] for depth in decode.DEPTHS}
    for left_value, right_value in zip(left_rows, right_rows, strict=True):
        left, right = mapping(left_value), mapping(right_value)
        for key in (
            "depth_target",
            "repetition",
            "prompt_tokens",
            "completion_tokens",
            "request_body_sha256",
        ):
            require(
                left[key] == right[key], "C1 workloads/output lengths are not paired"
            )
        depth = integer(left["depth_target"])
        require(depth in decode.DEPTHS, "Unrecognized frozen C1 depth")
        for row, totals in ((left, left_totals), (right, right_totals)):
            count = integer(row["counter_window_tokens"])
            window = integer(row["counter_window_ns"])
            ttft = integer(row["ttft_ns"])
            require(
                count > 0 and window > 0 and ttft >= 0,
                "Invalid exact C1 aggregation inputs",
            )
            values = totals[depth]
            values[0] += count
            values[1] += window
            values[2] += ttft
            values[3] += 1
    for depth in decode.DEPTHS:
        left, right = left_totals[depth], right_totals[depth]
        require(left[3] == right[3] and left[3] > 0, "Missing or unpaired frozen depth")
        before_rate, after_rate = (
            Fraction(left[0] * 1_000_000_000, left[1]),
            Fraction(right[0] * 1_000_000_000, right[1]),
        )
        before_ttft, after_ttft = (
            Fraction(left[2], left[3] * 1_000_000_000),
            Fraction(right[2], right[3] * 1_000_000_000),
        )
        rate_order = objective_order(before_rate, after_rate)
        ttft_order = objective_order(before_ttft, after_ttft, minimize=True)
        orders.extend((("throughput", rate_order), ("first_token", ttft_order)))
        axes[f"committed_rate:{depth}"] = {
            "family": "throughput",
            "role": "objective",
            "direction": "maximize",
            "unit": "tokens_per_second",
            "aggregation": "sum_committed_increments_over_sum_interval_ns",
            "baseline": exact_ratio(before_rate),
            "candidate": exact_ratio(after_rate),
            "order": rate_order,
        }
        axes[f"ttft:{depth}"] = {
            "family": "first_token",
            "role": "objective",
            "direction": "minimize",
            "unit": "seconds",
            "aggregation": "arithmetic_mean_first_content_or_reasoning_latency",
            "baseline": exact_ratio(before_ttft),
            "candidate": exact_ratio(after_ttft),
            "order": ttft_order,
        }
    for environment in environments:
        left_energy, right_energy = (
            mapping(baseline["energy:" + environment]),
            mapping(candidate["energy:" + environment]),
        )
        before_energy = after_energy = None
        if left_energy.get("status") == "verified":
            value = mapping(left_energy["observations"])[
                "joules_per_successful_task_rollout"
            ]
            if value is not None:
                before_energy = Fraction(number(value))
        if right_energy.get("status") == "verified":
            value = mapping(right_energy["observations"])[
                "joules_per_successful_task_rollout"
            ]
            if value is not None:
                after_energy = Fraction(number(value))
        energy_order: adapter.ObjectiveOrder = "missing"
        if before_energy is not None and after_energy is not None:
            energy_order = objective_order(before_energy, after_energy, minimize=True)
        orders.append(("energy", energy_order))
        axes["board_joules_per_success:" + environment] = {
            "family": "energy",
            "role": "reported",
            "direction": "minimize",
            "baseline": None if before_energy is None else exact_ratio(before_energy),
            "candidate": None if after_energy is None else exact_ratio(after_energy),
            "order": energy_order,
        }
    relation = policy.classify(orders)
    return {
        "axes": axes,
        "relation": relation,
        "dominates": relation == "dominates",
        "quality_preserved": quality_preserved,
        "timing_valid": True,
        "policy": "compiled_bend_goal_indexed_product_order_v1",
        "claim_scope": "Exact relation of recorded estimates; not statistical confidence or global optimality",
    }


def gate(call: Callable[[], dict[str, object]]) -> dict[str, object]:
    try:
        return {"status": "verified", "observations": call()}
    except (OSError, ValueError, KeyError, TypeError, OverflowError) as error:
        return {"status": "rejected", "reason": str(error)}


def qualify(manifest_path: Path) -> dict[str, object]:
    evidence = Evidence(manifest_path)
    manifest = document(evidence.retain(manifest_path))
    require(
        set(manifest) == {"schema_version", "profile", "baseline", "candidate"}
        and integer(manifest.get("schema_version")) == 1,
        "Manifest requires schema_version1, profile, baseline and candidate only",
    )
    profile = text(manifest.get("profile"))
    environments = profile_environments(profile)
    for name in (
        "serve/qualification.py",
        "bench/decode.py",
        "bench/cache.py",
        "bench/power.py",
        "eval/measure.py",
        "bend/adapter.py",
        "bend/build_toolchain.py",
        "bench/numerical.py",
    ):
        _ = evidence.retain(ROOT / name)
    arms: dict[str, object] = {}
    for name in ("baseline", "candidate"):
        arm = mapping(manifest.get(name))
        require(
            set(arm)
            == {
                "identity_before",
                "identity_after",
                "bend_directory",
                "decode_report",
                "capacity_directory",
                "numerical_reports",
                "evaluations",
            },
            f"{name}: expected explicit capture, Bend, C1, capacity, numerical and per-environment evaluation paths",
        )
        identity_result = gate(
            lambda arm=arm: captures(
                evidence, arm.get("identity_before"), arm.get("identity_after")
            )
        )
        identity = mapping(identity_result.get("observations", {}))
        gates: dict[str, object] = {"identity": identity_result}
        for label, function in (
            ("bend_proof", proof_gate),
            ("timing_validity", timing_gate),
            ("capacity", capacity_gate),
            ("numerical", numerical_gate),
        ):
            gates[label] = gate(
                lambda function=function, arm=arm, identity=identity: function(
                    evidence, arm, identity
                )
            )
        evaluations = mapping(arm.get("evaluations"))
        require(
            set(evaluations) == set(environments),
            f"{profile}: exact frozen environments required: {', '.join(environments)}",
        )
        for environment in environments:
            gates["quality:" + environment] = gate(
                lambda environment=environment, identity=identity, evaluations=evaluations: (
                    evaluation_gate(
                        evidence,
                        evidence.path(evaluations[environment]),
                        identity,
                        profile,
                        environment,
                    )
                )
            )
            gates["energy:" + environment] = gate(
                lambda environment=environment, evaluations=evaluations, identity=identity: (
                    energy_gate(
                        evidence,
                        evidence.path(evaluations[environment]),
                        environment,
                        identity,
                    )
                )
            )
        arms[name] = gates

    def compare() -> dict[str, object]:
        baseline, candidate = mapping(arms["baseline"]), mapping(arms["candidate"])
        directory = evidence.path(mapping(manifest["candidate"])["bend_directory"])
        policy = adapter.checked_policy(directory)
        return compare_observations(baseline, candidate, policy, profile=profile)

    comparison = gate(compare)
    observed = mapping(comparison.get("observations", {}))
    evidence_complete = {
        name: all(
            mapping(result).get("status") == "verified"
            for result in mapping(arm).values()
        )
        for name, arm in arms.items()
    }
    measurement_valid = (
        all(evidence_complete.values()) and comparison.get("status") == "verified"
    )
    qualified = (
        profile == "full"
        and all(evidence_complete.values())
        and comparison.get("status") == "verified"
        and observed.get("dominates") is True
    )
    for path, expected in evidence.hashes.items():
        require(
            digest(Path(path)) == expected,
            f"Raw evidence changed during qualification: {path}",
        )
    return {
        "schema_version": 2,
        "protocol": PROTOCOL,
        "verifier_sha256": digest(Path(__file__)),
        "manifest": str(manifest_path.resolve()),
        "profile": profile,
        "arms": arms,
        "evidence_complete": evidence_complete,
        "measurement_valid": measurement_valid,
        "comparison": comparison,
        "promotion_policy": "full_suite_complete_evidence_and_observed_dominance",
        "decision": "promote_candidate" if qualified else "retain_control",
        "qualified": qualified,
        "raw_artifacts_sha256": evidence.hashes,
        "quality_scope": "sampled_math_only_not_full_qualification"
        if profile == "tiny"
        else "core_suite",
        "claim_scope": "Observed frozen candidate comparison only; no absolute optimum or future latency guarantee",
    }


class Arguments(argparse.Namespace):
    command: str = ""
    container: str = ""
    base_url: str = ""
    key_file: Path = Path()
    output: Path = Path()
    match: Path | None = None
    native_exit_code: int | None = None
    manifest: Path = Path()
    record: Path = Path()
    identity: Path = Path()
    profile: str = ""
    environment: str = ""
    same_instance: bool = False
    directory: Path = Path()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    capture = commands.add_parser(
        "capture", help="Capture actual native serving identity; no inference"
    )
    capture.add_argument("--container", required=True)
    capture.add_argument("--base-url", required=True)
    capture.add_argument("--key-file", type=Path, required=True)
    capture.add_argument("--output", type=Path, required=True)
    capture.add_argument("--match", type=Path)
    capture.add_argument("--native-exit-code", type=int)
    freeze = commands.add_parser(
        "freeze-eval",
        help="Retain exact existing config, scorer and raw dataset hashes",
    )
    freeze.add_argument(
        "--profile",
        required=True,
        choices=(
            "smoke",
            "tiny",
            "diverse",
            "quick",
            "full",
            "agentic",
            "agentic-full",
        ),
    )
    freeze.add_argument("--environment", required=True)
    freeze.add_argument("--output", type=Path, required=True)
    freeze.add_argument("--match", type=Path)
    evaluation = commands.add_parser(
        "check-eval",
        help="Validate one native profile entry; never full-suite qualification or promotion",
    )
    evaluation.add_argument(
        "--profile", required=True, choices=("tiny", "diverse", "quick", "full")
    )
    evaluation.add_argument("--environment", required=True)
    evaluation.add_argument("--directory", type=Path, required=True)
    evaluation.add_argument("--identity", type=Path, required=True)
    evaluation.add_argument("--output", type=Path, required=True)
    qualification = commands.add_parser(
        "qualify", help="Recompute every evidence gate into a new canonical record"
    )
    qualification.add_argument("--manifest", type=Path, required=True)
    qualification.add_argument("--output", type=Path, required=True)
    verification = commands.add_parser(
        "verify", help="Rehash/recompute a record and require exact promotion identity"
    )
    verification.add_argument("--record", type=Path, required=True)
    verification.add_argument("--identity", type=Path, required=True)
    verification.add_argument("--same-instance", action="store_true")
    args = Arguments()
    _ = parser.parse_args(namespace=args)
    try:
        if args.command != "verify":
            require(
                not args.output.exists(),
                "Output already exists; retain old evidence and choose a new path",
            )
        if args.command == "freeze-eval":
            result = frozen_inputs(args.profile, args.environment, args.output.parent)
            if args.match is not None:
                require(
                    document(args.match) == result,
                    "Frozen evaluator/config/scorer/dataset inputs changed during native execution",
                )
            save(args.output, result)
            return 0
        if args.command == "capture":
            capture_identity(
                args.container,
                args.base_url,
                args.key_file,
                args.output,
                args.match,
                args.native_exit_code,
            )
            return 0
        if args.command == "check-eval":
            evidence = Evidence(args.output)
            identity = native_identity(
                document(evidence.retain(args.identity)).get("identity")
            )
            result = gate(
                lambda: evaluation_gate(
                    evidence,
                    args.directory.resolve(strict=True),
                    identity,
                    args.profile,
                    args.environment,
                )
            )
            result["raw_artifacts_sha256"] = evidence.hashes
            save(args.output, result)
            if result["status"] != "verified":
                print(
                    "Native profile entry rejected; inspect " + str(args.output),
                    file=sys.stderr,
                )
                return 1
            return 0
        if args.command == "qualify":
            result = qualify(args.manifest)
            save(args.output, result)
            if result["qualified"] is not True:
                print(
                    "Qualification rejected; retain control. Inspect separate gate reasons in "
                    + str(args.output),
                    file=sys.stderr,
                )
                return 1
            return 0
        record = document(args.record)
        require(record.get("protocol") == PROTOCOL, "Unknown qualification protocol")
        for path, expected in mapping(record.get("raw_artifacts_sha256")).items():
            require(
                digest(Path(path)) == expected,
                f"Raw evidence changed or disappeared: {path}",
            )
        recomputed = qualify(Path(text(record.get("manifest"))))
        require(
            record == recomputed,
            "Qualification record differs from recomputed raw evidence",
        )
        require(
            record.get("qualified") is True
            and record.get("decision") == "promote_candidate",
            "Record is not a qualified improvement; retain control",
        )
        live = document(args.identity)
        require(
            live.get("producer") == "serve.qualification.capture"
            and live.get("producer_sha256") == digest(Path(__file__)),
            "Promotion requires a fresh actual capture, not a recipe declaration",
        )
        current = native_identity(live.get("identity"))
        candidate = mapping(
            mapping(mapping(record.get("arms"))["candidate"])["identity"]
        )
        measured = mapping(candidate.get("observations"))
        # Instance continuity is mandatory within each original measured run.
        # A later restart may qualify only if every implementation/config byte matches.
        require(
            current == measured
            if args.same_instance
            else recipe_identity(current) == recipe_identity(measured),
            "Promotion immutable image/config/model/proof identity differs from measured candidate",
        )
        return 0
    except (
        OSError,
        ValueError,
        KeyError,
        TypeError,
        OverflowError,
        RecursionError,
        http.client.HTTPException,
    ) as error:
        print("Qualification rejected: " + str(error), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
