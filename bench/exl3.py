# Copyright (c) 2026 inference contributors.
"""EXL3 + Bend measurement lane: identity, native tiny math and C1 whole requests.

Standard library plus the prepared evaluator's ``tokenizers`` wheel only. Every
record is exclusive-create canonical JSON. Nothing here starts, stops, flushes
or reconfigures the serving container: identity uses Docker metadata, one
read-only in-container hashing probe, authenticated GET routes and a host
``nvidia-smi`` query. Generation requests are the measured workloads only.
"""

from __future__ import annotations

import csv
import hashlib
import http.client
import json
import math
import os
import re
import subprocess
import time
import tomllib
from collections.abc import Callable
from pathlib import Path
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from tokenizers import Tokenizer

ROOT = Path(__file__).resolve().parents[1]
EVAL = ROOT / "eval"
HOST = "127.0.0.1"
PORT = 18020
ENDPOINT = f"http://{HOST}:{PORT}"
MODEL = "qwen3.8-27b"
CONTEXT = 262144
RUNTIME_PYTHON = "/opt/venv/bin/python"
TARGET_MOUNT = "/models/qwen38-27b-exl3"
DRAFT_MOUNT = "/models/dflash2-exl3"
SERVER = "serve/exl3_server.py"
PATCHES = "/opt/qwen/exl3-patches.json"
PATCHES_LABEL = "io.litos.exl3.patches-sha256"
BEND_DIRECTORY = "bend-exl3"
BEND_IDENTITY = f"/opt/qwen/{BEND_DIRECTORY}/identity.json"
BEND_SCHEMA = "litos-exl3-bend-accept/1"
GPU_NAME = "NVIDIA GeForce RTX 3090"
POWER_LIMIT_WATTS = 350.0
DRAFT_PROPOSALS = 7
MANIFEST = ROOT / "prepare/exl3-manifest.json"
VERIFIERS_REVISION = "ef47b2e96284a00bdcfc1012b9624b0c41ee6a0e"
CAPTURE_PRODUCER = "bench.exl3.capture"
CAPTURE_SCHEMA = 1
DEPTHS = (1024, 8192, 32768)
OUTPUT_TOKENS = 1024
REPETITIONS = 5
INSTRUCTION = (
    "End of reference material. Write a careful technical summary of the main "
    "ideas above, then give one original worked Python example with tests."
)
PROMPTS = ROOT / "bench/throughput-prompts.jsonl"
NONCE = "[measurement run {repetition} of {repetitions} at depth {depth}]"
MAX_BODY = 64 * 1024 * 1024
REQUEST_TIMEOUT_SECONDS = 1800
PROBE_TIMEOUT_SECONDS = 600
PUBLIC_SECRET_MARKERS = ("KEY", "SECRET", "TOKEN", "PASSWORD", "CREDENTIAL")
C1_PROTOCOL = "exl3-c1-whole-request-v1"
MATH_INPUTS_PRODUCER = "bench.exl3.math_inputs"
PROBE_HASH_LIMIT = 64 * 1024 * 1024


# ---------------------------------------------------------------------------
# Fail-closed JSON/evidence helpers.


def require(condition: bool, message: str) -> None:
    """Reject invalid boundary inputs and incomplete observations."""
    if not condition:
        raise ValueError(message)


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


def integer(value: object) -> int:
    """Require an exact integer, never a boolean or missing count."""
    if type(value) is not int:
        raise ValueError("Expected an exact integer, not a flag or missing count")
    return value


def text(value: object) -> str:
    """Require a nonempty string."""
    if not isinstance(value, str) or not value:
        raise ValueError("Expected a nonempty string")
    return value


def canonical(value: object) -> bytes:
    """Sorted compact JSON with one trailing newline; NaN/Infinity rejected."""
    return (
        json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False) + "\n"
    ).encode()


def digest(path: Path) -> str:
    """SHA256 of the exact file bytes."""
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def pairs(items: list[tuple[str, object]]) -> dict[str, object]:
    """Build an object, rejecting duplicate keys instead of overwriting."""
    result: dict[str, object] = {}
    for key, value in items:
        require(key not in result, "Duplicate JSON object key")
        result[key] = value
    return result


def _constant(name: str) -> object:
    raise ValueError(f"Nonfinite JSON constant: {name}")


def loads(raw: bytes | str) -> object:
    """Decode JSON with duplicate-key and nonfinite-constant rejection."""
    return json.loads(raw, object_pairs_hook=pairs, parse_constant=_constant)


def document(path: Path) -> dict[str, object]:
    """Load one canonicalizable JSON object file."""
    result = mapping(loads(path.read_bytes()))
    _ = canonical(result)
    return result


def save(path: Path, value: object) -> None:
    """Exclusive-create canonical JSON; never overwrite evidence."""
    with path.open("xb") as stream:
        _ = stream.write(canonical(value))


def write_new(path: Path, raw: bytes) -> None:
    """Exclusive-create exact raw bytes."""
    with path.open("xb") as stream:
        _ = stream.write(raw)


class Evidence:
    """The explicit raw artifact closure, rehashed whenever it is retained again."""

    def __init__(self, manifest: Path) -> None:
        """Anchor relative evidence paths at the manifest's directory."""
        self.base: Path = manifest.resolve().parent
        self.hashes: dict[str, str] = {}

    def retain(self, path: Path) -> Path:
        """Hash one regular file; a changed rehash rejects the closure."""
        path = path.resolve(strict=True)
        require(path.is_file(), f"Missing regular evidence file: {path}")
        value = digest(path)
        old = self.hashes.setdefault(str(path), value)
        require(old == value, f"Evidence changed during verification: {path}")
        return path

    def tree(self, root: Path) -> dict[str, str]:
        """Retain every file below root; keep relative symlinks as pointer records."""
        require(root.is_dir(), f"Missing evidence directory: {root}")
        result: dict[str, str] = {}
        base = root.resolve()
        for path in sorted(root.rglob("*")):
            if "__pycache__" in path.parts:
                continue
            if path.is_symlink():
                target = os.readlink(path)
                require(
                    not Path(target).is_absolute(),
                    f"Evidence symlink must be relative: {path}",
                )
                resolved = (path.parent / target).resolve(strict=True)
                require(
                    resolved.is_relative_to(base),
                    f"Evidence symlink escapes its tree: {path}",
                )
                result[path.relative_to(root).as_posix()] = "symlink:" + target
                continue
            if path.is_file():
                retained = self.retain(path)
                result[path.relative_to(root).as_posix()] = self.hashes[str(retained)]
        require(bool(result), f"Empty evidence directory: {root}")
        return result


def docker(*arguments: str, timeout: int = 60) -> str:
    """Run one read-only Docker CLI query; any failure rejects the capture."""
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
            "Read-only Docker evidence query failed; inspect container access"
        ) from error
    return result.stdout.strip()


def snapshot_sources(
    directory: Path, names: tuple[str, ...]
) -> list[dict[str, object]]:
    """Copy exact repository producer/config bytes before any endpoint request."""
    result: list[dict[str, object]] = []
    for name in names:
        target = directory / "sources" / name
        target.parent.mkdir(mode=0o700, parents=True, exist_ok=True)
        raw = (ROOT / name).read_bytes()
        write_new(target, raw)
        result.append({
            "path": target.relative_to(directory).as_posix(),
            "sha256": hashlib.sha256(raw).hexdigest(),
            "size_bytes": len(raw),
        })
    return result


# ---------------------------------------------------------------------------
# Authenticated loopback HTTP.


class Client:
    """One fresh authenticated loopback connection per exchange; no retries."""

    def __init__(self, key: str) -> None:
        """Bind the private bearer credential; it is never written to evidence."""
        require(
            bool(key) and all(33 <= ord(char) <= 126 for char in key),
            "Invalid private API key",
        )
        self.key = key

    def exchange(
        self, method: str, path: str, payload: bytes | None
    ) -> tuple[int, bytes]:
        """Send one request and read the complete bounded response body."""
        headers = {"Authorization": "Bearer " + self.key}
        if payload is not None:
            headers["Content-Type"] = "application/json"
        connection = http.client.HTTPConnection(
            HOST, PORT, timeout=REQUEST_TIMEOUT_SECONDS
        )
        try:
            connection.request(method, path, body=payload, headers=headers)
            response = connection.getresponse()
            raw = response.read(MAX_BODY + 1)
            status = response.status
        except http.client.HTTPException as error:
            raise ValueError(f"HTTP exchange failed: {method} {path}") from error
        finally:
            connection.close()
        require(len(raw) <= MAX_BODY, f"Response body exceeds bound: {path}")
        return status, raw

    def json(self, method: str, path: str, payload: bytes | None) -> dict[str, object]:
        """Require HTTP 200 and one canonicalizable JSON object."""
        status, raw = self.exchange(method, path, payload)
        require(status == 200, f"{method} {path} returned HTTP {status}")
        result = mapping(loads(raw))
        _ = canonical(result)
        return result


def request_bytes(body: dict[str, object]) -> bytes:
    """Exact HTTP payload bytes for one frozen request body."""
    return json.dumps(
        body, sort_keys=True, separators=(",", ":"), ensure_ascii=False, allow_nan=False
    ).encode()


# ---------------------------------------------------------------------------
# Serving identity.

PROBE = r"""
import hashlib
import importlib.metadata
import importlib.util
import json
import os
import sys
from pathlib import Path

TARGET, DRAFT, PATCHES, BEND, LIMIT = sys.argv[1:]
SMALL = int(LIMIT)


def sha(path):
    value = hashlib.sha256()
    with open(path, "rb") as stream:
        while chunk := stream.read(1 << 20):
            value.update(chunk)
    return value.hexdigest()


def regular(path):
    if path.is_symlink() or not path.is_file():
        raise SystemExit("probe: missing regular file " + str(path))
    return path


def tree(root):
    files = {}
    for path in sorted(root.rglob("*")):
        relative = path.relative_to(root)
        if "__pycache__" in relative.parts:
            continue
        if path.is_symlink():
            files[relative.as_posix()] = "symlink:" + os.readlink(path)
        elif path.is_file():
            files[relative.as_posix()] = sha(path)
    if not files:
        raise SystemExit("probe: empty tree " + str(root))
    return files


def models(root):
    files = {}
    for path in sorted(Path(root).iterdir()):
        if path.name.startswith("."):
            continue
        size = regular(path).stat().st_size
        files[path.name] = {"size": size, "sha256": sha(path) if size <= SMALL else None}
    return files


def module(name):
    spec = importlib.util.find_spec(name)
    if spec is None or spec.origin is None:
        return None
    origin = Path(spec.origin).resolve(strict=True)
    if spec.submodule_search_locations is None:
        return {"path": str(origin), "sha256": sha(origin)}
    return {"path": str(origin.parent), "files": tree(origin.parent)}


def optional_text(path):
    if not os.path.lexists(path):
        return None
    raw = regular(Path(path)).read_bytes()
    return raw, {"sha256": hashlib.sha256(raw).hexdigest(), "text": raw.decode("utf-8")}


patches = None
found = optional_text(PATCHES)
if found is not None:
    raw, patches = found
    manifest = json.loads(raw)
    root = Path(manifest["engine"]["root"])
    if not root.is_absolute():
        raise SystemExit("probe: patch manifest engine root is not absolute")
    patches["rehashed_files"] = {
        name: sha(regular(root / name)) for name in sorted(manifest["files"])
    }
bend = optional_text(BEND)
engine = module("exllamav3")
if engine is None or "files" not in engine:
    raise SystemExit("probe: exllamav3 package is not installed")
distribution = importlib.metadata.distribution("exllamav3")
print(json.dumps({
    "python": sys.version,
    "executable": sys.executable,
    "opt_qwen": tree(Path("/opt/qwen")),
    "model_preparation": tree(Path("/model-preparation")),
    "target": models(TARGET),
    "draft": models(DRAFT),
    "engine": engine,
    "engine_version": distribution.version,
    "engine_direct_url": distribution.read_text("direct_url.json"),
    "extension": module("exllamav3_ext"),
    "distributions": sorted(
        f"{item.metadata['Name']}=={item.version}"
        for item in importlib.metadata.distributions()
    ),
    "patches": patches,
    "bend": None if bend is None else bend[1],
}, sort_keys=True))
"""


def _public_environment(values: object) -> list[str]:
    result: list[str] = []
    for value in sequence(values):
        entry = text(value)
        name = entry.partition("=")[0]
        if name.startswith("QWEN_") and not any(
            marker in name for marker in PUBLIC_SECRET_MARKERS
        ):
            result.append(entry)
    return sorted(result)


def _container(container: str) -> dict[str, object]:
    raw = mapping(
        loads(docker("container", "inspect", "--format", "{{json .}}", container))
    )
    state = mapping(raw.get("State"))
    config = mapping(raw.get("Config"))
    host = mapping(raw.get("HostConfig"))
    network = mapping(raw.get("NetworkSettings"))
    mounts = [
        {
            "type": mapping(item).get("Type"),
            "source": mapping(item).get("Source"),
            "destination": mapping(item).get("Destination"),
            "read_write": mapping(item).get("RW"),
        }
        for item in sequence(raw.get("Mounts"))
    ]
    result: dict[str, object] = {
        "id": raw.get("Id"),
        "name": raw.get("Name"),
        "image": raw.get("Image"),
        "created": raw.get("Created"),
        "started_at": state.get("StartedAt"),
        "running": state.get("Running"),
        "pid": state.get("Pid"),
        "restart_count": raw.get("RestartCount"),
        "config_image": config.get("Image"),
        "user": config.get("User"),
        "entrypoint": config.get("Entrypoint"),
        "command": config.get("Cmd"),
        "public_environment": _public_environment(config.get("Env")),
        "network_mode": host.get("NetworkMode"),
        "readonly_rootfs": host.get("ReadonlyRootfs"),
        "ports": network.get("Ports"),
        "mounts": sorted(mounts, key=lambda item: str(item["destination"])),
    }
    require(
        result["id"] == container
        and result["running"] is True
        and re.fullmatch(r"sha256:[0-9a-f]{64}", text(result["image"])) is not None
        and bool(text(result["started_at"])),
        "Selected container is not the running immutable instance",
    )
    return result


def _image(image: str) -> dict[str, object]:
    raw = mapping(loads(docker("image", "inspect", "--format", "{{json .}}", image)))
    config = mapping(raw.get("Config"))
    labels = config.get("Labels")
    result: dict[str, object] = {
        "id": raw.get("Id"),
        "created": raw.get("Created"),
        "labels": {} if labels is None else mapping(labels),
        "layers": mapping(raw.get("RootFS")).get("Layers"),
    }
    require(result["id"] == image, "Image inspection selected another image")
    return result


def _probe(container: str) -> dict[str, object]:
    raw = docker(
        "exec",
        container,
        RUNTIME_PYTHON,
        "-I",
        "-B",
        "-c",
        PROBE,
        TARGET_MOUNT,
        DRAFT_MOUNT,
        PATCHES,
        BEND_IDENTITY,
        str(PROBE_HASH_LIMIT),
        timeout=PROBE_TIMEOUT_SECONDS,
    )
    return mapping(loads(raw))


def _gpu() -> dict[str, object]:
    try:
        result = subprocess.run(
            [
                "nvidia-smi",
                "--query-gpu=uuid,name,pci.bus_id,power.limit,enforced.power.limit,driver_version,memory.total",
                "--format=csv,noheader,nounits",
            ],
            capture_output=True,
            text=True,
            timeout=30,
            check=True,
        )
    except (OSError, subprocess.SubprocessError) as error:
        raise ValueError("Host nvidia-smi identity query failed") from error
    rows = list(csv.reader(result.stdout.strip().splitlines()))
    require(
        len(rows) == 1 and len(rows[0]) == 7,
        "Expected exactly one visible GPU board",
    )
    uuid, name, bus, limit, enforced, driver, memory = (
        value.strip() for value in rows[0]
    )
    require(
        name == GPU_NAME
        and float(limit) == POWER_LIMIT_WATTS
        and float(enforced) == POWER_LIMIT_WATTS,
        "Measurement requires the declared RTX 3090 at 350 W; policy is never changed here",
    )
    return {
        "uuid": uuid,
        "name": name,
        "pci_bus_id": bus,
        "power_limit_watts": float(limit),
        "enforced_power_limit_watts": float(enforced),
        "driver_version": driver,
        "memory_total_mib": int(memory),
    }


def _served(client: Client) -> dict[str, object]:
    health = client.json("GET", "/health", None)
    require(health == {"status": "ok"}, "Serving health is not ok")
    models = client.json("GET", "/v1/models", None)
    data = sequence(models.get("data"))
    require(models.get("object") == "list" and len(data) == 1, "Expected one model")
    entry = mapping(data[0])
    require(
        entry.get("id") == MODEL and entry.get("max_model_len") == CONTEXT,
        "Served model alias or reported native context differs",
    )
    return {key: value for key, value in entry.items() if key != "created"}


def _pins() -> dict[str, dict[str, str]]:
    manifest = document(MANIFEST)
    return {
        role: {name: text(value) for name, value in mapping(manifest[role]).items()}
        for role in ("target", "draft")
    }


def _bend(value: object, tree: dict[str, str]) -> dict[str, object] | None:
    key = f"{BEND_DIRECTORY}/identity.json"
    if value is None:
        require(
            not any(name.startswith(BEND_DIRECTORY + "/") for name in tree),
            "Bend artifact directory lacks its identity document",
        )
        return None
    record = mapping(value)
    raw = text(record.get("text")).encode()
    sha = hashlib.sha256(raw).hexdigest()
    require(
        record.get("sha256") == sha == tree.get(key),
        "Bend identity bytes differ from the in-image tree hash",
    )
    identity = mapping(loads(raw))
    require(identity.get("schema") == BEND_SCHEMA, "Unsupported Bend identity schema")
    body = {name: item for name, item in identity.items() if name != "identity_sha256"}
    recomputed = hashlib.sha256(
        json.dumps(body, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()
    require(
        identity.get("identity_sha256") == recomputed,
        "Bend identity_sha256 does not bind its own recorded contents",
    )
    for name, expected in mapping(identity.get("artifacts")).items():
        require(
            tree.get(f"{BEND_DIRECTORY}/{name}") == text(expected),
            f"Baked Bend artifact differs from its identity: {name}",
        )
    return {
        "identity_sha256": recomputed,
        "identity_file_sha256": sha,
        "document": identity,
    }


def capture(container: str, client: Client) -> dict[str, object]:
    """Capture immutable serving identity; every inconsistency rejects it."""
    instance = _container(container)
    image = _image(text(instance["image"]))
    probe = _probe(container)
    tree = {name: text(value) for name, value in mapping(probe.get("opt_qwen")).items()}
    require(SERVER in tree, "Baked EXL3 server is missing")
    pins = _pins()
    for role, mount in (("target", TARGET_MOUNT), ("draft", DRAFT_MOUNT)):
        files = mapping(probe.get(role))
        for name, expected in pins[role].items():
            record = mapping(files.get(name))
            observed = record.get("sha256")
            # Weight bytes are rehashed by the image's startup inventory before
            # loading; per-capture identity records their sizes, not a rehash.
            require(
                observed == expected
                or (
                    observed is None and integer(record.get("size")) > PROBE_HASH_LIMIT
                ),
                f"{mount}/{name} differs from its manifest pin",
            )
    labels = mapping(image["labels"])
    patches_value = probe.get("patches")
    patches: dict[str, object] | None = None
    if patches_value is None:
        require(PATCHES_LABEL not in labels, "Patch label present without its manifest")
    else:
        record = mapping(patches_value)
        raw = text(record.get("text")).encode()
        manifest = mapping(loads(raw))
        sha = hashlib.sha256(raw).hexdigest()
        require(
            record.get("sha256") == sha == labels.get(PATCHES_LABEL),
            "Engine patch manifest differs from its image label",
        )
        rehashed = mapping(record.get("rehashed_files"))
        files = mapping(manifest.get("files"))
        require(set(rehashed) == set(files), "Patched file closure differs")
        for name, entry in files.items():
            require(
                rehashed[name] == mapping(entry).get("post"),
                f"Installed engine file differs from its post-patch hash: {name}",
            )
        acceptor = manifest.get("acceptor")
        if acceptor is not None:
            pinned = mapping(acceptor)
            require(
                pinned.get("root") == f"/opt/qwen/{BEND_DIRECTORY}",
                "Acceptor root differs from the baked Bend directory",
            )
            for name, expected in mapping(pinned.get("files")).items():
                require(
                    tree.get(f"{BEND_DIRECTORY}/{name}") == text(expected),
                    f"Baked acceptor file differs from the patch manifest: {name}",
                )
        patches = {"sha256": sha, "document": manifest, "rehashed_files": rehashed}
    bend = _bend(probe.get("bend"), tree)
    return {
        "container": instance,
        "image": image,
        "variant": labels.get("io.litos.exl3.variant"),
        "server_sha256": tree[SERVER],
        "opt_qwen_files": tree,
        "model_preparation_files": probe.get("model_preparation"),
        "repository_manifest_pins": pins,
        "target_files": probe.get("target"),
        "draft_files": probe.get("draft"),
        "engine": {
            "version": probe.get("engine_version"),
            "direct_url": probe.get("engine_direct_url"),
            "package": probe.get("engine"),
            "extension": probe.get("extension"),
            "manifest_engine_revision": document(MANIFEST).get("engine_revision"),
        },
        "runtime_python": probe.get("python"),
        "runtime_executable": probe.get("executable"),
        "distributions": probe.get("distributions"),
        "engine_patches": patches,
        "bend_acceptance": bend,
        "served_model": _served(client),
        "gpu": _gpu(),
        "tokenizer": _host_tokenizer(instance, probe, pins),
    }


def _host_tokenizer(
    instance: dict[str, object],
    probe: dict[str, object],
    pins: dict[str, dict[str, str]],
) -> dict[str, object]:
    expected = pins["target"]["tokenizer.json"]
    served = mapping(mapping(probe.get("target")).get("tokenizer.json")).get("sha256")
    require(served == expected, "Served tokenizer bytes differ from their manifest pin")
    best: tuple[str, str] | None = None
    for value in sequence(instance["mounts"]):
        mount = mapping(value)
        destination = text(mount.get("destination"))
        if TARGET_MOUNT == destination or TARGET_MOUNT.startswith(
            destination.rstrip("/") + "/"
        ):
            if best is None or len(destination) > len(best[1]):
                best = (text(mount.get("source")), destination)
    if best is None:
        raise ValueError("Target model directory is not a host mount")
    source, destination = best
    path = Path(source) / Path(TARGET_MOUNT).relative_to(destination) / "tokenizer.json"
    require(
        path.is_absolute() and path.resolve(strict=True) == path,
        "Host tokenizer path must be canonical",
    )
    require(
        digest(path) == expected,
        "Host tokenizer bytes differ from the served tokenizer",
    )
    return {"host_path": str(path), "sha256": expected}


def capture_file(
    container: str, client: Client, path: Path, before: Path | None
) -> dict[str, object]:
    """Write one capture envelope; an after-capture must match its before-capture."""
    started = time.time_ns()
    started_monotonic = time.monotonic_ns()
    identity = capture(container, client)
    record: dict[str, object] = {
        "schema_version": CAPTURE_SCHEMA,
        "producer": CAPTURE_PRODUCER,
        "producer_sha256": digest(Path(__file__)),
        "started_unix_ns": started,
        "started_monotonic_ns": started_monotonic,
        "finished_unix_ns": time.time_ns(),
        "finished_monotonic_ns": time.monotonic_ns(),
        "identity": identity,
    }
    if before is not None:
        previous = document(before)
        require(
            previous.get("producer") == CAPTURE_PRODUCER
            and previous.get("schema_version") == CAPTURE_SCHEMA
            and previous.get("producer_sha256") == record["producer_sha256"],
            "Capture producer changed during the measurement",
        )
        require(
            previous.get("identity") == identity,
            "Serving identity changed during the measurement",
        )
        require(
            integer(previous.get("finished_monotonic_ns")) < started_monotonic,
            "Captures are not ordered",
        )
        record["before_sha256"] = digest(before)
    save(path, record)
    return record


# ---------------------------------------------------------------------------
# Native tiny AIME25 math (unchanged Prime/Verifiers producer and grader).

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


def sandbox_image() -> str:
    """The pinned native sandbox image, which must exist locally."""
    image = (EVAL / ".cache/sandbox-image").read_text(encoding="utf-8").strip()
    require(
        re.fullmatch(r"sha256:[a-f0-9]{64}", image) is not None,
        "Missing pinned native sandbox image",
    )
    require(
        docker("image", "inspect", "--format", "{{.Id}}", image) == image,
        "Pinned native sandbox image is not present locally",
    )
    return image


def dataset_snapshot() -> tuple[Path, dict[str, object]]:
    """Locked local AIME25 snapshot directory and its lock entry."""
    entry = mapping(mapping(document(EVAL / "datasets.lock")["huggingface"])["aime25"])
    snapshot = (
        EVAL
        / ".cache/huggingface/hub"
        / ("datasets--" + text(entry["repo"]).replace("/", "--"))
        / "snapshots"
        / text(entry["revision"])
    )
    return snapshot, entry


def expected_call_sampling() -> dict[str, object]:
    """Provider wire sampling the unchanged native client sends from local.toml."""
    with (EVAL / "configs/local.toml").open("rb") as stream:
        local = mapping(tomllib.load(stream))
    sampling = mapping(local["sampling"])
    extra = mapping(sampling.pop("extra_body"))
    return {
        **{key: value for key, value in extra.items() if not isinstance(value, dict)},
        **sampling,
    }


def write_launch(provenance: Path, image: str) -> None:
    """Freeze the tiny profile, replacing only its runtime image with the pin."""
    config = (EVAL / "configs/tiny/aime25.toml").read_text(encoding="utf-8")
    launch, replacements = re.subn(
        r"^image = .*$", f'image = "{image}"', config, flags=re.MULTILINE
    )
    require(replacements == 1, "Tiny profile must bind one sandbox image")
    write_new(provenance / "aime25.toml", launch.encode())


def _tiny_plan(provenance: Path) -> dict[str, object]:
    with (EVAL / "configs/tiny/aime25.toml").open("rb") as stream:
        settings = mapping(tomllib.load(stream))
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
        "Tiny requires exactly three native shuffled tasks and one rollout each",
    )
    with (provenance / "aime25.toml").open("rb") as stream:
        launch = mapping(tomllib.load(stream))
    env = mapping(settings.get("env"))
    agent = mapping(env.get("agent"))
    runtime = mapping(agent.get("runtime"))
    runtime["image"] = (
        (EVAL / ".cache/sandbox-image").read_text(encoding="utf-8").strip()
    )
    agent["runtime"] = runtime
    env["agent"] = agent
    settings["env"] = env
    require(
        launch == settings,
        "Tiny launch differs from its profile beyond the sandbox pin",
    )
    snapshot, _ = dataset_snapshot()
    try:
        result = subprocess.run(
            [
                str(EVAL / ".venv/bin/python"),
                "-I",
                "-c",
                TINY_NATIVE_PLAN,
                str(EVAL),
                str(provenance),
                str(snapshot),
            ],
            capture_output=True,
            text=True,
            timeout=120,
            check=False,
        )
    except subprocess.TimeoutExpired as error:
        raise ValueError("Pinned offline tiny selection did not finish") from error
    require(result.returncode == 0, "Pinned offline native tiny task selection failed")
    plan = mapping(loads(result.stdout))
    tasks = sequence(plan.get("tasks"))
    require(
        integer(plan.get("shuffle_seed")) == 0
        and len(tasks) == 3
        and len({text(mapping(task).get("hash")) for task in tasks}) == 3,
        "Tiny native selection requires seed zero and three distinct tasks",
    )
    return plan


def math_inputs(provenance: Path) -> dict[str, object]:
    """Hash the evaluator/source/config/data closure and replay native selection."""
    files = [
        EVAL / name
        for name in (
            "prime-envs.lock",
            "datasets.lock",
            "uv.lock",
            "pyproject.toml",
            "configs/local.toml",
            "configs/tiny/aime25.toml",
            ".cache/sandbox-image",
        )
    ]
    files.extend([ROOT / "flake.lock", ROOT / "flake.nix", provenance / "aime25.toml"])
    for path in files:
        require(path.is_file(), f"Missing frozen evaluator input: {path}")
    files.extend(path for path in (EVAL / "runtime").rglob("*") if path.is_file())
    for source in (
        EVAL / ".sources/prime-envs/environments",
        EVAL / ".sources/verifiers/verifiers",
    ):
        require(source.is_dir(), f"Missing pinned evaluator source: {source}")
        files.extend(
            path
            for path in source.rglob("*")
            if path.suffix in (".py", ".toml", ".lock")
        )
    hashes = {str(path.resolve()): digest(path) for path in files if path.is_file()}
    snapshot, entry = dataset_snapshot()
    for item in sequence(entry["files"]):
        raw = mapping(item)
        path = snapshot / text(raw["path"])
        size = integer(raw["size"])
        require(path.stat().st_size == size, f"Pinned dataset size differs: {path}")
        sha = digest(path)
        algorithm = text(raw["algorithm"])
        if algorithm == "sha256":
            actual = sha
        else:
            require(algorithm == "git-sha1", "Unknown pinned dataset hash algorithm")
            blob = hashlib.sha1(f"blob {size}\0".encode())
            with path.open("rb") as stream:
                while chunk := stream.read(1024 * 1024):
                    blob.update(chunk)
            actual = blob.hexdigest()
        require(actual == text(raw["hash"]), f"Pinned dataset bytes differ: {path}")
        hashes[str(path.resolve())] = sha
    return {
        "schema_version": 1,
        "producer": MATH_INPUTS_PRODUCER,
        "profile": "tiny",
        "environment": "aime25",
        "files_sha256": hashes,
        "selection": _tiny_plan(provenance),
    }


def math_command(group: Path) -> tuple[list[str], Path]:
    """The unchanged native Prime/Verifiers CLI invocation and working directory."""
    snapshot, _ = dataset_snapshot()
    return (
        [
            "uv",
            "run",
            "--project",
            str(EVAL),
            "--no-sync",
            "eval",
            "@",
            str(EVAL / "configs/local.toml"),
            "@",
            str(group / "provenance/aime25.toml"),
            "-o",
            str(group / "aime25"),
            "--no-rich",
            "--no-push",
            "--env.taskset.dataset-name",
            str(snapshot),
        ],
        EVAL / ".sources/prime-envs",
    )


def math_environment(group: Path, key: str) -> dict[str, str]:
    """Offline native evaluator environment; the key is passed only via env."""
    removed = (
        "PYTHONPATH",
        "PYTHONHOME",
        "UV_FROZEN",
        "OPENAI_API_KEY",
        "QWEN_API_KEY",
        "DOCKER_CONTEXT",
        "DOCKER_TLS_VERIFY",
        "DOCKER_CERT_PATH",
    )
    env = {name: value for name, value in os.environ.items() if name not in removed}
    home = EVAL / ".cache/home"
    home.mkdir(mode=0o700, parents=True, exist_ok=True)
    env.update({
        "LC_ALL": "C",
        "PYTHONDONTWRITEBYTECODE": "1",
        "PYTHONUNBUFFERED": "1",
        "HOME": str(home),
        "HF_HOME": str(EVAL / ".cache/huggingface"),
        "HF_HUB_CACHE": str(EVAL / ".cache/huggingface/hub"),
        "HF_HUB_OFFLINE": "1",
        "HF_DATASETS_OFFLINE": "1",
        "HF_HUB_DISABLE_TELEMETRY": "1",
        "HF_DATASETS_CACHE": str(group / ".dataset-cache"),
        "UV_PYTHON": str(EVAL / ".venv/bin/python"),
        "UV_PYTHON_DOWNLOADS": "never",
        "UV_OFFLINE": "1",
        "DOCKER_HOST": "unix:///run/user/1000/docker.sock",
        "QWEN_API_KEY": key,
    })
    return env


def freeze_math(group: Path) -> dict[str, object]:
    """Create the fresh math group and bind its inputs before any request."""
    group.mkdir(mode=0o700)
    provenance = group / "provenance"
    provenance.mkdir(mode=0o700)
    write_launch(provenance, sandbox_image())
    for source in (
        EVAL / "configs/local.toml",
        EVAL / "prime-envs.lock",
        EVAL / "datasets.lock",
        EVAL / "uv.lock",
        EVAL / "pyproject.toml",
        ROOT / "flake.lock",
    ):
        write_new(provenance / source.name, source.read_bytes())
    command, cwd = math_command(group)
    save(
        provenance / "invocation.json",
        {
            "producer_argv": command,
            "producer_cwd": str(cwd),
            "credential": "QWEN_API_KEY loaded privately from the operator key file; value not retained",
        },
    )
    frozen = math_inputs(provenance)
    save(provenance / "aime25.evaluation-inputs-before.json", frozen)
    return frozen


def _trace_window(trace: dict[str, object]) -> tuple[int, int]:
    timing = mapping(trace.get("timing"))
    start = number(timing.get("start"))
    ends: list[float] = []
    for phase in ("boot", "setup", "agent", "finalize", "scoring"):
        span = mapping(timing.get(phase, {}))
        low, high = number(span.get("start", 0)), number(span.get("end", 0))
        if low == 0 and high == 0:
            continue
        require(low >= start and high >= low > 0, "Incomplete or reversed trace phase")
        ends.append(high)
    require(start > 0 and bool(ends), "No usable native trace envelope")
    return round(start * 1_000_000_000), round(max(ends) * 1_000_000_000)


def admit_math(
    evidence: Evidence, group: Path, window: tuple[int, int]
) -> dict[str, object]:
    """Replay the complete native AIME25 evidence; fail on any missing/failed call."""
    provenance = group / "provenance"
    frozen = document(
        evidence.retain(provenance / "aime25.evaluation-inputs-before.json")
    )
    require(
        frozen
        == document(evidence.retain(provenance / "aime25.evaluation-inputs-after.json"))
        and frozen.get("producer") == MATH_INPUTS_PRODUCER,
        "Math inputs are missing or changed during the native run",
    )
    for path, expected in mapping(frozen.get("files_sha256")).items():
        require(
            digest(evidence.retain(Path(path))) == expected,
            f"Frozen math input changed: {path}",
        )
    selection = mapping(frozen.get("selection"))
    directory = group / "aime25"
    paths = list(directory.glob("*/traces.jsonl"))
    require(len(paths) == 1, "Require one unfiltered native traces.jsonl")
    trace_path = evidence.retain(paths[0])
    config = document(evidence.retain(trace_path.parent / "configs/resolved/eval.json"))
    config.pop("run", None)
    config.pop("output_dir", None)
    require(
        config == mapping(selection.get("resolved_config")),
        "Resolved native taskset, harness, sampling, budget or runtime differs from the frozen plan",
    )
    require(
        config.get("model") == MODEL
        and mapping(mapping(config.get("env")).get("taskset")).get("id") == "aime25",
        "Native run selected another model or taskset",
    )
    logs = list(trace_path.parent.glob("logs/attempt_*/eval.log"))
    require(len(logs) == 1, "Missing unique native attempt log")
    log = evidence.retain(logs[0]).read_text(encoding="utf-8")
    require(
        len(re.findall(r"running 3x1 rollouts on qwen3\.8-27b", log)) == 1,
        "Missing unambiguous native 3x1 run plan",
    )
    planned = [mapping(task) for task in sequence(selection.get("tasks"))]
    sampling = expected_call_sampling()
    rows = [mapping(loads(line)) for line in trace_path.read_bytes().splitlines()]
    require(
        len(rows) == 3, "Require all three native episodes, without retry/filtering"
    )
    tasks: list[dict[str, object]] = []
    rewards: list[float] = []
    for ordinal, (episode, expected) in enumerate(zip(rows, planned, strict=True)):
        task = mapping(episode.get("task"))
        require(
            {key: task.get(key) for key in ("key", "hash", "type")} == expected,
            f"Task identity/order differs from the frozen plan at ordinal {ordinal}",
        )
        require(
            task.get("hash")
            == hashlib.sha256(
                json.dumps(task.get("data"), sort_keys=True).encode()
            ).hexdigest(),
            "Native task content hash mismatch",
        )
        require(
            episode.get("ok") is True and not sequence(episode.get("errors")),
            "Operationally failed native episode",
        )
        traces = sequence(episode.get("traces"))
        require(len(traces) == 1, "Require the native single-agent trace")
        trace = mapping(traces[0])
        require(
            trace.get("ok") is True
            and not sequence(trace.get("errors"))
            and trace.get("is_completed") is True,
            "Failed or incomplete native trace",
        )
        require(
            mapping(trace.get("verifiers")).get("commit") == VERIFIERS_REVISION,
            "Unpinned native scorer build",
        )
        calls = sequence(trace.get("calls"))
        require(
            len(calls) == 1, "Frozen one-turn null harness requires exactly one call"
        )
        call = mapping(calls[0])
        require(
            call.get("error") is None
            and call.get("model") == MODEL
            and call.get("endpoint") == "/chat/completions"
            and mapping(call.get("sampling")) == sampling
            and call.get("finish_reason") in ("stop", "length"),
            "Native call failed or used another model, endpoint or sampling",
        )
        start, end = _trace_window(trace)
        require(
            window[0] <= start <= end <= window[1],
            "Native trace does not lie inside its serving identity captures",
        )
        named = mapping(trace.get("rewards"))
        require(bool(named), "Missing native rewards")
        weighted: list[float] = []
        for name, reward in named.items():
            record = mapping(reward)
            score, weight = number(record.get("score")), number(record.get("weight"))
            weighted.append(number(score * weight))
            require(bool(name), "Unnamed native reward")
        reward_sum = number(math.fsum(weighted))
        rewards.append(reward_sum)
        tasks.append({
            "ordinal": ordinal,
            "key": task["key"],
            "hash": task["hash"],
            "trace_id": trace.get("id"),
            "native_rewards": named,
            "native_weighted_reward": reward_sum,
            "finish_reason": call["finish_reason"],
            "stop_condition": trace.get("stop_condition"),
            "truncated": call["finish_reason"] == "length",
        })
    return {
        "config_sha256": hashlib.sha256(canonical(config)).hexdigest(),
        "tasks": tasks,
        "rollouts": len(tasks),
        "scope": "sampled_math_only_not_full_qualification",
        "weighted_reward_mean": math.fsum(rewards) / len(rewards),
        "truncated_rollouts": sum(bool(task["truncated"]) for task in tasks),
    }


# ---------------------------------------------------------------------------
# C1 whole-request lane.


class RawTokenizer:
    """The served target tokenizer, loaded from bytes already bound to identity."""

    def __init__(self, path: Path, sha256: str) -> None:
        """Load exactly the hash-pinned tokenizer.json bytes."""
        from tokenizers import Tokenizer

        raw = path.read_bytes()
        require(hashlib.sha256(raw).hexdigest() == sha256, "Tokenizer bytes changed")
        self.tokenizer: Tokenizer = Tokenizer.from_str(raw.decode("utf-8"))
        self.sha256 = sha256

    def count(self, content: str) -> int:
        """Raw-content token count without special tokens or a chat template."""
        return len(self.tokenizer.encode(content, add_special_tokens=False).ids)


def corpus_document(source: Path) -> str:
    """The frozen C1 prompt corpus repeated to cover the deepest row."""
    prompts: list[str] = []
    for line in source.read_bytes().decode("utf-8").splitlines():
        conversations = sequence(mapping(loads(line)).get("conversations"))
        require(bool(conversations), "Invalid frozen prompt conversations")
        prompts.append(text(mapping(conversations[0]).get("value")))
    return "\n\n".join(prompts * 96)


def natural_prompt(
    tokenizer: RawTokenizer, document_text: str, depth: int, nonce: str
) -> tuple[str, int, int]:
    """Cut the corpus so raw content lands within two tokens of the depth."""
    require(depth in DEPTHS, "Unsupported C1 depth")
    low, high = 0, len(document_text)
    for _ in range(24):
        middle = (low + high) // 2
        content = nonce + "\n" + document_text[:middle] + "\n\n" + INSTRUCTION
        count = tokenizer.count(content)
        if abs(count - depth) <= 2:
            return content, middle, count
        if count < depth:
            low = middle
        else:
            high = middle
    raise ValueError("C1 depth sizing did not converge")


def _row_name(depth: int, repetition: int) -> str:
    return f"depth-{depth}-rep-{repetition}"


def plan_c1(
    directory: Path, client: Client, tokenizer: RawTokenizer
) -> dict[str, object]:
    """Freeze all prompt strings, request bytes and rendered IDs before measuring."""
    directory.mkdir(mode=0o700)
    corpus = corpus_document(
        directory.parent / "sources/bench/throughput-prompts.jsonl"
    )
    rows: list[dict[str, object]] = []
    for depth in DEPTHS:
        for repetition in range(REPETITIONS):
            nonce = NONCE.format(
                repetition=repetition + 1, repetitions=REPETITIONS, depth=depth
            )
            content, cut, count = natural_prompt(tokenizer, corpus, depth, nonce)
            body: dict[str, object] = {
                "model": MODEL,
                "messages": [{"role": "user", "content": content}],
                "max_tokens": OUTPUT_TOKENS,
                "temperature": 0,
                "top_p": 1,
                "n": 1,
            }
            payload = request_bytes(body)
            row = directory / _row_name(depth, repetition)
            row.mkdir(mode=0o700)
            write_new(row / "request.json", payload)
            status, raw = client.exchange(
                "POST", "/v1/chat/completions/render", payload
            )
            write_new(row / "render-response.json", raw)
            require(status == 200, f"Render returned HTTP {status}")
            ids = _token_ids(raw)
            require(
                len(ids) + OUTPUT_TOKENS <= CONTEXT,
                "Rendered prompt plus output budget exceeds native context",
            )
            rows.append({
                "depth_target": depth,
                "repetition": repetition,
                "nonce": nonce,
                "corpus_prefix_chars": cut,
                "raw_content_tokens": count,
                "rendered_prompt_tokens": len(ids),
                "rendered_token_ids_sha256": hashlib.sha256(canonical(ids)).hexdigest(),
                "request_sha256": hashlib.sha256(payload).hexdigest(),
                "render_response_sha256": hashlib.sha256(raw).hexdigest(),
            })
    plan: dict[str, object] = {
        "protocol": C1_PROTOCOL,
        "depths": list(DEPTHS),
        "repetitions": REPETITIONS,
        "order": "depth_then_repetition",
        "concurrency": 1,
        "output_budget": OUTPUT_TOKENS,
        "nonce_template": NONCE,
        "raw_content_tolerance_tokens": 2,
        "raw_content_tokenizer_sha256": tokenizer.sha256,
        "sampling": {"temperature": 0, "top_p": 1, "n": 1, "stream": False},
        "cache_policy": "deterministic_per_row_nonce_no_flush_no_warmup",
        "transport": "non-streaming chat completion; wall time is request send through complete response body",
        "rows": rows,
    }
    save(directory / "plan.json", plan)
    return plan


def _token_ids(raw: bytes) -> list[int]:
    value = mapping(loads(raw))
    require(set(value) == {"token_ids"}, "Unexpected render response fields")
    ids = [integer(item) for item in sequence(value["token_ids"])]
    require(bool(ids) and all(item >= 0 for item in ids), "Invalid rendered token IDs")
    return ids


def _spec(value: object, completion: int) -> dict[str, int]:
    record = mapping(value)
    require(set(record) == {"rounds", "committed"}, "Unexpected exl3_spec fields")
    rounds, committed = integer(record["rounds"]), integer(record["committed"])
    require(
        0 <= rounds <= committed <= completion
        and committed <= (DRAFT_PROPOSALS + 1) * rounds,
        "Inconsistent native speculative counters",
    )
    return {"rounds": rounds, "committed": committed}


def c1_row(directory: Path, planned: dict[str, object]) -> dict[str, object]:
    """Validate one row entirely from its retained raw files."""
    row = directory / _row_name(
        integer(planned["depth_target"]), integer(planned["repetition"])
    )
    payload = (row / "request.json").read_bytes()
    require(
        hashlib.sha256(payload).hexdigest() == planned["request_sha256"],
        "C1 request bytes differ from the frozen plan",
    )
    render = (row / "render-response.json").read_bytes()
    require(
        hashlib.sha256(render).hexdigest() == planned["render_response_sha256"],
        "C1 render receipt differs from the frozen plan",
    )
    prompt_tokens = len(_token_ids(render))
    timing = document(row / "timing.json")
    require(timing.get("status") == 200, "C1 request failed")
    started = integer(timing.get("request_started_monotonic_ns"))
    received = integer(timing.get("response_received_monotonic_ns"))
    wall = received - started
    require(wall > 0, "Nonpositive C1 request wall time")
    response = mapping(loads((row / "response.json").read_bytes()))
    choices = sequence(response.get("choices"))
    require(
        response.get("object") == "chat.completion"
        and response.get("model") == MODEL
        and len(choices) == 1,
        "Expected one chat completion",
    )
    choice = mapping(choices[0])
    message = mapping(choice.get("message"))
    finish = choice.get("finish_reason")
    require(
        choice.get("index") == 0
        and finish in ("stop", "length")
        and message.get("role") == "assistant"
        and "tool_calls" not in message,
        "Incomplete or unexpected C1 choice",
    )
    usage = mapping(response.get("usage"))
    require(
        set(usage)
        in (
            {"prompt_tokens", "completion_tokens", "total_tokens"},
            {"prompt_tokens", "completion_tokens", "total_tokens", "exl3_spec"},
        ),
        "Unexpected C1 usage fields",
    )
    prompt = integer(usage["prompt_tokens"])
    completion = integer(usage["completion_tokens"])
    require(
        prompt == prompt_tokens == planned["rendered_prompt_tokens"],
        "Native prompt usage differs from the rendered request",
    )
    require(
        integer(usage["total_tokens"]) == prompt + completion
        and 1 <= completion <= OUTPUT_TOKENS
        and (finish == "stop" or completion == OUTPUT_TOKENS),
        "Invalid C1 completion usage or finish",
    )
    spec = _spec(usage["exl3_spec"], completion) if "exl3_spec" in usage else None
    return {
        "depth_target": planned["depth_target"],
        "repetition": planned["repetition"],
        "request_sha256": planned["request_sha256"],
        "response_sha256": digest(row / "response.json"),
        "prompt_tokens": prompt,
        "completion_tokens": completion,
        "finish_reason": finish,
        "request_started_unix_ns": integer(timing.get("request_started_unix_ns")),
        "request_started_monotonic_ns": started,
        "response_received_monotonic_ns": received,
        "wall_ns": wall,
        "whole_request_tok_s": completion * 1_000_000_000 / wall,
        "exl3_spec": spec,
        "spec_accept_length": None
        if spec is None or spec["rounds"] == 0
        else spec["committed"] / spec["rounds"],
    }


def run_c1(
    directory: Path,
    client: Client,
    plan: dict[str, object],
    checkpoint: Callable[[], object],
) -> None:
    """Send the frozen rows once each, in order; retain raw bytes before checks."""
    for value in sequence(plan["rows"]):
        planned = mapping(value)
        checkpoint()
        row = directory / _row_name(
            integer(planned["depth_target"]), integer(planned["repetition"])
        )
        payload = (row / "request.json").read_bytes()
        started_unix = time.time_ns()
        started = time.monotonic_ns()
        status, raw = client.exchange("POST", "/v1/chat/completions", payload)
        received = time.monotonic_ns()
        write_new(row / "response.json", raw)
        save(
            row / "timing.json",
            {
                "status": status,
                "request_started_unix_ns": started_unix,
                "request_started_monotonic_ns": started,
                "response_received_monotonic_ns": received,
                "clock": "monotonic from request send through complete response body",
            },
        )
        save(row / "row.json", c1_row(directory, planned))


def admit_c1(evidence: Evidence, directory: Path) -> dict[str, object]:
    """Recompute every row and the pooled per-depth rates from raw files."""
    plan = document(evidence.retain(directory / "plan.json"))
    require(
        plan.get("protocol") == C1_PROTOCOL
        and plan.get("depths") == list(DEPTHS)
        and plan.get("repetitions") == REPETITIONS,
        "Unexpected C1 plan",
    )
    planned_rows = [mapping(value) for value in sequence(plan["rows"])]
    require(
        [(row["depth_target"], row["repetition"]) for row in planned_rows]
        == [
            (depth, repetition) for depth in DEPTHS for repetition in range(REPETITIONS)
        ],
        "C1 plan order differs",
    )
    rows: list[dict[str, object]] = []
    for planned in planned_rows:
        row = c1_row(directory, planned)
        name = _row_name(
            integer(planned["depth_target"]), integer(planned["repetition"])
        )
        for filename in (
            "request.json",
            "render-response.json",
            "response.json",
            "timing.json",
        ):
            evidence.retain(directory / name / filename)
        require(
            document(evidence.retain(directory / name / "row.json")) == row,
            "C1 producer row differs from raw replay",
        )
        rows.append(row)
    starts = [integer(row["request_started_monotonic_ns"]) for row in rows]
    ends = [integer(row["response_received_monotonic_ns"]) for row in rows]
    require(
        all(end <= start for end, start in zip(ends, starts[1:], strict=False)),
        "C1 requests overlapped; concurrency must be one",
    )
    metrics: dict[str, float] = {}
    pooled: dict[str, object] = {}
    for depth in DEPTHS:
        selected = [row for row in rows if row["depth_target"] == depth]
        require(len(selected) == REPETITIONS, "Incomplete C1 matrix")
        tokens = sum(integer(row["completion_tokens"]) for row in selected)
        wall = sum(integer(row["wall_ns"]) for row in selected)
        require(tokens > 0 and wall > 0, "Missing positive C1 whole-request window")
        metrics[f"c1_request_tok_s_{depth}"] = tokens * 1_000_000_000 / wall
        pooled[str(depth)] = {
            "completion_tokens": tokens,
            "wall_ns": wall,
            "repetitions": REPETITIONS,
        }
    specs = [row["exl3_spec"] for row in rows]
    spec_summary: dict[str, object] | None = None
    if any(spec is not None for spec in specs):
        records = [mapping(spec) for spec in specs if spec is not None]
        require(
            len(records) == len(rows), "Speculative counters missing on some C1 rows"
        )
        rounds = sum(integer(record["rounds"]) for record in records)
        committed = sum(integer(record["committed"]) for record in records)
        require(rounds > 0, "No speculative verify rounds were reported")
        metrics["spec_accept_length"] = committed / rounds
        spec_summary = {
            "rounds": rounds,
            "committed": committed,
            "scope": "C1 rows only: committed tokens per native verify round, pooled over all 15 requests",
        }
    return {
        "protocol": C1_PROTOCOL,
        "rows": rows,
        "metrics": metrics,
        "pooled": pooled,
        "speculation": spec_summary,
        "metric_scope": "whole-request output tok/s: sum completion tokens / sum request wall time per depth, including prefill, decode and HTTP",
        "ttft": "unavailable: non-streaming EXL3 transport has no first-token arrival",
        "committed_decode_tps": "unavailable: EXL3 exposes no incremental committed counters",
    }
