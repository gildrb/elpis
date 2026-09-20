#!/usr/bin/env python3
"""Retain and replay finite numerical observations from the immutable candidate.

Standalone components are NOT full-model serving, capacity, quality or power proof.
Run only in an idle diagnostic container under the caller's exclusive GPU lease.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
from collections.abc import Callable, Mapping
import inspect
import json
import math
import os
from pathlib import Path
import subprocess
import sys
import traceback
from types import ModuleType
from typing import TYPE_CHECKING, NoReturn, TypedDict

if TYPE_CHECKING:
    import numpy as np

    Scalar = np.bool_ | np.int8 | np.int16 | np.int32 | np.int64 | np.uint8 | np.uint16 | np.uint32 | np.uint64 | np.float16 | np.float32 | np.float64
    NumericArray = np.ndarray[tuple[int, ...], np.dtype[Scalar]]


class Event(TypedDict):
    suite: str
    kind: str
    arrays: str
    metadata: dict[str, object]


class Suite(TypedDict):
    source: str
    seed: int | None
    rng: str
    first_event: int
    error: str | None
    exit_code: int
    event_count: int

ROOT = Path(__file__).resolve().parents[1]
PROTOCOL = "qwen-component-numerics-v2"
SOURCES = (
    "bench/numerical.py",
    "patches/qualification/kvarn-prefill-tile-parity.py",
    "patches/qualification/kvarn-attention-regressions.py",
    "patches/qualification/kvarn-gather-parity.py",
    "patches/qualification/kvarn-commit-graph-blocker.py",
    "prepare/packed-forward-check.py",
    "prepare/convert-embedding.py",
    "prepare/source.sha256",
    "prepare/artifact.sha256",
    "prepare/embedding-validation.json",
    "patches/qualification/kvarn-nosync-parity.py",
)
SUITE_SPECS = (
    ("prefill", SOURCES[1], 20260913), ("attention", SOURCES[2], 20260918),
    ("native", SOURCES[10], 20260915), ("storage", SOURCES[3], 20260917),
    ("commit", SOURCES[4], 20260919),
    ("sampler", SOURCES[0], None), ("embedding", SOURCES[0], None),
)
RECIPE_FIELDS = (
    "image_sha256", "engine_base_commit", "ordered_patch_sha256", "container_env",
    "actual_server", "model_inventory", "bend_artifacts", "bend_toolchain",
    "server_config_sha256", "component_identity", "hardware",
)
LIMITATIONS = [
    "Standalone component observations, not full served-path validation or model quality.",
    "KVarN kernel error is relative to dequantized packed-KV PyTorch reference; it is not the approximation loss relative to unquantized KV.",
    "Native 262144-token traversal uses repeated real packed tiles and a raw tail, independently replayed over the entire visible history; this is not loaded-model capacity or unquantized-quality proof.",
    "Commit fixture executes real native pools and production commit runner, with deterministic toy draft projections; it does not exercise the loaded model's projections, Mamba recurrence or scheduler cancellation.",
    "Sampler coverage is greedy temperature=0, top_p=1, no penalties/grammar; no non-greedy, finite-RNG-law or broad sampling API claim.",
    "No W4A8 claim; an enabled A8 path requires its own numerical evidence.",
]


def runtime_components() -> dict[str, object]:
    """Self-contained, allocation-free installed source/binary/ABI capture."""
    import hashlib
    import importlib.metadata
    import importlib.util
    import os
    import platform
    from pathlib import Path
    import subprocess
    import sys

    def sha(path: Path) -> str:
        with path.open("rb") as stream:
            return hashlib.file_digest(stream, "sha256").hexdigest()

    spec = importlib.util.find_spec("sglang")
    if spec is None or spec.origin is None:
        raise ValueError("Installed SGLang package is missing")
    root = Path(spec.origin).parent
    patterns = (
        "kernels/ops/kvarn/*.py", "srt/mem_cache/kvarn/*.py",
        "srt/mem_cache/kvarn_allocator.py", "srt/mem_cache/kvarn_budget.py",
        "srt/mem_cache/kv_cache_configurator.py", "srt/layers/attention/kvarn_backend.py",
        "srt/layers/packed_w8_embedding.py", "srt/speculative/dflash*.py",
        "kernels/ops/speculative/dflash.py", "kernels/ops/speculative/reject_sampling.py",
        "srt/managers/schedule_batch.py", "srt/sampling/sampling_params.py",
    )
    modules = {}
    for pattern in patterns:
        paths = sorted(root.glob(pattern))
        if not paths:
            raise ValueError("Missing numerical runtime component: " + pattern)
        for path in paths:
            modules[path.relative_to(root).as_posix()] = sha(path)
    packages = {}
    for name in ("torch", "triton", "flashinfer-python", "sgl-kernel", "safetensors", "numpy", "compressed-tensors"):
        dist = importlib.metadata.distribution(name)
        files = {}
        for entry in dist.files or ():
            text = str(entry)
            # Hash actual installed native binaries, not just a claimed version.
            if text.endswith((".so", ".pyd", "/RECORD", "/METADATA")) or text == "torch/version.py":
                path = Path(str(dist.locate_file(entry)))
                if path.is_file():
                    files[text] = sha(path)
        if not files:
            raise ValueError("No installed package identity: " + name)
        packages[name] = {"version": dist.version, "files_sha256": files}
    result = subprocess.run([
        "nvidia-smi", "--query-gpu=uuid,name,pci.bus_id,driver_version,compute_cap",
        "--format=csv,noheader,nounits",
    ], check=True, text=True, capture_output=True, timeout=30)
    rows = [[part.strip() for part in row.split(",")] for row in result.stdout.strip().splitlines()]
    if len(rows) != 1 or len(rows[0]) != 5:
        raise ValueError("Exactly one diagnostic GPU is required")
    return {
        "modules_sha256": modules, "packages": packages,
        "kernel_environment": {name: os.environ.get(name) for name in (
            "TRITON_INTERPRET", "TRITON_DISABLE_LINE_INFO", "TRITON_PTXAS_PATH",
            "NVIDIA_TF32_OVERRIDE", "TORCH_ALLOW_TF32_CUBLAS_OVERRIDE",
            "CUBLAS_WORKSPACE_CONFIG", "CUDA_MODULE_LOADING", "CUDA_VISIBLE_DEVICES",
            "SGLANG_SIMULATE_ACC_LEN",
        )},
        "python": {"version": platform.python_version(), "implementation": platform.python_implementation(),
                   "cache_tag": sys.implementation.cache_tag, "machine": platform.machine(),
                   "libc": list(platform.libc_ver())},
        "gpu": dict(zip(("uuid", "name", "pci_bus_id", "driver_version", "compute_capability"), rows[0])),
    }


def require(condition: object, message: str) -> None:
    if not condition:
        raise ValueError(message)


def digest(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def canonical(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False) + "\n").encode()


def save(path: Path, value: object) -> None:
    with path.open("xb") as stream:
        stream.write(canonical(value))


def mapping(value: object) -> dict[str, object]:
    if not isinstance(value, dict):
        raise ValueError("Expected JSON object")
    result: dict[str, object] = {}
    for key, child in value.items():
        if not isinstance(key, str):
            raise ValueError("Expected string object key")
        result[key] = child
    return result


def sequence(value: object) -> list[object]:
    if not isinstance(value, list):
        raise ValueError("Expected JSON array")
    return list(value)


def integer(value: object) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise ValueError("Expected integer")
    return value


def text(value: object) -> str:
    if not isinstance(value, str):
        raise ValueError("Expected string")
    return value


def document(path: Path) -> dict[str, object]:
    def pairs(items: list[tuple[str, object]]) -> dict[str, object]:
        result: dict[str, object] = {}
        for key, value in items:
            require(key not in result, "Duplicate JSON key")
            result[key] = value
        return result

    def invalid(value: str) -> NoReturn:
        raise ValueError("Nonfinite JSON: " + value)

    def finite_float(value: str) -> float:
        result = float(value)
        if not math.isfinite(result):
            invalid(value)
        return result

    value: object = json.loads(path.read_bytes(), object_pairs_hook=pairs,
                               parse_constant=invalid, parse_float=finite_float)
    return mapping(value)


def recipe(identity: Mapping[str, object]) -> dict[str, object]:
    require(all(name in identity for name in RECIPE_FIELDS), "Incomplete serving component identity; recapture with current qualification producer")
    return {name: identity[name] for name in RECIPE_FIELDS}


def tree(directory: Path) -> list[dict[str, object]]:
    return [{"path": p.relative_to(directory).as_posix(), "sha256": digest(p), "size_bytes": p.stat().st_size}
            for p in sorted(directory.rglob("*")) if p.is_file() and p.name != "report.json"]


class Recorder:
    """Write numeric arrays immediately, including observations that later fail."""
    def __init__(self, directory: Path) -> None:
        self.directory = directory
        self.events: list[Event] = []
        self.suite = ""

    def __call__(self, kind: str, tensors: object, metadata: Mapping[str, object]) -> None:
        import numpy as np
        import torch

        arrays: dict[str, NumericArray] = {}

        def flatten(value: object, name: str) -> None:
            if isinstance(value, dict):
                for key, child in mapping(value).items():
                    require(key != "" and "/" not in key, "Invalid observation tensor key")
                    flatten(child, name + "/" + key if name else key)
            elif isinstance(value, (list, tuple)):
                for index, child in enumerate(value):
                    flatten(child, name + "/" + str(index))
            else:
                if not isinstance(value, torch.Tensor):
                    raise ValueError("Observation must be a tensor")
                value = value.detach().cpu().contiguous()
                # uint16 retains exact BF16 payload, without NumPy extension dtypes or pickle.
                arrays[name] = value.view(torch.uint16).numpy() if value.dtype == torch.bfloat16 else value.numpy()
        flatten(tensors, "")
        filename = f"arrays/{len(self.events):05d}.npz"
        with (self.directory / filename).open("xb") as stream:
            np.savez(stream, allow_pickle=False, **arrays)
        self.events.append({"suite": self.suite, "kind": kind, "arrays": filename, "metadata": dict(metadata)})


def _producer(path: Path) -> ModuleType:
    spec = importlib.util.spec_from_file_location(path.stem.replace("-", "_"), path)
    if spec is None or spec.loader is None:
        raise ValueError("Cannot load frozen numerical producer")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _entry(module: ModuleType, name: str) -> Callable[..., object]:
    value: object = getattr(module, name, None)
    if not callable(value):
        raise ValueError("Missing frozen producer entrypoint: " + name)
    return value


def _greedy_observations(record: Recorder) -> None:
    """Exercise the actual pinned selector/accept kernels; no model substitute."""
    import torch
    from sglang.kernels.ops.speculative.dflash import (
        selector_walk_triton,
        _compute_dflash_accept_bonus_triton_unchecked,
    )
    from bend.adapter import checked_speculation

    policy = checked_speculation(Path("/opt/qwen/bend"))
    policy_rows = torch.tensor(policy.decisions, dtype=torch.int32, device="cuda")
    # Seven proposal slots, four lattice choices, three score regimes.
    ids = torch.arange(3 * 7 * 4, device="cuda", dtype=torch.int64).reshape(3, 7, 4) + 10
    scores = torch.arange(3 * 7 * 4 * 4, device="cuda", dtype=torch.float32).reshape(3, 7, 4, 4).remainder(11)
    scores[1].zero_()  # tie goes to first index, including dependent transitions
    scores[2, :, :, 0] = float("nan")
    scores[2, :, :, 1] = float("-inf")
    scores[2, :, :, 2] = float("inf")
    uniforms = torch.full((3, 7), 0.5, device="cuda", dtype=torch.float32)
    temperatures = torch.ones(3, device="cuda", dtype=torch.float32)
    greedy = torch.ones(3, device="cuda", dtype=torch.int32)
    def select() -> tuple[torch.Tensor, torch.Tensor]:
        return selector_walk_triton(candidate_ids=ids, scores=scores, uniforms=uniforms,
                                    temperatures=temperatures, greedy_mask=greedy)
    tokens, probabilities = select()
    record("selector", {"candidate_ids": ids, "scores": scores, "tokens": tokens,
                        "probabilities": probabilities}, {"mode": "eager"})
    stream = torch.cuda.Stream()
    with torch.cuda.stream(stream):
        select()
    torch.cuda.current_stream().wait_stream(stream)
    graph = torch.cuda.CUDAGraph()
    with torch.cuda.graph(graph):
        graph_tokens, graph_probs = select()
    graph.replay()
    torch.cuda.synchronize()
    record("selector", {"candidate_ids": ids, "scores": scores, "tokens": graph_tokens,
                        "probabilities": graph_probs}, {"mode": "graph"})
    # Each row has a distinct first mismatch. Row7 accepts all seven proposals.
    candidates = torch.arange(64, device="cuda", dtype=torch.int64).reshape(8, 8) + 100
    target = torch.cat((candidates[:, 1:], candidates[:, :1] + 1000), dim=1).contiguous()
    for row in range(7):
        target[row, row] = 2000 + row
    prefix = torch.arange(8, device="cuda", dtype=torch.int32) + 262120
    outputs = [torch.empty(8, device="cuda", dtype=torch.int32) for _ in range(2)]
    outputs.append(torch.empty(8, device="cuda", dtype=torch.int64))
    emitted = torch.empty_like(candidates)
    new_lengths = torch.empty_like(prefix)
    def accept() -> None:
        _compute_dflash_accept_bonus_triton_unchecked(
            candidates, target, *outputs, emitted, prefix, new_lengths,
            bend_policy=policy_rows,
        )
    for mode in ("eager", "graph"):
        if mode == "eager":
            accept()
        else:
            with torch.cuda.stream(stream):
                accept()
            torch.cuda.current_stream().wait_stream(stream)
            accept_graph = torch.cuda.CUDAGraph()
            with torch.cuda.graph(accept_graph):
                accept()
            accept_graph.replay()
        torch.cuda.synchronize()
        record("accept", {"candidates": candidates, "target": target, "prefix": prefix,
                          "accept": outputs[0], "commit": outputs[1], "bonus": outputs[2],
                          "emitted": emitted, "new_lengths": new_lengths}, {"mode": mode})
    # Check the real request stop-token boundary on the kernel's committed prefix.
    # This is not scheduler reclamation or EOS-to-cache lifetime evidence.
    from array import array
    from sglang.srt.managers.schedule_batch import Req
    from sglang.srt.sampling.sampling_params import SamplingParams
    for row in range(8):
        committed = [integer(value) for value in emitted[row, :row + 1].cpu().tolist()]
        for position in range(row + 1):
            eos = committed[position]
            req = Req(rid="numerical-eos", origin_input_text="", origin_input_ids=array("q", [1]),
                      sampling_params=SamplingParams(temperature=0, top_p=1, max_new_tokens=32768),
                      eos_token_ids={eos})
            req.output_ids.extend([2, 3] + committed)
            stopped = req._check_token_based_finish(committed)
            record("eos", {"committed": torch.tensor(committed, dtype=torch.int64)},
                   {"row": row, "position": position, "eos": eos, "prior_length": 2,
                    "stopped": bool(stopped), "finished_len": req.finished_len,
                    "reason": req.finished_reason.to_json() if req.finished_reason else None})


def _embedding_inventory(root: Path, packed: bool) -> dict[str, str]:
    prefix = "model.language_model.embed_tokens."
    index = document(root / "model.safetensors.index.json")
    keys = [prefix + name for name in (("weight_packed", "weight_scale", "weight_shape") if packed else ("weight",))]
    weight_map = mapping(index["weight_map"])
    names = {"config.json", "model.safetensors.index.json"} | {text(weight_map[key]) for key in keys}
    require(all(Path(name).name == name for name in names), "Unsafe model shard path")
    return {name: digest(root / name) for name in sorted(names)}


def _embedding_observations(record: Recorder, packed: Path, dense: Path) -> dict[str, object]:
    """Bind the prepared all-row oracle to the real PackedW8Embedding CUDA API.

    The immutable CPU producer and convert-embedding oracle remain unmodified.
    This is their CUDA observation counterpart, not new embedding arithmetic.
    """
    import torch
    import numpy as np
    from safetensors import safe_open
    from sglang.srt.layers.packed_w8_embedding import PackedW8Embedding

    require(sys.byteorder == "little", "Embedding bitstream requires the pinned little-endian ABI")
    torch.set_default_dtype(torch.bfloat16)
    prefix = "model.language_model.embed_tokens."
    packed_map = _embedding_inventory(packed, True)
    dense_map = _embedding_inventory(dense, False)
    packed_weights = mapping(document(packed / "model.safetensors.index.json")["weight_map"])
    dense_weights = mapping(document(dense / "model.safetensors.index.json")["weight_map"])
    module = PackedW8Embedding()
    for name in ("weight_packed", "weight_scale", "weight_shape"):
        shard = text(packed_weights[prefix + name])
        require(shard in packed_map, "Unbound packed embedding shard")
        with safe_open(str(packed / shard), framework="pt", device="cpu") as handle:
            module.load_tensor(name, handle.get_tensor(prefix + name))
    module.finish_loading()
    module = module.cuda()
    output_hash, reference_hash = hashlib.sha256(), hashlib.sha256()
    dense_shard = text(dense_weights[prefix + "weight"])
    require(dense_shard in dense_map, "Unbound dense embedding shard")
    with safe_open(str(dense / dense_shard), framework="pt", device="cpu") as handle:
        reference = handle.get_slice(prefix + "weight")
        for start in range(0, module.num_embeddings, 512):
            ids = torch.arange(start, min(start + 512, module.num_embeddings), device="cuda", dtype=torch.int64)
            got = module.forward(ids)
            ref = reference[start:start + ids.numel(), :]
            if not isinstance(ref, torch.Tensor):
                raise ValueError("Safetensors embedding slice is not a tensor")
            require(got.dtype == ref.dtype == torch.bfloat16 and got.shape == ref.shape,
                    "Embedding output/reference representation mismatch")
            g = got.detach().cpu().contiguous().view(torch.uint16).numpy().reshape(-1)
            r = ref.contiguous().view(torch.uint16).numpy().reshape(-1)
            gb, rb = memoryview(g).cast("B"), memoryview(r).cast("B")
            output_hash.update(gb)
            reference_hash.update(rb)
            mismatches = np.flatnonzero(g != r)
            positions = mismatches[:16] if mismatches.size else np.array([0, g.size - 1], dtype=np.int64)
            record("embedding", {"ids": ids, "witness_positions": torch.from_numpy(positions),
                   "output_witness": torch.from_numpy(g[positions].copy()),
                   "reference_witness": torch.from_numpy(r[positions].copy())},
                   {"start": start, "rows": module.num_embeddings, "columns": module.embedding_dim,
                    "shape": list(got.shape), "device": str(got.device),
                    "output_dtype": str(got.dtype), "reference_dtype": str(ref.dtype),
                    "output_sha256": hashlib.sha256(gb).hexdigest(),
                    "reference_sha256": hashlib.sha256(rb).hexdigest(),
                    "mismatched_values": int(mismatches.size)})
    return {"output_sha256": output_hash.hexdigest(), "reference_sha256": reference_hash.hexdigest(),
            "rows": module.num_embeddings, "values": module.num_embeddings * module.embedding_dim,
            "algorithm": "sha256/C-order/BF16-little-endian/v1", "chunk_rows": 512}


def _collect(directory: Path, packed: Path, dense: Path) -> int:
    import torch

    record = Recorder(directory)
    suites: dict[str, Suite] = {}
    result: dict[str, object] = {"protocol": PROTOCOL, "events": record.events, "suites": suites, "limitations": LIMITATIONS,
              "runtime": {"torch": str(torch.__version__), "cuda": torch.version.cuda,
                          "cudnn": torch.backends.cudnn.version(),
                          "allow_tf32": torch.backends.cuda.matmul.allow_tf32,
                          "float32_matmul_precision": torch.get_float32_matmul_precision(),
                          "device": torch.cuda.get_device_name(0),
                          "capability": list(torch.cuda.get_device_capability(0))}}
    require(torch.cuda.device_count() == 1, "Exactly one GPU required")
    require(os.environ.get("KVARN_GATHER_CANDIDATE") in (None, ""), "External gather override forbidden")
    require(os.environ.get("TRITON_INTERPRET", "0") == "0", "CUDA evidence cannot use Triton interpreter")
    require(os.environ.get("SGLANG_SIMULATE_ACC_LEN") in (None, "0"), "Simulated acceptance is not numerical evidence")
    (directory / "arrays").mkdir(mode=0o700)
    try:
        for name, source, seed in SUITE_SPECS:
            record.suite = name
            suite: Suite = {"source": source, "seed": seed, "rng": "torch.Generator CUDA Philox; exact installed torch identity",
                            "first_event": len(record.events), "error": None, "exit_code": 1, "event_count": 0}
            suites[name] = suite
            try:
                torch.set_default_dtype(torch.float32)
                if seed is not None:
                    torch.manual_seed(seed)
                if name == "sampler":
                    _greedy_observations(record)
                    code = 0
                elif name == "embedding":
                    before = {"packed": _embedding_inventory(packed, True), "dense": _embedding_inventory(dense, False)}
                    result["embedding_inputs"] = before
                    result["embedding_digest"] = _embedding_observations(record, packed, dense)
                    code = 0
                    require(before == {"packed": _embedding_inventory(packed, True), "dense": _embedding_inventory(dense, False)},
                            "Prepared weights changed during observation")
                else:
                    module = _producer(ROOT / source)
                    setattr(module, "EVIDENCE", record)
                    if name == "commit":
                        observations = sequence(_entry(module, "native_geometry_cases")("cuda", 263168))
                        save(directory / "commit-summary.json", observations)
                        code = 0 if all(mapping(case).get("passed") is True for case in observations) else 1
                    elif name == "native":
                        generator = torch.Generator(device="cuda")
                        generator.manual_seed(20260915)
                        native = _entry(module, "run_native_graph_cases")("cuda", generator, 262144)
                        if not isinstance(native, tuple) or len(native) != 2:
                            raise ValueError("Invalid native producer result")
                        native_cases, boundary = sequence(native[0]), mapping(native[1])
                        save(directory / "native-summary.json", {"cases": native_cases, "boundary": boundary})
                        code = 0 if boundary.get("passed") is True and all(mapping(case).get("passed") is True for case in native_cases) else 1
                    else:
                        code = integer(_entry(module, "main")())
                suite["exit_code"] = code
            except Exception as error:
                suite["error"] = type(error).__name__ + ": " + str(error)
                suite["exit_code"] = 1
                traceback.print_exc()
            suite["event_count"] = len(record.events) - suite["first_event"]
            torch.cuda.empty_cache()
    finally:
        save(directory / "observations.json", result)
    return 0 if len(suites) == len(SUITE_SPECS) and all(s["exit_code"] == 0 and s["event_count"] > 0 for s in suites.values()) else 1


def _numeric(array: NumericArray) -> NumericArray:
    import numpy as np
    # Every uint16 array in this protocol is a raw BF16 tensor, never an index.
    return (array.astype(np.uint32) << 16).view(np.float32) if array.dtype == np.uint16 else array


def _compare(left: NumericArray, right: NumericArray, *, exact: bool = False,
             atol: float = 2**-10, rtol: float = 2**-7, rmse: float | None = None,
             max_abs: float | None = None) -> None:
    import numpy as np
    require(left.shape == right.shape, "Numerical output/reference shapes differ")
    if exact:
        require(left.dtype == right.dtype and np.array_equal(left, right), "Bit-exact numerical mismatch")
    a, b = _numeric(left).astype(np.float64), _numeric(right).astype(np.float64)
    require(np.isfinite(a).all() and np.isfinite(b).all(), "Nonfinite output/reference")
    diff = np.abs(a - b)
    require(np.all(diff <= atol + rtol * np.abs(b)), "Numerical residual exceeds fixed producer tolerance")
    if diff.size:
        if rmse is not None:
            require(float(np.sqrt(np.mean(diff * diff))) <= rmse, "RMSE exceeds fixed producer tolerance")
        if max_abs is not None:
            require(float(diff.max()) <= max_abs, "Maximum residual exceeds fixed producer tolerance")


def _native_reference(meta: Mapping[str, object], arrays: Mapping[str, NumericArray]) -> NumericArray:
    """CPU-only independent unpacking and exact full-history softmax replay."""
    import numpy as np

    require(meta["context"] == 262144 and meta["physical_pages"] == 2057
            and meta["last_page"] == 2056 and meta["window"] in (None, 2048)
            and meta["reference"] == "pytorch_dequantized_kv_full_multiplicity",
            "Missing exact native attention geometry/reference")
    for name, shape, dtype in (
        ("q", (8, 24, 256), np.uint16), ("table", (1, 2056), np.int32),
        ("requests", (8,), np.int32), ("lower", (8,), np.int32), ("upper", (8,), np.int32),
        ("page_kinds", (2048,), np.int64), ("counts", (8, 3, 128), np.int64),
        ("packed_tiles", (2, 4, 26880), np.uint8),
        ("raw_keys", (128, 4, 256), np.uint16), ("raw_values", (128, 4, 256), np.uint16),
        ("decoded_keys", (3, 128, 4, 256), np.float32),
        ("decoded_values", (3, 128, 4, 256), np.float32),
        ("output", (8, 24, 256), np.uint16), ("eager", (8, 24, 256), np.uint16),
        ("reference", (8, 24, 256), np.uint16),
    ):
        require(arrays[name].shape == shape and arrays[name].dtype == dtype,
                "Native attention array representation mismatch: " + name)
    table = np.zeros((1, 2056), dtype=np.int32)
    table[0, :2048] = np.arange(2, 2050, dtype=np.int32)
    table[0, 2047] = 2056
    kinds = np.concatenate((np.zeros(1024, dtype=np.int64),
                            np.ones(1023, dtype=np.int64), np.array([2], dtype=np.int64)))
    upper = np.arange(262137, 262145, dtype=np.int32)
    lower = np.zeros(8, dtype=np.int32) if meta["window"] is None else upper - 2048
    require(np.array_equal(arrays["table"], table) and np.array_equal(arrays["page_kinds"], kinds)
            and np.array_equal(arrays["lower"], lower) and np.array_equal(arrays["upper"], upper)
            and not np.any(arrays["requests"]), "Native history mapping or visibility changed")
    counts = np.zeros((8, 3, 128), dtype=np.int64)
    for row in range(8):
        lo, hi = int(lower[row]), int(upper[row])
        for logical in range(lo // 128, (hi + 127) // 128):
            start, end = max(lo - logical * 128, 0), min(hi - logical * 128, 128)
            counts[row, int(kinds[logical]), start:end] += 1
    require(np.array_equal(arrays["counts"], counts)
            and np.array_equal(counts.sum(axis=(1, 2)), upper - lower),
            "Oracle omits visible native history")

    def hadamard(value: NumericArray) -> NumericArray:
        result = value.astype(np.float32, copy=True)
        stride = 1
        while stride < 256:
            blocks = result.reshape(128, 256 // (2 * stride), 2, stride)
            left, right = blocks[..., 0, :].copy(), blocks[..., 1, :].copy()
            blocks[..., 0, :], blocks[..., 1, :] = left + right, left - right
            stride *= 2
        return result / 16

    keys = np.empty((3, 128, 4, 256), dtype=np.float32)
    values = np.empty_like(keys)
    for tile in range(2):
        for head in range(4):
            packed = arrays["packed_tiles"][tile, head]
            kbytes = packed[:16384].reshape(256, 64)
            kq = np.stack((kbytes & 15, kbytes >> 4), axis=-1).reshape(256, 128).astype(np.float32)
            ks = packed[16384:16896].view("<f2").astype(np.float32)
            kz = packed[16896:17408].view("<f2").astype(np.float32)
            kt = packed[17408:17664].view("<f2").astype(np.float32)
            vbytes = packed[17664:25856].reshape(128, 64)
            vq = np.stack(tuple((vbytes >> shift) & 3 for shift in (0, 2, 4, 6)),
                          axis=-1).reshape(128, 256).astype(np.float32)
            vc = packed[25856:26368].view("<f2").astype(np.float32)
            vs = packed[26368:26624].view("<f2").astype(np.float32)
            vz = packed[26624:26880].view("<f2").astype(np.float32)
            keys[tile, :, head] = hadamard(((kq * ks[:, None] + kz[:, None]) * kt[None, :]).T)
            values[tile, :, head] = hadamard((vq * vs[:, None] + vz[:, None]) * vc[None, :])
    keys[2], values[2] = _numeric(arrays["raw_keys"]), _numeric(arrays["raw_values"])
    _compare(arrays["decoded_keys"], keys)
    _compare(arrays["decoded_values"], values)
    require(np.isfinite(keys).all() and np.isfinite(values).all(), "Nonfinite packed oracle")
    pattern = -(1 + np.arange(256, dtype=np.float32) % 8 / 16) / 4
    require(np.array_equal(values[2], np.broadcast_to(pattern, (128, 4, 256))),
            "Lost deterministic native tail signal")
    q = _numeric(arrays["q"]).astype(np.float64)
    require(np.isfinite(q).all() and not np.any(q[0]), "Missing equal-mass native witness")
    result = np.empty((8, 24, 256), dtype=np.float32)
    for row in range(8):
        active = counts[row].reshape(-1) > 0
        multiplicity = counts[row].reshape(-1)[active].astype(np.float64)
        for head in range(24):
            kv_head = head // 6
            k = keys[:, :, kv_head].reshape(-1, 256)[active].astype(np.float64)
            v = values[:, :, kv_head].reshape(-1, 256)[active].astype(np.float64)
            scores = k @ q[row, head] / 16 + np.log(multiplicity)
            weights = np.exp(scores - scores.max())
            result[row, head] = weights @ v / weights.sum()
    # Match the declared BF16 result boundary, not a relaxed FP32 residual.
    bits = result.view(np.uint32)
    rounded = ((bits + 0x7FFF + ((bits >> 16) & 1)) >> 16).astype(np.uint16)
    require(np.min(np.abs(_numeric(rounded)[0])) > 0.125,
            "Zero output would pass native signal witness")
    return rounded


def _replay_event(event: Event, arrays: Mapping[str, NumericArray]) -> None:
    import numpy as np
    kind, meta = event["kind"], event["metadata"]
    if kind == "native_context":
        require(integer(meta["status"]) == integer(meta["eager_status"]) == integer(meta["write_status"]) == 0
                and meta["passed"] is True, "Native full-history producer failed")
        reference = _native_reference(meta, arrays)
        for name in ("reference", "eager", "output"):
            _compare(arrays[name], reference, rmse=2**-11)
        return
    if kind == "native_context_status":
        require(meta["context"] == 262144 and meta["physical_pages"] == meta["invalid_page"] == 2057
                and integer(meta["rejected_status"]) & 1 and integer(meta["sticky_status"]) & 1
                and meta["passed"] is True, "Native physical-page rejection/stickiness missing")
        require(arrays["table"].shape == (1, 2056) and arrays["table"][0, 2047] == 2056
                and np.array_equal(arrays["upper"], np.arange(262137, 262145))
                and np.array_equal(arrays["lower"], arrays["upper"] - 2048),
                "Native status graph inputs changed")
        return
    if kind in {"prefill", "nosync", "flash"}:
        require(integer(meta["status"]) == 0 and integer(meta.get("write_status", 0)) == 0, "Attention native status failure")
        out, ref = arrays["output"], arrays["reference"]
        require(arrays["q"].shape == out.shape and out.ndim == 3 and out.shape[1:] == (24, 256)
                and 1 <= out.shape[0] <= 8 and ref.ndim == 3 and ref.shape[1:] == (24, 256)
                and len(ref) == len(arrays["lower"]) == len(arrays["upper"])
                and arrays["table"].shape == (1, 2057), "Attention fixture geometry missing")
        if kind == "nosync":
            require(not np.any(out[len(ref):]), "Padded attention rows must be exactly zero")
            out = out[:len(ref)]
        _compare(out, ref, rtol=2**-7 + (2**-8 if kind == "flash" else 0),
                 rmse=0.0005 if kind == "flash" else 2**-11 if kind == "prefill" else None,
                 max_abs=0.02 if kind == "flash" else None)
        dead = arrays["upper"] <= arrays["lower"]
        require(not np.any(out[dead]), "Dead attention rows must be exactly zero")
    elif kind == "prefill_status":
        require(integer(meta["status"]) == (0 if meta["bad_page"] is None else 1), "Invalid page status mismatch")
    elif kind in {"gather", "gather_graph"}:
        require(integer(meta["status"]) == 0 and integer(meta.get("replay_status", 0)) == 0, "Gather status failure")
        require(arrays["locations"].ndim == 2 and arrays["locations"].size == 2184
                and arrays["lengths"].shape == (len(arrays["locations"]),), "Gather fixture geometry missing")
        require(arrays["locations"].dtype in (np.int32, np.int64)
                and arrays["lengths"].dtype in (np.int32, np.int64)
                and np.all(arrays["lengths"] >= 0)
                and np.all(arrays["lengths"] <= arrays["locations"].shape[1]),
                "Gather lengths/locations must be bounded integers")
        for field in ("keys", "values"):
            require(arrays[field].shape == (*arrays["locations"].shape, 8, 128), "Gather KV tensor missing")
            _compare(arrays[field], arrays["reference_" + field])
            for row, length in enumerate(arrays["lengths"]):
                require(not np.any(arrays[field][row, int(length):]), "Gather padding is not zero")
            if kind == "gather_graph":
                _compare(arrays[field], arrays["replay_" + field], exact=True)
    elif kind == "gather_invalid":
        require(integer(meta["status"]) & 1 and text(meta["oracle_error"]) != "", "Invalid gather did not fail closed against eager oracle")
    elif kind == "gather_sticky":
        require(meta == {"valid": 2, "invalid": 3}, "Gather lost sticky error bits")
    elif kind in {"capture_prefix", "commit"}:
        require(integer(meta["capacity"]) == 263168
                and integer(meta["target_status"]) == integer(meta["draft_status"]) == 0,
                "Native commit geometry/status mismatch")
        if kind == "capture_prefix":
            fields = [key.removeprefix("before/") for key in arrays if key.startswith("before/")]
            require(len(fields) == 16 * 5, "Missing target prefix layers")
            for field in fields:
                _compare(arrays["before/" + field], arrays["after/" + field], exact=True)
            for layer in range(16):
                require(arrays[f"before/{layer}/keys"].shape == arrays[f"before/{layer}/values"].shape == (1, 4, 256)
                        and int(arrays[f"before/{layer}/mask"].sum()) == 1,
                        "Capture neutrality must retain a nonempty committed prefix")
        else:
            accepted, offset, page = integer(meta["accepted"]), integer(meta["offset"]), integer(meta["page"])
            pages = [integer(value) for value in sequence(meta["pages"])]
            require(0 <= accepted <= 8 and (offset, page, pages) in (
                (120, 2056, [2056]), (124, 2055, [2055, 2056])),
                "Commit fixture is not native last-page/crossing boundary")
            require(meta["statuses"] == [{"target": 0, "draft": 0}] * 2, "Eager/graph commit status missing")
            first = page * 128 + offset
            require(np.array_equal(arrays["locations"], np.arange(first, first + 8).reshape(1, 8))
                    and np.array_equal(arrays["positions"], np.arange(262136, 262144).reshape(1, 8))
                    and arrays["hidden"].shape == (8, 512), "Commit input binding changed")
            for page_index, physical in enumerate(pages):
                expected = np.zeros(128, dtype=np.bool_)
                for location in range(first, first + accepted):
                    if location // 128 == physical:
                        expected[location % 128] = True
                rows = int(expected.sum())
                for layer in range(21):
                    index = page_index * 21 + layer
                    for mode in ("eager", "graph"):
                        require(np.array_equal(arrays[f"{mode}/{index}/mask"], expected), "Commit mask differs from accepted prefix")
                        for field in ("keys", "values"):
                            value = arrays[f"{mode}/{index}/{field}"]
                            require(value.shape == (
                                rows, 4 if layer < 16 else 8, 256 if layer < 16 else 128),
                                "Committed KV missing its accepted-prefix backing tensors")
                    for field in ("mask", "provisional", "length", "keys", "values"):
                        _compare(arrays[f"eager/{index}/{field}"], arrays[f"graph/{index}/{field}"],
                                 exact=field not in ("keys", "values"))
                    expected_length = int(np.flatnonzero(expected)[-1]) + 1 if rows else 0
                    for mode in ("eager", "graph"):
                        require(arrays[f"{mode}/{index}/provisional"].shape == (128,)
                                and arrays[f"{mode}/{index}/provisional"].dtype == np.bool_
                                and not np.any(arrays[f"{mode}/{index}/provisional"])
                                and arrays[f"{mode}/{index}/length"].shape == ()
                                and arrays[f"{mode}/{index}/length"] == expected_length,
                                "Commit retained rejected rows or wrong valid extent")
    elif kind == "embedding":
        require(integer(meta["rows"]) == 248320 and integer(meta["columns"]) == 5120 and meta["output_dtype"] == meta["reference_dtype"] == "torch.bfloat16", "Wrong embedding representation")
        start = integer(meta["start"])
        require(np.array_equal(arrays["ids"], np.arange(start, start + len(arrays["ids"]))), "Embedding row omission/reordering")
        require(len(arrays["ids"]) == 512 and meta["shape"] == [512, 5120], "Embedding chunk shape mismatch")
        require(len(text(meta["output_sha256"])) == 64
                and meta["output_sha256"] == meta["reference_sha256"] and meta["mismatched_values"] == 0,
                "Embedding all-value bitstream mismatch")
        _compare(arrays["output_witness"], arrays["reference_witness"], exact=True)
        require(np.all(arrays["witness_positions"] >= 0) and np.all(arrays["witness_positions"] < 512 * 5120),
                "Embedding witness position outside chunk")
        require(meta["device"] == "cuda:0", "Embedding forward did not execute on CUDA")
    elif kind == "selector":
        ids, scores = arrays["candidate_ids"], arrays["scores"]
        require(ids.shape == (3, 7, 4) and scores.shape == (3, 7, 4, 4), "Selector fixture geometry mismatch")
        fixture_ids = np.arange(3 * 7 * 4, dtype=np.int64).reshape(3, 7, 4) + 10
        fixture_scores = (np.arange(3 * 7 * 4 * 4, dtype=np.float32).reshape(3, 7, 4, 4) % 11)
        fixture_scores[1] = 0
        fixture_scores[2, :, :, 0] = np.nan
        fixture_scores[2, :, :, 1] = -np.inf
        fixture_scores[2, :, :, 2] = np.inf
        require(np.array_equal(ids, fixture_ids) and np.array_equal(scores, fixture_scores, equal_nan=True),
                "Selector lost deterministic tie/nonfinite/dependent-transition inputs")
        scores = np.clip(np.where(np.isnan(scores), -1e30, scores), np.float32(-1e30), np.float32(1e30))
        expected = np.empty((3, 7), dtype=np.int64)
        probabilities = np.zeros((3, 7, 4), dtype=np.float32)
        for row in range(3):
            previous = 0
            for slot in range(7):
                previous = int(np.argmax(scores[row, slot, previous]))
                expected[row, slot] = ids[row, slot, previous]
                probabilities[row, slot, previous] = 1
        _compare(arrays["tokens"], expected, exact=True)
        _compare(arrays["probabilities"], probabilities, exact=True)
    elif kind == "accept":
        candidates, target, prefix = arrays["candidates"], arrays["target"], arrays["prefix"]
        require(candidates.shape == target.shape == (8, 8) and prefix.shape == (8,), "Greedy acceptance fixture geometry mismatch")
        require(np.array_equal(candidates, np.arange(64).reshape(8, 8) + 100)
                and np.array_equal(prefix, np.arange(8) + 262120),
                "Greedy fixture candidates/native prefix changed")
        for row in range(8):
            length = 0
            while length < 7 and candidates[row, length + 1] == target[row, length]:
                length += 1
            require(length == row, "Missing rejection position/all-accepted fixture")
            bonus = target[row, length]
            require(arrays["accept"][row] == length and arrays["commit"][row] == length + 1
                    and arrays["bonus"][row] == bonus and arrays["new_lengths"][row] == prefix[row] + length + 1,
                    "Greedy acceptance/bonus/commit alignment mismatch")
            expected = np.concatenate((candidates[row, 1:1 + length], [bonus]))
            require(np.array_equal(arrays["emitted"][row, :length + 1], expected), "Committed emitted token prefix mismatch")
    elif kind == "eos":
        committed = arrays["committed"]
        row, position = integer(meta["row"]), integer(meta["position"])
        require(committed.shape == (row + 1,) and 0 <= position < len(committed),
                "EOS case missing committed proposal/bonus prefix")
        first = next((i for i, token in enumerate(committed) if token == integer(meta["eos"])), None)
        if first is None:
            raise ValueError("EOS absent from committed prefix")
        require(first == position and meta["stopped"] is True
                and integer(meta["finished_len"]) == integer(meta["prior_length"]) + first + 1
                and meta["reason"] == {"type": "stop", "matched": meta["eos"]},
                "EOS boundary differs from first stop token in committed prefix")
    else:
        raise ValueError("Unrecognized numerical observation: " + kind)


def verify_report(report_path: Path, serving_identity: dict[str, object]) -> dict[str, object]:
    """Replay retained arrays with fixed gates; never execute code from a report."""
    try:
        import numpy as np
    except ImportError as error:
        raise ValueError("Numerical replay needs NumPy; use eval/.venv/bin/python") from error
    report = document(report_path)
    require(report.get("protocol") == PROTOCOL and report.get("producer") == "bench.numerical", "Unknown numerical producer")
    require(report.get("native_exit_code") == 0, "Numerical producer failed; inspect retained stdout/stderr and observations")
    require(report.get("serving_recipe") == recipe(serving_identity), "Numerical evidence belongs to another serving recipe/component ABI")
    expected_identity = mapping(report["diagnostic_identity"])
    for name in ("image_sha256", "engine_base_commit", "ordered_patch_sha256", "container_env"):
        require(expected_identity[name] == serving_identity[name], "Diagnostic image/patch/settings mismatch: " + name)
    require(report["components_before"] == report["components_after"] == serving_identity["component_identity"], "Installed numerical components/ABI/hardware changed")
    root = report_path.parent
    paths: set[str] = set()
    for value in sequence(report["artifacts"]):
        item = mapping(value)
        name = text(item["path"])
        require(name != "" and not Path(name).is_absolute() and ".." not in Path(name).parts,
                "Unsafe artifact path")
        path = root / name
        require(Path(name).as_posix() == name
                and name not in paths and path.is_file() and not any(p.is_symlink() for p in (path, *path.parents)), "Unsafe or duplicate artifact")
        require(path.stat().st_size == integer(item["size_bytes"]) and digest(path) == text(item["sha256"]), "Altered numerical artifact: " + name)
        paths.add(name)
    require(paths == {p.relative_to(root).as_posix() for p in root.rglob("*") if p.is_file() and p != report_path}, "Numerical artifact closure differs")
    for source in SOURCES:
        require("sources/" + source in paths and digest(root / "sources" / source) == digest(ROOT / source), "Unrecognized numerical producer source: " + source)
    observations = document(root / "observations.json")
    require(observations["protocol"] == PROTOCOL, "Wrong observation schema")
    components = mapping(report["components_before"])
    runtime = mapping(observations["runtime"])
    packages = mapping(components["packages"])
    require(runtime["capability"] == [8, 6]
            and runtime["device"] == mapping(components["gpu"])["name"]
            and runtime["torch"] == mapping(packages["torch"])["version"],
            "Observed CUDA runtime does not match captured SM86 ABI")
    suites = {name: mapping(value) for name, value in mapping(observations["suites"]).items()}
    require(set(suites) == {name for name, _, _ in SUITE_SPECS}, "Missing numerical suite")
    events: list[Event] = []
    for value in sequence(observations["events"]):
        entry = mapping(value)
        require(set(entry) == {"suite", "kind", "arrays", "metadata"}, "Invalid numerical event schema")
        events.append({"suite": text(entry["suite"]), "kind": text(entry["kind"]),
                       "arrays": text(entry["arrays"]), "metadata": mapping(entry["metadata"])})
    require(len(events) > 0 and all(integer(s["exit_code"]) == 0 and s["error"] is None
            and integer(s["event_count"]) > 0 for s in suites.values()), "Missing/failed/inconclusive numerical suite")
    require([event["arrays"] for event in events] == [f"arrays/{i:05d}.npz" for i in range(len(events))],
            "Duplicate, reordered or omitted numerical array payload")
    def load(index: int) -> dict[str, NumericArray]:
        require(0 <= index < len(events), "Observation index outside schedule")
        event = events[index]
        require(event["arrays"] in paths and event["arrays"].endswith(".npz"), "Missing safe array file")
        archive = np.load(root / event["arrays"], allow_pickle=False)
        if not isinstance(archive, np.lib.npyio.NpzFile):
            raise ValueError("Expected numerical array archive")
        result: dict[str, NumericArray] = {}
        with archive:
            require(len(archive.files) == len(set(archive.files)), "Duplicate array payload")
            for key in archive.files:
                value = archive[key]
                require(value.dtype in (np.bool_, np.int8, np.int16, np.int32, np.int64,
                        np.uint8, np.uint16, np.uint32, np.uint64, np.float16, np.float32, np.float64),
                        "Non-native numeric evidence array")
                result[key] = value
        return result

    counts: dict[str, int] = {}
    for index, event in enumerate(events):
        require(event["suite"] in suites, "Unbound numerical observation")
        counts[event["kind"]] = counts.get(event["kind"], 0) + 1
        try:
            _replay_event(event, load(index))
        except (ValueError, KeyError, IndexError, TypeError) as error:
            raise ValueError(f"Numerical observation {index} ({event['kind']}): {error}") from error
    require(counts == {"prefill": 9, "prefill_status": 3, "nosync": 4, "flash": 2,
                       "gather": 4, "gather_invalid": 5, "gather_graph": 1, "gather_sticky": 1,
                       "native_context": 2, "native_context_status": 1,
                       "capture_prefix": 1, "commit": 18, "selector": 2, "accept": 2, "eos": 36,
                       "embedding": 485}, "Incomplete finite numerical case matrix")
    cursor = 0
    suite_kinds = {
        "prefill": {"prefill", "prefill_status"}, "attention": {"nosync", "flash"},
        "native": {"native_context", "native_context_status"},
        "storage": {"gather", "gather_invalid", "gather_graph", "gather_sticky"},
        "commit": {"capture_prefix", "commit"}, "sampler": {"selector", "accept", "eos"},
        "embedding": {"embedding"},
    }
    for suite, expected_source, expected_seed in SUITE_SPECS:
        values = suites[suite]
        first, count = integer(values["first_event"]), integer(values["event_count"])
        require(first == cursor and 0 < count <= len(events) - cursor, "Suite event interval missing/reordered")
        subset = events[first:first + count]
        require(all(event["suite"] == suite and event["kind"] in suite_kinds[suite] for event in subset),
                "Suite event interval mismatch")
        require(values["source"] == expected_source and values["seed"] == expected_seed,
                "Fixture source/seed differs from finite producer schedule")
        cursor += count
    require(cursor == len(events), "Unclaimed numerical events")
    for kind, names in {
        "nosync": ["mixed_live_dead", "graph_padding", "all_dead", "all_live_verify_block"],
        "flash": ["multi_chunk_130_pages", "single_chunk_control"],
        "gather": ["full_window_mixed_raw_packed", "two_rows_mixed_lengths", "padding_heavy_short_prefix", "zero_length_row"],
        "gather_invalid": ["invalid_unwritten_token", "invalid_page_zero", "invalid_page_out_of_range",
                           "invalid_negative_length", "invalid_length_over_width"],
    }.items():
        require([e["metadata"]["case"] for e in events if e["kind"] == kind] == names,
                "Missing required numerical case: " + kind)
    prefill = [e["metadata"] for e in events if e["kind"] == "prefill"]
    require(prefill[0].get("kind") == "serving_first_chunk"
            and [(m["pages"], m["raw_tail"], m["queries"], m["empty_rows"]) for m in prefill[1:]]
            == [(1, False, 8, []), (2, True, 8, []), (3, False, 8, []), (5, True, 8, []),
                (9, False, 8, []), (17, True, 8, []), (17, True, 5, []), (17, True, 8, [2, 6])],
            "Missing prefill raw/packed/padded/empty boundary fixture")
    require([e["metadata"]["bad_page"] for e in events if e["kind"] == "prefill_status"] == [0, 29, None],
            "Missing prefill native status boundary fixture")
    for kind in ("selector", "accept"):
        require([e["metadata"]["mode"] for e in events if e["kind"] == kind] == ["eager", "graph"], "Missing eager/graph sampler execution")
    require([(e["metadata"]["offset"], e["metadata"]["accepted"]) for e in events if e["kind"] == "commit"]
            == [(offset, accepted) for offset in (120, 124) for accepted in range(9)], "Missing commit boundary")
    native_indices = [i for i, event in enumerate(events) if event["kind"] == "native_context"]
    require([events[index]["metadata"]["window"] for index in native_indices] == [None, 2048],
            "Missing full-native and bounded-window oracle")
    full, window = (load(index) for index in native_indices)
    for field in ("q", "table", "requests", "upper", "packed_tiles", "raw_keys", "raw_values",
                  "page_kinds", "decoded_keys", "decoded_values"):
        _compare(full[field], window[field], exact=True)
    require(np.min(np.abs(_numeric(full["reference"])[0] - _numeric(window["reference"])[0])) > 0.25,
            "Native oracle cannot reject dropped far history")
    require([e["metadata"]["start"] for e in events if e["kind"] == "embedding"] == list(range(0, 248320, 512)), "Incomplete all-row embedding evidence")
    require([(e["metadata"]["row"], e["metadata"]["position"]) for e in events if e["kind"] == "eos"]
            == [(row, position) for row in range(8) for position in range(row + 1)], "Missing EOS proposal/bonus boundary")
    graph_accept = load(next(i for i, e in enumerate(events) if e["kind"] == "accept" and e["metadata"]["mode"] == "graph"))
    for index, event in enumerate(events):
        if event["kind"] == "eos":
            row = integer(event["metadata"]["row"])
            require(np.array_equal(load(index)["committed"], graph_accept["emitted"][row, :row + 1]),
                    "EOS boundary not bound to actual observed committed token prefix")
    inventories = {name: mapping(value) for name, value in mapping(observations["embedding_inputs"]).items()}
    model_inventory = mapping(serving_identity["model_inventory"])
    target_inventory = mapping(model_inventory["target"])
    require(set(inventories) == {"packed", "dense"} and all(
        set(inventory) == {"config.json", "model.safetensors.index.json", "model-00006-of-00007.safetensors"}
        for inventory in inventories.values()), "Incomplete immutable embedding input inventory")
    require(all(target_inventory.get(name) == sha for name, sha in inventories["packed"].items()), "Embedding weights differ from served prepared target")
    approved: dict[str, str] = {}
    for line in (root / "sources/prepare/artifact.sha256").read_text().splitlines():
        if line.strip() == "":
            continue
        parts = line.split()
        require(len(parts) == 2, "Invalid prepared artifact inventory")
        name = parts[1].removeprefix("*")
        require(name not in approved, "Duplicate prepared artifact inventory entry")
        approved[name] = parts[0]
    for name, sha in inventories["dense"].items():
        require(approved.get(name) == sha, "Dense embedding reference differs from prepared immutable artifact")
    embedding_digest = mapping(observations["embedding_digest"])
    expected_embedding = document(root / "sources/prepare/embedding-validation.json")
    require(embedding_digest["rows"] == 248320 and embedding_digest["values"] == 1271398400
            and embedding_digest["chunk_rows"] == 512
            and embedding_digest["algorithm"] == "sha256/C-order/BF16-little-endian/v1"
            and embedding_digest["output_sha256"] == embedding_digest["reference_sha256"]
            == expected_embedding["dense_embedding_sha256"],
            "Embedding complete observed bitstream differs from immutable prepared dense oracle")
    return {"coverage": ["kvarn_attention", "kvarn_native_context", "kvarn_storage", "packed_embedding", "dflash_commit", "dflash_sampler"],
            "scope": "standalone components, exact greedy recipe only", "events_replayed": len(events),
            "limitations": LIMITATIONS, "protocol": PROTOCOL}


def _docker(*args: str, timeout: int = 600) -> str:
    return subprocess.run(["docker", *args], check=True, capture_output=True, text=True, timeout=timeout).stdout.strip()


def run(args: argparse.Namespace) -> int:
    from bench.decode import container_identity
    options: dict[str, object] = vars(args)
    output, identity_path, packed, dense = (
        options[name] for name in ("output", "identity", "packed", "dense"))
    if not isinstance(output, Path) or not isinstance(identity_path, Path):
        raise ValueError("Expected output and identity paths")
    if not isinstance(packed, Path) or not isinstance(dense, Path):
        raise ValueError("Expected packed and dense paths")
    container = text(options["container"])
    directory = output.absolute()
    directory.mkdir(mode=0o700, parents=False, exist_ok=False)
    report: dict[str, object] = {"protocol": PROTOCOL, "producer": "bench.numerical", "native_exit_code": 1}
    identity: dict[str, object] = {}
    try:
        envelope = document(identity_path)
        identity = mapping(envelope["identity"])
        require(envelope.get("producer") == "serve.qualification.capture", "Expected authenticated serving capture")
        report["serving_recipe"] = recipe(identity)
        actual = container_identity(container)
        report["diagnostic_identity"] = actual
        for name in ("image_sha256", "engine_base_commit", "ordered_patch_sha256", "container_env"):
            require(actual[name] == identity[name], "Idle diagnostic differs from serving capture: " + name)
        identifier = text(actual["container_id"])
        capture = inspect.getsource(runtime_components) + "\nimport json\nprint(json.dumps(runtime_components(),sort_keys=True))"
        before: object = json.loads(_docker("exec", identifier, "python3", "-c", capture, timeout=600))
        report["components_before"] = mapping(before)
        require(report["components_before"] == identity["component_identity"], "Standalone numerical ABI differs from serving ABI")
        for source in SOURCES:
            target = directory / "sources" / source
            target.parent.mkdir(mode=0o700, parents=True, exist_ok=True)
            with target.open("xb") as stream:
                stream.write((ROOT / source).read_bytes())
        save(directory / "serving-capture.json", envelope)
        # The absolute output parent MUST be bound at the identical path in the idle container.
        command = ["docker", "exec", "-e", "PYTHONDONTWRITEBYTECODE=1", identifier,
                   "python3", str(directory / "sources/bench/numerical.py"), "_collect",
                   "--output", str(directory), "--packed", str(packed), "--dense", str(dense)]
        with (directory / "producer.stdout").open("xb") as stdout, (directory / "producer.stderr").open("xb") as stderr:
            completed = subprocess.run(command, stdout=stdout, stderr=stderr, check=False)
        report["native_exit_code"] = completed.returncode
        after: object = json.loads(_docker("exec", identifier, "python3", "-c", capture, timeout=600))
        report["components_after"] = mapping(after)
    except Exception as error:
        report["error"] = type(error).__name__ + ": " + str(error)
    report["artifacts"] = tree(directory)
    save(directory / "report.json", report)
    try:
        replay = verify_report(directory / "report.json", identity)
    except Exception as error:
        print(f"Numerical evidence rejected: {error}; retained {directory}", file=sys.stderr)
        return 1
    print(json.dumps(replay, sort_keys=True))
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    collect = sub.add_parser("_collect")
    collect.add_argument("--output", type=Path, required=True)
    collect.add_argument("--packed", type=Path, required=True)
    collect.add_argument("--dense", type=Path, required=True)
    runner = sub.add_parser("run")
    runner.add_argument("--container", required=True)
    runner.add_argument("--identity", type=Path, required=True)
    runner.add_argument("--output", type=Path, required=True)
    runner.add_argument("--packed", type=Path, required=True)
    runner.add_argument("--dense", type=Path, required=True)
    replay = sub.add_parser("verify")
    replay.add_argument("--report", type=Path, required=True)
    replay.add_argument("--identity", type=Path, required=True)
    args = parser.parse_args()
    options: dict[str, object] = vars(args)
    if options["command"] == "_collect":
        output, packed, dense = (options[name] for name in ("output", "packed", "dense"))
        if not isinstance(output, Path) or not isinstance(packed, Path) or not isinstance(dense, Path):
            raise ValueError("Expected collection paths")
        return _collect(output, packed, dense)
    if options["command"] == "run":
        return run(args)
    try:
        report_path, identity_path = options["report"], options["identity"]
        if not isinstance(report_path, Path) or not isinstance(identity_path, Path):
            raise ValueError("Expected replay paths")
        print(json.dumps(verify_report(report_path, mapping(document(identity_path)["identity"])), sort_keys=True))
    except (ValueError, KeyError, OSError, TypeError) as error:
        print(str(error), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
