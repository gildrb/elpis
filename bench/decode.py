# Copyright (c) 2026 inference contributors.
"""Single-request C1 decode-rate depth matrix; see docs/decode-bottlenecks.md.

Engineering measurement, not a quality score. Natural runs use the frozen chat
prompts from bench/throughput-prompts.jsonl padded to each requested input
depth and stop at their own EOS; committed tokens are counted from the
server's usage counter, not from streamed chunk counts.
"""

import argparse
import hashlib
import http.client
import json
import os
import re
import subprocess
import signal
import sys
import time
from pathlib import Path
from urllib.parse import urlsplit

from bench import cache
from bench.power import PowerSampler

DEPTHS = (1024, 8192, 32768)
OUTPUT_TOKENS = 1024
INSTRUCTION = (
    "End of reference material. Write a careful technical summary of the main "
    "ideas above, then give one original worked Python example with tests."
)
PROMPTS_FILE = Path(__file__).parent / "throughput-prompts.jsonl"
CONTAINER = "qwen-inference-inference-1"
SCHEMA_VERSION = 2
WORKLOAD_SCHEMA_VERSION = 2
MEASUREMENT_PROTOCOL = "sglang-continuous-usage-counter-delta-v2"


def canonical_bytes(value: object) -> bytes:
    """Canonical UTF-8 JSON used for replayable request and workload digests."""
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False, allow_nan=False).encode()


def artifact(directory: Path, path: Path) -> dict[str, object]:
    """Describe exact private artifact bytes, relative to the report directory."""
    raw = path.read_bytes()
    return {"path": path.relative_to(directory).as_posix(), "sha256": hashlib.sha256(raw).hexdigest(), "size_bytes": len(raw)}


def artifacts(directory: Path) -> list[dict[str, object]]:
    """Index completed artifacts without making a self-referential report hash."""
    return [artifact(directory, path) for path in sorted(directory.rglob("*")) if path.is_file()]


def capture_identity(directory: Path, container: str, endpoint: str, key_file: str, *, after: bool = False, native_exit_code: int = 0) -> dict[str, object]:
    """Use the qualification CLI's verified native identity, never a declaration."""
    name = "identity-after" if after else "identity-before"
    command = [
        sys.executable, "-m", "serve.qualification", "capture",
        "--container", container, "--base-url", endpoint,
        "--key-file", key_file, "--output", str(directory / f"{name}.json"),
    ]
    if after:
        command.extend(["--match", str(directory / "identity-before.json"), "--native-exit-code", str(native_exit_code)])
    with (directory / f"{name}.stdout").open("xb") as stdout, (directory / f"{name}.stderr").open("xb") as stderr:
        result = subprocess.run(command, stdout=stdout, stderr=stderr, check=False)
    if result.returncode:
        raise cache.BenchError(f"{name} capture or candidate match failed")
    envelope = cache.mapping(json.loads(
        (directory / f"{name}.json").read_bytes(), object_pairs_hook=cache.json_object,
        parse_float=cache.json_float, parse_constant=cache.json_constant,
    ))
    if envelope.get("producer") != "serve.qualification.capture" or envelope.get("schema_version") != 1:
        raise cache.BenchError("invalid rich identity envelope")
    return cache.mapping(envelope.get("identity"))


def snapshot_sources(directory: Path, names: tuple[str, ...]) -> list[dict[str, object]]:
    """Freeze measurement code/corpus bytes before making endpoint requests."""
    result: list[dict[str, object]] = []
    root = Path(__file__).resolve().parent.parent
    for name in names:
        target = directory / "sources" / name
        target.parent.mkdir(mode=0o700, parents=True, exist_ok=True)
        with target.open("xb") as handle:
            handle.write((root / name).read_bytes())
        result.append(artifact(directory, target))
    return result


def failure(directory: Path, error: Exception) -> None:
    """Preserve completed evidence and a sanitized rejection, without overwrites."""
    cache.save(directory, "failure.json", {
        "status": "rejected", "reason": str(error) if isinstance(error, cache.BenchError) else type(error).__name__,
        "artifacts": artifacts(directory),
    })

def spec_gauges(port: int, key: str) -> dict[str, float]:
    """Read Prometheus speculation gauges from the authenticated endpoint."""
    connection = http.client.HTTPConnection("127.0.0.1", port, timeout=30)
    try:
        connection.request("GET", "/metrics", headers={"Authorization": "Bearer " + key})
        response = connection.getresponse()
        if response.status != cache.HTTP_OK:
            raise cache.BenchError(f"metrics status {response.status}")
        text = response.read(16 * 1024 * 1024).decode()
    finally:
        connection.close()
    values: dict[str, float] = {}
    for line in text.splitlines():
        if not line.startswith("sglang:"):
            continue
        name = line.split("{", 1)[0]
        try:
            values[name] = float(line.rsplit(" ", 1)[1])
        except (IndexError, ValueError):
            continue
    return values


def container_identity(container: str) -> dict[str, object]:
    """Read identity from the selected running container, never the worktree."""
    def docker(*arguments: str) -> str:
        try:
            result = subprocess.run(
                ["docker", *arguments],
                capture_output=True, text=True, timeout=30, check=True,
            )
        except (OSError, subprocess.SubprocessError) as error:
            raise cache.BenchError("Selected container identity could not be read") from error
        value = result.stdout.strip()
        if not value:
            raise cache.BenchError("Selected container identity was empty")
        return value

    identifier = docker("inspect", "--type", "container", "-f", "{{.Id}}", container)
    if not re.fullmatch(r"[0-9a-f]{64}", identifier):
        raise cache.BenchError("Invalid selected container ID")
    if docker("inspect", "-f", "{{.State.Running}}", identifier) != "true":
        raise cache.BenchError("Selected serving container is not running")
    image = docker("inspect", "-f", "{{.Image}}", identifier)
    source = docker("exec", identifier, "cat", "/opt/qwen/patches/source.env")
    revision = re.search(r"^SGLANG_REVISION=([0-9a-f]{40})$", source, re.MULTILINE)
    if revision is None:
        raise cache.BenchError("Selected container has no valid engine revision")
    series_name = docker("exec", identifier, "cat", "/opt/qwen/patch-series")
    series_files = {
        "upstream": (),
        "baseline": ("baseline.series",),
        "experimental": ("baseline.series", "experimental.series"),
    }
    if series_name not in series_files:
        raise cache.BenchError("Selected container has an unknown patch series")
    series = "\n".join(
        docker("exec", identifier, "cat", f"/opt/qwen/patches/{filename}")
        for filename in series_files[series_name]
    )
    hashes = [line.split()[0] for line in series.splitlines() if line.strip() and not line.startswith("#")]
    if any(re.fullmatch(r"[0-9a-f]{64}", value) is None for value in hashes):
        raise cache.BenchError("Selected container has an invalid patch manifest")
    environment: object = json.loads(docker("inspect", "-f", "{{json .Config.Env}}", identifier))
    if not isinstance(environment, list) or not all(isinstance(part, str) for part in environment):
        raise cache.BenchError("Selected container environment is not a string list")
    public_environment: list[str] = []
    for part in environment:
        if isinstance(part, str) and part.startswith("QWEN_"):
            name = part.partition("=")[0]
            if not any(secret in name for secret in ("KEY", "SECRET", "TOKEN", "PASSWORD", "CREDENTIAL")):
                public_environment.append(part)
    return {
        "container_id": identifier,
        "image_sha256": image,
        "engine_base_commit": revision.group(1),
        "patch_series": series_name,
        "ordered_patch_sha256": hashes,
        "container_env": sorted(public_environment),
    }


def corpus_document(source: Path = PROMPTS_FILE) -> str:
    """The frozen prompt corpus repeated to cover the deepest matrix row."""
    prompts: list[str] = []
    for line in source.read_bytes().decode("utf-8").splitlines():
        value: object = json.loads(line, object_pairs_hook=cache.json_object)
        conversations = cache.mapping(value).get("conversations")
        if not isinstance(conversations, list) or not conversations:
            raise cache.BenchError("invalid frozen prompt conversations")
        first: object = conversations[0]
        prompt = cache.mapping(first).get("value")
        if not isinstance(prompt, str):
            raise cache.BenchError("invalid frozen prompt text")
        prompts.append(prompt)
    return "\n\n".join(prompts * 96)


def _tokenize(client: cache.Client, payload: dict[str, object]) -> tuple[int, dict[str, object]]:
    """Retain the successful structured HTTP receipt, without another request."""
    started = time.monotonic_ns()
    response = client.request("/v1/tokenize", payload)
    received = time.monotonic_ns()
    count = cache.integer(response.get("count"))
    tokens = cache.token_ids(response.get("tokens"))
    if "error" in response or not tokens or count != len(tokens):
        raise cache.BenchError("tokenization failed or count does not match returned token IDs")
    return count, {
        "method": "POST", "path": "/v1/tokenize", "status": cache.HTTP_OK,
        "request": payload, "response": response,
        "request_started_ns": started, "response_received_ns": received,
    }


def natural_prompt(
    client: cache.Client, depth: int, nonce: str, *, source: Path = PROMPTS_FILE,
) -> tuple[str, int, dict[str, object]]:
    """Build one frozen natural prompt at the exact requested token depth.

    The character cut is adjusted against the server tokenizer until the
    measured content token count lands within two tokens of the target.
    Return the successful receipt and corpus cut; raw-content tolerance is
    not a claim about chat-template overhead.
    """
    if cache.integer(depth) not in DEPTHS:
        raise cache.BenchError("unsupported C1 depth")
    document = corpus_document(source)
    low, high = 0, len(document)
    for _ in range(24):
        middle = (low + high) // 2
        content = nonce + "\n" + document[:middle] + "\n\n" + INSTRUCTION
        count, receipt = _tokenize(
            client, {"model": cache.MODEL, "prompt": content, "add_special_tokens": False},
        )
        if abs(count - depth) <= 2:
            return content, middle, receipt
        if count < depth:
            low = middle
        else:
            high = middle
    raise cache.BenchError("depth sizing did not converge")


def run_once(client: cache.Client, port: int, key: str, depth: int, nonce: str, directory: Path) -> dict[str, object]:
    """Measure cumulative committed counters at client-observed SSE boundaries."""
    content, prefix_chars, content_receipt = natural_prompt(
        client, depth, nonce, source=directory.parent / "sources/bench/throughput-prompts.jsonl",
    )
    with (directory / "content-tokenization.json").open("xb") as handle:
        handle.write(canonical_bytes(content_receipt))
    body = {
        "model": cache.MODEL,
        "messages": [{"role": "user", "content": content}],
        "max_tokens": OUTPUT_TOKENS,
        "temperature": 0,
        "top_p": 1,
        "n": 1,
        "stream": True,
        "stream_options": {"include_usage": True, "continuous_usage_stats": True},
    }
    payload = canonical_bytes(body)
    with (directory / "request.json").open("xb") as handle:
        handle.write(payload)
    # The pinned TokenizeRequest converts messages to ChatCompletionRequest and
    # shares _process_messages with generation. Do not infer template overhead.
    # Multimodal preparation can re-encode the rendered prompt; only measured
    # equality below admits it. Streaming cannot return prompt IDs on this pin.
    chat_tokens, chat_receipt = _tokenize(client, {"model": cache.MODEL, "messages": body["messages"]})
    with (directory / "chat-tokenization.json").open("xb") as handle:
        handle.write(canonical_bytes(chat_receipt))
    before = spec_gauges(port, key)
    connection = http.client.HTTPConnection("127.0.0.1", port, timeout=client.timeout)
    first_content_ns = None
    first_counter_ns = None
    first_counter = None
    terminal_ns = None
    done_ns = None
    prompt_tokens = None
    completed = None
    finish = None
    counter_samples: list[dict[str, object]] = []
    raw_stream = (directory / "response.sse").open("xb")
    timestamps = (directory / "timestamps.jsonl").open("x", encoding="utf-8")
    offset = 0
    started_ns = time.monotonic_ns()
    try:
        connection.request(
            "POST",
            "/v1/chat/completions",
            body=payload,
            headers={
                "Authorization": "Bearer " + client.key,
                "Content-Type": "application/json",
            },
        )
        response = connection.getresponse()
        cache.save(directory, "response-status.json", {"status": response.status})
        if response.status != cache.HTTP_OK:
            raw_stream.write(response.read(cache.MAX_BODY + 1))
            raise cache.BenchError(f"HTTP status {response.status}")
        for raw in response:
            observed_ns = time.monotonic_ns()
            raw_stream.write(raw)
            timestamps.write(json.dumps({"offset": offset, "length": len(raw), "observed_ns": observed_ns}) + "\n")
            offset += len(raw)
            line = raw.decode(errors="strict").strip()
            if not line.startswith("data:"):
                continue
            chunk = line[len("data:"):].strip()
            if chunk == "[DONE]":
                done_ns = observed_ns
                break
            if terminal_ns is not None:
                raise cache.BenchError("data after terminal usage record")
            event = cache.mapping(json.loads(chunk))
            if "error" in event:
                raise cache.BenchError("stream returned an error event")
            choices = event.get("choices")
            if not isinstance(choices, list) or len(choices) > 1:
                raise cache.BenchError("expected one streamed choice or terminal usage")
            if choices:
                choice = cache.mapping(choices[0])
                if type(choice.get("index")) is not int or choice["index"] != 0:
                    raise cache.BenchError("unexpected streamed choice index")
                delta_value = choice.get("delta")
                delta = {} if delta_value is None else cache.mapping(delta_value)
                content_delta = delta.get("content")
                reasoning_delta = delta.get("reasoning_content")
                if (
                    content_delta is not None and not isinstance(content_delta, str)
                    or reasoning_delta is not None and not isinstance(reasoning_delta, str)
                ):
                    raise cache.BenchError("content and reasoning deltas must be strings or null")
                reason = choice.get("finish_reason")
                if reason is not None:
                    if reason not in ("stop", "length") or finish is not None:
                        raise cache.BenchError("invalid or repeated stream finish reason")
                    finish = reason
                if first_content_ns is None and (content_delta or reasoning_delta):
                    first_content_ns = observed_ns
            usage_value = event.get("usage")
            if usage_value is not None:
                usage = cache.mapping(usage_value)
                current_prompt = usage.get("prompt_tokens")
                current_completed = usage.get("completion_tokens")
                if (
                    type(current_prompt) is not int or current_prompt < 0
                    or type(current_completed) is not int or current_completed < 0
                ):
                    raise cache.BenchError("usage counters must be nonnegative exact integers")
                if current_completed > OUTPUT_TOKENS:
                    raise cache.BenchError("completion token counter exceeded requested output budget")
                if current_prompt != chat_tokens:
                    raise cache.BenchError("stream prompt count differs from independent chat tokenization")
                if prompt_tokens is not None and current_prompt != prompt_tokens:
                    raise cache.BenchError("prompt token counter changed during stream")
                if completed is not None and current_completed < completed:
                    raise cache.BenchError("completion token counter decreased during stream")
                prompt_tokens = current_prompt
                completed = current_completed
                terminal = not choices
                counter_samples.append({
                    "observed_ns": observed_ns,
                    "prompt_tokens": current_prompt,
                    "completion_tokens": current_completed,
                    "terminal": terminal,
                })
                if first_counter_ns is None and current_completed > 0:
                    first_counter_ns = observed_ns
                    first_counter = current_completed
                if terminal:
                    if finish is None:
                        raise cache.BenchError("terminal usage preceded successful finish reason")
                    terminal_ns = observed_ns
            elif not choices:
                extension = cache.mapping(event.get("sglext"))
                extension_types = {
                    "routed_experts": str,
                    "cached_tokens_details": dict,
                    "spec_tokens_details": dict,
                }
                if (
                    not extension or not any(value is not None for value in extension.values())
                    or any(
                        name not in extension_types
                        or value is not None and not isinstance(value, extension_types[name])
                        for name, value in extension.items()
                    )
                ):
                    raise cache.BenchError("empty choices without typed SGLang metadata or usage")
    finally:
        connection.close()
        raw_stream.close()
        timestamps.close()
        cache.save(directory, "request-timing.json", {"request_started_ns": started_ns})
    if done_ns is None or terminal_ns is None:
        raise cache.BenchError("stream missing terminal usage or DONE")
    if (
        completed is None or first_counter is None or first_counter_ns is None
        or first_content_ns is None
    ):
        raise cache.BenchError("stream missing positive counters or first content/reasoning")
    if finish == "length" and completed != OUTPUT_TOKENS:
        raise cache.BenchError("length finish did not reach requested output budget")
    counter_delta = completed - first_counter
    counter_window_ns = terminal_ns - first_counter_ns
    elapsed_ns = done_ns - started_ns
    if counter_delta <= 0 or counter_window_ns <= 0 or elapsed_ns <= 0:
        raise cache.BenchError("nonpositive counter delta, counter window, or request window")
    after = spec_gauges(port, key)
    return {
        "schema_version": SCHEMA_VERSION,
        "measurement_protocol": MEASUREMENT_PROTOCOL,
        "request_body_sha256": hashlib.sha256(payload).hexdigest(),
        "nonce": nonce,
        "corpus_prefix_chars": prefix_chars,
        "prompt_tokens": prompt_tokens,
        "completion_tokens": completed,
        "finish_reason": finish,
        "request_started_ns": started_ns,
        "first_content_or_reasoning_observed_ns": first_content_ns,
        "first_positive_counter_observed_ns": first_counter_ns,
        "first_positive_completion_tokens": first_counter,
        "terminal_usage_observed_ns": terminal_ns,
        "done_observed_ns": done_ns,
        "counter_samples": counter_samples,
        "counter_window_tokens": counter_delta,
        "counter_window_ns": counter_window_ns,
        "elapsed_ns": elapsed_ns,
        "ttft_s": (first_content_ns - started_ns) / 1e9,
        "elapsed_seconds": elapsed_ns / 1e9,
        "committed_tok_s": counter_delta * 1e9 / counter_window_ns,
        "whole_request_tok_s": completed * 1e9 / elapsed_ns,
        "spec_accept_length_before": before.get("sglang:spec_accept_length", 0.0),
        "spec_accept_length_after": after.get("sglang:spec_accept_length", 0.0),
    }


def execute(client: cache.Client, port: int, key: str, repetitions: int, directory: Path) -> list[dict[str, object]]:
    """Reject unsupported matrices before running any depth or repetition."""
    if cache.integer(repetitions) < 1:
        raise cache.BenchError("repetitions must be a positive integer")
    unsupported = [
        depth for depth in DEPTHS
        if depth + OUTPUT_TOKENS + 2 > client.context_length
    ]
    if unsupported:
        raise cache.BenchError(
            f"unsupported depth matrix: depths {unsupported} plus output budget "
            f"{OUTPUT_TOKENS} and 2-token reserve exceed context {client.context_length}"
        )
    rows: list[dict[str, object]] = []
    for depth in DEPTHS:
        for repetition in range(repetitions):
            nonce = f"[measurement run {repetition + 1} of {repetitions} at depth {depth}]"
            row_directory = directory / f"depth-{depth}-rep-{repetition}"
            row_directory.mkdir(mode=0o700)
            sampler = PowerSampler()
            try:
                with sampler:
                    row = run_once(client, port, key, depth, nonce, row_directory)
            finally:
                if sampler.ended:
                    cache.save(row_directory, "power.json", {"summary": sampler.summary(), "samples": sampler.records()})
            row["power"] = sampler.summary()
            row["power_samples"] = sampler.records()
            row["request_path"] = (row_directory / "request.json").relative_to(directory).as_posix()
            row["raw_stream_path"] = (row_directory / "response.sse").relative_to(directory).as_posix()
            row["raw_timestamps_path"] = (row_directory / "timestamps.jsonl").relative_to(directory).as_posix()
            row["power_path"] = (row_directory / "power.json").relative_to(directory).as_posix()
            row.update({"depth_target": depth, "repetition": repetition})
            cache.save(row_directory, "row.json", row)
            rows.append(row)
            print(json.dumps(row), flush=True)
    return rows


def main() -> int:
    """Run one new-only candidate-bound matrix, retaining failed raw evidence."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--endpoint", required=True)
    parser.add_argument("--key-file", required=True)
    parser.add_argument("--timeout", type=int, default=cache.MAX_TIMEOUT)
    parser.add_argument("--repetitions", type=int, default=5)
    parser.add_argument("--output", required=True)
    parser.add_argument("--container", default=CONTAINER, help="Running serving container used for identity evidence")
    args = parser.parse_args()
    os.umask(0o077)
    signal.signal(signal.SIGALRM, cache.expired)
    directory = Path(args.output)
    try:
        directory.mkdir(mode=0o700)
    except OSError:
        sys.stderr.write("Decode probe: cannot exclusively create output directory.\n")
        return 2
    try:
        if cache.integer(args.repetitions) < 1:
            raise cache.BenchError("repetitions must be a positive integer")
        settings = cache.Settings(args.endpoint, args.key_file, "", DEPTHS[-1], args.timeout)
        client = cache.client_from_settings(settings, cache.NATIVE_CONTEXT_TOKENS, reserved_tokens=OUTPUT_TOKENS + 2)
        if urlsplit(args.endpoint).hostname != "127.0.0.1":
            raise cache.BenchError("decode endpoint must use 127.0.0.1")
        sources = snapshot_sources(directory, (
            "bench/decode.py", "bench/cache.py", "bench/power.py", "bench/throughput-prompts.jsonl",
        ))
        workload = {
            "schema_version": WORKLOAD_SCHEMA_VERSION,
            "depths": list(DEPTHS), "repetitions": args.repetitions,
            "order": "depth_then_repetition", "concurrency": 1,
            "nonce_template": "[measurement run {repetition + 1} of {repetitions} at depth {depth}]",
            "sampling": {"temperature": 0, "top_p": 1, "n": 1, "max_tokens": OUTPUT_TOKENS, "ignore_eos": False},
            "cache": {"policy": "deterministic_per_row_nonce_no_flush_no_warmup", "cache_salt": None},
            "timeout_seconds": args.timeout, "sources": sources,
            "power": {"gpu": "0", "sampling_interval_seconds": 0.5, "max_seconds": 86400, "max_samples": 200000},
        }
        with (directory / "workload.json").open("xb") as handle:
            handle.write(canonical_bytes(workload))
        identity = capture_identity(directory, args.container, args.endpoint, args.key_file)
        native_exit_code = 2
        try:
            rows = execute(client, client.port, client.key, args.repetitions, directory)
            native_exit_code = 0
        except (cache.BenchError, OSError, ValueError, http.client.HTTPException, RecursionError, OverflowError) as error:
            cache.save(directory, "request-failure.json", {
                "reason": str(error) if isinstance(error, cache.BenchError) else type(error).__name__,
            })
            raise
        finally:
            identity_after = capture_identity(directory, args.container, args.endpoint, args.key_file, after=True, native_exit_code=native_exit_code)
        if not rows:
            raise cache.BenchError("no rows measured")
        rates = [row["committed_tok_s"] for row in rows]
        if not all(isinstance(rate, float) for rate in rates):
            raise cache.BenchError("invalid measured rates")
        measured_rates = [rate for rate in rates if isinstance(rate, float)]
        report = {
            "schema_version": SCHEMA_VERSION, "evidence_schema_version": 1,
            "measurement_protocol": MEASUREMENT_PROTOCOL,
            "classification": "C1_DECODE_DEPTH_MATRIX",
            "identity": identity, "identity_after": identity_after,
            "rows": rows, "committed_tok_s_min": min(measured_rates), "committed_tok_s_max": max(measured_rates),
            "workload_sha256": hashlib.sha256(canonical_bytes(workload)).hexdigest(),
            "artifacts": artifacts(directory),
        }
        cache.save(directory, "decode-depth-matrix.json", report)
    except (cache.BenchError, OSError, ValueError, http.client.HTTPException, RecursionError, OverflowError) as error:
        failure(directory, error)
        sys.stderr.write("Decode probe rejected; inspect private failure evidence.\n")
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
