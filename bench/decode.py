# Copyright (c) 2026 inference contributors.
"""Single-request C1 decode-rate depth matrix; see docs/decode-bottlenecks.md.

Engineering measurement, not a quality score. Natural runs use the frozen chat
prompts from bench/throughput-prompts.jsonl padded to each requested input
depth and stop at their own EOS; committed tokens are counted from the
server's usage counter, not from streamed chunk counts.
"""

import argparse
import http.client
import json
import re
import subprocess
import threading
import time
from pathlib import Path

from bench import cache

DEPTHS = (1024, 8192, 32768)
OUTPUT_TOKENS = 1024
INSTRUCTION = (
    "End of reference material. Write a careful technical summary of the main "
    "ideas above, then give one original worked Python example with tests."
)
PROMPTS_FILE = Path(__file__).parent / "throughput-prompts.jsonl"
CONTAINER = "qwen-inference-inference-1"


class PowerSampler:
    """Bounded nvidia-smi power sampler for one request window."""

    def __init__(self) -> None:
        self.samples: list[float] = []
        self._stop = threading.Event()
        self._thread = threading.Thread(target=self._loop, daemon=True)

    def _loop(self) -> None:
        while not self._stop.is_set():
            try:
                raw = subprocess.run(
                    [
                        "nvidia-smi",
                        "--query-gpu=power.draw",
                        "--format=csv,noheader,nounits",
                    ],
                    capture_output=True,
                    text=True,
                    timeout=5,
                ).stdout.strip()
                self.samples.append(float(raw))
            except (subprocess.SubprocessError, ValueError):
                return
            self._stop.wait(0.5)

    def __enter__(self) -> "PowerSampler":
        self._thread.start()
        return self

    def __exit__(self, *_args: object) -> None:
        self._stop.set()
        self._thread.join(timeout=5)

    def summary(self) -> dict[str, float]:
        ordered = sorted(self.samples) if self.samples else [0.0]
        count = len(ordered)
        return {
            "watts_samples": float(count),
            "watts_min": ordered[0],
            "watts_p50": ordered[count // 2],
            "watts_p90": ordered[min(count - 1, (count * 9) // 10)],
            "watts_max": ordered[-1],
        }


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


def container_identity() -> dict[str, object]:
    """Record the live serving container's image and launch environment."""
    def inspect(field: str) -> str:
        return subprocess.run(
            ["docker", "inspect", "-f", field, CONTAINER],
            capture_output=True, text=True, timeout=30,
        ).stdout.strip()

    series = [
        line.split()[0]
        for line in (Path(__file__).parent.parent / "patches" / "experimental.series")
        .read_text()
        .splitlines()
        if line.strip()
    ]
    environment = inspect("{{json .Config.Env}}")
    return {
        "image_sha256": inspect("{{.Image}}"),
        "engine_base_commit": re.search(
            r"SGLANG_REVISION=([0-9a-f]{40})",
            Path(__file__).parent.parent.joinpath("patches", "source.env").read_text(),
        ).group(1),
        "ordered_patch_sha256": series,
        "container_env": sorted(
            part for part in json.loads(environment) if part.startswith("QWEN_")
        ),
    }


def corpus_document() -> str:
    """The frozen prompt corpus repeated to cover the deepest matrix row."""
    prompts = [
        json.loads(line)["conversations"][0]["value"]
        for line in PROMPTS_FILE.read_text().splitlines()
    ]
    return "\n\n".join(prompts * 96)


def natural_prompt(client: cache.Client, depth: int, nonce: str) -> str:
    """Build one frozen natural prompt at the exact requested token depth.

    The character cut is adjusted against the server tokenizer until the
    measured content token count lands within two tokens of the target.
    """
    document = corpus_document()
    low, high = 0, len(document)
    for _ in range(24):
        middle = (low + high) // 2
        content = nonce + "\n" + document[:middle] + "\n\n" + INSTRUCTION
        tokenized = client.request(
            "/v1/tokenize", {"model": cache.MODEL, "prompt": content, "add_special_tokens": False}
        )
        count = cache.integer(tokenized.get("count"))
        if abs(count - depth) <= 2:
            return content
        if count < depth:
            low = middle
        else:
            high = middle
    raise cache.BenchError("depth sizing did not converge")


def run_once(client: cache.Client, port: int, key: str, depth: int, nonce: str) -> dict[str, object]:
    """One streamed chat completion at the exact requested depth."""
    content = natural_prompt(client, depth, nonce)
    body = {
        "model": cache.MODEL,
        "messages": [{"role": "user", "content": content}],
        "max_tokens": OUTPUT_TOKENS,
        "temperature": 0,
        "stream": True,
        "stream_options": {"include_usage": True},
    }
    payload = json.dumps(body).encode()
    before = spec_gauges(port, key)
    connection = http.client.HTTPConnection("127.0.0.1", port, timeout=client.timeout)
    started = time.monotonic()
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
    if response.status != cache.HTTP_OK:
        raise cache.BenchError(f"HTTP status {response.status}")
    ttft = None
    usage = None
    finish = None
    for raw in response:
        line = raw.decode(errors="strict").strip()
        if not line.startswith("data: "):
            continue
        chunk = line[len("data: "):]
        if chunk == "[DONE]":
            break
        event = cache.mapping(json.loads(chunk))
        if event.get("usage"):
            usage = cache.mapping(event["usage"])
        choices = event.get("choices")
        if isinstance(choices, list) and choices:
            delta = cache.mapping(cache.mapping(choices[0]).get("delta") or {})
            if finish is None and cache.mapping(choices[0]).get("finish_reason"):
                finish = cache.mapping(choices[0])["finish_reason"]
            if ttft is None and (delta.get("content") or delta.get("reasoning_content")):
                ttft = time.monotonic() - started
    elapsed = time.monotonic() - started
    connection.close()
    after = spec_gauges(port, key)
    if usage is None:
        raise cache.BenchError("usage missing from stream")
    completed = cache.integer(usage.get("completion_tokens"))
    if completed <= 0 or ttft is None:
        raise cache.BenchError("no committed tokens or no first token")
    decode_window = elapsed - ttft
    return {
        "prompt_tokens": cache.integer(usage.get("prompt_tokens")),
        "completion_tokens": completed,
        "finish_reason": finish,
        "ttft_s": round(ttft, 3),
        "elapsed_seconds": elapsed,
        "decode_window_s": round(decode_window, 3),
        "committed_tok_s": round(completed / decode_window, 2),
        "spec_accept_length_before": before.get("sglang:spec_accept_length", 0.0),
        "spec_accept_length_after": after.get("sglang:spec_accept_length", 0.0),
    }


def execute(client: cache.Client, port: int, key: str, repetitions: int) -> list[dict[str, object]]:
    """Run the depth matrix with per-depth repetitions."""
    rows: list[dict[str, object]] = []
    for depth in DEPTHS:
        if depth + OUTPUT_TOKENS + 2 > client.context_length:
            continue
        for repetition in range(repetitions):
            nonce = f"[measurement run {repetition + 1} of {repetitions} at depth {depth}]"
            with PowerSampler() as sampler:
                row = run_once(client, port, key, depth, nonce)
                row["power"] = sampler.summary()
            row.update({"depth_target": depth, "repetition": repetition})
            rows.append(row)
            print(json.dumps(row), flush=True)
    return rows


def main() -> int:
    """Parse settings, run the matrix, save the report."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--endpoint", required=True)
    parser.add_argument("--key-file", required=True)
    parser.add_argument("--timeout", type=int, default=cache.MAX_TIMEOUT)
    parser.add_argument("--repetitions", type=int, default=5)
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    endpoint = args.endpoint
    key = Path(args.key_file).read_text(encoding="ascii").strip()
    port = int(endpoint.rsplit(":", 1)[1])
    client = cache.Client("127.0.0.1", port, key, args.timeout, cache.NATIVE_CONTEXT_TOKENS)
    rows = execute(client, port, key, args.repetitions)
    if not rows:
        raise cache.BenchError("no rows measured")
    rates = [float(row["committed_tok_s"]) for row in rows]
    report = {
        "schema_version": 1,
        "classification": "C1_DECODE_DEPTH_MATRIX",
        "identity": container_identity(),
        "rows": rows,
        "committed_tok_s_min": min(rates),
        "committed_tok_s_max": max(rates),
    }
    cache.save(Path(args.output), "decode-depth-matrix.json", report)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
