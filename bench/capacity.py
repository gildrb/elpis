# Copyright (c) 2026 inference contributors.
"""One exact-ID native capacity probe; see docs/capacity.md."""

import argparse
import hashlib
import http.client
import json
import os
import secrets
import signal
import time
from dataclasses import dataclass, field
from itertools import count
import sys
from pathlib import Path
from typing import override

from bench import cache, decode

ENGINE_OVERHEAD = 2
RESERVED_TOKENS = cache.OUTPUT_TOKENS + ENGINE_OVERHEAD
INSTRUCTION = (
    "\nEnd of synthetic ledger. New instruction: explain in plain English why "
    "a triangle has three sides and a square has four sides. Give one everyday "
    "example of each shape. Answer in a short paragraph.\nAnswer:"
)


def _input_ids(client: cache.Client, count: int, directory: Path) -> list[int]:
    fixture = cache.make_fixture(client, count)
    tokenized = client.request(
        "/v1/tokenize",
        {"model": cache.MODEL, "prompt": INSTRUCTION, "add_special_tokens": False},
    )
    instruction_ids = cache.token_ids(tokenized.get("tokens"))
    if (
        len(instruction_ids) == 0
        or cache.integer(tokenized.get("count")) != len(instruction_ids)
        or len(instruction_ids) >= count
    ):
        message = "instruction tokenization does not fit requested input"
        raise cache.BenchError(message)
    ids = fixture[2][: count - len(instruction_ids)] + instruction_ids
    cache.save(
        directory,
        "fixture.json",
        {
            "synthetic_text": fixture[0],
            "seed_ids": fixture[1],
            "instruction": INSTRUCTION,
            "instruction_ids": instruction_ids,
            "input_ids": ids,
        },
    )
    return ids


@dataclass(frozen=True)
class RecordedClient(cache.Client):
    """The existing bounded loopback protocol with private raw HTTP evidence."""

    directory: Path
    sequence: count[int] = field(default_factory=count)

    @override
    def request(self, path: str, payload: dict[str, object] | None = None) -> dict[str, object]:
        directory = self.directory / f"http-{next(self.sequence):03d}"
        directory.mkdir(mode=0o700)
        body = None if payload is None else decode.canonical_bytes(payload)
        cache.save(directory, "operation.json", {"method": "GET" if body is None else "POST", "path": path})
        if body is not None:
            with (directory / "request.json").open("xb") as handle:
                handle.write(body)
            if len(body) > cache.MAX_BODY:
                raise cache.BenchError("request body limit exceeded")
        connection = http.client.HTTPConnection(self.host, self.port, timeout=self.timeout)
        signal.setitimer(signal.ITIMER_REAL, self.timeout)
        started_ns = time.monotonic_ns()
        try:
            connection.request(
                "GET" if body is None else "POST", path, body=body,
                headers={"Authorization": "Bearer " + self.key, "Content-Type": "application/json"},
            )
            response = connection.getresponse()
            cache.save(directory, "status.json", {"status": response.status})
            with (directory / "response.raw").open("xb") as handle:
                received = 0
                while received <= cache.MAX_BODY:
                    try:
                        chunk = response.read1(min(65536, cache.MAX_BODY + 1 - received))
                    except http.client.IncompleteRead as error:
                        handle.write(error.partial)
                        raise
                    if not chunk:
                        if response.length not in (None, 0):
                            raise cache.BenchError("incomplete HTTP response body")
                        break
                    handle.write(chunk)
                    received += len(chunk)
            raw = (directory / "response.raw").read_bytes()
            if len(raw) > cache.MAX_BODY:
                raise cache.BenchError("response body limit exceeded")
            if response.status != cache.HTTP_OK:
                raise cache.BenchError(f"HTTP status {response.status}")
            decoded = cache.mapping(json.loads(
                raw, object_pairs_hook=cache.json_object,
                parse_float=cache.json_float, parse_constant=cache.json_constant,
            ))
            cache.save(directory, "response.json", decoded)
            if path == "/generate":
                cache.save(self.directory, "response.json", decoded)
            return decoded
        finally:
            finished_ns = time.monotonic_ns()
            signal.setitimer(signal.ITIMER_REAL, 0)
            connection.close()
            cache.save(directory, "timing.json", {"request_started_ns": started_ns, "response_finished_ns": finished_ns})


def _generation(client: RecordedClient, ids: list[int], salt: str, directory: Path) -> dict[str, object]:
    # Same bounded native request as cache.Client.generate; no chat template.
    body: dict[str, object] = {
        "input_ids": ids, "cache_salt": salt, "stream": False,
        "sampling_params": {"temperature": 0, "ignore_eos": True, "max_new_tokens": cache.OUTPUT_TOKENS},
        "return_logprob": True, "logprob_start_len": -1,
        "top_logprobs_num": 0, "return_text_in_logprobs": False,
    }
    with (directory / "request.json").open("xb") as handle:
        handle.write(decode.canonical_bytes(body))
    response = client.request("/generate", body)
    output = cache.token_ids(response.get("output_ids"))
    meta = cache.mapping(response.get("meta_info"))
    prompt = cache.integer(meta.get("prompt_tokens"))
    completed = cache.integer(meta.get("completion_tokens"))
    # Backend-added BOS/special tokens must fit the pre-existing two-slot reserve.
    # Report the observed delta, never infer a particular tokenizer's BOS count.
    overhead = prompt - len(ids)
    if not 0 <= overhead <= ENGINE_OVERHEAD:
        raise cache.BenchError("observed backend prompt overhead exceeds reserved slots")
    if completed != cache.OUTPUT_TOKENS or len(output) != completed:
        raise cache.BenchError("completion token count mismatch")
    if prompt + completed > cache.NATIVE_CONTEXT_TOKENS:
        raise cache.BenchError("observed prompt plus output exceeds native context")
    cached = cache.integer(meta.get("cached_tokens"))
    retractions = cache.integer(meta.get("num_retractions"))
    finish = cache.mapping(meta.get("finish_reason"))
    if finish.get("type") != "length":
        raise cache.BenchError("unexpected finish reason")
    text = response.get("text")
    if not isinstance(text, str) or not text.strip():
        raise cache.BenchError("generated text is missing or empty")
    observed: dict[str, object] = {
        "prompt_tokens": prompt, "completion_tokens": completed,
        "submitted_input_tokens": len(ids), "backend_prompt_overhead_tokens": overhead,
        "cached_tokens": cached, "num_retractions": retractions,
        "finish_reason": finish, "output_text": text, "output_ids": output,
        "logprobs": cache.logprobs(meta.get("output_token_logprobs"), output, allow_initial_null=False),
        "request_body_sha256": hashlib.sha256(decode.canonical_bytes(body)).hexdigest(),
    }
    cache.save(directory, "generation.json", observed)
    if cached != 0 or retractions != 0:
        raise cache.BenchError("capacity request reused cache or retracted")
    return observed


def execute(args: cache.Settings, directory: Path) -> dict[str, object]:
    """Submit one bounded exact-input allocation/generation probe, not a score."""
    # The rich capture has already verified the actual native API and backed pool.
    client_base = cache.client_from_settings(
        args, cache.NATIVE_CONTEXT_TOKENS, reserved_tokens=RESERVED_TOKENS,
    )
    client = RecordedClient(
        client_base.host, client_base.port, client_base.key, client_base.timeout,
        client_base.context_length, directory,
    )
    ids = _input_ids(client, args.input_tokens, directory)
    salt = secrets.token_hex(32)
    ids_bytes = decode.canonical_bytes(ids)
    with (directory / "input-ids.json").open("xb") as handle:
        handle.write(ids_bytes)
    plan = {
        "schema_version": 2, "observed_model_id": cache.MODEL,
        "input_tokens": len(ids), "requested_output_tokens": cache.OUTPUT_TOKENS,
        "engine_overhead_tokens": ENGINE_OVERHEAD,
        "total_budget_tokens": len(ids) + RESERVED_TOKENS,
        "input_ids_sha256": hashlib.sha256(ids_bytes).hexdigest(),
        "cache_salt": salt, "timeout_seconds": args.timeout,
        "overhead_accounting": "actual prompt_tokens minus submitted IDs; backend BOS/special overhead must be 0..2 and fit the original two reserved slots",
    }
    cache.save(directory, "plan.json", plan)
    observed = _generation(client, ids, salt, directory)
    prompt = cache.integer(observed["prompt_tokens"])
    completed = cache.integer(observed["completion_tokens"])
    near_native = len(ids) + RESERVED_TOKENS == cache.NATIVE_CONTEXT_TOKENS
    return {
        "schema_version": 2, "evidence_schema_version": 1,
        "status": "request_completed", "observed_model_id": cache.MODEL,
        **observed, "input_ids_sha256": plan["input_ids_sha256"],
        "actual_total_tokens": prompt + completed,
        "native_context_tokens": cache.NATIVE_CONTEXT_TOKENS,
        "native_coverage_fraction": (prompt + completed) / cache.NATIVE_CONTEXT_TOKENS,
        "near_native_completed": near_native,
        "near_native_rejection_reason": None if near_native else "requested input plus fixed output/reserve does not reach native context",
        "nonempty_output": True, "finite_aligned_output_logprobs": True,
        "meaningfulness": "operator_review_required",
        "prime_envs_quality": "not_evaluated",
        "sustained_concurrency_cache_qualification": "not_evaluated",
        "scope": "one exact-ID near-native allocation/generation probe; not sustained concurrency/cache or model-quality qualification",
    }


def main() -> int:
    """Run one capacity probe without changing the service.

    Returns:
        Zero for a completed request; two for an inconclusive probe.

    """
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--endpoint", default="http://127.0.0.1:18020")
    parser.add_argument("--key-file", required=True)
    parser.add_argument("--input-tokens", type=int, required=True)
    parser.add_argument("--timeout", type=int, default=900)
    parser.add_argument("--output", required=True, help="new private directory")
    parser.add_argument("--container", default=decode.CONTAINER)
    args = parser.parse_args()
    os.umask(0o077)
    signal.signal(signal.SIGALRM, cache.expired)
    directory = Path(args.output)
    try:
        directory.mkdir(mode=0o700)
    except OSError:
        sys.stderr.write(
            "Capacity probe: cannot exclusively create output directory.\n"
        )
        return 2
    try:
        sources = decode.snapshot_sources(directory, ("bench/capacity.py", "bench/cache.py", "bench/decode.py"))
        identity = decode.capture_identity(directory, args.container, args.endpoint, args.key_file)
        native_exit_code = 2
        try:
            settings = cache.Settings(args.endpoint, args.key_file, "", args.input_tokens, args.timeout)
            result = execute(settings, directory)
            native_exit_code = 0
        except (cache.BenchError, OSError, ValueError, http.client.HTTPException, RecursionError, OverflowError) as error:
            cache.save(directory, "request-failure.json", {
                "reason": str(error) if isinstance(error, cache.BenchError) else type(error).__name__,
            })
            raise
        finally:
            identity_after = decode.capture_identity(directory, args.container, args.endpoint, args.key_file, after=True, native_exit_code=native_exit_code)
        result.update({
            "identity": identity, "identity_after": identity_after, "sources": sources,
            "artifacts": decode.artifacts(directory),
        })
        cache.save(directory, "result.json", result)
    except (
        cache.BenchError,
        OSError,
        ValueError,
        http.client.HTTPException,
        RecursionError,
        OverflowError,
    ) as error:
        reason = (
            str(error)
            if isinstance(error, cache.BenchError)
            else "bounded I/O, JSON or numeric operation failed"
        )
        try:
            decode.failure(directory, error)
        except OSError:
            sys.stderr.write("Capacity probe: failure artifact could not be written.\n")
        sys.stderr.write(f"Capacity probe inconclusive: {reason}.\n")
        return 2
    sys.stdout.write("Capacity request completed; private output requires review.\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
