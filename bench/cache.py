"""Salt-isolated, emitted-token cache consistency diagnostic; see docs/cache.md."""

import argparse
import hashlib
import http.client
import json
import math
import os
import secrets
import signal
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from types import FrameType
from urllib.parse import urlsplit

MODEL = "qwen3.8-27b"
CUTOFF = 0.001
OUTPUT_TOKENS = 128
MAX_BODY = 16 * 1024 * 1024
MAX_TOKEN_IDS = 65536
MAX_TOKEN_ID = 2147483647
LOGPROB_FIELDS = 3
HTTP_OK = 200
MAX_PORT = 65535
MIN_INPUT_TOKENS = 1024
MAX_INPUT_TOKENS = 65000
MIN_TIMEOUT = 30
MAX_TIMEOUT = 1800
MAX_KEY_BYTES = 4096
MIN_KEY_CHARACTER = 33
MAX_KEY_CHARACTER = 126


class BenchError(Exception):
    """A fixed, sanitized diagnostic failure message."""


def expired(_signum: int, _frame: FrameType | None) -> None:
    """Interrupt the request when its deadline expires.

    Raises:
        BenchError: If validation or request preconditions fail.

    """
    message = "request deadline exceeded"
    raise BenchError(message)


def mapping(value: object) -> dict[str, object]:
    """Validate a JSON object and its string keys.

    Returns:
        A new string-keyed object dictionary.

    Raises:
        BenchError: If validation or request preconditions fail.

    """
    if not isinstance(value, dict):
        message = "expected JSON object"
        raise BenchError(message)
    result: dict[str, object] = {}
    for key, item in value.items():
        if not isinstance(key, str):
            message = "invalid JSON object key"
            raise BenchError(message)
        result[key] = item
    return result


def json_object(pairs: list[tuple[str, object]]) -> dict[str, object]:
    """Build a JSON object while rejecting duplicate keys.

    Returns:
        The object with its original values.

    Raises:
        BenchError: If validation or request preconditions fail.

    """
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            message = "duplicate JSON object key"
            raise BenchError(message)
        result[key] = value
    return result


def json_float(text: str) -> float:
    """Parse a finite JSON floating-point number.

    Returns:
        The finite parsed number.

    Raises:
        BenchError: If validation or request preconditions fail.

    """
    value = float(text)
    if not math.isfinite(value):
        message = "non-finite JSON number"
        raise BenchError(message)
    return value


def json_constant(_text: str) -> object:
    """Reject nonstandard JSON numeric constants.

    Raises:
        BenchError: If validation or request preconditions fail.

    """
    message = "non-standard JSON numeric constant"
    raise BenchError(message)


def integer(value: object) -> int:
    """Validate a nonnegative integer without accepting booleans.

    Returns:
        The validated nonnegative integer.

    Raises:
        BenchError: If validation or request preconditions fail.

    """
    if isinstance(value, bool) or not isinstance(value, int) or value < 0:
        message = "expected nonnegative integer"
        raise BenchError(message)
    return value


def token_ids(value: object) -> list[int]:
    """Validate bounded token IDs.

    Returns:
        The validated token ID list.

    Raises:
        BenchError: If validation or request preconditions fail.

    """
    if not isinstance(value, list) or len(value) > MAX_TOKEN_IDS:
        message = "invalid token ID list"
        raise BenchError(message)
    result = [integer(item) for item in value]
    if any(item > MAX_TOKEN_ID for item in result):
        message = "token ID outside supported range"
        raise BenchError(message)
    return result


def logprobs(
    value: object, expected: list[int], *, allow_initial_null: bool
) -> list[float | None]:
    """Validate aligned logprob rows and optional initial null.

    Returns:
        Aligned finite logprobs, with an allowed initial null preserved.

    Raises:
        BenchError: If validation or request preconditions fail.

    """
    if not isinstance(value, list) or len(value) != len(expected):
        message = "logprob row count mismatch"
        raise BenchError(message)
    result: list[float | None] = []
    for index, row in enumerate(value):
        if not isinstance(row, list) or len(row) != LOGPROB_FIELDS:
            message = "invalid logprob row"
            raise BenchError(message)
        if integer(row[1]) != expected[index] or row[2] is not None:
            message = "logprob token ID or text-field mismatch"
            raise BenchError(message)
        number: object = row[0]
        if number is None and index == 0 and allow_initial_null:
            result.append(None)
        elif isinstance(number, bool) or not isinstance(number, (int, float)):
            message = "invalid logprob value"
            raise BenchError(message)
        elif not math.isfinite(number) or number > 0:
            message = "logprob must be finite and nonpositive"
            raise BenchError(message)
        else:
            result.append(float(number))
    return result


def save(directory: Path, name: str, data: object) -> None:
    # Directory ownership is established with exclusive mkdir before any writes.
    """Create a JSON artifact exclusively in the owned directory."""
    with (directory / name).open("x", encoding="utf-8") as handle:
        json.dump(data, handle, allow_nan=False, separators=(",", ":"))
        handle.write("\n")


@dataclass(frozen=True)
class Settings:
    """Validated cache diagnostic command-line settings."""

    endpoint: str
    key_file: str
    input_tokens: int
    timeout: int

    @classmethod
    def from_namespace(cls, namespace: argparse.Namespace) -> "Settings":
        """Validate parsed diagnostic settings.

        Returns:
            Settings with validated string and integer fields.

        Raises:
            BenchError: If validation or request preconditions fail.

        """
        values = mapping(vars(namespace))
        endpoint = values.get("endpoint")
        key_file = values.get("key_file")
        if not isinstance(endpoint, str) or not isinstance(key_file, str):
            message = "invalid endpoint or credential path"
            raise BenchError(message)
        return cls(
            endpoint,
            key_file,
            integer(values.get("input_tokens")),
            integer(values.get("timeout")),
        )


@dataclass(frozen=True)
class Client:
    """Loopback HTTP client with bounded bodies and a request deadline."""

    host: str
    port: int
    key: str
    timeout: int

    def request(
        self, path: str, payload: dict[str, object] | None = None
    ) -> dict[str, object]:
        """Send a bounded authenticated request and validate its JSON object.

        Returns:
            The validated response object.

        Raises:
            BenchError: If validation or request preconditions fail.

        """
        body = (
            None if payload is None else json.dumps(payload, allow_nan=False).encode()
        )
        if body is not None and len(body) > MAX_BODY:
            message = "request body limit exceeded"
            raise BenchError(message)
        connection = http.client.HTTPConnection(
            self.host, self.port, timeout=self.timeout
        )
        signal.setitimer(signal.ITIMER_REAL, self.timeout)
        try:
            connection.request(
                "GET" if payload is None else "POST",
                path,
                body=body,
                headers={
                    "Authorization": "Bearer " + self.key,
                    "Content-Type": "application/json",
                },
            )
            response = connection.getresponse()
            if response.status != HTTP_OK:
                message = f"HTTP status {response.status}"
                raise BenchError(message)
            raw = response.read(MAX_BODY + 1)
            if len(raw) > MAX_BODY:
                message = "response body limit exceeded"
                raise BenchError(message)
            decoded: object = json.loads(
                raw,
                object_pairs_hook=json_object,
                parse_float=json_float,
                parse_constant=json_constant,
            )
            return mapping(decoded)
        finally:
            signal.setitimer(signal.ITIMER_REAL, 0)
            connection.close()

    def generate(
        self, ids: list[int], salt: str, outputs: int, *, input_scores: bool
    ) -> tuple[list[int], dict[str, object]]:
        """Generate tokens and validate allowlisted scoring metadata.

        Returns:
            Output token IDs and allowlisted scoring metadata.

        Raises:
            BenchError: If validation or request preconditions fail.

        """
        started = time.monotonic()
        response = self.request(
            "/generate",
            {
                "input_ids": ids,
                "cache_salt": salt,
                "stream": False,
                "sampling_params": {
                    "temperature": 0,
                    "ignore_eos": True,
                    "max_new_tokens": outputs,
                },
                "return_logprob": True,
                "logprob_start_len": 0 if input_scores else -1,
                "top_logprobs_num": 0,
                "return_text_in_logprobs": False,
            },
        )
        output = token_ids(response.get("output_ids"))
        meta = mapping(response.get("meta_info"))
        if integer(meta.get("prompt_tokens")) != len(ids):
            message = "prompt token count mismatch"
            raise BenchError(message)
        if len(output) != outputs or integer(meta.get("completion_tokens")) != outputs:
            message = "completion token count mismatch"
            raise BenchError(message)
        cached = integer(meta.get("cached_tokens"))
        if cached > len(ids):
            message = "invalid cached token count"
            raise BenchError(message)
        retractions = integer(meta.get("num_retractions"))
        finish = mapping(meta.get("finish_reason"))
        if finish.get("type") != "length":
            message = "unexpected finish reason"
            raise BenchError(message)
        selected = {
            "prompt_tokens": len(ids),
            "completion_tokens": outputs,
            "cached_tokens": cached,
            "num_retractions": retractions,
            "finish_reason": "length",
            "elapsed_seconds": time.monotonic() - started,
            "output_ids": output,
            "logprobs": logprobs(
                meta.get(
                    "input_token_logprobs" if input_scores else "output_token_logprobs"
                ),
                ids if input_scores else output,
                allow_initial_null=input_scores,
            ),
        }
        return output, selected


def _client_from_settings(args: Settings) -> Client:
    endpoint = urlsplit(args.endpoint)
    invalid_suffix = (
        endpoint.path not in {"", "/"}
        or len(endpoint.query) > 0
        or len(endpoint.fragment) > 0
    )
    if (
        endpoint.scheme != "http"
        or endpoint.hostname not in {"127.0.0.1", "::1"}
        or endpoint.username is not None
        or endpoint.password is not None
        or invalid_suffix
    ):
        message = "endpoint must be an HTTP loopback origin without credentials or path"
        raise BenchError(message)
    port = endpoint.port
    if port is None or not 1 <= port <= MAX_PORT:
        message = "endpoint requires a valid explicit port"
        raise BenchError(message)
    if (
        not MIN_INPUT_TOKENS <= args.input_tokens <= MAX_INPUT_TOKENS
        or not MIN_TIMEOUT <= args.timeout <= MAX_TIMEOUT
    ):
        message = "input count or timeout outside supported bounds"
        raise BenchError(message)
    with Path(args.key_file).open("rb") as key_file:
        raw_key = key_file.read(4097)
    if len(raw_key) > MAX_KEY_BYTES:
        message = "credential size limit exceeded"
        raise BenchError(message)
    key = raw_key.decode("ascii").replace("\n", "")
    if len(key) == 0 or not all(
        MIN_KEY_CHARACTER <= ord(char) <= MAX_KEY_CHARACTER for char in key
    ):
        message = "invalid credential format"
        raise BenchError(message)
    return Client(endpoint.hostname, port, key, args.timeout)


def _fixture(client: Client, input_tokens: int) -> tuple[str, list[int], list[int]]:
    models = client.request("/v1/models").get("data")
    if (
        not isinstance(models, list)
        or len(models) != 1
        or mapping(models[0]).get("id") != MODEL
    ):
        message = "served model identity mismatch"
        raise BenchError(message)
    nonce = secrets.token_hex(16)
    text = (
        f"Synthetic ledger {nonce}. Copper square follows amber circle. "
        "Record seven blue triangles, then repeat the numbered inventory calmly. "
    )
    tokenized = client.request(
        "/v1/tokenize",
        {
            "model": MODEL,
            "prompt": text,
            "add_special_tokens": False,
        },
    )
    seed = token_ids(tokenized.get("tokens"))
    if len(seed) == 0 or integer(tokenized.get("count")) != len(seed):
        message = "tokenizer count mismatch"
        raise BenchError(message)
    ids = (seed * ((input_tokens + len(seed) - 1) // len(seed)))[:input_tokens]
    return text, seed, ids


def _save_plan(
    directory: Path, ids: list[int], salts: tuple[str, str], timeout: int
) -> None:
    salt_a, salt_b = salts
    profile = {
        "image": (
            "lmsysorg/sglang:v0.5.19@sha256:"
            "d6e7288627be8b02be88e4bba38e73f6d50e2826869f753c13a4c4385ab3eda9"
        ),
        "historical_source_revision": "3958762c198b7e9e0167e6aedda1b8c3f9a8afb1",
        "source_manifest": "patches/manifest.json",
        "entrypoint_sha256": (
            "c994f0a56914b8dddba2d347cbac5ee963af04a2d11818321979e4a622a108dd"
        ),
        "target": "compact-target-rholsc8k/artifact",
        "draft": "Qwen3.8-27B-DFlash2-W4A16",
        "context_length": 65536,
        "max_total_tokens": 66560,
        "max_running_requests": 1,
        "mamba_cache": "extra_buffer/K8/BF16",
        "kv_cache_dtype": "fp8_e4m3",
        "mem_fraction_static": 0.94,
        "chunked_prefill_size": 1024,
        "input_logprob_chunk_size": 256,
        "dflash_block_size": 8,
        "draft_window": 2048,
        "attention": "FlashInfer target and draft",
        "NCCL_MAX_CTAS": 1,
        "sleep_on_idle": True,
    }
    save(
        directory,
        "plan.json",
        {
            "schema_version": 1,
            "model": MODEL,
            "profile_operator_confirmed_not_api_verified": profile,
            "input_tokens": len(ids),
            "prime_outputs": OUTPUT_TOKENS,
            "warm_outputs": OUTPUT_TOKENS,
            "continuation_token": 11,
            "salt_a": salt_a,
            "salt_b": salt_b,
            "cutoff": CUTOFF,
            "request_timeout_seconds": timeout,
            "input_ids_sha256": hashlib.sha256(
                json.dumps(ids, separators=(",", ":")).encode()
            ).hexdigest(),
        },
    )


def _estimate(warm: dict[str, object], cold: dict[str, object]) -> float:
    warm_scores: object = warm["logprobs"]
    cold_scores: object = cold["logprobs"]
    if not isinstance(warm_scores, list) or not isinstance(cold_scores, list):
        message = "missing aligned scores"
        raise BenchError(message)
    differences: list[float] = []
    for cold_score, warm_score in zip(
        cold_scores[-OUTPUT_TOKENS:], warm_scores, strict=True
    ):
        if not isinstance(cold_score, float) or not isinstance(warm_score, float):
            message = "non-numeric aligned score"
            raise BenchError(message)
        differences.append(cold_score - warm_score)
    estimator = (
        math.fsum(math.expm1(delta) - delta for delta in differences) / OUTPUT_TOKENS
    )
    if not math.isfinite(estimator):
        message = "non-finite emitted-token estimator"
        raise BenchError(message)
    return estimator


def execute(args: Settings, directory: Path) -> bool:
    """Run the salted cache comparison and write private artifacts.

    Returns:
        Whether the emitted-token estimator is below the cutoff.

    Raises:
        BenchError: If validation or request preconditions fail.

    """
    client = _client_from_settings(args)
    fixture = _fixture(client, args.input_tokens)
    ids = fixture[2]
    salt_a, salt_b = secrets.token_hex(32), secrets.token_hex(32)
    if salt_a == salt_b:
        message = "cache namespace collision"
        raise BenchError(message)
    save(
        directory,
        "fixture.json",
        {"synthetic_text": fixture[0], "seed_ids": fixture[1], "input_ids": ids},
    )
    _save_plan(directory, ids, (salt_a, salt_b), args.timeout)
    prime_ids, prime = client.generate(ids, salt_a, OUTPUT_TOKENS, input_scores=False)
    save(directory, "prime.json", prime)
    if prime["cached_tokens"] != 0 or prime["num_retractions"] != 0:
        message = "prime was not cold or retracted"
        raise BenchError(message)
    history = ids + prime_ids + [11]
    warm_ids, warm = client.generate(history, salt_a, OUTPUT_TOKENS, input_scores=False)
    save(directory, "warm.json", warm)
    if integer(warm["cached_tokens"]) <= len(ids) or warm["num_retractions"] != 0:
        message = "generated-prefix cache reuse not established or warm retracted"
        raise BenchError(message)
    _, cold = client.generate(history + warm_ids, salt_b, 0, input_scores=True)
    save(directory, "cold.json", cold)
    if cold["cached_tokens"] != 0 or cold["num_retractions"] != 0:
        message = "cold recomputation reused cache or retracted"
        raise BenchError(message)
    estimator = _estimate(warm, cold)
    passed = estimator < CUTOFF
    save(
        directory,
        "result.json",
        {
            "status": "pass" if passed else "fail",
            "emitted_token_approx_kl": estimator,
            "cutoff": CUTOFF,
            "aligned_token_count": OUTPUT_TOKENS,
            "warm_cached_tokens": warm["cached_tokens"],
            "cold_cached_tokens": cold["cached_tokens"],
            "scope": (
                "same-ID cold full-input scoring versus warm generated-token "
                "logprobs; not full-vocabulary KL"
            ),
        },
    )
    return passed


def main() -> int:
    """Run the diagnostic CLI and return its documented exit status.

    Returns:
        Zero for pass, one for fail, or two for an inconclusive run.

    """
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--endpoint", default="http://127.0.0.1:18020")
    parser.add_argument("--key-file", required=True)
    parser.add_argument(
        "--output", required=True, help="new private directory; must not exist"
    )
    parser.add_argument("--model", choices=[MODEL], default=MODEL)
    parser.add_argument("--input-tokens", type=int, default=45000)
    parser.add_argument("--timeout", type=int, default=900)
    parser.add_argument(
        "--confirm-qualified-profile", action="store_true", required=True
    )
    args = parser.parse_args()
    os.umask(0o077)
    signal.signal(signal.SIGALRM, expired)
    directory = Path(args.output)
    try:
        directory.mkdir(mode=0o700)
    except OSError:
        sys.stderr.write(
            "Cache diagnostic: cannot exclusively create output directory.\n"
        )
        return 2
    try:
        passed = execute(Settings.from_namespace(args), directory)
    except (
        BenchError,
        OSError,
        ValueError,
        http.client.HTTPException,
        RecursionError,
        OverflowError,
    ) as error:
        reason = (
            str(error)
            if isinstance(error, BenchError)
            else "bounded I/O, JSON or numeric operation failed"
        )
        try:
            save(
                directory, "failure.json", {"status": "inconclusive", "reason": reason}
            )
        except OSError:
            sys.stderr.write(
                "Cache diagnostic: failure artifact could not be written.\n"
            )
        sys.stderr.write(f"Cache diagnostic inconclusive: {reason}.\n")
        return 2
    sys.stdout.write(
        "Cache diagnostic: "
        + ("pass" if passed else "fail")
        + "; private artifacts written.\n"
    )
    return 0 if passed else 1


if __name__ == "__main__":
    sys.exit(main())
