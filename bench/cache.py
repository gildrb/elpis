# Copyright (c) 2026 Gil Rodrigues
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
NATIVE_CONTEXT_TOKENS = 262144
MAX_TOKEN_IDS = NATIVE_CONTEXT_TOKENS
CONTINUATION_TOKEN = 11
MAX_IDENTITY_BYTES = 65536
SHA256_LENGTH = 64
GIT_COMMIT_LENGTH = 40
MAX_PATCHES = 1024
MAX_TOKEN_ID = 2147483647
LOGPROB_FIELDS = 3
HTTP_OK = 200
MAX_PORT = 65535
MIN_INPUT_TOKENS = 1024
MAX_INPUT_TOKENS = NATIVE_CONTEXT_TOKENS - 2 * OUTPUT_TOKENS - 1
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
    runtime_identity: str
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
        runtime_identity = values.get("runtime_identity")
        if (
            not isinstance(endpoint, str)
            or not isinstance(key_file, str)
            or not isinstance(runtime_identity, str)
        ):
            message = "invalid endpoint, credential or runtime identity path"
            raise BenchError(message)
        return cls(
            endpoint,
            key_file,
            runtime_identity,
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
    context_length: int

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
        self,
        ids: list[int],
        salt: str,
        outputs: int,
        *,
        input_scores: bool,
        include_text: bool = False,
    ) -> tuple[list[int], dict[str, object]]:
        """Generate tokens and validate allowlisted scoring metadata.

        Returns:
            Output token IDs and allowlisted scoring metadata.

        Raises:
            BenchError: If validation or request preconditions fail.

        """
        if (
            len(ids) == 0
            or outputs not in {0, OUTPUT_TOKENS}
            or len(ids) + outputs > self.context_length
        ):
            message = "generation exceeds bounded native context budget"
            raise BenchError(message)
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
        selected: dict[str, object] = {
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
        if include_text:
            text = response.get("text")
            if not isinstance(text, str) or len(text.strip()) == 0:
                message = "generated text is missing or empty"
                raise BenchError(message)
            selected["output_text"] = text
        return output, selected


def client_from_settings(
    args: Settings, context_length: int, *, reserved_tokens: int = 2 * OUTPUT_TOKENS + 1
) -> Client:
    """Validate local request settings, credentials and reserved token budget.

    Returns:
        A bounded authenticated loopback client.

    Raises:
        BenchError: If settings or credentials fail validation.

    """
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
        reserved_tokens < OUTPUT_TOKENS
        or not MIN_INPUT_TOKENS <= args.input_tokens <= context_length - reserved_tokens
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
    return Client(endpoint.hostname, port, key, args.timeout, context_length)


def make_fixture(client: Client, input_tokens: int) -> tuple[str, list[int], list[int]]:
    """Verify the served model and build exact IDs from authenticated tokenization.

    Returns:
        Synthetic source text, seed IDs and repeated/truncated input IDs.

    Raises:
        BenchError: If model identity or tokenizer counts do not match.

    """
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


def _validate_provenance(identity: dict[str, object]) -> None:
    patches = identity.get("ordered_patch_sha256")
    if not isinstance(patches, list) or len(patches) > MAX_PATCHES:
        message = "runtime identity requires a bounded ordered patch digest list"
        raise BenchError(message)
    digests = [
        identity.get("image_sha256"),
        identity.get("launch_config_sha256"),
        identity.get("weights_sha256"),
        *patches,
    ]
    for value in digests:
        if (
            not isinstance(value, str)
            or len(value) != SHA256_LENGTH
            or not all(character in "0123456789abcdef" for character in value)
        ):
            message = "runtime identity requires lowercase SHA256 provenance digests"
            raise BenchError(message)
    commit = identity.get("engine_base_commit")
    if (
        not isinstance(commit, str)
        or len(commit) != GIT_COMMIT_LENGTH
        or not all(character in "0123456789abcdef" for character in commit)
    ):
        message = "runtime identity requires the exact engine base commit"
        raise BenchError(message)


def load_runtime_identity(directory: Path, path: str) -> tuple[str, int]:
    """Validate and exclusively snapshot exact operator-declared identity bytes.

    Returns:
        Identity SHA256 and declared runtime context length.

    Raises:
        BenchError: If the bounded identity declaration is invalid.

    """
    with Path(path).open("rb") as handle:
        raw = handle.read(MAX_IDENTITY_BYTES + 1)
    if len(raw) > MAX_IDENTITY_BYTES:
        message = "runtime identity size limit exceeded"
        raise BenchError(message)
    identity = mapping(
        json.loads(
            raw,
            object_pairs_hook=json_object,
            parse_float=json_float,
            parse_constant=json_constant,
        )
    )
    context_length = integer(identity.get("context_length"))
    if identity.keys() != {
        "image_sha256",
        "engine_base_commit",
        "ordered_patch_sha256",
        "launch_config_sha256",
        "weights_sha256",
        "model",
        "context_length",
        "execution",
        "speculation",
        "cache_salt_scope",
        "external_cache_enabled",
    }:
        message = "runtime identity field set mismatch"
        raise BenchError(message)
    if (
        identity.get("model") != MODEL
        or not MIN_INPUT_TOKENS + 2 * OUTPUT_TOKENS + 1
        <= context_length
        <= NATIVE_CONTEXT_TOKENS
        or identity.get("cache_salt_scope") != "in_process"
        or identity.get("external_cache_enabled") is not False
    ):
        message = (
            "runtime identity requires bounded native context and local salt scope"
        )
        raise BenchError(message)
    execution = identity.get("execution")
    speculation = identity.get("speculation")
    if (
        not isinstance(execution, str)
        or execution not in {"eager", "cuda_graphs"}
        or not isinstance(speculation, str)
        or speculation not in {"DFLASH", "none"}
    ):
        message = "runtime identity requires declared execution and speculation modes"
        raise BenchError(message)
    _validate_provenance(identity)
    with (directory / "runtime-identity.json").open("xb") as handle:
        handle.write(raw)
    return hashlib.sha256(raw).hexdigest(), context_length


def _save_plan(
    directory: Path,
    ids: list[int],
    salts: tuple[str, str],
    client: Client,
    identity_sha256: str,
) -> None:
    salt_a, salt_b = salts
    save(
        directory,
        "plan.json",
        {
            "schema_version": 2,
            "model": MODEL,
            "runtime_identity_sha256": identity_sha256,
            "runtime_identity_api_verified": False,
            "runtime_identity_source": "operator_declared",
            "observed_model_id": MODEL,
            "context_length_operator_declared": client.context_length,
            "input_tokens": len(ids),
            "prime_outputs": OUTPUT_TOKENS,
            "warm_outputs": OUTPUT_TOKENS,
            "continuation_token": CONTINUATION_TOKEN,
            "salt_a": salt_a,
            "salt_b": salt_b,
            "cutoff": CUTOFF,
            "request_timeout_seconds": client.timeout,
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
    identity_sha256, context_length = load_runtime_identity(
        directory, args.runtime_identity
    )
    client = client_from_settings(args, context_length)
    fixture = make_fixture(client, args.input_tokens)
    ids = fixture[2]
    salts = secrets.token_hex(32), secrets.token_hex(32)
    if salts[0] == salts[1]:
        message = "cache namespace collision"
        raise BenchError(message)
    save(
        directory,
        "fixture.json",
        {"synthetic_text": fixture[0], "seed_ids": fixture[1], "input_ids": ids},
    )
    _save_plan(directory, ids, salts, client, identity_sha256)
    prime_ids, prime = client.generate(ids, salts[0], OUTPUT_TOKENS, input_scores=False)
    save(directory, "prime.json", prime)
    if prime["cached_tokens"] != 0 or prime["num_retractions"] != 0:
        message = "prime was not cold or retracted"
        raise BenchError(message)
    history = ids + prime_ids + [CONTINUATION_TOKEN]
    warm_ids, warm = client.generate(
        history, salts[0], OUTPUT_TOKENS, input_scores=False
    )
    save(directory, "warm.json", warm)
    if integer(warm["cached_tokens"]) <= len(ids) or warm["num_retractions"] != 0:
        message = "generated-prefix cache reuse not established or warm retracted"
        raise BenchError(message)
    cold = client.generate(history + warm_ids, salts[1], 0, input_scores=True)[1]
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
            "runtime_identity_sha256": identity_sha256,
            "runtime_identity_api_verified": False,
            "runtime_identity_source": "operator_declared",
            "observed_model_id": MODEL,
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
        "--runtime-identity", required=True, help="operator-supplied identity JSON"
    )
    parser.add_argument(
        "--output", required=True, help="new private directory; must not exist"
    )
    parser.add_argument("--model", choices=[MODEL], default=MODEL)
    parser.add_argument(
        "--input-tokens",
        type=int,
        default=45000,
        help=f"{MIN_INPUT_TOKENS}..{MAX_INPUT_TOKENS}; bounded by declared context",
    )
    parser.add_argument("--timeout", type=int, default=900)
    parser.add_argument(
        "--confirm-runtime-identity", action="store_true", required=True
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
