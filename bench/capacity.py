# Copyright (c) 2026 inference contributors.
"""One exact-ID native capacity probe; see docs/capacity.md."""

import argparse
import hashlib
import http.client
import json
import os
import secrets
import signal
import sys
from pathlib import Path

from bench import cache

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


def execute(args: cache.Settings, directory: Path) -> None:
    """Submit one bounded exact-input capacity request and save private evidence.

    Raises:
        cache.BenchError: If declared capacity or observed request facts are invalid.

    """
    identity_sha256, context_length = cache.load_runtime_identity(
        directory, args.runtime_identity
    )
    client = cache.client_from_settings(
        args, context_length, reserved_tokens=RESERVED_TOKENS
    )
    ids = _input_ids(client, args.input_tokens, directory)
    salt = secrets.token_hex(32)
    cache.save(
        directory,
        "plan.json",
        {
            "schema_version": 1,
            "runtime_identity_sha256": identity_sha256,
            "runtime_identity_source": "operator_declared",
            "runtime_identity_api_verified": False,
            "observed_model_id": cache.MODEL,
            "context_length_operator_declared": context_length,
            "input_tokens": len(ids),
            "requested_output_tokens": cache.OUTPUT_TOKENS,
            "engine_overhead_tokens": ENGINE_OVERHEAD,
            "total_budget_tokens": len(ids) + RESERVED_TOKENS,
            "input_ids_sha256": hashlib.sha256(
                json.dumps(ids, separators=(",", ":")).encode()
            ).hexdigest(),
            "cache_salt": salt,
        },
    )
    observed = client.generate(
        ids, salt, cache.OUTPUT_TOKENS, input_scores=False, include_text=True
    )[1]
    cache.save(directory, "generation.json", observed)
    if observed["cached_tokens"] != 0 or observed["num_retractions"] != 0:
        message = "capacity request reused cache or retracted"
        raise cache.BenchError(message)
    cache.save(
        directory,
        "result.json",
        {
            "status": "request_completed",
            "runtime_identity_sha256": identity_sha256,
            "runtime_identity_source": "operator_declared",
            "runtime_identity_api_verified": False,
            "observed_model_id": cache.MODEL,
            "prompt_tokens": observed["prompt_tokens"],
            "completion_tokens": observed["completion_tokens"],
            "cached_tokens": observed["cached_tokens"],
            "num_retractions": observed["num_retractions"],
            "nonempty_output": True,
            "finite_aligned_output_logprobs": True,
            "meaningfulness": "operator_review_required",
            "prime_envs_quality": "not_evaluated",
            "scope": "one exact-ID request; not capacity qualification or quality",
        },
    )


def main() -> int:
    """Run one capacity probe without changing the service.

    Returns:
        Zero for a completed request; two for an inconclusive probe.

    """
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--endpoint", default="http://127.0.0.1:18020")
    parser.add_argument("--key-file", required=True)
    parser.add_argument("--runtime-identity", required=True)
    parser.add_argument("--input-tokens", type=int, required=True)
    parser.add_argument("--timeout", type=int, default=900)
    parser.add_argument("--output", required=True, help="new private directory")
    parser.add_argument(
        "--confirm-runtime-identity", action="store_true", required=True
    )
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
        execute(cache.Settings.from_namespace(args), directory)
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
            cache.save(
                directory, "failure.json", {"status": "inconclusive", "reason": reason}
            )
        except OSError:
            sys.stderr.write("Capacity probe: failure artifact could not be written.\n")
        sys.stderr.write(f"Capacity probe inconclusive: {reason}.\n")
        return 2
    sys.stdout.write("Capacity request completed; private output requires review.\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
