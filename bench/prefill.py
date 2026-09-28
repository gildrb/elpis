# Copyright (c) 2026 inference contributors.
"""Cold-prefill TTFT ladder for the EXL3 lane; see autoresearch.sh.

Every row sends one non-streaming 1-token request (TTFT) and then the same
prompt with a 32-token budget (continuation). A unique leading nonce line makes
each row's first 256-token KV page, and so every chained page after it, differ
from every earlier request of the ladder: each TTFT request is a cold prefill.
Rows are frozen and rendered before any generation and replayed from raw files.
"""

from __future__ import annotations

import hashlib
import itertools
import math
import time
from collections.abc import Callable
from pathlib import Path

from bench import exl3
from bench.exl3 import integer, mapping, require, sequence

PROTOCOL = "exl3-prefill-ttft-v1"
# (raw-content depth, repetitions), ascending depth; repetitions run consecutively.
LADDER = ((8192, 3), (32768, 3), (131072, 2), (262000, 1))
# The corpus always covers 1.05 x the deepest frozen row, whatever ladder is planned.
DEEPEST = 262000
COVERAGE_PERCENT = 105
BUDGETS = {"ttft": 1, "continuation": 32}
NONCE = "[prefill measurement {rep} of {reps} at depth {depth}]"
SAMPLING = {"temperature": 0, "top_p": 1, "n": 1, "stream": False}
ORDER = "ascending_depth_then_repetition; per row ttft then continuation"
CACHE_POLICY = (
    "unique leading nonce per row: its first 256-token KV page, and every chained "
    "page after it, differs from every earlier request of this ladder, so each TTFT "
    "request is a cold prefill with no prefix reuse; the continuation repeats that "
    "prompt and may reuse its pages; no flush, no warmup"
)
TTFT_SCOPE = (
    "streaming TTFT is unavailable (the server buffers SSE), so TTFT is the wall "
    "time of a 1-token non-streaming request: prefill plus the first verify round "
    "plus HTTP, monotonic from request send through complete response body"
)
PRIMARY_SCOPE = (
    "geometric mean over the ladder depths of prefill_tok_s_<depth> = sum of "
    "native prompt_tokens / sum of TTFT wall seconds at that depth"
)
ROW_FILES = tuple(
    f"{kind}-{name}.json"
    for kind in BUDGETS
    for name in ("request", "render-response", "response", "timing")
)


def check_ladder(ladder: tuple[tuple[int, int], ...]) -> None:
    """Accept only a nonempty ascending ladder inside the frozen corpus coverage."""
    require(bool(ladder), "Empty prefill ladder")
    require(
        all(type(depth) is int and type(reps) is int for depth, reps in ladder),
        "Prefill ladder entries must be exact integers",
    )
    require(all(reps > 0 for _, reps in ladder), "Prefill repetitions must be positive")
    depths = [depth for depth, _ in ladder]
    require(
        depths == sorted(set(depths)),
        "Prefill ladder depths must be strictly ascending",
    )
    require(
        depths[0] > 0 and depths[-1] <= DEEPEST,
        "Prefill depth outside the frozen corpus coverage",
    )


def metric_names(ladder: tuple[tuple[int, int], ...]) -> tuple[str, ...]:
    """Primary first, then per-depth prefill rate, TTFT and continuation wall."""
    check_ladder(ladder)
    return (
        "prefill_tok_s",
        *(f"prefill_tok_s_{depth}" for depth, _ in ladder),
        *(f"ttft_s_{depth}" for depth, _ in ladder),
        *(f"reuse_request_s_{depth}" for depth, _ in ladder),
    )


def corpus(source: Path, tokenizer: exl3.RawTokenizer) -> tuple[str, dict[str, object]]:
    """The C1 corpus prompts joined as C1 joins them, repeated to cover 1.05 x 262000."""
    prompts = exl3.corpus_prompts(source)
    required = -(-DEEPEST * COVERAGE_PERCENT // 100)
    # One pass plus its trailing separator is the repeating unit of the join.
    unit = tokenizer.count("\n\n".join(prompts) + "\n\n")
    require(unit > 0, "Frozen corpus pass has no tokens")
    factor = -(-required // unit)
    document = "\n\n".join(prompts * factor)
    tokens = tokenizer.count(document)
    require(
        tokens >= required,
        f"Prefill corpus covers {tokens} tokens, short of {required}",
    )
    return document, {
        "prompts": len(prompts),
        "join": "\n\n",
        "pass_tokens": unit,
        "repetitions": factor,
        "corpus_tokens": tokens,
        "required_tokens": required,
        "coverage": f"{COVERAGE_PERCENT}% of {DEEPEST}",
    }


def _sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def plan(
    directory: Path,
    client: exl3.Client,
    tokenizer: exl3.RawTokenizer,
    ladder: tuple[tuple[int, int], ...],
) -> dict[str, object]:
    """Freeze every prompt, both request bodies and their rendered IDs per row."""
    check_ladder(ladder)
    directory.mkdir(mode=0o700)
    document, coverage = corpus(
        directory.parent / "sources/bench/throughput-prompts.jsonl", tokenizer
    )
    rows: list[dict[str, object]] = []
    for depth, reps in ladder:
        for repetition in range(reps):
            started = time.monotonic_ns()
            nonce = NONCE.format(rep=repetition + 1, reps=reps, depth=depth)
            content, cut, count = exl3.sized_content(tokenizer, document, depth, nonce)
            row = directory / exl3._row_name(depth, repetition)
            row.mkdir(mode=0o700)
            record: dict[str, object] = {
                "depth_target": depth,
                "repetition": repetition,
                "repetitions": reps,
                "nonce": nonce,
                "corpus_prefix_chars": cut,
                "raw_content_tokens": count,
                "content_sha256": _sha(content.encode()),
            }
            rendered: list[int] | None = None
            for kind, budget in BUDGETS.items():
                payload = exl3.request_bytes({
                    "model": exl3.MODEL,
                    "messages": [{"role": "user", "content": content}],
                    "max_tokens": budget,
                    "temperature": 0,
                    "top_p": 1,
                    "n": 1,
                })
                exl3.write_new(row / f"{kind}-request.json", payload)
                status, raw = client.exchange(
                    "POST", "/v1/chat/completions/render", payload
                )
                exl3.write_new(row / f"{kind}-render-response.json", raw)
                require(status == 200, f"Render returned HTTP {status}")
                ids = exl3._token_ids(raw)
                require(
                    rendered is None or ids == rendered,
                    "TTFT and continuation requests render different prompts",
                )
                rendered = ids
                record[f"{kind}_request_sha256"] = _sha(payload)
                record[f"{kind}_render_response_sha256"] = _sha(raw)
            if rendered is None:
                raise ValueError("Prefill row rendered no request")
            require(
                len(rendered) + BUDGETS["continuation"] <= exl3.CONTEXT,
                "Rendered prompt plus continuation budget exceeds native context",
            )
            record["rendered_prompt_tokens"] = len(rendered)
            record["rendered_token_ids_sha256"] = _sha(exl3.canonical(rendered))
            record["planning_ns"] = time.monotonic_ns() - started
            rows.append(record)
    result: dict[str, object] = {
        "protocol": PROTOCOL,
        "ladder": [[depth, reps] for depth, reps in ladder],
        "order": ORDER,
        "concurrency": 1,
        "output_budgets": dict(BUDGETS),
        "nonce_template": NONCE,
        "instruction": exl3.INSTRUCTION,
        "raw_content_tolerance_tokens": 2,
        "raw_content_tokenizer_sha256": tokenizer.sha256,
        "corpus": coverage,
        "sampling": dict(SAMPLING),
        "cache_policy": CACHE_POLICY,
        "ttft_scope": TTFT_SCOPE,
        "rows": rows,
    }
    exl3.save(directory / "plan.json", result)
    return result


def run(
    directory: Path,
    client: exl3.Client,
    frozen: dict[str, object],
    checkpoint: Callable[[], object],
) -> None:
    """Send each row's two frozen requests once, in order; retain raw bytes first."""
    for value in sequence(frozen["rows"]):
        planned = mapping(value)
        checkpoint()
        row = directory / exl3._row_name(
            integer(planned["depth_target"]), integer(planned["repetition"])
        )
        for kind in BUDGETS:
            payload = (row / f"{kind}-request.json").read_bytes()
            started_unix = time.time_ns()
            started = time.monotonic_ns()
            status, raw = client.exchange("POST", "/v1/chat/completions", payload)
            received = time.monotonic_ns()
            exl3.write_new(row / f"{kind}-response.json", raw)
            exl3.save(
                row / f"{kind}-timing.json",
                {
                    "status": status,
                    "request_started_unix_ns": started_unix,
                    "request_started_monotonic_ns": started,
                    "response_received_monotonic_ns": received,
                    "clock": "monotonic from request send through complete response body",
                },
            )
            require(status == 200, f"Prefill {kind} request returned HTTP {status}")
        exl3.save(row / "row.json", measured_row(directory, planned))


def _exchange(row: Path, kind: str, planned: dict[str, object]) -> dict[str, object]:
    """Validate one request of a row entirely from its retained raw files."""
    payload = (row / f"{kind}-request.json").read_bytes()
    require(
        _sha(payload) == planned[f"{kind}_request_sha256"],
        f"Prefill {kind} request bytes differ from the frozen plan",
    )
    render = (row / f"{kind}-render-response.json").read_bytes()
    require(
        _sha(render) == planned[f"{kind}_render_response_sha256"],
        f"Prefill {kind} render receipt differs from the frozen plan",
    )
    ids = exl3._token_ids(render)
    rendered = integer(planned["rendered_prompt_tokens"])
    require(
        len(ids) == rendered
        and _sha(exl3.canonical(ids)) == planned["rendered_token_ids_sha256"],
        f"Prefill {kind} rendered IDs differ from the frozen plan",
    )
    timing = exl3.document(row / f"{kind}-timing.json")
    require(timing.get("status") == 200, f"Prefill {kind} request failed")
    started = integer(timing.get("request_started_monotonic_ns"))
    received = integer(timing.get("response_received_monotonic_ns"))
    wall = received - started
    require(wall > 0, f"Nonpositive prefill {kind} wall time")
    response = mapping(exl3.loads((row / f"{kind}-response.json").read_bytes()))
    choices = sequence(response.get("choices"))
    require(
        response.get("object") == "chat.completion"
        and response.get("model") == exl3.MODEL
        and len(choices) == 1,
        "Expected one chat completion",
    )
    choice = mapping(choices[0])
    message = mapping(choice.get("message"))
    finish = choice.get("finish_reason")
    content = message.get("content")
    reasoning = message.get("reasoning_content")
    require(
        choice.get("index") == 0
        and message.get("role") == "assistant"
        and set(message) == {"role", "content", "reasoning_content"}
        and isinstance(content, str)
        and (reasoning is None or isinstance(reasoning, str)),
        f"Incomplete or unexpected prefill {kind} choice",
    )
    usage = mapping(response.get("usage"))
    require(
        set(usage)
        in (
            {"prompt_tokens", "completion_tokens", "total_tokens"},
            {"prompt_tokens", "completion_tokens", "total_tokens", "exl3_spec"},
        ),
        f"Unexpected prefill {kind} usage fields",
    )
    prompt = integer(usage["prompt_tokens"])
    completion = integer(usage["completion_tokens"])
    require(
        prompt == rendered,
        f"Native {kind} prompt usage differs from the rendered request",
    )
    budget = BUDGETS[kind]
    require(
        integer(usage["total_tokens"]) == prompt + completion
        and 1 <= completion <= budget
        and finish in ("stop", "length")
        and (finish == "stop" or completion == budget)
        and (kind != "ttft" or completion == 1),
        f"Invalid prefill {kind} completion usage or finish",
    )
    spec = exl3._spec(usage["exl3_spec"], completion) if "exl3_spec" in usage else None
    generated: dict[str, object] = {"content": content, "reasoning_content": reasoning}
    return {
        "request_sha256": planned[f"{kind}_request_sha256"],
        "response_sha256": exl3.digest(row / f"{kind}-response.json"),
        "prompt_tokens": prompt,
        "completion_tokens": completion,
        "finish_reason": finish,
        "request_started_unix_ns": integer(timing.get("request_started_unix_ns")),
        "request_started_monotonic_ns": started,
        "response_received_monotonic_ns": received,
        "wall_ns": wall,
        "exl3_spec": spec,
        "text": generated,
        "text_sha256": _sha(exl3.canonical(generated)),
    }


def measured_row(directory: Path, planned: dict[str, object]) -> dict[str, object]:
    """Validate one row's TTFT and continuation from retained raw files."""
    row = directory / exl3._row_name(
        integer(planned["depth_target"]), integer(planned["repetition"])
    )
    ttft = _exchange(row, "ttft", planned)
    continuation = _exchange(row, "continuation", planned)
    require(
        integer(ttft["response_received_monotonic_ns"])
        <= integer(continuation["request_started_monotonic_ns"]),
        "Prefill requests overlapped; concurrency must be one",
    )
    ttft_wall = integer(ttft["wall_ns"])
    return {
        "depth_target": planned["depth_target"],
        "repetition": planned["repetition"],
        "rendered_prompt_tokens": planned["rendered_prompt_tokens"],
        "ttft": ttft,
        "continuation": continuation,
        "ttft_seconds": ttft_wall / 1_000_000_000,
        "prefill_tok_s": integer(ttft["prompt_tokens"]) * 1_000_000_000 / ttft_wall,
        "continuation_seconds": integer(continuation["wall_ns"]) / 1_000_000_000,
        "ttft_text": ttft["text"],
        "continuation_text": continuation["text"],
        "continuation_text_sha256": continuation["text_sha256"],
    }


def admit(
    evidence: exl3.Evidence,
    directory: Path,
    ladder: tuple[tuple[int, int], ...],
) -> dict[str, object]:
    """Recompute every row and the per-depth and primary metrics from raw files."""
    check_ladder(ladder)
    frozen = exl3.document(evidence.retain(directory / "plan.json"))
    require(
        frozen.get("protocol") == PROTOCOL
        and frozen.get("ladder") == [[depth, reps] for depth, reps in ladder]
        and frozen.get("output_budgets") == BUDGETS,
        "Unexpected prefill plan",
    )
    planned_rows = [mapping(value) for value in sequence(frozen["rows"])]
    require(
        [(row["depth_target"], row["repetition"]) for row in planned_rows]
        == [(depth, rep) for depth, reps in ladder for rep in range(reps)],
        "Prefill plan order differs",
    )
    rows: list[dict[str, object]] = []
    for planned in planned_rows:
        row = measured_row(directory, planned)
        name = exl3._row_name(
            integer(planned["depth_target"]), integer(planned["repetition"])
        )
        for filename in ROW_FILES:
            evidence.retain(directory / name / filename)
        require(
            exl3.document(evidence.retain(directory / name / "row.json")) == row,
            "Prefill producer row differs from raw replay",
        )
        rows.append(row)
    spans = [
        (
            integer(mapping(row[kind])["request_started_monotonic_ns"]),
            integer(mapping(row[kind])["response_received_monotonic_ns"]),
        )
        for row in rows
        for kind in BUDGETS
    ]
    require(
        all(
            previous[1] <= current[0] for previous, current in itertools.pairwise(spans)
        ),
        "Prefill requests overlapped; concurrency must be one",
    )
    rates: dict[str, float] = {}
    ttfts: dict[str, float] = {}
    reuses: dict[str, float] = {}
    pooled: dict[str, object] = {}
    for depth, reps in ladder:
        selected = [row for row in rows if row["depth_target"] == depth]
        require(len(selected) == reps, "Incomplete prefill ladder")
        prompt = sum(integer(mapping(row["ttft"])["prompt_tokens"]) for row in selected)
        ttft_wall = sum(integer(mapping(row["ttft"])["wall_ns"]) for row in selected)
        reuse_wall = sum(
            integer(mapping(row["continuation"])["wall_ns"]) for row in selected
        )
        require(
            prompt > 0 and ttft_wall > 0 and reuse_wall > 0,
            "Missing positive prefill window",
        )
        rates[f"prefill_tok_s_{depth}"] = prompt * 1_000_000_000 / ttft_wall
        ttfts[f"ttft_s_{depth}"] = ttft_wall / 1_000_000_000 / reps
        reuses[f"reuse_request_s_{depth}"] = reuse_wall / 1_000_000_000 / reps
        pooled[str(depth)] = {
            "prompt_tokens": prompt,
            "ttft_wall_ns": ttft_wall,
            "continuation_wall_ns": reuse_wall,
            "repetitions": reps,
        }
    primary = math.exp(
        math.fsum(math.log(rate) for rate in rates.values()) / len(rates)
    )
    metrics = {"prefill_tok_s": primary, **rates, **ttfts, **reuses}
    require(
        tuple(metrics) == metric_names(ladder)
        and all(math.isfinite(value) and value > 0 for value in metrics.values()),
        "Prefill metrics are incomplete or nonpositive",
    )
    return {
        "protocol": PROTOCOL,
        "ladder": [[depth, reps] for depth, reps in ladder],
        "rows": rows,
        "metrics": metrics,
        "pooled": pooled,
        "primary_scope": PRIMARY_SCOPE,
        "metric_scope": {
            "prefill_tok_s_<depth>": "sum native prompt_tokens / sum TTFT wall seconds at that depth",
            "ttft_s_<depth>": "mean TTFT wall seconds at that depth",
            "reuse_request_s_<depth>": "mean continuation wall seconds at that depth (32-token budget, same prompt right after its TTFT request); informational",
        },
        "cache_policy": CACHE_POLICY,
        "ttft_scope": TTFT_SCOPE,
    }
