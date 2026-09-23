# Exact-input native capacity diagnostic

Obtain approved exclusive GPU/service ownership before running this engineering
probe. It submits one generation request through SGLang's native API and **flushes
that owned service's cache first**. It never acquires the maintenance window,
starts/stops a service, changes runtime flags, retries or runs a quality score.
A successful request is not model-quality or deployment qualification. This
standalone diagnostic is not a prerequisite added to the tiny math baseline.

## Run one bounded probe

The current interface captures the actual running container before and after the
request through `serve.qualification capture`; it does not accept an operator's
`--runtime-identity` declaration or `--confirm-runtime-identity`. Admission requires
actual context 262144, a backed pool of at least 263168, the prepared packed
Qwen/DFlash2 pair, RTX 3090 at 280 W, and the pinned original Bend 2.0.26 release.
Captured identity binds the full container ID and start time, immutable image,
model inventories, Bend/compiler artifacts, runtime components and configuration
digests. Raw Docker Env/Cmd, server arguments and credentials are not evidence to
publish. Startup identity admission alone does not prove usable capacity.

Under an already-held exclusive maintenance window, set `OWNED_CONTAINER_ID` to
the full 64-hex ID of the running candidate you own. Passing
`--owned-container-id` explicitly authorizes its cache reset; it must equal the
captured ID. Use that same ID for `--container` rather than relying on the default
container name `qwen-inference-inference-1`.

```console
python3 -m bench.capacity --key-file /private/api-key \
  --container "$OWNED_CONTAINER_ID" \
  --owned-container-id "$OWNED_CONTAINER_ID" --seed 0 \
  --input-tokens 262014 --timeout 900 \
  --output /private/parent/new-capacity-probe
```

`--seed` is required and must be an unsigned 64-bit integer. It deterministically
derives the ledger nonce and cache salt under `qwen-native-capacity-seeded-v1`;
these are benchmark parameters, never authentication material. For paired runs,
retain the seed and optionally supply `--expected-input-ids-sha256` and
`--expected-request-body-sha256` from the earlier plan. A differing tokenization
or request hash is rejected **before** cache reset, not silently substituted.

Total request budget is `input_tokens + 128 output tokens + 2 engine overhead
slots`. `--input-tokens` accepts 1024 through 262014 without clamping. The two
slots are not submitted input IDs: actual `prompt_tokens` may exceed submitted
IDs by 0–2 backend-added tokens, and observed prompt plus output must fit 262144.
A smaller successful request is a diagnostic only; qualification's capacity gate
requires the full 262014-ID request. A runtime rejection is inconclusive, not a
reason to retry with a smaller input.

These historical total-budget stages remain useful planning references, not an
automatic or mandatory new ladder for the current tiny baseline. The current
probe always requires an admitted native-context instance, even for smaller
inputs. Each authorized invocation needs a fresh private output directory.

| Total budget | Exact `--input-tokens` | Output reserve | Engine slots |
|---:|---:|---:|---:|
| 131072 | 130942 | 128 | 2 |
| 163840 | 163710 | 128 | 2 |
| 196608 | 196478 | 128 | 2 |
| 229376 | 229246 | 128 | 2 |
| 245760 | 245630 | 128 | 2 |
| 262144 | 262014 | 128 | 2 |

The endpoint defaults to `http://127.0.0.1:18020`; the fixed model is `qwen3.8-27b`.
Use an explicit-port HTTP `127.0.0.1` origin without credentials, paths, proxies
or redirects for compatibility with both identity capture and the request client.
`--timeout` bounds each diagnostic HTTP request, not the whole command: 30–1800
seconds, default 900. Request and response bodies are bounded to 16 MiB; strict
JSON parsing rejects duplicate keys and non-finite numbers. There are five
sequential recorded diagnostic HTTP operations, plus the separate identity
captures' metadata/container checks. External ownership, the whole-window deadline
and recovery remain the operator's responsibility.

## Exact input and observed evidence

1. `GET /v1/models` must expose exactly the fixed model ID. Authenticated
   `POST /v1/tokenize` tokenizes the seeded synthetic ledger with
   `add_special_tokens: false`. Validate every ID and returned count, then
   repeat/truncate those exact IDs without claiming natural text at boundaries.
2. A second `POST /v1/tokenize` tokenizes the fixed triangle/square instruction.
   Append its IDs after enough ledger IDs to make the requested length exact.
   This is an inspectable engineering prompt, not a scored task, conversation,
   retrieval benchmark or context-recall score. No chat template or estimated
   text-to-token ratio is used.
3. After saving and checking the exact generation request, issue authenticated
   **`GET /flush_cache`**, without a JSON body. Require HTTP 200 and the exact
   pinned plain-text response (including both newlines):

   ```text
   Cache flushed.
   Please check backend logs for more details. (When there are running or waiting requests, the operation will not be performed.)
   ```

   Merely issuing a reset, receiving arbitrary JSON or assuming salt isolation is
   insufficient. A failed, unsupported or unacknowledged reset is inconclusive;
   there is no retry. The acknowledgment is not independent proof of quiescence:
   externally held exclusive ownership remains required.
4. `POST /generate` uses the deterministic `cache_salt`, temperature 0,
   `ignore_eos: true`, `max_new_tokens: 128`, `stream: false`,
   `return_logprob: true`, `logprob_start_len: -1`, `top_logprobs_num: 0` and
   `return_text_in_logprobs: false`. Require exactly 128 output IDs, allowed
   prompt overhead, length finish, nonempty text, finite nonpositive logprobs
   aligned with every output ID (no initial null), zero cached tokens and zero
   retractions. Prefix caching stays enabled; the salt is reproducible, not fresh
   random isolation, and does not replace the real reset.
5. Capture and match identity after the attempt, including on request failure.
   A failed after-capture cannot become successful evidence. Manually review any
   retained generated text: `meaningfulness` remains `operator_review_required`,
   and quality and sustained concurrency/cache qualification remain
   `not_evaluated`.

Forced 128-token output may continue irrelevantly after a good short answer;
nonempty output alone establishes neither coherence nor model quality. A cache
flush affects the entire service, and this request can evict cache entries.
Neither a salt nor a flush reserves GPU memory or proves cache correctness.

## Private artifacts and rejection semantics

The output parent must already exist; the output directory must not exist.
Creation is exclusive with mode 0700 and umask 077; artifact files are private
(mode 0600). A collision stops without overwriting. Do not publish raw generated
output, raw service logs or credentials.

- `identity-before.json`, `identity-after.json`: actual capture envelopes, with
  matching identity and the native attempt's exit code in the after-capture.
- `sources/`: retained capacity/cache/decode producer source bytes and hashes.
- `fixture.json`, `input-ids.json`: exact source/instruction text, tokenizer IDs
  and final submitted input IDs.
- `request.json`, `plan.json`: exact canonical native request, schema 3 budgets,
  protocol/seed/nonce/salt, workload hashes and optional expected hashes.
- `http-000/` through `http-004/`: ordered operation, POST request bytes where
  applicable, HTTP status, raw response bytes, parsed response and monotonic
  request/response timestamps. Files from an interrupted operation may be partial
  or absent; they are not successful evidence.
- `cache-reset.json`: owned-container and before-identity binding, validated
  acknowledgment and response hash.
- `response.json`, `generation.json`: private native response and derived output
  IDs/text, logprobs, observed counts, prompt overhead and request hash. Timings
  here are diagnostic, not a throughput qualification.
- `result.json`: completed request, source/artifact closure, identities, observed
  coverage and explicit unpassed quality/review gates. A smaller completed input
  has `near_native_completed: false` and an explicit rejection reason.
- `request-failure.json` records a failure within the request phase; `failure.json`
  records an inconclusive run. Completed phase artifacts remain. An after-capture
  failure may be the outer failure while the request failure remains separately
  available.

Exit **0** means this exact request completed and the after-identity matched.
Exit **2** means a precondition, request, capture or required evidence failed.
Neither is a quality score. Qualification separately replays the raw five-operation
sequence, tokenizer receipts, seeded fixture, exact request, reset, source hashes,
identity bounds and response counts. Its near-native gate requires 262014 submitted
IDs and 262142–262144 actual prompt-plus-output tokens, not a smaller request's
successful exit. This still establishes only one allocation/generation request,
not sustained concurrency, recurrence/cache correctness or model quality.

## Completed native request and earlier interruption

The [2026-09-20 native baseline ledger](../bench/results/bend20-native-baseline-20260920.json)
records one completed request on the 29-patch Bend 2.0.20 image
`sha256:54eed6bfc1726ba03753c19fdbbf4b28792e533b030c32716877b4599cd4b499`:
**262014 submitted/prompt tokens + 128 output = 262142 actual tokens**, within
the native 262144 context and backed 263168-token pool. Before/after identities
matched; cached tokens and retractions were both zero, and all output logprobs
were finite and aligned. The native generation HTTP interval was **638.808 s**;
this is diagnostic wall time, not a throughput qualification.

Seed **20260920**, exact input-ID hash
`36bad3462e716497b1c2e1e73f987c9c999d71f213fdfd071f3135f074396de2`
and request-body hash
`b03cd9fcb92458efaa428bd2998e8da334a92b4ddbc3b1fe4c85a62ecbf8a747`
match the earlier interrupted trial, as reported by the operator. Private output
review found a coherent initial geometric answer followed by the recorded forced
continuation after EOS under `ignore_eos`. The automated `meaningfulness` field
remains `operator_review_required`; this review does not turn the engineering
probe into a quality score.

The earlier full-size attempt remains **inconclusive**: its 900-second guardian
interrupted the request, with `RemoteDisconnected` and a failed identity-after
capture. That attempt established no completed output or throughput result; its
FP8 recovery was recorded as `restored_authenticated`. The later completion does
not rewrite that history. The operator subsequently observed the math window's
guardian report `baseline_restored_authenticated` with exit 0; this does not
confirm recovery for any later validation window. FP8 65536 recovery is never
native qualification.

This is one near-native allocation/generation request, not sustained concurrency,
cache/recurrence correctness, peak-memory safety, direct-context quality or
full-profile promotion. The separate first tiny-math/C1 measurement is linked
from [qualification](qualification.md), together with the completed standalone
component numerical suite and its explicit limits. Full served-path and
full-profile qualification remain unestablished.
