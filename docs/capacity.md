# Exact-input native capacity diagnostic

Obtain approved quiet GPU access before running this engineering probe. It submits
one generation request through SGLang's native API. Native does not mean
target-only: declare actual eager/CUDA-graph execution and DFLASH/no-speculation
in the required identity file. It never starts, stops or flushes a service, changes
runtime flags, retries a request or runs a quality score. A successful HTTP request
is not model-quality or deployment qualification.

## Run one bounded probe

Supply the exact operator-declared identity JSON described in [cache.md](cache.md).
Its context may be smaller than 262144. The script copies the exact bytes privately
and records their SHA256. It does not attest that the endpoint runs those bytes.
Keep the referenced engine base, ordered patches, deployed image, effective launch
configuration and target weight inventory available for private review.

```console
python3 -m bench.capacity --key-file /private/api-key \
  --runtime-identity /private/runtime-identity.json \
  --input-tokens 262014 --output /private/parent/new-capacity-probe \
  --confirm-runtime-identity
```

This example requires a declared 262144-token context. Total request budget is
`input_tokens + 128 output tokens + 2 engine overhead tokens`. The two internal
slots follow the conservative native request contract; they are not submitted
input IDs. `--input-tokens` must be at least 1024 and no greater than the declared
context minus 130. No input is silently clamped. A runtime with further limits can
still reject the request, producing an inconclusive artifact rather than a retry.

Run the following six total-budget stages separately, in order. The operator must
verify that the declared running context can accommodate each stage; the script
does not reconfigure it. Each stage needs its own approved invocation and new
private output directory.

| Total budget | Exact `--input-tokens` | Output reserve | Engine slots |
|---:|---:|---:|---:|
| 131072 | 130942 | 128 | 2 |
| 163840 | 163710 | 128 | 2 |
| 196608 | 196478 | 128 | 2 |
| 229376 | 229246 | 128 | 2 |
| 245760 | 245630 | 128 | 2 |
| 262144 | 262014 | 128 | 2 |

The endpoint defaults to `http://127.0.0.1:18020`. The fixed model is `qwen3.8-27b`.
The shared client permits explicit-port HTTP loopback origins only, without
credentials, paths, proxies or redirects. `--timeout` bounds each whole request:
30 through 1800 seconds, default 900. Bodies are bounded to 16 MiB. Identity JSON
is bounded to 65536 bytes. Strict parsing rejects duplicate keys and non-finite
numbers. There are four sequential HTTP calls, with no automatic retry.

## Exact input and observed evidence

1. Verify `/v1/models` exposes exactly the fixed model ID. Tokenize a fresh random
   synthetic ledger through authenticated `/v1/tokenize`. Validate all IDs and the
   returned count. Repeat/truncate those exact IDs, without claiming natural text
   at repetition boundaries.
2. Tokenize a short instruction separately through the same endpoint. Append its
   exact IDs after enough ledger IDs to make the requested input length exact.
   The instruction asks for a plain-English explanation of triangles and squares
   with everyday examples. It is an engineering output prompt, not a scored task
   or a benchmark corpus. No guessed text-to-token ratio or chat template is used.
3. Under a fresh random `cache_salt`, call native `/generate` with temperature 0,
   `ignore_eos: true`, exactly 128 requested outputs, no streaming and output-only
   logprobs. Require matching observed input/output counts, finite nonpositive
   logprobs aligned with all output IDs, nonempty output text, zero cached tokens
   and zero retractions. Salt isolation assumes in-process prefix caching with no
   remote/L3 cache, as declared and separately verified by the operator.
4. Review private generated text manually for meaningfulness. A completed request
   leaves `meaningfulness: operator_review_required` and
   `prime_envs_quality: not_evaluated`. It does not mark either gate passed.

The synthetic text is not a conversation, retrieval task or context-recall score.
The appended instruction only makes an answer inspectable. Forced 128-token output
may include irrelevant continuation after a good short answer; nonempty output
alone does not establish coherence. Normal prefix caching stays enabled. Salts do
not isolate scheduling or reserve memory, and this request can evict other users'
cache entries.

## Private artifacts and exit status

The output parent must already exist; the output directory must not exist. Creation
is exclusive, with mode 0700 and a restrictive umask. Artifact files are exclusive
and mode 0600. A directory collision stops without overwriting it. Do not publish
raw generated output or credentials.

- `runtime-identity.json`: original operator-declared identity bytes.
- `fixture.json`: exact source/instruction text, seed/instruction IDs and input IDs.
- `plan.json`: budgets, input-ID hash, identity hash, salt and observed model ID.
- `generation.json`: private text, exact output IDs, finite logprobs and allowlisted
  observed counts. Shared-client elapsed time is diagnostic metadata, not a
  throughput claim; use SGLang's official benchmark for standard timing.
- `result.json`: `request_completed` plus observed counts and explicit unpassed
  review/quality gates. `failure.json` instead records a sanitized inconclusive
  failure; any completed phase artifacts remain available.

Exit **0** means this one exact request completed with the listed checks. Exit
**2** means a precondition or request failed, or valid evidence was unavailable.
Neither exit code is a quality score. This does not run the six-stage ladder
automatically; obtain approval and use a fresh output directory for each stage.
No runtime results are established by adding this script or checking its help.
