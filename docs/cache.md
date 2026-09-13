# Salted generated-prefix diagnostic

Run only with approved access to an externally identified native Qwen service
with a declared context no larger than 262144 tokens. This retained engineering
diagnostic submits GPU work. It does not flush caches, restart services, change global cache
settings, or activate a host configuration. No runtime result is established by
adding this script.

## Run

```console
python3 bench/cache.py --key-file /path/to/api-key \
  --runtime-identity /private/runtime-identity.json \
  --output /private/parent/new-cache-probe \
  --confirm-runtime-identity
```

The parent directory must exist. The output directory must not exist. Creation
is exclusive and mode 0700; files use mode 0600 under a restrictive umask. A name
collision stops before writing anything. Keep all artifacts private. The script
prints only a pass/fail/inconclusive status, not prompts, tokens, credentials,
server configuration or HTTP response bodies.

`--endpoint` defaults to `http://127.0.0.1:18020` and accepts an explicit-port HTTP
loopback origin only, without a path, query, userinfo, proxy or redirect.
`--model` is fixed to `qwen3.8-27b`. `--input-tokens` defaults to 45000 and permits
1024 through `context_length - 257`, at most 261887. The upper bound reserves
both 128-token generation calls and the one-token continuation suffix within
the operator-declared context. Smaller context declarations support lower probe
stages without changing the estimator. `--timeout` is a whole-request deadline,
default 900 seconds, range 30 through 1800. Each response and request is limited
to 16 MiB. Duplicate object keys and
non-finite JSON numbers (including exponent overflow) are rejected. There are
five sequential API calls, with no automatic retry. This uses Python's standard
library and Linux/POSIX interval timers; no dependency installation is needed.

Exit codes: **0** passed this diagnostic; **1** exceeded its cutoff; **2** failed a
precondition or could not establish a valid comparison. Partial, allowlisted
phase artifacts remain available for an inconclusive run.

## Fixed comparison

1. Tokenize fresh synthetic ledger text through authenticated `/v1/tokenize`,
   using `{model, prompt, add_special_tokens: false}`. Validate its `tokens` and
   `count`. Repeat and truncate those exact token IDs to the requested input
   length. This is a synthetic token sequence, not a public or private corpus,
   chat conversation, or necessarily natural text after concatenation.
2. Prime a fresh random `cache_salt` A with that input and exactly 128 generated
   tokens. Require zero cached tokens and zero retractions. All generation uses
   native `/generate`, temperature 0, `ignore_eos: true`, no streaming, and
   `return_logprob: true`, with output-only logprobs (`logprob_start_len: -1`).
3. Append the exact prime output IDs and token ID **11**. Request another 128
   outputs under salt A. Require `meta_info.cached_tokens` strictly beyond the
   original prompt length and zero retractions. This establishes a generated
   prefix hit, not merely a cached initial prompt. Token 11 is a fixed synthetic
   continuation marker, not a user instruction or a claimed chat-template token.
4. Append those 128 warm output IDs. Under fresh salt B, recompute this complete
   identical ID sequence with zero new tokens, `logprob_start_len: 0`,
   `top_logprobs_num: 0`, and `return_text_in_logprobs: false`. Require zero cached
   tokens, zero outputs, zero retractions, and one input-logprob row per token.
   Validate every row's ID against the submitted IDs. Align the final 128 IDs
   with the warm output-logprob IDs before computing the estimator.
5. Compute `mean(expm1(cold_logprob - warm_logprob) -
   (cold_logprob - warm_logprob))`. The predeclared pass condition is **< 0.001**,
   matching the earlier emitted-token diagnostic in `docs/qualification.md`. Require finite
   nonpositive logprobs; only the first cold input row may have a null logprob.

Warm generation runs before cold recomputation. Two independent full-context
salted prefixes need not fit in the runtime's pool simultaneously. Use a fresh
invocation and fresh salts for each pair. Cache checkpoint alignment and eviction
determine the actual warm count; the script does not assume a hit at a specific
boundary. Choose an input length from the externally verified runtime's checkpoint
layout. Only reported cache metadata proves which prefix was reused.

## Runtime identity and external recipe provenance

Native refers to the SGLang API and model context, not target-only execution.
Both eager/CUDA-graph execution and DFLASH/no-speculation are supported when
honestly declared. There is no built-in launch recipe or runtime attestation. A pass does not qualify
or activate a deployment. `--confirm-runtime-identity` confirms that the operator
separately checked the running service against an exact, private identity file.
`/v1/models` must expose exactly the fixed model ID, but it cannot prove source,
model or launch identity. The script never reads `/server_info`, which may expose
secrets. Do not infer provenance from a repository revision or a historical report.

Supply a JSON object with exactly these fields (no credentials or raw server data):

| Field | Required value |
|---|---|
| `model` | `qwen3.8-27b` |
| `context_length` | verified runtime context integer, 1281 through 262144 |
| `execution` | `eager` or `cuda_graphs`, matching the actual runtime |
| `speculation` | `DFLASH` or `none`, matching the actual runtime |
| `cache_salt_scope` | `in_process` (normal local prefix caching stays enabled) |
| `external_cache_enabled` | boolean `false`; remote/L3 salt isolation is not assumed |
| `image_sha256` | deployed image's exact digest, without the `sha256:` prefix |
| `engine_base_commit` | exact 40-character lowercase hexadecimal base commit |
| `ordered_patch_sha256` | ordered array of applied patch SHA256s; empty if unpatched, at most 1024 |
| `launch_config_sha256` | SHA256 of the exact external effective launch configuration |
| `weights_sha256` | SHA256 of the inventory identifying all deployed target weight bytes |

All SHA256 digests must be 64 lowercase hexadecimal characters. The identity file
is limited to 65536 bytes and uses the same strict JSON parsing as API responses.
The script validates its shape, not whether its claims match the endpoint. Retain
the engine base, ordered patches, weight inventory and external launch configuration
privately for review. That external recipe must record all effective launch flags
and relevant environment settings, including context, pool, concurrency, cache policy,
precision, chunking and graph settings. No recipe is generated or guessed here.
Separately verify source/model identity and the absence of external cache storage.
Local prefix caching must remain enabled: salts namespace entries; they do not
disable prefix caching or reserve its memory.
A stale digest or a settings-only file is not evidence of the running bytes.

Before any HTTP request, the exact supplied identity bytes are copied exclusively
to `runtime-identity.json`. Their SHA256 is recorded in both `plan.json` and
`result.json`, explicitly marked `operator_declared` and
`runtime_identity_api_verified: false`. The observed model ID is recorded only
after `/v1/models` passes validation. No other runtime identity telemetry is
claimed; phase artifacts retain only allowlisted observed counts and scores.
Plan schema 2 contains diagnostic budgets, not an asserted historical 64K profile. The probe
does not establish that every allowed length fits GPU memory, or qualify output
capacity beyond its two 128-token calls. The token bound accounts for submitted
IDs and requested outputs, not engine-specific internal slots. A runtime that
reserves additional slots (including historical two-token overhead) can reject
near-maximum probes. Choose a smaller input after verifying the external recipe;
the script never silently clamps the input or retries a rejected request. Host power and service ownership remain
external responsibilities.

Artifacts contain the synthetic fixture and exact IDs, random salts, declared
runtime identity, input-ID digest, actual prompt/completion/cache/retraction counts,
allowlisted output IDs/logprobs, durations and final score. Raw generated text,
full HTTP responses and server configuration are not saved. `cold.json` contains
the full input-logprob array for exact alignment review.

## Scope and limitations

This is **same-ID cold full-input scoring versus warm generated-token scoring**.
It is not independent cold generation, full-vocabulary KL, broad quality,
DFlash/non-speculative equivalence, conversation recall, retrieval success or
proof for every checkpoint. Full-input-logprob recomputation takes a different
execution path from output-only generation; this intentionally reproduces the
prior numerical diagnostic, rather than claiming identical execution paths.
No tokens are retokenized between phases.

SGLang v0.5.19 declares `cache_salt` in `GenerateReqInput`. It is forwarded through
the tokenizer and scheduler to `RadixKey`, including Mamba cache insertion and
lookup. Nonempty salts namespace the **in-process** radix tree. Upstream
`RadixKey` explicitly excludes external L3/remote storage keys from that
contract. Do not use this cold-isolation claim with external storage enabled.
The operator must verify that the identified service has no external cache storage;
the identity file's declaration alone is not automatic verification.

Salts do not reserve memory or isolate scheduling. Other requests and idle
health generation may evict cache entries; these probes can evict other users'
entries and contend for runtime capacity. A cache precondition failure is
**inconclusive**, not a numerical failure. Obtain approved quiet access before a
comparison. No flush/restart is needed, but that does not make the work non-disruptive.

Historical schema references, not the selected runtime identity: SGLang v0.5.19 `entrypoints/http_server.py`,
`entrypoints/openai/{protocol,serving_tokenize}.py`, `managers/{io_struct,
tokenizer_manager,schedule_batch}.py` and `mem_cache/{radix_cache,
mamba_radix_cache}.py`. Source inspection alone is not a live qualification.
