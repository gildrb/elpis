# Salted generated-prefix diagnostic

Run only with approved access to the running, qualified Qwen service. This script
submits GPU work. It does not flush caches, restart services, change global cache
settings, or activate a host configuration. No runtime result is established by
adding this script.

## Run

```console
python3 bench/cache.py --key-file /path/to/api-key \
  --output /private/parent/new-cache-probe \
  --confirm-qualified-profile
```

The parent directory must exist. The output directory must not exist. Creation
is exclusive and mode 0700; files use mode 0600 under a restrictive umask. A name
collision stops before writing anything. Keep all artifacts private. The script
prints only a pass/fail/inconclusive status, not prompts, tokens, credentials,
server configuration or HTTP response bodies.

`--endpoint` defaults to `http://127.0.0.1:18020` and accepts an explicit-port HTTP
loopback origin only, without a path, query, userinfo, proxy or redirect.
`--model` is fixed to `qwen3.8-27b`. `--input-tokens` defaults to 45000 and permits
1024 through 65000. `--timeout` is a whole-request deadline, default 900 seconds,
range 30 through 1800. Each response and request is limited to 16 MiB. Duplicate object keys and
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

Warm replay runs before cold recomputation: the 66560-token pool cannot retain
two independent full-context salted prefixes at once. Use a fresh invocation
and fresh salts for each pair. Cache checkpoint alignment and eviction determine
the actual warm count; the script does not assume a hit at a specific boundary.
For a focused candidate near **46016**, `--input-tokens 45900` puts that boundary
within the 128 generated prime tokens, but only reported cache metadata proves
which checkpoint was reused.

## Profile commitment and evidence

`--confirm-qualified-profile` is an operator confirmation, **not automatic
runtime attestation**. `/v1/models` must expose exactly the fixed model ID. The
script does not read `/server_info` because that response can contain secrets.
Before running, separately verify the guarded service's pinned image and source
hashes, retained compact target/draft and unchanged qualified entrypoint.
`plan.json` records the required image digest, historical source revision and
entrypoint hash, not proof that the endpoint runs those bytes. The current
mandatory source manifest is `patches/manifest.json`; reviewed replacements are
local files in `patches/`. The historical fork revision is provenance only.
Serving and this diagnostic do not fetch or depend on access to that fork.

The committed profile is context **65536**, pool cap **66560**, C1, static fraction
**0.94**, prefill **1024**, Mamba **extra_buffer/K8/BF16**, FP8 KV, input-logprob
chunk **256**, DFlash block **8**, draft window **2048**, FlashInfer target and
draft attention, `NCCL_MAX_CTAS=1` and sleep-on-idle. The retained target is
`compact-target-rholsc8k/artifact`, with dense embeddings and the packed W4 head;
the draft is `Qwen3.8-27B-DFlash2-W4A16`. The output-capacity commitment remains
**8192**, but this diagnostic generates only **128** tokens per generation call.
It neither changes nor qualifies output capacity. The 280 W host policy remains
consumer-owned. Both mandatory source/model guard phases remain required.

Artifacts contain the synthetic fixture and exact IDs, random salts, declared
profile, input-ID digest, actual prompt/completion/cache/retraction counts,
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
The selected service does not configure external L3 storage.

Salts do not reserve memory or isolate scheduling. Other requests and idle
health generation may evict cache entries; these probes can evict other users'
entries and contend for C1. A cache precondition failure is **inconclusive**, not
a numerical failure. Obtain approved quiet access before a comparison. No
flush/restart is needed, but that does not make the work non-disruptive.

Source schema references: SGLang v0.5.19 `entrypoints/http_server.py`,
`entrypoints/openai/{protocol,serving_tokenize}.py`, `managers/{io_struct,
tokenizer_manager,schedule_batch}.py` and `mem_cache/{radix_cache,
mamba_radix_cache}.py`. Source inspection alone is not a live qualification.
