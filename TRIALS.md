# Trial log

## Target selection

“Qwen 27B Max” was resolved to the open `Qwen/Qwen3.8-27B` model. The API-only Max model is not a 27B checkpoint. LocalMaxxing and the syv-ai RTX 3090 work identified patched vLLM with AutoRound W4A16 as the fastest demonstrated single-card path that retained at least 64K context.

## 200 W baseline

The first controlled benchmark kept the existing 200 W policy. All candidates used the same pinned image, model revisions, 65,536 context, BF16 KV cache, prefix caching, one active sequence, and greedy real-prompt suite.

| Candidate | Median or observed decode | Outcome |
|---|---:|---|
| DFlash2, 7 drafts | 72.6 tok/s median | Selected |
| MTP, 4 drafts | 63.2 tok/s median | Rejected: about 15% slower |
| DFlash2 plus n-gram chain | 66.7–69.7 tok/s | Rejected: realistic regression |

DFlash2 used about 1 GB more VRAM than MTP but delivered the best tok/s and tok/J. The optional n-gram chain did not provide a useful gain on the document-copy task and reduced combined document throughput from 84.5 to 80.4 tok/s.

## Prefix cache

A repeated 23,196-token document prompt reached its first generated token in 1.22 seconds after the first turn, versus 29.71 seconds cold. This is a real agent benefit but is separate from steady decode throughput.

## Long-context false failure

The upstream needle script initially returned an empty visible answer at approximately 60K tokens. The model had spent its 32-token output allowance in the reasoning channel because the script did not disable thinking. This was a probe defect, not a context failure.

`needle-bench.py` makes the contract explicit: thinking disabled, greedy decoding, 64 output tokens, and measured API usage. It passed with 60,042 prompt tokens and recovered `ZXCVBNM12345` from 90% depth in 98.745 seconds.

## API and agent behavior

The selected DFlash2 configuration passed all 12 upstream API smoke checks, including deterministic greedy output, seeded sampling, logprobs, structured output, streaming, explicit thinking, and a 20K prompt. `tool-smoke.py` also produced the forced Hermes call `health_check({"status":"ok"})`.

## First guarded deployment

Commit `20bb430` built, staged, and booted successfully, but `qwen-inference.service` failed before `ExecStartPre` with systemd status `226/NAMESPACE`. The configured writable path did not exist. The guarded boot workflow installs a prebuilt generation and does not execute `system.activationScripts` in the way the module assumed.

The repair replaces that assumption with a root system service that creates the state directories after local filesystems mount and before user sessions. The user service allows the existing parent in its namespace and waits boundedly for the root service. A Nix contract now checks the root service ordering, required mount, oneshot persistence, and user-service writable parent. Full x86_64 Linux validation passes.

## 250 W policy

The 200 W trace kept GDDR6X at full speed while the GPU core fell to roughly 525–645 MHz. The user selected 250 W as the next efficiency point. This changes only power headroom: model weights, quantization, DFlash verification, context length, KV precision, prefix caching, reasoning, and sampling remain unchanged.

The 250 W run reached 123.2, 120.5, and 119.8 tok/s: **120.5 tok/s median**, 66.0% above 200 W. Cap-normalized efficiency rose from 0.363 to 0.482 tok/J, or 32.8%. Sustained temperature remained 69–71°C with a 54–57% fan command. The 60,042-token retrieval fell from 98.745 to 71.862 seconds, all 12 API/thinking checks passed, and the dependency-free 200-question GSM8K gate scored 95.5%.

## Rootless loopback publication

The repaired service then started successfully inside its container, but the authenticated host probe could not connect. Docker recorded the requested `127.0.0.1:18020` binding in `HostConfig`, while `NetworkSettings.Ports` was null. Rootless Docker did not publish a port for a container attached only to an `internal` bridge.

The corrected Compose contract keeps the API bound to host loopback but uses the rootless default bridge. The inference container remains read-only, capability-free, authenticated, model-read-only, and pinned; telemetry and runtime model preparation remain disabled. A live candidate deployment passed the authenticated tool-call probe from the host.

## Hermes boot synchronization

The next live check found Hermes still using its previous Ollama model. The upstream Hermes Nix module merges managed `config.yaml` settings from `system.activationScripts`, which the guarded boot-only deployment does not execute. Its new Nix settings therefore existed in the closure but not on disk.

The boot repair reuses the upstream merge script inside the already ordered `hermes-minimal-profile` oneshot. Qwen’s root state service now invokes the existing idempotent credential preparer as the service user before Hermes starts. Contracts inspect both generated boot scripts, and full Linux validation passes.

## Hermes named-provider authentication

The first real Hermes turn reached `http://127.0.0.1:18020/v1` but returned HTTP 401. `provider: custom` uses the generic OpenAI-compatible route and does not resolve a named `custom_providers` entry’s `key_env`. The correct identity is `custom:qwen-local` for both the default model and `qwen` alias. A live CLI override using that identity authenticated successfully, exposed Qwen’s reasoning channel, and returned `QWEN_OK`.

## Hermes v0.21.0

The pinned Hermes input moves from `v2026.8.19` / v0.20.5 to the latest stable `v2026.8.31` / v0.21.0 release at revision `29112bef099274229cadff79cdff7bf7b99c4b77`. The full x86_64 package, NixOS closure, generated managed configuration, and repository contract suite build successfully.

## SGLang capacity repair

The first SGLang boot served `max_total_num_tokens=13,758` and crash-looped under real Hermes load. Three separate measurements on the live card: the pinned AWQ weights load at 19.11 GB of 23.56 GB; post-init Triton JIT for the GDN kernels plus NCCL buffers consume about 1.8 GB outside the static pool; and `extra_buffer` reserves 5 mamba state slots per request, so `--max-mamba-cache-size 8` is already near the floor of 5. Hermes turns arrive with about a 12.2K-token prompt and an 8K output budget, which cannot fit a 13.7K pool: oversized requests were rejected and concurrent queueing hit the tokenizer stream timeout, which fail-fast kills the whole server.

Measured remedies, applied together: `--mamba-ssm-dtype bfloat16` (halves the GDN state, default was wider), `--kv-cache-dtype fp8_e4m3` (halves full-attention KV bytes per token), `--mem-fraction-static 0.89` (moves about 0.7 GB back outside the pool for JIT and NCCL), and `PYTORCH_CUDA_ALLOC_CONF=expandable_segments:True`. The result is `max_total_num_tokens=27,565` with 2.22 GB free after init. A live probe of that configuration passed the tool-call contract, completed a 10,163-token prompt with thinking enabled, and stayed healthy for follow-up requests, where the previous configuration died.


## 2026-09-12: controlled SGLang compact-target and batching trials

**Status:** the target remains sustained **150 single-request decode tok/s**, not 150 aggregate tok/s. It is not established by the completed eight-prompt C1 runs. The corrected block-8 DFLASH fallback reached **133.13 / 126.62 single-request decode tok/s** in two runs. Production promotion and same-target quality parity remain unqualified; these are maintenance-candidate measurements, not a change to the selected deployment above.

### Measurement contract and provenance

The pinned historical vLLM 0.27.1 HTTP client used eight shuffled custom prompts, seed 0, streaming `/v1/completions`, temperature 0, thinking enabled by the inherited chat template, EOS enabled and a 1,024-output-token cap. Dataset SHA256: `27da4fd8b2dcc133b98cec54bc337c34f5acb1b6372cc2fea1d8a92da9c78650`. Dataset/client evidence: `/tmp/inference-bench-client-dlvu56wn/`; invocation and image identity: `/tmp/inference-benchmark-client-ready.md`. No generated prompts, answers or credentials are recorded here.

“Decode” below is **reciprocal unweighted mean request TPOT**, `1000 / mean_tpot_ms`, using native unrounded JSON. It is not aggregate throughput. Aggregate is successful output tokens divided by benchmark wall seconds. Recovered request E2E is `TTFT + sum(ITLs)`; TPOT is `sum(ITLs)/(output_tokens - 1)`. ITLs are stream-chunk intervals: speculative chunks contain multiple tokens. Neither chunk counts nor native one-second “peak concurrency” buckets establish token acceptance or simultaneous active requests. Historical printed decode has an additional stdout-rounding difference.

All short-suite rows below completed **8/8 with zero reported failures**. Each is one run unless two values are shown. Seven responses per run reached the output cap; output content/lengths differ across configurations. Readable, nonempty responses and HTTP success do not establish complete useful answers, formal quality parity or exact-lossless sampling. No counterbalanced three-repeat comparison was completed. Startup/readiness, preceding probes, prefix warmth, run order and thermals are not fully controlled. In particular, the first corrected DFLASH full run followed a probe of its first prompt.

Runtime image: `lmsysorg/sglang:v0.5.19@sha256:d6e7288627be8b02be88e4bba38e73f6d50e2826869f753c13a4c4385ab3eda9`; GPU power cap remained 250 W. Compact artifact: `/mnt/ssd/storage/ai/qwen3.8-27b/models/compact-target-rholsc8k/artifact`, with `validation.json` and `convert.py` in its parent. It derives from AutoRound base `1f05c441c4e64ae0549de44fa9ea5a6d43610314`, fast variant `124c14e7e8c7d2f5402933b9af368e772a9fcf0c`; draft revision `4d30ec736ffc6b8688dc2ae2b502d9b48bdec279`. All 248,320 embedding rows matched the packed-table reference bit-for-bit after BF16 dequantization; unrelated tensors were preserved. This preserves the old quantized embedding values, **not identity with the current AWQ checkpoint**. See `/tmp/inference-compact-target-preparation.md` and the full per-file validation manifest.


Fork publication chronology: the initial private fork was created at `gildrb/sglang`, branch `downstream/v0.5.19-packed-dflash`, tip `cc168188fa3c6df95b3406b3eee716b175da4808` atop `0bcd822377da7b5718e674eaf9c870d349424dd1`; it is now preserved privately at `https://github.com/gildrb/sglang-private`. The user then authorized publication as the public native fork `https://github.com/gildrb/sglang` of `sgl-project/sglang`, branch `fix/v0.5.19-packed-head-dflash-fc`, exact tip `a02b738c39c5238453335b5379936c60e24bd9c0`. The public branch contains exactly the same two source fixes atop the same base, without private provenance. Public Actions are disabled; no rulesets or classic branch protection existed, and direct push was user-authorized. The original seed checkout `/tmp/sglang-private-seed-w8ugtq3o/sglang` retains private downstream provenance. This records source identity and publication, not a deployment switch.

### Short-workload results

| Candidate | Client concurrency | Decode tok/s, reciprocal mean TPOT | Aggregate output tok/s | Scope |
|---|---:|---:|---:|---|
| Original deployed AWQ baseline | 1 | 34.23 | 34.07 | Different precision/memory configuration |
| Repaired AWQ, lazy K8 | 2 | 35.61 | 67.21 | One run |
| Repaired AWQ, lazy K16 | 4 | 35.12 | 131.63 | One run; 8,413-token pool |
| Exact same AWQ C4 server, client C1 control | 1 | 34.30 | 34.11 | C4 aggregate ratio 3.8586x; inherited warm cache |
| Compact no-spec, extra_buffer K8 | 1 | 43.14 | 42.85 | Different checkpoint from AWQ |
| Compact DFLASH, **broken unloaded FC** | 1 | 35.04 | 34.82 | Invalid draft-conditioning baseline; see below |
| Compact corrected DFLASH, block8 | 1 | **133.13 / 126.62** | **128.61 / 122.24** | Two runs, not three matched repeats |
| Corrected block6 | 1 | 123.82 | 119.95 | No observed improvement |
| Corrected block10 | 1 | 111.49 | 107.74 | No observed improvement |
| Corrected block8, BF16 draft KV | 1 | 128.24 | 123.87 | Inside FP8 fallback run range |
| Corrected block8, cached-KV overlays | 1 | 132.23 | 127.70 | Inside fallback range; no demonstrated gain |
| Corrected speculative block8, lazy K8 | 2 | 106.33 | **186.83** | Higher aggregate, slower individual decode; pool 24,379 |
| Compact no-spec, lazy K16 | 4 | 43.23 | **161.69** | Pool 110,813; separate capacity/latency trade-off |

Original AWQ C1 used static fraction .92, auto/default FP32 Mamba, auto/BF16 KV, extra_buffer K8 and no expandable allocator. Repaired AWQ rows use .89, BF16 Mamba, FP8 KV and expandable segments. Thus original-baseline ratios combine several changes. The exact-server AWQ C1/C4 pair is cleaner but still only one run each. Compact corrected C1 uses extra_buffer K8; speculative C2 uses lazy K8 with normal verification; no-spec C4 uses lazy K16 without draft/verification allocations. These are not concurrency-only comparisons. Speculative C2 and compact no-spec C4 share the compact target but differ in mode, state/scratch allocation, concurrency and capacity. Aggregate throughput exceeding 150 does not meet the single-request 150 target.

Detailed numerical audit, per-request reconstruction and result paths: `/tmp/inference-batching-results-audit.md`. Raw result artifacts:

- AWQ: `/tmp/inference-baseline-c1-aw4hblyr/baseline.json`, `/tmp/inference-c2-results-tkyhqzko/c2.json`, `/tmp/inference-c4-results-fjmwo5uw/c4.json`, `/tmp/inference-matched-c1-caqwawvg/matched-c1.json`.
- Compact baselines: `/tmp/inference-compact-nospec-results-_bm_6lqs/compact-c1.json`, `/tmp/inference-compact-spec-results-v_ifhqh0/compact-dflash-c1.json`.
- Corrected block8: `/tmp/inference-dflash-fc-fixed-results-95sele7y/fc-fixed-c1.json`, `/tmp/inference-fc-repeat-c1-l6i6rpfl/repeat-c1.json`.
- Alternatives: `/tmp/inference-block6-results-76cpkthe/block6-c1.json`, `/tmp/inference-block10-results-6df6my47/block10-c1.json`, `/tmp/inference-draft-bf16-results-ghkd_1c2/draft-bf16-c1.json`, `/tmp/inference-cached-kv-results-z79oute9/cached-kv-c1.json`.
- Concurrency: `/tmp/inference-corrected-c2-results-8__nrjbi/corrected-c2.json` and adjacent `active-decode.log`/`gpu-telemetry.log`; `/tmp/inference-compact-c4-results-7metmpyd/compact-c4.json`. C2 server samples prove two active requests. Untimestamped telemetry includes idle periods; it does not support integrated benchmark energy or tok/J.

### Compatibility false start, negative experiments and bottleneck

The first DFLASH path silently ignored the draft's `fc.weight_packed`, `fc.weight_scale` and `fc.weight_shape`: its plain dense `nn.Linear` had no matching parameters and retained an untrained context projection. This was a loader defect, not evidence that correctly loaded DFLASH intrinsically regresses. The reviewed quant-aware ReplicatedLinear correction also checks full initial-load completeness. Existing compressed-head compatibility remains separate. With flags/checkpoint bytes unchanged, the corrected quantized FC reduced allocation and raised the reported pool from 34,095 to 38,971 tokens.

Exact corrected `dflash.py` SHA256: `56ceed99827f7142580820da1e3951f1f7bdf72256d6072a7b3a3d94915171a3` (original `bfdef4b6ebe54f0ed88e04295310102c88b4b85798604f736cdb46320f3929ef`). Corrected `logits_processor.py`: `b3f6649541db592898754f37c7f395b1f29475f2fb690df91a541c18c77937b3`. Reviews/provenance: `/tmp/inference-dflash-alignment-diagnosis.md`, `/tmp/inference-dflash-fc-compat-11_d9gez/`, `/tmp/inference-sglang-promotion-plan.md`. These corrections are qualified for the default full initial load, not partial/hot reload.

Draft-only Triton with FP8 failed compilation on SM86 (`fp8e4nv not supported`); no throughput result exists: `/tmp/inference-draft-triton-results-s73fjp0k/startup-failure.log`. Compile-only startup failed in the causal-convolution Inductor launcher with missing `_grid_2`; no error suppression or speed claim: `/tmp/inference-compile-results-aojp4spa/startup-failure.log`. Block6/block10, BF16 draft KV and cached KV did not demonstrate a speed gain. Cached-KV numerical fusion qualification remains separate from checkpoint-value proof.

The native cached-KV profile identifies **target verification/Marlin weight-matrix work**, not cached context-KV projection, as the principal measured bottleneck: target graph median 21.017 ms, draft/selector 2.468 ms, cached projection plus norm/RoPE about 0.134 ms per cycle. Target Marlin kernel-duration sum is 17.413 ms/replay; overlapping streams mean this is not an additive wall-time component. Thirty complete cycles have median 26.662 ms; approximately 90.7% of selected wall time contains recorded GPU work. CPU synchronization durations overlap GPU execution and must not be added as independent overhead. No native tile-autotune switch was found. Profile evidence: `/tmp/inference-cached-kv-profile-analysis.md`, `/tmp/inference-target-marlin-tuning-review.md`; trace `/mnt/ssd/storage/ai/qwen3.8-27b/cache/cached-kv-profile-9pivmi15/cached-kv-c1-cached-kv-profile-9pivmi15-TP-0.trace.json.gz`, SHA256 `67769820a0aeb88cd3c3adfc5f0ad8b7e49a7510b894a30f748b67fc0c8ca55a`. One instrumented short trace is not an unprofiled speed benchmark.

### Prefix reuse and quality gates

Corrected speculative C1 synthetic 12,200-input/128-output prefix replay passed 4/4 both times with matching texts. First-request TTFT fell from **12.2666 s cold to 0.3323 s warm**. The initial four-request suite was mixed: later requests already reused 8,192 then 11,968 cached tokens, so it is not four independent cold samples. Warm mean TTFT was 311.45 ms. Artifact pair: `/tmp/inference-fc-prefix-cold-5hit3ez1/prefix-cold.json`, `/tmp/inference-fc-prefix-warm-51ehkbf_/prefix-warm.json`; audit `/tmp/inference-prefix-cold-warm-audit.md`.

C1-primed speculative C2 replay passed 4/4 at 12,200 inputs/128 outputs each, mean TTFT **464.29 ms**, aggregate **185.60 tok/s**, mean TPOT **6.8586 ms**. Logs prove two active requests and four 11,968-cached/232-new prefills; texts match the priming run. This is shared-prefix warm reuse, **not cold independent C2 capacity**: the 24,379-token pool is below two independent 12,200+128 reservations (24,656). Artifacts: `/tmp/inference-c2-prefix-prime-4qq_ab16/prefix-cold.json`, `/tmp/inference-c2-prefix-warm-4pkwf6qm/prefix-warm.json`; audit `/tmp/inference-c2-prefix-audit.md`. Exact synthetic replay is not real agent-turn/tool quality evidence.

The existing 200-question corrected-DFLASH GSM8K gate scored **191/200 (95.5%)**, passing its native 95% threshold; seven of nine failures hit the 768-token cap. Runtime 377.964 s, mean 379.175 output tokens. Artifact: `/tmp/inference-quality-paired-b7ib1hbj/corrected-dflash.json`. **Same-target no-spec quality is pending**, so this is threshold passage, not quality parity. Broad sampling, real Hermes-length behavior and promotion require their own completed evidence. The next performance gate is counterbalanced matched repeats with fixed serving configuration, explicit cache policy and aligned acceptance/energy windows; preserve the known fallback and do not promote from short probes alone.

Compact no-spec C4 prefix audit: both runs passed 4/4 at 12,200 inputs/128 outputs with matching texts. Cold-start mean TTFT was **20.2316 s**, warm exact-replay mean **0.4186 s**; aggregate output was **16.9588 / 142.7372 tok/s**, not a DFLASH comparison. Four HTTP requests overlapped in both runs, but cold logs show **three active decodes plus one queued**, then the fourth alone; warm logs establish **four active decodes**, 12 Mamba states and no queue. Warm cached tokens total 48,456/48,800 (~99.30%), including repeated unique suffixes beyond the nominal 12K shared prefix. This is not pure new-turn reuse, four independently cold decodes or unrelated long-context capacity proof. Artifacts: `/tmp/inference-compact-c4-prefix-cold-jhcm8j3g/prefix-cold.json`, `/tmp/inference-compact-c4-prefix-warm-qz9_a5b3/prefix-warm.json` and adjacent `cache-evidence.log`; audit `/tmp/inference-compact-c4-prefix-audit.md`. One synthetic pair does not establish quality parity or repeatability; no-spec quality remains pending.


### Completed paired quality follow-up (supersedes pending no-spec status above)

Both existing 200-question runs are complete: corrected DFLASH **191/200 (95.5%)** versus compact no-spec **192/200 (96.0%)**, a **+1 item / +0.5 percentage-point** no-spec difference. Pairing failure indices gives **191 both correct, eight both wrong, one no-spec-only correct (index 87), zero spec-only correct**. Shared failures are indices 12, 45, 62, 85, 93, 119, 182 and 184; their expected answers agree. DFLASH failures hit the 768-token cap in **7/9** cases, no-spec in **5/8**. The sole discordant DFLASH failure is capped; cap association is not proof of cause. Summary files omit successful-item token counts/output text, so no complete per-item token or text-equivalence claim follows.

No-spec elapsed **1,812.463 s**, mean **377.515 output tokens**, versus DFLASH **377.964 s**, mean **379.175**. Both use the same existing fixture and scorer, one worker, temperature 0, thinking disabled and max 768 outputs. Fixture SHA256: `c33dcc6090f023fef25fe87711f6bd09d4de81658edb14468162cc9a9e5679fe`. Results: `/tmp/inference-quality-paired-b7ib1hbj/compact-nospec.json`, `corrected-dflash.json` and adjacent logs/protocol; paired failure details: `/tmp/inference-batching-results-audit.md`. The protocol's old prepared-status field is stale; completed results and execution-agent exit-zero reports establish completion. No-spec server **lazy K16** versus speculative C1 **extra_buffer K8** prevents pure speculation-only numeric isolation. Passing 95%, or differing by one item, establishes neither broad intelligence/distribution parity nor exact-lossless sampling. These are one-run capped-fixture outcomes; real-agent, tool, cache and sampling gates remain separate.


### Marlin K64 negative trial

The full eight-prompt C1 Marlin-K64 candidate completed **8/8, zero failures**, but reached only **123.074610 decode tok/s** (reciprocal mean TPOT **8.125153 ms**) and **118.895956 aggregate output tok/s** over **65.511059 s**. Output total was 7,789 tokens: seven 1,024-token caps and request 7 at 621. Artifact: `/tmp/inference-marlin-k64-results-hrzaaplu/marlin-k64-c1.json`; detailed reconstruction: `/tmp/inference-batching-results-audit.md`. Both throughput measures are below both stock corrected block8 runs (decode 126.62–133.13; aggregate 122.24–128.61). **No demonstrated gain; do not promote.** This is one trial with differing outputs and cache/order/thermal limitations, not a general proof about every K64 configuration or quality parity. The operator is restoring the stock fallback; this result alone does not verify restoration.


### 280 W policy decision and stock A/B/B2 observations

The user selected **280 W permanently**, superseding the earlier 250 W policy. The execution agent reports the active cap is 280 W, the cap-management timer is stopped, and `~/nix/modules/nixos/nvidia-quiet.nix` now declares 280 W with parse/diff checks passed. **The declarative source change is not deployed; switch is pending.** The planned return-to-250 W A2 was cancelled by this decision. This is a power-policy choice, not proof of a causal performance gain or model/runtime promotion.

| Stock corrected block8 C1 run | Power cap | Decode tok/s: reciprocal mean TPOT | Aggregate output tok/s | Wall seconds |
|---|---:|---:|---:|---:|
| A | 250 W | 127.655098 | 123.002320 | 63.641076 |
| B | 280 W | 139.049299 | 133.934011 | 58.446693 |
| B2 | 280 W | 138.101983 | 133.006773 | 58.854146 |

All three runs completed **8/8, zero failures**, with **all eight generated texts and per-request token lengths identical**: 1,130 input tokens and 7,828 outputs (seven 1,024-token caps; request 7 at 660). Aggregate rates and reconstructed request timing agree with the native summaries. Artifacts: `/tmp/inference-power-ab-kvy3_n17/{stock-250w-a.json,stock-280w-b.json,stock-280w-b2.json}` and adjacent logs; numerical audit `/tmp/inference-batching-results-audit.md`. The repeated 280 W observation is **138.10–139.05 single-request decode tok/s**, still below the **150 target**. Identical outputs strengthen this narrow comparison but do not establish broad quality or distribution parity.

There is one sequential 250 W run and two 280 W runs, **no return A2 or counterbalanced power control**. Do not present the roughly 8–9% observed increase as an isolated causal power-only effect: cache history, run order, thermals and preceding idle/work remain limits. The user policy decision does not remove those experimental limits.

`stock-280w-telemetry.csv` is final after SIGTERM, with **54 complete samples and a discarded partial tail**; buffering means full timed coverage is unproven. Complete timestamps span local `2026/09/12 14:15:44.444`–`14:16:37.492`. Host timezone was independently verified as CEST/UTC+2, consistent with client UTC; monotonic-request boundary alignment remains unestablished. All complete samples report a 280 W limit. The 41 samples with GPU utilization at least 90% show utilization **94–96%**, graphics clocks **1,485–1,605 MHz**, memory **9,501 MHz**, temperature **46–59°C**, and power **203.06–280.10 W**, including activity startup. These are bounded sample ranges, not full-run steady-state statistics, B2 telemetry, integrated energy, tok/J or proof of thermal throttling. No sustained-150 or production-promotion claim follows.


### Finalization decision and narrow Mamba checkpoint qualification

The user ended the **150/200 tok/s pursuit** and selected finalization around the observed **138–139 single-request decode tok/s at 280 W**, with memory safety and reproducibility taking priority. This supersedes the earlier 150-target pursuit; it is not an “always 140” guarantee. The exact final profile is being qualified with **context 24,576**, **input-logprob chunk 256**, stock kernels and three source corrections (packed head, quantized draft FC, Mamba checkpoint tracking). **Its benchmark is still running; the prior 280 W results are not measurements of that exact final profile.** Third-fix public commit/push and requested final deployment remain pending at this entry; neither is asserted complete.

The isolated Mamba correction replaces stale tracking lengths with a local out-of-place prefill-plus-commit post-length; it preserves live commit/scatter and publication ordering. Independent source review, seven reported CPU checks and a matched native generated-prefix/cold-reference diagnostic support **`extra_buffer` only**. In two frozen prompts, mean approximate KL fell from stock **0.02167921664366393** to fixed **0.000035783726386075915**, below the **predeclared 0.001 diagnostic cutoff**. Fixed per-sample values were 0.000007992375402146286 and 0.00006357507737000554. Both variants hit the same **256-aligned generated-prefix boundaries**: 4,352 and 4,096 cached tokens, extending 319 and 323 tokens beyond the initial inputs. This checks generated checkpoint reuse, not merely prefill cache hits.

The first stock diagnostic attempt with default input-logprob chunk **2,048** OOMed before producing KL and is **excluded**. Both completed stock/fixed diagnostics used chunk **256**, with no OOM/error matches in their complete server logs; stock failed the KL assertion, fixed passed. This is bounded evidence for those runs, not a universal no-OOM or memory-safety guarantee. Input-logprob chunking is distinct from transformer prefill chunking. The comparison is not proof of broad spec/no-spec or sampling-distribution parity: each variant compares its own generated trajectory with cold recomputation. `extra_buffer_lazy`, concurrency, cancellation/reclamation, all boundary offsets and the separate FlashInfer window issue remain outside this qualification.

Evidence: `/tmp/inference-dflash-mamba-checkpoint-qualification.md`; private protocol/client/server artifacts in `/tmp/inference-checkpoint-validation-vq8o7o22/` (`stock-chunk256.log`, `fixed-chunk256.log` and corresponding `*-server.log`). Frozen fixture SHA256: `df118399f26d3550f1d23e937734d980831661df1584099617a53de1ba5ffc13`; candidate worker SHA256: `bc0bd9318a91bd28c396a2e6832d1451a15934c18fb32d5c6db2ebd24995df83`. Source base remains public commit `a02b738c39c5238453335b5379936c60e24bd9c0`; no third-fix commit identity is assumed before publication. Keep private fixture/output artifacts out of the source publication. Existing benchmark, quality, cache-order and deployment caveats above remain in force.


### Final-profile short-suite qualification completed

The exact final candidate—**context 24,576, input-logprob chunk 256, stock kernels plus packed-head/quantized-FC/Mamba-checkpoint fixes, 280 W**—completed two eight-prompt C1 runs, both **8/8 with zero failures**:

| Run | Decode tok/s: reciprocal mean TPOT | Aggregate output tok/s | Mean TPOT ms | Wall seconds |
|---|---:|---:|---:|---:|
| Final A | 141.704096 | 136.752579 | 7.056959 | 57.256690 |
| Final B | 142.852777 | 137.759743 | 7.000214 | 56.838085 |

Artifacts: `/tmp/inference-final-qualification-o9vcvml2/final-c1-a.json` and `final-c1-b.json`; reconstruction/output audit `/tmp/inference-batching-results-audit.md`. Each has 1,130 input and 7,830 output tokens (seven 1,024-token caps, request 7 at 662). Seven texts match byte-for-byte across final A/B; request 1 differs. **All eight outputs in each final run differ from prior 280 W B2**, whose total was 7,828 tokens. Thus the profile transition is not an exact-output controlled speed comparison, and no causal gain from the third fix is claimed. The two runs qualify **consistent near-140 single-request decode on this short suite**, not always-140 throughput, broad quality/distribution parity, or renewed pursuit of 150/200. Existing single-suite, cap, cache/order/thermal and memory-safety limits remain.

Public fork `https://github.com/gildrb/sglang` now has the third source correction pushed at **`3958762c198b7e9e0167e6aedda1b8c3f9a8afb1`**, default branch `fix/v0.5.19-packed-head-dflash-fc`, Actions disabled, according to execution evidence. This supersedes the pending third-fix publication above. **The 24K input-logprob memory request is still running; no pass or universal no-OOM claim is made.** Source publication and short-suite completion do not alone establish final deployment.


### Final quality and bounded 24K memory gates completed

The final profile's existing GSM8K gate scored **193/200 (96.5%)**, in **331.871401 s**, mean **379.6 output tokens**, one worker. Seven failures remain; **four hit the 768-token cap**. Artifact: `/tmp/inference-final-qualification-o9vcvml2/final-quality.json` and adjacent log. Against the earlier same-fixture results, this is +2 items versus 191/200 speculative and +1 versus 192/200 no-spec. Paired failures show final-only correct indices 12 and 87 versus prior speculative, and 12 versus no-spec, with no reverse discordances. **Do not attribute these small score differences causally to the patch**: configuration, trajectories, cache/order and power history differ; one capped greedy numeric fixture is not broad intelligence, quality-equivalence or distribution-parity proof. Successful-item detailed outputs/tokens are not retained in these summaries.

Two authenticated cold **24,000-input-token full-input-logprob** requests each returned **HTTP 200**, all **24,000 logprob rows** and **128 output tokens**, with `cached_tokens=0`. Responses: `/tmp/inference-final-qualification-o9vcvml2/long-logprob-authenticated-response.json` and `long-logprob-warm-response.json`; the second filename does **not** make it warm—its metadata says zero cached. A separate no-input-logprob 24K request returned HTTP 200, **20,480 cached tokens** and 128 outputs (`long-cache-response.json`). A **24,576-token input** was rejected with HTTP 400 at context 24,576 (`over-context-response.json`), preserving output headroom rather than admitting an over-budget input. The initial incorrect-authentication HTTP 401 attempt is excluded. Response metadata was independently audited; HTTP statuses are execution-agent evidence. These probes support bounded final-profile memory/admission behavior, **not universal no-OOM, arbitrary long concurrency or all-input safety**.

The execution agent reports the user-authorized power-check expectation changed from 250 to 280 W and native `verify-workstation-behavior` **passed**. Source integration commit **`0662029`** is created; push sequencing is next and **deployment remains pending** at this entry. These completion states supersede the prior pending quality/24K probe statements, not the outstanding deployment or historical benchmark limits.


### Near-boundary admission and source publication follow-up

The execution agent reports a near-boundary request with **24,569 input tokens and six requested output tokens** returned **HTTP 200**, **five output tokens**, and **finish reason length 5**. This is evidence of bounded/clamped output admission for that request, alongside the separately observed 24,576-input rejection; **do not generalize that all over-budget requests return HTTP 400**. It is not a universal boundary or no-OOM guarantee.

Source integration commit **`0662029` is now pushed to `origin/main`**. The consumer's local inference-lock update has started; deployment is still pending. This supersedes the previous push-next status. `TRIALS.md` is frozen for the root agent's commit until deployment evidence arrives.
