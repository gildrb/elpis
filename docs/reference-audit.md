# Upstream reference audit

Audit date: 2026-09-13. This is a source and public-artifact audit, not a GPU qualification. No runtime pin, model artifact, or service setting was changed by this audit. Read the repository README, architecture and qualification contracts before applying any finding.

## Decision

Keep SGLang **v0.5.19 at `0bcd822377da7b5718e674eaf9c870d349424dd1` as the evidence-backed integration base**, with the reviewed local patches. It is still the latest public release, not an obsolete release selected in place of a newer stable version. The latest fetched main is a separate migration candidate. Neither version alone qualifies the packed W4A16 target plus W4A16 DFlash2 plus KVarN at **262,144 total tokens** on an RTX 3090. The 245,760-token DFlash2 configuration discussed by syv is a historical reference operating point, not this repository’s final objective.

New main has an upstream fix for the same committed-Mamba-boundary invariant already covered by the local prefix patch. It does not eliminate the inspected sampling-transform problems or supply native KVarN. An upgrade therefore requires explicit patch migration and a new qualification, not merely a new version string.

## Exact source identities

| Source | Fetched identity | Authority and limit |
|---|---|---|
| [SGLang main](https://github.com/sgl-project/sglang/tree/7078e5ffbc71f9f31d07018aff2f32530dac781a) | `7078e5ffbc71f9f31d07018aff2f32530dac781a`, committed 2026-09-13 10:29:14 UTC | Full Git checkout with history; snapshot of moving main, not a qualified local runtime |
| [SGLang v0.5.19](https://github.com/sgl-project/sglang/tree/0bcd822377da7b5718e674eaf9c870d349424dd1) | `0bcd822377da7b5718e674eaf9c870d349424dd1`, committed 2026-09-03 | Annotated tag dereferenced with Git; GitHub latest-release API independently reports v0.5.19, published 2026-09-05 |
| [syv reference](https://github.com/syv-ai/qwen38-27b-rtx3090/tree/18349177b7962ef1d699dc154844f9c04317a474) | `18349177b7962ef1d699dc154844f9c04317a474`, committed 2026-09-11 | Full Git checkout with history; **vLLM 0.28.0**, not SGLang |
| [Roycorp/LLM-inference](https://github.com/Roycorp/LLM-inference) | **Unavailable; no commit fetched** | Public Git clone, GitHub REST repository query and authenticated `gh api` all returned not found. This can mean missing, renamed or inaccessible; it does not prove deletion. No substitute repository was silently used. |
| [KVarN origin](https://github.com/huawei-csl/KVarN) | Advertised HEAD `7586257f1c632e63187bfacbbe21ccb51540f7b3` | `git ls-remote` only. Not a fetched source audit or proven ancestor of the syv copy. The audited implementation is the syv commit above. |

Historical local measurements in `bench/results/native.json` identify the stock image as `lmsysorg/sglang@sha256:d6e7288627be8b02be88e4bba38e73f6d50e2826869f753c13a4c4385ab3eda9`. That is historical measurement provenance, not the new build’s source contract. The current integration binds an upstream source commit plus the ordered patch SHA list. A Git tag alone does not authenticate either the applied patch sequence or container bytes.

Git history searches for `Roycorp` and `LLM-inference` in this repository, including content-change searches, found no reference. The syv current tree and commit-subject search also yielded none. This is a bounded history search, not proof that the unavailable repository never existed. Its methods and performance remain unaudited.

## SGLang support and release-to-main delta

The main checkpoint remains explicit about [`DFlash2DraftModel`](https://github.com/sgl-project/sglang/blob/7078e5ffbc71f9f31d07018aff2f32530dac781a/python/sglang/srt/models/dflash.py). It uses the `DFLASH` worker; the CLI name is not `DFLASH2`. The official DFlash2 model card also gives `--speculative-algorithm DFLASH` and `--speculative-num-draft-tokens 8`.

| Finding | Exact evidence | Consequence |
|---|---|---|
| DFlash2 and quantized-head support predate current main | `c14312a66420b75ca9a11bf1817c4db1fa26b097` (#35371); `1cf2b8c54d81802abc15dcf23a29b9cc687bc01e` (#35496) in model history | Feature-name support does not establish this packed artifact's loader compatibility. |
| Packed-only head still needs admission | Main `layers/logits_processor.py`, both definitions of `should_apply_lm_head_quant_method`, require `lm_head.weight`. Main DFlash2 accepts a dense weight **or supported quantization method**; it does not reject every quantized head. | A compressed WNA16 head with packed attributes but no dense `weight` still needs the local predicate contract. Audit the effective last function definition, not only the first occurrence. |
| W4 draft projection is not generally fixed upstream | Main `models/dflash.py` uses `ReplicatedLinear` for the Nemotron branch, but the ordinary DFlash branch still uses `nn.Linear` for `fc`. | The repository's quant-aware `fc` loading and required-weight checks remain relevant. Do not remove them because another model branch uses a quant-aware layer. |
| New upstream Mamba checkpoint fix | [`b805cc501444a6b98e26e3088851ba5e980704d7`](https://github.com/sgl-project/sglang/commit/b805cc501444a6b98e26e3088851ba5e980704d7), #37818 | Main supplies committed post-verify lengths instead of stale `batch.seq_lens`. Local `patches/mamba-cache-prefix.patch` computes `pre + commit` for the same invariant. This supports the local rationale; it is not proof of every recurrent/convolution-state rejection case. |
| Sampling transforms remain unchanged in the inspected helpers | AST comparison of release versus main: `build_dflash_verify_target_probs` and `apply_dflash_verify_logits_adjustments` are identical, excluding locations. | No evidence that moving to main fixes combined top-k/top-p, `min_p`, or evolving penalty-state issues in these helpers. This is static evidence, not a new GPU parity run. |

### Condition for removing the local Mamba prefix patch

On the selected v0.5.19 base, keep the local patch because the upstream fix is absent. On a future base containing `b805cc501444a6b98e26e3088851ba5e980704d7` or a verified equivalent, remove only the redundant patch after reviewing every call site: the supplied post-verify length must equal the committed prefix length, and checkpoint selection must never include rejected or future state. Rebind the selected upstream source commit and ordered patch SHA list; do not retain a redundant patch entry. Repeat rejection-depth, generated-prefix, boundary and native/graph cache qualification on that exact build. Merely finding the commit in history, or passing a patch application, is not the deletion condition.

Other relevant main changes include graph-pool borrowing and sizing (`9a05b470fa849b349e384ef3c1381f9a85c6c550`, #36911), sampler-mask capture/replay (`046cdaabaae3524a7cb9806f736cf52e09c49c7a`, #36630; `fd7743e0e1725f9f24844e6f3446fcf0f9ade815`, #36631), and Domino/NPU model support. These are real changes, not demonstrated gains for this configuration. The scoped release-to-main diff over the cache directory plus DFlash model/worker, logits processor and speculative argument hook has **95 files changed, 12,424 insertions and 4,290 deletions**. It is not a minimal backport surface.

### Ampere and weight quantization

The [current quantization guide](https://github.com/sgl-project/sglang/blob/7078e5ffbc71f9f31d07018aff2f32530dac781a/docs/docs/advanced_features/quantization.mdx) lists AWQ/GPTQ Marlin and compressed-tensors. Source `awq/awq.py` gives `AWQMarlinConfig.get_min_capability()` as 80. `compressed_tensors/schemes/compressed_tensors_wNa16.py` gives 80 and checks quantization and shape constraints. RTX 3090 is Ampere SM86, so it clears that hardware floor. This does not waive group-size, partition-shape, tensor-format or model-loader checks.

Do not conflate **NVFP4 weight loading through Marlin W4A16 fallback on SM80–SM90** with **NVFP4 KV-cache support**. These are different paths. Nor does the availability of FP8 storage mean Ampere has native FP8 tensor-core arithmetic. The official DFlash2 model-card benchmark uses H200 with FA3, not a 3090. Its attention choice and memory assumptions cannot be copied unchanged.

## Current upstream compressed KV versus KVarN

The [quantized-KV guide](https://github.com/sgl-project/sglang/blob/7078e5ffbc71f9f31d07018aff2f32530dac781a/docs/docs/advanced_features/quantized_kv_cache.mdx) marks FP4 experimental and warns that unfused dequantization can be extremely slow. The implementation supports more than FP8; saying “SGLang has no compressed KV” would be false.

| Path | Current source contract | RTX 3090 decision |
|---|---|---|
| `fp8_e4m3` / `fp8_e5m2` | Quantized storage with backend-dependent reads and scaling | Existing measured baseline is relevant only for its exact backend and scaling. Not a 262,144-token fit proof. |
| `nvfp4` | `arg_groups/kv_cache_hook.py:handle_kv4_compatibility` requires **SM100 or SM120**; helper has an SM90 quantization fallback, but launch gate is stricter | Not a supported SM86 launch option. Do not bypass the gate. |
| `mxfp8` | Same hook requires Blackwell for FA4 block-scaled operands | Not a supported SM86 launch option. |
| `fp4_mx_block16` | E2M1 4-bit K and V with one exponent scale per 16 elements; portable Torch-compiled quantizer; MHA allows Triton/torch-native/flex-attention/TRT-LLM paths | Not ruled out by an Ampere SM gate. It is an **experimental alternative to measure**, not a native fused low-bit 3090 replacement for KVarN. |
| KVarN `k4v2_g128` | No `kvarn`, `KIVI` or `turboquant` match in the scoped SGLang runtime/docs search. Syv ports KVarN's Hadamard rotation, iterative variance normalization, 4-bit K / 2-bit V per 128-token tile to vLLM. | Remains a local SGLang integration, with its own numerical, allocation and graph qualification burden. |

The critical difference is the read path. Main `fp4_kv_cache_quant_method.py` registers block16 MHA access as **plain BF16**, not native FP4 attention. `memory_pool.py:2470–2504` passes the complete layer K or V buffer and scales to `dequantize_kv_tensor`; its implementation invokes `FP4MXBlock16KVQuantizeUtil.batched_dequantize`. The generic Triton backend therefore consumes materialized BF16 buffers. This creates allocation/bandwidth costs which the compact storage ratio alone does not express. It is not equivalent to fused attention directly reading packed KVarN tiles.

For the target's 4 KV heads × 256 dimensions, both K and V at block16 FP4 require **1,152 stored bytes/token/layer**, before other buffers: 1,024 packed payload bytes plus 128 scale bytes. The syv KVarN port documents 840 bytes/token/layer without power-of-two slot padding, versus 2,048 for FP8. These are representation calculations/reference layout descriptions, **not observed local pool capacities**. Draft KV, all recurrent states, embeddings/head, scratch, graph pools, vision preprocessing and allocator slack also consume memory.

The same NVFP4 gate and block16 alternative already exist in v0.5.19; main is not needed just to discover these recipe names. DeepSeek-V4 “compressed KV” pools are a model-specific architecture, not a generic compression switch for Qwen3.8. SGLang diffusion's int4/int2 cache option is likewise not the autoregressive Qwen serving path.

## Public DFlash2 artifact revisions

Only metadata, cards and configs were fetched. No weights were downloaded or replaced. Revisions below came from Hugging Face model APIs; cards/configs for incoai and syvai were resolved at the exact listed commits.

| Public checkpoint | Observed revision | Scope |
|---|---|---|
| [incoai/Qwen3.8-27B-DFlash2](https://huggingface.co/incoai/Qwen3.8-27B-DFlash2/tree/dedf8df68adfb1afeaf7b7480c0a0243108177b4) | `dedf8df68adfb1afeaf7b7480c0a0243108177b4` | Original BF16 draft; card names SGLang and vLLM. |
| [z-lab/Qwen3.8-27B-DFlash2](https://huggingface.co/z-lab/Qwen3.8-27B-DFlash2/tree/50307d4c4cde6860d4eee73e2547cd786fe8e8a4) | `50307d4c4cde6860d4eee73e2547cd786fe8e8a4` | Card-declared mirror, separately versioned. Metadata checked; no weight-byte equivalence claim. |
| [syvai/Qwen3.8-27B-DFlash2-W4A16](https://huggingface.co/syvai/Qwen3.8-27B-DFlash2-W4A16/tree/4d30ec736ffc6b8688dc2ae2b502d9b48bdec279) | `4d30ec736ffc6b8688dc2ae2b502d9b48bdec279` | GPTQ symmetric group128 compressed-tensors W4A16. Same ancestry revision recorded locally; local inventory still controls actual bytes. |

Both inspected configs declare five layers, hidden size 5120, vocabulary 248320, `DFlash2DraftModel`, block 8, window 2048, maximum positions 262144, selector rank256/top-k16 and target layers `[5,19,33,47,61]`. The W4 config leaves kernel projections, candidate selector and hidden projection unquantized; `fc` is quantized. The card says the draft shares the target embeddings and head and is not a standalone model.

The reference's `prepare/fetch_dflash2.py` downloads floating HEAD without a revision argument. It is a convenience mechanism, **not a reproducible acquisition pin**. Do not copy it into the offline authenticated preparation flow. Maximum positions in a config do not establish that target+draft+KV fit at that context.

## Reference history and experiments worth adapting

The following are **reference observations and methods only**. Their throughput, quality and capacity do not become results of this SGLang repository.

| Syv history | Why it matters |
|---|---|
| `e0f5432f5058647e83da67c3d5420e88931f1f78` | Original vLLM0.27.1 KVarN port; its 262K evidence is explicitly non-speculative batch mode, not the historical DFlash2 245,760-token operating point or this repository’s 262,144-token objective. |
| `e4546d0f1e244fc78888490758f4cf8e3926cd16` | DFlash2 backport of vLLM#52816, W4 drafter and measurement wiring. |
| `a75ee4be40098e9d0b239cf4550ee12c4ac49338` and `b356e31526886b4bd614a79cd8600e7cc9383cf9` | Correct prefill/decode dispatch, then a complete 128-residue warm-cache sweep. Earlier graph-speed explanations were revised after fixing the correctness defect. |
| `cd2fa9435b3be1168da93d997b14fabd752c2133` | vLLM0.28.0 migration. Current README explicitly retains historical tables while the new GPU matrix is remeasured. |
| `8d0cef8ba929642d6524ccfc03919f227f821eaf` | Backport of vLLM#54282 separating draft Gumbel noise from target noise. A sampling-independence review lead, not proof that SGLang has the same bug or that applying a vLLM patch repairs it. |

### Syv precision, power and graph methodology

These details come from the same pinned syv tree: [preparation](https://github.com/syv-ai/qwen38-27b-rtx3090/blob/18349177b7962ef1d699dc154844f9c04317a474/prepare/README.md), [drafter calibration](https://github.com/syv-ai/qwen38-27b-rtx3090/blob/18349177b7962ef1d699dc154844f9c04317a474/drafter/README.md), [optimization experiments](https://github.com/syv-ai/qwen38-27b-rtx3090/blob/18349177b7962ef1d699dc154844f9c04317a474/docs/optimizations.md) and `single-user/start_qwen.sh`. They describe external vLLM experiments, not settings or gains adopted here.

| Axis | Reference configuration and controlled comparison | Local implication |
|---|---|---|
| Weights and embeddings | AutoRound W4A16 body. Base preparation changes untied `lm_head` and `embed_tokens` to INT8 group128 and MTP to INT8. The single-user fast variant instead uses GPTQ INT4 head/MTP; it is not the same artifact as the base requantization. DFlash2 is separately GPTQ W4A16, including `fc`, with small selector/convolution components BF16. | Name the exact target/head/embedding/draft artifacts in each comparison. The reference's quantized embedding lookup is not our historical dense-BF16 embedding path. |
| Activation and prefill precision | Single-user default remains W4A16. `INT8_ACT=int8` selects W4A8 Marlin for chosen linears; batch mode defaults to MLP INT8 activations. The negative-scale Marlin repair is essential for its AutoRound export. Reference seeded prefill compares MLP-only versus all supported linears at 1K/4K/16K/51K. INT8-QK prefill is a separate option: smoothed K, per-row Q scaling, BF16 P×V. | Do not change activation precision under the name of a kernel speedup. Separate prefill gain, decode gain, numerical error and reasoning loss. Its reported INT8 quality cost is not quality-neutral evidence. |
| Recurrent and compute precision | The launcher explicitly sets `--mamba-ssm-cache-dtype float16`; the reference contrasts FP32 state with FP16 state across 48 GDN layers and observes improved residency. Its speculative path rejects whole-model `--dtype float16` because the relevant Triton path expects BF16. | FP16 recurrent storage and BF16 model computation coexist; “all FP16” would misdescribe the recipe. This differs from the historical local BF16 Mamba baseline and needs independent recurrent/convolution-state checks. |
| Power and sustained load | Reference 3090 measurements use a **250 W power cap**. The tile-tuning campaign reports isolated burst improvements that shrink to roughly 0.4% end-to-end under sustained capped load. The historical local cap is 280 W. | A power cap is not measured draw or energy. Compare at one declared cap, record actual clocks/temperature/power when available, and retain a no-improvement verdict when repeated timings overlap. Do not attribute a cross-host gain solely to code. |
| Graphs and memory accounting | Reference V2 graph-memory accounting is explicit, with pinned KV bytes and graph-memory allowances. DFlash2+KVarN FULL capture was restored after a prefill/decode residue fix and a 128-residue sweep. MTP+KVarN still forces PIECEWISE for correctness. The revised same-server long-context comparison finds little capture-mode benefit; earlier larger claims mixed in the bug or changed step counts. | Measure eager/native versus captured execution using matching output/step counts and real cache hits. Charge graph pools and transient allocations before setting context. Do not import vLLM graph settings or its memory constants into SGLang. |

The reference also reports negative calibration results worth preserving: blending context-KV Hessians reduced DFlash2 greedy acceptance, and keeping `fc` BF16 did not improve acceptance in its trial. Neither simpler weight-error metrics nor a one-run timing improvement selected the final draft. Its old unseeded prefill harness reused prefixes and was replaced with distinct seeds; source pinning alone does not make those old numbers comparable.

### Qualification design, not additional completed runs

1. **Timing controls:** retain exact token IDs/template, reasoning mode, output budget, sampling and cache salt. Use interleaved repetitions and separate TTFT, client end-to-end output rate, decode rate and accepted tokens per verification step. Hold power cap and exclusive access fixed. A changed output or step count can explain an apparent kernel speedup.
2. **Boundary/cache controls:** adapt the principle of `bench/residue_sweep.py`, not its vLLM implementation. Exercise every relevant page/chunk/checkpoint residue, cold requests and real second-turn hits. Judge source reproduction against the requested task rather than one failure symptom. Include generated prefixes, divergent continuations, rejection depths, cancellation and retry. A warm self-hit is narrower than multi-turn correctness.
3. **KV alternatives:** compare FP8, local KVarN and upstream block16 with exact immutable image identities. Use the same experimental image for KVarN on/off so active sampler repairs do not confound the KV comparison. Predeclare arithmetic, memory, long-context and reasoning thresholds. Measure whole-model high-water, dequant/scratch overhead and draft/verify time. Qualify native before graphs, then repeat the same boundary checks under capture. These runs require endpoint/GPU approval; none ran during this audit.
4. **Workload separation:** syv's `labd_bench.py` separates reproduction, code, edits, quotations, summary and QA. Its `conc_ladder.py` separates salted independent prompts from shared prefixes and records queueing, preemptions and resident occupancy. Use those distinctions; do not equate advertised concurrency with resident capacity or long-prefill time with decode regression. Current local promotion remains C1.
5. **Independent quality:** a needle pass, self-consistency KL, short GSM8K sample or lossless-speculation algorithm description is not broad quality parity with BF16/FP8 target execution. Quantized KV changes target logits. Use the pinned upstream environments already under `eval/`, with actual scores and uncertainty reported separately from runtime timing.

Reference code is not automatically suitable for this repository's strict contracts. For example, the inspected syv concurrency script maps missing metrics to zero and suppresses sampler exceptions. Local evidence must instead distinguish missing telemetry and failed requests explicitly. Copy methodology selectively; retain local validation and artifact-ownership rules.

## Open evidence gaps

Roycorp source remains inaccessible. No local GPU execution, model-quality evaluation, direct 262,144-token capacity run, sampled-distribution proof, energy measurement or new lifecycle qualification was performed here. The public DFlash2 H200 measurements and syv RTX3090/vLLM measurements are external evidence only. Main-source support and a successful import/build are not deployment authorization.
