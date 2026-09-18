# Patch provenance and evidence limits

## Source and order

`source.env` pins the official SGLang repository at the exact stock-image commit
`0bcd822377da7b5718e674eaf9c870d349424dd1`, also resolved by `v0.5.19`.
The annotated tag object is `59f20bffdde59a35cc628372d85d20a979f6271b`;
it is not the source commit. Builds select the commit directly. The historical baseline
fork revision `3958762c198b7e9e0167e6aedda1b8c3f9a8afb1` already includes the
three baseline patches; do not use it as the patch input.

`baseline.series` lists three ordered SHA256-bound Git unified patches.
`experimental.series` lists fourteen more, applied after the baseline. All patch
paths are relative to the upstream repository root. `apply.sh` requires an exact,
clean upstream Git checkout and uses `git apply --check --index` followed by
`git apply --index` for each patch. Git records the changes in the build index;
a second invocation fails because the checkout is no longer clean. A failed
attempt may leave a partial build tree: discard that exclusively owned build
attempt, never continue on a live or shared checkout. Ignored stock build outputs
are not removed or replaced. The image remains digest-pinned by its Dockerfile.
There is no original-file archive, custom diff parser, source overlay, runtime
source verifier or source reconstruction dependency.

## Classification

| Build set | Ordered patches | Evidence scope |
|---|---|---|
| Baseline | packed-head-predicate, quant-aware-fc, mamba-cache-prefix | Historical measured 64K runtime; packaging changes do not qualify a new deployment |
| Experimental extension | qwen3_5, packed_w8_embedding, mm_utils, kvarn-candidate, sampler-checkpoint2, kvarn-pack-layout, quant-loader-guard, kvarn-native-rungs, packed-embedding-lora-defaults, kvarn-hybrid-attrs, kvarn-reserved-accounting, kvarn-prefill-tile | Source-preserved candidate, not full-model qualified |

KVarN remains experimental. The first 240K full-model attempt failed before
startup with a CUDA illegal memory access; it produced no candidate throughput,
TTFT or quality result. The split-packing repair passed 90 attention cases and
two status cases with zero compute-sanitizer errors. This is small-fixture kernel
evidence, not model capacity, numerical parity to FP8, cache lifecycle, quality
or CUDA-graph qualification. See `../bench/results/240k-native-attempt-01.json`,
`../bench/results/240k-packing-memcheck-01.json` and
`../bench/results/240k-packing-repair-01.json`.

The sampler checkpoint has CPU interpreter evidence, not CUDA compiler/native
GPU parity. The last quant-loader guard preserves the loader's validated HF
config identity and packed-module mappings before comparing checkpoint metadata;
its presence is not evidence of successful full-model startup. No experimental
patch is automatically selected by baseline serving.

## Migration proof

The old current working-tree ten-stage chain was reconstructed before removal,
including the uncommitted quant-loader guard and its updated qualification
manifest. All 21 original files matched the official commit and all 17 additions
were absent. Applying the standard Git series produced exactly the same 38 final
files. The independent three-patch baseline also matched all three prior final
hashes. `migration-evidence.json` records aggregate identities; it is evidence,
not a runtime input or source inventory. Apache-2.0 notices remain in patch
context and `LICENSE.sglang`.

## Loader restrictions

The head and FC changes support one full initial `DefaultModelLoader` load only.
Do not use hot reload or partial weight loading. The head helper assumes
successful Marlin processing; metadata alone does not prove numerical layout.
The FC check requires checkpoint parameters before derived Marlin buffers exist.
The Mamba correction tracks committed post-verify sequence lengths. Never alias
packed weights to dense `.weight` or accept arbitrary quantization methods.

The following measurements describe their recorded source and deployment, not
this new packaging or any 262144-token qualification target.

## Historical evidence, not launch configuration

The three default patches have scoped evidence in
[the native report](../bench/results/native.json): two 8-request C1 runs,
65K cold generation and a generated-prefix emitted-token consistency check.
Their original producer hashes, metric definitions and capacity limits stay
in that report. They do not qualify the new 262144-token recipe, arbitrary
sampling, cancellation/reclamation or C2/C4. The older 280 W cap is not a
new power-efficiency recommendation. See [current gates](../docs/qualification.md).

## Semantic review inventory

Every row uses the exact `source.env` base plus all earlier ordered patches.
Baseline/experimental above describe build selection, not semantic class.
Except for the equivalent Mamba correction below, upstream PR status is **not
recorded**. Source equivalence is validated for all rows but is not GPU proof.

| Order / patch | Semantic class | Subsystem / purpose and benefit | Main risk | Existing validation |
|---|---|---|---|---|
| 1 packed-head-predicate | compatibility | Logits: recognize processed compressed head for DFlash | Incorrect packed-layout admission | Historical baseline native runtime |
| 2 quant-aware-fc | compatibility | Draft model: load quantized FC through ReplicatedLinear | Partial/hot loading unsupported | Historical baseline native runtime |
| 3 mamba-cache-prefix | correctness | DFlash cache: checkpoint committed sequence boundary | Other cache lifecycle paths remain unqualified | Generated-prefix cache probe only |
| 4 qwen3_5 | memory | Model loader: admit packed embeddings | Loader metadata/layout mismatch | Packed arithmetic; full model unqualified |
| 5 packed_w8_embedding | memory | Embedding layer: retain packed weights | Quantized numerical or kernel mismatch | All-row packed arithmetic, not model quality |
| 6 mm_utils | compatibility | Multimodal handling: support packed embedding access | Multimodal parity unqualified | Source equivalence only |
| 7 kvarn-candidate | experimental | Attention/cache: reduce KV storage | Memory safety, numerical drift, lifecycle | First full-model attempt failed before startup |
| 8 sampler-checkpoint2 | correctness | Sampling: transformed proposal/target and residual/status semantics | Native CUDA parity and propagation | CPU interpreter only |
| 9 kvarn-pack-layout | correctness | KVarN store: split packing to repair shared addressing | Full-model interactions remain unqualified | 90 attention + 2 status; zero sanitizer errors |
| 10 quant-loader-guard | correctness | Loader: validate runtime bindings before checkpoint comparison | Metadata checks do not prove startup | Source equivalence only |

### Mamba upstream equivalent and removal gate

Upstream PR #37818, commit `b805cc501444a6b98e26e3088851ba5e980704d7`,
tracks DFlash Mamba checkpoints from post-verify lengths. It is present in
reviewed public main `7078e5ffbc71f9f31d07018aff2f32530dac781a`, but absent
from our selected release base. The local stage 3 computes the same committed
boundary inside its helper. Retain it at the current pin. Remove it only after
a separately reviewed base update contains the equivalent fix and rejection,
cache and graph qualification passes. See `../docs/reference-audit.md`.

## Stage 11: native context rungs (new semantic experiment)

- **Base:** exact `source.env` plus stages 1–10, without changes to those patches.
- **Class/subsystem:** experimental capacity admission in KVarN argument, pool
  and memory-plan code. Benefit: request six explicit native DFlash contexts
  through 262144 without assuming a fixed 1929-page allocation.
- **Contract:** context in {131072, 163840, 196608, 229376, 245760, 262144};
  pool exactly context + 1024; physical pages = pool / 128 + 1, including null
  page. Actual allocated pool must equal the request, never silently downsize.
  Target/draft geometry, tile math, eight tails, query/write bounds, workspace,
  SM86/BF16, status and dummy-page ownership guards are unchanged. Graph mode
  remains restricted to context245760/pool246784.
- **Risk/validation:** larger native specializations have no GPU evidence.
  Existing kernels take page counts from tensor shapes; they do not allocate
  context-length attention scratch. CPU checks cover all six argument admissions,
  rejected capacities and modes, conservative target+draft byte accounting,
  scalar pool rejection and no-undersized-builder behavior. They do not prove
  GPU storage shape admission, compiler behavior, 24GB fit, model startup or
  quality. See `kvarn-native-rungs-cpu.json`; upstream PR status not recorded.

### Target-only blocker

The allocator loops can manage one pool, but native KVarN sticky-error checks at
request transaction boundaries exist only in `srt/speculative/dflash_worker_v2.py`.
The ordinary `srt/managers/tp_worker.py` forward-to-sampling path does not check
those errors before publication. Removing the DFlash or five-layer budget guards
would therefore admit an unsafe native no-draft path. Graph capture also requires
an eight-token `TARGET_VERIFY` batch. Stage 11 deliberately preserves both guards.
A separate no-draft implementation needs explicit matching budget/accounting and
host-side status propagation before sampling/cache publication, plus lifecycle
qualification. This is a source blocker, not a measured target-only GPU failure.

## Stage 12: nullable no-LoRA defaults

**Base:** unchanged stages 1–11 at `source.env`. **Class:** compatibility.
**Subsystem/purpose:** packed target constructor admission; accept upstream's
ordinary no-path nullable enable flags, which are not normalized to `False` by
the no-LoRA CLI path. Only identity `None` and `False` are accepted for
`enable_lora` and `enable_lora_overlap_loading`; `lora_paths` must be `None`.
True flags, invalid types (including integer zero), empty/nonempty path values
and unsupported generic modes still fail. No LoRA implementation is enabled.
All other guards, tensor math, kernels and capacities are unchanged.

**Risk/validation:** this fixes a source-proven default mismatch, not later
loader or GPU behavior. Forty-two CPU cases exercise the actual constructor
with real config classes and mocked process context, stopping at the next
unchanged loader guard. Cases cover four allowed default combinations,
16 invalid flags, seven invalid paths and15 unchanged generic-mode rejections.
No model tensors, GPU or numerical checks ran. Evidence:
`packed-embedding-lora-defaults-cpu.json`. Upstream PR status: not recorded.

**Stage 13 — hybrid wrapper attribute aliases:** the 0.98 GPU admission window
allocated both KV pools and then crashed in `HybridLinearAttnBackend.__init__`
because `KVarNAttnBackend` never set `token_to_kv_pool`, `req_to_token_pool` or
`kv_index_translator`. The stage adds the three aliases exactly as upstream
flashinfer/triton constructors do. Risk/validation: nine CPU cases ran the real
constructor and wrapper against subclassed stub pools with isinstance guards
intact; a negative control reproduces the pre-fix AttributeError. No tensors,
model loading, GPU or numerics ran. Evidence: `kvarn-hybrid-attrs-cpu.json`.
Upstream PR status: not recorded.

## Stage 15: query-tiled packed attention kernel

**Base:** unchanged stages 1–14 at `source.env`. **Class:** performance repair
of a measured defect. The 2048-token kernel profile
(`../bench/results/packed-kvarn-2048-kernel-profile.json`) localized the
40–70× depth-dependent prefill gap entirely to `_packed_attention_split`
(63% of GPU busy, ~0.7% of fp32 peak, mean duration growing with cached depth
while GEMM/GDN/store stayed flat). **Subsystem/purpose:** retile the native
split kernel so one program serves every query row of the microbatch and the
whole grouped-head slice of one KV head: each packed page is dequantized once
per program (not once per query-head), masks load once per page block, and
scores/updates run through tensor-core `tl.dot` with fp32 accumulation and
tf32 inputs instead of per-token fp32 multiply-reduces. The PyTorch oracle
`packed_attention`, the reduce kernel, the store pipeline, the 8-query
microbatch loop, workspace shapes and the reviewed 64 MiB envelope are
unchanged. Kernel policy (bounds, raw/packed/preview/sink selection, sticky
status bits, empty-row zeros) is preserved; the wrapper documents the
single-request tile contract the backend already constructs.

**Risk/validation:** tensor-core/tf32 arithmetic differs numerically from the
per-query fp32 kernel inside the packed-value quantization envelope; parity is
validated by `qualification/kvarn-prefill-tile-parity.py` on one exclusive GPU
against the unchanged PyTorch oracle at the packing-repair tolerances
(atol 2⁻¹⁰, rtol 2⁻⁷, rmse 2⁻¹¹), including a serving-first-chunk (8-token
incomplete page, int64 table) case, raw-tail pages, partial-page bounds, empty
rows, sub-8 query counts and sticky-status negative controls. Serving required
three kernel revisions after the first parity pass: multiplicative masking
instead of 1-D `tl.where` (MLIR layout bug at TABLE_WIDTH=2057), int32 copies
of serving metadata, and 4-query/ROWS=32 wrapper tiles after the 8-query/ROWS=64
specialization CUDA-OOM'd at 0.67 GiB free. Host-side empty-split elision
launches only working splits (reduce masks the rest). Measured 2048-token
re-profile (`../bench/results/packed-kvarn-2048-kernel-profile-stage15.json`):
split 3.06× total / 6.12× per launch vs stage-14, chunk1→chunk2 mean growth
4.6×→1.17×. Measured 8192-token eight-chunk re-profile
(`../bench/results/packed-kvarn-8192-kernel-profile-stage15.json`): split mean
101→453 µs, linear ≈6.3 µs/page; elision helps only while pages<16; 26× gate
not met; naive 262144 split extrapolation ~3.8 h. No capacity or quality claim.
Benches are unchanged.

## Stage 16: 32-query prefill tile

**Base:** unchanged stages 1–15. **Class:** performance repair. Workspace
`max_query_tokens` 8→32 (64 MiB envelope still holds), backend prefill
chunk equals the workspace, kernel fuses those 32 queries in one launch
(internal 4-query tiles, BLOCK=32). Verify remains an 8-token block.
Measured 8192-token re-profile
(`../bench/results/packed-kvarn-8192-kernel-profile-stage16.json`): wall
143s→35s, launches 32768→4096, busy fraction 0.54→0.90. Marlin 45% at this
depth. 262144 split extrapolation ~2.0 h. syv-ai KVarN prefill at 100k is
1050 tok/s; this run is 568 tok/s GPU-span at 8k. KV-once across internal
tiles (`kvarn-prefill-kv-once.patch`) failed: 8192 41.2 s and 32768 169.4 s
versus stage16 35.0 s / 105.5 s. Not in the series.

## Stage 17: fused 32-query × one grouped head

**Base:** stages 1–16 (query32, not kv-once). **Class:** performance repair.
One program is all query rows of one grouped head and one split; packed K/V
dequantizes once per page tile; softmax accumulators stay in registers.
Grid `(query_heads, splits)` not `(kv_heads, splits)`. Overlay on stage16:
parity passed (48.7 s); 8192 wall 16.8 s vs 35.0 s; 32768 wall 107.6 s vs
105.5 s. No 32k gain. Not in the series. Benches unchanged.

## Stage 18: dequant + FlashInfer prefill

**Base:** stage16 query32. **Class:** performance repair. Huawei/syv path:
materialize packed tiles in rotated space, FlashInfer, Hadamard Q and
output only. Backend writes 128-token pages and seals before one FA over
the full query chunk. Chunk 64 pages (~33 MiB) above that. Overlay on
stage16: flash vs oracle rmse 7e-5; 8192 wall 15.2 s vs 35.0 s; 32768
wall 50.4 s vs 105.5 s (~650 tok/s). 8192 GPU profile: Marlin W4A16 6.16 s,
FlashInfer prefill 0.25 s. FA loses at 1024 (5.27 s vs stage16 4.05 s);
GPU-span 1569 tok/s still ahead. Rebuilt series image f0df3d2f (17 patches):
oracle rmse 7e-5; 8192 wall 17.9 s; 32768 wall 52.9 s. Benches unchanged.

## Stage 18b: always-FA dispatch

**Base:** stage18. **Class:** bug fix in the stage18 dispatch. The
`max_upper<=2048` gate ran the stage16 split kernel on the first two chunks
of every request; the gap profile (trace 1789405790, busy 0.914) shows
split-attn 0.70 s vs FA 2.4 ms per layer-chunk in-request — the standalone
1024 comparison had been JIT-skewed. Dispatch is now FA whenever native.
Patch sha256 623e7ba4640942cb6ef9dd9870e0c1416bc13d02dd272b40da8b507d3c54c7c8.
Image 7b2d45db: 8192 wall 16.9 s; 32768 wall 45.7 s (717 tok/s, 2.31x
stage16). Marlin measured at the fp16 ceiling (61-63 TFLOPs; cuBLAS 69;
torch._int_mm int8 44-50 TOPS, slower); the only lever beyond this is the
vLLM marlin-int8 W4A8 transplant. Benches unchanged.



## Stage 21: attention correctness repairs (P0-A/P0-B)

**Base:** stage20 series (through dflash-draft-vocab). **Class:** correctness
repair of two source defects introduced by earlier stages; both invalidated the
speed records measured on top of them.

**P0-A — inverted live-row mask in `packed_attention_out_nosync`.** Stage19j
(5da6aba) replaced the correct `output[empty] = 0` zeroing with
`output.mul_(torch.logical_not(row_live)...)` while removing host syncs for
CUDA-graph capture. The polarity is inverted: LIVE verify rows were multiplied
by zero and dead/padded rows were kept. The mask ran on every eight-token
target-verify step, so stage19j/19/20 generations came from a model whose
full-attention layers contributed zero attention output; the live endpoint
emitted incoherent text and the 26.5-155 tok/s records were measured on that
corrupted path. Stage19g parity (rmse-identical, `output[empty] = 0`) was
never re-run after the stage19j rewrite. Fix: `output.masked_fill_(~row_live,
0)` — assignment semantics (a stale NaN workspace cannot leak through
multiplication by zero), device-side only, CUDA-graph safe.

**P0-B — un-normalized, wrong-base chunk merge in `packed_attention_flash`.**
Since stage18 (09940c8), multi-chunk prefill (>64 pages = >8192 tokens)
combined FlashInfer-normalized chunk outputs as `a*O1 + b*O2` without dividing
by the merged softmax mass `a+b`, and computed weights with `torch.exp`
although FlashInfer returns log2-domain LSE (`ptx_log2` in the kernel). Every
context deeper than 8192 tokens was served with attention outputs scaled by up
to the chunk count. The stage18 oracle check ran only at 8192 tokens (exactly
one chunk), so the merge was never covered. Fix: exp2 weights, divide by
`a+b` (zero-mass rows stay 0/-inf), log2-domain LSE bookkeeping.

**Qualification:** `qualification/kvarn-attention-regressions.py` (exclusive
GPU, inside the candidate image). P0-A: mixed live/dead rows, graph-padding
geometry (n<queries), all-dead, the production all-live eight-token verify
block, NaN-poisoned workspace, and a negative control that re-applies the
inverted mask and must be detected. P0-B: 130-page (three-chunk, uneven, raw
tail) FA parity against the unchanged PyTorch oracle, a single-chunk control,
an empirical FlashInfer LSE-base probe (measured ratio to natural log 1.4427 =
1/ln2), and the equal-mass merge spec (outputs 2 and 4 must merge to 3).
Evidence: `../bench/results/attention-regressions-stage20-pre-fix.json`
(FAIL: live rows erased; multi-chunk rmse 1.1e-2) and
`../bench/results/attention-regressions-stage21-post-fix.json` (PASS: live-row
rmse 4.9e-5; multi-chunk rmse 2.5e-4 within the FA gate of kernel tolerances
plus one output bf16 ulp). Module identities recorded inside both reports.
All earlier stage19j/20 speed and acceptance records remain historical and are
not promotable; corrected measurements follow in the decode ledger.


## Stage 22 (staged, uncommitted): B2 commit-tail capture + store B-spec

**Base:** stage21 series (through dflash-draft-vocab). **Class:** performance.
Behind `--kvarn-commit-graph` (default OFF; requires graph mode; eager
fallback on capture failure, logged).

**C4 (audit F4).** Free-slot pinned mirror (`refresh_free_slot_mirror` /
`mirrored_tail_slots`, exact fallback on stale), device-only
`mark_sink_pages_out`, allocator admission reads the mirror. Removes the 42
scalar admission readbacks per check. Proof: 100 sync-free reads under
sync-debug-error, exhaustion fails closed to 0, refresh converges exactly.

**C2.** `begin/finish_status_mirror` (pinned D2H + event); draft check
overlapped across verify-input prep; post-verify drain removed on the fast
path; commit-tail + draft-append gated by ONE end-of-step check before
on_publish/results (fail-closed contract unchanged).

**C1.** `_KVarNCommitGraphRunner` captures the target commit loop +
draft-append branch; static buffers = worker locs/positions + own
commit_lens/hidden; neutral dummy-page warmup; dedicated graph mempool.

**Store B-spec (audit F6).** `_prepare_write` validation lanes sized
`B=next_power_of_2(count)` instead of fixed 128; GPU-qualified through the
full R1 suite including capture/replay.

**Qualification (overlays in `/tmp/b2impl`, fixtures + logs there):** R1
capture/replay bit-identical (commit_lens 0..8, poisoned no-op); R2 3-step
chain oracle bit-exact (accept 3/6/4); R3 shadow counter 200 trials, 0
mismatches; C4 admission proof; full suite re-run green on the built image.
Live validation found and fixed three integration bugs the fixtures cannot
see: the worker predicates `_kvarn_commit_graph_enabled/_supported` were
called but never defined; `mark_sink_pages_out` must stage CPU-resident
sink indices onto the cache device during capture prep; pinned mirrors must
be allocated outside `torch.inference_mode` (inference tensors reject
out-of-mode inplace updates). A/B store-tail bench (16+5 layers, 50 steps,
status 0 both arms): eager 8079/8164/8303 us/step vs captured
1142/1068/1066 @8/64/230 pages (7.1-7.8x, depth-independent; serving-scaled
~4.3 ms/step).

**ON arm unblocked (two live-only root causes, both fixture-pinned):**
(1) ensure_capture's warmup ran `discard_provisional` pool-wide AFTER the
verify graph staged the step, wiping it; capture now happens once at
decode-branch start, before any pool mutation (probe hidden sized to the
draft's concatenated context-feature width, not raw hidden). (2) the worker
tail appended target-hidden to draft KV UNCONDITIONALLY after replay —
the replay already contains that append, and re-appending committed rows
sets sticky bit 1; the tail now skips the eager append on replayed steps
(`commit_graph_replayed`). `qualification/kvarn-commit-graph-blocker.py`
pins both: A (warmup-wipe repro, must fail), B bit-1 fail-closed,
C neutral, D bit-4 independent, E fixed order, F real-tail repro
(detector), G gated-append fix; suite exit 0 on the built image.
Deployed endpoint runs stage22 with the flag ON.

## Stage 22 (deployed): F1 packed-NaN gate + F6 store B-spec

`kvarn-packed-gate.patch` gates packed loads and matmuls on representation
validity (raw-only sink pages and incomplete pages never feed the packed
operand); the deployed kernel's NaN contamination is reproduced by
`qualification/packed-nan-regression` (CPU proof + GPU fixture with
negative controls; deployed goes NaN where [5,7] is expected, gated fix is
exact, and bit-identical on finite data). The gate also removes the
redundant dual raw+packed computation: 984 vs 1810 us/launch at 230 pages.
`kvarn-store-bspec.patch` sizes `_prepare_write` validation lanes to
`next_power_of_2(count)` (audit F6). Measured 5-rep medians vs stage21:
90.9 (+12.7%) @1k, 76.9 (+9.6%) @8k, 57.1 (+26.9%) @32k
(`bench/results/decode-c1-stage22-off.json`).