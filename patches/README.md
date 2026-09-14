# Ordered SGLang patches

Apply patches only in a disposable build checkout at the exact commit in
[`source.env`](source.env):

```sh
git clone https://github.com/sgl-project/sglang.git /tmp/sglang-build
git -C /tmp/sglang-build checkout --detach 0bcd822377da7b5718e674eaf9c870d349424dd1
bash patches/apply.sh /tmp/sglang-build baseline
```

The source pin is the exact commit also resolved by `v0.5.19`, not a mutable
tag selection or the historical already-patched fork revision. The script requires an exact, clean
Git checkout, checks every selected patch SHA256, and runs ordered
`git apply --check --index` and `git apply --index`. It never launches a server.
Do not use a live or shared checkout. A failed application leaves a disposable
partial build, not an acceptable runtime.

| Order | Classification | Patch |
|---|---|---|
| 1 | Baseline | `packed-head-predicate.patch` |
| 2 | Baseline | `quant-aware-fc.patch` |
| 3 | Baseline | `mamba-cache-prefix.patch` |
| 4 | Experimental | `qwen3_5.patch` |
| 5 | Experimental | `packed_w8_embedding.patch` |
| 6 | Experimental | `mm_utils.patch` |
| 7 | Experimental | `kvarn-candidate.patch` |
| 8 | Experimental | `sampler-checkpoint2.patch` |
| 9 | Experimental | `kvarn-pack-layout.patch` |
| 10 | Experimental | `quant-loader-guard.patch` |
| 11 | Experimental | `kvarn-native-rungs.patch` |
| 12 | Experimental | `packed-embedding-lora-defaults.patch` |
| 13 | Experimental | `kvarn-hybrid-attrs.patch` |
| 14 | Experimental | `kvarn-reserved-accounting.patch` |
| 15 | Experimental | `kvarn-prefill-tile.patch` |
| 16 | Experimental | `kvarn-prefill-query32.patch` |
| 17 | — | `kvarn-prefill-kv-once.patch` (rejected; not in series) |
| 18 | Experimental | `kvarn-prefill-flashinfer.patch` |

[`baseline.series`](baseline.series) contains stages 1–3.
[`experimental.series`](experimental.series) contains stages 4–18, appended to
the baseline only when `experimental` is explicitly passed instead of `baseline`
on a **fresh** checkout. Each line is `SHA256  patch-filename`; line order is
application order. These are build sets, not runtime profiles.

The experimental set covers 40 files (23 modifications and 17 additions).
KVarN remains experimental: its first full-model 240K attempt failed before
startup. The packing repair passed 90 attention and two status small-fixture
cases with zero memory-check errors. This does **not** qualify full-model
capacity, quality, performance, cache lifecycle or CUDA graphs. Sampler CPU
interpreter checks do not establish native GPU parity.

[`NOTES.md`](NOTES.md) records source provenance, loader restrictions and
historical GPU evidence limits. [`migration-evidence.json`](migration-evidence.json)
records exact byte equivalence to the prior working-tree patch chain, including
the quant-loader guard. No full upstream originals or custom reconstruction
framework remain. SGLang is Apache-2.0; see [`LICENSE.sglang`](LICENSE.sglang).

## New native capacity experiment

Stage 11 is a separate semantic change, **not** part of the ten-stage migration
byte-equivalence proof. Native DFlash source admission now supports exactly
131072, 163840, 196608, 229376, 245760 or 262144 context tokens, each with an
explicit pool of `context + 1024`. Page-dependent storage guards derive their
sizes from that validated capacity. An undersized actual pool is rejected.
CUDA graphs remain limited to the previous 245760 envelope; no graph capacity
claim is added. Target-only remains source-blocked: the normal worker lacks
KVarN's required sticky-error check before sampling/publication.

[`kvarn-native-rungs-cpu.json`](kvarn-native-rungs-cpu.json) records 132 CPU
admission, integer budget and scalar pool checks in the pinned runtime image.
Platform admission is mocked; real pool scalar checks stop at the CUDA-only
boundary. These checks do not allocate native pools, compile CUDA kernels,
prove model fit or qualify GPU execution. All previous GPU evidence remains
bound to its old source and small-fixture scope.

## Nullable LoRA defaults compatibility

Stage 12 accepts only identity `None` or identity `False` for the two upstream
LoRA enable flags, and requires `lora_paths is None`. Normal no-LoRA CLI defaults
are nullable; no false CLI flag is available. `True`, numeric zero, other types
and any path value remain rejected. Every other packed loader guard is unchanged.
This enables no LoRA feature and changes no tensor math, kernels or capacity.
See `packed-embedding-lora-defaults-cpu.json`: 42 CPU cases ran the actual
constructor through these guards, then deliberately stopped before loading.
Passing admission does not establish model startup or numerical/GPU parity.

## Hybrid wrapper attribute aliases

Stage 13 sets the three attributes upstream's `HybridLinearAttnBackend` reads
from its full-attention child — `token_to_kv_pool`, `req_to_token_pool` and
`kv_index_translator` — matching the flashinfer/triton constructor convention.
The 0.98 admission window proved the gap: pools allocated, then
`AttributeError: 'KVarNAttnBackend' object has no attribute 'token_to_kv_pool'`
before API readiness. See `kvarn-hybrid-attrs-cpu.json`: nine CPU cases ran the
real constructor and the real wrapper with subclassed stub pools; a negative
control confirms the pre-fix contract still fails. This is wiring only: no
tensor math, kernel, GPU startup or capacity claim.

## Allocator-reserved token accounting

Stage 14 makes allocator-owned lifetime tokens a first-class component of the
idle memory-conservation invariant. The KVarN page allocator reserves exactly
one 128-token page for the graph-dummy address (`reserve_graph_dummy_page`,
enforced for the runner lifetime by `_release_page_ids`), so
`available + evictable + protected + session_held + uncached` falls 128 short
of `total` forever. The 0.98 stage-13 window proved it: pools built to
`total=263168`, the scheduler entered its event loop, and the first idle tick
crashed with `pool memory leak detected! [full] total=263168, available=263040`.
The reservation is by design; the leak report was false. `BaseTokenToKVPoolAllocator`
gains `reserved_size()` (default 0), `KVarNPageAllocator` reports the dummy page,
and the invariant becomes
`available + evictable + protected + session_held + uncached + reserved == total`
with `reserved` printed in every pool message. See
`kvarn-reserved-accounting-cpu.json`: 22 CPU cases ran the real allocator
(free-list arithmetic, reservation, `clear`, lifetime-free guard) and the real
checker (hybrid-SSM idle path, busy path, stock-allocator non-regression,
pre-fix negative control) inside the pinned stage-13 runtime image. This is
accounting only: no tensor math, kernel, GPU startup or capacity claim.

## Query-tiled packed attention kernel

Stage 15 repairs the measured prefill defect: the kernel profile showed
`_packed_attention_split` alone carried the depth-linear chunk-time slope
(63% of GPU busy at ≤2048 tokens, one program per query per head, fp32
multiply-reduces, per-query-head re-dequantization). The retile serves all
microbatch query rows and one KV head's grouped heads per program, dequantizes
each packed page once, loads page masks once, and computes scores/updates with
tensor-core dots (fp32 accumulate, tf32 inputs). Kernel policy and every
reviewed envelope (workspace, store pipeline, microbatch loop) are unchanged.
Validation is the GPU parity fixture `qualification/kvarn-prefill-tile-parity.py`
against the unchanged PyTorch oracle plus a measured re-profile of the prefill
slope; neither has run yet at this writing. No capacity or quality claim.
