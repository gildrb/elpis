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

[`baseline.series`](baseline.series) contains stages 1–3.
[`experimental.series`](experimental.series) contains stages 4–11, appended to
the baseline only when `experimental` is explicitly passed instead of `baseline`
on a **fresh** checkout. Each line is `SHA256  patch-filename`; line order is
application order. These are build sets, not runtime profiles.

The experimental set covers 38 files (21 modifications and 17 additions).
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
