# Decode bottleneck ledger

Machine-readable experiment results accompany each entry under
`bench/results/`; this file records the loop
profile -> rank -> reproduce -> minimal patch -> correctness test ->
paired benchmark -> keep/revert -> profile again for the sustained
single-request decode objective (RTX 3090, TP1, KVarN + DFlash2).

Baseline identity changes are recorded per entry. All stage19j/20 speed
records were measured on corrupted attention (see P0-A/P0-B in
[patch notes](../patches/NOTES.md)) and are not comparison baselines.

## Corrected baseline (stage21, image built from a7598a5)

Single-request streamed chat completions, exact input depths, 1024 committed
output tokens, greedy; `committed_tok_s = completion_tokens / (wall - TTFT)`.
Powers measured at the wall socket cap (280 W hardware limit).

Five paired repetitions each (`decode-c1-corrected-stage21.json`), median
(min..max):

| depth (actual) | TTFT s | decode tok/s median (range) | accept gauge | watts p50 |
|---:|---:|---|---:|---:|
| 1076 | 1.25 | 80.7 (78.8-90.4) | 2.4-4.9 | 268 |
| 8244 | 9.20 | 70.2 (66.9-76.3) | 3.1-5.5 | 270 |
| 32821 | 40.77 | 45.0 (43.5-47.9) | 2.7-3.6 | 275 |

Derived cycle time at the median accept gauge: ~36 ms (1k), ~50 ms (8k),
~70 ms (32k). Acceptance is content-dependent and comparable to the
competitor's 3.1-3.4; the deficit is cycle time.

Engine telemetry: `cuda graph: True`, accept 3.0-4.9 content-dependent,
engine gen throughput bursts 72-195 tok/s.

## B1 — verify attention cost grows with context depth

ID/priority/status: B1 / high / hypothesis, profiling pending.
Exact source location: `_packed_attention_split` launched by
`packed_attention_out_nosync` (patches/kvarn-prefill-flashinfer.patch);
per-layer per verify step.
Observed symptom: decode cycle time grows ~36 ms (1k ctx) -> ~63 ms (8k) ->
~78 ms (32k) while accept stays ~3-3.5; stage15 measured ~6.3 us/page for the
same kernel family; 256 pages x 16 layers x 6.3 us is ~26 ms at 32k context.
Mechanism: each verify step re-scans every packed KV page of the request
through a dequantizing Triton kernel; per-page cost dominates and scales
linearly with depth. Competitor attention cost at 25k context is ~1 ms per
verify position (~10x lower per page).
Affected workloads: every C1 decode deeper than a few thousand tokens.
Measured critical-path cost: pending profiler split (B1 profiling step).
Evidence: corrected baseline rows above; stage15 kernel profiles
(`packed-kvarn-*-kernel-profile-stage15.json`); hypothesis must be confirmed
by trace before patching.
Proposed fix: faster paged verify attention for the 8-query shape (SM86
specialization: 24 q heads / 4 kv heads / d 256, 8 rows), or amortized
dequant; prove parity against the PyTorch oracle via
`qualification/kvarn-attention-regressions.py`.
Correctness risks: inactive-row semantics, grouped-head indexing,
provisional/sink page policy must be preserved exactly.
Test/benchmark: regression fixture + `bench/decode.py` paired runs.
Decision: open.
Next largest bottleneck: B2.

## B2 — base cycle time at shallow context (36 ms vs competitor 26.5 ms)

ID/priority/status: B2 / high / open.
Observed symptom: at ~1k context the full speculative cycle costs ~36 ms
(81.5 tok/s at accept ~2.9); the competitor's DFlash2 step is 26.5 ms at
comparable accept. Marlin W4A16 target forward is measured at the fp16
ceiling (61-63 TFLOPs), so most of the gap is not GEMM throughput.
Suspects: per-step Python/bookkeeping outside graphs, draft launch overhead,
hidden-state gather, sampling, KVarN page lifecycle, detokenizer handoff.
Measured critical-path cost: pending profiler split.
Decision: open.

## B3 — client-vs-engine streaming gap (resolved earlier, verify)

ID/priority/status: B3 / closed for stage21.
Stream-interval 4 aligned client rate with engine gen throughput in the
corrected baseline (client 81.5 vs engine bursts 72-95 at 1k). Re-check after
any detokenizer/stream change.

## B4 — attention correctness repairs (closed)

P0-A inverted live-row mask and P0-B chunk-merge normalization/base were
fixed in stage21 with regression evidence; see `attention-regressions-*.json`
and [patch notes](../patches/NOTES.md). All speeds above are corrected-path.

## Second-triage findings (user audit at 6652260; source-derived counts)

Correctness outranks speed; measured ranking pending (`profile-triage`).

| ID | prio | summary | status |
|----|------|---------|--------|
| F1 | P0 | uninitialized packed scales reach the packed matmul on raw-only/incomplete pages; 0 x NaN contaminates accumulator before the output mask | fix in flight (`p0-packed-nan`, /tmp/p0fix) |
| F2 | P1 | 68 completion calls x 7 kernels = 476 launches/cycle even when no page seals | measure (`profile-triage`); interacts with B2 capture |
| F3 | P1 | draft gather: 87,360 tiny programs/pass, success-path atomic_or(0) on shared status | masked-atomic fix in flight (`gather-atomic`, /tmp/gather) |
| F4 | P1 | capacity admission: 42 scalar readbacks per check | C4 (B2) expected to cover; validation pending |
| F5 | P1 | draft-vocab restriction still computes full output head then masks | measure then compact-head go/no-go |
| F6 | P2 | 8-token writes use 128x128 validation pair-grid (CPU-verified fix) | queued after B2 bench (`kernel-war`) |
| F7 | P1 | stochastic sampling probability prep serialized (.item() per row; vocab-wide scan per program) | stochastic-only, not greedy deficit; deferred |

GPU window queue: kernel-war (B2) -> p0-packed-nan -> profile-triage /
gather-atomic. Correctness (F1) outranks all perf work.

## Stage 22 measured (deployed, commit-graph OFF)

F1 (packed-NaN gate, `kvarn-packed-gate.patch`) + F6 (store B-spec) landed
with B2 C1/C2/C4 staged behind `--kvarn-commit-graph` (default OFF). Full
fixture suite green on the built image (R1/R2/R3/C4-proof + all three repo
qualification suites; `attention-regressions-packed-nan-stage22.json`
reproduces the deployed defect and proves the gate). 5-rep matrix
(`decode-c1-stage22-off.json`), median vs stage21 baseline:

| depth | stage21 | stage22-off | stage22-on (B2) | on-vs-stage21 |
|---:|---:|---:|---:|---:|
| 1076 | 80.7 | 90.9 | 115.5 | +43.1% |
| 8244 | 70.2 | 76.9 | 91.7 | +30.6% |
| 32821 | 45.0 | 57.1 | 66.6 | +48.0% |

The 100 tok/s primary-workload floor is met at 1k (115.5) and in reach at
8k (91.7). ON-arm evidence: `decode-c1-stage22-on.json` (5 reps, no
capture fallback, zero scheduler exceptions, memory stable at 23.4 GiB
through the 12-minute matrix).

F1 also halves verify-attention kernel time at depth (microbench 984 vs
1810 us/launch @230 pages): the gate removes the redundant dual raw+packed
computation, not just the NaN hazard.

**B2 ON arm blocked (live-only):** first real speculative step raises
`status bits=1` in the overlapped status mirror (commit_prefix receiving
rows never staged provisional — same artifact kernel-war observed in its
A/B bench warmup). Three live-only integration bugs were fixed on the way
(missing `_kvarn_commit_graph_enabled/_supported` predicates; sink-page
device staging during capture; inference-mode pinned-mirror allocation).
Fixtures cannot see this class — the staging contract needs a fixture with
non-provisional commit rows before the flag can default on.
