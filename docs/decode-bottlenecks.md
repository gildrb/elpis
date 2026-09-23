# Decode bottleneck ledger

Machine-readable experiment results accompany each entry under
`bench/results/`; this file records the loop
profile -> rank -> reproduce -> minimal patch -> correctness test ->
paired benchmark -> keep/revert -> profile again for the sustained
single-request decode objective (RTX 3090, TP1, KVarN + DFlash2).

Baseline identity changes are recorded per entry. All stage19j/20 speed
records were measured on corrupted attention (see P0-A/P0-B in
[patch notes](../patches/NOTES.md)) and are not comparison baselines.

## Decode measurement protocol

New `bench/decode.py` reports and individual rows carry `schema_version: 2`
and `measurement_protocol: "sglang-continuous-usage-counter-delta-v2"`.
They are not equivalent to historical schema-1/unversioned rows using
`completion_tokens / (wall - TTFT)`: that old numerator includes the first
already-delivered multi-token chunk although its denominator excludes its
delivery interval. Historical results below remain unchanged and must not be
merged with protocol-2 rates as equivalent measurements.

The frozen natural prompt corpus and EOS behavior are unchanged. Requests use
`temperature: 0`, `top_p: 1`, `n: 1`, no `top_k`, and both
`stream_options.include_usage` and `continuous_usage_stats`. On pinned SGLang
`0bcd822377da7b5718e674eaf9c870d349424dd1`, streaming content/reasoning chunks
carry cumulative completion counters from each generation return; the terminal
usage record has `choices: []` and is followed by `[DONE]`. Multiple chunks may
repeat the same cumulative count and are never counted as tokens.
An earlier `choices: []` chunk with no usage may carry a nonempty typed `sglext`
envelope instead: `routed_experts` is a string, and `cached_tokens_details` and
single-choice `spec_tokens_details` are objects. Null extension fields are
allowed alongside a nonnull supported field. These metadata-only chunks do not
establish terminal usage or contribute counter samples.

Every data line is timestamped with `monotonic_ns` immediately on client receipt,
before decoding/parsing. The exact integer timestamp fields are
`request_started_ns` (immediately before the HTTP request),
`first_content_or_reasoning_observed_ns` (first nonempty content OR reasoning
delta), `first_positive_counter_observed_ns`, `terminal_usage_observed_ns`,
and `done_observed_ns`. Request timing excludes prompt sizing, serialization,
and speculation-gauge reads. `ttft_s` remains separately defined as
`(first_content_or_reasoning_observed_ns - request_started_ns) / 1e9`.

Each row preserves `prompt_tokens`, terminal `completion_tokens`,
`finish_reason`, `first_positive_completion_tokens`, and all `counter_samples`
in receipt order. Each sample contains the raw `prompt_tokens` and
`completion_tokens`, exact `observed_ns`, and a `terminal` boolean; equal
counter samples are retained. Derived fields are:

- `counter_window_tokens = completion_tokens - first_positive_completion_tokens`.
- `counter_window_ns = terminal_usage_observed_ns - first_positive_counter_observed_ns`.
- `committed_tok_s = counter_window_tokens * 1e9 / counter_window_ns`:
  **post-first-counter committed rate**, including client/transport observation
  costs, not kernel-only throughput and not the historical decode estimate.
- `elapsed_ns = done_observed_ns - request_started_ns`;
  `elapsed_seconds = elapsed_ns / 1e9`.
- `whole_request_tok_s = completion_tokens * 1e9 / elapsed_ns`:
  whole-request completed rate with an explicit request-start-to-DONE boundary.

The report retains its classification, running-container identity, rows, and
`committed_tok_s_min`/`committed_tok_s_max` (now exclusively protocol-2 rates);
rows retain depth/repetition, power evidence, and speculation gauges.
Admission requires a valid terminal usage record followed by DONE, a successful
`stop` or output-budget `length` finish reason, first content/reasoning, consistent
prompt counts, nonnegative nondecreasing exact integer completion counters
(booleans are invalid), a positive token delta, and positive counter/request
windows.
Completion counters cannot exceed the requested output budget; `length` requires
the terminal count to equal that budget, while natural `stop` may be shorter.
Choice deltas must be objects or null, with content/reasoning fields strings or
null; only nonempty strings establish TTFT.
A single positive counter repeated through terminal usage cannot produce a rate.
Missing or invalid evidence fails; there is no legacy estimate or
chunk-count fallback. Unsupported depth matrices fail before any row runs,
rather than silently dropping depths.

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

## Guarded eight-stage Marlin: exact fixtures, performance pending

The eight-stage candidate changes the retained four-stage copy pipeline only
for guarded original M1–8 SM86 BF16/U4B8/group128 full-K inputs, without
act-order/zero-points, using the already-selected128-thread M8/N128/K64 tile.
K%128=0, group_blocks8, blocks_per_sm1, non-atomic reduction and a51200-byte
conservative shared guard are required. Actual M8 addressing is43008 bytes;
grid, K stripes, reduction grouping, scratch and launch reservation are unchanged.
Only the compiled Bend policy selects stages8; otherwise stages4 remain.
Admission binds source schema9, verified schema6 and runtime wireV2.

The24 checked Bend2.0.26 laws establish policy/wire, period-two ring phase,
ordered tile/MMA and symbolic recurrence contracts plus layout/schedule
arithmetic—not CUDA async/memory safety, compiler refinement or native F32
equivalence. The root proof passed67.69s; generation/compile/verify, four CPU
consumers and the always-fallback-wire rejection passed. See the
[qualification scope](qualification.md#guarded-eight-stage-marlin-candidate-sampled-exactness-benchmark-pending).

Real candidate JIT passed231.13s. Fresh guarded captures and CPU comparison
passed624/624 bit-exact output fixtures and624/624 eager/graph dispatch pairs,
including graph/scratch checks. Observed registers108→117, stack0/local0,
shared reservation101376 bytes and grid82 do not establish occupancy or speed.
Image: `sha256:94d6dd975e406413ff8cdaa2bbccbaa181c3760379dbaeb50072e774e54e90e8`.
Private evidence under `/tmp/litos-recovery-ops-id8q0yvb/`:
`marlin-eight-stage-baseline-evidence-1`,
`marlin-eight-stage-candidate-evidence-1`,
`marlin-eight-stage-comparison-evidence-1`.

**Frozen benchmark pending; no throughput claim or promotion.** Retained best
remains95.380797 tok/s. Full-K-grid and two-stage candidates remain rejected:
their frozen short-I3 reward fell1→0, despite the latter's624 exact fixtures.
Sampled kernel parity is not whole-model equivalence or quality admission.
