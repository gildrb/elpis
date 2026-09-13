# Fresh procedural reasoning benchmark

Use `bench/reasoning.py` for bounded fresh-task quality measurement. It is not a serving-speed replacement, release gate, broad intelligence score, or proof of speculative/non-speculative equivalence. No passing threshold is declared. Keep the existing historical fixtures and results.

## Measured held-out result

The original frozen 8K producer scored **78/180 (43.3%)** on fresh held-out tasks:
**96 truncations**, **6 incorrect completed answers**, and zero API/parser/scorer/
generation failures. All requests remain in the denominator. The fixed plan and
original pilot exclusion were independently verified. Read the
[allowlisted evaluation](../bench/results/reasoning-evaluation.json) and
[family breakdown and limits](qualification.md#held-out-reasoning-evaluation).

The **13/18 at 32K** result is a separate post-hoc comparison on the eighteen pilot
questions. Do not substitute it for this 180-question 8K evaluation or pool the
results. Exact reproduction of the recorded evaluation needs its original
`cb941c7a…` source snapshot, not the newer `--bank-from` producer.

## Environment and CPU preparation

Reasoning Gym is pinned to [`49b07130b3fcd12f2d064bba7c43869543a0e7e7`](https://github.com/open-thought/reasoning-gym/tree/49b07130b3fcd12f2d064bba7c43869543a0e7e7). `pyproject.toml` selects the exact Git revision; `uv.lock` locks transitive packages. Build-tool versions are constrained explicitly, including setuptools, wheel and Hatchling. Use the repository's pinned Nix shell, which supplies Python 3.13 and the compiler needed by `pycosat`. Do not use unpinned `nixpkgs` shells or an arbitrary global Python environment.

```console
nix develop path:. --no-write-lock-file -c uv sync --locked --python python3.13 --no-managed-python
nix develop path:. --no-write-lock-file -c uv run --locked --python python3.13 --no-managed-python bench/reasoning.py --generate-only --count 2 --model-identity REVIEWED-INVENTORY-SHA256 --output /tmp/reasoning-pilot-bank
```

The output directory must not exist. Its parent must already exist. Every directory is mode 0700 and every generated file is mode 0600. No API call occurs in `--generate-only`. Both split banks are generated and every oracle must receive full credit from its upstream scorer. Generation is CPU work, including SAT-backed Zebra puzzles.

## Frozen design

`bench/reasoning-plan.json` predeclares nine equally weighted strata. The runner validates their exact configuration. Changing the design requires reviewing both files before collecting results.

| Family | Strata | Verified source behavior and limits |
|---|---|---|
| `knights_knaves` | 6, 8, 10 people; depth 3; width 3 | Enumerates truth assignments; rejects no-solution and multiple-solution problems. Only exact full assignment credit counts. |
| `zebra_puzzles` | 6 people × 5 characteristics; 7×6 | SAT-backed logic puzzle. Asks for **one person**, not the complete grid. |
| `shortest_path` | 24×24 and 32×32; 0.20 blocked | Custom conditioned distribution: feasible and optimal route length at least the grid side. BFS oracle accepts alternative optimal routes. |
| `sokoban` | 9×9; 5 boxes; generator search depth 120 | Scorer simulates moves and accepts a solved board; does not require the oracle route or minimal length. |
| `rearc` | 3 demonstrations; demonstration/query RNG bounds 0.30–0.70; query PSO 0.15–0.60 | Procedural ARC-like transformation. Full credit requires exact output grid; well-formed incorrect grids can earn upstream partial reward, counted incorrect here. |

This is plan schema **2**, chosen after the first smaller-difficulty pilot revealed a ceiling. That first pilot is discovery evidence, not an independent score baseline. Freeze this plan before its new pilot and fresh held-out evaluation. Do not pool results across these distributions.

Source inspection: `reasoning_gym/logic/knights_knaves.py`, `logic/zebra_puzzles.py`, `logic/contrib/logic_puzzle/`, `graphs/shortest_path.py`, `games/sokoban.py`, and `arc/rearc.py` at the pinned revision. Paths report feasible/infeasible counts, minimum/maximum solution lengths, and an always-`infeasible` baseline (zero under the new explicit conditioning). Conditioning rejections are counted per stratum across both generated banks. Path sampling separately counts feasible/infeasible candidates, too-short feasible rejections and duplicate rejections. Direction metadata is validated and must match the oracle answer. This is not the upstream unconditional path distribution. Native scorer entries are preserved after strict JSON-boundary validation: REARC output tuples must not be replaced by serialized lists when scoring.

`--generation-timeout 120` sets a per-item generator wall deadline, separate from the HTTP inactivity timeout. Linux main-thread SIGALRM interrupts generator work and restores the previous handler; a preexisting alarm is never replaced. Long uninterruptible native calls may delay Python signal handling. A generator failure or deadline writes a private counted failure artifact and aborts the run, without silently substituting an easier/faster item. Upstream REARC/Sokoban contain otherwise unbounded retry loops.

Each invocation draws independent 256-bit pilot and evaluation root seeds. SHA256 domain separation includes split, stratum, item index and retry. Every upstream dataset has size 1 and is indexed at 0; this avoids overlapping `Random(seed + idx)` ranges. Duplicate final prompt hashes are rejected across both banks, with at most 1000 candidates per item (conditioning and deduplication combined). This removes byte-identical prompts, not isomorphic puzzles or semantic duplicates.

`commitment.json` commits the plan, requested settings, model identity, runner and lock digests, and both seed commitments. `frozen.json` commits all prompt hashes before inference starts. Seeds, questions, expected answers and generated text remain private. Evaluation inference requires `--pilot-run` to exclude every prompt in the referenced prior pilot's banks. Use the pilot for the same frozen plan/schema. Only that supplied pilot is excluded; retain and reference the pilot used for design decisions. Pilot outcome-driven changes require a new plan before fresh evaluation; never reuse evaluation as a tuning set.

## Approved inference invocation

Obtain approval before using the GPU endpoint. Prefer exclusive access. If the service is shared, label the run shared-load and do not compare its timing with isolated serving evidence. The runner sends one request at a time, never flushes caches, never changes server capacity and never calls `server_info`. Replace the model identity placeholder with reviewed immutable deployment and model provenance, not merely the served alias. The runner validates the response model alias but cannot independently establish the actual loaded weights.

```console
nix develop path:. --no-write-lock-file -c uv run --locked --python python3.13 --no-managed-python bench/reasoning.py --mode pilot --count 2 --endpoint http://127.0.0.1:18020/v1 --key-file /mnt/ssd/storage/ai/qwen3.8-27b/api-key --model qwen3.8-27b --model-identity REVIEWED-INVENTORY-SHA256 --thinking enabled --max-tokens 8192 --output /tmp/reasoning-pilot
nix develop path:. --no-write-lock-file -c uv run --locked --python python3.13 --no-managed-python bench/reasoning.py --mode evaluation --count 10 --pilot-run /tmp/reasoning-pilot --endpoint http://127.0.0.1:18020/v1 --key-file /mnt/ssd/storage/ai/qwen3.8-27b/api-key --model qwen3.8-27b --model-identity REVIEWED-INVENTORY-SHA256 --thinking enabled --max-tokens 8192 --output /tmp/reasoning-evaluation
```

`--count` means items **per stratum** (1–100), not total. Default 2 selects 18 tasks and generates 36 across both splits. Explicit count 10 evaluates 90 tasks. Default output cap is **8192**, preserving the user's output budget. `--thinking enabled` sends `chat_template_kwargs.enable_thinking=true`; this records requested behavior, not proof that the server honored it. A separately labeled pilot may use `--max-tokens 2048` for budget sensitivity. Do not silently lower the evaluation cap or infer a server capacity change from a request cap.

At the earlier short-suite rate, 18 × 8192 outputs alone would take roughly 19 minutes. That excludes prefill, queueing and generation. It is only a budgeting estimate, not a measurement on these tasks. The HTTP inactivity timeout defaults to 600 seconds per network operation; it is not a total wall-clock request deadline. A slowly progressing response can take longer. Both non-loopback HTTP and redirects are rejected to protect the key. Input files, key bytes and HTTP response bodies have explicit size bounds.

## Replay, failure evidence and scoring

`--replay-from /tmp/reasoning-pilot-bank` loads an already frozen bank into a **new** exclusive output directory. Supply exactly the original mode, count, endpoint, model identity, thinking, token cap and timeout. It permits the deliberate change from generate-only to inference; all measurement settings, generation deadline, plan, lock, transport and runner must still match. It verifies seed commitments, item seed derivation, regenerated accepted entries, prompt hashes and full-credit oracle integrity before network access. Rejection counters are preserved from the source-bound frozen manifest; replay does not regenerate the rejected candidate stream. Supply `--model-identity` when generating a bank intended for later inference. A CPU-only bank with null identity cannot be replayed live. An evaluation bank must have committed `--pilot-run` provenance before it can be replayed live, and replay must supply that same validated pilot directory. Keep the original bank and invocation. Exact replay is not permission to pool repeated observations as independent fresh tasks.

```console
nix develop path:. --no-write-lock-file -c uv run --locked --python python3.13 --no-managed-python bench/reasoning.py --replay-from /tmp/reasoning-pilot-bank --count 2 --model-identity REVIEWED-INVENTORY-SHA256 --key-file /mnt/ssd/storage/ai/qwen3.8-27b/api-key --output /tmp/reasoning-pilot-replay
```

There is **no in-place resume**. Each result and checkpoint is an exclusive, fsynced file. A fatal failure writes a private traceback after output ownership has been established. Existing directories are never overwritten. An interrupted run's checkpoints remain inspectable; do not treat a partial checkpoint as a completed evaluation. Replay issues all selected requests again and uses a new directory.

Final content must have exactly one nonempty `<answer>...</answer>` pair. Only that trimmed span is scored. Reasoning content is not mined for answers. Statuses are mutually exclusive: full-credit correct, incorrect (including partial upstream reward), parser failure, truncation, API failure, and scorer failure. `finish_reason=length` is truncation regardless of an apparent answer. Malformed API JSON/schema and response model mismatch are API failures. The pinned Knights/Knaves, Sokoban and REARC scorers internally convert some exceptions to zero; those cannot be separated from incorrect answers by this runner. All completed requests, including failures, remain in the accuracy denominator. A nonzero operational failure count makes the measurement incomplete as quality evidence; there is no automatic passing threshold.

Only `summary.json` and the printed allowlisted summary are publication candidates. They include counts, request settings, identity/commitment digests, feasible/infeasible baselines, available usage count and aggregate request elapsed time. HTTP request elapsed time ends when the bounded response body is received, before JSON parsing, raw artifact writes and CPU scoring. Separate item elapsed time includes those operations, including native-entry regeneration. Neither timer includes initial bank generation or checkpoint writes between requests. Output tokens divided by summed request elapsed time is **end-to-end output throughput**, not decode speed, TTFT, or native benchmark throughput. Missing usage is not assumed zero; throughput is null unless all requests have usage. Validated per-request prompt/completion/reasoning/cache token fields are private result data when supplied by the server. Raw bodies and failure traces can contain sensitive text; never publish them or blindly copy the private directory into the repository.

## Controlled comparisons on an existing bank

`--replay-from` still requires exactly the same measurement settings and runner source. Use the separate `--bank-from` mode when deliberately comparing models or output budgets on the **same** accepted questions. It requires `--producer-root` pointing to the original frozen source tree. The importer verifies the original runner/transport/lock hashes, matching project dependencies and plan, seed commitments and derivation, frozen manifest and source summary binding. It regenerates every accepted native entry and checks its full-credit oracle before making any request.

```console
nix develop path:. --no-write-lock-file -c uv run --locked --python python3.13 --no-managed-python bench/reasoning.py --mode pilot --count 2 --bank-from /tmp/inference-hard-pilot-wx05q47m/run --producer-root /tmp/inference-hard-pilot-wx05q47m/source --model-identity REVIEWED-INVENTORY-SHA256 --key-file /mnt/ssd/storage/ai/qwen3.8-27b/api-key --max-tokens 32768 --output /tmp/reasoning-budget-comparison
```

Only endpoint, model, model identity, thinking, output cap and HTTP timeout may differ, and **each changed request setting requires its explicit CLI flag**. Mode, count, plan, prompt protocol, sampling temperature, concurrency, generation deadline, Python, transport and dependency lock must match. The original producer runner is verified while the new comparison runner is separately committed. Output remains a new exclusive private directory. `bank-import.json`, the new commitment and sanitized summary name the original frozen/commitment hashes, producer inventory and changed setting names. The inventory plan digest uses canonical validated JSON; source/dependency file digests use their original UTF-8 bytes. Original seeds, tasks and results are never overwritten.

A new comparison does not become a fresh evaluation. In particular, increasing the output cap after observing truncation is a **post-hoc budget diagnostic** on the same pilot questions, not held-out quality evidence. A pilot bank cannot be relabeled evaluation. Keep exact source snapshots and report each comparison arm separately. Rejection counters remain original source-bound counters; the importer replays accepted items, not the rejected candidate stream.

## Static synthetic conversation diagnostic

`bench/conversation.py` uses `bench/conversation_fixtures.py` and the same bounded HTTP implementation in `bench/transport.py` as the reasoning runner. It has no native client dependency. Each fresh case has three matched arms: full synthetic observation history, a programmatically verified fixed summary, and direct current observations. Old snapshots arrive last; timestamps, not arrival order, determine truth. Values and evidence IDs are random opaque identifiers. This is a static grounding diagnostic, **not** executed tools, interactive model history, actual client compaction, or evidence about a native agent's error accumulation.

```console
nix develop path:. --no-write-lock-file -c uv run --locked --python python3.13 --no-managed-python bench/conversation.py --generate-only --model-identity REVIEWED-INVENTORY-SHA256 --output /tmp/conversation-bank
nix develop path:. --no-write-lock-file -c uv run --locked --python python3.13 --no-managed-python bench/conversation.py --replay-from /tmp/conversation-bank --model-identity REVIEWED-INVENTORY-SHA256 --key-file /mnt/ssd/storage/ai/qwen3.8-27b/api-key --output /tmp/conversation-run
```

Default `--count 12` generates 12 cases and selects **36 requests**. Each case rotates the three arm positions; twelve cases balance each position four times. The random 256-bit seed, exact fixtures, settings and source/lock digests are committed before requests. Generation checks every expected answer with the fixture scorer and rejects duplicate prompts. Exact replay regenerates and verifies fixtures and all hashes into a new private directory. A bank intended for live replay must receive its immutable `--model-identity` at generation. No in-place resume or passing threshold exists.

Final content is strict JSON, without answer tags or Markdown. Per-arm summaries count full credit (all six values **and** evidence IDs correct), all-values-correct cases, total correct fields and evidence IDs, stale values, unsupported values, parser failures, API failures and truncation. Each completed request contributes six fields to the denominator, including failures. Malformed output is not labeled as six invented facts: its parser-failure count stays separate. Comparisons are paired by case; the three arms are not independent fresh cases. These fixed-summary/control prompts are deliberately simpler controls, not a difficulty-matched reasoning benchmark.

The shared transport and fixture source digests are part of replay identity. Preserve the exact source tree for measured runs before refactoring. Earlier reasoning pilot snapshots remain replayable only with their matching private source/plan/environment tree; a new runner hash must not silently impersonate that runner.

For a failing real request, follow [the quality diagnosis checklist](diagnose-quality.md).
