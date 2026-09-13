# Recorded benchmark runs

These are sanitized reports from actual runs, not newly executed benchmarks.
Private task banks, answers and raw model responses are deliberately not published.
The reports retain producer hashes and measurement limits; current code changes do not rewrite historical identities.

| Run | Report | Interpretation |
|---|---|---|
| Hard held-out reasoning, 180 tasks, 8,192 output tokens | [reasoning-evaluation.json](reasoning-evaluation.json) | **78 correct, 96 truncated, 6 completed incorrect**; 43.3% correct |
| Reasoning discovery pilot, 18 tasks | [reasoning-pilot.json](reasoning-pilot.json) | 9/18 correct; not held out |
| Same pilot bank, larger 32K output budget | [reasoning-budget32k.json](reasoning-budget32k.json) | 13/18 correct; post-hoc comparison, not held out or final profile |
| Conversation/cache diagnostic | [conversation-pilot.json](conversation-pilot.json) | Scoped diagnostic, not causal proof of the reported conversation failure |
| Baseline native throughput and compatibility | [native.json](native.json) | **130.99–132.78 tokens/s end-to-end; 135.90–137.69 tokens/s decode**. Short-suite 64K baseline, not candidate qualification |
| Cache consistency | [cache-45k.json](cache-45k.json), [cache-45900.json](cache-45900.json) | Workload-specific cache evidence |
| Baseline vision compatibility | [multimodal-baseline.json](multimodal-baseline.json) | Baseline only |
| 240K candidate: first native attempt | [240k-native-attempt-01.json](240k-native-attempt-01.json) | Packed rows passed; KVarN CUDA illegal memory access before model startup; baseline restored in 95.0 s |
| Packed-embedding trial | [packed64-trial.json](packed64-trial.json) | GPU row arithmetic passed; candidate startup failed; baseline restored |

**No completed 245,760-token candidate inference benchmark is claimed.** Candidate source/CPU checks are separate from model quality, capacity and GPU sampling qualification.

See [benchmark commands and methodology](../../docs/benchmarks.md), [qualification limits](../../docs/qualification.md), and the [uploaded patch chain](../../patches/README.md).
