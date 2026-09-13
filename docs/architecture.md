# Architecture

## Fixed target

Qwen3.8-27B + SGLang + DFlash2 on one NVIDIA RTX 3090 (SM86, 24 GiB,
TP=1). Optimize for one active agent: C1 latency, long-lived prefix reuse,
code/reasoning work and reliably usable context toward **262144 total tokens**.
C2/C4 are secondary measurements, not the design center. A smaller passing
context is a measured operating point, never a new model limit.

## Ownership

| Boundary | Owner |
|---|---|
| Execution, scheduling, sampling, OpenAI API | Exact pinned public upstream SGLang |
| Local changes | Ordered Git patches with SHA256, classification and evidence |
| Weights | Pinned public sources plus documented deterministic preparation |
| Runtime | Docker Compose; Nix supplies development tools and a thin adapter |
| GPU driver, storage, fan and optional power cap | Host |
| Capability tasks, scoring, rewards and traces | Pinned Prime Envs + Verifiers in `eval/` |
| Performance and cache diagnostics | Official SGLang utilities and focused `bench/` tools |
| Implementation correctness | Kernel/runtime checks, distinct from capability scores |

No private fork, vendored upstream source tree, runtime source overlays or
source reconstruction protocol. The upstream commit and ordered patch hashes
define the engine changes. The runtime image digest defines its dependency
closure. Model inventories define its actual weights. Record all three in a run.

## Patch lifecycle

Classify each patch as compatibility, correctness, memory, performance or
experimental. Document its base, subsystem, purpose, measured benefit,
correctness risk, validation and upstream issue/PR when known. An unavailable
measurement is **unmeasured**, not a zero-cost improvement.

Default patches need evidence. Experimental patches require explicit selection
and do not become defaults through build context inclusion. KVarN remains a
candidate: compare it against BF16/FP8 KV and applicable upstream compression.
Do not discard it because it is local, or promote it because reference numbers
look favorable. Once upstream contains equivalent functionality, remove the
local patch, advance the pin and repeat qualification.

## Qualification invariants

1. Compare target-only and DFlash2 with identical weights, prompts, templates,
   sampling and budgets. Proposal/target probability transforms, rejection
   positions, grammar masks, penalties and returned logprobs must be correct.
2. Commit only accepted tokens and their recurrent/convolution state. Prefix
   checkpoints must precede or equal the reused boundary, never include a
   rejected/future suffix. Exercise cancellation, divergence and restoration.
3. Prove capacity with actual deep prompts, completed prefill and meaningful
   generation, VRAM high-water, finite numerics and upstream capability evals.
   Server metadata and kernel tests alone are insufficient.
4. Freeze each A/B workload and quality decision rule before observing results.
   For KVarN on/off, use the same experimental image so active sampler repairs
   cannot be mistaken for a KV effect. Keep per-environment scores, errors and
   truncation rates; no combined
   intelligence score. Report uncertainty and failed experiments.
5. Bind results to recipe, model, patch, image and evaluator identities. Compare
   matched metrics and cache conditions. Never multiply gains from unlike
   fixtures or transfer another engine's results to this one.

See [qualification](qualification.md), [benchmarks](benchmarks.md),
[patch policy](patches.md), and the [reference audit](reference-audit.md).
