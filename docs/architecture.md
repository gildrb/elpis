# Architecture and runtime contracts

This repository is a reproducible deployment recipe, not another inference engine.
SGLang owns model execution, sampling, scheduling and cache allocation. Local
patches modify explicit, hash-bound portions of that engine. Docker and Nix must
serve the same single qualified configuration.

## Ownership

| Boundary | Owner | Required contract |
|---|---|---|
| Model acquisition | User | Install separately; no startup download or substitute model |
| Artifact preparation | `prepare/` | Offline, exclusive outputs, exact inventories and numerical proof |
| Runtime changes | `patches/` | Authenticate original bytes, patch bytes and resulting source bytes |
| Launch and recovery | `serve/`, Docker/Nix adapters | One GPU/process owner, authenticated readiness, bounded cleanup; repeat guards on restart |
| Host resources | Host configuration | NVIDIA driver/CDI, storage mounts, account, power and fan policy |
| Sampling and cache | Pinned SGLang plus reviewed patches | Only committed tokens/state become reusable; no silent fallback |
| Qualification | `bench/`, frozen plans and result records | Bind actual execution to immutable inputs; distinguish each kind of evidence |

The existing Nix consumer import remains `nix/qwen-inference.nix`. Host-specific
clients and monitoring do not belong in the portable serving recipe.

## One final profile

The target is 245,760 total tokens with DFlash2 on one RTX 3090. The temporary
64K baseline is a comparison and rollback target, not a shipped alternative.
Native and CUDA-graph stages are qualification procedures, not user-selectable
profiles. The target cannot be described as live-qualified until its capacity,
cache, numerical, quality and lifecycle checks pass.

## Evidence is not interchangeable

Source hashes and CPU imports establish provenance, not GPU correctness. Kernel
arithmetic checks do not prove full-model quality, allocator ownership or graph
behavior. Startup context metadata does not prove actual long-request capacity.
A healthy API does not prove reasoning quality. A quality canary is not statistical
non-inferiority. Keep requested settings separate from observed settings and
report any unavailable telemetry as unavailable, never zero.

For measured tuning, compare matched prompts, effective token IDs/templates,
sampling, budgets and cache conditions. Record draft/verify time, accepted tokens
by depth, memory high-water and client/server timing only when actually observed.
Use repeated interleaved comparisons where exclusive access is approved. Retain a
no-improvement verdict when spread exceeds the measured gain. Never retrofit an
acceptance threshold to a candidate's answers.

## Speculation and cache qualification

The following are required invariants, not claims that every case has passed:

- Proposal and target probabilities must use their actual sampling transforms.
  Greedy agreement alone does not establish sampled-distribution correctness.
- Every rejection position must select both the committed recurrent state and
  convolution state. Trimming attention KV length alone is insufficient.
- Prefix reuse must use a real state checkpoint at or before the requested
  boundary, never state produced from a future or rejected suffix.
- Reuse compatibility includes model/draft bytes, template/history and numerical
  cache policy. Cancellation, retry and divergent continuations need their own
  ownership checks.
- Numerical checks on the same packed representation do not establish equivalence
  to unquantized or FP8 KV. Report cache self-consistency and model-quality changes
  separately, including failures and inconclusive outcomes.

## References

The deployment layout follows ideas from [syv-ai/qwen38-27b-rtx3090](https://github.com/syv-ai/qwen38-27b-rtx3090).
The ownership, measurement and speculation checklist was also informed by
[MTPLX](https://github.com/youssofal/MTPLX/tree/21be78b3f51820eecef020e5e4855c0715eaf9a5).
These are independently expressed architecture ideas, not imported runtime code.
Neither project's performance or correctness claims qualify this CUDA stack.
