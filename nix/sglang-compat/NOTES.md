# Reviewed opt-in runtime sources

Keep exact bytes and original license/source notices. Do not run a broad formatter over the retained reference modules.

`manifest.json` pins the stock SGLang image, immutable fork revision and NAR hash, and original/replacement hashes for three modules: compressed-head selection, quant-aware draft fc loading, and the DFlash Mamba checkpoint boundary. Nix selects only those three files from the pinned fork. It does not build CUDA, replace the runtime package, or apply the retained patch diffs. The `reviewed_opt_in_runtime` status describes reviewed source wiring, not an activated deployment or universal quality parity.

The existing service runs `prepare` first in the exact pinned image, with no replacement mounts. Its verifier checks original image source before model preparation. The inference container mounts the three replacements read-only and checks their hashes before launch. A replacement mount hides the original, so checking replacements alone does not establish applicability. Preserve this two-phase service ordering; direct `docker compose up inference` bypasses the original-source phase.

The head and fc replacements are reviewed for one full initial DefaultModelLoader load only. Do not use hot reload or partial weight loading. The head helper assumes successful Marlin processing; metadata does not prove numerical layout. The fc check requires checkpoint parameters before derived Marlin buffers are created. The Mamba correction uses committed post-verify sequence lengths for checkpoint tracking; its measured generated-prefix consistency does not establish parity for every workload.

Do not relax hashes, apply fuzz, alias packed weights to dense `.weight`, or accept arbitrary quantization methods. An image/source change requires a reviewed rebase. Preserve the three patch diffs and manifest with qualification evidence.

## Compact profile and rollback

`workstation.qwenInference.profile = "compact-dflash"` requires `reviewedSource.enable = true`. It selects the retained compact target and original W4 draft, not a fresh download. Both preparation and inference verify all model file hashes against the retained provenance; missing or mismatched artifacts fail closed. See `../../prepare/REPRODUCE.md` for explicit, separate reproduction without overwriting originals.

The entrypoint sets context length 24576 and native input-logprob chunking enabled with chunk size 256. Compact serving uses one running request, DFlash block 8, draft window 2048, and FlashInfer target/draft attention. These bounds do not guarantee that every possible request is free of OOM. Final memory, cache, admission, and service checks remain distinct from source review.

The default profile remains `"awq"`, with the source overlay disabled. For rollback, select that profile and disable `reviewedSource.enable`, or restore the previous guarded Nix generation and service configuration. The current AWQ branch also retains context 24576 and logprob chunk 256. Preserve both model sets; do not silently fall back after a compact verification failure. No service activation is performed by these assets.
