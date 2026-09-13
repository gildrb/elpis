# Complete source packaging, without activation

The current Docker/Nix service still uses the three baseline patches in
`patches/manifest.json`. The separate `patches/qualification/` bundle contains
all remaining staged runtime changes. It is **source-only and unqualified**.
There is no runtime profile selector, default candidate launch, or fallback.
The intended later single serving target remains 245,760 total tokens.

## Coverage

| Stage | Paths in stage | Additional paths | Cumulative union |
|---|---:|---:|---:|
| Reviewed baseline | 3 | 3 | 3 |
| Packed embedding and multimodal fix | 3 | 3 | 6 |
| KVarN | 25 | 24 | 30 |
| Sampler semantic + residual/status checkpoint2 | 9 | 8 | 38 |

`speculative/dflash_worker_v2.py` (under `srt/`) is the overlap across baseline,
KVarN and sampler stages. Thus 3 + 3 + 25 + 9 - 2 = **38**, not 40. The union
contains **21 modified existing files and 17 new files**. Sampler checkpoint2
already combines its semantic and residual/status changes. Its two component
patches must not be applied again.

The bundle reuses the three baseline patches and original files without changes.
It adds exactly five patch files and eighteen previously missing original files.
The seventeen additions are represented by null original hashes and required
absence, not placeholder source files. `manifest.json` records all intermediate
and final hashes, patch hashes and paths. `manifest.sha256` records its identity.
Hashes cover kernel sources outside `srt/` as well as Python runtime sources.

The baseline's `dflash_worker_v2.py` stays at its baseline hash in serving.
Its candidate replacement includes two later changes. Only the head and FC files
have the same final bytes in both source bundles.

## One strict chain implementation

`patches/chain.py` is the standard-library-only implementation used by both
qualification delivery paths. Its `audit` mode reads authenticated inputs and
reconstructs all stages in memory. It imports no SGLang code and writes no source.
The parser accepts the exact unified-diff format used by this bundle; it does not
perform fuzzy matching, rebase patches, accept renames/deletions, or execute a
patch-provided command. Context, line positions/counts, declared paths and both
sides of every transition must match. Every declared path must reach its final
inventory hash. Duplicate JSON fields, stage names, patches and file paths fail.

All operations require the expected manifest SHA256 and digest-pinned base-image
identity. Original files must match; new files must be absent. Source and bundle
paths must be canonical and disjoint. Directory-relative file operations reject
symlink components and non-regular source files. Overlay writes use exclusively
created temporary files and verify the authenticated final bytes before and after publication. All staged
transformations happen in memory; the tool never modifies existing source files.
File reads are bounded to 2 MiB, including a second bound for files that grow while being read. New-file publication uses an atomic no-replace
link, so a competing creation fails rather than being overwritten.

Overlay mode requires the explicit `--exclusive-build-tree` acknowledgement
and an **exclusively owned disposable build tree**, with no concurrent writers.
Its destination must not exist: the tool creates that directory exclusively and
refuses any existing destination. Never use a live service, shared checkout,
model directory or frozen evidence. There is no in-place application mode.
A failed operation leaves an incomplete owned output tree, never an acceptable
runtime; discard that build attempt rather than resume permissively.

Modes `original` and `final` read-only check a specified source tree.
`overlay` exclusively creates a new destination and writes the reconstructed
final files. Both delivery paths use the same plan and transformations.
The CLI's image argument checks the declared identity; it cannot attest the daemon's image by
itself. The Docker FROM digest and original-source guards supply that boundary.
The Nix source overlay alone is not proof about an installed container image.

A read-only source audit, using the already prepared pinned development environment:

```console
uv run --locked --offline python patches/chain.py --bundle "$(pwd)/patches" --manifest-sha256 MANIFEST_SHA256 --image lmsysorg/sglang@sha256:d6e7288627be8b02be88e4bba38e73f6d50e2826869f753c13a4c4385ab3eda9 --mode audit
```

Replace `MANIFEST_SHA256` with the full digest in
`patches/qualification/manifest.sha256`. Repository revision review is the trust
boundary for changes to that digest, the verifier, or the build instructions.
No model files, driver, GPU, runtime imports, or network are needed for this audit.
Do not format the vendored originals to satisfy development lint rules. See
[development policy](development.md) for the explicit upstream-code distinction.

## Build-only delivery inputs

`docker/qualification.Dockerfile` starts from the exact stock image and checks
all actual originals and required absences. It reconstructs all eight ordered
patches (baseline3, packed3, KVarN1, sampler1) into a newly owned source overlay.
A separate explicit copy installs that overlay only in the disposable Docker
build layer, followed by verification of every installed final file. Its Dockerfile-
specific `.dockerignore` allows only the source bundle and its build recipe; it
is needed because the default serving build deliberately excludes these files.
The build has no model mount or GPU command. Its default entrypoint only verifies
all 38 final source hashes and exits. It does not launch SGLang. Neither default
`Dockerfile` nor `docker-compose.yml` selects this recipe.

`nix/qualification.nix` is a build-only derivation with `pkgs` as its sole input.
It produces `source/` with all 38 authenticated final files and `provenance/`
with the manifest, evidence identity and license. It does not fetch or build
SGLang, CUDA, kernels or model weights. It is not imported by the NixOS service
or foreground serving app. The flake may expose it as a build-only artifact;
that exposure does not mount it into a service or qualify an image.

Building either artifact requires separate approval. No build was run during
this packaging change. A successful future build establishes source packaging,
not correct GPU execution or deployment qualification.

## Provenance and license

`patches/qualification/source-evidence.json` contains sanitized source identities
and qualification limits. It carries no private filesystem paths, weights,
credentials, private prompts, answers or raw responses. The prior CPU evidence
is identified by its hashes; those records are not build dependencies and their
hashes alone are not public execution proof. Original sources retain their
notices. SGLang's Apache-2.0 license is included beside the qualification bundle.
The patch files preserve the exact reviewed private-stage bytes.

The sampler checkpoint has CPU interpreter evidence, not CUDA compiler/native
GPU parity. It has not been image-built or GPU-qualified. Its selected active-
penalty memory bound is source-derived, not a measured allocator/stream peak.
Frozen pre-sampler image evidence does not inherit the sampler repair's behavior.
Packed embedding arithmetic does not establish candidate startup or multimodal
parity. Source provenance cannot establish 245,760-token capacity or quality.

## Promotion remains separate

1. Independently review the complete source bundle and integration before an
   approved image build/rebinding. Preserve the original baseline and its guards.
2. Bind that image to reviewed launch settings, preparation/model inventories,
   qualification producers and gates. Private absolute paths must not become
   runtime/build dependencies. This bundle deliberately does not ship or enable
   the private candidate launcher, model preparation bindings or recovery owner.
3. Separately authorize native sampler/status propagation, scheduler/cache
   chronology, memory/capacity, quality and target/draft graph qualification.
4. Only after those gates pass, replace the single serving configuration through
   a separately approved lifecycle transaction. Preserve strict actual-image
   original checks and all38 replacement guards on every future restart.

`serve/`, `prepare/` and `bench/` changes are first-party lifecycle, artifact and
measurement integration, not extra SGLang runtime patch paths. Their checks and
qualification evidence do not substitute for the full upstream source bundle.

## File inventory

Paths are relative to `python/sglang`. `new` means the pinned original must be
absent. Full original, intermediate and final hashes are in the manifest.

| Path | Stage(s) | Original |
|---|---|---|
| `kernels/ops/kvarn/__init__.py` | KVarN | new |
| `kernels/ops/kvarn/decode.py` | KVarN | new |
| `kernels/ops/kvarn/gather.py` | KVarN | new |
| `kernels/ops/kvarn/sinkhorn.py` | KVarN | new |
| `kernels/ops/kvarn/store.py` | KVarN | new |
| `kernels/ops/speculative/dspark/dspark_accept.py` | sampler | existing |
| `kernels/ops/speculative/reject_sampling.py` | sampler | existing |
| `srt/arg_groups/kvarn_hook.py` | KVarN | new |
| `srt/arg_groups/pipeline.py` | KVarN | existing |
| `srt/arg_groups/speculative_hook.py` | KVarN | existing |
| `srt/layers/attention/attention_registry.py` | KVarN | existing |
| `srt/layers/attention/kvarn_backend.py` | KVarN | new |
| `srt/layers/attention/kvarn_draft_backend.py` | KVarN | new |
| `srt/layers/logits_processor.py` | baseline | existing |
| `srt/layers/packed_w8_embedding.py` | packed | new |
| `srt/managers/mm_utils.py` | packed | existing |
| `srt/mem_cache/allocation.py` | KVarN | existing |
| `srt/mem_cache/kv_cache_configurator.py` | KVarN | existing |
| `srt/mem_cache/kv_cache_dtype.py` | KVarN | existing |
| `srt/mem_cache/kvarn/__init__.py` | KVarN | new |
| `srt/mem_cache/kvarn/kernels.py` | KVarN | new |
| `srt/mem_cache/kvarn/layout.py` | KVarN | new |
| `srt/mem_cache/kvarn/pool.py` | KVarN | new |
| `srt/mem_cache/kvarn/types.py` | KVarN | new |
| `srt/mem_cache/kvarn_allocator.py` | KVarN | new |
| `srt/mem_cache/kvarn_budget.py` | KVarN | new |
| `srt/model_executor/model_runner_components/spec_aux_hidden_state.py` | KVarN | existing |
| `srt/model_executor/pool_configurator.py` | KVarN | existing |
| `srt/models/dflash.py` | baseline | existing |
| `srt/models/qwen3_5.py` | packed | existing |
| `srt/sampling/sampling_batch_info.py` | sampler | existing |
| `srt/sampling/verify_penalties.py` | sampler | new |
| `srt/server_args.py` | KVarN | existing |
| `srt/speculative/dflash_utils.py` | sampler | existing |
| `srt/speculative/dflash_worker_v2.py` | baseline → KVarN → sampler | existing |
| `srt/speculative/dspark_components/dspark_planner.py` | sampler | existing |
| `srt/speculative/dspark_components/dspark_verify.py` | sampler | existing |
| `srt/speculative/dspark_components/dspark_worker_v2.py` | sampler | existing |
