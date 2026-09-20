# Canonical Docker deployment

The root `Dockerfile`, `docker-compose.yml` and `serve/entrypoint.sh` are the
single serving recipe. Nix consumes this Compose file; it does not reconstruct
SGLang sources or run a second controller.

**This recipe is an unqualified 262,144-token packed Qwen3.8-27B + DFlash2
candidate.** It requires the experimental patched image and defaults to KVarN
KV with full decode verify and commit graphs. Historical measurements and
individual native smoke runs do not qualify the full recipe. There is no
automatic context reduction, representation fallback or model-family selection.
Build and launch are separate approvals.

## Prepare before launch

1. Install a compatible NVIDIA driver, Docker Compose v2 and NVIDIA Container
   Toolkit with CDI `nvidia.com/gpu=0`. Host drivers, GPU availability, power,
   fans and storage remain operator-owned. Do not stop the existing live baseline
   or run another deployment beside it without approval.
2. Set `QWEN_STATE_ROOT` to an existing canonical absolute private directory.
   Supply `models/compact-target-rholsc8k/packed/` and
   `models/Qwen3.8-27B-DFlash2-W4A16/` using [offline preparation](../prepare/REPRODUCE.md).
   Also supply the regular, non-symlink `overrides/draft_vocab_ids.json`;
   Compose mounts it at `/state/draft_vocab_ids.json`. It must contain the exact
   pinned 40,960 ordered target token IDs, not a sorted or regenerated substitute.
   The launcher authenticates their little-endian int64 storage SHA256 as
   `328af76c651b989efb40e31e6b1bfdb1b4a0928e1124359f8fb04654b1e44584`.
   Create private `cache/` and a mode-0600 `api-key` file owned by the operator.
   The key must be 1..4096 bytes, printable ASCII without whitespace, with at
   most one trailing newline. Nothing downloads or converts models at startup.
3. Create `qwen-inference-launch.lock` in that state directory only if absent,
   using exclusive creation (`O_CREAT | O_EXCL` or shell noclobber), mode 0600.
   Preserve the inode: never replace or unlink it while a deployment can exist.
4. For rootless Docker, default `QWEN_CONTAINER_USER=0:0` maps to the operator.
   For rootful Docker, set the state owner's numeric `UID:GID`. Never loosen
   private state permissions to work around ownership errors.

```sh
export QWEN_STATE_ROOT=/absolute/private/qwen-state
# Rootful only, when the current user owns state:
# export QWEN_CONTAINER_USER="$(id -u):$(id -g)"
docker compose --project-name qwen-inference config --quiet
# CPU/image build only; no GPU is attached:
docker compose --project-name qwen-inference build
# Starts the GPU: only after explicit exclusive-access approval.
export QWEN_ALLOW_UNQUALIFIED=1
docker compose --project-name qwen-inference up -d --wait --wait-timeout 1200
```

Default startup refuses to serve without `QWEN_ALLOW_UNQUALIFIED=1`. This explicit
opt-in permits unqualified diagnostic operation; it is not qualification or
promotion and does not bypass artifact, native-allocation or graph guards.
The API is `http://127.0.0.1:18020/v1`, model
`qwen3.8-27b`, authenticated with the private key as a Bearer token. Optional
`QWEN_PORT` changes only the host loopback mapping, not the in-container API.
Do not print raw server configuration or credentials.

## Source and artifact trust

The stock SGLang image is digest-pinned. Build applies a pinned, ordered Git
patch series; see [patch provenance](../patches/NOTES.md). The Dockerfile defaults
to `QWEN_PATCH_SERIES=experimental`, including the packed embedding, KVarN and
sampler patches required by the fixed runtime. Ordinary Compose builds use that
default. The build context is allowlisted. Model weights, keys and cache never
enter the image.
Full local model inventories are verified on every start. Source provenance is
established at build time, not by copying upstream originals into a second
runtime overlay. Deploy a reviewed immutable image digest with `QWEN_IMAGE`;
local development uses `qwen-inference:local`. Rebuilding or retagging an image
is not runtime qualification. Never use writable source mounts or entrypoint
overrides to bypass guards.

## Lifecycle and health

The container holds the shared state lock across `exec` into SGLang. A losing
container cannot stop a winning deployment. This lock excludes only deployments
that share its inode, not other states, accounts, Docker daemons or GPU programs.
Operators must reserve the GPU. Compose uses Docker's init, a 60-second stop
budget, and `restart: unless-stopped`. Docker reruns model and lock guards after
process exit. There is no custom supervisor, GPU-memory polling, source overlay
reconstruction or automatic cleanup of another Compose project.

The healthcheck requires `/health` and the authenticated expected `/v1/models`
entry. It runs every 30 seconds with a 310-second whole-probe budget and a
315-second Docker timeout. Startup has a 20-minute grace period; three failures
mark the container unhealthy. `/health` can generate a token when idle.
**Docker does not restart a merely unhealthy container.** Inspect failure logs
and explicitly recover with approved GPU ownership. A timed-out `up --wait` can
leave a running container; inspect it rather than assume cleanup succeeded.
These lifecycle settings have no new GPU qualification evidence.

Inspect `docker compose --project-name qwen-inference ps` and
`docker compose --project-name qwen-inference logs --tail 100 inference`.
Stop with `docker compose --project-name qwen-inference stop`. A manual stop
stays stopped. Retain the old deployment's image, artifacts and original
configuration for rollback; these repository edits do not touch it.

## Qualification control

The serving launcher fixes target `/models/compact-target-rholsc8k/packed`,
draft `/models/Qwen3.8-27B-DFlash2-W4A16` and alias `qwen3.8-27b`.
`QWEN_QUALIFICATION=speculative` is the only admitted speculation setting;
`target-only` is source-blocked because the packed loader requires DFlash.
It is not an available matched A/B arm.

`QWEN_QUALIFICATION_CONTEXT=262144` is the only admitted context. The Bend-backed
planner supplies the 263,168-token pool and page-128 geometry. Historical capacity
ladder rungs remain measurement records, not current launcher options. Actual
allocation and graph admission must still pass; metadata or planner success is
not GPU capacity proof.

`QWEN_QUALIFICATION_KV=kvarn` is the default. `fp8` and `bf16` remain internal
controls using the same packed target, draft and experimental image. Both require
`QWEN_COMMIT_GRAPH=0`; neither is a qualified fallback and either may exceed
24 GB at the fixed native context. No FP4 deployment selector is exposed.

`QWEN_QUALIFICATION_EXECUTION=default` selects full C1 decode verify graphs for
KVarN, with prefill graphs disabled. `QWEN_COMMIT_GRAPH=1` is the default and
requires KVarN plus default execution. `QWEN_QUALIFICATION_EXECUTION=eager`
disables decode graphs and requires `QWEN_COMMIT_GRAPH=0`. KVarN is serialized
and FlashInfer-autotune-free in both execution modes; eager also disables
overlap and autotuning for FP8/BF16. These are diagnostic controls, not claims of
native/full-profile qualification.

### Explicit experimental KVarN runtime

The ordinary Compose build already selects the experimental series. An explicit
tagged build of the same series can be used for an approved eager diagnostic.
Use the same image and packed artifacts for FP8/BF16 controls to isolate KV
rather than changing source or model representation together.

```sh
# CPU build only:
docker build --build-arg QWEN_PATCH_SERIES=experimental \
  --tag qwen-inference:experimental .
# GPU launch requires separate exclusive-access approval:
export QWEN_IMAGE=qwen-inference:experimental
export QWEN_ALLOW_UNQUALIFIED=1
export QWEN_QUALIFICATION=speculative
export QWEN_QUALIFICATION_CONTEXT=262144
export QWEN_QUALIFICATION_EXECUTION=eager
export QWEN_COMMIT_GRAPH=0
export QWEN_QUALIFICATION_KV=kvarn
docker compose --project-name qwen-inference up --no-build --pull never -d
```

The launch guard rejects any image whose build-series marker is not
`experimental`. KVarN uses the fixed packed target and unchanged W4A16 draft;
the patched loader reconstructs BF16 embedding values from packed W8 storage.
The native request stays at context 262,144 with pool 263,168 and page size 128.
Actual allocated pool capacity must equal the request; no silent reduction is
accepted. Do not weaken native allocation or graph guards to manufacture success.

Building this image is not evidence of model startup, usable capacity, numerical
parity, sustained cache/concurrency correctness or quality. See
[qualification requirements](qualification.md) before promoting any candidate.

### Zero-patch upstream build control

```sh
# CPU source/build control only; the canonical serving launcher rejects this image:
docker build --build-arg QWEN_PATCH_SERIES=upstream \
  --tag qwen-inference:upstream-control .
```

This verifies the exact clean upstream checkout and applies no patches. It is a
build/source control only: the fixed packed serving launcher rejects `upstream`
and `baseline` image markers. Do not select either as a canonical deployment or
bypass the guard to obtain a runtime comparison. Source or artifact incompatibility
is a valid failed control, not grounds for silently changing patches or weights.
Ordinary Dockerfile/Compose builds use `experimental`; build-series selection is
not a serving-quality certification.

### Fixed packed representation

The only served representation is `models/compact-target-rholsc8k/packed/`.
Nothing converts or copies models at startup, and there is no dense runtime
fallback. Nonempty `QWEN_MODEL_FAMILY`, `QWEN_MODEL_REPRESENTATION`,
`QWEN_SPEC_ALGORITHM` and `QWEN_DSPARK_DRAFT` are retired selectors and are
rejected, including their former defaults.

The packed guard checks the fixed 17-file source inventory against the
authenticated proof's source hashes, packed W8 group-2 configuration and exact
tensor layout. Offline preparation still supports derived dense inventory
verification and dense numerical references/oracles. Those tools and historical
dense results are legitimate evidence about the same model bytes, not an
alternate serving recipe. See [offline preparation](../prepare/REPRODUCE.md).

The launcher enables `SGLANG_EXPERIMENTAL_PACKED_W8_EMBEDDING=1` and uses
`--load-format safetensors --dtype bfloat16`, as required by the patched loader.
Any nonempty inherited packed-loader flag other than `1` is rejected.
Multimodal loading remains enabled; no language-only, LoRA, compilation or
parallel-mode escape is added. Hold these artifacts fixed when comparing KV or
execution controls. Byte reproduction or an individual loader/smoke success
does not establish full-profile quality, numerical parity or promotion.

### Bounded static-memory control

`QWEN_MEM_FRACTION_STATIC` accepts only `0.94`, `0.95`, `0.96`, `0.97`
or `0.98` (default). It changes only SGLang's existing static-memory fraction
argument. All choices remain behind the unqualified acknowledgment. The default
is a historical native-capacity candidate, not a promoted memory setting or
proof that a model fits. Keep the value fixed for matched comparisons and record
requested versus allocated
capacity; strict capacity rejection remains enabled. No automatic retries with
larger fractions or smaller contexts occur.
