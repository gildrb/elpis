# Canonical Docker deployment

The root `Dockerfile`, `docker-compose.yml` and `serve/entrypoint.sh` are the
single serving recipe. Nix consumes this Compose file; it does not reconstruct
SGLang sources or run a second controller.

**This recipe is an unqualified 262,144-token DFlash2 candidate.** The historical
64K measurements do not qualify it. FP8 KV is the ordinary source-series control;
it may not fit one 24 GB RTX 3090. No context reduction or experimental cache
patch is selected automatically. Build and launch are separate approvals.

## Prepare before launch

1. Install a compatible NVIDIA driver, Docker Compose v2 and NVIDIA Container
   Toolkit with CDI `nvidia.com/gpu=0`. Host drivers, GPU availability, power,
   fans and storage remain operator-owned. Do not stop the existing live baseline
   or run another deployment beside it without approval.
2. Set `QWEN_STATE_ROOT` to an existing canonical absolute private directory.
   Supply `models/compact-target-rholsc8k/artifact/` and
   `models/Qwen3.8-27B-DFlash2-W4A16/` using [offline preparation](../prepare/REPRODUCE.md).
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

Default startup refuses to serve without `QWEN_ALLOW_UNQUALIFIED=1`. This is an
acknowledgment, not qualification. The API is `http://127.0.0.1:18020/v1`, model
`qwen3.8-27b`, authenticated with the private key as a Bearer token. Optional
`QWEN_PORT` changes only the host loopback mapping, not the in-container API.
Do not print raw server configuration or credentials.

## Source and artifact trust

The stock SGLang image is digest-pinned. Build applies a pinned, ordered Git
patch series; see [patch provenance](../patches/NOTES.md). Ordinary builds do
not select experimental KVarN, packed embedding or sampler patches. The build
context is allowlisted. Model weights, keys and cache never enter the image.
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

`QWEN_QUALIFICATION=target-only` removes only DFlash speculation. It retains the
same context rung, pool (context plus 1,024), selected target KV, model, prefill, concurrency,
parsers and memory settings as `speculative` (the default). Both require the
unqualified acknowledgment. This is an internal matched control, not another
supported product profile. Both may fail capacity. No quality or performance
claim follows from accepted flags or advertised context metadata.

`QWEN_QUALIFICATION_CONTEXT` accepts only `131072`, `163840`, `196608`,
`229376`, `245760` or `262144` (default). This is the internal capacity ladder,
not a profile selector. Pair each rung with both speculation arms and the same
prompt, output budget, sampling and cache condition. The deployment objective
remains 262,144; a smaller successful rung does not qualify the objective.

`QWEN_QUALIFICATION_KV=bf16` selects the upstream BF16 KV control instead of
`fp8` (default). FlashInfer and the exact model artifacts remain unchanged;
both speculation arms share the selected target KV dtype. This may exceed
24 GB even at the first rung. No success or performance advantage is implied.
Upstream FP4 enum presence alone does not establish SM86/backend support, so no
FP4 deployment selector is exposed.

`QWEN_QUALIFICATION_EXECUTION=eager` disables decode CUDA graphs, overlap
scheduling and FlashInfer autotuning. Prefill graphs are already disabled.
Use the same execution setting on FP8/BF16 controls when comparing KVarN.
`default` retains the ordinary decode-graph settings; it is not a native run.

### Explicit experimental KVarN runtime

One Dockerfile builds both series. There is no separate source-only runtime.
The build argument below is explicit and never selected by ordinary Compose
builds. It includes all experimental patches; use this same image for FP8
controls to isolate KV rather than changing source and KV together.

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
export QWEN_QUALIFICATION_KV=kvarn
docker compose --project-name qwen-inference up --no-build --pull never -d
```

The launch guard checks the image's build-series marker. KVarN uses the same
verified BF16-embedding target and W4A16 draft artifacts; it does not silently
select packed embeddings. Native KVarN requires page 128, the exact selected context plus 1,024 pool,
serialized scheduling and disabled graphs. The separate eleventh experimental
patch admits all six native DFlash rungs with derived page-count guards. Its
132 CPU admission/budget checks are not GPU capacity or kernel-resource proof.
Actual allocated pool capacity must equal the request; no silent reduction is
accepted. **Target-only KVarN remains source-blocked**, because its ordinary
worker lacks required sticky-error checks before publishing tokens. It is not
a matched A/B arm. Graph qualification remains outside this recipe; the source
still limits that path to 245,760. Do not weaken guards to manufacture success.

No model startup, capacity, numerical, cache or quality result is claimed by
this experimental build. See [qualification requirements](qualification.md)
before measuring or promoting any candidate.

### Zero-patch upstream control

```sh
# CPU build only, same guarded runtime and model inventory checks:
docker build --build-arg QWEN_PATCH_SERIES=upstream \
  --tag qwen-inference:upstream-control .
```

This verifies the exact clean upstream checkout and applies no patches. Select
its reviewed immutable image with `QWEN_IMAGE` only for approved qualification.
It retains the same launch and local artifacts. Source or artifact incompatibility
is a valid failed control, not grounds for silently adding patches or changing
weights. Ordinary builds remain `baseline` (the three compatibility patches).
`experimental` adds the seven preserved experimental stages plus the separate
native-capacity stage. Build series are not serving-quality certifications.

### Explicit packed-embedding representation

`QWEN_MODEL_REPRESENTATION=dense` is the default. The optional `packed` value
requires an explicitly built experimental image and the separately supplied
`models/compact-target-rholsc8k/packed/` directory. It never converts or copies
models at startup. The draft path does not change. There is no automatic fallback
between directories or representations.

The packed guard checks the fixed 17-file source inventory against the authenticated
proof's source hashes, packed W8 group-2 configuration and exact tensor layout.
The dense guard continues to check the derived dense inventory. The full CPU
reproduction of their conversion is evidence about those artifact bytes, not
packed model startup, GPU memory savings, numerical inference parity or quality.
See [offline preparation](../prepare/REPRODUCE.md) for obtaining and verifying the
public inputs before explicitly installing either representation.

Hold representation fixed when comparing KV or speculation. A packed KVarN trial
changes two variables relative to a dense FP8 trial; it is not an isolated KV A/B.
The same unqualified acknowledgment and approved exclusive GPU access apply.

The packed selector explicitly enables `SGLANG_EXPERIMENTAL_PACKED_W8_EMBEDDING=1`
and uses `--load-format safetensors --dtype bfloat16`, as required by the patched
loader. Dense mode clears an absent, empty or zero packed-loader flag and rejects any
other inherited value, including `1`. Packed target-only is
rejected before model verification: the current loader admits DFlash only.
Multimodal loading remains enabled; no language-only, LoRA, compilation or
parallel-mode escape is added. This wiring still needs actual GPU-loader
qualification. Earlier inventory-only checks did not exercise model construction.

### Bounded static-memory control

`QWEN_MEM_FRACTION_STATIC` accepts only `0.94` (default), `0.95`, `0.96`, `0.97`
or `0.98`. It changes only SGLang's existing static-memory fraction argument.
All choices remain behind the unqualified acknowledgment. Higher values are
measurement candidates, not promoted defaults or proof that a model fits. Keep
the value fixed for matched comparisons and record requested versus allocated
capacity; strict capacity rejection remains enabled. No automatic retries with
larger fractions or smaller contexts occur.
