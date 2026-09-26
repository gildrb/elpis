# Canonical EXL3 Docker deployment

`Dockerfile.exl3`, `docker/build-exl3.sh`, `docker-compose.yml` and
`serve/exl3-entrypoint.sh` define the serving recipe. Nix consumes the same
prebuilt-image Compose configuration; it does not provide another engine.

The fixed recipe is Qwen3.8-27B EXL3 plus native DFlash2, one sequence, CQ3,
context **262144** and cache **270336**. These settings are not a full-context
capacity, performance or model-quality qualification. There is no smaller-context,
target-only, different-KV or alternate-engine fallback.

## Prepare and build

1. Install Docker Compose v2, Buildx, a compatible NVIDIA driver and NVIDIA
   Container Toolkit with CDI `nvidia.com/gpu=0`. Drivers, GPU reservation,
   storage, fans and power remain operator-owned.
2. Supply an existing canonical absolute private `QWEN_STATE_ROOT` containing
   `models/qwen38-27b-exl3/`, `models/dflash2-exl3/`, private writable `cache/`,
   and an operator-owned mode-0600 regular `api-key`. The key is 1..4096 bytes,
   printable ASCII without whitespace, with at most one trailing newline.
   Startup neither downloads nor converts models.
3. Create `qwen-inference-launch.lock` only if absent, with exclusive creation
   and mode 0600. Never replace or unlink its inode while any deployment can
   exist. Reuse the existing shared lock when migrating an occupied service.
4. For rootless Docker, `QWEN_CONTAINER_USER=0:0` maps to the operator. For
   rootful Docker, set the state owner's numeric `UID:GID`; do not weaken state
   permissions to work around an ownership mismatch.
5. The intended Docker daemon must already contain local tag
   `qwen-eta:exl3-native-comparison` with exact image ID
   `sha256:b35314f48c7684b4c9cf3d59f4c21395316aa1fc0925db782f460005aa2602ff`.
   Its recorded RepoDigest is not a downloadable registry manifest. A direct
   digest `FROM` attempted registry resolution and failed; there is no registry
   pull or substitute-image fallback.

```sh
# CPU image build, not a GPU launch:
bash docker/build-exl3.sh baseline qwen-inference:exl3   # or: candidate
export QWEN_STATE_ROOT=/absolute/private/qwen-state
export QWEN_IMAGE=qwen-inference:exl3
docker compose --project-name qwen-inference config --quiet
```

Use the build script, not `docker compose build` or a direct Dockerfile build.
It authenticates the local base's actual image ID before and after a
`--pull=false` build using the daemon-backed default builder, verifies the baked
base-ID label and only then assigns the output tag. It refuses an output tag
already pointing to the native base. The operator must exclusively control image
tags during the build: these checks detect ordinary retagging, not a hostile
Docker operator. Compose has no build stanza and uses `pull_policy: never`.

The `baseline` target retains the base's installed native EXL3/DFlash2 engine
unchanged. The `candidate` target additionally applies the SHA-pinned
`patches/exl3` series to the installed ExLlamaV3 and embeds the Bend acceptance
artifact (recorded by `/opt/qwen/exl3-patches.json` and image labels). Both
bake the standalone `serve/exl3_server.py`, startup guard, healthcheck and
model inventory, rather than mounting server code from `/tmp`. Build-time network
access installs the hash-pinned JSON Schema wheels from
`serve/exl3-requirements.txt`; serving uses offline Hugging Face/Transformers
settings and disables telemetry. EXL3, torch and transformers are not rebuilt or
replaced by that dependency install.

`prepare/exl3-manifest.json` records engine/model revisions and SHA256 identities.
Every start authenticates all 13 target and three draft runtime files, including
weights, config, quantization, tokenizer, merges and chat template. The verifier
rejects symlinks, unexpected loadable files, mismatches and changes during hashing.
Only inert publication files and a real `.cache` directory are allowed outside
the inventory. Model-byte identity is not a numerical or quality qualification.

## Ordinary Compose ownership and lifecycle

Do not execute a new launch beside the existing live service. After explicit
exclusive-GPU approval and an authorized cutover:

```sh
export QWEN_ALLOW_UNQUALIFIED=1
docker compose --project-name qwen-inference up --no-build --pull never \
  --detach --wait --wait-timeout 1200
```

The acknowledgment permits operation without full qualification. All model,
credential and ownership checks still apply. The EXL3 launcher has one fixed
recipe and rejects retired serving controls instead of ignoring them.

The ordinary image entrypoint is `docker/entrypoint.sh`: it acquires the shared
lifetime lock and execs the baked `/opt/qwen/serve/entrypoint.sh`, which is the
EXL3 launcher in this image. The lock excludes only deployments sharing that
inode, not other states, accounts, daemons or GPU applications.

Compose keeps loopback-only `127.0.0.1:${QWEN_PORT:-18020}`, read-only models,
credential and root filesystem, private writable cache, restricted tmpfs,
`cap_drop: ALL`, `no-new-privileges`, init, an eight-CPU/48-GiB limit,
`restart: unless-stopped` and a 60-second stop budget. The image routes compiler
and library caches into `/cache` and uses CDI's `/usr/local/nvidia/lib64` driver
path. The served model is `qwen3.8-27b` at `http://127.0.0.1:18020/v1`.

The healthcheck authenticates `/health` and the expected `/v1/models` entry. It
runs every 30 seconds, with a 310-second probe budget, 315-second Docker timeout,
20-minute startup grace and three failures to unhealthy. Docker does not restart
a merely unhealthy container. A failed `up --wait` can leave a running container;
inspect it rather than assuming cleanup. A manual stop remains stopped.

## API and tool-call boundaries

The authenticated API supports chat and raw text completions. Generation is
**greedy only** (`temperature=0`), `n=1`, with one native sequence executing at a
time. Input tokens plus the requested output budget must fit 262144. Request
bodies are bounded at 32 MiB. Unsupported fields and invalid option types are
rejected, not silently ignored. This is not a claim of complete OpenAI API parity.

Chat tools use the authenticated model's native template and native XML-like
function-call syntax. Responses expose OpenAI-style `tool_calls`, including JSON
argument strings and call IDs; assistant-call and matching tool-result history
can be submitted for continuation. Clients execute tools; the server does not
execute their functions. Supported selection is `auto`, `none`, `required` or a
named function, with `parallel_tool_calls` enforced on the result. JSON Schema
validation is offline. `strict: true` is a fail-closed schema postcondition, not
constrained generation: invalid model arguments or violated tool selection fail
rather than being repaired or reported as successful calls.

Chat `stream=true` is **buffered SSE**, marked
`X-EXL3-Transport: buffered-sse`: generation finishes before content/reasoning/tool
frames are sent. Optional usage and `[DONE]` complete the transport. It is not
incremental token streaming, and first-event arrival must not be reported as
TTFT. Raw completion streaming is unsupported. Native thinking controls remain
in `chat_template_kwargs`; OpenAI top-level `reasoning_effort` is also accepted:
`none` disables thinking, `minimal` maps to `low`, `high` and `max` map to `xhigh`,
and `low`, `medium` and `xhigh` are unchanged. Invalid values or conflicting
nested controls return HTTP 400. Existing nested OMP controls are unchanged;
reasoning and final content remain separate channels.

## Current persistent live deployment

The current authenticated promotion is `qwen-exl3-serving-4`, container
`22154417d27bc0ce2455d3f60ff1e3743dd7c40aca8ef0f502450a2463ffa945`, with image
`sha256:a8753e49905df860fc8537c01f402f513768d7e3f6c0dc9ee1ba6cbe488c8fdc` (cs11,
variant `candidate-ext`: the #61 stack of `docs/benchmarks.md` §6, cs10 plus the 5108
commit-replay gather and the one-pack acceptor loader). The canonical tag
`qwen-inference:exl3` identifies this image and `qwen-inference:exl3-previous` the
retained previous image `sha256:c3e161ab89c8ca459dba8294764588cd2b4374b2b48e34578c81e8b2f11a2971` (cs10).
The persistent configuration is
`/mnt/ssd/storage/ai/qwen3.8-27b/exl3-serving-4/compose.json` (Compose project
`eta-exl3-serving-4`, network `eta_default`), alongside unchanged copies of
`launch-gate.py`, `recovery.py` and `operate.py` and its promoted `cutover-window-1/`.
It sequentially reuses `/mnt/ssd/storage/ai/qwen3.8-27b/exl3-serving-1/cache`; preserve
the old state. Promotions are made by `/tmp/eta-promote.sh TAG IMAGE` (operator
tooling outside the repo), which replays the serving-2 guardian procedure below with
automatic guardian rollback. The previous `qwen-exl3-serving-3` (container
`288862e7573f5dec9abb9ecc06bb2d144c9926c1f8fb972efafcadf1fa0a235a`, image cs10, network
`eta_default`) and `qwen-exl3-serving-2` (container
`b5e51bc1f6ac85b1b2af8db3612ff300190145397bb48b31e4cb7bf0f2d30f28`, network
`litos_default`) are stopped and retained; their promoted windows still admit them for
rollback, so keep `litos_default` while any retained container uses it.

The original cutover promoted `qwen-exl3-serving-1`, container
`e22faabe5bc9244d88581e4abcab1459d545b82b154b731ea4ccb2de642efb7c`, with image
`sha256:f4bdcfb444f3215e57d23c67edd6929c4afa87eb95f5594d1df7bf438a19ae80`.
Its controls and evidence remain under
`/mnt/ssd/storage/ai/qwen3.8-27b/exl3-serving-1/`. That container is stopped and
retained, not deleted.

This live deployment deliberately differs from an ordinary root Compose launch:
the persistent guardian gate validates candidate identity and its promoted window,
acquires the **same existing shared lock inode**, then execs
`bash /opt/qwen/serve/entrypoint.sh` with the lock inherited. It must not call the
Docker ownership wrapper again and try to acquire a second lock. The server code
is still baked in the image; only host-owned guardian controls are mounted at
`/maintenance-control`, read-only. Preserve the control files, promoted receipt,
operation mutex and launch-lock inode. Do not hand-author authorization states,
replace the gate with a direct launch, or start a competing root Compose/Nix
service. Future maintenance must use the retained deployment and its approved
ownership procedure. Restart configuration is not a demonstrated cold-boot test.

Current private evidence is in `exl3-serving-4/evidence/` under the state root:
`main-verification.json`, `promotion-receipt.json`, `cutover-receipt.json`,
`endpoint-smoke.json`, `live-tool-smoke.json`, `hermes-real-tool-turns.json`,
`omp-smoke.jsonl`, `installed-exl3-server.py`, `guardian.log` and `thermal.csv`. The
guardian exited 0 with state `promoted_authenticated_main_verified`. Real Hermes
gateway 0.21.3 and interactive 0.21.4 terminal-tool turns and an OMP 18.3.1 read-tool
round trip passed against the new image; no Telegram delivery was repeated.

serving-2's evidence (`exl3-serving-2/evidence/`: `main-verification.json`,
`promotion-receipt.json`, `telegram-delivery.json`) records the top-level reasoning
compatibility change, Hermes 0.21.3/0.21.4 and OMP 18.2.11 turns, Telegram API checks
and one approved outbound delivery; **no fresh inbound user-to-bot exchange has been
exercised**. See [client routing](#host-client-routing) and
[verification boundaries](development.md#exl3-cutover-verification-status).

Original `exl3-serving-1/evidence/` retains `promotion-receipt.json`,
`main-promotion-verification.json`, `live-tool-smoke.json` and
`post-promotion-health.stderr`. That smoke exercised a named addition call
(`19 + 23`), client execution and continuation returning `42`, buffered tool SSE,
authentication, model identity and schema-error handling; authenticated health
and runtime CPU protocol proof passed. Neither promotion establishes full-context
capacity, quality or performance qualification. Ruff ALL style findings and host
ty dependency blockers remain; the upstream torch `inference_mode` issue is a
historical known runtime typing limitation, not a current runtime ty rerun.

## Host client routing

OMP's host runtime `~/.omp/agent/models.yml` defines `qwen-local/qwen3.8-27b`
using chat completions, the private key via `!cat`, temperature 0, the existing
nested Qwen thinking dialect and a ten-minute buffered first-event floor.
Explicit `thinking.requiresEffort: false` allows thinking off. The existing
cloud default is preserved: select `omp --model qwen-local/qwen3.8-27b` or choose
that model with `/model`.

Hermes's host runtime `config.yaml` uses local `api_mode: chat_completions` and
temperature 0. Its durable host-owned overlay in
`~/nix/modules/nixos/local-ai-backend.nix` was updated without OS activation;
the pinned installed old profile may still regenerate the old configuration.
Generic dotfiles were not changed. The live gateway 0.21.3 was not restarted;
its persisted session explicitly selects `custom:local/qwen3.8-27b` at
`http://127.0.0.1:18020/v1`. Its original request failed HTTP 400 on the old server
but now works with top-level reasoning compatibility. Interactive 0.21.4 had
previously recovered automatically from the rejected effort; gateway 0.21.3 did
not. These are verified host settings, not defaults installed by root Compose.
