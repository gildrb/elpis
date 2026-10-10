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
   an operator-owned mode-0700 `prefix-cache/` directory and an operator-owned
   mode-0600 regular `api-key`. The key is 1..4096 bytes, printable ASCII without
   whitespace, with at most one trailing newline. Compose creates none of these
   paths. Startup neither downloads nor converts models.
3. Create `qwen-inference-launch.lock` only if absent, with exclusive creation
   and mode 0600. Never replace or unlink its inode while any deployment can
   exist. Reuse the existing shared lock when migrating an occupied service.
4. For rootless Docker, `QWEN_CONTAINER_USER=0:0` maps to the operator. For
   rootful Docker, set the state owner's numeric `UID:GID`; do not weaken state
   permissions to work around an ownership mismatch.
5. Build the base image from source. Network access is used only in step 5a.
   a. `bash docker/fetch-base.sh` pulls the three pinned images by digest
      (CUDA 13.0.0 devel and runtime, uv 0.9.15) and downloads every file that
      `docker/base/sources.lock` names into `build/base-inputs/`: the exllamav3
      commit tarball (355c6ee), the CPython 3.13.10 build that uv installs, the
      Ubuntu `.deb` files from a fixed snapshot.ubuntu.com time, the base wheels
      (torch and CUDA wheels from download.pytorch.org/whl/cu130, all other wheels
      from PyPI) and the serve wheels. Each file must match its sha256, else the
      script stops.
   b. `bash docker/build-base.sh` builds `docker/base/Dockerfile` with no network
      in any RUN, `SOURCE_DATE_EPOCH` from the checked-out commit,
      `rewrite-timestamp=true` and no attestations. It tags `qwen-elpis:exl3-base`
      only if the image's content manifest equals the pin in
      `docker/base/engine-manifest.json`.

   The content manifest (`docker/base/manifest.py`) is the sha256 of a sorted
   listing: the installed Debian packages with versions, and the sha256, mode
   and path of every file and symlink under `/opt/uv-python` and `/opt/venv`
   (without `__pycache__`). nvcc does not give byte-identical output from build
   to build: nvcc puts its process ID into local symbol names, and cicc orders
   registers by memory layout (ASLR), which changes the PTX of some
   `gdn_conv_rule_norm_kernel` instances. ptxas also writes source mtimes into
   the `-lineinfo` tables; `patches/exl3-ext/ext.py` sets fixed mtimes. A fixed
   layout needs ASLR off, and Docker's default seccomp profile blocks that in
   RUN steps. So the compiled `exllamav3_ext` shared object and the exllamav3
   `RECORD` (which holds its hash) are not part of the pin. The base build
   records their sha256 in `/opt/elpis-base-manifest.json`, and
   `patches/exl3-ext/ext.py` requires the installed shared object to match that
   record. To check a base by hand, run `manifest.py check` in it:

```sh
docker run --rm --network none --user 0:0 \
  --mount type=bind,source="$PWD/docker/base/manifest.py",target=/tmp/manifest.py,readonly \
  --entrypoint /opt/venv/bin/python qwen-elpis:exl3-base \
  -I -B /tmp/manifest.py check /opt/elpis-base-manifest.json
```

   `docker/base/lock.py` wrote `requirements.lock` and `sources.lock` from
   `requirements.in`, `apt.in` and `serve/exl3-requirements.txt`. It needs network
   access and is not part of a build. Run it only to change an input.

```sh
bash docker/fetch-base.sh       # the only step with network access
bash docker/build-base.sh       # tags qwen-elpis:exl3-base
# CPU image build, not a GPU launch:
bash docker/build-exl3.sh candidate-ext qwen-inference:exl3   # or: baseline, candidate, candidate-rebuilt
export QWEN_STATE_ROOT=/absolute/private/qwen-state
export QWEN_IMAGE=qwen-inference:exl3
docker compose --project-name qwen-inference config --quiet
```

Use the build scripts, not `docker compose build` or a direct Dockerfile build.
`build-exl3.sh` first builds the `base-manifest` target: `manifest.py check` runs
in the base and its content sha256 must equal the pin. The value becomes the
`io.elpis.exl3.base-manifest-sha256` label of the image. The script also requires
the base tag to name the same image before and after the `--pull=false` build with
the daemon-backed default builder, checks the baked labels and only then assigns
the output tag. It refuses an output tag that names the base. The operator must
exclusively control image tags during the build: the before/after check detects
ordinary retagging, not a hostile Docker operator. Compose has no build stanza and
uses `pull_policy: never`.

The `baseline` target retains the base's installed native EXL3/DFlash2 engine
unchanged. The `candidate` target additionally applies the SHA-pinned
`patches/exl3` series to the installed ExLlamaV3 and embeds the Bend acceptance
artifacts (recorded by `/opt/qwen/exl3-patches.json` and image labels). The
`candidate-ext` target is `candidate` plus `exllamav3_ext` recompiled for sm_86
from the pinned `355c6ee` sources with the SHA-pinned `patches/exl3-ext` series;
`candidate-rebuilt` recompiles the same sources unpatched, as the toolchain
control. Both extension targets build in two phases: the first exports the
composed engine manifest, whose SHA-256 becomes the final image's
`io.elpis.exl3.patches-sha256` label. All targets bake the standalone
`serve/exl3_server.py`, startup guard, healthcheck and model inventory, rather
than mounting server code from `/tmp`. No RUN step has network access: the
hash-pinned JSON Schema wheels of `serve/exl3-requirements.txt` come from
`build/base-inputs/serve-wheels/`. The extension stages use the devel image of the
base build stage with its own g++, not an apt install. Serving uses offline
Hugging Face/Transformers settings and disables telemetry. Torch and
transformers are never rebuilt or replaced; only the extension targets replace
the installed `exllamav3_ext` shared object.

`prepare/exl3-manifest.json` records engine/model revisions and SHA256 identities.
Every start authenticates all 13 target and three draft runtime files, including
weights, config, quantization, tokenizer, merges and chat template. The verifier
rejects symlinks, unexpected loadable files, mismatches and changes during hashing.
Only inert publication files and a real `.cache` directory are allowed outside
the inventory. Model-byte identity is not a numerical or quality qualification.

## Ordinary Compose ownership and lifecycle

Do not launch beside another inference service on the same GPU or port. After
explicit exclusive-GPU approval:

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

The launcher passes `--cpu-cache-gib 8`: a host-RAM page tier (engine
`generator/cpu_cache.py`, upstream ExLlamaV3) of 8 GiB pinned memory, inside the
container's 48-GiB limit. Prefix pages evicted from the 270K-token GPU cache move
there and come back on the next prefix hit, so a long session that another client
pushed out does not re-prefill. Measured on elpis-fast (same server code, same tier):
a 94K-token prompt again after a 185K-token one 16.2 s instead of 79.6 s cold, same
text; a 193K-token agent session resumed in 36.5 s instead of 197 s. The tier copies
cache bytes; it does not change arithmetic. The persistent prefix cache
(`exllamav3.generator.persist`, patch 9501b) refuses to run with the tier, so the
launcher no longer passes `--prefix-cache`; Compose still binds `prefix-cache/`.
`--prefix-cache DIR` without the tier keeps the old behaviour: bound to the image
ID (`QWEN_IMAGE_ID`, full `sha256:<64 hex>`), `candidate-ext` only, off with
`QWEN_PREFIX_PERSIST=0`.

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
rather than being repaired or reported as successful calls. Tool `parameters` must be
a direct `type: object` with parameter schemas in its root `properties`,
`patternProperties` or `additionalProperties`. Root `allOf`, `anyOf`, `oneOf`, `not`,
`if`/`then`/`else` and `dependentSchemas` are accepted only when they constrain the
object (for example `required`) and declare no parameter schemas; a root `$ref` is
rejected.

The server matches tool-schema `pattern` and `patternProperties` with the `regex`
module from the base image, not Python `re`. All matches for one response share a
2-second budget. When the budget runs out, the request fails with HTTP 400
`pattern_timeout`. A tool schema that contains both `unevaluatedProperties` and
`patternProperties` is rejected. A client must send its request line and headers
within 60 seconds (this includes keep-alive idle time) and its body within 300
seconds; else the server closes the connection (HTTP 408 for a late body).
Generation and response writes have no timeout.

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
