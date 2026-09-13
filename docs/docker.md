# Standalone Docker service

Use the root `Dockerfile` and `docker-compose.yml` without Nix. They consume the same `serve/entrypoint.sh` launch flags and `serve/supervisor.py` health policy as Nix. There is one qualified 64K/C1 profile, not a configurable tuning matrix.

## Supply local state

1. Install Docker Engine, Docker Compose v2 and NVIDIA Container Toolkit with CDI configured for `nvidia.com/gpu=0`. This repository does not install drivers, change power limits or configure the host daemon. Rootless Docker also needs CDI enabled in that daemon and permission to use the GPU. Rootful Docker uses its own daemon configuration; do not run both deployments on the same GPU. The default container user is `0:0` for **rootless** Docker, where container root maps to the host operator. For **rootful** Docker, set `QWEN_CONTAINER_USER` to the numeric `UID:GID` that owns the state directory (for example, `export QWEN_CONTAINER_USER="$(id -u):$(id -g)"` when you own it). Docker validates the user setting. Keep the key and state private: do not add capabilities or loosen permissions to make rootful container root read another user's files.
2. Set `QWEN_STATE_ROOT` to an existing private directory. Supply `models/compact-target-rholsc8k/artifact/` and `models/Qwen3.8-27B-DFlash2-W4A16/` beneath it. Read [model reproduction](../prepare/REPRODUCE.md) separately. Serving never downloads, converts or substitutes models.
3. Supply an existing `api-key` file in that directory, owned by the operator with mode `0600`. Use a nonempty printable ASCII secret without whitespace (one trailing newline is accepted), at most 4096 bytes. Create a private writable `cache/` directory and, only if absent, an empty mode-`0600` file named `qwen-inference-launch.lock` in the state root using exclusive creation (`O_CREAT | O_EXCL` or shell noclobber). If it already exists, retain it without truncation. Preserve that lock file: do not unlink or replace it while any deployment is active. Do not put the secret in Compose, shell arguments or this repository.
4. Validate and build with the commands below. Building is CPU-only. It requires disk space for the stock runtime image but no models or GPU.
5. Start only with approved exclusive GPU access. Do not start Docker beside an existing Nix deployment.

```sh
export QWEN_STATE_ROOT=/absolute/path/to/qwen3.8-27b
# Rootless Docker: keep the default QWEN_CONTAINER_USER=0:0.
# Rootful Docker, with state owned by your current user:
# export QWEN_CONTAINER_USER="$(id -u):$(id -g)"
docker compose config --quiet
docker compose build
# This next command starts the GPU service; run only when approved.
docker compose up -d
```

The authenticated OpenAI-compatible endpoint is `http://127.0.0.1:18020/v1`, with model `qwen3.8-27b`. Only host loopback is published. The server must bind `0.0.0.0` inside the container for that mapping. Send the credential as a Bearer token. Never print raw server configuration, which can contain the key.

## Build and restart guards

The Dockerfile pins stock `lmsysorg/sglang:v0.5.19@sha256:d6e7288627be8b02be88e4bba38e73f6d50e2826869f753c13a4c4385ab3eda9`. It installs no packages, runtime, kernels or compiler. No fork is fetched. The build first verifies all three original files **in the actual base image**. It retains those originals in `/sglang-original`, hash-checks the three local patch files, applies them with `patch --fuzz=0`, then verifies exact replacement hashes. Context allowlisting excludes models, credentials and caches.

Before any guard or child starts, the container takes an exclusive nonblocking lifetime lock on the existing host `qwen-inference-launch.lock` file. Nix launchers use the same file. A losing launcher exits without cleaning up the winner. This prevents simultaneous ownership only when deployments use the same canonical state directory and preserve the lock inode. Every container start verifies retained originals and installed replacements. The shared launch script verifies full local model inventories and hashes before starting SGLang. Any mismatch fails closed. The original archive proves applicability to the checked base image at build time; it is not an independent runtime re-fetch of that image. Keep the built image and its digest under your deployment's trusted supply chain.

The foreground controller owns the guarded server child and shared health-monitor child. The server health timeout is **300 seconds**. Each complete health/authenticated-model probe has a **310-second** deadline. Startup readiness is bounded to **20 minutes**; once ready, **three failed probes**, **30 seconds apart**, trigger shutdown and nonzero exit. Child exit also fails the container. Cleanup sends TERM, then bounds worker shutdown to 45 seconds. Docker `restart: unless-stopped` reruns all guards. This is active recovery, not a Docker healthcheck that only marks a stuck container unhealthy. A manual `docker compose stop` remains stopped.

Both model directories and the key are read-only binds. The root filesystem is read-only. Writable state is limited to the cache bind, the ownership-lock file, 32 GiB shared memory, and bounded `/run` and `/tmp` tmpfs mounts. Capabilities are dropped, privilege escalation is disabled, and CPU/memory limits are 8 CPUs/48 GiB. The required host paths must already exist; Compose must not create empty replacement directories. GPU 0 is selected explicitly.

## Operate and qualify

Use `docker compose ps` and `docker compose logs --tail 100 inference` to inspect startup. Readiness is logged as `Authenticated model API is ready.` A running container alone is not API readiness. Use `docker compose down` to remove the deployment. Rebuild after changing repository source; a restart does not rebuild the image.

Do not use `--entrypoint`, Compose overrides or writable source mounts to bypass guards. Do not hot-reload weights or partially load checkpoints. Restore a previously verified image and its matching model artifacts for rollback; never weaken a failed hash check.

See [qualification](qualification.md), [native results](../bench/results/native.json), and [patch restrictions](../patches/NOTES.md). Existing runtime measurements do not establish that this Docker deployment has been GPU-qualified. Host driver, power/fan policy, monitoring and activation remain operator-owned.
