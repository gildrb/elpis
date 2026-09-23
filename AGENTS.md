# Repository Guidelines

## Project Overview

Litos is a verified serving-optimization lab for **Qwen3.8-27B on one RTX 3090 at 262,144-token native context**: a patched SGLang v0.5.19 server (KVarN packed KV + DFLASH2 speculative decoding) whose allocation planning, objective policy, greedy speculative-acceptance decisions, and host mirror-control actions are **computed and proven in Bend 2.0.20**, plus the measurement/qualification harness that turns every throughput claim into hash-bound raw evidence. Primary metric: pooled native-math `model_call_output_tok_s` from `bash autoresearch.sh` under an external GPU-window guardian. Mission rules live in `.omp/rules/native-262144-low-qty-only.md` (highest tok/s at native context; legit benchmarks; honest evidence) and `.omp/rules/bend-lang.md` (Bend best practices).

## Architecture & Data Flow

1. **Proof stage** — `PROOF.bend` (imports `LAWS.bend`) is checked by the repo-local source-mode Bend 2.0.20 checker (release ELF + `BUN_BE_BUN` running pinned upstream TS with one reviewed stack-safe comparator patch). Stock global `bend` overflows on this proof; use `nix build .#bend` / `nix run .#bend -- PROOF.bend` or `/tmp/litos-bend20-tool/bin/bend`.
2. **Artifact stage** — `bend/adapter.py generate → compile → verify` turns the checked proof into four CPU programs (`plan`, `select`, `speculate`, `runtime`) plus hash-pinned identity JSONs (source schema 7, build 5, verified 5) under one artifact directory; `bend/native_build.py` NVRTC-compiles the speculate leaf into the SM86 `acceptance.cubin` after fail-closed parity admission.
3. **Image stage** — `Dockerfile` (stages: bend-toolchain → marlin-build → bend-build → final) applies `patches/experimental.series` (sha256-pinned, applied to pinned `lmsysorg/sglang:v0.5.19@sha256:d6e7288…`) and embeds only proved artifacts; patches re-admit them at server startup (`checked_plan` / `checked_speculation` / `checked_runtime`).
4. **Serving** — container `qwen-bend20-*` serves OpenAI-compatible `/v1` on `127.0.0.1:18020` (auth key at `/mnt/ssd/storage/ai/qwen3.8-27b/api-key`); greedy-only acceptance is a Bend-law boundary, not a limitation to remove casually.
5. **Measurement** — `bash autoresearch.sh` → `bench/autoresearch.py` supervisor (guards an armed maintenance window) → nix-offline worker runs four producers in order: tiny AIME25, short I3, long GraphWalks (greedy, 178,769-token row), C1 decode depths 1024/8192/32768 ×5; every phase is identity-captured before/after and admitted by `serve/qualification.py` gates; only complete raw evidence prints `METRIC` lines.

## Key Directories

- `bend/` — Bend modules (`X.bend` impl, `X_spec.bend` independent reference, `X_laws.bend` laws, `X_proof.bend` proofs) for range/control/plan, selection, speculation, transaction, ownership, abi, numerical, selector domains; plus `adapter.py`, `build_toolchain.py`, `native.py`/`native_build.py`/`native.cu`.
- `patches/` — sha256-pinned native patch series (`experimental.series`, format: `<sha256>  <name>.patch`); `NOTES.md` is the measured-performance history (what is settled — do not re-litigate).
- `bench/` — measurement producers and the autoresearch supervisor/worker.
- `serve/` — `qualification.py` (fail-closed evidence gates; `require()` → `ValueError`), `entrypoint.sh` (in-container invariant checks), `healthcheck.py`.
- `eval/` — pinned Prime/verifiers stack (`eval/scripts/setup|sandbox|data|run`), direct-context lane (`eval/direct/run`, `eval/direct/configs/…`, pinned `.venv`s), frozen dataset locks.
- `docs/` — `benchmarks.md` (protocol), `qualification.md` (gates), `decode-bottlenecks.md` (ledger).
- `nix/` — `bend.nix` (source-mode checker package), compose/deployment adapters; flake outputs `.#bend`, `.#serve`, `.#deployment`.
- `bench/results/` — measured ledgers (append-only history; never rewrite).
- `/tmp/litos-recovery-ops-id8q0yvb/` + `/tmp/litos-native-recovery.py` — GPU maintenance-window/guardian tooling (external to the repo by design).

## Development Commands

```bash
bend PROOF.bend --check-only            # proof gate (use repo-local bend; stock global bend overflows)
nix build .#bend && nix run .#bend -- PROOF.bend --check-only
python3 bend/adapter.py generate --output DIR --bend /path/to/bend     # then compile/verify
nix develop --offline --no-write-lock-file -c bash eval/scripts/sandbox  # evaluator sandbox image
docker build -t qwen-litos:<tag> .                                       # serving image (CPU-only build)
bash autoresearch.sh              # frozen benchmark; needs armed window + operator descriptor
bash eval/scripts/run --profile tiny   # scored eval lane (also smoke/tiny/diverse/quick/full)
python3 -m py_compile <file>      # minimum check for edited Python
```

Format Python with the pinned formatter (`nix develop -c uv run --locked --offline … ruff format <files>`); the repo does not enforce `ruff check ALL` cleanly — do not chase pre-existing findings.

## Code Conventions & Common Patterns

- **Fail closed everywhere**: `require(cond, msg)` / `fail(msg)` raise `ValueError`; no clamping, fallbacks, or silent coercion. Distinct errors for absent/empty/zero/false.
- **Hash-pin identity**: every artifact, patch, config, dataset revision and binary is sha256-bound; validators compare exact normalized structures; symlinks in evidence are retained as verified relative-pointer records (`symlink:<target>`).
- **Freeze contracts change in pairs**: `eval/direct/configs/**.toml` sampling must be re-frozen together with the validator constants in `bench/direct_context.py` (`SAMPLING`); runner-parameter changes require a demonstrated flaw and are never compared across configs.
- **Bend module pattern**: optimized impl + independent spec + laws + equational proofs; no `@unsafe`, axioms, or proof-only lists leaking into production representations; parallel work uses explicit fork-join (`a b = f() g()`).
- **Affine ownership in Bend**: a binding is consumed once (`List.take` + `List.drop` on the same list is an error); use `+`-quantified Data fields or balanced Data trees for folds.
- Configs/TOMLs are identity inputs — edit only alongside their validators, with the reason in a comment.

## Important Files

- `autoresearch.sh` — fixed benchmark contract; **never edit mid-segment** (bump segment via `init_experiment(new_segment=true)` first).
- `bend/adapter.py` — artifact pipeline + `SOURCE_NAMES` closure; adding any imported `.bend` file REQUIRES adding it here or the Docker build fails.
- `serve/qualification.py` — all admission gates; `bench/autoresearch.py` — supervisor guard loop (paced; retries transient `/proc/locks` reads).
- `bench/direct_context.py` — long-row sampling contract; `eval/direct/configs/diverse/graphwalks-bfs.toml` — its frozen config.
- `patches/experimental.series` — series registry (a patch file present but unlisted does nothing).
- `Dockerfile` + `.dockerignore` — allowlist build context; new COPY sources must be allowlisted.

## Runtime/Tooling Preferences

- Bend: repo-pinned **2.0.20 source-mode** checker only for proofs (stock 2.0.20/2.0.25 overflow); `bend version` (not `--version`); learn with `bend guide`; Base via `bend base <name>`.
- Python: 3.12/3.13 via pinned `uv` in `nix develop` for tooling; `eval/.venv` (3.12) for the evaluator; **run eval tooling under the same nix environment** or native wheels fail on missing `libstdc++`.
- Docker: rootless (`DOCKER_HOST=unix:///run/user/1000/docker.sock`); GPU via CDI `nvidia.com/gpu=0`.
- Live services on this host (nextcloud/immich/paperless) share the docker daemon — never stop the daemon casually.

## Testing & QA

- No permanent test suite by convention; **never write tests or edit `README.md` unless explicitly asked**. Validation = run the real thing (proof gate, `py_compile`, artifact pipeline, smoke on a live candidate).
- Qualification fixtures (`patches/qualification/*.py`) are evidence producers, not unit tests; keep them that way.
- Every kept benchmark change requires: proof gate green, quality unchanged (tiny AIME reward), full raw-evidence admission, and honest `log_experiment` (failures are logged as `crash`, never retried silently).
- GPU windows: only Main, only via the maintenance-lease guardian with authenticated baseline restore; the operator descriptor (`/run/user/1000/litos-autoresearch-operator.json`) must be freshly installed per run and the output directory must not exist.
