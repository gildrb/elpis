# Repository Guidelines

## Project Overview

Litos serves **Qwen3.8-27B on one RTX 3090 at 262,144-token native context** with ExLlamaV3 (EXL3 4.00 bpw target) and native DFlash2 speculative decoding, and uses **Bend** to state and prove the decision logic the serving path must get right. The current Bend work is EXL3 greedy speculative acceptance executed in the serving path; later engine changes follow the same law → proof → measurement order. Throughput comes from the `bash autoresearch.sh` EXL3 lane; quality comes from pinned Prime Envs. Mission rules live in `.omp/rules/native-262144-low-qty-only.md` (highest tok/s at native context; legit benchmarks; honest evidence) and `.omp/rules/bend-lang.md` (Bend best practices).

## Architecture & Data Flow

1. **Proof stage** — `PROOF.bend` imports `LAWS.bend` (the accepted contract) and proves the production `bend/` definitions. Check it with the pinned toolchain: `nix build .#bend` / `nix run .#bend -- PROOF.bend` (unmodified Bend 2.0.27 release packaged by `nix/bend.nix` + `bend/build_toolchain.py`).
2. **Image stage** — `bash docker/build-exl3.sh <baseline|candidate> <tag>` builds `Dockerfile.exl3` on the authenticated local base `qwen-litos:exl3-native-comparison` (image ID pinned; ExLlamaV3 `355c6ee` + DFlash2). `baseline` leaves the engine unchanged; `candidate` applies the SHA-pinned `patches/exl3` series (`patches/exl3/apply.py`) and embeds the Bend acceptance artifact (built on the host into `build/bend-exl3`, installed at `/opt/qwen/bend-exl3`). Both bake `serve/exl3_server.py`, `serve/healthcheck.py`, `serve/exl3-entrypoint.sh` and `prepare/verify-models.py` + `prepare/exl3-manifest.json`.
3. **Serving** — `docker-compose.yml` (or `nix/qwen-inference.nix` / `.#serve`) runs the image; `docker/entrypoint.sh` takes the shared launch lock, the EXL3 launcher rehashes every model file against the manifest, then serves the authenticated OpenAI-compatible `/v1` on `127.0.0.1:18020` (model `qwen3.8-27b`; greedy only, one sequence, context 262144, cache 270336, CQ3). The live deployment is guardian-managed (see `docs/docker.md`).
4. **Measurement** — `bash autoresearch.sh` → `bench/autoresearch.py` EXL3 lane (protocol in `docs/benchmarks.md`); `eval/scripts/run` runs the pinned Prime Envs evaluator against the same endpoint, recording container/image identity and input hashes before and after.

## Key Directories

- `bend/` — Bend modules (`X.bend` impl, `X_spec.bend` independent reference, `X_laws.bend` laws, `X_proof.bend` proofs); `LAWS.bend` / `PROOF.bend` at the root.
- `serve/` — `exl3_server.py` (API server), `exl3-entrypoint.sh` (fixed launch recipe), `healthcheck.py`, `exl3-requirements.txt` (hash-pinned wheels).
- `prepare/` — `exl3-manifest.json` (engine/model revisions + per-file SHA256) and `verify-models.py` (fail-closed byte verifier).
- `bench/` — the autoresearch EXL3 lane, `power.py` (board-power sampler), `throughput-prompts.jsonl` (frozen C1 corpus).
- `eval/` — pinned Prime/verifiers stack (`eval/scripts/setup|sandbox|data|run`), power sidecar `eval/measure.py`, direct-context lane (`eval/direct/`), frozen dataset locks.
- `docs/` — `benchmarks.md` (protocol), `architecture.md`, `docker.md` (deployment + live evidence), `development.md`.
- `nix/` — `bend.nix` (Bend toolchain), `compose.nix` / `qwen-inference.nix` / `reference.nix` (EXL3 deployment adapters); flake outputs `.#bend`, `.#serve`, `.#deployment`.
- `/tmp/litos-recovery-ops-id8q0yvb/` + `/tmp/litos-native-recovery.py` — GPU maintenance-window/guardian tooling (external to the repo by design).

## Development Commands

```bash
nix build .#bend && nix run .#bend -- PROOF.bend   # proof gate
bash docker/build-exl3.sh baseline qwen-inference:exl3   # serving image (CPU-only; or `candidate`)
nix develop --offline --no-write-lock-file -c bash eval/scripts/sandbox  # evaluator sandbox image
bash autoresearch.sh                               # EXL3 benchmark lane; needs an armed GPU window
bash eval/scripts/run tiny                         # scored eval lane (also smoke/diverse/quick/full)
python3 -m py_compile <file>                       # minimum check for edited Python
```

Format Python with the pinned formatter (`nix develop -c uv run --locked --offline … ruff format <files>`); the repo does not enforce `ruff check ALL` cleanly — do not chase pre-existing findings.

## Code Conventions & Common Patterns

- **Fail closed everywhere**: `require(cond, msg)` / `fail(msg)` raise `ValueError`; no clamping, fallbacks, or silent coercion. Distinct errors for absent/empty/zero/false.
- **Hash-pin identity**: every image, model file, config, dataset revision and binary is sha256-bound; validators compare exact normalized structures.
- **Frozen runner parameters**: sampling/output-budget changes require a demonstrated flaw, apply to every arm, and are never compared across configs.
- **Bend module pattern**: optimized impl + independent spec + laws + equational proofs; no `@unsafe`, axioms, or proof-only lists leaking into production representations; parallel work uses explicit fork-join (`a b = f() g()`).
- **Affine ownership in Bend**: a binding is consumed at most once (`List.take` + `List.drop` on the same list is an error); use `+`-quantified Data fields or balanced Data trees for folds.
- Configs/TOMLs are identity inputs — edit only alongside their validators, with the reason in a comment.

## Important Files

- `autoresearch.sh` — fixed benchmark contract; **never edit mid-segment** (bump segment via `init_experiment(new_segment=true)` first).
- `LAWS.bend` — human-controlled contract; weakening a law needs explicit authorization.
- `serve/exl3-entrypoint.sh` — the single fixed launch recipe; it rejects retired controls.
- `prepare/exl3-manifest.json` — trust root for model bytes; the launcher refuses any mismatch.
- `Dockerfile.exl3` + `.dockerignore` — allowlist build context; new COPY sources must be allowlisted.

## Runtime/Tooling Preferences

- Bend: pinned toolchain via `.#bend`; `bend version` (not `--version`); learn with `bend guide`; Base via `bend base <name>`.
- Python: 3.12/3.13 via pinned `uv` in `nix develop` for tooling; `eval/.venv` (3.12) for the evaluator; **run eval tooling under the same nix environment** or native wheels fail on missing `libstdc++`.
- Docker: rootless (`DOCKER_HOST=unix:///run/user/1000/docker.sock`); GPU via CDI `nvidia.com/gpu=0`.
- Live services on this host (nextcloud/immich/paperless) share the docker daemon — never stop the daemon casually.

## Testing & QA

- No permanent test suite by convention; **never write tests or edit `README.md` unless explicitly asked**. Validation = run the real thing (proof gate, `py_compile`, image build, smoke on a live candidate).
- Every kept benchmark change requires: proof gate green, quality unchanged (tiny AIME reward), complete raw evidence, and honest `log_experiment` (failures are logged as `crash`, never retried silently).
- GPU windows: only Main, only via the maintenance-lease guardian with authenticated baseline restore.
