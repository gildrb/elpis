# Repository Guidelines

## Project Overview

Serving and optimization lab for **Qwen3.8-27B + DFlash2 speculative decoding on one RTX 3090** (24 GiB, SM86, TP=1), serving **262144 native tokens**. The current vehicle is pinned upstream SGLang v0.5.19 plus a visible patch layer — not a fork: upstream is pinned and patched, nothing is vendored.

Prime directive: **provably correct Bend code and measured, honest inference performance** — highest accurate tok/s and shortest TTFT at native context, qualified by frozen quality runs. Two binding agent rules encode this: `.omp/rules/bend-lang.md` (Bend law/proof/performance discipline) and `.omp/rules/native-262144-low-qty-only.md` (benchmark legitimacy, deployment, honesty). Read both before substantive work.

The engine is a current choice, not a hard requirement: any serving stack (vLLM, ExLlamaV3/EXL3, or another port) is a legitimate replacement if it beats the live recipe under the same frozen measurement configs and qualification gates. Translate ideas between engines; measure before adopting; never compare numbers across changed configs.

## Architecture & Data Flow

1. **Current engine: pinned upstream + patch layer.** SGLang commit `0bcd8223...` (`patches/source.env`) is modified only by `patches/baseline.series` (3 patches) + `patches/experimental.series` (14 more), applied by `patches/apply.sh` into a disposable clean checkout; every patch is sha256-bound and order matters. The `Dockerfile` bakes the series into a digest-pinned `lmsysorg/sglang:v0.5.19` image.
2. **Bend proof chain (the correctness core, engine-independent).** `LAWS.bend` states executed contracts; `PROOF.bend` discharges them; `bend/*.bend` implement the planner/policies per domain (control, selection, speculation, transaction, ownership, numerical, abi). `bend/adapter.py` snapshots the exact 41-file source closure, checks `PROOF.bend` with the pinned source-mode Bend 2.0.20, emits four CPU wire programs (`PLAN/SELECT/SPECULATE/RUNTIME.bend`), compiles (clang-19) and verifies them. `bend/native_build.py` admits the single 7-Bool scalar leaf in `speculate.c`, proves CPU/LLVM/128-mask parity against the checked policy, and NVRTC-compiles `speculate.c + native.cu` into the SM86 acceptance cubin used on the GPU DFlash path.
3. **Serving.** `docker/entrypoint.sh` (flock on the shared launch lock) execs `serve/entrypoint.sh` — a fail-closed guard chain that calls `bend.adapter.checked_plan` once for pool/page geometry (context 262144 → pool 263168, page 128) and execs `sglang.launch_server` (DFLASH block 8 / window 2048, `kvarn_k4v2_g128` KV, port 18020). API: `http://127.0.0.1:18020/v1`, model `qwen3.8-27b`, Bearer auth.
4. **Qualification.** `serve/qualification.py` (`python -m serve.qualification`) re-verifies the whole chain from raw artifacts — runtime identity capture, Bend proof gate binding image artifacts byte-for-byte to repo sources, byte-exact C1 SSE replay, capacity/numerical/energy/eval gates — and the compiled `ObjectivePolicy` (from `SELECT.bend`) decides `promote_candidate` vs `retain_control`.
5. **Weights** are reproduced offline, byte-exactly, under sha256 manifest gates (`prepare/`); serving never downloads, transforms, or silently replaces weights.

## Key Directories

| Directory | Purpose |
|---|---|
| `bend/` | Bend law/spec/proof sources, proof adapter + toolchain packager, CUDA acceptance kernel (`adapter.py`, `native_build.py`, `native.py`, `native.cu`) |
| `patches/` | Ordered sha256-bound SGLang patch series (current engine), guarded `apply.sh`, Marlin int8 transplant (`marlin-int8/`), GPU parity fixtures (`qualification/`), provenance (`NOTES.md`) |
| `bench/` | Measurement diagnostics: decode depth matrix, capacity probe, cache consistency, component numerics, power sampling, frozen autoresearch suite |
| `eval/` | Prime Envs + Verifiers quality harness (separate Python 3.12 uv project), frozen profiles/locks, power measurement, historical direct lane (`direct/`) |
| `prepare/` | Offline byte-exact model reproduction: hash manifests, assemble/quantize/convert recipe, verifiers |
| `serve/` | Container launch guard chain, healthcheck, qualification verifier |
| `docs/` | Canonical documentation; start at `docs/README.md` |
| `nix/` | Dev shell + tool pins; Bend 2.0.20 source-mode derivation (`bend.nix`); thin Compose adapter — never a second runtime recipe |
| `docker/` | Container entrypoint (flock guard) + patch application helper |

## Development Commands

All Python tooling runs inside the pinned Nix shell; always `--no-write-lock-file`, always `--locked`. Commands below operate the current SGLang-based recipe; the evidence and qualification rules apply to any engine:

```sh
nix develop . --no-write-lock-file -c uv sync --locked --python python3.13 --no-managed-python
nix develop . --no-write-lock-file -c uv run --locked --python python3.13 --no-managed-python ruff check .
nix develop . --no-write-lock-file -c uv run --locked --python python3.13 --no-managed-python ruff format --check .
nix develop . --no-write-lock-file -c uv run --locked --python python3.13 --no-managed-python ty check .
# add --offline after `uv run` once the locked environment exists
```

Bend (required before committing any Bend change; takes ~100 s and needs a 1 GiB stack):

```sh
bend PROOF.bend      # must end with "All terms check"
nix run .#bend       # pinned Bend 2.0.20 source-mode; the only accepted toolchain
```

Docker (canonical runtime for the current recipe):

```sh
export QWEN_STATE_ROOT=/absolute/private/qwen-state
docker compose --project-name qwen-inference build
export QWEN_ALLOW_UNQUALIFIED=1   # mandatory for every start; an acknowledgment, not qualification
docker compose --project-name qwen-inference up -d --wait --wait-timeout 1200
```

Patches (standalone reproduction; disposable checkout only):

```sh
git clone https://github.com/sgl-project/sglang.git /tmp/sglang-build
git -C /tmp/sglang-build checkout --detach 0bcd822377da7b5718e674eaf9c870d349424dd1
bash patches/apply.sh /tmp/sglang-build experimental
```

Eval / measurement: `eval/scripts/setup` → `eval/scripts/data aime24` → `eval/scripts/sandbox` → `eval/scripts/run smoke` (profiles: `smoke|tiny|diverse|quick|full|agentic`; `--dry-run` is model-free). `bash autoresearch.sh` is operator-only (armed maintenance window + private descriptor). Bench diagnostics run against the live endpoint: `python -m bench.decode|capacity|cache|numerical`.

## Code Conventions & Common Patterns

**Python** (strict gates: ruff `select=["ALL"]` + preview, line 88; ty `all="error"` + error-on-warning; no ignores, suppressions, or per-file exemptions anywhere):

- `from __future__ import annotations`; PEP 604 unions; `@dataclass(frozen=True, slots=True)` for policy tables.
- Fail-closed errors: `fail()`/`require()` raising `ValueError` with actionable messages; narrow exception handling only at CLI/`gate()` boundaries; no silent fallbacks.
- Evidence discipline: exclusive-create outputs (`open("xb")`, `mkdir` without `exist_ok`), canonical JSON (sorted keys, no NaN, duplicate keys rejected), symlink refusal, sha256 recorded per artifact, identity captured before/after runs.
- Subprocess discipline: no shell, stdin devnull, explicit timeouts, evidence JSON per invocation; ambient compiler-env overrides (`BUN_JSC_*`, `BUN_BE_BUN`, `NODE_OPTIONS`) detected and refused.
- Docstrings: imperative first-line summary; module docstrings state the trust model and claim scope (see `bend/adapter.SCOPE`).

**Bend** (full discipline in `.omp/rules/bend-lang.md`; read before touching any `.bend` file):

- File taxonomy: `name.bend` implementation; `name_spec.bend` independent specification sharing no code (only datatypes); `name_laws.bend` `law` statements; `name_proof.bend` `def Laws.<name>` proofs; `NAME.bend` (caps) standalone CPU entry printing one text wire protocol.
- `LAWS.bend` is the human-controlled contract: never weaken, narrow, or vacuate a law to make verification succeed; specs stay independent of implementations.
- Affine ownership: at most one use per resource with one unambiguous ownership flow; never `List.take` + `List.drop` on the same binding; never add `@unsafe` or blanket `+` to silence the checker.
- No linked lists for array-shaped work; balanced fork-join trees (`l r = build(...) build(...)`) with 2^p leaves; expose real parallelism; lists only at wire boundaries.
- Proofs cover the Bend model only — never claim the Python/CUDA implementation is proved without an explicit refinement argument. Performance claims require measured evidence on optimized artifacts.

**Cross-cutting patterns:**

- Geometry constants (context 262144 / pool 263168 / page 128) are deliberately duplicated in `control.bend`, `spec.bend`, `range.bend`, `LAWS.bend`, `bend/adapter.py`, and `serve/entrypoint.sh` — a context change is a coordinated cross-cutting rewrite, not a constant edit.
- Everything is hash-bound: editing any `bend/*.bend|py|cu` file (including `adapter.py`, `native.py`, `native.cu`) invalidates retained `/opt/qwen/bend` artifacts until the Docker generate → compile → verify → native-build chain reruns.
- Wire protocols are exact text with pinned headers (`QWEN_KVARN_PLAN_V2`, `QWEN_OBJECTIVE_POLICY_V1`, `QWEN_DFLASH_GREEDY_V1`, `QWEN_RUNTIME_CONTROL_V1`).
- The Bend policy/planner layer is engine-agnostic by construction (plain text wires + checked policies); an engine swap should consume the same checked artifacts rather than bypass them.

## Important Files

- `README.md` — recipe and status; `LAWS.bend` / `PROOF.bend` — the correctness contract and its proof.
- `bend/adapter.py` — proof/compile pipeline and checked startup APIs (`checked_plan`, `checked_speculation`, ...).
- `patches/source.env` + `baseline.series` / `experimental.series` — the current engine's pin and patch layer; `patches/NOTES.md` — provenance.
- `serve/entrypoint.sh` / `serve/qualification.py` — fail-closed launch and evidence gates.
- `docker-compose.yml` / `Dockerfile` — canonical deployment and image build.
- `docs/README.md` — documentation index; `docs/development.md`, `docs/qualification.md`, `docs/benchmarks.md`, `docs/decode-bottlenecks.md` are the operative protocol docs.
- `prepare/REPRODUCE.md` — offline model reproduction gates.
- `.omp/rules/bend-lang.md`, `.omp/rules/native-262144-low-qty-only.md` — binding agent rules.

## Runtime/Tooling Preferences

- **Nix pins all dev tools** (`flake.nix`): Python 3.13 (repo) / 3.12 (eval), uv 0.12.1, ruff `==0.16.7`, ty `==0.0.80`, clang-19, Bend 2.0.20. Never install tools into a global or agent Python; never bypass the dev shell.
- **Bend is the pinned source-mode 2.0.20 only** (`nix/bend.nix`, `nix run .#bend`): release ELF executing hash-pinned TypeScript via `BUN_BE_BUN` plus one reviewed stack-safe comparator patch. `adapter.generate` rejects any other bend; use `bend version` (not `--version`); resolve once via `command -v bend` and use that same executable throughout.
- **uv** always with `--locked --no-managed-python`; `eval/` is a separate locked project — never mix its environment with the root's (eval scripts deliberately unset inherited `PYTHONPATH`/`PYTHONHOME`).
- **Docker owns runtime; Nix is an adapter**: `nix/compose.nix` publishes the root compose file verbatim; there is no second launch recipe.
- Use the Git-backed `.` flake reference, never `path:.` (it snapshots multi-GB ignored data into the store); new files referenced by the flake must be git-tracked first.

## Testing & QA

There is **no test suite by design** (`eval/validation.md`: "No repository test suite is configured"). Correctness is enforced through evidence harnesses — each run is its own test and rejects as a whole on any validation mismatch:

- `patches/qualification/*.py` — GPU parity/regression fixtures, orchestrated by `python -m bench.numerical` (rmse vs PyTorch oracle, sanitizer-clean).
- `bench/decode.py`, `bench/capacity.py`, `bench/cache.py` — self-validating diagnostics: identity-before/after, raw per-request evidence, `failure.json` on rejection, exclusive output dirs.
- `prepare/verify-models.py`, `prepare/packed-forward-check.py`, `sha256sum --strict --check preparation.sha256` — byte-exact artifact authentication (never update expected hashes to accept a mismatch).
- `eval/scripts/run smoke|quick|full [--dry-run]` — frozen Prime Envs profiles (greedy, 32768 budget, pinned upstreams in `eval/prime-envs.lock`); all runs `--no-push`, traces stay private.
- Pre-commit gates: `bend PROOF.bend` (Bend changes), ruff + ty (Python), ShellCheck (shell).

Hard rules an assistant must never break:

- Never claim a measurement, speedup, capacity result, or quality score that was not actually run and admitted; incomplete evidence is incomplete, never zero or a tie.
- Never report file-search/agentic environment results as direct-context capacity evidence.
- Never weaken laws, guards, allocations, or checks to make a run pass; never silently downsize context or pool; a runtime rejection is inconclusive, never retried smaller.
- Never flush a shared production endpoint, start/stop serving from eval or bench, put keys in argv/logs/Git, or benchmark beside confounding GPU/CPU work.
- Engine comparisons (including non-SGLang stacks) must use the same frozen runner config for every arm; numbers across config changes are never compared or merged.
- Known doc discrepancy: `nix/STANDALONE.md` says canonical `mem-fraction-static` is 0.94; the code default is **0.98** (compose, entrypoint, and docs/docker.md agree) — treat 0.98 as authoritative.
