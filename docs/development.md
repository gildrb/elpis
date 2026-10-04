# Strict Python development

Use the pinned Nix dev shell and its Python 3.13. uv owns the project
virtual environment and lock. Do not install tools in an agent/global Python.
Use the Git-backed `.` flake reference for development. `path:.` includes ignored
evaluation datasets and caches in its source snapshot, which can be many GB.
New files referenced by the flake must be tracked before Git-backed evaluation;
do not stage unrelated user changes. Evaluation scripts run from the checkout
and are not embedded in the development shell.

```console
nix develop . --no-write-lock-file -c uv sync --locked --python python3.13 --no-managed-python
nix develop . --no-write-lock-file -c uv run --locked --python python3.13 --no-managed-python ruff check .
nix develop . --no-write-lock-file -c uv run --locked --python python3.13 --no-managed-python ruff format --check .
nix develop . --no-write-lock-file -c uv run --locked --python python3.13 --no-managed-python ty check .
```

Add `--offline` after `uv run` once the locked environment is available.
Ruff 0.16.7 and ty 0.0.80 are exact development pins. Serving runtime pins are separate from the upstream evaluation environment
pins described in [eval/README.md](../eval/README.md).

## Policy

Ruff selects ALL rules, including preview rules, targets Python 3.13 and
formats docstring code. Rule names are used because the pinned Ruff's
RUF201 rejects rule codes in selectors. ty sets every diagnostic to error
and treats any remaining warning as a failed check. The installed ty has
`--error all` and `--error-on-warning`; it has no `--strict` switch.
These settings do not prove that every dynamic Python boundary is typed.

The only lint choices are mutually exclusive docstring conventions and
formatter-owned styles. D211 (no blank line before class docstrings) wins
over D203; D212 (summary on first line) wins over D213. Following the pinned
Ruff rule documentation's formatter-compatibility advice, the formatter owns
indentation (E111, E114, E117, W191, D206), quotes (D300, Q000, Q001, Q002,
Q003), and trailing commas (COM812, COM819). Their named lint counterparts
are disabled, not source-level errors. ISC001 and ISC002 remain enabled;
the default multiline concatenation setting is formatter-compatible.
No file exclusions, per-file exemptions, type ignores or diagnostic
suppression directives are added.

## Scope and honest failures

Run checks read-only before editing. Default checks cover authored Python.
Canonical serving uses the existing immutable EXL3 engine image plus the baked
`serve/exl3_server.py`, not runtime source overlays. The guarded
`docker/build-exl3.sh` `baseline` build preserves that engine (`candidate` applies
the SHA-pinned `patches/exl3` series) and adds the hash-pinned
JSON Schema dependencies in `serve/exl3-requirements.txt`. The Python runtime
inside that image is separate from the repository's development environment.

The CPU development environment does not install serving torch, EXL3 or
transformers. Missing imports remain explicit environment blockers, not ignored
rules. Validate authored runtime modules in their separately pinned image before
claiming complete type coverage. Bend sources are checked with the pinned
`.#bend` toolchain (see [README, Prove](../README.md#prove)), not the Python gates;
`nix run .#bend-verdict -- PROOF.bend --verdict` rechecks them with Bend's
Lean-proven kernel (same Bend, plus the pinned Lean 4.34.0 from `nix/lean4.nix`).

Upstream evaluation environments use their separate setup and locked
dependencies under `eval/`. Keep full check logs private and group authored
findings by file when assigning cleanup. Do not claim passing quality gates
while diagnostics remain.
