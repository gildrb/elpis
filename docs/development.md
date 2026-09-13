# Strict Python development

Use the pinned Nix dev shell and its Python 3.13. uv owns the project
virtual environment and lock. Do not install tools in an agent/global Python.

```console
nix develop path:. --no-write-lock-file -c uv sync --locked --python python3.13 --no-managed-python
nix develop path:. --no-write-lock-file -c uv run --locked --python python3.13 --no-managed-python ruff check .
nix develop path:. --no-write-lock-file -c uv run --locked --python python3.13 --no-managed-python ruff format --check .
nix develop path:. --no-write-lock-file -c uv run --locked --python python3.13 --no-managed-python ty check .
```

Add `--offline` after `uv run` once the locked environment is available.
Ruff 0.16.7 and ty 0.0.80 are exact development pins. Existing runtime,
Reasoning Gym Git revision and build-tool pins remain unchanged.

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

Run checks read-only before editing. Default checks include authored Python
and vendored `patches/base` source. The latter is hash-authenticated upstream
input, not a cleanup target. Report its diagnostics separately; never format
or modify those bytes to obtain a green check. The CPU benchmark environment
also does not install the serving image's torch, safetensors,
compressed-tensors or SGLang dependencies. Missing imports in conversion and
vendored runtime files remain explicit environment blockers, not ignored
rules. Validate those modules in their separately pinned runtime before
claiming complete type coverage.

Private benchmark banks, source snapshots, commitments and producer locks
remain frozen. A changed project lock cannot replace their recorded identity.
Keep full check logs private and group authored findings by file when assigning
cleanup. Do not claim passing quality gates while diagnostics remain.
