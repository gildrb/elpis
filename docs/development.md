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
`.#bend` toolchain (see [AGENTS.md](../AGENTS.md)), not the Python gates;
`nix run .#bend-verdict -- PROOF.bend --verdict` rechecks them with Bend's
Lean-proven kernel (same Bend, plus the pinned Lean 4.34.0 from `nix/lean4.nix`).

Upstream evaluation environments use their separate setup and locked
dependencies under `eval/`. Keep full check logs private and group authored
findings by file when assigning cleanup. Do not claim passing quality gates
while diagnostics remain.

## EXL3 cutover verification status

The original serving-1 cutover passed runtime CPU protocol proof and a real
authenticated EXL3 named-tool addition/continuation, buffered tool SSE,
authentication, model identity, schema-error handling and post-promotion health.
Its evidence remains intact. The current serving-2 image adds top-level
`reasoning_effort` compatibility without changing nested OMP controls or transport.
See [deployment evidence](docker.md#current-persistent-live-deployment) for exact
identities and private receipt locations.

Serving-2's guarded build passed (1.43 s), as did CPU reasoning (0.78 s),
protocol (0.81 s), all 30 actual gateway schemas (0.71 s) and admission of the
entire actual Telegram gateway request, including full history (0.70 s, 30 tools).
That CPU admission did not generate or print private text. Real client proofs
against the new image:

- Hermes gateway 0.21.3: the original HTTP 400 was fixed; terminal execution
  `139 + 207` and continuation returned `346` (11.43 s), with the database
  tool-call/result ID pair verified.
- Interactive Hermes 0.21.4: terminal execution `137 + 205` and continuation
  returned `342` (32.31 s).
- OMP 18.2.11: its normal native tool catalog read `/etc/os-release` and returned
  NixOS (30.09 s).
- Telegram `getMe` and `getWebhookInfo` passed for `@gdrb_gatewaybot`, with no
  webhook and zero pending updates. `getChat` verified the exact existing
  allowlisted private recipient. The native Hermes sender delivered exactly
  one approved check (2.88 s), with its message ID confirmed. The gateway status
  socket reported PID 3655, Telegram connected and no attention required.
  No second poller was started or token disclosed.
  **A fresh inbound user-to-bot exchange remains unexercised**; outbound delivery
  is not a full ingress roundtrip.

These elapsed times are smoke observations, not benchmarks. Client selection,
host-only routing and the unactivated Hermes overlay are documented under
[host client routing](docker.md#host-client-routing).

These proofs do not establish full-context capacity, model quality, throughput
or genuine incremental streaming; SSE remains buffered until generation finishes.
`py_compile` and pinned Ruff format checks passed. These do not make the
development gates clean: **Ruff ALL style findings remain**, including
same-policy findings on new strings/complexity. The current host ty check reports
12 unresolved imports for container-only dependencies (`jinja2`, `jsonschema`,
`referencing`, `torch`, `exllamav3`), not a clean typecheck. Runtime ty was not
rerun; its previously reported **upstream torch bare `inference_mode` typing
issue** remains a historical known limitation. No suppression was added. Report
remaining diagnostics alongside runtime proof, not as all checks passed.

The Nix deployment and standalone launcher builds passed. The example
`serving-units` build remains unverified: uncached systemd dependencies required
source downloads, which timed out. This did not affect the running Docker service.

The host-owned Hermes overlay passed `nix-instantiate --parse`, not OS activation.
Its `nixfmt --check` failed on the mixed-format existing file; unrelated content
was not reformatted.
