# Nix development and thin service adapter

Use the Git-backed `.` flake reference from a clean, reviewed checkout. It
includes tracked files only. New flake inputs must be tracked, but do not stage
unrelated user changes. Avoid `path:.`: it copies ignored evaluation caches and
private traces into the Nix source store.

Docker EXL3 is the canonical deployment. Nix pins developer tools and publishes
the same prebuilt-image Compose file; it does not patch runtime sources, generate
a second launch configuration, monitor health, provision keys or manage GPU
memory. The fixed recipe uses native DFlash2, CQ3, context262144 and cache270336.
These are configuration settings, not full-context capacity or quality evidence.

## Development and reproduction

```sh
nix flake check . --no-write-lock-file
nix develop . --no-write-lock-file
nix build .#deployment --no-write-lock-file
```

Checks build the thin launcher and example user unit without activating them.
They do not contact Docker, attach a GPU or qualify image/model/runtime behavior.
The flake pins nixpkgs at `d482ef84049d9b7276b83a06e4e4d76983830097` for
`x86_64-linux`. Consumer overrides replace that tool pin and require rechecking.
See [development](../docs/development.md) and [Docker setup](../docs/docker.md).

## Foreground adapter

Provision the existing private state, EXL3 target/draft, key and persistent lock
as in the Docker guide. Build and review the image first in the intended daemon
using `bash docker/build-exl3.sh baseline qwen-inference:exl3` (or `candidate`). That script authenticates
the required local native base image ID; Compose has no build stanza. Nix never
implicitly builds or pulls the image.

```sh
export QWEN_IMAGE=qwen-inference:exl3
export QWEN_ALLOW_UNQUALIFIED=1
# GPU launch: execute only after exclusive-access approval.
nix run .#serve -- --state-root /absolute/private/qwen-state
```

The app directly executes Compose `up --no-build --pull never` in the foreground.
Ctrl-C delegates stop to Compose. The project name is `qwen-inference`, shared
with the documented Docker commands. Do not run this beside the user service,
a different Compose project or the old deployment. No controller attempts to
identify or remove foreign containers. Use Docker's health status, not process
presence, as readiness evidence. Unhealthy alone does not trigger restart.

## Existing NixOS consumer

The import `nix/qwen-inference.nix`, exported
`nixosModules.qwen-inference`, and `workstation.qwenInference` namespace remain.
The host owns state provisioning, drivers, CDI, rootless Docker, the serving
account and its linger setting. `nixosModules.reference` remains a small optional
rootless-Docker/account wiring example using `specialArgs.username`; it is not
a bootable host and does not configure storage or GPU drivers.

```nix
{
  imports = [ inference.nixosModules.qwen-inference ];
  workstation.qwenInference = {
    enable = true;
    stateRoot = "/mnt/models/qwen-state";
    requiredMountPoint = "/mnt/models";
    image = "qwen-inference:exl3"; # Prefer a reviewed immutable image ID/digest.
    allowUnqualified = true; # Explicit acknowledgment, not qualification.
  };
}
```

`port` remains a host-loopback mapping option. `model` remains read-only.
The rootless user service consumes `unix://%t/docker.sock`, runs Compose
`up --detach --no-build --pull never --wait --wait-timeout 1200`, and delegates
stop to Compose. Docker owns process restart. Systemd `active (exited)` means
startup completed; it is not continuous readiness. A failed wait may leave a
container running. Inspect Docker before retrying. Manual stop remains stopped.

## Migration boundary

Old automatic directory/key creation, source-overlay preparation, GPU polling,
custom Python health supervision and cleanup/retry loops are removed. Provision
state explicitly; missing bind sources fail closed. The container's persistent
state lock remains. Its protection does not extend to another state or daemon.
Do not activate this adapter over an occupied endpoint. The current live
`qwen-exl3-serving-2` deployment uses its persistent guardian configuration at
`/mnt/ssd/storage/ai/qwen3.8-27b/exl3-serving-2/compose.json`, not this ordinary
Nix launcher. Its guardian gate owns the same launch-lock inode and passes the
lock to the baked EXL3 model launcher. Preserve its promoted window and controls;
do not bypass the gate or launch this adapter beside it. See
[current deployment and evidence](../docs/docker.md#current-persistent-live-deployment).

Static Nix validation is not activation, cold-boot, hang-recovery,
suspend/resume, full-context capacity or model-quality proof. The actual EXL3
authenticated tool roundtrip and health smoke have passed. EXL3 has no runtime
memory-fraction, graph or KV selectors and no automatic fallback.
`allowUnqualified` remains the explicit acknowledgment; it does not bypass
model, credential or ownership guards.
