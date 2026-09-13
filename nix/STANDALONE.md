# Nix development and thin service adapter

Use the Git-backed `.` flake reference from a clean, reviewed checkout. It
includes tracked files only. New flake inputs must be tracked, but do not stage
unrelated user changes. Avoid `path:.`: it copies ignored evaluation caches and
private traces into the Nix source store.

Docker is the canonical deployment. Nix pins developer tools and publishes the
same root Compose file; it does not patch runtime sources, generate a second
launch configuration, monitor health, provision keys or manage GPU memory.
The candidate objective is **262,144 total tokens with DFlash2**, not a qualified
capacity claim. Historical 64K evidence belongs to the old external deployment.

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

Provision the existing private state, models, key and persistent lock as in the
Docker guide. Build and review the Docker image first in the intended daemon.
Nix never implicitly builds or pulls it.

```sh
export QWEN_IMAGE=qwen-inference:local
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
    image = "qwen-inference:local"; # Prefer a reviewed immutable digest.
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
Do not activate this adapter over the occupied baseline. Stop the old service
through its original configuration only after approval and preserve its rollback
generation, image and artifacts. Static Nix validation is not activation or a
cold-boot, hang-recovery, suspend/resume, capacity or model-quality result.
