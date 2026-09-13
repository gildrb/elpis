# Standalone Nix integration

The packaged 65,536-token profile is the qualified baseline, not the final
context target. The requested 245,760-token SGLang target remains unqualified.
Keep candidate settings isolated until runtime and quality qualification; this
packaging change does not claim that target is achieved.

1. Use a reviewed, immutable revision of this repository and its committed
   `flake.lock`. Run `nix flake check path:. --no-write-lock-file`, then
   `nix develop path:.`. Flakes must be enabled in Nix. The shell and checks target
   `x86_64-linux`; they do not configure a GPU or start Docker. `path:.` also
   includes new local files before they are tracked by Git; use a clean reviewed
   checkout for reproducibility.
2. Import `nixosModules.qwen-inference` into your existing NixOS host to retain
   full ownership of prerequisites. Alternatively import `nixosModules.reference`
   for the rootless Docker, CDI and lingering-user wiring below. Pass the account
   name as `specialArgs.username`. Do not import both modules separately.
3. Configure and validate the host's NVIDIA driver, GPU selection, filesystem
   mounts and policy. Provision the exact retained models separately, following
   `prepare/REPRODUCE.md`. Serving never downloads or converts missing models.
4. Build your complete host configuration without activation. Preserve a verified
   rollback generation and artifacts. Activate only after separate approval and
   the host's deployment gates. Start the generated user service, not a direct
   Compose invocation: the prepare phase must verify original image source.

Model acquisition and installation are separate user tasks. This repository
reproduces the pinned serving recipe and stack once the user supplies the exact
manifest-qualified models. It is not a model download/install tool. The startup
guards still reject missing or changed model bytes.

## Consumer flake wiring

Replace `<reviewed-inference-commit>` with a real reviewed commit. This is a
fragment for an existing host flake, not a bootable configuration:

```nix
{
  inputs.inference.url = "github:gildrb/inference/<reviewed-inference-commit>";
  # To use this repository's exact validated package set:
  inputs.nixpkgs.follows = "inference/nixpkgs";

  outputs = { nixpkgs, inference, ... }: {
    nixosConfigurations.gpu-host = nixpkgs.lib.nixosSystem {
      system = "x86_64-linux";
      specialArgs.username = "qwen";
      modules = [
        ./hardware-configuration.nix
        ./configuration.nix
        inference.nixosModules.reference
        {
          workstation.qwenInference = {
            stateRoot = "/mnt/models/qwen3.8-27b";
            requiredMountPoint = "/mnt/models";
          };
        }
      ];
    };
  };
}
```

The host must actually define and mount `/mnt/models`. `reference.nix` creates a
normal `qwen` account with linger, enables rootless Docker and NVIDIA Container
Toolkit, and enables serving. For an existing user, set `username` to that user
and check its subordinate UID/GID ranges and access to the state directory.
NixOS user units can be visible to other users; use the intended account's user
manager and protect its state. The reference does not configure login credentials,
SSH access, disks, bootloader, networking, `system.stateVersion`, or GPU drivers.

## Host requirements and boundaries

- Use Linux/NixOS with a working NVIDIA kernel driver compatible with the pinned
  SGLang image's CUDA runtime. Nix installed on macOS alone cannot serve this CUDA
  workload. The qualified GPU is an RTX 3090 with 24 GB VRAM. The generated
  deployment selects CDI `nvidia.com/gpu=0`; confirm GPU 0 is the intended card.
- The known consumer uses `services.xserver.videoDrivers = [ "nvidia" ]`,
  `hardware.nvidia.open = true`, modesetting, GSP, and the kernel package set's
  stable NVIDIA driver. These are observations, not settings imposed by this
  serving module. Driver choice, kernel compatibility, suspend/resume, fan
  settings and the qualified 280 W cap remain host-owned. The package pin alone
  does not pin the running host kernel, driver or firmware.
- Rootless Docker must run under the serving user's systemd manager with linger,
  subordinate UID/GID ranges, cgroup resource control, and a generated NVIDIA CDI
  specification accessible to the daemon. The service uses
  `unix://%t/docker.sock`; a rootful Docker daemon is not a substitute. Check the
  NVIDIA Container Toolkit CDI generator and `nvidia-smi` on the host first.
- Keep enough host RAM and disk for the models, container image and compilation
  cache. The deployment sets 48 GB container memory limits and 32 GB shared
  memory; these are not a measured total host-memory minimum. Keep GPU memory
  free before startup. State contains credentials and must remain private.
- The check builds generated service units and their referenced scripts,
  configuration and verified source overlay. It does not run GPU inference,
  download the container or model weights, validate a full bootable host closure,
  exercise rootless runtime permissions, or establish benchmark results. Initial
  evaluation/build can fetch pinned nixpkgs and binary dependencies. The three
  original source files and local patch diffs are vendored; all original, patch
  and generated replacement hashes are checked against their manifest.

The lock starts from the consumer's inspected nixpkgs revision
`d482ef84049d9b7276b83a06e4e4d76983830097`. If the consumer instead overrides
`inference.inputs.nixpkgs.follows`, repeat closure and runtime qualification:
that override replaces this repository's package pin. The image, reviewed source
and artifact identities remain pinned separately by the serving module and
manifests. See `README.md` and `docs/qualification.md` for their exact qualification limits.

## Supervised readiness and recovery

The user unit reports `active` only after the supervisor receives HTTP 200 from
`/health` and verifies the expected model in the authenticated `/v1/models`
response. Readiness has a 20-minute supervisor deadline within the unit's
45-minute startup timeout. The startup path still runs all source and model
guards before launching inference.

The pinned SGLang health endpoint generates one token when idle, or accepts
scheduler progress when busy. These probes can wake an idle server and are not
zero-work power measurements. The server allows 300 seconds without progress;
the supervisor bounds each complete health/API probe to 310 seconds. After
readiness it probes every 30 seconds and restarts after three consecutive
failures. Detection of a no-progress hang can take roughly 16–17 minutes,
followed by container cleanup, a 20-second retry delay and guarded startup.
This is a conservative recovery policy, not immediate failover or a guarantee
for every long-running workload.

There is no Compose healthcheck and no Docker `healthy` label to inspect.
Use the generated systemd user unit's status and journal. Supervisor failure
triggers container cleanup and a complete guarded restart; a failed guard is
never bypassed. Transient mount/start failures retry, but missing models,
invalid credentials or broken host prerequisites still need operator action.
A manual stop remains stopped.

This supervision change has CPU closure/build validation only. It has not been
activated or live-qualified on the GPU; prior benchmark evidence does not prove
its readiness, idle-power or fault-recovery behavior.

## Foreground serving with Nix (Linux)

Supply the exact model directories, a nonempty private `api-key` file, and an
empty/private `cache` directory under a canonical absolute state root. The state
root, `models` and `cache` must belong to the caller and have mode 0700; `api-key`
must be a regular caller-owned file with mode 0600. Model installation and key
provisioning are separate from the launcher. Rootless Docker/CDI and the host
`nvidia-smi` must already work.

```sh
nix run path:.#serve -- --help
# Starts GPU serving; execute only after explicit approval and provisioning:
nix run path:.#serve -- --state-root /absolute/private/qwen-state
```

The foreground controller uses the same `nix/compose.nix` as the NixOS module.
It verifies original image source and supplied models, waits for free GPU memory,
launches the fixed profile, and uses the same authenticated health supervisor.
Failed attempts clean up and retry after 20 seconds with all guards repeated.
Ctrl-C/SIGTERM cleans up the deployment. Do not run this alongside the NixOS
service or another controller: stop the previous owner first. All supported launchers acquire the same private
`STATE/qwen-inference-launch.lock` inode before touching containers. Nix creates
it only if absent; Docker requires it to be provisioned first. Never unlink or
replace that lock while a deployment can exist. An active lock owner blocks
another launcher. Once acquired, the controller cleans up a prior failed
Compose attempt before starting a new one.

`nix build path:.#deployment` exposes the generated Compose file for inspection.
Its state-root substitution is supplied by the controller. Direct Compose startup
is not the guarded foreground entrypoint. The Nix app is client-independent and
needs no dotfiles repository. It does not install drivers, alter GPU power, fetch
models, or install itself as a background service.

The NixOS adapter now invokes this same lock-owning controller with systemd
notification enabled. It does not run unconditional Compose cleanup hooks.
Cleanup failures retain the lock and retry without preparing another attempt.
Stop signals are deferred during bounded cleanup. A failed final cleanup returns
failure and requires operator action; it is never reported as a successful stop.

### Controller isolation

Supported Nix foreground and NixOS controllers first acquire a private lifetime
lock at `$XDG_RUNTIME_DIR/qwen-inference-controller.lock`, excluding another
supported Nix controller on the same user's rootless Docker daemon even when
state roots differ. They also acquire `STATE/qwen-inference-launch.lock` for
agreement with Docker delivery using that same state. Neither file is unlinked.
The Nix Compose project is `qwen-inference-` plus SHA256 of the canonical absolute
state path. Cleanup therefore addresses only that state's generated project.

These locks do not arbitrate every Docker process or GPU user. Docker delivery
with another state, another account/daemon, or a manual project-name override
is outside that exclusion. Keep one serving deployment per GPU; GPU-memory
preflight and the fixed foreground port prevent some conflicts but are not a
host-wide GPU reservation system. Stop unsupported competing deployments first.

### Migration from the former fixed project name

An existing deployment may still use the fixed Compose project name
`qwen-inference`. The new state-derived project deliberately does not clean it
up. Before the first new launch or approved activation, stop the old guarded
deployment through its own service and original configuration. Preserve that
configuration, artifacts and a verified rollback generation. Do not work around
a conflict by automatically stopping a foreign project or bypassing the GPU
preflight. The current live service is unchanged by these repository edits.
Consumer closure/build compatibility is not activation or live recovery proof.

### Bounded process cleanup limits

The launcher defers parent stop signals while it records a spawned process and
while cleanup runs; exec children do not inherit blocked stop-signal masks.
Exceptional command cleanup allows 10 seconds after TERM and another 10 seconds
after KILL. It checks both owned output/leader completion and process-group
absence. If cleanup remains incomplete, it fails explicitly instead of reporting
success or starting another serving attempt. An uninterruptible OS process or an
unresponsive Docker daemon can still require operator recovery. These deadlines
are not a guarantee that GPU memory is released or every container is removed.

Incomplete owned process-group cleanup exits with reserved status 78. The NixOS
unit excludes that status from automatic restart; other failures retain their
ordinary retry policy. Before an explicit restart, verify the old command group
and deployment state, complete any required operator cleanup, and confirm GPU
availability. This policy does not guarantee recovery after SIGKILL or host crash,
and does not prove that GPU memory has been released.
