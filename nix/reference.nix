# Import with specialArgs.username set to the dedicated serving account.
# This is a host integration example, not a bootable NixOS configuration.
# Driver, kernel, GPU power/fan policy and storage mounts belong to the host.
{ lib, username, ... }:
{
  imports = [ ./qwen-inference.nix ];

  users.users.${username} = {
    isNormalUser = lib.mkDefault true;
    linger = true;
    # NixOS allocates subordinate UID/GID ranges for normal users, required
    # by rootless Docker. An existing account must retain valid ranges.
  };

  virtualisation.docker = {
    enable = lib.mkDefault false;
    rootless = {
      enable = true;
      setSocketVariable = true;
    };
  };
  hardware.nvidia-container-toolkit.enable = true;

  workstation.qwenInference = {
    enable = lib.mkDefault true;
    stateRoot = lib.mkDefault "/srv/ai/models/qwen3.8-27b";
    # Set requiredMountPoint in the host when stateRoot lives on another disk.
  };
}
