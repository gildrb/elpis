{
	config,
	lib,
	pkgs,
	...
}:

let
	fallbackPowerLimitPercent = 70;
	powerLimitRules = [
		{
			match = "3060 Ti";
			watts = 120;
		}
		{
			match = "3090";
			watts = 250;
		}
	];
	powerLimitRuleScript = lib.concatMapStringsSep "\n" (rule: ''
    if echo "$gpu_name" | grep -qi -- ${lib.escapeShellArg rule.match}; then
      target_limit=${toString rule.watts}
    fi
  '') powerLimitRules;
	nvidiaPackage = config.hardware.nvidia.package;
	nvidiaTools = nvidiaPackage.bin or nvidiaPackage;
	nvidiaWorkstationReport = pkgs.writers.writeNuBin "nvidia-workstation-report" {
		makeWrapperArgs = [
			"--prefix"
			"PATH"
			":"
			(lib.makeBinPath [
				nvidiaTools
				pkgs.coreutils
				pkgs.systemd
				pkgs.vulkan-tools
			])
			"--set-default"
			"NVIDIA_WORKSTATION_NVIDIA_SMI_COMMAND"
			"${nvidiaTools}/bin/nvidia-smi"
			"--set-default"
			"NVIDIA_WORKSTATION_SYSTEMCTL_COMMAND"
			"${pkgs.systemd}/bin/systemctl"
			"--set-default"
			"NVIDIA_WORKSTATION_JOURNALCTL_COMMAND"
			"${pkgs.systemd}/bin/journalctl"
			"--set-default"
			"NVIDIA_WORKSTATION_VULKANINFO_COMMAND"
			"${pkgs.vulkan-tools}/bin/vulkaninfo"
			"--set-default"
			"NVIDIA_WORKSTATION_NVIDIA_CTK_COMMAND"
			"nvidia-ctk"
			"--set-default"
			"NVIDIA_WORKSTATION_PROC_CMDLINE"
			"/proc/cmdline"
			"--set-default"
			"NVIDIA_WORKSTATION_NVIDIA_DRM_PARAMETERS"
			"/sys/module/nvidia_drm/parameters"
			"--set-default"
			"NVIDIA_WORKSTATION_CDI_SPEC"
			"/run/cdi/nvidia-container-toolkit.json"
		];
	} (builtins.readFile ./nvidia-quiet/report.nu);

	nvidiaPowerMode = pkgs.writeShellApplication {
		name = "nvidia-workstation-power";
		runtimeInputs = [
			nvidiaTools
			pkgs.coreutils
			pkgs.gawk
			pkgs.gnugrep
		];
		text = ''
      usage() {
        printf 'Usage: nvidia-workstation-power [status|quiet|full] [--for SECONDS]\n' >&2
        printf '  status  Show the current GPU power posture.\n' >&2
        printf '  quiet   Apply the declarative quiet power caps.\n' >&2
        printf '  full    Temporarily restore each GPU default power limit, then reapply quiet caps.\n' >&2
        printf '  --for   Full-power window in seconds for full mode; default: 3600.\n' >&2
      }

      status() {
        if ! command -v nvidia-smi >/dev/null 2>&1; then
          echo "nvidia-smi is not available." >&2
          exit 127
        fi

        printf 'NVIDIA power mode status\n'
        nvidia-smi \
          --query-gpu=index,name,persistence_mode,power.draw,power.limit,power.default_limit,temperature.gpu,utilization.gpu \
          --format=csv
      }

      apply_mode() {
        local mode="$1"
        local _current_limit default_limit failed gpu_count gpu_index gpu_name gpu_rows target_limit

        if ! command -v nvidia-smi >/dev/null 2>&1; then
          echo "nvidia-smi is not available; cannot change NVIDIA power mode." >&2
          exit 127
        fi

        gpu_rows="$(nvidia-smi --query-gpu=index,name,power.limit,power.default_limit --format=csv,noheader,nounits)"
        if [[ -z "$gpu_rows" ]]; then
          echo "No NVIDIA GPUs detected; this host config expects NVIDIA GPUs." >&2
          exit 1
        fi

        gpu_count=0
        failed=0
        while IFS=, read -r gpu_index gpu_name _current_limit default_limit; do
          gpu_index="''${gpu_index//[[:space:]]/}"
          gpu_name="''${gpu_name# }"
          default_limit="''${default_limit//[[:space:]]/}"
          target_limit=""
          gpu_count=$((gpu_count + 1))

          case "$mode" in
            quiet)
              ${powerLimitRuleScript}
              if [[ -z "$target_limit" ]]; then
                if [[ "$default_limit" =~ ^[0-9]+([.][0-9]+)?$ ]]; then
                  target_limit="$(awk -v default_limit="$default_limit" -v percent="${toString fallbackPowerLimitPercent}" 'BEGIN { printf "%.0f", default_limit * percent / 100 }')"
                else
                  echo "Could not read the default power limit for $gpu_name." >&2
                  failed=1
                  continue
                fi
              fi
              ;;
            full)
              if [[ "$default_limit" =~ ^[0-9]+([.][0-9]+)?$ ]]; then
                target_limit="$(awk -v default_limit="$default_limit" 'BEGIN { printf "%.0f", default_limit }')"
              else
                echo "Could not read the default power limit for $gpu_name." >&2
                failed=1
                continue
              fi
              ;;
          esac

          if ! nvidia-smi -i "$gpu_index" -pm 1; then
            echo "Could not enable persistence mode for $gpu_name." >&2
            failed=1
            continue
          fi

          if ! nvidia-smi -i "$gpu_index" -pl "$target_limit"; then
            echo "Could not apply ''${target_limit}W power limit to $gpu_name." >&2
            failed=1
            continue
          fi

          printf 'Set %s to %sW (%s mode).\n' "$gpu_name" "$target_limit" "$mode"
        done <<< "$gpu_rows"

        if [[ "$gpu_count" -eq 0 ]]; then
          echo "No NVIDIA GPUs detected; this host config expects NVIDIA GPUs." >&2
          exit 1
        fi

        if [[ "$failed" -ne 0 ]]; then
          exit 1
        fi

        status
      }

      validate_full_power_seconds() {
        local full_power_seconds="$1"
        if [[ ! "$full_power_seconds" =~ ^[1-9][0-9]*$ ]]; then
          printf 'Full-power window must be a positive integer number of seconds: %s\n' "$full_power_seconds" >&2
          exit 2
        fi
      }

      schedule_quiet_revert() {
        local full_power_seconds="$1"
        local unit_name="nvidia-quiet-power-revert"

        validate_full_power_seconds "$full_power_seconds"

        ${pkgs.systemd}/bin/systemctl stop nvidia-quiet-power-limit.timer >/dev/null 2>&1 || true
        ${pkgs.systemd}/bin/systemctl stop "$unit_name.timer" "$unit_name.service" >/dev/null 2>&1 || true
        ${pkgs.systemd}/bin/systemctl reset-failed "$unit_name.timer" "$unit_name.service" >/dev/null 2>&1 || true

        ${pkgs.systemd}/bin/systemd-run \
          --quiet \
          --collect \
          --unit="$unit_name" \
          --on-active="''${full_power_seconds}s" \
          --description="Reapply quiet NVIDIA GPU power limits" \
          ${pkgs.bash}/bin/bash -lc '${pkgs.systemd}/bin/systemctl restart nvidia-quiet-power-limit.service && ${pkgs.systemd}/bin/systemctl start nvidia-quiet-power-limit.timer'

        printf 'Scheduled quiet NVIDIA power caps to reapply in %s seconds.\n' "$full_power_seconds"
      }

      mode="status"
      full_power_seconds="''${NVIDIA_WORKSTATION_FULL_POWER_SECONDS:-3600}"
      full_power_window_set=0
      mode_set=0

      while [[ $# -gt 0 ]]; do
        case "$1" in
          --for)
            if [[ $# -lt 2 ]]; then
              usage
              exit 2
            fi
            full_power_seconds="$2"
            full_power_window_set=1
            shift 2
            ;;
          status | quiet | full)
            if [[ "$mode_set" -eq 1 ]]; then
              usage
              exit 2
            fi
            mode="$1"
            mode_set=1
            shift
            ;;
          -h | --help)
            usage
            exit 0
            ;;
          *)
            usage
            exit 2
            ;;
        esac
      done

      if [[ "$mode" != "full" && "$full_power_window_set" -eq 1 ]]; then
        printf '%s\n' '--for is only valid with full mode.' >&2
        usage
        exit 2
      fi

      case "$mode" in
        status)
          status
          ;;
        quiet)
          if [[ "$EUID" -ne 0 ]]; then
            printf 'Changing NVIDIA power mode requires root. Run: sudo nvidia-workstation-power %s\n' "$mode" >&2
            exit 1
          fi
          apply_mode "$mode"
          ;;
        full)
          if [[ "$EUID" -ne 0 ]]; then
            printf 'Changing NVIDIA power mode requires root. Run: sudo nvidia-workstation-power %s --for %s\n' "$mode" "$full_power_seconds" >&2
            exit 1
          fi
          validate_full_power_seconds "$full_power_seconds"
          apply_mode "$mode"
          schedule_quiet_revert "$full_power_seconds"
          ;;
        *)
          usage
          exit 2
          ;;
      esac
    '';
	};
in
{
  # This is still the NixOS NVIDIA driver selection hook. SDDM uses X11 for the
  # greeter, while the selected Plasma desktop session remains Wayland.
	services.xserver.videoDrivers = [ "nvidia" ];

	hardware.nvidia = {
		modesetting.enable = true;
		moduleParams."nvidia-drm" = {
			modeset = lib.mkForce 1;
			fbdev = lib.mkForce 1;
		};
		open = true;
		gsp.enable = true;
		videoAcceleration = true;
		nvidiaSettings = true;
		nvidiaPersistenced = true;
		package = config.boot.kernelPackages.nvidiaPackages.stable;

    # Keep normal NVIDIA suspend hooks enabled for full-driver behavior, while
    # leaving PRIME runtime D3 off because this desktop is not an offload laptop.
		powerManagement.enable = true;
		powerManagement.finegrained = false;
		powerManagement.kernelSuspendNotifier = true;
	};

  # Load NVIDIA DRM before the display manager starts. The workstation reaches
  # SDDM through a triple-monitor NVIDIA path, so the driver module owns the
  # early KMS contract instead of letting the greeter race late module loading.
	boot.initrd.kernelModules = [
		"nvidia"
		"nvidia_modeset"
		"nvidia_drm"
	];

	boot.kernelParams = [
		"nvidia-drm.modeset=1"
		"nvidia-drm.fbdev=1"
	];

	environment.systemPackages = with pkgs; [
		libva-utils
		nvidiaPowerMode
		nvidiaWorkstationReport
		nvtopPackages.nvidia
		vulkan-tools
	];

	environment.sessionVariables = {
    # The driver package is installed by hardware.nvidia.videoAcceleration; keep
    # user sessions pointed at NVIDIA's NVDEC-backed VA-API path explicitly.
		LIBVA_DRIVER_NAME = "nvidia";
		LIBVA_MESSAGING_LEVEL = "1";
		NVD_BACKEND = "direct";
	};

	powerManagement.resumeCommands = ''
    ${pkgs.systemd}/bin/systemctl restart nvidia-quiet-power-limit.service
  '';

	systemd.timers.nvidia-quiet-power-limit = {
		description = "Reapply quiet NVIDIA GPU power limits";
		wantedBy = [ "timers.target" ];
		timerConfig = {
			OnBootSec = "1min";
			OnUnitInactiveSec = "5min";
			AccuracySec = "1min";
			Persistent = true;
			Unit = "nvidia-quiet-power-limit.service";
		};
	};

	systemd.services.nvidia-quiet-power-limit = {
		description = "Apply quiet NVIDIA GPU power limits";
		wantedBy = [ "multi-user.target" ];
		after = [
			"multi-user.target"
			"nvidia-persistenced.service"
		];
		wants = [
			"nvidia-persistenced.service"
		];

		path = [
			nvidiaTools
			pkgs.coreutils
			pkgs.gawk
			pkgs.gnugrep
		];

		serviceConfig = {
			Type = "oneshot";
		};

		script = ''
      if ! command -v nvidia-smi >/dev/null 2>&1; then
        echo "nvidia-smi is not available; cannot apply NVIDIA power limits." >&2
        exit 1
      fi

      # Persistence mode and power caps target the efficiency knee: materially
      # less heat and fan noise without touching clocks, voltage, memory
      # timings, or fan curves. Model rules win, including a quiet 3090 cap
      # for the headless compute GPU and a quieter 120W cap for the
      # current RTX 3060 Ti; unknown GPUs fall back to a 70% default-limit cap
      # until a more specific rule is declared.
      gpu_rows="$(nvidia-smi --query-gpu=index,name,power.limit,power.default_limit --format=csv,noheader,nounits)"
      gpu_count=0
      failed=0
      while IFS=, read -r gpu_index gpu_name _current_limit default_limit; do
        gpu_index="''${gpu_index//[[:space:]]/}"
        gpu_name="''${gpu_name# }"
        default_limit="''${default_limit//[[:space:]]/}"
        target_limit=""
        gpu_count=$((gpu_count + 1))

        ${powerLimitRuleScript}

        if [[ -z "$target_limit" ]]; then
          if [[ "$default_limit" =~ ^[0-9]+([.][0-9]+)?$ ]]; then
            target_limit="$(awk -v default_limit="$default_limit" -v percent="${toString fallbackPowerLimitPercent}" 'BEGIN { printf "%.0f", default_limit * percent / 100 }')"
          else
            echo "Could not read the default power limit for $gpu_name." >&2
            failed=1
            continue
          fi
        fi

        if ! nvidia-smi -i "$gpu_index" -pm 1; then
          echo "Could not enable persistence mode for $gpu_name." >&2
          failed=1
          continue
        fi

        if ! nvidia-smi -i "$gpu_index" -pl "$target_limit"; then
          echo "Could not apply ''${target_limit}W power limit to $gpu_name." >&2
          failed=1
          continue
        fi
      done <<< "$gpu_rows"

      if [[ "$gpu_count" -eq 0 ]]; then
        echo "No NVIDIA GPUs detected; this host config expects NVIDIA GPUs." >&2
        exit 1
      fi

      if [[ "$failed" -ne 0 ]]; then
        exit 1
      fi

      nvidia-smi --query-gpu=name,power.limit,power.default_limit --format=csv
    '';
	};
}
