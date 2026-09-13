{
	config,
	lib,
	pkgs,
	username,
	utils,
	...
}:

let
	cfg = config.workstation.qwenInference;
	stateRoot = cfg.stateRoot;
	stateRootParent = builtins.dirOf stateRoot;
	port = cfg.port;
	requiredMountPoint = cfg.requiredMountPoint;
	# A failed condition would skip the unit without applying Restart=.
	mountPreflight = lib.optionalString (requiredMountPoint != null) ''
		if ! ${pkgs.util-linux}/bin/mountpoint -q -- ${lib.escapeShellArg requiredMountPoint}; then
			echo "Required Qwen filesystem is not mounted; retrying later." >&2
			exit 1
		fi
	'';
	qwenCompose = import ./compose.nix {
		inherit pkgs lib stateRoot port;
		model = cfg.model;
	};
	qwenPrepare = pkgs.writeShellApplication {
		name = "qwen-inference-prepare";
		runtimeInputs = [
			pkgs.coreutils
			pkgs.openssl
		];
		text = ''
      ${mountPreflight}
      for _ in {1..60}; do
        [[ -d ${lib.escapeShellArg stateRoot} ]] && break
        sleep 1
      done
      [[ -d ${lib.escapeShellArg stateRoot} ]] || {
        echo "Qwen state root was not created by qwen-inference-state-dirs.service." >&2
        exit 1
      }
      for path in ${lib.escapeShellArg stateRoot} \
        ${lib.escapeShellArg "${stateRoot}/models"} \
        ${lib.escapeShellArg "${stateRoot}/cache"}; do
        if [[ -L "$path" ]]; then
          printf 'refusing symlinked Qwen state path: %s\n' "$path" >&2
          exit 1
        fi
        install -d -m 0700 "$path"
      done
      if [[ ! -s ${lib.escapeShellArg "${stateRoot}/api-key"} ]]; then
        umask 077
        openssl rand -hex 32 >${lib.escapeShellArg "${stateRoot}/api-key.tmp"}
        mv ${lib.escapeShellArg "${stateRoot}/api-key.tmp"} ${lib.escapeShellArg "${stateRoot}/api-key"}
      fi
      chmod 0600 ${lib.escapeShellArg "${stateRoot}/api-key"}
    '';
	};
	ensureQwenDirs = ''
    set -euo pipefail
    ${mountPreflight}
    owner=${lib.escapeShellArg username}
    for path in ${lib.escapeShellArg stateRoot} \
      ${lib.escapeShellArg "${stateRoot}/models"} \
      ${lib.escapeShellArg "${stateRoot}/cache"}; do
      if [[ -L "$path" ]]; then
        printf 'refusing symlinked Qwen state path: %s\n' "$path" >&2
        exit 1
      fi
      ${pkgs.coreutils}/bin/install -d -m 0700 -o "$owner" -g users "$path"
    done
  '';
in
{
	options.workstation.qwenInference = {
		enable = lib.mkEnableOption "Qwen3.8-27B SGLang inference";

		stateRoot = lib.mkOption {
			type = lib.types.externalPath;
			default = "/srv/ai/models/qwen3.8-27b";
			description = "Qwen3.8-27B model and inference cache directory.";
		};

		requiredMountPoint = lib.mkOption {
			type = lib.types.nullOr lib.types.externalPath;
			default = null;
			description = "Mount point that must be active before Qwen inference starts.";
		};

		port = lib.mkOption {
			type = lib.types.port;
			default = 18020;
			description = "Loopback port for the Qwen OpenAI-compatible API.";
		};

		model = lib.mkOption {
			type = lib.types.str;
			default = "qwen3.8-27b";
			readOnly = true;
			description = "Model name exposed by the inference server.";
		};
	};

	config = lib.mkIf cfg.enable {
		virtualisation.docker.rootless.daemon.settings.features.cdi = true;
		systemd.services.qwen-inference-state-dirs = {
			description = "Create Qwen inference state and credentials";
			# If a required mount starts late, request directory provisioning again.
			wantedBy = [ "multi-user.target" ] ++ lib.optional (requiredMountPoint != null)
				"${utils.escapeSystemdPath requiredMountPoint}.mount";
			startLimitIntervalSec = 0;
			after = [ "local-fs.target" ];
			before = [
				"systemd-user-sessions.service"
			];
			unitConfig.RequiresMountsFor = [ stateRoot ] ++ lib.optional (requiredMountPoint != null) requiredMountPoint;
			serviceConfig = {
				Type = "oneshot";
				RemainAfterExit = true;
				Restart = "on-failure";
				RestartSec = "20s";
			};
			script = ''
				${ensureQwenDirs}
				${pkgs.util-linux}/bin/runuser -u ${lib.escapeShellArg username} -- \
					${qwenPrepare}/bin/qwen-inference-prepare
			'';
		};
		systemd.user.services.qwen-inference = {
			description = "Qwen3.8-27B SGLang inference";
			wantedBy = [ "default.target" ];
			wants = [ "docker.service" ];
			# Retry transient failures indefinitely; every attempt reruns all guards.
			startLimitIntervalSec = 0;
			after = [
				"docker.service"
				"network-online.target"
			];
			path = [ pkgs.docker-compose (config.hardware.nvidia.package.bin or config.hardware.nvidia.package) ];
			serviceConfig = {
				Type = "notify";
				NotifyAccess = "all";
				KillMode = "mixed";
				Environment = [
					"DOCKER_HOST=unix://%t/docker.sock"
					"QWEN_COMPOSE=${qwenCompose}"
					"QWEN_SUPERVISOR=${../serve/supervisor.py}"
				];
				ExecStartPre = [ "${qwenPrepare}/bin/qwen-inference-prepare" ];
				ExecStart = "${pkgs.python3}/bin/python3 ${../serve/launch.py} --state-root ${lib.escapeShellArg stateRoot} --port ${toString port} --systemd";
				# Only the lock-owning launcher may clean up the Compose project.
				Restart = "always";
				RestartPreventExitStatus = [ 78 ];
				RestartSec = "20s";
				TimeoutStartSec = "45min";
				TimeoutStopSec = "2min";
				NoNewPrivileges = true;
				PrivateTmp = true;
				ProtectHome = "read-only";
				ProtectSystem = "strict";
				ReadWritePaths = [
					stateRootParent
					"%t"
				];
				UMask = "0077";
			};
		};

	};
}
