{
	config,
	lib,
	pkgs,
	username,
	...
}:

let
	cfg = config.workstation.qwenInference;
	stateRoot = cfg.stateRoot;
	stateRootParent = builtins.dirOf stateRoot;
	port = cfg.port;
	requiredMountPoint = cfg.requiredMountPoint;
	sglangImage = "lmsysorg/sglang:v0.5.19@sha256:d6e7288627be8b02be88e4bba38e73f6d50e2826869f753c13a4c4385ab3eda9";
	sglangEntrypoint = ./sglang-entrypoint.sh;
	qwenCompose = (pkgs.formats.yaml { }).generate "qwen-inference-compose.yaml" {
		services = {
			prepare = {
				image = sglangImage;
				entrypoint = [
					"bash"
					"/sglang-entrypoint"
				];
				command = [ ];
				pull_policy = "missing";
				environment = {
					DO_NOT_TRACK = "1";
					HF_HUB_DISABLE_TELEMETRY = "1";
					HOME = "/cache";
					MODELS_DIR = "/models";
					PREPARE = "1";
				};
				volumes = [
					"${stateRoot}/models:/models"
					"${stateRoot}/cache:/cache"
					"${sglangEntrypoint}:/sglang-entrypoint:ro"
				];
				deploy.resources.limits = {
					cpus = "8";
					memory = "48G";
				};
			};
			inference = {
				image = sglangImage;
				entrypoint = [
					"bash"
					"/sglang-entrypoint"
				];
				command = [ ];
				pull_policy = "missing";
				stop_grace_period = "60s";
				shm_size = "32gb";
				read_only = true;
				cap_drop = [ "ALL" ];
				security_opt = [ "no-new-privileges:true" ];
				tmpfs = [
					"/run:rw,noexec,nosuid,size=64m"
					"/tmp:rw,noexec,nosuid,size=2g"
				];
				ports = [ "127.0.0.1:${toString port}:${toString port}" ];
				environment = {
					API_KEY_FILE = "/app/api_key.txt";
					DO_NOT_TRACK = "1";
					HF_HUB_DISABLE_TELEMETRY = "1";
					HOME = "/cache";
					MODELS_DIR = "/models";
					PORT = toString port;
					PREPARE = "0";
					SERVED_MODEL_NAME = cfg.model;
				};
				volumes = [
					"${stateRoot}/models:/models:ro"
					"${stateRoot}/cache:/cache"
					"${stateRoot}/api-key:/app/api_key.txt:ro"
					"${sglangEntrypoint}:/sglang-entrypoint:ro"
				];
				deploy.resources = {
					limits = {
						cpus = "8";
						memory = "48G";
					};
					reservations.devices = [
						{
							driver = "cdi";
							device_ids = [ "nvidia.com/gpu=0" ];
							capabilities = [ "gpu" ];
						}
					];
				};
				healthcheck = {
					test = [
						"CMD"
						"python3"
						"-c"
						"import urllib.request; urllib.request.urlopen('http://127.0.0.1:${toString port}/health')"
					];
					interval = "30s";
					timeout = "5s";
					retries = 3;
					start_period = "20m";
				};
			};
		};
	};
	qwenPrepare = pkgs.writeShellApplication {
		name = "qwen-inference-prepare";
		runtimeInputs = [
			pkgs.coreutils
			pkgs.openssl
		];
		text = ''
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
      umask 077
      printf 'QWEN_API_KEY=%s\n' "$(cat ${lib.escapeShellArg "${stateRoot}/api-key"})" \
        >${lib.escapeShellArg "${stateRoot}/hermes.env.tmp"}
      mv ${lib.escapeShellArg "${stateRoot}/hermes.env.tmp"} ${lib.escapeShellArg "${stateRoot}/hermes.env"}
      chmod 0600 \
        ${lib.escapeShellArg "${stateRoot}/api-key"} \
        ${lib.escapeShellArg "${stateRoot}/hermes.env"}
    '';
	};
	qwenWaitGpu = pkgs.writeShellApplication {
		name = "qwen-inference-wait-gpu";
		runtimeInputs = [
			pkgs.coreutils
			(config.hardware.nvidia.package.bin or config.hardware.nvidia.package)
		];
		text = ''
      for _ in {1..60}; do
        used="$(nvidia-smi --query-gpu=memory.used --format=csv,noheader,nounits | head -n 1)"
        if [[ "$used" =~ ^[0-9]+$ ]] && (( used < 1000 )); then
          exit 0
        fi
        sleep 2
      done
      echo "GPU memory did not become free before Qwen startup." >&2
      exit 1
    '';
	};
	qwenHealth = import ./qwen-inference-health.nix {
		inherit
			lib
			pkgs
			port
			stateRoot
			;
	};
	ensureQwenDirs = ''
    set -euo pipefail
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
			wantedBy = [ "multi-user.target" ];
			after = [ "local-fs.target" ];
			before = [
				"hermes-agent.service"
				"systemd-user-sessions.service"
			];
			unitConfig.RequiresMountsFor = [ stateRoot ];
			serviceConfig = {
				Type = "oneshot";
				RemainAfterExit = true;
			};
			script = ''
				${ensureQwenDirs}
				${pkgs.util-linux}/bin/runuser -u ${lib.escapeShellArg username} -- \
					${qwenPrepare}/bin/qwen-inference-prepare
			'';
		};
		environment.systemPackages = [ qwenHealth ];
		systemd.user.services.qwen-inference = {
			description = "Qwen3.8-27B SGLang inference";
			wantedBy = [ "default.target" ];
			wants = [ "docker.service" ];
			startLimitBurst = 3;
			startLimitIntervalSec = 600;
			after = [
				"docker.service"
				"network-online.target"
			];
			unitConfig = lib.optionalAttrs (requiredMountPoint != null) {
				ConditionPathIsMountPoint = requiredMountPoint;
			};
			serviceConfig = {
				Type = "simple";
				Environment = [
					"COMPOSE_PROJECT_NAME=qwen-inference"
					"DOCKER_HOST=unix://%t/docker.sock"
				];
				ExecStartPre = [
					"${qwenPrepare}/bin/qwen-inference-prepare"
					"${pkgs.docker-compose}/bin/docker-compose -f ${qwenCompose} run --rm prepare"
					"${qwenWaitGpu}/bin/qwen-inference-wait-gpu"
				];
				ExecStart = "${pkgs.docker-compose}/bin/docker-compose -f ${qwenCompose} up --abort-on-container-exit --remove-orphans inference";
				ExecStop = "${pkgs.docker-compose}/bin/docker-compose -f ${qwenCompose} down";
				Restart = "always";
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

		systemd.user.services.qwen-inference-health = {
			description = "Verify Qwen completion and tool-call inference";
			after = [ "qwen-inference.service" ];
			onFailure = [ "qwen-inference-recover.service" ];
			serviceConfig = {
				Type = "oneshot";
				ExecStart = "${qwenHealth}/bin/qwen-inference-health";
				TimeoutStartSec = "7min";
			};
		};

		systemd.user.services.qwen-inference-recover = {
			description = "Recover failed Qwen inference";
			serviceConfig = {
				Type = "oneshot";
				ExecStart = "${pkgs.systemd}/bin/systemctl --user restart qwen-inference.service";
			};
		};

		systemd.user.timers.qwen-inference-health = {
			description = "Verify Qwen inference every fifteen minutes";
			wantedBy = [ "timers.target" ];
			timerConfig = {
				OnBootSec = "25min";
				OnUnitActiveSec = "15min";
				RandomizedDelaySec = "30s";
				Unit = "qwen-inference-health.service";
			};
		};
	};
}
