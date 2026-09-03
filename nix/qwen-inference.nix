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
	port = cfg.port;
	requiredMountPoint = cfg.requiredMountPoint;
	qwenImage = "ghcr.io/syv-ai/qwen38-27b-rtx3090@sha256:9a4ef2b51316f3ce1a23dd4bffc5e5c93669703daa5c0b0818258408058039ae";
	qwenBaseRevision = "1f05c441c4e64ae0549de44fa9ea5a6d43610314";
	qwenFastRevision = "124c14e7e8c7d2f5402933b9af368e772a9fcf0c";
	qwenDflashRevision = "4d30ec736ffc6b8688dc2ae2b502d9b48bdec279";
	qwenPinnedPrepare = pkgs.writeText "qwen-inference-pinned-prepare.sh" ''
    set -euo pipefail
    cd /app
    export PATH=/app/venv/bin:$PATH
    export HF_HUB_DISABLE_TELEMETRY=1

    marker=/app/models/.prepared-revisions
    expected='image=8d832f8758ae4fd36c29a15d3c45888922bc4377
base=${qwenBaseRevision}
fast=${qwenFastRevision}
dflash=${qwenDflashRevision}'
    if [[ -f "$marker" ]] && [[ "$(cat "$marker")" == "$expected" ]]; then
      echo "Pinned Qwen model set is already prepared."
      exit 0
    fi
    if [[ -e "$marker" ]]; then
      echo "Refusing to mutate a Qwen model set prepared from different revisions." >&2
      exit 1
    fi

    base=/app/models/Qwen3.8-27B-W4A16-AutoRound
    hf download dbirks/Qwen3.8-27B-W4A16-AutoRound \
      --revision ${qwenBaseRevision} --local-dir "$base"

    python - <<'PY'
from pathlib import Path

replacements = {
    Path("prepare/fetch_fast_variant.py"): (
        'snapshot_download("syvai/qwen3.8-27b-3090-fast-variant",',
        'snapshot_download("syvai/qwen3.8-27b-3090-fast-variant", revision="${qwenFastRevision}",',
    ),
    Path("prepare/fetch_dflash2.py"): (
        "snapshot_download(REPO, local_dir=D,",
        'snapshot_download(REPO, revision=None if BF16 else "${qwenDflashRevision}", local_dir=D,',
    ),
}
for path, (old, new) in replacements.items():
    text = path.read_text()
    if text.count(old) != 1:
        raise SystemExit(f"expected one pinned-download patch point in {path}")
    path.write_text(text.replace(old, new))
PY

    HF_REPO=dbirks/Qwen3.8-27B-W4A16-AutoRound \
      FAST_VARIANT=1 DFLASH2=1 bash docker/prepare.sh
    for required in \
      /app/models/Qwen3.8-27B-W4A16-AutoRound-fast/model.safetensors.index.json \
      /app/models/Qwen3.8-27B-DFlash2-W4A16/model.safetensors; do
      [[ -s "$required" ]] || {
        printf 'required prepared model artifact is missing: %s\n' "$required" >&2
        exit 1
      }
    done
    printf '%s\n' "$expected" >"$marker.tmp"
    mv "$marker.tmp" "$marker"
  '';
	qwenCompose = (pkgs.formats.yaml { }).generate "qwen-inference-compose.yaml" {
		networks.isolated.internal = true;
		services = {
			prepare = {
				image = qwenImage;
				entrypoint = [
					"bash"
					"/prepare-pinned"
				];
				command = [ ];
				pull_policy = "missing";
				environment = {
					DFLASH2 = "1";
					FAST_VARIANT = "1";
					HOME = "/cache";
				};
				volumes = [
					"${stateRoot}/models:/app/models"
					"${stateRoot}/cache:/cache"
					"${qwenPinnedPrepare}:/prepare-pinned:ro"
				];
				deploy.resources.limits = {
					cpus = "8";
					memory = "48G";
				};
			};
			inference = {
				image = qwenImage;
				command = [ "single" ];
				pull_policy = "missing";
				stop_grace_period = "60s";
				shm_size = "8gb";
				read_only = true;
				cap_drop = [ "ALL" ];
				security_opt = [ "no-new-privileges:true" ];
				tmpfs = [
					"/run:rw,noexec,nosuid,size=64m"
					"/tmp:rw,noexec,nosuid,size=2g"
				];
				networks = [ "isolated" ];
				ports = [ "127.0.0.1:${toString port}:${toString port}" ];
				environment = {
					CTX = "fast";
					DFLASH_TOKENS = "7";
					DO_NOT_TRACK = "1";
					HF_HUB_DISABLE_TELEMETRY = "1";
					HOME = "/cache";
					HOST = "0.0.0.0";
					MAX_SEQS = "1";
					PORT = toString port;
					PREFIX_CACHE = "1";
					PREPARE = "0";
					SPEC = "dflash2";
					TOOLS = "1";
					VERIFY = "1";
					VISION = "0";
					VLLM_DFLASH2_CHAIN = "0";
					VLLM_NO_USAGE_STATS = "1";
				};
				volumes = [
					"${stateRoot}/models:/app/models:ro"
					"${stateRoot}/cache:/cache"
					"${stateRoot}/api-key:/app/api_key.txt:ro"
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
						"curl"
						"-fsS"
						"http://127.0.0.1:${toString port}/health"
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
        key="$(openssl rand -hex 32)"
        printf '%s\n' "$key" >${lib.escapeShellArg "${stateRoot}/api-key.tmp"}
        printf 'QWEN_API_KEY=%s\n' "$key" >${lib.escapeShellArg "${stateRoot}/hermes.env.tmp"}
        mv ${lib.escapeShellArg "${stateRoot}/api-key.tmp"} ${lib.escapeShellArg "${stateRoot}/api-key"}
        mv ${lib.escapeShellArg "${stateRoot}/hermes.env.tmp"} ${lib.escapeShellArg "${stateRoot}/hermes.env"}
      elif [[ ! -s ${lib.escapeShellArg "${stateRoot}/hermes.env"} ]]; then
        umask 077
        printf 'QWEN_API_KEY=%s\n' "$(cat ${lib.escapeShellArg "${stateRoot}/api-key"})" \
          >${lib.escapeShellArg "${stateRoot}/hermes.env.tmp"}
        mv ${lib.escapeShellArg "${stateRoot}/hermes.env.tmp"} ${lib.escapeShellArg "${stateRoot}/hermes.env"}
      fi
      chmod 0600 \
        ${lib.escapeShellArg "${stateRoot}/api-key"} \
        ${lib.escapeShellArg "${stateRoot}/hermes.env"}
    '';
	};
	qwenWaitGpu = pkgs.writeShellApplication {
		name = "qwen-inference-wait-gpu";
		runtimeInputs = [
			pkgs.coreutils
			pkgs.curl
			pkgs.jq
			(config.hardware.nvidia.package.bin or config.hardware.nvidia.package)
		];
		text = ''
      if models="$(curl -fsS --max-time 5 http://127.0.0.1:11434/api/ps 2>/dev/null)"; then
        while IFS= read -r model; do
          [[ -n "$model" ]] || continue
          jq -n --arg model "$model" '{model: $model, keep_alive: 0}' |
            curl -fsS --max-time 30 -H 'Content-Type: application/json' \
              -d @- http://127.0.0.1:11434/api/generate >/dev/null
        done < <(jq -r '.models[]?.name' <<<"$models")
      fi
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
	qwenHealth = pkgs.writeShellApplication {
		name = "qwen-inference-health";
		runtimeInputs = [
			pkgs.coreutils
			pkgs.curl
			pkgs.jq
		];
		text = ''
      key_file=${lib.escapeShellArg "${stateRoot}/api-key"}
      [[ -s "$key_file" ]] || {
        echo "Qwen API key is missing." >&2
        exit 1
      }
      response="$(mktemp)"
      trap 'rm -f "$response"' EXIT
      for _ in 1 2; do
        if curl -fsS --max-time 120 \
          -H "Authorization: Bearer $(cat "$key_file")" \
          -H 'Content-Type: application/json' \
          -o "$response" \
          -d '{
            "model": "qwen3.8-27b",
            "messages": [{"role": "user", "content": "Call health_check with status ok."}],
            "tools": [{
              "type": "function",
              "function": {
                "name": "health_check",
                "description": "Report inference health.",
                "parameters": {
                  "type": "object",
                  "properties": {"status": {"type": "string"}},
                  "required": ["status"]
                }
              }
            }],
            "tool_choice": {"type": "function", "function": {"name": "health_check"}},
            "temperature": 0,
            "max_tokens": 64,
            "chat_template_kwargs": {"enable_thinking": false}
          }' \
          http://127.0.0.1:${toString port}/v1/chat/completions &&
          jq -e '.choices[0].message.tool_calls[0].function.name == "health_check"' \
            "$response" >/dev/null; then
          exit 0
        fi
        sleep 5
      done
      jq -r '.error.message // "Qwen completion/tool health check failed."' \
        "$response" >&2 2>/dev/null || true
      exit 1
    '';
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
		enable = lib.mkEnableOption "Qwen3.8-27B low-latency inference";

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
		system.activationScripts.ensureQwenInferenceDirs =
			lib.stringAfter [ "users" ] ensureQwenDirs;
		environment.systemPackages = [ qwenHealth ];
		systemd.user.services.qwen-inference = {
			description = "Qwen3.8-27B low-latency inference";
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
					stateRoot
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
