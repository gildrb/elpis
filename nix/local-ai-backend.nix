{
	config,
	inputs,
	lib,
	pkgs,
	username,
	...
}:

let
	hostSystem = pkgs.stdenv.hostPlatform.system;
	cfg = config.workstation.localAi;
	ollamaHome = cfg.ollamaHome;
	ollamaModels = "${ollamaHome}/models";
	qwenCfg = config.workstation.qwenInference;
	qwenModel = qwenCfg.model;
	qwenPort = qwenCfg.port;
	hermesHome = cfg.hermesHome;
	hermesManagedSetup =
		config.system.activationScripts."hermes-agent-setup".text;
	hermesPackage =
		inputs.hermesAgent.packages.${hostSystem}.messaging;
	dotfilesSource = inputs.dotfiles;
  # Hermes identity is SOUL.md under HERMES_HOME, not workspace AGENTS.md.
  # Copy into a dedicated store path so hermes documents get file content, not a path string.
	hermesSoul = builtins.path {
		path = "${dotfilesSource}/hermes/SOUL.md";
		name = "hermes-SOUL.md";
	};
	hermesSkin = builtins.path {
		path = "${dotfilesSource}/hermes/skins/death-note.yaml";
		name = "hermes-death-note.yaml";
	};
	signalCli = pkgs.signal-cli;
	signalState = "${hermesHome}/.local/share/signal-cli";
	signalEnv = "${hermesHome}/.hermes/.env";
	signalConfigured = pkgs.writeShellScript "hermes-signal-configured" ''
    [[ -n "''${SIGNAL_ACCOUNT:-}" ]]
  '';
	signalDaemon = pkgs.writeShellScript "hermes-signal-daemon" ''
    if [[ -z "''${SIGNAL_ACCOUNT:-}" ]]; then
      echo "SIGNAL_ACCOUNT is missing from ${hermesHome}/.hermes/.env" >&2
      exit 1
    fi
    exec ${signalCli}/bin/signal-cli \
      --config ${signalState} \
      --account "$SIGNAL_ACCOUNT" \
      daemon --http 127.0.0.1:8080
  '';
	signalLink = pkgs.writeShellApplication {
		name = "hermes-signal-link";
		runtimeInputs = [
			pkgs.coreutils
			pkgs.gawk
			pkgs.gnused
			pkgs.qrencode
			signalCli
			pkgs.systemd
		];
		text = ''
      install -d -m 0700 ${signalState}
      echo "In Signal on your phone, open Settings > Linked devices > Link new device."
      echo "Scan this QR, or open the device-link URI printed below it."
      signal-cli --config ${signalState} link -n HermesAgent |
        while IFS= read -r line; do
          printf '%s\n' "$line"
          case "$line" in
          tsdevice:?*) printf '%s' "$line" | qrencode -t ANSIUTF8 -m 2 ;;
          esac
        done

      account="$(signal-cli --config ${signalState} listAccounts | sed -n 's/^Number: //p')"
      if [[ ! "$account" =~ ^\+[0-9]+$ ]] || [[ "$account" == *$'\n'* ]]; then
        echo "Could not determine one linked Signal account." >&2
        exit 1
      fi

      env_file=${signalEnv}
      install -d -m 0700 "$(dirname "$env_file")"
      touch "$env_file"
      chmod 0600 "$env_file"
      tmp="$(mktemp "$(dirname "$env_file")/.signal-env.XXXXXX")"
      awk '!/^SIGNAL_(HTTP_URL|ACCOUNT|ALLOWED_USERS|HOME_CHANNEL)=/' "$env_file" >"$tmp"
      printf '%s\n' \
        'SIGNAL_HTTP_URL=http://127.0.0.1:8080' \
        "SIGNAL_ACCOUNT=$account" \
        "SIGNAL_ALLOWED_USERS=$account" \
        "SIGNAL_HOME_CHANNEL=$account" >>"$tmp"
      chmod 0600 "$tmp"
      mv "$tmp" "$env_file"

      echo "Signal linked. Hermes is restricted to your account and Note to Self."
      # These are system units; an unprivileged restart is denied. Report
      # the outcome instead of discarding the failure behind /dev/null.
      if ! systemctl --no-block try-restart hermes-signal.service hermes-agent.service; then
        echo "Could not restart hermes-signal and hermes-agent from this shell." >&2
        echo "Run: sudo systemctl restart hermes-signal hermes-agent" >&2
      fi
    '';
	};
  # The supported RTX 3060 Ti and RTX 3090 GPUs both use sm_86. Building
  # every upstream CUDA architecture makes the hosted closure exceed the
  # runner's time and memory budget without improving this host's runtime.
	ollamaCuda = pkgs.ollama-cuda.override {
		cudaArches = [ "sm_86" ];
	};
	liquidModel = "hf.co/LiquidAI/LFM2.5-2.6B-GGUF:Q4_K_M";
	fallbackModel = "qwen3:4b";
	# Qwen2 7B math specialist kept installed for direct use in Hax. Native
	# context is 4096; Hermes rejects models below its 64000 context floor,
	# so it must stay out of the Hermes model settings entirely.
	mathModel = "hf.co/mradermacher/INTELLECT-MATH-GGUF:Q4_K_M";
	# Nemotron-Nano-9B-v2 hybrid Mamba2: agentic 9B with a tiny KV cache, so
	# 64k context fits even the 8 GB RTX 3060 Ti alongside the Q4 weights.
	nemotronModel = "hf.co/bartowski/nvidia_NVIDIA-Nemotron-Nano-9B-v2-GGUF:Q4_K_M";
  # tmpfiles cannot chown these paths under the user-owned SSD storage
  # root. A root install -d creates the chain with the correct owner.
	ensureLocalAiDirs = ''
    set -euo pipefail
    owner=${lib.escapeShellArg username}
    ollama_home=${lib.escapeShellArg ollamaHome}
    ollama_models=${lib.escapeShellArg ollamaModels}
    hermes_home=${lib.escapeShellArg hermesHome}
    hermes_workspace="$hermes_home/workspace"
    hermes_profile="$hermes_home/.hermes"
    for path in "$ollama_home" "$ollama_models" "$hermes_home" \
      "$hermes_workspace" "$hermes_profile"; do
      if [[ -L "$path" ]]; then
        printf 'refusing symlinked local AI path: %s\n' "$path" >&2
        exit 1
      fi
      ${pkgs.coreutils}/bin/install -d -m 0700 -o "$owner" -g users "$path"
    done
    ${pkgs.coreutils}/bin/chown -R "$owner":users \
      "$hermes_home" "$hermes_workspace" "$hermes_profile"
  '';
in
{
	options.workstation.localAi = {
		ollamaHome = lib.mkOption {
			type = lib.types.externalPath;
			default = "/srv/ai/models/ollama";
			description = "Ollama models and state directory.";
		};

		hermesHome = lib.mkOption {
			type = lib.types.externalPath;
			default = "/srv/agents/hermes";
			description = "Hermes agent home and workspace directory.";
		};
	};

	config = {
	system.activationScripts.ensureLocalAiDirs =
		lib.stringAfter [ "users" ]
			ensureLocalAiDirs;


	systemd.services.local-ai-state-dirs = {
		description = "Create user-owned local AI state directories";
		wantedBy = [ "multi-user.target" ];
		after = [ "local-fs.target" ];
		before = [
			"ollama.service"
			"hermes-agent.service"
			"hermes-minimal-profile.service"
		];
		unitConfig.RequiresMountsFor = [
			ollamaHome
			hermesHome
		];
		serviceConfig = {
			Type = "oneshot";
			RemainAfterExit = true;
		};
		script = ensureLocalAiDirs;
	};

	systemd.services.ollama = {
		after = [ "local-ai-state-dirs.service" ];
		wants = [ "local-ai-state-dirs.service" ];
		serviceConfig = {
			DynamicUser = lib.mkForce false;
			Group = "users";
			StateDirectory = lib.mkForce [ ];
			SupplementaryGroups = lib.mkForce [
				"render"
				"video"
			];
			User = username;
		};
	};

	environment.systemPackages = [
		pkgs.himalaya
		signalCli
		signalLink
	];

	services.ollama = {
		enable = true;
		package = ollamaCuda;
		home = ollamaHome;
		models = ollamaModels;
		host = "127.0.0.1";
		port = 11434;
		openFirewall = false;
		environmentVariables = {
			OLLAMA_CONTEXT_LENGTH = "65536";
			OLLAMA_FLASH_ATTENTION = "1";
			OLLAMA_KEEP_ALIVE = "1h";
			OLLAMA_MAX_LOADED_MODELS = "1";
			OLLAMA_NO_CLOUD = "1";
			OLLAMA_NUM_PARALLEL = "1";
		};
		loadModels = [
			nemotronModel
			liquidModel
			fallbackModel
			mathModel
		];
		syncModels = false;
	};

	services.hermes-agent = {
		package = hermesPackage;
		enable = true;
		addToSystemPackages = true;
		createUser = false;
		user = username;
		group = "users";
		stateDir = hermesHome;
		workingDirectory = "${hermesHome}/workspace";
		settings = {
			_config_version = 38;
			model = {
				default = qwenModel;
				provider = "custom:qwen-local";
				base_url = "http://127.0.0.1:${toString qwenPort}/v1";
				context_length = 65536;
				max_tokens = 8192;
			};
			custom_providers = [
				{
					name = "qwen-local";
					base_url = "http://127.0.0.1:${toString qwenPort}/v1";
					key_env = "QWEN_API_KEY";
					models."${qwenModel}".context_length = 65536;
				}
				{
					name = "ollama-local";
					base_url = "http://127.0.0.1:11434/v1";
					models = {
						"${nemotronModel}".context_length =
							65536;
						"${liquidModel}".context_length =
							65536;
						"${fallbackModel}".context_length =
							40960;
					};
				}
			];
			model_aliases = {
				qwen = {
					model = qwenModel;
					provider = "custom:qwen-local";
					base_url = "http://127.0.0.1:${toString qwenPort}/v1";
				};
				liquid = {
					model = liquidModel;
					provider = "custom";
					base_url = "http://127.0.0.1:11434/v1";
				};
				fast = {
					model = fallbackModel;
					provider = "custom";
					base_url = "http://127.0.0.1:11434/v1";
				};
			};
			display = {
				interface = "tui";
				skin = "death-note";
			};

      # Lifecycle messages are useful for an operator back-channel, but Discord
      # is the user-facing chat surface. systemd already keeps the gateway
      # running, so routine NixOS activations and reboots must not look like
      # random gateway failures there.
			discord.gateway_restart_notification = false;
			terminal.backend = "local";
			toolsets = [
				"terminal"
				"file"
			];
			platform_toolsets.cli = [
				"terminal"
				"file"
			];
			platform_toolsets.signal = [
				"web"
				"vision"
				"skills"
				"memory"
				"session_search"
				"clarify"
			];
			platform_toolsets.telegram = [
				"web"
				"vision"
				"skills"
				"memory"
				"session_search"
				"clarify"
			];
		};
    # Workspace copy is optional context; HERMES_HOME/SOUL.md is the identity.
		documents."SOUL.md" = hermesSoul;
	};

	systemd.services.hermes-minimal-profile = {
		description = "Keep the Hermes profile minimal";
		# The symlink guard must gate this root script, not merely order it;
		# ordering alone would let the destructive steps run after a failed
		# check.
		requires = [ "local-ai-state-dirs.service" ];
		after = [ "local-ai-state-dirs.service" ];
		before = [ "hermes-agent.service" ];
		requiredBy = [ "hermes-agent.service" ];
		serviceConfig = {
			Type = "oneshot";
		};
		script = ''
      # Re-verify every user-owned path in the same root process that
      # mutates it: a planted symlink at .hermes, workspace, or their
      # parents would otherwise turn these rm/chown/cp steps into a
      # confused-deputy primitive.
      for path in ${hermesHome}/.hermes ${hermesHome}/.hermes/logs \
        ${hermesHome}/.hermes/skills ${hermesHome}/workspace; do
        if [[ -L "$path" ]]; then
          printf 'refusing symlinked Hermes profile path: %s\n' "$path" >&2
          exit 1
        fi
      done
      ${hermesManagedSetup}
      ${pkgs.coreutils}/bin/rm -rf -- ${hermesHome}/.hermes/skills
      ${pkgs.coreutils}/bin/install -d -o ${username} -g users -m 0700 \
        ${hermesHome}/.hermes \
        ${hermesHome}/.hermes/logs \
        ${hermesHome}/.hermes/skins \
        ${hermesHome}/.hermes/skills/email/himalaya
      # -h keeps chown from dereferencing a symlinked operand; the loop
      # above already refused that case, this is defense in depth.
      ${pkgs.coreutils}/bin/chown -R -h ${username}:users ${hermesHome}/.hermes
      ${pkgs.coreutils}/bin/cp -R --no-preserve=mode,ownership \
        ${hermesPackage}/share/hermes-agent/skills/email/himalaya/. \
        ${hermesHome}/.hermes/skills/email/himalaya/
      ${pkgs.coreutils}/bin/chown -R ${username}:users ${hermesHome}/.hermes/skills
      ${pkgs.coreutils}/bin/chmod -R u=rwX,go= ${hermesHome}/.hermes/skills
      ${pkgs.coreutils}/bin/install -o ${username} -g users -m 0600 /dev/null \
        ${hermesHome}/.hermes/.no-bundled-skills
      # Hermes loads identity only from $HERMES_HOME/SOUL.md. Force the
      # declarative SOUL over any previously seeded or hand-edited file.
      ${pkgs.coreutils}/bin/install -o ${username} -g users -m 0640 \
        ${hermesSoul} ${hermesHome}/.hermes/SOUL.md
      ${pkgs.coreutils}/bin/install -o ${username} -g users -m 0640 \
        ${hermesSkin} ${hermesHome}/.hermes/skins/death-note.yaml
      ${pkgs.coreutils}/bin/install -d -o ${username} -g users -m 0700 \
        ${hermesHome}/workspace
      ${pkgs.coreutils}/bin/rm -f -- ${hermesHome}/workspace/AGENTS.md
    '';
	};

  # The model loader must share ownership with Ollama because the private model
  # directory is deliberately inaccessible to systemd's default dynamic user.
	systemd.services.ollama-model-loader.serviceConfig = {
		DynamicUser = lib.mkForce false;
		Group = "users";
		User = username;
	};

	systemd.services.hermes-agent = {
		after = [
			"local-ai-state-dirs.service"
			"ollama.service"
			"hermes-signal.service"
		];
		wants = [
			"hermes-signal.service"
			"ollama.service"
		];
    # Hermes classifies SIGINT as a planned, graceful stop and SIGTERM as an
    # unexpected failure. Match that contract so systemd-driven activation and
    # shutdown do not get reported as crashes; genuine SIGTERM failures still
    # exit non-zero and are restarted by the upstream unit policy.
		serviceConfig = {
			EnvironmentFile = "-${qwenCfg.stateRoot}/hermes.env";
			KillSignal = "SIGINT";
		};
	};

  # Signal is transport only. Hermes continues to run inference through its
  # configured loopback endpoint. Account credentials and the
  # linked-device state stay private under the Hermes service home.
	systemd.services.hermes-signal = {
		description = "Signal transport for Hermes Agent";
		after = [ "network-online.target" ];
		wants = [ "network-online.target" ];
		wantedBy = [ "multi-user.target" ];
		# A dropped Signal link must be loud, not a silent skip: fail the
		# unit so the alert below fires and the operator re-links.
		onFailure = [ "hermes-signal-down.service" ];
		environment = {
			HOME = hermesHome;
			XDG_DATA_HOME = "${hermesHome}/.local/share";
		};
		serviceConfig = {
			EnvironmentFile = "-${hermesHome}/.hermes/.env";
			ExecCondition = signalConfigured;
			ExecStart = signalDaemon;
			Restart = "on-failure";
			RestartSec = 30;
			StartLimitBurst = 3;
			StartLimitIntervalSec = 90;
			User = username;
			Group = "users";
			UMask = "0077";
			NoNewPrivileges = true;
			PrivateTmp = true;
			ProtectSystem = "strict";
			ProtectHome = false;
			ReadWritePaths = [ hermesHome ];
		};
	};

	systemd.services.hermes-signal-down = {
		description = "Notify the operator that the Hermes Signal transport is down";
		serviceConfig = {
			Type = "oneshot";
			User = username;
			Group = "users";
		};
		# Anonymous publish is allowed by the write-only ntfy default and
		# reaches the subscribed phone; the topic name is the secret.
		script = ''
			${pkgs.curl}/bin/curl --max-time 10 -d \
				"Hermes Signal transport is down. If SIGNAL_ACCOUNT is set, re-link the device: ssh hephaistos hermes-signal-link" \
				"http://127.0.0.1:${toString config.workstation.selfHosting.ntfyPort}/alerts" \
				>/dev/null 2>&1 || true
		'';
	};

	systemd.paths.hermes-signal-credentials = {
		description = "Watch Hermes private messaging credentials";
		wantedBy = [ "multi-user.target" ];
		pathConfig.PathChanged = signalEnv;
	};

	# The signal-cli JSON-RPC daemon has no built-in authentication. Bind it
	# to loopback and restrict callers by owner: only the Hermes account
	# (and root) may open that port, so any other local process or
	# host-network container is rejected at the firewall.
	networking.firewall.extraCommands = ''
		# owner --uid-owner may appear once per rule, so allow root and
		# the Hermes account through a dedicated chain and reject every
		# other caller of the unauthenticated loopback daemon.
		iptables -N hermes-signal-guard 2>/dev/null || true
		iptables -F hermes-signal-guard
		iptables -A hermes-signal-guard -m owner --uid-owner 0 -j RETURN
		iptables -A hermes-signal-guard -m owner --uid-owner ${username} -j RETURN
		iptables -A hermes-signal-guard -j REJECT
		if ! iptables -C OUTPUT -o lo -p tcp --dport 8080 -j hermes-signal-guard 2>/dev/null; then
			iptables -I OUTPUT -o lo -p tcp --dport 8080 -j hermes-signal-guard
		fi
	'';

	systemd.services.hermes-signal-credentials = {
		description = "Reload Hermes after private messaging credential changes";
		serviceConfig.Type = "oneshot";
		script = ''
      ${pkgs.systemd}/bin/systemctl try-restart hermes-signal.service hermes-agent.service
    '';
	};
	};
}
