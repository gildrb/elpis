# One canonical deployment for NixOS and the foreground Nix app.
{ pkgs, lib, stateRoot, port ? 18020, model ? "qwen3.8-27b" }:
let
	sglangImage = "lmsysorg/sglang:v0.5.19@sha256:d6e7288627be8b02be88e4bba38e73f6d50e2826869f753c13a4c4385ab3eda9";
	sglangEntrypoint = ../serve/entrypoint.sh;
	compatManifest = builtins.fromJSON (builtins.readFile ../patches/manifest.json);
	# Select reviewed Python files only; never build or replace the runtime package.
	compatOverlay = pkgs.runCommand "sglang-reviewed-source-overlay" {
		nativeBuildInputs = [ pkgs.python3 pkgs.patch ];
	} ''
		mkdir -p "$out"
		cp -r ${../patches/base}/. "$out/"
		chmod -R u+w "$out"
		python3 ${../patches/verify.py} \
			--manifest ${../patches/manifest.json} \
			--phase original --root "$out" \
			--image ${lib.escapeShellArg sglangImage}
		${lib.concatMapStringsSep "\n" (module: ''
			echo '${module.patch_sha256}  ${../patches + "/${module.patch}"}' | sha256sum --check
			patch --batch --forward --fuzz=0 -p4 -d "$out" < ${../patches + "/${module.patch}"}
		'') compatManifest.modules}
		python3 ${../patches/verify.py} \
			--manifest ${../patches/manifest.json} \
			--phase replacement --root "$out" \
			--image ${lib.escapeShellArg sglangImage}
	'';
	compatVolumes = [
		"${../patches/manifest.json}:/sglang-compat-manifest.json:ro"
		"${../patches/verify.py}:/sglang-compat-verify.py:ro"
	];
	modelVolumes = [
		"${../prepare/verify-models.py}:/model-preparation/verify-models.py:ro"
		"${../prepare/manifest.json}:/model-preparation/manifest.json:ro"
		"${../prepare/artifact.sha256}:/model-preparation/artifact.sha256:ro"
		"${../prepare/draft.sha256}:/model-preparation/draft.sha256:ro"
		"${../prepare/embedding-validation.json}:/model-preparation/embedding-validation.json:ro"
	];
	qwenCompose = (pkgs.formats.yaml { }).generate "qwen-inference-compose.yaml" {
		services = {
			prepare = {
				image = sglangImage;
				entrypoint = [
					"bash"
					"-c"
					"python3 /sglang-compat-verify.py --manifest /sglang-compat-manifest.json --phase original --root ${lib.escapeShellArg compatManifest.source_root} --image ${lib.escapeShellArg sglangImage} && exec bash /sglang-entrypoint"
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
					"${stateRoot}/models:/models:ro"
					"${stateRoot}/cache:/cache"
					"${sglangEntrypoint}:/sglang-entrypoint:ro"
				] ++ compatVolumes ++ modelVolumes;
				deploy.resources.limits = {
					cpus = "8";
					memory = "48G";
				};
			};
			inference = {
				image = sglangImage;
				entrypoint = [
					"bash"
					"-c"
					"python3 /sglang-compat-verify.py --manifest /sglang-compat-manifest.json --phase replacement --root ${lib.escapeShellArg compatManifest.source_root} --image ${lib.escapeShellArg sglangImage} && exec bash /sglang-entrypoint"
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
					SERVED_MODEL_NAME = model;
					# Health accepts scheduler progress while busy, or generates one token
					# when idle. Allow long prefill without a short watchdog deadline.
					SGLANG_HEALTH_CHECK_TIMEOUT = "300";
				};
				volumes = [
					"${stateRoot}/models:/models:ro"
					"${stateRoot}/cache:/cache"
					"${stateRoot}/api-key:/app/api_key.txt:ro"
					"${sglangEntrypoint}:/sglang-entrypoint:ro"
				] ++ compatVolumes ++ modelVolumes ++ (
					map (module: "${compatOverlay}/${module.installed_path}:${compatManifest.source_root}/${module.installed_path}:ro") compatManifest.modules
				);
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

			};
		};
	};
in qwenCompose
