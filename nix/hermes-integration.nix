{
	config,
	lib,
	...
}:

let
	qwen = config.workstation.qwenInference;
in
{
	services.hermes-agent.settings = {
		model = {
			default = qwen.model;
			provider = "custom";
			base_url = "http://127.0.0.1:${toString qwen.port}/v1";
			context_length = 65536;
			max_tokens = 8192;
		};
		custom_providers = lib.mkAfter [
			{
				name = "qwen-local";
				base_url = "http://127.0.0.1:${toString qwen.port}/v1";
				key_env = "QWEN_API_KEY";
				models."${qwen.model}".context_length = 65536;
			}
		];
		model_aliases.qwen = {
			model = qwen.model;
			provider = "custom";
			base_url = "http://127.0.0.1:${toString qwen.port}/v1";
		};
	};

	systemd.services.hermes-agent.serviceConfig.EnvironmentFile =
		"-${qwen.stateRoot}/hermes.env";
}
