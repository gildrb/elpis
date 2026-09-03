{ ... }:

{
	imports = [
		./qwen-inference.nix
		./hermes-integration.nix
	];

	workstation.qwenInference = {
		enable = true;
		stateRoot = "/mnt/ssd/storage/ai/qwen3.8-27b";
		requiredMountPoint = "/mnt/ssd";
	};
}
