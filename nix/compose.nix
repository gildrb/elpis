# Publish Docker's canonical configuration. Nix does not reconstruct runtime sources.
{ pkgs }:
pkgs.writeText "qwen-inference-compose.yaml" (builtins.readFile ../docker-compose.yml)
