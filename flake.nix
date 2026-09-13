{
  description = "Guarded Qwen3.8-27B inference on an NVIDIA RTX 3090";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/d482ef84049d9b7276b83a06e4e4d76983830097";

  outputs = { self, nixpkgs }:
    let
      system = "x86_64-linux";
      pkgs = import nixpkgs { inherit system; };
      standaloneCompose = import ./nix/compose.nix {
        inherit pkgs;
        lib = nixpkgs.lib;
        stateRoot = "\${QWEN_STATE_ROOT:?set by guarded launcher}";
      };
      serve = pkgs.writeShellApplication {
        name = "qwen-serve";
        runtimeInputs = [ pkgs.python313 pkgs.docker-compose ];
        text = ''
          export QWEN_COMPOSE=${standaloneCompose}
          export QWEN_SUPERVISOR=${./serve/supervisor.py}
          exec python3 ${./serve/launch.py} "$@"
        '';
      };
      reference = nixpkgs.lib.nixosSystem {
        inherit system;
        specialArgs.username = "qwen";
        modules = [
          self.nixosModules.reference
          {
            # Evaluation fixture only: not a bootable machine configuration.
            system.stateVersion = "26.05";
            nixpkgs.config.allowUnfree = true;
          }
        ];
      };
    in {
      nixosModules.default = self.nixosModules.qwen-inference;
      nixosModules.qwen-inference = import ./nix/qwen-inference.nix;
      nixosModules.reference = import ./nix/reference.nix;

      packages.${system} = { deployment = standaloneCompose; inherit serve; };
      apps.${system}.serve = {
        type = "app";
        meta.description = "Run the fixed guarded serving stack in the foreground";
        program = "${serve}/bin/qwen-serve";
      };

      devShells.${system}.default = pkgs.mkShellNoCC {
        LD_LIBRARY_PATH = pkgs.lib.makeLibraryPath [ pkgs.stdenv.cc.cc ];
        packages = with pkgs; [
          python313
          uv
          gcc
          docker-client
          docker-compose
          curl
          jq
          openssl
          shellcheck
        ];
      };

      # Build generated units and their referenced scripts, Compose configuration
      # and authenticated source overlay. No daemon, models or GPU are needed.
      checks.${system} = {
      standalone-launcher = serve;
      serving-units = pkgs.linkFarm "qwen-serving-units" [
        {
          name = "qwen-inference.service";
          path = reference.config.systemd.user.units."qwen-inference.service".unit;
        }
        {
          name = "qwen-inference-state-dirs.service";
          path = reference.config.systemd.units."qwen-inference-state-dirs.service".unit;
        }
      ];
      };
    };
}
