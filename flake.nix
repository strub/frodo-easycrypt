{
  description = "easycrypt-test";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    easycrypt-nightly = {
      url = "github:Easycrypt/easycrypt?ref=f290633307d6709d6e747df88108a912771e2bb2";
      inputs.nixpkgs-lib.follows = "nixpkgs";
    };

    flake-parts = {
      url = "github:hercules-ci/flake-parts";
      inputs.nixpkgs-lib.follows = "nixpkgs";
    };
  };

  outputs = inputs@{ flake-parts, nixpkgs, easycrypt-nightly, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      imports = [ ];
      systems = [ "x86_64-linux" "aarch64-linux" "aarch64-darwin" "x86_64-darwin" ];
      perSystem = { pkgs, system, inputs', ... }:
        let
          easycrypt = easycrypt-nightly.packages.${system};
        in
        {
          # Per-system attributes can be defined here. The self' and inputs'
          # module parameters provide easy access to attributes of the same
          # system.

          # Equivalent to  inputs'.nixpkgs.legacyPackages.hello;
          _module.args.pkgs = import nixpkgs {
            inherit system;
            config.allowUnfree = true;
          };

          devShells.default = with pkgs; mkShellNoCC {
            packages = [
              direnv
              nix-direnv

              emacsPackages.proof-general
              easycrypt.with_provers
              why3
            ];

            shellHook = ''
              export PATH=$PWD/bin:$PATH
              easycrypt why3config
            '';
          };
        };
      flake = {
        # The usual flake attributes can be defined here, including system-
        # agnostic ones like nixosModule and system-enumerating ones, although
        # those are more easily expressed in perSystem.

      };
    };
}
