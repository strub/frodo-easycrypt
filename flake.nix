{
  description = "easycrypt-test";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    easycrypt-nightly = {
      url = "github:Easycrypt/easycrypt?ref=1ad6fedd02da81c549b6d74908252b585bd2ea18";
      inputs.nixpkgs-lib.follows = "nixpkgs";
    };
    jasmin-nightly = {
        url = "github:jasmin-lang/jasmin/83e232e0d0a1c056e6a66e04ff76379c4b5a376b";
        flake = false;
    };

    flake-parts = {
      url = "github:hercules-ci/flake-parts";
      inputs.nixpkgs-lib.follows = "nixpkgs";
    };
  };

  outputs = inputs@{ flake-parts, nixpkgs, easycrypt-nightly, jasmin-nightly, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      imports = [ ];
      systems = [ "x86_64-linux" "aarch64-linux" "aarch64-darwin" "x86_64-darwin" ];
      perSystem = { pkgs, system, ... }:
        let
          easycrypt = easycrypt-nightly.packages.${system};
          jasminc = pkgs.callPackage "${jasmin-nightly}/default.nix" { inherit pkgs; };
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

          devShells.default = pkgs.mkShellNoCC {
            packages = builtins.attrValues {
              easycrypt = easycrypt.with_provers;
              jasminc = jasminc;

              inherit (pkgs)
                direnv
                nix-direnv

                why3;
            };

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
