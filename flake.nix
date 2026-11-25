{
  description = "FIPS PUB 180-4, a literate Lean 4 specification of the Secure Hash Standard";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-parts.url = "github:hercules-ci/flake-parts";
    flake-parts.inputs.nixpkgs-lib.follows = "nixpkgs";
  };

  outputs = inputs@{ flake-parts, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = [ "x86_64-linux" "aarch64-linux" "aarch64-darwin" ];

      perSystem = { pkgs, ... }: {
        # Once nixpkgs-unstable ships Lean 4.36.0, update the pin and remove nix/lean-release.nix and its linker patches.
        packages.default = import ./nix/package.nix { inherit pkgs; };
        devShells.default = pkgs.mkShell {
          packages = with pkgs; [ elan lean-lsp-mcp pandoc ];
        };
      };
    };
}
