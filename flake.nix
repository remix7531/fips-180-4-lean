{
  description = "FIPS PUB 180-4 — literate Lean 4 specification of the Secure Hash Standard";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
        lean-lsp-mcp = pkgs.callPackage ./.nix/lean-lsp-mcp.nix { };
      in {
        devShells.default = pkgs.mkShell {
          buildInputs = [
            pkgs.gnumake
            pkgs.elan     # Lean 4 toolchain manager
            pkgs.pandoc   # HTML rendering
            lean-lsp-mcp  # Lean LSP MCP server for agentic proof development
          ];
        };
      }
    );
}
