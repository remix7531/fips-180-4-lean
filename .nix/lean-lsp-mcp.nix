{ lib
, python3Packages
, fetchFromGitHub
, callPackage
}:

# MCP server that exposes the Lean theorem prover (via the Lean LSP) to
# agentic LLM clients. See https://github.com/oOo0oOo/lean-lsp-mcp.
let
  leanclient = callPackage ./leanclient.nix { };
in
python3Packages.buildPythonApplication rec {
  pname = "lean-lsp-mcp";
  version = "0.26.1";
  pyproject = true;

  src = fetchFromGitHub {
    owner = "oOo0oOo";
    repo = "lean-lsp-mcp";
    rev = "v${version}";
    sha256 = "12nznr3p2hma0pnpx4avdfbxxqwzbfykdsf5gcm7p4d3gglc6xiq";
  };

  build-system = [ python3Packages.setuptools ];

  dependencies = with python3Packages; [
    leanclient
    mcp
    orjson
    certifi
  ];

  # `lean-lsp-mcp` pins `mcp==1.27.0` exactly. The Aeneas-pinned nixpkgs
  # ships an older `mcp`; relax the constraint since the MCP server API
  # is stable across these minor versions. (`leanclient` is the right
  # version already and stays pinned.)
  pythonRelaxDeps = [ "mcp" ];

  # Tests need a real Lean toolchain + downloaded mathlib; skip in the build.
  doCheck = false;

  meta = {
    description = "MCP server for the Lean theorem prover (via the Lean LSP)";
    homepage = "https://github.com/oOo0oOo/lean-lsp-mcp";
    license = lib.licenses.mit;
    mainProgram = "lean-lsp-mcp";
  };
}
