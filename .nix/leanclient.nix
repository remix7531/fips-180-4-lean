{ lib
, python3Packages
, fetchPypi
}:

# `leanclient` is a thin Python wrapper around `lake serve` (the Lean LSP).
# It's not yet packaged in nixpkgs, so we build it from PyPI here.
# Used by `lean-lsp-mcp` (see .nix/lean-lsp-mcp.nix).
python3Packages.buildPythonPackage rec {
  pname = "leanclient";
  version = "0.9.4";
  pyproject = true;

  src = fetchPypi {
    inherit pname version;
    sha256 = "1d84incjwiaif0y8yrphss9lv6qql44099q2dhgvmbcw4lclx881";
  };

  build-system = [ python3Packages.hatchling ];

  dependencies = with python3Packages; [
    orjson
    psutil
    tqdm
  ];

  # Tests require a real Lean toolchain at build time.
  doCheck = false;

  pythonImportsCheck = [ "leanclient" ];

  meta = {
    description = "Python client for the Lean LSP";
    homepage = "https://github.com/oOo0oOo/leanclient";
    license = lib.licenses.mit;
  };
}
