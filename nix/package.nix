{ pkgs }:

let
  inherit (pkgs) lib;
  leanVersion = lib.removePrefix "leanprover/lean4:v" (lib.trim (builtins.readFile ../lean-toolchain));
  packagedLean = pkgs.leanPackages.lean4;
  useRelease = packagedLean.version != leanVersion;
  patchInterpreter = useRelease && pkgs.stdenv.hostPlatform.isLinux;
  buildLakePackage = pkgs.buildLakePackage.override {
    lean4 = if useRelease then import ./lean-release.nix { inherit pkgs; version = leanVersion; }
      else packagedLean;
  };

  manifest = builtins.fromJSON (builtins.readFile ../lake-manifest.json);
  revisions = builtins.listToAttrs (map (package:
    lib.nameValuePair package.name package.rev) manifest.packages);
  cli = pkgs.fetchFromGitHub {
    owner = "leanprover";
    repo = "lean4-cli";
    rev = revisions.Cli;
    hash = "sha256-xXLnVWP8/6iGa1E4Zen/VI//yTAvzA5cqWgmPuvqe+Y=";
  };
  mdgen = pkgs.fetchFromGitHub {
    owner = "Seasawher";
    repo = "mdgen";
    rev = revisions.mdgen;
    hash = "sha256-Nlfz2ZKrHenFzpC52ZjWowAVfkB5KHztY57QTLX/aCY=";
  };
in
buildLakePackage {
  pname = "fips-pub-180-4";
  version = "0.1.0";
  meta.license = lib.licenses.lgpl3Plus;
  src = lib.fileset.toSource {
    root = ../.;
    fileset = lib.fileset.unions [
      ../LICENSE ../README.md ../lakefile.lean ../lake-manifest.json ../lean-toolchain
      ../spec.lean ../spec ../impl ../equiv ../scripts ../tests
    ];
  };
  lakeDeps = pkgs.runCommand "fips-pub-180-4-lake-sources" {} ''
    mkdir -p "$out"
    cp -r "${cli}" "$out/Cli"
    cp -r "${mdgen}" "$out/mdgen"
  '';
  buildTargets = [ "spec" "impl" "equiv" "tests" "cavp" ];

  # The release bundle supplies its own compiler and native libraries.
  postConfigure = lib.optionalString useRelease "unset LEAN_CC";
  nativeBuildInputs = lib.optional patchInterpreter pkgs.patchelf;
  # The bundled linker emits the standard Linux interpreter path.
  postBuild = lib.optionalString patchInterpreter ''
    patchelf --set-interpreter "${pkgs.stdenv.cc.bintools.dynamicLinker}" .lake/build/bin/cavp
  '';
  doCheck = true;
  checkPhase = ''
    runHook preCheck
    lake test -- --fast
    runHook postCheck
  '';

  # The bundled fixtures are relative to the package root.
  postInstall = ''
    rm "$out/bin/cavp"
    cat > "$out/bin/cavp" <<EOF
    #!${pkgs.runtimeShell}
    set -e
    cd "$out"
    exec "$out/.lake/build/bin/cavp" "\$@"
    EOF
    chmod +x "$out/bin/cavp"
  '';
  doInstallCheck = true;
  installCheckPhase = ''
    runHook preInstallCheck
    (cd "$TMPDIR" && "$out/bin/cavp" --spec --alg=SHA1 --no-monte --fast)
    runHook postInstallCheck
  '';
}
