{ pkgs, version }:

let
  bundles = {
    x86_64-linux = {
      suffix = "linux";
      hash = "sha256-K3qx7YuS0uar+vQTRII7UQBk28nAJgysc+tJarLepus=";
    };
    aarch64-linux = {
      suffix = "linux_aarch64";
      hash = "sha256-NUcZmBUhke+AlBjOW/Yfj8XyCeXjvgW0i9xJSf2z5yY=";
    };
    aarch64-darwin = {
      suffix = "darwin_aarch64";
      hash = "sha256-SaytqHSa0TQ+/xIko9JRCsYe1TNj03tec46MWH596r0=";
    };
  };
  platform = pkgs.stdenv.hostPlatform;
  bundle = bundles.${platform.system};
in
assert pkgs.lib.assertMsg (version == "4.36.0") "No Lean release archive is pinned for ${version}.";
pkgs.stdenv.mkDerivation {
  pname = "lean";
  inherit version;
  src = pkgs.fetchurl {
    url = "https://github.com/leanprover/lean4/releases/download/v${version}/lean-${version}-${bundle.suffix}.tar.zst";
    inherit (bundle) hash;
  };
  nativeBuildInputs = [ pkgs.zstd ] ++ pkgs.lib.optional platform.isLinux pkgs.patchelf;
  dontConfigure = true;
  dontBuild = true;
  dontStrip = true;
  dontPatchELF = true;
  installPhase = ''
    runHook preInstall
    mkdir -p "$out"
    cp -a . "$out"
  '' + pkgs.lib.optionalString platform.isLinux ''
    for program in "$out"/bin/*; do
      if patchelf --print-interpreter "$program" >/dev/null 2>&1; then
        patchelf --set-interpreter "${pkgs.stdenv.cc.bintools.dynamicLinker}" "$program"
      fi
    done
  '' + ''
    runHook postInstall
  '';
  doInstallCheck = true;
  installCheckPhase = ''
    "$out/bin/lean" --version | grep -F "version ${version},"
  '';
  meta.platforms = builtins.attrNames bundles;
}
