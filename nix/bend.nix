{ pkgs }:

let
  buildHelper = ../bend/build_toolchain.py;
  checkerPatch = ../patches/bend2-stack-safe-2.0.20.patch;
  source = pkgs.fetchurl {
    url = "https://codeload.github.com/bendlang/bend/tar.gz/a5269a6b2c5ccd6752b66df4bc6f60678b4f49bc";
    sha256 = "f2949ac7a1fc83ccdb7e42801c74f00481207026aef8667b3c8539d358b8b13f";
  };
in
pkgs.stdenv.mkDerivation {
  pname = "bend";
  version = "2.0.20";

  src = pkgs.fetchurl {
    url = "https://github.com/bendlang/bend/releases/download/v2.0.20/bend-2.0.20-linux-x64.tar.gz";
    sha256 = "dca589832e1645500ad258d27171ed6b5a30812bcc3088c9aedf437059be41e1";
  };
  inherit source;
  dontUnpack = true;
  nativeBuildInputs = [
    pkgs.makeWrapper
    pkgs.autoPatchelfHook
    pkgs.python3
  ];
  buildInputs = [ pkgs.stdenv.cc.cc ];
  dontConfigure = true;
  # Match the selected package's working ELF relocation; never rebuild its bundle.
  dontStrip = true;
  # The source-mode launcher is hash-pinned byte-for-byte; /bin/sh exists at runtime.
  dontPatchShebangs = true;

  buildPhase = ''
    runHook preBuild
    python3 ${buildHelper} build \
      "$src" "$source" ${checkerPatch} \
      staged toolchain.json --nix-relocation
    runHook postBuild
  '';

  installPhase = ''
    runHook preInstall
    mkdir -p "$out/bin" "$out/libexec/bend" "$out/share/bend"
    cp -r staged/bin staged/bend2 staged/guide "$out/libexec/bend/"
    makeWrapper "$out/libexec/bend/bin/bend" "$out/bin/bend" \
      --prefix PATH : "${pkgs.lib.makeBinPath [ pkgs.llvmPackages_19.clang ]}" \
      --set BEND_NO_TELEMETRY 1
    runHook postInstall
  '';

  postPhases = [ "recordToolchainPhase" ];
  recordToolchainPhase = ''
    python3 ${buildHelper} record-relocated \
      "$src" "$source" ${checkerPatch} "$out/libexec/bend" \
      "$out/share/bend/toolchain.json" ${./bend.nix}
  '';


  meta = {
    description = "Bend 2.0.20 source-mode checker/compiler (reviewed comparator patch) and Base";
    homepage = "https://github.com/bendlang/bend";
    license = pkgs.lib.licenses.asl20;
    platforms = [ "x86_64-linux" ];
  };
}
