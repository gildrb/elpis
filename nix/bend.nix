{ pkgs }:

let
  buildHelper = ../bend/build_toolchain.py;
  source = pkgs.fetchurl {
    url = "https://codeload.github.com/bendlang/bend/tar.gz/c8691aa93b0b1bb2fda277d9fc88c5aa797e88de";
    sha256 = "1e5006bff6cdf9f03b2e60f33c45ed1d91fa9dbbd633466c9f22e48880f9351a";
  };
in
pkgs.stdenv.mkDerivation {
  pname = "bend";
  version = "2.0.29";

  src = pkgs.fetchurl {
    url = "https://github.com/bendlang/bend/releases/download/v2.0.29/bend-2.0.29-linux-x64.tar.gz";
    sha256 = "e0ff4fa44581b42f6024d2a1128e7e518219a502cb726030c714a5c23d61726e";
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
  # The release launcher is hash-pinned byte-for-byte; /bin/sh exists at runtime.
  dontPatchShebangs = true;

  buildPhase = ''
    runHook preBuild
    python3 ${buildHelper} build \
      "$src" "$source" \
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
      "$src" "$source" "$out/libexec/bend" \
      "$out/share/bend/toolchain.json" ${./bend.nix}
  '';


  meta = {
    description = "Unmodified Bend 2.0.29 release checker/compiler and Base";
    homepage = "https://github.com/bendlang/bend";
    license = pkgs.lib.licenses.asl20;
    platforms = [ "x86_64-linux" ];
  };
}
