{ pkgs }:

let
  buildHelper = ../bend/build_toolchain.py;
  source = pkgs.fetchurl {
    url = "https://codeload.github.com/bendlang/bend/tar.gz/f52f0338b0d07fdbd948c285dadfd14278fb5c75";
    sha256 = "d2248931441b0bfd99da5002614249647b8c48d61622267f1a35f994931b8490";
  };
in
pkgs.stdenv.mkDerivation {
  pname = "bend";
  version = "2.0.26";

  src = pkgs.fetchurl {
    url = "https://github.com/bendlang/bend/releases/download/v2.0.26/bend-2.0.26-linux-x64.tar.gz";
    sha256 = "5edcc8e5c12d525655431ab02659ddf88e362aafbe7c7bb7f783a1ffaeb6165c";
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
    description = "Unmodified Bend 2.0.26 release checker/compiler and Base";
    homepage = "https://github.com/bendlang/bend";
    license = pkgs.lib.licenses.asl20;
    platforms = [ "x86_64-linux" ];
  };
}
