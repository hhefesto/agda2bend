# Agda and the libraries agda2bend translates, over corepkgs and the
# haskell-pkgs snapshot (which has Agda 2.8.0 for GHC 9.10.3). corepkgs has no
# agdaPackages, so this is the little of nixpkgs' Agda builder
# (pkgs/build-support/agda) that is needed: a library is its source checked
# with `agda --build-library`, its interfaces kept beside the sources; an Agda
# "with" libraries is the agda command given their library file.
{ pkgs }:
let
  inherit (pkgs) lib;
  # the snapshot's Agda wants emacs as a build tool (to byte-compile
  # agda-mode), and corepkgs has no emacs: agda-mode's .el files are
  # installed uncompiled, which nothing here uses
  haskellPackages = pkgs.haskellPackages.extend (
    final: prev: {
      Agda = pkgs.haskell.lib.compose.overrideCabal (_: { executableToolDepends = [ ]; }) (
        prev.Agda.override { emacs = null; }
      );
    }
  );
  Agda = haskellPackages.Agda;

  libraryFileOf =
    libs:
    pkgs.writeText "libraries" (lib.concatMapStringsSep "\n" (l: "${l}/${l.libraryFile}") libs + "\n");

  # agda with LIBS on its library path (no GHC: nothing here compiles Agda)
  agdaWith =
    libs:
    pkgs.runCommand "agda-with-libraries-${Agda.version}" { nativeBuildInputs = [ pkgs.makeWrapper ]; } ''
      mkdir -p $out/bin
      makeWrapper ${Agda}/bin/agda $out/bin/agda \
        --add-flags "--library-file=${libraryFileOf libs}"
    '';

  extensions = [
    "agda"
    "agda-lib"
    "agdai"
    "lagda"
    "lagda.md"
    "lagda.org"
    "lagda.rst"
    "lagda.tex"
    "lagda.typ"
  ];

  mkLibrary =
    {
      pname,
      version,
      src,
      deps ? [ ],
      postPatch ? "",
    }:
    pkgs.stdenv.mkDerivation {
      inherit
        pname
        version
        src
        postPatch
        ;
      nativeBuildInputs = [ (agdaWith deps) ];
      env.LC_ALL = "C.UTF-8";
      buildPhase = ''
        runHook preBuild
        agda --build-library
        runHook postBuild
      '';
      installPhase = ''
        runHook preInstall
        mkdir -p $out
        find \( ${
          lib.concatMapStringsSep " -or " (e: "-name '*.${e}'") extensions
        } \) -exec cp -p --parents -t "$out" {} +
        runHook postInstall
      '';
      passthru.libraryFile = "${pname}.agda-lib";
    };

  # the versions nixpkgs had when agda2bend's runs were made (2026-10)
  standard-library = mkLibrary {
    pname = "standard-library";
    version = "2.3";
    src = pkgs.fetchFromGitHub {
      owner = "agda";
      repo = "agda-stdlib";
      rev = "v2.3";
      hash = "sha256-JOeoek6OfyIk9vwTj5QUJU6LnRzwfiG0e0ysW6zbhZ8=";
    };
  };

  agda-categories = mkLibrary {
    pname = "agda-categories";
    version = "0.3.0";
    src = pkgs.fetchFromGitHub {
      owner = "agda";
      repo = "agda-categories";
      rev = "v0.3.0";
      hash = "sha256-/3e8CkaTr0bUBgzhjAvu2RV6y0gk77VRA4PE6vutKPc=";
    };
    deps = [ standard-library ];
    # its .agda-lib pins the stdlib down to the patch version; as nixpkgs does
    postPatch = ''
      sed -Ei 's/standard-library-[0-9.]+/standard-library/' agda-categories.agda-lib
    '';
  };
in
{
  inherit
    haskellPackages
    Agda
    agdaWith
    libraryFileOf
    standard-library
    agda-categories
    ;
}
