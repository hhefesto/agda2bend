# agda-export (tools/agda-export/agda-export.cabal), in the form cabal2nix
# writes: the package set has no top-level cabal2nix, so callCabal2nix cannot
# run at evaluation time (as in Telomare). Keep the dependency list equal to
# the .cabal's build-depends. nix/default.nix gives `src`.
{
  mkDerivation,
  Agda,
  base,
  bytestring,
  containers,
  deepseq,
  directory,
  filepath,
  lib,
  mtl,
  text,
  time,
  transformers,
  unix,
  unordered-containers,
  src,
}:
mkDerivation {
  pname = "agda-export";
  version = "0.1.0";
  inherit src;
  isLibrary = false;
  isExecutable = true;
  executableHaskellDepends = [
    Agda
    base
    bytestring
    containers
    deepseq
    directory
    filepath
    mtl
    text
    time
    transformers
    unix
    unordered-containers
  ];
  description = "Agda's elaborated definitions as S-expressions (agda2bend's front end)";
  license = lib.licenses.mit;
  mainProgram = "agda-export";
}
