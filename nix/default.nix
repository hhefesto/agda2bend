# Everything the flake exposes, as plain Nix over a package set (corepkgs with
# the haskell-pkgs snapshot) and the pinned Bend: the packages, the checks,
# the apps and the development shell. flake.nix calls this with the flake's
# source; default.nix and shell.nix call it through nix/legacy.nix.
{
  pkgs,
  src,
  bend,
}:
let
  inherit (pkgs) lib;
  agda = import ./agda.nix { inherit pkgs; };

  # the pinned bend command, telemetry off (upstream's launcher otherwise
  # checks for a newer release once a day)
  bendCmd = pkgs.writeShellScriptBin "bend" ''
    export BEND_NO_TELEMETRY=1
    exec ${bend}/bin/bend "$@"
  '';

  # What a build may see: the .bend sources and the C and JS of the one effect
  # (bend/effs/wall.c, the wall clock the logs are stamped with). Prose edits
  # rebuild nothing.
  bendFiles = lib.fileset.fileFilter (f: f.hasExt "bend") (src + "/bend");
  bendSrc = lib.fileset.toSource {
    root = src;
    fileset = lib.fileset.unions [
      bendFiles
      (src + "/bend/effs")
    ];
  };
  # the tests' fixtures too: Agda sources, their exports and the goldens
  testSrc = lib.fileset.toSource {
    root = src;
    fileset = lib.fileset.unions [
      bendFiles
      (src + "/bend/effs")
      (src + "/bend/tests/fixtures")
    ];
  };

  # A Bend 2 program compiled to a native binary (C via clang).
  bendBinary =
    name: entry:
    pkgs.runCommand name { nativeBuildInputs = [ bendCmd ]; } ''
      export HOME=$TMPDIR
      cp -r ${bendSrc}/bend src
      chmod -R u+w src
      mkdir -p $out/bin
      bend src/${entry} -o $out/bin/${name}
    '';

  # The front end (tools/agda-export, its FORMAT.md): Agda 2.8.0 with one more
  # backend, on the snapshot's Haskell Agda library, that writes every module's
  # elaborated definitions as S-expressions. It decides nothing; all
  # translation is Bend's.
  agda-export-unwrapped = pkgs.haskell.lib.compose.justStaticExecutables (
    agda.haskellPackages.callPackage ./agda-export.nix {
      src = lib.fileset.toSource {
        root = src + "/tools/agda-export";
        fileset = src + "/tools/agda-export";
      };
    }
  );
  # its AGDA_DIR: the libraries it resolves (the standard library and
  # agda-categories, interfaces prebuilt) and no defaults
  agdaExportDir = pkgs.runCommand "agda-export-dir" { } ''
    mkdir -p $out
    cp ${agda.libraryFileOf [ agda.standard-library agda.agda-categories ]} $out/libraries
    touch $out/defaults
  '';
  # `agda-export --export-dir=OUT FILE.agda`, run from the root of FILE's
  # library: OUT/<Module>.sexp for FILE and every module it imports,
  # OUT/_index.sexp (tools/agda-export/FORMAT.md). AGDA_DIR defaults to the
  # standard library and agda-categories.
  agda-export = pkgs.runCommand "agda-export" { nativeBuildInputs = [ pkgs.makeWrapper ]; } ''
    makeWrapper ${agda-export-unwrapped}/bin/agda-export $out/bin/agda-export \
      --set-default AGDA_DIR ${agdaExportDir}
  '';

  # agda2bend (bend/Agda2Bend.bend): `agda2bend translate FILE.agda OUT` runs
  # agda-export on FILE into OUT/export and translates its module's cone into
  # OUT/src, keeping only what the pinned bend checks (OUT/ledger.tsv says why
  # the rest went; `agda2bend report OUT` ranks the causes). The wrapper gives
  # it the pinned bend (BEND), agda-export (AGDA_EXPORT, with its AGDA_DIR) and
  # mkdir, realpath.
  agda2bend-unwrapped = bendBinary "agda2bend" "Agda2Bend.bend";
  agda2bend = pkgs.runCommand "agda2bend" { nativeBuildInputs = [ pkgs.makeWrapper ]; } ''
    makeWrapper ${agda2bend-unwrapped}/bin/agda2bend $out/bin/agda2bend \
      --set-default BEND ${bendCmd}/bin/bend \
      --set-default AGDA_EXPORT ${agda-export}/bin/agda-export \
      --prefix PATH : ${lib.makeBinPath [ pkgs.coreutils ]}
  '';

  # the agda command over the same libraries (`agda-stdlib`: the standard
  # library alone, what ana's transcript harness checks Agda with)
  agda-with-libraries = agda.agdaWith [
    agda.standard-library
    agda.agda-categories
  ];
  agda-stdlib = agda.agdaWith [ agda.standard-library ];

  packages = {
    inherit
      agda2bend
      agda2bend-unwrapped
      agda-export
      agda-export-unwrapped
      agda-with-libraries
      agda-stdlib
      ;
    inherit (agda) standard-library agda-categories;
    bend = bendCmd;
    default = agda2bend;
  };

  checks = {
    inherit agda2bend agda-export;
    # bend/tests/agda2bend.bend, compiled (the interpreter's stack does not
    # hold Level): the S-expression reader, the parser of Agda, the printer,
    # the gate, and the whole translation of the committed cones
    # (Function.Base, A2bFix) against their goldens. It must print `ok ` lines
    # only, OKS of them.
    tests =
      let
        oks = toString 57;
      in
      pkgs.runCommand "agda2bend-tests" { nativeBuildInputs = [ bendCmd ]; } ''
        export HOME=$TMPDIR
        cp -r ${testSrc}/bend src
        chmod -R u+w src
        bend src/tests/agda2bend.bend -o tests
        cd src/tests
        ../../tests > ../../out.txt 2>&1 || { cat ../../out.txt; exit 1; }
        cd ../..
        cat out.txt
        n=$(grep -c '^ok ' out.txt || true)
        all=$(wc -l < out.txt)
        if [ "$n" != ${oks} ] || [ "$all" != ${oks} ]; then
          echo "agda2bend-tests: want ${oks} ok lines and nothing else, got $n of $all lines"
          exit 1
        fi
        cp out.txt $out
      '';
  };

  apps = {
    default = "${agda2bend}/bin/agda2bend";
    agda2bend = "${agda2bend}/bin/agda2bend";
    agda-export = "${agda-export}/bin/agda-export";
    bend = "${bendCmd}/bin/bend";
  };

  # `nix develop`: bend, agda-export and agda over the same libraries.
  # corepkgs has no plain `mkShell`, so the shell is the derivation such a
  # `mkShell` makes, as in Telomare.
  devShells.default = pkgs.stdenvNoCC.mkDerivation {
    name = "agda2bend";
    nativeBuildInputs = [
      bendCmd
      agda-export
      agda-with-libraries
    ];
    env.BEND_NO_TELEMETRY = "1";
    # corepkgs builds with structured attributes, which leave `name` an
    # unexported shell variable; prompts that show the environment's name
    # read `$name`.
    shellHook = ''
      export name
    '';
    phases = [ "buildPhase" ];
    buildPhase = ''
      echo "This derivation is not meant to be built, only to be used with nix develop"
      touch $out
    '';
  };
in
{
  inherit
    packages
    checks
    apps
    devShells
    ;
}
