{
  description = "agda2bend: Agda in, checked Bend 2 out";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  # Bend 2, upstream's (bendlang/bend; its `default` package is the release
  # archive).  agda2bend needs no fork: whatever Bend does not check is
  # dropped and ledgered, never patched into the checker.
  inputs.bend2 = {
    url = "github:bendlang/bend";
    inputs.nixpkgs.follows = "nixpkgs";
  };

  outputs =
    { self, nixpkgs, bend2 }:
    let
      systems = [
        "x86_64-linux"
        "aarch64-linux"
      ];
      forAllSystems = nixpkgs.lib.genAttrs systems;
      pkgsFor =
        system:
        import nixpkgs {
          inherit system;
        };
      # What a build may see: the .bend sources and the C and JS of the one
      # effect (bend/effs/wall.c, the wall clock the logs are stamped with).
      # Prose edits rebuild nothing.
      bendSrc = nixpkgs.lib.fileset.toSource {
        root = ./.;
        fileset = nixpkgs.lib.fileset.unions [
          (nixpkgs.lib.fileset.fileFilter (f: f.hasExt "bend") ./bend)
          ./bend/effs
        ];
      };
      # the tests' fixtures: Agda sources, their exports and the goldens
      testSrc = nixpkgs.lib.fileset.toSource {
        root = ./.;
        fileset = nixpkgs.lib.fileset.unions [
          (nixpkgs.lib.fileset.fileFilter (f: f.hasExt "bend") ./bend)
          ./bend/effs
          ./bend/tests/fixtures
        ];
      };
      # the pinned bend command (upstream's wrapper puts clang on its PATH;
      # this one turns telemetry off: the daily version check, main.ts)
      bendFor =
        pkgs:
        pkgs.writeShellScriptBin "bend" ''
          export BEND_NO_TELEMETRY=1
          exec ${bend2.packages.${pkgs.stdenv.hostPlatform.system}.default}/bin/bend "$@"
        '';
      # A Bend 2 program compiled to a native binary (C via clang).
      bendBinary =
        pkgs: name: entry:
        pkgs.runCommand name { nativeBuildInputs = [ (bendFor pkgs) ]; } ''
          export HOME=$TMPDIR
          cp -r ${bendSrc}/bend src
          chmod -R u+w src
          mkdir -p $out/bin
          bend src/${entry} -o $out/bin/${name}
        '';
      # The front end (tools/agda-export, its FORMAT.md): Agda 2.8.0 with
      # one more backend, built on nixpkgs' Haskell Agda library, that writes
      # every module's elaborated definitions as S-expressions.  It decides
      # nothing; all translation is Bend's.
      agdaExportFor =
        pkgs:
        pkgs.haskell.lib.justStaticExecutables (
          pkgs.haskellPackages.callCabal2nix "agda-export" (nixpkgs.lib.fileset.toSource {
            root = ./tools/agda-export;
            fileset = ./tools/agda-export;
          }) { }
        );
      # its AGDA_DIR: the libraries it resolves (standard-library and
      # agda-categories, interfaces prebuilt) and no defaults
      agdaExportDir =
        pkgs:
        pkgs.runCommand "agda-export-dir" { } ''
          mkdir -p $out
          printf '%s\n' ${pkgs.agdaPackages.standard-library}/standard-library.agda-lib \
            ${pkgs.agdaPackages.agda-categories}/agda-categories.agda-lib > $out/libraries
          touch $out/defaults
        '';
    in
    {
      packages = forAllSystems (
        system:
        let
          pkgs = pkgsFor system;
        in
        {
          bend = bendFor pkgs;
          # `agda-export --export-dir=OUT FILE.agda`, run from the root of
          # FILE's library: OUT/<Module>.sexp for FILE and every module it
          # imports, OUT/_index.sexp (tools/agda-export/FORMAT.md).  AGDA_DIR
          # defaults to standard-library and agda-categories.
          agda-export-unwrapped = agdaExportFor pkgs;
          agda-export = pkgs.runCommand "agda-export" { nativeBuildInputs = [ pkgs.makeWrapper ]; } ''
            makeWrapper ${agdaExportFor pkgs}/bin/agda-export $out/bin/agda-export \
              --set-default AGDA_DIR ${agdaExportDir pkgs}
          '';
          # agda2bend (bend/Agda2Bend.bend): `agda2bend translate FILE.agda
          # OUT` runs agda-export on FILE into OUT/export and translates its
          # module's cone into OUT/src, keeping only what the pinned bend
          # checks (OUT/ledger.tsv says why the rest went; `agda2bend report
          # OUT` ranks the causes).  The wrapper gives it the pinned bend
          # (BEND), agda-export (AGDA_EXPORT, with its AGDA_DIR) and mkdir,
          # realpath.
          agda2bend-unwrapped = bendBinary pkgs "agda2bend" "Agda2Bend.bend";
          agda2bend = pkgs.runCommand "agda2bend" { nativeBuildInputs = [ pkgs.makeWrapper ]; } ''
            makeWrapper ${self.packages.${system}.agda2bend-unwrapped}/bin/agda2bend $out/bin/agda2bend \
              --set-default BEND ${bendFor pkgs}/bin/bend \
              --set-default AGDA_EXPORT ${self.packages.${system}.agda-export}/bin/agda-export \
              --prefix PATH : ${pkgs.lib.makeBinPath [ pkgs.coreutils ]}
          '';
          default = self.packages.${system}.agda2bend;
        }
      );

      checks = forAllSystems (
        system:
        let
          pkgs = pkgsFor system;
        in
        {
          # bend/tests/agda2bend.bend, compiled (the interpreter's stack does
          # not hold Level): the S-expression reader, the parser of Agda, the
          # printer, the gate, and the whole translation of the committed
          # cones (Function.Base, A2bFix) against their goldens.  It must
          # print `ok ` lines only, OKS of them.
          tests =
            let
              oks = 57;
            in
            pkgs.runCommand "agda2bend-tests" { nativeBuildInputs = [ (bendFor pkgs) ]; } ''
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
              if [ "$n" != ${toString oks} ] || [ "$all" != ${toString oks} ]; then
                echo "agda2bend-tests: want ${toString oks} ok lines and nothing else, got $n of $all lines"
                exit 1
              fi
              cp out.txt $out
            '';
          inherit (self.packages.${system}) agda2bend agda-export;
        }
      );

      apps = forAllSystems (system: {
        bend = {
          type = "app";
          program = "${self.packages.${system}.bend}/bin/bend";
          meta.description = "The pinned Bend 2 compiler and checker";
        };
        agda-export = {
          type = "app";
          program = "${self.packages.${system}.agda-export}/bin/agda-export";
          meta.description = "Agda 2.8.0's elaborated definitions as S-expressions (agda2bend's front end)";
        };
        agda2bend = {
          type = "app";
          program = "${self.packages.${system}.agda2bend}/bin/agda2bend";
          meta.description = "Agda in, checked Bend 2 out: translate FILE.agda OUT, emit DIR OUT, report OUT";
        };
        default = self.apps.${system}.agda2bend;
      });

      devShells = forAllSystems (
        system:
        let
          pkgs = pkgsFor system;
        in
        {
          default = pkgs.mkShell {
            packages = [
              (bendFor pkgs)
              self.packages.${system}.agda-export
              (pkgs.agda.withPackages (p: [ p.standard-library p.agda-categories ]))
            ];
          };
        }
      );
    };
}
