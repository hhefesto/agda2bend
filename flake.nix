{
  description = "agda2bend: Agda in, checked Bend 2 out";

  inputs = {
    # The ekala package ecosystem, as Telomare uses it. corepkgs supplies
    # stdenv, the compilers and the Haskell build machinery; haskell-pkgs
    # supplies the Hackage snapshot (Agda 2.8.0 for GHC 9.10.3) as a module
    # for corepkgs' `config.overlays.haskell`. They are consumed directly
    # rather than through the ekapkgs aggregate, which pins corepkgs from its
    # own lock file.
    corepkgs.url = "github:ekala-project/corepkgs";
    # corepkgs' formatter pulls nixpkgs in through treefmt-nix; nothing this
    # flake evaluates uses it, so it follows an input that is already here.
    corepkgs.inputs.treefmt-nix.inputs.nixpkgs.follows = "corepkgs/nix-lib";
    haskell-pkgs = {
      url = "github:ekala-project/haskell-pkgs";
      flake = false;
    };
    # Bend 2, upstream's (bendlang/bend; its `default` package is the release
    # archive, clang on its PATH). agda2bend needs no fork: whatever Bend
    # does not check is dropped and ledgered, never patched into the checker.
    bend.url = "github:bendlang/bend";
  };

  # An input's nixConfig is not applied transitively, so the cache this build
  # can draw on is named here: `ekala-corepkgs` holds the base system. Bend's
  # closure comes from cache.nixos.org.
  nixConfig = {
    extra-substituters = [ "https://ekala-corepkgs.cachix.org" ];
    extra-trusted-public-keys = [
      "ekala-corepkgs.cachix.org-1:DcZV+vegWoEzacbSdXFXU4S7728C0eS9RfGpKeyHd6w="
    ];
  };

  outputs =
    {
      self,
      corepkgs,
      haskell-pkgs,
      bend,
    }:
    let
      project =
        pkgs:
        import ./nix {
          inherit pkgs;
          src = ./.;
          bend = bend.packages.${pkgs.stdenv.hostPlatform.system}.default;
        };
    in
    corepkgs.lib.mkFlake {
      # corepkgs' stdenv is checked on x86_64-linux alone for now.
      systems = [ "x86_64-linux" ];
      modules = [ (import "${haskell-pkgs}/pkgs-module.nix") ];
      packages = pkgs: (project pkgs).packages;
      devShells = pkgs: (project pkgs).devShells;
      checks = pkgs: (project pkgs).checks;
      apps = pkgs: (project pkgs).apps;
    };
}
