{
  inputs = {
    hask = {
      url = "path:///home/vglfr/test/hask";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    utils.url = "github:numtide/flake-utils";
  };

  outputs = { nixpkgs, hask, utils, ... }:
    let mkShell = system: {
      devShells.default =
        let pkgs = nixpkgs.legacyPackages.${system};
        in pkgs.mkShell {
          AGDA_DIR = "./.agda";

          packages = [
            hask.defaultPackage.${system}

            (pkgs.agda.withPackages (ps: [ ps.standard-library ]))
            pkgs.emacs
            pkgs.emacsPackages.evil
            pkgs.just
          ];

          shellHook = ''
          '';
        };
    };
    in utils.lib.eachDefaultSystem mkShell;
}
