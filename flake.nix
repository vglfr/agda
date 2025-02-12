{
  inputs.utils.url = "github:numtide/flake-utils";

  outputs = { nixpkgs, utils, ... }:
    let mkShell = system: {
      devShells.default =
        let pkgs = nixpkgs.legacyPackages.${system};
        in pkgs.mkShell {
          AGDA_DIR = "./.agda";

          packages = [
            (pkgs.agda.withPackages (ps: [ ps.standard-library ]))
            pkgs.just
          ];

          shellHook = ''
          '';
        };
    };
    in utils.lib.eachDefaultSystem mkShell;
}
