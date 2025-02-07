{
  inputs.utils.url = "github:numtide/flake-utils";

  outputs = { nixpkgs, utils, ... }:
    let mkShell = system: {
      devShells.default =
        let pkgs = nixpkgs.legacyPackages.${system};
        in pkgs.mkShell {
          packages = [
            pkgs.agda
          ];

          shellHook = ''
          '';
        };
    };
    in utils.lib.eachDefaultSystem mkShell;
}
