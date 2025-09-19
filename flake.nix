{
  description = "Agda Environment";
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };
  outputs = { nixpkgs, flake-utils, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
      in
      {
        devShell = pkgs.mkShell {
          buildInputs = with pkgs; [
            just
            (agdaPackages.agda.withPackages (ps: [
              ps.standard-library
              ps.cubical
              ps.agda-categories
            ]))
          ];
        };
      }
  );
}
