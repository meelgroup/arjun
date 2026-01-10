{
  description = "minimal independent set calculator and CNF minimizer";
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";
    cadical = {
      url = "github:meelgroup/cadical/master";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    cadiback = {
      url = "github:meelgroup/cadiback/main";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    cryptominisat = {
      url = "github:msoos/cryptominisat/working-on-synth";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    sbva = {
      url = "github:meelgroup/sbva/master";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    evalmaxsat = {
      url = "github:meelgroup/EvalMaxSAT/master";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };
  outputs =
    {
      self,
      nixpkgs,
      cadical,
      cadiback,
      cryptominisat,
      sbva,
      evalmaxsat,
    }:
    let
      inherit (nixpkgs) lib;
      systems = lib.intersectLists lib.systems.flakeExposed lib.platforms.linux;
      forAllSystems = lib.genAttrs systems;
      nixpkgsFor = forAllSystems (system: nixpkgs.legacyPackages.${system});
      fs = lib.fileset;
      ensmallen-package =
        {
          stdenv,
          cmake,
          fetchzip,
          armadillo,
        }:
        stdenv.mkDerivation {
          name = "ensmallen";
          src = fetchzip {
            url = "https://ensmallen.org/files/ensmallen-2.22.2.tar.gz";
            hash = "sha256-awM1Si6AcbAi4bfr2nrcGngcqTYMp9m6g3UPpMC4/Ok=";
          };
          nativeBuildInputs = [ cmake ];
          buildInputs = [ armadillo ];
        };
      mlpack-package =
        {
          stdenv,
          fetchFromGitHub,
          lsd,
          cmake,
          armadillo,
          ensmallen,
          cereal,
          pkg-config,
        }:
        stdenv.mkDerivation {
          name = "mlpack";
          src = fetchFromGitHub {
            "owner" = "mlpack";
            "repo" = "mlpack";
            "rev" = "4.4.0";
            "hash" = "sha256-EPz8qPTUAldS+k5/qkZf8EKXKjnxElfJxlTEMLPhTQE=";
          };
          nativeBuildInputs = [
            pkg-config
            cmake
            armadillo
          ];
          buildInputs = [
            ensmallen
            cereal
          ];
        };
      arjun-package =
        {
          stdenv,
          fetchFromGitHub,
          cmake,
          sbva,
          evalmaxsat,
          zlib,
          gmp,
          mpfr,
          cadiback,
          pkg-config,
          mlpack,
          armadillo,
          cereal,
          ensmallen,
          cadical,
          cryptominisat5,
        }:
        stdenv.mkDerivation {
          name = "arjun";
          src = fs.toSource {
            root = ./.;
            fileset = fs.unions [
              ./CMakeLists.txt
              ./cmake
              ./src
              ./arjunConfig.cmake.in
              ./scripts
            ];
          };
          nativeBuildInputs = [
            cmake
          ];
          buildInputs = [
            zlib
            sbva
            evalmaxsat
            gmp
            mpfr
            cadiback
            mlpack
            armadillo
            cereal
            ensmallen
            cadical
            cryptominisat5
          ];
        };
    in
    {
      packages = forAllSystems (
        system:
        let
          ensmallen = nixpkgsFor.${system}.callPackage ensmallen-package { };
          mlpack = nixpkgsFor.${system}.callPackage mlpack-package { inherit ensmallen; };

          arjun = nixpkgsFor.${system}.callPackage arjun-package {
            inherit mlpack ensmallen;
            cadical = cadical.packages.${system}.cadical;
            cadiback = cadiback.packages.${system}.cadiback;
            cryptominisat5 = cryptominisat.packages.${system}.cryptominisat5;
            sbva = sbva.packages.${system}.sbva;
            evalmaxsat = evalmaxsat.packages.${system}.evalmaxsat;
          };
        in
        {
          inherit arjun;
          default = arjun;
        }
      );
    };
}
