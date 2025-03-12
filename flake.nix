{
  description = "BackBone Extractor for CaDiCal";
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";
    cadical = {
      url = "github:itepastra/cadical/add-flake";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    cadiback = {
      url = "github:itepastra/cadiback/add-flake";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    cryptominisat = {
      url = "github:itepastra/cryptominisat/add-flake";
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
    }:
    let
      inherit (nixpkgs) lib;
      systems = lib.intersectLists lib.systems.flakeExposed lib.platforms.linux;
      forAllSystems = lib.genAttrs systems;
      nixpkgsFor = forAllSystems (system: nixpkgs.legacyPackages.${system});
      fs = lib.fileset;
      sbva-package =
        {
          stdenv,
          eigen,
          fetchFromGitHub,
          cmake,
          autoPatchelfHook,
        }:
        stdenv.mkDerivation {
          name = "sbva";
          src = fetchFromGitHub {
            owner = "meelgroup";
            repo = "SBVA";
            rev = "5912435affe8c77ecf364093cea29e0fc5c1b5cb";
            hash = "sha256-BoR14FBH3eCPYio6l6d+oQp3/hu4U7t1STb9NgSWJ2M=";
          };
          nativeBuildInputs = [
            cmake
            autoPatchelfHook
          ];
          buildInputs = [ eigen ];
        };
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
            url = "https://ensmallen.org/files/ensmallen-2.21.1.tar.gz";
            hash = "sha256-6LZooaR0rmqWgEm0AxmWoVPuIahjOfwSFu5cssc7LA8=";
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
          zlib,
          gmp,
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
          src = fetchFromGitHub {
            owner = "itepastra";
            repo = "arjun";
            rev = "cf7e0a1e644a83b1109ce9fb4f17ab93d0348850";
            hash = "sha256-qQT16wNiRoNwpTpIxg80+SjGUhVXvuWYXFaS+kq2ezc=";
          };
          # src = fs.toSource {
          #   root = ./.;
          #   fileset = fs.unions [
          #     ./CMakeLists.txt
          #     ./cmake
          #     ./src
          #     ./arjunConfig.cmake.in
          #     ./scripts
          #   ];
          # };
          nativeBuildInputs = [
            cmake
          ];
          buildInputs = [
            zlib
            sbva
            gmp
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
          sbva = nixpkgsFor.${system}.callPackage sbva-package { };
          ensmallen = nixpkgsFor.${system}.callPackage ensmallen-package { };
          mlpack = nixpkgsFor.${system}.callPackage mlpack-package { inherit ensmallen; };

          arjun = nixpkgsFor.${system}.callPackage arjun-package {
            inherit sbva mlpack ensmallen;
            cadical = cadical.packages.${system}.cadical;
            cadiback = cadiback.packages.${system}.cadiback;
            cryptominisat5 = cryptominisat.packages.${system}.cryptominisat5;
          };
        in
        {
          inherit arjun;
          default = arjun;
        }
      );
    };
}
