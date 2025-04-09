{ lib, agdaPackages }:

agdaPackages.mkDerivation rec {
  version = "latest";
  pname   = "ternary-relations";
  src     = ./.;
  buildInputs = [
    agdaPackages.standard-library
  ];

  meta = {
    author = "Arjen Rouvoet";
  };
}
