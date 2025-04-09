{
  description = "PRSA Agda Library";

  inputs = 
    { 
      nixpkgs.url = "nixpkgs/nixos-24.11";
    };

  outputs = inputs @ { self, nixpkgs }:
  let 
    pkgs = import nixpkgs ({
      system = "x86_64-linux";
      config.allowUnfree = true;
    });

    ternary = pkgs.callPackage ./default.nix {};
  in rec {
    packages.x86_64-linux = {
      default = ternary;
    };
  };
}
