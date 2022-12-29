{
  # inspired by: https://serokell.io/blog/practical-nix-flakes#packaging-existing-applications
  description = "A Hello World in Haskell with a dependency and a devShell";
  inputs.nixpkgs.url = "nixpkgs";
  outputs = { self, nixpkgs }:
    let
      supportedSystems = [ "x86_64-linux" "x86_64-darwin" ];
      forAllSystems = f: nixpkgs.lib.genAttrs supportedSystems (system: f system);
      nixpkgsFor = forAllSystems (system: import nixpkgs {
        inherit system;
        overlays = [ self.overlay ];
      });
    in
    {
      overlay = (final: prev: {
        typedtc = final.haskellPackages.callCabal2nix "typedtc" ./. {};
      });
      packages = forAllSystems (system: {
         typedtc = nixpkgsFor.${system}.typedtc;
      });
      defaultPackage = forAllSystems (system: self.packages.${system}.typedtc);
      checks = self.packages;
      devShell = forAllSystems (system: let haskellPackages = nixpkgsFor.${system}.haskellPackages;
        in haskellPackages.shellFor {
          packages = p: [self.packages.${system}.typedtc];
          withHoogle = true;
          buildInputs = with haskellPackages; [
            haskell-language-server
            ghcid
            cabal-install
            fourmolu
            hlint
          ];
        # Change the prompt to show that you are in a devShell
        # shellHook = "export PS1='\\e[1;34mdev > \\e[0m'";
        });
  };
}
