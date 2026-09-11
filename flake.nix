{
  description = "Lean-first verified Modelica compiler experiment";
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/fd1462031fdee08f65fd0b4c6b64e22239a77870";
  # Same reference compiler as Rust Rumoca; only the optional comparison shell
  # uses it. Ordinary development and proof CI do not build OpenModelica.
  inputs.openmodelica.url = "git+https://github.com/jgoppert/OpenModelica?submodules=1&rev=a96aa1a682c463b0fd2d285b486c09a8b7fe496d";
  inputs.openmodelica.inputs.nixpkgs.follows = "nixpkgs";
  outputs = { nixpkgs, openmodelica, ... }:
    let
      systems = [ "x86_64-linux" "aarch64-linux" ];
      eachSystem = f: nixpkgs.lib.genAttrs systems (system: f (import nixpkgs { inherit system; }));
    in {
      devShells = eachSystem (pkgs: let
        editor = import ./nix/neovim.nix { inherit pkgs; };
        python = pkgs.python3.withPackages (ps: [ ps.lxml ] ++
          pkgs.lib.optionals pkgs.stdenv.hostPlatform.isx86_64 [ ps.fmpy ]);
        # Elan installs the official version from lean-toolchain. Its build
        # identity matches mathlib's upstream proof cache, unlike pkgs.lean4.
        common = [ pkgs.elan pkgs.gcc pkgs.git pkgs.curl pkgs.ripgrep pkgs.tokei
          pkgs.zip pkgs.unzip python ];
      in {
        default = pkgs.mkShell {
          packages = common ++ [ editor ];
          EDITOR = "${editor}/bin/nvim";
          VISUAL = "${editor}/bin/nvim";
        };
        verification = pkgs.mkShell {
          packages = common;
        };
        comparison = pkgs.mkShell {
          packages = common ++ [ openmodelica.packages.${pkgs.stdenv.hostPlatform.system}.default ];
        };
      });
    };
}
