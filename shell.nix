{ pkgs ? import <nixpkgs> {} }: # ignore provided nixpkgs, fetch required version
let
  unstable = (import ((builtins.fetchGit {
    url = https://github.com/NixOS/nixpkgs-channels.git;
    ref = "nixos-unstable";
    # to update, see the number of commits and the latest commit in
    # https://github.com/nixos/nixpkgs-channels/tree/nixos-unstable
    # 208,857 commits
    rev = "e4134747f5666bcab8680aff67fa3b63384f9a0f";
  })) {});
in
with unstable.pkgs;
stdenv.mkDerivation {
  name = "agda-env";
  buildInputs = [
      emacs
      haskellPackages.Agda
      (haskellPackages.ghcWithPackages (ps:
        [ ps.ieee ps.lens ]
      ))
      AgdaStdlib
      (writeShellScriptBin "agda-with-libs" ''
        ${haskellPackages.Agda.out}/bin/agda --include=${AgdaStdlib.out}/share/agda/ "$@"
      '')
  ];
}
