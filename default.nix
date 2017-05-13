{
  pkgs ? import <nixpkgs> { }
}:

# To use: run `nix-shell` or `nix-shell --run "exec zsh"`
# https://nixos.org/wiki/Development_Environments
# http://nixos.org/nix/manual/#sec-nix-shell

let
  # Pin a nixpkgs version
  pinned_pkgs = import (pkgs.fetchFromGitHub {
    owner  = "NixOS";
    repo   = "nixpkgs";
    # TODO: 17.03?
    # This is the commit that included math-classes. Thanks @vbgl!
    rev    = "d486fb053b3f148e5989d6cd3e07a69eaf75d0bf";
    sha256 = "14s283bwh77266zslc96gr7zqaijq5b9k4wp272ry27j5q8l3h4i";
  }) { };

  ### Dependencies
  coq = pinned_pkgs.coq_8_5;
  math_classes = pkgs.callPackage ./nix/math-classes.nix { };

in with pinned_pkgs; stdenv.mkDerivation {
  name = "coq${coq.coq-version}-big-o";
  src = ./.;
  buildInputs = [
    coq
    # TODO: update to a version of math-classes that includes the triangle inequality
    math_classes
    # coqPackages_8_5.math-classes
  ];
  enableParallelBuilding = true;
  installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";

  meta = with stdenv.lib; {
    homepage = https://github.com/siddharthist/coq-big-o;
    description = "A flexible yet easy-to-use formalization of Big O notation";
    maintainers = with maintainers; [ siddharthist ];
    platforms = coq.meta.platforms;
  };
}
