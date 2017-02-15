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
  coq_typeclass_hierarchy = with pinned_pkgs; callPackage (fetchFromGitHub {
    owner  = "siddharthist";
    repo   = "coq-typeclass-hierarchy";
    # This is the commit that made default.nix into a function
    rev    = "c079b02364c94b7aa18fc6cb02921ad6a76eb20e";
    sha256 = "1l5h02k0j2df4r8jvvf8nws777rda4piy2mfmvl5k2fgwz9slb1r";
  }) { };

in with pinned_pkgs; stdenv.mkDerivation {
  name = "coq${coq.coq-version}-complexity";
  src = ./.;
  buildInputs = [
    coq
    coq_typeclass_hierarchy
    coqPackages_8_5.math-classes # TODO: this is a transitive dep. can we remove it?
  ];
  enableParallelBuilding = true;
  installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";

  meta = with stdenv.lib; {
    homepage = https://github.com/siddharthist/coq-complexity;
    description = "A development of the fundamentals of complexity theory in Coq";
    maintainers = with maintainers; [ siddharthist ];
    platforms = coq.meta.platforms;
  };
}
