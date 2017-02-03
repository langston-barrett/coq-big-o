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
    rev    = "842a514b791bd1a772aedcd0514a26928a928770";
    sha256 = "11x2dxgdya0wvibl0k5g52izxg9si7yks2y93cyf6j87cn8xy3s1";
  }) { };

  # coq_typeclass_hierarchy = pkgs.callPackage "${coq_typeclass_hierarchy_src}" { };
  # self = with pinned_pkgs; callPackage ./default.nix { };

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
