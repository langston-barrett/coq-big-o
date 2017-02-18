# Big O Notation for Coq

<!-- Shamelessly stolen readthedocs.io badge -->
[![Build Status](https://travis-ci.org/siddharthist/coq-big-o.svg?branch=master)](https://travis-ci.org/siddharthist/coq-big-o)
[![Documentation](https://readthedocs.org/projects/docs/badge/?version=latest)](https://siddharthist.github.io/coq-big-o/html/toc.html)

A flexible yet easy-to-use formalization of Big O, Big Theta, and more
Bachmann-Landau notations based on seminormed vector spaces.

## Table of Contents

<!-- markdown-toc start - Don't edit this section. Run M-x markdown-toc-generate-toc again -->
**Table of Contents**

- [Big O Notation for Coq](#big-o-notation-for-coq)
    - [Table of Contents](#table-of-contents)
    - [Features](#features)
        - [Definitions](#definitions)
        - [Theorems & Lemmas](#theorems--lemmas)
    - [API Documentation](#api-documentation)
    - [Installation](#installation)
        - [Related Work](#related-work)
    - [Contributing](#contributing)

<!-- markdown-toc end -->

## Features

### Definitions

 - Bachmann-Landau notations
  - Big O
  - Big Ω
  - Big Θ
  - little o
  - little ω
 - (Optional) Unicode notation: `f ∈ ω(g) → g ∈ Ω(f)`
 - Alternate definitions and proofs of their equivalence

### Theorems & Lemmas

This is not an exhaustive list:

 - [x] Big Θ as an equivalence relation on functions
 - [x] Big O as a partial ordering on functions
 - [x] Duality of Big O and Big Ω: f ∈ O(g) ↔ g ∈ Ω(f)
 - [x] f ∈ o(g) → f ∈ O(g)
 - [x] f ∈ ω(g) → f ∈ Ω(g)
 - [x] Various facts about the compositions of functions
 - [x] Indifference of these notations to multiplication by constants
 - [ ] If you have ideas for useful lemmas, please open an issue!
 <!-- - [ ] little o as a partial ordering on functions? -->
 <!-- - [ ] Big Ω as a partial ordering on functions? -->
 <!-- - [ ] Can O and o be combined into something like a strict order? -->

## API Documentation
You can [view the documentation online][docs] or build it locally:
```
./configure && make html && firefox html/toc.html
```
to build the API documentation with `coqdoc`.

## Installation

You can build this package using the [Nix][nix] package manager:
```
nix-build . && ls result/lib/coq/8.5/user-contrib/BigO/
```
Alternatively, you can use the the standard
```
./configure && make
```

If you're using [Nix][nix], you can easily intergrate this library with your own
package's `default.nix` or `shell.nix`, and Coq should automatically find it.
```nix
{
  stdenv,
  coq,
  pkgs ? import <nixpkgs> { }
}:
let
  coq_big_o = with pkgs; callPackage (fetchFromGitHub {
    owner  = "siddharthist";
    repo   = "coq-big-o";
    rev    = "some commit hash"; # customize this
    sha256 = "appropriate sha256 checksum"; # and this
  }) { };
in stdenv.mkDerivation {
  name = "my-coq-project";
  src = ./.;
  buildInputs = [ coq coq_big_o ];
  ...
}
```
Otherwise, just copy what you built to somewhere that Coq will find it.

### Related Work

I don't know of any. If anyone else is interested in formal complexity theory,
let me know!

This project leans heavily on the [math-classes][math-classes] library for
definitions of algebraic structures, specifically seminormed vector spaces.

## Contributing

Pull requests for fixes, new results, or anything else are welcome! Just run
```
nix-shell
```
to be dropped into a shell with all dependencies installed.
 

[nix]: https://nixos.org/nix/
[docs]: https://siddharthist.github.io/coq-big-o/html/toc.html
[math-classes]: https://github.com/math-classes/math-classes
