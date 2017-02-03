# Complexity Theory in Coq

[![Build Status](https://travis-ci.org/siddharthist/coq-complexity.svg?branch=master)](https://travis-ci.org/siddharthist/coq-complexity)

This library defines basic notions of complexity: decision problems, function
runtimes, big-O notation, nondeterminism, complexity classes, and more.

## Table of Contents

<!-- markdown-toc start - Don't edit this section. Run M-x markdown-toc-generate-toc again -->
**Table of Contents**

<!-- markdown-toc end -->


## 

## Installation

You can build this package using the [Nix][nix] package manager:
```
nix-build . && ls result/lib/coq/8.5/user-contrib/Complexity/
```
Alternatively, you can download the dependencies and then use the the standard
```
./configure && make
```

If you're using [Nix][nix], you can easily intergrate this library with your own
package's `default.nix` or `shell.nix`, and your `COQPATH` environment variable
will automatically be set correctly.
```nix
{ stdenv, coq }:
let
  coq_complexity = 
    pkgs.callPackage ./path/to/coq-complexity/default.nix { };
in stdenv.mkDerivation {
  name = "my-coq-project";
  src = ./.;
  buildInputs = [ coq coq_complexity ];
  ...
}
```
Otherwise, just copy what you built to somewhere that Coq will find it.

## Usage

### Organization of Modules

TODO

### Documentation
Run
```
./configure && make html && firefox html/toc.html
```
to build the API documentation with `coqdoc`.

## Contributing

TODO

Pull requests for fixes, new classes, extra instances, or more tests are
welcome! Just run
```
nix-shell
```
to be dropped into a shell with all dependencies installed.
 
## Design and Related Work

### Design
TODO

### References
TODO

[nix]: https://nixos.org/nix/
