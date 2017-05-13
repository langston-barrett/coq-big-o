{ stdenv, fetchFromGitHub, coq }:

stdenv.mkDerivation {
  name = "math-classes";

  src = fetchFromGitHub {
    owner  = "math-classes";
    repo   = "math-classes";
    rev    = "578caf8adddc676e977f4ee12e483ed21e7ed870";
    sha256 = "05j11isvwg7sxsa386dixkrzxgf6lq0y8macmb1j156cg3kpfr5r";
  };

  buildInputs = [ coq ];
  enableParallelBuilding = true;
  installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";

  meta = with stdenv.lib; {
    homepage = https://math-classes.github.io;
    description = "A library of abstract interfaces for mathematical structures in Coq.";
    maintainers = with maintainers; [ siddharthist ];
    platforms = coq.meta.platforms;
  };
}
