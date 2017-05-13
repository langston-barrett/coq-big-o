{ stdenv, fetchFromGitHub, coq }:

stdenv.mkDerivation {
  name = "math-classes";

  src = fetchFromGitHub {
    owner  = "math-classes";
    repo   = "math-classes";
    rev    = "6f523f46d378913d0294094a5273a6a8de0b5dbf";
    sha256 = "1rm0h2yqxdv52wmc1zax4bb6ir89h9ij3jhzbdl8829n22b6v7mn";
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
