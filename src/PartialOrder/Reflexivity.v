Require Import BigO.Notation.
Require Import BigO.Util.DecField.
Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.interfaces.orders.
Require Import MathClasses.interfaces.vectorspace.

Section BigOReflexivity.
  Context `{SemiNormedSpace K V}.
  Context `{SemiNormedSpace K W}.
  Context `{!FullPseudoSemiRingOrder Kle Klt}.

  Lemma big_O_refl : reflexive (V → W) big_O.
    unfold reflexive.
    intros f.
    unfold big_O.
    do 2 (exists 1; split; try (apply zero_lt_one_dec)).
    intros n' one_le_n.
    now rewrite left_identity.
  Qed.
End BigOReflexivity.