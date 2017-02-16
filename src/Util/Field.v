Require Complexity.Util.Admitted.
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.interfaces.orders.
Require Import MathClasses.orders.semirings.

Section FieldLemmas.
  Context `{@Field F Ae Aplus Amult Azero Aone Aneg strong_setoids.default_apart Arecip}.

  Lemma zero_ne_one : (0 : F) ≠ (1 : F).
    unfold not.
    intros zero_eq_1.

    assert (Hyp : PropHolds (strong_setoids.default_apart 1 0)) by
      (exact (@field_nontrivial F Ae Aplus Amult Azero Aone Aneg strong_setoids.default_apart Arecip H)).
    unfold PropHolds in Hyp.
    assert (Hyp' : PropHolds (1 ≠ 0)).
    {
      unfold PropHolds.
      apply trivial_apart.
      exact Hyp.
    }
    unfold PropHolds in Hyp'.
    unfold not in Hyp'.
    apply Hyp'.
    now symmetry.
  Qed.
End FieldLemmas.

Section OrderedFieldLemmas.
  Context `{@Field F Ae Aplus Amult Azero Aone Aneg strong_setoids.default_apart Arecip}.
  Context `{@SemiRingOrder F Ae Aplus Amult Azero Aone Ale}.
  Context `{@PseudoSemiRingOrder F Ae strong_setoids.default_apart Aplus Amult Azero Aone Alt}.
  Context `{@FullPartialOrder F Ae strong_setoids.default_apart Ale Alt}.

  Lemma zero_lt_one : (0 : F) < (1 : F).
    assert (one_is_less_than_the_other : 0 < 1 \/ 1 < 0) by
      (apply apart_total_lt; apply zero_ne_one).
    assert (one_not_lt_zero : ¬ 1 < 0).
    {
      apply le_not_lt_flip.
      exact Admitted.zero_le_one.
    }
    unfold not in one_not_lt_zero.
    case one_is_less_than_the_other.
    {
      trivial.
    }
    {
      intros Hyp.
      apply one_not_lt_zero in Hyp.
      inversion Hyp.
    }
  Qed.
End OrderedFieldLemmas.