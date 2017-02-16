Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.interfaces.rationals.
Require Import MathClasses.orders.rationals.
Require Import MathClasses.orders.semirings.
Require Import MathClasses.interfaces.orders.

Section AdmittedSemiring.
  Context `{SemiRingOrder R}.
  Context `{!StrictSemiRingOrder Rlt}.

  (* Might be able to break this up into smaller cases on the signs of a and b *)
  Lemma order_preserving_mult_le : forall a b c : R, 0 < c -> a ≤ b -> c * a ≤ c * b.
    intros a b c c_ge_0 a_le_b.
  Admitted.

  Lemma order_preserving_mult_lt : forall a b c : R, 0 < c -> a < b -> c * a < c * b.
    intros a b c c_gt_0 a_lt_b.
  Admitted.

End AdmittedSemiring.

(*
 We require stronger assumptions for this lemma, because we only use it in the
 stronger setting, and I'm not sure it's true for weaker strutures like
 Semirings.
 *)
Section AdmittedField.
  Context `{@Field F Ae Aplus Amult Azero Aone Aneg strong_setoids.default_apart Arecip}.
  Context `{@SemiRingOrder F Ae Aplus Amult Azero Aone Ale}.
  Context `{@PseudoSemiRingOrder F Ae strong_setoids.default_apart Aplus Amult Azero Aone Alt}.
  Context `{@FullPartialOrder F Ae strong_setoids.default_apart Ale Alt}.

  Lemma zero_le_one : (0 : F) ≤ (1 : F).
  Admitted.
End AdmittedField.

Section AdmittedDecField.
  Context `{DecField K}.
  Context `{!TrivialApart K} `{!FullPseudoSemiRingOrder Kle Klt}.

  Lemma zero_le_one_dec : (0 : K) ≤ (1 : K).
  Admitted.
End AdmittedDecField.