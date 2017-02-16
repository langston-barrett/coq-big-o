Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.interfaces.rationals.
Require Import MathClasses.orders.rationals.
Require Import MathClasses.orders.semirings.
Require Import MathClasses.orders.dec_fields.
Require Import MathClasses.interfaces.orders.

Section AdmittedDecField.
  Context `{DecField K}.
  Context `{!FullPseudoSemiRingOrder Kle Klt}.

  Lemma zero_le_one_dec : (0 : K) ≤ (1 : K).
  Admitted.
End AdmittedDecField.