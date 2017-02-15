Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.interfaces.rationals.
Require Import MathClasses.orders.rationals.

Section Admitted.
  Context `{Rationals R}.
  Lemma zero_le_one : (0 : R) ≤ (1 : R).
  Admitted.

  (* Might be able to break this up into smaller cases on the signs of a and b *)
  Lemma order_preserving_mult_le : forall a b c : R, 0 < c -> a ≤ b -> c * a ≤ c * b.
    intros a b c c_ge_0 a_le_b.
  Admitted.

  Lemma order_preserving_mult_lt : forall a b c : R, 0 < c -> a < b -> c * a < c * b.
    intros a b c c_gt_0 a_lt_b.
  Admitted.
End Admitted.