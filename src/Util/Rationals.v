Require Import Complexity.Util.Admitted.
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.interfaces.orders.
Require Import MathClasses.interfaces.rationals.
Require Import MathClasses.orders.rationals.

Section Lemmas.
  Context `{Rationals R}.

  (* use the "ring" tactic *)
  Require Import Coq.setoid_ring.Ring.
  Add Ring R: (MathClasses.theory.rings.stdlib_ring_theory R).

  Instance neq_symmetric : Symmetric (≠).
  Proof.
    unfold Symmetric.
    intros x y x_neq_y.
    unfold not.
    unfold not in x_neq_y.
    intros y_eq_x.
    apply x_neq_y.
    now symmetry.
  Qed.

  Lemma zero_ne_one : (0 : R) ≠ (1 : R).
    assert (Hyp : PropHolds (1 ≠ 0)) by
      (exact (@decfield_nontrivial R e plus0 mult0 zero0 one0 neg recip0
            (@rationals_field R e plus0 mult0 zero0 one0 neg recip0 U H))).
    unfold PropHolds in Hyp.
    now symmetry.
  Qed.

  Lemma zero_lt_one : (0 : R) < (1 : R).
    unfold lt.
    unfold rationals_lt.
    unfold orders.dec_lt.
    split.
     - exact zero_le_one.
     - exact zero_ne_one.
  Qed.

  Lemma order_preserving_mult : forall x : R, 0 < x -> OrderPreserving (mult x).
    intros x x_ge_0.
    repeat (split; try apply _).
    intros a b.
    intros a_leq_b.
    now apply order_preserving_mult_le.
  Qed.

  (* This might be a lemma of math-classes? *)
  Lemma dec_recip_inverse_reverse : forall x : R, x ≠ 0 -> (/ x) * x = 1.
    intros x.
    rewrite commutativity.
    apply dec_recip_inverse.
  Qed.

  Lemma dec_recip_inverse_ge_0 : forall x : R, 0 < x -> (/ x) * x = 1.
    intros x x_gt_0.
    apply dec_recip_inverse_reverse.
    destruct x_gt_0 as [? ?].
    now symmetry.
  Qed.

  Lemma mult_pos_gt_0 : forall x y : R, 0 < x -> 0 < y -> 0 < x * y.
    intros x y x_ge_0 y_ge_0.
    assert (Hyp : x * 0 = 0) by ring.
    rewrite <- Hyp.
    apply order_preserving_mult_lt; assumption.
  Qed.
End Lemmas.