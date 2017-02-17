Require BigO.Util.Admitted.
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.interfaces.orders.
Require Import MathClasses.orders.dec_fields.
Require Import MathClasses.orders.semirings.

Section NoOrder.
  Context `{DecField K}.
  Context `{!FullPseudoSemiRingOrder Kle Klt}.
  Lemma plus_le : forall x y z : K, 0 < x -> 0 < y -> x + y ≤ z -> x ≤ z.
    intros x y z zero_lt_x zero_lt_y x_plus_y.
    destruct (decompose_le x_plus_y) as [a Hyp].
    destruct Hyp as [zero_le_a z_eq].

    apply (compose_le x z (y + a)).
    {
      setoid_replace 0 with (0 + 0) by (now rewrite left_identity).
      apply (plus_le_compat 0 _ 0 _); try assumption.
      now apply lt_le.
    }
    {
      now rewrite associativity.
    }
  Qed.
End NoOrder.

Section DecFieldLemmas.
  Context `{DecField K}.
  Context `{!FullPseudoSemiRingOrder Kle Klt}.
  Context `{!TotalOrder Kle}.

  Lemma zero_ne_one : (0 : K) ≠ (1 : K).
    unfold not.
    intros zero_eq_1.

    assert (Hyp : PropHolds (strong_setoids.default_apart 1 0)) by
      (exact (@decfield_nontrivial K Ae Aplus Amult Azero Aone Anegate Adec_recip H)).
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

  Lemma zero_lt_one_dec : (0 : K) < (1 : K).
    assert (one_is_less_than_the_other : 0 < 1 \/ 1 < 0) by
      (apply apart_total_lt; apply zero_ne_one).
    assert (one_not_lt_zero : ¬ 1 < 0).
    {
      apply le_not_lt_flip.
      exact Admitted.zero_le_one_dec.
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

  Lemma dec_recip_inverse_reverse : forall x : K, x ≠ 0 -> (/ x) * x = 1.
    intros x.
    rewrite commutativity.
    apply dec_recip_inverse.
  Qed.

  Lemma dec_recip_inverse_ge_0 : forall x : K, 0 < x -> (/ x) * x = 1.
    intros x x_gt_0.
    apply dec_recip_inverse_reverse.
    now apply lt_ne_flip.
  Qed.

  Lemma order_preserving_mult_le : forall a b c : K, 0 < c -> a ≤ b -> c * a ≤ c * b.
    intros a b c c_ge_0 a_le_b.
    now apply (order_preserving ((.*.) c) a b).
  Qed.

  Lemma order_preserving_mult : forall x : K, 0 < x -> OrderPreserving (mult x).
    intros x x_ge_0.
    repeat (split; try apply _).
    intros a b.
    intros a_leq_b.
    now apply order_preserving_mult_le.
  Qed.

  Lemma order_preserving_mult_lt : forall a b c : K, 0 < c -> a < b -> c * a < c * b.
    intros a b c c_gt_0 a_lt_b.
    now apply (strictly_order_preserving ((.*.) c) a b).
  Qed.

  Require Import Coq.setoid_ring.Ring.
  (* this is definitely in math-classes *)
  Add Ring R: (MathClasses.theory.rings.stdlib_ring_theory K).
  Lemma mult_pos_gt_0 : forall x y : K, 0 < x -> 0 < y -> 0 < x * y.
    intros x y x_ge_0 y_ge_0.
    assert (Hyp : x * 0 = 0) by ring.
    rewrite <- Hyp.
    apply order_preserving_mult_lt; assumption.
  Qed.
End DecFieldLemmas.