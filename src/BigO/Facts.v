Require Import Complexity.Util.DecField.
Require Import Complexity.BigO.Notation.
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.interfaces.orders.
Require Import MathClasses.interfaces.vectorspace.
Require Import MathClasses.orders.dec_fields.

Section OAndOmega.
  Context `{@SemiNormedSpace
              K V
              Ke Kle Kzero Knegate Kabs Vnorm Ke Kplus Kmult Kzero Kone Knegate Krecip
              Ve Vop Vunit Vnegate smkv
           }.
  Context `{!FullPseudoSemiRingOrder Kle Klt}.
  Context `{forall x y : K, Decision (x = y)}.

  (**
  A general and useful result about the duality of O and Ω.
  Informal proof/overview:
    - TODO
  *)
  Lemma O_and_Omega : forall f g : (V -> V), f ∈ O(g) <-> g ∈ Ω(f).
    split.
    {
      (* Unfurl our hypothesis *)
      intros f_O_g.
      unfold big_O in f_O_g.
      destruct f_O_g as [k [zero_lt_k [n0 [zero_lt_n0 f_O_g]]]].

      unfold big_Omega.
      exists (/k).
      split.
      {
        now apply MathClasses.orders.dec_fields.pos_dec_recip_compat.
      }
      {
        exists n0.
        split; try assumption.
        intros n n0_le_n.
        assert (∥ f n ∥ ≤ k * (∥ g n ∥)) by (now apply f_O_g).

        assert (inv_k_gt_0 : 0 < / k) by
            (now apply MathClasses.orders.dec_fields.pos_dec_recip_compat).
        assert (mult_inv_eq_1 : (/ k) * k = 1) by
            (now apply dec_recip_inverse_ge_0).
        setoid_replace (∥g n∥) with (1 * ∥g n∥) by (now rewrite left_identity).
        (* This is awkward, but causes Coq not to automagically multiply
            (/ k_O) * k_O *)
        rewrite <- mult_inv_eq_1.
        rewrite <- associativity.
        apply order_preserving.
        - now apply (order_preserving_mult (/ k)).
        - trivial.
      }
    }
    { (* g ∈ Ω(f) -> f ∈ O(g) *)
      intros g_Ω_f.

      (* Unfurl our hypothesis *)
      unfold big_Omega in g_Ω_f.
      destruct g_Ω_f as [k [zero_lt_k [n0 [zero_lt_n0 g_Ω_f]]]].

      unfold big_O.
      exists (/k).
      split.
      {
        now apply MathClasses.orders.dec_fields.pos_dec_recip_compat.
      }
      {
        exists n0.
        split; try assumption.
        intros n n0_le_n.
        assert (k * (∥ f n ∥) ≤ ∥ g n ∥) by (now apply g_Ω_f).

        assert (inv_k_gt_0 : 0 < / k) by
            (now apply MathClasses.orders.dec_fields.pos_dec_recip_compat).
        assert (mult_inv_eq_1 : (/ k) * k = 1) by
            (now apply dec_recip_inverse_ge_0).
        setoid_replace (∥f n∥) with (1 * ∥f n∥) by (now rewrite left_identity).
        (* This is awkward, but causes Coq not to automagically multiply
            (/ k_O) * k_O *)
        rewrite <- mult_inv_eq_1.
        rewrite <- associativity.
        apply order_preserving.
        - now apply (order_preserving_mult (/ k)).
        - trivial.
      }
    }
  Qed.
End OAndOmega.