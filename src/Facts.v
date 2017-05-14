Require Import BigO.Notation.
Require Import BigO.Util.DecField.
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.interfaces.orders.
Require Import MathClasses.interfaces.vectorspace.
Require Import MathClasses.orders.dec_fields.

Section Facts.
  Context `{SemiNormedSpace K V}.
  Context `{SemiNormedSpace K W1}.
  Context `{SemiNormedSpace K W2}.
  Context `{!FullPseudoSemiRingOrder Kle Klt}.
  Context `{forall x y : K, Decision (x = y)}.

  (**
  A general and useful result about the duality of O and Ω.
  Informal proof/overview:
    - TODO
  *)

  Lemma O_and_Omega : ∀ (f : V → W1) (g : V → W2), f ∈ O(g) ↔ g ∈ Ω(f).
    split.
    {
      (* Unfurl our hypothesis *)
      intros f_O_g.
      unfold big_O in *.
      destruct f_O_g as [k [zero_lt_k [m0 [zero_lt_m0 f_O_g]]]].

      unfold big_Omega.
      exists (/k).
      split.
      {
        now apply MathClasses.orders.dec_fields.pos_dec_recip_compat.
      }
      {
        exists m0.
        split; try assumption.
        intros m n0_le_n.
        assert (∥ f m ∥ ≤ k * (∥ g m ∥)) by (now apply f_O_g).

        assert (inv_k_gt_0 : 0 < / k) by
            (now apply MathClasses.orders.dec_fields.pos_dec_recip_compat).
        assert (mult_inv_eq_1 : (/ k) * k = 1) by
            (now apply dec_recip_inverse_ge_0).
        setoid_replace (∥g m∥) with (1 * ∥g m∥) by (now rewrite left_identity).
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
      unfold big_Omega in *.
      destruct g_Ω_f as [k [zero_lt_k [m0 [zero_lt_m0 g_Ω_f]]]].

      unfold big_O.
      exists (/k).
      split.
      {
        now apply MathClasses.orders.dec_fields.pos_dec_recip_compat.
      }
      {
        exists m0.
        split; try assumption.
        intros m n0_le_n.
        assert (k * (∥ f m ∥) ≤ ∥ g m ∥) by (now apply g_Ω_f).

        assert (inv_k_gt_0 : 0 < / k) by
            (now apply MathClasses.orders.dec_fields.pos_dec_recip_compat).
        assert (mult_inv_eq_1 : (/ k) * k = 1) by
            (now apply dec_recip_inverse_ge_0).
        setoid_replace (∥f m∥) with (1 * ∥f m∥) by (now rewrite left_identity).
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

  (**
   Little o is strictly more stringent than big O.
   *)
  Lemma o_implies_O : ∀ (f : V → W1) (g : V → W2), f ∈ o(g) → f ∈ O(g).
    intros f g f_o_g.
    unfold big_O.

    exists 1.
    split; try (apply zero_lt_one_dec).
    destruct (f_o_g 1 zero_lt_one_dec) as [m0 [zero_lt_m0 ?]].
    exists m0.
    split; assumption.
  Qed.

  (**
   Little ω is strictly more stringent than big Ω.
   *)
  Lemma omega_implies_Omega : ∀ (f : V → W1) (g : V → W2), f ∈ ω(g) → f ∈ Ω(g).
    intros f g f_ω_g.
    unfold big_Omega.

    exists 1.
    split; try (apply zero_lt_one_dec).
    destruct (f_ω_g 1 zero_lt_one_dec) as [m0 [zero_lt_m0 ?]].
    exists m0.
    split; assumption.
  Qed.

  (* Lemma big_Omega_mult_constant : ∀ (f g : (V -> V)) (c : K), f ∈ Ω(g) -> f ∈ Ω(c * g). *)
  (* Lemma big_O_mult_constant : ∀ (f g : (V -> V)) (c : K), f ∈ O(g) -> f ∈ O(c * g). *)
End Facts.