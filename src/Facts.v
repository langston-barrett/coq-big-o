Require Import BigO.Notation.
Require Import BigO.Util.DecField.
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.interfaces.orders.
Require Import MathClasses.interfaces.vectorspace.
Require Import MathClasses.orders.dec_fields.

Section Facts.
  Context `{@SemiNormedSpace
              K V
              Kequiv Kle Kzero Knegate Kabs Vnorm Kequiv Kplus Kmult Kzero Kone
              Knegate Krecip Ve Vop Vunit Vnegate smkv
           }.
  Context `{@SemiNormedSpace
              K W1
              Kequiv Kle Kzero Knegate Kabs Wnorm1 Kequiv Kplus Kmult Kzero Kone
              Knegate Krecip We1 Wop1 Wunit1 Wnegate1 smkw1
           }.
  Context `{@SemiNormedSpace
              K W2
              Kequiv Kle Kzero Knegate Kabs Wnorm2 Kequiv Kplus Kmult Kzero Kone
              Knegate Krecip We2 Wop2 Wunit2 Wnegate2 smkw2
           }.
  Context `{!FullPseudoSemiRingOrder Kle Klt}.
  Context `{!forall x y : K, Decision (x = y)}.

  (**
  A general and useful result about the duality of O and Ω.
  Informal proof/overview:
    - TODO
  *)

  Lemma O_and_Omega : forall f g : (V →  V), f ∈ O(g) ↔ g ∈ Ω(f).
    split.
    {
      (* Unfurl our hypothesis *)
      intros f_O_g.
      unfold big_O in f_O_g.
      destruct f_O_g as [k [zero_ne_k [n0 f_O_g]]].

      unfold big_Omega.
      exists (/k).
      split.
      { (* /k ≠ 0 *)
        unfold not.
        intros k_recip_zero.
        apply zero_ne_k.
        now apply MathClasses.theory.dec_fields.dec_recip_zero.
      }
      {
        exists n0.
        intros n n0_le_n.
        assert (∥ k · (g n) ∥ = abs k * ∥ (g n) ∥).
        Check @snm_scale K.
        apply (@snm_scale K Kequiv Kplus Kmult Kzero Kone Knegate Klt).
        assert (∥ f n ∥ = (abs k) * (∥ g n ∥)).
        symmetry.
          (* by (now apply f_O_g). *)

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

  (**
   Little o is strictly more stringent than big O.
   *)
  Lemma o_implies_O : forall f g : (V -> V), f ∈ o(g) -> f ∈ O(g).
    intros f g f_o_g.
    unfold big_O.

    exists 1.
    split; try (apply zero_lt_one_dec).
    destruct (f_o_g 1 zero_lt_one_dec) as [n0 [zero_lt_n0 ?]].
    exists n0.
    split; assumption.
  Qed.

  (**
   Little ω is strictly more stringent than big Ω.
   *)
  Lemma omega_implies_Omega : forall f g : (V -> V), f ∈ ω(g) -> f ∈ Ω(g).
    intros f g f_ω_g.
    unfold big_Omega.

    exists 1.
    split; try (apply zero_lt_one_dec).
    destruct (f_ω_g 1 zero_lt_one_dec) as [n0 [zero_lt_n0 ?]].
    exists n0.
    split; assumption.
  Qed.

  (* Lemma big_Omega_mult_constant : ∀ (f g : (V -> V)) (c : K), f ∈ Ω(g) -> f ∈ Ω(c * g). *)
  (* Lemma big_O_mult_constant : ∀ (f g : (V -> V)) (c : K), f ∈ O(g) -> f ∈ O(c * g). *)
End Facts.