Require Import BigO.Notation.
Require Import BigO.Util.DecField.
Require Import BigO.Util.Vectorspace.
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.interfaces.orders.
Require Import MathClasses.interfaces.vectorspace.
Require Import MathClasses.orders.semirings.
Require Import MathClasses.orders.dec_fields.

(**
 All notations absorb constant multiples.
 *)

Section Constants.
  Context `{@SemiNormedSpace
              K V
              Ke Kle Kzero Knegate Kabs Vnorm Ke Kplus Kmult Kzero Kone Knegate Krecip
              Ve Vop Vunit Vnegate smkv
           }.
  Context `{!FullPseudoSemiRingOrder Kle Klt}.
  Context `{forall x y : K, Decision (x = y)}.

  Lemma big_O_absorbs_constants : ∀ f g : (V → V),
      f ∈ O(g) -> forall c : K, 0 < c -> (fun n => c · f n) ∈ O(g).
    intros f g f_O_g c.
    destruct f_O_g as [k [zero_lt_k [n0 [zero_lt_n0 f_O_h]]]].
    unfold big_O.
    exists (c * k); split; try now apply (pseudo_srorder_pos_mult_compat c k).
    exists n0; split; try assumption.
    intros n n0_le_n.
    rewrite sm_and_mult; try assumption.
    rewrite <- associativity.
    apply order_preserving_mult_le; try assumption.
    now apply f_O_h.
  Qed.

  Lemma big_Omega_absorbs_constants : ∀ f g : (V → V),
      f ∈ Ω(g) -> forall c : K, 0 < c -> (fun n => c · f n) ∈ Ω(g).
    intros f g f_O_g c.
    destruct f_O_g as [k [zero_lt_k [n0 [zero_lt_n0 f_O_h]]]].
    unfold big_Omega.
    exists (c * k); split; try now apply (pseudo_srorder_pos_mult_compat c k).
    exists n0; split; try assumption.
    intros n n0_le_n.
    rewrite sm_and_mult; try assumption.
    rewrite <- associativity.
    apply order_preserving_mult_le; try assumption.
    now apply f_O_h.
  Qed.

  Lemma dec_recip_inverse_gt : ∀ c : K, 0 < c -> c / c = 1.
    intros c zero_lt_c.
    apply dec_recip_inverse.
    apply trivial_apart.
    apply apart_iff_total_lt.
    now right.
  Qed.

  Lemma little_o_absorbs_constants : ∀ f g : (V → V),
      f ∈ o(g) -> forall c : K, 0 < c -> (fun n => c · f n) ∈ o(g).
    intros f g f_o_g c zero_lt_c.
    unfold little_o.
    intros k zero_lt_k.
    destruct (f_o_g (/c * k)) as [n0 [zero_lt_n0 f_o_g']].
    - (apply pos_mult_compat; try trivial; try now apply pos_dec_recip_compat).
    - exists n0; split; try assumption.
      intros n n0_le_n.
      assert (∥ f n ∥ ≤ /c * k * (∥ g n ∥)) by (now apply f_o_g').
      rewrite sm_and_mult; try assumption.
      setoid_replace k with (1 * k) by (now rewrite left_identity).
      setoid_replace 1 with (c * /c) by (symmetry; now apply dec_recip_inverse_gt).
      do 2 (rewrite <- associativity).
      apply (order_preserving_mult_le (∥ f n ∥) (/ c * (k * (∥ g n ∥))) c);
        try assumption.
      now rewrite associativity.
  Qed.

  Lemma little_omega_absorbs_constants : ∀ f g : (V → V),
      f ∈ ω(g) -> forall c : K, 0 < c -> (fun n => c · f n) ∈ ω(g).
    intros f g f_ω_g c zero_lt_c.
    unfold little_omega.
    intros k zero_lt_k.
    destruct (f_ω_g (/c * k)) as [n0 [zero_lt_n0 f_ω_g']].
    - (apply pos_mult_compat; try trivial; try now apply pos_dec_recip_compat).
    - exists n0; split; try assumption.
      intros n n0_le_n.
      assert (/c * k * (∥g n∥) ≤ ∥f n∥) by (now apply f_ω_g').
      rewrite sm_and_mult; try assumption.
      setoid_replace k with (1 * k) by (now rewrite left_identity).
      setoid_replace 1 with (c * /c) by (symmetry; now apply dec_recip_inverse_gt).
      do 2 (rewrite <- associativity).
      apply (order_preserving_mult_le (/ c * (k * (∥ g n ∥))) (∥f n∥) c);
        try assumption.
      now rewrite associativity.
  Qed.
End Constants.