Require Import BigO.Notation.
Require Import BigO.Util.DecField.
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.interfaces.orders.
Require Import MathClasses.interfaces.vectorspace.

(**
 Facts about the compositions of functions and how they interact with our
 notations.
 *)

Section Composition.
  Context `{@SemiNormedSpace
              K V
              Ke Kle Kzero Knegate Kabs Vnorm Ke Kplus Kmult Kzero Kone Knegate Krecip
              Ve Vop Vunit Vnegate smkv
           }.
  Context `{!FullPseudoSemiRingOrder Kle Klt}.
  Context `{forall x y : K, Decision (x = y)}.

  (**
   Trying to avoid "increasing" and "decreasing", which don't correspond to
   these definitions.
   *)
  Definition shrinks (f : V -> V) : Prop := ∀ x : V, ∥f x∥ ≤ ∥x∥.
  Definition grows (f : V -> V) : Prop := ∀ x : V, ∥x∥ ≤ ∥f x∥.
  Definition strictly_shrinks (f : V -> V) : Prop := ∀ x : V, ∥f x∥ < ∥x∥.
  Definition strictly_grows (f : V -> V) : Prop := ∀ x : V, ∥x∥ < ∥f x∥.

  (**
   Composition is compatible with Big O when the outer function is decreasing.
   *)
  Lemma big_O_comp_dec : ∀ f g h : (V → V),
      f ∈ O(h) -> g ∈ O(h) -> shrinks f -> f ∘ g ∈ O(h).
    intros f g h f_O_h g_O_h f_shrinks.
    
    destruct f_O_h as [k_f [zero_lt_k_f [n0_f [zero_lt_n0_f f_O_h]]]].
    destruct g_O_h as [k_g [zero_lt_k_g [n0_g [zero_lt_n0_g g_O_h]]]].
    unfold shrinks in f_shrinks.

    unfold big_O.
    unfold compose.
    exists k_g; split; try assumption.
    exists n0_g; split; try assumption.
    intros n n0_g_le_n.

    transitivity (∥ g n ∥).
     - now rewrite f_shrinks.
     - now apply g_O_h.
  Qed.

  (**
   Composition is compatible with Big Ω when the outer function is increasing.
   *)
  Lemma big_Omega_comp_inc : ∀ f g h : (V → V),
      f ∈ Ω(h) -> g ∈ Ω(h) -> grows f -> f ∘ g ∈ Ω(h).
    intros f g h f_Ω_h g_Ω_h f_grows.
    
    destruct f_Ω_h as [k_f [zero_lt_k_f [n0_f [zero_lt_n0_f f_Ω_h]]]].
    destruct g_Ω_h as [k_g [zero_lt_k_g [n0_g [zero_lt_n0_g g_Ω_h]]]].
    unfold grows in f_grows.

    unfold big_Omega.
    unfold compose.
    exists k_g; split; try assumption.
    exists n0_g; split; try assumption.
    intros n n0_g_le_n.

    transitivity (∥ g n ∥).
     - now apply g_Ω_h.
     - now rewrite f_grows.
  Qed.

  (**
   Composition is compatible with little O when the outer function is decreasing.
   *)
  Lemma little_o_comp_dec : ∀ f g h : (V → V),
      f ∈ o(h) -> g ∈ o(h) -> shrinks f -> f ∘ g ∈ o(h).
    intros f g h f_o_h g_o_h f_shrinks.
    
    unfold little_o.
    unfold compose.
    intros k zero_lt_k.

    destruct (f_o_h k) as [n0_f [zero_lt_n0_f f_o_h']]; try assumption.
    destruct (g_o_h k) as [n0_g [zero_lt_n0_g g_o_h']]; try assumption.
    unfold shrinks in f_shrinks.

    exists (n0_f + n0_g).
    split; try (now apply semirings.pos_plus_compat).
    intros n n_ge_n0.

    assert (n0_f ≤ ∥ n ∥) by (now apply (plus_le n0_f n0_g)).
    assert (n0_g ≤ ∥ n ∥).
    {
      apply (plus_le n0_g n0_f (∥ n ∥)); try assumption.
      now rewrite commutativity.
    }

    transitivity (∥ g n ∥).
     - now rewrite f_shrinks.
     - now apply g_o_h'.
  Qed.

  (**
   Composition is compatible with little ω when the outer function is
   increasing.
   *)
  Lemma little_omega_comp_inc : ∀ f g h : (V → V),
      f ∈ ω(h) -> g ∈ ω(h) -> grows f -> f ∘ g ∈ ω(h).
    intros f g h f_ω_h g_ω_h f_grows.
    
    unfold little_omega.
    unfold compose.
    intros k zero_lt_k.

    destruct (f_ω_h k) as [n0_f [zero_lt_n0_f f_ω_h']]; try assumption.
    destruct (g_ω_h k) as [n0_g [zero_lt_n0_g g_ω_h']]; try assumption.
    unfold grows in f_grows.

    exists (n0_f + n0_g).
    split; try (now apply semirings.pos_plus_compat).
    intros n n_ge_n0.

    assert (n0_f ≤ ∥ n ∥) by (now apply (plus_le n0_f n0_g)).
    assert (n0_g ≤ ∥ n ∥).
    {
      apply (plus_le n0_g n0_f (∥ n ∥)); try assumption.
      now rewrite commutativity.
    }

    transitivity (∥ g n ∥).
     - now apply g_ω_h'.
     - now rewrite f_grows.
  Qed.
End Composition.