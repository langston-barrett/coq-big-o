Require Import BigO.Definition.
Require Import BigO.Util.Vectorspace.
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.interfaces.orders.
Require Import MathClasses.interfaces.vectorspace.
Require Import MathClasses.orders.dec_fields.

(**
 Alternative yet equivalent definitions of the notations with proofs of their
 equivalence.
 *)

Section AlternativeDefinitions.
  Context `{@SemiNormedSpace
              K V
              Ke Kle Kzero Knegate Kabs Vnorm Ke Kplus Kmult Kzero Kone Knegate Krecip
              Ve Vop Vunit Vnegate smkv
           }.

  Definition big_O_alt (f g : V -> V) : Prop :=
    ∃ k : K, 0 ≠ k ∧ ∃ n0 : V, ∀ n : V, ∥n0∥ ≤ ∥n∥ → ∥f n∥ ≤ ∥k · g n∥.
  (* Definition big_O_alt (f g : V -> V) : Prop := *)
  (*   exists k : K, 0 < k /\ exists n0 : K, 0 < n0 /\ forall n : V, n0 ≤ ∥n∥ -> ∥f n∥ ≤ ∥k · g n∥. *)

  (* Definition big_Omega_alt (f g : V -> V) : Prop := *)
  (*   exists k : K, 0 < k /\ exists n0 : K, 0 < n0 /\ forall n : V, n0 ≤ ∥n∥ -> (∥k · g n∥) ≤ ∥f n∥. *)

  (* Definition big_Theta_alt1 (f g : V -> V) : Prop := big_O_alt f g ∧ big_Omega_alt f g. *)
  (* Definition big_Theta_alt2 (f g : V -> V) : Prop :=  *)
  (*   exists k1 k2 n0 : K, 0 < k1 → 0 < k2 → 0 < n0 → *)
  (*     (forall n : V, n0 ≤ ∥n∥ -> ∥k1 · g n∥ ≤ ∥f n∥ ≤ ∥k2 · g n∥). *)

  (* Definition big_Theta_alt2 (f g : V -> V) : Prop :=  *)
  (*   exists k : K, 0 < k /\ exists n0 : K, 0 < n0 /\ forall n : V, n0 ≤ ∥n∥ -> ∥f n∥ ≤ ∥k · g n∥. *)

  Context `{!FullPseudoSemiRingOrder Kle Klt}.

  (* https://github.com/math-classes/math-classes/pull/38 *)
  Lemma sn_nonneg :  ∀ w, 0 ≤ ∥w∥.
  Admitted.

  Lemma big_O_alt_is_equiv : forall f g : V -> V, big_O f g ↔ big_O_alt f g.
    intros f g.
    split.
    { (* big_O f g → big_O_alt f g *)
      intros f_O_g.
      destruct f_O_g as [k_f [zero_lt_k_f [n0_f [zero_lt_n0_f f_O_g]]]].

      unfold big_O_alt.
      exists k_f. 
      destruct
      exists n0_f; split; try assumption.
      intros n n0_f_le_n.
      rewrite sm_and_mult; try assumption.
      now apply f_O_g.
    }
    { (* big_O f g ← big_O_alt f g *)
      intros f_O_g.
      destruct f_O_g as [k_f [zero_lt_k_f [n0_f [zero_lt_n0_f f_O_g]]]].

      unfold big_O.
      exists k_f; split; try assumption.
      exists n0_f; split; try assumption.
      intros n n0_f_le_n.

      rewrite <- sm_and_mult; try assumption.
      now apply f_O_g.
    }
  Qed.
End AlternativeDefinitions.