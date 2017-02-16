Require Complexity.Util.Admitted.
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.interfaces.orders.
Require Import MathClasses.interfaces.rationals.
Require Import MathClasses.orders.rationals.
Require Import MathClasses.orders.semirings.

(* TODO: move to own file *)
Section SemiringLemmas.
  Context `{@SemiRing R Re Rplus Rmult Rzero Rone}.
  Context `{@PseudoSemiRingOrder R Re Rap Rplus Rmult Rzero Rone Rlt}.

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

  Instance apart_symmetric : Symmetric (≶).
  Proof.
    unfold Symmetric.
    intros x y x_ap_y.
    assert (Hyp : x < y \/ y < x)
      by (now apply apart_iff_total_lt).
    apply apart_iff_total_lt.

    case Hyp.
    {
      intros proof_of_A.
      refine (or_intror _).
      exact proof_of_A.
    }
    {
      intros proof_of_B.
      refine (or_introl _).
      exact proof_of_B.
    }
  Qed.

  Instance default_apart_symmetric : Symmetric (strong_setoids.default_apart).
  Proof.
    unfold Symmetric.
    unfold strong_setoids.default_apart.
    exact neq_symmetric.
  Qed.
End SemiringLemmas.

Section Lemmas.
  Context `{Rationals R}.

  (* use the "ring" tactic *)

  (* Lemma zero_ne_one : (0 : R) ≠ (1 : R). *)
  (*   assert (Hyp : PropHolds (1 ≠ 0)) by *)
  (*     (exact (@decfield_nontrivial R e plus0 mult0 zero0 one0 neg recip0 *)
  (*           (@rationals_field R e plus0 mult0 zero0 one0 neg recip0 U H))). *)
  (*   unfold PropHolds in Hyp. *)
  (*   now symmetry. *)
  (* Qed. *)

  (* This might be a lemma of math-classes? *)
End Lemmas.