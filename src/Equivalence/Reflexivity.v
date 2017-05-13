Require Import BigO.Notation.
Require Import MathClasses.theory.abs.
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.interfaces.vectorspace.
Require Import MathClasses.interfaces.orders.

(* TODO: move me *)
Instance neq_symmetric : ∀ `{Equiv A} `{Symmetric A (=)}, @Symmetric A (≠).
Proof.
  unfold Symmetric.
  intros A Ae Aes x y x_neq_y.
  unfold not.
  unfold not in x_neq_y.
  intros y_eq_x.
  apply x_neq_y.
  now apply Aes.
Qed.

Section BigThetaReflexive.
  Context `{@SemiNormedSpace
              K V
              Ke Kle Kzero Knegate Kabs Vnorm Ke Kplus Kmult Kzero Kone Knegate Krecip
              Ve Vop Vunit Vnegate smkv
           }.
  Context `{!FullPseudoSemiRingOrder Kle Klt}.
  Context `{forall x y : K, Decision (x = y)}.
  Instance df : DecField K := vs_field.

  Lemma big_Theta_refl : reflexive _ big_Theta.
    unfold reflexive.
    intros f.
    unfold big_Theta.
    split.
    { (* big_O x x *)
      unfold big_O.
      exists 1. (* our constant k *)
      split.
      - apply (decfield_nontrivial K).
      - exists mon_unit. (* our constant n0 *)
        intros n nlen.
        rewrite sn_scale.
        rewrite abs_1.
        now rewrite left_identity.
    }
    { (* big_Omega x x *)
      unfold big_Omega.
      exists 1. (* our constant *)
      split.
      - apply (decfield_nontrivial K).
      - exists mon_unit. (* our constant *)
        intros n nlen.
        rewrite sn_scale.
        rewrite abs_1.
        now rewrite left_identity.
    }
  Qed.
End BigThetaReflexive.