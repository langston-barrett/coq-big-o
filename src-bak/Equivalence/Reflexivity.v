Require Import Complexity.BigO.Notation. (* exports definitions *)
Require Import Complexity.Util.Field.
Require Import Complexity.Util.Rationals.
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.interfaces.rationals.
Require Import MathClasses.orders.rationals.

Section BigThetaReflexive.
  Context `{Rationals R}.
  Lemma big_Theta_refl : reflexive _ big_Theta.
    unfold reflexive.
    intros f.
    unfold big_Theta.
    split.
    { (* big_O x x *)
      unfold big_O.
      exists 1. (* our constant k *)
      split.
       - exact zero_lt_one.
       - exists 1. (* our constant *)
        intros.
        split.
         * exact zero_lt_one.
         * intros n one_leq_n.
           rewrite left_identity.
           apply reflexivity.
    }

    { (* big_Omega x x *)
      unfold big_Omega.
      exists 1. (* our constant *)
      split.
       - exact zero_lt_one.
       - exists 1. (* our constant *)
         split.
         * exact zero_lt_one.
         * intros n one_leq_n.
           now rewrite left_identity.
    }
  Qed.
End BigThetaReflexive.