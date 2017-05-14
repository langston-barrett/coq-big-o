Require Import BigO.Notation.
Require Import BigO.Util.DecField.
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.interfaces.vectorspace.
Require Import MathClasses.interfaces.orders.

Section BigThetaReflexive.
  Context `{SemiNormedSpace K V}.
  Context `{SemiNormedSpace K W}.
  Context `{!FullPseudoSemiRingOrder Kle Klt}.

  Lemma big_Theta_refl : reflexive (V → W) big_Theta.
    unfold reflexive.
    intros f.
    unfold big_Theta.
    split.
    { (* big_O x x *)
      unfold big_O.
      exists 1. (* our constant k *)
      split.
       - exact zero_lt_one_dec.
       - exists 1. (* our constant *)
        intros.
        split.
         * exact zero_lt_one_dec.
         * intros n' one_leq_n.
           rewrite left_identity.
           apply reflexivity.
    }

    { (* big_Omega x x *)
      unfold big_Omega.
      exists 1. (* our constant *)
      split.
       - exact zero_lt_one_dec.
       - exists 1. (* our constant *)
         split.
         * exact zero_lt_one_dec.
         * intros n' one_leq_n.
           now rewrite left_identity.
    }
  Qed.
End BigThetaReflexive.