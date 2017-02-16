Require BigO.Util.Admitted.
Require Import BigO.Facts. (* f ∈ O(g) ↔ g ∈ Ω(f) *)
Require Import BigO.Notation.
Require Import Util.DecField.
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.interfaces.orders.
Require Import MathClasses.interfaces.vectorspace.
Require Import MathClasses.orders.dec_fields.

Section BigThetaSymmetry.
  Context `{@SemiNormedSpace
              K V
              Ke Kle Kzero Knegate Kabs Vnorm Ke Kplus Kmult Kzero Kone Knegate Krecip
              Ve Vop Vunit Vnegate smkv
           }.
  Context `{!FullPseudoSemiRingOrder Kle Klt}.
  Context `{forall x y : K, Decision (x = y)}.

  Lemma big_Theta_sym: symmetric _ big_Theta.
    unfold symmetric.
    intros f g big_Theta_f_g.
    unfold big_Theta in *.
    split.
    { (* big_O x y /\ big_Omega x y -> big_O y x *)
      destruct big_Theta_f_g as [HO HΩ].
      now apply O_and_Omega.
    }
    { (* big_O x y /\ big_Omega x y -> big_Omega y x *)
      destruct big_Theta_f_g as [HO HΩ].
      now apply O_and_Omega.
    }
  Qed.
End BigThetaSymmetry.