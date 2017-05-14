Require BigO.Util.Admitted.
Require Import BigO.Facts. (* f ∈ O(g) ↔ g ∈ Ω(f) *)
Require Import BigO.Notation.
Require Import Util.DecField.
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.interfaces.orders.
Require Import MathClasses.interfaces.vectorspace.
Require Import MathClasses.orders.dec_fields.

Section BigThetaSymmetry.
  Context `{SemiNormedSpace K V}.
  Context `{@SemiNormedSpace
              K W1
              Ke Kle Kzero Knegate Kabs Wnorm1 Ke Kplus Kmult Kzero Kone
              Knegate Krecip We1 Wop1 Wunit1 Wnegate1 smkw1
           }.
  Context `{@SemiNormedSpace
              K W2
              Ke Kle Kzero Knegate Kabs Wnorm2 Ke Kplus Kmult Kzero Kone
              Knegate Krecip We2 Wop2 Wunit2 Wnegate2 smkw2
           }.
  Context `{!FullPseudoSemiRingOrder Kle Klt}.
  Context `{forall x y : K, Decision (x = y)}.

  Lemma big_Theta_sym : ∀ (f : V → W1) (g : V → W2), f ∈ Θ(g) → g ∈ Θ(f).
    intros f g.
    unfold big_Theta in *.
    intros f_Theta_g.
    destruct f_Theta_g as [HO HΩ].
    split; now apply O_and_Omega.
  Qed.

End BigThetaSymmetry.

(* The iff version. Has to be in another section for big_Theta_sym to generalize *)

Section BigThetaSymmetry'.
  Context `{SemiNormedSpace K V}.
  Context `{@SemiNormedSpace
              K W1
              Ke Kle Kzero Knegate Kabs Wnorm1 Ke Kplus Kmult Kzero Kone
              Knegate Krecip We1 Wop1 Wunit1 Wnegate1 smkw1
           }.
  Context `{@SemiNormedSpace
              K W2
              Ke Kle Kzero Knegate Kabs Wnorm2 Ke Kplus Kmult Kzero Kone
              Knegate Krecip We2 Wop2 Wunit2 Wnegate2 smkw2
           }.
  Context `{!FullPseudoSemiRingOrder Kle Klt}.
  Context `{forall x y : K, Decision (x = y)}.
  Lemma big_Theta_sym' : ∀ (f : V → W1) (g : V → W2), f ∈ Θ(g) ↔ g ∈ Θ(f).
    split; apply big_Theta_sym.
  Qed.
End BigThetaSymmetry'.