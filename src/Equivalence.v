Require Import BigO.Equivalence.Reflexivity.
Require Import BigO.Equivalence.Symmetry.
Require Import BigO.Equivalence.Transitivity.
Require Import BigO.Notation.
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.interfaces.orders.
Require Import MathClasses.interfaces.vectorspace.
Require Import MathClasses.interfaces.vectorspace.
Require Import MathClasses.orders.dec_fields.

Section Big_Theta_Equivalence.
  Context `{SemiNormedSpace K V}.
  Context `{@SemiNormedSpace
              K W
              Ke Kle Kzero Knegate Kabs Wnorm Ke Kplus Kmult Kzero Kone Knegate Krecip
              We Wop Wunit Wnegate smkw
           }.
  Context `{!FullPseudoSemiRingOrder Kle Klt}.
  Context `{!TotalOrder Kle}.
  Context `{forall x y : K, Decision (x = y)}.

  Instance big_Theta_Equivalence : @Equivalence (V → W) big_Theta :=
    { Equivalence_Reflexive  := big_Theta_refl 
    ; Equivalence_Symmetric  := big_Theta_sym 
    ; Equivalence_Transitive := big_Theta_trans  
    }.
  Instance big_Theta_Setoid : @Setoid (V → W) big_Theta :=
    { setoid_eq := big_Theta_Equivalence }.

  Add Parametric Relation : (V → W) big_Theta
  reflexivity proved by (big_Theta_refl)
  symmetry proved by (big_Theta_sym)
  transitivity proved by (big_Theta_trans)
  as big_Theta_rel.
End Big_Theta_Equivalence.