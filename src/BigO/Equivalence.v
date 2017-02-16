Require Import Complexity.BigO.Equivalence.Reflexivity.
Require Import Complexity.BigO.Equivalence.Symmetry.
Require Import Complexity.BigO.Equivalence.Transitivity.
Require Import Complexity.BigO.Notation.
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.interfaces.orders.
Require Import MathClasses.interfaces.vectorspace.
Require Import MathClasses.interfaces.vectorspace.
Require Import MathClasses.orders.dec_fields.

(**
 TODO: Reduce "admitted" work in Complexity.Util.Admitted
 *)

Section Big_Theta_Equivalence.
  Context `{@SemiNormedSpace
              K V
              Ke Kle Kzero Knegate Kabs Vnorm Ke Kplus Kmult Kzero Kone Knegate Krecip
              Ve Vop Vunit Vnegate smkv
           }.
  Context `{!FullPseudoSemiRingOrder Kle Klt}.
  Context `{!TotalOrder Kle}.
  Context `{forall x y : K, Decision (x = y)}.

  Add Parametric Relation : (V -> V) big_Theta
  reflexivity proved by (@big_Theta_refl K V Ke Kle Kzero Knegate Kabs Vnorm Kplus Kmult Kone Krecip Ve Vop Vunit Vnegate smkv H Klt FullPseudoSemiRingOrder0)
  symmetry proved by (@big_Theta_sym K V Ke Kle Kzero Knegate Kabs Vnorm Kplus Kmult Kone Krecip Ve Vop Vunit Vnegate smkv H Klt FullPseudoSemiRingOrder0 H0)
  transitivity proved by (@big_Theta_trans K V Ke Kle Kzero Knegate Kabs Vnorm Kplus Kmult Kone Krecip Ve Vop Vunit Vnegate smkv H Klt FullPseudoSemiRingOrder0 TotalOrder0)
  as big_Theta_rel.
End Big_Theta_Equivalence.