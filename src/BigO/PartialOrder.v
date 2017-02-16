Require Import Complexity.BigO.Equivalence.
Require Import Complexity.BigO.Facts.
Require Import Complexity.BigO.Notation.
Require Import Complexity.BigO.PartialOrder.Reflexivity.
Require Import Complexity.BigO.PartialOrder.Transitivity.
Require Import Complexity.Util.DecField.
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.interfaces.orders.
Require Import MathClasses.interfaces.vectorspace.
Require Import MathClasses.orders.dec_fields.

(**
 The Big-O relation between functions induces a partial order: it acts somewhat
 like < on Ƶ, but not every two elements are related [1]. See the MathClasses
 library for more information on the interface of a PartialOrder.

 [1]: http://math.stackexchange.com/questions/703866/big-oh-and-big-theta-relations-confirmation
 *)

Section BigOPartialOrder.
  Context `{@SemiNormedSpace
              K V
              Ke Kle Kzero Knegate Kabs Vnorm Ke Kplus Kmult Kzero Kone Knegate Krecip
              Ve Vop Vunit Vnegate smkv
           }.
  Context `{!FullPseudoSemiRingOrder Kle Klt}.
  Context `{!TotalOrder Kle}.
  Context `{forall x y : K, Decision (x = y)}.

  Instance big_O_Preorder : @PreOrder (V -> V) big_O.
  Proof.
    split.
     - exact big_O_Reflexive.
     - exact big_O_Transitive.
  Qed.

  Instance big_O_Antisymmetric :
    @Antisymmetric (V -> V) big_Theta big_Theta_Equivalence big_O.
  Proof.
    split; try assumption.
    now apply O_and_Omega.
  Qed.

  Instance big_O_PartialOrder : @PartialOrder (V -> V) big_Theta big_O.
  Proof.
    split.
     - exact big_Theta_Setoid.
     - split;
        unfold equiv in *; unfold le in *.
      {
        intros x_O_x0.
        destruct H1 as [x_O_y x_Ω_y].
        destruct H2 as [x0_O_y0 x0_Ω_y0].
        assert (y_O_x : y ∈ O(x)) by (now apply O_and_Omega).
        transitivity x; try assumption.
        transitivity x0; try assumption.
      }
      {
        intros y_O_y0.
        destruct H1 as [x_O_y x_Ω_y].
        destruct H2 as [x0_O_y0 x0_Ω_y0].
        assert (y0_O_x0 : y0 ∈ O(x0)) by (now apply O_and_Omega).
        transitivity y; try assumption.
        transitivity y0; try assumption.
      }
    - exact big_O_Preorder.
    - exact big_O_Antisymmetric.
  Qed.
End BigOPartialOrder.