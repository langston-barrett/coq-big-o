Require Import Complexity.BigO.Notation.
Require Import Complexity.Util.DecField.
Require Import Coq.Classes.RelationClasses.
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.interfaces.orders.
Require Import MathClasses.interfaces.vectorspace.
Require Import MathClasses.orders.dec_fields.

(**
  Informal proof/overview:
    - TODO
 *)

Section BigOReflexivity.
  Context `{@SemiNormedSpace
              K V
              Ke Kle Kzero Knegate Kabs Vnorm Ke Kplus Kmult Kzero Kone Knegate Krecip
              Ve Vop Vunit Vnegate smkv
           }.
  Context `{!FullPseudoSemiRingOrder Kle Klt}.

  Lemma big_O_refl : reflexive _ big_O.
    unfold reflexive.
    intros f.
    unfold big_O.
    do 2 (exists 1; split; try (apply zero_lt_one_dec)).
    intros n one_le_n.
    now rewrite left_identity.
  Qed.

  Instance big_O_Reflexive : Reflexive big_O :=
    { reflexivity := big_O_refl }.
End BigOReflexivity.