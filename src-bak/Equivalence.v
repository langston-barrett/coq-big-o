Require Import Complexity.BigO.Definitions.
Require Import Complexity.BigO.Equivalence.Reflexivity.
Require Import Complexity.BigO.Equivalence.Symmetry.
Require Import Complexity.BigO.Equivalence.Transitivity.
Require Import MathClasses.interfaces.rationals.
Require Import MathClasses.interfaces.canonical_names.

(**
 Further work: 
  - ~~~~~ Reduce "admitted" work in Complexity.Util.Rationals ~~~~~
  - Implement with real numbers. Where can we find a typeclass interface?
  - Implement with minimal assumptions about the codomain: What kind of ordering
    is really required? i
  - Reduce the assumptions `{∀ x y, Decision (x ≤ y)}, `{∀ x, Decision (x = 0)}
 *)

Section Big_Theta_Equivalence.
  Context `{Rationals R}.

  Add Parametric Relation : (R -> R) big_Theta
  reflexivity proved by big_Theta_refl
  symmetry proved by big_Theta_sym
  transitivity proved by big_Theta_trans
  as big_Theta_rel.
End Big_Theta_Equivalence.