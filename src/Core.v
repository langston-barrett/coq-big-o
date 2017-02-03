Require Import Coq.Structures.Orders.

(**
 A decision problem can equivalently be viewed as a language. Because we don't
 have set-builder notation, the only way to define a language is with a definite
 (but not necessarily computable) criterion (proposition) that tells us whether
 or not something is in it.
 *)
Class Decision_Problem : Type :=
  { input         : Set
  ; in_language   : input -> Prop
  ; input_measure : input -> nat (** TODO: relax constraint to some other type? *)
  }.

(**
 TODO: should a measure just be an orderable type? with a non-standard
 ordering on functions that induces a big-O notation?
 *)
(* Class Measure : Type := { measure : Decision_Problem -> nat }. *)
(* Definition space_measure (n : nat) : nat := (). *)
(* Class ND_Space_Measure (problem : Decision_Problem) : Type := *)
(* Class Time_Measure (problem : Decision_Problem) : Type := *)
(* Class ND_Time_Measure (problem : Decision_Problem) : Type := *)

(* Class Complexity_Class (m : Measure) := *)
(*   { measure  :> *)
(*   ; in_class : Decision_Problem -> Prop *)
(*   } *)


(* Class Decider (problem : Decision_Problem) : Type := *)
(*   { decider : input -> (* TODO: our monad *) *)
(*   }. *)

(**
 TODO: Big-O
 How can we relate space and time??
 *)