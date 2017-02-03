Require Import TypeclassHierarchy.Interfaces.Semigroup. (* Monoid *)
Require Import TypeclassHierarchy.Interfaces.Functor.   (* Monad *)

(**
 This is a monad that wraps arbitrary computations that solve a decision problem
 and records how much of a given resource they use. It is designed to allow many
 underlying models of resources and computations including

 Resources:
   - Time (integers)
   - Space (integers)
   - Others? (monoids?)

 Models of computation:
   - Shallow embeddings as Coq functions
   - Turing Machines?
   - Others?

 It is essentially a glorified Writer monad, as it mostly allows "writing" to a
 Monoid, which is treated as the resource in question.

 This monad is based on concepts from
   - A Machine-Checked Proof of the Average-Case Complexity of Quicksort in Coq,
     van der Weegen et al.
   - A Coq Library For Internal Verification of Running-Times, McCarthy et al.
 *)

Class Resource_Monad (M : Type -> Type) :=
  { resource_monad_monad :> Monad M
  ; resource             : Set
  ; resource_monoid      :> Monoid resource
  }.

(* Instance Time_Monad : Resource_Monad *)