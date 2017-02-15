(* -*- mode: coq -*- *)
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.interfaces.naturals.
Require Import MathClasses.interfaces.orders.
Require Import MathClasses.orders.naturals.

(**
 A decision problem can equivalently be viewed as a language. Because we don't
 have set-builder notation, the only way to define a language is with a definite
 (but not necessarily computable) criterion (proposition) that tells us whether
 or not something is in it.

 It also bundles some way to measure the "size" of the input. The only
 constraint is that the size must be totally ordered.

 TODO: input_measure should output a resource
 *)
Class Decision_Problem {R : Set} : Type :=
  { input         : Set
  ; in_language   : input -> Prop
  ; input_measure : input -> R
  }.

(* Definition divides (x y : nat) := ∃ z, x * z = y. *)
(* Definition prime x := ∀ y, divides y x -> y = 1 \/ y = x. *)
(* Instance Primes : Language := *)
(*   { input           := nat *)
(*   ; in_language x   := prime x *)
(*   ; input_measure x := log x *)
(*   }. *)

(**
 TODO: introduce a non-monoidic class that is more general (semigroup?), but
 requires every computation to produce an explicit cost?
 *)

(**
 A Resource
   - Is a monoid: we can add them up between subroutines and embed computations
     that have "no cost".
   - Has a total ordering: resource usage can be compared between algorithms,
     the basis of complexity classes.
   - Has a Setoid/equivalence relation: using a Setoid means comparison doesn't
     have to be based on Coq's type-theoretic notion of equality, but instead on
     any user-defined eqivalence relation.

 This interface is designed to allow many underlying models of resources and
 computation, including but not limited to

 Resources:
   - Time
   - Space
   - Comparisons (as in sorting algorithms)
   - Network requests
   - Others? (arbitrary monoids)

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

Section Resource.
  Context (R : Type) {Re : Equiv R} {Rop: SgOp R} {Runit : MonUnit R} {Rle : Le R}.

  Class Resource : Prop :=
    { resource_monoid :> @Monoid R Re Rop Runit
    ; resource_ord    :> @TotalOrder R Re Rle
    }.
End Resource.

(* Definition big_O_plus (f g : Input -> Output) := (fun i : Input => f i + g i). *)

(* Instance BigO_SgOp : SgOp (Input -> Output) := big_O_plus. *)
(* Instance BigO_Semigroup : SemiGroup (Input -> Output). *)
(* Proof. *)
(*   split. *)

(* Class Complexity_Class (m : Measure) := *)
(*   { measure  :> *)
(*   ; in_class : Decision_Problem -> Prop *)
(*   } *)

(* Class Decider (problem : Decision_Problem) : Type := *)
(*   { decider : input -> (* TODO: our monad *) *)
(*   }. *)
