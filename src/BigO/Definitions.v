Require Import MathClasses.interfaces.abstract_algebra. (* ≤ *)
Require Import MathClasses.interfaces.rationals.        (* Rationals R *)
Require Import MathClasses.orders.rationals.            (* Le R *)

(**
 Based on Bachmann–Landau.
 *)
Section Definitions.
  Context `{Rationals R}.
  (**
    A function f is less than a function g iff g is greater than f for all inputs
    past a certain size. We write this f ∈ O(g)

    See Definition 7.2 of Sipser.

    I would write these uncurried (with a → instead of a ∧) but then I can't
    seem to extract the hypothesis k ≠ 0 with destruct.
    *)
  Definition big_O (f g : R -> R) : Prop :=
    exists k : R, 0 < k /\ exists n0 : R, 0 < n0 /\ forall n : R, n0 ≤ n -> f n ≤ k * g n.

  Definition big_Omega (f g : R -> R) : Prop :=
    exists k : R, 0 < k /\ exists n0 : R, 0 < n0 /\ forall n : R, n0 ≤ n -> k * g n ≤ f n.

  (* f(x) ∈ Θ(g(x)) iff f(x) ∈ O(g(x)) and f(x) ∈ Ω(g(x)) *)
  Definition big_Theta (f g : R -> R) : Prop := big_O f g /\ big_Omega f g.

  (**
   TODO: small o, etc.
   *)
End Definitions.
Arguments big_O {R} {e} {plus0} {mult0} {zero0} {one0} {neg} {recip0} {U} {H} _ _.
(* Definition big_O_plus (f g : Input -> Output) := (fun i : Input => f i + g i). *)

(* Instance BigO_SgOp : SgOp (Input -> Output) := big_O_plus. *)
(* Instance BigO_Semigroup : SemiGroup (Input -> Output). *)
(* Proof. *)
(*   split. *)