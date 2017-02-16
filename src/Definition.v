Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.interfaces.orders.
Require Import MathClasses.interfaces.vectorspace.
Require Import MathClasses.orders.dec_fields.

(**
 Based on Bachmann–Landau, but generalized to an arbitrary seminormed vector space.
 The most general definition uses topology, but we restrict ourselves to algebra.
 Should be considered experimental until some results are proved.
 *)
Section Definitions.
  Context `{@SemiNormedSpace
              K V
              Ke Kle Kzero Knegate Kabs Vnorm Ke Kplus Kmult Kzero Kone Knegate Krecip
              Ve Vop Vunit Vnegate smkv
           }.
  Context `{!FullPseudoSemiRingOrder Kle Klt}.
  (**
    A function f is less than a function g iff g is greater than f for all inputs
    past a certain size. We write this f ∈ O(g)

    See Definition 7.2 of Sipser.

    I would write these uncurried (with a → instead of a ∧) but then I can't
    seem to extract the hypothesis k ≠ 0 with destruct.
    *)
  Definition big_O (f g : V -> V) : Prop :=
    exists k : K, 0 < k /\ exists n0 : K, 0 < n0 /\ forall n : V, n0 ≤ ∥n∥ -> ∥f n∥ ≤ k * ∥g n∥.

  Definition big_Omega (f g : V -> V) : Prop :=
    exists k : K, 0 < k /\ exists n0 : K, 0 < n0 /\ forall n : V, n0 ≤ ∥n∥ -> (k * ∥g n∥) ≤ ∥f n∥.

  Definition big_Theta (f g : V -> V) : Prop := big_O f g /\ big_Omega f g.

  Definition little_o (f g : V -> V) : Prop :=
    forall k : K, 0 < k -> exists n0 : K, 0 < n0 /\ forall n : V, n0 ≤ ∥n∥ -> ∥f n∥ ≤ k * ∥g n∥.

  Definition little_omega (f g : V -> V) : Prop :=
    forall k : K, 0 < k -> exists n0 : K, 0 < n0 /\ forall n : V, n0 ≤ ∥n∥ -> (k * ∥g n∥) ≤ ∥f n∥.
End Definitions.
(* Arguments big_O {K} {H} {V} {H1} {n} {Kmult} {Kzero} _ _. *)