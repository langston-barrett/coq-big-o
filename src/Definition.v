Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.interfaces.orders.
Require Import MathClasses.interfaces.vectorspace.
Require Import MathClasses.orders.dec_fields.

(**
 Based on Bachmann–Landau, but generalized to arbitrary seminormed vector spaces.
 The functions need not have the same codomain, as long as the scalars are comparable.
 The simple case is when K=V=W1=W2=R (the reals), in which case we recover the
 usual Big O. Should be considered experimental until some results are proved.
 *)
Section Definitions.
  Context `{@SemiNormedSpace
              K V
              Ke Kle Kzero Knegate Kabs Vnorm Ke Kplus Kmult Kzero Kone
              Knegate Krecip Ve Vop Vunit Vnegate smkv
           }.
  Context `{@SemiNormedSpace
              K W1
              Ke Kle Kzero Knegate Kabs Wnorm1 Ke Kplus Kmult Kzero Kone
              Knegate Krecip We1 Wop1 Wunit1 Wnegate1 smkw1
           }.
  Context `{@SemiNormedSpace
              K W2
              Ke Kle Kzero Knegate Kabs Wnorm2 Ke Kplus Kmult Kzero Kone
              Knegate Krecip We2 Wop2 Wunit2 Wnegate2 smkw2
           }.
  Context `{!FullPseudoSemiRingOrder Kle Klt}.
  (**
    A function f is less than a function g iff g is greater than f for all inputs
    past a certain size. We write this f ∈ O(g)

    See Definition 7.2 of Sipser.

    I would write these uncurried (with a → instead of a ∧) but then I can't
    seem to extract the hypothesis k ≠ 0 with destruct.
   *)
  Definition big_O (f : V → W1) (g : V → W2) : Prop :=
    ∃ k : K, 0 < k ∧ ∃ n0 : K, 0 < n0 ∧ forall n : V, n0 ≤ ∥n∥ → ∥f n∥ ≤ k * ∥g n∥.

  Definition big_Omega (f : V → W1) (g : V → W2) : Prop :=
    ∃ k : K, 0 < k ∧ ∃ n0 : K, 0 < n0 ∧ forall n : V, n0 ≤ ∥n∥ → (k * ∥g n∥) ≤ ∥f n∥.

  Definition big_Theta (f : V → W1) (g : V → W2) : Prop := big_O f g ∧ big_Omega f g.

  Definition little_o (f : V → W1) (g : V → W2) : Prop := 
    ∀ k : K, 0 < k → ∃ n0 : K, 0 < n0 ∧ forall n : V, n0 ≤ ∥n∥ → ∥f n∥ ≤ k * ∥g n∥.

  Definition little_omega (f : V → W1) (g : V → W2) : Prop := 
    ∀ k : K, 0 < k → ∃ n0 : K, 0 < n0 ∧ forall n : V, n0 ≤ ∥n∥ → (k * ∥g n∥) ≤ ∥f n∥.
End Definitions.