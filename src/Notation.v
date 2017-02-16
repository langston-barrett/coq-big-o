Require Export BigO.Definition.

(**
 Convenient UTF-8 notation. In Spacemacs, you can type the following text
 followed by "enter" to get the appropriate symbol:
   - \in: ∈
   - \Theta: Θ
   - \Omega: Ω 
   - \omega: ω
 *)
Notation "f ∈ O( g )" := (big_O f g) (at level 50, no associativity).
Notation "f ∈ Ω( g )" := (big_Omega f g) (at level 50, no associativity).
Notation "f ∈ Θ( g )" := (big_Theta f g) (at level 50, no associativity).
Notation "f ∈ o( g )" := (little_o f g) (at level 50, no associativity).
Notation "f ∈ ω( g )" := (little_omega f g) (at level 50, no associativity).
