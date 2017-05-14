Require Import BigO.Notation.
Require Import BigO.Util.DecField.
Require Import Coq.Classes.RelationClasses.
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.interfaces.orders.
Require Import MathClasses.interfaces.vectorspace.
Require Import MathClasses.orders.dec_fields.

(**
  Informal proof/overview:

  Assume f,g,h:V→V such that f ∈ O(g) and g ∈ O(h). Then

  By assumption,
    - ∃ k_g, n_g such that ∀ n > n_g, f(n) ≤ k_g * g(n)
    - ∃ k_h, n_h such that ∀ n > n_h, g(n) ≤ k_h * h(n)

  then, ∀ n > max(n_g, n_h),
    - g(n) ≤ k_h * h(n)
    - k_g * g(n) ≤ (k_g * k_h) * h(n)
  and
    - f(n) ≤ k_g * g(n)
  so by transitivity of ≤,
    - f(n) ≤ k_g * g(n) ≤ (k_g * k_h) * h(n)
    - f(n) ≤ (k_g * k_h) * h(n)
  hence, f ∈ O(h).
 *)

Section BigOTransitivity.
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
  Context `{@SemiNormedSpace
              K W3
              Ke Kle Kzero Knegate Kabs Wnorm3 Ke Kplus Kmult Kzero Kone
              Knegate Krecip We3 Wop3 Wunit3 Wnegate3 smkw3
           }.
  Context `{!FullPseudoSemiRingOrder Kle Klt}.

  Lemma big_O_trans :
    ∀ (f : V → W1) (g : V → W2) (h : V → W3),
      f ∈ O(g) → g ∈ O(h) → f ∈ O(h).

    (* Some arithmetic that will come in handy soon *)
    unfold transitive.
    intros f g h.
    unfold big_Theta in *.
    unfold big_O.

    (* Unfurl our hypotheses: f ∈ O(g), g ∈ O(h) *)
    intros [k_f_g [k_f_g_gt_0 [n0_f_g [n0_f_g_gt_0 HO_f_g]]]]
           [k_g_h [k_g_h_gt_0 [n0_g_h [n0_g_h_gt_0 HO_g_h]]]].

    exists (k_f_g * k_g_h).
    split.
    { (* 0 < k_f_g * k_g_h *)
      apply mult_pos_gt_0;
        assumption.
    }
    {
      exists (n0_f_g + n0_g_h).

      split.
      { (* 0 < n0_f_g + n0_g_h *)
        apply semirings.plus_lt_compat_r; assumption.
      }
      {
        intros n.

        (* Prove that our new n_0 is greater than the previous *)
        intros n_ge_n0.
        assert (n_ge_n0_f_g : n0_f_g ≤ ∥n∥) by (now apply (plus_le n0_f_g n0_g_h)).
        assert (n_ge_n0_g_h : n0_g_h ≤ ∥n∥) by
            (rewrite commutativity in n_ge_n0; now apply (plus_le n0_g_h n0_f_g)).
        clear n_ge_n0.

        assert (fn_le_gn : ∥f n∥ ≤ k_f_g * ∥g n∥) by (now apply HO_f_g).
        assert (gn_le_hn : ∥g n∥ ≤ k_g_h * ∥h n∥) by (now apply HO_g_h).

        clear HO_f_g HO_g_h.

        transitivity (k_f_g * ∥g n∥); try assumption.
        rewrite (order_preserving_mult_le (∥g n∥) (k_g_h * ∥h n∥));
          try assumption.
        now rewrite associativity.
      }
    }
  Qed.
End BigOTransitivity.