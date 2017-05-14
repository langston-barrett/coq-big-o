Require Import BigO.Notation.
Require Import BigO.PartialOrder.Transitivity.
Require Import Coq.Classes.RelationClasses.
Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.interfaces.orders.
Require Import MathClasses.interfaces.vectorspace.
Require Import Util.DecField.
Require Util.Admitted.

(**
  Informal proof/overview:

  Assume f,g,h:V→V such that f ∈ Θ(g) and g ∈ Θ(h). Then

  [f ∈ O(h)]
    Proved in another file.

  [f ∈ Ω(h)]
  By assumption,
    - ∃ k_g, n_g such that ∀ n > n_g, k_g * g(n) ≤ f(n)
    - ∃ k_h, n_h such that ∀ n > n_h, k_h * h(n) ≤ g(n)

  then, ∀ n > max(n_g, n_h),
    - k_h * h(n) ≤ g(n)
    - (k_g * k_h) * h(n) ≤ k_g * g(n)
  and
    - k_g * g(n) ≤ f(n)
  so by transitivity of ≤,
    - (k_g * k_h) * h(n) ≤ k_g * g(n) ≤ f(n)
    - (k_g * k_h) * h(n) ≤ ≤ f(n)
  hence, f ∈ Ω(h).
 *)

Section BigThetaTransitivity.
  Context `{SemiNormedSpace K V}.
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

  (* Lemma big_Theta_trans: transitive (V → W) big_Theta. *)
  Lemma big_Theta_trans :
    ∀ (f : V → W1) (g : V → W2) (h : V → W3),
      f ∈ Θ(g) → g ∈ Θ(h) → f ∈ Θ(h).
    unfold transitive.
    intros f g h.
    unfold big_Theta in *.
    intros H_f_g H_g_h. split.
    { (* f ∈ O(h) *)
      now apply (big_O_trans f g h).
    }
    { (* f ∈ Ω(h) *)
      unfold big_Omega.

      (* Unfurl our hypothesis: f ∈ O(g) *)
      destruct H_f_g  as [_ [k_f_g [k_f_g_gt_0 [n0_f_g [n0_f_g_gt_0 HOm_f_g]]]]].
      destruct H_g_h  as [_ [k_g_h [k_g_h_gt_0 [n0_g_h [n0_g_h_gt_0 HOm_g_h]]]]].

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
          intros n'.

          (* Prove that our new n_0 is greater than the previous *)
          intros n_ge_n0.
          assert (n_ge_n0_f_g : n0_f_g ≤ ∥n'∥) by
              (now apply (DecField.plus_le n0_f_g n0_g_h)).
          assert (n_ge_n0_g_h : n0_g_h ≤ ∥n'∥) by
              (rewrite commutativity in n_ge_n0;
               now apply (DecField.plus_le n0_g_h n0_f_g)).
          clear n_ge_n0.

          assert (fn_le_gn : (k_f_g * ∥g n'∥) ≤ ∥f n'∥) by (now apply HOm_f_g).
          assert (gn_le_hn : (k_g_h * ∥h n'∥) ≤ ∥g n'∥) by (now apply HOm_g_h).

          clear HOm_f_g HOm_g_h.

          transitivity (k_f_g * ∥g n'∥); try assumption.
          rewrite <- associativity.
          rewrite (order_preserving_mult_le (k_g_h * ∥h n'∥) (∥g n'∥));
            now try assumption.
        }
      }
    }
  Qed.
End BigThetaTransitivity.
