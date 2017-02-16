Require Import Complexity.Util.Rationals.
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.interfaces.rationals.
Require Import MathClasses.orders.rationals.
Require Import MathClasses.orders.semirings.
Require Import MathClasses.interfaces.orders.
Require Import Complexity.BigO.Notation.

(**
  Informal proof/overview:

  Assume f,g,h:R→R such that f ∈ Θ(g) and g ∈ Θ(h). Then

  [f ∈ O(h)]
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
  Context `{Rationals R}.
  Lemma big_Theta_trans: transitive _ big_Theta.
    unfold transitive.
    intros f g h.
    unfold big_Theta in *.
    intros H_f_g H_g_h;
      split.
    { (* f ∈ O(h) *)
      unfold big_O.

      (* Unfurl our hypothesis: f ∈ O(g) *)
      destruct H_f_g as [HO_f_g _].
      destruct HO_f_g as [k_f_g HO_f_g].
      destruct HO_f_g as [k_f_g_gt_0 HO_f_g].
      destruct HO_f_g as [n0_f_g HO_f_g].
      destruct HO_f_g as [n0_f_g_gt_0 HO_f_g].

      (* Unfurl our hypothesis: g ∈ O(h) *)
      destruct H_g_h as [HO_g_h _].
      destruct HO_g_h as [k_g_h HO_g_h].
      destruct HO_g_h as [k_g_h_gt_0 HO_g_h].
      destruct HO_g_h as [n0_g_h HO_g_h].
      destruct HO_g_h as [n0_g_h_gt_0 HO_g_h].

      exists (k_f_g * k_g_h).
      split.
      { (* 0 < k_f_g * k_g_h *)
        apply Rationals.mult_pos_gt_0;
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
          assert (n0_gt_n0_f_g : n0_f_g < n0_f_g + n0_g_h) by
            (now apply semirings.pos_plus_lt_compat_r).
          assert (n0_gt_n0_g_h : n0_g_h < n0_f_g + n0_g_h) by
            (now apply semirings.pos_plus_lt_compat_l).

          intros n_ge_n0.

          assert (n_ge_n0_f_g : n0_f_g ≤ n).
          {
            destruct n0_gt_n0_f_g as [? _].
            transitivity (n0_f_g + n0_g_h); assumption.
          }
          assert (n_ge_n0_g_h : n0_g_h ≤ n).
          {
            destruct n0_gt_n0_g_h as [? _].
            transitivity (n0_f_g + n0_g_h); assumption.
          }

          clear n_ge_n0 n0_gt_n0_f_g n0_gt_n0_g_h.

          assert (fn_le_gn : f n ≤ k_f_g * g n) by (now apply HO_f_g).
          assert (gn_le_hn : g n ≤ k_g_h * h n) by (now apply HO_g_h).

          clear HO_f_g HO_g_h.

          transitivity (k_f_g * g n); try assumption.
          rewrite (Admitted.order_preserving_mult_le (g n) (k_g_h * h n));
            try assumption.
          now rewrite associativity.
        }
      }
    }
    { (* f ∈ Ω(h) *)
      unfold big_Omega.

      (* Unfurl our hypothesis: f ∈ O(g) *)
      destruct H_f_g as [_ HOm_f_g].
      destruct HOm_f_g as [k_f_g HOm_f_g].
      destruct HOm_f_g as [k_f_g_gt_0 HOm_f_g].
      destruct HOm_f_g as [n0_f_g HOm_f_g].
      destruct HOm_f_g as [n0_f_g_gt_0 HOm_f_g].

      (* Unfurl our hypothesis: g ∈ O(h) *)
      destruct H_g_h as [_ HOm_g_h].
      destruct HOm_g_h as [k_g_h HOm_g_h].
      destruct HOm_g_h as [k_g_h_gt_0 HOm_g_h].
      destruct HOm_g_h as [n0_g_h HOm_g_h].
      destruct HOm_g_h as [n0_g_h_gt_0 HOm_g_h].

      exists (k_f_g * k_g_h).
      split.
      { (* 0 < k_f_g * k_g_h *)
        apply Rationals.mult_pos_gt_0;
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
          assert (n0_gt_n0_f_g : n0_f_g < n0_f_g + n0_g_h) by
            (now apply semirings.pos_plus_lt_compat_r).
          assert (n0_gt_n0_g_h : n0_g_h < n0_f_g + n0_g_h) by
            (now apply semirings.pos_plus_lt_compat_l).

          intros n_ge_n0.

          assert (n_ge_n0_f_g : n0_f_g ≤ n).
          {
            destruct n0_gt_n0_f_g as [? _].
            transitivity (n0_f_g + n0_g_h); assumption.
          }
          assert (n_ge_n0_g_h : n0_g_h ≤ n).
          {
            destruct n0_gt_n0_g_h as [? _].
            transitivity (n0_f_g + n0_g_h); assumption.
          }

          clear n_ge_n0 n0_gt_n0_f_g n0_gt_n0_g_h.

          assert (fn_le_gn : k_f_g * g n ≤ f n) by (now apply HOm_f_g).
          assert (gn_le_hn : k_g_h * h n ≤ g n) by (now apply HOm_g_h).

          clear HOm_f_g HOm_g_h.

          transitivity (k_f_g * g n); try assumption.
          rewrite <- associativity.
          rewrite (Complexity.Util.Admitted.order_preserving_mult_le
                                   (k_g_h * h n) (g n));
            now try assumption.
        }
      }
    }
  Qed.
End BigThetaTransitivity.
