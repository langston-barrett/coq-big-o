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
              Ke Kle Kzero Knegate Kabs Vnorm Ke Kplus Kmult Kzero Kone Knegate Krecip
              Ve Vop Vunit Vnegate smkv
           }.
  Context `{!FullPseudoSemiRingOrder Kle Klt}.

  Lemma big_O_trans: transitive _ big_O.

    (* Some arithmetic that will come in handy soon *)
    unfold transitive.
    intros f g h.
    unfold big_Theta in *.
    intros H_f_g H_g_h.
    unfold big_O.

    (* Unfurl our hypothesis: f ∈ O(g) *)
    destruct H_f_g as [k_f_g HO_f_g].
    destruct HO_f_g as [k_f_g_gt_0 HO_f_g].
    destruct HO_f_g as [n0_f_g HO_f_g].
    destruct HO_f_g as [n0_f_g_gt_0 HO_f_g].

    (* Unfurl our hypothesis: g ∈ O(h) *)
    destruct H_g_h as [k_g_h HO_g_h].
    destruct HO_g_h as [k_g_h_gt_0 HO_g_h].
    destruct HO_g_h as [n0_g_h HO_g_h].
    destruct HO_g_h as [n0_g_h_gt_0 HO_g_h].

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

  Instance big_O_Transitive : Transitive big_O :=
    { transitivity := big_O_trans }.
End BigOTransitivity.