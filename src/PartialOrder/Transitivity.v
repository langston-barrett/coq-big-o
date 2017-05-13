Require Import BigO.Notation.
Require Import MathClasses.orders.dec_fields.
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.interfaces.vectorspace.

Instance neq_symmetric : ∀ `{Equiv A} `{Symmetric A (=)}, @Symmetric A (≠).
Proof.
  unfold Symmetric.
  intros A Ae Aes x y x_neq_y.
  unfold not.
  unfold not in x_neq_y.
  intros y_eq_x.
  apply x_neq_y.
  now apply Aes.
Qed.

(**
  Informal proof/overview:

  Assume f,g,h:V→V such that f ∈ O(g) and g ∈ O(h). Then

  By assumption,
    - ∃ k_g, n_g such that ∀ n ∈ V, ∥n∥ > ∥n_g∥ ⇒ ∥f(n)∥ ≤ ∥k_g · g(n)∥
    - ∃ k_h, n_h such that ∀ n ∈ V, ∥n∥ > ∥n_h∥ ⇒ ∥g(n)∥ ≤ ∥k_h · h(n)∥

  then, ∀ n ∈ V, ∥n∥ > max(∥n_g∥, ∥n_h∥),
    - ∥g(n)∥ ≤ ∥k_h · h(n)∥
    - ∥k_g · g(n)∥ ≤ ∥(k_g · k_h) · h(n)∥
  and
    - ∥f(n)∥ ≤ ∥k_g · g(n)∥
  so by transitivity of ≤,
    - ∥f(n)∥ ≤ ∥k_g · g(n)∥ ≤ ∥(k_g · k_h) · h(n)∥
    - ∥f(n)∥ ≤ ∥(k_g · k_h) · h(n)∥
  hence, f ∈ O(h).
 *)

Section BigOTransitivity.
  Context `{@SemiNormedSpace
              K V
              Ke Kle Kzero Knegate Kabs Vnorm Ke Kplus Kmult Kzero Kone Knegate Krecip
              Ve Vop Vunit Vnegate smkv
           }.
  Context `{∀ x y: K, Decision (x = y)}.

  Lemma big_O_trans: transitive _ big_O.

    (* Some arithmetic that will come in handy soon *)
    unfold transitive.
    intros f g h.
    unfold big_Theta in *.
    unfold big_O.

    (* Unfurl our hypotheses: f ∈ O(g), g ∈ O(h) *)
    intros [k_f_g [k_f_g_ne_0 [n0_f_g HO_f_g]]]
           [k_g_h [k_g_h_ne_0 [n0_g_h HO_g_h]]].

    exists (k_f_g * k_g_h).
    split.
    { (* 0 ≠ k_f_g * k_g_h *)
      now apply MathClasses.theory.rings.mult_ne_0.
    }
    {
      exists (n0_f_g & n0_g_h).
      intros n nlen.
      Check snm_triangle.

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