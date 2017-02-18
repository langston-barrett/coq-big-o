Require Import BigO.Definition.
Require Import MathClasses.interfaces.abstract_algebra.
Require Import MathClasses.interfaces.orders.
Require Import MathClasses.interfaces.vectorspace.
Require Import MathClasses.orders.dec_fields.

Section Vectorspace.
  Context `{@SemiNormedSpace
              K V
              Ke Kle Kzero Knegate Kabs Vnorm Ke Kplus Kmult Kzero Kone Knegate Krecip
              Ve Vop Vunit Vnegate smkv
           }.
  Context `{!FullPseudoSemiRingOrder Kle Klt}.

  Lemma abs_eq : forall k : K, 0 < k -> (abs k) = k.
    intros k zero_lt_k.
    unfold abs.
    destruct (proj2_sig (abs_sig k)) as [Hyp _].
    apply Hyp.
    now apply lt_le.
  Qed.

  Lemma sm_and_mult : ∀ (k : K) (v : V), 0 < k -> ∥k · v∥ = (k * ∥v∥).
    intros k v zero_lt_k.
    setoid_replace (k * ∥v∥) with ((abs k) * ∥v∥) by (now rewrite abs_eq).
    apply (sn_scale k v).
  Qed.
End Vectorspace.