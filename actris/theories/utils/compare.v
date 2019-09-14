From iris.heap_lang Require Export lang.
From iris.heap_lang Require Import proofmode notation.

Definition cmp_spec `{!heapG Σ} {A} (I : A → val → iProp Σ)
    (R : relation A) `{!RelDecision R} (cmp : val) : iProp Σ :=
  (∀ x x' v v',
    {{{ I x v ∗ I x' v' }}}
      cmp v v'
    {{{ RET #(bool_decide (R x x')); I x v ∗ I x' v' }}})%I.

Definition IZ `{!heapG Σ} (x : Z) (v : val) : iProp Σ := ⌜v = #x⌝%I.
Definition cmpZ : val := λ: "x" "y", "x" ≤ "y".

Lemma cmpZ_spec `{!heapG Σ} : cmp_spec IZ (≤) cmpZ.
Proof.
  rewrite /IZ. iIntros (x x' v v' Φ [-> ->]) "!> HΦ".
  wp_lam. wp_pures. by iApply "HΦ".
Qed.