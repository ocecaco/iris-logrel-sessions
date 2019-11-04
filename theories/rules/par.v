From logrel_heaplang_sessions Require Export lty ltyping basic arr prod.
From iris.heap_lang Require Export lifting metatheory.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Export lib.par.
From iris.heap_lang Require Import notation proofmode.

Section properties.
  Context `{heapG Σ, spawnG Σ}.

  Definition parallel : val := λ: "e1" "e2", "e1" #() ||| "e2" #().

  Lemma ltyped_store A B:
    ∅ ⊨ parallel : (() ⊸ A) → (() ⊸ B) ⊸ (A * B).
  Proof.
    iIntros (vs) "HΓ /=".
    wp_apply wp_value.
    iModIntro. iIntros (fa) "Hfa".
    rewrite /parallel. wp_pures.
    iIntros (fb) "Hfb". wp_pures.
    wp_apply (wp_par A B with "[Hfa] [Hfb]").
    - by wp_apply "Hfa".
    - by wp_apply "Hfb".
    - iIntros (v1 v2) "[HA HB]".
      iModIntro. iExists v1, v2. iSplit=> //.
      iFrame "HA HB".
  Qed.

End properties.
