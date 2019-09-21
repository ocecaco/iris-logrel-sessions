From iris_examples.logrel_heaplang_sessions Require Export lty ltyping arr.
From iris.heap_lang Require Export lifting metatheory.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.

Section types.
  Context `{heapG Σ}.

  Definition lty_sum (A1 A2 : lty Σ) : lty Σ := Lty (λ w,
    (∃ w1, ⌜w = InjLV w1⌝ ∗ A1 w1) ∨ (∃ w2, ⌜w = InjRV w2⌝ ∗ A2 w2))%I.
End types.

Infix "+" := lty_sum : lty_scope.

Section properties.
  Context `{heapG Σ}.

  Global Instance lty_sum_ne : NonExpansive2 (@lty_sum Σ).
  Proof. solve_proper. Qed.

  Lemma ltyped_injl Γ e A1 A2:
    (Γ ⊨ e : A1) -∗ Γ ⊨ InjL e : A1 + A2.
  Proof.
    iIntros "HA" (vs) "HΓ /=".
    wp_apply (wp_wand with "(HA [HΓ //])").
    iIntros (v) "HA".
    wp_pures.
    iLeft. iExists v. auto.
  Qed.

  Lemma ltyped_injr Γ e A1 A2:
    (Γ ⊨ e : A2) -∗ Γ ⊨ InjR e : A1 + A2.
  Proof.
    iIntros "HA" (vs) "HΓ /=".
    wp_apply (wp_wand with "(HA [HΓ //])").
    iIntros (v) "HA".
    wp_pures.
    iRight. iExists v. auto.
  Qed.

  Definition paircase : val :=
    λ: "pair" "left" "right",
    Case "pair" "left" "right".
  Lemma ltyped_paircase Γ A1 A2 B:
    Γ ⊨ paircase : (A1 + A2 → (A1 → B) → (A2 → B) → B)%lty.
  Proof.
    iIntros (vs) "HΓ /=".
    wp_apply wp_value.
    iIntros (p) "Hp".
    rewrite /paircase. wp_pures.
    iIntros (f_left) "Hleft". wp_pures.
    iIntros (f_right) "Hright". wp_pures.
    iDestruct "Hp" as "[Hp|Hp]".
    - iDestruct "Hp" as (w1 ->) "Hp". wp_pures.
      wp_apply (wp_wand with "(Hleft [Hp //])"). iIntros (v) "HB". iApply "HB".
    - iDestruct "Hp" as (w2 ->) "Hp". wp_pures.
      wp_apply (wp_wand with "(Hright [Hp //])"). iIntros (v) "HB". iApply "HB".
  Qed.

End properties.
