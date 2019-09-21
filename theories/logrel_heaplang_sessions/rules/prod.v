From iris_examples.logrel_heaplang_sessions Require Export lty ltyping split arr.
From iris.heap_lang Require Export lifting metatheory.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.

Section types.
  Context `{heapG Σ}.

  Definition lty_prod (A1 A2 : lty Σ) : lty Σ := Lty (λ w,
    ∃ w1 w2, ⌜w = PairV w1 w2⌝ ∗ A1 w1 ∗ A2 w2)%I.
End types.

Infix "*" := lty_prod : lty_scope.

Section properties.
  Context `{heapG Σ}.

  Global Instance lty_prod_ne : NonExpansive2 (@lty_prod Σ).
  Proof. solve_proper. Qed.

  Lemma ltyped_pair Γ Γ1 Γ2 e1 e2 A1 A2 :
    env_split Γ Γ1 Γ2 -∗ (Γ1 ⊨ e1 : A1) -∗ (Γ2 ⊨ e2 : A2) -∗ Γ ⊨ (e1,e2) : A1 * A2.
  Proof.
    iIntros "Hsplit H1 H2" (vs) "HΓ /=".
    iPoseProof ("Hsplit" with "HΓ") as "[HΓ1 HΓ2]".
    wp_apply (wp_wand with "(H2 [HΓ2 //])"); iIntros (w2) "HA2".
    wp_apply (wp_wand with "(H1 [HΓ1 //])"); iIntros (w1) "HA1".
    wp_pures. iExists w1, w2. by iFrame.
  Qed.

  (* TODO: use Any type to allow moving out one component of a pair *)
  Definition split : val := λ: "pair" "f", "f" (Fst "pair") (Snd "pair").
  Lemma ltyped_split Γ A1 A2 B:
    Γ ⊨ split : (A1 * A2 → (A1 → A2 → B) → B)%lty.
  Proof.
    iIntros (vs) "HΓ /=".
    wp_apply wp_value.
    iIntros (v) "Hv".
    iDestruct "Hv" as (w1 w2 ->) "[Hw1 Hw2]".
    rewrite /split. wp_pures.
    iIntros (f) "Hf".
    wp_pures.
    iPoseProof ("Hf" with "Hw1") as "Hf".
    wp_apply (wp_wand with "Hf").
    iIntros (g) "Hg".
    iPoseProof ("Hg" with "Hw2") as "Hg".
    iFrame "Hg".
  Qed.

End properties.
