From iris_examples.logrel_heaplang_sessions Require Export lty ltyping split arr.
From iris.heap_lang Require Export lifting metatheory.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.

Section types.
  Context `{heapG Σ}.

  Definition lty_prod (A1 A2 : lty Σ) : lty Σ := Lty (λ w,
    ∃ w1 w2, ⌜w = PairV w1 w2⌝ ∗ ▷ A1 w1 ∗ ▷ A2 w2)%I.
End types.

Infix "*" := lty_prod : lty_scope.

Section properties.
  Context `{heapG Σ}.

  Global Instance lty_prod_contractive n:
    Proper (dist_later n ==> dist_later n ==> dist n) (@lty_prod Σ).
  Proof. solve_contractive. Qed.
  Global Instance lty_prod_ne : NonExpansive2 (@lty_prod Σ).
  Proof. solve_proper. Qed.

  Lemma ltyped_pair Γ Γ1 Γ2 e1 e2 A1 A2 :
    env_split Γ Γ1 Γ2 →
    (Γ1 ⊨ e1 : A1) → (Γ2 ⊨ e2 : A2) →
    Γ ⊨ (e1,e2) : A1 * A2.
  Proof.
    intros Hsplit H1 H2. iIntros (vs) "HΓ /=".
    iPoseProof H1 as "H1".
    iPoseProof H2 as "H2".
    iPoseProof (Hsplit with "HΓ") as "[HΓ1 HΓ2]".
    wp_apply (wp_wand with "(H2 [HΓ2 //])"); iIntros (w2) "HA2".
    wp_apply (wp_wand with "(H1 [HΓ1 //])"); iIntros (w1) "HA1".
    wp_pures. iExists w1, w2. by iFrame.
  Qed.

  (* Tried to use the Any type to implement fst and snd, but it
  doesn't work because the result has to be of the type A * (any * B),
  which is useless since it is a pair again. *)
  Definition split : val := λ: "pair" "f", "f" (Fst "pair") (Snd "pair").
  Lemma ltyped_split A1 A2 B:
    ∅ ⊨ split : (A1 * A2 → (A1 ⊸ A2 ⊸ B) ⊸ B)%lty.
  Proof.
    iIntros (vs) "HΓ /=".
    wp_apply wp_value. iModIntro.
    iIntros (v) "Hv".
    rewrite /split. wp_pures.
    iDestruct "Hv" as (w1 w2 ->) "[Hw1 Hw2]".
    iIntros (f) "Hf".
    wp_pures.
    iPoseProof ("Hf" with "Hw1") as "Hf".
    wp_apply (wp_wand with "Hf").
    iIntros (g) "Hg".
    iPoseProof ("Hg" with "Hw2") as "Hg".
    iFrame "Hg".
  Qed.

End properties.
