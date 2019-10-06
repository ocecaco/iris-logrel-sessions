From logrel_heaplang_sessions Require Export lty ltyping arr universal.
From iris.heap_lang Require Export lifting metatheory.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.

Section types.
  Context `{heapG Σ}.

  Definition lty_exist (C : lty Σ → lty Σ) : lty Σ := Lty (λ w,
    ∃ A : lty Σ, C A w)%I.
End types.

Notation "∃ A1 .. An , C" :=
  (lty_exist (λ A1, .. (lty_exist (λ An, C%lty)) ..)) : lty_scope.

Section properties.
  Context `{heapG Σ}.

  Global Instance lty_exist_ne n : Proper (pointwise_relation _ (dist n) ==> dist n) (@lty_exist Σ).
  Proof. solve_proper. Qed.

  Lemma ltyped_pack Γ e C A :
    (Γ ⊨ e : C A) → Γ ⊨ e : ∃ A, C A.
  Proof.
    intros He. iIntros (vs) "HΓ /=".
    iPoseProof He as "He".
    wp_apply (wp_wand with "(He [HΓ //])"); iIntros (w) "HB". by iExists A.
  Qed.

  Definition unpack : val := λ: "exist" "f", "f" #() "exist".
  Lemma ltyped_unpack C B :
    ∅ ⊨ unpack : (∃ A, C A) → (∀ A, C A ⊸ B) ⊸ B.
  Proof.
    iIntros (vs) "HΓ /=".
    wp_apply wp_value.
    iModIntro. iIntros (v) "Hv".
    iDestruct "Hv" as (A) "Hv".
    rewrite /unpack. wp_pures.
    iIntros (fty) "Hfty". wp_pures.
    iSpecialize ("Hfty" $! A).
    wp_bind (fty _). wp_apply (wp_wand with "Hfty").
    iIntros (f) "Hf".
    wp_apply (wp_wand with "(Hf [Hv //])").
    iIntros (w) "HB". iApply "HB".
  Qed.

End properties.
