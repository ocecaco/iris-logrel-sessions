From logrel_heaplang_sessions Require Export lty ltyping.
From iris.heap_lang Require Export lifting metatheory.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.

Section types.
  Context `{heapG Σ}.

  Definition lty_forall (C : lty Σ → lty Σ) : lty Σ := Lty (λ w,
    ∀ A : lty Σ, WP w #() {{ w, C A w }})%I.
End types.

Notation "∀ A1 .. An , C" :=
  (lty_forall (λ A1, .. (lty_forall (λ An, C%lty)) ..)) : lty_scope.

Section properties.
  Context `{heapG Σ}.

  Global Instance lty_forall_ne n : Proper (pointwise_relation _ (dist n) ==> dist n) (@lty_forall Σ _).
  Proof. solve_proper. Qed.

  Global Instance lty_forall_contractive n : Proper (pointwise_relation _ (dist_later n) ==> dist n) (@lty_forall Σ _).
  Proof.
    intros F F' A.
    apply lty_ne.
    intros w.
    f_equiv.
    intros B.
    apply wp_contractive.
    { done. }
    intros u.
    specialize (A B).
    destruct n as [|n].
    + done.
    + by simpl.
  Qed.

  Lemma ltyped_tlam Γ e C :
    (∀ A, Γ ⊨ e : C A) → Γ ⊨ (λ: <>, e) : ∀ A, C A.
  Proof.
    intros He. iIntros (vs) "HΓ /=". wp_pures.
    iIntros (A) "/=". wp_pures.
    iPoseProof He as "He".
    iSpecialize ("He" $! vs with "HΓ").
    wp_apply (wp_wand with "He").
    iIntros (v) "H". eauto.
  Qed.

  Lemma ltyped_tapp Γ e C A :
    (Γ ⊨ e : ∀ A, C A) → Γ ⊨ e #() : C A.
  Proof.
    intros He. iIntros (vs) "HΓ /=".
    iPoseProof He as "He".
    wp_apply (wp_wand with "(He [HΓ //])"); iIntros (w) "HB". by iApply ("HB" $! A).
  Qed.

End properties.
