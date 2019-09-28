From iris_examples.logrel_heaplang_sessions Require Export lty ltyping.
From iris.heap_lang Require Export lifting metatheory.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.

Section types.
  Context `{heapG Σ}.
  Definition lty_rec1 (C : ltyC Σ -n> ltyC Σ) (rec : lty Σ) : lty Σ := Lty (λ w,
    ▷ C rec w)%I.
  Instance lty_rec1_contractive C : Contractive (lty_rec1 C).
  Proof. solve_contractive. Qed.
  Definition lty_rec (C : ltyC Σ -n> ltyC Σ) : lty Σ := fixpoint (lty_rec1 C).
End types.

(* To unfold a recursive type, we need to take a step. We thus define the
unfold operator to be the identity function. *)
Definition rec_unfold : val := λ: "x", "x".

Section properties.
  Context `{heapG Σ}.

  Global Instance lty_rec_ne n : Proper (dist n ==> dist n) (@lty_rec Σ).
  Proof. intros C C' HC. apply fixpoint_ne. solve_proper. Qed.

  Lemma lty_rec_unfold (C : ltyC Σ -n> ltyC Σ) : lty_rec C ≡ lty_rec1 C (lty_rec C).
  Proof. apply fixpoint_unfold. Qed.

  Lemma ltyped_fold Γ e (B : ltyC Σ -n> ltyC Σ) :
    (Γ ⊨ e : B (lty_rec B)) → Γ ⊨ e : lty_rec B.
  Proof.
    intros He. iIntros (vs) "HΓ /=".
    iPoseProof He as "He".
    wp_apply (wp_wand with "(He [HΓ //])"); iIntros (w) "HB".
    by iEval (rewrite lty_rec_unfold /lty_car /=).
  Qed.

  Lemma ltyped_unfold Γ e (B : ltyC Σ -n> ltyC Σ) :
    (Γ ⊨ e : lty_rec B) → Γ ⊨ rec_unfold e : B (lty_rec B).
  Proof.
    intros He. iIntros (vs) "HΓ /=".
    iPoseProof He as "He".
    wp_apply (wp_wand with "(He [HΓ //])"); iIntros (w) "HB".
    iEval (rewrite lty_rec_unfold /lty_car /=) in "HB". by wp_lam.
  Qed.
End properties.
