From iris_examples.logrel_heaplang_sessions Require Export lty ltyping.
From iris.heap_lang Require Export lifting metatheory.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.

Section types.
  Context `{heapG Σ}.
  Definition lty_rec1 (C : ltyC Σ -> ltyC Σ) `{!Contractive C} (rec : lty Σ) : lty Σ :=
    Lty (C rec)%I.

  Instance lty_rec1_contractive C `{!Contractive C} : Contractive (lty_rec1 C).
  Proof. solve_contractive. Qed.

  Definition lty_rec (C : ltyC Σ -> ltyC Σ) `{!Contractive C} : lty Σ :=
    fixpoint (lty_rec1 C).
End types.

Section properties.
  Context `{heapG Σ}.

  Lemma lty_rec_unfold (C : ltyC Σ → ltyC Σ) `{!Contractive C} :
    lty_rec C ≡ C (lty_rec C).
  Proof.
    by rewrite /lty_rec {1}fixpoint_unfold {1}/lty_rec1.
  Qed.

  (* This could be generalized to a subtyping rule. *)
  Lemma ltyped_equiv Γ e A1 A2:
    A1 ≡ A2 → (Γ ⊨ e : A1) →
    Γ ⊨ e : A2.
  Proof.
    intros Heq HA1. iIntros (vs) "HΓ".
    iPoseProof HA1 as "HA1".
    iSpecialize ("HA1" with "HΓ").
    wp_apply (wp_wand with "HA1").
    iIntros (v).
    iPoseProof Heq as "[Heq1 _]".
    iApply "Heq1".
  Qed.

End properties.
