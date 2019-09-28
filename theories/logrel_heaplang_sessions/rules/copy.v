From iris_examples.logrel_heaplang_sessions Require Export lty ltyping.
From iris.heap_lang Require Export lifting metatheory.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.

Section types.
  Context `{heapG Σ}.

  (* Copy is like a subtype: it selects all of those values of some
  type which are persistent. This can be used, for example, to get the
  unrestricted function type from the linear function type.

  This is less restrictive than a notion of Copy-types: there are some
  types for which some, but not all values are copy (functions being a
  good example). *)
  Definition lty_copy (A : lty Σ) : lty Σ := Lty (λ w, □ (A w))%I.
End types.

Notation "'copy' A" := (lty_copy A) (at level 10) : lty_scope.

Section properties.
  Context `{heapG Σ}.

  Global Instance lty_copy_copy A : @LTyCopy Σ (copy A)%lty.
  Proof.
    intros v. rewrite /Persistent. iIntros "#Hv".
    iModIntro. iModIntro. iApply "Hv".
  Qed.

  Lemma ltyped_copy_sub Γ e A:
    (Γ ⊨ e : copy A) -∗ Γ ⊨ e : A.
  Proof.
    iStartProof.
    iIntros "#H" (vs) "!> HΓ /=".
    wp_apply (wp_wand with "(H [HΓ //])"). iIntros (v) "Hcopy".
    iDestruct "Hcopy" as "#HA".
    iApply "HA".
  Qed.

  (* If the entire type is copy, then of course so is every value of
  that type. *)
  Lemma ltyped_copy_reflect Γ e A:
    LTyCopy A → (Γ ⊨ e : A) -∗ Γ ⊨ e : copy A.
  Proof.
    intros Hcopy. iIntros "#H" (vs) "!> HΓ /=".
    wp_apply (wp_wand with "(H [HΓ //])"). iIntros (v) "#HA".
    iModIntro. iApply "HA".
  Qed.

End properties.
