From logrel_heaplang_sessions Require Export lty ltyping any arr prod ref basic.
From iris.heap_lang Require Export lifting metatheory.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.

Section types.
  Context `{heapG Σ}.

  Definition weakrefN := nroot .@ "weakref".

  Definition lty_weakref (A : lty Σ) : lty Σ := Lty (λ w,
    ∃ (l : loc), ⌜w = #l⌝ ∗ inv (weakrefN .@ l) (∃ v : val, l ↦ v ∗ A v))%I.
End types.

Notation "'weakref' A" := (lty_weakref A) (at level 10) : lty_scope.

Section properties.
  Context `{heapG Σ}.

  Global Instance lty_weakref_contractive : Contractive (@lty_weakref Σ _).
  Proof. solve_contractive. Qed.

  Global Instance lty_weakref_ne : NonExpansive2 (@lty_weakref Σ _).
  Proof. solve_proper. Qed.

  Global Instance lty_weakref_unboxed A : LTyUnboxed (weakref A).
  Proof. iIntros (v). by iDestruct 1 as (l ->) "?". Qed.

  (* TODO: Kind of ugly that we have the Skip here, but otherwise I
  had an issue where the thing I wanted in my invariant had two laters
  around it instead of one. *)
  Definition fromstrong : val := λ: "x", Skip;; "x".
  Lemma ltyped_fromstrong A :
    ∅ ⊨ fromstrong : ref A → weakref A.
  Proof.
    iIntros (vs) "HΓ /=".
    wp_apply wp_value.
    iModIntro. iIntros (v) "Hv".
    iDestruct "Hv" as (l w) "[>#Hv [Hl HA]]".
    rewrite /fromstrong.
    wp_lam.
    iMod (inv_alloc (weakrefN .@ l) _ (∃ v : val, l ↦ v ∗ A v)%I with "[Hv Hl HA]") as "Hinv".
    { iModIntro. iExists w. iFrame "Hl HA". }
    wp_pures.
    iExists l.
    iFrame "Hv Hinv".
  Qed.

  Definition fetchandadd : val := λ: "r" "inc", FAA "r" "inc".
  Lemma ltyped_fetchandadd:
    ∅ ⊨ fetchandadd : weakref lty_int → lty_int → lty_int.
  Proof.
    iIntros (vs) "_ /=".
    wp_apply wp_value.
    iModIntro.
    iIntros (r) "#Hr".
    rewrite /fetchandadd. wp_pures.
    iModIntro.
    iIntros (inc) "Hinc".
    wp_pures.
    iDestruct "Hr" as (l ->) "Hr".
    iDestruct "Hinc" as (k) "->".
    iInv (weakrefN .@ l) as (n) "[>Hl >Hn]" "Hclose".
    iDestruct "Hn" as (m) "->".
    wp_faa.
    iMod ("Hclose" with "[Hl]") as "_".
    { iModIntro. iExists #(m + k). iFrame "Hl". by iExists (m + k). }
    iModIntro.
    by iExists m.
  Qed.

  Definition weakrefload : val := λ: "r", !"r".
  Lemma ltyped_weakrefload (A : lty Σ) {copyA : LTyCopy A} :
    ∅ ⊨ weakrefload : weakref A → A.
  Proof.
    iIntros (vs) "_ /=".
    wp_apply wp_value.
    iModIntro. iIntros (r) "#Hr".
    rewrite /weakrefload. wp_pures.
    iDestruct "Hr" as (l ->) "Hr".
    iInv (weakrefN .@ l) as (v) "[>Hl #HA]" "Hclose".
    wp_load. iMod ("Hclose" with "[Hl HA]") as "_".
    { iModIntro. iExists v. iFrame "Hl HA". }
    iModIntro. iFrame "HA".
  Qed.

  Definition weakrefstore : val := λ: "r" "x", "r" <- "x";; #().
  Lemma ltyped_weakrefstore (A : lty Σ) :
    ∅ ⊨ weakrefstore : weakref A → A → ().
  Proof.
    iIntros (vs) "_ /=".
    wp_apply wp_value.
    iModIntro. iIntros (r) "#Hr".
    rewrite /weakrefstore. wp_pures.
    iModIntro. iIntros (x) "HA". wp_pures.
    wp_bind (_ <- _)%E.
    iDestruct "Hr" as (l ->) "Hr".
    iInv (weakrefN .@ l) as (v) "[>Hl _]" "Hclose".
    wp_store. iMod ("Hclose" with "[Hl HA]") as "_".
    { iModIntro. iExists x. iFrame "Hl HA". }
    iModIntro. wp_pures. done.
  Qed.

End properties.
