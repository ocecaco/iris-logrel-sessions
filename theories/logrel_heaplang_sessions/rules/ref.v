From iris_examples.logrel_heaplang_sessions Require Export lty ltyping any arr prod.
From iris.heap_lang Require Export lifting metatheory.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.

Section types.
  Context `{heapG Σ}.

  Definition lty_ref (A : lty Σ) : lty Σ := Lty (λ w,
    ∃ (l : loc) (v : val), ⌜w = #l⌝ ∗ l ↦ v ∗ A v)%I.
End types.

Notation "'ref' A" := (lty_ref A) : lty_scope.

Section properties.
  Context `{heapG Σ}.

  Global Instance lty_ref_ne : NonExpansive2 (@lty_ref Σ _).
  Proof. solve_proper. Qed.

  Global Instance lty_ref_unboxed A : LTyUnboxed (ref A).
  Proof. iIntros (v). by iDestruct 1 as (i w ->) "?". Qed.

  Definition refalloc : val := λ: "init", ref "init".
  Lemma ltyped_alloc A :
    ∅ ⊨ refalloc : (A → ref A)%lty.
  Proof.
    iIntros (vs) "!> HΓ /=".
    wp_apply wp_value.
    iIntros (v) "Hv". rewrite /refalloc. wp_pures.
    wp_alloc l as "Hl".
    iExists l, v. iSplit=> //.
    iFrame "Hv Hl".
  Qed.

  (* The intuition for the any is that the value is still there, but
  it no longer holds any Iris resources. Just as in Rust, where a move
  might turn into a memcpy, which leaves the original memory
  unmodified, but moves the resources, in the sense that you can no
  longer use the memory at the old location. *)
  Definition refload : val := λ: "r", (!"r", "r").
  Lemma ltyped_load A :
    ∅ ⊨ refload : (ref A → A * ref any)%lty.
  Proof.
    iIntros (vs) "!> HΓ /=".
    wp_apply wp_value.
    iIntros (v) "Hv".
    iDestruct "Hv" as (l w ->) "[Hl Hw]".
    rewrite /refload.
    wp_pures. wp_load.
    wp_pures.
    iExists w, #l. iSplit=> //.
    iFrame "Hw".
    iExists l, w. iSplit=> //.
    iFrame "Hl".
  Qed.

  Definition refstore : val := λ: "r" "new", "r" <- "new";; "r".
  Lemma ltyped_store A B:
    ∅ ⊨ refstore : (ref A → B → ref B)%lty.
  Proof.
    iIntros (vs) "!> HΓ /=".
    wp_apply wp_value.
    iIntros (v) "Hv".
    iDestruct "Hv" as (l old ->) "[Hl Hold]".
    rewrite /refstore. wp_pures.
    iIntros (new) "Hnew". wp_pures.
    wp_store.
    iExists l, new. iSplit=> //.
    iFrame "Hl Hnew".
  Qed.
End properties.
