  Definition lty_ref (A : lty Σ) : lty Σ := Lty (λ w,
    ∃ (l : loc) (v : val), ⌜w = #l⌝ ∗ l ↦ v ∗ A v)%I.

Notation "'ref' A" := (lty_ref A) : lty_scope.

  Global Instance lty_ref_ne : NonExpansive2 (@lty_ref Σ _).
  Proof. solve_proper. Qed.

  Global Instance lty_ref_unboxed A : LTyUnboxed (ref A).
  Proof. iIntros (v). by iDestruct 1 as (i w ->) "?". Qed.

    Definition refalloc : val := λ: "init", ref "init".
  Lemma ltyped_alloc Γ A : Γ ⊨ refalloc : (A → ref A)%lty.
  Proof.
    iIntros (vs) "HΓ /=".
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
  Lemma ltyped_load Γ A : Γ ⊨ refload : (ref A → A * ref any)%lty.
  Proof.
    iIntros (vs) "HΓ /=".
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
  Lemma ltyped_store Γ A B:
    Γ ⊨ refstore : (ref A → B → ref B)%lty.
  Proof.
    iIntros (vs) "HΓ /=".
    wp_apply wp_value.
    iIntros (v) "Hv".
    iDestruct "Hv" as (l old ->) "[Hl Hold]".
    rewrite /refstore. wp_pures.
    iIntros (new) "Hnew". wp_pures.
    wp_store.
    iExists l, new. iSplit=> //.
    iFrame "Hl Hnew".
  Qed.
