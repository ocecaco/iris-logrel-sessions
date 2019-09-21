From iris.heap_lang.lib Require Import spin_lock.

  (* TODO: Maybe re-use the strong reference for this *)
  Definition lty_mutex (A : lty Σ) : lty Σ := Lty (λ w,
    ∃ (N : namespace) (γ : gname) (l : loc) (lk : val), ⌜ w = PairV lk #l ⌝ ∗ is_lock N γ lk (∃ inner, l ↦ inner ∗ A inner))%I.

  Definition lty_mutexguard (A : lty Σ) : lty Σ := Lty (λ w,
    ∃ (N : namespace) (γ : gname) (l : loc) (lk : val) (v : val), ⌜ w = PairV lk #l ⌝ ∗ is_lock N γ lk (∃ inner, l ↦ inner ∗ A inner) ∗ locked γ ∗ l ↦ v)%I.

Notation "'mutex' A" := (lty_mutex A) (at level 10) : lty_scope.
Notation "'mutexguard' A" := (lty_mutexguard A) (at level 10) : lty_scope.

  Definition mutexalloc : val := λ: "x", (newlock #(), ref "x").
  Lemma ltyped_mutexalloc Γ A:
     Γ ⊨ mutexalloc : A → mutex A.
  Proof.
    iIntros (vs) "HΓ /=".
    wp_apply wp_value.
    iIntros (v) "Hv".
    rewrite /mutexalloc. wp_pures.
    wp_alloc l as "Hl".
    wp_bind (newlock _).
    set (N := nroot .@ "makelock").
    iAssert (∃ inner, l ↦ inner ∗ A inner)%I with "[Hl Hv]" as "Hlock".
    { iExists v. iFrame "Hl Hv". }
    wp_apply (newlock_spec N with "Hlock").
    iIntros (lk γ) "Hlock".
    wp_pures.
    iExists N, γ, l, lk. iSplit=> //.
  Qed.

  Definition mutexacquire : val := λ: "x", acquire (Fst "x");; (! (Snd "x"), "x").
  Lemma ltyped_mutexacquire Γ A:
     Γ ⊨ mutexacquire : mutex A → A * mutexguard A.
  Proof.
    iIntros (vs) "HΓ /=".
    wp_apply wp_value.
    iIntros (m) "Hm".
    iDestruct "Hm" as (N γ l lk ->) "#Hlock".
    rewrite /mutexacquire. wp_pures.
    wp_bind (acquire _).
    wp_apply (acquire_spec N with "Hlock").
    iIntros "[Hlocked Hinner]".
    wp_pures.
    iDestruct "Hinner" as (v) "[Hl HA]".
    wp_load. wp_pures.
    iExists v, (lk, #l)%V. iSplit=> //.
    iFrame "HA".
    iExists N, γ, l, lk, v. iSplit=> //.
    iFrame "Hl Hlocked Hlock".
  Qed.

  Definition mutexrelease : val := λ: "inner" "guard", Snd "guard" <- "inner";; release (Fst "guard");; "guard".
  Lemma ltyped_mutexrelease Γ A:
     Γ ⊨ mutexrelease : A → mutexguard A → mutex A.
  Proof.
    iIntros (vs) "HΓ /=".
    wp_apply wp_value.
    iIntros (w1) "Hw1".
    rewrite /mutexrelease. wp_pures.
    iIntros (w2) "Hw2".
    iDestruct "Hw2" as (N γ l lk inner ->) "[#Hlock [Hlocked Hinner]]".
    wp_pures. wp_store.
    iAssert (∃ inner : val, l ↦ inner ∗ A inner)%I with "[Hinner Hw1]" as "Hinner".
    { iExists w1. iFrame "Hinner Hw1". }
    wp_bind (release _).
    wp_apply (release_spec N γ _ (∃ inner, l ↦ inner ∗ A inner)%I with "[Hlocked Hinner]").
    { iFrame "Hlock Hlocked Hinner". }
    iIntros "_".
    wp_pures.
    iExists N, γ, l, lk. iSplit=> //.
  Qed.
