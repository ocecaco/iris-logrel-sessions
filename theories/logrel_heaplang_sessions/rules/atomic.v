From iris_examples.logrel_heaplang_sessions Require Export lty ltyping basic ref.
From iris.heap_lang Require Export lifting metatheory.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.

Section types.
  Context `{heapG Σ}.

  Definition lty_atomic (A : lty Σ) : lty Σ := Lty (λ w,
    ∃ N : namespace, inv N (A w))%I.
End types.

Notation "'atomic' A" := (lty_atomic A) (at level 10) : lty_scope.

Section properties.
  Context `{heapG Σ}.

  Global Instance lty_atomic_ne : NonExpansive (@lty_atomic Σ _).
  Proof. solve_proper. Qed.

  Global Instance lty_atomic_copy A : @LTyCopy Σ (lty_atomic A)%lty.
  Proof.
    intros w. rewrite /Persistent.
    iIntros "#H". iModIntro. iExact "H".
  Qed.

  Definition fetchandadd : val := λ: "r" "inc", FAA "r" "inc".
  Lemma ltyped_copy_sub:
    ∅ ⊨ fetchandadd : atomic (lty_ref lty_int) → lty_int → lty_int.
  Proof.
    iIntros (vs) "_ /=". wp_apply wp_value.
    iModIntro. iIntros (r) "#Hr".
    rewrite /fetchandadd. wp_pures.
    iModIntro. iIntros (inc) "Hinc".
    wp_pures.
    iDestruct "Hinc" as (k) "->".
    iDestruct "Hr" as (N) "Hr".
    iInv N as (l v) "[>Heq [Hl Hint]]" "Hclose".
    iDestruct "Heq" as %Heq.
    rewrite Heq.
    rewrite /lty_int /lty_car.
    iDestruct "Hint" as (n) "Hint".
    iMod "Hl".
    iAssert (⌜v = #n⌝)%I with "[Hint]" as "Hint".
    { admit. } (* This should work because of timelessness? *)
    iDestruct "Hint" as %Hint. rewrite Hint.
    wp_faa.
    iMod ("Hclose" with "[Hl]") as "_".
    { iModIntro. iExists l, #(n + k).
      iSplit=> //. iFrame "Hl".
      iModIntro. by iExists (n + k). }
    iModIntro. by iExists n.
  Admitted.

  Definition atomicmake : val := λ: "x", "x".
  Lemma ltyped_atomicmake A:
    ∅ ⊨ atomicmake : A → atomic A.
  Proof.
    iIntros (vs) "_ /=".
    wp_apply wp_value.
    iModIntro. iIntros (w) "Hw".
    rewrite /atomicmake.
    iMod (inv_alloc nroot with "[Hw]") as "#Hinv".
    { iExact "Hw". }
    wp_pures. iExists nroot. iExact "Hinv".
  Qed.

End properties.
