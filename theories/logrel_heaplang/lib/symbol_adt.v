From iris_examples.logrel_heaplang Require Export ltyping.
From iris.heap_lang.lib Require Import assert.
From iris.algebra Require Import auth.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.

(* Semantic typing of a symbol ADT (taken from Dreyer's POPL'18 talk) *)
Definition symbol_adt_inc : val := λ: "x" <>, FAA "x" #1.
Definition symbol_adt_check : val := λ: "x" "y", assert: "y" < !"x".
Definition symbol_adt : val := λ: <>,
  let: "x" := Alloc #0 in (symbol_adt_inc "x", symbol_adt_check "x").
Definition symbol_adt_ty `{heapG Σ} : lty Σ :=
  (() → ∃ A, (() → A) * (A → ()))%lty.

(* The required ghost theory *)
Class symbolG Σ := { symbol_inG :> inG Σ (authR mnatUR) }.
Definition symbolΣ : gFunctors := #[GFunctor (authR mnatUR)].

Instance subG_symbolΣ {Σ} : subG symbolΣ Σ → symbolG Σ.
Proof. solve_inG. Qed.

Section symbol_ghosts.
  Context `{!symbolG Σ}.

  Definition counter (γ : gname) (n : nat) : iProp Σ := own γ (● (n : mnat)).
  Definition symbol (γ : gname) (n : nat) : iProp Σ := own γ (◯ (S n : mnat)).

  Global Instance counter_timeless γ n : Timeless (counter γ n).
  Proof. apply _. Qed.
  Global Instance symbol_timeless γ n : Timeless (symbol γ n).
  Proof. apply _. Qed.

  Lemma counter_exclusive γ n1 n2 : counter γ n1 -∗ counter γ n2 -∗ False.
  Proof.
    apply bi.wand_intro_r. rewrite -own_op own_valid /=. by iDestruct 1 as %[].
  Qed.
  Global Instance symbol_persistent γ n : Persistent (symbol γ n).
  Proof. apply _. Qed.

  Lemma counter_alloc n : (|==> ∃ γ, counter γ n)%I.
  Proof.
    iMod (own_alloc (● (n:mnat) ⋅ ◯ (n:mnat))) as (γ) "[Hγ Hγf]";
      first by apply auth_both_valid.
    iExists γ. by iFrame.
  Qed.

  Lemma counter_inc γ n : counter γ n ==∗ counter γ (S n) ∗ symbol γ n.
  Proof.
    rewrite -own_op.
    apply own_update, auth_update_alloc, mnat_local_update. omega.
  Qed.

  Lemma symbol_obs γ s n : counter γ n -∗ symbol γ s -∗ ⌜(s < n)%nat⌝.
  Proof.
    iIntros "Hc Hs".
    iDestruct (own_valid_2 with "Hc Hs") as %[?%mnat_included _]%auth_both_valid.
    iPureIntro. omega.
  Qed.
End symbol_ghosts.

Typeclasses Opaque counter symbol.

Section ltyped_symbol_adt.
  Context `{heapG Σ, symbolG Σ}.

  Definition symbol_adtN := nroot .@ "symbol_adt".

  Definition symbol_inv (γ : gname) (l : loc) : iProp Σ :=
    (∃ n : nat, l ↦ #n ∗ counter γ n)%I.

  Definition lty_symbol (γ : gname) : lty Σ := Lty (λ w,
    ∃ n : nat, ⌜w = #n⌝ ∧ symbol γ n)%I.

  Lemma ltyped_symbol_adt Γ : Γ ⊨ symbol_adt : symbol_adt_ty.
  Proof.
    iIntros (vs) "!# _ /=". iApply wp_value.
    iIntros "!#" (v ->). wp_lam. wp_alloc l as "Hl"; wp_pures.
    iMod (counter_alloc 0) as (γ) "Hc".
    iMod (inv_alloc symbol_adtN _ (symbol_inv γ l) with "[Hl Hc]") as "#?".
    { iExists 0%nat. by iFrame. }
    do 2 (wp_lam; wp_pures).
    iExists (lty_symbol γ), _, _; repeat iSplit=> //.
    - repeat rewrite /lty_car /=. iIntros "!#" (? ->). wp_pures.
      iInv symbol_adtN as (n) ">[Hl Hc]". wp_faa.
      iMod (counter_inc with "Hc") as "[Hc #Hs]".
      iModIntro; iSplitL; last eauto.
      iExists (S n). rewrite Nat2Z.inj_succ -Z.add_1_r. iFrame.
    - repeat rewrite /lty_car /=. iIntros "!#" (v).
      iDestruct 1 as (n ->) "#Hs". wp_pures. iApply wp_assert.
      wp_bind (!_)%E. iInv symbol_adtN as (n') ">[Hl Hc]". wp_load.
      iDestruct (symbol_obs with "Hc Hs") as %?. iModIntro. iSplitL.
      { iExists n'. iFrame. }
      wp_op. rewrite bool_decide_true; last lia. eauto.
  Qed.
End ltyped_symbol_adt.
