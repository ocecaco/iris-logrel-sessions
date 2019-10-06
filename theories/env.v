From logrel_heaplang_sessions Require Export lty.
From iris.heap_lang Require Export lifting metatheory.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.

Section Environment.
  Context {Σ : gFunctors}.
  Implicit Types A : lty Σ.

  Definition env_ltyped (Γ : gmap string (lty Σ))
             (vs : gmap string val) : iProp Σ :=
    ([∗ map] i ↦ A ∈ Γ, ∃ v, ⌜vs !! i = Some v⌝ ∗ lty_car A v)%I.

  Lemma env_ltyped_lookup Γ vs x A :
    Γ !! x = Some A →
    env_ltyped Γ vs -∗ ∃ v, ⌜ vs !! x = Some v ⌝ ∗ A v.
  Proof.
    iIntros (HΓx) "HΓ".
    iPoseProof (big_sepM_lookup with "HΓ") as "H"; eauto.
  Qed.

  Lemma env_ltyped_insert Γ vs x A v :
    A v -∗ env_ltyped Γ vs -∗
      env_ltyped (binder_insert x A Γ) (binder_insert x v vs).
  Proof.
    destruct x as [|x]=> /=; first by auto.
    iIntros "HA HΓ".
    rewrite /env_ltyped.
    set Γ' := <[x := A]> Γ.
    assert (Hx: Γ' !! x = Some A).
    { apply lookup_insert. }
    iApply (big_sepM_delete _ _ _ _ Hx).
    iSplitL "HA".
    - iExists v. iFrame. iPureIntro. apply lookup_insert.
    - assert (Hsub: delete x Γ' ⊆ Γ).
      { rewrite delete_insert_delete. apply delete_subseteq. }
      iPoseProof (big_sepM_subseteq _ _ _ Hsub with "HΓ") as "HΓ".
      iApply (big_sepM_mono with "HΓ"). simpl.
      iIntros (y B Hy) "HB".
      iDestruct "HB" as (w Hw) "HB".
      iExists w. iFrame. iPureIntro.
      apply lookup_delete_Some in Hy.
      destruct Hy as [Hxy _].
      rewrite -Hw.
      apply lookup_insert_ne.
      assumption.
  Qed.
End Environment.
