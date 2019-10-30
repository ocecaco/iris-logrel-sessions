From logrel_heaplang_sessions Require Export lty ltyping split copy.
From iris.heap_lang Require Export lifting metatheory.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.

Section types.
  Context `{heapG Σ}.

  (* I'm guessing the postcondition doesn't need an additional later
  for contractiveness since the WP already has one? *)
  Definition lty_arr (A1 A2 : lty Σ) : lty Σ := Lty (λ w,
    ∀ v, ▷ A1 v -∗ WP App w v {{ A2 }})%I.
End types.

Notation "A → B" := (lty_copy (lty_arr A B)) : lty_scope.
Infix "⊸" := lty_arr (at level 20, right associativity) : lty_scope.

Section properties.
  Context `{heapG Σ}.

  (* TODO: There's probably a cleaner way to do this *)
  Global Instance lty_arr_contractive n : Proper (dist_later n ==> dist_later n ==> dist n) lty_arr.
  Proof.
    intros A A' ? B B' ?.
    apply lty_ne.
    intros f.
    f_equiv.
    intros w.
    f_equiv.
    - by f_contractive.
    - apply wp_contractive.
      { apply _. }
      intros q.
      destruct n as [|n'].
      + done.
      + by simpl.
  Qed.

  Global Instance lty_arr_ne : NonExpansive2 (@lty_arr Σ _).
  Proof. solve_proper. Qed.

  Lemma ltyped_var Γ (x : string) A :
    Γ !! x = Some A → Γ ⊨ x : A.
  Proof.
    iIntros (HΓx vs) "HΓ /=".
    iDestruct (env_ltyped_lookup with "HΓ") as (v ->) "HA"; first done.
    by iApply wp_value.
  Qed.

  Lemma ltyped_app Γ Γ1 Γ2 e1 e2 A1 A2 :
    env_split Γ Γ1 Γ2 →
    (Γ1 ⊨ e1 : A1 ⊸ A2) → (Γ2 ⊨ e2 : A1) →
    Γ ⊨ e1 e2 : A2.
  Proof.
    intros Hsplit H1 H2.
    iIntros (vs) "HΓ /=".
    iPoseProof (Hsplit with "HΓ") as "[HΓ1 HΓ2]".
    iPoseProof H1 as "H1".
    iPoseProof H2 as "H2".
    wp_apply (wp_wand with "(H2 [HΓ2 //])").
    iIntros (v) "HA1".
    wp_apply (wp_wand with "(H1 [HΓ1 //])").
    iIntros (f) "Hf". iApply ("Hf" $! v with "HA1").
  Qed.

  Lemma ltyped_lam Γ x e A1 A2 :
    (binder_insert x A1 Γ ⊨ e : A2) →
    Γ ⊨ (λ: x, e) : A1 ⊸ A2.
  Proof.
    intros He.
    iPoseProof He as "He".
    iIntros (vs) "HΓ /=". wp_pures.
    iIntros (v) "HA1". wp_pures.
    iSpecialize ("He" $! (binder_insert x v vs) with "[HΓ HA1]").
    { iApply (env_ltyped_insert with "[HA1 //] [HΓ //]"). }
    destruct x as [|x]; rewrite /= -?subst_map_insert //.
  Qed.

  (* The first version of this had Γ ⊨ f : A1 → A2 with f : val, but
  it seemed strange to me that substitution does nothing to values,
  because f is probably a closure and might contain free
  variables. *)
  Lemma ltyped_rec Γ Γ' f x e A1 A2:
    env_copy Γ Γ' →
    (binder_insert f (A1 → A2)%lty (binder_insert x A1 Γ') ⊨ e : A2) →
    Γ ⊨ (rec: f x := e) : A1 → A2.
  Proof.
    intros Hcopy He.
    iPoseProof He as "He".
    iIntros (vs) "HΓ /=". wp_pures.
    iPoseProof (Hcopy with "HΓ") as "#HΓ'".
    iClear "HΓ". iLöb as "IH".
    iModIntro.
    iIntros (v) "HA1". wp_pures. set (r := RecV f x _).
    iSpecialize ("He" $! (binder_insert f r (binder_insert x v vs)) with "[HΓ' HA1]").
    { iApply (env_ltyped_insert with "IH"). iApply (env_ltyped_insert with "[HA1] [HΓ']").
      - iFrame "HA1".
      - iFrame "HΓ'". } (* Why doesn't // work here for env_ltyped_insert premises? *)
    destruct x as [|x], f as [|f]; rewrite /= -?subst_map_insert //.
    destruct (decide (x = f)) as [->|].
    - by rewrite subst_subst delete_idemp insert_insert -subst_map_insert.
    - rewrite subst_subst_ne // -subst_map_insert.
      by rewrite -delete_insert_ne // -subst_map_insert.
  Qed.

End properties.
