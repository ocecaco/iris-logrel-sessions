  Definition lty_arr (A1 A2 : lty Σ) : lty Σ := Lty (λ w,
    ∀ v, A1 v -∗ WP App w v {{ A2 }})%I.

Infix "→" := lty_arr : lty_scope.

  Global Instance lty_arr_ne : NonExpansive2 (@lty_arr Σ _).
  Proof. solve_proper. Qed.

  Lemma ltyped_var Γ (x : string) A : Γ !! x = Some A → Γ ⊨ x : A.
  Proof.
    iIntros (HΓx vs) "HΓ /=".
    iDestruct (env_ltyped_lookup with "HΓ") as (v ->) "HA"; first done.
    by iApply wp_value.
  Qed.

  Lemma ltyped_app Γ Γ1 Γ2 e1 e2 A1 A2 :
    env_split Γ Γ1 Γ2 -∗ (Γ1 ⊨ e1 : A1 → A2) -∗ (Γ2 ⊨ e2 : A1) -∗ Γ ⊨ e1 e2 : A2.
  Proof.
    iIntros "Hcompat H1 H2" (vs) "HΓ /=".
    iSpecialize ("Hcompat" with "HΓ").
    iDestruct "Hcompat" as "[HΓ1 HΓ2]".
    wp_apply (wp_wand with "(H2 [HΓ2 //])").
    iIntros (v) "HA1".
    wp_apply (wp_wand with "(H1 [HΓ1 //])").
    iIntros (f) "Hf". iApply ("Hf" $! v with "HA1").
  Qed.

  Lemma ltyped_lam Γ x e A1 A2 :
    (binder_insert x A1 Γ ⊨ e : A2) -∗
    Γ ⊨ (λ: x, e) : A1 → A2.
  Proof.
    iIntros "H" (vs) "HΓ /=". wp_pures.
    iIntros (v) "HA1". wp_pures.
    iSpecialize ("H" $! (binder_insert x v vs) with "[HΓ HA1]").
    { iApply (env_ltyped_insert with "[HA1 //] [HΓ //]"). }
    destruct x as [|x]; rewrite /= -?subst_map_insert //.
  Qed.
