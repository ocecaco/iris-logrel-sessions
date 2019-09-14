From iris.base_logic Require Export base_logic lib.iprop lib.own.
From iris.proofmode Require Export tactics.
From iris.algebra Require Import excl auth csum gmultiset frac_auth.
From iris.algebra Require Export local_updates.

Class contributionG Σ (A : ucmraT) `{!CmraDiscrete A} := {
  contribution_inG :> inG Σ
    (authR (optionUR (csumR (prodR positiveR A) (exclR unitO))))
}.

Definition server `{contributionG Σ A} (γ : gname) (n : nat) (x : A) : iProp Σ :=
  (if decide (n = O)
   then x ≡ ε ∗ own γ (● (Some (Cinr (Excl ())))) ∗ own γ (◯ (Some (Cinr (Excl ()))))
   else own γ (● (Some (Cinl (Pos.of_nat n, x)))))%I.
Typeclasses Opaque server.
Instance: Params (@server) 6.

Definition client `{contributionG Σ A} (γ : gname) (x : A) : iProp Σ :=
  own γ (◯ (Some (Cinl (1%positive, x)))).
Typeclasses Opaque client.
Instance: Params (@client) 5.

Section contribution.
  Context `{contributionG Σ A}.
  Implicit Types x y : A.

  Global Instance server_ne γ n : NonExpansive (server γ n).
  Proof. solve_proper. Qed.
  Global Instance server_proper γ n : Proper ((≡) ==> (≡)) (server γ n).
  Proof. apply (ne_proper _). Qed.
  Global Instance client_ne γ : NonExpansive (client γ).
  Proof. solve_proper. Qed.
  Global Instance client_proper γ : Proper ((≡) ==> (≡)) (client γ).
  Proof. apply (ne_proper _). Qed.

  Lemma contribution_init : (|==> ∃ γ, server γ 0 ε)%I.
  Proof.
    iMod (own_alloc (● (Some (Cinr (Excl ()))) ⋅ ◯ (Some (Cinr (Excl ())))))
      as (γ) "[Hγ Hγ']"; first by apply auth_both_valid_2.
    iExists γ. rewrite /server. by case_decide; auto with iFrame.
  Qed.

  Lemma server_0_empty γ x : server γ 0 x -∗ x ≡ ε.
  Proof. rewrite /server. case_decide=> //. iIntros "[? _] //". Qed.

  Lemma server_1_agree γ x y : server γ 1 x -∗ client γ y -∗ ⌜ x ≡ y ⌝.
  Proof.
    rewrite /server /client. case_decide=> //. iIntros "Hs Hc".
    iDestruct (own_valid_2 with "Hs Hc")
      as %[[[_ ?]%(inj Cinl)|Hincl]%Some_included _]%auth_both_valid; first done.
    move: Hincl. rewrite Cinl_included prod_included /= pos_included=> -[? _].
    by destruct (Pos.lt_irrefl 1).
  Qed.

  Lemma server_valid γ n x : server γ n x -∗ ✓ x.
  Proof.
    rewrite /server. case_decide.
    - iDestruct 1 as (->) "_". iPureIntro. apply ucmra_unit_valid.
    - iIntros "Hs". iDestruct (own_valid with "Hs") as %Hv.
      move: Hv. by rewrite auth_auth_valid=> -[??].
  Qed.

  Lemma client_valid γ x : client γ x -∗ ✓ x.
  Proof.
    rewrite /client. iIntros "Hs". iDestruct (own_valid with "Hs") as %Hv.
    move: Hv. by rewrite auth_frag_valid=> -[??].
  Qed.

  Lemma server_agree γ n x y : server γ n x -∗ client γ y -∗ ⌜ n ≠ 0 ∧ y ≼ x ⌝.
  Proof.
    rewrite /server /client. iIntros "Hs Hc". case_decide; subst.
    - iDestruct "Hs" as "(_ & _ & Hc')".
      by iDestruct (own_valid_2 with "Hc Hc'") as %?.
    - iDestruct (own_valid_2 with "Hs Hc")
        as %[[[??]%(inj Cinl)|Hincl]%Some_included _]%auth_both_valid.
      { setoid_subst. by destruct n. }
      move: Hincl. rewrite Cinl_included prod_included /= pos_included=> -[??].
      by destruct n.
  Qed.

  Lemma alloc_client γ n x :
    server γ n x ==∗ server γ (S n) x ∗ client γ ε.
  Proof.
    rewrite /server /client.
    destruct (decide (n = 0)) as [->|?]; case_decide; try done.
    - iDestruct 1 as (Hx) "[Hs Hc]"; setoid_subst.
      iMod (own_update_2 with "Hs Hc") as "[$ $]"; last done.
      apply auth_update, option_local_update.
      eapply transitivity with (Cinl (Pos.of_nat 1, ε), Cinl (1%positive, ε)).
      { apply exclusive_local_update. split; [done|]. apply ucmra_unit_valid. }
      by apply csum_local_update_l, prod_local_update_2.
    - iIntros "Hs". iMod (own_update with "Hs") as "[$ $]"; last done.
      eapply auth_update_alloc, transitivity
        with (Some (Cinl (Pos.of_nat (S n), x)), Some (Cinl (1%positive, ε))).
      { rewrite Nat2Pos.inj_succ // -Pos.add_1_l -{2}(left_id ε op x).
        rewrite -(right_id _ _ (Some (Cinl (1%positive, _)))).
        rewrite pair_op Cinl_op Some_op. apply op_local_update_discrete.
        intros [??]; split=> //=. by rewrite left_id. }
      by apply option_local_update, csum_local_update_l, prod_local_update_2.
  Qed.

  Lemma dealloc_client γ n x :
    server γ n x -∗ client γ ε ==∗ server γ (pred n) x.
  Proof.
    iIntros "Hs Hc". iDestruct (server_valid with "Hs") as %Hv.
    destruct (decide (n = 1)) as [->|]; simpl.
    - iDestruct (server_1_agree with "Hs Hc") as %->.
      rewrite /server /client; repeat case_decide=> //.
      iMod (own_update_2 with "Hs Hc") as "[$ $]"; last done.
      by apply auth_update, option_local_update, (replace_local_update _ _).
    - iDestruct (server_agree with "Hs Hc") as %[? [z ->]].
      rewrite /server /client. destruct n as [|[|n]]; case_decide=>//=.
      iApply (own_update_2 with "Hs Hc"). apply auth_update_dealloc.
      rewrite -(right_id _ _ (Some (Cinl (1%positive, _)))).
      rewrite Nat2Pos.inj_succ // -Pos.add_1_l.
      rewrite pair_op Cinl_op Some_op left_id. apply (cancel_local_update _ _ _).
  Qed.

  Lemma update_client γ n x y x' y' :
    (x,y) ~l~> (x',y') →
    server γ n x -∗ client γ y ==∗ server γ n x' ∗ client γ y'.
  Proof.
    iIntros (?) "Hs Hc". destruct (decide (n = 1)) as [->|]; simpl.
    - iDestruct (server_1_agree with "Hs Hc") as %?; setoid_subst.
      rewrite /server /client. case_decide=> //=.
      iMod (own_update_2 with "Hs Hc") as "[$ $]"; last done.
      by apply auth_update, option_local_update,
        csum_local_update_l, prod_local_update_2.
    - iDestruct (server_agree with "Hs Hc") as %[??].
      rewrite /server /client. case_decide=> //=.
      iMod (own_update_2 with "Hs Hc") as "[$ $]"; last done.
      by apply auth_update, option_local_update,
        csum_local_update_l, prod_local_update_2.
  Qed.

  (** Derived *)
  Lemma contribution_init_pow n :
    (|==> ∃ γ, server γ n ε ∗ [∗] replicate n (client γ ε))%I.
  Proof.
    iMod (contribution_init) as (γ) "Hs". iExists γ.
    iInduction n as [|n] "IH"; simpl; first by iFrame.
    iMod ("IH" with "Hs") as "[Hs $]". by iApply alloc_client.
  Qed.
End contribution.
