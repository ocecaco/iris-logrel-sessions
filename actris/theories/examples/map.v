From actris.channel Require Import proto_channel proofmode.
From iris.heap_lang Require Import proofmode notation lib.spin_lock.
From actris.utils Require Import llist contribution.
From iris.algebra Require Import gmultiset.

Definition par_map_worker : val :=
  rec: "go" "map" "l" "c" :=
    acquire "l";;
      send "c" #true;;
      if: ~recv "c" then release "l" else
      let: "x" := recv "c" in
    release "l";;
      let: "y" := "map" "x" in
    acquire "l";;
      send "c" #false;;
      send "c" "y";;
    release "l";;
    "go" "map" "l" "c".

Definition par_map_workers : val :=
  rec: "go" "n" "map" "l" "c" :=
    if: "n" = #0 then #() else
    Fork (par_map_worker "map" "l" "c");;
    "go" ("n" - #1) "map" "l" "c".

Definition par_map_service : val := λ: "n" "map" "c",
  let: "l" := newlock #() in
  par_map_workers "n" "map" "l" "c".

Definition par_map_client_loop : val :=
  rec: "go" "n" "c" "xs" "ys" :=
    if: "n" = #0 then #() else
    if: recv "c" then (* send item to map_worker *)
      if: lisnil "xs" then
        send "c" #false;;
        "go" ("n" - #1) "c" "xs" "ys"
      else
        send "c" #true;;
        send "c" (lpop "xs");;
        "go" "n" "c" "xs" "ys"
    else (* receive item from map_worker *)
      let: "zs" := recv "c" in
      lprep "ys" "zs";;
      "go" "n" "c" "xs" "ys".

Definition par_map_client : val := λ: "n" "map" "xs",
  let: "c" := start_chan (λ: "c", par_map_service "n" "map" "c") in
  let: "ys" := lnil #() in
  par_map_client_loop "n" "c" "xs" "ys";;
  lapp "xs" "ys".

Class mapG Σ A `{Countable A} := {
  map_contributionG :> contributionG Σ (gmultisetUR A);
  map_lockG :> lockG Σ;
}.

Section map.
  Context `{Countable A} {B : Type}.
  Context `{!heapG Σ, !proto_chanG Σ, !mapG Σ A}.
  Context (IA : A → val → iProp Σ) (IB : B → val → iProp Σ) (map : A → list B).
  Local Open Scope nat_scope.
  Implicit Types n : nat.

  Definition map_spec (vmap : val) : iProp Σ := (∀ x v,
    {{{ IA x v }}} vmap v {{{ l, RET #l; llist IB l (map x) }}})%I.

  Definition par_map_protocol_aux (rec : nat -d> gmultiset A -d> iProto Σ) :
      nat -d> gmultiset A -d> iProto Σ := λ i X,
    let rec : nat → gmultiset A → iProto Σ := rec in
    (if i is 0 then END else
     ((<!> x v, MSG v {{ IA x v }}; rec i (X ⊎ {[ x ]}))
        <+>
      rec (pred i) X
     ) <{⌜ i ≠ 1 ∨ X = ∅ ⌝}&>
         <?> x (l : loc), MSG #l {{ ⌜ x ∈ X ⌝ ∗ llist IB l (map x) }};
         rec i (X ∖ {[ x ]}))%proto.
  Instance par_map_protocol_aux_contractive : Contractive par_map_protocol_aux.
  Proof. solve_proper_prepare. f_equiv. solve_proto_contractive. Qed.
  Definition par_map_protocol := fixpoint par_map_protocol_aux.
  Global Instance par_map_protocol_unfold n X :
    ProtoUnfold (par_map_protocol n X) (par_map_protocol_aux par_map_protocol n X).
  Proof. apply proto_unfold_eq, (fixpoint_unfold par_map_protocol_aux). Qed.

  Definition map_worker_lock_inv (γ : gname) (c : val) : iProp Σ :=
    (∃ i X, server γ i X ∗ c ↣ iProto_dual (par_map_protocol i X))%I.

  Lemma par_map_worker_spec γl γ vmap lk c :
    map_spec vmap -∗
    {{{ is_lock nroot γl lk (map_worker_lock_inv γ c) ∗ client γ (∅ : gmultiset A) }}}
      par_map_worker vmap lk c
    {{{ RET #(); True }}}.
  Proof.
    iIntros "#Hmap !>" (Φ) "[#Hlk Hγ] HΦ". iLöb as "IH".
    wp_rec; wp_pures.
    wp_apply (acquire_spec with "Hlk"); iIntros "[Hl H]".
    iDestruct "H" as (i X) "[Hs Hc]".
    iDestruct (@server_agree with "Hs Hγ") as %[??]; destruct i as [|i]=>//=.
    iAssert ⌜ S i ≠ 1 ∨ X = ∅ ⌝%I as %?.
    { destruct i as [|i]; last auto with lia.
      iDestruct (@server_1_agree with "Hs Hγ") as %?%leibniz_equiv; auto. }
    wp_select. wp_branch; wp_pures; last first.
    { iMod (@dealloc_client with "Hs Hγ") as "Hs /=".
      wp_apply (release_spec with "[$Hlk $Hl Hc Hs]").
      { iExists i, _. iFrame. }
      iIntros "_". by iApply "HΦ". }
    wp_recv (x v) as "HI".
    iMod (@update_client with "Hs Hγ") as "[Hs Hγ]".
    { apply (gmultiset_local_update_alloc _ _ {[ x ]}). }
    rewrite left_id_L.
    wp_apply (release_spec with "[$Hlk $Hl Hc Hs]").
    { iExists (S i), _. iFrame. }
    clear dependent i X. iIntros "Hu". wp_apply ("Hmap" with "HI"); iIntros (l) "HI".
    wp_apply (acquire_spec with "[$Hlk $Hu]"); iIntros "[Hl H]".
    iDestruct "H" as (i X) "[Hs Hc]".
    iDestruct (@server_agree with "Hs Hγ")
      as %[??%gmultiset_included]; destruct i as [|i]=>//=.
    wp_select. wp_send with "[$HI]".
    { by rewrite gmultiset_elem_of_singleton_subseteq. }
    iMod (@update_client with "Hs Hγ") as "[Hs Hγ]".
    { by apply (gmultiset_local_update_dealloc _ _ {[ x ]}). }
    rewrite gmultiset_difference_diag.
    wp_apply (release_spec with "[$Hlk $Hl Hc Hs]").
    { iExists (S i), _. iFrame. }
    iIntros "Hu". by wp_apply ("IH" with "[$] [$]").
  Qed.

  Lemma par_map_workers_spec γl γ n vmap lk c :
    map_spec vmap -∗
    {{{ is_lock nroot γl lk (map_worker_lock_inv γ c) ∗
        [∗] replicate n (client γ (∅:gmultiset A)) }}}
      par_map_workers #n vmap lk c
    {{{ RET #(); True }}}.
  Proof.
    iIntros "#Hmap !>" (Φ) "[#Hlk Hγs] HΦ".
    iInduction n as [|n] "IH"; wp_rec; wp_pures; simpl.
    { by iApply "HΦ". }
    iDestruct "Hγs" as "[Hγ Hγs]".
    wp_apply (wp_fork with "[Hγ]").
    { iNext. wp_apply (par_map_worker_spec with "Hmap [$]"); auto. }
    wp_pures. rewrite Nat2Z.inj_succ Z.sub_1_r Z.pred_succ.
    wp_apply ("IH" with "[$] [$]").
  Qed.

  Lemma par_map_service_spec n vmap c :
    map_spec vmap -∗
    {{{ c ↣ iProto_dual (par_map_protocol n ∅) }}}
      par_map_service #n vmap c
    {{{ RET #(); True }}}.
  Proof.
    iIntros "#Hf !>"; iIntros (Φ) "Hc HΦ". wp_lam; wp_pures.
    iMod (contribution_init_pow (A:=gmultisetUR A) n) as (γ) "[Hs Hγs]".
    wp_apply (newlock_spec nroot (map_worker_lock_inv γ c) with "[Hc Hs]").
    { iExists n, ∅. iFrame. }
    iIntros (lk γl) "#Hlk".
    wp_apply (par_map_workers_spec with "Hf [$Hlk $Hγs]"); auto.
  Qed.

  Lemma par_map_client_loop_spec n c l k xs X ys :
    (n = 0 → X = ∅ ∧ xs = []) →
    {{{ llist IA l xs ∗ llist IB k ys ∗ c ↣ par_map_protocol n X }}}
      par_map_client_loop #n c #l #k
    {{{ ys', RET #();
      ⌜ys' ≡ₚ (xs ++ elements X) ≫= map⌝ ∗ llist IA l [] ∗ llist IB k (ys' ++ ys)
    }}}.
  Proof.
    iIntros (Hn Φ) "(Hl & Hk & Hc) HΦ".
    iLöb as "IH" forall (n l xs X ys Hn Φ); wp_rec; wp_pures; simpl.
    case_bool_decide; wp_pures; simplify_eq/=.
    { destruct Hn as [-> ->]; first lia.
      iApply ("HΦ" $! []); simpl; auto with iFrame. }
    destruct n as [|n]=> //=. wp_branch as %?|%_; wp_pures.
    - wp_apply (lisnil_spec with "Hl"); iIntros "Hl".
      destruct xs as [|x xs]; csimpl; wp_pures.
      + wp_select. wp_pures. rewrite Nat2Z.inj_succ Z.sub_1_r Z.pred_succ.
        iApply ("IH" with "[%] Hl Hk Hc [$]"); naive_solver.
      + wp_select. wp_apply (lpop_spec with "Hl"); iIntros (v) "[HIx Hl]".
        wp_send with "[$HIx]".
        wp_apply ("IH" with "[] Hl Hk Hc"); first done. iIntros (ys').
        rewrite gmultiset_elements_disj_union gmultiset_elements_singleton.
        rewrite assoc_L -(comm _ [x]). iApply "HΦ".
    - wp_recv (x l') as (Hx) "Hl'".
      wp_apply (lprep_spec with "[$Hk $Hl']"); iIntros "[Hk _]".
      wp_apply ("IH" with "[] Hl Hk Hc"); first done.
      iIntros (ys'); iDestruct 1 as (Hys) "Hk"; simplify_eq/=.
      iApply ("HΦ" $! (ys' ++ map x)). iSplit.
      + iPureIntro. rewrite (gmultiset_disj_union_difference {[ x ]} X)
          -?gmultiset_elem_of_singleton_subseteq //.
        rewrite (comm disj_union) gmultiset_elements_disj_union.
        by rewrite gmultiset_elements_singleton assoc_L bind_app -Hys /= right_id_L.
      + by rewrite -assoc_L.
  Qed.

  Lemma par_map_client_spec n vmap l xs :
    0 < n →
    map_spec vmap -∗
    {{{ llist IA l xs }}}
      par_map_client #n vmap #l
    {{{ ys, RET #(); ⌜ys ≡ₚ xs ≫= map⌝ ∗ llist IB l ys }}}.
  Proof.
    iIntros (?) "#Hmap !>"; iIntros (Φ) "Hl HΦ". wp_lam; wp_pures.
    wp_apply (start_chan_proto_spec (par_map_protocol n ∅)); iIntros (c) "// Hc".
    { wp_apply (par_map_service_spec with "Hmap Hc"); auto. }
    wp_pures. wp_apply (lnil_spec with "[//]"); iIntros (k) "Hk".
    wp_apply (par_map_client_loop_spec with "[$Hl $Hk $Hc //]"); first lia.
    iIntros (ys) "(?&Hl&Hk)". rewrite /= gmultiset_elements_empty !right_id_L.
    wp_apply (lapp_spec IB _ _ [] with "[$Hl $Hk]"); iIntros "[Hk _] /=".
    wp_pures. iApply "HΦ"; auto.
  Qed.
End map.
