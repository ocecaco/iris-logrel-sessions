From stdpp Require Import sorting.
From actris.channel Require Import proto_channel proofmode.
From iris.heap_lang Require Import proofmode notation.
From actris.utils Require Export llist compare.

Definition lmerge : val :=
  rec: "go" "cmp" "ys" "zs" :=
    if: lisnil "ys" then lapp "ys" "zs" else
    if: lisnil "zs" then #() else
    let: "y" := lhead "ys" in
    let: "z" := lhead "zs" in
    if: "cmp" "y" "z"
    then lpop "ys";; "go" "cmp" "ys" "zs";; lcons "y" "ys"
    else lpop "zs";; "go" "cmp" "ys" "zs";; lcons "z" "ys".

Definition sort_service : val :=
  rec: "go" "cmp" "c" :=
    let: "xs" := recv "c" in
    if: llength "xs" ≤ #1 then send "c" #() else
    let: "zs" := lsplit "xs" in
    let: "cy" := start_chan (λ: "c", "go" "cmp" "c") in
    let: "cz" := start_chan (λ: "c", "go" "cmp" "c") in
    send "cy" "xs";;
    send "cz" "zs";;
    recv "cy";; recv "cz";;
    lmerge "cmp" "xs" "zs";;
    send "c" #().

Definition sort_service_func : val := λ: "c",
  let: "cmp" := recv "c" in
  sort_service "cmp" "c".

Definition sort_client_func : val := λ: "cmp" "xs",
  let: "c" := start_chan sort_service_func in
  send "c" "cmp";; send "c" "xs";;
  recv "c".

Section sort.
  Context `{!heapG Σ, !proto_chanG Σ}.

  Definition sort_protocol {A} (I : A → val → iProp Σ) (R : A → A → Prop)
      `{!RelDecision R, !Total R} : iProto Σ :=
    (<!> (xs : list A) (l : loc), MSG #l {{ llist I l xs }};
     <?> (xs' : list A), MSG #() {{ ⌜ Sorted R xs' ⌝ ∗ ⌜ xs' ≡ₚ xs ⌝ ∗ llist I l xs' }};
     END)%proto.

  Definition sort_protocol_func : iProto Σ :=
    (<!> A (I : A → val → iProp Σ) (R : A → A → Prop)
         `{!RelDecision R, !Total R} (cmp : val),
       MSG cmp {{ cmp_spec I R cmp }};
     sort_protocol I R)%proto.

  Lemma lmerge_spec {A} (I : A → val → iProp Σ) (R : A → A → Prop)
      `{!RelDecision R, !Total R} (cmp : val) l1 l2 xs1 xs2 :
    cmp_spec I R cmp -∗
    {{{ llist I l1 xs1 ∗ llist I l2 xs2 }}}
      lmerge cmp #l1 #l2
    {{{ RET #(); llist I l1 (list_merge R xs1 xs2) }}}.
  Proof.
    iIntros "#Hcmp" (Ψ) "!> [Hl1 Hl2] HΨ".
    iLöb as "IH" forall (l2 xs1 xs2 Ψ).
    wp_lam. wp_apply (lisnil_spec with "Hl1"); iIntros "Hl1".
    destruct xs1 as [|x1 xs1]; wp_pures.
    { wp_apply (lapp_spec with "[$Hl1 $Hl2]"); iIntros "[Hl1 _] /=".
      iApply "HΨ". iFrame. by rewrite list_merge_nil_l. }
    wp_apply (lisnil_spec with "Hl2"); iIntros "Hl2".
    destruct xs2 as [|x2 xs2]; wp_pures.
    { iApply "HΨ". iFrame. }
    wp_apply (lhead_spec_aux with "Hl1"); iIntros (v1 l1') "[HIx1 Hl1]".
    wp_apply (lhead_spec_aux with "Hl2"); iIntros (v2 l2') "[HIx2 Hl2]".
    wp_apply ("Hcmp" with "[$HIx1 $HIx2]"); iIntros "[HIx1 HIx2] /=".
    case_bool_decide; wp_pures.
    - rewrite decide_True //.
      wp_apply (lpop_spec_aux with "Hl1"); iIntros "Hl1".
      wp_apply ("IH" $! _ _ (_ :: _) with "Hl1 [HIx2 Hl2]").
      { iExists _, _. iFrame. }
      iIntros "Hl1".
      wp_apply (lcons_spec with "[$Hl1 $HIx1]"). iIntros "Hl1". iApply "HΨ". iFrame.
    - rewrite decide_False //.
      wp_apply (lpop_spec_aux with "Hl2"); iIntros "Hl2".
      wp_apply ("IH" $! _ (_ :: _) with "[HIx1 Hl1] Hl2").
      { iExists _, _. iFrame. }
      iIntros "Hl1".
      wp_apply (lcons_spec with "[$Hl1 $HIx2]"); iIntros "Hl1". iApply "HΨ". iFrame.
  Qed.

  Lemma sort_service_spec {A} (I : A → val → iProp Σ) (R : A → A → Prop)
      `{!RelDecision R, !Total R} (cmp : val) p c :
    cmp_spec I R cmp -∗
    {{{ c ↣ (iProto_dual (sort_protocol I R) <++> p) }}}
      sort_service cmp c
    {{{ RET #(); c ↣ p }}}.
  Proof.
    iIntros "#Hcmp !>" (Ψ) "Hc HΨ". iLöb as "IH" forall (p c Ψ). wp_lam.
    wp_recv (xs l) as "Hl".
    wp_apply (llength_spec with "Hl"); iIntros "Hl".
    wp_op; case_bool_decide as Hlen; wp_if.
    { assert (Sorted R xs).
      { destruct xs as [|x1 [|x2 xs]]; simpl in *; eauto with lia. }
      wp_send with "[$Hl]"; first by auto. by iApply "HΨ". }
    wp_apply (lsplit_spec with "Hl"); iIntros (l2 vs1 vs2);
      iDestruct 1 as (->) "[Hl1 Hl2]".
    wp_apply (start_chan_proto_spec (sort_protocol I R)); iIntros (cy) "Hcy".
    { rewrite -{2}(right_id END%proto _ (iProto_dual _)).
      wp_apply ("IH" with "Hcy"); auto. }
    wp_apply (start_chan_proto_spec (sort_protocol I R)); iIntros (cz) "Hcz".
    { rewrite -{2}(right_id END%proto _ (iProto_dual _)).
      wp_apply ("IH" with "Hcz"); auto. }
    wp_send with "[$Hl1]".
    wp_send with "[$Hl2]".
    wp_recv (ys1) as (??) "Hl1".
    wp_recv (ys2) as (??) "Hl2".
    wp_apply (lmerge_spec with "Hcmp [$Hl1 $Hl2]"); iIntros "Hl".
    wp_send ((list_merge R ys1 ys2)) with "[$Hl]".
    - iSplit; iPureIntro.
      + by apply (Sorted_list_merge _).
      + rewrite (merge_Permutation R). by f_equiv.
    - by iApply "HΨ".
  Qed.

  Lemma sort_service_func_spec p c :
    {{{ c ↣ (iProto_dual sort_protocol_func <++> p) }}}
      sort_service_func c
    {{{ RET #(); c ↣ p }}}.
  Proof.
    iIntros (Ψ) "Hc HΨ". wp_lam.
    wp_recv (A I R ?? cmp) as "#Hcmp".
    by wp_apply (sort_service_spec with "Hcmp Hc").
  Qed.

  Lemma sort_client_func_spec {A} (I : A → val → iProp Σ) R
       `{!RelDecision R, !Total R} cmp l (xs : list A) :
    cmp_spec I R cmp -∗
    {{{ llist I l xs }}}
      sort_client_func cmp #l
    {{{ ys, RET #(); ⌜Sorted R ys⌝ ∗ ⌜ys ≡ₚ xs⌝ ∗ llist I l ys }}}.
  Proof.
    iIntros "#Hcmp !>" (Φ) "Hl HΦ". wp_lam.
    wp_apply (start_chan_proto_spec sort_protocol_func); iIntros (c) "Hc".
    { rewrite -(right_id END%proto _ (iProto_dual _)).
      wp_apply (sort_service_func_spec with "Hc"); auto. }
    wp_send with "[$Hcmp]".
    wp_send with "[$Hl]".
    wp_recv (ys) as "(Hsorted & Hperm & Hl)".
    wp_pures. iApply "HΦ"; iFrame.
  Qed.
End sort.
