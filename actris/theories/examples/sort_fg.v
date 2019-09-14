From stdpp Require Export sorting.
From actris.channel Require Import proto_channel proofmode.
From iris.heap_lang Require Import proofmode notation.
From iris.heap_lang Require Import assert.
From actris.utils Require Import llist compare.

Definition cont := true.
Definition stop := false.

Definition sort_service_fg_split : val :=
  rec: "go" "c" "c1" "c2" :=
    if: ~(recv "c") then send "c1" #stop;; send "c2" #stop else
    let: "x" := recv "c" in
    send "c1" #cont;; send "c1" "x";;
    "go" "c" "c2" "c1".

Definition sort_service_fg_forward : val :=
  rec: "go" "c" "cin" :=
    if: ~(recv "cin") then send "c" #stop else
    let: "x" := recv "cin" in
    send "c" #cont;; send "c" "x";;
    "go" "c" "cin".

Definition sort_service_fg_merge : val :=
  rec: "go" "cmp" "c" "x1" "c1" "c2" :=
    if: ~recv "c2" then
      send "c" #cont;; send "c" "x1";;
      sort_service_fg_forward "c" "c1"
    else
      let: "x2" := recv "c2" in
      if: "cmp" "x1" "x2" then
        send "c" #cont;; send "c" "x1";; "go" "cmp" "c" "x2" "c2" "c1"
      else
        send "c" #cont;; send "c" "x2";; "go" "cmp" "c" "x1" "c1" "c2".

Definition sort_service_fg : val :=
  rec: "go" "cmp" "c" :=
    if: ~(recv "c") then send "c" #stop else
    let: "x" := recv "c" in
    if: ~(recv "c") then send "c" #cont;; send "c" "x";; send "c" #stop else
    let: "y" := recv "c" in
    let: "c1" := start_chan (λ: "c", "go" "cmp" "c") in
    let: "c2" := start_chan (λ: "c", "go" "cmp" "c") in
    send "c1" #cont;; send "c1" "x";;
    send "c2" #cont;; send "c2" "y";;
    sort_service_fg_split "c" "c1" "c2";;
    let: "x" := (if: recv "c1" then recv "c1" else assert #false) in
    sort_service_fg_merge "cmp" "c" "x" "c1" "c2".

Definition sort_service_fg_func : val := λ: "c",
  let: "cmp" := recv "c" in
  sort_service_fg "cmp" "c".

Definition send_all : val :=
  rec: "go" "c" "xs" :=
    if: lisnil "xs" then #() else
    send "c" #cont;; send "c" (lpop "xs");; "go" "c" "xs".

Definition recv_all : val :=
  rec: "go" "c" "ys" :=
    if: ~recv "c" then #() else
    let: "x" := recv "c" in
    "go" "c" "ys";; lcons "x" "ys".

Definition sort_client_fg : val := λ: "cmp" "xs",
  let: "c" := start_chan (λ: "c", sort_service_fg "cmp" "c") in
  send_all "c" "xs";;
  send "c" #stop;;
  recv_all "c" "xs".

Section sort_fg.
  Context `{!heapG Σ, !proto_chanG Σ}.

  Section sort_fg_inner.
  Context {A} (I : A → val → iProp Σ) (R : relation A) `{!RelDecision R, !Total R}.

  Definition sort_fg_tail_protocol_aux (xs : list A)
      (rec : list A -d> iProto Σ) : list A -d> iProto Σ := λ ys,
    ((<?> y v, MSG v {{ ⌜ TlRel R y ys ⌝ ∗ I y v }}; (rec : _ → iProto Σ) (ys ++ [y]))
     <&{⌜ ys ≡ₚ xs ⌝}> END)%proto.

  Instance sort_fg_tail_protocol_aux_contractive xs :
    Contractive (sort_fg_tail_protocol_aux xs).
  Proof. solve_proto_contractive. Qed.
  Definition sort_fg_tail_protocol (xs : list A) : list A → iProto Σ :=
    fixpoint (sort_fg_tail_protocol_aux xs).
  Global Instance sort_fg_tail_protocol_unfold xs ys :
    ProtoUnfold (sort_fg_tail_protocol xs ys)
      (sort_fg_tail_protocol_aux xs (sort_fg_tail_protocol xs) ys).
  Proof. apply proto_unfold_eq, (fixpoint_unfold (sort_fg_tail_protocol_aux _)). Qed.

  Definition sort_fg_head_protocol_aux
      (rec : list A -d> iProto Σ) : list A -d> iProto Σ := λ xs,
    ((<!> x v, MSG v {{ I x v }}; (rec : _ → iProto Σ) (xs ++ [x]))
     <+> sort_fg_tail_protocol xs [])%proto.

  Instance sort_fg_head_protocol_aux_contractive :
    Contractive sort_fg_head_protocol_aux.
  Proof. solve_proto_contractive. Qed.

  Definition sort_fg_head_protocol : list A → iProto Σ :=
    fixpoint sort_fg_head_protocol_aux.
  Global Instance sort_fg_head_protocol_unfold xs :
    ProtoUnfold (sort_fg_head_protocol xs)
      (sort_fg_head_protocol_aux sort_fg_head_protocol xs).
  Proof. apply proto_unfold_eq, (fixpoint_unfold sort_fg_head_protocol_aux). Qed.

  Definition sort_fg_protocol : iProto Σ := sort_fg_head_protocol [].

  Lemma sort_service_fg_split_spec c p c1 c2 xs xs1 xs2 :
    {{{
      c ↣ (iProto_dual (sort_fg_head_protocol xs) <++> p) ∗
      c1 ↣ sort_fg_head_protocol xs1 ∗ c2 ↣ sort_fg_head_protocol xs2
    }}}
      sort_service_fg_split c c1 c2
    {{{ xs' xs1' xs2', RET #();
      ⌜xs' ≡ₚ xs1' ++ xs2'⌝ ∗
      c ↣ (iProto_dual (sort_fg_tail_protocol (xs ++ xs') []) <++> p) ∗
      c1 ↣ sort_fg_tail_protocol (xs1 ++ xs1') [] ∗
      c2 ↣ sort_fg_tail_protocol (xs2 ++ xs2') []
    }}}.
  Proof.
    iIntros (Ψ) "(Hc & Hc1 & Hc2) HΨ". iLöb as "IH" forall (c c1 c2 xs xs1 xs2 Ψ).
    wp_rec. wp_branch.
    - wp_recv (x v) as "HI". wp_select. wp_send with "[$HI]".
      wp_apply ("IH" with "Hc Hc2 Hc1").
      iIntros (xs' xs1' xs2'); iDestruct 1 as (Hxs') "(Hc & Hc2 & Hc1)".
      rewrite -!(assoc_L (++)).
      iApply "HΨ". iFrame "Hc Hc1 Hc2". by rewrite Hxs' (comm (++) xs1') assoc_L.
    - wp_select. wp_select.
      iApply ("HΨ" $! [] [] []). rewrite !right_id_L. by iFrame.
  Qed.

  Lemma sort_service_fg_forward_spec c p cin xs ys zs xs' ys' :
    xs ≡ₚ xs' ++ zs →
    ys ≡ₚ ys' ++ zs →
    Sorted R ys →
    (∀ x, TlRel R x ys' → TlRel R x ys) →
    {{{
      c ↣ (iProto_dual (sort_fg_tail_protocol xs ys) <++> p) ∗
      cin ↣ sort_fg_tail_protocol xs' ys'
    }}}
      sort_service_fg_forward c cin
    {{{ RET #(); c ↣ p ∗ cin ↣ END }}}.
  Proof.
    iIntros (Hxs Hys Hsorted Hrel Ψ) "[Hc Hcin] HΨ".
    iLöb as "IH" forall (c cin xs ys xs' ys' Hxs Hys Hsorted Hrel).
    wp_rec. wp_branch as %_ | %Hys'.
    - wp_recv (x v) as (Htl) "HI".
      wp_select. wp_send with "[$HI]"; first by auto.
      wp_apply ("IH" with "[%] [%] [%] [%] Hc Hcin HΨ").
      * done.
      * by rewrite Hys -!assoc_L (comm _ zs).
      * auto using Sorted_snoc.
      * intros x'.
        inversion 1; discriminate_list || simplify_list_eq. by constructor.
    - wp_select with "[]".
      { by rewrite /= Hys Hxs Hys'. }
      iApply "HΨ". iFrame.
  Qed.

  Lemma sort_service_fg_merge_spec cmp c p c1 c2 xs ys xs1 xs2 y1 w1 ys1 ys2 :
    xs ≡ₚ xs1 ++ xs2 →
    ys ≡ₚ ys1 ++ ys2 →
    Sorted R ys →
    TlRel R y1 ys →
    (∀ x, TlRel R x ys2 → R x y1 → TlRel R x ys) →
    cmp_spec I R cmp -∗
    {{{
      c ↣ (iProto_dual (sort_fg_tail_protocol xs ys) <++> p) ∗
      c1 ↣ sort_fg_tail_protocol xs1 (ys1 ++ [y1]) ∗
      c2 ↣ sort_fg_tail_protocol xs2 ys2 ∗
      I y1 w1
    }}}
      sort_service_fg_merge cmp c w1 c1 c2
    {{{ RET #(); c ↣ p }}}.
  Proof.
    iIntros (Hxs Hys Hsort Htl Htl_le) "#Hcmp !>".
    iIntros (Ψ) "(Hc & Hc1 & Hc2 & HIy1) HΨ".
    iLöb as "IH" forall (c1 c2 xs1 xs2 ys y1 w1 ys1 ys2 Hxs Hys Hsort Htl Htl_le).
    wp_rec. wp_branch as %_ | %Hys2.
    - wp_recv (x v) as (Htl2) "HIx".
      wp_pures. wp_apply ("Hcmp" with "[$HIy1 $HIx]"); iIntros "[HIy1 HIx]".
      case_bool_decide.
      + wp_select. wp_send with "[$HIy1 //]".
        wp_apply ("IH" with "[%] [%] [%] [%] [%] Hc Hc2 Hc1 HIx HΨ").
        * by rewrite comm.
        * by rewrite assoc (comm _ ys2) Hys.
        * by apply Sorted_snoc.
        * by constructor.
        * intros x'.
          inversion 1; discriminate_list || simplify_list_eq. by constructor.
      + wp_select. wp_send with "[$HIx]".
        { iPureIntro. by apply Htl_le, total_not. }
        wp_apply ("IH" with "[% //] [%] [%] [%] [%] Hc Hc1 Hc2 HIy1 HΨ").
        * by rewrite Hys assoc.
        * by apply Sorted_snoc, Htl_le, total_not.
        * constructor. by apply total_not.
        * intros x'.
          inversion 1; discriminate_list || simplify_list_eq. by constructor.
    - wp_select. wp_send with "[$HIy1 //]".
      wp_apply (sort_service_fg_forward_spec with "[$Hc $Hc1]").
      * done.
      * by rewrite Hys Hys2 -!assoc_L (comm _ xs2).
      * by apply Sorted_snoc.
      * intros x'.
        inversion 1; discriminate_list || simplify_list_eq. by constructor.
      * iIntros "[Hc Hc1]". iApply "HΨ". iFrame.
  Qed.

  Lemma sort_service_fg_spec cmp c p :
    cmp_spec I R cmp -∗
    {{{ c ↣ (iProto_dual sort_fg_protocol <++> p) }}}
      sort_service_fg cmp c
    {{{ RET #(); c ↣ p }}}.
  Proof.
    iIntros "#Hcmp !>" (Ψ) "Hc HΨ". iLöb as "IH" forall (c p Ψ).
    wp_rec; wp_pures. wp_branch; wp_pures.
    - wp_recv (x1 v1) as "HIx1". wp_branch; wp_pures.
      + wp_recv (x2 v2) as "HIx2".
        wp_apply (start_chan_proto_spec (sort_fg_protocol <++> END)%proto).
        { iIntros (cy) "Hcy". wp_apply ("IH" with "Hcy"). auto. }
        iIntros (cy) "Hcy".
        wp_apply (start_chan_proto_spec (sort_fg_protocol <++> END)%proto).
        { iIntros (cz) "Hcz". wp_apply ("IH" with "Hcz"); auto. }
        iIntros (cz) "Hcz". rewrite !right_id.
        wp_select. wp_send with "[$HIx1]".
        wp_select. wp_send with "[$HIx2]".
        wp_apply (sort_service_fg_split_spec with "[$Hc $Hcy $Hcz]").
        iIntros (xs' xs1' xs2'); iDestruct 1 as (Hxs') "(Hc & Hcy & Hcz) /=".
        wp_branch as %_ | %[]%Permutation_nil_cons.
        wp_recv (x v) as "[_ HIx]".
        wp_apply (sort_service_fg_merge_spec _ _ _ _ _ _ [] _ _ _ _ [] []
          with "Hcmp [$Hc $Hcy $Hcz $HIx]"); simpl; auto using TlRel_nil, Sorted_nil.
        by rewrite Hxs' Permutation_middle.
      + wp_select. wp_send with "[$HIx1]"; first by auto using TlRel_nil.
        wp_select. by iApply "HΨ".
    - wp_select. by iApply "HΨ".
  Qed.
  
  Lemma send_all_spec c p xs' l xs :
    {{{ llist I l xs ∗ c ↣ (sort_fg_head_protocol xs' <++> p) }}}
      send_all c #l
    {{{ RET #(); llist I l [] ∗ c ↣ (sort_fg_head_protocol (xs' ++ xs) <++> p) }}}.
  Proof.
    iIntros (Φ) "[Hl Hc] HΦ".
    iInduction xs as [|x xs] "IH" forall (xs').
    { wp_lam. wp_apply (lisnil_spec with "Hl"); iIntros "Hl"; wp_pures.
      iApply "HΦ". rewrite right_id_L. iFrame. }
    wp_lam. wp_apply (lisnil_spec with "Hl"); iIntros "Hl". wp_select.
    wp_apply (lpop_spec with "Hl"); iIntros (v) "[HIx Hl]".
    wp_send with "[$HIx]". wp_apply ("IH" with "Hl Hc"). by rewrite -assoc_L.
  Qed.

  Lemma recv_all_spec c p l xs ys' :
    Sorted R ys' →
    {{{ llist I l [] ∗ c ↣ (sort_fg_tail_protocol xs ys' <++> p) }}}
      recv_all c #l
    {{{ ys, RET #();
        ⌜Sorted R (ys' ++ ys)⌝ ∗ ⌜ys' ++ ys ≡ₚ xs⌝ ∗ llist I l ys ∗ c ↣ p
    }}}.
  Proof.
    iIntros (Hsort Φ) "[Hl Hc] HΦ".
    iLöb as "IH" forall (xs ys' Φ Hsort).
    wp_lam. wp_branch as %_ | %Hperm; wp_pures.
    - wp_recv (y v) as (Htl) "HIx".
      wp_apply ("IH" with "[] Hl Hc"); first by auto using Sorted_snoc.
      iIntros (ys). rewrite -!assoc_L. iDestruct 1 as (??) "[Hl Hc]".
      wp_apply (lcons_spec with "[$Hl $HIx]"); iIntros "Hl"; wp_pures.
      iApply ("HΦ" with "[$Hl $Hc]"); simpl; eauto.
    - iApply ("HΦ" $! []); rewrite /= right_id_L; by iFrame.
  Qed.

  Lemma sort_client_fg_spec cmp l xs :
    cmp_spec I R cmp -∗
    {{{ llist I l xs }}}
      sort_client_fg cmp #l
    {{{ ys, RET #(); ⌜Sorted R ys⌝ ∗ ⌜ys ≡ₚ xs⌝ ∗ llist I l ys }}}.
  Proof.
    iIntros "#Hcmp !>" (Φ) "Hl HΦ". wp_lam.
    wp_apply (start_chan_proto_spec (sort_fg_protocol <++> END)%proto);
      iIntros (c) "Hc".
    { wp_apply (sort_service_fg_spec with "Hcmp Hc"); auto. }
    wp_apply (send_all_spec with "[$Hl $Hc]"); iIntros "[Hl Hc]".
    wp_select.
    wp_apply (recv_all_spec with "[$Hl $Hc]"); auto.
    iIntros (ys) "/=". iDestruct 1 as (??) "[Hk _]".
    iApply "HΦ"; auto with iFrame.
  Qed.
  
  End sort_fg_inner.

  Definition sort_fg_func_protocol : iProto Σ :=
    (<!> A (I : A → val → iProp Σ) (R : A → A → Prop)
         `{!RelDecision R, !Total R} (cmp : val),
       MSG cmp {{ cmp_spec I R cmp }};
     sort_fg_head_protocol I R [])%proto.

  Lemma sort_service_fg_func_spec c p :
    {{{ c ↣ (iProto_dual sort_fg_func_protocol <++> p) }}}
      sort_service_fg_func c
    {{{ RET #(); c ↣ p }}}.
  Proof.
    iIntros (Ψ) "Hc HΨ". wp_lam.
    wp_recv (A I R ? ? cmp) as "#Hcmp".
    by wp_apply (sort_service_fg_spec with "Hcmp Hc").
  Qed.
End sort_fg.