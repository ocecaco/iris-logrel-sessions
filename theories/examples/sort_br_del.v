From stdpp Require Import sorting.
From actris.channel Require Import proto_channel proofmode.
From iris.heap_lang Require Import proofmode notation.
From actris.examples Require Import sort.

Definition sort_service_br : val :=
  rec: "go" "cmp" "c" :=
    if: ~recv "c" then #() else
    sort_service "cmp" "c";;
    "go" "cmp" "c".

Definition sort_service_del : val :=
  rec: "go" "cmp" "c" :=
    if: ~recv "c" then #() else
    send "c" (start_chan (λ: "c", sort_service "cmp" "c"));;
    "go" "cmp" "c".

Definition sort_service_br_del : val :=
  rec: "go" "cmp" "c" :=
    if: recv "c" then
      sort_service "cmp" "c";;
      "go" "cmp" "c"
    else if: recv "c" then
      send "c" (start_chan (λ: "c", "go" "cmp" "c"));;
      "go" "cmp" "c"
    else #().

Section sort_service_br_del.
  Context `{!heapG Σ, !proto_chanG Σ}.
  Context {A} (I : A → val → iProp Σ) (R : A → A → Prop) `{!RelDecision R, !Total R}.

  Definition sort_protocol_br_aux (rec : iProto Σ) : iProto Σ :=
    ((sort_protocol I R <++> rec) <+> END)%proto.
  Instance sort_protocol_br_aux_contractive : Contractive sort_protocol_br_aux.
  Proof. solve_proto_contractive. Qed.
  Definition sort_protocol_br : iProto Σ := fixpoint sort_protocol_br_aux.
  Global Instance sort_protocol_br_unfold :
    ProtoUnfold sort_protocol_br (sort_protocol_br_aux sort_protocol_br).
  Proof. apply proto_unfold_eq, (fixpoint_unfold sort_protocol_br_aux). Qed.

  Lemma sort_service_br_spec cmp c :
    cmp_spec I R cmp -∗
    {{{ c ↣ iProto_dual sort_protocol_br }}}
      sort_service_br cmp c
    {{{ RET #(); c ↣ END }}}.
  Proof.
    iIntros "#Hcmp !>" (Ψ) "Hc HΨ". iLöb as "IH" forall (c Ψ).
    wp_rec. wp_branch; wp_pures.
    { wp_apply (sort_service_spec with "Hcmp Hc"); iIntros "Hc".
      by wp_apply ("IH" with "Hc"). }
    by iApply "HΨ".
  Qed.

  Definition sort_protocol_del_aux (rec : iProto Σ) : iProto Σ :=
    ((<?> c, MSG c {{ c ↣ sort_protocol I R }}; rec) <+> END)%proto.
  Instance sort_protocol_del_aux_contractive : Contractive sort_protocol_del_aux.
  Proof. solve_proto_contractive. Qed.
  Definition sort_protocol_del : iProto Σ := fixpoint sort_protocol_del_aux.
  Global Instance sort_protocol_del_unfold :
    ProtoUnfold sort_protocol_del (sort_protocol_del_aux sort_protocol_del).
  Proof. apply proto_unfold_eq, (fixpoint_unfold sort_protocol_del_aux). Qed.

  Lemma sort_protocol_del_spec cmp c :
    cmp_spec I R cmp -∗
    {{{ c ↣ iProto_dual sort_protocol_del }}}
      sort_service_del cmp c
    {{{ RET #(); c ↣ END }}}.
  Proof.
    iIntros "#Hcmp !>" (Ψ) "Hc HΨ". iLöb as "IH" forall (Ψ).
    wp_rec. wp_branch; wp_pures.
    { wp_apply (start_chan_proto_spec (sort_protocol I R <++> END)%proto);
        iIntros (c') "Hc'".
      { wp_pures. wp_apply (sort_service_spec with "Hcmp Hc'"); auto. }
      wp_send with "[$Hc']". by wp_apply ("IH" with "Hc"). }
    by iApply "HΨ".
  Qed.

  Definition sort_protocol_br_del_aux (rec : iProto Σ) : iProto Σ :=
    ((sort_protocol I R <++> rec) <+> ((<?> c, MSG c {{ c ↣ rec }}; rec) <+> END))%proto.
  Instance sort_protocol_br_del_aux_contractive : Contractive sort_protocol_br_del_aux.
  Proof. solve_proto_contractive. Qed.
  Definition sort_protocol_br_del : iProto Σ := fixpoint sort_protocol_br_del_aux.
  Global Instance sort_protocol_br_del_unfold :
    ProtoUnfold sort_protocol_br_del (sort_protocol_br_del_aux sort_protocol_br_del).
  Proof. apply proto_unfold_eq, (fixpoint_unfold sort_protocol_br_del_aux). Qed.

  Lemma sort_service_br_del_spec cmp c :
    cmp_spec I R cmp -∗
    {{{ c ↣ iProto_dual sort_protocol_br_del }}}
      sort_service_br_del cmp c
    {{{ RET #(); c ↣ END }}}.
  Proof.
    iIntros "#Hcmp !>" (Ψ) "Hc HΨ". iLöb as "IH" forall (c Ψ).
    wp_rec. wp_branch; wp_pures.
    { wp_apply (sort_service_spec with "Hcmp Hc"); iIntros "Hc".
      by wp_apply ("IH" with "Hc"). }
    wp_branch; wp_pures.
    { wp_apply (start_chan_proto_spec sort_protocol_br_del); iIntros (c') "Hc'".
      { wp_apply ("IH" with "Hc'"); auto. }
      wp_send with "[$Hc']".
      by wp_apply ("IH" with "Hc"). }
    by iApply "HΨ".
  Qed.
End sort_service_br_del.
