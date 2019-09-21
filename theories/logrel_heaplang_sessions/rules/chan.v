From actris.channel Require Import proto_channel proofmode.

  (* TODO: Maybe don't use iProto directly, but wrap it in a
  record. *)
  Definition lty_chan (P : iProto Σ) : lty Σ := Lty (λ w, w ↣ P)%I.

  Definition lproto_end : iProto Σ := END%proto.
  Definition lproto_send (A : lty Σ) (P : iProto Σ) := (<!> v, MSG v {{ A v }}; P)%proto.
  Definition lproto_recv (A : lty Σ) (P : iProto Σ) := (<?> v, MSG v {{ A v }}; P)%proto.

  (* TODO: Prove lemmas about this, showing that it works properly
  with respect to send and receive. *)
  Definition lproto_dual (P : iProto Σ) : iProto Σ := iProto_dual P.

Notation "'chan' A" := (lty_chan A) (at level 10) : lty_scope.

  (* TODO: Not sure why I need to put the let here, but otherwise I
  can't get rid of the modality in the premises, becaues I don't have
  a WP as my goal. *)
  Definition chanalloc : val := λ: "u", let: "cc" := new_chan #() in "cc".
  Lemma ltyped_chanalloc Γ P:
    Γ ⊨ chanalloc : () → (chan P * chan (lproto_dual P)).
  Proof.
    iIntros (vs) "HΓ /=".
    wp_apply wp_value.
    iIntros (u) "Hu".
    rewrite /lty_unit /lty_car.
    iDestruct "Hu" as %Hu.
    rewrite Hu.
    rewrite /chanalloc.
    wp_pures.
    wp_apply (new_chan_proto_spec with "[//]").
    iIntros (c1 c2) "Hp".
    iPoseProof ("Hp" $! P) as "Hp".
    iMod "Hp".
    wp_pures.
    iExists c1, c2. iSplit=> //.
  Qed.

  Definition chansend : val := λ: "chan" "val", send "chan" "val";; "chan".
  Lemma ltyped_chansend Γ A P:
    Γ ⊨ chansend : chan (lproto_send A P) → A → chan P.
  Proof.
    iIntros (vs) "HΓ /=".
    wp_apply wp_value.
    iIntros (c) "Hc".
    rewrite /chansend. wp_pures.
    iIntros (w) "Hw".
    wp_pures.
    rewrite /lty_chan /lty_car /=.
    wp_apply (send_proto_spec with "Hc").
    iExists w. simpl. iSplit=> //.
    iFrame "Hw".
    iModIntro.
    iIntros "Hc".
    wp_pures.
    iFrame "Hc".
  Qed.

  Definition chanrecv : val := λ: "chan", (recv "chan", "chan").
  Lemma ltyped_chanrecv Γ A P:
    Γ ⊨ chanrecv : chan (lproto_recv A P) → A * chan P.
  Proof.
    iIntros (vs) "HΓ /=".
    wp_apply wp_value.
    iIntros (c) "Hc".
    rewrite /lty_chan /lty_car.
    rewrite /chanrecv. wp_pures.
    wp_apply (recv_proto_spec with "Hc").
    iIntros (v) "Hc HA". simpl. wp_pures.
    iExists v, c. iSplit=> //.
    iFrame "HA Hc".
  Qed.
