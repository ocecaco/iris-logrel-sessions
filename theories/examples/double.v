From iris.heap_lang Require Export lifting metatheory.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode lib.par lib.spin_lock.
From iris.algebra Require Import agree frac csum excl.
From actris.channel Require Import proto_channel channel proofmode.

Definition prog (c : val) : expr :=
  let: "lock" := newlock #() in
  let: "d1" := new_chan #() in
  let: "d1send" := Fst "d1" in
  let: "d1recv" := Snd "d1" in
  let: "d2" := new_chan #() in
  let: "d2send" := Fst "d2" in
  let: "d2recv" := Snd "d2" in
  (
    acquire "lock";;
    let: "x1" := recv c in
    release "lock";;
    send "d1send" "x1";;
    let: "x2" := recv "d2recv" in
    if: "x1" ≤ "x2"
    then acquire "lock";; send "c" "x1";; release "lock"
    else Skip
  ) ||| (
    acquire "lock";;
    let: "x2" := recv c in
    release "lock";;
    send "d2send" "x2";;
    let: "x1" := recv "d1recv" in
    if: "x2" < "x1"
    then acquire "lock";; send "c" "x2";; release "lock"
    else Skip
  ).

Section GhostState.
  (* one-shot RA, slightly modified from iris-examples *)
  Definition oneshotR := csumR (exclR unitO) (agreeR natO).
  Class oneshotG Σ := { oneshot_inG :> inG Σ oneshotR }.
  Definition oneshotΣ : gFunctors := #[GFunctor oneshotR].
  Instance subG_oneshotΣ {Σ} : subG oneshotΣ Σ → oneshotG Σ.
  Proof. solve_inG. Qed.

  Definition pending `{oneshotG Σ} γ := own γ (Cinl (Excl tt)).
  Definition shot `{oneshotG Σ} γ (n : nat) := own γ (Cinr (to_agree n)).

  Lemma new_pending `{oneshotG Σ} : (|==> ∃ γ, pending γ)%I.
  Proof. by apply own_alloc. Qed.

  Lemma shoot `{oneshotG Σ} (n : nat) γ : pending γ ==∗ shot γ n.
  Proof.
    apply own_update.
      by apply cmra_update_exclusive.
  Qed.

  Lemma shot_not_pending `{oneshotG Σ} γ n :
    shot γ n -∗ pending γ -∗ False.
  Proof.
    iIntros "Hs Hp".
    iPoseProof (own_valid_2 with "Hs Hp") as "H".
    iDestruct "H" as %[].
  Qed.

  Lemma shot_agree `{oneshotG Σ} γ (n m : nat) :
    shot γ n -∗ shot γ m -∗ ⌜n = m⌝.
  Proof.
    iIntros "Hs1 Hs2".
    iDestruct (own_valid_2 with "Hs1 Hs2") as %Hfoo.
    iPureIntro. by apply agree_op_invL'.
Qed.
End GhostState.

Section Double.
  Context `{heapG Σ, proto_chanG Σ, oneshotG Σ}.

  Definition proto_begin : iProto Σ :=
    (<?> x1 : nat, MSG #x1; <?> x2 : nat, MSG #x2; <!> MSG #(min x1 x2); END)%proto.

  Definition chan_begin (c : val) (γ1 γ2 : gname) : iProp Σ :=
    (c ↣ proto_begin)%I.
  Definition chan_half1 (c : val) (γ1 γ2 : gname) : iProp Σ :=
    (∃ x1 : nat, shot γ2 x1 ∗ c ↣ <?> x2 : nat, MSG #x2; <!> MSG #(min x1 x2); END)%I.
  Definition chan_half2 (c : val) (γ1 γ2 : gname) : iProp Σ :=
    (∃ x1 : nat, shot γ1 x1 ∗ c ↣ <?> x2 : nat, MSG #x2; <!> MSG #(min x1 x2); END)%I.
  Definition chan_whole (c : val) (γ1 γ2 : gname) : iProp Σ :=
    (∃ x1 x2 : nat, shot γ1 x1 ∗ shot γ2 x2 ∗ c ↣ <!> MSG #(min x1 x2); END)%I.

  Definition chan_inv (c : val) (γ1 γ2 : gname) : iProp Σ :=
    (chan_begin c γ1 γ2 ∨
     chan_half1 c γ1 γ2 ∨
     chan_half2 c γ1 γ2 ∨
     chan_whole c γ1 γ2)%I.

  Lemma wp_prog (N : namespace) (c : val):
    {{{ c ↣ proto_begin }}} prog c {{{ v, RET v; True }}}.
  Proof.
    iIntros (Φ) "Hc HΦ".
    rewrite /prog.

    iMod new_pending as (γ1) "Hγ1".
    iMod new_pending as (γ2) "Hγ2".

    (* Create lock *)
    wp_apply (newlock_spec N (chan_inv c γ1 γ2) with "[Hc]").
    { iLeft. iFrame "Hc". }
    iIntros (lk γ) "#Hlock".
    wp_pures.

    (* Create channel A -> B *)
    wp_apply new_chan_proto_spec.
    { done. }
    iIntros (d1send d1recv) "Hd1".
    iDestruct ("Hd1" $! (<!> x : nat, MSG #x {{ shot γ1 x }}; END)%proto) as ">[Hd1send Hd1recv]".
    wp_pures.

    (* Create channel B -> A *)
    wp_apply new_chan_proto_spec.
    { done. }
    iIntros (d2send d2recv) "Hd2".
    iDestruct ("Hd2" $! (<!> x : nat, MSG #x {{ shot γ2 x }}; END)%proto) as ">[Hd2send Hd2recv]".
    wp_pures.

    (* Fork into two threads *)
    wp_apply (wp_par with "[Hd1send Hd2recv Hγ1]").

    - (* Acquire lock *)
      wp_apply (acquire_spec with "Hlock").
      iIntros "[Hlocked Hc]". wp_pures.
      iDestruct "Hc" as "[Hc|[Hc|[Hc|Hc]]]".
      + wp_apply (recv_proto_spec with "Hc").
        iIntros (n) "Hc _ /=".
        wp_pures.
        iMod (shoot n γ1 with "Hγ1") as "#Hγ1".
        wp_apply (release_spec with "[Hlock Hlocked Hc Hγ1]").
        { iFrame "Hlock Hlocked".
          iRight. iRight. iLeft.
          iExists n. iFrame "Hγ1 Hc". }
        iIntros "_". wp_pures.

        (* Send the value to the other thread *)
        wp_apply (send_proto_spec with "Hd1send").
        iExists n. iSplit=> //. iSplitR=> //.
        iModIntro. iIntros "Hd1send /=". wp_pures.

        (* Receive the other thread's value *)
        wp_apply (recv_proto_spec with "Hd2recv").
        iIntros (m) "Hd2recv #Hγ2 /=". wp_pures.

        case_bool_decide; admit.
      + admit.
      + (* Impossible, since this means our one-shot has already been fired *)
        admit.
      + (* Impossible, since this means our one-shot has already been fired *)
        admit.
    - admit.
  Admitted.

  (* We need to prove using ghost state that at most two receives will
  be performed in the beginning. Afterwards, we might be able to use
  an agreement RA to have the two processes communicate the value they
  have received and to determine who has the lowest one. Then the
  invariant needs to ensure that only the process with the lowest
  value can access it. *)

End Double.
