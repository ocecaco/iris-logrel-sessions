From actris.channel Require Import proto_channel proofmode.
From iris.heap_lang Require Import proofmode notation lib.spin_lock.
From actris.utils Require Import contribution.

Definition prog1 : val := λ: <>,
  let: "c" := start_chan (λ: "c'", send "c'" #42) in
  recv "c".

Definition prog2 : val := λ: <>,
  let: "c" := start_chan (λ: "c'", send "c'" (ref #42)) in
  ! (recv "c").

Definition prog3 : val := λ: <>,
  let: "c1" := start_chan (λ: "c1'",
    let: "cc2" := new_chan #() in
    send "c1'" (Fst "cc2");;
    send (Snd "cc2") #42) in
  recv (recv "c1").

Definition prog4 : val := λ: <>,
  let: "c" := start_chan (λ: "c'",
    let: "x" := recv "c'" in send "c'" ("x" + #2)) in
  send "c" #40;;
  recv "c".

Definition prog5 : val := λ: <>,
  let: "c" := start_chan (λ: "c'",
    let: "f" := recv "c'" in send "c'" (λ: <>, "f" #() + #2)) in
  let: "r" := ref #40 in
  send "c" (λ: <>, !"r");;
  recv "c" #().

Definition prog_lock : val := λ: <>,
  let: "c" := start_chan (λ: "c'",
    let: "l" := newlock #() in
    Fork (acquire "l";; send "c'" #21;; release "l");;
    acquire "l";; send "c'" #21;; release "l") in
  recv "c" + recv "c".

Section proofs.
Context `{heapG Σ, proto_chanG Σ}.

Definition prot1 : iProto Σ :=
  (<?> MSG #42; END)%proto.

Definition prot2 : iProto Σ :=
  (<?> l : loc, MSG #l {{ l ↦ #42 }}; END)%proto.

Definition prot3 : iProto Σ :=
  (<?> c : val, MSG c {{ c ↣ prot1 }}; END)%proto.

Definition prot4 : iProto Σ :=
  (<!> x : Z, MSG #x; <?> MSG #(x + 2); END)%proto.

Definition prot5 : iProto Σ :=
  (<!> (P : iProp Σ) (Φ : Z → iProp Σ) (vf : val),
     MSG vf {{ {{{ P }}} vf #() {{{ x, RET #x; Φ x }}} }};
   <?> (vg : val),
     MSG vg {{ {{{ P }}} vg #() {{{ x, RET #(x + 2); Φ x }}} }};
   END)%proto.

Fixpoint prot_lock (n : nat) : iProto Σ :=
  match n with
  | 0 => END
  | S n' => <?> MSG #21; prot_lock n'
  end%proto.

Lemma prog1_spec : {{{ True }}} prog1 #() {{{ RET #42; True }}}.
Proof.
  iIntros (Φ) "_ HΦ". wp_lam.
  wp_apply (start_chan_proto_spec prot1); iIntros (c) "Hc".
  - by wp_send with "[]".
  - wp_recv as "_". by iApply "HΦ".
Qed.

Lemma prog2_spec : {{{ True }}} prog2 #() {{{ RET #42; True }}}.
Proof.
  iIntros (Φ) "_ HΦ". wp_lam.
  wp_apply (start_chan_proto_spec prot2); iIntros (c) "Hc".
  - wp_alloc l as "Hl". by wp_send with "[$Hl]".
  - wp_recv (l) as "Hl". wp_load. by iApply "HΦ".
Qed.

Lemma prog3_spec : {{{ True }}} prog3 #() {{{ RET #42; True }}}.
Proof.
  iIntros (Φ) "_ HΦ". wp_lam.
  wp_apply (start_chan_proto_spec prot3); iIntros (c) "Hc".
  - wp_apply (new_chan_proto_spec with "[//]").
    iIntros (c2 c2') "Hcc2". iMod ("Hcc2" $! prot1) as "[Hc2 Hc2']".
    wp_send with "[$Hc2]". by wp_send with "[]".
  - wp_recv (c2) as "Hc2". wp_recv as "_". by iApply "HΦ".
Qed.

Lemma prog4_spec : {{{ True }}} prog4 #() {{{ RET #42; True }}}.
Proof.
  iIntros (Φ) "_ HΦ". wp_lam.
  wp_apply (start_chan_proto_spec prot4); iIntros (c) "Hc".
  - wp_recv (x) as "_". by wp_send with "[]".
  - wp_send with "[//]". wp_recv as "_". by iApply "HΦ".
Qed.

Lemma prog5_spec : {{{ True }}} prog5 #() {{{ RET #42; True }}}.
Proof.
  iIntros (Φ) "_ HΦ". wp_lam.
  wp_apply (start_chan_proto_spec prot5); iIntros (c) "Hc".
  - wp_recv (P Ψ vf) as "#Hf". wp_send with "[]"; last done.
    iIntros "!>" (Ψ') "HP HΨ'". wp_apply ("Hf" with "HP"); iIntros (x) "HΨ".
    wp_pures. by iApply "HΨ'".
  - wp_alloc l as "Hl".
    wp_send ((l ↦ #40)%I (λ w, ⌜ w = 40%Z ⌝ ∗ l ↦ #40)%I) with "[]".
    { iIntros "!>" (Ψ') "Hl HΨ'". wp_load. iApply "HΨ'"; auto. }
    wp_recv (vg) as "#Hg". wp_apply ("Hg" with "Hl"); iIntros (x) "[-> Hl]".
    by iApply "HΦ".
Qed.

Lemma prog_lock_spec `{!lockG Σ, contributionG Σ unitUR} :
  {{{ True }}} prog_lock #() {{{ RET #42; True }}}.
Proof.
  iIntros (Φ) "_ HΦ". wp_lam.
  wp_apply (start_chan_proto_spec (prot_lock 2)); iIntros (c) "Hc".
  - iMod (contribution_init) as (γ) "Hs".
    iMod (alloc_client with "Hs") as "[Hs Hcl1]".
    iMod (alloc_client with "Hs") as "[Hs Hcl2]".
    wp_apply (newlock_spec nroot (∃ n, server γ n ε ∗
      c ↣ iProto_dual (prot_lock n))%I
      with "[Hc Hs]"); first by eauto with iFrame.
    iIntros (lk γlk) "#Hlk".
    iAssert (□ (client γ ε -∗
      WP acquire lk;; send c #21;; release lk {{ _, True }}))%I as "#Hhelp".
    { iIntros "!> Hcl".
      wp_apply (acquire_spec with "[$]"); iIntros "[Hl H]".
      iDestruct "H" as (n) "[Hs Hc]".
      iDestruct (server_agree with "Hs Hcl") as %[? _].
      destruct n as [|n]=> //=. wp_send with "[//]".
      iMod (dealloc_client with "Hs Hcl") as "Hs /=".
      wp_apply (release_spec with "[$Hlk $Hl Hc Hs]"); eauto with iFrame. }
    wp_apply (wp_fork with "[Hcl1]").
    { iNext. by iApply "Hhelp". }
    by wp_apply "Hhelp".
  - wp_recv as "_". wp_recv as "_". wp_pures. by iApply "HΦ".
Qed.
End proofs.
