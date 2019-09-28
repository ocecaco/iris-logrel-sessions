From iris.heap_lang Require Export lifting metatheory.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode lib.par.
From actris.channel Require Import proto_channel channel proofmode.

Definition prog (c : val) : expr :=
  let: "d1" := new_chan #() in
  let: "d1send" := Fst "d1" in
  let: "d1recv" := Snd "d1" in
  let: "d2" := new_chan #() in
  let: "d2send" := Fst "d2" in
  let: "d2recv" := Snd "d2" in
  (
    let: "x1" := recv c in
    send "d1send" "x1";;
    let: "x2" := recv "d2recv" in
    if: "x1" ≤ "x2" then send "c" "x1" else Skip
  ) ||| (
    let: "x2" := recv c in
    send "d2send" "x2";;
    let: "x1" := recv "d1recv" in
    if: "x2" < "x1" then send "c" "x2" else Skip
  ).

Section Double.
  Context `{heapG Σ, proto_chanG Σ}.

  Definition prog_proto : iProto Σ :=
    (<?> x1 : nat, MSG #x1; <?> x2 : nat, MSG #x2; <!> MSG #(min x1 x2); END)%proto.

  Lemma wp_prog (c : val):
    {{{ c ↣ prog_proto }}} prog c {{{ v, RET v; True }}}.
  Proof.
    iIntros (Φ) "Hc HΦ".
  Admitted.

  (* We need to prove using ghost state that at most two receives will
  be performed in the beginning. Afterwards, we might be able to use
  an agreement RA to have the two processes communicate the value they
  have received and to determine who has the lowest one. Then the
  invariant needs to ensure that only the process with the lowest
  value can access it. *)
End Double.
