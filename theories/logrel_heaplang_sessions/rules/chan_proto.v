From iris_examples.logrel_heaplang_sessions Require Export lty.
From iris.heap_lang Require Export lifting metatheory.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From actris.channel Require Import proto_channel proofmode.

Record lproto Σ := Lproto {
  lproto_car :> iProto Σ;
}.
Arguments Lproto {_} _%proto.
(* I actually don't know what this next line means *)
Arguments lty_car {_} _ _ : simpl never.
Bind Scope lproto_scope with lproto.
Delimit Scope lproto_scope with lproto.

Section protocols.
  Context `{heapG Σ, proto_chanG Σ}.

  Definition lproto_end : lproto Σ := Lproto END.
  Definition lproto_send (A : lty Σ) (P : lproto Σ) :=
    Lproto (<!> v, MSG v {{ A v }}; (P : iProto _))%proto.
  Definition lproto_recv (A : lty Σ) (P : lproto Σ) :=
    Lproto (<?> v, MSG v {{ A v }}; (P : iProto _))%proto.

  (* TODO: Prove lemmas about this, showing that it works properly
  with respect to protocols built using send and receive. *)
  Definition lproto_dual (P : lproto Σ) : lproto Σ := Lproto (iProto_dual (P : iProto _)).
End protocols.

Notation "'END'" := (lproto_end) : lproto_scope.
Notation "<!!> A ; P" := (lproto_send A P) (at level 20, A, P at level 200) : lproto_scope.
Notation "<??> A ; P" := (lproto_recv A P) (at level 20, A, P at level 200) : lproto_scope.
