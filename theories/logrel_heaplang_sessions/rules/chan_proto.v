From iris_examples.logrel_heaplang_sessions Require Export lty.
From iris.heap_lang Require Export lifting metatheory.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From actris.channel Require Import proto_channel proofmode.

Section protocols.
  Context `{heapG Σ, proto_chanG Σ}.

  Definition lproto_end : iProto Σ := END%proto.
  Definition lproto_send (A : lty Σ) (P : iProto Σ) := (<!> v, MSG v {{ A v }}; P)%proto.
  Definition lproto_recv (A : lty Σ) (P : iProto Σ) := (<?> v, MSG v {{ A v }}; P)%proto.

  (* TODO: Prove lemmas about this, showing that it works properly
  with respect to protocols built using send and receive. *)
  Definition lproto_dual (P : iProto Σ) : iProto Σ := iProto_dual P.
End protocols.
