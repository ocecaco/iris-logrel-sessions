From logrel_heaplang_sessions Require Export lty.
From iris.heap_lang Require Export lifting metatheory.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From actris.channel Require Import proto_channel proofmode.

Record lproto Σ := Lproto {
  lproto_car :> iProto Σ;
}.
Arguments Lproto {_} _%proto.
Arguments lproto_car {_} _ : simpl never.
Bind Scope lproto_scope with lproto.
Delimit Scope lproto_scope with lproto.

Section lproto_ofe.
  Context `{Σ : gFunctors}.

  Instance lproto_equiv : Equiv (lproto Σ) := λ P Q, (P : iProto _) ≡ (Q : iProto _).
  Instance lproto_dist : Dist (lproto Σ) := λ n P Q, (P : iProto _) ≡{n}≡ (Q : iProto _).

  Lemma lproto_ofe_mixin : OfeMixin (lproto Σ).
  Proof. by apply (iso_ofe_mixin (lproto_car : _ → iProto _)). Qed.
  Canonical Structure lprotoC := OfeT (lproto Σ) lproto_ofe_mixin.

  Global Instance lproto_cofe : Cofe lprotoC.
  Proof. by apply (iso_cofe (@Lproto _ : _ → lprotoC) lproto_car). Qed.

  Global Instance lproto_inhabited : Inhabited (lproto Σ) := populate (Lproto inhabitant).

  Global Instance lproto_car_ne : NonExpansive lproto_car.
  Proof. intros n A A' H. exact H. Qed.

  Global Instance lproto_car_proper : Proper ((≡) ==> (≡)) lproto_car.
  Proof. intros A A' H. exact H. Qed.
End lproto_ofe.

Arguments lprotoC : clear implicits.

Section protocols.
  Context `{heapG Σ, proto_chanG Σ}.

  Definition lproto_end : lproto Σ := Lproto END.

  Definition lproto_send (A : lty Σ) (P : lproto Σ) :=
    Lproto (<!> v, MSG v {{ A v }}; (P : iProto _))%proto.
  Definition lproto_recv (A : lty Σ) (P : lproto Σ) :=
    Lproto (<?> v, MSG v {{ A v }}; (P : iProto _))%proto.

  Definition lproto_branch (P1 P2 : lproto Σ) :=
    Lproto ((P1 : iProto _) <&> (P2 : iProto _))%proto.
  Definition lproto_select (P1 P2 : lproto Σ) :=
    Lproto ((P1 : iProto _) <+> (P2 : iProto _))%proto.

  Definition lproto_rec1 (C : lprotoC Σ → lprotoC Σ)
             `{!Contractive C}
             (rec : lproto Σ) : lproto Σ :=
    Lproto (C rec).

  Instance lproto_rec1_contractive C `{!Contractive C} : Contractive (lproto_rec1 C).
  Proof. Admitted.

  Definition lproto_rec (C : lprotoC Σ → lprotoC Σ) `{!Contractive C} : lproto Σ :=
    fixpoint (lproto_rec1 C).

  (* TODO: Prove lemmas about this, showing that it works properly
  with respect to protocols built using send and receive. *)
  Definition lproto_dual (P : lproto Σ) : lproto Σ := Lproto (iProto_dual (P : iProto _)).
End protocols.

Notation "'END'" := (lproto_end) : lproto_scope.
Notation "<!!> A ; P" := (lproto_send A P) (at level 20, A, P at level 200) : lproto_scope.
Notation "<??> A ; P" := (lproto_recv A P) (at level 20, A, P at level 200) : lproto_scope.
Infix "<+++>" := (lproto_select) (at level 60) : lproto_scope.
Infix "<&&&>" := (lproto_branch) (at level 85) : lproto_scope.
