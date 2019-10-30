From logrel_heaplang_sessions Require Export lty ltyping basic copy any arr sum prod ref weakref rec existential universal mutex chan chan_proto.
From iris.heap_lang Require Export lifting metatheory.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From iris.heap_lang.lib Require Import spin_lock.
From actris.channel Require Import proto_channel proofmode.

(* Contractiveness of arrow *)
Section Tests.
  Context `{heapG Σ, lockG Σ, proto_chanG Σ}.

  (* arrow is contractive in both arguments *)
  Definition arr_rec (X : lty Σ) : lty Σ := X → X.
  Instance arr_rec_contractive : Contractive arr_rec.
  Proof. solve_contractive. Qed.
  Definition lty_arr_rec : lty Σ := lty_rec arr_rec.
  (* Identity function belongs to μX.X → X *)
  Lemma lty_arr_rec_id:
    (∅ ⊨ (λ: "x", "x")%V : lty_arr_rec).
  Proof.
    iIntros (vs) "_ /=".
    wp_apply wp_value.
    rewrite /lty_arr_rec lty_rec_unfold /arr_rec.
    iModIntro. iIntros (w) "Hw".
    wp_pures. iApply "Hw".
  Qed.

  (* sum is contractive *)
  Definition sum_rec (X : lty Σ) : lty Σ := (X + X)%lty.
  Instance sum_rec_contractive : Contractive sum_rec.
  Proof. solve_contractive. Qed.
  Definition lty_sum_rec : lty Σ := lty_rec sum_rec.

  (* product is contractive *)
  Definition prod_rec (X : lty Σ) : lty Σ := (X * X)%lty.
  Instance prod_rec_contractive : Contractive prod_rec.
  Proof. solve_contractive. Qed.
  Definition lty_prod_rec : lty Σ := lty_rec prod_rec.

  (* ref is contractive *)
  Definition lty_ref_rec : lty Σ := lty_rec lty_ref.

  (* weakref is contractive *)
  Definition lty_weakref_rec : lty Σ := lty_rec lty_weakref.

  (* existential is contractive *)
  Definition exist_rec (X : lty Σ) := (∃ Y, X)%lty.
  Instance exist_rec_contractive : Contractive exist_rec.
  Proof. solve_contractive. Qed.
  Definition lty_exist_rec : lty Σ := lty_rec exist_rec.

  (* universal is contractive *)
  (* Definition forall_rec (X : lty Σ) := (∀ Y, X)%lty. *)
  (* Instance forall_rec_contractive : Contractive forall_rec. *)
  (* Proof. solve_contractive. Qed. *)
  (* Definition lty_forall_rec : lty Σ := lty_rec forall_rec. *)

  (* mutex is contractive *)
  Definition lty_mutex_rec : lty Σ := lty_rec lty_mutex.
  Definition lty_mutexguard_rec : lty Σ := lty_rec lty_mutexguard.

  (* recursive channels *)
  Definition chan_rec (X : lty Σ) := lty_chan (<??> X; END).
  Instance chan_rec_contractive : Contractive chan_rec.
  Proof. solve_contractive. Qed.
  Definition lty_chan_rec : lty Σ := lty_rec chan_rec.

End Tests.
