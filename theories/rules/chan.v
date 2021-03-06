From logrel_heaplang_sessions Require Export lty ltyping basic arr prod sum chan_proto.
From iris.heap_lang Require Export lifting metatheory.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.
From actris.channel Require Import proto_channel proofmode.

Section types.
  Context `{heapG Σ, proto_chanG Σ}.
  Definition lty_chan (P : lproto Σ) : lty Σ := Lty (λ w, w ↣ P)%I.
End types.

Notation "'chan' A" := (lty_chan A) (at level 10) : lty_scope.

Section properties.
  Context `{heapG Σ, proto_chanG Σ}.

  Global Instance lty_chan_ne : NonExpansive lty_chan.
  Proof. solve_proper. Qed.

  (* TODO: Not sure why I need to put the let here, but otherwise I
  can't get rid of the modality in the premises, becaues I don't have
  a WP as my goal. *)
  Definition chanalloc : val := λ: "u", let: "cc" := new_chan #() in "cc".
  Lemma ltyped_chanalloc P:
    ∅ ⊨ chanalloc : () → (chan P * chan (lproto_dual P)).
  Proof.
    iIntros (vs) "HΓ /=".
    wp_apply wp_value.
    iModIntro. iIntros (u) "Hu".
    rewrite /lty_unit /lty_car.
    rewrite /chanalloc.
    wp_pures.
    iDestruct "Hu" as %Hu.
    wp_apply (new_chan_proto_spec with "[//]").
    iIntros (c1 c2) "Hp".
    iPoseProof ("Hp" $! P) as "Hp".
    iMod "Hp".
    wp_pures.
    iExists c1, c2. iSplit=> //.
    iDestruct "Hp" as "[Hp1 Hp2]".
    iSplitL "Hp1"; by iModIntro.
  Qed.

  Definition chansend : val := λ: "chan" "val", send "chan" "val";; "chan".
  Lemma ltyped_chansend A P:
    ∅ ⊨ chansend : chan (<!!> A; P) → A ⊸ chan P.
  Proof.
    iIntros (vs) "HΓ /=".
    wp_apply wp_value.
    iModIntro. iIntros (c) "Hc".
    rewrite /chansend. wp_pures.
    iIntros (w) "Hw".
    wp_pures.
    rewrite /lty_chan /lty_car /=.
    wp_send with "[$Hw]".
    wp_pures.
    iFrame "Hc".
  Qed.

  Definition chanrecv : val := λ: "chan", (recv "chan", "chan").
  Lemma ltyped_chanrecv A P:
    ∅ ⊨ chanrecv : chan (<??> A; P) → A * chan P.
  Proof.
    iIntros (vs) "HΓ /=".
    wp_apply wp_value.
    iModIntro. iIntros (c) "Hc".
    rewrite /lty_chan /lty_car.
    rewrite /chanrecv. wp_pures.
    wp_recv (v) as "HA". wp_pures.
    iExists v, c. iSplit=> //.
    iFrame "HA Hc".
  Qed.

  Definition chanfst : val := λ: "c", send "c" #true;; "c".
  Lemma ltyped_chanfst P1 P2:
    ∅ ⊨ chanfst : chan (P1 <+++> P2) → chan P1.
  Proof.
    iIntros (vs) "_ /=".
    rewrite /chanfst.
    wp_apply wp_value.
    iModIntro. iIntros (c) "Hc".
    wp_pures.
    wp_select.
    wp_pures.
    iExact "Hc".
  Qed.

  Definition chansnd : val := λ: "c", send "c" #false;; "c".
  Lemma ltyped_chansnd P1 P2:
    ∅ ⊨ chansnd : chan (P1 <+++> P2) → chan P2.
  Proof.
    iIntros (vs) "_ /=".
    rewrite /chansnd.
    wp_apply wp_value.
    iModIntro. iIntros (c) "Hc".
    wp_pures.
    wp_select.
    wp_pures.
    iExact "Hc".
  Qed.

  Definition chanbranch : val := λ: "c",
    let b := recv "c" in if: b then InjL "c" else InjR "c".
  Lemma ltyped_chanbranch P1 P2:
    ∅ ⊨ chanbranch : chan (P1 <&&&> P2) → chan P1 + chan P2.
  Proof.
    iIntros (vs) "_ /=".
    wp_apply wp_value.
    iModIntro. iIntros (c) "Hc".
    rewrite /chanbranch. wp_pures.
    rewrite {1}/lty_chan {1}/lproto_branch {1}/lty_car {1}/lproto_car.
    wp_branch; wp_pures.
    - iLeft. iExists c. iSplit=> //.
    - iRight. iExists c. iSplit=> //.
  Qed.

End properties.
