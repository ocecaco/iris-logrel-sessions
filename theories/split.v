From logrel_heaplang_sessions Require Export lty env.
From iris.heap_lang Require Export lifting metatheory.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.

Section EnvironmentSplitting.
  Context {Σ : gFunctors}.
  Implicit Types A : lty Σ.

  Definition env_split Γ Γ1 Γ2 : Prop :=
    ((∀ vs, env_ltyped Γ vs -∗ env_ltyped Γ1 vs ∗ env_ltyped Γ2 vs)%I : iProp Σ).

  Lemma env_split_empty:
    env_split ∅ ∅ ∅.
  Proof.
    iStartProof. iIntros (vs) "HΓ".
    iSplitL; by rewrite /env_ltyped big_sepM_empty.
  Qed.

  Lemma env_split_left Γ Γ1 Γ2 x A:
    Γ !! x = None →
    env_split Γ Γ1 Γ2 →
    env_split (<[x := A]> Γ) (<[x := A]> Γ1) Γ2.
  Proof.
    intros HΓx Hsplit.
    iStartProof. iIntros (vs) "HΓ".
    iPoseProof (big_sepM_insert with "HΓ") as "[Hv HΓ]"; try assumption.
    iPoseProof (Hsplit with "HΓ") as "[HΓ1 HΓ2]". iFrame.
    iApply (big_sepM_insert_2 with "[Hv]"); simpl; iFrame.
  Qed.

  Lemma env_split_comm Γ Γ1 Γ2:
    env_split Γ Γ1 Γ2 → env_split Γ Γ2 Γ1.
  Proof.
    intros Hsplit. iStartProof. iIntros (vs) "HΓ".
    iDestruct (Hsplit with "HΓ") as "[HΓ1 HΓ2]".
    iFrame.
  Qed.

  Lemma env_split_right Γ Γ1 Γ2 x A:
    Γ !! x = None →
    env_split Γ Γ1 Γ2 →
    env_split (<[x := A]> Γ) Γ1 (<[x := A]> Γ2).
  Proof.
    intros HΓx Hsplit. iStartProof.
    iApply env_split_comm.
    iApply env_split_left; try assumption.
      by iApply env_split_comm.
  Qed.

  (* TODO: Get rid of side condition that x does not appear in Γ *)
  Lemma env_split_copy Γ Γ1 Γ2 (x : string) A:
    Γ !! x = None →
    LTyCopy A →
    env_split Γ Γ1 Γ2 →
    env_split (<[x := A]> Γ) (<[x := A]> Γ1) (<[x := A]> Γ2).
  Proof.
    intros Hcopy HΓx Hsplit. iIntros (vs) "HΓ".
    iPoseProof (big_sepM_insert with "HΓ") as "[Hv HΓ]"; try assumption.
    iDestruct "Hv" as (v ?) "#HAv".
    iPoseProof (Hsplit with "HΓ") as "[HΓ1 HΓ2]".
    iSplitL "HΓ1"; iApply big_sepM_insert_2; simpl; iFrame; eauto.
  Qed.

  (* TODO: Prove lemmas about this *)
  Definition env_copy Γ Γ' : Prop :=
    ((∀ vs, env_ltyped Γ vs -∗ □ env_ltyped Γ' vs) : iProp Σ)%I.
End EnvironmentSplitting.