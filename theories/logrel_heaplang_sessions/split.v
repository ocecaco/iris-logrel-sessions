From iris.heap_lang Require Export lifting metatheory.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.

(* TODO: Should this be an iProp or just a Prop? Is it ever the case that splitting an environment is only allowed when you have some resource? *)
Definition env_split `{heapG Σ} Γ Γ1 Γ2 : iProp Σ := (∀ vs, env_ltyped Γ vs -∗ env_ltyped Γ1 vs ∗ env_ltyped Γ2 vs)%I.

Lemma env_split_empty `{heapG Σ}:
  env_split ∅ ∅ ∅.
Proof.
  iIntros (vs) "H".
  iSplitL; by rewrite /env_ltyped big_sepM_empty.
Qed.

Lemma env_split_left `{heapG Σ} Γ Γ1 Γ2 x A:
  Γ !! x = None → env_split Γ Γ1 Γ2 -∗ env_split (<[x := A]> Γ) (<[x := A]> Γ1) Γ2.
Proof.
  intros HΓx.
  iIntros "Hsplit" (vs) "HΓ".
  iPoseProof (big_sepM_insert with "HΓ") as "[Hv HΓ]"; try assumption.
  iPoseProof ("Hsplit" with "HΓ") as "[HΓ1 HΓ2]". iFrame.
  iApply (big_sepM_insert_2 with "[Hv]"); simpl; iFrame.
Qed.

Lemma env_split_comm `{heapG Σ} Γ Γ1 Γ2:
  env_split Γ Γ1 Γ2 -∗ env_split Γ Γ2 Γ1.
Proof.
  iIntros "Hsplit" (vs) "HΓ".
  iDestruct ("Hsplit" with "HΓ") as "[HΓ1 HΓ2]".
  iFrame.
Qed.

Lemma env_split_right `{heapG Σ} Γ Γ1 Γ2 x A:
  Γ !! x = None → env_split Γ Γ1 Γ2 -∗ env_split (<[x := A]> Γ) Γ1 (<[x := A]> Γ2).
Proof.
  intros HΓx.
  iIntros "Hsplit".
  iApply env_split_comm.
  iApply env_split_left; try assumption.
  by iApply env_split_comm.
Qed.

(* TODO: Get rid of side condition that x does not appear in Γ *)
Lemma env_split_copy `{heapG Σ} Γ Γ1 Γ2 x A:
  Γ !! x = None → LTyCopy A → env_split Γ Γ1 Γ2 -∗ env_split (<[x := A]> Γ) (<[x := A]> Γ1) (<[x := A]> Γ2).
Proof.
  intros Hcopy HΓx. iIntros "Hsplit" (vs) "HΓ".
  iPoseProof (big_sepM_insert with "HΓ") as "[Hv HΓ]"; try assumption.
  (* This next line is possible because of the Persistent instance *)
  iDestruct "Hv" as (v ?) "#HAv".
  iPoseProof ("Hsplit" with "HΓ") as "[HΓ1 HΓ2]".
  iSplitL "HΓ1"; iApply big_sepM_insert_2; simpl; iFrame; eauto.
Qed.
