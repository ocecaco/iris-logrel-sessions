From iris.heap_lang Require Export proofmode notation.
From iris.heap_lang Require Import assert.

(** Immutable ML-style functional lists *)
Fixpoint llist `{heapG Σ} {A} (I : A → val → iProp Σ)
    (l : loc) (xs : list A) : iProp Σ :=
  match xs with
  | [] => l ↦ NONEV
  | x :: xs => ∃ (v : val) (l' : loc), I x v ∗ l ↦ SOMEV (v,#l') ∗ llist I l' xs
  end%I.
Arguments llist : simpl never.

Definition lnil : val := λ: <>, ref NONE.
Definition lcons : val := λ: "x" "l", "l" <- SOME ("x", ref (!"l")).

Definition lisnil : val := λ: "l",
  match: !"l" with
    SOME "p" => #false
  | NONE => #true
  end.

Definition lhead : val := λ: "l",
  match: !"l" with
    SOME "p" => Fst "p"
  | NONE => assert: #false
  end.

Definition lpop : val := λ: "l",
  match: !"l" with
    SOME "p" => "l" <- !(Snd "p");; Fst "p"
  | NONE => assert: #false
  end.

Definition llookup : val :=
  rec: "go" "l" "n" :=
    if: "n" = #0 then lhead "l" else
    match: !"l" with
      SOME "p" => "go" (Snd "p") ("n" - #1)
    | NONE => assert: #false
    end.

Definition llength : val :=
  rec: "go" "l" :=
    match: !"l" with
      NONE => #0
    | SOME "p" => #1 + "go" (Snd "p")
    end.

Definition lapp : val :=
  rec: "go" "l" "k" :=
    match: !"l" with
      NONE => "l" <- !"k"
    | SOME "p" => "go" (Snd "p") "k"
    end.
Definition lprep : val := λ: "l" "k",
  lapp "k" "l";; "l" <- !"k".

Definition lsnoc : val :=
  rec: "go" "l" "x" :=
    match: !"l" with
      NONE => "l" <- SOME ("x", ref NONE)
    | SOME "p" => "go" (Snd "p") "x"
    end.

Definition lsplit_at : val :=
  rec: "go" "l" "n" :=
    if: "n" ≤ #0 then let: "k" := ref (! "l") in "l" <- NONE;; "k" else
    match: !"l" with
      NONE => ref NONE
    | SOME "p" => "go" (Snd "p") ("n" - #1)
    end.

Definition lsplit : val := λ: "l", lsplit_at "l" (llength "l" `quot` #2).

Section lists.
Context `{heapG Σ} {A} (I : A → val → iProp Σ).
Implicit Types i : nat.
Implicit Types xs : list A.
Implicit Types l : loc.
Local Arguments llist {_ _ _} _ _ !_ /.

Lemma llist_fmap {B} (J : B → val → iProp Σ) (f : A → B) l xs :
  □ (∀ x v, I x v -∗ J (f x) v) -∗
  llist I l xs -∗ llist J l (f <$> xs).
Proof.
  iIntros "#Hf Hll". iInduction xs as [|x xs] "IH" forall (l); csimpl; auto.
  iDestruct "Hll" as (v l') "(Hx & Hl & Hll)". iExists _, _. iFrame "Hl".
  iSplitL "Hx". by iApply "Hf". by iApply "IH".
Qed.

Lemma lnil_spec :
  {{{ True }}} lnil #() {{{ l, RET #l; llist I l [] }}}.
Proof. iIntros (Φ _) "HΦ". wp_lam. wp_alloc l. by iApply "HΦ". Qed.

Lemma lcons_spec l x xs v :
  {{{ llist I l xs ∗ I x v }}} lcons v #l {{{ RET #(); llist I l (x :: xs) }}}.
Proof.
  iIntros (Φ) "[Hll Hx] HΦ". wp_lam. destruct xs as [|x' xs]; simpl; wp_pures.
  - wp_load. wp_alloc k. wp_store. iApply "HΦ"; eauto with iFrame.
  - iDestruct "Hll" as (v' l') "(HIx' & Hl & Hll)".
    wp_load. wp_alloc k. wp_store. iApply "HΦ"; eauto 10 with iFrame.
Qed.

Lemma lisnil_spec l xs:
  {{{ llist I l xs }}}
    lisnil #l
  {{{ RET #(if xs is [] then true else false); llist I l xs }}}.
Proof.
  iIntros (Φ) "Hll HΦ". wp_lam. destruct xs as [|x xs]; simpl; wp_pures.
  - wp_load; wp_pures. by iApply "HΦ".
  - iDestruct "Hll" as (v l') "(HIx & Hl & Hll)".
    wp_load; wp_pures. iApply "HΦ"; eauto with iFrame.
Qed.

(** Not the nicest spec, they leaks *)
Lemma lhead_spec_aux l x xs :
  {{{ llist I l (x :: xs) }}}
    lhead #l
  {{{ v (l' : loc), RET v; I x v ∗ l ↦ SOMEV (v,#l') ∗ llist I l' xs }}}.
Proof.
  iIntros (Φ) "/=". iDestruct 1 as (v l') "(HIx & Hl & Hll)". iIntros "HΦ".
  wp_lam. wp_load; wp_pures. iApply "HΦ"; eauto with iFrame.
Qed.
Lemma lpop_spec_aux l l' v xs :
  {{{ l ↦ SOMEV (v,#l') ∗ llist I l' xs }}} lpop #l {{{ RET v; llist I l xs }}}.
Proof.
  iIntros (Φ) "[Hl Hll] HΦ".
  wp_lam. wp_load. wp_pures. destruct xs as [|x' xs]; simpl; wp_pures.
  - wp_load. wp_store. wp_pures. iApply "HΦ"; eauto with iFrame.
  - iDestruct "Hll" as (v' l'') "(HIx' & Hl' & Hll)".
    wp_load. wp_store. wp_pures. iApply "HΦ"; eauto with iFrame.
Qed.

Lemma lhead_spec l x xs :
  {{{ llist I l (x :: xs) }}}
    lhead #l
  {{{ v, RET v; I x v ∗ (I x v -∗ llist I l (x :: xs)) }}}.
Proof.
  iIntros (Φ) "Hll HΦ". wp_apply (lhead_spec_aux with "Hll").
  iIntros (v l') "(HIx&?&?)". iApply "HΦ". iIntros "{$HIx} HIx".
  simpl; eauto with iFrame.
Qed.

Lemma lpop_spec l x xs :
  {{{ llist I l (x :: xs) }}} lpop #l {{{ v, RET v; I x v ∗ llist I l xs }}}.
Proof.
  iIntros (Φ) "/=". iDestruct 1 as (v l') "(HIx & Hl & Hll)". iIntros "HΦ".
  wp_apply (lpop_spec_aux with "[$]"); iIntros "Hll". iApply "HΦ"; iFrame.
Qed.

Lemma llookup_spec l i xs x :
  xs !! i = Some x →
  {{{ llist I l xs }}}
    llookup #l #i
  {{{ v, RET v; I x v ∗ (I x v -∗ llist I l xs) }}}.
Proof.
  iIntros (Hi Φ) "Hll HΦ".
  iInduction xs as [|x' xs] "IH" forall (l i x Hi Φ); [done|simpl; wp_rec; wp_pures].
  destruct i as [|i]; simplify_eq/=; wp_pures.
  - wp_apply (lhead_spec with "Hll"); iIntros (v) "[HI Hll]".
    iApply "HΦ"; eauto with iFrame.
  - iDestruct "Hll" as (v l') "(HIx' & Hl' & Hll)". wp_load; wp_pures.
    rewrite Nat2Z.inj_succ Z.sub_1_r Z.pred_succ.
    wp_apply ("IH" with "[//] Hll"); iIntros (v') "[HIx Hll]".
    iApply "HΦ". iIntros "{$HIx} HIx". iExists v, l'. iFrame. by iApply "Hll".
Qed.

Lemma llength_spec l xs :
  {{{ llist I l xs }}} llength #l {{{ RET #(length xs); llist I l xs }}}.
Proof.
  iIntros (Φ) "Hll HΦ".
  iInduction xs as [|x xs] "IH" forall (l Φ); simpl; wp_rec; wp_pures.
  - wp_load; wp_pures. by iApply "HΦ".
  - iDestruct "Hll" as (v l') "(HIx & Hl' & Hll)". wp_load; wp_pures.
    wp_apply ("IH" with "Hll"); iIntros "Hll". wp_pures.
    rewrite (Nat2Z.inj_add 1). iApply "HΦ"; eauto with iFrame.
Qed.

Lemma lapp_spec l1 l2 xs1 xs2 :
  {{{ llist I l1 xs1 ∗ llist I l2 xs2 }}}
    lapp #l1 #l2
  {{{ RET #(); llist I l1 (xs1 ++ xs2) ∗ l2 ↦ - }}}.
Proof.
  iIntros (Φ) "[Hll1 Hll2] HΦ".
  iInduction xs1 as [|x1 xs1] "IH" forall (l1 Φ); simpl; wp_rec; wp_pures.
  - wp_load. wp_pures. destruct xs2 as [|x2 xs2]; simpl; wp_pures.
    + wp_load. wp_store. iApply "HΦ". eauto with iFrame.
    + iDestruct "Hll2" as (v2 l2') "(HIx2 & Hl2 & Hll2)". wp_load. wp_store.
      iApply "HΦ". iSplitR "Hl2"; eauto 10 with iFrame.
  - iDestruct "Hll1" as (v1 l') "(HIx1 & Hl1 & Hll1)". wp_load; wp_pures.
    wp_apply ("IH" with "Hll1 Hll2"); iIntros "[Hll Hl2]".
    iApply "HΦ"; eauto with iFrame.
Qed.

Lemma lprep_spec l1 l2 xs1 xs2 :
  {{{ llist I l1 xs2 ∗ llist I l2 xs1 }}}
    lprep #l1 #l2
  {{{ RET #(); llist I l1 (xs1 ++ xs2) ∗ l2 ↦ - }}}.
Proof.
  iIntros (Φ) "[Hll1 Hll2] HΦ". wp_lam.
  wp_apply (lapp_spec with "[$Hll2 $Hll1]"); iIntros "[Hll2 Hl1]".
  iDestruct "Hl1" as (w) "Hl1". destruct (xs1 ++ xs2) as [|x xs]; simpl; wp_pures.
  - wp_load. wp_store. iApply "HΦ"; eauto with iFrame.
  - iDestruct "Hll2" as (v l') "(HIx & Hl2 & Hll2)". wp_load. wp_store.
    iApply "HΦ"; iSplitR "Hl2"; eauto with iFrame.
Qed.

Lemma lsnoc_spec l xs x v :
  {{{ llist I l xs ∗ I x v }}} lsnoc #l v {{{ RET #(); llist I l (xs ++ [x]) }}}.
Proof.
  iIntros (Φ) "[Hll HIx] HΦ".
  iInduction xs as [|x' xs] "IH" forall (l Φ); simpl; wp_rec; wp_pures.
  - wp_load. wp_alloc k. wp_store. iApply "HΦ"; eauto with iFrame.
  - iDestruct "Hll" as (v' l') "(HIx' & Hl & Hll)". wp_load; wp_pures.
    wp_apply ("IH" with "Hll HIx"); iIntros "Hll". iApply "HΦ"; eauto with iFrame.
Qed.

Lemma lsplit_at_spec l xs (n : nat) :
  {{{ llist I l xs }}}
    lsplit_at #l #n
  {{{ k, RET #k; llist I l (take n xs) ∗ llist I k (drop n xs) }}}.
Proof.
  iIntros (Φ) "Hll HΦ".
  iInduction xs as [|x xs] "IH" forall (l n Φ); simpl; wp_rec; wp_pures.
  - destruct n as [|n]; simpl; wp_pures.
    + wp_load. wp_alloc k. wp_store. iApply "HΦ"; iFrame.
    + wp_load. wp_alloc k. iApply "HΦ"; iFrame.
  - iDestruct "Hll" as (v l') "(HIx & Hl & Hll)". destruct n as [|n]; simpl; wp_pures.
    + wp_load. wp_alloc k. wp_store. iApply "HΦ"; eauto with iFrame.
    + wp_load; wp_pures. rewrite Nat2Z.inj_succ Z.sub_1_r Z.pred_succ.
      wp_apply ("IH" with "[$]"); iIntros (k) "[Hll Hlk]".
      iApply "HΦ"; eauto with iFrame.
Qed.

Lemma lsplit_spec l xs :
  {{{ llist I l xs }}}
    lsplit #l
  {{{ k xs1 xs2, RET #k; ⌜ xs = xs1 ++ xs2 ⌝ ∗ llist I l xs1 ∗ llist I k xs2 }}}.
Proof.
  iIntros (Φ) "Hl HΦ". wp_lam.
  wp_apply (llength_spec with "Hl"); iIntros "Hl". wp_pures.
  rewrite Z.quot_div_nonneg; [|lia..]. rewrite -(Z2Nat_inj_div _ 2).
  wp_apply (lsplit_at_spec with "Hl"); iIntros (k) "[Hl Hk]".
  iApply "HΦ". iFrame. by rewrite take_drop.
Qed.
End lists.
