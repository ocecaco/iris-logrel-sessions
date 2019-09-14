From actris.channel Require Import proto_channel proofmode.
From iris.heap_lang Require Import proofmode notation.
From actris.utils Require Import llist compare contribution group.
From actris.examples Require Import map sort_fg.
From iris.algebra Require Import gmultiset.

(** Functional version of map reduce (aka the specification) *)
Definition map_reduce {A B C} `{EqDecision K}
    (map : A → list (K * B)) (red : K → list B → list C) : list A → list C :=
  mbind (curry red) ∘ group ∘ mbind map.
Instance: Params (@map_reduce) 7.

(** Distributed version *)
Definition par_map_reduce_map : val :=
  rec: "go" "n" "cmap" "csort" "xs" :=
    if: "n" = #0 then #() else
    if: recv "cmap" then (* send item to mapper *)
      if: lisnil "xs" then
        send "cmap" #false;;
        "go" ("n" - #1) "cmap" "csort" "xs"
      else
        send "cmap" #true;;
        send "cmap" (lpop "xs");;
        "go" "n" "cmap" "csort" "xs"
    else (* receive item from mapper *)
      let: "zs" := recv "cmap" in
      send_all "csort" "zs";;
      "go" "n" "cmap" "csort" "xs".

Definition par_map_reduce_collect : val :=
  rec: "go" "csort" "i" "ys" :=
    if: ~recv "csort" then NONE else
    let: "jy" := recv "csort" in
    let: "j" := Fst "jy" in let: "y" := Snd "jy" in
    if: "i" = "j" then lcons "y" "ys";; "go" "csort" "j" "ys" else
    SOME ("j", "y").

Definition par_map_reduce_reduce : val :=
  rec: "go" "n" "csort" "cred" "acc" "zs" :=
    if: "n" = #0 then #() else
    if: recv "cred" then (* Send item to mapper *)
      match: "acc" with
        NONE =>
         (* nothing left *)
         send "cred" #false;; "go" ("n" - #1) "csort" "cred" NONE "zs"
      | SOME "acc" =>
         (* Read subsequent items with the same key *)
         let: "ys" := lnil #() in lcons (Snd "acc") "ys";;
         let: "new_acc" := par_map_reduce_collect "csort" (Fst "acc") "ys" in
         send "cred" #true;;
         send "cred" (Fst "acc", "ys");;
         "go" "n" "csort" "cred" "new_acc" "zs"
      end
    else (* receive item from mapper *)
      let: "zs'" := recv "cred" in
      lprep "zs" "zs'";;
      "go" "n" "csort" "cred" "acc" "zs".

Definition cmpZfst : val := λ: "x" "y", Fst "x" ≤ Fst "y".

Definition par_map_reduce : val := λ: "n" "m" "map" "red" "xs",
  let: "cmap" := start_chan (λ: "c", par_map_service "n" "map" "c") in
  let: "csort" := start_chan (λ: "c", sort_service_fg cmpZfst "c") in
  par_map_reduce_map "n" "cmap" "csort" "xs";;
  send "csort" #stop;;
  let: "cred" := start_chan (λ: "c", par_map_service "m" "red" "c") in
  (* We need the first sorted element in the loop to compare subsequent elements *)
  if: ~recv "csort" then #() else (* Handle the empty case *)
  let: "jy" := recv "csort" in
  par_map_reduce_reduce "m" "csort" "cred" (SOME "jy") "xs".


(** Properties about the functional version *)
Section map_reduce.
  Context {A B C} `{EqDecision K} (map : A → list (K * B)) (red : K → list B → list C).
  Context `{!∀ j, Proper ((≡ₚ) ==> (≡ₚ)) (red j)}.

  Global Instance bind_red_perm : Proper ((≡ₚₚ) ==> (≡ₚ)) (mbind (curry red)).
  Proof.
    induction 1 as [|[i1 xs1] [i2 xs2] ixss1 ixss2 [??]|[i1 xs1] [i2 xs2] ixss|];
      simplify_eq/=; try done.
    - repeat (done || f_equiv).
    - by rewrite !assoc_L (comm _ (red i2 xs2)).
    - by etrans.
  Qed.
  Global Instance map_reduce_perm : Proper ((≡ₚ) ==> (≡ₚ)) (map_reduce map red).
  Proof. intros xs1 xs2 Hxs. by rewrite /map_reduce /= Hxs. Qed.
End map_reduce.

(** Correctness proofs of the distributed version *)
Class map_reduceG Σ A B `{Countable A, Countable B} := {
  map_reduce_mapG :> mapG Σ A;
  map_reduce_reduceG :> mapG Σ (Z * list B);
}.

Section mapper.
  Context `{Countable A, Countable B} {C : Type}.
  Context `{!heapG Σ, !proto_chanG Σ, !map_reduceG Σ A B}.
  Context (IA : A → val → iProp Σ) (IB : Z → B → val → iProp Σ) (IC : C → val → iProp Σ).
  Context (map : A → list (Z * B)) (red : Z → list B → list C).
  Context `{!∀ j, Proper ((≡ₚ) ==> (≡ₚ)) (red j)}.
  Local Open Scope nat_scope.
  Implicit Types n : nat.

  Definition IZB (iy : Z * B) (w : val) : iProp Σ :=
    (∃ w', ⌜ w = (#iy.1, w')%V ⌝ ∧ IB iy.1 iy.2 w')%I.
  Definition IZBs (iys : Z * list B) (w : val) : iProp Σ :=
    (∃ (l : loc), ⌜ w = (#iys.1, #l)%V ⌝ ∗ llist (IB iys.1) l (iys.2))%I.
  Definition RZB : relation (Z * B) := prod_relation (≤)%Z (λ _ _ : B, True).

  Instance RZB_dec : RelDecision RZB.
  Proof. solve_decision. Qed.
  Instance RZB_total : Total RZB.
  Proof. intros [i1 y1] [i2 y2]. destruct (total (≤)%Z i1 i2); [left|right]; done. Qed.
  Instance RZB_trans : Transitive RZB.
  Proof. by apply (prod_relation_trans _). Qed.
  Lemma RZB_cmp_spec : cmp_spec IZB RZB cmpZfst.
  Proof.
    iIntros ([i1 y1] [i2 y2] v1 v2) "!>"; iIntros (Φ) "[HI1 HI2] HΦ".
    iDestruct "HI1" as (w1 ->) "HI1". iDestruct "HI2" as (w2 ->) "HI2 /=".
    wp_lam; wp_pures. iSpecialize ("HΦ" with "[HI1 HI2]").
    { iSplitL "HI1"; rewrite /IZB /=; eauto with iFrame. }
    repeat case_bool_decide=> //; unfold RZB, prod_relation in *; naive_solver.
  Qed.

  Lemma par_map_reduce_map_spec n cmap csort l xs X ys :
    (n = 0 → X = ∅ ∧ xs = []) →
    {{{
      llist IA l xs ∗
      cmap ↣ par_map_protocol IA IZB map n (X : gmultiset A) ∗
      csort ↣ sort_fg_head_protocol IZB RZB ys
    }}}
      par_map_reduce_map #n cmap csort #l
    {{{ ys', RET #();
      ⌜ys' ≡ₚ (xs ++ elements X) ≫= map⌝ ∗
      llist IA l [] ∗ csort ↣ sort_fg_head_protocol IZB RZB (ys ++ ys')
    }}}.
  Proof.
    iIntros (Hn Φ) "(Hl & Hcmap & Hcsort) HΦ".
    iLöb as "IH" forall (n xs X ys Hn Φ); wp_rec; wp_pures; simpl.
    case_bool_decide; wp_pures; simplify_eq/=.
    { destruct Hn as [-> ->]; first lia.
      iApply ("HΦ" $! []). rewrite right_id_L. auto with iFrame. }
    destruct n as [|n]=> //=. wp_branch as %?|%_; wp_pures.
    - wp_apply (lisnil_spec with "Hl"); iIntros "Hl".
      destruct xs as [|x xs]; csimpl; wp_pures.
      + wp_select. wp_pures. rewrite Nat2Z.inj_succ Z.sub_1_r Z.pred_succ.
        iApply ("IH" $! _ [] with "[%] Hl Hcmap Hcsort HΦ"); naive_solver.
      + wp_select. wp_apply (lpop_spec with "Hl"); iIntros (v) "[HIx Hl]".
        wp_send with "[$HIx]".
        wp_apply ("IH" with "[%] Hl Hcmap Hcsort"); first done. iIntros (ys').
        rewrite gmultiset_elements_disj_union gmultiset_elements_singleton.
        rewrite assoc_L -(comm _ [x]). iApply "HΦ".
    - wp_recv (x k) as (Hx) "Hk".
      rewrite -(right_id END%proto _ (sort_fg_head_protocol _ _ _)).
      wp_apply (send_all_spec with "[$Hk $Hcsort]"); iIntros "[_ Hcsort]".
      rewrite right_id.
      wp_apply ("IH" with "[] Hl Hcmap Hcsort"); first done.
      iIntros (ys'). iDestruct 1 as (Hys) "Hcsort"; simplify_eq/=.
      rewrite -assoc_L. iApply ("HΦ" $! (map x ++ ys') with "[$Hcsort]").
      iPureIntro. rewrite (gmultiset_disj_union_difference {[ x ]} X)
        -?gmultiset_elem_of_singleton_subseteq //.
      rewrite (comm disj_union) gmultiset_elements_disj_union.
      by rewrite gmultiset_elements_singleton assoc_L bind_app -Hys /= right_id_L comm.
  Qed.

  Lemma par_map_reduce_collect_spec csort iys iys_sorted i l ys :
    let acc := from_option (λ '(i,y,w), [(i,y)]) [] in
    let accv := from_option (λ '(i,y,w), SOMEV (#(i:Z),w)) NONEV in
    ys ≠ [] →
    Sorted RZB (iys_sorted ++ ((i,) <$> ys)) →
    i ∉ iys_sorted.*1 →
    {{{
      llist (IB i) l (reverse ys) ∗
      csort ↣ sort_fg_tail_protocol IZB RZB iys (iys_sorted ++ ((i,) <$> ys))
    }}}
      par_map_reduce_collect csort #i #l
    {{{ ys' miy, RET accv miy;
      ⌜ Sorted RZB ((iys_sorted ++ ((i,) <$> ys ++ ys')) ++ acc miy) ⌝ ∗
      ⌜ from_option (λ '(j,_,_), i ≠ j ∧ j ∉ iys_sorted.*1)
                    (iys_sorted ++ ((i,) <$> ys ++ ys') ≡ₚ iys) miy ⌝ ∗
      llist (IB i) l (reverse (ys ++ ys')) ∗
      csort ↣ from_option (λ _, sort_fg_tail_protocol IZB RZB iys
        ((iys_sorted ++ ((i,) <$> ys ++ ys')) ++ acc miy)) END%proto miy ∗
      from_option (λ '(i,y,w), IB i y w) True miy
    }}}.
  Proof.
    iIntros (acc accv Hys Hsort Hi Φ) "[Hl Hcsort] HΦ".
    iLöb as "IH" forall (ys Hys Hsort Hi Φ); wp_rec; wp_pures; simpl.
    wp_branch as %_|%Hperm; last first; wp_pures.
    { iApply ("HΦ" $! [] None with "[Hl $Hcsort]"); simpl.
     iEval (rewrite !right_id_L); auto with iFrame. }
    wp_recv ([j y] ?) as (Htl w ->) "HIy /=". wp_pures. rewrite -assoc_L.
    case_bool_decide as Hij; simplify_eq/=; wp_pures.
    - wp_apply (lcons_spec with "[$Hl $HIy]"); iIntros "Hl".
      rewrite -reverse_snoc. wp_apply ("IH" $! (ys ++ [y])
        with "[%] [%] [//] Hl [Hcsort] [HΦ]"); try iClear "IH".
      + intros ?; discriminate_list.
      + rewrite fmap_app /= assoc_L. by apply Sorted_snoc.
      + by rewrite fmap_app /= assoc_L.
      + iIntros "!>" (ys' miy). rewrite -!(assoc_L _ ys) /=. iApply "HΦ".
    - iApply ("HΦ" $! [] (Some (j,y,w))).
      rewrite /= !right_id_L assoc_L. iFrame. iPureIntro; split.
      { by apply Sorted_snoc. }
      split; first congruence.
      intros [[j' y'] [-> Hj]]%elem_of_list_fmap.
      destruct Hij; do 2 f_equal.
      destruct ys as [|y'' ys _] using rev_ind; first done.
      move: Htl. rewrite fmap_app assoc_L /=.
      inversion 1 as [|?? [? _]]; discriminate_list || simplify_list_eq.
      assert (RZB (j',y') (i,y'')) as [??]; last (simpl in *; lia).
      apply (Sorted_StronglySorted _) in Hsort.
      eapply elem_of_StronglySorted_app; set_solver.
  Qed.

  Lemma par_map_reduce_reduce_spec n iys iys_sorted miy zs l Y csort cred :
    let acc := from_option (λ '(i,y,w), [(i,y)]) [] in
    let accv := from_option (λ '(i,y,w), SOMEV (#(i:Z),w)) NONEV in
    (n = 0 → miy = None ∧ Y = ∅) →
    from_option (λ '(i,_,_), i ∉ iys_sorted.*1) (iys_sorted ≡ₚ iys) miy →
    Sorted RZB (iys_sorted ++ acc miy) →
    {{{
      llist IC l zs ∗
      csort ↣ from_option (λ _, sort_fg_tail_protocol IZB RZB iys
        (iys_sorted ++ acc miy)) END%proto miy ∗
      cred ↣ par_map_protocol IZBs IC (curry red) n (Y : gmultiset (Z * list B)) ∗
      from_option (λ '(i,y,w), IB i y w) True miy
    }}}
      par_map_reduce_reduce #n csort cred (accv miy) #l
    {{{ zs', RET #();
       ⌜ (group iys_sorted ≫= curry red) ++ zs' ≡ₚ (group iys ++ elements Y) ≫= curry red ⌝ ∗
       llist IC l (zs' ++ zs)
    }}}.
  Proof.
    iIntros (acc accv Hn Hmiy Hsort Φ) "(Hl & Hcsort & Hcred & HImiy) HΦ".
    iLöb as "IH" forall (n iys_sorted miy zs Y Hn Hmiy Hsort Φ); wp_rec; wp_pures; simpl.
    case_bool_decide; wp_pures; simplify_eq/=.
    { destruct Hn as [-> ->]; first lia.
      iApply ("HΦ" $! [] with "[$Hl]"); iPureIntro; simpl.
      by rewrite gmultiset_elements_empty !right_id_L Hmiy. }
    destruct n as [|n]=> //=. wp_branch as %?|%_; wp_pures.
    - destruct miy as [[[i y] w]|]; simplify_eq/=; wp_pures; last first.
      + wp_select. wp_pures. rewrite Nat2Z.inj_succ Z.sub_1_r Z.pred_succ.
        iApply ("IH" $! _ _ None
          with "[%] [%] [%] Hl Hcsort Hcred [] HΦ"); naive_solver.
      + wp_apply (lnil_spec (IB i) with "[//]"); iIntros (k) "Hk".
        wp_apply (lcons_spec with "[$Hk $HImiy]"); iIntros "Hk".
        wp_apply (par_map_reduce_collect_spec _ _ _ _ _ [_] 
          with "[$Hk $Hcsort]"); try done.
        iIntros (ys' miy). iDestruct 1 as (? Hmiy') "(Hk & Hcsort & HImiy)"; csimpl.
        wp_select; wp_pures. wp_send ((i, reverse (y :: ys'))) with "[Hk]".
        { iExists k; simpl; auto. }
        wp_pures. iApply ("IH" $! _ (_ ++ _) miy
          with "[%] [%] [//] Hl Hcsort Hcred HImiy"); first done.
        { destruct miy as [[[i' y'] w']|]; set_solver +Hmiy'. }
        iIntros "!>" (zs'). iDestruct 1 as (Hperm) "HIC".
        iApply ("HΦ" with "[$HIC]"); iPureIntro; move: Hperm.
        rewrite gmultiset_elements_disj_union gmultiset_elements_singleton.
        rewrite group_snoc // reverse_Permutation.
        rewrite !bind_app /= right_id_L -!assoc_L -(comm _ zs') !assoc_L.
        apply (inj (++ _)).
    - wp_recv ([i ys] k) as (Hy) "Hk".
      wp_apply (lprep_spec with "[$Hl $Hk]"); iIntros "[Hl _]".
      wp_apply ("IH" with "[ ] [//] [//] Hl Hcsort Hcred HImiy"); first done.
      iIntros (zs'); iDestruct 1 as (Hzs) "HIC"; simplify_eq/=.
      iApply ("HΦ" $! (zs' ++ red i ys)). iSplit; last by rewrite -assoc_L.
      iPureIntro. rewrite (gmultiset_disj_union_difference {[ i,ys ]} Y)
        -?gmultiset_elem_of_singleton_subseteq //.
      rewrite (comm disj_union) gmultiset_elements_disj_union.
      rewrite gmultiset_elements_singleton assoc_L Hzs !bind_app /=.
      by rewrite right_id_L !assoc_L.
  Qed.

  Lemma par_map_reduce_spec n m vmap vred l xs :
    0 < n → 0 < m →
    map_spec IA IZB map vmap -∗
    map_spec IZBs IC (curry red) vred -∗
    {{{ llist IA l xs }}}
      par_map_reduce #n #m vmap vred #l
    {{{ zs, RET #(); ⌜zs ≡ₚ map_reduce map red xs⌝ ∗ llist IC l zs }}}.
  Proof.
    iIntros (??) "#Hmap #Hred !>"; iIntros (Φ) "Hl HΦ". wp_lam; wp_pures.
    wp_apply (start_chan_proto_spec (par_map_protocol IA IZB map n ∅));
      iIntros (cmap) "// Hcmap".
    { wp_pures. wp_apply (par_map_service_spec with "Hmap Hcmap"); auto. }
    wp_apply (start_chan_proto_spec (sort_fg_protocol IZB RZB <++> END)%proto);
      iIntros (csort) "Hcsort".
    { wp_apply (sort_service_fg_spec with "[] Hcsort"); last by auto.
      iApply RZB_cmp_spec. }
    rewrite right_id.
    wp_apply (par_map_reduce_map_spec with "[$Hl $Hcmap $Hcsort]"); first lia.
    iIntros (iys). rewrite gmultiset_elements_empty right_id_L.
    iDestruct 1 as (Hiys) "[Hl Hcsort] /=". wp_select; wp_pures; simpl.
    wp_apply (start_chan_proto_spec (par_map_protocol IZBs IC (curry red) m ∅));
      iIntros (cred) "// Hcred".
    { wp_pures. wp_apply (par_map_service_spec with "Hred Hcred"); auto. }
    wp_branch as %_|%Hnil; last first.
    { wp_pures. iApply ("HΦ" $! [] with "[$Hl]"); simpl.
      by rewrite /map_reduce /= -Hiys -Hnil. }
    wp_recv ([i y] ?) as (_ w ->) "HIB /="; wp_pures.
    wp_apply (par_map_reduce_reduce_spec _ _ [] (Some (i, y, w)) []
      with "[$Hl $Hcsort $Hcred $HIB]"); simpl; auto; [lia|set_solver|].
    iIntros (zs). rewrite /= gmultiset_elements_empty !right_id.
    iDestruct 1 as (Hzs) "Hk". wp_pures.
    iApply ("HΦ" with "[$Hk]"). by rewrite Hzs Hiys.
  Qed.
End mapper.
