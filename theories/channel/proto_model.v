From iris.base_logic Require Import base_logic.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import cofe_solver.
Set Default Proof Using "Type".

Module Export action.
  Inductive action := Send | Receive.
  Instance action_inhabited : Inhabited action := populate Send.
  Definition action_dual (a : action) : action :=
    match a with Send => Receive | Receive => Send end.
  Instance action_dual_involutive : Involutive (=) action_dual.
  Proof. by intros []. Qed.
  Canonical Structure actionO := leibnizO action.
End action.

Definition protoOF_helper (V : Type) (PROPn PROP : ofeT) : oFunctor :=
  optionOF (actionO * (V -d> (▶ ∙ -n> PROPn) -n> PROP)).
Definition proto_result (V : Type) (PROPn PROP : ofeT) `{!Cofe PROPn, !Cofe PROP} :
  solution (protoOF_helper V PROPn PROP) := solver.result _.
Definition proto (V : Type) (PROPn PROP : ofeT) `{!Cofe PROPn, !Cofe PROP} : ofeT :=
  proto_result V PROPn PROP.
Instance proto_cofe {V} `{!Cofe PROPn, !Cofe PROP} : Cofe (proto V PROPn PROP).
Proof. apply _. Qed.

Definition proto_fold {V} `{!Cofe PROPn, !Cofe PROP} :
    protoOF_helper V PROPn PROP (proto V PROPn PROP) _ -n> proto V PROPn PROP :=
  solution_fold (proto_result V PROPn PROP).
Definition proto_unfold {V} `{!Cofe PROPn, !Cofe PROP} :
    proto V PROPn PROP -n> protoOF_helper V PROPn PROP (proto V PROPn PROP) _ :=
  solution_unfold (proto_result V PROPn PROP).

Lemma proto_fold_unfold {V} `{!Cofe PROPn, !Cofe PROP} (p : proto V PROPn PROP) :
  proto_fold (proto_unfold p) ≡ p.
Proof. apply solution_fold_unfold. Qed.
Lemma proto_unfold_fold {V} `{!Cofe PROPn, !Cofe PROP}
    (p : protoOF_helper V PROPn PROP (proto V PROPn PROP) _) :
  proto_unfold (proto_fold p) ≡ p.
Proof. apply solution_unfold_fold. Qed.

Definition proto_end {V} `{!Cofe PROPn, !Cofe PROP} : proto V PROPn PROP :=
  proto_fold None.
Definition proto_message {V} `{!Cofe PROPn, !Cofe PROP} (a : action)
    (pc : V → (laterO (proto V PROPn PROP) -n> PROPn) -n> PROP) : proto V PROPn PROP :=
  proto_fold (Some (a, pc)).

Instance proto_message_ne {V} `{!Cofe PROPn, !Cofe PROP} a n :
  Proper (pointwise_relation V (dist n) ==> dist n)
         (proto_message (PROPn:=PROPn) (PROP:=PROP) a).
Proof. intros c1 c2 Hc. rewrite /proto_message. f_equiv. by repeat constructor. Qed.
Instance proto_message_proper {V} `{!Cofe PROPn, !Cofe PROP} a :
  Proper (pointwise_relation V (≡) ==> (≡))
         (proto_message (PROPn:=PROPn) (PROP:=PROP) a).
Proof. intros c1 c2 Hc. rewrite /proto_message. f_equiv. by repeat constructor. Qed.

Lemma proto_case {V} `{!Cofe PROPn, !Cofe PROP} (p : proto V PROPn PROP) :
  p ≡ proto_end ∨ ∃ a pc, p ≡ proto_message a pc.
Proof.
  destruct (proto_unfold p) as [[a pc]|] eqn:E; simpl in *; last first.
  - left. by rewrite -(proto_fold_unfold p) E.
  - right. exists a, pc. by rewrite -(proto_fold_unfold p) E.
Qed.
Instance proto_inhabited {V} `{!Cofe PROPn, !Cofe PROP} :
  Inhabited (proto V PROPn PROP) := populate proto_end.

Lemma proto_message_equivI {SPROP : sbi} {V} `{!Cofe PROPn, !Cofe PROP} a1 a2 pc1 pc2 :
  proto_message (V:=V) (PROPn:=PROPn) (PROP:=PROP) a1 pc1 ≡ proto_message a2 pc2
  ⊣⊢@{SPROP} ⌜ a1 = a2 ⌝ ∧ (∀ v, pc1 v ≡ pc2 v).
Proof.
  trans (proto_unfold (proto_message a1 pc1) ≡ proto_unfold (proto_message a2 pc2) : SPROP)%I.
  { iSplit.
    - iIntros "Heq". by iRewrite "Heq".
    - iIntros "Heq". rewrite -{2}(proto_fold_unfold (proto_message _ _)).
      iRewrite "Heq". by rewrite proto_fold_unfold. }
  rewrite /proto_message !proto_unfold_fold bi.option_equivI bi.prod_equivI /=.
  by rewrite bi.discrete_fun_equivI bi.discrete_eq.
Qed.

Definition proto_cont_map
   `{!Cofe PROPn, !Cofe PROPn', !Cofe PROP, !Cofe PROP', !Cofe A, !Cofe B}
    (gn : PROPn' -n> PROPn) (g : PROP -n> PROP') (h : A -n> B) :
    ((laterO A -n> PROPn) -n> PROP) -n> (laterO B -n> PROPn') -n> PROP' :=
  ofe_morO_map (ofe_morO_map (laterO_map h) gn) g.

(** Append *)
Program Definition proto_app_flipped_aux {V} `{!Cofe PROPn, !Cofe PROP}
    (p2 : proto V PROPn PROP) (rec : proto V PROPn PROP -n> proto V PROPn PROP) :
    proto V PROPn PROP -n> proto V PROPn PROP := λne p1,
  match proto_unfold p1 return _ with
  | None => p2
  | Some (a, c) => proto_message a (proto_cont_map cid cid rec ∘ c)
  end.
Next Obligation.
  intros V PROPn ? PROP ? rec n p2 p1 p1' Hp.
  apply (ofe_mor_ne _ _ proto_unfold) in Hp.
  destruct Hp as [[??][??] [-> ?]|]; simplify_eq/=; last done.
  f_equiv=> v /=. by f_equiv.
Qed.

Instance proto_app_flipped_aux_contractive {V} `{!Cofe PROPn, !Cofe PROP}
  (p2 : proto V PROPn PROP) : Contractive (proto_app_flipped_aux p2).
Proof.
  intros n rec1 rec2 Hrec p1. simpl.
  destruct (proto_unfold p1) as [[a c]|]; last done.
  f_equiv=> v /=. do 2 f_equiv.
  intros=> p'. apply Next_contractive. destruct n as [|n]=> //=.
Qed.

Definition proto_app_flipped {V} `{!Cofe PROPn, !Cofe PROP}
    (p2 : proto V PROPn PROP) : proto V PROPn PROP -n> proto V PROPn PROP :=
  fixpoint (proto_app_flipped_aux p2).
Definition proto_app {V} `{!Cofe PROPn, !Cofe PROP}
  (p1 p2 : proto V PROPn PROP) : proto V PROPn PROP := proto_app_flipped p2 p1.
Instance: Params (@proto_app) 5.

Lemma proto_app_flipped_unfold {V} `{!Cofe PROPn, !Cofe PROP} (p1 p2 : proto V PROPn PROP):
  proto_app_flipped p2 p1 ≡ proto_app_flipped_aux p2 (proto_app_flipped p2) p1.
Proof. apply (fixpoint_unfold (proto_app_flipped_aux p2)). Qed.
Lemma proto_app_unfold {V} `{!Cofe PROPn, !Cofe PROP} (p1 p2 : proto V PROPn PROP):
  proto_app (V:=V) p1 p2 ≡ proto_app_flipped_aux p2 (proto_app_flipped p2) p1.
Proof. apply (fixpoint_unfold (proto_app_flipped_aux p2)). Qed.

Lemma proto_app_end_l {V} `{!Cofe PROPn, !Cofe PROP} (p2 : proto V PROPn PROP) :
  proto_app proto_end p2 ≡ p2.
Proof.
  rewrite proto_app_unfold /proto_end /=.
  pose proof (proto_unfold_fold (V:=V) (PROPn:=PROPn) (PROP:=PROP) None) as Hfold.
  by destruct (proto_unfold (proto_fold None))
    as [[??]|] eqn:E; rewrite E; inversion Hfold.
Qed.
Lemma proto_app_message {V} `{!Cofe PROPn, !Cofe PROP} a c (p2 : proto V PROPn PROP) :
  proto_app (proto_message a c) p2
  ≡ proto_message a (proto_cont_map cid cid (proto_app_flipped p2) ∘ c).
Proof.
  rewrite proto_app_unfold /proto_message /=.
  pose proof (proto_unfold_fold (V:=V) (PROPn:=PROPn) (PROP:=PROP) (Some (a, c))) as Hfold.
  destruct (proto_unfold (proto_fold (Some (a, c))))
    as [[??]|] eqn:E; inversion Hfold as [?? [Ha Hc]|]; simplify_eq/=.
  rewrite /proto_message. do 3 f_equiv. intros v=> /=.
  apply equiv_dist=> n. f_equiv. by apply equiv_dist.
Qed.

Instance proto_app_ne {V} `{!Cofe PROPn, !Cofe PROP} :
  NonExpansive2 (proto_app (V:=V) (PROPn:=PROPn) (PROP:=PROP)).
Proof.
  intros n p1 p1' Hp1 p2 p2' Hp2. rewrite /proto_app -Hp1 {p1' Hp1}.
  revert p1. induction (lt_wf n) as [n _ IH]=> p1 /=.
  rewrite !proto_app_flipped_unfold /proto_app_flipped_aux /=.
  destruct (proto_unfold p1) as [[a c]|]; last done.
  f_equiv=> v f /=. do 2 f_equiv. intros p. apply Next_contractive.
  destruct n as [|n]=> //=. apply IH; first lia; auto using dist_S.
Qed.
Instance proto_app_proper {V} `{!Cofe PROPn, !Cofe PROP} :
  Proper ((≡) ==> (≡) ==> (≡)) (proto_app (V:=V) (PROPn:=PROPn) (PROP:=PROP)).
Proof. apply (ne_proper_2 _). Qed.

Lemma proto_app_end_r {V} `{!Cofe PROPn, !Cofe PROP} (p1 : proto V PROPn PROP) :
  proto_app p1 proto_end ≡ p1.
Proof.
  apply equiv_dist=> n. revert p1. induction (lt_wf n) as [n _ IH]=> p1 /=.
  destruct (proto_case p1) as [->|(a & c & ->)].
  - by rewrite !proto_app_end_l.
  - rewrite !proto_app_message /=. f_equiv=> v c' /=. f_equiv=> p' /=. f_equiv.
    apply Next_contractive. destruct n as [|n]=> //=.
    apply IH; first lia; auto using dist_S.
Qed.
Lemma proto_app_assoc {V} `{!Cofe PROPn, !Cofe PROP} (p1 p2 p3 : proto V PROPn PROP) :
  proto_app p1 (proto_app p2 p3) ≡ proto_app (proto_app p1 p2) p3.
Proof.
  apply equiv_dist=> n. revert p1. induction (lt_wf n) as [n _ IH]=> p1 /=.
  destruct (proto_case p1) as [->|(a & c & ->)].
  - by rewrite !proto_app_end_l.
  - rewrite !proto_app_message /=. f_equiv=> v c' /=. f_equiv=> p' /=. f_equiv.
    apply Next_contractive. destruct n as [|n]=> //=.
    apply IH; first lia; auto using dist_S.
Qed.

(** Functor *)
Program Definition proto_map_aux {V}
   `{!Cofe PROPn, !Cofe PROPn', !Cofe PROP, !Cofe PROP'}
    (f : action → action) (gn : PROPn' -n> PROPn) (g : PROP -n> PROP')
    (rec : proto V PROPn PROP -n> proto V PROPn' PROP') :
    proto V PROPn PROP -n> proto V PROPn' PROP' := λne p,
  match proto_unfold p return _ with
  | None => proto_end
  | Some (a, c) => proto_message (f a) (proto_cont_map gn g rec ∘ c)
  end.
Next Obligation.
  intros V PROPn ? PROPn' ? PROP ? PROP' ? f g1 g2 rec n p1 p2 Hp.
  apply (ofe_mor_ne _ _ proto_unfold) in Hp.
  destruct Hp as [[??][??] [-> ?]|]; simplify_eq/=; last done.
  f_equiv=> v /=. by f_equiv.
Qed.
Instance proto_map_aux_contractive {V}
   `{!Cofe PROPn, !Cofe PROPn', !Cofe PROP, !Cofe PROP'}
    (f : action → action) (gn : PROPn' -n> PROPn) (g : PROP -n> PROP') :
  Contractive (proto_map_aux (V:=V) f gn g).
Proof.
  intros n rec1 rec2 Hrec p. simpl.
  destruct (proto_unfold p) as [[a c]|]; last done.
  f_equiv=> v /=. do 2 f_equiv.
  intros=> p'. apply Next_contractive. destruct n as [|n]=> //=.
Qed.
Definition proto_map {V}
   `{!Cofe PROPn, !Cofe PROPn', !Cofe PROP, !Cofe PROP'}
    (f : action → action) (gn : PROPn' -n> PROPn) (g : PROP -n> PROP') :
    proto V PROPn PROP -n> proto V PROPn' PROP' :=
  fixpoint (proto_map_aux f gn g).

Lemma proto_map_unfold {V} `{!Cofe PROPn, !Cofe PROPn', !Cofe PROP, !Cofe PROP'}
    (f : action → action) (gn : PROPn' -n> PROPn) (g : PROP -n> PROP') p :
  proto_map (V:=V) f gn g p ≡ proto_map_aux f gn g (proto_map f gn g) p.
Proof. apply (fixpoint_unfold (proto_map_aux f gn g)). Qed.
Lemma proto_map_end {V} `{!Cofe PROPn, !Cofe PROPn', !Cofe PROP, !Cofe PROP'}
    (f : action → action) (gn : PROPn' -n> PROPn) (g : PROP -n> PROP') :
  proto_map (V:=V) f gn g proto_end ≡ proto_end.
Proof.
  rewrite proto_map_unfold /proto_end /=.
  pose proof (proto_unfold_fold (V:=V) (PROPn:=PROPn) (PROP:=PROP) None) as Hfold.
  by destruct (proto_unfold (proto_fold None))
    as [[??]|] eqn:E; rewrite E; inversion Hfold.
Qed.
Lemma proto_map_message {V} `{!Cofe PROPn, !Cofe PROPn', !Cofe PROP, !Cofe PROP'}
    (f : action → action) (gn : PROPn' -n> PROPn) (g : PROP -n> PROP') a c :
  proto_map (V:=V) f gn g (proto_message a c) ≡ proto_message (f a) (proto_cont_map gn g (proto_map f gn g) ∘ c).
Proof.
  rewrite proto_map_unfold /proto_message /=.
  pose proof (proto_unfold_fold (V:=V) (PROPn:=PROPn) (PROP:=PROP) (Some (a, c))) as Hfold.
  destruct (proto_unfold (proto_fold (Some (a, c))))
    as [[??]|] eqn:E; inversion Hfold as [?? [Ha Hc]|]; simplify_eq/=.
  rewrite /proto_message. do 3 f_equiv. intros v=> /=.
  apply equiv_dist=> n. f_equiv. by apply equiv_dist.
Qed.

Lemma proto_map_ne {V} `{!Cofe PROPn, !Cofe PROPn', !Cofe PROP, !Cofe PROP'}
    (f1 f2 : action → action) (gn1 gn2 : PROPn' -n> PROPn) (g1 g2 : PROP -n> PROP') p n :
  (∀ a, f1 a = f2 a) → (∀ x, gn1 x ≡{n}≡ gn2 x) → (∀ x, g1 x ≡{n}≡ g2 x) →
  proto_map (V:=V) f1 gn1 g1 p ≡{n}≡ proto_map (V:=V) f2 gn2 g2 p.
Proof.
  intros Hf. revert p. induction (lt_wf n) as [n _ IH]=> p Hgn Hg /=.
  destruct (proto_case p) as [->|(a & c & ->)].
  - by rewrite !proto_map_end.
  - rewrite !proto_map_message /= Hf. f_equiv=> v /=. do 2 (f_equiv; last done).
    intros p'. apply Next_contractive. destruct n as [|n]=> //=.
    apply IH; first lia; auto using dist_S.
Qed.
Lemma proto_map_ext {V} `{!Cofe PROPn, !Cofe PROPn', !Cofe PROP, !Cofe PROP'}
    (f1 f2 : action → action) (gn1 gn2 : PROPn' -n> PROPn) (g1 g2 : PROP -n> PROP') p :
  (∀ a, f1 a = f2 a) → (∀ x, gn1 x ≡ gn2 x) → (∀ x, g1 x ≡ g2 x) →
  proto_map (V:=V) f1 gn1 g1 p ≡ proto_map (V:=V) f2 gn2 g2 p.
Proof.
  intros Hf Hgn Hg. apply equiv_dist=> n.
  apply proto_map_ne=> // ?; by apply equiv_dist.
Qed.
Lemma proto_map_id {V} `{!Cofe PROPn, !Cofe PROP} (p : proto V PROPn PROP) :
  proto_map id cid cid p ≡ p.
Proof.
  apply equiv_dist=> n. revert p. induction (lt_wf n) as [n _ IH]=> p /=.
  destruct (proto_case p) as [->|(a & c & ->)].
  - by rewrite !proto_map_end.
  - rewrite !proto_map_message /=. f_equiv=> v c' /=. f_equiv=> p' /=. f_equiv.
    apply Next_contractive. destruct n as [|n]=> //=.
    apply IH; first lia; auto using dist_S.
Qed.
Lemma proto_map_compose {V}
   `{!Cofe PROPn, !Cofe PROPn', !Cofe PROPn'', !Cofe PROP, !Cofe PROP', !Cofe PROP''}
    (f1 f2 : action → action)
    (gn1 : PROPn'' -n> PROPn') (gn2 : PROPn' -n> PROPn)
    (g1 : PROP -n> PROP') (g2 : PROP' -n> PROP'') (p : proto V PROPn PROP) :
  proto_map (f2 ∘ f1) (gn2 ◎ gn1) (g2 ◎ g1) p ≡ proto_map f2 gn1 g2 (proto_map f1 gn2 g1 p).
Proof.
  apply equiv_dist=> n. revert p. induction (lt_wf n) as [n _ IH]=> p /=.
  destruct (proto_case p) as [->|(a & c & ->)].
  - by rewrite !proto_map_end.
  - rewrite !proto_map_message /=. f_equiv=> v c' /=. do 3 f_equiv. move=> p' /=.
    do 3 f_equiv. apply Next_contractive. destruct n as [|n]=> //=.
    apply IH; first lia; auto using dist_S.
Qed.

Lemma proto_map_app {V} `{!Cofe PROPn, !Cofe PROPn', !Cofe PROP, !Cofe PROP'}
    (f : action → action) (gn : PROPn' -n> PROPn) (g : PROP -n> PROP') p1 p2 :
  proto_map (V:=V) f gn g (proto_app p1 p2)
  ≡ proto_app (proto_map (V:=V) f gn g p1) (proto_map (V:=V) f gn g p2).
Proof.
  apply equiv_dist=> n. revert p1 p2. induction (lt_wf n) as [n _ IH]=> p1 p2 /=.
  destruct (proto_case p1) as [->|(a & c & ->)].
  - by rewrite proto_map_end !proto_app_end_l.
  - rewrite proto_map_message !proto_app_message proto_map_message /=.
    f_equiv=> v c' /=. do 2 f_equiv. move=> p' /=. do 2 f_equiv.
    apply Next_contractive. destruct n as [|n]=> //=.
    apply IH; first lia; auto using dist_S.
Qed.

Program Definition protoOF (V : Type) (Fn F : oFunctor)
    `{!∀ A B `{!Cofe A, !Cofe B}, Cofe (oFunctor_car Fn A B)}
    `{!∀ A B `{!Cofe A, !Cofe B}, Cofe (oFunctor_car F A B)} : oFunctor := {|
  oFunctor_car A _ B _ := proto V (oFunctor_car Fn B A) (oFunctor_car F A B);
  oFunctor_map A1 _ A2 _ B1 _ B2 _ fg :=
    proto_map id (oFunctor_map Fn (fg.2, fg.1)) (oFunctor_map F fg)
|}.
Next Obligation.
  intros V Fn F ?? A1 ? A2 ? B1 ? B2 ? n f g [??] p; simpl in *.
  apply proto_map_ne=> // y; by apply oFunctor_ne.
Qed.
Next Obligation.
  intros V Fn F ?? A ? B ? p; simpl in *. rewrite /= -{2}(proto_map_id p).
  apply proto_map_ext=> //= y; by rewrite oFunctor_id.
Qed.
Next Obligation.
  intros V Fn F ?? A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' p; simpl in *.
  rewrite -proto_map_compose.
  apply proto_map_ext=> //= y; by rewrite oFunctor_compose.
Qed.

Instance protoOF_contractive (V : Type) (Fn F : oFunctor)
    `{!∀ A B `{!Cofe A, !Cofe B}, Cofe (oFunctor_car Fn A B)}
    `{!∀ A B `{!Cofe A, !Cofe B}, Cofe (oFunctor_car F A B)} :
  oFunctorContractive Fn → oFunctorContractive F → 
  oFunctorContractive (protoOF V Fn F).
Proof.
  intros ?? A1 ? A2 ? B1 ? B2 ? n f g Hfg p; simpl in *.
  apply proto_map_ne=> //= y.
  - destruct n; [|destruct Hfg]; by apply oFunctor_contractive.
  - destruct n; [|destruct Hfg]; by apply oFunctor_contractive.
Qed.
