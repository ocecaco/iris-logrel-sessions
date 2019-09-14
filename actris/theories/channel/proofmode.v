From iris.heap_lang Require Export proofmode notation.
From iris.proofmode Require Export tactics.
From actris Require Export proto_channel.
From iris.proofmode Require Import coq_tactics reduction spec_patterns.

(** Classes *)
Class ActionDualIf (d : bool) (a1 a2 : action) :=
  dual_action_if : a2 = if d then action_dual a1 else a1.
Hint Mode ActionDualIf ! ! - : typeclass_instances.

(** Tactics for proving contractiveness of protocols *)
Ltac f_proto_contractive :=
  match goal with
  | _ => apply iProto_branch_contractive
  | _ => apply iProto_message_contractive; simpl; intros; [reflexivity|..]
  | H : _ ≡{?n}≡ _ |- _ ≡{?n'}≡ _ => apply (dist_le n); [apply H|lia]
  end;
  try match goal with
  | |- @dist_later ?A _ ?n ?x ?y =>
         destruct n as [|n]; simpl in *; [exact Logic.I|change (@dist A _ n x y)]
  end.

Ltac solve_proto_contractive :=
  solve_proper_core ltac:(fun _ => first [f_contractive | f_proto_contractive | f_equiv]).

(** Normalization of protocols *)
Instance action_dual_if_false a : ActionDualIf false a a := eq_refl.
Instance action_dual_if_true_send : ActionDualIf true Send Receive := eq_refl.
Instance action_dual_if_true_receive : ActionDualIf true Receive Send := eq_refl.

Class ProtoNormalize {Σ} (d : bool) (p : iProto Σ)
    (pas : list (bool * iProto Σ)) (q : iProto Σ) :=
  proto_normalize :
    q ≡ (iProto_dual_if d p <++>
         foldr (iProto_app ∘ curry iProto_dual_if) END pas)%proto.
Hint Mode ProtoNormalize ! ! ! ! - : typeclass_instances.
Arguments ProtoNormalize {_} _ _%proto _%proto _%proto.

Class ProtoContNormalize {Σ TT} (d : bool) (pc : TT → val * iProp Σ * iProto Σ)
    (pas : list (bool * iProto Σ)) (qc : TT → val * iProp Σ * iProto Σ) :=
  proto_cont_normalize x :
    (qc x).1.1 = (pc x).1.1 ∧
    (qc x).1.2 ≡ (pc x).1.2 ∧
    ProtoNormalize d ((pc x).2) pas ((qc x).2).
Hint Mode ProtoContNormalize ! ! ! ! ! - : typeclass_instances.

Notation ProtoUnfold p1 p2 := (∀ d pas q,
  ProtoNormalize d p2 pas q → ProtoNormalize d p1 pas q).

Section classes.
  Context `{!proto_chanG Σ, !heapG Σ}.
  Implicit Types p : iProto Σ.
  Implicit Types TT : tele.

  (** Classes *)
  Lemma proto_unfold_eq p1 p2 : p1 ≡ p2 → ProtoUnfold p1 p2.
  Proof. rewrite /ProtoNormalize=> Hp d pas q ->. by rewrite Hp. Qed.

  Global Instance proto_normalize_done p : ProtoNormalize false p [] p | 0.
  Proof. by rewrite /ProtoNormalize /= right_id. Qed. 
  Global Instance proto_normalize_done_dual p :
    ProtoNormalize true p [] (iProto_dual p) | 0.
  Proof. by rewrite /ProtoNormalize /= right_id. Qed.
  Global Instance proto_normalize_done_dual_end :
    ProtoNormalize (Σ:=Σ) true END [] END | 0.
  Proof. by rewrite /ProtoNormalize /= right_id iProto_dual_end. Qed.

  Global Instance proto_normalize_dual d p pas q :
    ProtoNormalize (negb d) p pas q →
    ProtoNormalize d (iProto_dual p) pas q.
  Proof. rewrite /ProtoNormalize=> ->. by destruct d; rewrite /= ?involutive. Qed.

  Global Instance proto_normalize_app_l d p1 p2 pas q :
    ProtoNormalize d p1 ((d,p2) :: pas) q →
    ProtoNormalize d (p1 <++> p2) pas q.
  Proof.
    rewrite /ProtoNormalize=> -> /=. rewrite assoc.
    by destruct d; by rewrite /= ?iProto_dual_app.
  Qed.

  Global Instance proto_normalize_end d d' p pas q :
    ProtoNormalize d p pas q →
    ProtoNormalize d' END ((d,p) :: pas) q | 0.
  Proof.
    rewrite /ProtoNormalize=> -> /=.
    destruct d'; by rewrite /= ?iProto_dual_end left_id.
  Qed.

  Global Instance proto_normalize_app_r d p1 p2 pas q :
    ProtoNormalize d p2 pas q →
    ProtoNormalize false p1 ((d,p2) :: pas) (p1 <++> q) | 0.
  Proof. by rewrite /ProtoNormalize=> -> /=. Qed.

  Global Instance proto_normalize_app_r_dual d p1 p2 pas q :
    ProtoNormalize d p2 pas q →
    ProtoNormalize true p1 ((d,p2) :: pas) (iProto_dual p1 <++> q) | 0.
  Proof. by rewrite /ProtoNormalize=> -> /=. Qed.

  Global Instance proto_cont_normalize_O d v P p q pas :
    ProtoNormalize d p pas q →
    ProtoContNormalize d (tele_app (TT:=TeleO) (v,P,p)) pas
                         (tele_app (TT:=TeleO) (v,P,q)).
  Proof. rewrite /ProtoContNormalize=> ?. by apply tforall_forall. Qed.

  Global Instance proto_cont_normalize_S {A} {TT : A → tele} d
      (pc qc : ∀ a, TT a -t> val * iProp Σ * iProto Σ) pas :
    (∀ a, ProtoContNormalize d (tele_app (pc a)) pas (tele_app (qc a))) →
    ProtoContNormalize d (tele_app (TT:=TeleS TT) pc) pas (tele_app (TT:=TeleS TT) qc).
  Proof.
    rewrite /ProtoContNormalize=> H. apply tforall_forall=> /= x.
    apply tforall_forall, (H x).
  Qed.

  Global Instance proto_normalize_message {TT} d a1 a2
      (pc qc : TT → val * iProp Σ * iProto Σ) pas :
    ActionDualIf d a1 a2 →
    ProtoContNormalize d pc pas qc →
    ProtoNormalize d (iProto_message a1 pc) pas
                     (iProto_message a2 qc).
  Proof.
    rewrite /ActionDualIf /ProtoContNormalize /ProtoNormalize=> -> H.
    destruct d; simpl.
    - rewrite iProto_dual_message iProto_app_message.
      apply iProto_message_proper; apply tforall_forall=> x /=; apply H.
    - rewrite iProto_app_message.
      apply iProto_message_proper; apply tforall_forall=> x /=; apply H.
  Qed.

  Global Instance proto_normalize_branch d a1 a2 P1 P2 p1 p2 q1 q2 pas :
    ActionDualIf d a1 a2 →
    ProtoNormalize d p1 pas q1 → ProtoNormalize d p2 pas q2 →
    ProtoNormalize d (iProto_branch a1 P1 P2 p1 p2) pas
                     (iProto_branch a2 P1 P2 q1 q2).
  Proof.
    rewrite /ActionDualIf /ProtoNormalize=> -> -> ->.
    destruct d; by rewrite /= -?iProto_app_branch -?iProto_dual_branch.
  Qed.

  (** Automatically perform normalization of protocols in the proof mode *)
  Global Instance mapsto_proto_from_assumption q c p1 p2 :
    ProtoNormalize false p1 [] p2 →
    FromAssumption q (c ↣ p1) (c ↣ p2).
  Proof.
    rewrite /FromAssumption /ProtoNormalize=> ->.
    by rewrite /= right_id bi.intuitionistically_if_elim.
  Qed.
  Global Instance mapsto_proto_from_frame q c p1 p2 :
    ProtoNormalize false p1 [] p2 →
    Frame q (c ↣ p1) (c ↣ p2) True.
  Proof.
    rewrite /Frame /ProtoNormalize=> ->.
    by rewrite /= !right_id bi.intuitionistically_if_elim.
  Qed.
End classes.

(** Symbolic execution tactics *)
(* TODO: strip laters *)
Lemma tac_wp_recv `{!proto_chanG Σ, !heapG Σ} {TT : tele} Δ i j K
    c p (pc : TT → val * iProp Σ * iProto Σ) Φ :
  envs_lookup i Δ = Some (false, c ↣ p)%I →
  ProtoNormalize false p [] (iProto_message Receive pc) →
  let Δ' := envs_delete false i false Δ in
  (∀.. x : TT,
    match envs_app false
        (Esnoc (Esnoc Enil j ((pc x).1.2)) i (c ↣ (pc x).2)) Δ' with
    | Some Δ'' => envs_entails Δ'' (WP fill K (of_val (pc x).1.1) {{ Φ }})
    | None => False
    end) →
  envs_entails Δ (WP fill K (recv c) {{ Φ }}).
Proof.
  rewrite envs_entails_eq /ProtoNormalize /= tforall_forall right_id=> ? Hp HΦ.
  rewrite envs_lookup_sound //; simpl. rewrite -Hp.
  rewrite -wp_bind. eapply bi.wand_apply; [by eapply recv_proto_spec|f_equiv].
  rewrite -bi.later_intro bi_tforall_forall; apply bi.forall_intro=> x.
  specialize (HΦ x). destruct (envs_app _ _) as [Δ'|] eqn:HΔ'=> //.
  rewrite envs_app_sound //; simpl.
  by rewrite right_id HΦ bi.wand_curry.
Qed.

Tactic Notation "wp_recv_core" tactic3(tac_intros) "as" tactic3(tac) :=
  let solve_mapsto _ :=
    let c := match goal with |- _ = Some (_, (?c ↣ _)%I) => c end in
    iAssumptionCore || fail "wp_recv: cannot find" c "↣ ? @ ?" in
  wp_pures;
  let Hnew := iFresh in
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_recv _ _ Hnew K))
      |fail 1 "wp_recv: cannot find 'recv' in" e];
    [solve_mapsto ()
       |iSolveTC || fail 1 "wp_send: protocol not of the shape <?>"
    |pm_reduce; simpl; tac_intros;
     tac Hnew;
     wp_finish]
  | _ => fail "wp_recv: not a 'wp'"
  end.

Tactic Notation "wp_recv" "as" constr(pat) :=
  wp_recv_core (idtac) as (fun H => iDestructHyp H as pat).

Tactic Notation "wp_recv" "(" intropattern_list(xs) ")" "as" constr(pat) :=
  wp_recv_core (intros xs) as (fun H => iDestructHyp H as pat).
Tactic Notation "wp_recv" "(" intropattern_list(xs) ")" "as" "(" simple_intropattern(x1) ")"
    constr(pat) :=
  wp_recv_core (intros xs) as (fun H => iDestructHyp H as ( x1 ) pat).
Tactic Notation "wp_recv" "(" intropattern_list(xs) ")" "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) ")" constr(pat) :=
  wp_recv_core (intros xs) as (fun H => iDestructHyp H as ( x1 x2 ) pat).
Tactic Notation "wp_recv" "(" intropattern_list(xs) ")" "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) ")" constr(pat) :=
  wp_recv_core (intros xs) as (fun H => iDestructHyp H as ( x1 x2 x3 ) pat).
Tactic Notation "wp_recv" "(" intropattern_list(xs) ")" "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4) ")"
    constr(pat) :=
  wp_recv_core (intros xs) as (fun H => iDestructHyp H as ( x1 x2 x3 x4 ) pat).
Tactic Notation "wp_recv" "(" intropattern_list(xs) ")" "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) ")" constr(pat) :=
  wp_recv_core (intros xs) as (fun H => iDestructHyp H as ( x1 x2 x3 x4 x5 ) pat).
Tactic Notation "wp_recv" "(" intropattern_list(xs) ")" "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) ")" constr(pat) :=
  wp_recv_core (intros xs) as (fun H => iDestructHyp H as ( x1 x2 x3 x4 x5 x6 ) pat).
Tactic Notation "wp_recv" "(" intropattern_list(xs) ")" "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7) ")"
    constr(pat) :=
  wp_recv_core (intros xs) as (fun H => iDestructHyp H as ( x1 x2 x3 x4 x5 x6 x7 ) pat).
Tactic Notation "wp_recv" "(" intropattern_list(xs) ")" "as" "(" simple_intropattern(x1)
    simple_intropattern(x2) simple_intropattern(x3) simple_intropattern(x4)
    simple_intropattern(x5) simple_intropattern(x6) simple_intropattern(x7)
    simple_intropattern(x8) ")" constr(pat) :=
  wp_recv_core (intros xs) as (fun H => iDestructHyp H as ( x1 x2 x3 x4 x5 x6 x7 x8 ) pat).

Lemma tac_wp_send `{!proto_chanG Σ, !heapG Σ} {TT : tele} Δ neg i js K
    c v p (pc : TT → val * iProp Σ * iProto Σ) Φ :
  envs_lookup i Δ = Some (false, c ↣ p)%I →
  ProtoNormalize false p [] (iProto_message Send pc) →
  let Δ' := envs_delete false i false Δ in
  (∃.. x : TT,
    match envs_split (if neg is true then Right else Left) js Δ' with
    | Some (Δ1,Δ2) =>
       match envs_app false (Esnoc Enil i (c ↣ (pc x).2)) Δ2 with
       | Some Δ2' =>
          v = (pc x).1.1 ∧
          envs_entails Δ1 (pc x).1.2 ∧
          envs_entails Δ2' (WP fill K (of_val #()) {{ Φ }})
       | None => False
       end
    | None => False
    end) →
  envs_entails Δ (WP fill K (send c v) {{ Φ }}).
Proof.
  rewrite envs_entails_eq /ProtoNormalize /= right_id texist_exist=> ? Hp [x HΦ].
  rewrite envs_lookup_sound //; simpl. rewrite -Hp.
  rewrite -wp_bind. eapply bi.wand_apply; [by eapply send_proto_spec|f_equiv].
  rewrite bi_texist_exist -(bi.exist_intro x).
  destruct (envs_split _ _ _) as [[Δ1 Δ2]|] eqn:? => //.
  destruct (envs_app _ _ _) as [Δ2'|] eqn:? => //.
  rewrite envs_split_sound //; rewrite (envs_app_sound Δ2) //; simpl.
  destruct HΦ as (-> & -> & ->). rewrite bi.pure_True // left_id.
  by rewrite -bi.later_intro right_id.
Qed.

Tactic Notation "wp_send_core" tactic3(tac_exist) "with" constr(pat) :=
  let solve_mapsto _ :=
    let c := match goal with |- _ = Some (_, (?c ↣ _)%I) => c end in
    iAssumptionCore || fail "wp_send: cannot find" c "↣ ? @ ?" in
  let solve_done d :=
    lazymatch d with
    | true =>
       done ||
       let Q := match goal with |- envs_entails _ ?Q => Q end in
       fail "wp_send: cannot solve" Q "using done"
    | false => idtac
    end in
  lazymatch spec_pat.parse pat with
  | [SGoal (SpecGoal GSpatial ?neg ?Hs_frame ?Hs ?d)] =>
     let Hs' := eval cbv in (if neg then Hs else Hs_frame ++ Hs) in
     wp_pures;
     lazymatch goal with
     | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
       first
         [reshape_expr e ltac:(fun K e' => eapply (tac_wp_send _ neg _ Hs' K))
         |fail 1 "wp_send: cannot find 'send' in" e];
       [solve_mapsto ()
       |iSolveTC || fail 1 "wp_send: protocol not of the shape <!>"
       |pm_reduce; simpl; tac_exist;
        repeat lazymatch goal with
        | |- ∃ _, _ => eexists _
        end;
        lazymatch goal with
        | |- False => fail "wp_send:" Hs' "not found"
        | _ => split; [try fast_done|split;[iFrame Hs_frame; solve_done d|wp_finish]]
        end]
     | _ => fail "wp_send: not a 'wp'"
     end
  | _ => fail "wp_send: only a single goal spec pattern supported"
  end.

Tactic Notation "wp_send" "with" constr(pat) :=
  wp_send_core (idtac) with pat.
Tactic Notation "wp_send" "(" uconstr(x1) ")" "with" constr(pat) :=
  wp_send_core (eexists x1) with pat.
Tactic Notation "wp_send" "(" uconstr(x1) uconstr(x2) ")" "with" constr(pat) :=
  wp_send_core (eexists x1; eexists x2) with pat.
Tactic Notation "wp_send" "(" uconstr(x1) uconstr(x2) uconstr(x3) ")"
    "with" constr(pat) :=
  wp_send_core (eexists x1; eexists x2; eexists x3) with pat.
Tactic Notation "wp_send" "(" uconstr(x1) uconstr(x2) uconstr(x3) uconstr(x4) ")"
    "with" constr(pat) :=
  wp_send_core (eexists x1; eexists x2; eexists x3; eexists x4) with pat.
Tactic Notation "wp_send" "(" uconstr(x1) uconstr(x2) uconstr(x3) uconstr(x4)
    uconstr(x5) ")" "with" constr(pat) :=
  wp_send_core (eexists x1; eexists x2; eexists x3; eexists x4; eexists x5) with pat.
Tactic Notation "wp_send" "(" uconstr(x1) uconstr(x2) uconstr(x3) uconstr(x4) ")"
    uconstr(x5) uconstr(x6) ")" "with" constr(pat) :=
  wp_send_core (eexists x1; eexists x2; eexists x3; eexists x4; eexists x5;
                eexists x6) with pat.
Tactic Notation "wp_send" "(" uconstr(x1) uconstr(x2) uconstr(x3) uconstr(x4) ")"
    uconstr(x5) uconstr(x6) uconstr(x7) ")" "with" constr(pat) :=
  wp_send_core (eexists x1; eexists x2; eexists x3; eexists x4; eexists x5;
                eexists x6; eexists x7) with pat.
Tactic Notation "wp_send" "(" uconstr(x1) uconstr(x2) uconstr(x3) uconstr(x4) ")"
    uconstr(x5) uconstr(x6) uconstr(x7) uconstr(x8) ")" "with" constr(pat) :=
  wp_send_core (eexists x1; eexists x2; eexists x3; eexists x4; eexists x5;
                eexists x6; eexists x7; eexists x8) with pat.

Lemma tac_wp_branch `{!proto_chanG Σ, !heapG Σ} Δ i j K
    c p P1 P2 (p1 p2 : iProto Σ) Φ :
  envs_lookup i Δ = Some (false, c ↣ p)%I →
  ProtoNormalize false p [] (p1 <{P1}&{P2}> p2) →
  let Δ' := envs_delete false i false Δ in
  (∀ b : bool,
    match envs_app false
        (Esnoc (Esnoc Enil j (if b then P1 else P2)) i (c ↣ (if b then p1 else p2))) Δ' with
    | Some Δ'' => envs_entails Δ'' (WP fill K (of_val #b) {{ Φ }})
    | None => False
    end) →
  envs_entails Δ (WP fill K (recv c) {{ Φ }}).
Proof.
  rewrite envs_entails_eq /ProtoNormalize /= right_id=> ? Hp HΦ.
  rewrite envs_lookup_sound //; simpl. rewrite -Hp.
  rewrite -wp_bind. eapply bi.wand_apply; [by eapply branch_spec|f_equiv].
  rewrite -bi.later_intro; apply bi.forall_intro=> b.
  specialize (HΦ b). destruct (envs_app _ _) as [Δ'|] eqn:HΔ'=> //.
  rewrite envs_app_sound //; simpl. by rewrite right_id HΦ.
Qed.

Tactic Notation "wp_branch_core" "as" tactic3(tac1) tactic3(tac2) :=
  let solve_mapsto _ :=
    let c := match goal with |- _ = Some (_, (?c ↣ _)%I) => c end in
    iAssumptionCore || fail "wp_branch: cannot find" c "↣ ? @ ?" in
  wp_pures;
  let Hnew := iFresh in
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
    first
      [reshape_expr e ltac:(fun K e' => eapply (tac_wp_branch _ _ Hnew K))
      |fail 1 "wp_branch: cannot find 'recv' in" e];
    [solve_mapsto ()
       |iSolveTC || fail 1 "wp_send: protocol not of the shape <&>"
    |pm_reduce; intros []; [tac1 Hnew|tac2 Hnew]; wp_finish]
  | _ => fail "wp_branch: not a 'wp'"
  end.

Tactic Notation "wp_branch" "as" constr(pat1) "|" constr(pat2) :=
  wp_branch_core as (fun H => iDestructHyp H as pat1) (fun H => iDestructHyp H as pat2).
Tactic Notation "wp_branch" "as" "%" intropattern(pat1) "|" constr(pat2) :=
  wp_branch_core as (fun H => iPure H as pat1) (fun H => iDestructHyp H as pat2).
Tactic Notation "wp_branch" "as" constr(pat1) "|" "%" intropattern(pat2) :=
  wp_branch_core as (fun H => iDestructHyp H as pat1) (fun H => iPure H as pat2).
Tactic Notation "wp_branch" "as" "%" intropattern(pat1) "|" "%" intropattern(pat2) :=
  wp_branch_core as (fun H => iPure H as pat1) (fun H => iPure H as pat2).
Tactic Notation "wp_branch" := wp_branch as %_ | %_.

Lemma tac_wp_select `{!proto_chanG Σ, !heapG Σ} Δ neg i js K
    c (b : bool) p P1 P2 (p1 p2 : iProto Σ) Φ :
  envs_lookup i Δ = Some (false, c ↣ p)%I →
  ProtoNormalize false p [] (p1 <{P1}+{P2}> p2) →
  let Δ' := envs_delete false i false Δ in
  match envs_split (if neg is true then Right else Left) js Δ' with
  | Some (Δ1,Δ2) =>
     match envs_app false (Esnoc Enil i (c ↣ if b then p1 else p2)) Δ2 with
     | Some Δ2' =>
        envs_entails Δ1 (if b then P1 else P2) ∧
        envs_entails Δ2' (WP fill K (of_val #()) {{ Φ }})
     | None => False
     end
  | None => False
  end →
  envs_entails Δ (WP fill K (send c #b) {{ Φ }}).
Proof.
  rewrite envs_entails_eq /ProtoNormalize /= right_id=> ? Hp HΦ.
  rewrite envs_lookup_sound //; simpl. rewrite -Hp.
  rewrite -wp_bind. eapply bi.wand_apply; [by eapply select_spec|].
  rewrite -assoc; f_equiv.
  destruct (envs_split _ _ _) as [[Δ1 Δ2]|] eqn:? => //.
  destruct (envs_app _ _ _) as [Δ2'|] eqn:? => //.
  rewrite envs_split_sound //; rewrite (envs_app_sound Δ2) //; simpl.
  destruct HΦ as [-> ->]. by rewrite -bi.later_intro right_id.
Qed.

Tactic Notation "wp_select" "with" constr(pat) :=
  let solve_mapsto _ :=
    let c := match goal with |- _ = Some (_, (?c ↣ _)%I) => c end in
    iAssumptionCore || fail "wp_select: cannot find" c "↣ ? @ ?" in
  let solve_done d :=
    lazymatch d with
    | true =>
       done ||
       let Q := match goal with |- envs_entails _ ?Q => Q end in
       fail "wp_select: cannot solve" Q "using done"
    | false => idtac
    end in
  lazymatch spec_pat.parse pat with
  | [SGoal (SpecGoal GSpatial ?neg ?Hs_frame ?Hs ?d)] =>
     let Hs' := eval cbv in (if neg then Hs else Hs_frame ++ Hs) in
     wp_pures;
     lazymatch goal with
     | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
       first
         [reshape_expr e ltac:(fun K e' => eapply (tac_wp_select _ neg _ Hs' K))
         |fail 1 "wp_select: cannot find 'send' in" e];
       [solve_mapsto ()
       |iSolveTC || fail 1 "wp_select: protocol not of the shape <+>"
       |pm_reduce;
        lazymatch goal with
        | |- False => fail "wp_select:" Hs' "not fresh"
        | _ => split;[iFrame Hs_frame; solve_done d|wp_finish]
        end]
     | _ => fail "wp_select: not a 'wp'"
     end
  | _ => fail "wp_select: only a single goal spec pattern supported"
  end.

Tactic Notation "wp_select" := wp_select with "[//]".
