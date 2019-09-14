From actris.channel Require Export channel.
From actris.channel Require Import proto_model.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import proofmode notation.
From iris.algebra Require Import auth excl.
From actris.utils Require Import auth_excl.
Export action.

Definition start_chan : val := λ: "f",
  let: "cc" := new_chan #() in
  Fork ("f" (Snd "cc"));; Fst "cc".

(** Camera setup *)
Class proto_chanG Σ := {
  proto_chanG_chanG :> chanG Σ;
  proto_chanG_authG :> auth_exclG (laterO (proto val (iPreProp Σ) (iPreProp Σ))) Σ;
}.

Definition proto_chanΣ := #[
  chanΣ;
  GFunctor (authRF(optionURF (exclRF (laterOF (protoOF val idOF idOF)))))
].
Instance subG_chanΣ {Σ} : subG proto_chanΣ Σ → proto_chanG Σ.
Proof. intros [??%subG_auth_exclG]%subG_inv. constructor; apply _. Qed.

(** Types *)
Definition iProto Σ := proto val (iProp Σ) (iProp Σ).
Delimit Scope proto_scope with proto.
Bind Scope proto_scope with iProto.

(** Operators *)
Definition iProto_end_def {Σ} : iProto Σ := proto_end.
Definition iProto_end_aux : seal (@iProto_end_def). by eexists. Qed.
Definition iProto_end := iProto_end_aux.(unseal).
Definition iProto_end_eq : @iProto_end = @iProto_end_def := iProto_end_aux.(seal_eq).
Arguments iProto_end {_}.

Program Definition iProto_message_def {Σ} {TT : tele} (a : action)
    (pc : TT → val * iProp Σ * iProto Σ) : iProto Σ :=
  proto_message a (λ v, λne f, ∃ x : TT,
    (* Need the laters to make [iProto_message] contractive *)
    ⌜ v = (pc x).1.1 ⌝ ∗
    ▷ (pc x).1.2 ∗
    f (Next (pc x).2))%I.
Next Obligation. solve_proper. Qed.
Definition iProto_message_aux : seal (@iProto_message_def). by eexists. Qed.
Definition iProto_message := iProto_message_aux.(unseal).
Definition iProto_message_eq : @iProto_message = @iProto_message_def := iProto_message_aux.(seal_eq).
Arguments iProto_message {_ _} _ _%proto.
Instance: Params (@iProto_message) 3.

Notation "< a > x1 .. xn , 'MSG' v {{ P } } ; p" :=
  (iProto_message
    a
    (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn, (v%V,P%I,p%proto)) ..))
  (at level 20, a at level 10, x1 binder, xn binder, v at level 20, P, p at level 200) : proto_scope.
Notation "< a > x1 .. xn , 'MSG' v ; p" :=
  (iProto_message
    a
    (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn, (v%V,True%I,p%proto)) ..))
  (at level 20, a at level 10, x1 binder, xn binder, v at level 20, p at level 200) : proto_scope.
Notation "< a > 'MSG' v {{ P } } ; p" :=
  (iProto_message
    a
    (tele_app (TT:=TeleO) (v%V,P%I,p%proto)))
  (at level 20, a at level 10, v at level 20, P, p at level 200) : proto_scope.
Notation "< a > 'MSG' v ; p" :=
  (iProto_message
    a
    (tele_app (TT:=TeleO) (v%V,True%I,p%proto)))
  (at level 20, a at level 10, v at level 20, p at level 200) : proto_scope.

Notation "<!> x1 .. xn , 'MSG' v {{ P } } ; p" :=
  (iProto_message
    Send
    (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn, (v%V,P%I,p%proto)) ..))
  (at level 20, x1 binder, xn binder, v at level 20, P, p at level 200) : proto_scope.
Notation "<!> x1 .. xn , 'MSG' v ; p" :=
  (iProto_message
    Send
    (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn, (v%V,True%I,p%proto)) ..))
  (at level 20, x1 binder, xn binder, v at level 20, p at level 200) : proto_scope.
Notation "<!> 'MSG' v {{ P } } ; p" :=
  (iProto_message
    (TT:=TeleO)
    Send
    (tele_app (TT:=TeleO) (v%V,P%I,p%proto)))
  (at level 20, v at level 20, P, p at level 200) : proto_scope.
Notation "<!> 'MSG' v ; p" :=
  (iProto_message
    (TT:=TeleO)
    Send
    (tele_app (TT:=TeleO) (v%V,True%I,p%proto)))
  (at level 20, v at level 20, p at level 200) : proto_scope.

Notation "<?> x1 .. xn , 'MSG' v {{ P } } ; p" :=
  (iProto_message
    Receive
    (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn, (v%V,P%I,p%proto)) ..))
  (at level 20, x1 binder, xn binder, v at level 20, P, p at level 200) : proto_scope.
Notation "<?> x1 .. xn , 'MSG' v ; p" :=
  (iProto_message
    Receive
    (tele_app (TT:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. )) $
                       λ x1, .. (λ xn, (v%V,True%I,p%proto)) ..))
  (at level 20, x1 binder, xn binder, v at level 20, p at level 200) : proto_scope.
Notation "<?> 'MSG' v {{ P } } ; p" :=
  (iProto_message
    Receive
    (tele_app (TT:=TeleO) (v%V,P%I,p%proto)))
  (at level 20, v at level 20, P, p at level 200) : proto_scope.
Notation "<?> 'MSG' v ; p" :=
  (iProto_message
    Receive
    (tele_app (TT:=TeleO) (v%V,True%I,p%proto)))
  (at level 20, v at level 20, p at level 200) : proto_scope.

Notation "'END'" := iProto_end : proto_scope.

(** Dual *)
Definition iProto_dual {Σ} (p : iProto Σ) : iProto Σ :=
  proto_map action_dual cid cid p.
Arguments iProto_dual {_} _%proto.
Instance: Params (@iProto_dual) 1.
Definition iProto_dual_if {Σ} (d : bool) (p : iProto Σ) : iProto Σ :=
  if d then iProto_dual p else p.
Arguments iProto_dual_if {_} _ _%proto.
Instance: Params (@iProto_dual_if) 2.

(** Branching *)
Definition iProto_branch {Σ} (a : action) (P1 P2 : iProp Σ)
    (p1 p2 : iProto Σ) : iProto Σ :=
  (<a> (b : bool), MSG #b {{ if b then P1 else P2 }}; if b then p1 else p2)%proto.
Typeclasses Opaque iProto_branch.
Arguments iProto_branch {_} _ _%I _%I _%proto _%proto.
Instance: Params (@iProto_branch) 2.
Infix "<{ P1 }+{ P2 }>" := (iProto_branch Send P1 P2) (at level 85) : proto_scope.
Infix "<{ P1 }&{ P2 }>" := (iProto_branch Receive P1 P2) (at level 85) : proto_scope.
Infix "<+{ P2 }>" := (iProto_branch Send True P2) (at level 85) : proto_scope.
Infix "<&{ P2 }>" := (iProto_branch Receive True P2) (at level 85) : proto_scope.
Infix "<{ P1 }+>" := (iProto_branch Send P1 True) (at level 85) : proto_scope.
Infix "<{ P1 }&>" := (iProto_branch Receive P1 True) (at level 85) : proto_scope.
Infix "<+>" := (iProto_branch Send True True) (at level 85) : proto_scope.
Infix "<&>" := (iProto_branch Receive True True) (at level 85) : proto_scope.

(** Append *)
Definition iProto_app {Σ} (p1 p2 : iProto Σ) : iProto Σ := proto_app p1 p2.
Arguments iProto_app {_} _%proto _%proto.
Instance: Params (@iProto_app) 1.
Infix "<++>" := iProto_app (at level 60) : proto_scope.

(** Auxiliary definitions and invariants *)
Fixpoint proto_interp `{!proto_chanG Σ} (vs : list val) (p1 p2 : iProto Σ) : iProp Σ :=
  match vs with
  | [] => p1 ≡ iProto_dual p2
  | v :: vs => ∃ pc p2',
     p2 ≡ (proto_message Receive pc)%proto ∗
     (∀ f : laterO (iProto Σ) -n> iProp Σ, f (Next p2') -∗ pc v f) ∗
     ▷ proto_interp vs p1 p2'
  end%I.
Arguments proto_interp {_ _} _ _%proto _%proto : simpl nomatch.

Record proto_name := ProtName {
  proto_c_name : chan_name;
  proto_l_name : gname;
  proto_r_name : gname
}.

Definition to_proto_auth_excl `{!proto_chanG Σ} (p : iProto Σ) :=
  to_auth_excl (Next (proto_map id iProp_fold iProp_unfold p)).

Definition proto_own_frag `{!proto_chanG Σ} (γ : proto_name) (s : side)
    (p : iProto Σ) : iProp Σ :=
  own (side_elim s proto_l_name proto_r_name γ) (◯ to_proto_auth_excl p)%I.

Definition proto_own_auth `{!proto_chanG Σ} (γ : proto_name) (s : side)
    (p : iProto Σ) : iProp Σ :=
  own (side_elim s proto_l_name proto_r_name γ) (● to_proto_auth_excl p)%I.

Definition proto_inv `{!proto_chanG Σ} (γ : proto_name) : iProp Σ :=
  (∃ l r pl pr,
    chan_own (proto_c_name γ) Left l ∗
    chan_own (proto_c_name γ) Right r ∗
    proto_own_auth γ Left pl ∗
    proto_own_auth γ Right pr ∗
    ▷ ((⌜r = []⌝ ∗ proto_interp l pl pr) ∨
       (⌜l = []⌝ ∗ proto_interp r pr pl)))%I.

Definition protoN := nroot .@ "proto".

Definition mapsto_proto_def `{!proto_chanG Σ, !heapG Σ}
    (c : val) (p : iProto Σ) : iProp Σ :=
  (∃ s (c1 c2 : val) γ,
    ⌜ c = side_elim s c1 c2 ⌝ ∗
    proto_own_frag γ s p ∗ is_chan protoN (proto_c_name γ) c1 c2 ∗ inv protoN (proto_inv γ))%I.
Definition mapsto_proto_aux : seal (@mapsto_proto_def). by eexists. Qed.
Definition mapsto_proto {Σ pΣ hΣ} := mapsto_proto_aux.(unseal) Σ pΣ hΣ.
Definition mapsto_proto_eq : @mapsto_proto = @mapsto_proto_def := mapsto_proto_aux.(seal_eq).
Arguments mapsto_proto {_ _ _} _ _%proto.
Instance: Params (@mapsto_proto) 4 := {}.

Notation "c ↣ p" := (mapsto_proto c p)
  (at level 20, format "c  ↣  p").

Section proto.
  Context `{!proto_chanG Σ, !heapG Σ}.
  Implicit Types p : iProto Σ.
  Implicit Types TT : tele.

  (** Non-expansiveness of operators *)
  Lemma iProto_message_contractive {TT} a
      (pc1 pc2 : TT → val * iProp Σ * iProto Σ) n :
    (∀.. x, (pc1 x).1.1 = (pc2 x).1.1) →
    (∀.. x, dist_later n ((pc1 x).1.2) ((pc2 x).1.2)) →
    (∀.. x, dist_later n ((pc1 x).2) ((pc2 x).2)) →
    iProto_message a pc1 ≡{n}≡ iProto_message a pc2.
  Proof.
    rewrite !tforall_forall=> Hv HP Hp.
    rewrite iProto_message_eq /iProto_message_def.
    f_equiv=> v f /=. apply bi.exist_ne=> x.
    repeat (apply Hv || apply HP || apply Hp || f_contractive || f_equiv).
  Qed.
  Lemma iProto_message_ne {TT} a
      (pc1 pc2 : TT → val * iProp Σ * iProto Σ) n :
    (∀.. x, (pc1 x).1.1 = (pc2 x).1.1) →
    (∀.. x, (pc1 x).1.2 ≡{n}≡ (pc2 x).1.2) →
    (∀.. x, (pc1 x).2 ≡{n}≡ (pc2 x).2) →
    iProto_message a pc1 ≡{n}≡ iProto_message a pc2.
  Proof.
    rewrite !tforall_forall=> Hv HP Hp.
    apply iProto_message_contractive; apply tforall_forall; eauto using dist_dist_later.
  Qed.
  Lemma iProto_message_proper {TT} a
      (pc1 pc2 : TT → val * iProp Σ * iProto Σ) :
    (∀.. x, (pc1 x).1.1 = (pc2 x).1.1) →
    (∀.. x, (pc1 x).1.2 ≡ (pc2 x).1.2) →
    (∀.. x, (pc1 x).2 ≡ (pc2 x).2) →
    iProto_message a pc1 ≡ iProto_message a pc2.
  Proof.
    rewrite !tforall_forall=> Hv HP Hp. apply equiv_dist => n.
    apply iProto_message_ne; apply tforall_forall=> x; by try apply equiv_dist.
  Qed.

  Global Instance iProto_branch_contractive n a :
    Proper (dist_later n ==> dist_later n ==>
            dist_later n ==> dist_later n ==> dist n) (@iProto_branch Σ a).
  Proof.
    intros p1 p1' Hp1 p2 p2' Hp2 P1 P1' HP1 P2 P2' HP2.
    apply iProto_message_contractive=> /= -[] //.
  Qed.
  Global Instance iProto_branch_ne n a :
    Proper (dist n ==> dist n ==> dist n ==> dist n ==> dist n) (@iProto_branch Σ a).
  Proof.
    intros p1 p1' Hp1 p2 p2' Hp2 P1 P1' HP1 P2 P2' HP2.
    by apply iProto_message_ne=> /= -[].
  Qed.
  Global Instance iProto_branch_proper a :
    Proper ((≡) ==> (≡) ==> (≡) ==> (≡) ==> (≡)) (@iProto_branch Σ a).
  Proof.
    intros p1 p1' Hp1 p2 p2' Hp2 P1 P1' HP1 P2 P2' HP2.
    by apply iProto_message_proper=> /= -[].
  Qed.

  (** Dual *)
  Global Instance iProto_dual_ne : NonExpansive (@iProto_dual Σ).
  Proof. solve_proper. Qed.
  Global Instance iProto_dual_proper : Proper ((≡) ==> (≡)) (@iProto_dual Σ).
  Proof. apply (ne_proper _). Qed.
  Global Instance iProto_dual_if_ne d : NonExpansive (@iProto_dual_if Σ d).
  Proof. solve_proper. Qed.
  Global Instance iProto_dual_if_proper d : Proper ((≡) ==> (≡)) (@iProto_dual_if Σ d).
  Proof. apply (ne_proper _). Qed.

  Global Instance iProto_dual_involutive : Involutive (≡) (@iProto_dual Σ).
  Proof.
    intros p. rewrite /iProto_dual -proto_map_compose -{2}(proto_map_id p).
    apply: proto_map_ext=> //. by intros [].
  Qed.

  Lemma iProto_dual_end : iProto_dual (Σ:=Σ) END ≡ END%proto.
  Proof. by rewrite iProto_end_eq /iProto_dual proto_map_end. Qed.
  Lemma iProto_dual_message {TT} a (pc : TT → val * iProp Σ * iProto Σ) :
    iProto_dual (iProto_message a pc)
    ≡ iProto_message (action_dual a) (prod_map id iProto_dual ∘ pc).
  Proof.
    rewrite /iProto_dual iProto_message_eq /iProto_message_def proto_map_message.
    by f_equiv=> v f /=.
  Qed.

  Lemma iProto_dual_branch a P1 P2 p1 p2 :
    iProto_dual (iProto_branch a P1 P2 p1 p2)
    ≡ iProto_branch (action_dual a) P1 P2 (iProto_dual p1) (iProto_dual p2).
  Proof.
    rewrite /iProto_branch iProto_dual_message /=.
    by apply iProto_message_proper=> /= -[].
  Qed.

  (** Append *)
  Global Instance iProto_app_ne : NonExpansive2 (@iProto_app Σ).
  Proof. apply _. Qed.
  Global Instance iProto_app_proper : Proper ((≡) ==> (≡) ==> (≡)) (@iProto_app Σ).
  Proof. apply (ne_proper_2 _). Qed.

  Lemma iProto_app_message {TT} a (pc : TT → val * iProp Σ * iProto Σ) p2 :
    (iProto_message a pc <++> p2)%proto ≡ iProto_message a (prod_map id (flip iProto_app p2) ∘ pc).
  Proof.
    rewrite /iProto_app iProto_message_eq /iProto_message_def proto_app_message.
    by f_equiv=> v f /=.
  Qed.

  Global Instance iProto_app_end_l : LeftId (≡) END%proto (@iProto_app Σ).
  Proof.
    intros p. by rewrite iProto_end_eq /iProto_end_def /iProto_app proto_app_end_l.
  Qed.
  Global Instance iProto_app_end_r : RightId (≡) END%proto (@iProto_app Σ).
  Proof.
    intros p. by rewrite iProto_end_eq /iProto_end_def /iProto_app proto_app_end_r.
  Qed.
  Global Instance iProto_app_assoc : Assoc (≡) (@iProto_app Σ).
  Proof. intros p1 p2 p3. by rewrite /iProto_app proto_app_assoc. Qed.

  Lemma iProto_app_branch a P1 P2 p1 p2 q :
    (iProto_branch a P1 P2 p1 p2 <++> q)%proto
    ≡ (iProto_branch a P1 P2 (p1 <++> q) (p2 <++> q))%proto.
  Proof.
    rewrite /iProto_branch iProto_app_message.
    by apply iProto_message_proper=> /= -[].
  Qed.

  Lemma iProto_dual_app p1 p2 :
    iProto_dual (p1 <++> p2) ≡ (iProto_dual p1 <++> iProto_dual p2)%proto.
  Proof. by rewrite /iProto_dual /iProto_app proto_map_app. Qed.

  (** Auxiliary definitions and invariants *)
  Global Instance proto_interp_ne : NonExpansive2 (proto_interp vs).
  Proof. induction vs; solve_proper. Qed.
  Global Instance proto_interp_proper vs : Proper ((≡) ==> (≡) ==> (≡)) (proto_interp vs).
  Proof. apply (ne_proper_2 _). Qed.

  Global Instance to_proto_auth_excl_ne : NonExpansive to_proto_auth_excl.
  Proof. solve_proper. Qed.
  Global Instance proto_own_ne γ s : NonExpansive (proto_own_frag γ s).
  Proof. solve_proper. Qed.
  Global Instance mapsto_proto_ne c : NonExpansive (mapsto_proto c).
  Proof. rewrite mapsto_proto_eq. solve_proper. Qed.
  Global Instance mapsto_proto_proper c : Proper ((≡) ==> (≡)) (mapsto_proto c).
  Proof. apply (ne_proper _). Qed.

  Lemma proto_own_auth_agree γ s p p' :
    proto_own_auth γ s p -∗ proto_own_frag γ s p' -∗ ▷ (p ≡ p').
  Proof.
    iIntros "Hauth Hfrag".
    iDestruct (own_valid_2 with "Hauth Hfrag") as "Hvalid".
    iDestruct (to_auth_excl_valid with "Hvalid") as "Hvalid".
    iDestruct (bi.later_eq_1 with "Hvalid") as "Hvalid"; iNext.
    assert (∀ p,
      proto_map id iProp_unfold iProp_fold (proto_map id iProp_fold iProp_unfold p) ≡ p) as help.
    { intros p''. rewrite -proto_map_compose -{2}(proto_map_id p'').
      apply proto_map_ext=> // pc /=; by rewrite iProp_fold_unfold. }
    rewrite -{2}(help p). iRewrite "Hvalid". by rewrite help.
  Qed.

  Lemma proto_own_auth_update γ s p p' p'' :
    proto_own_auth γ s p -∗ proto_own_frag γ s p' ==∗
    proto_own_auth γ s p'' ∗ proto_own_frag γ s p''.
  Proof.
    iIntros "Hauth Hfrag".
    iDestruct (own_update_2 with "Hauth Hfrag") as "H".
    { eapply (auth_update _ _ (to_proto_auth_excl p'') (to_proto_auth_excl p'')).
      apply option_local_update. by apply exclusive_local_update. }
    by rewrite own_op.
  Qed.

  Lemma proto_interp_send v vs pc p1 p2 :
    proto_interp vs (proto_message Send pc) p2 -∗
    (∀ f : laterO (iProto Σ) -n> iProp Σ, f (Next p1) -∗ pc v f) -∗
    proto_interp (vs ++ [v]) p1 p2.
  Proof.
    iIntros "Heval Hc". iInduction vs as [|v' vs] "IH" forall (p2); simpl.
    - iDestruct "Heval" as "#Heval".
      iExists _, (iProto_dual p1). iSplit.
      { rewrite -{2}(involutive iProto_dual p2). iRewrite -"Heval".
        rewrite /iProto_dual. by rewrite proto_map_message. }
      iSplit.
      { iIntros (f) "Hf /=". by iApply "Hc". }
      by rewrite involutive.
    - iDestruct "Heval" as (pc' p2') "(Heq & Hc' & Heval)".
      iExists pc', p2'. iFrame "Heq Hc'". iNext. iApply ("IH" with "Heval Hc").
  Qed.

  Lemma proto_interp_recv v vs p1 pc :
     proto_interp (v :: vs) p1 (proto_message Receive pc) -∗ ∃ p2,
       (∀ f : laterO (iProto Σ) -n> iProp Σ, f (Next p2) -∗ pc v f) ∗
       ▷ proto_interp vs p1 p2.
  Proof.
    simpl. iDestruct 1 as (pc' p2) "(Heq & Hc & Hp2)". iExists p2. iFrame "Hp2".
    iDestruct (@proto_message_equivI with "Heq") as "[_ Heq]".
    iSpecialize ("Heq" $! v). rewrite bi.ofe_morO_equivI.
    iIntros (f) "Hfp2". iRewrite ("Heq" $! f). by iApply "Hc".
  Qed.

  Lemma proto_interp_False p pc v vs :
    proto_interp (v :: vs) p (proto_message Send pc) -∗ False.
  Proof.
    simpl. iDestruct 1 as (pc' p2') "[Heq _]".
    by iDestruct (@proto_message_equivI with "Heq") as "[% _]".
  Qed.

  Lemma proto_interp_nil p1 p2 : proto_interp [] p1 p2 -∗ p1 ≡ iProto_dual p2.
  Proof. done. Qed.

  Arguments proto_interp : simpl never.

  (** The actual specs *)
  Lemma proto_init E cγ c1 c2 p :
    is_chan protoN cγ c1 c2 -∗
    chan_own cγ Left [] -∗ chan_own cγ Right [] ={E}=∗
    c1 ↣ p ∗ c2 ↣ iProto_dual p.
  Proof.
    iIntros "#Hcctx Hcol Hcor".
    iMod (own_alloc (● (to_proto_auth_excl p) ⋅
                     ◯ (to_proto_auth_excl p))) as (lγ) "[Hlsta Hlstf]".
    { by apply auth_both_valid_2. }
    iMod (own_alloc (● (to_proto_auth_excl (iProto_dual p)) ⋅
                     ◯ (to_proto_auth_excl (iProto_dual p)))) as (rγ) "[Hrsta Hrstf]".
    { by apply auth_both_valid_2. }
    pose (ProtName cγ lγ rγ) as pγ.
    iMod (inv_alloc protoN _ (proto_inv pγ) with "[-Hlstf Hrstf Hcctx]") as "#Hinv".
    { iNext. rewrite /proto_inv. eauto 10 with iFrame. }
    iModIntro. rewrite mapsto_proto_eq. iSplitL "Hlstf".
    - iExists Left, c1, c2, pγ; iFrame; auto.
    - iExists Right, c1, c2, pγ; iFrame; auto.
  Qed.

  (** Accessor style lemmas *)
  Lemma proto_send_acc {TT} E c (pc : TT → val * iProp Σ * iProto Σ) :
    ↑protoN ⊆ E →
    c ↣ iProto_message Send pc -∗ ∃ s c1 c2 γ,
      ⌜ c = side_elim s c1 c2 ⌝ ∗
      is_chan protoN (proto_c_name γ) c1 c2 ∗ |={E,E∖↑protoN}=> ∃ vs,
        chan_own (proto_c_name γ) s vs ∗
        ▷ ∀ (x : TT),
           (pc x).1.2 -∗
           chan_own (proto_c_name γ) s (vs ++ [(pc x).1.1]) ={E∖↑protoN,E}=∗
           c ↣ (pc x).2.
  Proof.
    iIntros (?). rewrite {1}mapsto_proto_eq iProto_message_eq.
    iDestruct 1 as (s c1 c2 γ ->) "[Hstf #[Hcctx Hinv]]".
    iExists s, c1, c2, γ. iSplit; first done. iFrame "Hcctx".
    iInv protoN as (l r pl pr) "(>Hclf & >Hcrf & Hstla & Hstra & Hinv')" "Hclose".
    (* TODO: refactor to avoid twice nearly the same proof *)
    iModIntro. destruct s.
    - iExists _.
      iIntros "{$Hclf} !>" (x) "HP Hclf".
      iRename "Hstf" into "Hstlf".
      iDestruct (proto_own_auth_agree with "Hstla Hstlf") as "#Heq".
      iMod (proto_own_auth_update _ _ _ _ (pc x).2
        with "Hstla Hstlf") as "[Hstla Hstlf]".
      iMod ("Hclose" with "[-Hstlf]") as "_".
      { iNext. iExists _,_,_,_. iFrame "Hcrf Hstra Hstla Hclf". iLeft.
        iRewrite "Heq" in "Hinv'".
        iDestruct "Hinv'" as "[[-> Heval]|[-> Heval]]".
        { iSplit=> //. iApply (proto_interp_send with "Heval [HP]").
          iIntros (f) "Hf /=". iExists x. by iFrame. }
        destruct r as [|vr r]; last first.
        { iDestruct (proto_interp_False with "Heval") as %[]. }
        iSplit; first done; simpl. iRewrite (proto_interp_nil with "Heval").
        iApply (proto_interp_send _ [] with "[] [HP]").
        { by rewrite /proto_interp involutive. }
        iIntros (f) "Hf /=". iExists x. by iFrame. }
      iModIntro. rewrite mapsto_proto_eq. iExists Left, c1, c2, γ. iFrame; auto.
    - iExists _.
      iIntros "{$Hcrf} !>" (x) "HP Hcrf".
      iRename "Hstf" into "Hstrf".
      iDestruct (proto_own_auth_agree with "Hstra Hstrf") as "#Heq".
      iMod (proto_own_auth_update _ _ _ _ (pc x).2
        with "Hstra Hstrf") as "[Hstra Hstrf]".
      iMod ("Hclose" with "[-Hstrf]") as "_".
      { iNext. iExists _, _, _, _. iFrame "Hcrf Hstra Hstla Hclf". iRight.
        iRewrite "Heq" in "Hinv'".
        iDestruct "Hinv'" as "[[-> Heval]|[-> Heval]]"; last first.
        { iSplit=> //. iApply (proto_interp_send with "Heval [HP]").
          iIntros (f) "Hf /=". iExists x. by iFrame. }
        destruct l as [|vl l]; last first.
        { iDestruct (proto_interp_False with "Heval") as %[]. }
        iSplit; first done; simpl. iRewrite (proto_interp_nil with "Heval").
        iApply (proto_interp_send _ [] with "[] [HP]").
        { by rewrite /proto_interp involutive. }
        iIntros (f) "Hf /=". iExists x. by iFrame. }
      iModIntro. rewrite mapsto_proto_eq. iExists Right, c1, c2, γ. iFrame; auto.
  Qed.

  Lemma proto_recv_acc {TT} E c (pc : TT → val * iProp Σ * iProto Σ) :
    ↑protoN ⊆ E →
    c ↣ iProto_message Receive pc -∗ ∃ s c1 c2 γ,
      ⌜ c = side_elim s c2 c1 ⌝ ∗
      is_chan protoN (proto_c_name γ) c1 c2 ∗ |={E,E∖↑protoN}=> ∃ vs,
        chan_own (proto_c_name γ) s vs ∗
        ▷ ((chan_own (proto_c_name γ) s vs ={E∖↑protoN,E}=∗
             c ↣ iProto_message Receive pc) ∧
           (∀ v vs',
             ⌜ vs = v :: vs' ⌝ -∗
             chan_own (proto_c_name γ) s vs' ={E∖↑protoN,E}=∗ ▷ ▷ ∃ x : TT,
             ⌜ v = (pc x).1.1 ⌝ ∗ c ↣ (pc x).2 ∗ (pc x).1.2)).
  Proof.
    iIntros (?). rewrite {1}mapsto_proto_eq iProto_message_eq.
    iDestruct 1 as (s c1 c2 γ ->) "[Hstf #[Hcctx Hinv]]".
    iExists (side_elim s Right Left), c1, c2, γ. iSplit; first by destruct s.
    iFrame "Hcctx".
    iInv protoN as (l r pl pr) "(>Hclf & >Hcrf & Hstla & Hstra & Hinv')" "Hclose".
    iExists (side_elim s r l). iModIntro.
    (* TODO: refactor to avoid twice nearly the same proof *)
    destruct s; simpl.
    - iIntros "{$Hcrf} !>".
      iRename "Hstf" into "Hstlf".
      iDestruct (proto_own_auth_agree with "Hstla Hstlf") as "#Heq".
      iSplit.
      + iIntros "Hown".
        iMod ("Hclose" with "[-Hstlf]") as "_".
        { iNext. iExists l, r, _, _. iFrame. }
        iModIntro. rewrite mapsto_proto_eq.
        iExists Left, c1, c2, γ. by iFrame "Hcctx ∗ Hinv".
      + iIntros (v vs ->) "Hown".
        iDestruct "Hinv'" as "[[>% _]|[> -> Heval]]"; first done.
        iAssert (▷ proto_interp (v :: vs) pr (iProto_message_def Receive pc))%I
          with "[Heval]" as "Heval".
        { iNext. by iRewrite "Heq" in "Heval". }
        iDestruct (proto_interp_recv with "Heval") as (q) "[Hf Heval]".
        iMod (proto_own_auth_update _ _ _ _ q with "Hstla Hstlf") as "[Hstla Hstlf]".
        iMod ("Hclose" with "[-Hstlf Hf]") as %_.
        { iExists _, _,_ ,_. eauto 10 with iFrame. }
        iIntros "!> !>".
        set (f lp := (∃ q, lp ≡ Next q ∧ c1 ↣ q)%I).
        assert (NonExpansive f) by solve_proper.
        iDestruct ("Hf" $! (OfeMor f) with "[Hstlf]") as (x) "(Hv & HP & Hf) /=".
        { iExists q. iSplit; first done. rewrite mapsto_proto_eq.
          iExists Left, c1, c2, γ. iFrame; auto. }
        iDestruct "Hf" as (q') "[#Hq Hc]". iModIntro.
        iExists x. iFrame "Hv HP". by iRewrite "Hq".
    - iIntros "{$Hclf} !>".
      iRename "Hstf" into "Hstrf".
      iDestruct (proto_own_auth_agree with "Hstra Hstrf") as "#Heq".
      iSplit.
      + iIntros "Hown".
        iMod ("Hclose" with "[-Hstrf]") as "_".
        { iNext. iExists l, r, _, _. iFrame. }
        iModIntro. rewrite mapsto_proto_eq.
        iExists Right, c1, c2, γ. by iFrame "Hcctx ∗ Hinv".
      + iIntros (v vs ->) "Hown".
        iDestruct "Hinv'" as "[[>-> Heval]|[>% _]]"; last done.
        iAssert (▷ proto_interp (v :: vs) pl (iProto_message_def Receive pc))%I
          with "[Heval]" as "Heval".
        { iNext. by iRewrite "Heq" in "Heval". }
        iDestruct (proto_interp_recv with "Heval") as (q) "[Hf Heval]".
        iMod (proto_own_auth_update _ _ _ _ q with "Hstra Hstrf") as "[Hstra Hstrf]".
        iMod ("Hclose" with "[-Hstrf Hf]") as %_.
        { iExists _, _, _, _. eauto 10 with iFrame. }
        iIntros "!> !>".
        set (f lp := (∃ q, lp ≡ Next q ∧ c2 ↣ q)%I).
        assert (NonExpansive f) by solve_proper.
        iDestruct ("Hf" $! (OfeMor f) with "[Hstrf]") as (x) "(Hv & HP & Hf) /=".
        { iExists q. iSplit; first done. rewrite mapsto_proto_eq.
          iExists Right, c1, c2, γ. iFrame; auto. }
        iDestruct "Hf" as (q') "[#Hq Hc]". iModIntro.
        iExists x. iFrame "Hv HP". by iRewrite "Hq".
  Qed.

  (** Specifications of send and receive *)
  Lemma new_chan_proto_spec :
    {{{ True }}}
      new_chan #()
    {{{ c1 c2, RET (c1,c2); (∀ p, |={⊤}=> c1 ↣ p ∗ c2 ↣ iProto_dual p) }}}.
  Proof.
    iIntros (Ψ _) "HΨ". iApply wp_fupd. wp_apply new_chan_spec=> //.
    iIntros (c1 c2 γ) "(Hc & Hl & Hr)". iApply "HΨ"; iIntros "!>" (p).
    iApply (proto_init ⊤ γ c1 c2 p with "Hc Hl Hr").
  Qed.

  Lemma start_chan_proto_spec p Ψ (f : val) :
    ▷ (∀ c, c ↣ iProto_dual p -∗ WP f c {{ _, True }}) -∗
    ▷ (∀ c, c ↣ p -∗ Ψ c) -∗
    WP start_chan f {{ Ψ }}.
  Proof.
    iIntros "Hfork HΨ". wp_lam.
    wp_apply (new_chan_proto_spec with "[//]"); iIntros (c1 c2) "Hc".
    iMod ("Hc" $! p) as "[Hc1 Hc2]".
    wp_apply (wp_fork with "[Hfork Hc2]").
    { iNext. wp_apply ("Hfork" with "Hc2"). }
    wp_pures. iApply ("HΨ" with "Hc1").
  Qed.

  Lemma send_proto_spec_packed {TT} c (pc : TT → val * iProp Σ * iProto Σ) (x : TT) :
    {{{ c ↣ iProto_message Send pc ∗ (pc x).1.2 }}}
      send c (pc x).1.1
    {{{ RET #(); c ↣ (pc x).2 }}}.
  Proof.
    iIntros (Ψ) "[Hp Hf] HΨ".
    iDestruct (proto_send_acc ⊤ with "Hp") as (γ s c1 c2 ->) "[#Hc Hvs]"; first done.
    iApply (send_spec with "[$]"). iMod "Hvs" as (vs) "[Hch H]".
    iModIntro. iExists vs. iFrame "Hch".
    iIntros "!> Hvs". iApply "HΨ".
    iMod ("H" $! x with "Hf Hvs"); auto.
  Qed.

  Lemma send_proto_spec {TT} Ψ c v (pc : TT → val * iProp Σ * iProto Σ) :
    c ↣ iProto_message Send pc -∗
    (∃.. x : TT,
      ⌜ v = (pc x).1.1 ⌝ ∗ (pc x).1.2 ∗ ▷ (c ↣ (pc x).2 -∗ Ψ #())) -∗
    WP send c v {{ Ψ }}.
  Proof.
    iIntros "Hc H". iDestruct (bi_texist_exist with "H") as (x ->) "[HP HΨ]".
    by iApply (send_proto_spec_packed with "[$]").
  Qed.

  Lemma try_recv_proto_spec_packed {TT} c (pc : TT → val * iProp Σ * iProto Σ) :
    {{{ c ↣ iProto_message Receive pc }}}
      try_recv c
    {{{ v, RET v; (⌜v = NONEV⌝ ∧ c ↣ iProto_message Receive pc) ∨
                  (∃ x : TT, ⌜v = SOMEV ((pc x).1.1)⌝ ∗ c ↣ (pc x).2 ∗ (pc x).1.2) }}}.
  Proof.
    iIntros (Ψ) "Hp HΨ".
    iDestruct (proto_recv_acc ⊤ with "Hp") as (γ s c1 c2 ->) "[#Hc Hvs]"; first done.
    wp_apply (try_recv_spec with "[$]"). iSplit.
    - iMod "Hvs" as (vs) "[Hch [H _]]".
      iIntros "!> !>". iMod ("H" with "Hch") as "Hch". iApply "HΨ"; auto.
    - iMod "Hvs" as (vs) "[Hch [_ H]]".
      iIntros "!>". iExists vs. iIntros "{$Hch} !>" (v vs' ->) "Hch".
      iMod ("H" with "[//] Hch") as "H". iIntros "!> !> !>".
      iDestruct "H" as (x ->) "H". iApply "HΨ"; auto.
  Qed.

  Lemma recv_proto_spec_packed {TT} c (pc : TT → val * iProp Σ * iProto Σ) :
    {{{ c ↣ iProto_message Receive pc }}}
      recv c
    {{{ x, RET (pc x).1.1; c ↣ (pc x).2 ∗ (pc x).1.2 }}}.
  Proof.
    iIntros (Ψ) "Hp HΨ".
    iDestruct (proto_recv_acc ⊤ with "Hp") as (γ s c1 c2 ->) "[#Hc Hvs]"; first done.
    wp_apply (recv_spec with "[$]"). iMod "Hvs" as (vs) "[Hch [_ H]]".
    iModIntro. iExists vs. iFrame "Hch". iIntros "!>" (v vs' ->) "Hvs'".
    iMod ("H" with "[//] Hvs'") as "H"; iIntros "!> !> !>".
    iDestruct "H" as (x ->) "H". by iApply "HΨ".
  Qed.

  Lemma recv_proto_spec {TT} Ψ c (pc : TT → val * iProp Σ * iProto Σ) :
    c ↣ iProto_message Receive pc -∗
    ▷ (∀.. x : TT, c ↣ (pc x).2 -∗ (pc x).1.2 -∗ Ψ (pc x).1.1) -∗
    WP recv c {{ Ψ }}.
  Proof.
    iIntros "Hc H". iApply (recv_proto_spec_packed with "[$]").
    iIntros "!>" (x) "[Hc HP]". iDestruct (bi_tforall_forall with "H") as "H".
    iApply ("H" with "[$] [$]").
  Qed.

  (** Branching *)
  Lemma select_spec c (b : bool) P1 P2 p1 p2 :
    {{{ c ↣ (p1 <{P1}+{P2}> p2) ∗ if b then P1 else P2 }}}
      send c #b
    {{{ RET #(); c ↣ (if b then p1 else p2) }}}.
  Proof.
    rewrite /iProto_branch. iIntros (Ψ) "[Hc HP] HΨ".
    iApply (send_proto_spec with "Hc"); simpl; eauto with iFrame.
  Qed.

  Lemma branch_spec c P1 P2 p1 p2 :
    {{{ c ↣ (p1 <{P1}&{P2}> p2) }}}
      recv c
    {{{ b, RET #b; c ↣ (if b : bool then p1 else p2) ∗ if b then P1 else P2 }}}.
  Proof.
    rewrite /iProto_branch. iIntros (Ψ) "Hc HΨ".
    iApply (recv_proto_spec with "Hc"); simpl.
    iIntros "!>" (b) "Hc HP". iApply "HΨ". iFrame.
  Qed.
End proto.
