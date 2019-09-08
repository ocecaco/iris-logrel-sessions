From iris.heap_lang Require Export lifting metatheory.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.

(* The domain of semantic types: persistent Iris predicates over values *)
Record lty Σ := Lty {
  lty_car :> val → iProp Σ;
}.
Arguments Lty {_} _%I.
Arguments lty_car {_} _ _ : simpl never.
Bind Scope lty_scope with lty.
Delimit Scope lty_scope with lty.

(* The COFE structure on semantic types *)
Section lty_ofe.
  Context `{Σ : gFunctors}.

  (* Equality of semantic types is extensional equality *)
  Instance lty_equiv : Equiv (lty Σ) := λ A B, ∀ w, A w ≡ B w.
  Instance lty_dist : Dist (lty Σ) := λ n A B, ∀ w, A w ≡{n}≡ B w.

  (* OFE and COFE structure is taken from isomorphism with val -d> iProp Σ *)
  Lemma lty_ofe_mixin : OfeMixin (lty Σ).
  Proof. by apply (iso_ofe_mixin (lty_car : _ → val -d> _)). Qed.
  Canonical Structure ltyC := OfeT (lty Σ) lty_ofe_mixin.

  Global Instance lty_cofe : Cofe ltyC.
  Proof.
    by apply (iso_cofe (@Lty _ : (val -d> _) → ltyC) lty_car).
  Qed.

  Global Instance lty_inhabited : Inhabited (lty Σ) := populate (Lty inhabitant).

  Global Instance lty_car_ne n : Proper (dist n ==> (=) ==> dist n) lty_car.
  Proof. by intros A A' ? w ? <-. Qed.
  Global Instance lty_car_proper : Proper ((≡) ==> (=) ==> (≡)) lty_car.
  Proof. by intros A A' ? w ? <-. Qed.
End lty_ofe.

Arguments ltyC : clear implicits.

(* Typing for operators *)
Class LTyUnboxed `{heapG Σ} (A : lty Σ) :=
  lty_unboxed v : A v -∗ ⌜ val_is_unboxed v ⌝.

Class LTyUnOp `{heapG Σ} (op : un_op) (A B : lty Σ) :=
  lty_un_op v : A v -∗ ∃ w, ⌜ un_op_eval op v = Some w ⌝ ∗ B w.

Class LTyBinOp `{heapG Σ} (op : bin_op) (A1 A2 B : lty Σ) :=
  lty_bin_op v1 v2 : A1 v1 -∗ A2 v2 -∗ ∃ w, ⌜ bin_op_eval op v1 v2 = Some w ⌝ ∗ B w.

(* The type formers *)
Section types.
  Context `{heapG Σ}.

  Definition lty_unit : lty Σ := Lty (λ w, ⌜ w = #() ⌝%I).
  Definition lty_bool : lty Σ := Lty (λ w, ∃ b : bool, ⌜ w = #b ⌝)%I.
  Definition lty_int : lty Σ := Lty (λ w, ∃ n : Z, ⌜ w = #n ⌝)%I.

  Definition lty_arr (A1 A2 : lty Σ) : lty Σ := Lty (λ w,
    ∀ v, A1 v -∗ WP App w v {{ A2 }})%I.

  Definition lty_prod (A1 A2 : lty Σ) : lty Σ := Lty (λ w,
    ∃ w1 w2, ⌜w = PairV w1 w2⌝ ∗ A1 w1 ∗ A2 w2)%I.

  Definition lty_sum (A1 A2 : lty Σ) : lty Σ := Lty (λ w,
    (∃ w1, ⌜w = InjLV w1⌝ ∗ A1 w1) ∨ (∃ w2, ⌜w = InjRV w2⌝ ∗ A2 w2))%I.

  Definition lty_forall (C : lty Σ → lty Σ) : lty Σ := Lty (λ w,
    ∀ A : lty Σ, WP w #() {{ w, C A w }})%I.
  Definition lty_exist (C : lty Σ → lty Σ) : lty Σ := Lty (λ w,
    ∃ A : lty Σ, C A w)%I.

  Definition lty_rec1 (C : ltyC Σ -n> ltyC Σ) (rec : lty Σ) : lty Σ := Lty (λ w,
    ▷ C rec w)%I.
  Instance lty_rec1_contractive C : Contractive (lty_rec1 C).
  Proof. solve_contractive. Qed.
  Definition lty_rec (C : ltyC Σ -n> ltyC Σ) : lty Σ := fixpoint (lty_rec1 C).

  Definition tyN := nroot .@ "ty".
  Definition lty_ref (A : lty Σ) : lty Σ := Lty (λ w,
    ∃ l : loc, ⌜w = #l⌝ ∗ (∃ v, l ↦ v ∗ A v))%I.
End types.

(* Nice notations *)
Notation "()" := lty_unit : lty_scope.
Infix "→" := lty_arr : lty_scope.
Infix "*" := lty_prod : lty_scope.
Infix "+" := lty_sum : lty_scope.
Notation "∀ A1 .. An , C" :=
  (lty_forall (λ A1, .. (lty_forall (λ An, C%lty)) ..)) : lty_scope.
Notation "∃ A1 .. An , C" :=
  (lty_exist (λ A1, .. (lty_exist (λ An, C%lty)) ..)) : lty_scope.
Notation "'ref' A" := (lty_ref A) : lty_scope.

(* The semantic typing judgment *)
Definition env_ltyped `{heapG Σ} (Γ : gmap string (lty Σ))
    (vs : gmap string val) : iProp Σ :=
  ([∗ map] i ↦ A;v ∈ Γ; vs, lty_car A v)%I.
Definition ltyped  `{heapG Σ}
    (Γ : gmap string (lty Σ)) (e : expr) (A : lty Σ) : iProp Σ :=
  (∀ vs, env_ltyped Γ vs -∗ WP subst_map vs e {{ A }})%I.
Notation "Γ ⊨ e : A" := (ltyped Γ e A)
  (at level 100, e at next level, A at level 200).

(* Context combining *)
Definition env_compatible `{heapG Σ} Γ1 Γ2 := (∀ vs, env_ltyped (Γ1 ∪ Γ2) vs -∗ env_ltyped Γ1 vs ∗ env_ltyped Γ2 vs)%I.

(* To unfold a recursive type, we need to take a step. We thus define the
unfold operator to be the identity function. *)
Definition rec_unfold : val := λ: "x", "x".

Section types_properties.
  Context `{heapG Σ}.
  Implicit Types A B : lty Σ.
  Implicit Types C : lty Σ → lty Σ.

  (* Boring stuff: all type formers are non-expansive *)
  Global Instance lty_prod_ne : NonExpansive2 (@lty_prod Σ).
  Proof. solve_proper. Qed.
  Global Instance lty_sum_ne : NonExpansive2 (@lty_sum Σ).
  Proof. solve_proper. Qed.
  Global Instance lty_arr_ne : NonExpansive2 (@lty_arr Σ _).
  Proof. solve_proper. Qed.
  Global Instance lty_forall_ne n : Proper (pointwise_relation _ (dist n) ==> dist n) (@lty_forall Σ _).
  Proof. solve_proper. Qed.
  Global Instance lty_exist_ne n : Proper (pointwise_relation _ (dist n) ==> dist n) (@lty_exist Σ).
  Proof. solve_proper. Qed.
  Global Instance lty_rec_ne n : Proper (dist n ==> dist n) (@lty_rec Σ).
  Proof. intros C C' HC. apply fixpoint_ne. solve_proper. Qed.
  Global Instance lty_ref_ne : NonExpansive2 (@lty_ref Σ _).
  Proof. solve_proper. Qed.

  Lemma lty_rec_unfold (C : ltyC Σ -n> ltyC Σ) : lty_rec C ≡ lty_rec1 C (lty_rec C).
  Proof. apply fixpoint_unfold. Qed.

  (* Environments *)
  Lemma env_ltyped_lookup Γ vs x A :
    Γ !! x = Some A →
    env_ltyped Γ vs -∗ ∃ v, ⌜ vs !! x = Some v ⌝ ∗ A v.
  Proof.
    iIntros (HΓx) "HΓ".
    iDestruct (big_sepM2_lookup_1 with "HΓ") as (v ?) "H"; eauto.
  Qed.
  Lemma env_ltyped_insert Γ vs x A v :
    A v -∗ env_ltyped Γ vs -∗
    env_ltyped (binder_insert x A Γ) (binder_insert x v vs).
  Proof.
    destruct x as [|x]=> /=; first by auto.
    iIntros "HA HΓ".
    by iApply (big_sepM2_insert_2 with "[HA] HΓ").
  Qed.

  (* Unboxed types *)
  Global Instance lty_unit_unboxed : LTyUnboxed ().
  Proof. by iIntros (v ->). Qed.
  Global Instance lty_bool_unboxed : LTyUnboxed lty_bool.
  Proof. iIntros (v). by iDestruct 1 as (b) "->". Qed.
  Global Instance lty_int_unboxed : LTyUnboxed lty_int.
  Proof. iIntros (v). by iDestruct 1 as (i) "->". Qed.
  Global Instance lty_ref_unboxed A : LTyUnboxed (ref A).
  Proof. iIntros (v). by iDestruct 1 as (i ->) "?". Qed.

  (* Operator typing *)
  Global Instance lty_bin_op_eq A : LTyUnboxed A → LTyBinOp EqOp A A lty_bool.
  Proof.
    iIntros (? v1 v2) "A1 _". rewrite /bin_op_eval /lty_car /=.
    iDestruct (lty_unboxed with "A1") as %Hunb.
    rewrite decide_True; last solve_vals_compare_safe.
    eauto.
  Qed.
  Global Instance lty_bin_op_arith op :
    TCElemOf op [PlusOp; MinusOp; MultOp; QuotOp; RemOp;
                 AndOp; OrOp; XorOp; ShiftLOp; ShiftROp] →
    LTyBinOp op lty_int lty_int lty_int.
  Proof.
    iIntros (? v1 v2); iDestruct 1 as (i1) "->"; iDestruct 1 as (i2) "->".
    repeat match goal with H : TCElemOf _ _ |- _ => inversion_clear H end;
      rewrite /lty_car /=; eauto.
  Qed.
  Global Instance lty_bin_op_compare op :
    TCElemOf op [LeOp; LtOp] →
    LTyBinOp op lty_int lty_int lty_bool.
  Proof.
    iIntros (? v1 v2); iDestruct 1 as (i1) "->"; iDestruct 1 as (i2) "->".
    repeat match goal with H : TCElemOf _ _ |- _ => inversion_clear H end;
      rewrite /lty_car /=; eauto.
  Qed.
  Global Instance lty_bin_op_bool op :
    TCElemOf op [AndOp; OrOp; XorOp] →
    LTyBinOp op lty_bool lty_bool lty_bool.
  Proof.
    iIntros (? v1 v2); iDestruct 1 as (i1) "->"; iDestruct 1 as (i2) "->".
    repeat match goal with H : TCElemOf _ _ |- _ => inversion_clear H end;
      rewrite /lty_car /=; eauto.
  Qed.

  (* The semantic typing rules *)
  Lemma ltyped_var Γ (x : string) A : Γ !! x = Some A → Γ ⊨ x : A.
  Proof.
    iIntros (HΓx vs) "HΓ /=".
    iDestruct (env_ltyped_lookup with "HΓ") as (v ->) "HA"; first done.
    by iApply wp_value.
  Qed.

  Lemma ltyped_unit Γ : Γ ⊨ #() : ().
  Proof. iIntros (vs) "_ /=". by iApply wp_value. Qed.
  Lemma ltyped_bool Γ (b : bool) : Γ ⊨ #b : lty_bool.
  Proof. iIntros (vs) "_ /=". iApply wp_value. rewrite /lty_car /=. eauto. Qed.
  Lemma ltyped_nat Γ (n : Z) : Γ ⊨ #n : lty_int.
  Proof. iIntros (vs) "_ /=". iApply wp_value. rewrite /lty_car /=. eauto. Qed.

  Lemma ltyped_app Γ1 Γ2 e1 e2 A1 A2 :
    env_compatible Γ1 Γ2 -∗ (Γ1 ⊨ e1 : A1 → A2) -∗ (Γ2 ⊨ e2 : A1) -∗ Γ1 ∪ Γ2 ⊨ e1 e2 : A2.
  Proof.
    iIntros "Hcompat H1 H2" (vs) "HΓ /=".
    iSpecialize ("Hcompat" with "HΓ").
    iDestruct "Hcompat" as "[HΓ1 HΓ2]".
    wp_apply (wp_wand with "(H2 [HΓ2 //])").
    iIntros (v) "HA1".
    wp_apply (wp_wand with "(H1 [HΓ1 //])").
    iIntros (f) "Hf". iApply ("Hf" $! v with "HA1").
  Qed.

  Lemma ltyped_lam Γ x e A1 A2 :
    (binder_insert x A1 Γ ⊨ e : A2) -∗
    Γ ⊨ (λ: x, e) : A1 → A2.
  Proof.
    iIntros "H" (vs) "HΓ /=". wp_pures.
    iIntros (v) "HA1". wp_pures.
    iSpecialize ("H" $! (binder_insert x v vs) with "[HΓ HA1]").
    { iApply (env_ltyped_insert with "[HA1 //] [HΓ //]"). }
    (* TODO: What does the question mark mean here? *)
    destruct x as [|x]; rewrite /= -?subst_map_insert //.
  Qed.

End types_properties.
