From stdpp Require Export prelude.
From Coq Require Export SetoidPermutation.

Fixpoint group_insert {A} `{EqDecision K} (i : K) (x : A)
    (ixss : list (K * list A)) : list (K * list A) :=
  match ixss with
  | [] => [(i,[x])]
  | (j,xs) :: ixss =>
     if decide (i = j) then (j,x::xs) :: ixss else (j,xs) :: group_insert i x ixss
  end.

Fixpoint group {A} `{EqDecision K} (ixs : list (K * A)) : list (K * list A) :=
  match ixs with
  | [] => []
  | (i,x) :: ixs => group_insert i x (group ixs)
  end.

Instance: Params (@group_insert) 5.
Instance: Params (@group) 3.

Local Infix "≡ₚₚ" :=
  (PermutationA (prod_relation (=) (≡ₚ))) (at level 70, no associativity) : stdpp_scope.
Notation "(≡ₚₚ)" := (PermutationA (prod_relation (=) (≡ₚ))) (only parsing) : stdpp_scope.

Section group.
  Context {A : Type} `{EqDecision K}.
  Implicit Types i : K.
  Implicit Types xs : list A.
  Implicit Types ixs : list (K * A).
  Implicit Types ixss : list (K * list A).

  Lemma elem_of_group_insert j i x ixss :
    j ∈ (group_insert i x ixss).*1 → i = j ∨ j ∈ ixss.*1.
  Proof.
    induction ixss as [|[i' x'] ixss IH];
      repeat (simplify_eq/= || case_decide); set_solver.
  Qed.

  Lemma group_insert_commute i1 i2 x1 x2 ixss :
    group_insert i1 x1 (group_insert i2 x2 ixss) ≡ₚₚ group_insert i2 x2 (group_insert i1 x1 ixss).
  Proof.
    induction ixss as [|[j x] ixss IH]; repeat (simplify_eq/= || case_decide);
      repeat constructor; done.
 Qed.

  Lemma group_insert_nodup i x ixss :
    NoDup ixss.*1 → NoDup (group_insert i x ixss).*1.
  Proof.
    pose proof @elem_of_group_insert.
    induction ixss as [|[j xs] ixss IH]; csimpl; inversion_clear 1;
      repeat (simplify_eq/= || case_decide); repeat constructor; set_solver.
  Qed.
  Lemma group_nodup ixs : NoDup (group ixs).*1.
  Proof.
    induction ixs as [|[i x] ixs IH]; csimpl;
      auto using group_insert_nodup, NoDup_nil_2.
  Qed.

  Lemma grouped_permutation_elem_of ixss1 ixss2 i :
    ixss1 ≡ₚₚ ixss2 → i ∈ ixss1.*1 → i ∈ ixss2.*1.
  Proof.
    induction 1 as [|[i1 xs1] [i2 xs2] ixss1 ixss2 [??]|[i1 xs1] [i2 xs2] ixss|];
      set_solver.
  Qed.

  Lemma grouped_permutation_nodup ixss1 ixss2 :
    ixss1 ≡ₚₚ ixss2 → NoDup ixss1.*1 → NoDup ixss2.*1.
  Proof.
    pose proof @grouped_permutation_elem_of.
    induction 1 as [|[i1 xs1] [i2 xs2] ixss1 ixss2 [??]|[i1 xs1] [i2 xs2] ixss|];
      csimpl; rewrite ?NoDup_cons; try set_solver.
  Qed.

  Lemma group_insert_perm ixss1 ixss2 i x :
    NoDup ixss1.*1 →
    ixss1 ≡ₚₚ ixss2 → group_insert i x ixss1 ≡ₚₚ group_insert i x ixss2.
  Proof.
    induction 2 as [|[i1 xs1] [i2 xs2] ixss1 ixss2 [??]|[i1 xs1] [i2 xs2] ixss|];
      repeat match goal with
      | _ => progress (simplify_eq/= || case_decide)
      | H : NoDup (_ :: _) |- _ => inversion_clear H
      end; first [repeat constructor; by auto
                 |set_solver
                 |etrans; eauto using grouped_permutation_nodup].
  Qed.

  Global Instance group_perm : Proper ((≡ₚ) ==> (≡ₚₚ)) (@group A K _).
  Proof.
    induction 1; repeat (simplify_eq/= || case_decide || case_match);
      first [by etrans|auto using group_insert_perm, group_nodup, group_insert_commute].
  Qed.

  Lemma group_fmap (i : K) xs : xs ≠ [] → group ((i,) <$> xs) ≡ₚₚ [(i, xs)].
  Proof.
    induction xs as [|x1 [|x2 xs] IH]; intros; simplify_eq/=; try done.
    etrans.
    { apply group_insert_perm, IH; auto using group_insert_nodup, group_nodup. }
    simpl; by case_decide.
  Qed.
  Lemma group_insert_snoc ixss i x j ys :
    i ≠ j →
    group_insert i x (ixss ++ [(j, ys)]) ≡ₚₚ group_insert i x ixss ++ [(j,ys)].
  Proof.
    intros. induction ixss as [|[i' xs'] ixss IH];
      repeat (simplify_eq/= || case_decide); repeat constructor; by auto.
  Qed.
  Lemma group_snoc ixs j ys :
    j ∉ ixs.*1 → ys ≠ [] → group (ixs ++ ((j,) <$> ys)) ≡ₚₚ group ixs ++ [(j,ys)].
  Proof.
    induction ixs as [|[i x] ixs IH]; csimpl; [by auto using group_fmap|].
    rewrite ?not_elem_of_cons; intros [??]. etrans; [|by apply group_insert_snoc].
    apply group_insert_perm, IH; auto using group_nodup.
  Qed.
End group.
