From iris.proofmode Require Import tactics.
From iris.algebra Require Import excl auth.
From iris.base_logic.lib Require Import own.
Set Default Proof Using "Type".

Class auth_exclG (A : ofeT) (Σ : gFunctors) := AuthExclG {
  exclG_authG :> inG Σ (authR (optionUR (exclR A)));
}.

Definition auth_exclΣ (F : oFunctor) `{!oFunctorContractive F} : gFunctors :=
  #[GFunctor (authRF (optionURF (exclRF F)))].

Instance subG_auth_exclG (F : oFunctor) `{!oFunctorContractive F} {Σ} :
  subG (auth_exclΣ F) Σ → auth_exclG (F (iPreProp Σ) _) Σ.
Proof. solve_inG. Qed.

Definition to_auth_excl {A : ofeT} (a : A) : option (excl A) :=
  Excl' a.
Instance: Params (@to_auth_excl) 1.

Section auth_excl_ofe.
  Context {A : ofeT}.

  Global Instance to_auth_excl_ne : NonExpansive (@to_auth_excl A).
  Proof. solve_proper. Qed.

  Global Instance to_auth_excl_proper :
    Proper ((≡) ==> (≡)) (@to_auth_excl A).
  Proof. solve_proper. Qed.
End auth_excl_ofe.

Section auth_excl.
  Context `{!auth_exclG A Σ}.
  Implicit Types x y : A.

  Lemma to_auth_excl_valid x y :
    ✓ (● to_auth_excl x ⋅ ◯ to_auth_excl y) -∗ (x ≡ y : iProp Σ).
  Proof.
    iIntros "Hvalid".
    iDestruct (auth_both_validI with "Hvalid") as "[_ [Hle Hvalid]]"; simpl.
    iDestruct "Hle" as ([z|]) "Hy"; last first.
    - by rewrite bi.option_equivI /= excl_equivI.
    - iRewrite "Hy" in "Hvalid".
      by rewrite uPred.option_validI /= excl_validI /=.
  Qed.

  Lemma excl_eq γ x y :
    own γ (● to_auth_excl x) -∗ own γ (◯ to_auth_excl y) -∗ x ≡ y.
  Proof.
    iIntros "Hauth Hfrag".
    iDestruct (own_valid_2 with "Hauth Hfrag") as "Hvalid".
    iDestruct (to_auth_excl_valid with "Hvalid") as "$".
  Qed.

  Lemma excl_update γ x y z :
    own γ (● to_auth_excl y) -∗ own γ (◯ to_auth_excl x) ==∗
    own γ (● to_auth_excl z) ∗ own γ (◯ to_auth_excl z).
  Proof.
    iIntros "Hauth Hfrag".
    iDestruct (own_update_2 with "Hauth Hfrag") as "H".
    { eapply (auth_update _ _ (to_auth_excl z) (to_auth_excl z)).
      eapply option_local_update.
      eapply exclusive_local_update. done. }
    by rewrite own_op.
  Qed.
End auth_excl.
