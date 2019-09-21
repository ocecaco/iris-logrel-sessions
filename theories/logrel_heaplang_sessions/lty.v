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
Class LTyUnboxed `{Σ : gFunctors} (A : lty Σ) :=
  lty_unboxed v : A v -∗ ⌜ val_is_unboxed v ⌝.

Class LTyUnOp `{Σ : gFunctors} (op : un_op) (A B : lty Σ) :=
  lty_un_op v : A v -∗ ∃ w, ⌜ un_op_eval op v = Some w ⌝ ∗ B w.

Class LTyBinOp `{Σ : gFunctors} (op : bin_op) (A1 A2 B : lty Σ) :=
  lty_bin_op v1 v2 : A1 v1 -∗ A2 v2 -∗ ∃ w, ⌜ bin_op_eval op v1 v2 = Some w ⌝ ∗ B w.

(* Copy types *)
Class LTyCopy `{Σ : gFunctors} (A : lty Σ) :=
  lty_copy v :> Persistent (A v).
