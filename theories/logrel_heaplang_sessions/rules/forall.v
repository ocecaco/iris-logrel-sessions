From iris_examples.logrel_heaplang_sessions Require Export lty.
From iris.heap_lang Require Export lifting metatheory.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.

Section types.
  Context `{heapG Σ}.

  Definition lty_forall (C : lty Σ → lty Σ) : lty Σ := Lty (λ w,
    ∀ A : lty Σ, WP w #() {{ w, C A w }})%I.
End types.

Notation "∀ A1 .. An , C" :=
  (lty_forall (λ A1, .. (lty_forall (λ An, C%lty)) ..)) : lty_scope.

Section properties.
  Context `{heapG Σ}.

  Global Instance lty_forall_ne n : Proper (pointwise_relation _ (dist n) ==> dist n) (@lty_forall Σ _).
  Proof. solve_proper. Qed.
End properties.
