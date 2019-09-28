From iris_examples.logrel_heaplang_sessions Require Export lty ltyping.
From iris.heap_lang Require Export lifting metatheory.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.

Section types.
  Context `{heapG Σ}.

  Definition lty_unit : lty Σ := Lty (λ w, ⌜ w = #() ⌝%I).
  Definition lty_bool : lty Σ := Lty (λ w, ∃ b : bool, ⌜ w = #b ⌝)%I.
  Definition lty_int : lty Σ := Lty (λ w, ∃ n : Z, ⌜ w = #n ⌝)%I.

End types.

Notation "()" := lty_unit : lty_scope.

Section properties.
  Context `{heapG Σ}.

  (* TODO: Why doesn't Coq automatically infer the Σ from the context here? *)
  Global Instance lty_unit_unboxed : @LTyUnboxed Σ ().
  Proof. by iIntros (v ->). Qed.
  Global Instance lty_bool_unboxed : @LTyUnboxed Σ lty_bool.
  Proof. iIntros (v). by iDestruct 1 as (b) "->". Qed.
  Global Instance lty_int_unboxed : @LTyUnboxed Σ lty_int.
  Proof. iIntros (v). by iDestruct 1 as (i) "->". Qed.

  Lemma ltyped_unit Γ : Γ ⊨ #() : ().
  Proof. iIntros (vs) "!> _ /=". by iApply wp_value. Qed.
  Lemma ltyped_bool Γ (b : bool) : Γ ⊨ #b : lty_bool.
  Proof. iIntros (vs) "!> _ /=". iApply wp_value. rewrite /lty_car /=. eauto. Qed.
  Lemma ltyped_nat Γ (n : Z) : Γ ⊨ #n : lty_int.
  Proof. iIntros (vs) "!> _ /=". iApply wp_value. rewrite /lty_car /=. eauto. Qed.
End properties.
