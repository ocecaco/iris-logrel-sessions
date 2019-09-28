From iris_examples.logrel_heaplang_sessions Require Export lty env.
From iris.heap_lang Require Export lifting metatheory.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.

(* The semantic typing judgment *)
Definition ltyped `{heapG Σ}
    (Γ : gmap string (lty Σ)) (e : expr) (A : lty Σ) : iProp Σ :=
  (□ ∀ vs, env_ltyped Γ vs -∗ WP subst_map vs e {{ A }})%I.

Notation "Γ ⊨ e : A" := (ltyped Γ e A)
  (at level 100, e at next level, A at level 200).
