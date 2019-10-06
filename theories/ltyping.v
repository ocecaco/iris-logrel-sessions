From logrel_heaplang_sessions Require Export lty env.
From iris.heap_lang Require Export lifting metatheory.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.

(* The semantic typing judgment *)
(* This is a Prop, which means that we cannot have typing judgments
that are contingent on some resources being in the current context. *)
Definition ltyped `{heapG Σ}
    (Γ : gmap string (lty Σ)) (e : expr) (A : lty Σ) : Prop :=
  ((∀ vs, env_ltyped Γ vs -∗ WP subst_map vs e {{ A }}) : iProp Σ)%I.

Notation "Γ ⊨ e : A" := (ltyped Γ e A)
  (at level 100, e at next level, A at level 200).
