From iris_examples.logrel_heaplang_sessions Require Export lty.
From iris.heap_lang Require Export lifting metatheory.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode.

Section types.
  Context `{heapG Σ}.

  Definition lty_any : lty Σ := Lty (λ w, True%I).
End types.

Notation any := lty_any.
