  Definition lty_sum (A1 A2 : lty Σ) : lty Σ := Lty (λ w,
    (∃ w1, ⌜w = InjLV w1⌝ ∗ A1 w1) ∨ (∃ w2, ⌜w = InjRV w2⌝ ∗ A2 w2))%I.

Infix "+" := lty_sum : lty_scope.

  Global Instance lty_sum_ne : NonExpansive2 (@lty_sum Σ).
  Proof. solve_proper. Qed.
