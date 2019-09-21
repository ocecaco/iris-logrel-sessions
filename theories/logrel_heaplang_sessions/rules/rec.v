  Definition lty_rec1 (C : ltyC Σ -n> ltyC Σ) (rec : lty Σ) : lty Σ := Lty (λ w,
    ▷ C rec w)%I.
  Instance lty_rec1_contractive C : Contractive (lty_rec1 C).
  Proof. solve_contractive. Qed.
  Definition lty_rec (C : ltyC Σ -n> ltyC Σ) : lty Σ := fixpoint (lty_rec1 C).

(* To unfold a recursive type, we need to take a step. We thus define the
unfold operator to be the identity function. *)
Definition rec_unfold : val := λ: "x", "x".

    Global Instance lty_rec_ne n : Proper (dist n ==> dist n) (@lty_rec Σ).
  Proof. intros C C' HC. apply fixpoint_ne. solve_proper. Qed.

    Lemma lty_rec_unfold (C : ltyC Σ -n> ltyC Σ) : lty_rec C ≡ lty_rec1 C (lty_rec C).
  Proof. apply fixpoint_unfold. Qed.
