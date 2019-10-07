From iris.heap_lang Require Export lifting metatheory.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode lib.par lib.spin_lock.
From iris.algebra Require Import agree frac csum excl.

Definition prog_simpler (prize : loc) (l : loc) : expr :=
  (
    if: !#l = #0
    then FAA #prize #1
    else Skip
  ) ||| (
    if: !#l ≠ #0
    then FAA #prize #1
    else Skip
  );;
  #().

Section Proofs.
  Context `{heapG Σ}.

  Lemma wp_prog_simpler (N : namespace) (prize l : loc) (k : nat):
    (inv N (l ↦ #k) -∗
     {{{ prize ↦ #0 }}}
       prog_simpler prize l
     {{{ RET #(); prize ↦ #1 }}})%I.
  Proof.
    iIntros "#Hinv" (Φ) "!> Hprize HΦ".
    rewrite /prog_simpler.
    wp_pures.
    wp_bind (par _ _)%E.
    wp_apply (wp_par (λ _, True)%I (λ _, True)%I).
    - (* Thread 1 *)
      wp_bind (! _)%E.
      iInv "Hinv" as ">Hl" "Hclose".
      wp_load.
      iMod ("Hclose" with "Hl").
      iModIntro.

      wp_pures. case_bool_decide; wp_pures.
      + (* n = 0 *)
        admit.
      + (* n ≠ 0 *)
        done.

    - (* Thread 2 *)
      wp_bind (! _)%E.
      iInv "Hinv" as ">Hl" "Hclose".
      wp_load.
      iMod ("Hclose" with "Hl").
      iModIntro.

      wp_pures. case_bool_decide; wp_pures.
      + (* n = 0 *)
        done.
      + (* n ≠ 0 *)
        admit.

    - iIntros (? ?) "[_ _]". iModIntro.
      wp_pures.
      admit.
  Admitted.

End Proofs.