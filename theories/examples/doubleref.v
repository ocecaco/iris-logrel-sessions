From iris.heap_lang Require Export lifting metatheory.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode lib.par lib.spin_lock.
From iris.algebra Require Import agree frac csum excl.

Definition prog (prize : loc) (n m : nat) : expr :=
  let: "a" := ref #n in
  let: "b" := ref #m in
  (
    if: !"a" ≤ !"b"
    then FAA #prize #1
    else Skip
  ) ||| (
    if: !"b" < !"a"
    then FAA #prize #1
    else Skip
  );;
  #().

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

  Lemma wp_prog prize n m:
    ({{{ prize ↦ #0 }}} prog prize n m {{{ RET #(); prize ↦ #1 }}})%I.
  Proof.
    iIntros (Φ) "!> Hprize HΦ".
    rewrite /prog.
    wp_alloc a as "Ha". wp_pures.
    wp_alloc b as "Hb". wp_pures.
    iCombine "Ha Hb" as "Hab".
    iMod (inv_alloc nroot with "Hab") as "#Hinv".
    wp_pures.
    wp_bind (par _ _)%E.
    wp_apply (wp_par (λ _, True%I) (λ _, True%I)).
    - (* Thread 1 *)
      wp_bind (! _)%E.
      iInv "Hinv" as ">[Ha Hb]" "Hclose".
      wp_load.
      iMod ("Hclose" with "[Ha Hb]").
      { iModIntro. iFrame "Ha Hb". }
      iModIntro.

      wp_bind (! _)%E.
      iInv "Hinv" as ">[Ha Hb]" "Hclose".
      wp_load.
      iMod ("Hclose" with "[Ha Hb]").
      { iModIntro. iFrame "Ha Hb". }
      iModIntro.

      wp_pures. case_bool_decide; wp_pures.
      + (* n ≤ m *)
        admit.
      + (* n > m *)
        admit.

    - (* Thread 2 *)
      wp_bind (! _)%E.
      iInv "Hinv" as ">[Ha Hb]" "Hclose".
      wp_load.
      iMod ("Hclose" with "[Ha Hb]").
      { iModIntro. iFrame "Ha Hb". }
      iModIntro.

      wp_bind (! _)%E.
      iInv "Hinv" as ">[Ha Hb]" "Hclose".
      wp_load.
      iMod ("Hclose" with "[Ha Hb]").
      { iModIntro. iFrame "Ha Hb". }
      iModIntro.
      wp_pures. case_bool_decide; wp_pures.
      + (* n > m *)
        admit.
      + (* n ≤ m *)
        admit.
  Admitted.

  Lemma wp_prog_simpler (prize l : loc) (k : nat):
    ({{{ prize ↦ #0 ∗ l ↦ #k }}} prog_simpler prize l {{{ RET #(); prize ↦ #1 ∗ l ↦ #k }}})%I.
  Proof.
    iIntros (Φ) "!> [Hprize Hl] HΦ".
    iMod (inv_alloc nroot with "Hl") as "#Hinv".
    rewrite /prog_simpler.
    wp_pures.
    wp_bind (par _ _)%E.
    wp_apply (wp_par (λ _, True%I) (λ _, True%I)).
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
    - (* Thread 2*)
      wp_bind (! _)%E.
      iInv "Hinv" as ">Hl" "Hclose".
      wp_load.
      iMod ("Hclose" with "Hl").
      iModIntro.

      wp_pures. case_bool_decide; wp_pures.
      + (* n ≠ 0 *)
        done.
      + (* n = 0 *)
        admit.

    - iIntros (? ?) "[_ _]". iModIntro.
      wp_pures.
      admit.
  Admitted.

End Proofs.
