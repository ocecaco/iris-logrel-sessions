From iris.heap_lang Require Export lifting metatheory.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode lib.par lib.spin_lock.
From iris.algebra Require Import agree frac csum excl frac_auth.
From actris.channel Require Import proto_channel channel proofmode.
From logrel_heaplang_sessions Require Export lty ltyping basic arr chan chan_proto.

Definition prog : val := λ: "c",
  let: "lock" := newlock #() in
  let: "p" := (
    acquire "lock";;
    let: "x1" := recv "c" in
    release "lock";;
    "x1"
  ) ||| (
    acquire "lock";;
    let: "x2" := recv "c" in
    release "lock";;
    "x2"
  ) in "p".

Section GhostState.
  Class fracG Σ := { frac_inG :> inG Σ fracR }.
  Definition fracΣ : gFunctors := #[GFunctor fracR].
  Instance subG_fracΣ {Σ} : subG fracΣ Σ → fracG Σ.
  Proof. solve_inG. Qed.
End GhostState.

Section Double.
  Context `{heapG Σ, proto_chanG Σ, fracG Σ, spawnG Σ}.

  Definition proto_begin : iProto Σ :=
    (<?> x1 : Z, MSG #x1; <?> x2 : Z, MSG #x2; END)%proto.

  Definition chan_inv (c : val) (γ : gname) : iProp Σ :=
    ((c ↣ <?> x1 : Z, MSG #x1; <?> x2 : Z, MSG #x2; END) ∨
     (own γ (1/2)%Qp ∗ c ↣ <?> x2 : Z, MSG #x2; END) ∨
     (own γ 1%Qp ∗ c ↣ END))%I.

  Lemma wp_prog (N : namespace) (c : val):
    {{{ ▷ (c ↣ proto_begin) }}} prog c {{{ v, RET v; ∃ k1 k2 : Z, ⌜v = (#k1, #k2)%V⌝ }}}.
  Proof.
    iIntros (Φ) "Hc HΦ".
    rewrite /prog.

    iMod (own_alloc 1%Qp) as (γ) "[Hcredit1 Hcredit2]".
    { done. }

    (* Create lock *)
    wp_apply (newlock_spec N (chan_inv c γ) with "[Hc]").
    { iLeft. iFrame "Hc". }
    iIntros (lk γlk) "#Hlock".
    wp_pures.

    (* Fork into two threads *)
    wp_bind (par _ _).
    wp_apply (wp_par (λ v, ∃ k : Z, ⌜v = #k⌝)%I (λ v, ∃ k : Z, ⌜v = #k⌝)%I with "[Hcredit1] [Hcredit2]").
    - (* Acquire lock *)
      wp_apply (acquire_spec with "Hlock").
      iIntros "[Hlocked Hc]". wp_pures.
      iDestruct "Hc" as "[Hc|[Hc|Hc]]".
      + wp_recv (x1) as "_". wp_pures.
        wp_apply (release_spec with "[Hlocked Hcredit1 Hc]").
        { iFrame "Hlock Hlocked". iRight. iLeft. iFrame "Hcredit1 Hc". }
        iIntros "_". wp_pures.
        by iExists x1.
      + iDestruct "Hc" as "[Hcredit2 Hc]".
        wp_recv (x1) as "_". wp_pures.
        iCombine "Hcredit1 Hcredit2" as "Hcredit".
        wp_apply (release_spec with "[Hlocked Hcredit Hc]").
        { iFrame "Hlock Hlocked". iRight. iRight. iFrame "Hcredit Hc". }
        iIntros "_". wp_pures.
        by iExists x1.
      + iDestruct "Hc" as "[Hcredit2 Hc]".
        iCombine "Hcredit1 Hcredit2" as "Hcredit".
        iExFalso. iDestruct (own_valid with "Hcredit") as "%".
        done.
    - (* Acquire lock *)
      wp_apply (acquire_spec with "Hlock").
      iIntros "[Hlocked Hc]". wp_pures.
      iDestruct "Hc" as "[Hc|[Hc|Hc]]".
      + wp_recv (x1) as "_". wp_pures.
        wp_apply (release_spec with "[Hlocked Hcredit2 Hc]").
        { iFrame "Hlock Hlocked". iRight. iLeft. iFrame "Hcredit2 Hc". }
        iIntros "_". wp_pures.
        by iExists x1.
      + iDestruct "Hc" as "[Hcredit1 Hc]".
        wp_recv (x1) as "_". wp_pures.
        iCombine "Hcredit1 Hcredit2" as "Hcredit".
        wp_apply (release_spec with "[Hlocked Hcredit Hc]").
        { iFrame "Hlock Hlocked". iRight. iRight. iFrame "Hcredit Hc". }
        iIntros "_". wp_pures.
        by iExists x1.
      + iDestruct "Hc" as "[Hcredit1 Hc]".
        iCombine "Hcredit1 Hcredit2" as "Hcredit".
        iExFalso. iDestruct (own_valid with "Hcredit") as "%".
        done.
    - iIntros (x1 x2) "[Hx1 Hx2]".
      iModIntro. wp_pures.
      iApply "HΦ".
      iDestruct "Hx1" as (k1) "->".
      iDestruct "Hx2" as (k2) "->".
      by iExists k1, k2.
  Qed.

  Lemma lty_prog (N : namespace):
    ∅ ⊨ prog : chan (<??> lty_int; <??> lty_int; END) → (lty_int * lty_int).
  Proof.
    iIntros (vs) "_ /=".
    wp_apply wp_value.
    iModIntro. iIntros (c) "Hc".
    wp_apply (wp_prog N with "[Hc]").
    { iModIntro. admit. }
    iIntros (r) "Hr".
    iDestruct "Hr" as (k1 k2) "->".
    iExists #k1, #k2. iSplit=> //.
    iSplit; by eauto.
  Admitted.

End Double.
