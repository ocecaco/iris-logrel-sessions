From iris.heap_lang Require Export lifting metatheory.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import notation proofmode lib.par lib.spin_lock.
From iris.algebra Require Import agree frac csum excl frac_auth.
From actris.channel Require Import proto_channel channel proofmode.

Definition prog (c : val) : expr :=
  let: "lock" := newlock #() in
  (
    acquire "lock";;
    recv c;;
    release "lock"
  ) ||| (
    acquire "lock";;
    recv c;;
    release "lock"
  );;
  #().

Section GhostState.
  Definition doubleR := frac_authR natR.
  Class doubleG Σ := { double_inG :> inG Σ doubleR }.
  Definition doubleΣ : gFunctors := #[GFunctor doubleR].
  Instance subG_doubleΣ {Σ} : subG doubleΣ Σ → doubleG Σ.
  Proof. solve_inG. Qed.

  Class fracG Σ := { frac_inG :> inG Σ fracR }.
  Definition fracΣ : gFunctors := #[GFunctor fracR].
  Instance subG_fracΣ {Σ} : subG fracΣ Σ → fracG Σ.
  Proof. solve_inG. Qed.

  Definition auth (n : nat) : doubleR := ●F (n : natR).
  Definition partial (q : Qp) (n : nat) : doubleR := ◯F{q} n.
End GhostState.

Section Double.
  Context `{heapG Σ, proto_chanG Σ, doubleG Σ, fracG Σ}.

  Lemma partial_split γ n:
    own γ (partial 1 n) -∗ own γ (partial (1/2) n) ∗ own γ (partial (1/2) n).
  Proof. Admitted.

  Lemma partial_inc γ q n m:
    own γ (auth n) ∗ own γ (partial q m) ==∗ own γ (auth (n + 1)) ∗ own γ (partial q (m + 1)).
  Proof. Admitted.

  Definition proto_begin : iProto Σ :=
    (<?> x1 : nat, MSG #x1; <?> x2 : nat, MSG #x2; END)%proto.

  Definition chan_inv (c : val) (γ1 γ2 : gname) : iProp Σ :=
    ((own γ1 (auth 0) ∗ c ↣ <?> x1 : nat, MSG #x1; <?> x2 : nat, MSG #x2; END) ∨
     (own γ1 (auth 1) ∗ own γ2 (1/2)%Qp ∗ c ↣ <?> x2 : nat, MSG #x2; END) ∨
     (own γ1 (auth 2) ∗ own γ2 1%Qp ∗ c ↣ END))%I.

  Lemma wp_prog (N : namespace) (c : val):
    {{{ c ↣ proto_begin }}} prog c {{{ v, RET v; ⌜v = #()⌝ }}}.
  Proof.
    iIntros (Φ) "Hc HΦ".
    rewrite /prog.

    iMod (own_alloc (auth 0 ⋅ partial 1 0)) as (γ1) "[Hauth Hpartial]".
    { admit. }
    iMod (own_alloc 1%Qp) as (γ2) "[Hcredit1 Hcredit2]".
    { admit. }

    (* Create lock *)
    wp_apply (newlock_spec N (chan_inv c γ1 γ2) with "[Hc Hauth]").
    { iLeft. iFrame "Hc Hauth". }
    iIntros (lk γlk) "#Hlock".
    wp_pures.

    iPoseProof (partial_split with "Hpartial") as "[Hpartial1 Hpartial2]".

    (* Fork into two threads *)
    wp_bind (par _ _).
    wp_apply (wp_par (λ _, own γ1 (partial (1/2) 1)) (λ _, own γ1 (partial (1/2) 1)) with "[Hpartial1 Hcredit1]").
    - (* Acquire lock *)
      wp_apply (acquire_spec with "Hlock").
      iIntros "[Hlocked Hc]". wp_pures.
      iDestruct "Hc" as "[Hc|[Hc|Hc]]".
      + iDestruct "Hc" as "[Hauth Hc]".
        wp_recv (x1) as "_". wp_pures.
        iMod (partial_inc with "[Hauth Hpartial1]") as "[Hauth Hpartial1]".
        { iFrame "Hauth Hpartial1". }
        wp_apply (release_spec with "[Hlocked Hcredit1 Hauth Hc]").
        { iFrame "Hlock Hlocked". iRight. iLeft. iFrame "Hauth Hcredit1 Hc". }
        iIntros "_". wp_pures.
        iApply "Hpartial1".
      +
      + admit. (* Impossible due to fractions *)
    - admit.
  Admitted.

  (* We need to prove using ghost state that at most two receives will
  be performed in the beginning. Afterwards, we might be able to use
  an agreement RA to have the two processes communicate the value they
  have received and to determine who has the lowest one. Then the
  invariant needs to ensure that only the process with the lowest
  value can access it. *)

End Double.
