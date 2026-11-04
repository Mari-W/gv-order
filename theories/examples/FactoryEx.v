(** * The factory with an existential result, in the empty world

    A factory spawns a worker and returns a handle, as a future or a
    task API does. The box mk is the term [fac] of Factory.v. Its result
    is now an existential, so the point of the handle is hidden, and
    E-Pack introduces it at the lower bound ⊥.

      mk   = !(f = λu. let () = u in let p = new ∗ in let (c, c′) = p in
                       let () = spawn (λv. let () = v in close (send ⟨∗, c⟩)) in c′)

      mk   : □(∗ ⊸ ∃^⊥ ι. {}. (?∗.Close)@ι)                         (Tmk0)
      mk   : □(∀ζ. ∗ ⊸ ∃^⊥ ι. {ζ ≺ ι, ζ+1 ≺ ι}. (?∗.Close)@ι)       (Tmk1)

      main = let (g, f) = ⟨mk, mk⟩ in
             let p = (force g) ∗ in
             let q = (force f) ∗ in
             let () = recvclose p in recvclose q

    The two types share the term. At Tmk0 new creates the channel with
    the empty creation constraint. At Tmk1 it creates it with the
    constraint {ζ ≺ ι, ζ+1 ≺ ι}, where ζ is the box variable. Both are
    the list form L ≺ ι of [t_newfresh_lh_open] with no upper points,
    so betweenness holds with nothing to check. The body
    returns c′ packed with E-Pack at the instance [ι], and the
    constraint of the existential is the creation constraint itself, so
    the hypothesis of new proves it.

    The let of one variable is the let pair on ⟨e, ∗⟩ followed by a
    let ∗, as in [let_new]. main opens p with E-Open right after the
    let pair, before the let ∗, so that no unopened ∃^⊥ sits in the
    context of a later premise. The first call needs no point, because
    Tmk0 has no ∀. The second call instantiates ζ with the point of p,
    which the hypothesis of the first E-Open makes known. Opening q
    gives p ≺ q and p+1 ≺ q, and these are the two facts that recv and
    close on p need while main holds q. main creates no channel and
    types in the empty world [Wpo []] ([fx_deadlock_free]).

    Factory.v needs a world with constants for the same pattern (sharp
    edges 107). Without the existential, the result type of the box
    names the point of the handle. Under Tfa that point is the box
    variable, and the first call has to instantiate it with a point
    known at the start of main, which the empty world lacks
    ([fx_no_first_call]). At the one-point type of [fac] the point is a
    constant, and the empty world knows no constant. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.Factory.

Set Default Proof Using "All".

(** ?∗.Close, the end the client holds. *)
Definition Sr : sty := SSeq (SRcv 0 TUnit) SEnd.

Definition mk : expr := fac.

(** ∃^⊥ ι. {l ≺ ι ∣ l ∈ L}. (?∗.Close)@ι, the result of a call. *)
Definition Tmk_res (L : list point) : ty := TEx LBot 1 (fresh_bcs L []) (TSess Sr (pvar 0)).

Definition Tmk (m : nat) (L : list point) : ty :=
  TBox m 0 (BCs [] (λ _, False)) (TLolli None None TUnit (TLolli None None TUnit (Tmk_res L))).

Definition Tmk0 : ty := Tmk 0 [].
Definition Tmk1 : ty := Tmk 1 [pvar 0; Pt (NVar 0) 1].

(** E-Pack at the instance [ι], ι the point variable 0 of the body of
    new. The constraint is the hypothesis of new. *)
Ltac mk_pack :=
  apply (t_pack _ _ _ _ _ _ _ _ _ _ _ [pvar 0]);
  [ done
  | constructor; [right; eexists _, _, (pvar 0); split_and!; [by right; left|by left|done]|constructor]
  | apply hyp_in_fact; by right; left
  | done
  | tstep ].

(** The worker and the return after new. The channel is at the point
    variable 0 of the body of new, c at 1 and c′ at 0. *)
Ltac mk_tail HW :=
  cbn; tstep;
  [ tstep; [|apply KTSpawn|done|apply ubs_none];
    eapply (tv_lam _ HW _ _ _ _ _ TUnit TUnit (Some (Pt (NVar 0) 1)) (Some (Pt (NVar 0) 0)) 2);
      [set_solver| |];
    [ intros y Hy; mem_cases Hy; apply sle_refl, HW
    | cbn; tstep; [tstep|]; cbn; unfold sendclose; tstep;
      [ tstep; [tstep; tstep|apply (KTSend _ _ _ 0 TUnit SEnd (Pt (NVar 0) 0)); cbn; set_solver|done|];
        apply ubs_intro; [intros y Hy; mem_cases Hy|];
        exists (Pt (NVar 0) 1); split; [done|]; right; apply (slt_po _ _ (Pt (NVar 0) 0) HW)
      | apply KTClos
      | done
      | apply ubs_intro; [intros y Hy; mem_cases Hy|];
        exists (Pt (NVar 0) 1); split; [done|]; apply sle_refl, HW ] ]
  | mk_pack ].

Lemma mk0_typed W F : strict W → typed W ∅ [] ∅ [] F mk Tmk0.
Proof.
  intros HWs. pose proof (proj1 HWs) as HW. unfold mk, fac, Tmk0, Tmk.
  apply (t_exp W _ _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|box_k0].
  cbn. eapply (tv_lam W HW _ _ _ _ _ TUnit _ None None 1); [set_solver|cbn; set_solver|].
  cbn. tstep; [tstep|]. cbn.
  apply (t_newfresh_lh_open W _ _ _ _ _ _ _ Sd [] []); [constructor|set_solver|].
  mk_tail HW.
Qed.

Lemma mk1_typed W F : strict W → typed W ∅ [] ∅ [] F mk Tmk1.
Proof.
  intros HWs. pose proof (proj1 HWs) as HW. unfold mk, fac, Tmk1, Tmk.
  apply (t_exp W _ _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|box_k0].
  cbn. eapply (tv_lam W HW _ _ _ _ _ TUnit _ None None 1); [set_solver|cbn; set_solver|].
  cbn. tstep; [tstep|]. cbn.
  apply (t_newfresh_lh_open W _ _ _ _ _ _ _ Sd [pvar 0; Pt (NVar 0) 1] []).
  { constructor; [skn_payload|constructor; [skn_payload|constructor]]. }
  { intros l h _ Hh. by apply elem_of_nil in Hh. }
  mk_tail HW.
Qed.

(** ** The client *)

Definition fx_main : expr :=
  LetP (Pair mk mk)
    (LetP (Pair (App (App EForce (Var 1)) EUnit) EUnit) (LetU (Var 0)
    (LetP (Pair (App (App EForce (Var 2)) EUnit) EUnit) (LetU (Var 0)
      (LetU (recvclose (Var 3)) (recvclose (Var 1))))))).

Lemma fx_typed : styped ∅ [] [] (∅, None) fx_main TUnit.
Proof.
  apply styped_Wpo. pose proof Wpo_nil_strict' as HWs.
  pose proof (proj1 HWs) as HW. set (W := Wpo []) in *. unfold fx_main.
  (* let (g, f) = ⟨mk, mk⟩ *)
  eapply (tv_letp W HW _ _ _ _ _ _ Tmk0 Tmk1); [reflexivity| |].
  { tstep; [apply mk1_typed, HWs|apply mk0_typed, HWs]. }
  (* let p = (force g) ∗, opened at once *)
  cbn. eapply (tv_letp W HW _ _ _ _ _ _ (Tmk_res []) TUnit); [reflexivity| |].
  { tstep; [tstep|].
    eapply tv_app; [exact HW|reflexivity| |tstep|apply ubs_none].
    apply (typed_force0 W _ _ _ _ _ _ 0 (BCs [] (λ _, False)) None (TLolli None None TUnit (Tmk_res [])) []);
      [done|done| |constructor|apply ubs_none|tstep].
    apply bcs_hold_intro. by intros ? []. }
  apply (t_open W _ _ _ _ _ _ 1 LBot 1 (fresh_bcs [] []) (TSess Sr (pvar 0)) TUnit);
    [done|intros Hun; exact Hun|].
  fresh_clean.
  tstep; [tstep|]. cbn.
  (* let q = (force f) ∗ at ζ = ι_p, opened at once *)
  eapply (tv_letp W HW _ _ _ _ _ _ (Tmk_res [pvar 0; Pt (NVar 0) 1]) TUnit); [reflexivity| |].
  { tstep; [tstep|].
    eapply tv_app; [exact HW|reflexivity| |tstep|apply ubs_none].
    apply (typed_force0 W _ _ _ _ _ _ 1 (BCs [] (λ _, False)) None
             (TLolli None None TUnit (Tmk_res [pvar 0; Pt (NVar 0) 1])) [pvar 0]);
      [done|done| |constructor; [skn_payload|constructor]|apply ubs_none|tstep].
    apply bcs_hold_intro. by intros ? []. }
  apply (t_open W _ _ _ _ _ _ 1 LBot 1 (fresh_bcs [pvar 0; Pt (NVar 0) 1] [])
           (TSess Sr (pvar 0)) TUnit); [done|intros Hun; exact Hun|].
  fresh_clean.
  set (Ψ := hyps_inst (pshift 1) [(bcs_inst (pshift 1) (fresh_bcs [] []), [pvar 0])] ++
            [(bcs_inst (pshift 1) (fresh_bcs [pvar 0; Pt (NVar 0) 1] []), ids 1)]).
  assert (slt W Ψ (pvar 1) (pvar 0)) as H0.
  { apply (slt_fresh_l W Ψ (pshift 1) [pvar 0; Pt (NVar 0) 1] [] (pvar 0) (pvar 0));
      [by right; left|by left]. }
  assert (slt W Ψ (Pt (NVar 1) 1) (pvar 0)) as H1.
  { apply (slt_fresh_l W Ψ (pshift 1) [pvar 0; Pt (NVar 0) 1] [] (pvar 0) (Pt (NVar 0) 1));
      [by right; left|by right; left]. }
  tstep; [tstep|]. cbn.
  tstep.
  - (* recvclose p at ι_p, holding q at ι_q *)
    unfold recvclose. tstep.
    + tstep; [tstep|apply KTRecv|kscope|].
      apply ubs_intro; [intros y Hy; mem_cases Hy; exact H0|done].
    + cbn. tstep; [tstep|]. cbn. tstep; [tstep|apply KTClos|done|].
      apply ubs_intro; [intros y Hy; mem_cases Hy; exact H1|done].
  - (* recvclose q *)
    unfold recvclose. tstep.
    + tstep; [tstep|apply KTRecv|kscope|]. apply ubs_intro; [intros y Hy; mem_cases Hy|done].
    + cbn. tstep; [tstep|]. cbn. tstep; [tstep|apply KTClos|done|].
      apply ubs_intro; [intros y Hy; mem_cases Hy|done].
Qed.

Theorem fx_deadlock_free : deadlock_free (∅, {[+ fx_main +]}).
Proof.
  apply (soundness (Wpo []) _ TUnit (Wpo_strict _)).
  apply ptyped_closed_s; [constructor|apply fx_typed].
Qed.

(** ** Why the existential

    At the start of main the empty world knows no point and there is no
    hypothesis, so force has no instance at a box with a ∀. The first
    call of the parametric factory [faca] of Factory.v, whose result
    names the box variable, has no type there. *)

Lemma Wpo_nil_unknown x : ¬ skn (Wpo []) [] x.
Proof.
  intros [Hk|(C & xs & y & Hin & _)].
  - unfold pt_known, Wpo in Hk. cbn in Hk. set_solver.
  - by apply elem_of_nil in Hin.
Qed.

Lemma fx_no_first_call ub T :
  ¬ konst_ty (seqs (Wpo []) []) (slt (Wpo []) []) (skn (Wpo []) []) KForce (TLolli ub None Tfa T).
Proof.
  intros Hk. inversion Hk as [kq Tq Gq xs Hsig _ HK|]; subst.
  inversion Hsig as [| | | | | | | |n k C ub' T' ? ss Hn _ _]; subst.
  destruct xs as [|x xs]; [done|]. apply Forall_cons in HK as [Hx _].
  by apply (Wpo_nil_unknown x).
Qed.
