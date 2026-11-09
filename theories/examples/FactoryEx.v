(** * The factory with an existential result

    A factory spawns a worker and returns a handle, as a future or a
    task API does. The box mk is the body of [fac] of Factory.v. Its
    result is an existential, so the point of the handle is hidden, and
    E-Pack introduces it at the lower bound ⊥. Under syntactic points
    (sharp edges 173) mk takes a point parameter and the package carries
    the point value of the hidden point, see [mk] below.

      mk   = !(f = λu. let () = u in let p = new ∗ in let (c, c′) = p in
                       let () = spawn (λv. let () = v in close (send ⟨∗, c⟩)) in c′)

    Under the constant world (sharp edges 172) new creates the channel
    at the field point ζ[0] of the box variable ζ, and the box
    constraint states the facts of ζ[0] that the result promises:

      mk   : □(∀ζ. {ζ[0]‾ ≺ ζ[0][0], ζ[0]‾+1 ≺ ζ[0][0]}.
                 ∗ ⊸ ∃^⊥ ι. {ῑ ≺ ι[0], ῑ+1 ≺ ι[0]}. (?∗.Close)@ῑ)       (Tmk0)
      mk   : □(∀ζ. {ζ ≺ ζ[0], ζ+1 ≺ ζ[0]}.
                 ∗ ⊸ ∃^⊥ ι. {ζ ≺ ι, ζ+1 ≺ ι}. (?∗.Close)@ῑ)            (Tmk1)

      main = let (g, f) = ⟨mk, mk⟩ in
             let p = (force g) ∗ in
             let q = (force f) ∗ in
             let () = recvclose p in recvclose q

    The two types share the term ([mk_typed]). The body packs c′ at the
    instance ζ[0], and the box constraint proves the constraint of the
    existential there. The first call instantiates ζ with the top-level
    point ζ₀ of main, whose hypothesis is the box constraint of Tmk0 at
    ζ₀ ([fx_Ψ]). The second call instantiates ζ with the point ῑ_p of
    p, and the hypothesis of opening p is the box constraint of Tmk1 at
    ῑ_p. Opening q gives ῑ_p ≺ ι_q and ῑ_p+1 ≺ ι_q, the two facts that
    recv and close on p need while main holds q. Before the constant
    world Tmk0 had no ∀ and main needed no point.

    The let of one variable is the let pair on ⟨e, ∗⟩ followed by a
    let ∗, as in [let_new]. main opens p with E-Open right after the
    let pair, before the let ∗, so that no unopened ∃^⊥ sits in the
    context of a later premise. main creates no channel and types
    under the hypothesis of ζ₀ ([fx_deadlock_free]).

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

(** Under syntactic points mk takes a point parameter π : pt(ζ̄) in
    place of the unit, creates the channel by new (π[0]) at ζ[0]
    ([KPay 0], and x̄[i] = x[i]) and returns the point ζ[0] with the
    handle, so that a caller can pass it on (sharp edges 173). *)
Definition mk : expr :=
  EBox (Lam (let_new_pair_at (App (Konst (KPay 0)) (Var 0))
    (LetU (App ESpawn (Lam (LetU (Var 0) (sendclose (Var 2)))))
      (Pair (App (Konst (KPay 0)) (Var 2)) (Var 0))))).

(** ∃^⊥ ι. C. pt(ι) ⊗ (?∗.Close)@ῑ, the result of a call. *)
Definition Tres (C : bcs) : ty := TEx LBot 1 C (TProd (TPt (pvar 0)) (TSess Sr (pt_dual (pvar 0)))).

(** ∃^⊥ ι. {l ≺ ι ∣ l ∈ L}. (?∗.Close)@ῑ. *)
Definition Tmk_res (L : list point) : ty := Tres (fresh_bcs L []).

(** Under the constant world (sharp edges 172) the box creates the
    channel with new@ζ[0] at the field point of its variable ζ, and the
    box constraint states the facts of ζ[0] that the result promises.
    The caller proves them for its instance. *)
Abbreviation x0 := (Pt (NPayload (NVar 0) 0 0) 0).
Abbreviation x00 := (Pt (NPayload (NPayload (NVar 0) 0 0) 0 0) 0).

Definition Tmk (Cb Cr : bcs) : ty :=
  TBox 1 0 Cb (TLolli None None TUnit (TLolli None None (TPt (pt_dual (pvar 0))) (Tres Cr))).

(** Tmk0: ∀ζ. {ζ[0]‾ ≺ ζ[0][0], ζ[0]‾+1 ≺ ζ[0][0]}. ∗ ⊸ ∃^⊥ ι. {ῑ ≺ ι[0], ῑ+1 ≺ ι[0]}. (?∗.Close)@ῑ.
    The result holds the facts that the second call needs at ζ = ῑ. *)
Definition Cr0 : bcs := BCs [] (λ g, g = FLt (pt_dual (pvar 0)) x0 ∨ g = FLt (pt_shift 1 (pt_dual (pvar 0))) x0).
Definition Cb0 : bcs := BCs [] (λ g, g = FLt (pt_dual x0) x00 ∨ g = FLt (pt_shift 1 (pt_dual x0)) x00).
Definition Tmk0 : ty := Tmk Cb0 Cr0.

(** Tmk1: ∀ζ. {ζ ≺ ζ[0], ζ+1 ≺ ζ[0]}. ∗ ⊸ ∃^⊥ ι. {ζ ≺ ι, ζ+1 ≺ ι}. (?∗.Close)@ῑ. *)
Definition Cb1 : bcs := BCs [] (λ g, g = FLt (pvar 0) x0 ∨ g = FLt (Pt (NVar 0) 1) x0).
Definition Tmk1 : ty := Tmk Cb1 (fresh_bcs [pvar 0; Pt (NVar 0) 1] []).

(** The box at any constraint whose facts give the result's facts at
    the instance ζ[0]. *)
Lemma mk_typed W F Cb Cr :
  strict W →
  (∀ Ψ, (bcs_inst (pshift 1) Cb, [pvar 0]) ∈ Ψ → bcs_hold (seqs W Ψ) (slt W Ψ) Cr [x0]) →
  typed W ∅ [] ∅ [] F mk (Tmk Cb Cr).
Proof.
  intros HWs HCr. pose proof (proj1 HWs) as HW. unfold mk, Tmk.
  assert (∀ Ψ, (bcs_inst (pshift 1) Cb, [pvar 0]) ∈ Ψ → skn W Ψ x0) as Hk0.
  { intros Ψ Hin. right; eexists _, _, (pvar 0); split_and!; [exact Hin|by left|done]. }
  apply (t_exp W _ _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|box_k0].
  cbn. eapply (tv_lam W HW _ _ _ _ _ _ _ None None 1); [set_solver|cbn; set_solver|].
  cbn. unfold let_new_pair_at. apply (t_new_v W _ _ _ _ _ _ _ Sd x0 _ HWs); [| |].
  { intros F'. cbn. eapply (tv_appk W HW _ _ _ _ (KPay 0) _ None (TPt (pt_dual (pvar 0))));
      [tstep|apply KTPay, Hk0; by left|done|apply ubs_none]. }
  { apply Hk0. by left. }
  cbn. tstep.
  - tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam _ HW _ _ _ _ _ TUnit TUnit (Some (pt_shift 1 x0)) (Some (pt_dual x0)) 2);
      [set_solver| |].
    + intros y Hy; mem_cases Hy; apply sle_refl, HW.
    + cbn; tstep; [tstep|]; cbn; unfold sendclose; tstep.
      * tstep; [tstep; tstep|apply (KTSend _ _ _ 0 TUnit SEnd x0); cbn; set_solver|done|].
        apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pt_shift 1 x0); split; [done|]; right; apply (slt_po _ _ x0 HW).
      * apply KTClos.
      * done.
      * apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pt_shift 1 x0); split; [done|]; apply sle_refl, HW.
  - apply (t_pack _ _ _ _ _ _ _ _ _ _ _ [x0]).
    + done.
    + constructor; [right; eexists _, _, (pvar 0); split_and!; [by left|by left|done]|constructor].
    + apply HCr. by left.
    + done.
    + cbn. tstep; [tstep|].
      eapply (tv_appk W HW _ _ _ _ (KPay 0) _ None (TPt (pt_dual (pvar 0))));
        [tstep|apply KTPay, Hk0; by left|done|apply ubs_none].
Qed.

Lemma mk0_typed W F : strict W → typed W ∅ [] ∅ [] F mk Tmk0.
Proof.
  intros HWs. apply mk_typed; [done|]. intros Ψ Hin.
  apply bcs_hold_intro. intros g [-> | ->] _; cbn.
  - eapply (sl_hyp0 _ _ _ _ (pt_dual x0) x00); [exact Hin|by left|cbn; lia|reflexivity|reflexivity].
  - eapply (sl_hyp0 _ _ _ _ (pt_shift 1 (pt_dual x0)) x00); [exact Hin|by right|cbn; lia|reflexivity|reflexivity].
Qed.

Lemma mk1_typed W F : strict W → typed W ∅ [] ∅ [] F mk Tmk1.
Proof.
  intros HWs. apply mk_typed; [done|]. intros Ψ Hin.
  apply bcs_hold_fresh_intro. intros f [(i & Hi & ->)|(j & Hj & ->)] Hs; [|cbn in Hj; lia].
  destruct i as [|[|i]]; [| |cbn in Hi; lia]; cbn.
  - eapply (sl_hyp0 _ _ _ _ (pvar 0) x0); [exact Hin|by left|cbn; lia|reflexivity|reflexivity].
  - eapply (sl_hyp0 _ _ _ _ (Pt (NVar 0) 1) x0); [exact Hin|by right|cbn; lia|reflexivity|reflexivity].
Qed.

(** ** The client *)

Definition fx_main : expr :=
  LetP (Pair mk mk)
    (LetP (Pair (App (App EForce (Var 1)) (EPt (pt_dual (pconst 0)))) EUnit) (LetU (Var 0)
    (LetP (Var 1)
    (LetP (Pair (App (App EForce (Var 4)) (Var 1)) EUnit) (LetU (Var 0)
    (LetP (Var 1)
      (LetU (recvclose (Var 4)) (recvclose (Var 0))))))))).

(** main has one top-level point ζ₀, with the facts of Cb0 at ζ₀, so
    that the first call has an instance (sharp edges 172). Under
    syntactic points ζ₀ is the constant 0, and main passes the literal
    ζ̄₀ to the first call and the point of p to the second. *)
Definition fx_Ψ : hyps := [] ++ [(Cb0, [pconst 0])].

Lemma fx_created : created (Wpo []) fx_Ψ.
Proof.
  apply created_snoc; [constructor| |constructor|fresh_const].
  set (r := λ x : point, 3 * pt_off x +
              match pt_name x with NPayload (NPayload _ _ _) _ _ => 20 | NPayload _ _ _ => 10 | _ => 0 end).
  apply (cc_ok_inner _ _ _ (λ x y, r x < r y)).
  - intros x y z; lia.
  - intros x; lia.
  - intros [q pb o] _. unfold r, pt_shift. simpl. lia.
  - intros g [-> | ->] _; eexists _, _; (split; [done|]); unfold r; cbn; lia.
  - intros [q pb o] _. unfold r, pt_shift, pt_dual. simpl. lia.
Qed.

Lemma fx_typed : styped ∅ fx_Ψ [] (∅, None) fx_main TUnit.
Proof.
  apply styped_Wpo. pose proof Wpo_nil_strict' as HWs.
  pose proof (proj1 HWs) as HW. set (W := Wpo []) in *. unfold fx_main, fx_Ψ. cbn.
  (* let (g, f) = ⟨mk, mk⟩ *)
  eapply (tv_letp W HW _ _ _ _ _ _ Tmk0 Tmk1); [reflexivity| |].
  { tstep; apply typed_hyps_nil; [exact HWs|apply mk1_typed, HWs|exact HWs|apply mk0_typed, HWs]. }
  (* let p = (force g) ζ̄₀ at ζ = ζ₀, opened at once *)
  cbn. eapply (tv_letp W HW _ _ _ _ _ _ (Tres Cr0) TUnit); [reflexivity| |].
  { tstep; [tstep|].
    eapply tv_app; [exact HW|reflexivity| | |apply ubs_none].
    - apply (typed_force0 W _ _ _ _ _ _ 1 Cb0 None
               (TLolli None None (TPt (pt_dual (pvar 0))) (Tres Cr0)) [pconst 0]);
        [done|done| | |apply ubs_none|tstep].
      + apply hyp_in_fact. by left.
      + constructor; [right; eexists _, _, (pconst 0); split_and!; [by left|by left|done]|constructor].
    - tstep. right; eexists _, _, (pconst 0); split_and!; [by left|by left|done]. }
  apply (t_open W _ _ _ _ _ _ 1 LBot 1 Cr0 (TProd (TPt (pvar 0)) (TSess Sr (pt_dual (pvar 0)))) TUnit);
    [done|intros Hun; exact Hun|].
  fresh_clean.
  tstep; [tstep|]. cbn.
  (* let (π_p, p) = p *)
  tstep; [tstep|]. cbn.
  (* let q = (force f) π_p at ζ = ῑ_p, opened at once *)
  eapply (tv_letp W HW _ _ _ _ _ _ (Tmk_res [pt_dual (pvar 0); pt_dual (Pt (NVar 0) 1)]) TUnit); [reflexivity| |].
  { tstep; [tstep|].
    eapply tv_app; [exact HW|reflexivity| | |apply ubs_none].
    - apply (typed_force0 W _ _ _ _ _ _ 1 Cb1 None
               (TLolli None None (TPt (pt_dual (pvar 0))) (Tmk_res [pvar 0; Pt (NVar 0) 1])) [pt_dual (pvar 0)]);
        [done|done| |constructor; [right; eexists _, _, (pvar 0); split_and!; [by right; left|by left|done]|constructor]|apply ubs_none|tstep].
      apply bcs_hold_intro. intros g [-> | ->] _; cbn.
      + eapply (sl_hyp0 _ _ _ [pvar 0] (pt_dual (pvar 0)) x0); [by right; left|by left|cbn; lia|reflexivity|reflexivity].
      + eapply (sl_hyp0 _ _ _ [pvar 0] (pt_shift 1 (pt_dual (pvar 0))) x0);
          [by right; left|by right|cbn; lia|reflexivity|reflexivity].
    - tstep. }
  apply (t_open W _ _ _ _ _ _ 1 LBot 1 (fresh_bcs [pt_dual (pvar 0); pt_dual (Pt (NVar 0) 1)] [])
           (TProd (TPt (pvar 0)) (TSess Sr (pt_dual (pvar 0)))) TUnit); [done|intros Hun; exact Hun|].
  fresh_clean.
  match goal with |- typed _ _ ?Q _ _ _ _ _ => set (Ψ := Q) end.
  assert (slt W Ψ (pt_dual (pvar 1)) (pvar 0)) as H0.
  { apply (slt_fresh_l W Ψ (pshift 1) [pt_dual (pvar 0); pt_dual (Pt (NVar 0) 1)] [] (pvar 0) (pt_dual (pvar 0)));
      [by right; right; left|by left]. }
  assert (slt W Ψ (pt_dual (Pt (NVar 1) 1)) (pvar 0)) as H1.
  { apply (slt_fresh_l W Ψ (pshift 1) [pt_dual (pvar 0); pt_dual (Pt (NVar 0) 1)] [] (pvar 0) (pt_dual (Pt (NVar 0) 1)));
      [by right; right; left|by right; left]. }
  tstep; [tstep|]. cbn.
  (* let (π_q, q) = q *)
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
Proof. apply (soundness_created_s fx_Ψ _ TUnit fx_created); [constructor|apply fx_typed]. Qed.

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
  intros Hk. inversion Hk as [kq Tq Gq xs Hsig _ HK| | |]; subst.
  inversion Hsig as [| | | | | | | |n k C ub' T' ? ss Hn _ _]; subst.
  destruct xs as [|x xs]; [done|]. apply Forall_cons in HK as [Hx _].
  by apply (Wpo_nil_unknown x).
Qed.
