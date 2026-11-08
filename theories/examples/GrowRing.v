(** * growing ring: typable, lock-free fragment under R2-recv (Padovani 2014, Example III.7)

    Padovani's ring (padovani2014deadlock p8):

      Ring = *c?(x, y).(νa) x?(z).(νb)(c!⟨z, b⟩ | c!⟨b, a⟩) | y!⟨a⟩
      (νe)(Ring | c!⟨e, e⟩)

    Each node sends a fresh channel to its neighbour on y and, at the
    same time, receives one on x. Then it splits into two nodes joined
    by a fresh channel b. The ring doubles its diameter every round.

    The translation spawns the send on y first, then receives on x and
    spawns both recursive calls. The y-thread holds no self, so the
    guard is met by the receive on x.

      Sch = μX. ?(∃κ. X@κ).Close                       (ReceivedChain.v)
      ring : □(∀ι₁ ι₂. Cr. ∗ ⊸ (Sch@ι₁ ⊗ S̄ch@ι₂ ⊸^{ι₁+1} ∗))
      ring = !(f = λp. let (x, y) = p in let (a, a′) = new@(ι₂[0]) ∗ in
                 let () = spawn (λw. let () = w in close (send ⟨a, y⟩)) in
                 let (z, x) = recv x in let () = close x in
                 let (b, b′) = new@(ι₁[1]) ∗ in
                 let () = spawn (λw. let () = w in (force f) ⟨z, b′⟩) in
                 spawn (λw. let () = w in (force f) ⟨b, a′⟩))
      rg_main = let (r, u) = ⟨ring, ∗⟩ in let () = u in
                let (e, e′) = new@γ ∗ in (force r) ⟨e, e′⟩

    The node at (X, Y) calls (X[0], X[1]‾) and (X[1], Y[0]‾). The
    channel b sits at the payload point X[1], which no message uses.
    The constraint Cr holds six facts at every pair reachable from
    (ι₁, ι₂) ([rg_F], [rreach]):

      Y ≺ Y[0]‾          the send of a on y
      X+1 ≺ X[0]‾        close x while z is held
      X+1 ≺ Y[0]         close x while a′ is held (and recv x, via X ≺ X+1)
      Ȳ ≺ Y[0]‾          the lower point Ȳ of the y-thread
      X+1 ≺ X[1], X[1]‾  the lower point X+1 of the two call threads

    Every fact climbs one payload level, and along a reachable pair X
    is never deeper than Y. So the rank 2·depth + offset rises along
    every fact ([rg0_rank]). Under the constant world the creation
    facts of e are facts of W, and the same rank makes W well founded
    (lockfree/Fragment.v). *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.ExampleTools.
From LRGV Require Import examples.ReceivedChain examples.cfst.CfstTools.

Set Default Proof Using "All".

(** ** The pairs of a ring and their facts *)

Inductive rreach (X0 Y0 : point) : point → point → Prop :=
  | rr_root : rreach X0 Y0 X0 Y0
  | rr_l X Y : rreach X0 Y0 X Y → rreach X0 Y0 (pt_payload X 0) (pt_dual (pt_payload X 1))
  | rr_r X Y : rreach X0 Y0 X Y → rreach X0 Y0 (pt_payload X 1) (pt_dual (pt_payload Y 0)).

Definition rg_F (X Y : point) (g : fact) : Prop :=
  g = FLt Y (pt_dual (pt_payload Y 0)) ∨
  g = FLt (pt_shift 1 X) (pt_dual (pt_payload X 0)) ∨
  g = FLt (pt_shift 1 X) (pt_payload Y 0) ∨
  g = FLt (pt_dual Y) (pt_dual (pt_payload Y 0)) ∨
  g = FLt (pt_shift 1 X) (pt_payload X 1) ∨
  g = FLt (pt_shift 1 X) (pt_dual (pt_payload X 1)).

Lemma rreach_trans X0 Y0 X1 Y1 X Y : rreach X0 Y0 X1 Y1 → rreach X1 Y1 X Y → rreach X0 Y0 X Y.
Proof. intros H1 H2. induction H2 as [|X Y _ IH|X Y _ IH]; [done|exact (rr_l _ _ _ _ IH)|exact (rr_r _ _ _ _ IH)]. Qed.

Lemma rreach_inst σ X0 Y0 X Y :
  rreach X0 Y0 X Y → rreach (pt_inst σ X0) (pt_inst σ Y0) (pt_inst σ X) (pt_inst σ Y).
Proof.
  induction 1 as [|X Y _ IH|X Y _ IH]; [apply rr_root| |];
    rewrite pt_inst_dual, !pt_inst_payload; [exact (rr_l _ _ _ _ IH)|exact (rr_r _ _ _ _ IH)].
Qed.

Lemma rg_F_inst σ X Y g : rg_F X Y g → rg_F (pt_inst σ X) (pt_inst σ Y) (fact_map (pt_inst σ) g).
Proof.
  intros H. unfold rg_F in *.
  repeat destruct H as [H|H]; subst g; cbn [fact_map];
    rewrite ?pt_inst_dual, ?pt_inst_payload, ?pt_inst_shift;
    repeat (first [left; reflexivity|right]); reflexivity.
Qed.

(** ** The box *)

Definition rg_P (g : fact) : Prop := ∃ X Y, rreach (pvar 0) (pvar 1) X Y ∧ rg_F X Y g.
Definition rg_C : bcs := BCs [] rg_P.

Definition rg_body : ty :=
  TLolli (Some (pv 0 1)) None (TProd (TSess Sch (pv 0 0)) (TSess (dual Sch) (pv 1 0))) TUnit.
Definition rg_ty : ty := TBox 2 0 rg_C (TLolli None None TUnit rg_body).

Definition ring : expr :=
  EBox (Lam (LetP (Var 0) (let_new_pair
    (LetU (App ESpawn (Lam (LetU (Var 0) (App EClos (App ESend (Pair (Var 2) (Var 3)))))))
    (LetP (App ERecv (Var 3)) (LetU (App EClos (Var 0)) (let_new_pair
      (LetU (App ESpawn (Lam (LetU (Var 0) (App (App EForce (Var 10)) (Pair (Var 4) (Var 1))))))
        (App ESpawn (Lam (LetU (Var 0) (App (App EForce (Var 10)) (Pair (Var 2) (Var 5)))))))))))))).

Definition rg_main : expr :=
  LetP (Pair ring EUnit) (LetU (Var 0) (let_new_pair (App (App EForce (Var 3)) (Pair (Var 1) (Var 0))))).

Abbreviation rx0 := (Pt (NPayload (NVar 0) 0 0) 0).
Abbreviation rx1 := (Pt (NPayload (NVar 0) 0 1) 0).
Abbreviation ry0 := (Pt (NPayload (NVar 1) 0 0) 0).

(** The two calls feed the pairs (X[0], X[1]‾) and (X[1], Y[0]‾). *)
Lemma rg_sub (xs : list point) X1 Y1 :
  xs = [X1; Y1] → rreach (pvar 0) (pvar 1) X1 Y1 →
  ∀ g, rg_P g → fact_scoped 2 g → rg_P (fact_map (pt_inst (plist xs)) g).
Proof.
  intros -> H1 g (X & Y & HR & HF) _. exists (pt_inst (plist [X1; Y1]) X), (pt_inst (plist [X1; Y1]) Y).
  split; [|by apply rg_F_inst]. eapply rreach_trans; [exact H1|].
  apply (rreach_inst (plist [X1; Y1])) in HR. rewrite !pt_inst_pvar_at in HR. exact HR.
Qed.

Lemma rg_call W Ψ X1 Y1 :
  (rg_C, ids 2) ∈ Ψ → rreach (pvar 0) (pvar 1) X1 Y1 →
  pn_vb 2 (pt_name X1) → pn_vb 2 (pt_name Y1) →
  bcs_hold (seqs W Ψ) (slt W Ψ) rg_C [X1; Y1].
Proof.
  intros Hg HR H1 H2. apply bcs_hold_self; [done|constructor; [done|constructor; [done|constructor]]|].
  by apply (rg_sub _ X1 Y1).
Qed.

Lemma rg_root W Ψ x y :
  (rg_C, ids 2) ∈ Ψ → rg_F (pvar 0) (pvar 1) (FLt x y) → fact_scoped 2 (FLt x y) → slt W Ψ x y.
Proof.
  intros Hg HF Hs. eapply (sl_hyp0 _ _ rg_P (ids 2) x y); [done| |done| |].
  - exists (pvar 0), (pvar 1). split; [constructor|done].
  - destruct Hs. by apply pt_inst_ids.
  - destruct Hs. by apply pt_inst_ids.
Qed.

Ltac rgf :=
  apply rg_root; [by left|unfold rg_F; repeat (first [left; reflexivity|right]); reflexivity|cbn; lia].

Lemma rg_kn W Ψ x : (rg_C, ids 2) ∈ Ψ → pt_root x = NVar 0 ∨ pt_root x = NVar 1 → skn W Ψ x.
Proof.
  intros Hg [Hx|Hx].
  - apply (skn_in W Ψ rg_C (ids 2) (pvar 0)); [done|inlist|done].
  - apply (skn_in W Ψ rg_C (ids 2) (pvar 1)); [done|inlist|done].
Qed.

Lemma ring_typed W F : strict W → typed W ∅ [] ∅ [] F ring rg_ty.
Proof.
  intros HWs. pose proof (proj1 HWs) as HW. unfold ring, rg_ty.
  apply (t_exp W _ _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|box_k0].
  box_open rg_C rg_body. cbn. unfold rg_body.
  eapply (tv_lam W HW _ _ _ _ _ _ _ _ None 1); [set_solver|cbn; set_solver|].
  cbn. tstep; [tstep|]. cbn.
  (* a, a′ at ι₂[0] *)
  apply (t_new_at W _ _ _ _ _ _ _ Sch ry0 HWs); [apply rg_kn; [by left|by right]|].
  cbn. tstep.
  { (* the y-thread: send a on y, close y *)
    tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pv 1 1)) (Some (pt_dual (pv 1 0))) 2); [set_solver| |].
    { intros y Hy. mem_cases Hy; first [apply sle_refl, HW|right; rgf]. }
    cbn. tstep; [tstep|]. cbn.
    eapply (tv_appk W HW _ _ _ _ KClos _ (Some (pv 1 1)) (TSess SEnd (pv 1 1))).
    - eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pv 1 0))
                (TProd (TSess Sch ry0) (TSess (SSeq (SSnd 1 (TSess Sch (pvar 0))) SEnd) (pv 1 0)))).
      + tstep; [|tstep]. eapply t_conv; [|tstep]. conv_sess.
      + apply (KTSend _ _ _ 1 (TSess Sch (pvar 0)) SEnd (pv 1 0)).
        intros h Hh. cbn in Hh. apply elem_of_singleton in Hh as ->. rgf.
      + kscope.
      + apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pv 1 1). split; [done|]. right. apply (slt_po W _ (pv 1 0) HW).
    - apply KTClos.
    - done.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 1 1). split; [done|]. apply sle_refl, HW. }
  (* recv z on x at ι₁ while a′ is held *)
  cbn. tstep.
  { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (pv 0 0))
              (TSess (SSeq (SRcv 1 (TSess Sch (pvar 0))) SEnd) (pv 0 0))).
    - eapply t_conv; [|tstep]. conv_sess.
    - apply KTRecv.
    - kscope.
    - apply ubs_intro.
      + intros y Hy. mem_cases Hy. apply (sl_trans _ _ _ (pv 0 1)); [apply (slt_po W _ (pv 0 0) HW)|rgf].
      + exists (pv 0 1). split; [done|]. right. apply (slt_po W _ (pv 0 0) HW). }
  (* close x at ι₁+1 while z and a′ are held *)
  cbn. tstep.
  { tstep; [tstep|apply KTClos|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy; rgf|].
    exists (pv 0 1). split; [done|]. apply sle_refl, HW. }
  (* b, b′ at ι₁[1] *)
  apply (t_new_at W _ _ _ _ _ _ _ Sch rx1 HWs); [apply rg_kn; [by left|by left]|].
  cbn. tstep.
  { (* the call at (ι₁[0], ι₁[1]‾) *)
    tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pt_shift 1 rx0)) (Some (pv 0 1)) 2); [set_solver| |].
    { intros y Hy. mem_cases Hy; right; rgf. }
    cbn. tstep; [tstep|]. cbn.
    eapply tv_app; [exact HW|reflexivity| | |].
    - apply (typed_force0 W _ _ _ _ _ _ 2 rg_C None rg_body [rx0; pt_dual rx1]);
        [done|done| | |apply ubs_none|tstep].
      + apply rg_call; [by left| |cbn; lia|cbn; lia]. apply (rr_l (pvar 0) (pvar 1) (pvar 0) (pvar 1) (rr_root _ _)).
      + constructor; [apply rg_kn; [by left|by left]|constructor; [apply rg_kn; [by left|by left]|constructor]].
    - tstep; tstep.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pt_shift 1 rx0). split; [done|]. apply sle_refl, HW. }
  (* the call at (ι₁[1], ι₂[0]‾) *)
  cbn. tstep; [|apply KTSpawn|done|apply ubs_none].
  eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pt_shift 1 rx1)) (Some (pv 0 1)) 2); [set_solver| |].
  { intros y Hy. mem_cases Hy; right; rgf. }
  cbn. tstep; [tstep|]. cbn.
  eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force0 W _ _ _ _ _ _ 2 rg_C None rg_body [rx1; pt_dual ry0]);
      [done|done| | |apply ubs_none|tstep].
    + apply rg_call; [by left| |cbn; lia|cbn; lia]. apply (rr_r (pvar 0) (pvar 1) (pvar 0) (pvar 1) (rr_root _ _)).
    + constructor; [apply rg_kn; [by left|by left]|constructor; [apply rg_kn; [by left|by right]|constructor]].
  - tstep; tstep.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (pt_shift 1 rx1). split; [done|]. apply sle_refl, HW.
Qed.

(** ** The top-level constraint over γ = 0

    main forces the ring at (γ, γ̄), so C₀ holds the facts of every
    pair reachable from (γ, γ̄). *)
Definition rg0_P (g : fact) : Prop := ∃ X Y, rreach (pvar 0) (pt_dual (pvar 0)) X Y ∧ rg_F X Y g.
Definition rg0_C : bcs := BCs [] rg0_P.

Fixpoint pdepth (p : pname) : nat := match p with NPayload q _ _ => S (pdepth q) | _ => 0 end.

(** 2·depth + offset, blind to polarity. *)
Definition rg_rank (x : point) : nat := 2 * pdepth (pt_name x) + pt_off x.

Lemma rreach_rank X Y :
  rreach (pvar 0) (pt_dual (pvar 0)) X Y →
  pt_off X = 0 ∧ pt_off Y = 0 ∧ pdepth (pt_name X) ≤ pdepth (pt_name Y).
Proof. induction 1 as [|X Y _ IH|X Y _ IH]; cbn; lia. Qed.

Lemma rg0_rank x y : rg0_P (FLt x y) → rg_rank x < rg_rank y.
Proof.
  intros (X & Y & HR & HF). destruct (rreach_rank X Y HR) as (HX & HY & Hd).
  unfold rg_rank. repeat destruct HF as [HF|HF]; injection HF as -> ->; cbn; lia.
Qed.

Lemma rg0_acyclic : c0_acyclic 1 rg0_C.
Proof.
  apply (c0_acyclic_rank 1 rg0_P rg_rank).
  - intros x. unfold rg_rank, pt_shift. cbn. lia.
  - exact rg0_rank.
  - done.
Qed.

(** The run reads the variable γ as the constant γ, at the same depth. *)
Lemma pdepth_c0 n p : pdepth (c0_name n p) = pdepth p.
Proof. induction p as [a|a|q IH b i]; cbn; [done| |by rewrite IH]. by destruct (decide (a < n)). Qed.

Lemma rg_rank_c0 x : rg_rank (c0_pt 1 x) = rg_rank x.
Proof. unfold rg_rank, c0_pt. cbn. by rewrite pdepth_c0. Qed.

Lemma rg0_hyp W x y : rg0_P (FLt x y) → fact_scoped 1 (FLt x y) → slt W [(rg0_C, ids 1)] x y.
Proof.
  intros H Hs. eapply (sl_hyp0 _ _ rg0_P (ids 1) x y); [by apply list_elem_of_singleton|done|done| |].
  all: by apply pt_inst_ids; destruct Hs.
Qed.

Lemma rg_typed : styped ∅ [(rg0_C, ids 1)] [] (∅, None) rg_main TUnit.
Proof.
  apply styped_Wpo. pose proof Wpo_nil_strict' as HWs.
  pose proof (proj1 HWs) as HW. set (W := Wpo []) in *. unfold rg_main.
  tstep.
  { tstep; [tstep|apply typed_hyps_wk; [exact HWs|apply ring_typed, HWs]]. }
  cbn. tstep; [tstep|]. cbn.
  apply (t_new_at W _ _ _ _ _ _ _ Sch (pvar 0) HWs).
  { apply (skn_in W _ rg0_C (ids 1) (pvar 0)); [by left|inlist|done]. }
  cbn. eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force0 W _ _ _ _ _ _ 2 rg_C None rg_body [pvar 0; pt_dual (pvar 0)]);
      [done|done| | |apply ubs_none|tstep].
    + apply bcs_hold_intro. intros g (X & Y & HR & HF) Hs.
      assert (rg0_P (fact_map (pt_inst (plist [pvar 0; pt_dual (pvar 0)])) g)) as H0.
      { exists (pt_inst (plist [pvar 0; pt_dual (pvar 0)]) X), (pt_inst (plist [pvar 0; pt_dual (pvar 0)]) Y).
        split; [|by apply rg_F_inst].
        apply (rreach_inst (plist [pvar 0; pt_dual (pvar 0)])) in HR. rewrite !pt_inst_pvar_at in HR. exact HR. }
      assert (fact_scoped 1 (fact_map (pt_inst (plist [pvar 0; pt_dual (pvar 0)])) g)) as Hs1.
      { apply fact_scoped_inst; [vb_list|exact Hs]. }
      revert H0 Hs1. destruct (fact_map (pt_inst (plist [pvar 0; pt_dual (pvar 0)])) g) as [x y].
      intros H0 Hs1. cbn [fact_holds]. by apply rg0_hyp.
    + constructor; [|constructor; [|constructor]];
        apply (skn_in W _ rg0_C (ids 1) (pvar 0)); first [by left|inlist|done].
  - tstep; tstep.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|done].
Qed.

Lemma rg_deadlock_free : deadlock_free (∅, {[+ rg_main +]}).
Proof.
  apply (soundness_source 1 rg0_C _ TUnit (c0_acyclic_creation _ _ rg0_acyclic));
    [constructor|apply rg_typed].
Qed.
