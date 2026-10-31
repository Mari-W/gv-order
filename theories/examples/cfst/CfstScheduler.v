(** * Milner's cyclic scheduler (Mordido and Pérez 2026, A.5, pp. 37–39)

    Three partial schedulers in a ring and three workers. A unary
    choice carries no information, and K4 gives select the readiness
    and cost of send and branch those of receive. So select Start and
    select Next become sends of ∗, and the branches on them become
    receives. The acknowledgement () is ∗.

      Wk = µX. !∗;?∗;X     (scheduler to worker, Start and then the ack)
      Sc = µX. !∗;!∗;X     (scheduler to its successor, Start and then Next)

      follower : □(∀π ω σ ζ. C. ∗ ⊸^⊥_⊤ (S̄c@π ⊗ Wk@ω ⊗ Sc@σ ⊸^ζ_⊤ ∗))
      follower = !(f = λ⟨prev, ⟨wk, succ⟩⟩.
                   recv prev; send wk; send succ; recv wk; recv prev;
                   (force f) ⟨prev, ⟨wk, send succ⟩⟩)
      worker   : □(∀κ ζ. {κ+k ≺ ζ ∣ k}. ∗ ⊸^⊥_⊤ (W̄k@κ ⊸^ζ_⊤ ∗))
      worker   = !(w = λx. recv x; (force w) (send x))
      leader   = send a1; send c1; recv a1; (force follower) ⟨d3, ⟨a1, send c1⟩⟩

    C holds, for every round r, the twelve facts that make each action
    of a round lie below the two channels the follower still holds,
    at the instants 2r and 2r+1 of each channel, and the ceiling ζ
    above all of them. The instants alternate between the channels, so
    C needs the parity of the instant. No linear rank of the instants
    meets it, already for one follower: π+2r ≺ ω+2r and ω+2r+1 ≺ π+2r+1
    rule out ranks a·k + b. The world of the closed program has a rank
    9⌊k/2⌋ + b(X, k mod 2). Mordido and Pérez fix the sequences n + 6k
    at new, n = 1, 3, 5 for the worker channels and n = 2, 4, 6 for the
    scheduler channels. We need no such choice: the world states the
    interleaving, and every instant of every channel is a point. Both
    semantics are synchronous (their Fig. 15). *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.cfst.CfstTools.

Set Default Proof Using "All".

Definition Wk : sty := SMu (SSeq (SSnd 0 TUnit) (SSeq (SRcv 0 TUnit) (SVar 0))).
Definition Sc : sty := SMu (SSeq (SSnd 0 TUnit) (SSeq (SSnd 0 TUnit) (SVar 0))).

(** The facts of round r over prev = 0, worker = 1, succ = 2. *)
Definition fround (r : nat) : list fact :=
  let e := 2 * r in
  [FLt (pv 0 e) (pv 1 e); FLt (pv 0 e) (pv 2 e);
   FLt (pv 1 e) (pv 0 (S e)); FLt (pv 1 e) (pv 2 e);
   FLt (pv 2 e) (pv 0 (S e)); FLt (pv 2 e) (pv 1 (S e));
   FLt (pv 1 (S e)) (pv 0 (S e)); FLt (pv 1 (S e)) (pv 2 (S e));
   FLt (pv 0 (S e)) (pv 1 (S (S e))); FLt (pv 0 (S e)) (pv 2 (S e));
   FLt (pv 2 (S e)) (pv 0 (S (S e))); FLt (pv 2 (S e)) (pv 1 (S (S e)))].

Definition fl_P (g : fact) : Prop :=
  (∃ r, g ∈ fround r) ∨
  (∃ k, g = FLt (pv 0 k) (pv 3 0) ∨ g = FLt (pv 1 k) (pv 3 0) ∨ g = FLt (pv 2 k) (pv 3 0)).
Definition fl_C : bcs := BCs [] fl_P.

Definition fl_body : ty :=
  TLolli (Some (pv 3 0)) None
    (TProd (TSess (dual Sc) (pv 0 0)) (TProd (TSess Wk (pv 1 0)) (TSess Sc (pv 2 0)))) TUnit.
Definition fl_ty : ty := TBox 4 0 fl_C (TLolli None None TUnit fl_body).

Definition follower : expr :=
  EBox (Lam (LetP (Var 0) (LetP (Var 0)
    (LetP (App ERecv (Var 3)) (LetU (Var 1)
    (LetP (Pair (App ESend (Pair EUnit (Var 3))) EUnit) (LetU (Var 0)
    (LetP (Pair (App ESend (Pair EUnit (Var 4))) EUnit) (LetU (Var 0)
    (LetP (App ERecv (Var 3)) (LetU (Var 1)
    (LetP (App ERecv (Var 6)) (LetU (Var 1)
      (App (App EForce (Var 15)) (Pair (Var 0) (Pair (Var 2) (App ESend (Pair EUnit (Var 5))))))))))))))))))).

Definition wk_P (g : fact) : Prop := ∃ k, g = FLt (pv 0 k) (pv 1 0).
Definition wk_C : bcs := BCs [] wk_P.
Definition wk_body : ty := TLolli (Some (pv 1 0)) None (TSess (dual Wk) (pv 0 0)) TUnit.
Definition wk_ty : ty := TBox 2 0 wk_C (TLolli None None TUnit wk_body).

Definition worker : expr :=
  EBox (Lam (LetP (App ERecv (Var 0)) (LetU (Var 1)
    (App (App EForce (Var 3)) (App ESend (Pair EUnit (Var 0))))))).

Lemma fround_shift r g :
  g ∈ fround r → fact_map (pt_inst (plist [pv 0 2; pv 1 2; pv 2 2; pv 3 0])) g ∈ fround (S r).
Proof.
  unfold fround. replace (2 * S r) with (S (S (2 * r))) by lia.
  intros Hg. repeat (apply elem_of_cons in Hg as [->|Hg]; [cbn; inlist|]).
  by apply elem_of_nil in Hg.
Qed.

Lemma fl_step g : fl_P g → fact_scoped 4 g →
  fl_P (fact_map (pt_inst (plist [pv 0 2; pv 1 2; pv 2 2; pv 3 0])) g).
Proof.
  intros [(r & Hg)|(k & [-> | [-> | ->]])] _.
  - left. exists (S r). by apply fround_shift.
  - right. exists (2 + k). cbn. by left.
  - right. exists (2 + k). cbn. by right; left.
  - right. exists (2 + k). cbn. by right; right.
Qed.

Lemma fl_ty_pscoped : pscoped 0 fl_ty.
Proof. split; [constructor|]. unfold fl_body. body_scope. Qed.

Lemma wk_ty_pscoped : pscoped 0 wk_ty.
Proof. split; [constructor|]. unfold wk_body. body_scope. Qed.

Lemma worker_typed W F : world_wf W → typed W ∅ [] ∅ [] F worker wk_ty.
Proof.
  intros HW. unfold worker, wk_ty.
  apply (t_box W _ _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|box_k0].
  fold wk_ty.
  change (lenv_pinst (pshift 2) [Some wk_ty]) with [Some (pinst_ty (pshift 2) wk_ty)].
  rewrite (pinst_closed _ wk_ty) by apply wk_ty_pscoped.
  change (bcs_inst (pshift 2) wk_C) with wk_C. cbn. unfold wk_body.
  eapply (tv_lam W HW _ _ _ _ _ _ _ _ None 1); [set_solver|cbn; set_solver|].
  cbn. tstep.
  { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (pv 0 0))
              (TSess (SSeq (SRcv 0 TUnit) (SSeq (SSnd 0 TUnit) (dual Wk))) (pv 0 0))).
    - eapply t_conv; [|tstep]. conv_sess.
    - apply KTRecv.
    - kscope.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 1 0). split; [done|]. right. hyp0 (pv 0 0) (pv 1 0). }
  cbn. tstep; [tstep|]. cbn.
  eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force0 W _ _ _ _ _ _ 2 wk_C None wk_body [pv 0 2; pv 1 0]);
      [done|done| | |apply ubs_none|tstep].
    + apply bcs_hold_self; [by left|vb_list|]. intros g (k & ->) _. by exists (S (S k)).
    + apply (skn_ids2 W _ wk_C); [by left|done|done].
  - eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pv 0 1)) (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) (dual Wk)) (pv 0 1)))).
    + tstep; tstep.
    + apply (KTSend _ _ _ 0 TUnit (dual Wk) (pv 0 1)). cbn. set_solver.
    + kscope.
    + apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 1 0). split; [done|]. right. hyp0 (pv 0 1) (pv 1 0).
  - apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (pv 1 0). split; [done|]. apply sle_refl, HW.
Qed.

Ltac flt x y :=
  eapply (sl_hyp0 _ _ fl_P [pv 0 0; pv 1 0; pv 2 0; pv 3 0] x y);
    [by left|first [left; exists 0; cbn; inlist|right; eexists; first [by left|by right; left|by right; right]]
    |fsc|done|done].

Ltac flg := match goal with |- slt _ _ ?a ?b => flt a b end.

Lemma fl_call W Ψ : (fl_C, ids 4) ∈ Ψ → bcs_hold (seqs W Ψ) (slt W Ψ) fl_C [pv 0 2; pv 1 2; pv 2 2; pv 3 0].
Proof. intros Hg. apply bcs_hold_self; [done|vb_list|exact fl_step]. Qed.

Lemma follower_typed W F : world_wf W → typed W ∅ [] ∅ [] F follower fl_ty.
Proof.
  intros HW. unfold follower, fl_ty.
  apply (t_box W _ _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|box_k0].
  fold fl_ty.
  change (lenv_pinst (pshift 4) [Some fl_ty]) with [Some (pinst_ty (pshift 4) fl_ty)].
  rewrite (pinst_closed _ fl_ty) by apply fl_ty_pscoped.
  change (bcs_inst (pshift 4) fl_C) with fl_C. cbn. unfold fl_body.
  eapply (tv_lam W HW _ _ _ _ _ _ _ _ None 1); [set_solver|cbn; set_solver|].
  cbn. tstep; [tstep|]. cbn. tstep; [tstep|]. cbn.
  (* 1. recv prev (Start) at π *)
  tstep.
  { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (pv 0 0))
              (TSess (SSeq (SRcv 0 TUnit) (SSeq (SRcv 0 TUnit) (dual Sc))) (pv 0 0))).
    - eapply t_conv; [|tstep]. conv_sess.
    - apply KTRecv.
    - kscope.
    - apply ubs_intro; [intros y Hy; mem_cases Hy; flg|].
      exists (pv 3 0). split; [done|]. right. flt (pv 0 0) (pv 3 0). }
  cbn. tstep; [tstep|]. cbn.
  (* 2. send wk (Start) at ω *)
  tstep.
  { tstep; [tstep|].
    eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pv 1 0))
              (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) (SSeq (SRcv 0 TUnit) Wk)) (pv 1 0)))).
    - tstep; [|tstep]. eapply t_conv; [|tstep]. conv_sess.
    - apply (KTSend _ _ _ 0 TUnit (SSeq (SRcv 0 TUnit) Wk) (pv 1 0)). cbn. set_solver.
    - kscope.
    - apply ubs_intro; [intros y Hy; mem_cases Hy; flg|].
      exists (pv 3 0). split; [done|]. right. flt (pv 1 0) (pv 3 0). }
  cbn. tstep; [tstep|]. cbn.
  (* 3. send succ (Start) at σ *)
  tstep.
  { tstep; [tstep|].
    eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pv 2 0))
              (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) (SSeq (SSnd 0 TUnit) Sc)) (pv 2 0)))).
    - tstep; [|tstep]. eapply t_conv; [|tstep]. conv_sess.
    - apply (KTSend _ _ _ 0 TUnit (SSeq (SSnd 0 TUnit) Sc) (pv 2 0)). cbn. set_solver.
    - kscope.
    - apply ubs_intro; [intros y Hy; mem_cases Hy; flg|].
      exists (pv 3 0). split; [done|]. right. flt (pv 2 0) (pv 3 0). }
  cbn. tstep; [tstep|]. cbn.
  (* 4. recv wk (ack) at ω+1 *)
  tstep.
  { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (pv 1 1)) (TSess (SSeq (SRcv 0 TUnit) Wk) (pv 1 1)));
      [tstep|apply KTRecv|kscope|].
    apply ubs_intro; [intros y Hy; mem_cases Hy; flg|].
    exists (pv 3 0). split; [done|]. right. flt (pv 1 1) (pv 3 0). }
  cbn. tstep; [tstep|]. cbn.
  (* 5. recv prev (Next) at π+1 *)
  tstep.
  { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (pv 0 1)) (TSess (SSeq (SRcv 0 TUnit) (dual Sc)) (pv 0 1)));
      [tstep|apply KTRecv|kscope|].
    apply ubs_intro; [intros y Hy; mem_cases Hy; flg|].
    exists (pv 3 0). split; [done|]. right. flt (pv 0 1) (pv 3 0). }
  cbn. tstep; [tstep|]. cbn.
  (* 6. send succ (Next) at σ+1 inside the argument, then the tail call *)
  eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force0 W _ _ _ _ _ _ 4 fl_C None fl_body [pv 0 2; pv 1 2; pv 2 2; pv 3 0]);
      [done|done| | |apply ubs_none|tstep].
    + apply fl_call. by left.
    + assert (∀ i, i < 4 → skn W [(fl_C, [pv 0 0; pv 1 0; pv 2 0; pv 3 0])] (pv i 2)) as Hs.
      { intros i Hi. apply (skn_in W _ fl_C [pv 0 0; pv 1 0; pv 2 0; pv 3 0] (pv i 0)); [by left| |done].
        destruct i as [|[|[|[|]]]]; try lia; inlist. }
      constructor; [apply Hs; lia|constructor; [apply Hs; lia|constructor; [apply Hs; lia|]]].
      constructor; [|constructor].
      apply (skn_in W _ fl_C [pv 0 0; pv 1 0; pv 2 0; pv 3 0] (pv 3 0)); [by left|inlist|done].
  - eapply (tv_pair W HW _ _ _ _ _ _ (TSess (dual Sc) (pv 0 2))); [reflexivity| |tstep].
    eapply (tv_pair W HW _ _ _ _ _ _ (TSess Wk (pv 1 2))); [reflexivity| |tstep].
    eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pv 2 1)) (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) Sc) (pv 2 1)))).
    + tstep; tstep.
    + apply (KTSend _ _ _ 0 TUnit Sc (pv 2 1)). cbn. set_solver.
    + kscope.
    + apply ubs_intro; [intros y Hy; mem_cases Hy; flg|].
      exists (pv 3 0). split; [done|]. right. flt (pv 2 1) (pv 3 0).
  - apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (pv 3 0). split; [done|]. apply sle_refl, HW.
Qed.

(** ** The ring for k = 3

    Channels A1, A2, A3 = 0, 1, 2 (scheduler i to worker i), C1, C2,
    C3 = 3, 4, 5 (scheduler i to scheduler i+1, with c the sender and
    d the receiver), and the ceiling z = 6.

      main = let (fl, wk) = ⟨follower, worker⟩ in
             let (a1, b1) = new ∗ in … let (c3, d3) = new ∗ in
             spawn (λu. leader);
             spawn (λu. (force fl) ⟨d1, ⟨a2, c2⟩⟩);
             spawn (λu. (force fl) ⟨d2, ⟨a3, c3⟩⟩);
             spawn (λu. (force wk) b1); spawn (λu. (force wk) b2);
             (force wk) b3

    The followers run at (C1, A2, C2) and (C2, A3, C3) from instant 0.
    The leader acts on A1 and C1 twice before it becomes a follower at
    (C3, A1, C1) with the instants (0, 2, 2). *)

Definition i2 : list point := [pc 3 0; pc 1 0; pc 4 0; pc 6 0].
Definition i3 : list point := [pc 4 0; pc 2 0; pc 5 0; pc 6 0].
Definition iL : list point := [pc 5 0; pc 0 2; pc 3 2; pc 6 0].

Definition lead_facts : list fact :=
  [FLt (pc 0 0) (pc 5 0); FLt (pc 0 0) (pc 3 0); FLt (pc 3 0) (pc 5 0); FLt (pc 3 0) (pc 0 1);
   FLt (pc 0 1) (pc 5 0); FLt (pc 0 1) (pc 3 1); FLt (pc 3 1) (pc 5 0); FLt (pc 3 1) (pc 0 2)].

Definition sch_L (x y : point) : Prop :=
  (∃ xs r, xs ∈ [i2; i3; iL] ∧ FLt x y ∈ fact_map (pt_inst (plist xs)) <$> fround r) ∨
  FLt x y ∈ lead_facts ∨
  (∃ a k, a < 6 ∧ x = pc a k ∧ y = pc 6 0).

Definition leader : expr :=
  LetP (Pair (App ESend (Pair EUnit (Var 12))) EUnit) (LetU (Var 0)
  (LetP (Pair (App ESend (Pair EUnit (Var 8))) EUnit) (LetU (Var 0)
  (LetP (App ERecv (Var 3)) (LetU (Var 1)
  (App (App EForce (Var 20)) (Pair (Var 7) (Pair (Var 0) (App ESend (Pair EUnit (Var 3))))))))))).

Definition sch_main : expr :=
  LetP (Pair follower worker)
  (LetP (App ENew EUnit) (LetP (App ENew EUnit) (LetP (App ENew EUnit)
  (LetP (App ENew EUnit) (LetP (App ENew EUnit) (LetP (App ENew EUnit)
  (LetU (App ESpawn (Lam (LetU (Var 0) leader)))
  (LetU (App ESpawn (Lam (LetU (Var 0) (App (App EForce (Var 14)) (Pair (Var 5) (Pair (Var 10) (Var 4)))))))
  (LetU (App ESpawn (Lam (LetU (Var 0) (App (App EForce (Var 14)) (Pair (Var 3) (Pair (Var 8) (Var 2)))))))
  (LetU (App ESpawn (Lam (LetU (Var 0) (App (App EForce (Var 13)) (Var 11)))))
  (LetU (App ESpawn (Lam (LetU (Var 0) (App (App EForce (Var 13)) (Var 9)))))
    (App (App EForce (Var 12)) (Var 6))))))))))))).

Section ring.
  Context (W : world) (HW : world_wf W).
  Context (Hk : ∀ a, a ≤ 6 → pt_known W (pc a 0)).
  Context (HL : ∀ x y, sch_L x y → w_lt W x y).

  Lemma fl_hold xs : xs ∈ [i2; i3; iL] → bcs_hold (seqs W []) (slt W []) fl_C xs.
  Proof.
    intros Hxs. apply bcs_hold_intro. intros g [(r & Hg)|(k & Hg)] _.
    - destruct g as [x y|x y].
      + apply sl_w, HL. left. exists xs, r. split; [done|].
        by apply (list_elem_of_fmap_2 (fact_map (pt_inst (plist xs))) _ (FLt x y)).
      + exfalso. unfold fround in Hg.
        repeat (apply elem_of_cons in Hg as [Hg|Hg]; [discriminate|]). by apply elem_of_nil in Hg.
    - repeat apply elem_of_cons in Hxs as [->|Hxs]; try (by apply elem_of_nil in Hxs);
        destruct Hg as [-> | [-> | ->]]; cbn; apply sl_w, HL; right; right;
        eexists _, _; (split; [|split; reflexivity]); lia.
  Qed.

  Lemma lead_lt Ψ x y : FLt x y ∈ lead_facts → slt W Ψ x y.
  Proof. intros H. apply sl_w, HL. by right; left. Qed.

  Lemma ceil_lt Ψ a k : a < 6 → slt W Ψ (pc a k) (pc 6 0).
  Proof. intros H. apply sl_w, HL. right; right. by exists a, k. Qed.

  Lemma round0_lt Ψ xs x y : xs ∈ [i2; i3; iL] → FLt x y ∈ fround 0 →
    slt W Ψ (pt_inst (plist xs) x) (pt_inst (plist xs) y).
  Proof.
    intros Hxs H. apply sl_w, HL. left. exists xs, 0. split; [done|].
    by apply (list_elem_of_fmap_2 (fact_map (pt_inst (plist xs))) _ (FLt x y)).
  Qed.

  Lemma wk_hold a : a < 6 → bcs_hold (seqs W []) (slt W []) wk_C [pc a 0; pc 6 0].
  Proof. intros Ha. apply bcs_hold_intro. intros g (k & ->) _. cbn. by apply ceil_lt. Qed.

  Lemma sch_typed : typed W ∅ [] ∅ [] (∅, None) sch_main TUnit.
  Proof.
    unfold sch_main.
    tstep.
    { tstep; [apply worker_typed, HW|apply follower_typed, HW]. }
    cbn. tstep.
    { tstep; [tstep|apply (KTNew _ _ _ Wk (pc 0 0) (or_introl (Hk 0 ltac:(lia))))|done|apply ubs_none]. }
    cbn. tstep.
    { tstep; [tstep|apply (KTNew _ _ _ Wk (pc 1 0) (or_introl (Hk 1 ltac:(lia))))|done|apply ubs_none]. }
    cbn. tstep.
    { tstep; [tstep|apply (KTNew _ _ _ Wk (pc 2 0) (or_introl (Hk 2 ltac:(lia))))|done|apply ubs_none]. }
    cbn. tstep.
    { tstep; [tstep|apply (KTNew _ _ _ Sc (pc 3 0) (or_introl (Hk 3 ltac:(lia))))|done|apply ubs_none]. }
    cbn. tstep.
    { tstep; [tstep|apply (KTNew _ _ _ Sc (pc 4 0) (or_introl (Hk 4 ltac:(lia))))|done|apply ubs_none]. }
    cbn. tstep.
    { tstep; [tstep|apply (KTNew _ _ _ Sc (pc 5 0) (or_introl (Hk 5 ltac:(lia))))|done|apply ubs_none]. }
    cbn.
    assert (∀ a, a < 6 → Forall (skn W []) [pc a 0; pc 6 0]) as HK2.
    { intros a Ha. constructor; [left; apply Hk; lia|constructor; [left; apply Hk; lia|constructor]]. }
    assert (∀ xs, xs ∈ [i2; i3; iL] → Forall (skn W []) xs) as HK4.
    { intros xs Hxs. repeat apply elem_of_cons in Hxs as [->|Hxs]; try (by apply elem_of_nil in Hxs);
        do 4 (constructor; [left; unfold pt_known; cbn; first [apply (Hk 0)|apply (Hk 1)|apply (Hk 2)
          |apply (Hk 3)|apply (Hk 4)|apply (Hk 5)|apply (Hk 6)]; lia|]); constructor. }
    (* the leader *)
    tstep.
    { tstep; [|apply KTSpawn|done|apply ubs_none].
      eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pc 6 0)) (Some (pc 0 0)) 0); [set_solver| |].
      { intros y Hy. mem_cases Hy; first [apply sle_refl, HW|right; apply lead_lt; inlist]. }
      cbn. tstep; [tstep|]. unfold leader. cbn.
      tstep.
      { tstep; [tstep|].
        eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pc 0 0))
                  (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) (SSeq (SRcv 0 TUnit) Wk)) (pc 0 0)))).
        - tstep; [|tstep]. eapply t_conv; [|tstep]. conv_sess.
        - apply (KTSend _ _ _ 0 TUnit (SSeq (SRcv 0 TUnit) Wk) (pc 0 0)). cbn. set_solver.
        - kscope.
        - apply ubs_intro; [intros y Hy; mem_cases Hy; apply lead_lt; inlist|].
          exists (pc 6 0). split; [done|]. right. apply ceil_lt. lia. }
      cbn. tstep; [tstep|]. cbn. tstep.
      { tstep; [tstep|].
        eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pc 3 0))
                  (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) (SSeq (SSnd 0 TUnit) Sc)) (pc 3 0)))).
        - tstep; [|tstep]. eapply t_conv; [|tstep]. conv_sess.
        - apply (KTSend _ _ _ 0 TUnit (SSeq (SSnd 0 TUnit) Sc) (pc 3 0)). cbn. set_solver.
        - kscope.
        - apply ubs_intro; [intros y Hy; mem_cases Hy; apply lead_lt; inlist|].
          exists (pc 6 0). split; [done|]. right. apply ceil_lt. lia. }
      cbn. tstep; [tstep|]. cbn. tstep.
      { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (pc 0 1)) (TSess (SSeq (SRcv 0 TUnit) Wk) (pc 0 1)));
          [tstep|apply KTRecv|kscope|].
        apply ubs_intro; [intros y Hy; mem_cases Hy; apply lead_lt; inlist|].
        exists (pc 6 0). split; [done|]. right. apply ceil_lt. lia. }
      cbn. tstep; [tstep|]. cbn.
      eapply tv_app; [exact HW|reflexivity| | |].
      - apply (typed_force0 W _ _ _ _ _ _ 4 fl_C None fl_body iL); [done|done| | |apply ubs_none|tstep].
        + apply fl_hold. inlist.
        + apply HK4. inlist.
      - eapply (tv_pair W HW _ _ _ _ _ _ (TSess (dual Sc) (pc 5 0))); [reflexivity| |tstep].
        eapply (tv_pair W HW _ _ _ _ _ _ (TSess Wk (pc 0 2))); [reflexivity| |tstep].
        eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pc 3 1)) (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) Sc) (pc 3 1)))).
        + tstep; tstep.
        + apply (KTSend _ _ _ 0 TUnit Sc (pc 3 1)). cbn. set_solver.
        + kscope.
        + apply ubs_intro; [intros y Hy; mem_cases Hy; apply lead_lt; inlist|].
          exists (pc 6 0). split; [done|]. right. apply ceil_lt. lia.
      - apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pc 6 0). split; [done|]. apply sle_refl, HW. }
    cbn. tstep.
    { tstep; [|apply KTSpawn|done|apply ubs_none].
      eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pc 6 0)) (Some (pc 3 0)) 0); [set_solver| |].
      { intros y Hy. mem_cases Hy; first [apply sle_refl, HW
          |right; apply (round0_lt [] i2 (pv 0 0) (pv 1 0)); inlist
          |right; apply (round0_lt [] i2 (pv 0 0) (pv 2 0)); inlist]. }
      cbn. tstep; [tstep|]. cbn.
      eapply tv_app; [exact HW|reflexivity| | |].
      - apply (typed_force0 W _ _ _ _ _ _ 4 fl_C None fl_body i2);
          [done|done|apply fl_hold; inlist|apply HK4; inlist|apply ubs_none|tstep].
      - tstep; [tstep; tstep|tstep].
      - apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pc 6 0). split; [done|]. apply sle_refl, HW. }
    cbn. tstep.
    { tstep; [|apply KTSpawn|done|apply ubs_none].
      eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pc 6 0)) (Some (pc 4 0)) 0); [set_solver| |].
      { intros y Hy. mem_cases Hy; first [apply sle_refl, HW
          |right; apply (round0_lt [] i3 (pv 0 0) (pv 1 0)); inlist
          |right; apply (round0_lt [] i3 (pv 0 0) (pv 2 0)); inlist]. }
      cbn. tstep; [tstep|]. cbn.
      eapply tv_app; [exact HW|reflexivity| | |].
      - apply (typed_force0 W _ _ _ _ _ _ 4 fl_C None fl_body i3);
          [done|done|apply fl_hold; inlist|apply HK4; inlist|apply ubs_none|tstep].
      - tstep; [tstep; tstep|tstep].
      - apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pc 6 0). split; [done|]. apply sle_refl, HW. }
    cbn. tstep.
    { tstep; [|apply KTSpawn|done|apply ubs_none].
      eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pc 6 0)) (Some (pc 0 0)) 0); [set_solver| |].
      { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
      cbn. tstep; [tstep|]. cbn.
      eapply tv_app; [exact HW|reflexivity| | |].
      - apply (typed_force0 W _ _ _ _ _ _ 2 wk_C None wk_body [pc 0 0; pc 6 0]);
          [done|done|apply wk_hold; lia|apply HK2; lia|apply ubs_none|tstep].
      - tstep.
      - apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pc 6 0). split; [done|]. apply sle_refl, HW. }
    cbn. tstep.
    { tstep; [|apply KTSpawn|done|apply ubs_none].
      eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pc 6 0)) (Some (pc 1 0)) 0); [set_solver| |].
      { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
      cbn. tstep; [tstep|]. cbn.
      eapply tv_app; [exact HW|reflexivity| | |].
      - apply (typed_force0 W _ _ _ _ _ _ 2 wk_C None wk_body [pc 1 0; pc 6 0]);
          [done|done|apply wk_hold; lia|apply HK2; lia|apply ubs_none|tstep].
      - tstep.
      - apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pc 6 0). split; [done|]. apply sle_refl, HW. }
    cbn. eapply tv_app; [exact HW|reflexivity| | |].
    - apply (typed_force0 W _ _ _ _ _ _ 2 wk_C None wk_body [pc 2 0; pc 6 0]);
        [done|done|apply wk_hold; lia|apply HK2; lia|apply ubs_none|tstep].
    - tstep.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|done].
  Qed.
End ring.

(** ** The world and its rank

    rk X k = 9⌊k/2⌋ + b(X, k mod 2) with (b0, b1) = (0,3), (3,6), (6,9)
    for A1, A2, A3 and (2,7), (5,10), (8,13) for C1, C2, C3. The
    ceiling z ranks above all of them. *)

Definition sch_b0 (a : nat) : nat :=
  match a with 0 => 0 | 1 => 3 | 2 => 6 | 3 => 2 | 4 => 5 | 5 => 8 | _ => 0 end.
Definition sch_b1 (a : nat) : nat :=
  match a with 0 => 3 | 1 => 6 | 2 => 9 | 3 => 7 | 4 => 10 | 5 => 13 | _ => 1 end.

Definition rk (a k : nat) : nat := 9 * Nat.div2 k + (if Nat.even k then sch_b0 a else sch_b1 a).

Definition sch_rank (x : point) : nat * nat :=
  match pt_root x with
  | NConst 6 => (1, pt_off x)
  | NConst a => (0, rk a (pt_off x))
  | _ => (0, pt_off x)
  end.

Definition Wsch : world := wgen (list_to_set (NConst <$> [0; 1; 2; 3; 4; 5; 6])) (λ _ _, False) sch_L.

Lemma div2_even_S k :
  (Nat.div2 (S k) = Nat.div2 k ∧ Nat.even k = true ∧ Nat.even (S k) = false) ∨
  (Nat.div2 (S k) = S (Nat.div2 k) ∧ Nat.even k = false ∧ Nat.even (S k) = true).
Proof.
  induction k as [|k [(H1 & H2 & H3)|(H1 & H2 & H3)]]; [by left|right|left].
  - change (Nat.div2 (S (S k))) with (S (Nat.div2 k)). change (Nat.even (S (S k))) with (Nat.even k).
    split_and!; congruence.
  - change (Nat.div2 (S (S k))) with (S (Nat.div2 k)). change (Nat.even (S (S k))) with (Nat.even k).
    split_and!; congruence.
Qed.

Lemma rk_S a k : rk a k < rk a (S k).
Proof.
  unfold rk. assert (sch_b0 a < sch_b1 a ∧ sch_b1 a < sch_b0 a + 9) as [Hb1 Hb2]
    by (destruct a as [|[|[|[|[|[|]]]]]]; cbn; lia).
  destruct (div2_even_S k) as [(H1 & H2 & H3)|(H1 & H2 & H3)]; rewrite H1, H2, H3; lia.
Qed.

Lemma rk_SS a n : rk a (S (S n)) = 9 + rk a n.
Proof. unfold rk. cbn [Nat.div2 Nat.even]. lia. Qed.

Lemma Wsch_strict : strict Wsch.
Proof.
  apply (wgen_strict_lex _ _ _ id sch_rank); try done.
  - intros p Hp. apply elem_of_list_to_set, list_elem_of_fmap in Hp as (a & -> & _). by exists a.
  - intros x y Hxy. right. rewrite !elem_of_list_to_set.
    destruct Hxy as [(xs & r & Hxs & Hg)|[Hg|(a & k & Ha & -> & ->)]].
    + apply list_elem_of_fmap in Hg as (g & Hg & Hm). unfold fround in Hm.
      repeat apply elem_of_cons in Hxs as [->|Hxs]; try (by apply elem_of_nil in Hxs);
        (repeat (apply elem_of_cons in Hm as [->|Hm]; [injection Hg as -> ->; cbn; set_solver|]));
        by apply elem_of_nil in Hm.
    + repeat (apply elem_of_cons in Hg as [Hg|Hg]; [injection Hg as -> ->; cbn; set_solver|]).
      by apply elem_of_nil in Hg.
    + cbn. destruct a as [|[|[|[|[|[|]]]]]]; try lia; set_solver.
  - intros x. unfold lexlt, sch_rank, pt_shift, pt_root. cbn [pt_name pt_off].
    rewrite Nat.add_1_r.
    destruct (pn_root (pt_name x)) as [[|[|[|[|[|[|[|a]]]]]]]| |]; cbn [fst snd]; right;
      (split; [done|]); first [apply rk_S|lia].
  - intros x y Hxy. unfold id.
    destruct Hxy as [(xs & r & Hxs & Hg)|[Hg|(a & k & Ha & -> & ->)]].
    + apply list_elem_of_fmap in Hg as (g & Hg & Hm). unfold fround in Hm.
      remember (2 * r) as e eqn:He.
      assert (Nat.div2 e = r ∧ Nat.even e = true) as [Hd0 He0].
      { subst e. split; [apply Nat.div2_double|]. apply Nat.even_spec. by exists r. }
      assert (Nat.div2 (S e) = r ∧ Nat.even (S e) = false) as [Hd1 He1].
      { destruct (div2_even_S e) as [(H1 & H2 & H3)|(H1 & H2 & H3)]; [|congruence].
        split; [congruence|done]. }
      assert (∀ a, rk a e = 9 * r + sch_b0 a) as Hr0 by (intros a; unfold rk; by rewrite Hd0, He0).
      assert (∀ a, rk a (S e) = 9 * r + sch_b1 a) as Hr1 by (intros a; unfold rk; by rewrite Hd1, He1).
      clear Hd0 He0 Hd1 He1 He.
      repeat apply elem_of_cons in Hxs as [->|Hxs]; try (by apply elem_of_nil in Hxs);
        (repeat (apply elem_of_cons in Hm as [->|Hm];
           [injection Hg as -> ->; unfold lexlt, sch_rank; cbn -[rk];
            rewrite ?rk_SS, ?Hr0, ?Hr1; cbn; lia|]));
        by apply elem_of_nil in Hm.
    + repeat (apply elem_of_cons in Hg as [Hg|Hg]; [injection Hg as -> ->; unfold lexlt, sch_rank, rk; cbn; lia|]).
      by apply elem_of_nil in Hg.
    + unfold lexlt, sch_rank. cbn. destruct a as [|[|[|[|[|[|]]]]]]; cbn; lia.
Qed.

Lemma sch_deadlock_free : deadlock_free (∅, {[+ sch_main +]}).
Proof.
  apply (soundness Wsch _ TUnit Wsch_strict).
  apply ptyped_closed; [constructor|]. apply sch_typed; [apply Wsch_strict| |].
  - intros a Ha. unfold pt_known, Wsch. simpl.
    destruct a as [|[|[|[|[|[|[|]]]]]]]; try lia; set_solver.
  - intros x y H. by apply glt_base.
Qed.
