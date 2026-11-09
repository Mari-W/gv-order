(** * Milner's cyclic scheduler (Mordido and Pérez 2026, A.5, pp. 37–39)

    Three partial schedulers in a ring and three workers. A unary
    choice carries no information, and K4 gives select the readiness
    and cost of send and branch those of receive. So select Start and
    select Next become sends of ∗, and the branches on them become
    receives. The acknowledgement () is ∗.

      Wk = µX. !∗;?∗;X     (scheduler to worker, Start and then the ack)
      Sc = µX. !∗;!∗;X     (scheduler to its successor, Start and then Next)

      follower : □(∀π ω σ ζ. C. ∗ ⊸ (S̄c@π ⊗ Wk@ω ⊗ Sc@σ ⊸^ζ ∗))
      follower = !(f = λ⟨prev, ⟨wk, succ⟩⟩.
                   recv prev; send wk; send succ; recv wk; recv prev;
                   (force f) ⟨prev, ⟨wk, send succ⟩⟩)
      worker   : □(∀κ ζ. {κ+k ≺ ζ ∣ k}. ∗ ⊸ (W̄k@κ ⊸^ζ ∗))
      worker   = !(w = λx. recv x; (force w) (send x))
      leader   = send a1; send c1; recv a1; (force follower) ⟨d3, ⟨a1, send c1⟩⟩

    C holds, for every round r, the twelve facts that make each action
    of a round lie below the two channels the follower still holds,
    at the instants 2r and 2r+1 of each channel, and the ceiling ζ
    above all of them. The instants alternate between the channels, so
    C needs the parity of the instant. No linear rank of the instants
    meets it, already for one follower. π+2r ≺ ω+2r and
    ω+2r+1 ≺ π+2r+1 rule out ranks a·k + b. The closed program uses the
    rank 9⌊k/2⌋ + b(X, k mod 2). The ceiling is a top-level point z
    that no channel occupies. Each channel is created with the facts
    that order its instants against the instants of the channels that
    exist already, by this rank, and with every instant below z
    ([sch_C]). Mordido and Pérez fix the sequences n + 6k at new,
    n = 1, 3, 5 for the worker channels and n = 2, 4, 6 for the
    scheduler channels. The creation constraints fix an order at new
    in the same way. The facts the program uses are not enough as
    creation constraints. A later channel derives facts between earlier
    channels, which conservativity asks the earlier constraints to
    state already. Both semantics are synchronous (their Fig. 15).

    With end points the gates compare a blocking point with the partner
    points of the other held ends. C and the creation constraints state
    every fact between all polarities of its two points. The ranks
    ignore polarity, so the same rank orders them. *)

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

(** With end points every fact holds between all polarities of its two
    points, which covers the gates u ≺ v̄ and the ends the caller
    passes at either polarity. *)
Definition fl_P (g : fact) : Prop :=
  (∃ r x y c c', FLt x y ∈ fround r ∧ g = FLt (pt_polar c x) (pt_polar c' y)) ∨
  (∃ k c, g = FLt (pt_polar c (pv 0 k)) (pv 3 0) ∨ g = FLt (pt_polar c (pv 1 k)) (pv 3 0) ∨
          g = FLt (pt_polar c (pv 2 k)) (pv 3 0)).
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

Lemma sc_inst_polar σ c x : pt_inst σ (pt_polar c x) = pt_polar c (pt_inst σ x).
Proof. destruct c; [done|apply pt_inst_dual]. Qed.

Lemma fl_step g : fl_P g → fact_scoped 4 g →
  fl_P (fact_map (pt_inst (plist [pv 0 2; pv 1 2; pv 2 2; pv 3 0])) g).
Proof.
  intros [(r & x & y & c & c' & Hg & ->)|(k & c & [-> | [-> | ->]])] _; cbn [fact_map]; rewrite ?sc_inst_polar.
  - left. eexists (S r), _, _, c, c'. split; [apply (fround_shift r (FLt x y) Hg)|reflexivity].
  - right. exists (2 + k), c. by left.
  - right. exists (2 + k), c. by right; left.
  - right. exists (2 + k), c. by right; right.
Qed.

Lemma fl_ty_pscoped : pscoped 0 fl_ty.
Proof. split; [constructor|]. unfold fl_body. body_scope. Qed.

Lemma wk_ty_pscoped : pscoped 0 wk_ty.
Proof. split; [constructor|]. unfold wk_body. body_scope. Qed.

Lemma worker_typed W F : world_wf W → typed W ∅ [] ∅ [] F worker wk_ty.
Proof.
  intros HW. unfold worker, wk_ty.
  apply (t_exp W _ _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|box_k0].
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
    [by left
    |first [left; first [eexists 0, _, _, true, true; (split; [|reflexivity]); cbn; inlist
                        |eexists 0, _, _, true, false; (split; [|reflexivity]); cbn; inlist
                        |eexists 0, _, _, false, true; (split; [|reflexivity]); cbn; inlist
                        |eexists 0, _, _, false, false; (split; [|reflexivity]); cbn; inlist]
           |right; first [eexists _, true; first [by left|by right; left|by right; right]
                         |eexists _, false; first [by left|by right; left|by right; right]]]
    |fsc|done|done].

Ltac flg := match goal with |- slt _ _ ?a ?b => flt a b end.

Lemma fl_call W Ψ : (fl_C, ids 4) ∈ Ψ → bcs_hold (seqs W Ψ) (slt W Ψ) fl_C [pv 0 2; pv 1 2; pv 2 2; pv 3 0].
Proof. intros Hg. apply bcs_hold_self; [done|vb_list|exact fl_step]. Qed.

Lemma follower_typed W F : world_wf W → typed W ∅ [] ∅ [] F follower fl_ty.
Proof.
  intros HW. unfold follower, fl_ty.
  apply (t_exp W _ _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|box_k0].
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

(** ** The ranks

    rk X k = 9⌊k/2⌋ + b(X, k mod 2) with (b0, b1) = (0,3), (3,6), (6,9)
    for A1, A2, A3 = 0, 1, 2 and (2,7), (5,10), (8,13) for C1, C2,
    C3 = 3, 4, 5. *)

Definition sch_b0 (a : nat) : nat :=
  match a with 0 => 0 | 1 => 3 | 2 => 6 | 3 => 2 | 4 => 5 | 5 => 8 | _ => 0 end.
Definition sch_b1 (a : nat) : nat :=
  match a with 0 => 3 | 1 => 6 | 2 => 9 | 3 => 7 | 4 => 10 | 5 => 13 | _ => 1 end.

Definition rk (a k : nat) : nat := 9 * Nat.div2 k + (if Nat.even k then sch_b0 a else sch_b1 a).

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

Lemma rk_mono a k l : k < l → rk a k < rk a l.
Proof.
  intros H. induction H as [|l _ IH]; [apply rk_S|]. eapply Nat.lt_trans; [exact IH|apply rk_S].
Qed.

Lemma rk_lt_inv a k l : rk a k < rk a l → k < l.
Proof.
  intros H. destruct (decide (k < l)) as [|Hn]; [done|].
  destruct (decide (k = l)) as [->|Hne]; [lia|]. pose proof (rk_mono a l k ltac:(lia)). lia.
Qed.

(** ** The creation constraints of the ring

    The channels are created in the order A1, A2, A3, C1, C2, C3 under
    the top-level ceiling z. When channel a is created, the channels
    b < a exist, and its constraint relates every instant of a to every
    instant of every b by rank and puts every instant of a below z.
    Under the binder of channel a, channel b is the variable a - b and
    z is a + 1. This is the priority assignment of Mordido and Pérez at
    new. The facts the followers and the leader use relate no two of
    A1, A2, A3. The constraint of C1 alone would derive facts between
    A1 and A2 through C1, and conservativity asks for them before C1
    exists ([sch_ok]). The rank states them. *)
(** Under syntactic points the ring's channels and z are constants: the
    ladder [cl_Ψ] of CfstTools.v with N = 6, where channel b is the
    constant 5 - b and z is 6 (sharp edges 173). *)
Definition sch_Ψ (a : nat) : hyps := cl_Ψ rk 6 a.

Lemma length_ids n : length (ids n) = n.
Proof. unfold ids. by rewrite length_fmap, length_seq. Qed.

Lemma ids_shift n : pvar 0 :: (pt_inst (pshift 1) <$> ids n) = ids (S n).
Proof.
  unfold ids. simpl. f_equal. rewrite <-list_fmap_compose. apply list_eq. intros i.
  rewrite !list_lookup_fmap. destruct (decide (i < n)).
  - rewrite !lookup_seq_lt by lia. cbn. rewrite pt_shift_0. unfold pshift. by rewrite Nat.add_1_r.
  - rewrite !lookup_seq_ge by lia. done.
Qed.

Lemma open_ids n x : pn_vb (S n) (pt_name x) → pt_inst (pup 1 (plist (ids n))) x = x.
Proof.
  intros Hx. rewrite <-(pt_inst_pvar x) at 2. apply pt_inst_ext_root. intros a Ha.
  pose proof (pn_vb_root _ _ _ Hx Ha) as Hlt. unfold pup. case_decide as Ha1; [done|].
  unfold plist, ids. rewrite list_lookup_fmap, lookup_seq_lt by lia. cbn.
  rewrite pt_shift_0. unfold pvar. do 2 f_equal. lia.
Qed.

Lemma slt_ofs W Ψ c k l : world_wf W → k < l → slt W Ψ (pv c k) (pv c l).
Proof.
  intros HW H. induction H as [|l _ IH].
  - pose proof (slt_po W Ψ (pv c k) HW) as G. unfold pt_shift in G. simpl in G. by rewrite Nat.add_1_r in G.
  - eapply sl_trans; [exact IH|]. pose proof (slt_po W Ψ (pv c l) HW) as G.
    unfold pt_shift in G. simpl in G. by rewrite Nat.add_1_r in G.
Qed.

(** Program order along offsets, between any polarities. *)
Lemma slt_ofs_any W Ψ v c c' k l : world_wf W → k < l → slt W Ψ (pt_polar c (pv v k)) (pt_polar c' (pv v l)).
Proof.
  intros HW H.
  assert (∀ m d d', slt W Ψ (pt_polar d (pv v m)) (pt_polar d' (pv v (S m)))) as Hs.
  { intros m [] [];
      [pose proof (slt_po W Ψ (pv v m) HW) as G|pose proof (sl_dpo W Ψ (pv v m)) as G
      |pose proof (sl_dpo W Ψ (pt_dual (pv v m))) as G|pose proof (slt_po W Ψ (pt_dual (pv v m)) HW) as G];
      unfold pt_shift, pt_dual in G; simpl in G; rewrite Nat.add_1_r in G; exact G. }
  revert c'. induction H as [|l _ IH]; intros c'; [apply Hs|].
  eapply sl_trans; [apply (IH true)|apply Hs].
Qed.

Lemma pv_lift_polar c v k : pt_inst (λ a, pvar (a + 1)) (pt_polar c (pv v k)) = pt_polar c (pv (S v) k).
Proof. rewrite sc_inst_polar. unfold pt_inst. cbn. by rewrite Nat.add_1_r. Qed.

Lemma pv_shift_polar c v k : pt_inst (pshift 1) (pt_polar c (pv v k)) = pt_polar c (pv (S v) k).
Proof. rewrite sc_inst_polar. unfold pt_inst, pshift. cbn. by rewrite Nat.add_1_r. Qed.

Lemma slt_shift W Ψ L x y :
  strict W → slt W Ψ x y → slt W (hyps_inst (pshift 1) Ψ ++ L) (pt_inst (pshift 1) x) (pt_inst (pshift 1) y).
Proof.
  intros HW H. apply (slt_pinst_s W W (pshift 1) (proj1 HW) (wext_refl _ HW) Ψ); [|exact H].
  apply hyps_hold_sub. intros g Hg. apply elem_of_app. by left.
Qed.

Lemma pv_shift c k : pt_inst (pshift 1) (pv c k) = pv (S c) k.
Proof. unfold pt_inst, pshift. cbn. by rewrite Nat.add_1_r. Qed.

Lemma pv_lift c k : pt_inst (λ a, pvar (a + 1)) (pv c k) = pv (S c) k.
Proof. unfold pt_inst. cbn. by rewrite Nat.add_1_r. Qed.

(** ** The ring for k = 3

      main = let (fl, wk) = ⟨follower, worker⟩ in
             let (a1, b1) = new ∗ in … let (c3, d3) = new ∗ in
             spawn (λu. leader);
             spawn (λu. (force fl) ⟨d1, ⟨a2, c2⟩⟩);
             spawn (λu. (force fl) ⟨d2, ⟨a3, c3⟩⟩);
             spawn (λu. (force wk) b1); spawn (λu. (force wk) b2);
             (force wk) b3

    The followers run at (C1, A2, C2) and (C2, A3, C3) from instant 0.
    The leader acts on A1 and C1 twice before it becomes a follower at
    (C3, A1, C1) with the instants (0, 2, 2). After the six [new]s
    channel b is the variable 5 - b, so A1, A2, A3, C1, C2, C3 are 5, 4,
    3, 2, 1, 0, and z is 6. *)

Definition i2 : list point := [pt_dual (pc 2 0); pc 4 0; pc 1 0; pc 6 0].
Definition i3 : list point := [pt_dual (pc 1 0); pc 3 0; pc 0 0; pc 6 0].
Definition iL : list point := [pt_dual (pc 0 0); pc 5 2; pc 2 2; pc 6 0].

Definition lead_facts : list fact :=
  [FLt (pc 5 0) (pc 0 0); FLt (pc 5 0) (pc 2 0); FLt (pc 2 0) (pc 0 0); FLt (pc 2 0) (pc 5 1);
   FLt (pc 5 1) (pc 0 0); FLt (pc 5 1) (pc 2 1); FLt (pc 2 1) (pc 0 0); FLt (pc 2 1) (pc 5 2)].

Definition leader : expr :=
  LetP (Pair (App ESend (Pair EUnit (Var 12))) EUnit) (LetU (Var 0)
  (LetP (Pair (App ESend (Pair EUnit (Var 8))) EUnit) (LetU (Var 0)
  (LetP (App ERecv (Var 3)) (LetU (Var 1)
  (App (App EForce (Var 20)) (Pair (Var 7) (Pair (Var 0) (App ESend (Pair EUnit (Var 3))))))))))).

Definition sch_main : expr :=
  LetP (Pair follower worker)
  (let_new_pair_at (EPt (pconst 5)) (let_new_pair_at (EPt (pconst 4)) (let_new_pair_at (EPt (pconst 3))
  (let_new_pair_at (EPt (pconst 2)) (let_new_pair_at (EPt (pconst 1)) (let_new_pair_at (EPt (pconst 0))
  (LetU (App ESpawn (Lam (LetU (Var 0) leader)))
  (LetU (App ESpawn (Lam (LetU (Var 0) (App (App EForce (Var 14)) (Pair (Var 5) (Pair (Var 10) (Var 4)))))))
  (LetU (App ESpawn (Lam (LetU (Var 0) (App (App EForce (Var 14)) (Pair (Var 3) (Pair (Var 8) (Var 2)))))))
  (LetU (App ESpawn (Lam (LetU (Var 0) (App (App EForce (Var 13)) (Var 11)))))
  (LetU (App ESpawn (Lam (LetU (Var 0) (App (App EForce (Var 13)) (Var 9)))))
    (App (App EForce (Var 12)) (Var 6))))))))))))).

Section ring.
  Context (W : world) (HW : world_wf W) (Ψ : hyps).
  Context (HR : ∀ b b' k l c c', b < 6 → b' < 6 → rk b k < rk b' l →
                  slt W Ψ (pt_polar c (pc (5 - b) k)) (pt_polar c' (pc (5 - b') l))).
  Context (Hz : ∀ b k c, b < 6 → slt W Ψ (pt_polar c (pc (5 - b) k)) (pc 6 0)).

  (** A fact between two channel points whose ranks rise, at any
      polarities. *)
  Ltac hr := match goal with |- slt _ _ (MkPt (NConst ?v) ?cb ?k) (MkPt (NConst ?w) ?cb' ?l) =>
    apply (HR (5 - v) (5 - w) k l cb cb'); [cbn; lia|cbn; lia|] end.

  Lemma fl_hold xs : xs ∈ [i2; i3; iL] → bcs_hold (seqs W Ψ) (slt W Ψ) fl_C xs.
  Proof.
    intros Hxs. apply bcs_hold_intro. intros g [(r & x & y & c & c' & Hm & ->)|(k & c & Hg)] _.
    - unfold fround in Hm. remember (2 * r) as e eqn:He.
      assert (Nat.div2 e = r ∧ Nat.even e = true) as [Hd0 He0].
      { subst e. split; [apply Nat.div2_double|]. apply Nat.even_spec. by exists r. }
      assert (Nat.div2 (S e) = r ∧ Nat.even (S e) = false) as [Hd1 He1].
      { destruct (div2_even_S e) as [(H1 & H2 & H3)|(H1 & H2 & H3)]; [|congruence].
        split; [congruence|done]. }
      assert (∀ a, rk a e = 9 * r + sch_b0 a) as Hr0 by (intros a; unfold rk; by rewrite Hd0, He0).
      assert (∀ a, rk a (S e) = 9 * r + sch_b1 a) as Hr1 by (intros a; unfold rk; by rewrite Hd1, He1).
      clear Hd0 He0 Hd1 He1 He.
      repeat apply elem_of_cons in Hxs as [->|Hxs]; try (by apply elem_of_nil in Hxs);
        (repeat (apply elem_of_cons in Hm as [Hm|Hm];
           [injection Hm as -> ->; destruct c, c';
            cbn [fact_map fact_holds]; unfold i2, i3, iL, pt_inst, pt_shift, pt_polar, pt_dual; cbn; hr;
            rewrite ?rk_SS, ?Hr0, ?Hr1; cbn; lia|]));
        by apply elem_of_nil in Hm.
    - repeat apply elem_of_cons in Hxs as [->|Hxs]; try (by apply elem_of_nil in Hxs);
        destruct Hg as [-> | [-> | ->]]; destruct c; cbn [fact_map fact_holds]; unfold i2, i3, iL, pt_inst, pt_shift, pt_polar, pt_dual; cbn;
        match goal with |- slt _ _ (MkPt (NConst ?v) ?cb ?k) _ => apply (Hz (5 - v) k cb); cbn; lia end.
  Qed.

  Lemma hr_pt v w k l c c' : v < 6 → w < 6 → rk (5 - v) k < rk (5 - w) l →
    slt W Ψ (pt_polar c (pc v k)) (pt_polar c' (pc w l)).
  Proof. intros Hv Hw H. replace v with (5 - (5 - v)) by lia. replace w with (5 - (5 - w)) by lia. apply HR; lia. Qed.

  Lemma lead_lt c c' x y : FLt x y ∈ lead_facts → slt W Ψ (pt_polar c x) (pt_polar c' y).
  Proof.
    intros H. repeat (apply elem_of_cons in H as [H|H];
      [injection H as -> ->; apply hr_pt; [lia|lia|vm_compute; lia]|]).
    by apply elem_of_nil in H.
  Qed.

  Lemma ceil_lt v k c : v < 6 → slt W Ψ (pt_polar c (pc v k)) (pc 6 0).
  Proof. intros H. replace v with (5 - (5 - v)) by lia. apply Hz. lia. Qed.

  Lemma round0_lt xs x y : xs ∈ [i2; i3; iL] → FLt x y ∈ fround 0 →
    slt W Ψ (pt_inst (plist xs) x) (pt_inst (plist xs) y).
  Proof.
    intros Hxs H. pose proof (fl_hold xs Hxs (FLt x y)) as G. apply G.
    apply bcs_open_nil. split; [left; exists 0, x, y, true, true; by split|].
    assert (length xs = 4) as ->
      by (repeat apply elem_of_cons in Hxs as [->|Hxs]; try (by apply elem_of_nil in Hxs); done).
    unfold fround in H. repeat (apply elem_of_cons in H as [H|H]; [injection H as -> ->; cbn; lia|]).
    by apply elem_of_nil in H.
  Qed.

  Lemma wk_hold v c : v < 6 → bcs_hold (seqs W Ψ) (slt W Ψ) wk_C [pt_polar c (pc v 0); pc 6 0].
  Proof. intros Hv. apply bcs_hold_intro. intros g (k & ->) _. destruct c; [exact (ceil_lt v k true Hv)|exact (ceil_lt v k false Hv)]. Qed.
End ring.

(** A rank fact or a ceiling fact at the polarities of the goal. *)
Ltac hrp HRP := first [apply (HRP _ _ _ _ true true)|apply (HRP _ _ _ _ true false)
                      |apply (HRP _ _ _ _ false true)|apply (HRP _ _ _ _ false false)];
  [lia|lia|vm_compute; lia].
Ltac clp CL := first [apply (CL _ _ true)|apply (CL _ _ false)]; lia.

(** The six channels and z are the top-level points of the program
    ([created], sharp edges 172). *)
Lemma sch_created a : a ≤ 6 → created (Wpo []) (sch_Ψ a).
Proof. apply (cl_created rk rk_S 6). Qed.

(** One [new] of the ring: channel a at its point variable k = 5 - a
    with the session type St. *)
Ltac sch_new W HWs K St k :=
  apply (t_new_at W _ _ _ _ _ _ _ St (pconst k) HWs);
    [ground|apply (cl_skn rk rk_S 6 W 6 _ (6 - k)); [lia|lia|cbn; f_equal; lia]|];
  cbn -[sch_Ψ cl_C wk_ty fl_ty].

Lemma sch_typed : styped ∅ (sch_Ψ 6) [] (∅, None) sch_main TUnit.
Proof.
  apply styped_Wpo. pose proof Wpo_nil_strict' as HWs.
  pose proof (proj1 HWs) as HW. set (W := Wpo []) in *. unfold sch_main, let_new_pair_at.
  tstep.
  { tstep; apply typed_hyps_wk; [exact HWs|apply worker_typed, HW|exact HWs|apply follower_typed, HW]. }
  pose proof (cl_inv_all rk rk_S 6 W 6 HWs ltac:(lia)) as I6.
  cbn -[sch_Ψ cl_C wk_ty fl_ty].
  sch_new W HWs K6 Wk 5. sch_new W HWs K6 Wk 4. sch_new W HWs K6 Wk 3.
  sch_new W HWs K6 Sc 2. sch_new W HWs K6 Sc 1. sch_new W HWs K6 Sc 0.
  destruct I6 as [HR Hz].
  pose proof (fl_hold W HW _ HR Hz) as FH. pose proof (hr_pt W HW _ HR Hz) as HRP.
  pose proof (ceil_lt W HW _ HR Hz) as CL.
  pose proof (wk_hold W HW _ HR Hz) as WH.
  assert (∀ v k c, v ≤ 6 → skn W (sch_Ψ 6) (pt_polar c (pc v k))) as HKv.
  { intros v k c Hv. apply (cl_skn rk rk_S 6 W 6 _ (6 - v)); [lia|lia|destruct c; cbn; f_equal; lia]. }
  assert (∀ v c, v < 6 → Forall (skn W (sch_Ψ 6)) [pt_polar c (pc v 0); pc 6 0]) as HK2.
  { intros v c Hv. constructor; [apply HKv; lia|constructor; [apply (HKv _ _ true); lia|constructor]]. }
  assert (∀ xs, xs ∈ [i2; i3; iL] → Forall (skn W (sch_Ψ 6)) xs) as HK4.
  { intros xs Hxs. repeat apply elem_of_cons in Hxs as [->|Hxs]; try (by apply elem_of_nil in Hxs);
      unfold i2, i3, iL; repeat (constructor; [first [apply (HKv _ _ true); lia|apply (HKv _ _ false); lia]|]); constructor. }
  (* the leader *)
  tstep.
  { tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pc 6 0)) (Some (pt_dual (pc 5 0))) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy; first [apply sle_refl, HW|right; hrp HRP]. }
    cbn. tstep; [tstep|]. unfold leader. cbn.
    tstep.
    { tstep; [tstep|].
      eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pc 5 0))
                (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) (SSeq (SRcv 0 TUnit) Wk)) (pc 5 0)))).
      - tstep; [|tstep]. eapply t_conv; [|tstep]. conv_sess.
      - apply (KTSend _ _ _ 0 TUnit (SSeq (SRcv 0 TUnit) Wk) (pc 5 0)). cbn. set_solver.
      - kscope.
      - apply ubs_intro; [intros y Hy; mem_cases Hy; hrp HRP|].
        exists (pc 6 0). split; [done|]. right. clp CL. }
    cbn. tstep; [tstep|]. cbn. tstep.
    { tstep; [tstep|].
      eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pc 2 0))
                (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) (SSeq (SSnd 0 TUnit) Sc)) (pc 2 0)))).
      - tstep; [|tstep]. eapply t_conv; [|tstep]. conv_sess.
      - apply (KTSend _ _ _ 0 TUnit (SSeq (SSnd 0 TUnit) Sc) (pc 2 0)). cbn. set_solver.
      - kscope.
      - apply ubs_intro; [intros y Hy; mem_cases Hy; hrp HRP|].
        exists (pc 6 0). split; [done|]. right. clp CL. }
    cbn. tstep; [tstep|]. cbn. tstep.
    { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (pc 5 1)) (TSess (SSeq (SRcv 0 TUnit) Wk) (pc 5 1)));
        [tstep|apply KTRecv|kscope|].
      apply ubs_intro; [intros y Hy; mem_cases Hy; hrp HRP|].
      exists (pc 6 0). split; [done|]. right. clp CL. }
    cbn. tstep; [tstep|]. cbn.
    eapply tv_app; [exact HW|reflexivity| | |].
    - apply (typed_force0 W _ _ _ _ _ _ 4 fl_C None fl_body iL); [done|done| | |apply ubs_none|tstep].
      + apply FH. inlist.
      + apply HK4. inlist.
    - eapply (tv_pair W HW _ _ _ _ _ _ (TSess (dual Sc) (pt_dual (pc 0 0)))); [reflexivity| |tstep].
      eapply (tv_pair W HW _ _ _ _ _ _ (TSess Wk (pc 5 2))); [reflexivity| |tstep].
      eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pc 2 1)) (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) Sc) (pc 2 1)))).
      + tstep; tstep.
      + apply (KTSend _ _ _ 0 TUnit Sc (pc 2 1)). cbn. set_solver.
      + kscope.
      + apply ubs_intro; [intros y Hy; mem_cases Hy; hrp HRP|].
        exists (pc 6 0). split; [done|]. right. clp CL.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pc 6 0). split; [done|]. apply sle_refl, HW. }
  cbn. tstep.
  { tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pc 6 0)) (Some (pc 2 0)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy; first [apply sle_refl, HW
        |right; hrp HRP]. }
    cbn. tstep; [tstep|]. cbn.
    eapply tv_app; [exact HW|reflexivity| | |].
    - apply (typed_force0 W _ _ _ _ _ _ 4 fl_C None fl_body i2);
        [done|done|apply FH; inlist|apply HK4; inlist|apply ubs_none|tstep].
    - tstep; [tstep; tstep|tstep].
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pc 6 0). split; [done|]. apply sle_refl, HW. }
  cbn. tstep.
  { tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pc 6 0)) (Some (pc 1 0)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy; first [apply sle_refl, HW
        |right; hrp HRP]. }
    cbn. tstep; [tstep|]. cbn.
    eapply tv_app; [exact HW|reflexivity| | |].
    - apply (typed_force0 W _ _ _ _ _ _ 4 fl_C None fl_body i3);
        [done|done|apply FH; inlist|apply HK4; inlist|apply ubs_none|tstep].
    - tstep; [tstep; tstep|tstep].
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pc 6 0). split; [done|]. apply sle_refl, HW. }
  cbn. tstep.
  { tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pc 6 0)) (Some (pc 5 0)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep; [tstep|]. cbn.
    eapply tv_app; [exact HW|reflexivity| | |].
    - apply (typed_force0 W _ _ _ _ _ _ 2 wk_C None wk_body [pt_dual (pc 5 0); pc 6 0]);
        [done|done|apply (WH _ false); lia|apply (HK2 _ false); lia|apply ubs_none|tstep].
    - tstep.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pc 6 0). split; [done|]. apply sle_refl, HW. }
  cbn. tstep.
  { tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pc 6 0)) (Some (pc 4 0)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep; [tstep|]. cbn.
    eapply tv_app; [exact HW|reflexivity| | |].
    - apply (typed_force0 W _ _ _ _ _ _ 2 wk_C None wk_body [pt_dual (pc 4 0); pc 6 0]);
        [done|done|apply (WH _ false); lia|apply (HK2 _ false); lia|apply ubs_none|tstep].
    - tstep.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pc 6 0). split; [done|]. apply sle_refl, HW. }
  cbn. eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force0 W _ _ _ _ _ _ 2 wk_C None wk_body [pt_dual (pc 3 0); pc 6 0]);
      [done|done|apply (WH _ false); lia|apply (HK2 _ false); lia|apply ubs_none|tstep].
  - tstep.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|done].
Qed.

Theorem sch_deadlock_free : deadlock_free (∅, {[+ sch_main +]}).
Proof. apply (soundness_created_s (sch_Ψ 6) _ TUnit (sch_created 6 ltac:(lia))); [constructor|apply sch_typed]. Qed.
