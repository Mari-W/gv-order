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
    state already. Both semantics are synchronous (their Fig. 15). *)

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
    [by left|first [left; exists 0; cbn; inlist|right; eexists; first [by left|by right; left|by right; right]]
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
Definition sch_P (a : nat) (g : fact) : Prop :=
  (∃ b k j, b < a ∧ rk b k < rk a j ∧ g = FLt (pv (a - b) k) (pv 0 j)) ∨
  (∃ b k j, b < a ∧ rk a j < rk b k ∧ g = FLt (pv 0 j) (pv (a - b) k)) ∨
  (∃ j, g = FLt (pv 0 j) (pv (S a) 0)).
Definition sch_C (a : nat) : bcs := BCs (ids (S a)) (sch_P a).

(** The hypotheses after the channels b < a: b is the variable a-1-b
    and z is a. *)
Fixpoint sch_Ψ (a : nat) : hyps :=
  match a with
  | 0 => [(top_C0, ids 1)]
  | S a' => hyps_inst (pshift 1) (sch_Ψ a') ++ [(bcs_inst (pshift 1) (sch_C a'), ids 1)]
  end.

Definition sch_inv (W : world) (a : nat) : Prop :=
  (∀ b b' k l, b < a → b' < a → rk b k < rk b' l → slt W (sch_Ψ a) (pv (a - 1 - b) k) (pv (a - 1 - b') l)) ∧
  (∀ b k, b < a → slt W (sch_Ψ a) (pv (a - 1 - b) k) (pv a 0)).

Definition sch_kn (a : nat) : Prop := ∀ v, v ≤ a → ∃ C, (C, [pvar v]) ∈ sch_Ψ a.

Lemma length_ids n : length (ids n) = n.
Proof. unfold ids. by rewrite length_fmap, length_seq. Qed.

Lemma ids_shift n : pvar 0 :: (pt_inst (pshift 1) <$> ids n) = ids (S n).
Proof.
  unfold ids. simpl. f_equal. rewrite <-list_fmap_compose. apply list_eq. intros i.
  rewrite !list_lookup_fmap. destruct (decide (i < n)).
  - rewrite !lookup_seq_lt by lia. cbn. rewrite pt_inst_pvar_at. unfold pshift. by rewrite Nat.add_1_r.
  - rewrite !lookup_seq_ge by lia. done.
Qed.

Lemma open_ids n x : pn_vb (S n) (pt_name x) → pt_inst (pup 1 (plist (ids n))) x = x.
Proof.
  intros Hx. rewrite <-(pt_inst_pvar x) at 2. apply pt_inst_ext_root. intros a Ha.
  pose proof (pn_vb_root _ _ _ Hx Ha) as Hlt. unfold pup. case_decide as Ha1; [done|].
  unfold plist, ids. rewrite list_lookup_fmap, lookup_seq_lt by lia. cbn.
  rewrite pt_inst_pvar_at. unfold pvar. do 2 f_equal. lia.
Qed.

Lemma slt_ofs W Ψ c k l : world_wf W → k < l → slt W Ψ (pv c k) (pv c l).
Proof.
  intros HW H. induction H as [|l _ IH].
  - pose proof (slt_po W Ψ (pv c k) HW) as G. unfold pt_shift in G. simpl in G. by rewrite Nat.add_1_r in G.
  - eapply sl_trans; [exact IH|]. pose proof (slt_po W Ψ (pv c l) HW) as G.
    unfold pt_shift in G. simpl in G. by rewrite Nat.add_1_r in G.
Qed.

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

Lemma sch_ok W a : sch_inv W a → cc_ok (seqs W (sch_Ψ a)) (slt W (sch_Ψ a)) (sch_C a).
Proof.
  intros [HR Hz].
  apply (cc_ok_out _ _ (sch_C a) olt); [exact olt_trans|exact olt_irrefl|intros x _; apply olt_po| | |].
  - intros x y (f & Hf & _ & E).
    destruct Hf as [(b & k & j & _ & _ & ->)|[(b & k & j & _ & _ & ->)|(j & ->)]]; discriminate E.
  - intros x y (f & Hf & _ & E). cbn [bc_facts bc_env] in *.
    destruct Hf as [(b & k & j & Hb & _ & ->)|[(b & k & j & Hb & _ & ->)|(j & ->)]];
      unfold sch_C in E; cbn [fact_map bc_env] in E; rewrite !open_ids in E by (cbn; lia); injection E as -> ->; cbn.
    + right; left. split; [intros [=]; lia|done].
    + right; right. split; [done|intros [=]; lia].
    + right; right. split; [done|intros [=]].
  - intros u p q v (f & Hf & _ & E) (f' & Hf' & _ & E') Hu Hp Hq Hv Hpq. cbn [bc_facts bc_env] in *.
    destruct Hf as [(b & k & j & Hb & Hr & ->)|[(b & k & j & Hb & Hr & ->)|(j & ->)]];
      unfold sch_C in E; cbn [fact_map bc_env] in E; rewrite !open_ids in E by (cbn; lia); injection E as -> ->;
      cbn in Hu; try done.
    destruct Hf' as [(b' & k' & j' & Hb' & Hr' & ->)|[(b' & l & j' & Hb' & Hr' & ->)|(j' & ->)]];
      unfold sch_C in E'; cbn [fact_map bc_env] in E'; rewrite !open_ids in E' by (cbn; lia); injection E' as -> ->;
      cbn in Hq, Hv; try done.
    + assert (j ≤ j') as Hj by (destruct Hpq as [[= ->]|[_ Hpq]]; cbn in *; lia).
      assert (rk a j ≤ rk a j') by (destruct (decide (j = j')) as [->|]; [lia|]; pose proof (rk_mono a j j'); lia).
      pose proof (glt_up (seqs W (sch_Ψ a)) _ _ _ (HR b b' k l Hb Hb' ltac:(lia))) as G.
      rewrite !pv_lift in G. by replace (S (a - 1 - b)) with (a - b) in G by lia;
        replace (S (a - 1 - b')) with (a - b') in G by lia.
    + pose proof (glt_up (seqs W (sch_Ψ a)) _ _ _ (Hz b k Hb)) as G.
      rewrite !pv_lift in G. by replace (S (a - 1 - b)) with (a - b) in G by lia.
Qed.

Lemma sch_inv_step W a : strict W → sch_inv W a → sch_inv W (S a).
Proof.
  intros HW [HR Hz].
  set (env := pt_inst (pshift 1) <$> ids (S a)).
  assert ((BCs env (sch_P a), [pvar 0]) ∈ sch_Ψ (S a)) as Hm.
  { cbn [sch_Ψ]. apply elem_of_app. right. by left. }
  assert (∀ x y, sch_P a (FLt x y) → fact_scoped (S (S a)) (FLt x y) → slt W (sch_Ψ (S a)) x y) as Hn.
  { intros x y Hf Hs. eapply (sl_hyp W _ env (sch_P a) [pvar 0] (FLt x y)); [exact Hm|exact Hf| |].
    - unfold env. cbn [length]. by rewrite length_fmap, length_ids.
    - cbn [fact_map app]. unfold env. rewrite ids_shift. destruct Hs as [Hx Hy].
      by rewrite !pt_inst_ids. }
  split.
  - intros b b' k l Hb Hb' Hr.
    destruct (decide (b = a)) as [->|Hba]; destruct (decide (b' = a)) as [->|Hba'].
    + replace (S a - 1 - a) with 0 by lia. apply slt_ofs; [exact (proj1 HW)|]. by eapply rk_lt_inv.
    + replace (S a - 1 - a) with 0 by lia. replace (S a - 1 - b') with (a - b') by lia.
      apply Hn; [right; left; exists b', l, k; split_and!; [lia|done|done]|cbn; lia].
    + replace (S a - 1 - a) with 0 by lia. replace (S a - 1 - b) with (a - b) by lia.
      apply Hn; [left; exists b, k, l; split_and!; [lia|done|done]|cbn; lia].
    + pose proof (slt_shift W (sch_Ψ a) [(bcs_inst (pshift 1) (sch_C a), ids 1)] _ _ HW
                    (HR b b' k l ltac:(lia) ltac:(lia) Hr)) as G.
      rewrite !pv_shift in G. by replace (S a - 1 - b) with (S (a - 1 - b)) by lia;
        replace (S a - 1 - b') with (S (a - 1 - b')) by lia.
  - intros b k Hb. destruct (decide (b = a)) as [->|Hba].
    + replace (S a - 1 - a) with 0 by lia. apply Hn; [right; right; by exists k|cbn; lia].
    + pose proof (slt_shift W (sch_Ψ a) [(bcs_inst (pshift 1) (sch_C a), ids 1)] _ _ HW
                    (Hz b k ltac:(lia))) as G.
      rewrite !pv_shift in G. by replace (S a - 1 - b) with (S (a - 1 - b)) by lia.
Qed.

Lemma sch_inv_0 W : sch_inv W 0.
Proof. split; intros; lia. Qed.

Lemma sch_kn_step a : sch_kn a → sch_kn (S a).
Proof.
  intros H [|v] Hv.
  - eexists. cbn [sch_Ψ]. apply elem_of_app. right. by left.
  - destruct (H v ltac:(lia)) as (C & HC). exists (bcs_inst (pshift 1) C). cbn [sch_Ψ].
    apply elem_of_app. left. unfold hyps_inst. apply list_elem_of_fmap. exists (C, [pvar v]).
    split; [|done]. cbn. unfold pt_inst, pshift. cbn. by rewrite Nat.add_1_r.
Qed.

Lemma sch_kn_0 : sch_kn 0.
Proof. intros v Hv. assert (v = 0) as -> by lia. exists top_C0. by left. Qed.

Lemma sch_skn W a x : sch_kn a → pt_root x = NVar 0 ∨ (∃ v, v ≤ a ∧ pt_root x = NVar v) →
  skn W (sch_Ψ a) x.
Proof.
  intros H [Hx|(v & Hv & Hx)].
  - destruct (H 0 ltac:(lia)) as (C & HC). eapply skn_inst; [exact HC|by left|done].
  - destruct (H v Hv) as (C & HC). eapply skn_inst; [exact HC|by left|done].
Qed.

Lemma sch_env W a : sch_kn a → Forall (skn W (sch_Ψ a)) (bc_env (sch_C a)).
Proof.
  intros H. apply Forall_forall. intros x Hx. unfold sch_C in Hx. cbn [bc_env] in Hx. unfold ids in Hx.
  apply list_elem_of_fmap in Hx as (v & -> & Hv). apply elem_of_seq in Hv.
  apply (sch_skn W a); [done|right; exists v; split; [lia|done]].
Qed.

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

Definition i2 : list point := [pv 2 0; pv 4 0; pv 1 0; pv 6 0].
Definition i3 : list point := [pv 1 0; pv 3 0; pv 0 0; pv 6 0].
Definition iL : list point := [pv 0 0; pv 5 2; pv 2 2; pv 6 0].

Definition lead_facts : list fact :=
  [FLt (pv 5 0) (pv 0 0); FLt (pv 5 0) (pv 2 0); FLt (pv 2 0) (pv 0 0); FLt (pv 2 0) (pv 5 1);
   FLt (pv 5 1) (pv 0 0); FLt (pv 5 1) (pv 2 1); FLt (pv 2 1) (pv 0 0); FLt (pv 2 1) (pv 5 2)].

Definition leader : expr :=
  LetP (Pair (App ESend (Pair EUnit (Var 12))) EUnit) (LetU (Var 0)
  (LetP (Pair (App ESend (Pair EUnit (Var 8))) EUnit) (LetU (Var 0)
  (LetP (App ERecv (Var 3)) (LetU (Var 1)
  (App (App EForce (Var 20)) (Pair (Var 7) (Pair (Var 0) (App ESend (Pair EUnit (Var 3))))))))))).

Definition sch_main : expr :=
  LetP (Pair follower worker)
  (let_new_pair (let_new_pair (let_new_pair
  (let_new_pair (let_new_pair (let_new_pair
  (LetU (App ESpawn (Lam (LetU (Var 0) leader)))
  (LetU (App ESpawn (Lam (LetU (Var 0) (App (App EForce (Var 14)) (Pair (Var 5) (Pair (Var 10) (Var 4)))))))
  (LetU (App ESpawn (Lam (LetU (Var 0) (App (App EForce (Var 14)) (Pair (Var 3) (Pair (Var 8) (Var 2)))))))
  (LetU (App ESpawn (Lam (LetU (Var 0) (App (App EForce (Var 13)) (Var 11)))))
  (LetU (App ESpawn (Lam (LetU (Var 0) (App (App EForce (Var 13)) (Var 9)))))
    (App (App EForce (Var 12)) (Var 6))))))))))))).

Section ring.
  Context (W : world) (HW : world_wf W) (Ψ : hyps).
  Context (HR : ∀ b b' k l, b < 6 → b' < 6 → rk b k < rk b' l → slt W Ψ (pv (5 - b) k) (pv (5 - b') l)).
  Context (Hz : ∀ b k, b < 6 → slt W Ψ (pv (5 - b) k) (pv 6 0)).

  (** A fact between two channel points whose ranks rise. *)
  Ltac hr := match goal with |- slt _ _ (Pt (NVar ?v) ?k) (Pt (NVar ?w) ?l) =>
    apply (HR (5 - v) (5 - w) k l); [cbn; lia|cbn; lia|] end.

  Lemma fl_hold xs : xs ∈ [i2; i3; iL] → bcs_hold (seqs W Ψ) (slt W Ψ) fl_C xs.
  Proof.
    intros Hxs. apply bcs_hold_intro. intros g [(r & Hm)|(k & Hg)] _.
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
        (repeat (apply elem_of_cons in Hm as [->|Hm];
           [cbn [fact_map fact_holds]; unfold i2, i3, iL, pt_inst, pt_shift; cbn; hr;
            rewrite ?rk_SS, ?Hr0, ?Hr1; cbn; lia|]));
        by apply elem_of_nil in Hm.
    - repeat apply elem_of_cons in Hxs as [->|Hxs]; try (by apply elem_of_nil in Hxs);
        destruct Hg as [-> | [-> | ->]]; cbn [fact_map fact_holds]; unfold i2, i3, iL, pt_inst, pt_shift; cbn;
        match goal with |- slt _ _ (Pt (NVar ?v) ?k) _ => apply (Hz (5 - v) k); cbn; lia end.
  Qed.

  Lemma lead_lt x y : FLt x y ∈ lead_facts → slt W Ψ x y.
  Proof.
    intros H. repeat (apply elem_of_cons in H as [H|H]; [injection H as -> ->; hr; vm_compute; lia|]).
    by apply elem_of_nil in H.
  Qed.

  Lemma ceil_lt v k : v < 6 → slt W Ψ (pv v k) (pv 6 0).
  Proof. intros H. replace v with (5 - (5 - v)) by lia. apply Hz. lia. Qed.

  Lemma round0_lt xs x y : xs ∈ [i2; i3; iL] → FLt x y ∈ fround 0 →
    slt W Ψ (pt_inst (plist xs) x) (pt_inst (plist xs) y).
  Proof.
    intros Hxs H. pose proof (fl_hold xs Hxs (FLt x y)) as G. apply G.
    apply bcs_open_nil. split; [left; by exists 0|].
    assert (length xs = 4) as ->
      by (repeat apply elem_of_cons in Hxs as [->|Hxs]; try (by apply elem_of_nil in Hxs); done).
    unfold fround in H. repeat (apply elem_of_cons in H as [H|H]; [injection H as -> ->; cbn; lia|]).
    by apply elem_of_nil in H.
  Qed.

  Lemma wk_hold v : v < 6 → bcs_hold (seqs W Ψ) (slt W Ψ) wk_C [pv v 0; pv 6 0].
  Proof. intros Hv. apply bcs_hold_intro. intros g (k & ->) _. cbn. by apply ceil_lt. Qed.
End ring.

(** One [new] of the ring: channel a with the session type St. *)
Ltac sch_new W HWs a St Ia Ka I K :=
  apply (t_new_open W _ _ ∅ _ _ _ _ St (sch_C a)); [apply sch_ok, Ia|apply sch_env, Ka|];
  rewrite ?tenv_pinst_empty, ?sf_pinst_none, ?fhyps_pinst_empty;
  change (hyps_inst (pshift 1) (sch_Ψ a) ++ [(bcs_inst (pshift 1) (sch_C a), ids 1)]) with (sch_Ψ (S a));
  pose proof (sch_inv_step W a HWs Ia) as I; pose proof (sch_kn_step a Ka) as K;
  cbn -[sch_Ψ sch_C wk_ty fl_ty];
  rewrite ?(pinst_closed _ wk_ty wk_ty_pscoped), ?(pinst_closed _ fl_ty fl_ty_pscoped).

Lemma sch_typed : styped ∅ [(top_C0, ids 1)] [] (∅, None) sch_main TUnit.
Proof.
  apply styped_Wpo. pose proof Wpo_nil_strict' as HWs.
  pose proof (proj1 HWs) as HW. set (W := Wpo []) in *. unfold sch_main.
  change [(top_C0, ids 1)] with (sch_Ψ 0).
  tstep.
  { tstep; apply typed_hyps_wk; [exact HWs|apply worker_typed, HW|exact HWs|apply follower_typed, HW]. }
  pose proof (sch_inv_0 W) as I0. pose proof sch_kn_0 as K0.
  cbn -[sch_Ψ sch_C wk_ty fl_ty].
  sch_new W HWs 0 Wk I0 K0 I1 K1. sch_new W HWs 1 Wk I1 K1 I2 K2. sch_new W HWs 2 Wk I2 K2 I3 K3.
  sch_new W HWs 3 Sc I3 K3 I4 K4. sch_new W HWs 4 Sc I4 K4 I5 K5. sch_new W HWs 5 Sc I5 K5 I6 K6.
  destruct I6 as [HR Hz].
  pose proof (fl_hold W HW _ HR Hz) as FH. pose proof (lead_lt W HW _ HR Hz) as LL.
  pose proof (ceil_lt W HW _ HR Hz) as CL. pose proof (round0_lt W HW _ HR Hz) as R0.
  pose proof (wk_hold W HW _ HR Hz) as WH.
  assert (∀ v k, v ≤ 6 → skn W (sch_Ψ 6) (pv v k)) as HKv.
  { intros v k Hv. apply (sch_skn W 6); [exact K6|right; exists v; split; [lia|done]]. }
  assert (∀ v, v < 6 → Forall (skn W (sch_Ψ 6)) [pv v 0; pv 6 0]) as HK2.
  { intros v Hv. constructor; [apply HKv; lia|constructor; [apply HKv; lia|constructor]]. }
  assert (∀ xs, xs ∈ [i2; i3; iL] → Forall (skn W (sch_Ψ 6)) xs) as HK4.
  { intros xs Hxs. repeat apply elem_of_cons in Hxs as [->|Hxs]; try (by apply elem_of_nil in Hxs);
      unfold i2, i3, iL; repeat (constructor; [apply HKv; lia|]); constructor. }
  (* the leader *)
  tstep.
  { tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pv 6 0)) (Some (pv 5 0)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy; first [apply sle_refl, HW|right; apply LL; inlist]. }
    cbn. tstep; [tstep|]. unfold leader. cbn.
    tstep.
    { tstep; [tstep|].
      eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pv 5 0))
                (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) (SSeq (SRcv 0 TUnit) Wk)) (pv 5 0)))).
      - tstep; [|tstep]. eapply t_conv; [|tstep]. conv_sess.
      - apply (KTSend _ _ _ 0 TUnit (SSeq (SRcv 0 TUnit) Wk) (pv 5 0)). cbn. set_solver.
      - kscope.
      - apply ubs_intro; [intros y Hy; mem_cases Hy; apply LL; inlist|].
        exists (pv 6 0). split; [done|]. right. apply CL. lia. }
    cbn. tstep; [tstep|]. cbn. tstep.
    { tstep; [tstep|].
      eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pv 2 0))
                (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) (SSeq (SSnd 0 TUnit) Sc)) (pv 2 0)))).
      - tstep; [|tstep]. eapply t_conv; [|tstep]. conv_sess.
      - apply (KTSend _ _ _ 0 TUnit (SSeq (SSnd 0 TUnit) Sc) (pv 2 0)). cbn. set_solver.
      - kscope.
      - apply ubs_intro; [intros y Hy; mem_cases Hy; apply LL; inlist|].
        exists (pv 6 0). split; [done|]. right. apply CL. lia. }
    cbn. tstep; [tstep|]. cbn. tstep.
    { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (pv 5 1)) (TSess (SSeq (SRcv 0 TUnit) Wk) (pv 5 1)));
        [tstep|apply KTRecv|kscope|].
      apply ubs_intro; [intros y Hy; mem_cases Hy; apply LL; inlist|].
      exists (pv 6 0). split; [done|]. right. apply CL. lia. }
    cbn. tstep; [tstep|]. cbn.
    eapply tv_app; [exact HW|reflexivity| | |].
    - apply (typed_force0 W _ _ _ _ _ _ 4 fl_C None fl_body iL); [done|done| | |apply ubs_none|tstep].
      + apply FH. inlist.
      + apply HK4. inlist.
    - eapply (tv_pair W HW _ _ _ _ _ _ (TSess (dual Sc) (pv 0 0))); [reflexivity| |tstep].
      eapply (tv_pair W HW _ _ _ _ _ _ (TSess Wk (pv 5 2))); [reflexivity| |tstep].
      eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pv 2 1)) (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) Sc) (pv 2 1)))).
      + tstep; tstep.
      + apply (KTSend _ _ _ 0 TUnit Sc (pv 2 1)). cbn. set_solver.
      + kscope.
      + apply ubs_intro; [intros y Hy; mem_cases Hy; apply LL; inlist|].
        exists (pv 6 0). split; [done|]. right. apply CL. lia.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 6 0). split; [done|]. apply sle_refl, HW. }
  cbn. tstep.
  { tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pv 6 0)) (Some (pv 2 0)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy; first [apply sle_refl, HW
        |right; apply (R0 i2 (pv 0 0) (pv 1 0)); inlist
        |right; apply (R0 i2 (pv 0 0) (pv 2 0)); inlist]. }
    cbn. tstep; [tstep|]. cbn.
    eapply tv_app; [exact HW|reflexivity| | |].
    - apply (typed_force0 W _ _ _ _ _ _ 4 fl_C None fl_body i2);
        [done|done|apply FH; inlist|apply HK4; inlist|apply ubs_none|tstep].
    - tstep; [tstep; tstep|tstep].
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 6 0). split; [done|]. apply sle_refl, HW. }
  cbn. tstep.
  { tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pv 6 0)) (Some (pv 1 0)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy; first [apply sle_refl, HW
        |right; apply (R0 i3 (pv 0 0) (pv 1 0)); inlist
        |right; apply (R0 i3 (pv 0 0) (pv 2 0)); inlist]. }
    cbn. tstep; [tstep|]. cbn.
    eapply tv_app; [exact HW|reflexivity| | |].
    - apply (typed_force0 W _ _ _ _ _ _ 4 fl_C None fl_body i3);
        [done|done|apply FH; inlist|apply HK4; inlist|apply ubs_none|tstep].
    - tstep; [tstep; tstep|tstep].
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 6 0). split; [done|]. apply sle_refl, HW. }
  cbn. tstep.
  { tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pv 6 0)) (Some (pv 5 0)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep; [tstep|]. cbn.
    eapply tv_app; [exact HW|reflexivity| | |].
    - apply (typed_force0 W _ _ _ _ _ _ 2 wk_C None wk_body [pv 5 0; pv 6 0]);
        [done|done|apply WH; lia|apply HK2; lia|apply ubs_none|tstep].
    - tstep.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 6 0). split; [done|]. apply sle_refl, HW. }
  cbn. tstep.
  { tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pv 6 0)) (Some (pv 4 0)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep; [tstep|]. cbn.
    eapply tv_app; [exact HW|reflexivity| | |].
    - apply (typed_force0 W _ _ _ _ _ _ 2 wk_C None wk_body [pv 4 0; pv 6 0]);
        [done|done|apply WH; lia|apply HK2; lia|apply ubs_none|tstep].
    - tstep.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 6 0). split; [done|]. apply sle_refl, HW. }
  cbn. eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force0 W _ _ _ _ _ _ 2 wk_C None wk_body [pv 3 0; pv 6 0]);
      [done|done|apply WH; lia|apply HK2; lia|apply ubs_none|tstep].
  - tstep.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|done].
Qed.

Theorem sch_deadlock_free : deadlock_free (∅, {[+ sch_main +]}).
Proof. apply (soundness_source 1 top_C0 _ TUnit (c0_acyclic_creation _ _ top_acyclic)); [constructor|apply sch_typed]. Qed.
