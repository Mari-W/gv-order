(** * Fuel holds values that no send and no spawn can hand on (stage S7, report)

    The fuel analogue of [send_gap] (stage S4, decision Q14). F-Send and
    F-Spawn hand on the ends M of the transfer set, the ends the payload
    or the thunk mentions (decision Q3). No clause of [Vfuel] relates the
    ends of a value to its map Π. So [Vfuel] holds a closure that
    mentions an end it does not hold, and no send and no spawn can hand
    it on.

    The closure [dead_thunk q] = λ_. let ∗ = Ω in close q mentions q,
    holds nothing, and is in [Vfuel] at every level and refill, because
    its body only takes β steps ([Vfuel_dead]).

    - [fuel_send_gap]. The pair ⟨dead_thunk q, d⟩ is in [Vfuel] at the
      payload type of d, and send ⟨dead_thunk q, d⟩ is not in [FuelE] at
      level 1. Its label moves {q}, and the sender holds only d. So the
      compatibility lemma of E-Send fails over groundings in [Vfuel].
    - [fw_counterexample]. The thread
        fw o = let ⟨w, c⟩ = recv o in let ∗ = close c in spawn w
      types by P-Term at every refill N, with a transformer met at
      reserve 0 ([fw_ptyped], [fw_typed], [fw_tix]), and is not in
      [fsem N]. F-Recv quantifies over every incoming value of [Vfuel],
      and after it receives [dead_thunk o] and closes o, its spawn moves
      {o}, which it no longer holds ([fw_not_fsem]). So the theorem
      `fsem_of_cost` (A.3, old name [ctyped_fsem]) is false for the
      definitions of stage S6. *)

From GV Require Export fuel.FuelSub static.Typing.

(** ** A term that only takes β steps *)

Definition div_ω : expr := Lam (App (Var 0) (Var 0)).
Definition div_Ω : expr := App div_ω div_ω.

Lemma tstep_div_Ω α e' : tstep div_Ω α e' → α = LBeta ∧ e' = div_Ω.
Proof.
  intros H. apply tstep_inv in H as [Hh|(f & e0 & e0' & Hf & Heq & -> & Hs)].
  - inversion Hh; subst. done.
  - destruct f; simpl in Heq; try discriminate; injection Heq as <- <-;
      exfalso; apply (val_no_tstep _ _ _ Hs); done.
Qed.

Lemma tstep_dead e α e' : tstep (LetU div_Ω e) α e' → α = LBeta ∧ e' = LetU div_Ω e.
Proof.
  intros H. destruct (tstep_fill_inv (FLetU e) div_Ω α e' I ltac:(simpl; tauto) H) as (e0 & Hs & ->).
  apply tstep_div_Ω in Hs as [-> ->]. done.
Qed.

(** let ∗ = Ω in e is in [FuelE] at every level, refill, result, frame,
    reserve, map and ticket count. *)
Lemma FuelE_dead n : ∀ N σ d r Π φ tk e, LetU div_Ω e ∈ F^N _ n⟦σ ▷ d ; r⟧(Π, φ, tk).
Proof.
  induction n as [|n IH]; intros N σ d r Π φ tk e; [apply FuelE_0|].
  apply FuelE_S. intros N' g Π' φ' _ _ _ _ _. cbn [emap]. split.
  - intros Hv. done.
  - intros α e' Hst. apply tstep_dead in Hst as [-> ->]. cbn [Fobl f_beta]. apply IH.
Qed.

Definition dead_thunk (q : cend) : expr := Lam (LetU div_Ω (EClose (Chan q))).

(** The thunk type ∗ ⊸ ∗ with frame 0, transformer 1̂ and floor 0. *)
Definition T_thk : ty := TLolli None None (Some 0) tid (Some 0) TUnit (Some 0) TUnit (Some 0).

Lemma Vfuel_dead N n a q : dead_thunk q ∈ FV^N _ n⟦RTy T_thk a⟧(∅, ∅).
Proof.
  apply Vfuel_eq. cbn [Vres Vty]. exists (LetU div_Ω (EClose (Chan q))). split_and!; [done|done| |].
  - intros o f H. by rewrite lookup_empty in H.
  - intros N' j φ' Πu φu u r tk _ _ _ _ _ _ _ _. apply FuelE_dead.
Qed.

Lemma fends_dead q : q ∈ fends (dead_thunk q).
Proof. simpl. set_solver. Qed.

Lemma fle_0 f : fle (Some 0) f.
Proof. destruct f; simpl; lia. Qed.

(** ** The send gap *)

Definition S_snd : sty := SSeq (SSnd 0 T_thk (Some 0)) SEnd.

Theorem fuel_send_gap N (q d : cend) (z : point) f σ dfr r tk :
  let v := Pair (dead_thunk q) (Chan d) in
  (∀ n, v ∈ FV^N _ n⟦RTy (TProd T_thk (Some 0) (TSess S_snd z) (Some 0)) (Some 0)⟧({[d := S_snd]}, {[d := f]})) ∧
  ¬ ESend v ∈ F^N _ 1⟦σ ▷ dfr ; r⟧({[d := S_snd]}, {[d := f]}, tk).
Proof.
  intros v. split.
  - intros n. rewrite <-(map_empty_union {[d := S_snd]}), <-(map_empty_union {[d := f]}).
    apply Vfuel_pair; [apply map_disjoint_empty_l|apply map_disjoint_empty_l|apply Vfuel_dead|].
    apply Vfuel_end. apply fle_0.
  - intros HF.
    assert (tstep (ESend v) (LSess (SSend d (fends (dead_thunk q)) (dead_thunk q))) (Chan d)) as Hst.
    { apply tstep_head. by apply t_act_send. }
    pose proof (fuel_obl N 0 _ _ tk _ HF _ _ Hst) as H. cbn [Fobl] in H. unfold f_send in H.
    destruct H as (_ & S0 & m & T & b & S & _ & _ & HM & _).
    pose proof (HM q (fends_dead q)) as Hq. rewrite dom_singleton_L in Hq. set_solver.
Qed.

(** ** The spawn forwarder *)

Definition S_fw : sty := SSeq (SRcv 0 T_thk (Some 2)) SEnd.

Lemma unfold_S_fw : unfoldS S_fw = SSeq (SRcv 0 T_thk (Some 2)) SEnd.
Proof. reflexivity. Qed.

(** let ⟨w, c⟩ = recv o in let ∗ = close c in spawn w *)
Definition fw (o : cend) : expr := LetP (ERecv (Chan o)) (LetU (EClose (Var 0)) (ESpawn (Var 1))).

(** After receiving [dead_thunk o] and closing o, the spawn moves {o},
    which the thread no longer holds. Five steps, so level 5. *)
Lemma fw_not_fuel N o φ tk : ¬ FuelT N 5 {[o := S_fw]} φ tk (fw o).
Proof.
  intros H5. set (w := dead_thunk o).
  set (e2 := LetU (EClose (Var 0)) (ESpawn (Var 1))).
  (* receive w on o *)
  assert (tstep (fw o) (LSess (SRecv o w)) (LetP (Pair w (Chan o)) e2)) as St1.
  { apply (t_act_ctx (FLetP e2)); [done|]. apply tstep_head. by apply t_act_recv. }
  pose proof (fuel_obl N 4 _ _ tk _ H5 _ _ St1) as H. cbn [Fobl] in H. unfold f_recv in H.
  destruct H as (_ & S0 & m & T & b & S & HΠ & Hun & Hk).
  rewrite lookup_singleton_eq in HΠ. injection HΠ as <-.
  rewrite unfold_S_fw in Hun. injection Hun as <- <- <- <-.
  specialize (Hk 4 ∅ ∅ ltac:(lia) (map_disjoint_empty_l _) (map_disjoint_empty_l _) (Vfuel_dead N 4 _ o)).
  cbn beta in Hk.
  (* β: let ⟨w, c⟩ = ⟨w, o⟩ *)
  assert (tstep (LetP (Pair w (Chan o)) e2) LBeta (LetU (EClose (Chan o)) (ESpawn w))) as St2.
  { apply tstep_head. change (LetU (EClose (Chan o)) (ESpawn w)) with (subst2 w (Chan o) e2).
    by apply t_act_let_pair. }
  pose proof (fuel_obl N 3 _ _ tk _ Hk _ _ St2) as H. cbn [Fobl f_beta] in H. clear Hk.
  (* close o *)
  assert (tstep (LetU (EClose (Chan o)) (ESpawn w)) (LSess (SClose o)) (LetU EUnit (ESpawn w))) as St3.
  { apply (t_act_ctx (FLetU (ESpawn w))); [done|]. apply tstep_head, t_act_close. }
  pose proof (fuel_obl N 2 _ _ tk _ H _ _ St3) as H'. cbn [Fobl] in H'. unfold f_close in H'.
  destruct H' as (_ & S1 & _ & _ & H'). clear H.
  (* β: let ∗ = ∗ *)
  assert (tstep (LetU EUnit (ESpawn w)) LBeta (ESpawn w)) as St4.
  { apply tstep_head, t_act_let_unit. }
  pose proof (fuel_obl N 1 _ _ tk _ H' _ _ St4) as H. cbn [Fobl f_beta] in H. clear H'.
  (* spawn w moves {o} *)
  assert (tstep (ESpawn w) (LSpawn (fends w) w) EUnit) as St5.
  { apply tstep_head. by apply t_act_spawn. }
  pose proof (fuel_obl N 0 _ _ tk _ H _ _ St5) as H'. cbn [Fobl] in H'. unfold f_spawn in H'.
  destruct H' as (HM & _).
  pose proof (HM o (fends_dead o)) as Ho. rewrite dom_fmap_L, dom_delete_L in Ho. set_solver.
Qed.

Lemma fw_not_fsem N o : ¬ fsem N {[o := S_fw]} (fw o).
Proof. intros [tk H]. exact (fw_not_fuel N o _ tk (H 5)). Qed.

(** ** The forwarder types, at every refill *)

Definition W_fw : world := World ∅ (λ _, False) ∅ (λ _ _, False).

Definition fw_cost : fuel := fadd (fadd (Some 0) (Some 1)) (fadd (fadd (Some 0) (Some 1)) (Some 0)).
Definition fw_tix : tix := tseq tid (tseq tid (tseq tid (tspawn (tapp tid 0) tid))).

Lemma fw_tix_met tk : meets fw_tix 0 tk.
Proof. unfold meets, fw_tix. simpl. lia. Qed.

Lemma tenv_heads_nil : tenv_heads ∅ = ∅.
Proof. apply set_eq. intros y. rewrite elem_of_tenv_heads. setoid_rewrite lookup_empty. set_solver. Qed.

Lemma tok_tid t : tok tid t.
Proof. right. left. done. Qed.

Lemma fw_typed N o x :
  typed W_fw N {[o := TE S_fw x N]} hc_empty [] (∅, None) (fw o) TUnit None fw_cost fw_tix.
Proof.
  unfold fw, fw_cost, fw_tix.
  eapply (e_letp W_fw N {[o := TE S_fw x N]} {[o := TE S_fw x N]} ∅ ∅ hc_empty [] [] [] [] (∅, None)
            _ _ T_thk (Some 2) _ N (Some 0)).
  - split; [apply map_disjoint_empty_r|by rewrite map_union_empty].
  - constructor.
  - eapply (e_recv W_fw N _ _ _ _ _ S_fw x 0 T_thk (Some 2) SEnd).
    + reflexivity.
    + simpl. split_and!; done.
    + simpl. rewrite tenv_heads_nil. split_and!; [set_solver|done|done].
    + apply e_chan. intros ? Hin. inversion Hin.
  - intros o'. by rewrite lookup_empty.
  - constructor.
  - eapply (e_letu W_fw N ∅ ∅ ∅ ∅ hc_empty _ _ _ _ (∅, None)).
    + split; [apply map_disjoint_empty_l|by rewrite map_union_empty].
    + apply lsplit_l, lsplit_r, lsplit_nil.
    + eapply (e_close W_fw N _ _ _ _ _ SEnd); [reflexivity| |].
      * simpl. rewrite tenv_heads_nil. split_and!; [intros y Hy; exfalso; set_solver|done|done].
      * apply e_var. split; [done|]. intros [|[|y]] σ' Hy; simpl in Hy; [by injection Hy as <-|done|].
        rewrite lookup_nil in Hy. done.
    + intros o'. by rewrite lookup_empty.
    + apply lage_none, lage_some; [|apply lage_nil]. apply age_credit. simpl. lia.
    + eapply e_spawn; [| |apply tok_tid].
      * apply e_var. split; [done|]. intros [|[|y]] σ' Hy; simpl in Hy; [done|by injection Hy as <-|].
        rewrite lookup_nil in Hy. done.
      * simpl. lia.
    + apply tok_tid.
  - apply tok_tid.
Qed.

Theorem fw_ptyped N o x : ptyped N W_fw {[o := (S_fw, x)]} (∅, {[+ fw o +]}) TUnit.
Proof.
  eapply (p_term N W_fw _ ∅ ∅ _ TUnit None fw_cost fw_tix).
  - constructor.
  - intros o'. rewrite dom_empty_L. set_solver.
  - set_solver.
  - set_solver.
  - rewrite map_union_empty. unfold tenv_of. rewrite map_fmap_singleton. apply fw_typed.
Qed.

(** P-Term types the forwarder at every refill N, and it is not in
    [fsem N]. *)
Theorem fw_counterexample N o x :
  ptyped N W_fw {[o := (S_fw, x)]} (∅, {[+ fw o +]}) TUnit ∧
  (∀ tk, meets fw_tix 0 tk) ∧
  ¬ fsem N {[o := S_fw]} (fw o).
Proof. split_and!; [apply fw_ptyped|apply fw_tix_met|apply fw_not_fsem]. Qed.
