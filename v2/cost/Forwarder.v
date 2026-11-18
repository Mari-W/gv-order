(** * The forwarder of S7.1, after decision Q15 (stage S7)

    Before Q15, [Vfuel] held the closure
      dead_thunk q = λ_. let ∗ = Ω in close q,
    which mentions q and holds nothing, and the thread
      fw o = let ⟨w, c⟩ = recv o in let ∗ = close c in spawn w
    was typed by P-Term at every refill and not in [fsem]
    (docs/redesign/progress.md, S7.1). Q15 asks a closure in [Vfuel] to
    hold exactly the ends it mentions. [dead_thunk_rejected] checks that
    the closure is gone, and [fw_typed] and [fw_ptyped] keep the typing
    of the forwarder, so that [fw_fsem] (cost/CostFund.v) gets its
    [fsem] from [fsem_of_cost]. *)

From GV Require Export fuel.FuelSub static.Typing.


(** ** The closure Q15 rejects *)

Definition div_ω : expr := Lam (App (Var 0) (Var 0)).
Definition div_Ω : expr := App div_ω div_ω.

Definition dead_thunk (q : cend) : expr := Lam (LetU div_Ω (EClose (Chan q))).

(** The thunk type ∗ ⊸ ∗ with frame 0, transformer 1̂ and floor 0. *)
Definition T_thk : ty := TLolli None None (Some 0) tid (Some 0) TUnit (Some 0) TUnit (Some 0).

Lemma fends_dead q : q ∈ fends (dead_thunk q).
Proof. simpl. set_solver. Qed.

(** A closure in [Vfuel] at ∅ mentions no end, so [dead_thunk q] is in
    [Vfuel] at no map that misses q. *)
Lemma dead_thunk_rejected N n a q Π φ :
  q ∉ dom Π → ¬ dead_thunk q ∈ FV^N _ n⟦RTy T_thk a⟧(Π, φ).
Proof. intros Hq H. apply Vfuel_exact in H. apply Hq. rewrite <-H. apply fends_dead. Qed.


(** ** The spawn forwarder *)

Definition S_fw : sty := SSeq (SRcv 0 T_thk (Some 2)) SEnd.

Lemma unfold_S_fw : unfoldS S_fw = SSeq (SRcv 0 T_thk (Some 2)) SEnd.
Proof. reflexivity. Qed.

(** let ⟨w, c⟩ = recv o in let ∗ = close c in spawn w *)
Definition fw (o : cend) : expr := LetP (ERecv (Chan o)) (LetU (EClose (Var 0)) (ESpawn (Var 1))).

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
  - apply pfree_singleton.
  - set_solver.
  - rewrite map_union_empty. unfold tenv_of. rewrite map_fmap_singleton. apply fw_typed.
Qed.
