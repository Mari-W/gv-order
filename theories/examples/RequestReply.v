(** * request/reply: typable, recursive (SHARP-EDGES 65)

    C states every round at once:

      C = {ι+k ≺ ι′+k,  ι′+k ≺ ι+k+1  ∣  k ∈ ℕ}
      srv : □(∀ι ι′. C. ∗ ⊸^⊥_⊤ (Sa@ι ⊗ Sb@ι′ ⊸^{ι′}_⊤ ∗))
      srv = !(f = λp. let (a, b) = p in let (x, a) = recv a in let () = x in
                     spawn (λv. let () = v in (force f) ⟨a, send ⟨∗, b⟩⟩))
      cli : the same box over the dual sessions
      cli = !(f = λp. let (a, b) = p in let (a, u) = ⟨send ⟨∗, a⟩, ∗⟩ in let () = u in
                     let (x, b) = recv b in let () = x in
                     spawn (λv. let () = v in (force f) ⟨a, b⟩))
      main = let (s, c) = ⟨srv, cli⟩ in let (a, a′) = new ∗ in let (b, b′) = new ∗ in
             let () = spawn (λu. let () = u in (force s) ⟨a, b⟩) in (force c) ⟨a′, b′⟩

    The recursive force at (ι+1, ι′+1) asks C there, and C[ι+1, ι′+1] ⊆ C,
    so the body's own hypothesis gives it ([bcs_hold_self]). The send in
    the server's thunk blocks at ι′ while the pair holds a at ι+1, the
    fact ι′ ≺ ι+1 of C. main forces both boxes at ((a,0), (b,0)), where
    C is (a,k) ≺ (b,k) and (b,k) ≺ (a,k+1) for every k, the facts of
    [Wrr]. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.ExampleTools.

Set Default Proof Using "All".

Definition rq_P (g : fact) : Prop := ∃ k, g = FLt (pv 0 k) (pv 1 k) ∨ g = FLt (pv 1 k) (pv 0 (S k)).
Definition rq_C : bcs := BCs [] rq_P.

Definition srv_body : ty :=
  TLolli (Some (pv 1 0)) None (TProd (TSess Sa (pv 0 0)) (TSess Sb (pv 1 0))) TUnit.
Definition cli_body : ty :=
  TLolli (Some (pv 1 0)) None (TProd (TSess (dual Sa) (pv 0 0)) (TSess (dual Sb) (pv 1 0))) TUnit.

Definition srv : expr :=
  EBox (Lam (LetP (Var 0) (LetP (App ERecv (Var 1)) (LetU (Var 1)
    (App ESpawn (Lam (LetU (Var 0)
      (App (App EForce (Var 6)) (Pair (Var 1) (App ESend (Pair EUnit (Var 3)))))))))))).

Definition cli : expr :=
  EBox (Lam (LetP (Var 0) (LetP (Pair (App ESend (Pair EUnit (Var 1))) EUnit) (LetU (Var 0)
    (LetP (App ERecv (Var 2)) (LetU (Var 1)
      (App ESpawn (Lam (LetU (Var 0) (App (App EForce (Var 8)) (Pair (Var 4) (Var 1)))))))))))).

Definition rr_main : expr :=
  LetP (Pair srv cli) (LetP (App ENew EUnit) (LetP (App ENew EUnit)
    (LetU (App ESpawn (Lam (LetU (Var 0) (App (App EForce (Var 6)) (Pair (Var 4) (Var 2))))))
      (App (App EForce (Var 4)) (Pair (Var 2) (Var 0)))))).




(** C[ι+1, ι′+1] ⊆ C. *)
Lemma rq_step g : rq_P g → fact_scoped 2 g → rq_P (fact_map (pt_inst (plist [pv 0 1; pv 1 1])) g).
Proof. intros (k & [-> | ->]) _; exists (S k); [by left|by right]. Qed.

Lemma rq_call W Ψ :
  (rq_C, ids 2) ∈ Ψ → bcs_hold (seqs W Ψ) (slt W Ψ) rq_C [pv 0 1; pv 1 1].
Proof. intros Hg. apply bcs_hold_self; [done|vb_list|exact rq_step]. Qed.

Lemma srv_typed W F : world_wf W → typed W ∅ [] ∅ [] F srv (TBox 2 rq_C (TLolli None None TUnit srv_body)).
Proof.
  intros HW. unfold srv.
  apply (t_box W _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|].
  box_open rq_C srv_body. cbn. unfold srv_body.
  eapply (tv_lam W HW _ _ _ _ _ _ _ _ None 1); [set_solver|cbn; set_solver|].
  cbn. tstep; [tstep|]. cbn. tstep.
  { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (pv 0 0)) (TSess (SRcv 0 TUnit Sa) (pv 0 0))).
    - eapply t_conv; [|tstep]. conv_sess.
    - apply KTRecv.
    - kscope.
    - apply ubs_intro; [intros y Hy; mem_cases Hy; hyp0 (pv 0 0) (pv 1 0)|].
      exists (pv 1 0). split; [done|]. right. hyp0 (pv 0 0) (pv 1 0). }
  cbn. tstep; [tstep|]. cbn. tstep; [|apply KTSpawn|done|apply ubs_none].
  eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pv 1 1)) (Some (pv 1 0)) 2); [set_solver| |].
  { intros y Hy. mem_cases Hy; first [apply sle_refl, HW|right; hyp0 (pv 1 0) (pv 0 1)]. }
  cbn. tstep; [tstep|]. cbn.
  eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force W _ _ _ _ _ _ 2 rq_C None srv_body [pv 0 1; pv 1 1]);
      [done|done| | |apply ubs_none|tstep].
    + apply rq_call. by left.
    + apply (skn_ids2 W _ rq_C); [by left|done|done].
  - tstep.
    + eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pv 1 0)) (TProd TUnit (TSess (SSnd 0 TUnit Sb) (pv 1 0)))).
      * tstep; [|tstep]. eapply t_conv; [|tstep]. conv_sess.
      * apply (KTSend _ _ _ 0 TUnit Sb (pv 1 0)). cbn. set_solver.
      * kscope.
      * apply ubs_intro; [intros y Hy; mem_cases Hy; hyp0 (pv 1 0) (pv 0 1)|].
        exists (pv 1 1). split; [done|]. right. apply (slt_po W _ (pv 1 0) HW).
    + tstep.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (pv 1 1). split; [done|]. apply sle_refl, HW.
Qed.

Lemma cli_typed W F : world_wf W → typed W ∅ [] ∅ [] F cli (TBox 2 rq_C (TLolli None None TUnit cli_body)).
Proof.
  intros HW. unfold cli.
  apply (t_box W _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|].
  box_open rq_C cli_body. cbn. unfold cli_body.
  eapply (tv_lam W HW _ _ _ _ _ _ _ _ None 1); [set_solver|cbn; set_solver|].
  cbn. tstep; [tstep|]. cbn. tstep.
  { tstep; [tstep|].
    eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pv 0 0))
              (TProd TUnit (TSess (SSnd 0 TUnit (dual Sa)) (pv 0 0)))).
    - tstep; [|tstep]. eapply t_conv; [|tstep]. conv_sess.
    - apply (KTSend _ _ _ 0 TUnit (dual Sa) (pv 0 0)). cbn. set_solver.
    - kscope.
    - apply ubs_intro; [intros y Hy; mem_cases Hy; hyp0 (pv 0 0) (pv 1 0)|].
      exists (pv 1 0). split; [done|]. right. hyp0 (pv 0 0) (pv 1 0). }
  cbn. tstep; [tstep|]. cbn. tstep.
  { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (pv 1 0)) (TSess (SRcv 0 TUnit (dual Sb)) (pv 1 0))).
    - eapply t_conv; [|tstep]. conv_sess.
    - apply KTRecv.
    - kscope.
    - apply ubs_intro; [intros y Hy; mem_cases Hy; hyp0 (pv 1 0) (pv 0 1)|].
      exists (pv 1 0). split; [done|]. apply sle_refl, HW. }
  cbn. tstep; [tstep|]. cbn. tstep; [|apply KTSpawn|done|apply ubs_none].
  eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pv 1 1)) (Some (pv 1 0)) 2); [set_solver| |].
  { intros y Hy. mem_cases Hy;
      first [right; hyp0 (pv 1 0) (pv 0 1)|right; apply (slt_po W _ (pv 1 0) HW)]. }
  cbn. tstep; [tstep|]. cbn.
  eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force W _ _ _ _ _ _ 2 rq_C None cli_body [pv 0 1; pv 1 1]);
      [done|done| | |apply ubs_none|tstep].
    + apply rq_call. by left.
    + apply (skn_ids2 W _ rq_C); [by left|done|done].
  - tstep; tstep.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (pv 1 1). split; [done|]. apply sle_refl, HW.
Qed.

(** C at ((a,0), (b,0)) is the facts of [Wrr]. *)
Lemma rq_hold_W W :
  (∀ k, w_lt W (pc 0 k) (pc 1 k)) → (∀ k, w_lt W (pc 1 k) (pc 0 (S k))) →
  bcs_hold (w_eq W) (w_lt W) rq_C [pc 0 0; pc 1 0].
Proof. intros H1 H2. apply bcs_hold_intro. intros g (k & [-> | ->]) _; [apply H1|apply H2]. Qed.

Lemma rr_typed W : world_wf W → pt_known W (pc 0 0) → pt_known W (pc 1 0) →
  (∀ k, w_lt W (pc 0 k) (pc 1 k)) → (∀ k, w_lt W (pc 1 k) (pc 0 (S k))) →
  typed W ∅ [] ∅ [] (∅, None) rr_main TUnit.
Proof.
  intros HW Ha Hb H1 H2. unfold rr_main.
  assert (bcs_hold (seqs W []) (slt W []) rq_C [pc 0 0; pc 1 0]) as HC.
  { eapply bcs_hold_mono; [intros ? ? ?; by apply se_w|intros ? ? ?; by apply sl_w|by apply rq_hold_W]. }
  assert (Forall (skn W []) [pc 0 0; pc 1 0]) as HK.
  { constructor; [by left|constructor; [by left|constructor]]. }
  tstep.
  { tstep; [apply cli_typed, HW|apply srv_typed, HW]. }
  cbn. tstep.
  { tstep; [tstep|apply (KTNew _ _ _ Sa (pc 0 0) (or_introl Ha))|done|apply ubs_none]. }
  cbn. tstep.
  { tstep; [tstep|apply (KTNew _ _ _ Sb (pc 1 0) (or_introl Hb))|done|apply ubs_none]. }
  cbn. tstep.
  { tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pc 1 0)) (Some (pc 0 0)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy; first [apply sle_refl, HW|right; by apply sl_w]. }
    cbn. tstep; [tstep|]. cbn.
    eapply tv_app; [exact HW|reflexivity| | |].
    - apply (typed_force W _ _ _ _ _ _ 2 rq_C None srv_body [pc 0 0; pc 1 0]);
        [done|done|exact HC|exact HK|apply ubs_none|tstep].
    - tstep; tstep.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pc 1 0). split; [done|]. apply sle_refl, HW. }
  cbn. eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force W _ _ _ _ _ _ 2 rq_C None cli_body [pc 0 0; pc 1 0]);
      [done|done|exact HC|exact HK|apply ubs_none|tstep].
  - tstep; tstep.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|done].
Qed.

Definition rr_L (x y : point) : Prop :=
  ∃ k, (x = pc 0 k ∧ y = pc 1 k) ∨ (x = pc 1 k ∧ y = pc 0 (S k)).

(** The uniform facts (a,k) ≺ (b,k) ≺ (a,k+1), strict by the ranks
    2(k+1) and 2(k+1)+1. *)
Definition Wrr : world := wgen (list_to_set (NConst <$> [0; 1])) (λ _ _, False) rr_L.

Lemma Wrr_strict : strict Wrr.
Proof.
  apply (wgen_strict _ _ _ id (prank (λ _, 2) (λ a, a) (λ _ _ _, 0))); try done.
  - intros p Hp. apply elem_of_list_to_set, list_elem_of_fmap in Hp as (a & -> & _). by exists a.
  - intros x y (k & [[-> ->]|[-> ->]]); right; rewrite !elem_of_list_to_set; cbn; set_solver.
  - intros x. apply prank_shift. lia.
  - intros x y (k & [[-> ->]|[-> ->]]); unfold id, prank; cbn; lia.
Qed.

Lemma rr_deadlock_free : deadlock_free (∅, {[+ rr_main +]}).
Proof.
  apply (soundness Wrr _ TUnit Wrr_strict).
  apply ptyped_closed; [constructor|]. apply rr_typed; [apply Wrr_strict| | | |].
  - unfold pt_known, Wrr. simpl. set_solver.
  - unfold pt_known, Wrr. simpl. set_solver.
  - intros k. apply glt_base. exists k. by left.
  - intros k. apply glt_base. exists k. by right.
Qed.
