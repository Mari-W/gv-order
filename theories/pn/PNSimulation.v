(** * Deadlock freedom of the source program, by simulation

    [pn_deadlock_free] (PNTranslate.v) makes the translation e′ of a
    closed program deadlock free in lang/Semantics.v. This file carries
    that back to the source e in the semantics of Padovani and Novara
    (PNSemantics.v).

    - [trel Ξ M s t m] relates a source term s and a target term t at a
      mode m, the shape of a P&N type that the translation reads. It
      contains every translation [pn_typed] produces ([trel_of_typed]),
      the administrative forms reached on the way to a source step, and
      it is closed under renaming and substitution ([trel_subst]).
    - Every source step is matched by target steps, the corresponding
      step plus administrative ones ([fwd]). After a message both ends
      close at once ([fwd] at [SOut] and [SIn]), so the extra close
      never blocks. At new the target creates the channel inside the
      encoded let of new and takes two β steps to the let pair of the
      two ends ([tr_new] to [tr_newp]).
    - When the source is stuck, administrative steps bring every target
      thread to a value or to a pending send or receive ([final]).

    A fix runs its body once at every source unfolding, and the target
    forces its box at the same moment ([tr_fix]), so the theorem
    [pn_deadlock_free_source] covers every fix λf.e
    (padovani-novara.md §9). *)

From stdpp Require Import base gmap gmultiset relations.
From LRGV Require Import lang.ThreadSim.
From LRGV Require Export pn.PNSemantics pn.PNTranslate pn.PNExamples.

Set Default Proof Using "All".

(** ** Modes *)

Inductive mode :=
  | MUnit
  | MSum (m1 m2 : mode)
  | MChan (m : mode)
  | MRecC
  | MFn (m1 m2 : mode)
  | MBox (m1 m2 : mode).

(** A channel that carries the recursive channel has the mode of the
    recursive channel, so that a recursive type and its unfolding agree. *)
Definition mchan (m : mode) : mode := match m with MRecC => MRecC | _ => MChan m end.
Definition pay (m : mode) : mode := match m with MChan m => m | MRecC => MRecC | _ => MUnit end.
Definition chanm (m : mode) : Prop := match m with MChan _ | MRecC => True | _ => False end.

Lemma pay_mchan m : pay (mchan m) = m.
Proof. by destruct m. Qed.
Lemma chanm_mchan m : chanm (mchan m).
Proof. by destruct m. Qed.

Fixpoint pmode (t : pty) : mode :=
  match t with
  | PUnit => MUnit
  | PSum t s => MSum (pmode t) (pmode s)
  | PChan _ t _ => mchan (pmode t)
  | PRec _ _ _ => MRecC
  | PDisp _ t => pmode t
  | PArr t r _ s =>
      match r with Some _ => MFn (pmode t) (pmode s) | None => MBox (pmode t) (pmode s) end
  end.

Lemma mode_lshift k t : pmode (lshift k t) = pmode t.
Proof.
  induction t as [| | p t IH n|p m n|m t IH|t IH1 r σ s IH2]; simpl; try done.
  - by rewrite IH.
  - destruct r; simpl; by rewrite IH1, IH2.
Qed.

Lemma mode_pconv1 t t' : pconv1 t t' → pmode t = pmode t'.
Proof. destruct 1; simpl; [done|]. by rewrite mode_lshift. Qed.

Lemma mode_pconv t t' : pconv t t' → pmode t = pmode t'.
Proof.
  induction 1 as [|t t' t'' H _ IH|t t' t'' H _ IH]; [done| |].
  - by rewrite (mode_pconv1 _ _ H).
  - by rewrite <-(mode_pconv1 _ _ H).
Qed.

Definition fmode (p : bool) : mode := if p then MBox MUnit MUnit else MFn MUnit MUnit.

(** ** Administrative forms of the target

    [send1 t] is send_tr applied to the channel t, [recv1 t] is recv_tr
    applied to t, [fork1 p t] is fork_tr applied to the thunk t and
    [fthunk p t] the thunk it spawns. [boxlam b] is a λ of level ⊤ and
    [injbox1 t] the injection after its λ. *)

Notation send1 t :=
  (Lam (LetU (App EClos (App ESend (Pair (Var 0) (rename S t)))) unitv)).
Notation recvk := (LetU (App EClos (Var 0)) (Var 1)).
Notation recv1 t := (LetP (App ERecv t) recvk).
Notation fthunk p t :=
  (Lam (LetU (Var 0) (App EForce (App (if p then App EForce (rename S t) else rename S t) unitv)))).
Notation fork1 p t := (LetU (App ESpawn (fthunk p t)) unitv).
Notation boxlam b := (EBox (Lam (rename (upren S) b))).
Notation injbox1 t := (EBox (Inj1 (rename S t))).
Notation injbox2 t := (EBox (Inj2 (rename S t))).

(** ** The relation *)

Inductive trel (Ξ : chan → mode) : (nat → option mode) → expr → expr → mode → Prop :=
  | tr_var M x m :
      M x = Some m → trel Ξ M (Var x) (Var x) m
  | tr_unit M :
      trel Ξ M EUnit unitv MUnit
  | tr_chan M a :
      trel Ξ M (Chan a) (Chan a) (Ξ a)
  | tr_lam M b b' m1 m2 :
      trel Ξ (Some m1 .: M) b b' m2 →
      trel Ξ M (Lam b) (Lam b') (MFn m1 m2)
  | tr_blam M b b' m1 m2 :
      trel Ξ (Some m1 .: M) b b' m2 →
      trel Ξ M (Lam b) (boxlam b') (MBox m1 m2)
  | tr_fix M e e' m :
      trel Ξ (Some m .: M) e e' m →
      trel Ξ M (EBox e) (App EForce (EBox (subst thk e'))) m
  | tr_app M s1 s2 t1 t2 m1 m2 :
      trel Ξ M s1 t1 (MFn m1 m2) → trel Ξ M s2 t2 m1 →
      trel Ξ M (App s1 s2) (App t1 t2) m2
  | tr_appb M s1 s2 t1 t2 m1 m2 :
      trel Ξ M s1 t1 (MBox m1 m2) → trel Ξ M s2 t2 m1 →
      trel Ξ M (App s1 s2) (App (App EForce t1) t2) m2
  | tr_new M e e' mc m :
      chanm mc →
      trel Ξ (Some mc .: Some mc .: M) e e' m →
      trel Ξ M (LetP (App ENew EUnit) e) (let_new_pair e') m
  | tr_newp M a e e' mc m :
      chanm mc → Ξ a = mc →
      trel Ξ (Some mc .: Some mc .: M) e e' m →
      trel Ξ M (LetP (Pair (Chan a) (Chan a)) e) (LetP (Pair (Chan a) (Chan a)) e') m
  | tr_send M s1 s2 t1 t2 mc :
      chanm mc → trel Ξ M s1 t1 mc → trel Ξ M s2 t2 (pay mc) →
      trel Ξ M (App (App ESend s1) s2) (App (App send_tr t1) t2) MUnit
  | tr_send1 M s1 s2 t1 t2 mc :
      chanm mc → is_val t1 → trel Ξ M s1 t1 mc → trel Ξ M s2 t2 (pay mc) →
      trel Ξ M (App (App ESend s1) s2) (App (send1 t1) t2) MUnit
  | tr_recv M s t mc :
      chanm mc → trel Ξ M s t mc →
      trel Ξ M (App ERecv s) (App recv_tr t) (pay mc)
  | tr_recv1 M s t mc :
      chanm mc → is_val t → trel Ξ M s t mc →
      trel Ξ M (App ERecv s) (recv1 t) (pay mc)
  | tr_fork M p s t :
      trel Ξ M s t (fmode p) →
      trel Ξ M (App ESpawn s) (App (fork_tr p) t) MUnit
  | tr_fork1 M p s t :
      is_val t → trel Ξ M s t (fmode p) →
      trel Ξ M (App ESpawn s) (fork1 p t) MUnit
  | tr_inj1 M s t m1 m2 :
      trel Ξ M s t m1 → trel Ξ M (Inj1 s) (App inj1_tr t) (MSum m1 m2)
  | tr_inj1b M s t m1 m2 :
      is_val t → trel Ξ M s t m1 → trel Ξ M (Inj1 s) (injbox1 t) (MSum m1 m2)
  | tr_inj2 M s t m1 m2 :
      trel Ξ M s t m2 → trel Ξ M (Inj2 s) (App inj2_tr t) (MSum m1 m2)
  | tr_inj2b M s t m1 m2 :
      is_val t → trel Ξ M s t m2 → trel Ξ M (Inj2 s) (injbox2 t) (MSum m1 m2)
  | tr_case M s t e1 e1' e2 e2' m1 m2 m :
      trel Ξ M s t (MSum m1 m2) →
      trel Ξ (Some m1 .: M) e1 e1' m → trel Ξ (Some m2 .: M) e2 e2' m →
      trel Ξ M (Case s e1 e2) (Case (App EForce t) e1' e2') m.

(** ** Renaming and substitution facts for the gadgets *)

Lemma is_val_rename r e : is_val (rename r e) = is_val e.
Proof. induction e; simpl; try done; by rewrite ?IHe1, ?IHe2, ?IHe. Qed.

Lemma is_val_subst σ e : is_val e → is_val (subst σ e).
Proof.
  revert σ. induction e; simpl; intros σ He; try done; auto.
  apply andb_True in He as [??]. apply andb_True. auto.
Qed.

Lemma fchans_subst_sup σ e : fchans e ⊆ fchans (subst σ e).
Proof. revert σ. induction e; intros σ; simpl; try set_solver. Qed.

Lemma subst_scons_S Y e : subst (Y .: Var) (rename S e) = e.
Proof. rewrite subst_rename. apply subst_ids. Qed.

Lemma rn_S r t : rename (upren r) (rename S t) = rename S (rename r t).
Proof. rewrite !rename_rename. by apply rename_ext. Qed.

Lemma sb_S σ t : subst (up σ) (rename S t) = rename S (subst σ t).
Proof. rewrite subst_rename, rename_subst. by apply subst_ext. Qed.

Lemma rn_boxlam r b :
  rename (upren (upren r)) (rename (upren S) b) = rename (upren S) (rename (upren r) b).
Proof. rewrite !rename_rename. apply rename_ext. by intros [|x]. Qed.

Lemma sb_boxlam σ b :
  subst (up (up σ)) (rename (upren S) b) = rename (upren S) (subst (up σ) b).
Proof.
  rewrite subst_rename, rename_subst. apply subst_ext. intros [|x]; simpl; [done|].
  unfold compose. by rewrite !rename_rename.
Qed.

Lemma rename_as_subst r e : rename r e = subst (λ x, Var (r x)) e.
Proof.
  revert r. induction e; intros r; simpl; f_equal; auto.
  all: try (rewrite IHe; apply subst_ext; by intros [|x]).
  - rewrite IHe2. apply subst_ext. by intros [|[|x]].
  - rewrite IHe2. apply subst_ext. by intros [|x].
  - rewrite IHe3. apply subst_ext. by intros [|x].
Qed.

Lemma sb_thk σ e : subst (up σ) (subst thk e) = subst thk (subst (up σ) e).
Proof.
  rewrite !subst_subst. apply subst_ext. intros [|y]; [done|].
  change (subst (up σ) (Var (S y)) = subst thk (rename S (σ y))).
  rewrite subst_rename. simpl. rewrite rename_as_subst. by apply subst_ext.
Qed.

Lemma rn_thk r e : rename (upren r) (subst thk e) = subst thk (rename (upren r) e).
Proof. rewrite rename_subst, subst_rename. apply subst_ext. by intros [|x]. Qed.

(** The force of the box of a fix substitutes the fix for f. *)
Lemma force_thk e :
  subst1 (EBox (subst thk e)) (subst thk e) = subst (App EForce (EBox (subst thk e)) .: Var) e.
Proof. unfold subst1. rewrite subst_subst. apply subst_ext. by intros [|x]. Qed.

Lemma fchans_thk e : fchans (subst thk e) ⊆ fchans e.
Proof.
  pose proof (fchans_subst e thk ∅) as H. rewrite union_empty_r_L in H. apply H.
  apply allfv_forall. intros [|x]; simpl; set_solver.
Qed.

Lemma rename_unitv r : rename r unitv = unitv.
Proof. done. Qed.
Lemma subst_unitv σ : subst σ unitv = unitv.
Proof. done. Qed.
Lemma rename_send_tr r : rename r send_tr = send_tr.
Proof. done. Qed.
Lemma subst_send_tr σ : subst σ send_tr = send_tr.
Proof. done. Qed.
Lemma rename_recv_tr r : rename r recv_tr = recv_tr.
Proof. done. Qed.
Lemma subst_recv_tr σ : subst σ recv_tr = recv_tr.
Proof. done. Qed.
Lemma rename_fork_tr r p : rename r (fork_tr p) = fork_tr p.
Proof. by destruct p. Qed.
Lemma subst_fork_tr σ p : subst σ (fork_tr p) = fork_tr p.
Proof. by destruct p. Qed.
Lemma subst_inj1_tr σ : subst σ inj1_tr = inj1_tr.
Proof. done. Qed.
Lemma subst_inj2_tr σ : subst σ inj2_tr = inj2_tr.
Proof. done. Qed.

Lemma rename_inj_expr r e1 e2 :
  (∀ x y, r x = r y → x = y) → rename r e1 = rename r e2 → e1 = e2.
Proof.
  assert (∀ r, (∀ x y, r x = r y → x = y) → ∀ x y, upren r x = upren r y → x = y) as Hup.
  { intros r' Hr [|x] [|y]; simpl; unfold compose; try done.
    intros [= ?]. f_equal. by apply Hr. }
  revert r e2. induction e1; intros r e2 Hr; destruct e2; simpl; intros [=]; f_equal; eauto.
Qed.

(** ** The relation under renaming and substitution *)

Lemma trel_rename Ξ M s t m :
  trel Ξ M s t m → ∀ M' r, (∀ x mx, M x = Some mx → M' (r x) = Some mx) →
  trel Ξ M' (rename r s) (rename r t) m.
Proof.
  assert (∀ (M M' : nat → option mode) r m1,
    (∀ x mx, M x = Some mx → M' (r x) = Some mx) →
    ∀ x mx, (Some m1 .: M) x = Some mx → (Some m1 .: M') (upren r x) = Some mx) as Hup.
  { intros M0 M0' r m1 Hr [|x] mx; simpl; auto. }
  induction 1; intros M' r Hr; simpl.
  - apply tr_var. auto.
  - apply tr_unit.
  - apply tr_chan.
  - apply tr_lam. eauto.
  - rewrite rn_boxlam. apply tr_blam. eauto.
  - rewrite rn_thk. apply tr_fix. eauto.
  - eapply tr_app; eauto.
  - eapply tr_appb; eauto.
  - pose proof (rename_let_new_pair r e') as E. simpl in E. rewrite E.
    eapply tr_new; [done|]. eauto.
  - eapply tr_newp; [done|done|]. eauto.
  - eapply tr_send; eauto.
  - rewrite rn_S. eapply tr_send1; eauto. by rewrite is_val_rename.
  - eapply tr_recv; eauto.
  - eapply tr_recv1; [done| |eauto]. by rewrite is_val_rename.
  - destruct p; [apply (tr_fork _ _ true)|apply (tr_fork _ _ false)]; eauto.
  - destruct p; simpl; rewrite rn_S; [eapply (tr_fork1 _ _ true _ (rename r t))|eapply (tr_fork1 _ _ false _ (rename r t))]; (by rewrite is_val_rename) || eauto.
  - eapply tr_inj1; eauto.
  - rewrite rn_S. eapply tr_inj1b; [by rewrite is_val_rename|eauto].
  - eapply tr_inj2; eauto.
  - rewrite rn_S. eapply tr_inj2b; [by rewrite is_val_rename|eauto].
  - eapply tr_case; eauto.
Qed.

Lemma trel_subst Ξ M s t m :
  trel Ξ M s t m → ∀ M' σ σ',
  (∀ x mx, M x = Some mx → trel Ξ M' (σ x) (σ' x) mx) →
  trel Ξ M' (subst σ s) (subst σ' t) m.
Proof.
  assert (∀ M M' σ σ' m1,
    (∀ x mx, M x = Some mx → trel Ξ M' (σ x) (σ' x) mx) →
    ∀ x mx, (Some m1 .: M) x = Some mx → trel Ξ (Some m1 .: M') (up σ x) (up σ' x) mx) as Hup.
  { intros M0 M0' σ σ' m1 Hσ [|x] mx; simpl.
    - intros [= <-]. by constructor.
    - intros Hx. unfold compose. eapply trel_rename; [by apply Hσ|]. done. }
  induction 1; intros M' σ σ' Hσ; simpl.
  - auto.
  - apply tr_unit.
  - apply tr_chan.
  - apply tr_lam. eauto.
  - rewrite sb_boxlam. apply tr_blam. eauto.
  - rewrite sb_thk. apply tr_fix. eauto 10.
  - eapply tr_app; eauto.
  - eapply tr_appb; eauto.
  - pose proof (subst_let_new_pair σ' e') as E. simpl in E. rewrite E.
    eapply tr_new; [done|]. eauto 10.
  - eapply tr_newp; [done|done|]. eauto 10.
  - eapply tr_send; eauto.
  - rewrite sb_S. eapply tr_send1; eauto. by apply is_val_subst.
  - eapply tr_recv; eauto.
  - eapply tr_recv1; [done| |eauto]. by apply is_val_subst.
  - destruct p; [apply (tr_fork _ _ true)|apply (tr_fork _ _ false)]; eauto.
  - destruct p; simpl; rewrite sb_S; [eapply (tr_fork1 _ _ true _ (subst σ' t))|eapply (tr_fork1 _ _ false _ (subst σ' t))]; (by apply is_val_subst) || eauto.
  - eapply tr_inj1; eauto.
  - rewrite sb_S. eapply tr_inj1b; [by apply is_val_subst|eauto].
  - eapply tr_inj2; eauto.
  - rewrite sb_S. eapply tr_inj2b; [by apply is_val_subst|eauto].
  - eapply tr_case; eauto.
Qed.

(** The relation reads Ξ only at the channels of the source. *)
Lemma trel_xi Ξ M s t m :
  trel Ξ M s t m → ∀ Ξ', (∀ c, c ∈ fchans s → Ξ' c = Ξ c) → trel Ξ' M s t m.
Proof.
  induction 1; intros Ξ' HΞ; simpl in HΞ.
  - by constructor.
  - constructor.
  - rewrite <-HΞ by set_solver. constructor.
  - constructor. auto.
  - constructor. auto.
  - constructor. auto.
  - eapply tr_app; [apply IHtrel1|apply IHtrel2]; set_solver.
  - eapply tr_appb; [apply IHtrel1|apply IHtrel2]; set_solver.
  - eapply tr_new; [done|apply IHtrel; set_solver].
  - eapply tr_newp; [done| |apply IHtrel; set_solver].
    rewrite HΞ; [done|set_solver].
  - eapply tr_send; [done|apply IHtrel1|apply IHtrel2]; set_solver.
  - eapply tr_send1; [done|done|apply IHtrel1|apply IHtrel2]; set_solver.
  - eapply tr_recv; [done|apply IHtrel]; set_solver.
  - eapply tr_recv1; [done|done|apply IHtrel]; set_solver.
  - eapply tr_fork; apply IHtrel; set_solver.
  - eapply tr_fork1; [done|apply IHtrel]; set_solver.
  - eapply tr_inj1; apply IHtrel; set_solver.
  - eapply tr_inj1b; [done|apply IHtrel]; set_solver.
  - eapply tr_inj2; apply IHtrel; set_solver.
  - eapply tr_inj2b; [done|apply IHtrel]; set_solver.
  - eapply tr_case; [apply IHtrel1|apply IHtrel2|apply IHtrel3]; set_solver.
Qed.

Lemma trel_fchans Ξ M s t m : trel Ξ M s t m → fchans t ⊆ fchans s.
Proof.
  induction 1; simpl; rewrite ?fchans_rename; try set_solver.
  all: try (pose proof (fchans_thk e'); set_solver).
  all: try (destruct p; simpl; rewrite ?fchans_rename; set_solver).
  all: unfold let_new_pair, let_new; simpl; rewrite ?fchans_rename; set_solver.
Qed.

Lemma trel_mono Ξ M s t m :
  trel Ξ M s t m → ∀ M', (∀ x mx, M x = Some mx → M' x = Some mx) → trel Ξ M' s t m.
Proof.
  intros H M' HM. rewrite <-(rename_id s), <-(rename_id t).
  eapply trel_rename; [done|]. done.
Qed.

(** ** Every translation is related *)

Definition menv (Γ : penv) : nat → option mode :=
  λ x, match Γ !! x with Some (Some t) => Some (pmode t) | _ => None end.

Lemma menv_cons t Γ x mx :
  (Some (pmode t) .: menv Γ) x = Some mx → menv (Some t :: Γ) x = Some mx.
Proof. by destruct x. Qed.

Lemma pn_split_l Γ Γ1 Γ2 x t :
  pn_split Γ Γ1 Γ2 → Γ1 !! x = Some (Some t) → Γ !! x = Some (Some t).
Proof.
  intros Hs. revert x. induction Hs; intros [|x]; simpl; auto; done.
Qed.

Lemma pn_split_r Γ Γ1 Γ2 x t :
  pn_split Γ Γ1 Γ2 → Γ2 !! x = Some (Some t) → Γ !! x = Some (Some t).
Proof.
  intros Hs. revert x. induction Hs; intros [|x]; simpl; auto; done.
Qed.

Lemma menv_split_l Γ Γ1 Γ2 x mx :
  pn_split Γ Γ1 Γ2 → menv Γ1 x = Some mx → menv Γ x = Some mx.
Proof.
  unfold menv. intros Hs. destruct (Γ1 !! x) as [[t|]|] eqn:E; try done.
  by rewrite (pn_split_l _ _ _ _ _ Hs E).
Qed.

Lemma menv_split_r Γ Γ1 Γ2 x mx :
  pn_split Γ Γ1 Γ2 → menv Γ2 x = Some mx → menv Γ x = Some mx.
Proof.
  unfold menv. intros Hs. destruct (Γ2 !! x) as [[t|]|] eqn:E; try done.
  by rewrite (pn_split_r _ _ _ _ _ Hs E).
Qed.

Lemma env_lev_un Γ : penv_un Γ → env_lev Γ = None.
Proof.
  induction Γ as [|[t|] Γ IH]; intros Hu; simpl; [done| |].
  - rewrite (Hu t) by set_solver. simpl. apply IH. intros t' ?. apply Hu. set_solver.
  - apply IH. intros t' ?. apply Hu. set_solver.
Qed.

Lemma pn_typed_lam_inv Γ b t τ e' :
  pn_typed Γ (Lam b) t τ e' → ∃ b0, e' = lam_tr (env_lev Γ) b0.
Proof.
  remember (Lam b) as s eqn:Hs. induction 1; try discriminate; eauto.
Qed.

Lemma trel_blam_inv Ξ M b b0 m :
  trel Ξ M (Lam b) (boxlam b0) m → ∃ m1 m2, m = MBox m1 m2 ∧ trel Ξ (Some m1 .: M) b b0 m2.
Proof.
  inversion 1; subst. exists m1, m2. split; [done|].
  match goal with H : rename _ ?x = rename _ b0 |- _ =>
    apply rename_inj_expr in H as ->; [done|] end.
  intros [|x] [|y]; simpl; unfold compose; congruence.
Qed.

Ltac splitf := repeat match goal with H : Is_true (_ && _) |- _ => apply andb_True in H as [? ?] end.

Lemma trel_of_typed Ξ Γ e t τ e' :
  pn_typed Γ e t τ e' → trel Ξ (menv Γ) e e' (pmode t).
Proof.
  induction 1; simpl.
  - constructor. unfold menv. by destruct H as [-> _].
  - constructor.
  - unfold lam_tr. destruct (env_lev Γ); simpl; [apply tr_lam|apply tr_blam];
      (eapply trel_mono; [by apply IHpn_typed|]); intros [|x] mx; done.
  - eapply tr_app.
    + eapply trel_mono; [by apply IHpn_typed1|]. intros. by eapply menv_split_l.
    + eapply trel_mono; [by apply IHpn_typed2|]. intros. by eapply menv_split_r.
  - rewrite mode_lshift. eapply tr_appb.
    + eapply trel_mono; [by apply IHpn_typed1|]. intros. by eapply menv_split_l.
    + rewrite mode_lshift in IHpn_typed2.
      eapply trel_mono; [exact IHpn_typed2|]. intros. by eapply menv_split_r.
  - eapply (tr_new _ _ _ _ (mchan (pmode t))); [apply chanm_mchan|].
    eapply trel_mono; [by apply IHpn_typed|]. intros [|[|x]] mx; done.
  - eapply (tr_send _ _ _ _ _ _ (mchan (pmode t))); [apply chanm_mchan| |].
    + eapply trel_mono; [by apply IHpn_typed1|]. intros. by eapply menv_split_l.
    + rewrite pay_mchan.
      eapply trel_mono; [by apply IHpn_typed2|]. intros. by eapply menv_split_r.
  - rewrite <-(pay_mchan (pmode t)).
    apply tr_recv; [apply chanm_mchan|]. by apply IHpn_typed.
  - apply tr_fork. by destruct r.
  - apply tr_fix. eapply trel_mono; [by apply IHpn_typed|]. intros [|x] mx; done.
  - apply tr_inj1. auto.
  - apply tr_inj2. auto.
  - eapply tr_case.
    + eapply trel_mono; [by apply IHpn_typed1|]. intros. by eapply menv_split_l.
    + eapply trel_mono; [by apply IHpn_typed2|].
      intros [|x] mx; simpl; [done|]. intros. by eapply menv_split_r.
    + eapply trel_mono; [by apply IHpn_typed3|].
      intros [|x] mx; simpl; [done|]. intros. by eapply menv_split_r.
  - rewrite <-(mode_pconv _ _ H0). auto.
Qed.

(** ** Canonical forms and administrative normalization *)

Definition M0 : nat → option mode := λ _, None.
Definition xi_ok (Ξ : chan → mode) : Prop := ∀ a, chanm (Ξ a).

Lemma trel_konst Ξ M k t m : trel Ξ M (Konst k) t m → False.
Proof. inversion 1. Qed.

Lemma trel_app_send Ξ M x t m : trel Ξ M (App ESend x) t m → False.
Proof. inversion 1; subst; eauto using trel_konst. Qed.

Lemma trel_sval_app Ξ M s1 s2 t m : trel Ξ M (App s1 s2) t m → is_sval (App s1 s2) → False.
Proof.
  intros H Hv. destruct s1 as [| | [] | | | | | | | | | |]; try done.
  inversion H; subst; eauto using trel_konst.
Qed.

Ltac closedtac := match goal with
  | HM : ∀ x, ?M x = None, H : ?M _ = Some _ |- _ => rewrite HM in H; discriminate
  end.
Ltac chantac := match goal with
  | Hxi : xi_ok ?Ξ, H : ?Ξ ?a = ?m |- _ => specialize (Hxi a); rewrite H in Hxi; contradiction
  end.

Lemma lam_force_eq X b : subst (up (X .: Var)) (rename (upren S) b) = b.
Proof.
  rewrite subst_rename. rewrite <-(subst_ids b) at 2. apply subst_ext. by intros [|x].
Qed.

Lemma src_canon Ξ M s t m :
  trel Ξ M s t m → (∀ x, M x = None) → xi_ok Ξ → is_sval s →
  match m with
  | MUnit => s = EUnit
  | MSum _ _ => ∃ v, is_sval v ∧ (s = Inj1 v ∨ s = Inj2 v)
  | MChan _ | MRecC => ∃ a, s = Chan a
  | MFn _ _ | MBox _ _ => ∃ b, s = Lam b
  end.
Proof.
  intros H HM Hxi Hv. destruct H; simpl in Hv; try done; eauto; try closedtac.
  all: try (exfalso; eapply trel_sval_app; [|exact Hv]; by eapply tr_app).
  all: try (exfalso; eapply trel_sval_app; [|exact Hv]; by eapply tr_appb).
  specialize (Hxi a). destruct (Ξ a); simpl in *; try done; eauto.
Qed.

Lemma val_norm Ξ M s t m :
  trel Ξ M s t m → (∀ x, M x = None) → is_sval s →
  ∃ w, bstar t w ∧ is_val w ∧ trel Ξ M s w m.
Proof.
  induction 1; intros HM Hv; simpl in Hv; try done; try closedtac.
  all: try (exfalso; eapply trel_sval_app; [|exact Hv]; by eapply tr_app).
  all: try (exfalso; eapply trel_sval_app; [|exact Hv]; by eapply tr_appb).
  all: try (eexists; split_and!; [apply rtc_refl|done|]; by constructor).
  - destruct (IHtrel HM Hv) as (w & Hs & Hw & Hr). exists (injbox1 w). split_and!.
    + eapply rtc_r.
      * eapply (rtc_congruence (λ x, App inj1_tr x)); [|done]. intros. by apply TStepAppR.
      * by apply TStepHead, HeadApp.
    + done.
    + by apply tr_inj1b.
  - destruct (IHtrel HM Hv) as (w & Hs & Hw & Hr). exists (injbox2 w). split_and!.
    + eapply rtc_r.
      * eapply (rtc_congruence (λ x, App inj2_tr x)); [|done]. intros. by apply TStepAppR.
      * by apply TStepHead, HeadApp.
    + done.
    + by apply tr_inj2b.
Qed.

Lemma fn_norm Ξ M s t m1 m2 :
  trel Ξ M s t (MFn m1 m2) → (∀ x, M x = None) → xi_ok Ξ → is_sval s →
  ∃ b b', s = Lam b ∧ bstar t (Lam b') ∧ trel Ξ (Some m1 .: M) b b' m2.
Proof.
  intros H HM Hxi Hv. destruct (val_norm _ _ _ _ _ H HM Hv) as (w & Hs & Hw & Hr).
  inversion Hr; subst; simpl in *; try done; try closedtac; try chantac; eauto.
Qed.

Lemma box_norm Ξ M s t m1 m2 :
  trel Ξ M s t (MBox m1 m2) → (∀ x, M x = None) → xi_ok Ξ → is_sval s →
  ∃ b b' w, s = Lam b ∧ bstar t w ∧ is_val w ∧ bstar (App EForce w) (Lam b') ∧
    trel Ξ (Some m1 .: M) b b' m2 ∧ trel Ξ M s w (MBox m1 m2).
Proof.
  intros H HM Hxi Hv. destruct (val_norm _ _ _ _ _ H HM Hv) as (w & Hs & Hw & Hr).
  inversion Hr; subst; simpl in *; try done; try closedtac; try chantac.
  - exists b, b', (boxlam b'). split_and!; try done.
    apply rtc_once. apply TStepHead.
    rewrite <-(lam_force_eq (boxlam b') b') at 2. apply HeadForce.
Qed.

Lemma chan_norm Ξ M s t mc :
  trel Ξ M s t mc → chanm mc → (∀ x, M x = None) → is_sval s →
  ∃ a, s = Chan a ∧ bstar t (Chan a) ∧ mc = Ξ a.
Proof.
  intros H Hc HM Hv. destruct (val_norm _ _ _ _ _ H HM Hv) as (w & Hs & Hw & Hr).
  inversion Hr; subst; simpl in *; try done; try closedtac; eauto.
Qed.

Lemma unit_norm Ξ M s t :
  trel Ξ M s t MUnit → (∀ x, M x = None) → xi_ok Ξ → is_sval s →
  s = EUnit ∧ bstar t unitv.
Proof.
  intros H HM Hxi Hv. destruct (val_norm _ _ _ _ _ H HM Hv) as (w & Hs & Hw & Hr).
  inversion Hr; subst; simpl in *; try done; try closedtac; try chantac.
Qed.

Lemma sum_norm Ξ M s t m1 m2 :
  trel Ξ M s t (MSum m1 m2) → (∀ x, M x = None) → xi_ok Ξ → is_sval s →
  ∃ v w, is_val w ∧
    ((s = Inj1 v ∧ bstar t (injbox1 w) ∧ trel Ξ M v w m1) ∨
     (s = Inj2 v ∧ bstar t (injbox2 w) ∧ trel Ξ M v w m2)).
Proof.
  intros H HM Hxi Hv. destruct (val_norm _ _ _ _ _ H HM Hv) as (w & Hs & Hw & Hr).
  inversion Hr; subst; simpl in *; try done; try closedtac; try chantac; eauto 10.
Qed.

(** A target value related to a source that steps does not occur. The
    lemma keeps the form it had while a fix unfolded in the source
    alone. *)
Lemma val_stutter Ξ M s w m α s' :
  trel Ξ M s w m → (∀ x, M x = None) → is_val w → src_step s α s' →
  α = SBeta ∧ trel Ξ M s' w m.
Proof.
  intros H. revert α s'. induction H; intros α s' HM Hw Hst; simpl in Hw; try done.
  all: try (exfalso; apply src_step_not_val in Hst; done).
  - inversion Hst as [? ? ? Hh| | | | | |]; subst; [inversion Hh|].
    match goal with Hi : src_step s _ _ |- _ => destruct (IHtrel _ _ HM H Hi) as [-> ?] end.
    split; [done|]. by apply tr_inj1b.
  - inversion Hst as [? ? ? Hh| | | | | |]; subst; [inversion Hh|].
    match goal with Hi : src_step s _ _ |- _ => destruct (IHtrel _ _ HM H Hi) as [-> ?] end.
    split; [done|]. by apply tr_inj2b.
Qed.

Lemma src_progress Ξ M s t m :
  trel Ξ M s t m → (∀ x, M x = None) → xi_ok Ξ → is_sval s ∨ ∃ α s', src_step s α s'.
Proof.
  intros H HM Hxi. induction H; simpl; auto.
  - by rewrite HM in H.
  - right. eexists _, _. by apply SSHead, SHFix.
  - right. destruct (IHtrel1 HM) as [Hv1|(α & s' & ?)]; [|eexists _, _; by apply SSAppL].
    destruct (IHtrel2 HM) as [Hv2|(α & s' & ?)]; [|eexists _, _; by apply SSAppR].
    destruct (src_canon _ _ _ _ _ H HM Hxi Hv1) as [b ->].
    eexists _, _. by apply SSHead, SHApp.
  - right. destruct (IHtrel1 HM) as [Hv1|(α & s' & ?)]; [|eexists _, _; by apply SSAppL].
    destruct (IHtrel2 HM) as [Hv2|(α & s' & ?)]; [|eexists _, _; by apply SSAppR].
    destruct (src_canon _ _ _ _ _ H HM Hxi Hv1) as [b ->].
    eexists _, _. by apply SSHead, SHApp.
  - right. eexists _, _. apply SSLetP, SSHead, (SHNew inhabitant).
  - right. eexists _, _. by apply SSHead, SHLetP.
  - right. destruct (IHtrel1 HM) as [Hv1|(α & s' & ?)];
      [|eexists _, _; apply SSAppL, SSAppR; [done|eassumption]].
    destruct (IHtrel2 HM) as [Hv2|(α & s' & ?)]; [|eexists _, _; by apply SSAppR].
    pose proof (src_canon _ _ _ _ _ H0 HM Hxi Hv1) as Hc.
    destruct mc; try done; destruct Hc as [a ->]; eexists _, _; by apply SSHead, SHSend.
  - right. destruct (IHtrel1 HM) as [Hv1|(α & s' & ?)];
      [|eexists _, _; apply SSAppL, SSAppR; [done|eassumption]].
    destruct (IHtrel2 HM) as [Hv2|(α & s' & ?)]; [|eexists _, _; by apply SSAppR].
    pose proof (src_canon _ _ _ _ _ H1 HM Hxi Hv1) as Hc.
    destruct mc; try done; destruct Hc as [a ->]; eexists _, _; by apply SSHead, SHSend.
  - right. destruct (IHtrel HM) as [Hv1|(α & s' & ?)]; [|eexists _, _; by apply SSAppR].
    pose proof (src_canon _ _ _ _ _ H0 HM Hxi Hv1) as Hc.
    destruct mc; try done; destruct Hc as [a ->]; eexists _, _; apply SSHead, (SHRecv _ EUnit); done.
  - right. destruct (IHtrel HM) as [Hv1|(α & s' & ?)]; [|eexists _, _; by apply SSAppR].
    pose proof (src_canon _ _ _ _ _ H1 HM Hxi Hv1) as Hc.
    destruct mc; try done; destruct Hc as [a ->]; eexists _, _; apply SSHead, (SHRecv _ EUnit); done.
  - right. destruct (IHtrel HM) as [Hv1|(α & s' & ?)]; [|eexists _, _; by apply SSAppR].
    eexists _, _. by apply SSHead, SHSpawn.
  - right. destruct (IHtrel HM) as [Hv1|(α & s' & ?)]; [|eexists _, _; by apply SSAppR].
    eexists _, _. by apply SSHead, SHSpawn.
  - destruct (IHtrel HM) as [?|(α & s' & ?)]; [by left|right; eexists _, _; by apply SSInj1].
  - destruct (IHtrel HM) as [?|(α & s' & ?)]; [by left|right; eexists _, _; by apply SSInj1].
  - destruct (IHtrel HM) as [?|(α & s' & ?)]; [by left|right; eexists _, _; by apply SSInj2].
  - destruct (IHtrel HM) as [?|(α & s' & ?)]; [by left|right; eexists _, _; by apply SSInj2].
  - right. destruct (IHtrel1 HM) as [Hv|(α & s' & ?)]; [|eexists _, _; by apply SSCase].
    destruct (src_canon _ _ _ _ _ H HM Hxi Hv) as (v & Hv' & [->| ->]);
      eexists _, _; apply SSHead; by constructor.
Qed.

(** ** Inversion of source steps *)

Lemma sinv_app s1 s2 α s' :
  src_step (App s1 s2) α s' →
  src_head (App s1 s2) α s' ∨ (∃ s1', src_step s1 α s1' ∧ s' = App s1' s2) ∨
  (is_sval s1 ∧ ∃ s2', src_step s2 α s2' ∧ s' = App s1 s2').
Proof. inversion 1; subst; eauto 10. Qed.

Lemma sinv_letp p e α s' :
  src_step (LetP p e) α s' →
  src_head (LetP p e) α s' ∨ ∃ p', src_step p α p' ∧ s' = LetP p' e.
Proof. inversion 1; subst; eauto. Qed.

Lemma sinv_case s e1 e2 α s' :
  src_step (Case s e1 e2) α s' →
  src_head (Case s e1 e2) α s' ∨ ∃ s0, src_step s α s0 ∧ s' = Case s0 e1 e2.
Proof. inversion 1; subst; eauto. Qed.

Lemma sinv_inj1 s α s' : src_step (Inj1 s) α s' → ∃ s0, src_step s α s0 ∧ s' = Inj1 s0.
Proof. inversion 1 as [? ? ? Hh| | | | | |]; subst; [inversion Hh|eauto]. Qed.

Lemma sinv_inj2 s α s' : src_step (Inj2 s) α s' → ∃ s0, src_step s α s0 ∧ s' = Inj2 s0.
Proof. inversion 1 as [? ? ? Hh| | | | | |]; subst; [inversion Hh|eauto]. Qed.

Lemma sinv_konst k α s' : src_step (Konst k) α s' → False.
Proof. intros H. by apply src_step_not_val in H. Qed.

Lemma sinv_new α p' :
  src_step (App ENew EUnit) α p' → ∃ a, α = SNew a ∧ p' = Pair (Chan a) (Chan a).
Proof.
  intros H. apply sinv_app in H as [Hh|[(? & H & _)|(_ & ? & H & _)]].
  - inversion Hh; subst. eauto.
  - by apply sinv_konst in H.
  - by apply src_step_not_val in H.
Qed.

Lemma sinv_pair a b α p' : src_step (Pair (Chan a) (Chan b)) α p' → False.
Proof. inversion 1 as [? ? ? Hh| | | | | |]. inversion Hh. Qed.

(** ** What a source step asks of the target *)

Definition upd (Ξ : chan → mode) (a : chan) (mc : mode) : chan → mode :=
  λ c, if decide (c = a) then mc else Ξ c.

Lemma xi_ok_upd Ξ a mc : xi_ok Ξ → chanm mc → xi_ok (upd Ξ a mc).
Proof. intros H Hc c. unfold upd. by destruct (decide (c = a)). Qed.

Definition xok (Ξ : chan → mode) (α : slab) (Ξ' : chan → mode) : Prop :=
  match α with SNew a => ∃ mc, Ξ' = upd Ξ a mc | _ => Ξ' = Ξ end.

(** A spawned thread ⟨v ()⟩ against force (v′ (box ∗)). *)
Definition Rsp (Ξ : chan → mode) (M : nat → option mode) (s t : expr) : Prop :=
  ∃ t0, t = App EForce t0 ∧ trel Ξ M s t0 MUnit.

(** [post Ξ M α t Q]. The target t performs the step that matches the
    source label α, with administrative β steps before and after, and
    ends in a state that satisfies Q. A message is followed by the close
    of the sender, and the receiver closes right after its β. *)
Definition post (Ξ : chan → mode) (M : nat → option mode) (α : slab) (t : expr)
    (Q : (chan → mode) → expr → Prop) : Prop :=
  match α with
  | SBeta => ∃ t', bstar t t' ∧ Q Ξ t'
  | SNew a => ∃ mc t0 t1 t', chanm mc ∧ bstar t t0 ∧ tstep t0 (LNew a) t1 ∧ bstar t1 t' ∧
      Q (upd Ξ a mc) t'
  | SSpawn v => ∃ t0 w t1 tn t', bstar t t0 ∧ tstep t0 (LSpawn w) t1 ∧
      bstar (App w EUnit) tn ∧ Rsp Ξ M (App v EUnit) tn ∧ bstar t1 t' ∧ Q Ξ t'
  | SOut a v => ∃ t0 w t1 t2 t', bstar t t0 ∧ tstep t0 (LSess (SSend a w)) t1 ∧
      trel Ξ M v w (pay (Ξ a)) ∧ tstep t1 (LSess (SClos a)) t2 ∧ bstar t2 t' ∧ Q Ξ t'
  | SIn a v => ∃ t0, bstar t t0 ∧ ∀ w, is_val w → ∃ t1, tstep t0 (LSess (SRecv a w)) t1 ∧
      (trel Ξ M v w (pay (Ξ a)) → ∃ t1' t2 t', bstar t1 t1' ∧
         tstep t1' (LSess (SClos a)) t2 ∧ bstar t2 t' ∧ Q Ξ t')
  end.

Lemma post_ectx Ξ M α t Q Q' K :
  ectx K → post Ξ M α t Q → (∀ Ξ' t', xok Ξ α Ξ' → Q Ξ' t' → Q' Ξ' (K t')) →
  post Ξ M α (K t) Q'.
Proof.
  intros HK Hp HQ. destruct α; simpl in *.
  - destruct Hp as (t' & Hs & Hq). exists (K t'). split; [by apply bstar_ectx|]. by apply HQ.
  - destruct Hp as (mc & t0 & t1 & t' & Hc & Hs & Ht & Hs1 & Hq).
    exists mc, (K t0), (K t1), (K t'). split_and!; [done|by apply bstar_ectx|by apply HK|by apply bstar_ectx|].
    apply HQ; [by exists mc|done].
  - destruct Hp as (t0 & w & t1 & tn & t' & Hs & Ht & Hn & Hr & Hs' & Hq).
    exists (K t0), w, (K t1), tn, (K t'). split_and!; try done; try by apply bstar_ectx.
    + by apply HK.
    + by apply HQ.
  - destruct Hp as (t0 & w & t1 & t2 & t' & Hs & H1 & Hr & H2 & Hs' & Hq).
    exists (K t0), w, (K t1), (K t2), (K t'). split_and!; try done; try by apply bstar_ectx.
    + by apply HK.
    + by apply HK.
    + by apply HQ.
  - destruct Hp as (t0 & Hs & Hw). exists (K t0). split; [by apply bstar_ectx|].
    intros w Hv. destruct (Hw w Hv) as (t1 & H1 & Hk). exists (K t1). split; [by apply HK|].
    intros Hr. destruct (Hk Hr) as (t1' & t2 & t' & Hs1 & H2 & Hs2 & Hq).
    exists (K t1'), (K t2), (K t'). split_and!; try by apply bstar_ectx.
    + by apply HK.
    + by apply HQ.
Qed.

Lemma post_pre Ξ M α t t0 Q : bstar t t0 → post Ξ M α t0 Q → post Ξ M α t Q.
Proof.
  intros H0 Hp. destruct α; simpl in *.
  - destruct Hp as (t' & Hs & Hq). eexists. split; [by etrans|done].
  - destruct Hp as (mc & t1 & t2 & t' & Hc & Hs & Ht & Hs2 & Hq).
    eexists _, _, _, _. split_and!; [done|by etrans|done|done|done].
  - destruct Hp as (t1 & w & t2 & tn & t' & Hs & ?). eexists _, _, _, _, _. split; [by etrans|done].
  - destruct Hp as (t1 & w & t2 & t3 & t' & Hs & ?). eexists _, _, _, _, _. split; [by etrans|done].
  - destruct Hp as (t1 & Hs & Hw). eexists. split; [by etrans|done].
Qed.

Lemma trel_sib Ξ Ξ' α M s t m :
  xok Ξ α Ξ' → (∀ a, α = SNew a → a ∉ fchans s) → trel Ξ M s t m → trel Ξ' M s t m.
Proof.
  intros Hx Hf Ht. destruct α; simpl in Hx; try (by subst).
  destruct Hx as [mc ->]. eapply trel_xi; [done|]. intros c Hc. unfold upd.
  destruct (decide (c = a)) as [->|]; [|done]. by destruct (Hf a eq_refl).
Qed.

Lemma sub1_ok Ξ M v w m1 :
  trel Ξ M v w m1 → (∀ x, M x = None) →
  ∀ x mx, (Some m1 .: M) x = Some mx → trel Ξ M ((v .: Var) x) ((w .: Var) x) mx.
Proof. intros Hr HM [|x] mx; simpl; [by intros [= <-]|by rewrite HM]. Qed.

Lemma send_from_send1 Ξ M a v t2 :
  trel Ξ M v t2 (pay (Ξ a)) → (∀ x, M x = None) → is_sval v →
  post Ξ M (SOut a v) (App (send1 (Chan a)) t2) (λ Ξ' t', trel Ξ' M EUnit t' MUnit).
Proof.
  intros H2 HM Hv. destruct (val_norm _ _ _ _ _ H2 HM Hv) as (w2 & Hs2 & Hw2 & Hr2).
  simpl. eexists (LetU (App EClos (App ESend (Pair w2 (Chan a)))) unitv), w2,
    (LetU (App EClos (Chan a)) unitv), (LetU EUnit unitv), unitv. split_and!.
  - eapply rtc_trans; [apply (bstar_ectx (λ x, App (send1 (Chan a)) x)); [by apply ectx_appr|exact Hs2]|].
    apply rtc_once. exact (TStepHead _ _ _ (HeadApp _ _ Hw2)).
  - apply TStepLetU, TStepAppR; [done|]. by apply TStepHead, HeadSend.
  - done.
  - apply TStepLetU, TStepHead, HeadClos.
  - apply rtc_once, TStepHead, HeadLetU.
  - apply tr_unit.
Qed.

Lemma recv_from_recv1 Ξ M a v m :
  m = pay (Ξ a) →
  post Ξ M (SIn a v) (recv1 (Chan a)) (λ Ξ' t', trel Ξ' M v t' m).
Proof.
  intros ->. simpl. exists (recv1 (Chan a)). split; [apply rtc_refl|].
  intros w Hw. exists (LetP (Pair w (Chan a)) recvk). split; [by apply TStepLetP, TStepHead, HeadRecv|].
  intros Hr. exists (LetU (App EClos (Chan a)) w), (LetU EUnit w), w. split_and!.
  - apply rtc_once. exact (TStepHead _ _ _ (HeadLetP w (Chan a) recvk Hw I)).
  - apply TStepLetU, TStepHead, HeadClos.
  - apply rtc_once, TStepHead, HeadLetU.
  - done.
Qed.

Lemma spawn_from_fork1 Ξ M p v w :
  is_val w → trel Ξ M v w (fmode p) →
  post Ξ M (SSpawn v) (fork1 p w) (λ Ξ' t', trel Ξ' M EUnit t' MUnit).
Proof.
  intros Hw Hr. simpl.
  exists (fork1 p w), (fthunk p w), (LetU EUnit unitv),
    (App EForce (App (if p then App EForce w else w) unitv)), unitv. split_and!.
  - apply rtc_refl.
  - by apply TStepLetU, TStepHead, HeadSpawn.
  - eapply rtc_l; [by apply TStepHead, HeadApp|].
    assert (subst1 EUnit (LetU (Var 0) (App EForce (App (if p then App EForce (rename S w)
              else rename S w) unitv))) = LetU EUnit (App EForce (App (if p then App EForce w
              else w) unitv))) as ->.
    { unfold subst1. destruct p; simpl; by rewrite subst_scons_S. }
    apply rtc_once, TStepHead, HeadLetU.
  - eexists. split; [done|]. destruct p.
    + exact (tr_appb _ _ _ _ _ _ _ _ Hr (tr_unit _ _)).
    + exact (tr_app _ _ _ _ _ _ _ _ Hr (tr_unit _ _)).
  - apply rtc_once, TStepHead, HeadLetU.
  - apply tr_unit.
Qed.

(** ** Forward simulation of one thread *)

Ltac fresh_sub Hfr := let a := fresh "a" in let Ha := fresh "Ha" in
  intros a Ha; specialize (Hfr a Ha); simpl in Hfr; set_solver.

Lemma fwd Ξ M s t m :
  trel Ξ M s t m → (∀ x, M x = None) → xi_ok Ξ →
  ∀ α s', src_step s α s' → (∀ a, α = SNew a → a ∉ fchans s) →
  post Ξ M α t (λ Ξ' t', trel Ξ' M s' t' m).
Proof.
  induction 1 as [M x m Hx|M|M a|M b b' m1 m2 Hb IH|M b b' m1 m2 Hb IH
    |M e0 e0' m He0 IH
    |M s1 s2 t1 t2 m1 m2 H1 IH1 H2 IH2|M s1 s2 t1 t2 m1 m2 H1 IH1 H2 IH2
    |M e e' mc m Hc He IH|M a e e' mc m Hc Ha He IH
    |M s1 s2 t1 t2 mc Hc H1 IH1 H2 IH2|M s1 s2 t1 t2 mc Hc Hv1 H1 IH1 H2 IH2
    |M s t mc Hc H IH|M s t mc Hc Hv H IH
    |M p s t H IH|M p s t Hv H IH
    |M s t m1 m2 H IH|M s t m1 m2 Hv H IH|M s t m1 m2 H IH|M s t m1 m2 Hv H IH
    |M s t e1 e1' e2 e2' m1 m2 m H IH H1 IH1 H2 IH2];
    intros HM Hxi α s' Hst Hfr.
  (* values *)
  - by rewrite HM in Hx.
  - by apply src_step_not_val in Hst.
  - by apply src_step_not_val in Hst.
  - by apply src_step_not_val in Hst.
  - by apply src_step_not_val in Hst.
  (* fix λf.e unfolds in the source, and the target forces its box *)
  - inversion Hst as [? ? ? Hh| | | | | |]; subst. inversion Hh; subst.
    simpl. exists (subst1 (EBox (subst thk e0')) (subst thk e0')). split.
    + apply rtc_once, TStepHead, HeadForce.
    + rewrite force_thk. eapply trel_subst; [exact He0|]. intros [|x] mx; simpl.
      * intros [= <-]. by apply tr_fix.
      * by rewrite HM.
  (* application *)
  - apply sinv_app in Hst as [Hh|[(s1' & Hst1 & ->)|(Hv1 & s2' & Hst2 & ->)]].
    + inversion Hh; subst; try (exfalso; by eauto using trel_konst, trel_app_send).
      destruct (fn_norm _ _ _ _ _ _ H1 HM Hxi I) as (b & b' & [= <-] & Hs1 & Hb).
      match goal with Hv : Is_true (is_sval s2) |- _ =>
        destruct (val_norm _ _ _ _ _ H2 HM Hv) as (w2 & Hs2 & Hw2 & Hr2) end.
      simpl. exists (subst1 w2 b'). split.
      * eapply rtc_trans; [apply (bstar_ectx (λ x, App x t2)); [apply ectx_appl|exact Hs1]|].
        eapply rtc_trans; [apply (bstar_ectx (λ x, App (Lam b') x)); [by apply ectx_appr|exact Hs2]|].
        by apply rtc_once, TStepHead, HeadApp.
      * eapply trel_subst; [exact Hb|]. by apply sub1_ok.
    + eapply (post_ectx _ _ _ _ _ _ (λ x, App x t2)); [apply ectx_appl| |].
      * apply IH1; [done|done|exact Hst1|fresh_sub Hfr].
      * intros Ξ' t' Hx Hq. eapply tr_app; [exact Hq|]. eapply trel_sib; [exact Hx| |exact H2].
        fresh_sub Hfr.
    + destruct (fn_norm _ _ _ _ _ _ H1 HM Hxi Hv1) as (b & b' & -> & Hs1 & Hb).
      eapply post_pre; [apply (bstar_ectx (λ x, App x t2)); [apply ectx_appl|exact Hs1]|].
      eapply (post_ectx _ _ _ _ _ _ (λ x, App (Lam b') x)); [by apply ectx_appr| |].
      * apply IH2; [done|done|exact Hst2|fresh_sub Hfr].
      * intros Ξ' t' Hx Hq. eapply tr_app; [|exact Hq].
        eapply trel_sib; [exact Hx| |apply tr_lam, Hb]. fresh_sub Hfr.
  (* application of a function of level ⊤ *)
  - apply sinv_app in Hst as [Hh|[(s1' & Hst1 & ->)|(Hv1 & s2' & Hst2 & ->)]].
    + inversion Hh; subst; try (exfalso; by eauto using trel_konst, trel_app_send).
      destruct (box_norm _ _ _ _ _ _ H1 HM Hxi I) as (b & b' & w & [= <-] & Hs1 & Hw & Hf & Hb & _).
      match goal with Hv : Is_true (is_sval s2) |- _ =>
        destruct (val_norm _ _ _ _ _ H2 HM Hv) as (w2 & Hs2 & Hw2 & Hr2) end.
      simpl. exists (subst1 w2 b'). split.
      * eapply rtc_trans.
        { apply (bstar_ectx (λ x, App (App EForce x) t2)); [|exact Hs1].
          apply ectx_appl2; done. }
        eapply rtc_trans; [apply (bstar_ectx (λ x, App x t2)); [apply ectx_appl|exact Hf]|].
        eapply rtc_trans; [apply (bstar_ectx (λ x, App (Lam b') x)); [by apply ectx_appr|exact Hs2]|].
        by apply rtc_once, TStepHead, HeadApp.
      * eapply trel_subst; [exact Hb|]. by apply sub1_ok.
    + eapply (post_ectx _ _ _ _ _ _ (λ x, App (App EForce x) t2)).
      * apply ectx_appl2; done.
      * apply IH1; [done|done|exact Hst1|fresh_sub Hfr].
      * intros Ξ' t' Hx Hq. eapply tr_appb; [exact Hq|]. eapply trel_sib; [exact Hx| |exact H2].
        fresh_sub Hfr.
    + destruct (box_norm _ _ _ _ _ _ H1 HM Hxi Hv1) as (b & b' & w & -> & Hs1 & Hw & Hf & Hb & _).
      eapply post_pre.
      { apply (bstar_ectx (λ x, App (App EForce x) t2)); [|exact Hs1].
        apply ectx_appl2; done. }
      eapply post_pre; [apply (bstar_ectx (λ x, App x t2)); [apply ectx_appl|exact Hf]|].
      eapply (post_ectx _ _ _ _ _ _ (λ x, App (Lam b') x)); [by apply ectx_appr| |].
      * apply IH2; [done|done|exact Hst2|fresh_sub Hfr].
      * intros Ξ' t' Hx Hq. eapply tr_app; [|exact Hq].
        eapply trel_sib; [exact Hx| |apply tr_lam, Hb]. fresh_sub Hfr.
  (* let a = new() in e. The target creates the channel inside the
     encoded let of new and takes two β steps to the let pair. *)
  - apply sinv_letp in Hst as [Hh|(p' & Hstp & ->)]; [inversion Hh|].
    apply sinv_new in Hstp as (a & -> & ->).
    set (e'' := rename (upren (upren (λ x, 2 + x))) e').
    simpl. exists mc, (let_new_pair e'),
      (LetP (Pair (Pair (Chan a) (Chan a)) EUnit) (LetU (Var 0) (LetP (Var 1) e''))),
      (LetP (Pair (Chan a) (Chan a)) e').
    split_and!; [done|apply rtc_refl|apply TStepLetP, TStepPairL, TStepHead, HeadNew| |].
    + eapply rtc_l; [apply TStepHead, HeadLetP; done|].
      unfold subst2. cbn [subst scons]. unfold e''. rewrite let_new_body.
      apply rtc_once, TStepHead, HeadLetU.
    + eapply tr_newp; [done|unfold upd; by rewrite decide_True|].
      eapply trel_xi; [exact He|]. intros c Hcf. unfold upd.
      destruct (decide (c = a)) as [->|]; [|done].
      exfalso. apply (Hfr a eq_refl). simpl. set_solver.
  (* the let pair of the two ends *)
  - apply sinv_letp in Hst as [Hh|(p' & Hstp & ->)]; [|by apply sinv_pair in Hstp].
    inversion Hh as [| |u v e0 Hu Hv| | | | | |]; subst.
    simpl. exists (subst2 (Chan a) (Chan a) e'). split.
    + by apply rtc_once, TStepHead, HeadLetP.
    + eapply trel_subst; [exact He|]. intros [|[|x]] mx; simpl.
      { intros [= <-]. apply tr_chan. }
      { intros [= <-]. apply tr_chan. }
      by rewrite HM.
  (* send *)
  - apply sinv_app in Hst as [Hh|[(e1' & Hst1 & ->)|(Hv1 & s2' & Hst2 & ->)]].
    + inversion Hh as [| | | | | | |a v Hv|]; subst.
      destruct (chan_norm _ _ _ _ _ H1 Hc HM I) as (a' & [= <-] & Hs1 & ->).
      eapply post_pre.
      { apply (bstar_ectx (λ x, App (App send_tr x) t2)); [|exact Hs1].
        apply ectx_appl2; done. }
      eapply post_pre.
      { apply rtc_once. apply TStepAppL. exact (TStepHead _ _ _ (HeadApp _ (Chan a) I)). }
      by apply send_from_send1.
    + apply sinv_app in Hst1 as [Hh|[(? & Hk & _)|(_ & s1' & Hst1 & ->)]].
      * inversion Hh.
      * by apply sinv_konst in Hk.
      * eapply (post_ectx _ _ _ _ _ _ (λ x, App (App send_tr x) t2)).
        { apply ectx_appl2; done. }
        { apply IH1; [done|done|exact Hst1|fresh_sub Hfr]. }
        intros Ξ' t' Hx Hq. eapply tr_send; [done|exact Hq|].
        eapply trel_sib; [exact Hx| |exact H2]. fresh_sub Hfr.
    + simpl in Hv1. destruct (val_norm _ _ _ _ _ H1 HM Hv1) as (w1 & Hs1 & Hw1 & Hr1).
      eapply post_pre.
      { apply (bstar_ectx (λ x, App (App send_tr x) t2)); [|exact Hs1].
        apply ectx_appl2; done. }
      eapply post_pre.
      { apply rtc_once. apply TStepAppL. exact (TStepHead _ _ _ (HeadApp _ w1 Hw1)). }
      eapply (post_ectx _ _ _ _ _ _ (λ x, App (send1 w1) x)); [by apply ectx_appr| |].
      * apply IH2; [done|done|exact Hst2|fresh_sub Hfr].
      * intros Ξ' t' Hx Hq. eapply tr_send1; [done|done| |exact Hq].
        eapply trel_sib; [exact Hx| |exact Hr1]. fresh_sub Hfr.
  - apply sinv_app in Hst as [Hh|[(e1' & Hst1 & ->)|(Hv2 & s2' & Hst2 & ->)]].
    + inversion Hh as [| | | | | | |a v Hv|]; subst.
      destruct (chan_norm _ _ _ _ _ H1 Hc HM I) as (a' & [= <-] & Hs1 & ->).
      rewrite <-(bstar_val _ _ Hv1 Hs1). by apply send_from_send1.
    + apply sinv_app in Hst1 as [Hh|[(? & Hk & _)|(_ & s1' & Hst1 & ->)]].
      * inversion Hh.
      * by apply sinv_konst in Hk.
      * destruct (val_stutter _ _ _ _ _ _ _ H1 HM Hv1 Hst1) as [-> Hr].
        simpl. eexists. split; [apply rtc_refl|]. by eapply tr_send1.
    + eapply (post_ectx _ _ _ _ _ _ (λ x, App (send1 t1) x)); [by apply ectx_appr| |].
      * apply IH2; [done|done|exact Hst2|fresh_sub Hfr].
      * intros Ξ' t' Hx Hq. eapply tr_send1; [done|done| |exact Hq].
        eapply trel_sib; [exact Hx| |exact H1]. fresh_sub Hfr.
  (* recv *)
  - apply sinv_app in Hst as [Hh|[(e1' & Hk & ->)|(_ & s0 & Hst0 & ->)]].
    + inversion Hh as [| | | | | | | |a v Hv]; subst.
      destruct (chan_norm _ _ _ _ _ H Hc HM I) as (a' & [= <-] & Hs & ->).
      eapply post_pre.
      { apply (bstar_ectx (λ x, App recv_tr x)); [by apply ectx_appr|exact Hs]. }
      eapply post_pre.
      { apply rtc_once. exact (TStepHead _ _ _ (HeadApp _ (Chan a) I)). }
      by apply recv_from_recv1.
    + by apply sinv_konst in Hk.
    + eapply (post_ectx _ _ _ _ _ _ (λ x, App recv_tr x)); [by apply ectx_appr| |].
      * apply IH; [done|done|exact Hst0|fresh_sub Hfr].
      * intros Ξ' t' Hx Hq. by eapply tr_recv.
  - apply sinv_app in Hst as [Hh|[(e1' & Hk & ->)|(_ & s0 & Hst0 & ->)]].
    + inversion Hh as [| | | | | | | |a v Hv']; subst.
      destruct (chan_norm _ _ _ _ _ H Hc HM I) as (a' & [= <-] & Hs & ->).
      rewrite <-(bstar_val _ _ Hv Hs). by apply recv_from_recv1.
    + by apply sinv_konst in Hk.
    + destruct (val_stutter _ _ _ _ _ _ _ H HM Hv Hst0) as [-> Hr].
      simpl. eexists. split; [apply rtc_refl|]. by eapply tr_recv1.
  (* fork *)
  - apply sinv_app in Hst as [Hh|[(e1' & Hk & ->)|(_ & s0 & Hst0 & ->)]].
    + inversion Hh as [| | | | | |v Hv| |]; subst.
      destruct (val_norm _ _ _ _ _ H HM Hv) as (w & Hs & Hw & Hr).
      assert (is_val (fork_tr p)) by (by destruct p).
      eapply post_pre.
      { apply (bstar_ectx (λ x, App (fork_tr p) x)); [by apply ectx_appr|exact Hs]. }
      destruct p; (eapply post_pre;
        [apply rtc_once; apply TStepHead; exact (HeadApp _ w Hw)|]);
        exact (spawn_from_fork1 _ _ _ _ _ Hw Hr).
    + by apply sinv_konst in Hk.
    + assert (is_val (fork_tr p)) by (by destruct p).
      eapply (post_ectx _ _ _ _ _ _ (λ x, App (fork_tr p) x)); [by apply ectx_appr| |].
      * apply IH; [done|done|exact Hst0|fresh_sub Hfr].
      * intros Ξ' t' Hx Hq. by eapply tr_fork.
  - apply sinv_app in Hst as [Hh|[(e1' & Hk & ->)|(_ & s0 & Hst0 & ->)]].
    + inversion Hh; subst. by apply spawn_from_fork1.
    + by apply sinv_konst in Hk.
    + destruct (val_stutter _ _ _ _ _ _ _ H HM Hv Hst0) as [-> Hr].
      simpl. eexists. split; [apply rtc_refl|]. by eapply tr_fork1.
  (* injections *)
  - apply sinv_inj1 in Hst as (s0 & Hst0 & ->).
    eapply (post_ectx _ _ _ _ _ _ (λ x, App inj1_tr x)); [by apply ectx_appr| |].
    + apply IH; [done|done|exact Hst0|fresh_sub Hfr].
    + intros Ξ' t' Hx Hq. by apply tr_inj1.
  - destruct (val_stutter _ _ _ _ _ _ _ (tr_inj1b _ _ _ _ m1 m2 Hv H) HM ltac:(done) Hst) as [-> Hr].
    simpl. eexists. split; [apply rtc_refl|done].
  - apply sinv_inj2 in Hst as (s0 & Hst0 & ->).
    eapply (post_ectx _ _ _ _ _ _ (λ x, App inj2_tr x)); [by apply ectx_appr| |].
    + apply IH; [done|done|exact Hst0|fresh_sub Hfr].
    + intros Ξ' t' Hx Hq. by apply tr_inj2.
  - destruct (val_stutter _ _ _ _ _ _ _ (tr_inj2b _ _ _ _ m1 m2 Hv H) HM ltac:(done) Hst) as [-> Hr].
    simpl. eexists. split; [apply rtc_refl|done].
  (* case *)
  - assert (ectx (λ x, Case (App EForce x) e1' e2')) as HK.
    { apply ectx_case2. }
    apply sinv_case in Hst as [Hh|(s0 & Hst0 & ->)].
    + inversion Hh as [| | |v e0 e3 Hv|v e0 e3 Hv| | | |]; subst.
      * destruct (sum_norm _ _ _ _ _ _ H HM Hxi Hv) as (v' & w & Hw & [([= <-] & Hs & Hr)|(? & _)]);
          [|done].
        simpl. exists (subst1 w e1'). split.
        { eapply rtc_trans; [apply (bstar_ectx _ _ _ HK Hs)|].
          eapply rtc_l; [apply TStepCase, TStepHead, HeadForce|].
          replace (subst1 (injbox1 w) (Inj1 (rename S w))) with (Inj1 w)
            by (unfold subst1; simpl; by rewrite subst_scons_S).
          by apply rtc_once, TStepHead, HeadCase1. }
        eapply trel_subst; [exact H1|]. by apply sub1_ok.
      * destruct (sum_norm _ _ _ _ _ _ H HM Hxi Hv) as (v' & w & Hw & [(? & _)|([= <-] & Hs & Hr)]);
          [done|].
        simpl. exists (subst1 w e2'). split.
        { eapply rtc_trans; [apply (bstar_ectx _ _ _ HK Hs)|].
          eapply rtc_l; [apply TStepCase, TStepHead, HeadForce|].
          replace (subst1 (injbox2 w) (Inj2 (rename S w))) with (Inj2 w)
            by (unfold subst1; simpl; by rewrite subst_scons_S).
          by apply rtc_once, TStepHead, HeadCase2. }
        eapply trel_subst; [exact H2|]. by apply sub1_ok.
    + eapply (post_ectx _ _ _ _ _ _ _ HK).
      * apply IH; [done|done|exact Hst0|fresh_sub Hfr].
      * intros Ξ' t' Hx Hq. eapply tr_case; [exact Hq| |].
        { eapply trel_sib; [exact Hx| |exact H1]. fresh_sub Hfr. }
        { eapply trel_sib; [exact Hx| |exact H2]. fresh_sub Hfr. }
Qed.

(** ** Threads and processes *)

(** A thread of the source against a thread of the target. The main
    thread is related at unit, a spawned thread ⟨v ()⟩ by [Rsp]. *)
Definition Rt (Ξ : chan → mode) (s t : expr) : Prop := trel Ξ M0 s t MUnit ∨ Rsp Ξ M0 s t.

Lemma fwd_rt Ξ s t α s' :
  Rt Ξ s t → xi_ok Ξ → src_step s α s' → (∀ a, α = SNew a → a ∉ fchans s) →
  post Ξ M0 α t (λ Ξ' t', Rt Ξ' s' t').
Proof.
  intros [H|(t0 & -> & H)] Hxi Hst Hfr.
  - eapply (post_ectx _ _ _ _ _ _ (λ x, x)); [apply ectx_id| |].
    + eapply fwd; [exact H|done|done|exact Hst|exact Hfr].
    + intros Ξ' t' _ Hq. by left.
  - eapply (post_ectx _ _ _ _ _ _ (λ x, App EForce x)); [by apply ectx_appr| |].
    + eapply fwd; [exact H|done|done|exact Hst|exact Hfr].
    + intros Ξ' t' _ Hq. right. by eexists.
Qed.

Lemma Rt_fchans Ξ s t : Rt Ξ s t → fchans t ⊆ fchans s.
Proof.
  intros [H|(t0 & -> & H)]; apply trel_fchans in H; simpl; set_solver.
Qed.

Lemma Rt_xi Ξ Ξ' s t : Rt Ξ s t → (∀ c, c ∈ fchans s → Ξ' c = Ξ c) → Rt Ξ' s t.
Proof.
  intros [H|(t0 & -> & H)] HΞ; [left|right; eexists; split; [done|]]; by eapply trel_xi.
Qed.

(** The process relation. Both sides restrict the same names, and Ξ
    gives every channel a channel mode. *)
Definition prel (p q : proc) : Prop :=
  p.1 = q.1 ∧ ∃ Ξ, xi_ok Ξ ∧ mrel (Rt Ξ) p.2 q.2.

Lemma sim_step p p' q : src_tau p p' → prel p q → ∃ q', pred_star q q' ∧ prel p' q'.
Proof.
  destruct p as [C Es], q as [Cq Et]. unfold src_tau.
  intros Hs (HC & Ξ & Hxi & Hm). simpl in HC, Hm. subst Cq.
  inversion Hs as [C0 E e e' Hst|C0 E e a e' Hst HaC HaE Hae|C0 E e v e' Hst
                  |C0 E a v e e' f f' Hse Hsf HaC|]; subst.
  - destruct (mrel_extract_l _ _ _ _ Hm) as (Et0 & t & -> & HR & Hm0).
    destruct (fwd_rt _ _ _ _ _ HR Hxi Hst ltac:(done)) as (t' & Hs' & Hq).
    exists (C, Et0 ⊎ {[+ t' +]}). split; [by apply bstar_proc|].
    split; [done|]. exists Ξ. split; [done|]. by apply mrel_snoc.
  - destruct (mrel_extract_l _ _ _ _ Hm) as (Et0 & t & -> & HR & Hm0).
    destruct (fwd_rt _ _ _ _ _ HR Hxi Hst ltac:(by intros ? [= <-]))
      as (mc & t0 & tn & t' & Hc & Hs0 & Ht & Hs1 & Hq).
    exists (C ∪ {[a]}, Et0 ⊎ {[+ t' +]}). split.
    + eapply rtc_trans; [by apply bstar_proc|]. eapply rtc_l; [apply PStepNew; [done|done| |]|].
      * pose proof (mrel_echans _ _ _ (Rt_fchans Ξ) Hm0). set_solver.
      * apply bstar_fchans in Hs0. apply Rt_fchans in HR. set_solver.
      * by apply bstar_proc.
    + split; [done|]. exists (upd Ξ a mc). split; [by apply xi_ok_upd|].
      apply mrel_snoc; [done|]. eapply mrel_impl; [|exact Hm0].
      intros s t1 Hin HR1. eapply Rt_xi; [exact HR1|]. intros c Hcs. unfold upd.
      destruct (decide (c = a)) as [->|]; [|done]. exfalso. apply HaE.
      apply elem_of_echans. eauto.
  - destruct (mrel_extract_l _ _ _ _ Hm) as (Et0 & t & -> & HR & Hm0).
    destruct (fwd_rt _ _ _ _ _ HR Hxi Hst ltac:(done))
      as (t0 & w & t1 & tn & t' & Hs0 & Ht & Hn & Hr & Hs1 & Hq).
    exists (C, Et0 ⊎ {[+ t' +]} ⊎ {[+ tn +]}). split.
    + eapply rtc_trans; [by apply bstar_proc|].
      eapply rtc_l; [by apply PStepSpawn|].
      eapply rtc_trans; [by apply bstar_proc|]. by apply bstar_proc2.
    + split; [done|]. exists Ξ. split; [done|].
      apply mrel_snoc; [by right|]. by apply mrel_snoc.
  - destruct (mrel_extract_l _ _ _ _ Hm) as (Et1 & tf & -> & HRf & Hm1).
    destruct (mrel_extract_l _ _ _ _ Hm1) as (Et0 & te & -> & HRe & Hm0).
    destruct (fwd_rt _ _ _ _ _ HRe Hxi Hse ltac:(done))
      as (t0 & w & t1 & t2 & te' & Hs0 & H1 & Hrw & H2 & Hs2 & Hqe).
    destruct (fwd_rt _ _ _ _ _ HRf Hxi Hsf ltac:(done)) as (u0 & Hu0 & Hw).
    destruct (Hw w (tstep_send_val _ _ _ _ H1)) as (u1 & Hu1 & Hk).
    destruct (Hk Hrw) as (u1' & u2 & tf' & Hs1 & Hu2 & Hs3 & Hqf).
    exists (C ∖ {[a]}, Et0 ⊎ {[+ te' +]} ⊎ {[+ tf' +]}). split.
    + eapply rtc_trans; [by apply bstar_proc2|].
      eapply rtc_trans; [by apply bstar_proc|].
      eapply rtc_l; [by eapply PStepMsg|].
      eapply rtc_trans; [by apply bstar_proc|].
      eapply rtc_l; [by eapply PStepClose|].
      eapply rtc_trans; [by apply bstar_proc2|]. by apply bstar_proc.
    + split; [done|]. exists Ξ. split; [done|].
      apply mrel_snoc; [done|]. by apply mrel_snoc.
Qed.

Lemma sim_star p p' q : rtc src_tau p p' → prel p q → ∃ q', pred_star q q' ∧ prel p' q'.
Proof.
  intros H. revert q. induction H as [|p1 p2 p3 H12 _ IH]; intros q Hp; [by exists q|].
  destruct (sim_step _ _ _ H12 Hp) as (q2 & Hq2 & Hp2).
  destruct (IH _ Hp2) as (q3 & Hq3 & Hp3). exists q3. split; [by etrans|done].
Qed.

(** ** Administrative steps never block *)

(** A stuck source thread is (), a pending send or a pending receive,
    and administrative β steps bring its target to a value, a pending
    send or a pending receive on the same channel. *)
Definition cls (s t : expr) : Prop :=
  (s = EUnit ∧ is_val t) ∨
  (∃ a v s'' w, src_step s (SOut a v) s'' ∧ act t = Some (ASend a w)) ∨
  (∃ a v s'', src_step s (SIn a v) s'' ∧ act t = Some (ARecv a)).

Lemma classify Ξ C E s t :
  xi_ok Ξ → src_irred (C, E ⊎ {[+ s +]}) → Rt Ξ s t → ∃ t', bstar t t' ∧ cls s t'.
Proof.
  intros Hxi Hirr HR.
  assert (∃ t1, trel Ξ M0 s t1 MUnit) as [t1 Ht1]
    by (destruct HR as [?|(? & _ & ?)]; eauto).
  destruct (src_progress _ _ _ _ _ Ht1 (λ _, eq_refl) Hxi) as [Hv|(α & s' & Hst)].
  - destruct HR as [H|(t0 & -> & H)].
    + destruct (unit_norm _ _ _ _ H (λ _, eq_refl) Hxi Hv) as [-> Hs].
      exists unitv. split; [done|by left].
    + destruct (unit_norm _ _ _ _ H (λ _, eq_refl) Hxi Hv) as [-> Hs].
      exists EUnit. split; [|by left]. eapply rtc_r.
      * apply (bstar_ectx (λ x, App EForce x)); [by apply ectx_appr|exact Hs].
      * apply TStepHead, HeadForce.
  - destruct α as [|a|v|a v|a v].
    + exfalso. eapply Hirr. by apply SPBeta.
    + set (b := fresh (C ∪ echans E ∪ fchans s)).
      assert (b ∉ C ∪ echans E ∪ fchans s) by apply is_fresh.
      destruct (src_step_new_any _ _ _ Hst b) as [s'' Hs''].
      exfalso. eapply Hirr. apply SPNew; [exact Hs''|set_solver..].
    + exfalso. eapply Hirr. by apply SPSpawn.
    + destruct (fwd_rt _ _ _ _ _ HR Hxi Hst ltac:(by intros ? [=]))
        as (t0 & w & t1' & t2 & t' & Hs0 & H1 & _).
      exists t0. split; [done|]. right; left.
      destruct (act_step _ _ _ H1) as (x & Hx & Ho). apply offers_send in Ho as ->. eauto 10.
    + destruct (fwd_rt _ _ _ _ _ HR Hxi Hst ltac:(by intros ? [=])) as (u0 & Hs0 & Hw).
      destruct (Hw EUnit I) as (u1 & Hu1 & _).
      exists u0. split; [done|]. right; right.
      destruct (act_step _ _ _ Hu1) as (x & Hx & Ho). apply offers_recv in Ho as ->. eauto 10.
Qed.

Lemma cls_step s t α t' :
  cls s t → tstep t α t' →
  (∃ a v s'' w, src_step s (SOut a v) s'' ∧ α = LSess (SSend a w)) ∨
  (∃ a v s'' w, src_step s (SIn a v) s'' ∧ α = LSess (SRecv a w)).
Proof.
  intros [(_ & Hv)|[(a & v & s'' & w & Hs & Hact)|(a & v & s'' & Hs & Hact)]] Hst.
  - exfalso. eauto using val_no_tstep.
  - destruct (act_step _ _ _ Hst) as (x & Hx & Ho). rewrite Hact in Hx. injection Hx as <-.
    left. destruct α as [|[]| |]; simpl in Ho; try done. destruct Ho as [-> ->]. eauto 10.
  - destruct (act_step _ _ _ Hst) as (x & Hx & Ho). rewrite Hact in Hx. injection Hx as <-.
    right. destruct α as [|[]| |]; simpl in Ho; try done. destruct Ho as [-> _]. eauto 10.
Qed.

Lemma final p q :
  prel p q → (∀ q', pred_star q q' → safe q') → src_irred p → src_final p.
Proof.
  destruct p as [C Es], q as [Cq Et]. intros (HC & Ξ & Hxi & Hm) Hsafe Hirr.
  simpl in HC, Hm. subst Cq.
  destruct (normalize _ cls _ _ Hm) as (Et' & Hst & Hm').
  { intros s t Hs HR. destruct (gmultiset_split1 _ _ Hs) as [E0 ->].
    by eapply classify. }
  destruct (Hsafe (C, Et') (msb_pred _ _ _ Hst)) as [Hterm|(q'' & Hred)].
  - destruct Hterm as (v & E1 & [= -> ->] & Hv & HE1).
    intros s Hs. simpl in Hs.
    destruct (mrel_elem_l _ _ _ _ Hm' Hs) as (t' & Ht' & Hc).
    assert (is_val t') as Hvt.
    { apply gmultiset_elem_of_disj_union in Ht' as [Ht'|Ht'].
      - by apply gmultiset_elem_of_singleton in Ht' as ->.
      - by rewrite (HE1 _ Ht'). }
    destruct Hc as [(-> & _)|[(? & ? & ? & ? & _ & Hact)|(? & ? & ? & _ & Hact)]]; [done| |];
      by rewrite act_val in Hact.
  - exfalso. unfold preduction in Hred.
    inversion Hred as [|C0 E0 e e' Hste|C0 E0 e c e' Hste|C0 E0 e v e' Hste
                      |C0 E0 c v e e' f f' Hse Hsf|C0 E0 c e e' f f' Hse Hsf Hc
                      |C0 E0 c b e e' f f' Hse Hsf Hc
                      |C0 E0 e c d e' Hste]; subst.
    + destruct (mrel_extract _ _ _ _ Hm') as (Es0 & s & -> & Hc & _).
      destruct (cls_step _ _ _ _ Hc Hste) as [(? & ? & ? & ? & _ & [=])|(? & ? & ? & ? & _ & [=])].
    + destruct (mrel_extract _ _ _ _ Hm') as (Es0 & s & -> & Hc & _).
      destruct (cls_step _ _ _ _ Hc Hste) as [(? & ? & ? & ? & _ & [=])|(? & ? & ? & ? & _ & [=])].
    + destruct (mrel_extract _ _ _ _ Hm') as (Es0 & s & -> & Hc & _).
      destruct (cls_step _ _ _ _ Hc Hste) as [(? & ? & ? & ? & _ & [=])|(? & ? & ? & ? & _ & [=])].
    + destruct (mrel_extract _ _ _ _ Hm') as (Es1 & sf & -> & Hcf & Hm1).
      destruct (mrel_extract _ _ _ _ Hm1) as (Es0 & se & -> & Hce & _).
      destruct (cls_step _ _ _ _ Hce Hse)
        as [(a & ve & se' & w & Hse' & [= -> ->])|(? & ? & ? & ? & _ & [=])].
      destruct (cls_step _ _ _ _ Hcf Hsf)
        as [(? & ? & ? & ? & _ & [=])|(a' & vf & sf' & w' & Hsf' & [= -> ->])].
      destruct (src_step_recv_any _ _ _ _ Hsf' ve (src_step_send_val _ _ _ _ Hse'))
        as [sf'' Hsf''].
      match type of Hse' with src_step _ (SOut ?ch _) _ => destruct (decide (ch ∈ C)) end.
      * eapply Hirr. by eapply SPCommRes.
      * eapply Hirr. by eapply SPCommFree.
    + destruct (mrel_extract _ _ _ _ Hm') as (Es1 & sf & -> & Hcf & Hm1).
      destruct (mrel_extract _ _ _ _ Hm1) as (Es0 & se & -> & Hce & _).
      destruct (cls_step _ _ _ _ Hce Hse) as [(? & ? & ? & ? & _ & [=])|(? & ? & ? & ? & _ & [=])].
    + destruct (mrel_extract _ _ _ _ Hm') as (Es1 & sf & -> & Hcf & Hm1).
      destruct (mrel_extract _ _ _ _ Hm1) as (Es0 & se & -> & Hce & _).
      destruct (cls_step _ _ _ _ Hce Hse) as [(? & ? & ? & ? & _ & [=])|(? & ? & ? & ? & _ & [=])].
    + destruct (mrel_extract _ _ _ _ Hm') as (Es0 & s & -> & Hc & _).
      destruct (cls_step _ _ _ _ Hc Hste) as [(? & ? & ? & ? & _ & [=])|(? & ? & ? & ? & _ & [=])].
Qed.

(** ** The theorem *)

Theorem pn_deadlock_free_source e τ e' :
  pn_typed [] e PUnit τ e' → pn_deadlock_free_src e.
Proof.
  intros Ht q Hq Hirr.
  set (Ξ0 := λ _ : chan, MRecC).
  assert (trel Ξ0 M0 e e' MUnit) as Hr.
  { eapply trel_mono; [exact (trel_of_typed Ξ0 _ _ _ _ _ Ht)|].
    intros x mx. unfold menv. by destruct x. }
  assert (prel (∅, {[+ e +]}) (∅, {[+ e' +]})) as Hp.
  { split; [done|]. exists Ξ0. split; [by intros a|].
    replace ({[+ e +]} : gmultiset expr) with ({[+ e +]} ⊎ (∅ : gmultiset expr)) by multiset_solver.
    replace ({[+ e' +]} : gmultiset expr) with ({[+ e' +]} ⊎ (∅ : gmultiset expr)) by multiset_solver.
    constructor; [by left|constructor]. }
  destruct (sim_star _ _ _ Hq Hp) as (q' & Hq' & Hp').
  eapply final; [exact Hp'| |exact Hirr].
  intros q'' Hq''. apply (pn_deadlock_free e τ e' Ht). by etrans.
Qed.

(** ** The examples in the source semantics *)

Theorem fibo_deadlock_free_src : pn_deadlock_free_src fibo_main.
Proof.
  destruct fibo_typed as (τ & e' & H). exact (pn_deadlock_free_source _ τ e' H).
Qed.

Theorem pipe_deadlock_free_src : pn_deadlock_free_src pipe_main.
Proof.
  destruct pipe_main_typed as (τ & e' & H). exact (pn_deadlock_free_source _ τ e' H).
Qed.

(** The fixes of pdf p. 14 and a fix whose body forks, none of them a
    λ, in the source semantics. *)
Theorem div_deadlock_free_src : pn_deadlock_free_src div_main.
Proof. destruct div_typed as (τ & e' & H). exact (pn_deadlock_free_source _ τ e' H). Qed.

Theorem divsend_deadlock_free_src : pn_deadlock_free_src divsend_main.
Proof. destruct divsend_typed as (τ & e' & H). exact (pn_deadlock_free_source _ τ e' H). Qed.

Theorem fixfork_deadlock_free_src : pn_deadlock_free_src fixfork_main.
Proof. destruct fixfork_typed as (τ & e' & H). exact (pn_deadlock_free_source _ τ e' H). Qed.
