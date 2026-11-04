(** * Deadlock freedom of the source program, by simulation, version 3

    Version 3 (docs/extensions/adequacy/mordido-perez.md, section 15)
    is version 2 with n-ary choices and with channels created after a
    segment call. The text below describes version 2 where version 3
    agrees with it.

    [mp3_deadlock_free] (MP2Translate.v) makes the translation e′ of a
    closed program deadlock free in lang/Semantics.v. This file carries
    that back to the source e in the semantics of Mordido and Pérez
    (MP2Semantics.v).

    - [trm M s t m] relates a source term s and a target term t at a
      mode m, the shape of a type that the translation reads: data
      (unit and channels), a linear function, or a box that is forced
      before application. It contains every translation [mtyped]
      produces ([trm_of_typed]) and the forced form of a recursive
      function, and it is closed under renaming and substitution.
    - Every source step is matched by target steps, the corresponding
      step plus administrative β steps ([fwd]). Communication is
      synchronous on both sides, so a message, a choice and a close
      each match one target step. new matches new ∗ followed by the two
      administrative β steps of the encoded let [let_new_pair].
    - When the source is stuck, administrative steps bring every target
      thread to a value, to the matching pending action, or to a term
      that offers nothing ([classify]).

    The theorem [mp3_deadlock_free_source] needs no premise beyond the
    typing. docs/extensions/adequacy/mordido-perez.md, section 14,
    explains the model. *)

From stdpp Require Import base gmap gmultiset relations.
From LRGV Require Import lang.Safety.
From LRGV Require Export mp.MP2Semantics mp.MP3Examples.

Set Default Proof Using "All".

(** ** Modes *)

Inductive md := MdD | MdF (m1 m2 : md) | MdB (m1 m2 : md).

Fixpoint mode_of (T : mty) : md :=
  match T with
  | MArr T _ _ V => MdF (mode_of T) (mode_of V)
  | MPoly _ T _ V => MdB (mode_of T) (mode_of V)
  | MSeg _ _ _ _ => MdB MdD MdD
  | _ => MdD
  end.

Lemma mode_msub σ τ T : mode_of (msub σ τ T) = mode_of T.
Proof. induction T; simpl; try done. by rewrite IHT1, IHT2. Qed.

Lemma mode_payty P : mode_of (payty P) = MdD.
Proof. by destruct P. Qed.

Lemma mode_rpayty p P : mode_of (rpayty p P) = MdD.
Proof. destruct p, P; done. Qed.

(** ** The relation

    [forced b′] is the target after it forced the translation of
    rec f. λx.b, before the argument is a value. *)

Abbreviation forced b := (Lam (subst (up (EBox (Lam b) .: Var)) b)).

Inductive trm : (nat → option md) → expr → expr → md → Prop :=
  | tr_var M x m :
      M x = Some m → trm M (Var x) (Var x) m
  | tr_unit M :
      trm M EUnit unitv MdD
  | tr_chan M a :
      trm M (Chan a) (Chan a) MdD
  | tr_lam M b b' m1 m2 :
      trm (Some m1 .: M) b b' m2 →
      trm M (Lam b) (Lam b') (MdF m1 m2)
  | tr_fix M b b' m1 m2 :
      trm (Some m1 .: Some (MdB m1 m2) .: M) b b' m2 →
      trm M (EBox (Lam b)) (EBox (Lam b')) (MdB m1 m2)
  | tr_app M s1 s2 t1 t2 m1 m2 :
      trm M s1 t1 (MdF m1 m2) → trm M s2 t2 m1 →
      trm M (App s1 s2) (App t1 t2) m2
  | tr_appb M s1 s2 t1 t2 m1 m2 :
      trm M s1 t1 (MdB m1 m2) → trm M s2 t2 m1 →
      trm M (App s1 s2) (App (App EForce t1) t2) m2
  | tr_appf M b b' s2 t2 m1 m2 :
      trm (Some m1 .: Some (MdB m1 m2) .: M) b b' m2 → trm M s2 t2 m1 →
      trm M (App (EBox (Lam b)) s2) (App (forced b') t2) m2
  | tr_letu M s1 s2 t1 t2 m :
      trm M s1 t1 MdD → trm M s2 t2 m →
      trm M (LetU s1 s2) (LetU (App EForce t1) t2) m
  | tr_new M e e' m :
      trm (Some MdD .: Some MdD .: M) e e' m →
      trm M (LetP (App ENew EUnit) e) (let_new_pair e') m
  | tr_letp M s1 s2 t1 t2 e e' m :
      trm M s1 t1 MdD → trm M s2 t2 MdD → trm (Some MdD .: Some MdD .: M) e e' m →
      trm M (LetP (Pair s1 s2) e) (LetP (Pair t1 t2) e') m
  | tr_recv M s t e e' m :
      trm M s t MdD → trm (Some MdD .: Some MdD .: M) e e' m →
      trm M (LetP (App ERecv s) e) (LetP (App ERecv t) e') m
  | tr_send M s1 s2 t1 t2 :
      trm M s1 t1 MdD → trm M s2 t2 MdD →
      trm M (App ESend (Pair s1 s2)) (App ESend (Pair t1 t2)) MdD
  | tr_close M s t :
      trm M s t MdD → trm M (App EClos s) (LetU (App EClos t) unitv) MdD
  | tr_sel M s t (b : bool) :
      trm M s t MdD →
      trm M (App (if b then ESel2 else ESel1) s) (App (if b then ESel2 else ESel1) t) MdD
  | tr_match M s t e1 e1' e2 e2' m :
      trm M s t MdD → trm (Some MdD .: M) e1 e1' m → trm (Some MdD .: M) e2 e2' m →
      trm M (Case (App EBra s) e1 e2) (Case (App EBra t) e1' e2') m
  | tr_fork M s t :
      trm M s t (MdF MdD MdD) → trm M (App ESpawn s) (App fork_tr t) MdD.

(** ** Renaming and substitution *)

Lemma rn_S r t : rename (upren r) (rename S t) = rename S (rename r t).
Proof. rewrite !rename_rename. by apply rename_ext. Qed.

Lemma sb_S σ t : subst (up σ) (rename S t) = rename S (subst σ t).
Proof. rewrite subst_rename, rename_subst. by apply subst_ext. Qed.

Lemma rename_as_subst r e : rename r e = subst (λ x, Var (r x)) e.
Proof.
  revert r. induction e; intros r; simpl; f_equal; auto.
  all: try (rewrite IHe; apply subst_ext; by intros [|x]).
  - rewrite IHe2. apply subst_ext. by intros [|[|x]].
  - rewrite IHe2. apply subst_ext. by intros [|x].
  - rewrite IHe3. apply subst_ext. by intros [|x].
Qed.

Lemma rn_forced r b :
  rename (upren r) (subst (up (EBox (Lam b) .: Var)) b) =
  subst (up (EBox (Lam (rename (upren (upren r)) b)) .: Var)) (rename (upren (upren r)) b).
Proof.
  rewrite rename_subst, subst_rename. apply subst_ext. intros [|[|x]]; simpl; [done| |done].
  change (rename (upren r) (rename S (EBox (Lam b))) = rename S (rename r (EBox (Lam b)))).
  by rewrite rn_S.
Qed.

Lemma sb_forced σ b :
  subst (up σ) (subst (up (EBox (Lam b) .: Var)) b) =
  subst (up (EBox (Lam (subst (up (up σ)) b)) .: Var)) (subst (up (up σ)) b).
Proof.
  rewrite !subst_subst. apply subst_ext. intros [|[|y]]; [done| |].
  - change (subst (up σ) (rename S (EBox (Lam b))) = rename S (subst σ (EBox (Lam b)))).
    by rewrite sb_S.
  - transitivity (rename S (σ y)); [done|].
    change (up (up σ) (S (S y))) with (rename S (rename S (σ y))).
    rewrite !subst_rename, rename_as_subst. by apply subst_ext.
Qed.

Lemma subst_unitv σ : subst σ unitv = unitv.
Proof. done. Qed.
Lemma subst_fork σ : subst σ fork_tr = fork_tr.
Proof. done. Qed.

Lemma trm_rename M s t m :
  trm M s t m → ∀ M' r, (∀ x mx, M x = Some mx → M' (r x) = Some mx) →
  trm M' (rename r s) (rename r t) m.
Proof.
  assert (∀ (M M' : nat → option md) r m1,
    (∀ x mx, M x = Some mx → M' (r x) = Some mx) →
    ∀ x mx, (Some m1 .: M) x = Some mx → (Some m1 .: M') (upren r x) = Some mx) as Hup.
  { intros M0 M0' r m1 Hr [|x] mx; simpl; auto. }
  induction 1; intros M' r Hr; simpl.
  - apply tr_var. auto.
  - apply tr_unit.
  - apply tr_chan.
  - apply tr_lam. eauto.
  - apply tr_fix. eauto.
  - eapply tr_app; eauto.
  - eapply tr_appb; eauto.
  - rewrite rn_forced. eapply tr_appf; eauto.
  - eapply tr_letu; eauto.
  - change (trm M' (rename r (LetP (App ENew EUnit) e)) (rename r (let_new_pair e')) m).
    rewrite rename_let_new_pair. eapply tr_new. eauto.
  - eapply tr_letp; eauto.
  - eapply tr_recv; eauto.
  - eapply tr_send; eauto.
  - eapply tr_close; eauto.
  - destruct b; [apply (tr_sel _ _ _ true)|apply (tr_sel _ _ _ false)]; eauto.
  - eapply tr_match; eauto.
  - change (trm M' (App ESpawn (rename r s)) (App fork_tr (rename r t)) MdD). eapply tr_fork; eauto.
Qed.

Lemma trm_subst M s t m :
  trm M s t m → ∀ M' σ σ',
  (∀ x mx, M x = Some mx → trm M' (σ x) (σ' x) mx) →
  trm M' (subst σ s) (subst σ' t) m.
Proof.
  assert (∀ M M' σ σ' m1,
    (∀ x mx, M x = Some mx → trm M' (σ x) (σ' x) mx) →
    ∀ x mx, (Some m1 .: M) x = Some mx → trm (Some m1 .: M') (up σ x) (up σ' x) mx) as Hup.
  { intros M0 M0' σ σ' m1 Hσ [|x] mx; simpl.
    - intros [= <-]. by constructor.
    - intros Hx. unfold compose. eapply trm_rename; [by apply Hσ|]. done. }
  induction 1; intros M' σ σ' Hσ; simpl.
  - auto.
  - apply tr_unit.
  - apply tr_chan.
  - apply tr_lam. eauto.
  - apply tr_fix. eauto 10.
  - eapply tr_app; eauto.
  - eapply tr_appb; eauto.
  - rewrite sb_forced. eapply tr_appf; eauto 10.
  - eapply tr_letu; eauto.
  - change (trm M' (subst σ (LetP (App ENew EUnit) e)) (subst σ' (let_new_pair e')) m).
    rewrite subst_let_new_pair. eapply tr_new. eauto 10.
  - eapply tr_letp; eauto 10.
  - eapply tr_recv; eauto 10.
  - eapply tr_send; eauto.
  - eapply tr_close; eauto.
  - destruct b; [apply (tr_sel _ _ _ true)|apply (tr_sel _ _ _ false)]; eauto.
  - eapply tr_match; eauto.
  - change (trm M' (App ESpawn (subst σ s)) (App fork_tr (subst σ' t)) MdD). eapply tr_fork; eauto.
Qed.

Lemma trm_mono M s t m :
  trm M s t m → ∀ M', (∀ x mx, M x = Some mx → M' x = Some mx) → trm M' s t m.
Proof.
  intros H M' HM. rewrite <-(rename_id s), <-(rename_id t).
  eapply trm_rename; [done|]. done.
Qed.

Lemma trm_fchans M s t m : trm M s t m → fchans t ⊆ fchans s.
Proof.
  induction 1; simpl; try set_solver.
  - assert (fchans (subst (up (EBox (Lam b') .: Var)) b') ⊆ fchans b' ∪ fchans b') as H1.
    { apply fchans_subst. apply allfv_forall. intros [|[|x]]; simpl; [set_solver| |set_solver].
      unfold compose. rewrite fchans_rename. simpl. set_solver. }
    set_solver.
  - rewrite fchans_rename. set_solver.
Qed.

(** ** Every translation is related *)

Definition mdenv (Γ : menv) : nat → option md :=
  λ x, match Γ !! x with Some (Some t) => Some (mode_of t) | _ => None end.

Lemma msplit_l Γ Γ1 Γ2 x t :
  msplit Γ Γ1 Γ2 → Γ1 !! x = Some (Some t) → Γ !! x = Some (Some t).
Proof. intros Hs. revert x. induction Hs; intros [|x]; simpl; auto; done. Qed.

Lemma msplit_r Γ Γ1 Γ2 x t :
  msplit Γ Γ1 Γ2 → Γ2 !! x = Some (Some t) → Γ !! x = Some (Some t).
Proof. intros Hs. revert x. induction Hs; intros [|x]; simpl; auto; done. Qed.

Lemma mdenv_l Γ Γ1 Γ2 x mx : msplit Γ Γ1 Γ2 → mdenv Γ1 x = Some mx → mdenv Γ x = Some mx.
Proof.
  unfold mdenv. intros Hs. destruct (Γ1 !! x) as [[t|]|] eqn:E; try done.
  by rewrite (msplit_l _ _ _ _ _ Hs E).
Qed.

Lemma mdenv_r Γ Γ1 Γ2 x mx : msplit Γ Γ1 Γ2 → mdenv Γ2 x = Some mx → mdenv Γ x = Some mx.
Proof.
  unfold mdenv. intros Hs. destruct (Γ2 !! x) as [[t|]|] eqn:E; try done.
  by rewrite (msplit_r _ _ _ _ _ Hs E).
Qed.

Lemma mdenv_cons1 t Γ x mx :
  mdenv (Some t :: Γ) x = Some mx → (Some (mode_of t) .: mdenv Γ) x = Some mx.
Proof. by destruct x. Qed.

Lemma mdenv_cons2 t1 t2 Γ x mx :
  mdenv (Some t1 :: Some t2 :: Γ) x = Some mx →
  (Some (mode_of t1) .: Some (mode_of t2) .: mdenv Γ) x = Some mx.
Proof. by destruct x as [|[|x]]. Qed.

Lemma mdenv_open Γ i pol Q Q' p x mx :
  Γ !! i = Some (Some (MEx pol Q)) →
  mdenv (<[i := Some (MCh pol Q' p)]> Γ) x = Some mx → mdenv Γ x = Some mx.
Proof.
  unfold mdenv, menv in *. intros Hi. rewrite list_lookup_insert. case_decide as Hd.
  - destruct Hd as [-> _]. rewrite Hi. done.
  - destruct (decide (i = x)) as [->|]; [|done]. exfalso. apply Hd. split; [done|]. by eapply lookup_lt_Some.
Qed.

Ltac mono_split := intros ? ?; first [by eapply mdenv_l | by eapply mdenv_r].

Lemma trm_of_typed Θ Γ e T ef e' :
  mtyped Θ Γ e T ef e' → trm (mdenv Γ) e e' (mode_of T).
Proof.
  induction 1; simpl.
  - apply tr_var. unfold mdenv. by destruct H as [-> _].
  - apply tr_unit.
  - apply tr_lam. eapply trm_mono; [exact IHmtyped|]. intros ? ? Hx; exact (mdenv_cons1 _ _ _ _ Hx).
  - eapply tr_app.
    + eapply trm_mono; [exact IHmtyped1|]. mono_split.
    + eapply trm_mono; [exact IHmtyped2|]. mono_split.
  - rewrite mode_msub. eapply tr_appb.
    + eapply trm_mono; [exact IHmtyped1|]. mono_split.
    + rewrite mode_msub in IHmtyped2. eapply trm_mono; [exact IHmtyped2|]. mono_split.
  - apply tr_fix. eapply trm_mono; [exact IHmtyped|]. intros ? ? Hx; exact (mdenv_cons2 _ _ _ _ _ Hx).
  - apply tr_fix. eapply trm_mono; [exact IHmtyped|]. intros ? ? Hx; exact (mdenv_cons2 _ _ _ _ _ Hx).
  - eapply tr_appb.
    + eapply trm_mono; [exact IHmtyped1|]. mono_split.
    + eapply trm_mono; [exact IHmtyped2|]. mono_split.
  - eapply trm_mono; [exact IHmtyped|]. intros. by eapply mdenv_open.
  - exact IHmtyped.
  - eapply tr_app.
    + apply tr_lam. eapply trm_mono; [exact IHmtyped2|]. intros x mx Hx.
      destruct x as [|x]; [exact Hx|]. simpl. by eapply mdenv_r.
    + eapply trm_mono; [exact IHmtyped1|]. mono_split.
  - eapply tr_letu.
    + eapply trm_mono; [exact IHmtyped1|]. mono_split.
    + eapply trm_mono; [exact IHmtyped2|]. mono_split.
  - apply tr_new. eapply trm_mono; [exact IHmtyped|]. intros ? ? Hx; exact (mdenv_cons2 _ _ _ _ _ Hx).
  - apply tr_new. eapply trm_mono; [exact IHmtyped|]. intros ? ? Hx; exact (mdenv_cons2 _ _ _ _ _ Hx).
  - apply tr_new. eapply trm_mono; [exact IHmtyped|]. intros ? ? Hx; exact (mdenv_cons2 _ _ _ _ _ Hx).
  - eapply tr_send.
    + rewrite mode_payty in IHmtyped1. eapply trm_mono; [exact IHmtyped1|]. mono_split.
    + eapply trm_mono; [exact IHmtyped2|]. mono_split.
  - eapply tr_recv.
    + eapply trm_mono; [exact IHmtyped1|]. mono_split.
    + eapply trm_mono; [exact IHmtyped2|]. intros x mx Hx.
      apply mdenv_cons2 in Hx. rewrite mode_rpayty in Hx. destruct x as [|[|x]]; [exact Hx|exact Hx|].
      simpl in *. by eapply mdenv_r.
  - by apply tr_close.
  - by apply tr_sel.
  - eapply tr_match.
    + eapply trm_mono; [exact IHmtyped1|]. mono_split.
    + eapply trm_mono; [exact IHmtyped2|]. intros [|x] mx Hx; [exact Hx|]. simpl in *. by eapply mdenv_r.
    + eapply trm_mono; [exact IHmtyped3|]. intros [|x] mx Hx; [exact Hx|]. simpl in *. by eapply mdenv_r.
  - by apply tr_fork.
  - exact IHmtyped.
  - exact IHmtyped.
Qed.

(** ** Values and canonical forms *)

Definition M0 : nat → option md := λ _, None.

Lemma trm_M0 M s t m : trm M s t m → (∀ x, M x = None) → trm M0 s t m.
Proof. intros H HM. eapply trm_mono; [exact H|]. intros x mx Hx. by rewrite HM in Hx. Qed.

Lemma trm_val M s t m : trm M s t m → (∀ x, M x = None) → is_val s → is_val t.
Proof. induction 1; intros HM Hv; simpl in *; try done. Qed.

Lemma trm_konst M k t m : trm M (Konst k) t m → False.
Proof. inversion 1. Qed.

Lemma trm_sel_konst M (b : bool) t m : trm M (if b then ESel2 else ESel1) t m → False.
Proof. destruct b; apply trm_konst. Qed.

Lemma canon_d M s t : trm M s t MdD → (∀ x, M x = None) → is_val s →
  (s = EUnit ∧ t = unitv) ∨ (∃ a, s = Chan a ∧ t = Chan a).
Proof.
  intros H HM Hv. inversion H; subst; simpl in Hv; try done; eauto.
Qed.

Lemma canon_f M s t m1 m2 : trm M s t (MdF m1 m2) → (∀ x, M x = None) → is_val s →
  ∃ b b', s = Lam b ∧ t = Lam b' ∧ trm (Some m1 .: M) b b' m2.
Proof.
  intros H HM Hv. inversion H; subst; simpl in Hv; try done; eauto.
Qed.

Lemma canon_b M s t m1 m2 : trm M s t (MdB m1 m2) → (∀ x, M x = None) → is_val s →
  ∃ b b', s = EBox (Lam b) ∧ t = EBox (Lam b') ∧ trm (Some m1 .: Some (MdB m1 m2) .: M) b b' m2.
Proof.
  intros H HM Hv. inversion H; subst; simpl in Hv; try done; eauto.
Qed.

Lemma trm_box_f M e t m1 m2 : trm M (EBox e) t (MdF m1 m2) → False.
Proof. inversion 1. Qed.

Lemma trm_lam_b M e t m1 m2 : trm M (Lam e) t (MdB m1 m2) → False.
Proof. inversion 1. Qed.

(** ** Inversion of source steps *)

Lemma sinv_app s1 s2 α s' :
  src_step (App s1 s2) α s' →
  src_head (App s1 s2) α s' ∨ (∃ s1', src_step s1 α s1' ∧ s' = App s1' s2) ∨
  (is_val s1 ∧ ∃ s2', src_step s2 α s2' ∧ s' = App s1 s2').
Proof. inversion 1; subst; eauto 10. Qed.

Lemma sinv_pair s1 s2 α s' :
  src_step (Pair s1 s2) α s' →
  (∃ s1', src_step s1 α s1' ∧ s' = Pair s1' s2) ∨ (is_val s1 ∧ ∃ s2', src_step s2 α s2' ∧ s' = Pair s1 s2').
Proof. inversion 1 as [? ? ? Hh| | | | | | |]; subst; eauto 10. inversion Hh. Qed.

Lemma sinv_letu s1 s2 α s' :
  src_step (LetU s1 s2) α s' → src_head (LetU s1 s2) α s' ∨ ∃ s1', src_step s1 α s1' ∧ s' = LetU s1' s2.
Proof. inversion 1; subst; eauto. Qed.

Lemma sinv_letp s1 s2 α s' :
  src_step (LetP s1 s2) α s' → src_head (LetP s1 s2) α s' ∨ ∃ s1', src_step s1 α s1' ∧ s' = LetP s1' s2.
Proof. inversion 1; subst; eauto. Qed.

Lemma sinv_case s e1 e2 α s' :
  src_step (Case s e1 e2) α s' → src_head (Case s e1 e2) α s' ∨ ∃ s0, src_step s α s0 ∧ s' = Case s0 e1 e2.
Proof. inversion 1; subst; eauto. Qed.

Lemma sinv_konst k α s' : src_step (Konst k) α s' → False.
Proof. intros H. exact (src_val_no_step (Konst k) α s' I H). Qed.

Lemma sinv_sel (b : bool) α s' : src_step (if b then ESel2 else ESel1) α s' → False.
Proof. destruct b; apply sinv_konst. Qed.

(** ** Target terms that offer nothing *)

Lemma act_app_l e1 e2 : is_val e1 = false → act (App e1 e2) = act e1.
Proof. intros H. simpl. by rewrite H. Qed.
Lemma act_app_r e1 e2 : is_val e1 → is_val e2 = false → act (App e1 e2) = act e2.
Proof. intros H1 H2. simpl. by rewrite (is_val_true _ H1), H2. Qed.
Lemma act_pair_l e1 e2 : is_val e1 = false → act (Pair e1 e2) = act e1.
Proof. intros H. simpl. by rewrite H. Qed.
Lemma act_pair_r e1 e2 : is_val e1 → act (Pair e1 e2) = act e2.
Proof. intros H. simpl. by rewrite (is_val_true _ H). Qed.
Lemma act_letu e1 e2 : is_val e1 = false → act (LetU e1 e2) = act e1.
Proof. intros H. simpl. by rewrite H. Qed.
Lemma act_letp e1 e2 : is_val e1 = false → act (LetP e1 e2) = act e1.
Proof. intros H. simpl. by rewrite H. Qed.
Lemma act_case e e1 e2 : is_val e = false → act (Case e e1 e2) = act e.
Proof. intros H. simpl. by rewrite H. Qed.

Lemma not_val e : ¬ is_val e → is_val e = false.
Proof. by destruct (is_val e). Qed.

Abbreviation bstar := (rtc (λ x y, tstep x LBeta y)).

Definition ectx2 (K : expr → expr) : Prop := ∀ e α e', tstep e α e' → tstep (K e) α (K e').

Lemma bstar_ectx K e e' : ectx2 K → bstar e e' → bstar (K e) (K e').
Proof. intros HK. apply rtc_congruence. intros. by apply HK. Qed.

Lemma ectx_appl e2 : ectx2 (λ x, App x e2).
Proof. intros ???. apply TStepAppL. Qed.
Lemma ectx_appr v : is_val v → ectx2 (λ x, App v x).
Proof. intros ????. by apply TStepAppR. Qed.
Lemma ectx_pairl e2 : ectx2 (λ x, Pair x e2).
Proof. intros ???. apply TStepPairL. Qed.
Lemma ectx_pairr v : is_val v → ectx2 (λ x, Pair v x).
Proof. intros ????. by apply TStepPairR. Qed.
Lemma ectx_letu e2 : ectx2 (λ x, LetU x e2).
Proof. intros ???. apply TStepLetU. Qed.
Lemma ectx_letp e2 : ectx2 (λ x, LetP x e2).
Proof. intros ???. apply TStepLetP. Qed.
Lemma ectx_case e1 e2 : ectx2 (λ x, Case x e1 e2).
Proof. intros ???. apply TStepCase. Qed.
Lemma ectx_comp K1 K2 : ectx2 K1 → ectx2 K2 → ectx2 (λ x, K1 (K2 x)).
Proof. intros H1 H2 ???. auto. Qed.
Lemma ectx_id : ectx2 (λ x, x).
Proof. by intros ???. Qed.

Ltac ectac := repeat first
  [ apply ectx_id | apply ectx_appl | (apply ectx_appr; done) | apply ectx_pairl
  | (apply ectx_pairr; done) | apply ectx_letu | apply ectx_letp | apply ectx_case
  | (apply (ectx_comp (λ x, App x _)); [apply ectx_appl|])
  | (apply (ectx_comp (λ x, App _ x)); [apply ectx_appr; done|])
  | (apply (ectx_comp (λ x, Pair x _)); [apply ectx_pairl|])
  | (apply (ectx_comp (λ x, Pair _ x)); [apply ectx_pairr; done|])
  | (apply (ectx_comp (λ x, LetU x _)); [apply ectx_letu|])
  | (apply (ectx_comp (λ x, LetP x _)); [apply ectx_letp|])
  | (apply (ectx_comp (λ x, Case x _ _)); [apply ectx_case|]) ].

Lemma force_step b : tstep (App EForce (EBox (Lam b))) LBeta (forced b).
Proof. apply TStepHead. exact (HeadForce (Lam b)). Qed.

(** A source thread is a value, steps, or is stuck, and then its target
    reaches a term that offers nothing. *)
Lemma tri M s t m : trm M s t m → (∀ x, M x = None) →
  is_val s ∨ (∃ α s', src_step s α s') ∨ (∃ t', bstar t t' ∧ act t' = None ∧ is_val t' = false).
Proof.
  intros H HM. induction H as [M x m Hx|M|M a|M b b' m1 m2 Hb IH|M b b' m1 m2 Hb IH
    |M s1 s2 t1 t2 m1 m2 H1 IH1 H2 IH2|M s1 s2 t1 t2 m1 m2 H1 IH1 H2 IH2|M b b' s2 t2 m1 m2 Hb IHb H2 IH2
    |M s1 s2 t1 t2 m H1 IH1 H2 IH2|M e e' m He IH|M s1 s2 t1 t2 e e' m H1 IH1 H2 IH2 He IH
    |M s t e e' m H IH He IHe|M s1 s2 t1 t2 H1 IH1 H2 IH2|M s t H IH|M s t b H IH
    |M s t e1 e1' e2 e2' m H IH H1 IH1 H2 IH2|M s t H IH]; simpl; auto.
  - by rewrite HM in Hx.
  - (* application *)
    destruct (IH1 HM) as [Hv1|[(α & s' & Hs)|(t' & Hs & Ha & Hv)]].
    + destruct (IH2 HM) as [Hv2|[(α & s' & Hs)|(t' & Hs & Ha & Hv)]].
      * destruct (canon_f _ _ _ _ _ H1 HM Hv1) as (b & b' & -> & -> & _).
        right; left. eexists _, _. by apply SSHead, SHApp.
      * right; left. eexists _, _. by apply SSAppR.
      * right; right. exists (App t1 t'). split_and!; [apply (bstar_ectx (λ x, App t1 x)); [|done]|..].
        { apply ectx_appr. by apply (trm_val _ _ _ _ H1 HM). }
        { rewrite (act_app_r t1 t'); [done|by apply (trm_val _ _ _ _ H1 HM)|done]. }
        { done. }
    + right; left. eexists _, _. by apply SSAppL.
    + right; right. exists (App t' t2). split_and!; [by apply (bstar_ectx (λ x, App x t2)); [apply ectx_appl|]|by rewrite act_app_l|done].
  - (* application of a box *)
    destruct (IH1 HM) as [Hv1|[(α & s' & Hs)|(t' & Hs & Ha & Hv)]].
    + destruct (canon_b _ _ _ _ _ H1 HM Hv1) as (b & b' & -> & -> & _).
      destruct (IH2 HM) as [Hv2|[(α & s' & Hs)|(t' & Hs & Ha & Hv)]].
      * right; left. eexists _, _. by apply SSHead, SHFix.
      * right; left. eexists _, _. by apply SSAppR.
      * right; right. exists (App (forced b') t'). split_and!.
        { eapply rtc_l; [apply TStepAppL, force_step|]. by apply (bstar_ectx (λ x, App (forced b') x)); [apply ectx_appr|]. }
        { by rewrite act_app_r. }
        { done. }
    + right; left. eexists _, _. by apply SSAppL.
    + right; right. exists (App (App EForce t') t2). split_and!.
      * apply (bstar_ectx (λ x, App (App EForce x) t2)); [|done]. ectac.
      * rewrite act_app_l by done. by rewrite act_app_r.
      * done.
  - (* the forced box *)
    destruct (IH2 HM) as [Hv2|[(α & s' & Hs)|(t' & Hs & Ha & Hv)]].
    + right; left. eexists _, _. by apply SSHead, SHFix.
    + right; left. eexists _, _. by apply SSAppR.
    + right; right. exists (App (forced b') t'). split_and!.
      * by apply (bstar_ectx (λ x, App (forced b') x)); [apply ectx_appr|].
      * by rewrite act_app_r.
      * done.
  - (* e₁; e₂ *)
    destruct (IH1 HM) as [Hv1|[(α & s' & Hs)|(t' & Hs & Ha & Hv)]].
    + destruct (canon_d _ _ _ H1 HM Hv1) as [[-> ->]|(a & -> & ->)].
      * right; left. eexists _, _. by apply SSHead, SHLetU.
      * right; right. exists (LetU (App EForce (Chan a)) t2). split_and!; [apply rtc_refl|done|done].
    + right; left. eexists _, _. by apply SSLetU.
    + right; right. exists (LetU (App EForce t') t2). split_and!.
      * apply (bstar_ectx (λ x, LetU (App EForce x) t2)); [|done]. ectac.
      * rewrite act_letu by done. by rewrite act_app_r.
      * done.
  - (* new *)
    right; left. eexists _, _. apply SSLetP, SSHead, (SHNew inhabitant).
  - (* let (x, y) = (u, v) *)
    destruct (IH1 HM) as [Hv1|[(α & s' & Hs)|(t' & Hs & Ha & Hv)]].
    + destruct (IH2 HM) as [Hv2|[(α & s' & Hs)|(t' & Hs & Ha & Hv)]].
      * right; left. eexists _, _. by apply SSHead, SHLetP.
      * right; left. eexists _, _. by apply SSLetP, SSPairR.
      * right; right. exists (LetP (Pair t1 t') e'). pose proof (trm_val _ _ _ _ H1 HM Hv1) as Hw1. split_and!.
        { apply (bstar_ectx (λ x, LetP (Pair t1 x) e')); [|done]. ectac. }
        { rewrite act_letp by (simpl; rewrite Hv; by destruct (is_val t1)). by rewrite act_pair_r. }
        { done. }
    + right; left. eexists _, _. by apply SSLetP, SSPairL.
    + right; right. exists (LetP (Pair t' t2) e'). split_and!.
      * apply (bstar_ectx (λ x, LetP (Pair x t2) e')); [|done]. ectac.
      * rewrite act_letp by (simpl; by rewrite Hv). by rewrite act_pair_l.
      * done.
  - (* receive *)
    destruct (IH HM) as [Hv1|[(α & s' & Hs)|(t' & Hs & Ha & Hv)]].
    + destruct (canon_d _ _ _ H HM Hv1) as [[-> ->]|(a & -> & ->)].
      * right; right. exists (LetP (App ERecv unitv) e'). split_and!; [apply rtc_refl|done|done].
      * right; left. eexists _, _. apply SSLetP, SSHead, (SHRecv a EUnit). done.
    + right; left. eexists _, _. by apply SSLetP, SSAppR.
    + right; right. exists (LetP (App ERecv t') e'). split_and!.
      * apply (bstar_ectx (λ x, LetP (App ERecv x) e')); [|done]. ectac.
      * rewrite act_letp by done. by rewrite act_app_r.
      * done.
  - (* send *)
    destruct (IH1 HM) as [Hv1|[(α & s' & Hs)|(t' & Hs & Ha & Hv)]].
    + pose proof (trm_val _ _ _ _ H1 HM Hv1) as Hw1.
      destruct (IH2 HM) as [Hv2|[(α & s' & Hs)|(t' & Hs & Ha & Hv)]].
      * destruct (canon_d _ _ _ H2 HM Hv2) as [[-> ->]|(a & -> & ->)].
        { right; right. exists (App ESend (Pair t1 unitv)). split_and!; [apply rtc_refl| |done].
          simpl. rewrite (is_val_true _ Hw1). simpl. by destruct t1. }
        { right; left. eexists _, _. by apply SSHead, SHSend. }
      * right; left. eexists _, _. by apply SSAppR, SSPairR.
      * right; right. exists (App ESend (Pair t1 t')). split_and!.
        { apply (bstar_ectx (λ x, App ESend (Pair t1 x))); [|done]. ectac. }
        { rewrite act_app_r; [|done|simpl; by rewrite (is_val_true _ Hw1), Hv]. by rewrite act_pair_r. }
        { done. }
    + right; left. eexists _, _. by apply SSAppR, SSPairL.
    + right; right. exists (App ESend (Pair t' t2)). split_and!.
      * apply (bstar_ectx (λ x, App ESend (Pair x t2))); [|done]. ectac.
      * rewrite act_app_r; [|done|simpl; by rewrite Hv]. by rewrite act_pair_l.
      * done.
  - (* close *)
    destruct (IH HM) as [Hv1|[(α & s' & Hs)|(t' & Hs & Ha & Hv)]].
    + destruct (canon_d _ _ _ H HM Hv1) as [[-> ->]|(a & -> & ->)].
      * right; right. exists (LetU (App EClos unitv) unitv). split_and!; [apply rtc_refl|done|done].
      * right; left. eexists _, _. by apply SSHead, SHClose.
    + right; left. eexists _, _. by apply SSAppR.
    + right; right. exists (LetU (App EClos t') unitv). split_and!.
      * apply (bstar_ectx (λ x, LetU (App EClos x) unitv)); [|done]. ectac.
      * rewrite act_letu by done. by rewrite act_app_r.
      * done.
  - (* select *)
    assert (is_val (if b then ESel2 else ESel1)) as Hk by (by destruct b).
    destruct (IH HM) as [Hv1|[(α & s' & Hs)|(t' & Hs & Ha & Hv)]].
    + destruct (canon_d _ _ _ H HM Hv1) as [[-> ->]|(a & -> & ->)].
      * right; right. exists (App (if b then ESel2 else ESel1) unitv). split_and!; [apply rtc_refl| |];
          by destruct b.
      * right; left. eexists _, _. by apply SSHead, SHSel.
    + right; left. eexists _, _. by apply SSAppR.
    + right; right. exists (App (if b then ESel2 else ESel1) t'). split_and!.
      * apply (bstar_ectx (λ x, App (if b then ESel2 else ESel1) x)); [|done]. ectac.
      * by rewrite act_app_r.
      * by destruct b.
  - (* match *)
    destruct (IH HM) as [Hv1|[(α & s' & Hs)|(t' & Hs & Ha & Hv)]].
    + destruct (canon_d _ _ _ H HM Hv1) as [[-> ->]|(a & -> & ->)].
      * right; right. exists (Case (App EBra unitv) e1' e2'). split_and!; [apply rtc_refl|done|done].
      * right; left. eexists _, _. apply SSHead, (SHBra a false).
    + right; left. eexists _, _. by apply SSCase, SSAppR.
    + right; right. exists (Case (App EBra t') e1' e2'). split_and!.
      * apply (bstar_ectx (λ x, Case (App EBra x) e1' e2')); [|done]. ectac.
      * rewrite act_case by done. by rewrite act_app_r.
      * done.
  - (* fork *)
    destruct (IH HM) as [Hv1|[(α & s' & Hs)|(t' & Hs & Ha & Hv)]].
    + right; left. eexists _, _. by apply SSHead, SHSpawn.
    + right; left. eexists _, _. by apply SSAppR.
    + right; right. exists (App fork_tr t'). split_and!.
      * by apply (bstar_ectx (λ x, App fork_tr x)); [apply ectx_appr|].
      * by rewrite act_app_r.
      * done.
Qed.

(** ** What a source step asks of the target *)

(** A spawned thread ◦⟨v ()⟩ against force (v′ (box ∗)). *)
Definition Rsp (s t : expr) : Prop := ∃ t0, t = App EForce t0 ∧ trm M0 s t0 MdD.

(** [post α t Q]: the target t performs the step that matches the
    source label α, with administrative β steps before and after, and
    ends in a state that satisfies Q. *)
Definition post (α : slab) (t : expr) (Q : expr → Prop) : Prop :=
  match α with
  | SBeta => ∃ t', bstar t t' ∧ Q t'
  | SNew a => ∃ t0 t1 t', bstar t t0 ∧ tstep t0 (LNew a) t1 ∧ bstar t1 t' ∧ Q t'
  | SSpawn v => ∃ t0 w t1 tn t', bstar t t0 ∧ tstep t0 (LSpawn w) t1 ∧
      bstar (App w EUnit) tn ∧ Rsp (App v EUnit) tn ∧ bstar t1 t' ∧ Q t'
  | SOut a v => ∃ t0 w t1, bstar t t0 ∧ tstep t0 (LSess (SSend a w)) t1 ∧ trm M0 v w MdD ∧ Q t1
  | SIn a v => ∃ t0, bstar t t0 ∧ ∀ w, is_val w → ∃ t1, tstep t0 (LSess (SRecv a w)) t1 ∧
      (trm M0 v w MdD → Q t1)
  | SSl a b => ∃ t0 t1, bstar t t0 ∧ tstep t0 (LSess (SSel a b)) t1 ∧ Q t1
  | SBr a b => ∃ t0 t1 t', bstar t t0 ∧ tstep t0 (LSess (SBra a b)) t1 ∧ bstar t1 t' ∧ Q t'
  | SCl a => ∃ t0 t1 t', bstar t t0 ∧ tstep t0 (LSess (SClos a)) t1 ∧ bstar t1 t' ∧ Q t'
  end.

Lemma post_ectx α t Q Q' K :
  ectx2 K → post α t Q → (∀ t', Q t' → Q' (K t')) → post α (K t) Q'.
Proof.
  intros HK Hp HQ. destruct α; simpl in *.
  - destruct Hp as (t' & Hs & Hq). exists (K t'). split; [by apply bstar_ectx|auto].
  - destruct Hp as (t0 & t1 & t' & Hs & Ht & Hs' & Hq). exists (K t0), (K t1), (K t').
    split_and!; [by apply bstar_ectx|by apply HK|by apply bstar_ectx|auto].
  - destruct Hp as (t0 & w & t1 & tn & t' & Hs & Ht & Hn & Hr & Hs' & Hq).
    exists (K t0), w, (K t1), tn, (K t'). split_and!; try done; try (by apply bstar_ectx); [by apply HK|auto].
  - destruct Hp as (t0 & w & t1 & Hs & Ht & Hr & Hq). exists (K t0), w, (K t1).
    split_and!; [by apply bstar_ectx|by apply HK|done|auto].
  - destruct Hp as (t0 & Hs & Hw). exists (K t0). split; [by apply bstar_ectx|].
    intros w Hv. destruct (Hw w Hv) as (t1 & H1 & Hk). exists (K t1). split; [by apply HK|auto].
  - destruct Hp as (t0 & t1 & Hs & Ht & Hq). exists (K t0), (K t1).
    split_and!; [by apply bstar_ectx|by apply HK|auto].
  - destruct Hp as (t0 & t1 & t' & Hs & Ht & Hs' & Hq). exists (K t0), (K t1), (K t').
    split_and!; [by apply bstar_ectx|by apply HK|by apply bstar_ectx|auto].
  - destruct Hp as (t0 & t1 & t' & Hs & Ht & Hs' & Hq). exists (K t0), (K t1), (K t').
    split_and!; [by apply bstar_ectx|by apply HK|by apply bstar_ectx|auto].
Qed.

Lemma post_pre α t t0 Q : bstar t t0 → post α t0 Q → post α t Q.
Proof.
  intros H0 Hp. destruct α; simpl in *.
  - destruct Hp as (t' & Hs & Hq). eexists. split; [by etrans|done].
  - destruct Hp as (t1 & t2 & t' & Hs & ?). eexists _, _, _. split; [by etrans|done].
  - destruct Hp as (t1 & w & t2 & tn & t' & Hs & ?). eexists _, _, _, _, _. split; [by etrans|done].
  - destruct Hp as (t1 & w & t2 & Hs & ?). eexists _, _, _. split; [by etrans|done].
  - destruct Hp as (t1 & Hs & Hw). eexists. split; [by etrans|done].
  - destruct Hp as (t1 & t2 & Hs & ?). eexists _, _. split; [by etrans|done].
  - destruct Hp as (t1 & t2 & t' & Hs & ?). eexists _, _, _. split; [by etrans|done].
  - destruct Hp as (t1 & t2 & t' & Hs & ?). eexists _, _, _. split; [by etrans|done].
Qed.

Lemma sub1_ok M v w m1 :
  trm M v w m1 → (∀ x, M x = None) →
  ∀ x mx, (Some m1 .: M) x = Some mx → trm M ((v .: Var) x) ((w .: Var) x) mx.
Proof. intros Hr HM [|x] mx; simpl; [by intros [= <-]|by rewrite HM]. Qed.

Lemma sub2_ok M u v u' v' m1 m2 :
  trm M u u' m1 → trm M v v' m2 → (∀ x, M x = None) →
  ∀ x mx, (Some m2 .: Some m1 .: M) x = Some mx → trm M ((v .: u .: Var) x) ((v' .: u' .: Var) x) mx.
Proof. intros H1 H2 HM [|[|x]] mx; simpl; [by intros [= <-]|by intros [= <-]|by rewrite HM]. Qed.

Lemma subst_scons_S Y e : subst (Y .: Var) (rename S e) = e.
Proof. rewrite subst_rename. apply subst_ids. Qed.

(** The thunk that fork_tr spawns, and its two β steps. *)
Definition fthunk (w : expr) : expr := Lam (LetU (Var 0) (App EForce (App (rename S w) unitv))).

Lemma fork_beta w :
  subst1 w (LetU (App ESpawn (Lam (LetU (Var 0) (App EForce (App (Var 1) unitv))))) unitv) =
  LetU (App ESpawn (fthunk w)) unitv.
Proof. reflexivity. Qed.

Lemma thunk_beta w :
  subst1 EUnit (LetU (Var 0) (App EForce (App (rename S w) unitv))) = LetU EUnit (App EForce (App w unitv)).
Proof. unfold subst1. simpl. by rewrite subst_scons_S. Qed.

Ltac selc := repeat match goal with
  | H : (if ?b then ESel2 else ESel1) = _ |- _ => destruct b; try discriminate H; clear H
  | H : _ = (if ?b then ESel2 else ESel1) |- _ => destruct b; try discriminate H; clear H
  end.

Ltac hdabs := try (exfalso; first [by eapply trm_konst | by eapply trm_sel_konst | by eapply trm_box_f
                                  | by eapply trm_lam_b]; fail).

(** ** Forward simulation of one thread *)

Lemma fwd M s t m :
  trm M s t m → (∀ x, M x = None) →
  ∀ α s', src_step s α s' → post α t (λ t', trm M s' t' m).
Proof.
  induction 1 as [M x m Hx|M|M a|M b b' m1 m2 Hb IH|M b b' m1 m2 Hb IH
    |M s1 s2 t1 t2 m1 m2 H1 IH1 H2 IH2|M s1 s2 t1 t2 m1 m2 H1 IH1 H2 IH2|M b b' s2 t2 m1 m2 Hb IHb H2 IH2
    |M s1 s2 t1 t2 m H1 IH1 H2 IH2|M e e' m He IH|M s1 s2 t1 t2 e e' m H1 IH1 H2 IH2 He IH
    |M s t e e' m H IH He IHe|M s1 s2 t1 t2 H1 IH1 H2 IH2|M s t H IH|M s t b H IH
    |M s t e1 e1' e2 e2' m H IH H1 IH1 H2 IH2|M s t H IH];
    intros HM α s' Hst.
  - by rewrite HM in Hx.
  - exfalso. eapply src_val_no_step; [|exact Hst]; done.
  - exfalso. eapply src_val_no_step; [|exact Hst]; done.
  - exfalso. eapply src_val_no_step; [|exact Hst]; done.
  - exfalso. eapply src_val_no_step; [|exact Hst]; done.
  - (* application *)
    apply sinv_app in Hst as [Hh|[(s1' & Hst1 & ->)|(Hv1 & s2' & Hst2 & ->)]].
    + inversion Hh; subst; selc; hdabs.
      destruct (canon_f _ _ _ _ _ H1 HM I) as (b0 & b' & [= ->] & -> & Hb).
      match goal with Hv : Is_true (is_val s2) |- _ => pose proof (trm_val _ _ _ _ H2 HM Hv) as Hw end.
      simpl. exists (subst1 t2 b'). split.
      * apply rtc_once. by apply TStepHead, HeadApp.
      * eapply trm_subst; [exact Hb|]. by apply sub1_ok.
    + eapply (post_ectx _ _ _ _ (λ x, App x t2)); [apply ectx_appl|by apply IH1|].
      intros t' Hq; cbv beta in Hq. by eapply tr_app.
    + destruct (canon_f _ _ _ _ _ H1 HM Hv1) as (b0 & b' & -> & -> & Hb).
      eapply (post_ectx _ _ _ _ (λ x, App (Lam b') x)); [by apply ectx_appr|by apply IH2|].
      intros t' Hq; cbv beta in Hq. eapply tr_app; [by apply tr_lam|exact Hq].
  - (* application of a box *)
    apply sinv_app in Hst as [Hh|[(s1' & Hst1 & ->)|(Hv1 & s2' & Hst2 & ->)]].
    + inversion Hh; subst; selc; hdabs.
      destruct (canon_b _ _ _ _ _ H1 HM I) as (b0 & b' & [= ->] & -> & Hb).
      match goal with Hv : Is_true (is_val s2) |- _ => pose proof (trm_val _ _ _ _ H2 HM Hv) as Hw end.
      simpl. exists (subst (t2 .: EBox (Lam b') .: Var) b'). split.
      * eapply rtc_l; [apply TStepAppL, force_step|]. apply rtc_once.
        replace (subst (t2 .: EBox (Lam b') .: Var) b') with (subst1 t2 (subst (up (EBox (Lam b') .: Var)) b'))
          by apply subst1_subst.
        by apply TStepHead, HeadApp.
      * eapply trm_subst; [exact Hb|]. apply sub2_ok; [by apply tr_fix|done|done].
    + eapply (post_ectx _ _ _ _ (λ x, App (App EForce x) t2)); [ectac|by apply IH1|].
      intros t' Hq; cbv beta in Hq. by eapply tr_appb.
    + destruct (canon_b _ _ _ _ _ H1 HM Hv1) as (b0 & b' & -> & -> & Hb).
      eapply post_pre; [apply rtc_once, TStepAppL, force_step|].
      eapply (post_ectx _ _ _ _ (λ x, App (forced b') x)); [by apply ectx_appr|by apply IH2|].
      intros t' Hq; cbv beta in Hq. by eapply tr_appf.
  - (* the forced box *)
    apply sinv_app in Hst as [Hh|[(s1' & Hst1 & ->)|(Hv1 & s2' & Hst2 & ->)]].
    + inversion Hh; subst; selc.
      match goal with Hv : Is_true (is_val s2) |- _ => pose proof (trm_val _ _ _ _ H2 HM Hv) as Hw end.
      simpl. exists (subst (t2 .: EBox (Lam b') .: Var) b'). split.
      * apply rtc_once.
        replace (subst (t2 .: EBox (Lam b') .: Var) b') with (subst1 t2 (subst (up (EBox (Lam b') .: Var)) b'))
          by apply subst1_subst.
        by apply TStepHead, HeadApp.
      * eapply trm_subst; [exact Hb|]. apply sub2_ok; [by apply tr_fix|done|done].
    + exfalso. eapply src_val_no_step; [|exact Hst1]; done.
    + eapply (post_ectx _ _ _ _ (λ x, App (forced b') x)); [by apply ectx_appr|by apply IH2|].
      intros t' Hq; cbv beta in Hq. by eapply tr_appf.
  - (* e₁; e₂ *)
    apply sinv_letu in Hst as [Hh|(s1' & Hst1 & ->)].
    + inversion Hh; subst. inversion H1; subst.
      simpl. exists t2. split; [|done].
      eapply rtc_l; [apply TStepLetU, TStepHead, (HeadForce EUnit)|]. apply rtc_once, TStepHead, HeadLetU.
    + eapply (post_ectx _ _ _ _ (λ x, LetU (App EForce x) t2)); [ectac|by apply IH1|].
      intros t' Hq; cbv beta in Hq. by eapply tr_letu.
  - (* new *)
    apply sinv_letp in Hst as [Hh|(p' & Hstp & ->)]; [inversion Hh|].
    apply sinv_app in Hstp as [Hh|[(? & Hk & _)|(_ & ? & Hk & _)]].
    + (* new ∗, then the two administrative β steps of [let_new_pair] *)
      inversion Hh; subst; selc. simpl. eexists _, _, _.
      split_and!; [apply rtc_refl|apply TStepLetP, TStepPairL, TStepHead, HeadNew| |].
      * eapply rtc_l; [apply TStepHead, HeadLetP; done|].
        apply rtc_once. apply TStepHead, HeadLetU.
      * unfold subst2. simpl. rewrite let_new_body.
        apply tr_letp; [apply tr_chan|apply tr_chan|exact He].
    + by apply sinv_konst in Hk.
    + exfalso. eapply src_val_no_step; [|exact Hk]; done.
  - (* let (x, y) = (u, v) *)
    apply sinv_letp in Hst as [Hh|(p' & Hstp & ->)].
    + inversion Hh; subst.
      match goal with Hu : Is_true (is_val s1), Hv : Is_true (is_val s2) |- _ =>
        pose proof (trm_val _ _ _ _ H1 HM Hu) as Hw1; pose proof (trm_val _ _ _ _ H2 HM Hv) as Hw2 end.
      simpl. exists (subst2 t1 t2 e'). split; [by apply rtc_once, TStepHead, HeadLetP|].
      eapply trm_subst; [exact He|]. by apply sub2_ok.
    + apply sinv_pair in Hstp as [(s1' & Hs1 & ->)|(Hv1 & s2' & Hs2 & ->)].
      * eapply (post_ectx _ _ _ _ (λ x, LetP (Pair x t2) e')); [ectac|by apply IH1|].
        intros t' Hq; cbv beta in Hq. by eapply tr_letp.
      * pose proof (trm_val _ _ _ _ H1 HM Hv1) as Hw1.
        eapply (post_ectx _ _ _ _ (λ x, LetP (Pair t1 x) e')); [ectac|by apply IH2|].
        intros t' Hq; cbv beta in Hq. by eapply tr_letp.
  - (* receive *)
    apply sinv_letp in Hst as [Hh|(p' & Hstp & ->)]; [inversion Hh|].
    apply sinv_app in Hstp as [Hh|[(? & Hk & _)|(_ & s0' & Hs0 & ->)]].
    + inversion Hh; subst; selc.
      destruct (canon_d _ _ _ H HM I) as [[[=] _]|(a' & [= <-] & ->)].
      simpl. exists (LetP (App ERecv (Chan a)) e'). split; [apply rtc_refl|].
      intros w Hw. exists (LetP (Pair w (Chan a)) e'). split; [by apply TStepLetP, TStepHead, HeadRecv|].
      intros Hr. apply tr_letp; [|apply tr_chan|exact He].
      eapply trm_mono; [exact Hr|]. intros ? ? Hx. discriminate Hx.
    + by apply sinv_konst in Hk.
    + eapply (post_ectx _ _ _ _ (λ x, LetP (App ERecv x) e')); [ectac|by apply IH|].
      intros t' Hq; cbv beta in Hq. by eapply tr_recv.
  - (* send *)
    apply sinv_app in Hst as [Hh|[(? & Hk & _)|(_ & p' & Hp & ->)]].
    + inversion Hh; subst; selc.
      destruct (canon_d _ _ _ H2 HM I) as [[[=] _]|(a' & [= <-] & ->)].
      match goal with Hv : Is_true (is_val s1) |- _ => pose proof (trm_val _ _ _ _ H1 HM Hv) as Hw1 end.
      simpl. exists (App ESend (Pair t1 (Chan a))), t1, (Chan a).
      split_and!; [apply rtc_refl|by apply TStepHead, HeadSend|by eapply trm_M0|apply tr_chan].
    + by apply sinv_konst in Hk.
    + apply sinv_pair in Hp as [(s1' & Hs1 & ->)|(Hv1 & s2' & Hs2 & ->)].
      * eapply (post_ectx _ _ _ _ (λ x, App ESend (Pair x t2))); [ectac|by apply IH1|].
        intros t' Hq; cbv beta in Hq. by eapply tr_send.
      * pose proof (trm_val _ _ _ _ H1 HM Hv1) as Hw1.
        eapply (post_ectx _ _ _ _ (λ x, App ESend (Pair t1 x))); [ectac|by apply IH2|].
        intros t' Hq; cbv beta in Hq. by eapply tr_send.
  - (* close *)
    apply sinv_app in Hst as [Hh|[(? & Hk & _)|(_ & s0' & Hs0 & ->)]].
    + inversion Hh; subst; selc.
      destruct (canon_d _ _ _ H HM I) as [[[=] _]|(a' & [= <-] & ->)].
      simpl. exists (LetU (App EClos (Chan a)) unitv), (LetU EUnit unitv), unitv.
      split_and!; [apply rtc_refl|by apply TStepLetU, TStepHead, HeadClos
                  |apply rtc_once, TStepHead, HeadLetU|apply tr_unit].
    + by apply sinv_konst in Hk.
    + eapply (post_ectx _ _ _ _ (λ x, LetU (App EClos x) unitv)); [ectac|by apply IH|].
      intros t' Hq; cbv beta in Hq. by eapply tr_close.
  - (* select *)
    destruct b.
    + apply sinv_app in Hst as [Hh|[(? & Hk & _)|(_ & s0' & Hs0 & ->)]].
      * inversion Hh; subst; selc.
        destruct (canon_d _ _ _ H HM I) as [[[=] _]|(a' & [= <-] & ->)].
        simpl. exists (App ESel2 (Chan a)), (Chan a).
        split_and!; [apply rtc_refl|apply TStepHead, HeadSel2|apply tr_chan].
      * by apply sinv_konst in Hk.
      * eapply (post_ectx _ _ _ _ (λ x, App ESel2 x)); [by apply ectx_appr|by apply IH|].
        intros t' Hq; cbv beta in Hq. by apply (tr_sel _ _ _ true).
    + apply sinv_app in Hst as [Hh|[(? & Hk & _)|(_ & s0' & Hs0 & ->)]].
      * inversion Hh; subst; selc.
        destruct (canon_d _ _ _ H HM I) as [[[=] _]|(a' & [= <-] & ->)].
        simpl. exists (App ESel1 (Chan a)), (Chan a).
        split_and!; [apply rtc_refl|apply TStepHead, HeadSel1|apply tr_chan].
      * by apply sinv_konst in Hk.
      * eapply (post_ectx _ _ _ _ (λ x, App ESel1 x)); [by apply ectx_appr|by apply IH|].
        intros t' Hq; cbv beta in Hq. by apply (tr_sel _ _ _ false).
  - (* match *)
    apply sinv_case in Hst as [Hh|(s0 & Hs0 & ->)].
    + inversion Hh; subst.
      destruct (canon_d _ _ _ H HM I) as [[[=] _]|(a' & [= <-] & ->)].
      simpl. exists (Case (App EBra (Chan a)) e1' e2'), (Case (inj_of b (Chan a)) e1' e2'),
        (subst1 (Chan a) (if b then e2' else e1')).
      split_and!; [apply rtc_refl|by apply TStepCase, TStepHead, HeadBra|..].
      * apply rtc_once. destruct b; apply TStepHead; [apply HeadCase2|apply HeadCase1]; done.
      * destruct b; (eapply trm_subst; [eassumption|]); (apply sub1_ok; [apply tr_chan|done]).
    + apply sinv_app in Hs0 as [Hh|[(? & Hk & _)|(_ & s1' & Hs1 & ->)]].
      * inversion Hh; subst; selc.
      * by apply sinv_konst in Hk.
      * eapply (post_ectx _ _ _ _ (λ x, Case (App EBra x) e1' e2')); [ectac|by apply IH|].
        intros t' Hq; cbv beta in Hq. by eapply tr_match.
  - (* fork *)
    apply sinv_app in Hst as [Hh|[(? & Hk & _)|(_ & s0' & Hs0 & ->)]].
    + inversion Hh; subst; selc.
      match goal with Hv : Is_true (is_val s) |- _ => destruct (canon_f _ _ _ _ _ H HM Hv) as (b & b' & -> & -> & Hb) end.
      simpl. exists (LetU (App ESpawn (fthunk (Lam b'))) unitv), (fthunk (Lam b')), (LetU EUnit unitv),
        (App EForce (App (Lam b') unitv)), unitv. split_and!.
      * apply rtc_once. unfold fork_tr. rewrite <-fork_beta. by apply TStepHead, HeadApp.
      * by apply TStepLetU, TStepHead, HeadSpawn.
      * eapply rtc_l; [unfold fthunk; by apply TStepHead, HeadApp|]. rewrite thunk_beta.
        apply rtc_once, TStepHead, HeadLetU.
      * eexists. split; [done|]. eapply tr_app; [eapply trm_M0; [by apply tr_lam|done]|apply tr_unit].
      * apply rtc_once, TStepHead, HeadLetU.
      * apply tr_unit.
    + by apply sinv_konst in Hk.
    + eapply (post_ectx _ _ _ _ (λ x, App fork_tr x)); [by apply ectx_appr|by apply IH|].
      intros t' Hq; cbv beta in Hq. by eapply tr_fork.
Qed.

(** ** Threads and processes *)

(** A thread of the source against a thread of the target. The main
    thread is related at data, a spawned thread ◦⟨v ()⟩ by [Rsp]. *)
Definition Rt (s t : expr) : Prop := trm M0 s t MdD ∨ Rsp s t.

Lemma fwd_rt s t α s' : Rt s t → src_step s α s' → post α t (λ t', Rt s' t').
Proof.
  intros [H|(t0 & -> & H)] Hst.
  - eapply (post_ectx _ _ _ _ (λ x, x)); [apply ectx_id| |].
    + eapply fwd; [exact H|done|exact Hst].
    + intros t' Hq. by left.
  - eapply (post_ectx _ _ _ _ (λ x, App EForce x)); [by apply ectx_appr| |].
    + eapply fwd; [exact H|done|exact Hst].
    + intros t' Hq. right. by eexists.
Qed.

Lemma Rt_fchans s t : Rt s t → fchans t ⊆ fchans s.
Proof. intros [H|(t0 & -> & H)]; apply trm_fchans in H; simpl; set_solver. Qed.

(** Multisets of threads related one to one. *)
Inductive mrel (P : expr → expr → Prop) : gmultiset expr → gmultiset expr → Prop :=
  | mrel_nil : mrel P ∅ ∅
  | mrel_cons s t Es Et : P s t → mrel P Es Et → mrel P ({[+ s +]} ⊎ Es) ({[+ t +]} ⊎ Et).

Lemma mrel_flip P Es Et : mrel P Es Et → mrel (flip P) Et Es.
Proof. induction 1; by constructor. Qed.

Lemma mrel_extract P Es Et0 t :
  mrel P Es (Et0 ⊎ {[+ t +]}) → ∃ Es0 s, Es = Es0 ⊎ {[+ s +]} ∧ P s t ∧ mrel P Es0 Et0.
Proof.
  intros H. remember (Et0 ⊎ {[+ t +]}) as Et eqn:HEt. revert Et0 HEt.
  induction H as [|s1 t1 Es1 Et1 HP Hm IH]; intros Et0 HEt.
  - exfalso. multiset_solver.
  - destruct (decide (t1 = t)) as [->|Hne].
    + exists Es1, s1. split_and!; [multiset_solver|done|].
      assert (Et1 = Et0) as -> by multiset_solver. done.
    + assert (t ∈ Et1) as Ht by multiset_solver.
      destruct (gmultiset_split1 _ _ Ht) as [Et2 ->].
      destruct (IH Et2 eq_refl) as (Es2 & s & -> & HPs & Hm2).
      exists ({[+ s1 +]} ⊎ Es2), s. split_and!; [multiset_solver|done|].
      assert (Et0 = {[+ t1 +]} ⊎ Et2) as -> by multiset_solver. by constructor.
Qed.

Lemma mrel_extract_l P Es0 s Et :
  mrel P (Es0 ⊎ {[+ s +]}) Et → ∃ Et0 t, Et = Et0 ⊎ {[+ t +]} ∧ P s t ∧ mrel P Es0 Et0.
Proof.
  intros H. apply mrel_flip in H. destruct (mrel_extract _ _ _ _ H) as (Et0 & t & -> & Hp & Hm).
  exists Et0, t. split_and!; [done|done|]. apply mrel_flip in Hm.
  by induction Hm; constructor.
Qed.

Lemma mrel_snoc P s t Es Et : P s t → mrel P Es Et → mrel P (Es ⊎ {[+ s +]}) (Et ⊎ {[+ t +]}).
Proof. intros. rewrite (comm_L (⊎) Es), (comm_L (⊎) Et). by constructor. Qed.

Lemma mrel_elem_l P Es Et s : mrel P Es Et → s ∈ Es → ∃ t, t ∈ Et ∧ P s t.
Proof.
  induction 1 as [|s1 t1 Es Et HP Hm IH]; [multiset_solver|].
  rewrite gmultiset_elem_of_disj_union, gmultiset_elem_of_singleton.
  intros [->|Hs]; [exists t1; split; [multiset_solver|done]|].
  destruct (IH Hs) as (t & ? & ?). exists t. split; [multiset_solver|done].
Qed.

Lemma mrel_elem_r P Es Et t : mrel P Es Et → t ∈ Et → ∃ s, s ∈ Es ∧ P s t.
Proof.
  induction 1 as [|s1 t1 Es Et HP Hm IH]; [multiset_solver|].
  rewrite gmultiset_elem_of_disj_union, gmultiset_elem_of_singleton.
  intros [->|Ht]; [exists s1; split; [multiset_solver|done]|].
  destruct (IH Ht) as (s & ? & ?). exists s. split; [multiset_solver|done].
Qed.

Lemma mrel_echans P Es Et :
  (∀ s t, P s t → fchans t ⊆ fchans s) → mrel P Es Et → echans Et ⊆ echans Es.
Proof.
  intros HP Hm c. rewrite !elem_of_echans. intros (t & Ht & Hc).
  destruct (mrel_elem_r _ _ _ _ Hm Ht) as (s & Hs & Hst). exists s. split; [done|].
  by apply (HP _ _ Hst).
Qed.

Lemma bstar_fchans t t' : bstar t t' → fchans t' ⊆ fchans t.
Proof.
  induction 1 as [|x y z Hxy _ IH]; [done|]. apply tstep_fchans in Hxy. simpl in Hxy. set_solver.
Qed.

(** β steps of single threads. *)
Definition msb (E E' : gmultiset expr) : Prop :=
  ∃ E0 e e', tstep e LBeta e' ∧ E = E0 ⊎ {[+ e +]} ∧ E' = E0 ⊎ {[+ e' +]}.

Lemma msb_bstar E t t' : bstar t t' → rtc msb (E ⊎ {[+ t +]}) (E ⊎ {[+ t' +]}).
Proof.
  induction 1 as [|x y z Hxy _ IH]; [done|]. eapply rtc_l; [|exact IH]. by exists E, x, y.
Qed.

Lemma msb_frame F E E' : rtc msb E E' → rtc msb (F ⊎ E) (F ⊎ E').
Proof.
  induction 1 as [|x y z (E0 & e & e' & Hst & -> & ->) _ IH]; [done|].
  eapply rtc_l; [|exact IH]. exists (F ⊎ E0), e, e'. split_and!; [done|multiset_solver..].
Qed.

Lemma msb_pred C E E' : rtc msb E E' → pred_star (C, E) (C, E').
Proof.
  induction 1 as [|x y z (E0 & e & e' & Hst & -> & ->) _ IH]; [done|].
  eapply rtc_l; [|exact IH]. by apply PStepBeta.
Qed.

Lemma bstar_proc C E t t' : bstar t t' → pred_star (C, E ⊎ {[+ t +]}) (C, E ⊎ {[+ t' +]}).
Proof. intros. by apply msb_pred, msb_bstar. Qed.

Lemma bstar_proc2 C E F t t' :
  bstar t t' → pred_star (C, E ⊎ {[+ t +]} ⊎ F) (C, E ⊎ {[+ t' +]} ⊎ F).
Proof.
  intros H. assert (∀ x, E ⊎ {[+ x +]} ⊎ F = (E ⊎ F) ⊎ {[+ x +]}) as HE by (intros; multiset_solver).
  rewrite !HE. by apply bstar_proc.
Qed.

(** The process relation. Both sides restrict the same names. *)
Definition prel2 (p q : proc) : Prop := p.1 = q.1 ∧ mrel Rt p.2 q.2.

Lemma sim_step p p' q : src_pstep p p' → prel2 p q → ∃ q', pred_star q q' ∧ prel2 p' q'.
Proof.
  destruct p as [C Es], q as [Cq Et].
  intros Hs (HC & Hm). simpl in HC, Hm. subst Cq.
  inversion Hs as [C0 E e e' Hst|C0 E e a e' Hst HaC HaE Hae|C0 E e v e' Hst
                  |C0 E a v e e' f f' Hse Hsf|C0 E a b e e' f f' Hse Hsf|C0 E a e e' f f' Hse Hsf HaC]; subst.
  - destruct (mrel_extract_l _ _ _ _ Hm) as (Et0 & t & -> & HR & Hm0).
    destruct (fwd_rt _ _ _ _ HR Hst) as (t' & Hs' & Hq).
    exists (C, Et0 ⊎ {[+ t' +]}). split; [by apply bstar_proc|].
    split; [done|]. by apply mrel_snoc.
  - destruct (mrel_extract_l _ _ _ _ Hm) as (Et0 & t & -> & HR & Hm0).
    destruct (fwd_rt _ _ _ _ HR Hst) as (t0 & t1 & t' & Hs0 & Ht & Hs1 & Hq).
    exists (C ∪ {[a]}, Et0 ⊎ {[+ t' +]}). split.
    + eapply rtc_trans; [|by apply bstar_proc].
      eapply rtc_r; [by apply bstar_proc|]. apply PStepNew; [done|done| |].
      * pose proof (mrel_echans _ _ _ Rt_fchans Hm0). set_solver.
      * apply bstar_fchans in Hs0. apply Rt_fchans in HR. set_solver.
    + split; [done|]. by apply mrel_snoc.
  - destruct (mrel_extract_l _ _ _ _ Hm) as (Et0 & t & -> & HR & Hm0).
    destruct (fwd_rt _ _ _ _ HR Hst) as (t0 & w & t1 & tn & t' & Hs0 & Ht & Hn & Hr & Hs1 & Hq).
    exists (C, Et0 ⊎ {[+ t' +]} ⊎ {[+ tn +]}). split.
    + eapply rtc_trans; [by apply bstar_proc|].
      eapply rtc_l; [by apply PStepSpawn|].
      eapply rtc_trans; [by apply bstar_proc|]. by apply bstar_proc2.
    + split; [done|]. apply mrel_snoc; [by right|]. by apply mrel_snoc.
  - destruct (mrel_extract_l _ _ _ _ Hm) as (Et1 & tf & -> & HRf & Hm1).
    destruct (mrel_extract_l _ _ _ _ Hm1) as (Et0 & te & -> & HRe & Hm0).
    destruct (fwd_rt _ _ _ _ HRe Hse) as (t0 & w & t1 & Hs0 & H1 & Hrw & Hqe).
    destruct (fwd_rt _ _ _ _ HRf Hsf) as (u0 & Hu0 & Hw).
    destruct (Hw w (tstep_send_val _ _ _ _ H1)) as (u1 & Hu1 & Hk).
    exists (C, Et0 ⊎ {[+ t1 +]} ⊎ {[+ u1 +]}). split.
    + eapply rtc_trans; [by apply bstar_proc2|].
      eapply rtc_trans; [by apply bstar_proc|].
      apply rtc_once. by eapply PStepMsg.
    + split; [done|]. apply mrel_snoc; [by apply Hk|]. by apply mrel_snoc.
  - destruct (mrel_extract_l _ _ _ _ Hm) as (Et1 & tf & -> & HRf & Hm1).
    destruct (mrel_extract_l _ _ _ _ Hm1) as (Et0 & te & -> & HRe & Hm0).
    destruct (fwd_rt _ _ _ _ HRe Hse) as (t0 & t1 & Hs0 & H1 & Hqe).
    destruct (fwd_rt _ _ _ _ HRf Hsf) as (u0 & u1 & u' & Hu0 & Hu1 & Hu' & Hqf).
    exists (C, Et0 ⊎ {[+ t1 +]} ⊎ {[+ u' +]}). split.
    + eapply rtc_trans; [by apply bstar_proc2|].
      eapply rtc_trans; [by apply bstar_proc|].
      eapply rtc_l; [by eapply PStepChoice|]. by apply bstar_proc.
    + split; [done|]. apply mrel_snoc; [done|]. by apply mrel_snoc.
  - destruct (mrel_extract_l _ _ _ _ Hm) as (Et1 & tf & -> & HRf & Hm1).
    destruct (mrel_extract_l _ _ _ _ Hm1) as (Et0 & te & -> & HRe & Hm0).
    destruct (fwd_rt _ _ _ _ HRe Hse) as (t0 & t1 & t' & Hs0 & H1 & Hs1 & Hqe).
    destruct (fwd_rt _ _ _ _ HRf Hsf) as (u0 & u1 & u' & Hu0 & Hu1 & Hu' & Hqf).
    exists (C ∖ {[a]}, Et0 ⊎ {[+ t' +]} ⊎ {[+ u' +]}). split.
    + eapply rtc_trans; [by apply bstar_proc2|].
      eapply rtc_trans; [by apply bstar_proc|].
      eapply rtc_l; [by eapply PStepClose|].
      eapply rtc_trans; [by apply bstar_proc2|]. by apply bstar_proc.
    + split; [done|]. apply mrel_snoc; [done|]. by apply mrel_snoc.
Qed.

Lemma sim_star p p' q : rtc src_pstep p p' → prel2 p q → ∃ q', pred_star q q' ∧ prel2 p' q'.
Proof.
  intros H. revert q. induction H as [|p1 p2 p3 H12 _ IH]; intros q Hp; [by exists q|].
  destruct (sim_step _ _ _ H12 Hp) as (q2 & Hq2 & Hp2).
  destruct (IH _ Hp2) as (q3 & Hq3 & Hp3). exists q3. split; [by etrans|done].
Qed.

(** ** Administrative steps never block *)

(** A stuck source thread is a value, a pending action, or stuck for
    good, and administrative β steps bring its target to a value, to the
    matching pending action, or to a term that offers nothing. *)
Definition cls (s t : expr) : Prop :=
  (is_val s ∧ is_val t ∧ (t = EUnit → s = EUnit)) ∨
  (∃ a v s'' w, src_step s (SOut a v) s'' ∧ act t = Some (ASend a w)) ∨
  (∃ a v s'', src_step s (SIn a v) s'' ∧ act t = Some (ARecv a)) ∨
  (∃ a b s'', src_step s (SSl a b) s'' ∧ act t = Some (ASel a b)) ∨
  (∃ a b s'', src_step s (SBr a b) s'' ∧ act t = Some (ABra a)) ∨
  (∃ a s'', src_step s (SCl a) s'' ∧ act t = Some (AClos a)) ∨
  (act t = None ∧ is_val t = false).

Lemma act_val e : is_val e → act e = None.
Proof.
  induction e; simpl; intros Hv; try done; auto.
  apply andb_True in Hv as [H1 H2]. rewrite (is_val_true _ H1). auto.
Qed.

Lemma classify C E s t :
  src_irred (C, E ⊎ {[+ s +]}) → Rt s t → ∃ t', bstar t t' ∧ cls s t'.
Proof.
  intros Hirr HR.
  assert (∀ α s', src_step s α s' → ∃ t', bstar t t' ∧ cls s t') as Hstep.
  { intros α s' Hst. destruct α as [|a|v|a v|a v|a b|a b|a].
    - exfalso. eapply Hirr. by apply SPBeta.
    - set (b := fresh (C ∪ echans E ∪ fchans s)).
      assert (b ∉ C ∪ echans E ∪ fchans s) by apply is_fresh.
      destruct (src_step_new_any _ _ _ Hst b) as [s'' Hs''].
      exfalso. eapply Hirr. apply SPNew; [exact Hs''|set_solver..].
    - exfalso. eapply Hirr. by apply SPSpawn.
    - destruct (fwd_rt _ _ _ _ HR Hst) as (t0 & w & t1' & Hs0 & H1 & _).
      exists t0. split; [done|]. right; left.
      destruct (act_step _ _ _ H1) as (x & Hx & Ho). apply offers_send in Ho as ->. eauto 10.
    - destruct (fwd_rt _ _ _ _ HR Hst) as (u0 & Hs0 & Hw).
      destruct (Hw unitv I) as (u1 & Hu1 & _).
      exists u0. split; [done|]. do 2 right; left.
      destruct (act_step _ _ _ Hu1) as (x & Hx & Ho). apply offers_recv in Ho as ->. eauto 10.
    - destruct (fwd_rt _ _ _ _ HR Hst) as (t0 & t1' & Hs0 & H1 & _).
      exists t0. split; [done|]. do 3 right; left.
      destruct (act_step _ _ _ H1) as (x & Hx & Ho). apply offers_sel in Ho as ->. eauto 10.
    - destruct (fwd_rt _ _ _ _ HR Hst) as (t0 & t1' & t'' & Hs0 & H1 & _).
      exists t0. split; [done|]. do 4 right; left.
      destruct (act_step _ _ _ H1) as (x & Hx & Ho). apply offers_bra in Ho as ->. eauto 10.
    - destruct (fwd_rt _ _ _ _ HR Hst) as (t0 & t1' & t'' & Hs0 & H1 & _).
      exists t0. split; [done|]. do 5 right; left.
      destruct (act_step _ _ _ H1) as (x & Hx & Ho). apply offers_clos in Ho as ->. eauto 10. }
  destruct HR as [H|(t0 & -> & H)].
  - destruct (tri _ _ _ _ H (λ _, eq_refl)) as [Hv|[(α & s' & Hst)|(t' & Hs & Ha & Hv)]].
    + destruct (canon_d _ _ _ H (λ _, eq_refl) Hv) as [[-> ->]|(a & -> & ->)];
        (eexists; split; [apply rtc_refl|left; split_and!; [done|done|by intros [=]]]).
    + by apply (Hstep α s').
    + exists t'. split; [done|]. do 6 right. done.
  - destruct (tri _ _ _ _ H (λ _, eq_refl)) as [Hv|[(α & s' & Hst)|(t' & Hs & Ha & Hv)]].
    + destruct (canon_d _ _ _ H (λ _, eq_refl) Hv) as [[-> ->]|(a & -> & ->)].
      * exists EUnit. split; [apply rtc_once, TStepHead, (HeadForce EUnit)|left; done].
      * exists (App EForce (Chan a)). split; [apply rtc_refl|]. do 6 right. done.
    + by apply (Hstep α s').
    + exists (App EForce t'). split; [by apply (bstar_ectx (λ x, App EForce x)); [apply ectx_appr|]|].
      do 6 right. split; [by rewrite act_app_r|done].
Qed.

Lemma cls_step s t α t' :
  cls s t → tstep t α t' →
  (∃ a v s'' w, src_step s (SOut a v) s'' ∧ α = LSess (SSend a w)) ∨
  (∃ a v s'' w, src_step s (SIn a v) s'' ∧ α = LSess (SRecv a w)) ∨
  (∃ a b s'', src_step s (SSl a b) s'' ∧ α = LSess (SSel a b)) ∨
  (∃ a b s'' b', src_step s (SBr a b) s'' ∧ α = LSess (SBra a b')) ∨
  (∃ a s'', src_step s (SCl a) s'' ∧ α = LSess (SClos a)).
Proof.
  intros Hc Hst. destruct (act_step _ _ _ Hst) as (x & Hx & Ho).
  destruct Hc as [(_ & Hv & _)|[(a & v & s'' & w & Hs & Hact)|[(a & v & s'' & Hs & Hact)
    |[(a & b & s'' & Hs & Hact)|[(a & b & s'' & Hs & Hact)|[(a & s'' & Hs & Hact)|(Hact & _)]]]]]];
    try (rewrite Hx in Hact; injection Hact as ->).
  - exfalso. eauto using val_no_tstep.
  - left. destruct α as [|[]| |]; simpl in Ho; try done. destruct Ho as [-> ->]. eauto 10.
  - right; left. destruct α as [|[]| |]; simpl in Ho; try done. destruct Ho as [-> _]. eauto 10.
  - do 2 right; left. destruct α as [|[]| |]; simpl in Ho; try done. destruct Ho as [-> ->]. eauto 10.
  - do 3 right; left. destruct α as [|[]| |]; simpl in Ho; try done. subst. eauto 10.
  - do 4 right. destruct α as [|[]| |]; simpl in Ho; try done. subst. eauto 10.
  - rewrite Hx in Hact. discriminate.
Qed.

Lemma normalize P P' Es Et :
  mrel P Es Et → (∀ s t, s ∈ Es → P s t → ∃ t', bstar t t' ∧ P' s t') →
  ∃ Et', rtc msb Et Et' ∧ mrel P' Es Et'.
Proof.
  induction 1 as [|s t Es Et HP Hm IH]; intros HPP.
  - exists ∅. split; [done|constructor].
  - destruct (HPP s t) as (t' & Hs & HP'); [multiset_solver|done|].
    destruct IH as (Et' & Hst & Hm').
    { intros s0 t0 Hin. apply HPP. multiset_solver. }
    exists ({[+ t' +]} ⊎ Et'). split; [|by constructor].
    apply (rtc_trans _ ({[+ t' +]} ⊎ Et)).
    + rewrite (comm_L (⊎) {[+ t +]}), (comm_L (⊎) {[+ t' +]}). by apply msb_bstar.
    + by apply msb_frame.
Qed.

Lemma cls_val s t : cls s t → is_val t → is_val s ∧ (t = EUnit → s = EUnit).
Proof.
  intros Hc Hv.
  destruct Hc as [(? & _ & ?)|[(? & ? & ? & ? & _ & Hact)|[(? & ? & ? & _ & Hact)
    |[(? & ? & ? & _ & Hact)|[(? & ? & ? & _ & Hact)|[(? & ? & _ & Hact)|(_ & Hn)]]]]]];
    try (by rewrite act_val in Hact); [done|]. by rewrite Hn in Hv.
Qed.

Lemma final p q :
  prel2 p q → (∀ q', pred_star q q' → safe q') → src_irred p → src_final p.
Proof.
  destruct p as [C Es], q as [Cq Et]. intros (HC & Hm) Hsafe Hirr.
  simpl in HC, Hm. subst Cq.
  destruct (normalize _ cls _ _ Hm) as (Et' & Hst & Hm').
  { intros s t Hs HR. destruct (gmultiset_split1 _ _ Hs) as [E0 ->]. by eapply classify. }
  destruct (Hsafe (C, Et') (msb_pred _ _ _ Hst)) as [Hterm|(q'' & Hred)].
  - destruct Hterm as (v & E1 & [= -> ->] & Hv & HE1).
    rewrite (comm_L (⊎)) in Hm'. destruct (mrel_extract _ _ _ _ Hm') as (Es0 & s0 & -> & Hc & Hm0).
    split; [done|]. exists s0, Es0. split_and!; [simpl; multiset_solver|by apply (cls_val _ _ Hc Hv)|].
    intros s Hs. destruct (mrel_elem_l _ _ _ _ Hm0 Hs) as (t & Ht & Hct).
    rewrite (HE1 _ Ht) in Hct. by apply (cls_val _ _ Hct).
  - exfalso. unfold preduction in Hred.
    inversion Hred as [|C0 E0 e e' Hste|C0 E0 e c e' Hste|C0 E0 e v e' Hste
                      |C0 E0 c v e e' f f' Hse Hsf|C0 E0 c e e' f f' Hse Hsf Hc
                      |C0 E0 c b e e' f f' Hse Hsf|C0 E0 e c d e' Hste]; subst.
    + destruct (mrel_extract _ _ _ _ Hm') as (Es0 & s & -> & Hc & _).
      destruct (cls_step _ _ _ _ Hc Hste) as [(? & ? & ? & ? & _ & [=])|[(? & ? & ? & ? & _ & [=])
        |[(? & ? & ? & _ & [=])|[(? & ? & ? & ? & _ & [=])|(? & ? & _ & [=])]]]].
    + destruct (mrel_extract _ _ _ _ Hm') as (Es0 & s & -> & Hc & _).
      destruct (cls_step _ _ _ _ Hc Hste) as [(? & ? & ? & ? & _ & [=])|[(? & ? & ? & ? & _ & [=])
        |[(? & ? & ? & _ & [=])|[(? & ? & ? & ? & _ & [=])|(? & ? & _ & [=])]]]].
    + destruct (mrel_extract _ _ _ _ Hm') as (Es0 & s & -> & Hc & _).
      destruct (cls_step _ _ _ _ Hc Hste) as [(? & ? & ? & ? & _ & [=])|[(? & ? & ? & ? & _ & [=])
        |[(? & ? & ? & _ & [=])|[(? & ? & ? & ? & _ & [=])|(? & ? & _ & [=])]]]].
    + destruct (mrel_extract _ _ _ _ Hm') as (Es1 & sf & -> & Hcf & Hm1).
      destruct (mrel_extract _ _ _ _ Hm1) as (Es0 & se & -> & Hce & _).
      destruct (cls_step _ _ _ _ Hce Hse) as [(a & ve & se' & w & Hse' & [= -> ->])|[(? & ? & ? & ? & _ & [=])
        |[(? & ? & ? & _ & [=])|[(? & ? & ? & ? & _ & [=])|(? & ? & _ & [=])]]]].
      destruct (cls_step _ _ _ _ Hcf Hsf) as [(? & ? & ? & ? & _ & [=])|[(a' & vf & sf' & w' & Hsf' & [= -> ->])
        |[(? & ? & ? & _ & [=])|[(? & ? & ? & ? & _ & [=])|(? & ? & _ & [=])]]]].
      destruct (src_step_recv_any _ _ _ _ Hsf' ve (src_step_send_val _ _ _ _ Hse')) as [sf'' Hsf''].
      eapply Hirr. by eapply SPCom.
    + destruct (mrel_extract _ _ _ _ Hm') as (Es1 & sf & -> & Hcf & Hm1).
      destruct (mrel_extract _ _ _ _ Hm1) as (Es0 & se & -> & Hce & _).
      destruct (cls_step _ _ _ _ Hce Hse) as [(? & ? & ? & ? & _ & [=])|[(? & ? & ? & ? & _ & [=])
        |[(? & ? & ? & _ & [=])|[(? & ? & ? & ? & _ & [=])|(a & se' & Hse' & [= ->])]]]].
      destruct (cls_step _ _ _ _ Hcf Hsf) as [(? & ? & ? & ? & _ & [=])|[(? & ? & ? & ? & _ & [=])
        |[(? & ? & ? & _ & [=])|[(? & ? & ? & ? & _ & [=])|(a' & sf' & Hsf' & [= ->])]]]].
      eapply Hirr. by eapply SPClose.
    + destruct (mrel_extract _ _ _ _ Hm') as (Es1 & sf & -> & Hcf & Hm1).
      destruct (mrel_extract _ _ _ _ Hm1) as (Es0 & se & -> & Hce & _).
      destruct (cls_step _ _ _ _ Hce Hse) as [(? & ? & ? & ? & _ & [=])|[(? & ? & ? & ? & _ & [=])
        |[(a & b' & se' & Hse' & [= -> ->])|[(? & ? & ? & ? & _ & [=])|(? & ? & _ & [=])]]]].
      destruct (cls_step _ _ _ _ Hcf Hsf) as [(? & ? & ? & ? & _ & [=])|[(? & ? & ? & ? & _ & [=])
        |[(? & ? & ? & _ & [=])|[(a' & b0 & sf' & b1 & Hsf' & [= -> ->])|(? & ? & _ & [=])]]]].
      match type of Hse' with src_step _ (SSl _ ?bb) _ => destruct (src_step_bra_any _ _ _ _ Hsf' bb) as [sf'' Hsf''] end.
      eapply Hirr. by eapply SPCh.
    + destruct (mrel_extract _ _ _ _ Hm') as (Es0 & s & -> & Hc & _).
      destruct (cls_step _ _ _ _ Hc Hste) as [(? & ? & ? & ? & _ & [=])|[(? & ? & ? & ? & _ & [=])
        |[(? & ? & ? & _ & [=])|[(? & ? & ? & ? & _ & [=])|(? & ? & _ & [=])]]]].
Qed.

(** ** The theorem *)

Theorem mp3_deadlock_free_source e ef e' :
  mtyped pc0 [] e MUnit ef e' → mp_deadlock_free_src e.
Proof.
  intros Ht q Hq Hirr.
  assert (trm M0 e e' MdD) as Hr.
  { eapply trm_mono; [exact (trm_of_typed _ _ _ _ _ _ Ht)|].
    intros x mx Hx. unfold mdenv in Hx. simpl in Hx. discriminate Hx. }
  assert (prel2 (∅, {[+ e +]}) (∅, {[+ e' +]})) as Hp.
  { split; [done|].
    replace ({[+ e +]} : gmultiset expr) with ({[+ e +]} ⊎ (∅ : gmultiset expr)) by multiset_solver.
    replace ({[+ e' +]} : gmultiset expr) with ({[+ e' +]} ⊎ (∅ : gmultiset expr)) by multiset_solver.
    constructor; [by left|constructor]. }
  destruct (sim_star _ _ _ Hq Hp) as (q' & Hq' & Hp').
  eapply final; [exact Hp'| |exact Hirr].
  intros q'' Hq''. apply (mp3_deadlock_free e ef e' Ht). by etrans.
Qed.

(** ** The examples in the source semantics *)

Theorem rt_deadlock_free_src3 : mp_deadlock_free_src rt_main.
Proof. destruct rt_main_typed as (ef & e' & H). exact (mp3_deadlock_free_source _ _ _ H). Qed.

Theorem st_deadlock_free_src3 : mp_deadlock_free_src st_main.
Proof. destruct st_main_typed as (ef & e' & H). exact (mp3_deadlock_free_source _ _ _ H). Qed.

Theorem df_deadlock_free_src3 : mp_deadlock_free_src df_main.
Proof. destruct df_main_typed as (ef & e' & H). exact (mp3_deadlock_free_source _ _ _ H). Qed.

Theorem t2_deadlock_free_src3 : mp_deadlock_free_src t2_main.
Proof. destruct t2_main_typed as (ef & e' & H). exact (mp3_deadlock_free_source _ _ _ H). Qed.

Theorem ch3_deadlock_free_src3 : mp_deadlock_free_src ch3_main.
Proof. destruct ch3_main_typed as (ef & e' & H). exact (mp3_deadlock_free_source _ _ _ H). Qed.

Theorem rr_deadlock_free_src3 : mp_deadlock_free_src rr_main.
Proof. destruct rr_main_typed as (ef & e' & H). exact (mp3_deadlock_free_source _ _ _ H). Qed.

Theorem rtA_deadlock_free_src3 : mp_deadlock_free_src rtA_main.
Proof. destruct rtA_main_typed as (ef & e' & H). exact (mp3_deadlock_free_source _ _ _ H). Qed.

Theorem rtB_deadlock_free_src3 : mp_deadlock_free_src rtB_main.
Proof. destruct rtB_main_typed as (ef & e' & H). exact (mp3_deadlock_free_source _ _ _ H). Qed.
