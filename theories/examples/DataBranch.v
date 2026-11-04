(** * A branch on a received bit (SHARP-EDGES 4, docs/extensions/data-dependent-worlds.md)

    db_main b creates three channels, e first, then c, then d, spawns
    a closer for the other end of c, a closer for the other end of d
    and a sender of the bit b on the other end of e, receives the bit,
    closes e and branches on it.

      db_main b =
        let (e, e′) = new ∗ in let (c, c′) = new ∗ in let (d, d′) = new ∗ in
        let () = spawn (λu. let () = u in close c′) in
        let () = spawn (λu. let () = u in close d′) in
        let () = spawn (λu. let () = u in close (send ⟨bit b, e′⟩)) in
        let (z, e) = recv e in let () = close e in
        case z of inl u ⇒ let () = u in let () = close c in close d
                | inr u ⇒ let () = u in let () = close d in close c

    The inl branch closes c while it holds d, the inr branch closes d
    while it holds c. With c at x and d at y, E-App asks x ≺ y in the
    first branch and y ≺ x in the second, and E-Case types both
    branches under one Γ. SHARP-EDGES 4 records such a program as
    deadlock free and not derivable. It is derivable.

    What is proved here.

    - [db_typed] : db_main b has a source derivation for both bits, with
      no top-level points. The receiver gives the bit a type whose side
      for the other bit carries an unsatisfiable fact about the payload
      points of the receive, ∗ ⊕ ∃{z[0]+5 ≺ z[0]+1}.∗ for b = false.
      E-Open in the dead branch adds the fact, and the creation
      constraints anchor c and d to z[0]+1 and z[0]+5, so the dead
      branch derives the reverse order. The static facts give the order
      of the live branch. [db_deadlock_free] follows from [soundness].

    - [db_component_unrealizable] : the case node of db_main, with the
      bit typed at ∗ ⊕ ∗ (no fact on either side), c : Close@x and
      d : Close@y, has no source derivation under any hypotheses Φ, Ψ
      that a strict world realizes. The proof is semantic. A derivation
      gives the case node in the logical relation at every realizing
      world (the fundamental theorem), and both inl ∗ and inr ∗ lie in
      V⟦∗ ⊕ ∗⟧. Readiness of close c; close d asks x ≺ y in the world,
      readiness of close d; close c asks y ≺ x in the same world, and a
      strict world has no cycle. [db_component_untyped_top] instantiates
      it at the hypotheses a source program starts with.

    - [db_rnode_unrealizable] : the same for the receive of db_main and
      everything after it ([db_main_shape]), with e at the session type
      ?(∗ ⊕ ∗).Close. O-Recv of the relation quantifies over every
      payload in V⟦∗ ⊕ ∗⟧, so both bits reach the case in one world.

    - [df_keep] : replacing every case by the case whose branches are
      both the branch a run takes reflects deadlock freedom, for a
      program that never builds the other injection. It is a tool for
      programs whose dead branch does not type. db_main does not need
      it.

    So one world per component limits a component whose interface types
    the bit without facts. A closed program whose bit comes from a
    constant puts the facts on the bit. The design note discusses what
    this means for the candidates. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.LitTools lang.ThreadSim.

Set Default Proof Using "All".

(** ** The program *)

Definition bit (b : bool) : expr := if b then Inj2 EUnit else Inj1 EUnit.

(** One branch drops the unit payload, closes i, then closes j. *)
Definition db_branch (i j : nat) : expr :=
  LetU (Var 0) (LetU (App EClos (Var i)) (App EClos (Var j))).

(** Indices as the body of the three lets of new sees them, with the
    convention of [let_new_pair] (a at 1, b at 0, outer from 2). d′ is
    0, d 1, c′ 2, c 3, e′ 4 and e 5. After the let of the received pair
    e is 0, z 1, d 3 and c 5, and inside a branch u is 0, z 2, d 4 and
    c 6. [let_new_pair] renames them, and db_main holds the case node
    [db_case] below. *)
Definition db_tail (i1 j1 i2 j2 : nat) : expr :=
  LetP (App ERecv (Var 5))
    (LetU (App EClos (Var 0)) (Case (Var 1) (db_branch i1 j1) (db_branch i2 j2))).

Definition db_spawns (b : bool) (rest : expr) : expr :=
  LetU (App ESpawn (Lam (LetU (Var 0) (App EClos (Var 3)))))
  (LetU (App ESpawn (Lam (LetU (Var 0) (App EClos (Var 1)))))
  (LetU (App ESpawn (Lam (LetU (Var 0) (App EClos (App ESend (Pair (bit b) (Var 5)))))))
    rest)).

Definition db_main (b : bool) : expr :=
  let_new_pair (let_new_pair (let_new_pair (db_spawns b (db_tail 6 4 4 6)))).

(** ** Keeping one branch of every case

    keep b replaces case s e₁ e₂ by the case whose two branches are
    both e₁ (b = false) or both e₂ (b = true). okb b e says that e
    holds no injection of the other side and no branch constant, so
    that no run of e ever takes the dropped branch. *)

Fixpoint keep (b : bool) (e : expr) : expr :=
  match e with
  | Var x => Var x
  | EUnit => EUnit
  | Konst k => Konst k
  | Chan c => Chan c
  | Lam e => Lam (keep b e)
  | App e1 e2 => App (keep b e1) (keep b e2)
  | Pair e1 e2 => Pair (keep b e1) (keep b e2)
  | LetU e1 e2 => LetU (keep b e1) (keep b e2)
  | LetP e1 e2 => LetP (keep b e1) (keep b e2)
  | Inj1 e => Inj1 (keep b e)
  | Inj2 e => Inj2 (keep b e)
  | Case e e1 e2 =>
      Case (keep b e) (keep b (if b then e2 else e1)) (keep b (if b then e2 else e1))
  | EBox e => EBox (keep b e)
  end.

Fixpoint okb (b : bool) (e : expr) : Prop :=
  match e with
  | Var _ | EUnit | Chan _ => True
  | Konst k => k ≠ KBra
  | Lam e | EBox e => okb b e
  | App e1 e2 | Pair e1 e2 | LetU e1 e2 | LetP e1 e2 => okb b e1 ∧ okb b e2
  | Inj1 e => b = false ∧ okb b e
  | Inj2 e => b = true ∧ okb b e
  | Case e e1 e2 => okb b e ∧ okb b e1 ∧ okb b e2
  end.

Lemma keep_rename b e : ∀ r, keep b (rename r e) = rename r (keep b e).
Proof. induction e; intros r; simpl; f_equal; auto. all: destruct b; auto. Qed.

Lemma keep_up b σ x : keep b (up σ x) = up (keep b ∘ σ) x.
Proof. destruct x; simpl; [done|]. unfold compose. by rewrite keep_rename. Qed.

Lemma keep_up2 b σ x : keep b (up (up σ) x) = up (up (keep b ∘ σ)) x.
Proof. rewrite keep_up. apply up_ext. intros. apply keep_up. Qed.

Lemma keep_subst b e : ∀ σ, keep b (subst σ e) = subst (keep b ∘ σ) (keep b e).
Proof.
  induction e; intros σ; simpl; f_equal; auto.
  all: try destruct b.
  all: repeat match goal with
    | IH : ∀ σ, keep _ (subst σ ?e) = _ |- context [keep _ (subst ?s ?e)] => rewrite (IH s)
    end.
  all: apply subst_ext; intros; first [apply keep_up2|apply keep_up].
Qed.

Lemma keep_subst1 b v e : keep b (subst1 v e) = subst1 (keep b v) (keep b e).
Proof. unfold subst1. rewrite keep_subst. apply subst_ext. by intros []. Qed.

Lemma keep_subst2 b u v e : keep b (subst2 u v e) = subst2 (keep b u) (keep b v) (keep b e).
Proof. unfold subst2. rewrite keep_subst. apply subst_ext. by intros [|[]]. Qed.

Lemma is_val_keep b e : is_val (keep b e) = is_val e.
Proof. induction e; simpl; try done; by rewrite ?IHe1, ?IHe2. Qed.

Lemma keep_chsubst b c d e : keep b (chsubst c d e) = chsubst c d (keep b e).
Proof. induction e; simpl; f_equal; auto. all: destruct b; auto. Qed.

Lemma fchans_keep b e : fchans (keep b e) ⊆ fchans e.
Proof. induction e; simpl; try set_solver. destruct b; set_solver. Qed.

(** okb is stable under renaming and substitution. *)
Lemma okb_rename b e : ∀ r, okb b e → okb b (rename r e).
Proof. induction e; intros r; simpl; naive_solver. Qed.

Lemma okb_subst b e : ∀ σ, (∀ x, okb b (σ x)) → okb b e → okb b (subst σ e).
Proof.
  assert (∀ σ, (∀ x, okb b (σ x)) → ∀ x, okb b (up σ x)) as Hup.
  { intros σ H [|x]; simpl; [done|]. unfold compose. by apply okb_rename. }
  induction e; intros σ Hσ; simpl; try naive_solver.
Qed.

Lemma okb_subst1 b v e : okb b v → okb b e → okb b (subst1 v e).
Proof. intros. apply okb_subst; [|done]. by intros []. Qed.

Lemma okb_subst2 b u v e : okb b u → okb b v → okb b e → okb b (subst2 u v e).
Proof. intros. apply okb_subst; [|done]. by intros [|[]]. Qed.

Lemma okb_chsubst b c d e : okb b e → okb b (chsubst c d e).
Proof. induction e; simpl; naive_solver. Qed.

(** The values a label carries. *)
Definition lab_ok (b : bool) (α : tlabel) : Prop :=
  match α with
  | LSess (SRecv _ v) | LSess (SSend _ v) | LSpawn v => okb b v
  | _ => True
  end.

Definition keep_lab (b : bool) (α : tlabel) : tlabel :=
  match α with
  | LSess (SRecv c v) => LSess (SRecv c (keep b v))
  | LSess (SSend c v) => LSess (SSend c (keep b v))
  | LSpawn v => LSpawn (keep b v)
  | _ => α
  end.

(** A step of an okb term keeps okb, and so does every value it gives
    away, and it takes no branch step. *)
Lemma okb_step b e α e' :
  tstep e α e' → okb b e →
  (match α with LSess (SRecv _ v) => okb b v | _ => True end → okb b e') ∧
  match α with
  | LSess (SSend _ v) | LSpawn v => okb b v
  | LSess (SBra _ _) => False
  | _ => True
  end.
Proof.
  induction 1 as [e α e' Hh| | | | | | | | | ]; simpl; intros Hok.
  - destruct Hh; simpl in *; try (destruct Hok as [Hk _]; by destruct Hk);
      repeat match goal with H : _ ∧ _ |- _ => destruct H end;
      split; try done; try (intros; by apply okb_subst1);
      try (intros; by apply okb_subst2); try naive_solver.
  - destruct Hok as [H1 H2]. destruct (IHtstep H1) as [Hc Hl]. split; [|done].
    intros Hv. split; [by apply Hc|done].
  - destruct Hok as [H1 H2]. destruct (IHtstep H2) as [Hc Hl]. split; [|done].
    intros Hv. split; [done|by apply Hc].
  - destruct Hok as [H1 H2]. destruct (IHtstep H1) as [Hc Hl]. split; [|done].
    intros Hv. split; [by apply Hc|done].
  - destruct Hok as [H1 H2]. destruct (IHtstep H2) as [Hc Hl]. split; [|done].
    intros Hv. split; [done|by apply Hc].
  - destruct Hok as [H1 H2]. destruct (IHtstep H1) as [Hc Hl]. split; [|done].
    intros Hv. split; [by apply Hc|done].
  - destruct Hok as [H1 H2]. destruct (IHtstep H1) as [Hc Hl]. split; [|done].
    intros Hv. split; [by apply Hc|done].
  - destruct Hok as [H1 H2]. destruct (IHtstep H2) as [Hc Hl]. split; [|done].
    intros Hv. split; [done|by apply Hc].
  - destruct Hok as [H1 H2]. destruct (IHtstep H2) as [Hc Hl]. split; [|done].
    intros Hv. split; [done|by apply Hc].
  - destruct Hok as (H1 & H2 & H3). destruct (IHtstep H1) as [Hc Hl]. split; [|done].
    intros Hv. split_and!; [by apply Hc|done|done].
Qed.

(** keep commutes with a step of an okb term. *)
Lemma keep_step b e α e' :
  tstep e α e' → okb b e → tstep (keep b e) (keep_lab b α) (keep b e').
Proof.
  induction 1 as [e α e' Hh| | | | | | | | | ]; simpl; intros Hok.
  - apply TStepHead. destruct Hh; simpl in *.
    + rewrite keep_subst1. constructor. by rewrite is_val_keep.
    + constructor.
    + rewrite keep_subst2. constructor; by rewrite is_val_keep.
    + constructor.
    + constructor. by rewrite is_val_keep.
    + constructor. by rewrite is_val_keep.
    + constructor. by rewrite is_val_keep.
    + constructor.
    + constructor.
    + constructor.
    + destruct Hok as [Hk _]. by destruct Hk.
    + destruct Hok as ([-> _] & _ & _). rewrite keep_subst1. constructor. by rewrite is_val_keep.
    + destruct Hok as ([-> _] & _ & _). rewrite keep_subst1. constructor. by rewrite is_val_keep.
    + rewrite keep_subst1. constructor.
    + constructor.
  - apply TStepAppL. by apply IHtstep, Hok.
  - apply TStepAppR; [by rewrite is_val_keep|]. by apply IHtstep, Hok.
  - apply TStepPairL. by apply IHtstep, Hok.
  - apply TStepPairR; [by rewrite is_val_keep|]. by apply IHtstep, Hok.
  - apply TStepLetU. by apply IHtstep, Hok.
  - apply TStepLetP. by apply IHtstep, Hok.
  - apply TStepInj1. by apply IHtstep, Hok.
  - apply TStepInj2. by apply IHtstep, Hok.
  - apply TStepCase. by apply IHtstep, Hok.
Qed.

(** Shapes of keep. *)
Lemma keep_inv_konst b e k : keep b e = Konst k → e = Konst k.
Proof. destruct e; simpl; congruence. Qed.
Lemma keep_inv_chan b e c : keep b e = Chan c → e = Chan c.
Proof. destruct e; simpl; congruence. Qed.
Lemma keep_inv_unit b e : keep b e = EUnit → e = EUnit.
Proof. destruct e; simpl; congruence. Qed.
Lemma keep_inv_lam b e e0 : keep b e = Lam e0 → ∃ e1, e = Lam e1.
Proof. destruct e; simpl; try congruence. eauto. Qed.
Lemma keep_inv_box b e e0 : keep b e = EBox e0 → ∃ e1, e = EBox e1.
Proof. destruct e; simpl; try congruence. eauto. Qed.
Lemma keep_inv_pair b e u v : keep b e = Pair u v → ∃ u' v', e = Pair u' v' ∧ keep b u' = u ∧ keep b v' = v.
Proof. destruct e; simpl; try congruence. intros [= <- <-]. eauto. Qed.
Lemma keep_inv_inj1 b e u : keep b e = Inj1 u → ∃ u', e = Inj1 u'.
Proof. destruct e; simpl; try congruence. eauto. Qed.
Lemma keep_inv_inj2 b e u : keep b e = Inj2 u → ∃ u', e = Inj2 u'.
Proof. destruct e; simpl; try congruence. eauto. Qed.

Ltac kinv :=
  repeat match goal with
  | H : Konst _ = keep _ _ |- _ => symmetry in H
  | H : Chan _ = keep _ _ |- _ => symmetry in H
  | H : EUnit = keep _ _ |- _ => symmetry in H
  | H : Lam _ = keep _ _ |- _ => symmetry in H
  | H : EBox _ = keep _ _ |- _ => symmetry in H
  | H : Pair _ _ = keep _ _ |- _ => symmetry in H
  | H : keep _ _ = Konst _ |- _ => apply keep_inv_konst in H; subst
  | H : keep _ _ = Chan _ |- _ => apply keep_inv_chan in H; subst
  | H : keep _ _ = EUnit |- _ => apply keep_inv_unit in H; subst
  | H : keep _ _ = Lam _ |- _ => destruct (keep_inv_lam _ _ _ H) as [? ->]; clear H
  | H : keep _ _ = EBox _ |- _ => destruct (keep_inv_box _ _ _ H) as [? ->]; clear H
  | H : keep _ _ = Pair _ _ |- _ =>
      let u := fresh "u" in let v := fresh "v" in
      destruct (keep_inv_pair _ _ _ _ H) as (u & v & -> & ? & ?); clear H
  end.

(** Labels up to their values. *)
Definition lshape (α : tlabel) : tlabel :=
  match α with
  | LSess (SRecv c _) => LSess (SRecv c EUnit)
  | LSess (SSend c _) => LSess (SSend c EUnit)
  | LSpawn _ => LSpawn EUnit
  | _ => α
  end.

(** A step of keep b e comes from a step of e with a label of the same
    shape. A send keeps its value up to keep. *)
Lemma keep_reflect b e : ∀ α f, tstep (keep b e) α f →
  ∃ α' e', tstep e α' e' ∧ lshape α' = lshape α ∧
    (∀ c v, α = LSess (SSend c v) → ∃ v', α' = LSess (SSend c v') ∧ keep b v' = v).
Proof.
  induction e; intros α f Hst; simpl in Hst.
  - inversion Hst; subst. inversion H.
  - inversion Hst; subst. inversion H.
  - inversion Hst; subst. inversion H.
  - inversion Hst; subst. inversion H.
  - inversion Hst; subst. inversion H.
  - apply tstep_app_inv in Hst as [(e1' & Hs & ->)|[(Hv & e2' & Hs & ->)|(Hv1 & Hv2 & Hh)]].
    + destruct (IHe1 _ _ Hs) as (α' & e' & ? & ? & ?). eexists _, _. split; [by apply TStepAppL|done].
    + rewrite is_val_keep in Hv. destruct (IHe2 _ _ Hs) as (α' & e' & ? & ? & ?).
      eexists _, _. split; [by apply TStepAppR|done].
    + rewrite is_val_keep in Hv1, Hv2. inversion Hh; subst; kinv.
      * eexists _, _. split; [apply TStepHead; constructor; by rewrite <-(is_val_keep b)|].
        split; [done|]. intros; discriminate.
      * eexists _, _. split; [apply TStepHead; constructor|]. split; [done|]. intros; discriminate.
      * eexists _, _. split; [apply TStepHead; by constructor|]. split; [done|]. intros; discriminate.
      * eexists _, _. split; [apply TStepHead; apply (HeadRecv _ EUnit); done|]. split; [done|].
        intros; discriminate.
      * simpl in Hv2. apply andb_True in Hv2 as [Hv2 _].
        eexists _, _. split; [apply TStepHead; by constructor|]. split; [done|].
        intros c' v [= -> <-]. eauto.
      * eexists _, _. split; [apply TStepHead; constructor|]. split; [done|]. intros; discriminate.
      * eexists _, _. split; [apply TStepHead; constructor|]. split; [done|]. intros; discriminate.
      * eexists _, _. split; [apply TStepHead; constructor|]. split; [done|]. intros; discriminate.
      * eexists _, _. split; [apply TStepHead; constructor|]. split; [done|]. intros; discriminate.
      * eexists _, _. split; [apply TStepHead; constructor|]. split; [done|]. intros; discriminate.
      * eexists _, _. split; [apply TStepHead; constructor|]. split; [done|]. intros; discriminate.
  - apply tstep_pair_inv in Hst as [(e1' & Hs & ->)|(Hv & e2' & Hs & ->)].
    + destruct (IHe1 _ _ Hs) as (α' & e' & ? & ? & ?). eexists _, _. split; [by apply TStepPairL|done].
    + rewrite is_val_keep in Hv. destruct (IHe2 _ _ Hs) as (α' & e' & ? & ? & ?).
      eexists _, _. split; [by apply TStepPairR|done].
  - apply tstep_letu_inv in Hst as [(e1' & Hs & ->)|(Hu & -> & ->)].
    + destruct (IHe1 _ _ Hs) as (α' & e' & ? & ? & ?). eexists _, _. split; [by apply TStepLetU|done].
    + apply keep_inv_unit in Hu as ->. eexists _, _. split; [apply TStepHead; constructor|].
      split; [done|]. intros; discriminate.
  - apply tstep_letp_inv in Hst as [(e1' & Hs & ->)|(u & v & Hp & Hu & Hv & -> & ->)].
    + destruct (IHe1 _ _ Hs) as (α' & e' & ? & ? & ?). eexists _, _. split; [by apply TStepLetP|done].
    + destruct (keep_inv_pair _ _ _ _ Hp) as (u' & v' & -> & <- & <-).
      rewrite is_val_keep in Hu, Hv. eexists _, _. split; [apply TStepHead; by constructor|].
      split; [done|]. intros; discriminate.
  - apply tstep_inj1_inv in Hst as (e1' & Hs & ->).
    destruct (IHe _ _ Hs) as (α' & e' & ? & ? & ?). eexists _, _. split; [by apply TStepInj1|done].
  - apply tstep_inj2_inv in Hst as (e1' & Hs & ->).
    destruct (IHe _ _ Hs) as (α' & e' & ? & ? & ?). eexists _, _. split; [by apply TStepInj2|done].
  - apply tstep_case_inv in Hst as [(e1' & Hs & ->)|[(v & Hv & Hval & -> & ->)|(v & Hv & Hval & -> & ->)]].
    + destruct (IHe1 _ _ Hs) as (α' & e' & ? & ? & ?). eexists _, _. split; [by apply TStepCase|done].
    + destruct (keep_inv_inj1 _ _ _ Hv) as [u' ->]. simpl in Hv. injection Hv as <-.
      rewrite is_val_keep in Hval. eexists _, _. split; [apply TStepHead; by constructor|].
      split; [done|]. intros; discriminate.
    + destruct (keep_inv_inj2 _ _ _ Hv) as [u' ->]. simpl in Hv. injection Hv as <-.
      rewrite is_val_keep in Hval. eexists _, _. split; [apply TStepHead; by constructor|].
      split; [done|]. intros; discriminate.
  - inversion Hst; subst. inversion H.
Qed.

(** new can pick any name. *)
Lemma new_retarget e c e' c' : tstep e (LNew c) e' → ∃ e'', tstep e (LNew c') e''.
Proof.
  intros H. remember (LNew c) as α eqn:Hα.
  induction H; subst; try discriminate.
  - inversion H; simplify_eq. eexists. apply TStepHead. apply HeadNew.
  - destruct (IHtstep eq_refl) as [e'' ?]. eexists. by apply TStepAppL.
  - destruct (IHtstep eq_refl) as [e'' ?]. eexists. by apply TStepAppR.
  - destruct (IHtstep eq_refl) as [e'' ?]. eexists. by apply TStepPairL.
  - destruct (IHtstep eq_refl) as [e'' ?]. eexists. by apply TStepPairR.
  - destruct (IHtstep eq_refl) as [e'' ?]. eexists. by apply TStepLetU.
  - destruct (IHtstep eq_refl) as [e'' ?]. eexists. by apply TStepLetP.
  - destruct (IHtstep eq_refl) as [e'' ?]. eexists. by apply TStepInj1.
  - destruct (IHtstep eq_refl) as [e'' ?]. eexists. by apply TStepInj2.
  - destruct (IHtstep eq_refl) as [e'' ?]. eexists. by apply TStepCase.
Qed.

(** ** keep on processes

    A soup is related to the soup of its kept threads, thread by
    thread, and every thread of the source is okb. *)

Definition kthr (b : bool) (s t : expr) : Prop := okb b s ∧ t = keep b s.

Definition krel (b : bool) (p q : proc) : Prop := p.1 = q.1 ∧ mrel (kthr b) p.2 q.2.

Lemma mrel_echsubst b c d Es Et :
  mrel (kthr b) Es Et → mrel (kthr b) (echsubst c d Es) (echsubst c d Et).
Proof.
  induction 1 as [|s t Es Et [Hok ->] Hm IH].
  - unfold echsubst. rewrite !gmultiset_map_empty. constructor.
  - rewrite !echsubst_disj_union, !echsubst_singleton. constructor; [|done].
    split; [by apply okb_chsubst|]. by rewrite keep_chsubst.
Qed.

Lemma kthr_fchans b s t : kthr b s t → fchans t ⊆ fchans s.
Proof. intros [_ ->]. apply fchans_keep. Qed.

Ltac kextract H Hok Hm' :=
  destruct (mrel_extract_l _ _ _ _ H) as (? & ? & -> & [Hok ->] & Hm').

Lemma krel_step b p p' q :
  krel b p q → preduction p p' → ∃ q', preduction q q' ∧ krel b p' q'.
Proof.
  destruct p as [C Es], q as [C' Et]. intros [HC Hm] Hst. simpl in HC, Hm. subst C'.
  inversion Hst as
    [|C0 E e e' Hs E1 E2
     |C0 E e c e' Hs Hc1 Hc2 Hc3 E1 E2
     |C0 E e v e' Hs E1 E2
     |C0 E c v e e' f f' He Hf E1 E2
     |C0 E c e e' f f' He Hf Hc E1 E2
     |C0 E c bb e e' f f' He Hf E1 E2
     |C0 E e c d e' Hs Hc E1 E2]; subst.
  - (* β *)
    kextract Hm Hok Hm1. destruct (okb_step _ _ _ _ Hs Hok) as [Hc _].
    eexists. split; [apply PStepBeta, (keep_step _ _ _ _ Hs Hok)|].
    split; [done|]. simpl. apply mrel_snoc; [|done]. split; [by apply Hc|done].
  - (* new *)
    kextract Hm Hok Hm1. destruct (okb_step _ _ _ _ Hs Hok) as [Hk _].
    eexists. split.
    + apply PStepNew; [apply (keep_step _ _ _ _ Hs Hok)|done| |].
      * intros Hin. apply Hc2. by apply (mrel_echans _ _ _ (kthr_fchans b) Hm1).
      * intros Hin. apply Hc3. by apply (fchans_keep b e).
    + split; [done|]. simpl. apply mrel_snoc; [|done]. split; [by apply Hk|done].
  - (* spawn *)
    kextract Hm Hok Hm1. destruct (okb_step _ _ _ _ Hs Hok) as [Hk Hv].
    eexists. split; [apply PStepSpawn, (keep_step _ _ _ _ Hs Hok)|].
    split; [done|]. simpl. apply mrel_snoc; [|apply mrel_snoc; [|done]].
    + split; [simpl; by split|done].
    + split; [by apply Hk|done].
  - (* message *)
    kextract Hm Hokf Hm1. kextract Hm1 Hok Hm2.
    destruct (okb_step _ _ _ _ He Hok) as [Hke Hv].
    destruct (okb_step _ _ _ _ Hf Hokf) as [Hkf _].
    eexists. split.
    + apply (PStepMsg _ _ c (keep b v)); [apply (keep_step _ _ _ _ He Hok)|apply (keep_step _ _ _ _ Hf Hokf)].
    + split; [done|]. simpl. apply mrel_snoc; [|apply mrel_snoc; [|done]].
      * split; [by apply Hkf|done].
      * split; [by apply Hke|done].
  - (* close *)
    kextract Hm Hokf Hm1. kextract Hm1 Hok Hm2.
    destruct (okb_step _ _ _ _ He Hok) as [Hke _].
    destruct (okb_step _ _ _ _ Hf Hokf) as [Hkf _].
    eexists. split.
    + apply PStepClose; [apply (keep_step _ _ _ _ He Hok)|apply (keep_step _ _ _ _ Hf Hokf)|done].
    + split; [done|]. simpl. apply mrel_snoc; [|apply mrel_snoc; [|done]].
      * split; [by apply Hkf|done].
      * split; [by apply Hke|done].
  - (* choice, which an okb thread never takes *)
    kextract Hm Hok Hm1. destruct (okb_step _ _ _ _ Hf Hok) as [_ []].
  - (* link *)
    kextract Hm Hok Hm1. destruct (okb_step _ _ _ _ Hs Hok) as [Hk _].
    eexists. split; [apply PStepLink; [apply (keep_step _ _ _ _ Hs Hok)|done]|].
    split; [done|]. simpl. apply mrel_echsubst, mrel_snoc; [|done]. split; [by apply Hk|done].
Qed.

Lemma krel_steps b p p' q :
  krel b p q → pred_star p p' → ∃ q', pred_star q q' ∧ krel b p' q'.
Proof.
  intros Hr Hs. revert q Hr. induction Hs as [p|p p1 p' H1 _ IH]; intros q Hr.
  - by exists q.
  - destruct (krel_step _ _ _ _ Hr H1) as (q1 & Hq1 & Hr1).
    destruct (IH _ Hr1) as (q' & Hq' & Hr'). exists q'. split; [|done].
    by eapply rtc_l.
Qed.

(** A step of a kept thread, read back on its source thread. *)
Lemma kreflect b s α f :
  tstep (keep b s) α f →
  ∃ α' s', tstep s α' s' ∧ lshape α' = lshape α ∧
    (∀ c v, α = LSess (SSend c v) → ∃ v', α' = LSess (SSend c v') ∧ keep b v' = v).
Proof. apply keep_reflect. Qed.

Ltac lshape_inv H :=
  match type of H with
  | lshape ?a = _ => destruct a as [|[]| |]; simpl in H; simplify_eq
  end.

Lemma krel_progress b p q q' :
  krel b p q → preduction q q' → ∃ p', preduction p p'.
Proof.
  destruct p as [C Es], q as [C' Et]. intros [HC Hm] Hst. simpl in HC, Hm. subst C'.
  inversion Hst as
    [|C0 E e e' Hs E1 E2
     |C0 E e c e' Hs Hc1 Hc2 Hc3 E1 E2
     |C0 E e v e' Hs E1 E2
     |C0 E c v e e' f f' He Hf E1 E2
     |C0 E c e e' f f' He Hf Hc E1 E2
     |C0 E c bb e e' f f' He Hf E1 E2
     |C0 E e c d e' Hs Hc E1 E2]; subst.
  - destruct (mrel_extract _ _ _ _ Hm) as (Es0 & s & -> & [_ ->] & _).
    destruct (kreflect _ _ _ _ Hs) as (α' & s' & Hs' & Hl & _). lshape_inv Hl.
    eexists. by apply PStepBeta.
  - destruct (mrel_extract _ _ _ _ Hm) as (Es0 & s & -> & [_ ->] & _).
    destruct (kreflect _ _ _ _ Hs) as (α' & s' & Hs' & Hl & _). lshape_inv Hl.
    set (c' := fresh (C ∪ echans Es0 ∪ fchans s)).
    assert (c' ∉ C ∪ echans Es0 ∪ fchans s) as Hc' by apply is_fresh.
    destruct (new_retarget _ _ _ c' Hs') as [s'' Hs''].
    eexists. apply (PStepNew _ _ _ c' s''); [done|set_solver|set_solver|set_solver].
  - destruct (mrel_extract _ _ _ _ Hm) as (Es0 & s & -> & [_ ->] & _).
    destruct (kreflect _ _ _ _ Hs) as (α' & s' & Hs' & Hl & _). lshape_inv Hl.
    eexists. by eapply PStepSpawn.
  - destruct (mrel_extract _ _ _ _ Hm) as (Es1 & sf & -> & [_ ->] & Hm1).
    destruct (mrel_extract _ _ _ _ Hm1) as (Es0 & se & -> & [_ ->] & _).
    destruct (kreflect _ _ _ _ He) as (α1 & se' & Hse & _ & Hsnd).
    destruct (Hsnd c v eq_refl) as (v' & -> & _).
    destruct (kreflect _ _ _ _ Hf) as (α2 & sf' & Hsf & Hl & _). lshape_inv Hl.
    destruct (recv_retarget _ _ _ _ v' Hsf (tstep_send_val _ _ _ _ Hse)) as [sf'' Hsf''].
    eexists. by eapply PStepMsg.
  - destruct (mrel_extract _ _ _ _ Hm) as (Es1 & sf & -> & [_ ->] & Hm1).
    destruct (mrel_extract _ _ _ _ Hm1) as (Es0 & se & -> & [_ ->] & _).
    destruct (kreflect _ _ _ _ He) as (α1 & se' & Hse & Hl1 & _). lshape_inv Hl1.
    destruct (kreflect _ _ _ _ Hf) as (α2 & sf' & Hsf & Hl2 & _). lshape_inv Hl2.
    eexists. by eapply PStepClose.
  - destruct (mrel_extract _ _ _ _ Hm) as (Es1 & sf & -> & [_ ->] & Hm1).
    destruct (mrel_extract _ _ _ _ Hm1) as (Es0 & se & -> & [_ ->] & _).
    destruct (kreflect _ _ _ _ He) as (α1 & se' & Hse & Hl1 & _). lshape_inv Hl1.
    destruct (kreflect _ _ _ _ Hf) as (α2 & sf' & Hsf & Hl2 & _). lshape_inv Hl2.
    eexists. by eapply PStepChoice.
  - destruct (mrel_extract _ _ _ _ Hm) as (Es0 & s & -> & [_ ->] & _).
    destruct (kreflect _ _ _ _ Hs) as (α' & s' & Hs' & Hl & _). lshape_inv Hl.
    eexists. by eapply PStepLink.
Qed.

Lemma krel_terminated b p q : krel b p q → terminated q → terminated p.
Proof.
  destruct p as [C Es], q as [C' Et]. intros [HC Hm] (v & E & [= -> ->] & Hv & HE).
  simpl in HC, Hm. subst C. rewrite (comm_L (⊎)) in Hm.
  destruct (mrel_extract _ _ _ _ Hm) as (Es0 & s & -> & [_ Hs] & Hm0).
  exists s, Es0. split_and!.
  - by rewrite (comm_L (⊎)).
  - by rewrite <-(is_val_keep b), <-Hs.
  - intros e He. destruct (mrel_elem_l _ _ _ _ Hm0 He) as (t & Ht & [_ ->]).
    apply (keep_inv_unit b), HE, Ht.
Qed.

Lemma krel_safe b p q : krel b p q → safe q → safe p.
Proof.
  intros Hr [Ht|(q' & Hq')]; [left; by eapply krel_terminated|right].
  by eapply krel_progress.
Qed.

(** Safety is reflected along keep for a closed thread that is okb. *)
Theorem df_keep b e : okb b e → deadlock_free (∅, {[+ keep b e +]}) → deadlock_free (∅, {[+ e +]}).
Proof.
  intros Hok Hdf p' Hs.
  assert (krel b (∅, {[+ e +]}) (∅, {[+ keep b e +]})) as Hr.
  { split; [done|]. simpl. rewrite <-(right_id_L ∅ (⊎) {[+ e +]}), <-(right_id_L ∅ (⊎) {[+ keep b e +]}).
    constructor; [by split|constructor]. }
  destruct (krel_steps _ _ _ _ Hr Hs) as (q' & Hq' & Hr').
  eapply krel_safe; [exact Hr'|]. by apply Hdf.
Qed.

(** ** The component has no derivation under realizable hypotheses

    db_case is the case node of db_main, in the context the run gives
    it. The received bit z is at 1, d at 3 and c at 7, and every other
    entry is spent ([db_typed_false] reaches this node with this context, except
    that it gives z a type with a fact). A world W realizes Φ and Ψ when an instance σ of the point
    variables makes every hypothesis of Ψ hold in W and puts every
    variable of Φ (the hypotheses on the future) below a set of points ρ. *)

Definition db_case : expr := Case (Var 1) (db_branch 8 4) (db_branch 4 8).

Definition db_ctx (x y : point) (k : nat) : lenv :=
  [None; Some (TSum TUnit TUnit); None; Some (TSess SEnd y); None; None; None;
   Some (TSess SEnd x)] ++ replicate k None.

Definition realizable (Φ : fhyps) (Ψ : hyps) : Prop :=
  ∃ W σ ρ, strict W ∧ inst_ok W (fhyps_pinst σ Φ) ρ ∧
    hyps_hold (w_eq W) (w_lt W) (pt_known W) (hyps_inst σ Ψ).

Definition chc : chan := "c".
Definition chd : chan := "d".

Definition db_Θ (x y : point) : tenv :=
  <[chd := One (SEnd, y)]> {[chc := One (SEnd, x)]}.

Definition db_γ (b : bool) : nat → expr :=
  λ i, match i with 1 => bit b | 3 => Chan chd | 7 => Chan chc | _ => EUnit end.

Lemma db_comp_cd R x y :
  tenv_comp R (db_Θ x y) {[chd := One (SEnd, y)]} {[chc := One (SEnd, x)]}.
Proof.
  split.
  - intros c. unfold db_Θ. destruct (decide (c = chd)) as [->|Hd].
    + rewrite lookup_insert_eq, lookup_singleton_eq, lookup_singleton_ne by done. constructor.
    + rewrite lookup_insert_ne, lookup_singleton_ne by done.
      destruct (decide (c = chc)) as [->|Hc].
      * rewrite lookup_singleton_eq. constructor.
      * rewrite lookup_singleton_ne by done. constructor.
  - intros c e1 e2 H1 H2. apply lookup_singleton_Some in H1 as [<- _].
    by rewrite lookup_singleton_ne in H2.
Qed.

Lemma grounding_nones n W k γ : grounding n W ∅ (replicate k None) γ.
Proof. revert γ. induction k; intros γ; simpl; [done|apply IHk]. Qed.

Lemma lenv_pinst_replicate σ k : lenv_pinst σ (replicate k None) = replicate k None.
Proof. unfold lenv_pinst. by rewrite fmap_replicate. Qed.

Lemma db_ground n W b x y k :
  world_wf W →
  grounding n W (db_Θ x y)
    ([None; Some (TSum TUnit TUnit); None; Some (TSess SEnd y); None; None; None;
      Some (TSess SEnd x)] ++ replicate k None) (db_γ b).
Proof.
  intros HW. cbn [grounding app].
  exists ∅, (db_Θ x y). split; [apply tenv_comp_empty_l, (wf_eq_sym _ HW)|]. split.
  { apply Vrel_sum_iff. destruct b; [right|left]; eexists; (split; [done|]); by apply Vrel_unit_iff. }
  exists {[chd := One (SEnd, y)]}, {[chc := One (SEnd, x)]}. split; [apply db_comp_cd|]. split.
  { apply Vrel_sess_iff. eexists _, _, _. split_and!; [done|done|apply seq_refl|apply (wf_eq_refl _ HW)]. }
  exists {[chc := One (SEnd, x)]}, ∅. split; [apply tenv_comp_empty_r|]. split.
  { apply Vrel_sess_iff. eexists _, _, _. split_and!; [done|done|apply seq_refl|apply (wf_eq_refl _ HW)]. }
  apply grounding_nones.
Qed.

(** [cc2 i j] steps only by closing i. *)
Definition cc2 (i j : chan) : expr := LetU (App EClos (Chan i)) (App EClos (Chan j)).

Lemma cc2_step i j α t : tstep (cc2 i j) α t → α = LSess (SClos i).
Proof.
  intros H. apply tstep_letu_inv in H as [(e1' & Hs & _)|(? & _)]; [|discriminate].
  apply tstep_app_inv in Hs as [(? & Hs & _)|[(_ & ? & Hs & _)|(_ & _ & Hh)]].
  - inversion Hs; subst. inversion H.
  - inversion Hs; subst. inversion H.
  - by inversion Hh.
Qed.

Lemma cc2_can i j : tstep (cc2 i j) (LSess (SClos i)) (LetU EUnit (App EClos (Chan j))).
Proof. apply TStepLetU, TStepHead, HeadClos. Qed.

(** Readiness of [cc2 i j], holding i at x and j at y, gives x ≺ y. *)
Lemma cc2_ready W F i j x y :
  i ≠ j →
  ready_t W (<[j := One (SEnd, y)]> {[i := One (SEnd, x)]}) F (cc2 i j) → w_lt W x y.
Proof.
  intros Hij Hr. set (Θ := <[j := One (SEnd, y)]> {[i := One (SEnd, x)]}) in *.
  assert (Θ !! i = Some (One (SEnd, x))) as Hi.
  { unfold Θ. rewrite lookup_insert_ne by done. apply lookup_singleton_eq. }
  assert (Θ !! j = Some (One (SEnd, y))) as Hj.
  { unfold Θ. apply lookup_insert_eq. }
  destruct Hr as [_ [Hl|Hb]].
  { intros α t Hs. by rewrite (cc2_step _ _ _ _ Hs). }
  { destruct Hl as (cd & t & Hs). apply cc2_step in Hs. discriminate. }
  assert (offered_t Θ (cc2 i j) (i, false)) as Hoff.
  { exists (SClos i), (LetU EUnit (App EClos (Chan j))). split; [apply cc2_can|]. simpl. split; [done|].
    exists (SEnd, x). unfold tenv_entry. simpl. rewrite Hi. split_and!; [done|done|discriminate]. }
  destruct (Hb (i, false) (SEnd, x) Hoff) as [H1 _].
  { unfold tenv_entry. simpl. by rewrite Hi. }
  apply (H1 (j, false) (SEnd, y)).
  - unfold tenv_entry. simpl. by rewrite Hj.
  - intros (σ & t & Hs & Hsel). apply cc2_step in Hs. injection Hs as ->.
    destruct Hsel as [Hc _]. simpl in Hc. by subst.
Qed.

(** One run of the related case at the bit b reaches a ready check. *)
Lemma db_case_subst b :
  subst (db_γ b) db_case = Case (bit b) (LetU (Var 0) (cc2 chc chd)) (LetU (Var 0) (cc2 chd chc)).
Proof. by destruct b. Qed.

Lemma db_Θ_swap x y : db_Θ x y = <[chc := One (SEnd, x)]> {[chd := One (SEnd, y)]}.
Proof.
  unfold db_Θ. apply map_eq. intros c.
  destruct (decide (c = chd)) as [->|Hd]; [|destruct (decide (c = chc)) as [->|Hc]].
  - by rewrite lookup_insert_eq, lookup_insert_ne, lookup_singleton_eq.
  - by rewrite lookup_insert_ne, lookup_singleton_eq, lookup_insert_eq.
  - by rewrite !lookup_insert_ne, !lookup_singleton_ne.
Qed.

Ltac ebeta HE st :=
  eapply Erel_S_step in HE; [|apply TStepHead; st];
  cbn [Ecase_gen Eobl at_cost tcost nlower pred] in HE.

Lemma db_case_lt W T F b x y :
  Erel 3 W (db_Θ x y) T F (subst (db_γ b) db_case) →
  if b then w_lt W y x else w_lt W x y.
Proof.
  intros HE. rewrite db_case_subst in HE. destruct b.
  - ebeta HE ltac:(by apply HeadCase2). change (subst1 EUnit (LetU (Var 0) (cc2 chd chc)))
      with (LetU EUnit (cc2 chd chc)) in HE.
    ebeta HE ltac:(apply HeadLetU).
    apply Erel_S_iff in HE as (_ & HR & _).
    rewrite db_Θ_swap in HR. apply (cc2_ready W F chd chc y x); [done|]. apply HR.
    intros Hirr. apply (Hirr _ _ (cc2_can _ _)).
  - ebeta HE ltac:(by apply HeadCase1). change (subst1 EUnit (LetU (Var 0) (cc2 chc chd)))
      with (LetU EUnit (cc2 chc chd)) in HE.
    ebeta HE ltac:(apply HeadLetU).
    apply Erel_S_iff in HE as (_ & HR & _).
    apply (cc2_ready W F chc chd x y); [done|]. apply HR.
    intros Hirr. apply (Hirr _ _ (cc2_can _ _)).
Qed.

Theorem db_component_unrealizable Φ Ψ F T x y k :
  styped Φ Ψ (db_ctx x y k) F db_case T → ¬ realizable Φ Ψ.
Proof.
  intros Hs (W & σ & ρ & HWs & Hρ & HΨ).
  pose proof (proj1 HWs) as HW.
  pose proof (styped_typed W _ _ _ _ _ _ Hs) as Ht.
  pose proof (typed_sem_rules _ _ _ _ _ _ _ _ Ht W ρ σ HW (wext_refl _ HWs) Hρ HΨ) as Hr.
  apply sem_rules_fundamental in Hr; [|done].
  rewrite tenv_pinst_empty in Hr.
  assert (∀ b, Erel 3 W (db_Θ (pt_inst σ x) (pt_inst σ y)) (pinst_ty σ T)
                 (sf_inst ρ (sf_pinst σ F)) (subst (db_γ b) db_case)) as HE.
  { intros b. apply (Hr 3 W (db_Θ (pt_inst σ x) (pt_inst σ y)) (db_Θ (pt_inst σ x) (pt_inst σ y)) (db_γ b)).
    - apply wext_refl, HWs.
    - apply tenv_comp_empty_l, (wf_eq_sym _ HW).
    - unfold db_ctx, lenv_pinst. rewrite fmap_app, fmap_replicate. cbn.
      apply db_ground, HW. }
  pose proof (db_case_lt _ _ _ true _ _ (HE true)) as H1.
  pose proof (db_case_lt _ _ _ false _ _ (HE false)) as H2.
  apply (proj2 HWs (pt_inst σ x)). exact (wf_lt_trans _ HW _ _ _ H2 H1).
Qed.

(** The same node with a bit whose sides carry facts C₁ and C₂. It has
    no derivation when one strict world realizes the hypotheses, C₁ and
    C₂ together. So a derivation needs the two sides not to be
    realizable together with the hypotheses. [db_typed] makes one side
    unrealizable. *)

Definition db_ctx2 (C1 C2 : bcs) (x y : point) (k : nat) : lenv :=
  [None; Some (TSum (TEx LNone 0 C1 TUnit) (TEx LNone 0 C2 TUnit)); None;
   Some (TSess SEnd y); None; None; None; Some (TSess SEnd x)] ++ replicate k None.

Definition realizable2 (Φ : fhyps) (Ψ : hyps) (C1 C2 : bcs) : Prop :=
  ∃ W σ ρ, strict W ∧ inst_ok W (fhyps_pinst σ Φ) ρ ∧
    hyps_hold (w_eq W) (w_lt W) (pt_known W) (hyps_inst σ Ψ) ∧
    bcs_hold (w_eq W) (w_lt W) (bcs_inst σ C1) [] ∧
    bcs_hold (w_eq W) (w_lt W) (bcs_inst σ C2) [].

Lemma tenv_heads_nil : tenv_heads ∅ = ∅.
Proof. unfold tenv_heads. by rewrite map_fold_empty. Qed.

Lemma db_ground2 n W b C1 C2 x y k :
  world_wf W → bcs_hold (w_eq W) (w_lt W) C1 [] → bcs_hold (w_eq W) (w_lt W) C2 [] →
  grounding n W (db_Θ x y)
    ([None; Some (TSum (TEx LNone 0 C1 TUnit) (TEx LNone 0 C2 TUnit)); None;
      Some (TSess SEnd y); None; None; None; Some (TSess SEnd x)] ++ replicate k None) (db_γ b).
Proof.
  intros HW H1 H2. cbn [grounding app].
  exists ∅, (db_Θ x y). split; [apply tenv_comp_empty_l, (wf_eq_sym _ HW)|]. split.
  { apply Vrel_sum_iff. destruct b; [right|left]; eexists; (split; [done|]);
      apply Vrel_ex_iff; (split; [rewrite tenv_heads_nil; by split|]);
      exists []; split_and!; first [done|by apply Forall_nil|by apply Vrel_unit_iff]. }
  exists {[chd := One (SEnd, y)]}, {[chc := One (SEnd, x)]}. split; [apply db_comp_cd|]. split.
  { apply Vrel_sess_iff. eexists _, _, _. split_and!; [done|done|apply seq_refl|apply (wf_eq_refl _ HW)]. }
  exists {[chc := One (SEnd, x)]}, ∅. split; [apply tenv_comp_empty_r|]. split.
  { apply Vrel_sess_iff. eexists _, _, _. split_and!; [done|done|apply seq_refl|apply (wf_eq_refl _ HW)]. }
  apply grounding_nones.
Qed.

Theorem db_component_sides Φ Ψ F T x y k C1 C2 :
  styped Φ Ψ (db_ctx2 C1 C2 x y k) F db_case T → ¬ realizable2 Φ Ψ C1 C2.
Proof.
  intros Hs (W & σ & ρ & HWs & Hρ & HΨ & H1 & H2).
  pose proof (proj1 HWs) as HW.
  pose proof (styped_typed W _ _ _ _ _ _ Hs) as Ht.
  pose proof (typed_sem_rules _ _ _ _ _ _ _ _ Ht W ρ σ HW (wext_refl _ HWs) Hρ HΨ) as Hr.
  apply sem_rules_fundamental in Hr; [|done].
  rewrite tenv_pinst_empty in Hr.
  assert (∀ b, Erel 3 W (db_Θ (pt_inst σ x) (pt_inst σ y)) (pinst_ty σ T)
                 (sf_inst ρ (sf_pinst σ F)) (subst (db_γ b) db_case)) as HE.
  { intros b. apply (Hr 3 W (db_Θ (pt_inst σ x) (pt_inst σ y)) (db_Θ (pt_inst σ x) (pt_inst σ y)) (db_γ b)).
    - apply wext_refl, HWs.
    - apply tenv_comp_empty_l, (wf_eq_sym _ HW).
    - unfold db_ctx2, lenv_pinst. rewrite fmap_app, fmap_replicate. cbn.
      by apply db_ground2. }
  pose proof (db_case_lt _ _ _ true _ _ (HE true)) as Hl1.
  pose proof (db_case_lt _ _ _ false _ _ (HE false)) as Hl2.
  apply (proj2 HWs (pt_inst σ x)). exact (wf_lt_trans _ HW _ _ _ Hl2 Hl1).
Qed.

(** The hypotheses of a source program are realizable. A program
    starts under a creation constraint C₀ over n top-level points, and
    the world wc0 n C₀ realizes it ([soundness_source]). So the case
    node of db_main does not type at any context the program starts
    in, for every choice of the points of c and d. *)
Corollary db_component_untyped_top n C0 F T x y k :
  creation_ok n nofact nofact (λ _, False) C0 →
  ¬ styped ∅ [(C0, ids n)] (db_ctx x y k) F db_case T.
Proof.
  intros HC Hs. apply c0_creation_ok in HC.
  apply (db_component_unrealizable _ _ _ _ _ _ _ Hs).
  exists (wc0 n C0), (plist (c0_consts n)), (λ _, ∅). split_and!.
  - by apply wc0_strict.
  - intros φ u. unfold fhyps_pinst. by rewrite fmap_empty, lookup_empty.
  - by apply wc0_holds.
Qed.

(** ** db_main types, and the dead branch learns a fact from the bit

    The receiver types the bit at ∗ ⊕ ∃{z[0]+5 ≺ z[0]+1}.∗ (for b =
    false), where z is the point of the receive on e and z[0] its first
    payload point. The second side of the sum has no value in a strict
    world, and the sender never builds it. E-Open in the inr branch adds
    z[0]+5 ≺ z[0]+1 to the hypotheses, and with the creation constraints
    that give d below z[0]+5 and c above z[0]+1 it derives y ≺ x, the
    order the inr branch needs. The inl branch reads x ≺ y from the
    creation constraint of d. So one world (the facts of the three
    creation constraints) types both branches, and the hypotheses of the
    dead branch are not realizable. The creation constraint of e states
    z+1 ≺ z[0]+5, so that c and d can be created between z+1 and the
    payload points. For b = true the roles of the two sides swap. *)

(** ι[0] + k *)
Definition sl0 (a k : nat) : point := Pt (NPayload (NVar a) 0 0) k.

Definition Ce : bcs := BCs [] (λ g, g = FLt (pv 0 1) (sl0 0 5)).
Definition Cdead : bcs := BCs [pvar 0] (λ g, g = FLt (pv 0 5) (pv 0 1)).
Definition Tz : ty := TSum TUnit (TEx LNone 0 Cdead TUnit).
Definition Se : sty := SSeq (SRcv 1 Tz) SEnd.
Definition Tz_t : ty := TSum (TEx LNone 0 Cdead TUnit) TUnit.
Definition Se_t : sty := SSeq (SRcv 1 Tz_t) SEnd.

Definition rkv (x : point) : nat :=
  2 * pt_off x + match pt_name x with NVar _ => 0 | _ => 1 end.

Lemma Ce_ok peq plt : cc_ok peq plt Ce.
Proof.
  apply (cc_ok_inner peq plt _ (λ x y, rkv x < rkv y)); [intros; lia|intros; lia| |].
  - intros x _. unfold rkv, pt_shift. simpl. destruct (pt_name x); lia.
  - intros g -> _. eexists _, _. split; [done|]. cbn. lia.
Qed.

Lemma sl_fresh_l W Ψ L H x l : (fresh_bcs L H, [x]) ∈ Ψ → l ∈ L → slt W Ψ l x.
Proof.
  intros Hg Hl. apply sl_h. exists (fresh_bcs L H), [x]. split; [done|].
  apply fresh_open. left. by exists l.
Qed.

Lemma sl_fresh_r W Ψ L H x h : (fresh_bcs L H, [x]) ∈ Ψ → h ∈ H → slt W Ψ x h.
Proof.
  intros Hg Hh. apply sl_h. exists (fresh_bcs L H), [x]. split; [done|].
  apply fresh_open. right. by exists h.
Qed.

Lemma db_typed_false : styped ∅ [] [] (∅, None) (db_main false) TUnit.
Proof.
  apply styped_Wpo. pose proof Wpo_nil_strict' as HWs. pose proof (proj1 HWs) as HW.
  set (W := Wpo []) in *. unfold db_main, let_new_pair.
  apply (t_new_open W _ _ ∅ _ _ _ _ Se Ce); [apply Ce_ok|constructor|].
  fresh_clean.
  apply (t_newfresh_lh_open W _ _ ∅ _ _ _ _ SEnd [pv 0 1; sl0 0 1] [sl0 0 5]).
  { cbn. repeat (apply Forall_cons; split); try (apply Forall_nil; done);
      (eapply skn_inst; [by left|by left|done]). }
  { intros l h Hl Hh. apply list_elem_of_singleton in Hh as ->.
    rewrite elem_of_cons, list_elem_of_singleton in Hl. destruct Hl as [->| ->].
    - hyp0 (pv 0 1) (sl0 0 5).
    - apply slt_po_lt; [exact HW|lia]. }
  fresh_clean.
  apply (t_newfresh_lh_open W _ _ ∅ _ _ _ _ SEnd [pv 1 1; pvar 0] [sl0 1 5]).
  { cbn. repeat (apply Forall_cons; split); try (apply Forall_nil; done).
    - eapply skn_inst; [by left|by left|done].
    - eapply skn_inst; [by right; left|by left|done].
    - eapply skn_inst; [by left|by left|done]. }
  { intros l h Hl Hh. apply list_elem_of_singleton in Hh as ->.
    rewrite elem_of_cons, list_elem_of_singleton in Hl. destruct Hl as [->| ->].
    - hyp0 (pv 0 1) (sl0 0 5).
    - apply (slt_fresh_r W _ (pshift 1) [pv 0 1; sl0 0 1] [sl0 0 5] (pvar 0) (sl0 0 5));
        [by right; left|by left]. }
  fresh_clean.
  rewrite !bcs_inst_fresh.
  change (pt_inst (pshift 1) (pt_inst (pshift 1) (pvar 0))) with (pvar 2).
  change (pt_inst (pshift 1) (pvar 0)) with (pvar 1).
  change (bcs_inst (pshift 1) (bcs_inst (pshift 1) (bcs_inst (pshift 1) Ce))) with Ce.
  cbn [fmap list_fmap].
  change (pt_inst (pshift 1) (pt_inst (pshift 1) (pv 0 1))) with (pv 2 1).
  change (pt_inst (pshift 1) (pt_inst (pshift 1) (sl0 0 1))) with (sl0 2 1).
  change (pt_inst (pshift 1) (pt_inst (pshift 1) (sl0 0 5))) with (sl0 2 5).
  change (pt_inst (pshift 1) (pv 1 1)) with (pv 2 1).
  change (pt_inst (pshift 1) (pvar 0)) with (pvar 1).
  change (pt_inst (pshift 1) (sl0 1 5)) with (sl0 2 5).
  set (Ψ := [(Ce, [pvar 2]); (fresh_bcs [pv 2 1; sl0 2 1] [sl0 2 5], [pvar 1]);
             (fresh_bcs [pv 2 1; pvar 1] [sl0 2 5], [pvar 0])]).
  assert (slt W Ψ (pv 2 1) (pvar 1)) as Hz1x.
  { apply (sl_fresh_l _ _ [pv 2 1; sl0 2 1] [sl0 2 5]); [by right; left|by left]. }
  assert (slt W Ψ (pv 2 1) (pvar 0)) as Hz1y.
  { apply (sl_fresh_l _ _ [pv 2 1; pvar 1] [sl0 2 5]); [by right; right; left|by left]. }
  assert (slt W Ψ (pvar 1) (pvar 0)) as Hxy.
  { apply (sl_fresh_l _ _ [pv 2 1; pvar 1] [sl0 2 5]); [by right; right; left|by right; left]. }
  assert (slt W Ψ (pvar 2) (pvar 1)) as Hzx.
  { eapply sl_trans; [apply (slt_po W _ (pvar 2) HW)|exact Hz1x]. }
  assert (slt W Ψ (pvar 2) (pvar 0)) as Hzy.
  { eapply sl_trans; [apply (slt_po W _ (pvar 2) HW)|exact Hz1y]. }
  tstep.
  { (* spawn (λu. let () = u in close c′) *)
    tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pvar 1)) (Some (pvar 1)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep; [tstep|]. cbn. tstep; [tstep|apply KTClos|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (pvar 1). split; [by rewrite lookup_insert_eq|apply sle_refl, HW]. }
  cbn. tstep.
  { (* spawn (λu. let () = u in close d′) *)
    tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pvar 0)) (Some (pvar 0)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep; [tstep|]. cbn. tstep; [tstep|apply KTClos|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (pvar 0). split; [by rewrite lookup_insert_eq|apply sle_refl, HW]. }
  cbn. tstep.
  { (* spawn the sender of inl ∗ *)
    tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pv 2 1)) (Some (pvar 2)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep; [tstep|]. cbn. tstep.
    - tstep; [|apply (KTSend _ _ _ 1 Tz SEnd (pvar 2)); cbn; set_solver|cbn; repeat split; apply Forall_singleton; intros ? Hv; injection Hv; lia|].
      + tstep; first [tstep|cbn; apply t_inj1, (tv_unit W HW); reflexivity].
      + apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pv 2 1). split; [done|]. right. apply (slt_po W _ (pvar 2) HW).
    - apply KTClos.
    - done.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 2 1). split; [done|]. apply sle_refl, HW. }
  cbn. eapply (tv_letp W HW _ _ _ _ _ _ (payload_at 1 Tz (pvar 2)) (TSess SEnd (pv 2 1)));
    [reflexivity| |].
  { tstep; [tstep|apply KTRecv|cbn; repeat split; apply Forall_singleton; intros ? Hv; injection Hv; lia|].
    apply ubs_intro; [intros y Hy; mem_cases Hy; done|done]. }
  cbn. tstep.
  { tstep; [tstep|apply KTClos|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy; done|done]. }
  cbn. set (Cd := bcs_inst (plist [pt_payload (pvar 2) 0]) Cdead).
  eapply (tv_case W _ _ _ _ _ _ _ TUnit (TEx LNone 0 Cd TUnit) TUnit); [exact HW|reflexivity|tstep| |].
  - (* inl closes c, then d *)
    cbn. tstep; [tstep|]. cbn. tstep.
    + tstep; [tstep|apply KTClos|done|].
      apply ubs_intro; [intros y Hy; mem_cases Hy; done|done].
    + tstep; [tstep|apply KTClos|done|].
      apply ubs_intro; [intros y Hy; mem_cases Hy|done].
  - (* inr opens the payload, which states z[0]+5 ≺ z[0]+1 *)
    cbn. apply (t_open W _ _ _ _ _ _ 0 LNone 0 Cd TUnit TUnit); [done|intros Hu; exact Hu|].
    replace (hyps_inst (pshift 0) Ψ) with Ψ by reflexivity.
    rewrite fhyps_pinst_empty, tenv_pinst_empty, sf_pinst_none.
    change (pinst_ty (pshift 0) TUnit) with TUnit.
    replace (lenv_pinst (pshift 0) _) with
      [Some (TEx LNone 0 Cd TUnit); None; None; None;
           Some (TSess SEnd (pvar 0)); None; None; None;
           Some (TSess SEnd (pvar 1)); None; None; None; None; None; None] by reflexivity.
    cbn [insert list_insert].
    set (Ψ' := Ψ ++ [(bcs_inst (pshift 0) Cd, ids 0)]).
    assert (slt W Ψ' (sl0 2 5) (sl0 2 1)) as Hdead.
    { apply sl_h. exists (bcs_inst (pshift 0) Cd), []. split.
      { unfold Ψ'. apply elem_of_app. right. by left. }
      exists (FLt (sl0 2 5) (sl0 2 1)). split; [|reflexivity].
      exists (FLt (pv 0 5) (pv 0 1)). split_and!; [done| |reflexivity].
      cbn. lia. }
    assert (slt W Ψ' (pvar 0) (pvar 1)) as Hyx.
    { eapply sl_trans.
      { apply (sl_fresh_r _ _ [pv 2 1; pvar 1] [sl0 2 5]); [|by left].
        apply elem_of_app. left. by right; right; left. }
      eapply sl_trans; [exact Hdead|].
      apply (sl_fresh_l _ _ [pv 2 1; sl0 2 1] [sl0 2 5]); [|by right; left].
      apply elem_of_app. left. by right; left. }
    tstep; [tstep|]. cbn. tstep.
    + tstep; [tstep|apply KTClos|done|].
      apply ubs_intro; [intros y Hy; mem_cases Hy; done|done].
    + tstep; [tstep|apply KTClos|done|].
      apply ubs_intro; [intros y Hy; mem_cases Hy|done].
Qed.

Lemma db_typed_true : styped ∅ [] [] (∅, None) (db_main true) TUnit.
Proof.
  apply styped_Wpo. pose proof Wpo_nil_strict' as HWs. pose proof (proj1 HWs) as HW.
  set (W := Wpo []) in *. unfold db_main, let_new_pair.
  apply (t_new_open W _ _ ∅ _ _ _ _ Se_t Ce); [apply Ce_ok|constructor|].
  fresh_clean.
  apply (t_newfresh_lh_open W _ _ ∅ _ _ _ _ SEnd [pv 0 1; sl0 0 1] [sl0 0 5]).
  { cbn. repeat (apply Forall_cons; split); try (apply Forall_nil; done);
      (eapply skn_inst; [by left|by left|done]). }
  { intros l h Hl Hh. apply list_elem_of_singleton in Hh as ->.
    rewrite elem_of_cons, list_elem_of_singleton in Hl. destruct Hl as [->| ->].
    - hyp0 (pv 0 1) (sl0 0 5).
    - apply slt_po_lt; [exact HW|lia]. }
  fresh_clean.
  apply (t_newfresh_lh_open W _ _ ∅ _ _ _ _ SEnd [pv 1 1; sl0 1 1] [pvar 0; sl0 1 5]).
  { cbn. repeat (apply Forall_cons; split); try (apply Forall_nil; done).
    - eapply skn_inst; [by left|by left|done].
    - eapply skn_inst; [by left|by left|done].
    - eapply skn_inst; [by right; left|by left|done].
    - eapply skn_inst; [by left|by left|done]. }
  { intros l h Hl Hh.
    rewrite elem_of_cons, list_elem_of_singleton in Hl, Hh.
    destruct Hl as [->| ->], Hh as [->| ->].
    - apply (slt_fresh_l W _ (pshift 1) [pv 0 1; sl0 0 1] [sl0 0 5] (pvar 0) (pv 0 1));
        [by right; left|by left].
    - hyp0 (pv 0 1) (sl0 0 5).
    - apply (slt_fresh_l W _ (pshift 1) [pv 0 1; sl0 0 1] [sl0 0 5] (pvar 0) (sl0 0 1));
        [by right; left|by right; left].
    - apply slt_po_lt; [exact HW|lia]. }
  fresh_clean.
  rewrite !bcs_inst_fresh.
  change (pt_inst (pshift 1) (pt_inst (pshift 1) (pvar 0))) with (pvar 2).
  change (pt_inst (pshift 1) (pvar 0)) with (pvar 1).
  change (bcs_inst (pshift 1) (bcs_inst (pshift 1) (bcs_inst (pshift 1) Ce))) with Ce.
  cbn [fmap list_fmap].
  change (pt_inst (pshift 1) (pt_inst (pshift 1) (pv 0 1))) with (pv 2 1).
  change (pt_inst (pshift 1) (pt_inst (pshift 1) (sl0 0 1))) with (sl0 2 1).
  change (pt_inst (pshift 1) (pt_inst (pshift 1) (sl0 0 5))) with (sl0 2 5).
  change (pt_inst (pshift 1) (pv 1 1)) with (pv 2 1).
  change (pt_inst (pshift 1) (sl0 1 1)) with (sl0 2 1).
  change (pt_inst (pshift 1) (pvar 0)) with (pvar 1).
  change (pt_inst (pshift 1) (sl0 1 5)) with (sl0 2 5).
  set (Ψ := [(Ce, [pvar 2]); (fresh_bcs [pv 2 1; sl0 2 1] [sl0 2 5], [pvar 1]);
             (fresh_bcs [pv 2 1; sl0 2 1] [pvar 1; sl0 2 5], [pvar 0])]).
  assert (slt W Ψ (pv 2 1) (pvar 1)) as Hz1x.
  { apply (sl_fresh_l _ _ [pv 2 1; sl0 2 1] [sl0 2 5]); [by right; left|by left]. }
  assert (slt W Ψ (pv 2 1) (pvar 0)) as Hz1y.
  { apply (sl_fresh_l _ _ [pv 2 1; sl0 2 1] [pvar 1; sl0 2 5]); [by right; right; left|by left]. }
  assert (slt W Ψ (pvar 0) (pvar 1)) as Hyx.
  { apply (sl_fresh_r _ _ [pv 2 1; sl0 2 1] [pvar 1; sl0 2 5]); [by right; right; left|by left]. }
  assert (slt W Ψ (pvar 2) (pvar 1)) as Hzx.
  { eapply sl_trans; [apply (slt_po W _ (pvar 2) HW)|exact Hz1x]. }
  assert (slt W Ψ (pvar 2) (pvar 0)) as Hzy.
  { eapply sl_trans; [apply (slt_po W _ (pvar 2) HW)|exact Hz1y]. }
  tstep.
  { (* spawn (λu. let () = u in close c′) *)
    tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pvar 1)) (Some (pvar 1)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep; [tstep|]. cbn. tstep; [tstep|apply KTClos|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (pvar 1). split; [by rewrite lookup_insert_eq|apply sle_refl, HW]. }
  cbn. tstep.
  { (* spawn (λu. let () = u in close d′) *)
    tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pvar 0)) (Some (pvar 0)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep; [tstep|]. cbn. tstep; [tstep|apply KTClos|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (pvar 0). split; [by rewrite lookup_insert_eq|apply sle_refl, HW]. }
  cbn. tstep.
  { (* spawn the sender of inr ∗ *)
    tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pv 2 1)) (Some (pvar 2)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep; [tstep|]. cbn. tstep.
    - tstep; [|apply (KTSend _ _ _ 1 Tz_t SEnd (pvar 2)); cbn; set_solver|cbn; repeat split; apply Forall_singleton; intros ? Hv; injection Hv; lia|].
      + tstep; first [tstep|cbn; apply t_inj2, (tv_unit W HW); reflexivity].
      + apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pv 2 1). split; [done|]. right. apply (slt_po W _ (pvar 2) HW).
    - apply KTClos.
    - done.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pv 2 1). split; [done|]. apply sle_refl, HW. }
  cbn. eapply (tv_letp W HW _ _ _ _ _ _ (payload_at 1 Tz_t (pvar 2)) (TSess SEnd (pv 2 1)));
    [reflexivity| |].
  { tstep; [tstep|apply KTRecv|cbn; repeat split; apply Forall_singleton; intros ? Hv; injection Hv; lia|].
    apply ubs_intro; [intros y Hy; mem_cases Hy; done|done]. }
  cbn. tstep.
  { tstep; [tstep|apply KTClos|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy; done|done]. }
  cbn. set (Cd := bcs_inst (plist [pt_payload (pvar 2) 0]) Cdead).
  eapply (tv_case W _ _ _ _ _ _ _ (TEx LNone 0 Cd TUnit) TUnit TUnit); [exact HW|reflexivity|tstep| |].
  - (* inl opens the payload, which states z[0]+5 ≺ z[0]+1 *)
    cbn. apply (t_open W _ _ _ _ _ _ 0 LNone 0 Cd TUnit TUnit); [done|intros Hu; exact Hu|].
    replace (hyps_inst (pshift 0) Ψ) with Ψ by reflexivity.
    rewrite fhyps_pinst_empty, tenv_pinst_empty, sf_pinst_none.
    change (pinst_ty (pshift 0) TUnit) with TUnit.
    replace (lenv_pinst (pshift 0) _) with
      [Some (TEx LNone 0 Cd TUnit); None; None; None;
           Some (TSess SEnd (pvar 0)); None; None; None;
           Some (TSess SEnd (pvar 1)); None; None; None; None; None; None] by reflexivity.
    cbn [insert list_insert].
    set (Ψ' := Ψ ++ [(bcs_inst (pshift 0) Cd, ids 0)]).
    assert (slt W Ψ' (sl0 2 5) (sl0 2 1)) as Hdead.
    { apply sl_h. exists (bcs_inst (pshift 0) Cd), []. split.
      { unfold Ψ'. apply elem_of_app. right. by left. }
      exists (FLt (sl0 2 5) (sl0 2 1)). split; [|reflexivity].
      exists (FLt (pv 0 5) (pv 0 1)). split_and!; [done| |reflexivity].
      cbn. lia. }
    assert (slt W Ψ' (pvar 1) (pvar 0)) as Hxy.
    { eapply sl_trans.
      { apply (sl_fresh_r _ _ [pv 2 1; sl0 2 1] [sl0 2 5]); [|by left].
        apply elem_of_app. left. by right; left. }
      eapply sl_trans; [exact Hdead|].
      apply (sl_fresh_l _ _ [pv 2 1; sl0 2 1] [pvar 1; sl0 2 5]); [|by right; left].
      apply elem_of_app. left. by right; right; left. }
    tstep; [tstep|]. cbn. tstep.
    + tstep; [tstep|apply KTClos|done|].
      apply ubs_intro; [intros y Hy; mem_cases Hy; done|done].
    + tstep; [tstep|apply KTClos|done|].
      apply ubs_intro; [intros y Hy; mem_cases Hy|done].
  - (* inr closes d, then c *)
    cbn. tstep; [tstep|]. cbn. tstep.
    + tstep; [tstep|apply KTClos|done|].
      apply ubs_intro; [intros y Hy; mem_cases Hy; done|done].
    + tstep; [tstep|apply KTClos|done|].
      apply ubs_intro; [intros y Hy; mem_cases Hy|done].
Qed.

Theorem db_typed b : styped ∅ [] [] (∅, None) (db_main b) TUnit.
Proof. destruct b; [apply db_typed_true|apply db_typed_false]. Qed.

(** Deadlock freedom for both bits, from [soundness]. *)
Theorem db_deadlock_free b : deadlock_free (∅, {[+ db_main b +]}).
Proof.
  apply (soundness (Wpo []) _ TUnit (Wpo_strict _)).
  apply ptyped_closed_s; [constructor|apply db_typed].
Qed.

(** ** The receiving component with a fact-free session type

    The same limit with the channel in the interface instead of the
    bit. db_rnode is the receive of db_main with what follows it, in the
    context the derivation of db_main reaches it with: d at 1, c at 5
    and e at 9, where e has the session type ?(∗ ⊕ ∗).Close. O-Recv of
    the relation quantifies over every payload in V⟦∗ ⊕ ∗⟧, so both
    bits reach the case in the same world. *)

Definition Se0 : sty := SSeq (SRcv 0 (TSum TUnit TUnit)) SEnd.

Definition db_rnode : expr := LetP (App ERecv (Var 9)) (LetU (App EClos (Var 0)) db_case).

Definition db_rctx (x y z : point) (k : nat) : lenv :=
  [None; Some (TSess SEnd y); None; None; None; Some (TSess SEnd x); None; None; None;
   Some (TSess Se0 z)] ++ replicate k None.

Definition che : chan := "e".

Definition db_Θ3 (x y z : point) : tenv :=
  <[chd := One (SEnd, y)]> (<[chc := One (SEnd, x)]> {[che := One (Se0, z)]}).

Definition db_ρ : nat → expr :=
  λ i, match i with 1 => Chan chd | 5 => Chan chc | 9 => Chan che | _ => EUnit end.

Lemma tenv_comp_insert1 R Θ c a :
  Θ !! c = None → tenv_comp R (<[c := One a]> Θ) {[c := One a]} Θ.
Proof.
  intros Hc. split.
  - intros c'. destruct (decide (c' = c)) as [->|Hne].
    + rewrite lookup_insert_eq, lookup_singleton_eq, Hc. constructor.
    + rewrite lookup_insert_ne, lookup_singleton_ne by done. destruct (Θ !! c'); constructor.
  - intros c' e1 e2 H1 H2. apply lookup_singleton_Some in H1 as [<- _]. congruence.
Qed.

Lemma db_rground n W x y z k :
  world_wf W →
  grounding n W (db_Θ3 x y z)
    ([None; Some (TSess SEnd y); None; None; None; Some (TSess SEnd x); None; None; None;
      Some (TSess Se0 z)] ++ replicate k None) db_ρ.
Proof.
  intros HW. cbn [grounding app].
  exists {[chd := One (SEnd, y)]}, (<[chc := One (SEnd, x)]> {[che := One (Se0, z)]}).
  split; [apply tenv_comp_insert1; by rewrite lookup_insert_ne, lookup_singleton_ne|]. split.
  { apply Vrel_sess_iff. eexists _, _, _. split_and!; [done|done|apply seq_refl|apply (wf_eq_refl _ HW)]. }
  exists {[chc := One (SEnd, x)]}, {[che := One (Se0, z)]}.
  split; [apply tenv_comp_insert1; by rewrite lookup_singleton_ne|]. split.
  { apply Vrel_sess_iff. eexists _, _, _. split_and!; [done|done|apply seq_refl|apply (wf_eq_refl _ HW)]. }
  exists {[che := One (Se0, z)]}, ∅. split; [apply tenv_comp_empty_r|]. split.
  { apply Vrel_sess_iff. eexists _, _, _. split_and!; [done|done|apply seq_refl|apply (wf_eq_refl _ HW)]. }
  apply grounding_nones.
Qed.

(** The head of an environment with one end of c. *)
Lemma tenv_hd_one Θ c u k Θ1 s k' :
  tenv_hd Θ c u k Θ1 → Θ !! c = Some (One (s, k')) →
  Θ1 = delete c Θ ∧ k = k' ∧ unfoldS s = u.
Proof.
  intros (s0 & [[Hn ->]|(e' & He' & [-> | ->])] & Hu) Hc.
  - rewrite lookup_insert_eq in Hc. injection Hc as -> ->.
    split_and!; [|done|done]. by rewrite delete_insert_eq, delete_id.
  - by rewrite lookup_insert_eq in Hc.
  - by rewrite lookup_insert_eq in Hc.
Qed.

Lemma db_Θ3_e x y z : db_Θ3 x y z !! che = Some (One (Se0, z)).
Proof. unfold db_Θ3. by rewrite !lookup_insert_ne, lookup_singleton_eq. Qed.

Lemma db_Θ3_del x y z : delete che (db_Θ3 x y z) = db_Θ x y.
Proof.
  unfold db_Θ3, db_Θ. apply map_eq. intros c.
  destruct (decide (c = che)) as [->|He].
  - rewrite lookup_delete_eq, !lookup_insert_ne, lookup_singleton_ne by done. done.
  - rewrite lookup_delete_ne by done.
    destruct (decide (c = chd)) as [->|Hd]; [by rewrite !lookup_insert_eq|].
    rewrite !(lookup_insert_ne _ chd) by done.
    destruct (decide (c = chc)) as [->|Hc]; [by rewrite lookup_insert_eq, lookup_singleton_eq|].
    by rewrite lookup_insert_ne, !lookup_singleton_ne.
Qed.

Lemma db_rnode_subst :
  subst db_ρ db_rnode =
    LetP (App ERecv (Chan che)) (subst (up (up db_ρ)) (LetU (App EClos (Var 0)) db_case)).
Proof. done. Qed.

Lemma db_rnode_body b :
  subst2 (bit b) (Chan che) (subst (up (up db_ρ)) (LetU (App EClos (Var 0)) db_case)) =
    LetU (App EClos (Chan che)) (subst (db_γ b) db_case).
Proof. by destruct b. Qed.

Lemma db_rnode_lt W T F (b : bool) x y z :
  strict W →
  Erel 6 W (db_Θ3 x y z) T F (subst db_ρ db_rnode) →
  if b then w_lt W y x else w_lt W x y.
Proof.
  intros HWs HE. rewrite db_rnode_subst in HE.
  (* the receive, at the payload bit b *)
  eapply Erel_S_step in HE;
    [|apply TStepLetP, TStepHead, (HeadRecv che (bit b)); by destruct b].
  cbn [Ecase_gen Eobl] in HE. destruct HE as (Θ1 & m & U & s & k & Hhd & HE).
  destruct (tenv_hd_one _ _ _ _ _ _ _ Hhd (db_Θ3_e x y z)) as (-> & -> & Hu).
  rewrite db_Θ3_del in HE. cbn in Hu. injection Hu as <- <- <-.
  assert (db_Θ x y !! che = None) as Hn.
  { unfold db_Θ. by rewrite lookup_insert_ne, lookup_singleton_ne. }
  set (Θe := <[che := One (SEnd, pt_shift 1 z)]> (db_Θ x y)).
  pose proof (HE W 5 ∅ Θe Θe) as HE'. clear HE. rename HE' into HE.
  specialize (HE (wext_refl _ HWs)). specialize (HE ltac:(cbn; lia)).
  specialize (HE ltac:(left; by split)). specialize (HE (tenv_comp_empty_r _ _)).
  assert (Vrel 5 W ∅ (payload_at 0 (TSum TUnit TUnit) z) (bit b)) as Hv.
  { apply Vrel_sum_iff. destruct b; [right|left]; eexists; (split; [done|]); by apply Vrel_unit_iff. }
  specialize (HE Hv).
  (* the β step of the pair *)
  eapply Erel_S_step in HE; [|apply TStepHead, HeadLetP; [by destruct b|done]].
  cbn [Ecase_gen Eobl at_cost tcost nlower pred] in HE. rewrite db_rnode_body in HE.
  (* the close of e, a giving step at the same index *)
  eapply Erel_S_step in HE; [|apply TStepLetU, TStepHead, HeadClos].
  cbn [Ecase_gen Eobl at_cost tcost scost] in HE. destruct HE as (Θ2 & k2 & Hhd2 & HE).
  destruct (tenv_hd_one _ _ _ _ _ _ _ Hhd2 (lookup_insert_eq _ _ _)) as (-> & _ & _).
  unfold Θe in HE. rewrite delete_insert_eq, delete_id in HE by done.
  (* the β step of let () *)
  eapply Erel_S_step in HE; [|apply TStepHead, HeadLetU].
  cbn [Ecase_gen Eobl at_cost tcost nlower pred] in HE.
  by apply (db_case_lt W T F b x y).
Qed.

Theorem db_rnode_unrealizable Φ Ψ F T x y z k :
  styped Φ Ψ (db_rctx x y z k) F db_rnode T → ¬ realizable Φ Ψ.
Proof.
  intros Hs (W & σ & ρ & HWs & Hρ & HΨ).
  pose proof (proj1 HWs) as HW.
  pose proof (styped_typed W _ _ _ _ _ _ Hs) as Ht.
  pose proof (typed_sem_rules _ _ _ _ _ _ _ _ Ht W ρ σ HW (wext_refl _ HWs) Hρ HΨ) as Hr.
  apply sem_rules_fundamental in Hr; [|done].
  rewrite tenv_pinst_empty in Hr.
  set (Θ := db_Θ3 (pt_inst σ x) (pt_inst σ y) (pt_inst σ z)).
  assert (Erel 6 W Θ (pinst_ty σ T) (sf_inst ρ (sf_pinst σ F)) (subst db_ρ db_rnode)) as HE.
  { apply (Hr 6 W Θ Θ db_ρ).
    - apply wext_refl, HWs.
    - apply tenv_comp_empty_l, (wf_eq_sym _ HW).
    - unfold db_rctx, lenv_pinst. rewrite fmap_app, fmap_replicate. cbn.
      apply db_rground, HW. }
  pose proof (db_rnode_lt _ _ _ true _ _ _ HWs HE) as H1.
  pose proof (db_rnode_lt _ _ _ false _ _ _ HWs HE) as H2.
  apply (proj2 HWs (pt_inst σ x)). exact (wf_lt_trans _ HW _ _ _ H2 H1).
Qed.

Corollary db_rnode_untyped_top n C0 F T x y z k :
  creation_ok n nofact nofact (λ _, False) C0 →
  ¬ styped ∅ [(C0, ids n)] (db_rctx x y z k) F db_rnode T.
Proof.
  intros HC Hs. apply c0_creation_ok in HC.
  apply (db_rnode_unrealizable _ _ _ _ _ _ _ _ Hs).
  exists (wc0 n C0), (plist (c0_consts n)), (λ _, ∅). split_and!.
  - by apply wc0_strict.
  - intros φ u. unfold fhyps_pinst. by rewrite fmap_empty, lookup_empty.
  - by apply wc0_holds.
Qed.

(** db_rnode is the tail of db_main after the three lets of new and the
    three spawns. *)
Lemma db_main_shape b :
  db_main b = let_new (let_new (let_new
    (LetU (App ESpawn (Lam (LetU (Var 0) (App EClos (Var 5)))))
    (LetU (App ESpawn (Lam (LetU (Var 0) (App EClos (Var 1)))))
    (LetU (App ESpawn (Lam (LetU (Var 0) (App EClos (App ESend (Pair (bit b) (Var 9)))))))
      db_rnode))))).
Proof. by destruct b. Qed.
