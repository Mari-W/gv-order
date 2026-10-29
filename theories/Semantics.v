(** * Labelled term semantics of GV♯ (Fig. 2)

    A labelled relation e --λ--> e' where labels λ (written α in the
    Coq code, as λ is reserved notation) record the effect:
    β for pure reductions, session labels σ (c?v, c!v, c!, c↔d) for
    communication, (νc) for creating a channel and ⇑v for spawning a
    thread. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export Syntax.

(** ** Labels *)

(** Session labels σ ::= c?v | c!v | c! *)
Inductive slabel :=
  | SRecv (c : chan) (v : expr)    (* c?v : receiving value v on c *)
  | SSend (c : chan) (v : expr)    (* c!v : sending value v on c *)
  | SClos (c : chan)               (* c!  : closing c *)
  | SLink (cd : gset chan).        (* ↔{c,d} : request to forward the pair *)

(** Term labels α ::= β | σ | (νc) | ⇑v

    The forwarding label (§4.5) is a session label like any other: it
    is an offer the configuration makes on the channels it names, so
    the same process rule (P-Act-Session) lifts it and the same
    machinery applies. Its subject set has two elements rather than
    one — which is why [subjs] is set-valued — and as in the paper the
    pair is unordered. *)
Inductive tlabel :=
  | LBeta
  | LSess (σ : slabel)
  | LNew (c : chan)                (* (νc) : creation of channel c *)
  | LSpawn (v : expr).             (* ⇑v   : spawning thread v ∗ *)

(** ** Head steps

    T-Act-Recv receives any value, not only closed ones: a receive
    step must exist for every value some sender might emit, or a
    send/receive pair could fail to synchronize at the process level
    (the composite would deadlock even though both components are
    semantically well-behaved — the logical relation at low step index
    admits open λ-values, so restricting reception to closed values
    would falsify compositionality of CONNECT at index 1). *)

Inductive head_step : expr → tlabel → expr → Prop :=
  | HeadApp e v :                                       (* T-Act-App *)
      is_val v →
      head_step (App (Lam e) v) LBeta (subst1 v e)
  | HeadLetU e :                                        (* T-Act-Let* *)
      head_step (LetU EUnit e) LBeta e
  | HeadLetP u v e :                                    (* T-Act-LetPair *)
      is_val u → is_val v →
      head_step (LetP (Pair u v) e) LBeta (subst2 u v e)
  | HeadNew c :                                         (* T-Act-New *)
      (* both ends of a channel carry the one name c *)
      head_step (App ENew EUnit) (LNew c) (Pair (Chan c) (Chan c))
  | HeadSpawn v :                                       (* T-Act-Spawn *)
      is_val v →
      head_step (App ESpawn v) (LSpawn v) EUnit
  | HeadRecv c v :                                      (* T-Act-Recv *)
      is_val v →
      head_step (App ERecv (Chan c)) (LSess (SRecv c v)) (Pair v (Chan c))
  | HeadSend v c :                                      (* T-Act-Send *)
      is_val v →
      head_step (App ESend (Pair v (Chan c))) (LSess (SSend c v)) (Chan c)
  | HeadClos c :                                        (* T-Act-Close *)
      head_step (App EClos (Chan c)) (LSess (SClos c)) EUnit
  | HeadCase1 v e1 e2 :                                 (* T-Act-Case-Inl *)
      is_val v →
      head_step (Case (Inj1 v) e1 e2) LBeta (subst1 v e1)
  | HeadCase2 v e1 e2 :                                 (* T-Act-Case-Inr *)
      is_val v →
      head_step (Case (Inj2 v) e1 e2) LBeta (subst1 v e2)
  | HeadForce e :                                       (* T-Act-Force *)
      (* force is a konst, so forcing is ordinary application and
         needs no evaluation context of its own.  The thunk's body
         resumes unevaluated (call-by-name), with the thunk
         substituted for its own bound occurrence: forcing unrolls one
         step of the recursion, so !e is Lily's fix (§4.2) and
         replicating it re-runs the suspended computation *)
      head_step (App EForce (EBox e)) LBeta (subst1 (EBox e) e)
  | HeadLink c d :                                      (* T-Act-Link *)
      (* the paper's ↔{c,d} carries a set of two channels; the order
         does not matter — symmetry is in the process rules.  The ends
         are NOT required to be distinct: a self-forwarding is a redex
         like any other, and letting it step is what keeps it visible.
         Were it stuck, a configuration could carry one silently and
         no clause would ever examine it (commit 25c38d8,
         [dead_related]) — and substitution creates exactly that
         residue.  Stepping, it emits the singleton label {[c]}, which
         the forwarding clause of the logical relation cannot satisfy
         (it demands two DISTINCT ends with dual protocols), so such a
         configuration is simply not related.  Typed terms never build
         the redex: [link] consumes a session type and its dual, and
         linearity forbids one channel supplying both. *)
      head_step (App ELink (Pair (Chan c) (Chan d)))
        (LSess (SLink {[c; d]})) EUnit.

(** ** Context closure (T-Act-Ctx)

    Evaluation contexts E ::= [] | E e | v E | ⟨E,e⟩ | ⟨v,E⟩
                            | let ∗ = E in e | let ⟨a,b⟩ = E in e
    realized as congruence rules (with value side conditions for the
    right-of-value frames). *)

Inductive tstep : expr → tlabel → expr → Prop :=
  | TStepHead e α e' :
      head_step e α e' → tstep e α e'
  | TStepAppL e1 α e1' e2 :
      tstep e1 α e1' → tstep (App e1 e2) α (App e1' e2)
  | TStepAppR v e2 α e2' :
      is_val v → tstep e2 α e2' → tstep (App v e2) α (App v e2')
  | TStepPairL e1 α e1' e2 :
      tstep e1 α e1' → tstep (Pair e1 e2) α (Pair e1' e2)
  | TStepPairR v e2 α e2' :
      is_val v → tstep e2 α e2' → tstep (Pair v e2) α (Pair v e2')
  | TStepLetU e1 α e1' e2 :
      tstep e1 α e1' → tstep (LetU e1 e2) α (LetU e1' e2)
  | TStepLetP e1 α e1' e2 :
      tstep e1 α e1' → tstep (LetP e1 e2) α (LetP e1' e2)
  | TStepInj1 e α e' :
      tstep e α e' → tstep (Inj1 e) α (Inj1 e')
  | TStepInj2 e α e' :
      tstep e α e' → tstep (Inj2 e) α (Inj2 e')
  | TStepCase e α e' e1 e2 :
      (* no congruence under EBox: a box suspends evaluation *)
      tstep e α e' → tstep (Case e e1 e2) α (Case e' e1 e2).

(** GV-style term reduction: just the pure steps. *)
Definition reduction (e e' : expr) : Prop := tstep e LBeta e'.
Notation red_star := (rtc reduction).

(** ** Anatomy of a label

    Read by the process rules of Fig. 3, not by Fig. 2; kept below the
    figure so that [slabel] .. [tstep] above is exactly what Fig. 2
    displays, in one uninterrupted stretch. *)

(** The paper's two-element sets, and their symmetry. *)
Lemma upair_comm (c d : chan) : ({[c; d]} : gset chan) = {[d; c]}.
Proof. apply set_eq. set_solver. Qed.

Lemma upair_eq_inv (a b c d : chan) :
  ({[a; b]} : gset chan) = {[c; d]} → a ≠ b →
  (a = c ∧ b = d) ∨ (a = d ∧ b = c).
Proof.
  intros H Hab.
  assert (a ∈ ({[c; d]} : gset chan)) as Ha by (rewrite <-H; set_solver).
  assert (b ∈ ({[c; d]} : gset chan)) as Hb by (rewrite <-H; set_solver).
  assert (c ∈ ({[a; b]} : gset chan)) as Hc by (rewrite H; set_solver).
  assert (d ∈ ({[a; b]} : gset chan)) as Hd by (rewrite H; set_solver).
  set_solver.
Qed.

(** The subjects of a label: one channel for the point-to-point
    actions, both ends for a forwarding offer. *)
Definition subjs (σ : slabel) : gset chan :=
  match σ with
  | SRecv c _ | SSend c _ | SClos c => {[c]}
  | SLink cd => cd
  end.

(** Channels escaping the local scope due to a communication effect:
    an output c!v leaks the channels occurring in the message v. *)
Definition sentc (σ : slabel) : gset chan :=
  match σ with SSend _ v => fchans v | _ => ∅ end.

(** Channels returning into the local scope due to a communication
    effect: an input c?v brings back those channels of the message v
    whose other end is already held by the soup E before the step, the
    receiving thread included. This is the receiving half of the π-calculus Close rule. A channel can
    travel back to the holder of its other end once P-Connect composes
    over cycles; restricting it at once keeps the process-level
    environment a map with one end per channel. *)
Definition backc (σ : slabel) (E : gmultiset expr) : gset chan :=
  match σ with SRecv _ v => fchans v ∩ echans E | _ => ∅ end.

(** ** Basic lemmas *)

Lemma val_head_step v α e' : head_step v α e' → is_val v → False.
Proof. by destruct 1. Qed.

Lemma val_no_tstep v α e' : tstep v α e' → is_val v → False.
Proof.
  induction 1; simpl; intros Hv; try done; eauto using val_head_step;
    apply andb_True in Hv as [? ?]; auto.
Qed.

(** ** Step inversion by head constructor *)

Lemma tstep_app_inv e1 e2 α e' :
  tstep (App e1 e2) α e' →
  (∃ e1', tstep e1 α e1' ∧ e' = App e1' e2)
  ∨ (is_val e1 ∧ ∃ e2', tstep e2 α e2' ∧ e' = App e1 e2')
  ∨ (is_val e1 ∧ is_val e2 ∧ head_step (App e1 e2) α e').
Proof.
  intros H. inversion H; simplify_eq; eauto 10.
  inversion H0; simplify_eq; simpl; eauto 10.
Qed.

Lemma tstep_pair_inv e1 e2 α e' :
  tstep (Pair e1 e2) α e' →
  (∃ e1', tstep e1 α e1' ∧ e' = Pair e1' e2)
  ∨ (is_val e1 ∧ ∃ e2', tstep e2 α e2' ∧ e' = Pair e1 e2').
Proof.
  intros H. inversion H; simplify_eq; eauto 10.
  inversion H0.
Qed.

Lemma tstep_letu_inv e1 e2 α e' :
  tstep (LetU e1 e2) α e' →
  (∃ e1', tstep e1 α e1' ∧ e' = LetU e1' e2)
  ∨ (e1 = EUnit ∧ α = LBeta ∧ e' = e2).
Proof.
  intros H. inversion H; simplify_eq; eauto 10.
  inversion H0; simplify_eq; eauto 10.
Qed.

Lemma tstep_letp_inv e1 e2 α e' :
  tstep (LetP e1 e2) α e' →
  (∃ e1', tstep e1 α e1' ∧ e' = LetP e1' e2)
  ∨ (∃ u v, e1 = Pair u v ∧ is_val u ∧ is_val v ∧
     α = LBeta ∧ e' = subst2 u v e2).
Proof.
  intros H. inversion H; simplify_eq; eauto 10.
  inversion H0; simplify_eq; eauto 10.
Qed.

Lemma tstep_inj1_inv e α e' :
  tstep (Inj1 e) α e' → ∃ e'', tstep e α e'' ∧ e' = Inj1 e''.
Proof.
  intros H. inversion H; simplify_eq; eauto.
  inversion H0.
Qed.

Lemma tstep_inj2_inv e α e' :
  tstep (Inj2 e) α e' → ∃ e'', tstep e α e'' ∧ e' = Inj2 e''.
Proof.
  intros H. inversion H; simplify_eq; eauto.
  inversion H0.
Qed.

Lemma tstep_case_inv e e1 e2 α e' :
  tstep (Case e e1 e2) α e' →
  (∃ e'', tstep e α e'' ∧ e' = Case e'' e1 e2)
  ∨ (∃ v, e = Inj1 v ∧ is_val v ∧ α = LBeta ∧ e' = subst1 v e1)
  ∨ (∃ v, e = Inj2 v ∧ is_val v ∧ α = LBeta ∧ e' = subst1 v e2).
Proof.
  intros H. inversion H; simplify_eq; eauto 10.
  inversion H0; simplify_eq; eauto 10.
Qed.

(** ** Evaluation frames

    One-level evaluation contexts, used to state closure of the
    logical relation under evaluation position generically. *)

Inductive frame :=
  | FAppL (e2 : expr)
  | FAppR (v1 : expr)
  | FPairL (e2 : expr)
  | FPairR (v1 : expr)
  | FLetU (e2 : expr)
  | FLetP (e2 : expr)
  | FInj1
  | FInj2
  | FCase (e1 e2 : expr).

Definition fill_frame (f : frame) (e : expr) : expr :=
  match f with
  | FAppL e2 => App e e2
  | FAppR v1 => App v1 e
  | FPairL e2 => Pair e e2
  | FPairR v1 => Pair v1 e
  | FLetU e2 => LetU e e2
  | FLetP e2 => LetP e e2
  | FInj1 => Inj1 e
  | FInj2 => Inj2 e
  | FCase e1 e2 => Case e e1 e2
  end.

(** Right-of-value frames require the value side condition. *)
Definition frame_val (f : frame) : Prop :=
  match f with FAppR v1 | FPairR v1 => is_val v1 | _ => True end.

(** The channels a frame contributes. *)
Definition frame_chans (f : frame) : gset chan :=
  match f with
  | FAppL e | FAppR e | FPairL e | FPairR e | FLetU e | FLetP e => fchans e
  | FCase e1 e2 => fchans e1 ∪ fchans e2
  | FInj1 | FInj2 => ∅
  end.

Lemma fchans_fill_frame f e :
  fchans (fill_frame f e) = frame_chans f ∪ fchans e.
Proof. destruct f; simpl; set_solver. Qed.

Lemma tstep_fill f e α e' :
  frame_val f → tstep e α e' →
  tstep (fill_frame f e) α (fill_frame f e').
Proof. destruct f; simpl; intros; eauto using tstep. Qed.

Lemma tstep_fill_inv f e α E' :
  frame_val f → ¬ is_val e →
  tstep (fill_frame f e) α E' →
  ∃ e', tstep e α e' ∧ E' = fill_frame f e'.
Proof.
  destruct f; simpl; intros Hf Hv Hst.
  - apply tstep_app_inv in Hst
      as [(e' & ? & ->)|[(Hval & _)|(Hval & _)]]; eauto.
    all: by destruct (Hv Hval).
  - apply tstep_app_inv in Hst
      as [(e' & Hst' & _)|[(_ & e' & ? & ->)|(_ & Hval & _)]]; eauto.
    + exfalso. eauto using val_no_tstep.
    + by destruct (Hv Hval).
  - apply tstep_pair_inv in Hst as [(e' & ? & ->)|(Hval & _)]; eauto.
    by destruct (Hv Hval).
  - apply tstep_pair_inv in Hst as [(e' & Hst' & _)|(_ & e' & ? & ->)]; eauto.
    exfalso. eauto using val_no_tstep.
  - apply tstep_letu_inv in Hst as [(e' & ? & ->)|(-> & _)]; eauto.
    by destruct Hv.
  - apply tstep_letp_inv in Hst
      as [(e' & ? & ->)|(u & v & -> & Hu & Hv' & _)]; eauto.
    exfalso. apply Hv. simpl. by apply andb_True.
  - apply tstep_inj1_inv in Hst as (e' & ? & ->); eauto.
  - apply tstep_inj2_inv in Hst as (e' & ? & ->); eauto.
  - apply tstep_case_inv in Hst
      as [(e' & ? & ->)|[(v & -> & Hv' & _)|(v & -> & Hv' & _)]]; eauto.
    all: by destruct (Hv Hv').
Qed.

(** Values carried by communication labels are values. *)
Lemma head_step_label_val e α e' :
  head_step e α e' →
  match α with
  | LSess (SRecv _ v) | LSess (SSend _ v) | LSpawn v => is_val v
  | _ => True
  end.
Proof. by destruct 1. Qed.

Lemma tstep_label_val e α e' :
  tstep e α e' →
  match α with
  | LSess (SRecv _ v) | LSess (SSend _ v) | LSpawn v => is_val v
  | _ => True
  end.
Proof. induction 1; [by eapply head_step_label_val|done..]. Qed.

Lemma tstep_send_val e c v e' :
  tstep e (LSess (SSend c v)) e' → is_val v.
Proof. intros H. exact (tstep_label_val _ _ _ H). Qed.

(** ** Channel footprint of a step

    The channels a transition can introduce: a step's result mentions
    at most the channels of the source plus those carried by the
    label. This is the ambient invariant fc(E) ⊆ C ∪ dom Σ in motion,
    which the composition lemmas thread explicitly (§4.5). *)
Definition lchans (α : tlabel) : gset chan :=
  match α with
  | LBeta => ∅
  | LSess (SRecv c w) => {[c]} ∪ fchans w
  | LSess (SSend c _) => {[c]}
  | LSess (SClos c) => {[c]}
  | LSess (SLink cd) => cd
  | LNew c => {[c]}
  | LSpawn v => fchans v
  end.

Lemma head_step_fchans e α e' :
  head_step e α e' → fchans e' ⊆ fchans e ∪ lchans α.
Proof.
  destruct 1; simpl;
    try (etrans; [apply fchans_subst1_sub|]);
    try (etrans; [apply fchans_subst2_sub|]);
    set_solver.
Qed.

Lemma tstep_fchans e α e' :
  tstep e α e' → fchans e' ⊆ fchans e ∪ lchans α.
Proof.
  induction 1; simpl; try set_solver.
  by apply head_step_fchans.
Qed.

(** A forwarding label always carries a two-element set. *)
(** A forwarding label carries a pair — possibly degenerate, when the
    term names one channel twice; that case is what the relation
    refutes rather than what the semantics forbids. *)
Lemma tstep_link_shape e cd e' :
  tstep e (LSess (SLink cd)) e' → ∃ c d, cd = {[c; d]}.
Proof.
  intros H. remember (LSess (SLink cd)) as α eqn:Hα.
  induction H; subst; try (by apply IHtstep).
  match goal with Hh : head_step _ _ _ |- _ =>
    inversion Hh; simplify_eq; eauto end.
Qed.

(** Both ends named by a forwarding label are free in the term. *)
Lemma tstep_link_subj e cd e' :
  tstep e (LSess (SLink cd)) e' → cd ⊆ fchans e.
Proof.
  intros H. remember (LSess (SLink cd)) as α eqn:Hα.
  induction H; subst; simpl; try (specialize (IHtstep eq_refl); set_solver).
  match goal with Hh : head_step _ _ _ |- _ =>
    inversion Hh; simplify_eq; simpl; set_solver end.
Qed.

(** The value carried by a spawn or send label is a subterm of the
    stepping expression, so its channels are among the expression's. *)
Lemma tstep_spawn_val_fchans e v e' :
  tstep e (LSpawn v) e' → fchans v ⊆ fchans e.
Proof.
  intros H. remember (LSpawn v) as α eqn:Hα.
  induction H; subst; simpl; try (specialize (IHtstep eq_refl); set_solver).
  match goal with Hh : head_step _ _ _ |- _ =>
    inversion Hh; simplify_eq; simpl; set_solver end.
Qed.

Lemma tstep_send_val_fchans e c v e' :
  tstep e (LSess (SSend c v)) e' → fchans v ⊆ fchans e.
Proof.
  intros H. remember (LSess (SSend c v)) as α eqn:Hα.
  induction H; subst; simpl; try (specialize (IHtstep eq_refl); set_solver).
  match goal with Hh : head_step _ _ _ |- _ =>
    inversion Hh; simplify_eq; simpl; set_solver end.
Qed.

(** Receives can be retargeted to any other value: the term LTS offers
    an input transition for every value. *)
Lemma recv_retarget e c w e' w' :
  tstep e (LSess (SRecv c w)) e' → is_val w' →
  ∃ e'', tstep e (LSess (SRecv c w')) e''.
Proof.
  intros H Hw'. remember (LSess (SRecv c w)) as α eqn:Hα.
  induction H; subst; try discriminate.
  - inversion H; simplify_eq. eexists. apply TStepHead. by apply HeadRecv.
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

(** Process labels π ::= τ | σ

    Forwarding is not a label of its own: an offer ↔{c,d} whose ends
    are both free is an offer like any other, lifted by the single
    rule P-Act-Session. *)
Inductive plabel :=
  | PTau
  | PSess (σ : slabel).

(** ** The labelled transition relation (Fig. 3)

    In P-Act-New the new channel c must be globally fresh: not
    restricted yet, and not free in any thread (the paper keeps this
    implicit in the well-formedness of the "new" name). Rule
    P-Act-Close writes the paper's C ∪ {c} source as membership
    c ∈ C. P-Act-Msg does not ask for c to be restricted: two threads
    may synchronise on a free channel too. *)

Inductive proc_step : proc → plabel → proc → Prop :=
  | PStepSession C E e σ e' :                          (* P-Act-Session *)
      (* one rule for every external offer, forwarding included: all
         of the label's subjects must be free *)
      tstep e (LSess σ) e' →
      subjs σ ## C →
      proc_step (C, E ⊎ {[+ e +]}) (PSess σ)
                ((C ∖ sentc σ) ∪ backc σ (E ⊎ {[+ e +]}), E ⊎ {[+ e' +]})
  | PStepBeta C E e e' :                               (* P-Act-Beta *)
      tstep e LBeta e' →
      proc_step (C, E ⊎ {[+ e +]}) PTau (C, E ⊎ {[+ e' +]})
  | PStepNew C E e c e' :                              (* P-Act-New *)
      tstep e (LNew c) e' →
      c ∉ C → c ∉ echans E → c ∉ fchans e →
      proc_step (C, E ⊎ {[+ e +]}) PTau
                (C ∪ {[c]}, E ⊎ {[+ e' +]})
  | PStepSpawn C E e v e' :                            (* P-Act-Spawn *)
      tstep e (LSpawn v) e' →
      proc_step (C, E ⊎ {[+ e +]}) PTau
                (C, E ⊎ {[+ e' +]} ⊎ {[+ App v EUnit +]})
  | PStepMsg C E c v e e' f f' :                       (* P-Act-Msg *)
      tstep e (LSess (SSend c v)) e' →
      tstep f (LSess (SRecv c v)) f' →
      proc_step (C, E ⊎ {[+ e +]} ⊎ {[+ f +]}) PTau
                (C, E ⊎ {[+ e' +]} ⊎ {[+ f' +]})
  | PStepClose C E c e e' f f' :                       (* P-Act-Close *)
      tstep e (LSess (SClos c)) e' →
      tstep f (LSess (SClos c)) f' →
      c ∈ C →
      proc_step (C, E ⊎ {[+ e +]} ⊎ {[+ f +]}) PTau
                (C ∖ {[c]}, E ⊎ {[+ e' +]} ⊎ {[+ f' +]})
  | PStepLink C E e c d e' :                           (* P-Act-Link *)
      (* the paper's rule, verbatim: the removed end c must be
         restricted, and the whole resulting configuration — the other
         threads AND the actor's continuation — is substituted, so
         c's peer gets fused with whoever holds d.  The label set is
         unordered, so this one rule also removes the other end
         (instantiate c and d the other way round, [upair_comm]).
         Soundness of the whole-soup substitution against the logical
         relation rests on channel tightness — without it the
         substitution rewrites junk-carrying siblings and no
         renaming-transport lemma exists (mechanized counterexamples: commit 25c38d8).
         The ends need not be distinct: for c = d the substitution is
         the identity and the rule simply releases the name, which is
         what a self-forwarding means — the thread held both ends, so
         the channel is spent.  Releasing is safe precisely because a
         configuration carrying a self-forwarding on a FREE channel
         offers the singleton label and is refuted by the relation, so
         no live name can be stolen this way.  There is no separate
         lifted rule: an offer with both ends free is P-Act-Session. *)
      tstep e (LSess (SLink {[c; d]})) e' →
      c ∈ C →
      proc_step (C, E ⊎ {[+ e +]}) PTau
                (C ∖ {[c]}, echsubst c d (E ⊎ {[+ e' +]})).

(** Process reduction p --> p' is p --τ--> p'. *)
Definition preduction (p p' : proc) : Prop := proc_step p PTau p'.
Notation pred_star := (rtc preduction).

(** Irreducible terms and processes (Def. 3.1).

    [irred] is stated here rather than next to [tstep], so that the
    two halves of the definition sit together and the paper can cite
    the pair with a single link. *)
Definition irred (e : expr) : Prop := ∀ α e', ¬ tstep e α e'.

Definition pirred (p : proc) : Prop := ∀ π p', ¬ proc_step p π p'.

Lemma val_irred v : is_val v → irred v.
Proof. intros ? α e' ?. eauto using val_no_tstep. Qed.

(** Inversion for session-labelled process transitions: only
    P-Act-Session can produce them. *)
Lemma proc_step_sess_inv C E σ p' :
  proc_step (C, E) (PSess σ) p' →
  ∃ E0 e e',
    E = E0 ⊎ {[+ e +]} ∧ tstep e (LSess σ) e' ∧ subjs σ ## C ∧
    p' = ((C ∖ sentc σ) ∪ backc σ E, E0 ⊎ {[+ e' +]}).
Proof. intros H. inversion H; simplify_eq. eauto 10. Qed.

(** ** Internalizing communication (Lemma 2.3)

    Two disjoint processes communicating over an external channel c can
    be put together, turning the communication into an internal τ
    step; c need not be closed over, since P-Act-Msg does not require
    its subject to be restricted. Note: following P-Act-Msg (Fig. 3),
    the combined channel set is unchanged — the channels sent along c stay
    in scope of the combined process (the draft's Eq. (9) instead
    subtracts sentc(c!v); that spot is marked "XXX (not yet)" in the
    margin, and is not derivable from Fig. 3 as stated).

    The receiving side's own channel set grows by backc(c?v) on its
    own ([proc_step_recv_chans]): those are channels of v whose other
    end the receiver already holds. Both ends then occur free in the
    two components, so in the composite they are already in the cut
    C0 between them, and the composite's channel set C1 ∪ C2 ∪ C0 is
    unchanged. *)

Lemma internalize_comm C0 C1 E1 C1' E1' C2 E2 C2' E2' c v :
  proc_step (C1, E1) (PSess (SSend c v)) (C1', E1') →
  proc_step (C2, E2) (PSess (SRecv c v)) (C2', E2') →
  C1 ## C2 → c ∉ C1 →
  proc_step (C1 ∪ C2 ∪ C0, E1 ⊎ E2) PTau
            (C1 ∪ C2 ∪ C0, E1' ⊎ E2').
Proof.
  intros Hs Hr _ _.
  apply proc_step_sess_inv in Hs as (F1 & e & e' & -> & Hstep1 & _ & Heq1).
  apply proc_step_sess_inv in Hr as (F2 & f & f' & -> & Hstep2 & _ & Heq2).
  simplify_eq.
  assert (F1 ⊎ {[+ e +]} ⊎ (F2 ⊎ {[+ f +]})
          = (F1 ⊎ F2) ⊎ {[+ e +]} ⊎ {[+ f +]}) as -> by multiset_solver.
  assert (F1 ⊎ {[+ e' +]} ⊎ (F2 ⊎ {[+ f' +]})
          = (F1 ⊎ F2) ⊎ {[+ e' +]} ⊎ {[+ f' +]}) as -> by multiset_solver.
  by eapply PStepMsg.
Qed.

(** What an input does to the receiver's channel set: it grows by
    exactly the channels of the message that the receiver's soup
    already mentions. *)
Lemma proc_step_recv_chans C E C' E' c v :
  proc_step (C, E) (PSess (SRecv c v)) (C', E') →
  C' = C ∪ (fchans v ∩ echans E).
Proof.
  intros H.
  apply proc_step_sess_inv in H as (E0 & e & e' & -> & _ & _ & Heq).
  simplify_eq. simpl. set_solver.
Qed.

(** ** Internalizing a close

    The same construction for the other synchronising action. Two
    disjoint processes that both offer to close the external channel c
    can be put together and closed over c, and the offers become an
    internal τ step.

    One difference to [internalize_comm], and it is the point of the
    lemma: the τ step CONSUMES the channel. P-Act-Close removes c from
    the restricted set, so the combined process ends at C1 ∪ C2, not at
    C1 ∪ C2 ∪ {[c]} — closing is the only way a name leaves scope
    besides forwarding.

    The premises' own channel sets are untouched: sentc (SClos c) = ∅,
    so C1' = C1 and C2' = C2 (a close leaks nothing), which is why the
    conclusion can be read off C1 and C2 alone. The freshness premises
    c ∉ C1 and c ∉ C2 are load-bearing here (they are what makes the
    subtraction come out as C1 ∪ C2), unlike in [internalize_comm]
    where they are not consumed; both are anyway forced by
    P-Act-Session's side condition subjs σ ## C on the two assumed
    transitions. *)

Lemma internalize_close C1 E1 C1' E1' C2 E2 C2' E2' c :
  proc_step (C1, E1) (PSess (SClos c)) (C1', E1') →
  proc_step (C2, E2) (PSess (SClos c)) (C2', E2') →
  C1 ## C2 → c ∉ C1 → c ∉ C2 →
  proc_step (C1 ∪ C2 ∪ {[c]}, E1 ⊎ E2) PTau
            (C1 ∪ C2, E1' ⊎ E2').
Proof.
  intros H1 H2 _ Hc1 Hc2.
  apply proc_step_sess_inv in H1 as (F1 & e & e' & -> & Hstep1 & _ & Heq1).
  apply proc_step_sess_inv in H2 as (F2 & f & f' & -> & Hstep2 & _ & Heq2).
  simplify_eq.
  assert (F1 ⊎ {[+ e +]} ⊎ (F2 ⊎ {[+ f +]})
          = (F1 ⊎ F2) ⊎ {[+ e +]} ⊎ {[+ f +]}) as -> by multiset_solver.
  assert (F1 ⊎ {[+ e' +]} ⊎ (F2 ⊎ {[+ f' +]})
          = (F1 ⊎ F2) ⊎ {[+ e' +]} ⊎ {[+ f' +]}) as -> by multiset_solver.
  (* P-Act-Close fires at the combined process and retires c; the
     subtraction is then exactly C1 ∪ C2 because c is fresh for both. *)
  pose proof (PStepClose (C1 ∪ C2 ∪ {[c]}) (F1 ⊎ F2) c e e' f f'
                Hstep1 Hstep2 ltac:(set_solver)) as Hstep.
  assert ((C1 ∪ C2 ∪ {[c]}) ∖ {[c]} = C1 ∪ C2) as Heq by set_solver.
  by rewrite Heq in Hstep.
Qed.
