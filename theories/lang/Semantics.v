(** * Labelled term semantics of GV♯ (Fig. 2)

    A labelled relation e --λ--> e' where labels λ (written α in the
    Coq code, as λ is reserved notation) record the effect:
    β for pure reductions, session labels σ (c?v, c!v, c!, c↔d) for
    communication, (νc) for creating a channel and ⇑v for spawning a
    thread. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export lang.Syntax.

(** ** Labels *)

(** Session labels σ ::= o?v | o!v | o! | o↔o' | o◁i | o▷i. Every
    subject is an end o = (c, b), the channel c and the polarity bit b
    of the end's point (syntactic points, sharp edges 173). *)
Inductive slabel :=
  | SRecv (c : cend) (v : expr)    (* o?v : receiving value v on o *)
  | SSend (c : cend) (v : expr)    (* o!v : sending value v on o *)
  | SClos (c : cend)               (* o!  : closing o *)
  | SLink (cd : gset cend)         (* ↔{o,o'} : request to forward the pair *)
  | SSel (c : cend) (b : bool)     (* o◁i : selecting branch i on o,
                                      i = 1 for false, i = 2 for true (K4) *)
  | SBra (c : cend) (b : bool).    (* o▷i : branching on o, branch i taken *)

(** The injection of a branch: inj₁ for false, inj₂ for true. *)
Definition inj_of (b : bool) (e : expr) : expr := if b then Inj2 e else Inj1 e.

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
  | LNew (c : chan) (x : point)    (* (νc)@x : creation of channel c at x *)
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
  | HeadNew c x :                                       (* T-Act-New *)
      (* both ends of a channel carry the one name c, and their bits
         are the polarities of x and x̄ *)
      head_step (App ENew (EPt x)) (LNew c x)
        (Pair (Chan c (pt_pol x)) (Chan c (negb (pt_pol x))))
  | HeadPay i x :                                       (* T-Act-Pay *)
      head_step (App (Konst (KPay i)) (EPt x)) LBeta (EPt (pt_payload x i))
  | HeadSucc x :                                        (* T-Act-Succ *)
      head_step (App (Konst KSucc) (EPt x)) LBeta (EPt (pt_shift 1 x))
  | HeadSpawn v :                                       (* T-Act-Spawn *)
      is_val v →
      head_step (App ESpawn v) (LSpawn v) EUnit
  | HeadRecv c β v :                                    (* T-Act-Recv *)
      is_val v →
      head_step (App ERecv (Chan c β)) (LSess (SRecv (c, β) v)) (Pair v (Chan c β))
  | HeadSend v c β :                                    (* T-Act-Send *)
      is_val v →
      head_step (App ESend (Pair v (Chan c β))) (LSess (SSend (c, β) v)) (Chan c β)
  | HeadClos c β :                                      (* T-Act-Close *)
      head_step (App EClos (Chan c β)) (LSess (SClos (c, β))) EUnit
  | HeadSel1 c β :                                      (* T-Act-Select₁ *)
      (* the selecting end continues at a negative point (sel_pt) *)
      head_step (App ESel1 (Chan c β)) (LSess (SSel (c, β) false)) (Chan c false)
  | HeadSel2 c β :                                      (* T-Act-Select₂ *)
      head_step (App ESel2 (Chan c β)) (LSess (SSel (c, β) true)) (Chan c false)
  | HeadBra c β b :                                     (* T-Act-Branch *)
      (* branch waits for either pick and returns the channel in the
         injection of the branch taken, at a positive point (bra_pt) *)
      head_step (App EBra (Chan c β)) (LSess (SBra (c, β) b)) (inj_of b (Chan c true))
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
  | HeadLink c bc d bd :                                (* T-Act-Link *)
      (* The label ↔{o,o'} is a set, so the order of the ends does not
         matter. The ends need not be distinct. A self-forwarding steps
         with the label {[o]}, which the link clause of the relation
         rejects, so a stuck self-link can never hide in a related
         configuration. Typed terms never build one. *)
      head_step (App ELink (Pair (Chan c bc) (Chan d bd)))
        (LSess (SLink {[(c, bc); (d, bd)]})) EUnit.

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

(** ** Anatomy of a label

    Read by the process rules of Fig. 3, not by Fig. 2; kept below the
    figure so that [slabel] .. [tstep] above is exactly what Fig. 2
    displays, in one uninterrupted stretch. *)

(** The paper's two-element sets, and their symmetry. *)
Lemma upair_comm `{Countable A} (c d : A) : ({[c; d]} : gset A) = {[d; c]}.
Proof. apply set_eq. set_solver. Qed.

Lemma upair_eq_inv `{Countable A} (a b c d : A) :
  ({[a; b]} : gset A) = {[c; d]} → a ≠ b →
  (a = c ∧ b = d) ∨ (a = d ∧ b = c).
Proof.
  intros Hs Hab.
  assert (a ∈ ({[c; d]} : gset A)) as Ha by (rewrite <-Hs; set_solver).
  assert (b ∈ ({[c; d]} : gset A)) as Hb by (rewrite <-Hs; set_solver).
  assert (c ∈ ({[a; b]} : gset A)) as Hc by (rewrite Hs; set_solver).
  assert (d ∈ ({[a; b]} : gset A)) as Hd by (rewrite Hs; set_solver).
  set_solver.
Qed.

(** The subjects of a label, as channel names: one channel for the
    point-to-point actions, both for a forwarding offer. *)
Definition subjs (σ : slabel) : gset chan :=
  match σ with
  | SRecv c _ | SSend c _ | SClos c | SSel c _ | SBra c _ => {[c.1]}
  | SLink cd => set_map fst cd
  end.

(** Channels escaping the local scope due to a communication effect:
    an output c!v leaks the channels occurring in the message v. *)
Definition sentc (σ : slabel) : gset chan :=
  match σ with SSend _ v => fchans v | _ => ∅ end.

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
  | LSess (SRecv c w) => {[c.1]} ∪ fchans w
  | LSess (SSend c _) => {[c.1]}
  | LSess (SClos c) => {[c.1]}
  | LSess (SLink cd) => set_map fst cd
  | LSess (SSel c _) | LSess (SBra c _) => {[c.1]}
  | LNew c _ => {[c]}
  | LSpawn v => fchans v
  end.

Lemma head_step_fchans e α e' :
  head_step e α e' → fchans e' ⊆ fchans e ∪ lchans α.
Proof.
  destruct 1; simpl; try destruct b;
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
  tstep e (LSess (SLink cd)) e' → ∃ c bc d bd, cd = {[(c, bc); (d, bd)]}.
Proof.
  intros H. remember (LSess (SLink cd)) as α eqn:Hα.
  induction H; subst; try (by apply IHtstep).
  match goal with Hh : head_step _ _ _ |- _ =>
    inversion Hh; simplify_eq; eauto end.
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

(** A branch can take either pick: the term LTS offers c▷i for both i. *)
Lemma bra_retarget e c i e' j :
  tstep e (LSess (SBra c i)) e' → ∃ e'', tstep e (LSess (SBra c j)) e''.
Proof.
  intros H. remember (LSess (SBra c i)) as α eqn:Hα.
  induction H; subst; try discriminate.
  - inversion H; simplify_eq. eexists. apply TStepHead. apply HeadBra.
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
                (C ∖ sentc σ, E ⊎ {[+ e' +]})
  | PStepBeta C E e e' :                               (* P-Act-Beta *)
      tstep e LBeta e' →
      proc_step (C, E ⊎ {[+ e +]}) PTau (C, E ⊎ {[+ e' +]})
  | PStepNew C E e c x e' :                            (* P-Act-New *)
      tstep e (LNew c x) e' →
      c ∉ C → c ∉ echans E → c ∉ fchans e →
      proc_step (C, E ⊎ {[+ e +]}) PTau
                (C ∪ {[c]}, E ⊎ {[+ e' +]})
  | PStepSpawn C E e v e' :                            (* P-Act-Spawn *)
      tstep e (LSpawn v) e' →
      proc_step (C, E ⊎ {[+ e +]}) PTau
                (C, E ⊎ {[+ e' +]} ⊎ {[+ App v EUnit +]})
  | PStepMsg C E c b v e e' f f' :                     (* P-Act-Msg *)
      (* a send on one end meets a receive on the other *)
      tstep e (LSess (SSend (c, b) v)) e' →
      tstep f (LSess (SRecv (c, negb b) v)) f' →
      proc_step (C, E ⊎ {[+ e +]} ⊎ {[+ f +]}) PTau
                (C, E ⊎ {[+ e' +]} ⊎ {[+ f' +]})
  | PStepClose C E c b e e' f f' :                     (* P-Act-Close *)
      tstep e (LSess (SClos (c, b))) e' →
      tstep f (LSess (SClos (c, negb b))) f' →
      c ∈ C →
      proc_step (C, E ⊎ {[+ e +]} ⊎ {[+ f +]}) PTau
                (C ∖ {[c]}, E ⊎ {[+ e' +]} ⊎ {[+ f' +]})
  | PStepChoice C E c β b e e' f f' :                  (* P-Act-Choice *)
      (* a selection meets a branch on the other end of the same
         channel, like a message without payload; the channel may be
         free or restricted *)
      tstep e (LSess (SSel (c, β) b)) e' →
      tstep f (LSess (SBra (c, negb β) b)) f' →
      proc_step (C, E ⊎ {[+ e +]} ⊎ {[+ f +]}) PTau
                (C, E ⊎ {[+ e' +]} ⊎ {[+ f' +]})
  | PStepLink C E e c bc d bd e' :                     (* P-Act-Link *)
      (* The paper's rule. The removed end c must be restricted, and the
         whole resulting soup is substituted, the actor's continuation
         included, so c's peer is fused with whoever holds d. The label
         is unordered, so the same rule removes either end
         ([upair_comm]). For c = d the substitution is the identity and
         the rule releases the name. An offer with both ends free is
         P-Act-Session. *)
      tstep e (LSess (SLink {[(c, bc); (d, bd)]})) e' →
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
    p' = (C ∖ sentc σ, E0 ⊎ {[+ e' +]}).
Proof. intros H. inversion H; simplify_eq. eauto 10. Qed.
