(** * Thread steps (stage S1, proposal §2.7)

    A labelled relation e --α--> e' on terms. The head rules are named
    after the paper's T-Act rules, and T-Act-Ctx closes them under one
    evaluation frame at a time.

    Labels carry what the relation reads. A send and a spawn carry the
    value v. The ends that leave the thread with it are [fends v], the
    set the process semantics extrudes from the restricted channels at an
    external send (§2.7). A
    [new] carries the name c of the new channel and nothing else. *)

From stdpp Require Import relations.
From GV Require Export lang.Notations.

(** ** Labels *)

(** Session labels, offers on ends. *)
Inductive slabel :=
  | SSend (o : cend) (v : expr)                  (* o!v, moving the ends of v *)
  | SRecv (o : cend) (v : expr)                  (* o?v *)
  | SClose (o : cend)                            (* o! *)
  | SSel (o : cend) (i : bool)                   (* o◁i *)
  | SBra (o : cend) (i : bool)                   (* o▷i *)
  | SLink (os : gset cend).                      (* ↔{o1, o2}, an unordered pair *)

Inductive tlabel :=
  | LBeta                                    (* β, let, case, force *)
  | LNew (c : chan)                         (* new creates c *)
  | LSpawn (v : expr)                        (* spawn of the thunk v, moving its ends *)
  | LSess (σ : slabel).

Global Instance slabel_eq_dec : EqDecision slabel.
Proof. solve_decision. Defined.
Global Instance tlabel_eq_dec : EqDecision tlabel.
Proof. solve_decision. Defined.

(** ** Head steps (the T-Act rules)

    T-Act-Recv receives any value, so that a receive can meet whatever a
    sender emits. Select and branch keep their end, because the name of
    an end does not depend on its point (§2.2). *)

Inductive head_step : expr → tlabel → expr → Prop :=
  | t_act_app e v :                                     (* T-Act-App *)
      is_val v →
      head_step (App (Lam e) v) LBeta (subst1 v e)
  | t_act_let_unit e :                                  (* T-Act-Let-Unit *)
      head_step (LetU EUnit e) LBeta e
  | t_act_let_pair u v e :                              (* T-Act-Let-Pair *)
      is_val u → is_val v →
      head_step (LetP (Pair u v) e) LBeta (subst2 u v e)
  | t_act_case_inl v e1 e2 :                            (* T-Act-Case-Inl *)
      is_val v →
      head_step (Case (Inj false v) e1 e2) LBeta (subst1 v e1)
  | t_act_case_inr v e1 e2 :                            (* T-Act-Case-Inr *)
      is_val v →
      head_step (Case (Inj true v) e1 e2) LBeta (subst1 v e2)
  | t_act_force e :                                     (* T-Act-Force *)
      (* the body resumes with the thunk for its own bound occurrence *)
      head_step (EForce (EBox e)) LBeta (subst1 (EBox e) e)
  | t_act_new c :                                       (* T-Act-New *)
      head_step ENew (LNew c) (Pair (Chan c⁺) (Chan c⁻))
  | t_act_spawn v :                                     (* T-Act-Spawn *)
      is_val v →
      head_step (ESpawn v) (LSpawn v) EUnit
  | t_act_send v o :                                    (* T-Act-Send *)
      is_val v →
      head_step (ESend (Pair v (Chan o))) (LSess (SSend o v)) (Chan o)
  | t_act_recv o v :                                    (* T-Act-Recv *)
      is_val v →
      head_step (ERecv (Chan o)) (LSess (SRecv o v)) (Pair v (Chan o))
  | t_act_close o :                                     (* T-Act-Close *)
      head_step (EClose (Chan o)) (LSess (SClose o)) EUnit
  | t_act_select i o :                                  (* T-Act-Select *)
      head_step (ESel i (Chan o)) (LSess (SSel o i)) (Chan o)
  | t_act_branch i o :                                  (* T-Act-Branch *)
      head_step (EBra (Chan o)) (LSess (SBra o i)) (Inj i (Chan o))
  | t_act_link o1 o2 :                                  (* T-Act-Link *)
      (* the label is a set, so the order of the ends does not matter;
         the ends need not differ, and the relation rejects a self link *)
      head_step (ELink (Pair (Chan o1) (Chan o2))) (LSess (SLink {[o1; o2]})) EUnit.

(** ** Evaluation frames *)

Inductive frame :=
  | FAppL (e2 : expr)
  | FAppR (v1 : expr)
  | FPairL (e2 : expr)
  | FPairR (v1 : expr)
  | FLetU (e2 : expr)
  | FLetP (e2 : expr)
  | FInj (b : bool)
  | FCase (e1 e2 : expr)
  | FOp (k : prim).

Definition fill_frame (f : frame) (e : expr) : expr :=
  match f with
  | FAppL e2 => App e e2
  | FAppR v1 => App v1 e
  | FPairL e2 => Pair e e2
  | FPairR v1 => Pair v1 e
  | FLetU e2 => LetU e e2
  | FLetP e2 => LetP e e2
  | FInj b => Inj b e
  | FCase e1 e2 => Case e e1 e2
  | FOp k => Op k e
  end.

(** Right-of-value frames ask for a value on the left. *)
Definition frame_val (f : frame) : Prop :=
  match f with FAppR v1 | FPairR v1 => is_val v1 | _ => True end.

(** A map of ends on a frame. *)
Definition frame_emap (g : cend → cend) (f : frame) : frame :=
  match f with
  | FAppL e2 => FAppL (emap g e2) | FAppR v => FAppR (emap g v)
  | FPairL e2 => FPairL (emap g e2) | FPairR v => FPairR (emap g v)
  | FLetU e2 => FLetU (emap g e2) | FLetP e2 => FLetP (emap g e2)
  | FInj b => FInj b
  | FCase e1 e2 => FCase (emap g e1) (emap g e2)
  | FOp k => FOp k
  end.

Lemma emap_fill g f e : emap g (fill_frame f e) = fill_frame (frame_emap g f) (emap g e).
Proof. by destruct f. Qed.

Lemma frame_val_emap g f : frame_val (frame_emap g f) ↔ frame_val f.
Proof. destruct f; simpl; rewrite ?is_val_emap; done. Qed.

(** ** Thread steps: head steps under evaluation frames (T-Act-Ctx) *)

Inductive tstep : expr → tlabel → expr → Prop :=
  | tstep_head e α e' :
      head_step e α e' → tstep e α e'
  | t_act_ctx f e α e' :                                (* T-Act-Ctx *)
      (* no frame under λ or a box: both suspend evaluation *)
      frame_val f → tstep e α e' → tstep (fill_frame f e) α (fill_frame f e').

(** ** Anatomy of a label *)

Lemma upair_comm `{Countable A} (c d : A) : ({[c; d]} : gset A) = {[d; c]}.
Proof. apply set_eq. set_solver. Qed.

(** The subjects of a session label, as channels. *)
Definition subjs (σ : slabel) : gset chan :=
  match σ with
  | SSend o _ | SRecv o _ | SClose o | SSel o _ | SBra o _ => {[ech o]}
  | SLink os => set_map ech os
  end.

(** The channels an external send extrudes: those of the ends of its value. *)
Definition sentc (σ : slabel) : gset chan :=
  match σ with SSend _ v => fchans v | _ => ∅ end.

(** ** Basic lemmas *)

Lemma val_head_step v α e' : head_step v α e' → is_val v → False.
Proof. by destruct 1. Qed.

Lemma val_no_tstep v α e' : tstep v α e' → is_val v → False.
Proof.
  induction 1 as [|f e α e' Hf Hs IH]; [eauto using val_head_step|].
  destruct f; simpl in *; try done; intros Hv; apply andb_True in Hv as [? ?]; auto.
Qed.

Lemma tstep_fill f e α e' :
  frame_val f → tstep e α e' → tstep (fill_frame f e) α (fill_frame f e').
Proof. apply t_act_ctx. Qed.

(** One inversion for every thread step. *)
Lemma tstep_inv e α e' :
  tstep e α e' →
  head_step e α e' ∨
  ∃ f e0 e0', frame_val f ∧ e = fill_frame f e0 ∧ e' = fill_frame f e0' ∧ tstep e0 α e0'.
Proof. destruct 1; [by left|right; eauto 10]. Qed.

(** A head redex steps only at its head: its hole holds a value. *)
Lemma head_redex_val f e0 α e' : frame_val f → head_step (fill_frame f e0) α e' → is_val e0.
Proof.
  intros Hf Hh. destruct f; simpl in *; inversion Hh; subst; simpl;
    rewrite ?andb_True; auto.
Qed.

(** A step in a frame is a step of the hole, unless the hole is a value. *)
Lemma tstep_fill_inv f e α E' :
  frame_val f → ¬ is_val e →
  tstep (fill_frame f e) α E' →
  ∃ e', tstep e α e' ∧ E' = fill_frame f e'.
Proof.
  intros Hf Hv Hst. apply tstep_inv in Hst as [Hh|(f' & e0 & e0' & Hf' & Heq & -> & Hs)].
  { exfalso. apply Hv. by eapply head_redex_val. }
  destruct f, f'; simpl in *; simplify_eq; eauto.
  all: exfalso; eauto using val_no_tstep.
Qed.

(** Values carried by labels are values. *)
Definition lval (α : tlabel) : Prop :=
  match α with
  | LSess (SRecv _ v) | LSess (SSend _ v) | LSpawn v => is_val v
  | _ => True
  end.

Lemma tstep_label_val e α e' : tstep e α e' → lval α.
Proof. induction 1 as [e α e' Hh| ]; [by destruct Hh|done]. Qed.

(** ** Footprint of a step *)

(** A link label is a pair, possibly degenerate. *)
Lemma tstep_link_shape e os e' :
  tstep e (LSess (SLink os)) e' → ∃ o1 o2, os = {[o1; o2]}.
Proof.
  intros H. remember (LSess (SLink os)) as α eqn:Hα.
  induction H as [e α e' Hh|]; subst; [|by apply IHtstep].
  inversion Hh; simplify_eq; eauto.
Qed.

(** A receive can take any value, and a branch either pick. *)
Lemma recv_retarget e o w e' w' :
  tstep e (LSess (SRecv o w)) e' → is_val w' →
  ∃ e'', tstep e (LSess (SRecv o w')) e''.
Proof.
  intros H Hw'. remember (LSess (SRecv o w)) as α eqn:Hα.
  induction H as [e α e' Hh|f e α e' Hf Hs IH]; subst.
  - inversion Hh; simplify_eq. eexists. apply tstep_head. by apply t_act_recv.
  - destruct (IH eq_refl) as [e'' ?]. eexists. by apply t_act_ctx.
Qed.

Lemma bra_retarget e o i e' j :
  tstep e (LSess (SBra o i)) e' → ∃ e'', tstep e (LSess (SBra o j)) e''.
Proof.
  intros H. remember (LSess (SBra o i)) as α eqn:Hα.
  induction H as [e α e' Hh|f e α e' Hf Hs IH]; subst.
  - inversion Hh; simplify_eq. eexists. apply tstep_head, t_act_branch.
  - destruct (IH eq_refl) as [e'' ?]. eexists. by apply t_act_ctx.
Qed.

(** ** Irreducible terms *)

Definition irred (e : expr) : Prop := ∀ α e', ¬ tstep e α e'.

Lemma val_irred v : is_val v → irred v.
Proof. intros ? α e' ?. eauto using val_no_tstep. Qed.
