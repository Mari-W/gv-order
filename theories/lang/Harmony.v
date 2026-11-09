(** * Harmony of a reduction semantics with the process LTS

    [red] is a reduction semantics on soups (C, E) with multi-frame
    evaluation contexts. It is defined without the labelled [tstep], so
    [harmony] (red p p' ↔ preduction p p') is a real theorem. CLOSE
    carries the c ∈ C premise of P-Act-Close, and NEW the freshness of
    P-Act-New. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Import lang.Semantics.

(** ** Evaluation contexts

    𝓔 ::= [] | 𝓔 e | v 𝓔 | ⟨𝓔,e⟩ | ⟨v,𝓔⟩ | let ∗ = 𝓔 in e
        | let ⟨a,b⟩ = 𝓔 in e | inj1 𝓔 | inj2 𝓔 | case 𝓔 (a.e)(a.e)

    as lists of the one-level frames of Semantics.v, innermost frame
    first; [ectx_val] enforces the value side condition on the
    right-of-value frames. *)

Definition ectx := list frame.

Fixpoint fill (K : ectx) (e : expr) : expr :=
  match K with
  | [] => e
  | f :: K' => fill K' (fill_frame f e)
  end.

Definition ectx_val (K : ectx) : Prop := Forall frame_val K.

(** ** The pure reduction M −→V M′ (label-free)

    The five β-redexes, then closure under evaluation contexts.
    This intentionally duplicates the LBeta cases of [head_step]:
    the reduction semantics must stand on its own. *)

Inductive head_red : expr → expr → Prop :=
  | HRedApp e v :
      is_val v →
      head_red (App (Lam e) v) (subst1 v e)
  | HRedLetU e :
      head_red (LetU EUnit e) e
  | HRedLetP u v e :
      is_val u → is_val v →
      head_red (LetP (Pair u v) e) (subst2 u v e)
  | HRedCase1 v e1 e2 :
      is_val v →
      head_red (Case (Inj1 v) e1 e2) (subst1 v e1)
  | HRedCase2 v e1 e2 :
      is_val v →
      head_red (Case (Inj2 v) e1 e2) (subst1 v e2)
  | HRedForce e :
      head_red (App EForce (EBox e)) (subst1 (EBox e) e)
  | HRedPay i x :
      head_red (App (Konst (KPay i)) (EPt x)) (EPt (pt_payload x i))
  | HRedSucc x :
      head_red (App (Konst KSucc) (EPt x)) (EPt (pt_shift 1 x)).

Definition vred (e e' : expr) : Prop :=
  ∃ K eh eh', ectx_val K ∧ e = fill K eh ∧ e' = fill K eh' ∧
              head_red eh eh'.

(** ** The reduction semantics on soups *)

Inductive red : proc → proc → Prop :=
  | RedLift C E e e' :                                  (* LIFTV *)
      vred e e' →
      red (C, E ⊎ {[+ e +]}) (C, E ⊎ {[+ e' +]})
  | RedNew C E K c x :                                  (* NEW *)
      ectx_val K →
      c ∉ C → c ∉ echans E → c ∉ fchans (fill K (App ENew (EPt x))) →
      red (C, E ⊎ {[+ fill K (App ENew (EPt x)) +]})
          (C ∪ {[c]}, E ⊎ {[+ fill K (Pair (Chan c (pt_pol x)) (Chan c (negb (pt_pol x)))) +]})
  | RedSpawn C E K v :                                  (* SPAWN *)
      ectx_val K → is_val v →
      red (C, E ⊎ {[+ fill K (App ESpawn v) +]})
          (C, E ⊎ {[+ fill K EUnit +]} ⊎ {[+ App v EUnit +]})
  | RedCom C E K K' v c b :                             (* COM *)
      ectx_val K → ectx_val K' → is_val v →
      red (C, E ⊎ {[+ fill K (App ESend (Pair v (Chan c b))) +]}
             ⊎ {[+ fill K' (App ERecv (Chan c (negb b))) +]})
          (C, E ⊎ {[+ fill K (Chan c b) +]}
             ⊎ {[+ fill K' (Pair v (Chan c (negb b))) +]})
  | RedClose C E K K' c b :                             (* CLOSE *)
      ectx_val K → ectx_val K' →
      c ∈ C →
      red (C, E ⊎ {[+ fill K (App EClos (Chan c b)) +]}
             ⊎ {[+ fill K' (App EClos (Chan c (negb b))) +]})
          (C ∖ {[c]},
           E ⊎ {[+ fill K EUnit +]} ⊎ {[+ fill K' EUnit +]})
  | RedChoice1 C E K K' c b :                           (* CHOICE, i = 1 *)
      ectx_val K → ectx_val K' →
      red (C, E ⊎ {[+ fill K (App ESel1 (Chan c b)) +]}
             ⊎ {[+ fill K' (App EBra (Chan c (negb b))) +]})
          (C, E ⊎ {[+ fill K (Chan c false) +]}
             ⊎ {[+ fill K' (Inj1 (Chan c true)) +]})
  | RedChoice2 C E K K' c b :                           (* CHOICE, i = 2 *)
      ectx_val K → ectx_val K' →
      red (C, E ⊎ {[+ fill K (App ESel2 (Chan c b)) +]}
             ⊎ {[+ fill K' (App EBra (Chan c (negb b))) +]})
          (C, E ⊎ {[+ fill K (Chan c false) +]}
             ⊎ {[+ fill K' (Inj2 (Chan c true)) +]})
  | RedLinkL C E K c bc d bd :                          (* LINK *)
      (* the paper's rule: the removed end is restricted and the whole
         resulting configuration is substituted; the two rules are the
         two orientations of the unordered pair over ordered syntax.
         The ends need not differ — a self-forwarding on a restricted
         name substitutes by the identity and releases the name, and
         the LTS admits it, so harmony would fail if [red] did not. *)
      ectx_val K → c ∈ C →
      red (C, E ⊎ {[+ fill K (App ELink (Pair (Chan c bc) (Chan d bd))) +]})
          (C ∖ {[c]}, echsubst c d (E ⊎ {[+ fill K EUnit +]}))
  | RedLinkR C E K c bc d bd :
      ectx_val K → d ∈ C →
      red (C, E ⊎ {[+ fill K (App ELink (Pair (Chan c bc) (Chan d bd))) +]})
          (C ∖ {[d]}, echsubst d c (E ⊎ {[+ fill K EUnit +]})).

(** ** The context/label bridge

    [fill_tstep]: filling a step into an evaluation context is a step
    (iterated [tstep_fill]).  [tstep_fill_decomp]: every labelled step
    decomposes as an evaluation context around a head step (induction
    on [tstep]; each congruence rule appends one frame, its value side
    condition supplying [ectx_val]). *)

Lemma fill_app K K' e : fill (K ++ K') e = fill K' (fill K e).
Proof. revert e. induction K as [|f K IH]; intros e; simpl; auto. Qed.

Lemma ectx_val_app K K' :
  ectx_val K → ectx_val K' → ectx_val (K ++ K').
Proof. apply Forall_app_2. Qed.

Lemma ectx_val_frame f : frame_val f → ectx_val [f].
Proof. intros Hf. by apply Forall_singleton. Qed.

Lemma fill_tstep K e α e' :
  ectx_val K → tstep e α e' → tstep (fill K e) α (fill K e').
Proof.
  revert e e'. induction K as [|f K IH]; intros e e' HK Hst; simpl;
    [done|].
  apply Forall_cons in HK as [Hf HK].
  apply IH; [done|]. by apply tstep_fill.
Qed.

Lemma tstep_fill_decomp e α e' :
  tstep e α e' →
  ∃ K eh eh', ectx_val K ∧ e = fill K eh ∧ e' = fill K eh' ∧
              head_step eh α eh'.
Proof.
  induction 1 as
    [f0 β f1 Hh
    |f0 β f1 g0 Hst IH|v0 g0 β g1 Hv Hst IH
    |f0 β f1 g0 Hst IH|v0 g0 β g1 Hv Hst IH
    |f0 β f1 g0 Hst IH|f0 β f1 g0 Hst IH
    |f0 β f1 Hst IH|f0 β f1 Hst IH|f0 β f1 g0 g1 Hst IH];
    [exists [], f0, f1; split_and!; [apply Forall_nil; done|done..]|..];
    destruct IH as (K & eh & eh' & HK & -> & -> & Hh);
    [ exists (K ++ [FAppL g0]), eh, eh'
    | exists (K ++ [FAppR v0]), eh, eh'
    | exists (K ++ [FPairL g0]), eh, eh'
    | exists (K ++ [FPairR v0]), eh, eh'
    | exists (K ++ [FLetU g0]), eh, eh'
    | exists (K ++ [FLetP g0]), eh, eh'
    | exists (K ++ [FInj1]), eh, eh'
    | exists (K ++ [FInj2]), eh, eh'
    | exists (K ++ [FCase g0 g1]), eh, eh' ];
    rewrite !fill_app; simpl;
    (split_and!; [|done..]);
    (apply ectx_val_app; [done|apply ectx_val_frame; done]).
Qed.

(** ** Pure reduction vs β-labelled steps *)

Lemma head_red_head_step e e' : head_red e e' → head_step e LBeta e'.
Proof. destruct 1; by constructor. Qed.

Lemma head_step_beta_head_red e e' : head_step e LBeta e' → head_red e e'.
Proof. inversion 1; by constructor. Qed.

Lemma vred_reduction e e' : vred e e' ↔ reduction e e'.
Proof.
  split.
  - intros (K & eh & eh' & HK & -> & -> & Hh).
    apply fill_tstep; [done|]. apply TStepHead.
    by apply head_red_head_step.
  - intros Hst.
    apply tstep_fill_decomp in Hst as (K & eh & eh' & HK & -> & -> & Hh).
    exists K, eh, eh'. split_and!; try done.
    by apply head_step_beta_head_red.
Qed.

(** ** Harmony *)

Theorem harmony_forward p p' : red p p' → preduction p p'.
Proof.
  destruct 1 as
    [C E e e' Hv|C E K c x HK Hc1 Hc2 Hc3|C E K v HK Hval
    |C E K K' v c b HK HK' Hval|C E K K' c b HK HK' Hc
    |C E K K' c b HK HK'|C E K K' c b HK HK'
    |C E K c bc d bd HK Hc|C E K c bc d bd HK Hd].
  - apply PStepBeta. by apply vred_reduction.
  - eapply PStepNew; [|done|done|done].
    apply fill_tstep; [done|]. apply TStepHead. apply HeadNew.
  - apply PStepSpawn.
    apply fill_tstep; [done|]. apply TStepHead. by apply HeadSpawn.
  - eapply PStepMsg.
    + apply fill_tstep; [done|]. apply TStepHead. by apply HeadSend.
    + apply fill_tstep; [done|]. apply TStepHead. by apply HeadRecv.
  - eapply PStepClose; [..|done].
    + apply fill_tstep; [done|]. apply TStepHead. apply HeadClos.
    + apply fill_tstep; [done|]. apply TStepHead. apply HeadClos.
  - eapply (PStepChoice _ _ _ _ false).
    + apply fill_tstep; [done|]. apply TStepHead. apply HeadSel1.
    + apply fill_tstep; [done|]. apply TStepHead. apply (HeadBra _ _ false).
  - eapply (PStepChoice _ _ _ _ true).
    + apply fill_tstep; [done|]. apply TStepHead. apply HeadSel2.
    + apply fill_tstep; [done|]. apply TStepHead. apply (HeadBra _ _ true).
  - eapply PStepLink; [|done].
    apply fill_tstep; [done|]. apply TStepHead. by apply HeadLink.
  - eapply PStepLink; [|done].
    rewrite upair_comm.
    apply fill_tstep; [done|]. apply TStepHead. by apply HeadLink.
Qed.

(** Head inversion for forwarding, keeping the label pair abstract so
    the unordered-set equation stays at the [gset] level (a bare
    [inversion] would inject through the mapset record). *)
Lemma head_step_link_inv e cd e' :
  head_step e (LSess (SLink cd)) e' →
  ∃ c bc d bd, e = App ELink (Pair (Chan c bc) (Chan d bd)) ∧ cd = {[(c, bc); (d, bd)]} ∧
         e' = EUnit.
Proof. inversion 1; eauto 8. Qed.

Theorem harmony_backward p p' : preduction p p' → red p p'.
Proof.
  intros Hst; inversion Hst; subst.
  - (* P-Act-Beta *)
    apply RedLift. by apply vred_reduction.
  - (* P-Act-New *)
    match goal with H : tstep _ (LNew _ _) _ |- _ =>
      apply tstep_fill_decomp in H as (K & eh & eh' & HK & -> & -> & Hh)
    end.
    inversion Hh; subst.
    by apply RedNew.
  - (* P-Act-Spawn *)
    match goal with H : tstep _ (LSpawn _) _ |- _ =>
      apply tstep_fill_decomp in H as (K & eh & eh' & HK & -> & -> & Hh)
    end.
    inversion Hh; subst.
    by apply RedSpawn.
  - (* P-Act-Msg *)
    match goal with H : tstep _ (LSess (SSend _ _)) _ |- _ =>
      apply tstep_fill_decomp in H as (K & eh & eh' & HK & -> & -> & Hh)
    end.
    match goal with H : tstep _ (LSess (SRecv _ _)) _ |- _ =>
      apply tstep_fill_decomp in H
        as (K' & fh & fh' & HK' & -> & -> & Hh')
    end.
    inversion Hh; subst. inversion Hh'; subst.
    by apply RedCom.
  - (* P-Act-Close *)
    match goal with H : tstep _ (LSess (SClos _)) _ |- _ =>
      apply tstep_fill_decomp in H as (K & eh & eh' & HK & -> & -> & Hh)
    end.
    match goal with H : tstep _ (LSess (SClos _)) _ |- _ =>
      apply tstep_fill_decomp in H
        as (K' & fh & fh' & HK' & -> & -> & Hh')
    end.
    inversion Hh; subst. inversion Hh'; subst.
    by apply RedClose.
  - (* P-Act-Choice *)
    match goal with H : tstep _ (LSess (SSel _ _)) _ |- _ =>
      apply tstep_fill_decomp in H as (K & eh & eh' & HK & -> & -> & Hh)
    end.
    match goal with H : tstep _ (LSess (SBra _ _)) _ |- _ =>
      apply tstep_fill_decomp in H
        as (K' & fh & fh' & HK' & -> & -> & Hh')
    end.
    inversion Hh; subst; inversion Hh'; subst.
    + by apply RedChoice1.
    + by apply RedChoice2.
  - (* P-Act-Link: recover the orientation of the pair *)
    match goal with H : tstep _ (LSess (SLink _)) _ |- _ =>
      apply tstep_fill_decomp in H as (K & eh & eh' & HK & -> & -> & Hh)
    end.
    apply head_step_link_inv in Hh as (c0 & bc0 & d0 & bd0 & -> & Hp & ->).
    destruct (decide ((c0, bc0) = (d0, bd0))) as [Heq0|Hne0].
    + (* the term names one end twice, so the label's two ends
         coincide with it and the rule fires degenerately *)
      injection Heq0 as -> ->.
      assert ((c, bc) = (d0, bd0)) as Hc0.
      { assert ((c, bc) ∈ ({[(d0, bd0); (d0, bd0)]} : gset cend)) as Hin
          by (rewrite <-Hp; clear; set_solver).
        clear -Hin. set_solver. }
      assert ((d, bd) = (d0, bd0)) as Hd0.
      { assert ((d, bd) ∈ ({[(d0, bd0); (d0, bd0)]} : gset cend)) as Hin
          by (rewrite <-Hp; clear; set_solver).
        clear -Hin. set_solver. }
      injection Hc0 as -> ->. injection Hd0 as -> ->.
      by apply RedLinkL.
    + destruct (upair_eq_inv _ _ _ _ (eq_sym Hp) Hne0)
        as [[Ha Hb]|[Ha Hb]]; injection Ha as <- <-; injection Hb as <- <-.
      * by apply RedLinkL.
      * by apply RedLinkR.
Qed.

Theorem harmony p p' : red p p' ↔ preduction p p'.
Proof. split; [apply harmony_forward|apply harmony_backward]. Qed.
