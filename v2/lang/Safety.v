(** * Safety of the untyped runtime (stage S1)

    The redex of a term ([act]), read once and offered once
    ([act_offer_sig], with [act_offer] as its corollary), progress for
    terms and for configurations, and preservation of closedness. A
    process that offers no step is terminated or stuck. *)

From stdpp Require Import relations.
From GV Require Export lang.Process.

(** ** Properties of processes *)

(** A terminated process has released every channel, its main thread
    is a value, and every spawned thread is ∗. *)
Definition terminated (p : proc) : Prop :=
  ∃ v E, p = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧ (∀ e, e ∈ E → e = EUnit).

Definition safe (p : proc) : Prop :=
  terminated p ∨ ∃ p', preduction p p'.

Definition deadlock_free (p : proc) : Prop :=
  ∀ p', pred_star p p' → safe p'.

(** ** The action offered by a term *)

Inductive action :=
  | ABeta
  | ANew (ℓ : family)
  | ANewAt (κ : field) (o : cend)
  | ASpawn (v : expr)
  | ARecv (o : cend)
  | ASend (o : cend) (v : expr)
  | AClose (o : cend)
  | ALink (o1 o2 : cend)
  | ASel (o : cend) (i : bool)
  | ABra (o : cend).

Global Instance action_eq_dec : EqDecision action.
Proof. solve_decision. Defined.

(** The redex of a saturated operator applied to a value. *)
Definition act_op (k : prim) (v : expr) : option action :=
  match k, v with
  | PSend, Pair w (Chan o) => Some (ASend o w)
  | PRecv, Chan o => Some (ARecv o)
  | PClose, Chan o => Some (AClose o)
  | PSel i, Chan o => Some (ASel o i)
  | PBra, Chan o => Some (ABra o)
  | PLink, Pair (Chan o1) (Chan o2) => Some (ALink o1 o2)
  | PSpawn, _ => Some (ASpawn v)
  | PForce, EBox _ => Some ABeta
  | PNewAt κ, Chan o => Some (ANewAt κ o)
  | _, _ => None
  end.

(** The redex of a term under the evaluation frames. *)
Fixpoint act (e : expr) : option action :=
  match e with
  | Var _ | EUnit | Chan _ | Lam _ | EBox _ => None
  | ENew ℓ => Some (ANew ℓ)
  | App e1 e2 =>
      if is_val e1 then
        if is_val e2 then match e1 with Lam _ => Some ABeta | _ => None end
        else act e2
      else act e1
  | Op k e1 => if is_val e1 then act_op k e1 else act e1
  | Pair e1 e2 => if is_val e1 then act e2 else act e1
  | LetU e1 _ =>
      if is_val e1 then match e1 with EUnit => Some ABeta | _ => None end
      else act e1
  | LetP e1 _ =>
      if is_val e1 then match e1 with Pair _ _ => Some ABeta | _ => None end
      else act e1
  | ELet e1 _ => if is_val e1 then Some ABeta else act e1
  | Inj1 e1 | Inj2 e1 => act e1
  | Case e1 _ _ =>
      if is_val e1 then match e1 with Inj1 _ | Inj2 _ => Some ABeta | _ => None end
      else act e1
  end.

(** The labels an action admits. *)
Definition offers (a : action) (α : tlabel) : Prop :=
  match a, α with
  | ABeta, LBeta => True
  | ANew ℓ, LNew ℓ' _ => ℓ = ℓ'
  | ANewAt κ o, LNewAt κ' o' _ => κ = κ' ∧ o = o'
  | ASpawn v, LSpawn M w => v = w ∧ M = fends v
  | ARecv o, LSess (SRecv o' w) => o = o' ∧ is_val w
  | ASend o v, LSess (SSend o' M w) => o = o' ∧ v = w ∧ M = fends v
  | AClose o, LSess (SClose o') => o = o'
  | ALink o1 o2, LSess (SLink os) => os = {[o1; o2]}
  | ASel o i, LSess (SSel o' i') => o = o' ∧ i = i'
  | ABra o, LSess (SBra o' _) => o = o'
  | _, _ => False
  end.

(** The channels a session action acts on, [None] for the silent ones. *)
Definition asubjs (a : action) : option (gset chan) :=
  match a with
  | ABeta | ANew _ | ANewAt _ _ | ASpawn _ => None
  | ARecv o | ASend o _ | AClose o | ASel o _ | ABra o => Some {[ech o]}
  | ALink o1 o2 => Some {[ech o1; ech o2]}
  end.

(** The ends a session action acts on. *)
Definition aends (a : action) : option (gset cend) :=
  match a with
  | ABeta | ANew _ | ANewAt _ _ | ASpawn _ => None
  | ARecv o | ASend o _ | AClose o | ASel o _ | ABra o => Some {[o]}
  | ALink o1 o2 => Some {[o1; o2]}
  end.

Lemma act_fill f e : frame_val f → ¬ is_val e → act (fill_frame f e) = act e.
Proof.
  intros Hf Hv. assert (is_val e = false) as Hv' by (destruct (is_val e); naive_solver).
  destruct f; simpl in *; rewrite ?Hv'; try done.
  all: by rewrite (is_val_true _ Hf), ?Hv'.
Qed.

Lemma act_val e : is_val e → act e = None.
Proof.
  induction e; simpl; intros Hv; try done; auto.
  apply andb_True in Hv as [H1 H2]. rewrite (is_val_true _ H1). auto.
Qed.

(** ** [act] is sound and complete for [tstep] *)

Lemma act_head e α e' : head_step e α e' → ∃ a, act e = Some a ∧ offers a α.
Proof.
  destruct 1; simpl;
    repeat match goal with
           | Hb : Is_true (is_val ?u) |- context [is_val ?u] => rewrite (is_val_true u Hb)
           end; simpl; (eexists; split; [reflexivity|simpl; auto]).
Qed.

Lemma act_step e α e' : tstep e α e' → ∃ a, act e = Some a ∧ offers a α.
Proof.
  induction 1 as [e α e' Hh|f e α e' Hf Hs IH]; [exact (act_head _ _ _ Hh)|].
  rewrite act_fill; [exact IH|exact Hf|]. intros Hv. exact (val_no_tstep e α e' Hs Hv).
Qed.

(** The step offered by an operator redex, with its continuation. *)
Lemma op_offer k v a α :
  is_val v → act_op k v = Some a → offers a α → {e' | head_step (Op k v) α e'}.
Proof.
  intros Hv Ha Hoff.
  destruct k; destruct v; simpl in Ha; try discriminate.
  all: repeat match type of Ha with
    | context [match ?w with _ => _ end] => destruct w; try discriminate
    end.
  all: injection Ha as <-; destruct α as [| | | |σ]; try destruct σ; simpl in Hoff;
    try contradiction; destruct_and?; subst.
  all: simpl in Hv; rewrite ?andb_True in Hv; destruct_and?.
  all: eexists; first [apply t_act_send|apply t_act_recv
    |match goal with |- head_step (ESpawn ?w) _ _ => apply (t_act_spawn w) end|apply t_act_close
    |apply t_act_select|apply t_act_branch|apply t_act_link|apply t_act_force|apply t_act_new_at]; simpl; rewrite ?andb_True; auto.
Qed.

(** [act_offer], once: an offered label has a step, computed. *)
Lemma act_offer_sig e a α : act e = Some a → offers a α → {e' | tstep e α e'}.
Proof.
  revert a α.
  induction e as [x| |o|e0 IH|e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2
                 |e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH|e1 IH|e0 IH0 e1 IH1 e2 IH2|e1 IH|ℓ|k e1 IH];
    simpl; intros a α Ha Hoff; try discriminate.
  - (* application *)
    destruct (is_val e1) eqn:Hb1;
      [|destruct (IH1 _ _ Ha Hoff) as [e1' Hst];
        exists (App e1' e2); by apply (t_act_ctx (FAppL e2))].
    destruct (is_val e2) eqn:Hb2;
      [|destruct (IH2 _ _ Ha Hoff) as [e2' Hst]; exists (App e1 e2');
        apply (t_act_ctx (FAppR e1)); [simpl; by rewrite Hb1|done]].
    destruct e1; try discriminate. injection Ha as <-. destruct α; try done.
    eexists. apply tstep_head, t_act_app. by rewrite Hb2.
  - (* pair *)
    destruct (is_val e1) eqn:Hb1.
    + destruct (IH2 _ _ Ha Hoff) as [e2' Hst]. exists (Pair e1 e2').
      apply (t_act_ctx (FPairR e1)); [simpl; by rewrite Hb1|done].
    + destruct (IH1 _ _ Ha Hoff) as [e1' Hst]. exists (Pair e1' e2).
      by apply (t_act_ctx (FPairL e2)).
  - (* let ∗ *)
    destruct (is_val e1) eqn:Hb1;
      [|destruct (IH1 _ _ Ha Hoff) as [e1' Hst]; exists (LetU e1' e2);
        by apply (t_act_ctx (FLetU e2))].
    destruct e1; try discriminate. injection Ha as <-. destruct α; try done.
    eexists. apply tstep_head, t_act_let_unit.
  - (* let pair *)
    destruct (is_val e1) eqn:Hb1;
      [|destruct (IH1 _ _ Ha Hoff) as [e1' Hst]; exists (LetP e1' e2);
        by apply (t_act_ctx (FLetP e2))].
    destruct e1 as [| | | | |u w| | | | | | | | |]; try discriminate.
    injection Ha as <-. destruct α; try done.
    pose proof (is_val_of_true _ Hb1) as Hv1. simpl in Hv1.
    apply andb_True in Hv1 as [Hu Hw].
    eexists. by apply tstep_head, t_act_let_pair.
  - (* let *)
    destruct (is_val e1) eqn:Hb1;
      [|destruct (IH1 _ _ Ha Hoff) as [e1' Hst]; exists (ELet e1' e2);
        by apply (t_act_ctx (FLet e2))].
    injection Ha as <-. destruct α; try done.
    eexists. apply tstep_head, t_act_let. by rewrite Hb1.
  - (* inl *)
    destruct (IH _ _ Ha Hoff) as [e1' Hst]. exists (Inj1 e1'). by apply (t_act_ctx FInj1).
  - (* inr *)
    destruct (IH _ _ Ha Hoff) as [e1' Hst]. exists (Inj2 e1'). by apply (t_act_ctx FInj2).
  - (* case *)
    destruct (is_val e0) eqn:Hb0;
      [|destruct (IH0 _ _ Ha Hoff) as [e0' Hst]; exists (Case e0' e1 e2);
        by apply (t_act_ctx (FCase e1 e2))].
    destruct e0 as [| | | | | | | | |v|v| | | |]; try discriminate;
      injection Ha as <-; destruct α; try done; simpl in Hb0.
    + eexists. apply tstep_head, t_act_case_inl. by rewrite Hb0.
    + eexists. apply tstep_head, t_act_case_inr. by rewrite Hb0.
  - (* new_ℓ *)
    injection Ha as <-. destruct α; try done. simpl in Hoff. subst.
    eexists. apply tstep_head, t_act_new.
  - (* operator *)
    destruct (is_val e1) eqn:Hb1;
      [|destruct (IH _ _ Ha Hoff) as [e1' Hst]; exists (Op k e1');
        by apply (t_act_ctx (FOp k))].
    destruct (op_offer k e1 a α) as [e' Hh]; [by rewrite Hb1|done|done|].
    exists e'. by apply tstep_head.
Qed.

Lemma act_offer e a α : act e = Some a → offers a α → ∃ e', tstep e α e'.
Proof. intros Ha Hoff. destruct (act_offer_sig e a α Ha Hoff) as [e' ?]. by exists e'. Qed.

(** ** Consequences at the term level *)

Lemma act_None_irred e : act e = None → irred e.
Proof. intros Ha α e' Hst. apply act_step in Hst as (a & ? & _). congruence. Qed.

Lemma act_send_val e o v : act e = Some (ASend o v) → is_val v.
Proof.
  intros Ha.
  destruct (act_offer _ _ (LSess (SSend o (fends v) v)) Ha (conj eq_refl (conj eq_refl eq_refl)))
    as [e' Hst].
  exact (tstep_label_val _ _ _ Hst).
Qed.

(** A label for every action. *)
Definition alabel (a : action) : tlabel :=
  match a with
  | ABeta => LBeta
  | ANew ℓ => LNew ℓ ""
  | ANewAt κ o => LNewAt κ o ""
  | ASpawn v => LSpawn (fends v) v
  | ARecv o => LSess (SRecv o EUnit)
  | ASend o v => LSess (SSend o (fends v) v)
  | AClose o => LSess (SClose o)
  | ALink o1 o2 => LSess (SLink {[o1; o2]})
  | ASel o i => LSess (SSel o i)
  | ABra o => LSess (SBra o false)
  end.

Lemma offers_alabel a : offers a (alabel a).
Proof. destruct a; simpl; auto. Qed.

(** Progress for terms: a term is irreducible or it steps. *)
Lemma tstep_progress e : irred e ∨ ∃ α e', tstep e α e'.
Proof.
  destruct (act e) as [a|] eqn:Ha; [right|left; by apply act_None_irred].
  destruct (act_offer _ _ (alabel a) Ha (offers_alabel a)) as [e' ?]. eauto.
Qed.

(** ** Reading an action back off a label *)

Lemma offers_beta a : offers a LBeta → a = ABeta.
Proof. by destruct a. Qed.
Lemma offers_new a ℓ c : offers a (LNew ℓ c) → a = ANew ℓ.
Proof. destruct a; try done. by intros ->. Qed.
Lemma offers_new_at a κ o c : offers a (LNewAt κ o c) → a = ANewAt κ o.
Proof. destruct a; try done. by intros [-> ->]. Qed.
Lemma offers_spawn a M v : offers a (LSpawn M v) → a = ASpawn v.
Proof. destruct a; try done. by intros [-> _]. Qed.
Lemma offers_send a o M v : offers a (LSess (SSend o M v)) → a = ASend o v.
Proof. destruct a; try done. by intros (-> & -> & _). Qed.
Lemma offers_recv a o v : offers a (LSess (SRecv o v)) → a = ARecv o.
Proof. destruct a; try done. by intros [-> _]. Qed.
Lemma offers_close a o : offers a (LSess (SClose o)) → a = AClose o.
Proof. destruct a; try done. by intros ->. Qed.
Lemma offers_link a os :
  offers a (LSess (SLink os)) → ∃ o1 o2, a = ALink o1 o2 ∧ os = {[o1; o2]}.
Proof. destruct a; try done. intros ->. eauto. Qed.
Lemma offers_sel a o i : offers a (LSess (SSel o i)) → a = ASel o i.
Proof. destruct a; try done. by intros [-> ->]. Qed.
Lemma offers_bra a o i : offers a (LSess (SBra o i)) → a = ABra o.
Proof. destruct a; try done. by intros ->. Qed.

Lemma offers_asubjs a σ : offers a (LSess σ) → asubjs a = Some (subjs σ).
Proof.
  destruct a, σ; simpl; try naive_solver.
  intros ->. f_equal. rewrite set_map_union_L, !set_map_singleton_L. done.
Qed.

Lemma asubjs_offers a S :
  asubjs a = Some S → {σ | subjs σ = S ∧ offers a (LSess σ)}.
Proof.
  destruct a as [|ℓ|κ o|v|o|o v|o|o1 o2|o i|o]; simpl; intros Hs; try discriminate;
    injection Hs as <-.
  - exists (SRecv o EUnit). by split.
  - exists (SSend o (fends v) v). by split.
  - exists (SClose o). by split.
  - exists (SLink {[o1; o2]}). split; [|done].
    simpl. by rewrite set_map_union_L, !set_map_singleton_L.
  - exists (SSel o i). by split.
  - exists (SBra o false). by split.
Qed.

Lemma aends_asubjs a : is_Some (aends a) ↔ is_Some (asubjs a).
Proof. destruct a; simpl; split; intros [? ?]; try discriminate; eauto. Qed.

(** ** Kinds of actions *)

(** A link costs nothing in the live table, so its redex is
    administrative. It is a session action too, because it names two
    ends. *)
Definition is_admin (a : action) : Prop :=
  match a with ABeta | ANew _ | ANewAt _ _ | ASpawn _ | ALink _ _ => True | _ => False end.

Definition is_sess (a : action) : Prop := is_Some (asubjs a).

Definition admin_lbl (α : tlabel) : Prop :=
  match α with
  | LBeta | LNew _ _ | LNewAt _ _ _ | LSpawn _ _ | LSess (SLink _) => True
  | LSess _ => False
  end.

Lemma offers_admin a α : offers a α → is_admin a ↔ admin_lbl α.
Proof. destruct a, α; simpl; try done; destruct σ; done. Qed.

(** ** Deciding the steps of a thread *)

Definition partner_ok (a : action) (b : option action) : Prop :=
  match a, b with
  | ARecv o, Some (ASend o' _) => o' = o‾
  | ASend o _, Some (ARecv o') => o' = o‾
  | AClose o, Some (AClose o') => o' = o‾
  | ASel o _, Some (ABra o') => o' = o‾
  | ABra o, Some (ASel o' _) => o' = o‾
  | _, _ => False
  end.

Global Instance partner_ok_dec a b : Decision (partner_ok a b).
Proof. destruct a, b as [[]|]; simpl; apply _. Defined.

(** A thread takes part in a closed step. *)
Definition tenabled (q : config) (t : nat) : Prop := ∃ ev q', itstep q ev q' ∧ t ∈ ev_parts ev.

Definition partner_need (C : gset chan) (M : gmap nat expr) (t : nat) (a : action) : Prop :=
  match a with
  | ABeta | ANew _ | ANewAt _ _ | ASpawn _ => True
  | ALink o1 o2 => ech o1 ∈ C ∨ ech o2 ∈ C
  | AClose o => ech o ∈ C ∧ ∃ j f, j ≠ t ∧ M !! j = Some f ∧ partner_ok a (act f)
  | _ => ∃ j f, j ≠ t ∧ M !! j = Some f ∧ partner_ok a (act f)
  end.

Lemma tenabled_act q t e : tenabled q t → q.2 !! t = Some e → ∃ a, act e = Some a.
Proof.
  intros (ev & q' & [Hst _] & Ht) He.
  destruct (istep_actor q ev q' t e Hst Ht He) as (α & e' & Hs & _).
  destruct (act_step _ _ _ Hs) as (a & Ha & _). by exists a.
Qed.

Lemma tenabled_partner C M t e a :
  tenabled (C, M) t → M !! t = Some e → act e = Some a → partner_need C M t a.
Proof.
  intros (ev & q' & [Hst Hτ] & Ht) He Ha.
  assert (∀ α e', tstep e α e' → offers a α) as Hoff.
  { intros α e' Hs. destruct (act_step _ _ _ Hs) as (a' & Ha' & Ho). congruence. }
  remember (C, M) as q0 eqn:Hq0.
  destruct Hst as [C0 M0 i e0 e0' Hi Hs|C0 M0 i e0 ℓ c e0' Hi Hs HC Hc
    |C0 M0 i e0 κ o c e0' Hi Hs HC Hc|C0 M0 i j e0 Mv v e0' Hi Hs Hj
    |C0 M0 i j o Mv v e0 e0' f f' Hij Hi Hj He0 Hf|C0 M0 i j o e0 e0' f f' Hij Hi Hj He0 Hf HC
    |C0 M0 i j o bb e0 e0' f f' Hij Hi Hj He0 Hf|C0 M0 i e0 o1 o2 e0' Hi Hs HC
    |C0 M0 i e0 σ e0' Hi Hs HC];
    injection Hq0 as -> ->; simpl in Ht, Hτ; try discriminate;
    set_unfold in Ht; destruct_or?; subst.
  all: repeat match goal with
    | H1 : ?M !! ?i = Some ?x, H2 : ?M !! ?i = Some ?y |- _ =>
        rewrite H1 in H2; injection H2 as <-
    end.
  - apply Hoff in Hs. destruct a; simpl in Hs |- *; tauto.
  - apply Hoff in Hs. destruct a; simpl in Hs |- *; tauto.
  - apply Hoff in Hs. destruct a; simpl in Hs |- *; tauto.
  - apply Hoff in Hs. destruct a; simpl in Hs |- *; tauto.
  - apply Hoff, offers_send in He0 as ->.
    destruct (act_step _ _ _ Hf) as (b & Hb & Hob). apply offers_recv in Hob as ->.
    simpl. exists j, f. split_and!; [done|done|by rewrite Hb].
  - apply Hoff, offers_recv in Hf as ->.
    destruct (act_step _ _ _ He0) as (b & Hb & Hob). apply offers_send in Hob as ->.
    simpl. exists i, e0. split_and!; [done|done|by rewrite Hb, edual_edual].
  - apply Hoff, offers_close in He0 as ->.
    destruct (act_step _ _ _ Hf) as (b & Hb & Hob). apply offers_close in Hob as ->.
    simpl. split; [done|]. exists j, f. split_and!; [done|done|by rewrite Hb].
  - apply Hoff, offers_close in Hf as ->.
    destruct (act_step _ _ _ He0) as (b & Hb & Hob). apply offers_close in Hob as ->.
    simpl. rewrite ech_edual. split; [done|]. exists i, e0.
    split_and!; [done|done|by rewrite Hb, edual_edual].
  - apply Hoff, offers_sel in He0 as ->.
    destruct (act_step _ _ _ Hf) as (b' & Hb & Hob). apply offers_bra in Hob as ->.
    simpl. exists j, f. split_and!; [done|done|by rewrite Hb].
  - apply Hoff, offers_bra in Hf as ->.
    destruct (act_step _ _ _ He0) as (b' & Hb & Hob). apply offers_sel in Hob as ->.
    simpl. exists i, e0. split_and!; [done|done|by rewrite Hb, edual_edual].
  - apply Hoff, offers_link in Hs as (o1' & o2' & -> & Hos). simpl.
    assert (o1 ∈ ({[o1'; o2']} : gset cend)) as Hin by (rewrite <-Hos; set_solver).
    set_unfold in Hin. destruct Hin as [->| ->]; auto.
Qed.

Lemma find_in_map {A} (M : gmap nat A) (P : nat → A → Prop) `{∀ j x, Decision (P j x)} :
  {jx : nat * A | M !! jx.1 = Some jx.2 ∧ P jx.1 jx.2} + {∀ j x, M !! j = Some x → ¬ P j x}.
Proof.
  destruct (list_find (λ jx : nat * A, P jx.1 jx.2) (map_to_list M)) as [[k [j x]]|] eqn:Hf.
  - left. exists (j, x). apply list_find_Some in Hf as (Hk & HP & _). split; [|done].
    apply elem_of_map_to_list. by eapply list_elem_of_lookup_2.
  - right. intros j x Hjx HP. apply list_find_None in Hf.
    apply (proj1 (List.Forall_forall _ _) Hf (j, x)); [|exact HP].
    apply list_elem_of_In, elem_of_map_to_list. done.
Qed.

(** Whether a thread takes part in a closed step, with the step. *)
Lemma try_thread (q : config) (t : nat) :
  {evq : event * config | itstep q evq.1 evq.2 ∧ t ∈ ev_parts evq.1} + {¬ tenabled q t}.
Proof.
  destruct q as [C M].
  destruct (M !! t) as [e|] eqn:He.
  2:{ right. intros (ev & q' & [Hst _] & Ht). destruct (istep_parts_some _ _ _ _ Hst Ht) as [? Hx].
      simpl in Hx. congruence. }
  destruct (act e) as [a|] eqn:Ha.
  2:{ right. intros Hen. destruct (tenabled_act _ _ _ Hen He) as [a Ha']. congruence. }
  pose proof (tenabled_partner C M t e a) as Hneed.
  destruct a as [|ℓ|κ o|v|o|o v|o|o1 o2|o i|o].
  - left. destruct (act_offer_sig e _ LBeta Ha I) as [e' Hs].
    exists (EvBeta t, (C, <[t := e']> M)). split; [split; [by eapply p_act_beta|done]|simpl; set_solver].
  - left. set (c := fresh (C ∪ echans (soup M))).
    assert (c ∉ C ∪ echans (soup M)) as Hc by apply is_fresh.
    destruct (act_offer_sig e _ (LNew ℓ c) Ha eq_refl) as [e' Hs].
    exists (EvNew t ℓ c, (C ∪ {[c]}, <[t := e']> M)).
    split; [split; [eapply p_act_new; [done|done|set_solver|set_solver]|done]|simpl; set_solver].
  - left. set (c := fresh (C ∪ echans (soup M))).
    assert (c ∉ C ∪ echans (soup M)) as Hc by apply is_fresh.
    destruct (act_offer_sig e _ (LNewAt κ o c) Ha (conj eq_refl eq_refl)) as [e' Hs].
    exists (EvNewAt t κ o c, (C ∪ {[c]}, <[t := e']> M)).
    split; [split; [eapply p_act_new_at; [done|done|set_solver|set_solver]|done]|simpl; set_solver].
  - left. destruct (act_offer_sig e _ (LSpawn (fends v) v) Ha (conj eq_refl eq_refl)) as [e' Hs].
    set (j := fresh (dom M)). assert (M !! j = None) as Hj by (apply not_elem_of_dom, is_fresh).
    exists (EvSpawn t j (fends v), (C, <[j := App v EUnit]> (<[t := e']> M))).
    split; [split; [by eapply p_act_spawn|done]|simpl; set_solver].
  - destruct (find_in_map M (λ j f, j ≠ t ∧ partner_ok (ARecv o) (act f)))
      as [[[j f] [Hj [Hjt Hok]]]|Hno].
    + left. simpl in *. destruct (act f) as [[| | | | |o' w| | | |]|] eqn:Hf; simpl in Hok; try done.
      subst o'.
      destruct (act_offer_sig f _ (LSess (SSend o‾ (fends w) w)) Hf
        (conj eq_refl (conj eq_refl eq_refl))) as [f' Hsf].
      destruct (act_offer_sig e _ (LSess (SRecv o w)) Ha
        (conj eq_refl (act_send_val f _ w Hf))) as [e' Hse].
      exists (EvMsg j t o‾ (fends w), (C, <[t := e']> (<[j := f']> M))).
      split; [split; [|done]|simpl; set_solver].
      eapply p_act_msg; [done|done|done|exact Hsf|]. by rewrite edual_edual.
    + right. intros Hen. destruct (Hneed Hen He Ha) as (j & f & Hjt & Hj & Hok).
      by apply (Hno j f Hj).
  - destruct (find_in_map M (λ j f, j ≠ t ∧ partner_ok (ASend o v) (act f)))
      as [[[j f] [Hj [Hjt Hok]]]|Hno].
    + left. simpl in *. destruct (act f) as [[| | | |o'| | | | |]|] eqn:Hf; simpl in Hok; try done.
      subst o'.
      destruct (act_offer_sig e _ (LSess (SSend o (fends v) v)) Ha
        (conj eq_refl (conj eq_refl eq_refl))) as [e' Hse].
      destruct (act_offer_sig f _ (LSess (SRecv o‾ v)) Hf
        (conj eq_refl (act_send_val e _ v Ha))) as [f' Hsf].
      exists (EvMsg t j o (fends v), (C, <[j := f']> (<[t := e']> M))).
      split; [split; [|done]|simpl; set_solver].
      eapply p_act_msg; [by apply not_eq_sym|done..].
    + right. intros Hen. destruct (Hneed Hen He Ha) as (j & f & Hjt & Hj & Hok).
      by apply (Hno j f Hj).
  - destruct (decide (ech o ∈ C)) as [HC|HC].
    2:{ right. intros Hen. by destruct (Hneed Hen He Ha) as [? _]. }
    destruct (find_in_map M (λ j f, j ≠ t ∧ partner_ok (AClose o) (act f)))
      as [[[j f] [Hj [Hjt Hok]]]|Hno].
    + left. simpl in *. destruct (act f) as [[| | | | | |o'| | |]|] eqn:Hf; simpl in Hok; try done.
      subst o'.
      destruct (act_offer_sig e _ (LSess (SClose o)) Ha eq_refl) as [e' Hse].
      destruct (act_offer_sig f _ (LSess (SClose o‾)) Hf eq_refl) as [f' Hsf].
      exists (EvClose t j o, (C ∖ {[ech o]}, <[j := f']> (<[t := e']> M))).
      split; [split; [|done]|simpl; set_solver].
      eapply p_act_close; [by apply not_eq_sym|done..].
    + right. intros Hen. destruct (Hneed Hen He Ha) as (_ & j & f & Hjt & Hj & Hok).
      by apply (Hno j f Hj).
  - destruct (act_offer_sig e _ (LSess (SLink {[o1; o2]})) Ha eq_refl) as [e' Hse].
    destruct (decide (ech o1 ∈ C)) as [HC|HC].
    { left. exists (EvLink t o1 o2, (C ∖ {[ech o1]}, emap (csub o1 o2) <$> (<[t := e']> M))).
      split; [split; [by eapply p_act_link|done]|simpl; set_solver]. }
    destruct (decide (ech o2 ∈ C)) as [HD|HD].
    { left. exists (EvLink t o2 o1, (C ∖ {[ech o2]}, emap (csub o2 o1) <$> (<[t := e']> M))).
      split; [split; [|done]|simpl; set_solver]. eapply p_act_link; [done| |done].
      by rewrite upair_comm. }
    right. intros Hen. by destruct (Hneed Hen He Ha).
  - destruct (find_in_map M (λ j f, j ≠ t ∧ partner_ok (ASel o i) (act f)))
      as [[[j f] [Hj [Hjt Hok]]]|Hno].
    + left. simpl in *. destruct (act f) as [[| | | | | | | | |o']|] eqn:Hf; simpl in Hok; try done.
      subst o'.
      destruct (act_offer_sig e _ (LSess (SSel o i)) Ha (conj eq_refl eq_refl)) as [e' Hse].
      destruct (act_offer_sig f _ (LSess (SBra o‾ i)) Hf eq_refl) as [f' Hsf].
      exists (EvChoice t j o i, (C, <[j := f']> (<[t := e']> M))).
      split; [split; [|done]|simpl; set_solver].
      eapply p_act_choice; [by apply not_eq_sym|done..].
    + right. intros Hen. destruct (Hneed Hen He Ha) as (j & f & Hjt & Hj & Hok).
      by apply (Hno j f Hj).
  - destruct (find_in_map M (λ j f, j ≠ t ∧ partner_ok (ABra o) (act f)))
      as [[[j f] [Hj [Hjt Hok]]]|Hno].
    + left. simpl in *. destruct (act f) as [[| | | | | | | |o' i|]|] eqn:Hf; simpl in Hok; try done.
      subst o'.
      destruct (act_offer_sig f _ (LSess (SSel o‾ i)) Hf (conj eq_refl eq_refl)) as [f' Hsf].
      destruct (act_offer_sig e _ (LSess (SBra o i)) Ha eq_refl) as [e' Hse].
      exists (EvChoice j t o‾ i, (C, <[t := e']> (<[j := f']> M))).
      split; [split; [|done]|simpl; set_solver].
      eapply p_act_choice; [done|done|done|exact Hsf|]. by rewrite edual_edual.
    + right. intros Hen. destruct (Hneed Hen He Ha) as (j & f & Hjt & Hj & Hok).
      by apply (Hno j f Hj).
Qed.

Lemma find_enabled (q : config) (ts : list nat) :
  {evq : event * config | itstep q evq.1 evq.2} + {∀ t, t ∈ ts → ¬ tenabled q t}.
Proof.
  induction ts as [|t ts IH].
  - right. intros t Ht. by apply elem_of_nil in Ht.
  - destruct (try_thread q t) as [[evq [Hs _]]|Hn]; [left; by exists evq|].
    destruct IH as [[evq Hs]|Hno]; [left; by exists evq|].
    right. intros u Hu. apply elem_of_cons in Hu as [->|Hu]; auto.
Qed.

(** A configuration without closed steps. *)
Definition stuck (q : config) : Prop := ∀ ev q', ¬ itstep q ev q'.

Lemma stuck_of q : (∀ t, t ∈ elements (dom q.2) → ¬ tenabled q t) → stuck q.
Proof.
  intros Hno ev q' Hs. destruct (istep_parts_nonempty _ _ _ (proj1 Hs)) as [t Ht].
  destruct (istep_parts_some _ _ _ _ (proj1 Hs) Ht) as [e He].
  apply (Hno t); [apply elem_of_elements, elem_of_dom; by exists e|by exists ev, q'].
Qed.

(** Whether some thread offers an external step. *)
Lemma find_offer (q : config) :
  {evq : event * config | istep q evq.1 evq.2}
  + {∀ t e a S, q.2 !! t = Some e → act e = Some a → asubjs a = Some S → ¬ S ## q.1}.
Proof.
  destruct q as [C M].
  assert (∀ (t : nat) e, Decision (∃ a S, act e = Some a ∧ asubjs a = Some S ∧ S ## C)) as Hdec.
  { intros t e. destruct (act e) as [a|]; [|right; naive_solver].
    destruct (asubjs a) as [S|] eqn:HS; [|right; naive_solver].
    destruct (decide (S ## C)); [left; eauto|right; naive_solver]. }
  destruct (@find_in_map _ M (λ t e, ∃ a S, act e = Some a ∧ asubjs a = Some S ∧ S ## C) Hdec)
    as [[[t e] [He Hok]]|Hno].
  - left. simpl in *. destruct (act e) as [a|] eqn:Ha; [|exfalso; naive_solver].
    destruct (asubjs a) as [S|] eqn:HS; [|exfalso; naive_solver].
    destruct (decide (S ## C)) as [HSC|HSC]; [|exfalso; naive_solver].
    destruct (asubjs_offers a S HS) as (σ & Hσ & Hoff).
    destruct (act_offer_sig e a (LSess σ) Ha Hoff) as [e' Hs].
    exists (EvSess t σ, (C ∖ sentc σ, <[t := e']> M)). simpl.
    eapply p_act_session; [done|done|by rewrite Hσ].
  - right. simpl. intros t e a S Ht Ha HS HSC. apply (Hno t e Ht). eauto.
Qed.

(** ** Progress *)

Theorem istep_progress q : (∀ ev q', ¬ istep q ev q') ∨ ∃ ev q', istep q ev q'.
Proof.
  destruct (find_enabled q (elements (dom q.2))) as [[[ev q'] [Hs _]]|Hno].
  { right. by exists ev, q'. }
  destruct (find_offer q) as [[[ev q'] Hs]|Hnoff].
  { right. by exists ev, q'. }
  left. intros ev q' Hs. destruct (decide (ev_tau ev)) as [Hτ|Hτ].
  - apply (stuck_of q Hno ev q'). by split.
  - destruct Hs as [| | | | | | | |C M i e σ e' Hi Hst HC]; try (by apply Hτ).
    destruct (act_step _ _ _ Hst) as (a & Ha & Hoff).
    apply (Hnoff i e a (subjs σ) Hi Ha); [by apply offers_asubjs|done].
Qed.

Theorem proc_progress p : pirred p ∨ ∃ π p', pstep p π p'.
Proof.
  destruct (erase_surj p) as [q <-].
  destruct (istep_progress q) as [Hno|(ev & q' & Hs)].
  - left. intros π p' Hs. destruct (pstep_lift q π p' Hs) as (ev & q' & Hs' & _).
    by apply (Hno ev q').
  - right. exists (ev_plabel ev), (erase q'). by apply istep_erase.
Qed.

(** ** Preservation of closedness *)

Lemma closed_at_rename e : ∀ n m r,
  closed_at n e → (∀ x, x < n → r x < m) → closed_at m (rename r e).
Proof.
  induction e; simpl; intros n m r Hc Hr; rewrite ?andb_True in Hc |- *; destruct_and?;
    split_and?; try done.
  all: try (repeat match goal with H : Is_true (bool_decide _) |- _ => apply bool_decide_unpack in H end;
    apply bool_decide_pack; by auto).
  all: first [eapply IHe|eapply IHe1|eapply IHe2|eapply IHe3]; [eassumption|].
  all: intros [|[|x]] Hx; simpl; unfold compose, upren, scons; simpl; try lia.
  all: try (apply Hr; lia).
  all: try (assert (x < n) as Hx' by lia; apply Hr in Hx'; lia).
  all: try (assert (S x < n) as Hx' by lia; apply Hr in Hx'; lia).
  all: try (assert (0 < n) as Hx' by lia; apply Hr in Hx'; lia).
Qed.

Lemma closed_at_subst e : ∀ n m σ,
  closed_at n e → (∀ x, x < n → closed_at m (σ x)) → closed_at m (subst σ e).
Proof.
  induction e; simpl; intros n m σ Hc Hσ; rewrite ?andb_True in Hc |- *; destruct_and?;
    split_and?; try done.
  all: try (repeat match goal with H : Is_true (bool_decide _) |- _ => apply bool_decide_unpack in H end;
    by auto).
  all: first [eapply IHe|eapply IHe1|eapply IHe2|eapply IHe3]; [eassumption|].
  all: intros [|[|x]] Hx; simpl; unfold compose; try done; try (apply bool_decide_pack; lia).
  all: try (apply Hσ; lia).
  all: rewrite ?rename_rename; eapply closed_at_rename; [apply Hσ; lia|]; intros; simpl; lia.
Qed.

Lemma closed_subst1 v e : closed_at 0 v → closed_at 1 e → closed_at 0 (subst1 v e).
Proof. intros Hv He. eapply closed_at_subst; [exact He|]. intros [|x] Hx; [done|lia]. Qed.

Lemma closed_subst2 u v e :
  closed_at 0 u → closed_at 0 v → closed_at 2 e → closed_at 0 (subst2 u v e).
Proof. intros Hu Hv He. eapply closed_at_subst; [exact He|]. intros [|[|x]] Hx; [done|done|lia]. Qed.

(** The values a label carries are closed. *)
Definition lclosed (α : tlabel) : Prop :=
  match α with
  | LSess (SRecv _ v) | LSess (SSend _ _ v) | LSpawn _ v => closed_at 0 v
  | _ => True
  end.

Lemma head_step_closed e α e' :
  head_step e α e' → closed_at 0 e →
  (match α with LSess (SRecv _ v) => closed_at 0 v | _ => True end) →
  closed_at 0 e' ∧ lclosed α.
Proof.
  destruct 1; simpl; intros Hc Hr; rewrite ?andb_True in Hc |- *; destruct_and?;
    split_and?; auto.
  - by apply closed_subst1.
  - by apply closed_subst1.
  - by apply closed_subst2.
  - by apply closed_subst1.
  - by apply closed_subst1.
  - by apply closed_subst1.
  - by destruct i.
Qed.

Lemma tstep_closed e α e' :
  tstep e α e' → closed_at 0 e →
  (match α with LSess (SRecv _ v) => closed_at 0 v | _ => True end) →
  closed_at 0 e' ∧ lclosed α.
Proof.
  induction 1 as [|f e α e' Hf Hs IH]; [by apply head_step_closed|].
  intros Hc Hr. destruct f; simpl in *; rewrite ?andb_True in Hc |- *; destruct_and?;
    destruct (IH ltac:(done) Hr); split_and?; done.
Qed.

(** Every thread of a configuration is closed. *)
Definition closed_conf (q : config) : Prop := ∀ i e, q.2 !! i = Some e → closed_at 0 e.

Lemma closed_emap g e n : closed_at n (emap g e) = closed_at n e.
Proof. revert n. induction e; intros n; simpl; by rewrite ?IHe, ?IHe1, ?IHe2, ?IHe3. Qed.

Lemma closed_conf_insert C C' M i e :
  closed_conf (C, M) → closed_at 0 e → closed_conf (C', <[i := e]> M).
Proof.
  intros HM He k ek Hk. simpl in Hk.
  apply lookup_insert_Some in Hk as [[<- <-]|[_ Hk]]; [done|]. by eapply HM.
Qed.

Theorem itstep_closed q ev q' : itstep q ev q' → closed_conf q → closed_conf q'.
Proof.
  intros [Hst Hτ] Hq.
  destruct Hst as [C M i e e' Hi Hst|C M i e ℓ c e' Hi Hst HC Hc|C M i e κ o c e' Hi Hst HC Hc
    |C M i j e Mv v e' Hi Hst Hj
    |C M i j o Mv v e e' f f' Hij Hi Hj He Hf|C M i j o e e' f f' Hij Hi Hj He Hf HC
    |C M i j o b e e' f f' Hij Hi Hj He Hf|C M i e o1 o2 e' Hi Hst HC
    |C M i e σ e' Hi Hst HC]; simpl in Hτ; try discriminate.
  all: try (eapply (closed_conf_insert C); [done|];
            by eapply (tstep_closed _ _ _ Hst); [eapply Hq|]).
  - (* spawn: the parent's continuation and the thunk applied to ∗ *)
    destruct (tstep_closed _ _ _ Hst) as [He' Hv]; [by eapply Hq|done|].
    eapply (closed_conf_insert C); [by eapply (closed_conf_insert C)|]. simpl in *. rewrite andb_True. by split.
  - (* the receiver gets the sender's value *)
    destruct (tstep_closed _ _ _ He) as [He' Hv]; [by eapply Hq|done|].
    eapply (closed_conf_insert C); [by eapply (closed_conf_insert C)|].
    by eapply (tstep_closed _ _ _ Hf); [eapply Hq|].
  - destruct (tstep_closed _ _ _ He) as [He' _]; [by eapply Hq|done|].
    eapply (closed_conf_insert C); [by eapply (closed_conf_insert C)|].
    by eapply (tstep_closed _ _ _ Hf); [eapply Hq|].
  - destruct (tstep_closed _ _ _ He) as [He' _]; [by eapply Hq|done|].
    eapply (closed_conf_insert C); [by eapply (closed_conf_insert C)|].
    by eapply (tstep_closed _ _ _ Hf); [eapply Hq|].
  - (* the link renames every thread *)
    destruct (tstep_closed _ _ _ Hst) as [He' _]; [by eapply Hq|done|].
    intros k ek Hk. simpl in Hk. apply lookup_fmap_Some in Hk as (ek0 & <- & Hk).
    rewrite closed_emap. apply lookup_insert_Some in Hk as [[<- <-]|[_ Hk]]; [done|by eapply Hq].
Qed.
