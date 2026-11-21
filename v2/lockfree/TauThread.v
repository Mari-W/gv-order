(** * No τ-divergence, thread by thread (stage S1)

    [no_tau_divergence] speaks about the whole process: from every
    reachable soup, administrative steps terminate. Lock freedom needs it
    for one thread: a thread that never takes a channel step takes
    finitely many administrative steps, whatever the other threads do
    meanwhile ([thread_acc]). The measure is the accessibility of the
    thread's term with every end erased ([cerase]). Erasing the ends makes
    the measure blind to the renaming of a link ([cerase_emap]) and to
    the choice of fresh names at a creation. *)

From stdpp Require Import relations.
From GV Require Export lockfree.Fair.

(** ** Administrative process steps *)

Definition padmin (p p' : proc) : Prop :=
  ∃ q ev q', erase q = p ∧ istep q ev q' ∧ erase q' = p' ∧ ev_admin ev.

Definition no_tau_divergence (p : proc) : Prop :=
  ∀ q, pred_star p q → Acc (λ y x, padmin x y) q.

Lemma padmin_preduction p p' : padmin p p' → preduction p p'.
Proof.
  intros (q & ev & q' & <- & Hst & <- & Had). unfold preduction.
  replace PTau with (ev_plabel ev) by (by destruct ev). by apply istep_erase.
Qed.

(** A lifting with a named thread. *)
Lemma lift_thread C E e : ∃ M i, M !! i = None ∧ soup M = E ∧
  erase (C, <[i := e]> M) = (C, E ⊎ {[+ e +]}).
Proof.
  destruct (soup_surj E) as [M HM].
  set (i := fresh (dom M)). assert (M !! i = None) as Hi by (apply not_elem_of_dom, is_fresh).
  exists M, i. split_and!; [done|done|]. unfold erase; simpl. by rewrite soup_insert, HM.
Qed.

Lemma padmin_beta C E e e' :
  tstep e LBeta e' → padmin (C, E ⊎ {[+ e +]}) (C, E ⊎ {[+ e' +]}).
Proof.
  intros Hs. destruct (lift_thread C E e) as (M & i & Hi & HM & Hq).
  exists (C, <[i := e]> M), (EvSolo i LBeta PickNone), (C, <[i := e']> (<[i := e]> M)). split_and!.
  - done.
  - eapply p_act_beta; [by rewrite lookup_insert_eq|done].
  - unfold erase; simpl. by rewrite insert_insert_eq, soup_insert, HM.
  - done.
Qed.

Lemma padmin_new C E e c e' :
  tstep e (LNew c) e' → c ∉ C → c ∉ echans E → c ∉ fchans e →
  padmin (C, E ⊎ {[+ e +]}) (C ∪ {[c]}, E ⊎ {[+ e' +]}).
Proof.
  intros Hs HC HE He. destruct (lift_thread C E e) as (M & i & Hi & HM & Hq).
  exists (C, <[i := e]> M), (EvSolo i (LNew c) PickNone), (C ∪ {[c]}, <[i := e']> (<[i := e]> M)). split_and!.
  - done.
  - eapply p_act_new; [by rewrite lookup_insert_eq|done|done|].
    rewrite soup_insert, HM, echans_disj_union, echans_singleton by done. set_solver.
  - unfold erase; simpl. by rewrite insert_insert_eq, soup_insert, HM.
  - done.
Qed.


Lemma padmin_spawn C E e v e' :
  tstep e (LSpawn v) e' →
  padmin (C, E ⊎ {[+ e +]}) (C, E ⊎ {[+ e' +]} ⊎ {[+ App v EUnit +]}).
Proof.
  intros Hs. destruct (lift_thread C E e) as (M & i & Hi & HM & Hq).
  assert (∃ j, <[i := e]> M !! j = None) as [j Hj]
    by (exists (fresh (dom (<[i := e]> M))); apply not_elem_of_dom, is_fresh).
  assert (i ≠ j) as Hij by (intros ->; by rewrite lookup_insert_eq in Hj).
  assert (M !! j = None) as HjM by (by rewrite lookup_insert_ne in Hj).
  exists (C, <[i := e]> M), (EvSolo i (LSpawn v) (PickChild j)),
    (C, <[j := App v EUnit]> (<[i := e']> (<[i := e]> M))). split_and!.
  - done.
  - eapply p_act_spawn; [by rewrite lookup_insert_eq|done|done].
  - unfold erase; simpl. rewrite insert_insert_eq, soup_insert by (by rewrite lookup_insert_ne).
    by rewrite soup_insert, HM.
  - done.
Qed.

Lemma padmin_link C E e o1 o2 e' :
  tstep e (LSess (SLink ({[o1]} ∪ {[o2]}))) e' → ech o1 ∈ C →
  padmin (C, E ⊎ {[+ e +]}) (C ∖ {[ech o1]}, emapE (csub o1 o2) (E ⊎ {[+ e' +]})).
Proof.
  intros Hs HC. destruct (lift_thread C E e) as (M & i & Hi & HM & Hq).
  exists (C, <[i := e]> M), (EvSolo i (LSess (SLink ({[o1]} ∪ {[o2]}))) (PickLink o1 o2)),
    (C ∖ {[ech o1]}, emap (csub o1 o2) <$> (<[i := e']> (<[i := e]> M))). split_and!.
  - done.
  - eapply p_act_link; [by rewrite lookup_insert_eq|done|done].
  - unfold erase, emapE; simpl. by rewrite soup_fmap, insert_insert_eq, soup_insert, HM.
  - done.
Qed.

(** ** Erasing every end *)

Definition cerase : expr → expr := emap (λ _, EPos "").

Lemma cerase_emap g e : cerase (emap g e) = cerase e.
Proof. unfold cerase. rewrite emap_emap. by apply emap_ext. Qed.

Lemma cerase_idem e : cerase (cerase e) = cerase e.
Proof. apply cerase_emap. Qed.

Lemma cerase_subst1 v e : cerase (subst1 v e) = subst1 (cerase v) (cerase e).
Proof. apply emap_subst1. Qed.
Lemma cerase_subst2 u v e : cerase (subst2 u v e) = subst2 (cerase u) (cerase v) (cerase e).
Proof. apply emap_subst2. Qed.

Definition serase (σ : slabel) : slabel :=
  match σ with
  | SSend _ v => SSend (EPos "") (cerase v)
  | SRecv _ v => SRecv (EPos "") (cerase v)
  | SClose _ => SClose (EPos "")
  | SSel _ i => SSel (EPos "") i
  | SBra _ i => SBra (EPos "") i
  | SLink os => SLink (set_map (λ _, EPos "") os)
  end.

Definition lerase (α : tlabel) : tlabel :=
  match α with
  | LBeta => LBeta
  | LNew _ => LNew ""
  | LSpawn v => LSpawn (cerase v)
  | LSess σ => LSess (serase σ)
  end.

Lemma set_map_erase_idem (M : gset cend) :
  set_map (λ _, EPos "") (set_map (λ _, EPos "") M : gset cend) = (set_map (λ _, EPos "") M : gset cend).
Proof. set_solver. Qed.

Lemma lerase_idem α : lerase (lerase α) = lerase α.
Proof. destruct α as [| | |[]]; simpl; by rewrite ?cerase_idem, ?set_map_erase_idem. Qed.

Lemma admin_lerase α : admin_lbl (lerase α) ↔ admin_lbl α.
Proof. destruct α as [| | |[]]; done. Qed.

(** An erased term steps with the erased label, to the erased result up
    to the names a creation picks. *)
Lemma tstep_cerase e α e' :
  tstep e α e' → ∃ x', tstep (cerase e) (lerase α) x' ∧ cerase x' = cerase e'.
Proof.
  induction 1 as [e α e' Hh|f e α e' Hf Hs (x' & Hx & Hxe)].
  - destruct Hh; simpl.
    all: try (eexists; split; [apply tstep_head; unfold cerase; simpl;
              constructor; by rewrite ?is_val_emap
              |fold cerase; rewrite ?cerase_subst1, ?cerase_subst2; simpl; fold cerase;
               by rewrite ?cerase_idem]).
    all: try (eexists; split; [apply tstep_head, (t_act_new _ "")|done]).
    all: try (eexists; split; [apply tstep_head, (t_act_new_at _ (EPos "") "")|done]).
    all: try (exists EUnit; split; [|done]; apply tstep_head; unfold cerase; simpl;
              rewrite <-fends_emap; apply t_act_spawn; by rewrite is_val_emap).
    all: try (exists (Chan (EPos "")); split; [|done]; apply tstep_head; unfold cerase; simpl;
              rewrite <-fends_emap; apply t_act_send; by rewrite is_val_emap).
    all: try (match goal with |- context [SRecv _ (cerase ?w)] =>
              exists (Pair (cerase w) (Chan (EPos ""))); split;
              [apply tstep_head; unfold cerase; simpl; apply t_act_recv; by rewrite is_val_emap
              |unfold cerase; simpl; by rewrite emap_emap] end).
    all: try (match goal with |- context [EForce (EBox ?b)] =>
              exists (subst1 (EBox (cerase b)) (cerase b)); split;
              [apply tstep_head, t_act_force
              |unfold cerase; rewrite !emap_subst1; simpl; rewrite !emap_emap; done] end).
    all: try (match goal with |- context [Inj ?i (Chan _)] =>
              exists (Inj i (Chan (EPos ""))); split; [apply tstep_head, t_act_branch|by destruct i]
              end).
    all: try (exists EUnit; split; [|done]; apply tstep_head; unfold cerase; simpl;
              rewrite set_map_union_L, !set_map_singleton_L; apply t_act_link).
  - exists (fill_frame (frame_emap (λ _, EPos "") f) x'). split.
    + unfold cerase at 1. rewrite emap_fill. apply t_act_ctx; [by apply frame_val_emap|done].
    + unfold cerase. rewrite !emap_fill. f_equal; [|done]. destruct f; simpl; f_equal; by rewrite ?cerase_idem.
Qed.

(** ** Steps are deterministic up to erasure *)

Lemma fill_frame_inj f f' e e' :
  frame_val f → frame_val f' → ¬ is_val e → ¬ is_val e' →
  fill_frame f e = fill_frame f' e' → f = f' ∧ e = e'.
Proof.
  intros Hf Hf' He He' Heq. destruct f, f'; simpl in *; simplify_eq; try done.
Qed.

Lemma tstep_det_cerase e α1 e1 α2 e2 :
  tstep e α1 e1 → tstep e α2 e2 → lerase α1 = lerase α2 → cerase e1 = cerase e2.
Proof.
  intros H1. revert α2 e2.
  induction H1 as [e α e' Hh|f e α e' Hf Hs IH]; intros α2 g2 H2 Hl.
  - apply tstep_inv in H2 as [Hh2|(f & e0 & e0' & Hf & -> & -> & Hs0)].
    + inversion Hh; subst; inversion Hh2; subst; simpl in *; simplify_eq; try done.
      all: unfold cerase in *; simpl; rewrite ?Hl; try done.
      all: by destruct i.
    + exfalso. apply (val_no_tstep e0 α2 e0' Hs0). by eapply head_redex_val.
  - apply tstep_inv in H2 as [Hh2|(f' & e0 & e0' & Hf' & Heq & -> & Hs0)].
    + exfalso. apply (val_no_tstep e α e' Hs). by eapply head_redex_val.
    + assert (¬ is_val e) as Hv1 by (intros Hv; exact (val_no_tstep e α e' Hs Hv)).
      assert (¬ is_val e0) as Hv2 by (intros Hv; exact (val_no_tstep e0 α2 e0' Hs0 Hv)).
      destruct (fill_frame_inj f f' e e0 Hf Hf' Hv1 Hv2 Heq) as [<- <-].
      unfold cerase. rewrite !emap_fill. f_equal. exact (IH _ _ Hs0 Hl).
Qed.

(** ** The measure *)

(** One administrative step of an erased term, erased again. *)
Definition tR (y x : expr) : Prop :=
  ∃ α x', admin_lbl α ∧ tstep x α x' ∧ y = cerase x'.

Lemma tR_step e α e' : admin_lbl α → tstep e α e' → tR (cerase e') (cerase e).
Proof.
  intros Hα Hs. destruct (tstep_cerase e α e' Hs) as (x' & Hx & Hxe).
  exists (lerase α), x'. split_and!; [by apply admin_lerase|done|done].
Qed.

(** Every link redex of a soup reachable from p has a restricted end.
    Typing supplies it. In the untyped semantics a thread may close a
    channel and then run a self link on it forever, which no process step
    fires. *)
Definition links_restricted (p : proc) : Prop :=
  ∀ q E e o1 o2, pred_star p q → q.2 = E ⊎ {[+ e +]} → act e = Some (ALink o1 o2) →
    ech o1 ∈ q.1 ∨ ech o2 ∈ q.1.

Lemma act_cerase e : act (cerase e) = amap (λ _, EPos "") <$> act e.
Proof. apply act_emap. Qed.

(** An admin-accessible soup has admin-accessible threads. *)
Lemma padmin_acc_thread p q :
  links_restricted p → pred_star p q →
  Acc (λ y x, padmin x y) q → ∀ E e, q.2 = E ⊎ {[+ e +]} → Acc tR (cerase e).
Proof.
  intros Hlr Hpq Hacc. revert Hpq.
  induction Hacc as [[C E0] _ IH]. intros Hpq E e HE. simpl in HE. subst E0.
  assert (∀ q', padmin (C, E ⊎ {[+ e +]}) q' → pred_star p q') as Hr'.
  { intros q' Hq'. etrans; [exact Hpq|]. apply rtc_once. by apply padmin_preduction. }
  constructor. intros y (α & x' & Hα & Hst & ->).
  destruct (act_step _ _ _ Hst) as (a' & Ha' & Ho). rewrite act_cerase in Ha'.
  destruct (act e) as [a|] eqn:Ha; [|done]. simpl in Ha'. injection Ha' as <-.
  assert (∀ α0 e0, tstep e α0 e0 → lerase α0 = lerase α → cerase x' = cerase e0) as Hdet.
  { intros α0 e0 Hs0 Hl. destruct (tstep_cerase e α0 e0 Hs0) as (x0 & Hx0 & <-).
    eapply tstep_det_cerase; [exact Hst|exact Hx0|]. by rewrite lerase_idem, Hl. }
  destruct a as [| |v|o|o v|o|o1 o2|o i|o]; simpl in Ho;
    destruct α as [|c1|M w|[| | | | |os]]; simpl in Hα; try contradiction.
  - (* β *)
    destruct (act_offer e ABeta LBeta Ha I) as [e' He'].
    rewrite (Hdet _ _ He' eq_refl).
    pose proof (padmin_beta C E e e' He') as Hpa.
    exact (IH _ Hpa (Hr' _ Hpa) E e' eq_refl).
  - (* new, at a globally fresh name *)
    set (c0 := fresh (C ∪ echans E ∪ fchans e)).
    assert (c0 ∉ C ∪ echans E ∪ fchans e) as Hc0 by apply is_fresh.
    destruct (act_offer e ANew (LNew c0) Ha I) as [e' He'].
    rewrite (Hdet _ _ He' ltac:(simpl in *; by subst)).
    pose proof (padmin_new C E e c0 e' He' ltac:(set_solver) ltac:(set_solver) ltac:(set_solver))
      as Hpa.
    exact (IH _ Hpa (Hr' _ Hpa) E e' eq_refl).
  - (* spawn *)
    destruct (act_offer e (ASpawn v) (LSpawn v) Ha eq_refl) as [e' He'].
    simpl in Ho. subst.
    rewrite (Hdet _ _ He' ltac:(simpl; fold cerase; by rewrite cerase_idem)).
    pose proof (padmin_spawn C E e v e' He') as Hpa.
    apply (IH _ Hpa (Hr' _ Hpa) (E ⊎ {[+ App v EUnit +]}) e'). simpl. multiset_solver.
  - (* link, at a restricted end *)
    destruct (act_offer e (ALink o1 o2) (LSess (SLink ({[o1]} ∪ {[o2]}))) Ha eq_refl) as [e' He'].
    simpl in Ho. subst os.
    rewrite (Hdet _ _ He' ltac:(simpl; f_equal; f_equal; set_solver)).
    assert (∀ p1 p2, tstep e (LSess (SLink ({[p1]} ∪ {[p2]}))) e' → ech p1 ∈ C →
              Acc tR (cerase e')) as Hlk.
    { intros p1 p2 Hs' Hc'. pose proof (padmin_link C E e p1 p2 e' Hs' Hc') as Hpa.
      rewrite <-(cerase_emap (csub p1 p2) e').
      apply (IH _ Hpa (Hr' _ Hpa) (emapE (csub p1 p2) E)).
      simpl. by rewrite emapE_disj_union, emapE_singleton. }
    destruct (Hlr (C, E ⊎ {[+ e +]}) E e o1 o2 Hpq eq_refl Ha) as [Hc|Hd]; simpl in *.
    + exact (Hlk o1 o2 He' Hc).
    + apply (Hlk o2 o1); [|done]. by rewrite upair_comm.
Qed.

(** Every thread of every reachable configuration is admin-accessible. *)
Theorem thread_acc p q s e :
  links_restricted p → no_tau_divergence p → pred_star p (erase q) →
  q.2 !! s = Some e → Acc tR (cerase e).
Proof.
  intros Hlr Hnd Hr He.
  apply (padmin_acc_thread p (erase q) Hlr Hr (Hnd _ Hr) (soup (delete s q.2))).
  simpl. by apply soup_delete.
Qed.
