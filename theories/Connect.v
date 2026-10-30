(** * P-Connect (§11)

    Two components, each P-related in the same world, compose over a
    cut C₀: components at n give the composite at n (sharp edges 45).
    The world W₁ ⊔ W₂ of the spec's statement enters through
    monotonicity at the end ([Prel_connect]).

    The proof goes by induction on n and, at a fixed level S n', by
    induction on the syntactic size of the composite's soup. Every
    giving step (send, close, link, and the τ of P-Act-Link) removes a
    redex and leaves the soup strictly smaller, while renaming,
    junk substitution and fusion of the other component keep its size
    (sharp edges 46). *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export Internalize.

(** ** The size of a soup *)

Fixpoint esize (e : expr) : nat :=
  match e with
  | Var _ | EUnit | Konst _ | Chan _ => 1
  | Lam e | Inj1 e | Inj2 e | EBox e => S (esize e)
  | App e1 e2 | Pair e1 e2 | LetU e1 e2 | LetP e1 e2 => S (esize e1 + esize e2)
  | Case e e1 e2 => S (esize e + esize e1 + esize e2)
  end.

Definition msize (E : gmultiset expr) : nat := sum_list (esize <$> elements E).

Lemma msize_empty : msize ∅ = 0.
Proof. unfold msize. by rewrite gmultiset_elements_empty. Qed.

Lemma msize_disj_union E1 E2 : msize (E1 ⊎ E2) = msize E1 + msize E2.
Proof.
  unfold msize. rewrite gmultiset_elements_disj_union, fmap_app, sum_list_with_app.
  done.
Qed.

Lemma msize_singleton e : msize {[+ e +]} = esize e.
Proof. unfold msize. rewrite gmultiset_elements_singleton. simpl. lia. Qed.

Lemma esize_chsubst c d e : esize (chsubst c d e) = esize e.
Proof. induction e; simpl; lia. Qed.

Lemma esize_eswap a b e : esize (eswap a b e) = esize e.
Proof. induction e; simpl; lia. Qed.

Lemma msize_echsubst c d E : msize (echsubst c d E) = msize E.
Proof.
  induction E as [|e E IH] using gmultiset_ind.
  - by rewrite echsubst_empty.
  - rewrite echsubst_disj_union, echsubst_singleton, !msize_disj_union, !msize_singleton.
    by rewrite esize_chsubst, IH.
Qed.

Lemma msize_msswap a b E : msize (msswap a b E) = msize E.
Proof.
  induction E as [|e E IH] using gmultiset_ind.
  - unfold msswap. by rewrite gmultiset_map_empty.
  - rewrite msswap_disj_union, msswap_singleton, !msize_disj_union, !msize_singleton.
    by rewrite esize_eswap, IH.
Qed.

(** Giving steps of a thread shrink it. *)
Definition giving (σ : slabel) : Prop :=
  match σ with SRecv _ _ => False | _ => True end.

Lemma tstep_giving_size e σ e' : tstep e (LSess σ) e' → giving σ → esize e' < esize e.
Proof.
  intros H Hg. remember (LSess σ) as α eqn:Hα. revert Hα.
  induction H as [e α e' Hh| | | | | | | | | ]; intros ->; simpl;
    try (specialize (IHtstep eq_refl); lia).
  inversion Hh; subst; simpl; try done; lia.
Qed.

(** ** Configurations over a cut

    Component 1 runs at TA, component 2 at TB, one of them at T and
    the other at ∗, so that the two roles are symmetric. *)

Definition ctys (TA TB T : ty) : Prop := (TA = T ∧ TB = TUnit) ∨ (TA = TUnit ∧ TB = T).

Lemma ctys_sym TA TB T : ctys TA TB T → ctys TB TA T.
Proof. unfold ctys. naive_solver. Qed.

Lemma ctys_prim TA TB T : prim T → ctys TA TB T → prim TA ∧ prim TB.
Proof. intros HT [[-> ->]|[-> ->]]; split; try done; constructor. Qed.

(** The implicit well-formedness of the spec's P-Connect: dual cut
    ends at aliased points, the restricted sets and the interfaces
    pairwise disjoint. *)
Record cut_ok (W : world) (Σ1 Σ2 ΣC ΣC' : senv) (C0 C1 C2 : gset chan) : Prop := {
  co_strict : strict W;
  co_d1 : Σ1 ##ₘ ΣC;
  co_d2 : Σ2 ##ₘ ΣC';
  co_d12 : Σ1 ##ₘ Σ2;
  co_dom : dom ΣC = C0;
  co_dom' : dom ΣC' = C0;
  co_cut : ∀ c e e', ΣC !! c = Some e → ΣC' !! c = Some e' →
             w_eq W e.2 e'.2 ∧ sdual e.1 e'.1;
  co_C1Σ2 : C1 ## dom Σ2;
  co_C2Σ1 : C2 ## dom Σ1;
  co_C1Σ1 : C1 ## dom Σ1;
  co_C2Σ2 : C2 ## dom Σ2;
  co_C10 : C1 ## C0;
  co_C20 : C2 ## C0;
  co_C12 : C1 ## C2
}.

Lemma cut_ok_sym W Σ1 Σ2 ΣC ΣC' C0 C1 C2 :
  cut_ok W Σ1 Σ2 ΣC ΣC' C0 C1 C2 → cut_ok W Σ2 Σ1 ΣC' ΣC C0 C2 C1.
Proof.
  intros [HW ? ? ? ? ? Hcut ? ? ? ? ? ? ?]. split; try done; try by symmetry.
  intros c e e' H1 H2. destruct (Hcut c e' e H2 H1) as [Hq Hd].
  split; [by apply (wf_eq_sym _ (proj1 HW))|by apply sdual_sym].
Qed.

Section cut_facts.
  Context (W : world) (Σ1 Σ2 ΣC ΣC' : senv) (C0 C1 C2 : gset chan).
  Context (H : cut_ok W Σ1 Σ2 ΣC ΣC' C0 C1 C2).

  Lemma co_Σ1C0 : dom Σ1 ## C0.
  Proof. rewrite <-(co_dom _ _ _ _ _ _ _ _ H). apply map_disjoint_dom, (co_d1 _ _ _ _ _ _ _ _ H). Qed.

  Lemma co_Σ2C0 : dom Σ2 ## C0.
  Proof. rewrite <-(co_dom' _ _ _ _ _ _ _ _ H). apply map_disjoint_dom, (co_d2 _ _ _ _ _ _ _ _ H). Qed.

  Lemma co_dom_a : dom (Σ1 ∪ ΣC) = dom Σ1 ∪ C0.
  Proof. by rewrite dom_union_L, (co_dom _ _ _ _ _ _ _ _ H). Qed.

  Lemma co_dom_b : dom (Σ2 ∪ ΣC') = dom Σ2 ∪ C0.
  Proof. by rewrite dom_union_L, (co_dom' _ _ _ _ _ _ _ _ H). Qed.

  Lemma co_union_comm : Σ1 ∪ Σ2 = Σ2 ∪ Σ1.
  Proof. apply map_union_comm, (co_d12 _ _ _ _ _ _ _ _ H). Qed.
End cut_facts.

Lemma union3_comm (C0 C1 C2 : gset chan) : C2 ∪ C1 ∪ C0 = C1 ∪ C2 ∪ C0.
Proof. set_solver. Qed.

(** The goal at level n. *)
Definition conn_at (n : nat) (T : ty) : Prop :=
  ∀ W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA TB,
    ctys TA TB T → cut_ok W Σ1 Σ2 ΣC ΣC' C0 C1 C2 →
    Prel n W (Σ1 ∪ ΣC) TA (C1, E1) → Prel n W (Σ2 ∪ ΣC') TB (C2, E2) →
    Prel n W (Σ1 ∪ Σ2) T (C1 ∪ C2 ∪ C0, E1 ⊎ E2).

(** The goal at level n for soups below size m. *)
Definition conn_lt (n : nat) (T : ty) (m : nat) : Prop :=
  ∀ W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 TA TB,
    msize (E1 ⊎ E2) < m →
    ctys TA TB T → cut_ok W Σ1 Σ2 ΣC ΣC' C0 C1 C2 →
    Prel n W (Σ1 ∪ ΣC) TA (C1, E1) → Prel n W (Σ2 ∪ ΣC') TB (C2, E2) →
    Prel n W (Σ1 ∪ Σ2) T (C1 ∪ C2 ∪ C0, E1 ⊎ E2).

(** ** Soups *)

Lemma gmultiset_split_in (E1 E2 E0 : gmultiset expr) (e : expr) :
  E1 ⊎ E2 = E0 ⊎ {[+ e +]} →
  (∃ F1, E1 = F1 ⊎ {[+ e +]} ∧ E0 = F1 ⊎ E2) ∨
  (∃ F2, E2 = F2 ⊎ {[+ e +]} ∧ E0 = E1 ⊎ F2).
Proof.
  intros Heq. assert (e ∈ E1 ⊎ E2) as He by (rewrite Heq; multiset_solver).
  apply gmultiset_elem_of_disj_union in He as [He|He].
  - left. exists (E1 ∖ {[+ e +]}). split; [multiset_solver|].
    apply (inj (.⊎ {[+ e +]})). rewrite <-Heq. multiset_solver.
  - right. exists (E2 ∖ {[+ e +]}). split; [multiset_solver|].
    apply (inj (.⊎ {[+ e +]})). rewrite <-Heq. multiset_solver.
Qed.

Lemma gmultiset_split_in2 (E1 E2 E0 : gmultiset expr) (e f : expr) :
  E1 ⊎ E2 = E0 ⊎ {[+ e +]} ⊎ {[+ f +]} →
  (∃ F1, E1 = F1 ⊎ {[+ e +]} ⊎ {[+ f +]} ∧ E0 = F1 ⊎ E2) ∨
  (∃ F2, E2 = F2 ⊎ {[+ e +]} ⊎ {[+ f +]} ∧ E0 = E1 ⊎ F2) ∨
  (∃ F1 F2, E1 = F1 ⊎ {[+ e +]} ∧ E2 = F2 ⊎ {[+ f +]} ∧ E0 = F1 ⊎ F2) ∨
  (∃ F1 F2, E1 = F1 ⊎ {[+ f +]} ∧ E2 = F2 ⊎ {[+ e +]} ∧ E0 = F1 ⊎ F2).
Proof.
  intros Heq.
  destruct (gmultiset_split_in _ _ _ _ Heq) as [(G1 & -> & HG)|(G2 & -> & HG)].
  - destruct (gmultiset_split_in _ _ _ _ (eq_sym HG)) as [(H1 & -> & HH)|(H2 & -> & HH)].
    + left. exists H1. split; [done|]. apply (inj (.⊎ {[+ e +]})). rewrite HH. multiset_solver.
    + right; right; right. exists G1, H2. split_and!; [done|done|].
      apply (inj (.⊎ {[+ e +]})). rewrite HH. multiset_solver.
  - destruct (gmultiset_split_in _ _ _ _ (eq_sym HG)) as [(H1 & -> & HH)|(H2 & -> & HH)].
    + right; right; left. exists H1, G2. split_and!; [done|done|].
      apply (inj (.⊎ {[+ e +]})). rewrite HH. multiset_solver.
    + right; left. exists H2. split; [done|]. apply (inj (.⊎ {[+ e +]})). rewrite HH. multiset_solver.
Qed.

(** A soup of values with nothing restricted does not step. *)
Lemma vals_pirred (E : gmultiset expr) :
  (∀ e, e ∈ E → is_val e) → pirred (∅, E).
Proof.
  intros Hv π p' Hst. inversion Hst; subst;
    match goal with H : tstep ?e _ _ |- _ =>
      apply (val_no_tstep e _ _ H), Hv; multiset_solver end.
Qed.


(** ** Termination and readiness of the composite *)

Lemma tenv_of_empty_inv (Σ : senv) : tenv_of Σ = ∅ → Σ = ∅.
Proof.
  intros H. apply map_empty. intros c. pose proof (f_equal (lookup c) H) as Hc.
  unfold tenv_of in Hc. rewrite lookup_fmap, lookup_empty in Hc.
  by destruct (Σ !! c).
Qed.

Lemma Prel_S_stop_prim n W Σ T p :
  Prel (S n) W Σ T p → prim T → pirred p →
  Σ = ∅ ∧ ∃ v E, p = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧ Vrel (S n) W ∅ T v ∧
                 (∀ e, e ∈ E → e = EUnit).
Proof.
  intros HP HT Hirr. destruct (Prel_S_irred _ _ _ _ _ HP Hirr) as (v & E & -> & Hv & HV & HE).
  pose proof (Vrel_prim_empty _ _ _ _ _ HT HV) as H0. rewrite H0 in HV.
  split; [by apply tenv_of_empty_inv|]. by exists v, E.
Qed.

Lemma Prel_S_ready n W Σ T p : Prel (S n) W Σ T p → prim T → ready_p W Σ p.
Proof.
  intros HP HT. destruct (proc_progress p) as [Hirr|(π & p' & Hst)].
  - destruct (Prel_S_stop_prim _ _ _ _ _ HP HT Hirr) as (-> & v & E & -> & Hv & _ & HE).
    intros _. split.
    + intros _. exists v, E. done.
    + intros k e He. exfalso. unfold tenv_entry, tenv_of in He.
      rewrite lookup_fmap, lookup_empty in He. by destruct k.2.
  - apply Prel_S_iff in HP as (_ & Hr & _). apply Hr. intros Hirr. by apply (Hirr π p').
Qed.

Section stop_ready.
  Context (n' : nat) (T : ty) (HT : prim T).
  Context (W : world) (Σ1 Σ2 ΣC ΣC' : senv) (C0 C1 C2 : gset chan) (E1 E2 : gmultiset expr).
  Context (Hok : cut_ok W Σ1 Σ2 ΣC ΣC' C0 C1 C2).
  Context (HP1 : Prel (S n') W (Σ1 ∪ ΣC) T (C1, E1)).
  Context (HP2 : Prel (S n') W (Σ2 ∪ ΣC') TUnit (C2, E2)).

  Lemma conn_ready : ready_p W (Σ1 ∪ Σ2) (C1 ∪ C2 ∪ C0, E1 ⊎ E2).
  Proof.
    destruct Hok as [HW Hd1 Hd2 Hd12 HC0 HC0' Hcut H1 H2 _ _ _ _ _].
    apply (ready_connect W W W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 HW Hd1 Hd2 Hd12 HC0 HC0'
             Hcut H2 H1 (λ _ _ _ _ _ _ H, H) (λ _ _ _ _ _ _ H, H)
             (Prel_S_ready _ _ _ _ _ HP1 HT) (Prel_S_ready _ _ _ _ _ HP2 prim_unit)).
    intros Ht e He. destruct (Prel_S_stop_prim _ _ _ _ _ HP2 prim_unit (terminated_pirred _ Ht))
        as (_ & v & U & [= _ ->] & _ & HV & HU).
      apply Vrel_unit_iff in HV as [_ ->].
      apply gmultiset_elem_of_disj_union in He as [He|He]; [|by apply HU].
      by apply gmultiset_elem_of_singleton in He.
  Qed.

  Lemma conn_stop : pirred (C1 ∪ C2 ∪ C0, E1 ⊎ E2) →
    ∃ v E, (C1 ∪ C2 ∪ C0, E1 ⊎ E2) = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧
           Vrel (S n') W (tenv_of (Σ1 ∪ Σ2)) T v ∧ (∀ e, e ∈ E → e = EUnit).
  Proof.
    intros Hirr.
    destruct (conn_ready (λ p' Hp', Hirr _ _ Hp')) as [Ht _].
    assert (∀ k, ¬ offered_p (Σ1 ∪ Σ2) (C1 ∪ C2 ∪ C0, E1 ⊎ E2) k) as Hno.
    { intros k (σ & q & Hq & _). exact (Hirr _ _ Hq). }
    destruct (Ht Hno) as (v & U & Heq & Hv & HU).
    injection Heq as HC HE.
    assert (C1 = ∅ ∧ C2 = ∅ ∧ C0 = ∅) as (-> & -> & ->) by (clear -HC; set_solver).
    assert (∀ e, e ∈ E1 ⊎ E2 → is_val e) as Hvals.
    { intros e. rewrite HE. intros [He|He]%gmultiset_elem_of_disj_union.
      - apply gmultiset_elem_of_singleton in He. by subst.
      - rewrite (HU e He). constructor. }
    destruct (Prel_S_stop_prim _ _ _ _ _ HP1 HT) as (H1 & v1 & U1 & [= HE1] & Hv1 & HV1 & HU1).
    { apply vals_pirred. intros e He. apply Hvals. multiset_solver. }
    destruct (Prel_S_stop_prim _ _ _ _ _ HP2 prim_unit) as (H2 & v2 & U2 & [= HE2] & _ & HV2 & HU2).
    { apply vals_pirred. intros e He. apply Hvals. multiset_solver. }
    apply Vrel_unit_iff in HV2 as [_ ->].
    assert (Σ1 = ∅ ∧ Σ2 = ∅) as [-> ->].
    { split; [exact (map_positive_l _ _ H1)|exact (map_positive_l _ _ H2)]. }
    exists v1, (U1 ⊎ ({[+ EUnit +]} ⊎ U2)). split_and!.
    - rewrite HE1, HE2. apply pair_equal_spec. split; [set_solver|multiset_solver].
    - done.
    - rewrite (left_id_L ∅ (∪)). unfold tenv_of. rewrite fmap_empty. done.
    - intros e [He|[He|He]%gmultiset_elem_of_disj_union]%gmultiset_elem_of_disj_union;
        [by apply HU1|by apply gmultiset_elem_of_singleton in He|by apply HU2].
  Qed.
End stop_ready.

(** ** Pointwise reasoning about environments *)

Ltac mdisj_close :=
  match goal with
  | H : ?A ##ₘ ?B, E1 : ?A !! ?r = Some _, E2 : ?B !! ?r = Some _ |- _ =>
      exfalso; exact (proj1 (map_disjoint_spec A B) H r _ _ E1 E2)
  | H : dom ?A ## dom ?B, E1 : ?A !! ?r = Some _, E2 : ?B !! ?r = Some _ |- _ =>
      exfalso; apply (H r); eapply elem_of_dom_2; eassumption
  | H : ?r ∈ dom ?M, E : ?M !! ?r = None |- _ =>
      exfalso; apply elem_of_dom in H as [? H]; congruence
  | H : ?r ∉ dom ?M, E : ?M !! ?r = Some _ |- _ =>
      exfalso; apply H; eapply elem_of_dom_2; eassumption
  end.

Ltac mlk := repeat (rewrite ?lookup_union, ?lookup_difference, ?lookup_intersection,
                      ?lookup_fmap in * ).

Ltac mdestr :=
  repeat match goal with
  | |- context [?M !! ?r] =>
      let E := fresh "L" in destruct (M !! r) eqn:E; rewrite ?E in *
  | H : context [?M !! ?r] |- _ =>
      lazymatch type of H with
      | ?M !! ?r = _ => fail
      | _ => let E := fresh "L" in destruct (M !! r) eqn:E; rewrite ?E in *
      end
  end.

Ltac mpoint := mlk; mdestr; simpl in *; simplify_eq; try done; try mdisj_close.

(** ** The step cases, for steps of component 1 *)

Section steps.
  Context (n' : nat) (T : ty) (HT : prim T).
  Context (IHo : ∀ j, j ≤ n' → conn_at j T).
  Context (m : nat) (IHi : conn_lt (S n') T m).
  Context (W : world) (Σ1 Σ2 ΣC ΣC' : senv) (C0 C1 C2 : gset chan)
    (E1 E2 : gmultiset expr) (TA TB : ty).
  Context (Hm : msize (E1 ⊎ E2) = m) (Hty : ctys TA TB T)
    (Hok : cut_ok W Σ1 Σ2 ΣC ΣC' C0 C1 C2).
  Context (HP1 : Prel (S n') W (Σ1 ∪ ΣC) TA (C1, E1))
    (HP2 : Prel (S n') W (Σ2 ∪ ΣC') TB (C2, E2)).

  Local Notation C := (C1 ∪ C2 ∪ C0).
  Local Notation Σ := (Σ1 ∪ Σ2).

  Lemma HW : strict W.
  Proof. apply Hok. Qed.
  Lemma HWf : world_wf W.
  Proof. apply HW. Qed.

  Lemma Σ2C : Σ2 ##ₘ ΣC.
  Proof.
    apply map_disjoint_dom. rewrite (co_dom _ _ _ _ _ _ _ _ Hok).
    apply (co_Σ2C0 _ _ _ _ _ _ _ _ Hok).
  Qed.
  Lemma Σ1C' : Σ1 ##ₘ ΣC'.
  Proof.
    apply map_disjoint_dom. rewrite (co_dom' _ _ _ _ _ _ _ _ Hok).
    apply (co_Σ1C0 _ _ _ _ _ _ _ _ Hok).
  Qed.

  (** Q-Send for a send of component 1 on an interface channel. *)
  Lemma ext_send F1 e c w e' :
    E1 = F1 ⊎ {[+ e +]} → tstep e (LSess (SSend c w)) e' → c ∉ C →
    Psend_case (Vrel (S n')) (Prel (S n')) W Σ T (C, E1 ⊎ E2) c w
      (C ∖ fchans w, F1 ⊎ E2 ⊎ {[+ e' +]}).
  Proof.
    intros HE Hst Hc. pose proof Σ2C as H2C. pose proof Σ1C' as H1C'.
    pose proof (co_Σ1C0 _ _ _ _ _ _ _ _ Hok) as HΣ1C0.
    pose proof (co_Σ2C0 _ _ _ _ _ _ _ _ Hok) as HΣ2C0.
    destruct Hok as [HW' Hd1 Hd2 Hd12 HC0 HC0' Hcut HC1Σ2 HC2Σ1 HC1Σ1 HC2Σ2 HC10 HC20 HC12].
    assert (proc_step (C1, E1) (PSess (SSend c w)) (C1 ∖ fchans w, F1 ⊎ {[+ e' +]})) as Hst1.
    { rewrite HE. apply (PStepSession C1 F1 e (SSend c w) e' Hst). simpl. clear -Hc. set_solver. }
    pose proof (Prel_S_step _ _ _ _ _ _ _ HP1 Hst1) as Hc1. simpl in Hc1.
    destruct Hc1 as (Σ0 & Σv & mm & U & s & k & Σe & Θe & (s0 & HΣa & Hu) & Hd0v & Hc0 & Hcv
                     & HdΘ & Hsplit & HΘΣ & HV & HP1').
    pose proof (Vrel_fchans _ _ _ _ _ HV) as Hfw.
    unfold tenv_of in Hfw. rewrite dom_union_L, dom_fmap_L in Hfw.
    assert (dom Σe ⊆ dom Θe) as HΣeΘ by apply Hsplit.
    assert (c ∈ dom Σ1) as HcΣ1.
    { assert (c ∈ dom (Σ1 ∪ ΣC)) as H by (rewrite HΣa, dom_insert_L; clear; set_solver).
      rewrite dom_union_L, HC0 in H. clear -H Hc. set_solver. }
    assert (dom (Σ1 ∪ ΣC) = {[c]} ∪ dom Σ0 ∪ dom Σv) as HdΣa
      by (rewrite HΣa, dom_insert_L, dom_union_L; clear; set_solver).
    rewrite dom_union_L, HC0 in HdΣa, HΘΣ.
    assert (dom Θe ⊆ C1) as HΘC1 by (rewrite HdΘ; clear; set_solver).
    set (Σv' := Σv ∖ ΣC). set (Σvc := Σv ∩ ΣC).
    exists ((Σ0 ∖ ΣC) ∪ Σ2), Σv', mm, U, s, k, (Σe ∪ (ΣC' ∩ Σv)), (Θe ∪ tenv_of Σvc).
    split_and!.
    - exists s0. split; [|done]. apply map_eq. intros r.
      pose proof (f_equal (lookup r) HΣa) as Hr.
      destruct (decide (r = c)) as [->|Hrc].
      + rewrite lookup_insert_eq in Hr |- *. mpoint.
      + rewrite lookup_insert_ne in Hr |- * by done. subst Σv'. mpoint.
    - apply map_disjoint_spec. intros r x y Hx Hy. subst Σv'.
      pose proof (f_equal (lookup r) HΣa) as Hr.
      destruct (decide (r = c)) as [->|Hrc];
        [rewrite lookup_insert_eq in Hr|rewrite lookup_insert_ne in Hr by done]; mpoint.
    - rewrite dom_union_L, dom_difference_L. apply map_disjoint_dom in Hd12.
      clear -Hc0 HcΣ1 Hd12. set_solver.
    - subst Σv'. rewrite dom_difference_L. clear -Hcv. set_solver.
    - simpl. subst Σvc. unfold tenv_of. rewrite dom_union_L, dom_fmap_L, dom_intersection_L, HC0, Hfw.
      clear -HdΣa HΘC1 HC1Σ1 HC10 HC12 HC2Σ1 HC20 HdΘ. set_solver.
    - split.
      + subst Σvc. unfold tenv_of. rewrite !dom_union_L, dom_fmap_L, !dom_intersection_L, HC0, HC0'.
        clear -HΣeΘ. set_solver.
      + intros r o Hro. subst Σvc. unfold tenv_of in Hro. rewrite lookup_union, lookup_fmap in Hro.
        destruct (Θe !! r) as [o'|] eqn:HΘr.
        * rewrite union_Some_l in Hro. injection Hro as <-. destruct Hsplit as [_ Hsp].
          pose proof (Hsp r o' HΘr) as H. assert (r ∈ C1) as HrC1 by (apply HΘC1; by eapply elem_of_dom_2).
          assert (ΣC' !! r = None) as HrC'.
          { apply not_elem_of_dom. rewrite HC0'. clear -HrC1 HC10. set_solver. }
          rewrite lookup_union, lookup_intersection, HrC'. simpl.
          destruct o' as [e1|e1 e2]; [destruct H as (e0 & -> & ?); by exists e0|].
          destruct H as (-> & ?). done.
        * pose proof (f_equal (lookup r) HΣa) as Hr.
          destruct (decide (r = c)) as [->|Hrc].
          { assert (ΣC !! c = None) as HCc.
            { apply not_elem_of_dom. rewrite HC0. clear -Hc. set_solver. }
            exfalso. rewrite lookup_intersection, HCc in Hro. mpoint. }
          rewrite lookup_insert_ne in Hr by done. rewrite lookup_intersection in Hro.
          destruct (Σv !! r) as [x|] eqn:Hvr; [|done]. destruct (ΣC !! r) as [x'|] eqn:HCr; [|done].
          simpl in Hro. injection Hro as <-.
          assert (r ∈ C0) as HrC0 by (rewrite <-HC0; by eapply elem_of_dom_2).
          assert (Σ1 !! r = None) as HΣ1r.
          { apply not_elem_of_dom. clear -HΣ1C0 HrC0. set_solver. }
          assert (x' = x) as ->.
          { rewrite lookup_union, HΣ1r, HCr, lookup_union, Hvr in Hr. simpl in Hr.
            destruct (Σ0 !! r) eqn:H0r; simpl in Hr; [|by injection Hr].
            exfalso. by apply (proj1 (map_disjoint_spec _ _) Hd0v r _ _ H0r Hvr). }
          assert (is_Some (ΣC' !! r)) as [y Hy] by (apply elem_of_dom; by rewrite HC0').
          assert (Σe !! r = None) as HΣer.
          { apply not_elem_of_dom. intros Hin. apply HΣeΘ, HΘC1 in Hin.
            clear -Hin HrC0 HC10. set_solver. }
          exists y. rewrite lookup_union, HΣer, lookup_intersection, Hy, Hvr. simpl.
          destruct (Hcut r x y HCr Hy) as [Hq Hd]. split_and!; [done| |by apply sdual_sym].
          by apply (wf_eq_sym _ (proj1 HW')).
    - subst Σvc. unfold tenv_of. rewrite dom_union_L, dom_fmap_L, dom_intersection_L, dom_union_L, HC0.
      apply map_disjoint_dom in Hd12. clear -HΘC1 HC1Σ1 HC1Σ2 Hd12 HC10 HdΣa HΣ1C0 HΣ2C0. set_solver.
    - assert (tenv_of Σv' ∪ (Θe ∪ tenv_of Σvc) = tenv_of Σv ∪ Θe) as ->; [|done].
      assert (dom Θe ## dom Σv) as HΘv by (clear -HΘΣ HdΣa; set_solver).
      apply map_eq. intros r. subst Σv' Σvc. unfold tenv_of. mpoint.
    - set (Σ1' := <[c := (s, pt_shift 1 k)]> ((Σ0 ∖ ΣC) ∪ Σe)).
      set (Σ2' := Σ2 ∪ (ΣC' ∩ Σv)).
      assert (<[c:=(s, pt_shift 1 k)]> (Σ0 ∖ ΣC ∪ Σ2 ∪ (Σe ∪ ΣC' ∩ Σv)) = Σ1' ∪ Σ2') as ->.
      { apply map_eq. intros r. subst Σ1' Σ2'.
        destruct (decide (r = c)) as [->|Hrc]; [by rewrite lookup_union, !lookup_insert_eq, union_Some_l|].
        rewrite lookup_union, !lookup_insert_ne by done.
        assert (dom Σe ## dom Σ2) as HeΣ2 by (clear -HΣeΘ HΘC1 HC1Σ2; set_solver).
        assert (dom Σe ## dom ΣC') as HeC' by (rewrite HC0'; clear -HΣeΘ HΘC1 HC10; set_solver).
        mpoint. }
      assert (C ∖ fchans w = (C1 ∖ fchans w) ∪ C2 ∪ (C0 ∖ dom Σv)) as ->.
      { rewrite Hfw. clear -HdΣa HΘC1 HC12 HC20 HC2Σ1 HC10. set_solver. }
      assert (F1 ⊎ E2 ⊎ {[+ e' +]} = (F1 ⊎ {[+ e' +]}) ⊎ E2) as -> by multiset_solver.
      apply (IHi W Σ1' Σ2' (Σ0 ∩ ΣC) (ΣC' ∖ Σv) _ _ _ _ _ TA TB); [|done| | |].
      + rewrite <-Hm, HE, !msize_disj_union, !msize_singleton.
        pose proof (tstep_giving_size _ _ _ Hst I). lia.
      + assert (c ∉ C0) as HcC0 by (clear -Hc; set_solver).
        apply map_disjoint_dom in Hd12, Hd0v.
        assert (dom Σ1' = {[c]} ∪ ((dom Σ0 ∖ C0) ∪ dom Σe)) as HD1.
        { subst Σ1'. by rewrite dom_insert_L, dom_union_L, dom_difference_L, HC0. }
        assert (dom Σ2' = dom Σ2 ∪ (C0 ∩ dom Σv)) as HD2.
        { subst Σ2'. by rewrite dom_union_L, dom_intersection_L, HC0'. }
        assert (dom (Σ0 ∩ ΣC) = C0 ∖ dom Σv) as HD3.
        { rewrite dom_intersection_L, HC0. clear -HdΣa Hd0v HcC0. set_solver. }
        assert (dom (ΣC' ∖ Σv) = C0 ∖ dom Σv) as HD4.
        { by rewrite dom_difference_L, HC0'. }
        assert (dom Σ0 ⊆ dom Σ1 ∪ C0) as H0a by (clear -HdΣa; set_solver).
        assert (dom Σe ⊆ C1) as He1 by (clear -HΣeΘ HΘC1; set_solver).
        assert (dom Σe ⊆ fchans w) as Hew by (clear -HΣeΘ HdΘ; set_solver).
        split; [done| | | | | | | | | | | | |];
          try (apply map_disjoint_dom); rewrite ?HD1, ?HD2, ?HD3, ?HD4.
        * clear -HcC0 He1 HC10. set_solver.
        * clear -HΣ2C0. set_solver.
        * clear -HcΣ1 Hd12 HcC0 H0a He1 HC1Σ2 HC10 HΣ2C0. set_solver.
        * done.
        * done.
        * intros r x y Hx Hy. apply lookup_intersection_Some in Hx as [Hx _].
          apply lookup_difference_Some in Hy as [Hy Hvr].
          assert (r ∈ C0) as HrC0 by (rewrite <-HC0'; by eapply elem_of_dom_2).
          assert (r ≠ c) as Hrc by (intros ->; done).
          pose proof (f_equal (lookup r) HΣa) as Hr. rewrite lookup_insert_ne in Hr by done.
          assert (Σ1 !! r = None) as HΣ1r.
          { apply not_elem_of_dom. clear -HΣ1C0 HrC0. set_solver. }
          rewrite !lookup_union, HΣ1r, Hx, Hvr in Hr. simpl in Hr.
          destruct (ΣC !! r) eqn:HCr; [|by rewrite union_Some_l in Hr]. simpl in Hr.
          injection Hr as ->. by apply (Hcut r).
        * clear -HC1Σ2 HC10. set_solver.
        * clear -HcΣ1 HC2Σ1 H0a He1 HC12 HC20. set_solver.
        * clear -HcΣ1 HC1Σ1 H0a Hew HC10. set_solver.
        * clear -HC2Σ2 HC20. set_solver.
        * clear -HC10. set_solver.
        * clear -HC20. set_solver.
        * clear -HC12. set_solver.
      + assert (dom Σ0 ## dom Σe) as H0e by (clear -HdΣa HΣeΘ HΘC1 HC1Σ1 HC10; set_solver).
        assert (Σ1' ∪ Σ0 ∩ ΣC = <[c:=(s, pt_shift 1 k)]> (Σ0 ∪ Σe)) as -> ; [|done].
        apply map_eq. intros r. subst Σ1'.
        destruct (decide (r = c)) as [->|Hrc]; [by rewrite lookup_union, !lookup_insert_eq, union_Some_l|].
        rewrite lookup_union, !lookup_insert_ne by done. mpoint.
      + assert (Σ2' ∪ ΣC' ∖ Σv = Σ2 ∪ ΣC') as -> ; [|done].
        apply map_eq. intros r. subst Σ2'. mpoint.
  Qed.
End steps.
