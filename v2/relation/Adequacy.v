(** * Semantic process typing and adequacy (stage S3, Appendix A.3)

      Σ ⊨_W p : T    [sem_ptyped κ_DF W Σ p T]    deadlock freedom
      Σ ⊫_W p : T    [sem_ptyped κ_L W Σ p T]     liveness

    A closed process in P at every level is deadlock free, for every
    cost table ([adequacy_gen]). A τ step lowers the level by at most
    [cmax κ], so the level reaches every state of a run, and an
    irreducible state is terminated, because P-Stop asks a value of the
    main thread and no session step is open to an empty interface. In
    κ_L the administrative steps cost nothing, so they are read inside
    the least fixpoint of one level, and no state reached admits an
    infinite sequence of them ([live_adequacy]). *)

From GV Require Export relation.Closure lockfree.TauThread.

Definition sem_ptyped (κ : ctable) (W : world) (Σ : senv) (p : proc) (T : ty) : Prop :=
  ∀ n, Prel κ n W Σ T p.

Notation "Σ ⊨_ W p : T" := (sem_ptyped κ_DF W Σ p T)
  (at level 74, W at level 0, p at level 60, T at level 60,
   format "Σ  ⊨_ W  p  :  T").
Notation "Σ ⊫_ W p : T" := (sem_ptyped κ_L W Σ p T)
  (at level 74, W at level 0, p at level 60, T at level 60,
   format "Σ  ⊫_ W  p  :  T").

Lemma chans_of_empty : chans_of ∅ = ∅.
Proof. unfold chans_of. by rewrite dom_empty_L, set_map_empty. Qed.

Section adequacy.
  Context (κ : ctable).

  (** A τ step lowers the level by at most [cmax κ]. *)
  Lemma Prel_tau n W T p p' :
    Prel κ (n + S (cmax κ)) W ∅ T p → preduction p p' → Prel κ n W ∅ T p'.
  Proof.
    intros HP (q & ev & q' & <- & Hst & <- & Hτ).
    replace (n + S (cmax κ)) with (S (n + cmax κ)) in HP by lia.
    apply Prel_S_iff in HP. destruct (HP W (wext_refl W)) as (_ & _ & H1 & _).
    destruct (H1 q ev q' eq_refl Hst Hτ) as [A1 A2].
    { rewrite chans_of_empty. apply disjoint_empty_r. }
    pose proof (ev_cost_le κ ev Hτ).
    destruct (decide (ev_cost κ ev = 0)) as [Hc|Hc].
    - eapply Prel_down; [|exact (A1 Hc)]. lia.
    - eapply Prel_down; [|exact (A2 Hc)]. lia.
  Qed.

  Lemma Prel_steps m : ∀ W n T p p',
    nsteps preduction m p p' → Prel κ (m * S (cmax κ) + n) W ∅ T p → Prel κ n W ∅ T p'.
  Proof.
    induction m as [|m IH]; intros W n T p p' Hrun HP.
    { by inversion Hrun; subst. }
    inversion Hrun as [|? ? p1 ? Hp1 Hrest]; subst.
    apply (IH W n T p1 p' Hrest). apply (Prel_tau _ W T p p1); [|done].
    by replace (m * S (cmax κ) + n + S (cmax κ)) with (S m * S (cmax κ) + n) by lia.
  Qed.

  (** An irreducible closed process in P is terminated. *)
  Lemma Prel_safe n W T p : Prel κ (S n) W ∅ T p → safe p.
  Proof.
    intros HP. apply Prel_S_iff in HP. destruct (HP W (wext_refl W)) as (Hs & _ & Hst).
    destruct (proc_progress p) as [Hirr|(π & p' & Hπ)].
    - left. destruct (Hs Hirr) as (v & E & -> & Hv & HE). exists v, E.
      split_and!; [done|by eapply Vrel_val|done].
    - right. destruct π as [|σ]; [by exists p'|exfalso].
      destruct Hπ as (q & ev & q' & Hq & Hi & Hq' & Hl).
      destruct ev as [| | | | | | | |i σ']; simpl in Hl; try discriminate. injection Hl as ->.
      destruct Hst as (_ & H2 & H3 & H4 & H5 & H6 & H7).
      destruct σ as [o M w|o w|o|o b|o b|os].
      + destruct (H2 q i o M w q' Hq Hi) as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & A & _).
        by rewrite lookup_empty in A.
      + destruct (H3 q i o w q' Hq Hi) as (? & ? & ? & ? & ? & ? & A & _).
        by rewrite lookup_empty in A.
      + destruct (H4 q i o q' Hq Hi) as (? & ? & A & _). by rewrite lookup_empty in A.
      + destruct (H5 q i o b q' Hq Hi) as (? & ? & ? & ? & A & _). by rewrite lookup_empty in A.
      + destruct (H6 q i o b q' Hq Hi) as (? & ? & ? & ? & A & _). by rewrite lookup_empty in A.
      + destruct (H7 q i os q' Hq Hi) as (? & ? & ? & ? & ? & _ & _ & A & _).
        by rewrite lookup_empty in A.
  Qed.

  Theorem adequacy_gen W T p : sem_ptyped κ W ∅ p T → deadlock_free p.
  Proof.
    intros HP p' Hsteps. apply rtc_nsteps_1 in Hsteps as [m Hm].
    apply (Prel_safe 0 W T), (Prel_steps m W 1 T p p' Hm), HP.
  Qed.
End adequacy.

(** ∅ ⊨_W p : T ⟹ deadlock_free p. *)
Theorem adequacy W T p : ∅ ⊨_W p : T → deadlock_free p.
Proof. apply adequacy_gen. Qed.

(** In κ_L an administrative step costs nothing, so a closed process in
    P at a positive level admits no infinite sequence of them. *)
Lemma Prel_acc_live n W T p : Prel κ_L (S n) W ∅ T p → Acc (λ y x, padmin x y) p.
Proof.
  intros HP.
  cut (∀ W Σ T p, Prel κ_L (S n) W Σ T p → Σ = ∅ → Acc (λ y x, padmin x y) p); [eauto|].
  clear. refine (Prel_S_ind κ_L n (λ W Σ T p, Σ = ∅ → Acc (λ y x, padmin x y) p) _).
  intros W Σ T p H ->. constructor. intros p' (q & ev & q' & Hq & Hst & <- & Had).
  destruct (H W (wext_refl W)) as (_ & _ & H1 & _).
  assert (ev_tau ev ∧ ev_cost κ_L ev = 0) as [Hτ Hc].
  { destruct ev; simpl in Had; try contradiction; done. }
  destruct (H1 q ev q' Hq Hst Hτ) as [A1 _].
  { rewrite chans_of_empty. apply disjoint_empty_r. }
  by apply (A1 Hc).
Qed.

(** ∅ ⊫_W p : T ⟹ deadlock_free p ∧ no_tau_divergence p. *)
Theorem live_adequacy W T p : ∅ ⊫_W p : T → deadlock_free p ∧ no_tau_divergence p.
Proof.
  intros HP. split; [by eapply adequacy_gen|].
  intros q Hq. apply rtc_nsteps_1 in Hq as [m Hm].
  apply (Prel_acc_live 0 W T), (Prel_steps κ_L m W 1 T p q Hm), HP.
Qed.

(** ** Sanity checks

    The terminated process is in P at every level. *)

Lemma no_istep_done q ev q' : erase q = (∅, {[+ EUnit +]}) → ¬ istep q ev q'.
Proof.
  intros Hq Hst. destruct (istep_parts_nonempty _ _ _ Hst) as [t Ht].
  destruct (istep_parts_some _ _ _ t Hst Ht) as [e He].
  destruct (istep_actor _ _ _ t e Hst Ht He) as (α & e' & Hs & _).
  assert (e ∈ soup q.2) as Hin by (apply elem_of_soup; eauto).
  destruct q as [C M]. injection Hq as _ HM. simpl in Hin. rewrite HM in Hin.
  apply gmultiset_elem_of_singleton in Hin as ->. by apply (val_no_tstep _ _ _ Hs).
Qed.

Lemma Prel_done κ n W : Prel κ n W ∅ TUnit (∅, {[+ EUnit +]}).
Proof.
  destruct n as [|n]; [apply Prel_0|]. apply Prel_S_iff. intros W1 HW1.
  split; [|split; [|unfold Psteps; split_and!]].
  - intros _. exists EUnit, ∅. split_and!.
    + f_equal. multiset_solver.
    + by apply Vrel_unit_iff.
    + intros e He. multiset_solver.
  - intros Hirr. exfalso. apply Hirr. intros π p' (q & ev & q' & Hq & Hst & _).
    by eapply no_istep_done.
  - intros q ev q' Hq Hst. exfalso. by eapply no_istep_done.
  - intros q i o M w q' Hq Hst. exfalso. by eapply no_istep_done.
  - intros q i o w q' Hq Hst. exfalso. by eapply no_istep_done.
  - intros q i o q' Hq Hst. exfalso. by eapply no_istep_done.
  - intros q i o b q' Hq Hst. exfalso. by eapply no_istep_done.
  - intros q i o b q' Hq Hst. exfalso. by eapply no_istep_done.
  - intros q i os q' Hq Hst. exfalso. by eapply no_istep_done.
Qed.

(** A β-redex takes one step of cost κ(β), read inside the level in κ_L
    and one level down in κ_DF. *)
Lemma tstep_beta_unit α e' : tstep (App (Lam EUnit) EUnit) α e' → α = LBeta ∧ e' = EUnit.
Proof.
  intros Hst. apply tstep_inv in Hst as [Hh|(f & e0 & e0' & Hf & Heq & -> & Hs)].
  - inversion Hh; subst. done.
  - destruct f; simpl in Heq; try discriminate; injection Heq as <- <-;
      exfalso; apply (val_no_tstep _ _ _ Hs); done.
Qed.

Lemma Erel_beta_unit κ n W F : Erel κ n W ∅ TUnit F (App (Lam EUnit) EUnit).
Proof.
  destruct n as [|n]; [apply Erel_0|]. apply Erel_S_iff. intros W1 HW1.
  split; [|split; [|unfold Esteps; split_and!]].
  1: { intros Hirr. exfalso. apply (Hirr LBeta EUnit). apply tstep_head. by apply (t_act_app EUnit). }
  1: { intros _ Hs. exfalso. destruct (Hs LBeta EUnit) as [σ Hσ]; [|done].
       apply tstep_head. by apply (t_act_app EUnit). }
  1: { intros e' Hst. apply tstep_beta_unit in Hst as [_ ->].
       split; intros; apply Vrel_Erel, Vrel_unit_iff; done. }
  all: intros; match goal with H : tstep _ _ _ |- _ => apply tstep_beta_unit in H as [? _] end;
    discriminate.
Qed.
