(** * Existential points, semantically (sharp edges 97)

    E-Pack puts a term of type T[xs/ιs] at known points xs that meet C
    into ∃ιs. C. T. E-Open uses a hypothesis of type ∃ιs. C. T at a
    fresh instance that meets C. E-OpenPair opens the existential
    scrutinee of a let pair. Each continuation is good at every
    instance that meets C in every later world, which is what V-Ex
    hands out. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export rules.FreshRules.

Set Default Proof Using "All".

(** E at T gives E at T′ when every later value at T is a value at T′. *)
Lemma Erel_Vsub n : ∀ W Θ T T' F e, strict W →
  (∀ j W' Θ' v, j ≤ n → wext W W' → Vrel j W' Θ' T v → Vrel j W' Θ' T' v) →
  Erel n W Θ T F e → Erel n W Θ T' F e.
Proof.
  induction n as [n IHn] using lt_wf_ind.
  destruct n as [|n']; [intros; apply Erel_0|].
  intros W Θ T T' F e HW HV HE. revert T' HW HV.
  induction HE as [W Θ T F e Hval Hrdy Hstep] using Erel_S_ind.
  intros T' HW HV.
  assert (∀ j W0 Θ0 F0 e0, j ≤ n' → wext W W0 →
            Erel j W0 Θ0 T F0 e0 → Erel j W0 Θ0 T' F0 e0) as HEj.
  { intros j W0 Θ0 F0 e0 Hj HW0. apply (IHn j ltac:(lia)); [by destruct HW0 as (_&_&_&?)|].
    intros i W' Θ' v Hi HW'. apply HV; [lia|by eapply wext_trans]. }
  apply Erel_S_iff. split_and!; [|done|].
  { intros Hirr. apply HV; [lia|by apply wext_refl|]. by apply Hval. }
  intros α e' Hst. specialize (Hstep α e' Hst).
  destruct α as [|[c w|c w|c|cd]|c|w]; simpl in Hstep |- *.
  - eapply HEj; [lia|by apply wext_refl|exact Hstep].
  - destruct Hstep as (Θ1 & m & U & s & k & Hhd & H).
    exists Θ1, m, U, s, k. split; [done|].
    intros W' j Θ2 Θ1c Θ' HW' Hj Hext Hc HVw.
    eapply HEj; [lia|exact HW'|by apply (H W' j Θ2 Θ1c Θ')].
  - destruct Hstep as (Θr & Θ1 & Θ2 & m & U & s & k & Θ' &
                       Hhd & Hc & HVw & Hext & HE').
    exists Θr, Θ1, Θ2, m, U, s, k, Θ'. split_and!; try done. exact (proj2 HE' T' HW HV).
  - destruct Hstep as (Θ1 & k & Hhd & HE').
    exists Θ1, k. split; [done|]. exact (proj2 HE' T' HW HV).
  - destruct Hstep as (c & d & Θ1 & Θm & sc & sd & kc & kd &
                       -> & ? & ? & ? & ? & HE').
    exists c, d, Θ1, Θm, sc, sd, kc, kd. split_and!; [done..|]. exact (proj2 HE' T' HW HV).
  - (* O-New: rename the new point away from the points of T' *)
    intros Hc. destruct (Hstep Hc) as (a & s & s' & W1 & Ha & Hdu & Hfr & HE').
    destruct (fresh_const (w_names W ∪ tenv_roots Θ ∪ ty_roots T ∪ ty_roots T'
                           ∪ frame_roots F)) as [a1 Ha1].
    destruct (Erel_new_rename _ _ _ _ _ _ _ c s s' a a1 (proj1 HW) Hfr Ha
                ltac:(set_solver) HE') as (W1' & Hfr' & HE1).
    exists a1, (stysw a a1 s), (stysw a a1 s'), W1'. split_and!.
    + set_solver.
    + by apply sdual_sw.
    + done.
    + eapply HEj; [lia|by destruct Hfr' as (? & _)|exact HE1].
  - destruct Hstep as (Θ1 & Θ2 & ub & lb & ? & HVw & HE').
    exists Θ1, Θ2, ub, lb. split_and!; [done|done|].
    eapply HEj; [lia|by apply wext_refl|exact HE'].
Qed.

(** E-Pack: a term of type T[xs/ιs], at known points xs that meet C
    and lie at or above the lower point, has type ∃ιs. C. T. *)
Lemma sem_typed_pack W Θ Δ F e lb m C T xs :
  length xs = m → Forall (pt_known W) xs → bcs_hold (w_eq W) (w_lt W) C xs →
  lb_below W lb (heads (ty_inst xs T)) →
  sem_typed W Θ Δ F e (ty_inst xs T) → sem_typed W Θ Δ F e (TEx lb m C T).
Proof.
  intros Hxs HK HC Hlb He n W' Θ' Θ'' γ HW Hc Hg.
  eapply Erel_Vsub; [by destruct HW as (_&_&_&?)| |by apply (He n W' Θ' Θ'' γ)].
  intros j W2 Θ2 v Hj HW2 HV. pose proof (wext_trans _ _ _ HW HW2) as HWW2.
  pose proof (wext_wf _ _ HWW2) as HW2f.
  apply Vrel_ex_iff. split; [|exists xs; split_and!; [done| | |done]].
  - pose proof (Vrel_heads_above _ _ _ _ _ HW2f HV) as Hab.
    pose proof (lb_below_mono _ _ _ _ HWW2 Hlb) as Hlb2.
    destruct lb as [x|]; simpl in *.
    + intros y (k & e0 & Hk & ->)%elem_of_tenv_heads_entry.
      destruct (Hab k e0 Hk) as (h & Hh & Hle). eapply le_le_W; [done| |exact Hle]. by apply Hlb2.
    + apply set_eq. intros y. split; [|set_solver].
      intros (k & e0 & Hk & ->)%elem_of_tenv_heads_entry.
      destruct (Hab k e0 Hk) as (h & Hh & _). set_solver.
  - eapply Forall_impl; [exact HK|]. intros x. unfold pt_known. destruct HWW2 as (? & _). set_solver.
  - destruct HWW2 as (_ & He2 & Hl2 & _). eapply bcs_hold_mono; [exact He2|exact Hl2|exact HC].
Qed.

(** Opening an existential hypothesis: its value is related at some
    known instance that meets C. *)
Lemma grounding_open n W Θ Δ γ i lb m C T :
  Δ !! i = Some (Some (TEx lb m C T)) → grounding n W Θ Δ γ →
  ∃ xs, length xs = m ∧ Forall (pt_known W) xs ∧ bcs_hold (w_eq W) (w_lt W) C xs ∧
    grounding n W Θ (<[i := Some (ty_inst xs T)]> Δ) γ.
Proof.
  revert i Θ γ. induction Δ as [|o Δ IH]; intros i Θ γ Hi Hg; [done|].
  destruct i as [|i]; simpl in Hi.
  - injection Hi as ->. simpl in Hg. destruct Hg as (Θ1 & Θ2 & Hc & HV & Hg).
    apply Vrel_ex_iff in HV as [_ (xs & Hxs & HK & HC & HV)].
    exists xs. split_and!; [done..|]. simpl. by exists Θ1, Θ2.
  - destruct o as [U|]; simpl in Hg.
    + destruct Hg as (Θ1 & Θ2 & Hc & HV & Hg).
      destruct (IH i Θ2 (γ ∘ S) Hi Hg) as (xs & Hxs & HK & HC & Hg').
      exists xs. split_and!; [done..|]. simpl. by exists Θ1, Θ2.
    + destruct (IH i Θ (γ ∘ S) Hi Hg) as (xs & Hxs & HK & HC & Hg').
      exists xs. by split_and!.
Qed.

(** E-Open: a hypothesis of type ∃ιs. C. T may be used at a fresh
    instance that meets C, in every later world. *)
Lemma sem_typed_open W Θ Δ F e i lb m C T U :
  Δ !! i = Some (Some (TEx lb m C T)) →
  (∀ W1 xs, wext W W1 → length xs = m → Forall (pt_known W1) xs →
     bcs_hold (w_eq W1) (w_lt W1) C xs →
     sem_typed W1 Θ (<[i := Some (ty_inst xs T)]> Δ) F e U) →
  sem_typed W Θ Δ F e U.
Proof.
  intros Hi He n W' Θ' Θ'' γ HW Hc Hg.
  destruct (grounding_open _ _ _ _ _ _ _ _ _ _ Hi Hg) as (xs & Hxs & HK & HC & Hg').
  apply (He W' xs HW Hxs HK HC n W' Θ' Θ'' γ); [|done|done].
  apply wext_refl. by destruct HW as (_&_&_&?).
Qed.

(** E-OpenPair: the scrutinee of a let pair has type ∃ιs. C. T₁ ⊗ T₂,
    and the body is good at every instance that meets C. *)
Lemma sem_typed_openp W Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 lb m C T1 T2 T :
  tenv_comp (w_eq W) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
  sem_typed W Θ1 Δ1 (F ∪ (tenv_heads Θ2 ∪ lenv_heads Δ2)) e1 (TEx lb m C (TProd T1 T2)) →
  (∀ W1 xs, wext W W1 → length xs = m → Forall (pt_known W1) xs →
     bcs_hold (w_eq W1) (w_lt W1) C xs →
     sem_typed W1 Θ2 (Some (ty_inst xs T2) :: Some (ty_inst xs T1) :: Δ2) F e2 T) →
  sem_typed W Θ Δ F (LetP e1 e2) T.
Proof.
  intros Hc Hsp He1 He2 n W' Θ' Θ'' γ HW Hc'' Hg. simpl.
  change (LetP (subst γ e1) (subst (up (up γ)) e2))
    with (fill_frame (FLetP (subst (up (up γ)) e2)) (subst γ e1)).
  eapply (sem_elim W Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 (TEx lb m C (TProd T1 T2)) T
            (λ γ, FLetP (subst (up (up γ)) e2)));
    [done|done|done|done| |done|done|done].
  clear dependent Θ' Θ'' n γ W'.
  intros n W' Θ' Θ'' γ HW Hc' Hg W'' j Θ1' Θ3 v HW'' Hj Hc3 HV. simpl.
  pose proof (wext_trans _ _ _ HW HW'') as HW2.
  apply Vrel_ex_iff in HV as [_ (xs & Hxs & HK & HC & HV)].
  unfold ty_inst in HV. cbn [pinst_ty] in HV.
  apply Vrel_prod_iff in HV as (v1 & v2 & Θa & Θb & -> & Hcab & HV1 & HV2).
  pose proof (Vrel_val _ _ _ _ _ HV1) as Hv1. pose proof (Vrel_val _ _ _ _ _ HV2) as Hv2.
  pose proof (tenv_comp_mono _ _ _ _ _ (proj1 (proj2 HW'')) Hc') as Hc'W.
  destruct (comp_bind2 _ _ _ _ _ _ _ _ (wext_sym _ _ HW2) Hc3 Hcab Hc'W) as (X & A & HX & HXA & HA).
  apply (Erel_det_beta _ _ _ _ _ _ (subst2 v1 v2 (subst (up (up γ)) e2))).
  - by apply TStepHead, HeadLetP.
  - intros α e'' Hst. apply tstep_letp_inv in Hst as [(e1' & Hst & _)|(u & w & Heq & _ & _ & -> & ->)].
    + exfalso. eapply val_no_tstep; [exact Hst|]. simpl. by apply andb_True.
    + by injection Heq as -> ->.
  - rewrite subst2_subst.
    apply (He2 W'' xs HW2 Hxs HK HC j W'' X Θ3); [apply wext_refl; by destruct HW2 as (_&_&_&?)|done|].
    exists Θb, A. split_and!; [done|done|].
    exists Θa, Θ'. split_and!; [done|done|].
    eapply grounding_ext; [|eapply grounding_down; [exact Hj|]].
    { intros i. done. }
    eapply grounding_mono; [exact (wext_wf _ _ HW)|exact HW''|exact Hg].
Qed.

(** * ∀ apart from □ (sharp edges 101)

    E-Gen generalizes a value that holds no channel over the points ιs
    under the constraint C. E-Inst instantiates a term of type
    ∀ιs. C. T at known points that meet C. *)

Lemma is_val_subst_g γ e : is_val e → is_val (subst γ e).
Proof.
  revert γ. induction e; intros γ; simpl; try done; intros H.
  all: try (apply andb_True in H as [H1 H2]; apply andb_True; split; auto).
  all: auto.
Qed.

(** E-Gen, the value restriction: v is a value, its environment is
    unlimited, and it is good at every instance that meets C in every
    later world. *)
Lemma sem_typed_gen W Δ F v m C T :
  is_val v → lenv_unl Δ → term_wf ∅ Δ v →
  (∀ W1 xs, wext W W1 → length xs = m → Forall (pt_known W1) xs →
     bcs_hold (w_eq W1) (w_lt W1) C xs →
     sem_typed W1 ∅ Δ F v (ty_inst xs T)) →
  sem_typed W ∅ Δ F v (TAll m C T).
Proof.
  intros Hv Hu (Hfc & Hfv & _) He n W' Θ' Θ'' γ HW Hc Hg.
  pose proof (wext_wf _ _ HW) as HW'.
  pose proof (grounding_unl _ _ _ _ _ HW' Hu Hg) as ->.
  apply tenv_comp_empty_inv in Hc as ->.
  destruct n as [|n']; [apply Erel_0|].
  apply Vrel_Erel. apply Vrel_all_iff. split_and!.
  - done.
  - by apply is_val_subst_g.
  - assert (fchans (subst γ v) ⊆ fchans v ∪ dom (∅ : tenv)) as Hsub.
    { apply fchans_subst. eapply allfv_mono; [|exact Hfv].
      intros x (T' & Hx). by eapply grounding_fchans. }
    rewrite Hfc, dom_empty_L in Hsub. set_solver.
  - intros W2 xs HW2 Hxs HC HK.
    pose proof (wext_trans _ _ _ HW HW2) as HWW2.
    assert (Erel (S n') W2 ∅ (ty_inst xs T) F (subst γ v)) as HE.
    { apply (He W2 xs HWW2 Hxs HK HC (S n') W2 ∅ ∅ γ).
      - apply wext_refl. by destruct HWW2 as (_&_&_&?).
      - apply tenv_comp_empty_r.
      - eapply grounding_mono; [exact HW'|exact HW2|exact Hg]. }
    apply Erel_S_iff in HE as (Hval & _ & _). apply Hval.
    apply val_irred. by apply is_val_subst_g.
Qed.

(** E-Inst: a term of type ∀ιs. C. T has type T[xs/ιs] at known points
    xs that meet C. *)
Lemma sem_typed_inst W Θ Δ F e m C T xs :
  length xs = m → Forall (pt_known W) xs → bcs_hold (w_eq W) (w_lt W) C xs →
  sem_typed W Θ Δ F e (TAll m C T) → sem_typed W Θ Δ F e (ty_inst xs T).
Proof.
  intros Hxs HK HC He n W' Θ' Θ'' γ HW Hc Hg.
  eapply Erel_Vsub; [by destruct HW as (_&_&_&?)| |by apply (He n W' Θ' Θ'' γ)].
  intros j W2 Θ2 v Hj HW2 HV. pose proof (wext_trans _ _ _ HW HW2) as HWW2.
  apply Vrel_all_iff in HV as (-> & _ & _ & H). apply H.
  - apply wext_refl. by destruct HWW2 as (_&_&_&?).
  - done.
  - destruct HWW2 as (_ & He2 & Hl2 & _). eapply bcs_hold_mono; [exact He2|exact Hl2|exact HC].
  - eapply Forall_impl; [exact HK|]. intros x. unfold pt_known. destruct HWW2 as (? & _). set_solver.
Qed.
