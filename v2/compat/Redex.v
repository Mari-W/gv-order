(** * Operator redexes, once for every cost table (stage S4)

    For each saturated operator k and each value v in V at the type of
    its argument, Op k v is in E at the type of its result, under the
    conditions of the typing rule read in the world ([Erel_send] to
    [Erel_new_at], [Erel_new], [Erel_force]). The β redexes are
    [Erel_beta] and [Erel_app].

    Two facts about V carry the proofs. The environment of a value in V
    holds exactly the ends the value mentions ([Vrel_exact], decision
    Q14), so a send and a spawn hand over the environment of the value,
    which O-Send and O-Spawn therefore need not state. The heads of the
    environment of a value lie above the heads of its type when its type
    has no ⊥ flag ([Vrel_heads]), so readiness of a send follows from
    the payload premises of E-Send. *)

From GV Require Export compat.Blind types.Duality.
From GV Require lockfree.FairRun.

(** Excluded middle, without the notations of lockfree/FairRun.v. *)
Notation excluded_middle := lockfree.FairRun.excluded_middle.

(** ** Exact ends and heads of values in V *)

Section values.
  Context (κ : ctable).

  Lemma Vrel_exact n W Θ T v : Vrel κ n W Θ T v → dom Θ = fends v.
  Proof.
    revert W Θ v. induction T as [T IH] using tsize_ind. intros W Θ v.
    destruct T as [|ub lb c T1 U a|T1 U|T1 U|m kk C ub c U|s x a mt|lb m C T1].
    - intros [-> ->]%Vrel_unit_iff. by rewrite dom_empty_L.
    - by intros (e & -> & Hfe & _)%Vrel_lolli_iff.
    - intros (v1 & v2 & Θ1 & Θ2 & -> & _ & -> & H1 & H2)%Vrel_prod_iff. simpl.
      rewrite dom_union_L. erewrite (IH T1), (IH U); [done|simpl; lia|done|simpl; lia|done].
    - intros [(v' & -> & H)|(v' & -> & H)]%Vrel_sum_iff; simpl;
        [eapply (IH T1)|eapply (IH U)]; eauto; simpl; lia.
    - intros (-> & e & -> & Hfe & _)%Vrel_box_iff. simpl. by rewrite dom_empty_L.
    - intros (o & s' & -> & -> & _)%Vrel_sess_iff. simpl. by rewrite dom_singleton_L.
    - intros (_ & xs & _ & _ & H)%Vrel_ex_iff. eapply (IH (ty_inst xs T1)); [|exact H].
      unfold ty_inst. rewrite tsize_pinst. simpl. lia.
  Qed.

  Lemma at_cost_V_exact n c m W Θ T v :
    olt ozero n → at_cost_V n c (Vrel κ) (Vrel κ m) W Θ T v → dom Θ = fends v.
  Proof.
    intros Hn [H0 H1]. destruct (decide (c = 0)) as [Hc|Hc];
      [exact (Vrel_exact _ _ _ _ _ (H0 Hc))|exact (Vrel_exact _ _ _ _ _ (H1 Hc ozero Hn (or_intror eq_refl)))].
  Qed.

  Lemma Vrel_heads n W Θ T v :
    Vrel κ n W Θ T v → hbot T = false →
    ∀ o S x, Θ !! o = Some (S, x) → ∃ h, h ∈ heads T ∧ w_le W h x‾.
  Proof.
    revert W Θ v. induction T as [T IH] using tsize_ind. intros W Θ v.
    destruct T as [|ub lb c T1 U a|T1 U|T1 U|m kk C ub c U|s x0 a mt|lb m C T1].
    - intros [-> ->]%Vrel_unit_iff _ o S x Hx. by rewrite lookup_empty in Hx.
    - intros (e & -> & _ & Hlb & _)%Vrel_lolli_iff Hb o S x Hx.
      assert (x‾ ∈ senv_heads Θ) as Hh by (apply elem_of_senv_heads; eauto).
      destruct lb as [| |l]; simpl in Hlb, Hb |- *; try discriminate.
      + rewrite Hlb in Hh. set_solver.
      + exists l. split; [set_solver|by apply Hlb].
    - intros (v1 & v2 & Θ1 & Θ2 & -> & _ & -> & H1 & H2)%Vrel_prod_iff Hb o S x Hx.
      simpl in Hb. apply orb_false_iff in Hb as [Hb1 Hb2].
      apply lookup_union_Some_raw in Hx as [Hx|[_ Hx]].
      + destruct (IH T1 ltac:(simpl; lia) _ _ _ H1 Hb1 o S x Hx) as (h0 & ? & ?).
        exists h0. simpl. set_solver.
      + destruct (IH U ltac:(simpl; lia) _ _ _ H2 Hb2 o S x Hx) as (h0 & ? & ?).
        exists h0. simpl. set_solver.
    - intros [(v' & -> & H)|(v' & -> & H)]%Vrel_sum_iff Hb o S x Hx;
        simpl in Hb; apply orb_false_iff in Hb as [Hb1 Hb2].
      + destruct (IH T1 ltac:(simpl; lia) _ _ _ H Hb1 o S x Hx) as (h0 & ? & ?).
        exists h0. simpl. set_solver.
      + destruct (IH U ltac:(simpl; lia) _ _ _ H Hb2 o S x Hx) as (h0 & ? & ?).
        exists h0. simpl. set_solver.
    - intros (-> & _)%Vrel_box_iff _ o S x Hx. by rewrite lookup_empty in Hx.
    - intros (o' & s' & -> & -> & _)%Vrel_sess_iff _ o S x Hx.
      apply lookup_singleton_Some in Hx as [-> Heq]. injection Heq as -> ->. exists x‾.
      split; [simpl; set_solver|by left].
    - intros (Hlb & _)%Vrel_ex_iff Hb o S x Hx.
      assert (x‾ ∈ senv_heads Θ) as Hh by (apply elem_of_senv_heads; eauto).
      destruct lb as [| |l]; simpl in Hlb, Hb |- *; try done.
      + rewrite Hlb in Hh. set_solver.
      + exists l. split; [set_solver|by apply Hlb].
  Qed.
End values.

(** ** Steps of a redex *)

(** A term whose evaluation positions hold values steps only at its
    head. *)
Lemma tstep_head_only e α e' :
  (∀ f e0, frame_val f → e = fill_frame f e0 → is_val e0) →
  tstep e α e' → head_step e α e'.
Proof.
  intros Hv Hst. apply tstep_inv in Hst as [Hh|(f & e0 & e0' & Hf & -> & -> & Hs)]; [done|].
  exfalso. apply (val_no_tstep _ _ _ Hs). by apply (Hv f).
Qed.

Lemma op_head_only k v α e' : is_val v → tstep (Op k v) α e' → head_step (Op k v) α e'.
Proof. intros Hv. apply tstep_head_only. intros [] e0 _ [=]; by subst. Qed.

Ltac head_only :=
  apply tstep_head_only;
  [intros [] ? ? [=]; subst; simpl in *; rewrite ?andb_True; naive_solver|assumption].

(** A term with a τ step is not stable, so it is ready. *)
Lemma ready_tau W Θ F e α e' :
  tstep e α e' → (∀ σ, α ≠ LSess σ) → ready _ W(Θ ∣ F, e).
Proof. intros Hst Hα Hs. destruct (Hs _ _ Hst) as [σ ->]. by destruct (Hα σ). Qed.

(** A term whose session steps all act on o alone, with o at x below
    every other held end and below F, is ready. *)
Lemma ready_on W Θ F e o S x :
  ¬ is_val e → (∃ σ e', tstep e (LSess σ) e' ∧ o ∈ sends σ) →
  (∀ σ e', tstep e (LSess σ) e' → sends σ = {[o]}) →
  Θ !! o = Some (S, x) →
  (∀ o' S' x', Θ !! o' = Some (S', x') → o' ≠ o → W ⊢ x ≺ x'‾) →
  (∀ y, y ∈ F → W ⊢ x ≺ y) →
  ready _ W(Θ ∣ F, e).
Proof.
  intros Hv (σ0 & e0 & Hst0 & Hs0) Hon Ho Hrest HF _. split.
  - intros Hno. exfalso. apply (Hno o). split; [by apply elem_of_dom_2 in Ho|eauto].
  - right. intros o1 S1 x1 [_ (σ & e' & Hst & Hs)] Hx1.
    rewrite (Hon _ _ Hst) in Hs. apply elem_of_singleton in Hs as ->.
    rewrite Ho in Hx1. simplify_eq. split; [|done].
    intros o' S' x' Hx' Hno. apply (Hrest o' S' x' Hx'). intros ->. apply Hno.
    split; [by apply elem_of_dom_2 in Ho|eauto].
Qed.

Section redex.
  Context (κ : ctable).

  (** One unfolding of E from its three clauses, in every later world. *)
  Lemma Erel_S_intro n W Θ T F e :
    ¬ irred e →
    (∀ W1, W ⊑ W1 → ready _ W1(Θ ∣ F, e)) →
    (∀ W1 α e', W ⊑ W1 → tstep e α e' →
       Eobl κ n (Vrel κ) (Erel κ) (Vrel κ n) (Erel κ n) W1 Θ T F α e') →
    Erel κ n W Θ T F e.
  Proof.
    intros Hni Hr Hs. apply Erel_iff. intros W1 HW1. split_and!.
    - intros Hi. by destruct Hni.
    - intros _. by apply Hr.
    - apply Esteps_iff. intros α e' Hst. by apply Hs.
  Qed.

  (** A value after a step of cost c. *)
  Lemma at_cost_val n c W Θ T F v :
    Vrel κ n W Θ T v → at_cost_E n c (Erel κ) (Erel κ n) W Θ T F v.
  Proof.
    intros HV. split; [intros _; by apply Vrel_Erel|]. intros _ j Hj. apply Vrel_Erel.
    eapply Vrel_down; [|exact HV]. exact (oadd_le_l _ _ _ Hj).
  Qed.

  Lemma at_cost_payload n c W Θ T T' v :
    teq (ty_df T) (ty_df T') →
    Vrel κ n W Θ T v → at_cost_V n c (Vrel κ) (Vrel κ n) W Θ T' v.
  Proof.
    intros Heq HV. apply (Vrel_teq κ _ _ _ _ _ _ Heq) in HV.
    split; [by intros _|]. intros _ j Hj _. eapply Vrel_down; [|exact HV]. by apply olt_ole.
  Qed.

  (** ** β redexes *)

  Lemma Erel_beta n W Θ T F e e' :
    (∀ α e'', tstep e α e'' → α = LBeta ∧ e'' = e') → tstep e LBeta e' →
    (∀ j, ole (oadd j (c_beta κ)) n → Erel κ j W Θ T F e') → Erel κ n W Θ T F e.
  Proof.
    intros Hdet Hst HE. apply Erel_S_intro.
    - intros Hi. exact (Hi _ _ Hst).
    - intros W1 _. eapply ready_tau; [exact Hst|done].
    - intros W1 α e'' HW1 Hs. destruct (Hdet _ _ Hs) as [-> ->]. simpl.
      split.
      + intros Hc. eapply Erel_mono; [done|]. apply HE. rewrite Hc. apply ole_refl.
      + intros Hc j Hj. eapply Erel_mono; [done|]. by apply HE.
  Qed.

  (** A force step, at cost κ(force). *)
  Lemma Erel_fstep n W Θ T F e e' :
    (∀ α e'', tstep e α e'' → α = LForce ∧ e'' = e') → tstep e LForce e' →
    (∀ j, ole (oadd j (c_force κ)) n → Erel κ j W Θ T F e') → Erel κ n W Θ T F e.
  Proof.
    intros Hdet Hst HE. apply Erel_S_intro.
    - intros Hi. exact (Hi _ _ Hst).
    - intros W1 _. eapply ready_tau; [exact Hst|done].
    - intros W1 α e'' HW1 Hs. destruct (Hdet _ _ Hs) as [-> ->]. simpl.
      split.
      + intros Hc. eapply Erel_mono; [done|]. apply HE. rewrite Hc. apply ole_refl.
      + intros Hc j Hj. eapply Erel_mono; [done|]. by apply HE.
  Qed.

  Lemma Erel_app n W Θ1 Θ2 ub lb c T1 U a2 F f w :
    Θ1 ##ₘ Θ2 → ub_ltu W ub F →
    Vrel κ n W Θ1 (TLolli ub lb c T1 U a2) f → Vrel κ n W Θ2 T1 w →
    Erel κ n W (Θ1 ∪ Θ2) U F (App f w).
  Proof.
    intros Hd Hub (e & -> & _ & _ & H)%Vrel_lolli_iff Hw.
    pose proof (Vrel_val κ _ _ _ _ _ Hw) as Hwv.
    apply (Erel_beta _ _ _ _ _ _ (subst1 w e)).
    - intros α e'' Hs. assert (head_step (App (Lam e) w) α e'') as Hh by head_only.
      inversion Hh; by subst.
    - by apply tstep_head, t_act_app.
    - intros j Hj. apply H; [apply wext_refl|exact Hj|done|done|].
      eapply Vrel_down; [|exact Hw]. exact (oadd_le_l _ _ _ Hj).
  Qed.

  (** ** Session operators *)

  Lemma Erel_send aq1 aq2 n W Θ m U S0 S x F v mt1 mt2 :
    unfoldS S0 = SSeq (SSnd m U) S → hbot (payload_at m U x) = false →
    (∀ y, y ∈ heads (payload_at m U x) → W ⊢ x ≺ y) → (∀ y, y ∈ F → W ⊢ x ≺ y) →
    Vrel κ n W Θ (TProd (payload_at m U x) (TSess S0 x aq1 mt1)) v →
    Erel κ n W Θ (TSess S x⁺ aq2 mt2) F (ESend v).
  Proof.
    intros Hu Hb Hh HF HV.    apply Vrel_prod_iff in HV as (w & vo & Θw & Θo & -> & Hd & -> & Hw & Ho).
    apply Vrel_sess_iff in Ho as (o & s' & -> & -> & Hs').
    destruct (seqv_unfold_snd _ _ _ _ _ Hs' Hu) as (U' & S' & Hu' & HU & HS).
    pose proof (Vrel_val κ _ _ _ _ _ Hw) as Hwv.
    assert (Θw !! o = None) as Hwo by (eapply map_disjoint_Some_r; [exact Hd|apply lookup_singleton_eq]).
    assert (tstep (ESend (Pair w (Chan o))) (LSess (SSend o w)) (Chan o)) as Hst
      by (by apply tstep_head, t_act_send).
    assert (∀ α e', tstep (ESend (Pair w (Chan o))) α e' →
              α = LSess (SSend o w) ∧ e' = Chan o) as Hdet.
    { intros α e' Hs. apply op_head_only in Hs; [|simpl; by rewrite andb_True].
      inversion Hs; by subst. }
    apply Erel_S_intro.
    - intros Hi. exact (Hi _ _ Hst).
    - intros W1 HW1. eapply (ready_on _ _ _ _ o s' x); [simpl; tauto|eexists _, _; split; [exact Hst|simpl; set_solver]| | | |].
      + intros σ e' Hs. destruct (Hdet _ _ Hs) as [[= ->] _]. done.
      + apply lookup_union_Some_r; [done|apply lookup_singleton_eq].
      + intros o' S2 x' Hx' Hne. apply lookup_union_Some_raw in Hx' as [Hx'|[_ Hx']].
        * destruct (Vrel_heads κ _ _ _ _ _ Hw Hb o' S2 x' Hx') as (h & Hh' & Hle).
          eapply w_lt_mono; [exact HW1|].
          destruct Hle as [<-|Hlt]; [by apply Hh|eapply w_lt_trans; [by apply Hh|exact Hlt]].
        * by apply lookup_singleton_Some in Hx' as [? _].
      + intros y Hy. eapply w_lt_mono; [done|by apply HF].
    - intros W1 α e' HW1 Hs. destruct (Hdet _ _ Hs) as [-> ->]. simpl.
      exists s', x, m, U', S', Θw, ∅. split_and!.
      + apply lookup_union_Some_r; [done|apply lookup_singleton_eq].
      + done.
      + apply map_disjoint_empty_r.
      + rewrite map_union_empty, delete_union, delete_singleton_eq, map_union_empty.
        by apply delete_id.
      + apply (at_cost_payload _ _ _ _ (payload_at m U x)).
        * rewrite <-!payload_at_df. unfold payload_at. apply teq_pinst. by apply teq_sym.
        * by eapply Vrel_mono.
      + apply at_cost_val. rewrite insert_empty. apply Vrel_sess_iff.
        exists o, S'. split_and!; [done|done|done].
  Qed.

  Lemma Erel_recv aq1 aq2 n W Θ m U S0 S x F v mt1 mt2 :
    unfoldS S0 = SSeq (SRcv m U) S → (∀ y, y ∈ F → W ⊢ x ≺ y) →
    Vrel κ n W Θ (TSess S0 x aq1 mt1) v →
    Erel κ n W Θ (TProd (payload_at m U x) (TSess S x⁺ aq2 mt2)) F (ERecv v).
  Proof.
    intros Hu HF HV.    apply Vrel_sess_iff in HV as (o & s' & -> & -> & Hs').
    destruct (seqv_unfold_rcv _ _ _ _ _ Hs' Hu) as (U' & S' & Hu' & HU & HS).
    assert (tstep (ERecv (Chan o)) (LSess (SRecv o EUnit)) (Pair EUnit (Chan o))) as Hst
      by (by apply tstep_head, t_act_recv).
    assert (∀ α e', tstep (ERecv (Chan o)) α e' →
              ∃ w, α = LSess (SRecv o w) ∧ e' = Pair w (Chan o) ∧ is_val w) as Hdet.
    { intros α e' Hs. apply op_head_only in Hs; [|done]. inversion Hs; subst; eauto. }
    apply Erel_S_intro.
    - intros Hi. exact (Hi _ _ Hst).
    - intros W1 HW1. eapply (ready_on _ _ _ _ o s' x); [simpl; tauto|eexists _, _; split; [exact Hst|simpl; set_solver]| | | |].
      + intros σ e' Hs. by destruct (Hdet _ _ Hs) as (w & [= ->] & _).
      + apply lookup_singleton_eq.
      + intros o' Sx x' Hx' Hne. by apply lookup_singleton_Some in Hx' as [? _].
      + intros y Hy. eapply w_lt_mono; [done|by apply HF].
    - intros W1 α e' HW1 Hs. destruct (Hdet _ _ Hs) as (w & -> & -> & Hwv). simpl.
      exists s', x, m, U', S'. split_and!; [apply lookup_singleton_eq|done|].
      intros j Θin Hj Hd Hw. apply Vrel_Erel. rewrite insert_singleton_eq.
      apply Vrel_prod_iff. exists w, (Chan o), Θin, {[o := (S', x⁺)]}. split_and!.
      + done.
      + apply map_disjoint_singleton_r. eapply map_disjoint_Some_l; [exact Hd|apply lookup_singleton_eq].
      + apply map_union_comm. apply map_disjoint_singleton_l.
        eapply map_disjoint_Some_l; [exact Hd|apply lookup_singleton_eq].
      + refine (proj1 (Vrel_teq κ j W1 Θin (payload_at m U' x) (payload_at m U x) w _) Hw).
        rewrite <-!payload_at_df. unfold payload_at. by apply teq_pinst.
      + apply Vrel_sess_iff. exists o, S'. done.
  Qed.

  Lemma Erel_close aq1 n W Θ S0 x F v mt :
    unfoldS S0 = SEnd → (∀ y, y ∈ F → W ⊢ x ≺ y) →
    Vrel κ n W Θ (TSess S0 x aq1 mt) v → Erel κ n W Θ TUnit F (EClose v).
  Proof.
    intros Hu HF HV.    apply Vrel_sess_iff in HV as (o & s' & -> & -> & Hs').
    pose proof (seqv_unfold_end _ _ Hs' Hu) as Hu'.
    assert (tstep (EClose (Chan o)) (LSess (SClose o)) EUnit) as Hst
      by (by apply tstep_head, t_act_close).
    assert (∀ α e', tstep (EClose (Chan o)) α e' → α = LSess (SClose o) ∧ e' = EUnit) as Hdet.
    { intros α e' Hs. apply op_head_only in Hs; [|done]. inversion Hs; by subst. }
    apply Erel_S_intro.
    - intros Hi. exact (Hi _ _ Hst).
    - intros W1 HW1. eapply (ready_on _ _ _ _ o s' x); [simpl; tauto|eexists _, _; split; [exact Hst|simpl; set_solver]| | | |].
      + intros σ e' Hs. by destruct (Hdet _ _ Hs) as [[= ->] _].
      + apply lookup_singleton_eq.
      + intros o' Sx x' Hx' Hne. by apply lookup_singleton_Some in Hx' as [? _].
      + intros y Hy. eapply w_lt_mono; [done|by apply HF].
    - intros W1 α e' HW1 Hs. destruct (Hdet _ _ Hs) as [-> ->]. simpl.
      exists s', x. split_and!; [apply lookup_singleton_eq|done|].
      rewrite delete_singleton_eq. apply at_cost_val. by apply Vrel_unit_iff.
  Qed.

  Lemma Erel_select aq1 aq2 (i : bool) n W Θ S0 x S1 S2 F v mt1 mt2 :
    unfoldS S0 = SPlus S1 S2 → (∀ y, y ∈ F → W ⊢ x ≺ y) →
    Vrel κ n W Θ (TSess S0 x aq1 mt1) v →
    Erel κ n W Θ (TSess (if i then S2 else S1) (sel_pt x i) aq2 mt2) F (ESel i v).
  Proof.
    intros Hu HF HV.    apply Vrel_sess_iff in HV as (o & s' & -> & -> & Hs').
    destruct (seqv_unfold_plus _ _ _ _ Hs' Hu) as (S1' & S2' & Hu' & H1 & H2).
    assert (tstep (ESel i (Chan o)) (LSess (SSel o i)) (Chan o)) as Hst
      by (by apply tstep_head, t_act_select).
    assert (∀ α e', tstep (ESel i (Chan o)) α e' → α = LSess (SSel o i) ∧ e' = Chan o) as Hdet.
    { intros α e' Hs. apply op_head_only in Hs; [|done]. inversion Hs; by subst. }
    apply Erel_S_intro.
    - intros Hi. exact (Hi _ _ Hst).
    - intros W1 HW1. eapply (ready_on _ _ _ _ o s' x); [simpl; tauto|eexists _, _; split; [exact Hst|simpl; set_solver]| | | |].
      + intros σ e' Hs. by destruct (Hdet _ _ Hs) as [[= ->] _].
      + apply lookup_singleton_eq.
      + intros o' Sx x' Hx' Hne. by apply lookup_singleton_Some in Hx' as [? _].
      + intros y Hy. eapply w_lt_mono; [done|by apply HF].
    - intros W1 α e' HW1 Hs. destruct (Hdet _ _ Hs) as [-> ->]. simpl.
      exists s', x, S1', S2'. split_and!; [apply lookup_singleton_eq|done|].
      rewrite insert_singleton_eq. apply at_cost_val. apply Vrel_sess_iff.
      exists o, (bsel i S1' S2'). split_and!; [done|done|]. by destruct i.
  Qed.

  Lemma Erel_branch aq1 aq2 aq3 n W Θ S0 x S1 S2 F v mt1 mt2 mt3 :
    unfoldS S0 = SWith S1 S2 → (∀ y, y ∈ F → W ⊢ x ≺ y) →
    Vrel κ n W Θ (TSess S0 x aq1 mt1) v →
    Erel κ n W Θ (TSum (TSess S1 (bra_pt x false) aq2 mt2) (TSess S2 (bra_pt x true) aq3 mt3)) F (EBra v).
  Proof.
    intros Hu HF HV.    apply Vrel_sess_iff in HV as (o & s' & -> & -> & Hs').
    destruct (seqv_unfold_with _ _ _ _ Hs' Hu) as (S1' & S2' & Hu' & H1 & H2).
    assert (tstep (EBra (Chan o)) (LSess (SBra o false)) (Inj false (Chan o))) as Hst
      by (by apply tstep_head, t_act_branch).
    assert (∀ α e', tstep (EBra (Chan o)) α e' →
              ∃ i, α = LSess (SBra o i) ∧ e' = Inj i (Chan o)) as Hdet.
    { intros α e' Hs. apply op_head_only in Hs; [|done]. inversion Hs; subst; eauto. }
    apply Erel_S_intro.
    - intros Hi. exact (Hi _ _ Hst).
    - intros W1 HW1. eapply (ready_on _ _ _ _ o s' x); [simpl; tauto|eexists _, _; split; [exact Hst|simpl; set_solver]| | | |].
      + intros σ e' Hs. by destruct (Hdet _ _ Hs) as (i & [= ->] & _).
      + apply lookup_singleton_eq.
      + intros o' Sx x' Hx' Hne. by apply lookup_singleton_Some in Hx' as [? _].
      + intros y Hy. eapply w_lt_mono; [done|by apply HF].
    - intros W1 α e' HW1 Hs. destruct (Hdet _ _ Hs) as (i & -> & ->). simpl.
      exists s', x, S1', S2'. split_and!; [apply lookup_singleton_eq|done|].
      rewrite insert_singleton_eq. apply at_cost_val. apply Vrel_sum_iff.
      destruct i; [right|left]; eexists; (split; [done|]); apply Vrel_sess_iff; eexists _, _; done.
  Qed.

  Lemma sdual_of s1 s2 S : seqv s1 S → seqv s2 (dual S) → sdual s1 s2.
  Proof.
    unfold sdual, seqv. intros H1 H2. rewrite sty_df_dual in *.
    eapply sequiv_trans; [exact H2|]. apply sequiv_dual, sequiv_sym, H1.
  Qed.

  Lemma Erel_link aq1 aq2 n W Θ S x F v mt1 mt2 :
    Vrel κ n W Θ (TProd (TSess S x aq1 mt1) (TSess (dual S) x‾ aq2 mt2)) v → Erel κ n W Θ TUnit F (ELink v).
  Proof.
    intros HV.    apply Vrel_prod_iff in HV as (v1 & v2 & Θ1 & Θ2 & -> & Hd & -> & H1 & H2).
    apply Vrel_sess_iff in H1 as (o1 & s1 & -> & -> & Hs1).
    apply Vrel_sess_iff in H2 as (o2 & s2 & -> & -> & Hs2).
    assert (o1 ≠ o2) as Hne.
    { intros ->. pose proof (map_disjoint_Some_l _ _ o2 _ Hd (lookup_singleton_eq _ _)) as Hc.
      by rewrite lookup_singleton_eq in Hc. }
    assert (tstep (ELink (Pair (Chan o1) (Chan o2))) (LSess (SLink ({[o1]} ∪ {[o2]}))) EUnit) as Hst
      by (by apply tstep_head, t_act_link).
    assert (∀ α e', tstep (ELink (Pair (Chan o1) (Chan o2))) α e' →
              α = LSess (SLink ({[o1]} ∪ {[o2]})) ∧ e' = EUnit) as Hdet.
    { intros α e' Hs. apply op_head_only in Hs; [|done]. inversion Hs; by subst. }
    apply Erel_S_intro.
    - intros Hi. exact (Hi _ _ Hst).
    - intros W1 _ Hs. split.
      + intros Hno. exfalso. apply (Hno o1). split; [rewrite dom_union_L, dom_singleton_L; set_solver|].
        eexists _, _. split; [exact Hst|simpl; set_solver].
      + left. by eexists _, _.
    - intros W1 α e' HW1 Hs. destruct (Hdet _ _ Hs) as [-> ->]. simpl.
      exists o1, o2, s1, s2, x. split_and!; [done|done| | |by eapply sdual_of|].
      + by apply lookup_union_Some_l, lookup_singleton_eq.
      + apply lookup_union_Some_r; [done|apply lookup_singleton_eq].
      + match goal with |- context [delete o1 (delete o2 ?m)] =>
          assert (delete o1 (delete o2 m) = ∅) as -> end.
        { apply map_eq. intros k. rewrite lookup_empty.
          destruct (decide (k = o1)) as [->|H1]; [by rewrite lookup_delete_eq|].
          rewrite lookup_delete_ne by done.
          destruct (decide (k = o2)) as [->|H2]; [by rewrite lookup_delete_eq|].
          rewrite lookup_delete_ne by done.
          apply lookup_union_None. split; by apply lookup_singleton_ne. }
        apply at_cost_val. by apply Vrel_unit_iff.
  Qed.

  Lemma Varr_top_of_Vrel n W Θ ub lb c aU v :
    Vrel κ n W Θ (TLolli ub lb c TUnit TUnit aU) v →
    Varr κ n (Vrel κ) (Erel κ) (λ _ _ Θ' w, Θ' = ∅ ∧ w = EUnit)
      (λ _ W' Θ' F e, Erel κ n W' Θ' TUnit F e) TUnit TUnit UTop LBot W Θ v.
  Proof.
    intros HV. apply (Vrel_thunk κ _ _ _ ub lb).
    eapply (Vrel_blind κ); [|exact HV]. done.
  Qed.
  Lemma Erel_spawn n W Θ ub lb c aU F v :
    Vrel κ n W Θ (TLolli ub lb c TUnit TUnit aU) v → Erel κ n W Θ TUnit F (ESpawn v).
  Proof.
    intros HV.    pose proof (Vrel_val κ _ _ _ _ _ HV) as Hv.
    assert (tstep (ESpawn v) (LSpawn v) EUnit) as Hst by (by apply tstep_head, t_act_spawn).
    assert (∀ α e', tstep (ESpawn v) α e' → α = LSpawn v ∧ e' = EUnit) as Hdet.
    { intros α e' Hs. apply op_head_only in Hs; [|done]. inversion Hs; by subst. }
    apply Erel_S_intro.
    - intros Hi. exact (Hi _ _ Hst).
    - intros W1 _. eapply ready_tau; [exact Hst|done].
    - intros W1 α e' HW1 Hs. destruct (Hdet _ _ Hs) as [-> ->]. simpl.
      exists Θ, ∅. split_and!.
      + apply map_disjoint_empty_r.
      + by rewrite map_union_empty.
      + eapply Varr_top_of_Vrel, Vrel_mono; [exact HW1|exact HV].
      + apply at_cost_val. by apply Vrel_unit_iff.
  Qed.

  (** ** Creation *)

  Lemma Vrel_newpair n W c S y aq1 aq2 mt1 mt2 :
    Vrel κ n W (new_env c S y ∅) (TProd (TSess S y aq1 mt1) (TSess (dual S) y‾ aq2 mt2))
      (Pair (Chan c⁺) (Chan c⁻)).
  Proof.
    unfold new_env. rewrite insert_empty, insert_union_singleton_l.
    apply Vrel_prod_iff. eexists _, _, _, _. split_and!; [done| |done| |].
    - apply map_disjoint_singleton_l, lookup_singleton_ne; done.
    - apply Vrel_sess_iff. eexists _, _. split_and!; [done|done|apply seqv_refl].
    - apply Vrel_sess_iff. eexists _, _. split_and!; [done|done|apply seqv_refl].
  Qed.

  Lemma ENew_step α e' : tstep ENew α e' → ∃ c, α = LNew c ∧ e' = Pair (Chan c⁺) (Chan c⁻).
  Proof. intros Hs. apply tstep_head_only in Hs; [|by intros []]. inversion Hs; subst; eauto. Qed.

  (** A creation at a field: the point is fixed, the world stays. *)
  Lemma Erel_new_fld aq1 aq2 n W S y F mt1 mt2 :
    Erel κ n W ∅ (TProd (TSess S y aq1 mt1) (TSess (dual S) y‾ aq2 mt2)) F ENew.
  Proof.
    assert (tstep ENew (LNew "") (Pair (Chan ""⁺) (Chan ""⁻))) as Hst
      by (by apply tstep_head, t_act_new).
    apply Erel_S_intro.
    - intros Hi. exact (Hi _ _ Hst).
    - intros W1 _. eapply ready_tau; [exact Hst|done].
    - intros W1 α e' HW1 Hs. destruct (ENew_step _ _ Hs) as (c & -> & ->). simpl.
      intros _. exists S, y, W1. split; [apply wext_refl|]. apply at_cost_val, Vrel_newpair.
  Qed.

  (** A constant base that W ranks nowhere and no point of env has. *)
  Lemma fresh_const (W : world) (env : list point) :
    ∃ a, NConst a ∉ w_roots W ∧ ∀ y, y ∈ env → pt_root y ≠ NConst a.
  Proof.
    set (cs := omap (λ r, match r with NConst n => Some n | _ => None end)
                 (elements (w_roots W) ++ (pt_root <$> env))).
    exists (fresh (list_to_set cs : gset nat)).
    pose proof (is_fresh (list_to_set cs : gset nat)) as Hf. split.
    - intros Hin. apply Hf, elem_of_list_to_set, list_elem_of_omap. exists (NConst (fresh (list_to_set cs : gset nat))).
      split; [|done]. apply elem_of_app. left. by apply elem_of_elements.
    - intros y Hy Hr. apply Hf, elem_of_list_to_set, list_elem_of_omap. exists (pt_root y).
      split; [|by rewrite Hr]. apply elem_of_app. right. apply list_elem_of_fmap. by exists y.
  Qed.

  (** The semantic form of (gen-new) in the ranked world W, with the
      environment of C already instantiated. *)
  Definition gen_new_sem (W : world) (C : bcs) : Prop :=
    well_founded (new_step C) ∧
    (∀ x y, cfact C x y → ¬ in_tree0 x → ¬ in_tree0 y → W ⊢ ctx_pt C x ≺ ctx_pt C y) ∧
    ∃ Sr : point → list point → Prop,
      (∀ s T, Sr s T → T ≠ []) ∧
      (∀ u y, cfact C u y → in_tree0 u → ¬ in_tree0 y →
         ∃ T, Sr u T ∧ ∀ t, t ∈ T → W ⊢ t ≺ ctx_pt C y) ∧
      (∀ s T s', Sr s T → new_step C s' s →
         ∃ T', Sr s' T' ∧ ∀ t', t' ∈ T' → ∃ t, t ∈ T ∧ W ⊢ t' ≺ t) ∧
      (∀ s T z, Sr s T → cfact C z s → ¬ in_tree0 z → ∃ t, t ∈ T ∧ W ⊢ ctx_pt C z ≺ t).

  Lemma gen_new_sem_mono W W' C : W ⊑ W' → gen_new_sem W C → gen_new_sem W' C.
  Proof.
    intros HW (Hwf & Hcc & Sr & Hne & Hex & Hst & Hen). split_and!; [done| |exists Sr; split_and!; [done| | |]].
    - intros. eapply w_lt_mono; [exact HW|]. by apply Hcc.
    - intros u y Hf Hu Hy. destruct (Hex u y Hf Hu Hy) as (T & HT & H). exists T. split; [done|].
      intros t Ht. eapply w_lt_mono; [exact HW|]. by apply H.
    - intros s T s' HT Hs. destruct (Hst s T s' HT Hs) as (T' & HT' & H). exists T'. split; [done|].
      intros t' Ht'. destruct (H t' Ht') as (t & Ht & Hlt). exists t. split; [done|]. by eapply w_lt_mono.
    - intros s T z HT Hf Hz. destruct (Hen s T z HT Hf Hz) as (t & Ht & Hlt). exists t. split; [done|].
      by eapply w_lt_mono.
  Qed.

  Lemma gen_new_sem_wf_new W C : wf_new C → gen_new_sem W C.
  Proof.
    intros [HC Hwf]. split_and!; [done| |exists (λ _ _, False); split_and!; try done].
    - intros x y [Hf Hs] _ Hy. exfalso. by apply Hy, (HC x y).
    - intros u y [Hf Hs] _ Hy. exfalso. by apply Hy, (HC u y).
  Qed.

  (** The ranks of W with offsets at the bases W does not rank rise
      along W. *)
  Lemma rk0_lt W x y : wranked W → W ⊢ x ≺ y →
    olt (wgrow_rank W (λ y, onat (pt_off y)) x) (wgrow_rank W (λ y, onat (pt_off y)) y).
  Proof.
    unfold wgrow_rank. intros HW [Hp|(Hx & Hy & Hlt)].
    - pose proof (rin_po W x y Hp) as Hr. destruct (po_root x y Hp) as [_ Ho].
      destruct (decide (rin W x)) as [Hx|Hx].
      + rewrite decide_True by tauto. by apply rank_po.
      + rewrite decide_False by tauto. by apply onat_lt.
    - rewrite !decide_True by done. by apply w_ord_rank.
  Qed.

  #[universes(polymorphic)] Lemma rank_base_le R b Hwf x β :
    ole (b x) β → (∀ y, R y x → olt (rank_base R b Hwf y) β) → ole (rank_base R b Hwf x) β.
  Proof.
    intros Hb Hy. unfold rank_base. generalize (Hwf x). intros [h]. cbn [rank_bacc].
    apply ole_lim_l. intros [|]; [done|]. apply ole_lim_l. intros [y Hr]. cbn [proj1_sig proj2_sig].
    eapply ole_trans; [apply ole_succ_succ, (rank_bacc_irr R b y _ (Hwf y))|]. exact (Hy y Hr).
  Qed.

  (** A creation at a fresh base under (gen-new). The creation grows
      the world by the fresh constant a and by the bases of the context
      points of C. The tree of a gets the least ranks of C with program
      order above the context points below it ([rank_base]). A point
      paired with the set T stays at or below the rank of the largest
      point of T, so each exit holds. The largest point exists under
      excluded middle ([list_max_rank]). *)
  Lemma Erel_new (EM : excluded_middle) aq1 aq2 n W C S F mt1 mt2 :
    wranked W → gen_new_sem W C →
    Erel κ n W ∅ (TEx LBot 1 C (TProd (TSess S (pvar 0) aq1 mt1) (TSess (dual S) (pvar 0)‾ aq2 mt2))) F ENew.
  Proof.
    intros HR HG.
    assert (tstep ENew (LNew "") (Pair (Chan ""⁺) (Chan ""⁻))) as Hst
      by (by apply tstep_head, t_act_new).
    apply Erel_S_intro.
    - intros Hi. exact (Hi _ _ Hst).
    - intros W1 _. eapply ready_tau; [exact Hst|done].
    - intros W1 α e' HW1 Hs. destruct (ENew_step _ _ Hs) as (c & -> & ->). simpl. intros _.
      destruct (gen_new_sem_mono _ _ _ HW1 HG) as (Hwf & Hcc & Sr & HnT & Hex & Hstp & Hen).
      pose proof (proj1 (wext_ranked _ _ HW1) HR) as HR1.
      destruct (fresh_const W1 (bc_env C)) as (a & Ha1 & Ha2).
      set (π := MkPt (NConst a) true 0).
      set (σ := plist (π :: bc_env C)).
      assert (σ 0 = MkPt (NConst a) true 0) as Hσ by done.
      set (rk0 := wgrow_rank W1 (λ y, onat (pt_off y))).
      assert (∀ x y, W1 ⊢ x ≺ y → olt (rk0 x) (rk0 y)) as Hrk0.
      { intros x y. unfold rk0, wgrow_rank. intros [Hp|(Hx & Hy & Hlt)].
        - pose proof (rin_po W1 x y Hp) as Hr. destruct (po_root x y Hp) as [_ Ho].
          destruct (decide (rin W1 x)) as [Hx|Hx].
          + rewrite decide_True by tauto. by apply rank_po.
          + rewrite decide_False by tauto. by apply onat_lt.
        - rewrite !decide_True by done. by apply w_ord_rank. }
      set (b0 := λ u0 : point, olim (λ s : {y : point | pt_root y ≠ NConst a ∧ bcs_at C [π] (FLt y (pt_inst σ u0))},
                   osucc (rk0 (proj1_sig s)))).
      set (ρ := λ x, if decide (pt_root x = NConst a) then rank_base (new_step C) b0 Hwf (pt_unroot a x)
                     else onat (pt_off x)).
      set (B := {[NConst a]} ∪ (list_to_set (pt_root <$> bc_env C) : gset pname)).
      assert (ranks_po B ρ) as Hρ.
      { intros x _. unfold ρ. change (pt_root x⁺) with (pt_root x). change (pt_root x‾⁺) with (pt_root x).
        destruct (decide (pt_root x = NConst a)) as [Hx|Hx].
        - pose proof (pt_root_unroot a x Hx) as H0.
          split; apply rank_base_lt; (split; [done|split; [done|right]]);
            [left|right]; done.
        - split; apply onat_lt; simpl; lia. }
      set (W' := wgrow W1 HR1 B ρ Hρ).
      assert (∀ x y, rin W' x → rin W' y → olt (w_rank W' x) (w_rank W' y) → W' ⊢ x ≺ y) as HltW.
      { intros x y Hx Hy H. right. split_and!; [done|done|]. apply w_ord_rank; [apply wgrow_ranked|done|done|done]. }
      assert (∀ x, pt_root x = NConst a → w_rank W' x = rank_base (new_step C) b0 Hwf (pt_unroot a x)) as Hra.
      { intros x Hx. unfold W'. rewrite wgrow_rank_new; [unfold ρ; by rewrite decide_True|]. unfold rin. rewrite Hx. done. }
      assert (∀ x, pt_root x ≠ NConst a → w_rank W' x = rk0 x) as Hro.
      { intros x Hx. unfold W'. change (w_rank (wgrow W1 HR1 B ρ Hρ) x) with (wgrow_rank W1 ρ x).
        unfold rk0, wgrow_rank. case_decide; [done|].
        unfold ρ. by rewrite decide_False. }
      (* the instance of a point of the tree of 0, and of a context point *)
      assert (∀ p, in_tree0 p → pt_root (pt_inst σ p) = NConst a ∧ rin W' (pt_inst σ p) ∧
                w_rank W' (pt_inst σ p) = rank_base (new_step C) b0 Hwf p) as Htr.
      { intros p Hp. assert (pt_root (pt_inst σ p) = NConst a) as Hr by (rewrite pt_root_inst_var, Hp; done).
        split_and!; [done|apply wgrow_rin; rewrite Hr; set_solver|].
        by rewrite (Hra _ Hr), (pt_unroot_inst a σ Hσ p Hp). }
      assert (∀ p, pn_vb (1 + length (bc_env C)) (pt_name p) → ¬ in_tree0 p →
                pt_inst σ p = ctx_pt C p ∧ pt_root (pt_inst σ p) ≠ NConst a ∧ rin W' (pt_inst σ p)) as Hout.
      { intros p Hsp Hp. apply pn_vb_root in Hsp as ([|j] & Hj & Hjl); [by destruct Hp|].
        simpl in Hjl. destruct (lookup_lt_is_Some_2 (bc_env C) j ltac:(lia)) as [yj Hyj].
        assert (pt_root (pt_inst σ p) = pt_root yj) as Hr.
        { rewrite pt_root_inst_var. change (pt_root p) with (pn_root (pt_name p)). rewrite Hj.
          simpl. unfold σ, plist. simpl. by rewrite Hyj. }
        split_and!.
        - unfold ctx_pt. apply pt_inst_ext_root. intros b Hb. change (pt_root p) with (pn_root (pt_name p)) in Hb.
          rewrite Hj in Hb. injection Hb as <-. done.
        - rewrite Hr. apply Ha2. by eapply list_elem_of_lookup_2.
        - apply wgrow_rin. rewrite Hr. apply elem_of_union_r, elem_of_list_to_set.
          apply list_elem_of_fmap. exists yj. split; [done|]. by eapply list_elem_of_lookup_2. }
      (* a point paired with T lies at or below the rank of some t ∈ T *)
      assert (∀ s, in_tree0 s → ∀ T, Sr s T → ∃ t, t ∈ T ∧ ole (rank_base (new_step C) b0 Hwf s) (rk0 t)) as Hinv.
      { intros s. induction (Hwf s) as [s _ IH]. intros Hsin T HT.
        destruct (list_max_rank EM rk0 T (HnT s T HT)) as (tm & Htm & Hmax).
        exists tm. split; [done|]. apply rank_base_le.
        - unfold b0. apply ole_lim_l. intros [y [Hyr Hy]]. cbn [proj1_sig].
          apply bcs_at_iff in Hy as ([z0 s0] & Hf & Hsc & Heq). simpl in Heq. injection Heq as Ey Es.
          try change (plist ([π] ++ bc_env C)) with σ in Ey, Es. try change (plist (π :: bc_env C)) with σ in Ey, Es.
          assert (in_tree0 s0) as Hs0.
          { destruct (decide (in_tree0 s0)) as [?|Hn]; [done|]. exfalso.
            destruct Hsc as [_ Hsc]. destruct (Hout s0 Hsc Hn) as (_ & Hne & _).
            apply Hne. rewrite <-Es. by apply Htr. }
          assert (s0 = s) as ->.
          { rewrite <-(pt_unroot_inst a σ Hσ s0 Hs0), <-(pt_unroot_inst a σ Hσ s Hsin). by rewrite Es. }
          assert (¬ in_tree0 z0) as Hz0.
          { intros Hz. apply Hyr. rewrite Ey. by apply Htr. }
          destruct Hsc as [Hsz Hss]. destruct (Hout z0 Hsz Hz0) as (Ez & _ & _). rewrite Ey, Ez.
          destruct (Hen s T z0 HT) as (t & Ht & Hlt); [split; [done|split; done]|done|].
          eapply olt_trans_le; [apply Hrk0, Hlt|apply Hmax, Ht].
        - intros s' Hs'. destruct (Hstp s T s' HT Hs') as (T' & HT' & Hlt).
          destruct (IH s' Hs' (proj1 Hs') T' HT') as (t' & Ht' & Hle).
          destruct (Hlt t' Ht') as (t & Ht & Hlt').
          eapply ole_trans_lt; [exact Hle|]. eapply olt_trans_le; [apply Hrk0, Hlt'|apply Hmax, Ht]. }
      exists S, π, W'. split; [apply wgrow_ext|].
      apply at_cost_val. apply Vrel_ex_iff. split; [done|]. exists [π]. split_and!; [done| |].
      + intros x y Hf. pose proof Hf as Hf0.
        apply bcs_at_iff in Hf as ([x0 y0] & Hf & Hsc & Heq). simpl in Heq. injection Heq as -> ->.
        try change (plist ([π] ++ bc_env C)) with σ in Hf0 |- *. try change (plist (π :: bc_env C)) with σ in Hf0 |- *.
        assert (cfact C x0 y0) as Hcf by (split; [done|exact Hsc]).
        destruct Hsc as [Hsx Hsy].
        destruct (decide (in_tree0 y0)) as [Hy0|Hy0], (decide (in_tree0 x0)) as [Hx0|Hx0].
        * destruct (Htr y0 Hy0) as (_ & Hry & Ey). destruct (Htr x0 Hx0) as (_ & Hrx & Ex).
          apply HltW; [done|done|]. rewrite Ex, Ey. apply rank_base_lt.
          split; [done|split; [done|left; exact Hcf]].
        * destruct (Htr y0 Hy0) as (_ & Hry & Ey). destruct (Hout x0 Hsx Hx0) as (_ & Hx & Hrx).
          apply HltW; [done|done|]. rewrite (Hro _ Hx), Ey.
          eapply olt_trans_le; [|apply rank_base_ge].
          unfold b0, olt. apply (ole_lim_r _ _ (exist _ (pt_inst σ x0) (conj Hx Hf0))). apply ole_refl.
        * destruct (Htr x0 Hx0) as (_ & Hrx & Ex). destruct (Hout y0 Hsy Hy0) as (Ey & Hy & Hry).
          destruct (Hex x0 y0 Hcf Hx0 Hy0) as (T & HT & Hlt).
          destruct (Hinv x0 Hx0 T HT) as (t & Ht & Hle).
          apply HltW; [done|done|]. rewrite Ex, (Hro _ Hy), Ey.
          eapply ole_trans_lt; [exact Hle|]. by apply Hrk0, Hlt.
        * destruct (Hout x0 Hsx Hx0) as (Ex & _ & _). destruct (Hout y0 Hsy Hy0) as (Ey & _ & _).
          rewrite Ex, Ey. eapply w_lt_mono; [apply wgrow_ext|]. by apply Hcc.
      + unfold ty_inst. simpl. rewrite pt_inst_dual, !pt_inst_pvar_at. simpl. apply Vrel_newpair.
  Qed.

  (** ** Creation in a strict world

      The semantic form of (acyc-new) in the world W, with the
      environment of C already instantiated. *)
  Definition acyc_new_sem (W : world) (C : bcs) : Prop :=
    (∀ x, in_tree0 x → ¬ tc (new_step C) x x) ∧
    (∀ z y, cbridge C z y → W ⊢ ctx_pt C z ≺ ctx_pt C y).

  Lemma acyc_new_sem_mono W W' C : W ⊑ W' → acyc_new_sem W C → acyc_new_sem W' C.
  Proof. intros HW [H1 H2]. split; [done|]. intros z y Hb. eapply w_lt_mono; [exact HW|]. by apply H2. Qed.

  (** Proposition A of docs/redesign/check-df-acyclic.md. The world of a
      creation at a fresh base a is the closure of the order of W1, of
      the facts of C at a and of program order ([aw_W]). A chain of the
      closure that leaves the tree of a and comes back passes through a
      bridge, which W1 orders already ([aw_bridge]). The invariant
      [aw_inv] records the shape of a chain by where its two ends lie,
      so the closure is irreflexive. Constructive: membership in the
      tree compares bases. *)
  Section acyc_world.
    Context (W1 : world) (C : bcs) (a : nat).
    Context (Ha1 : NConst a ∉ w_roots W1) (Ha2 : ∀ y, y ∈ bc_env C → pt_root y ≠ NConst a).
    Context (Hcyc : ∀ x, in_tree0 x → ¬ tc (new_step C) x x).
    Context (Hbr : ∀ z y, cbridge C z y → W1 ⊢ ctx_pt C z ≺ ctx_pt C y).
    Context (HS1 : wstrict W1).

    Definition aw_pt : point := MkPt (NConst a) true 0.
    Definition aw_σ : nat → point := plist (aw_pt :: bc_env C).
    Definition aw_in (p : point) : Prop := pt_root p = NConst a.
    Definition aw_env : gset pname := list_to_set (pt_root <$> bc_env C).

    Local Instance aw_in_dec p : Decision (aw_in p).
    Proof. unfold aw_in. apply _. Defined.

    Lemma aw_σ0 : aw_σ 0 = MkPt (NConst a) true 0.
    Proof. done. Qed.

    Lemma aw_in_po x y : po x y → aw_in x ↔ aw_in y.
    Proof. intros Hp. apply po_root in Hp as [Hr _]. unfold aw_in. by rewrite Hr. Qed.

    Lemma aw_tree p : in_tree0 p → aw_in (pt_inst aw_σ p) ∧ pt_unroot a (pt_inst aw_σ p) = p.
    Proof.
      intros Hp. split; [unfold aw_in; by rewrite pt_root_inst_var, Hp|].
      exact (pt_unroot_inst a aw_σ aw_σ0 p Hp).
    Qed.

    Lemma aw_out p : pn_vb (1 + length (bc_env C)) (pt_name p) → ¬ in_tree0 p →
      pt_inst aw_σ p = ctx_pt C p ∧ ¬ aw_in (pt_inst aw_σ p) ∧ pt_root (pt_inst aw_σ p) ∈ aw_env.
    Proof.
      intros Hsp Hp. apply pn_vb_root in Hsp as ([|j] & Hj & Hjl); [by destruct Hp|].
      simpl in Hjl. destruct (lookup_lt_is_Some_2 (bc_env C) j ltac:(lia)) as [yj Hyj].
      assert (pt_root (pt_inst aw_σ p) = pt_root yj) as Hr.
      { rewrite pt_root_inst_var. change (pt_root p) with (pn_root (pt_name p)). rewrite Hj.
        simpl. unfold aw_σ, plist. simpl. by rewrite Hyj. }
      split_and!.
      - unfold ctx_pt. apply pt_inst_ext_root. intros b Hb. change (pt_root p) with (pn_root (pt_name p)) in Hb.
        rewrite Hj in Hb. injection Hb as <-. done.
      - unfold aw_in. rewrite Hr. apply Ha2. by eapply list_elem_of_lookup_2.
      - rewrite Hr. unfold aw_env. apply elem_of_list_to_set, list_elem_of_fmap. exists yj.
        split; [done|]. by eapply list_elem_of_lookup_2.
    Qed.

    Definition aw_t (p q : point) : Prop := aw_in p ∧ aw_in q ∧ new_step C (pt_unroot a p) (pt_unroot a q).
    Definition aw_entry (z q : point) : Prop :=
      ∃ z0 v0, cfact C z0 v0 ∧ ¬ in_tree0 z0 ∧ in_tree0 v0 ∧ z = pt_inst aw_σ z0 ∧ q = pt_inst aw_σ v0.
    Definition aw_exit (p y : point) : Prop :=
      ∃ u0 y0, cfact C u0 y0 ∧ in_tree0 u0 ∧ ¬ in_tree0 y0 ∧ p = pt_inst aw_σ u0 ∧ y = pt_inst aw_σ y0.
    Definition aw_step (p q : point) : Prop :=
      (¬ aw_in p ∧ ¬ aw_in q ∧ W1 ⊢ p ≺ q) ∨ aw_entry p q ∨ aw_exit p q ∨ aw_t p q.

    Lemma aw_rtc_un p q : rtc aw_t p q → rtc (new_step C) (pt_unroot a p) (pt_unroot a q).
    Proof. induction 1 as [|p q r (_ & _ & H) _ IH]; [done|]. by eapply rtc_l. Qed.

    Lemma aw_tc_un p q : tc aw_t p q → tc (new_step C) (pt_unroot a p) (pt_unroot a q).
    Proof. induction 1 as [p q (_ & _ & H)|p q r (_ & _ & H) _ IH]; [by apply tc_once|]. by eapply tc_l. Qed.

    Lemma aw_bridge z v u y : aw_entry z v → rtc aw_t v u → aw_exit u y → W1 ⊢ z ≺ y.
    Proof.
      intros (z0 & v0 & Hzv & Hz0 & Hv0 & -> & ->) Hvu (u0 & y0 & Huy & Hu0 & Hy0 & -> & ->).
      pose proof Hzv as [_ [Hsz _]]. pose proof Huy as [_ [_ Hsy]].
      destruct (aw_out z0 Hsz Hz0) as (Ez & _ & _). destruct (aw_out y0 Hsy Hy0) as (Ey & _ & _).
      rewrite Ez, Ey. apply Hbr. split_and!; [done|done|right]. exists v0, u0. split_and!; [done|done| |done].
      apply aw_rtc_un in Hvu. by rewrite (proj2 (aw_tree v0 Hv0)), (proj2 (aw_tree u0 Hu0)) in Hvu.
    Qed.

    Lemma aw_le_lt x y z : w_le W1 x y → W1 ⊢ y ≺ z → W1 ⊢ x ≺ z.
    Proof. intros [->|H] H'; [done|by eapply w_lt_trans]. Qed.
    Lemma aw_lt_le x y z : W1 ⊢ x ≺ y → w_le W1 y z → W1 ⊢ x ≺ z.
    Proof. intros H [<-|H']; [done|by eapply w_lt_trans]. Qed.
    Lemma aw_le_trans x y z : w_le W1 x y → w_le W1 y z → w_le W1 x z.
    Proof. intros [->|H] H'; [done|right; by eapply aw_lt_le]. Qed.

    Definition aw_inv (p q : point) : Prop :=
      (¬ aw_in p → ¬ aw_in q → W1 ⊢ p ≺ q) ∧
      (¬ aw_in p → aw_in q → ∃ z v, w_le W1 p z ∧ aw_entry z v ∧ rtc aw_t v q) ∧
      (aw_in p → ¬ aw_in q → ∃ u y, rtc aw_t p u ∧ aw_exit u y ∧ w_le W1 y q) ∧
      (aw_in p → aw_in q → tc aw_t p q ∨
         ∃ u y z v, rtc aw_t p u ∧ aw_exit u y ∧ w_le W1 y z ∧ aw_entry z v ∧ rtc aw_t v q).

    Lemma aw_inv_trans p q r : aw_inv p q → aw_inv q r → aw_inv p r.
    Proof.
      intros (A1 & A2 & A3 & A4) (B1 & B2 & B3 & B4).
      destruct (decide (aw_in q)) as [Hq|Hq]; split_and!.
      - intros Hp Hr. destruct (A2 Hp Hq) as (z & v & Hpz & He & Hvq).
        destruct (B3 Hq Hr) as (u & y & Hqu & Hx & Hyr).
        pose proof (aw_bridge z v u y He (rtc_trans _ _ _ Hvq Hqu) Hx) as Hzy.
        exact (aw_le_lt _ _ _ Hpz (aw_lt_le _ _ _ Hzy Hyr)).
      - intros Hp Hr. destruct (A2 Hp Hq) as (z & v & Hpz & He & Hvq).
        destruct (B4 Hq Hr) as [Hqr|(u & y & z' & v' & Hqu & Hx & Hyz & He' & Hvr)].
        + exists z, v. split_and!; [done|done|]. eapply rtc_trans; [exact Hvq|by apply tc_rtc].
        + pose proof (aw_bridge z v u y He (rtc_trans _ _ _ Hvq Hqu) Hx) as Hzy.
          exists z', v'. split_and!; [|done|done]. right. exact (aw_le_lt _ _ _ Hpz (aw_lt_le _ _ _ Hzy Hyz)).
      - intros Hp Hr. destruct (B3 Hq Hr) as (u' & y' & Hqu' & Hx' & Hyr).
        destruct (A4 Hp Hq) as [Hpq|(u & y & z & v & Hpu & Hx & Hyz & He & Hvq)].
        + exists u', y'. split_and!; [|done|done]. eapply rtc_trans; [by apply tc_rtc|exact Hqu'].
        + pose proof (aw_bridge z v u' y' He (rtc_trans _ _ _ Hvq Hqu') Hx') as Hzy.
          exists u, y. split_and!; [done|done|]. right. exact (aw_le_lt _ _ _ Hyz (aw_lt_le _ _ _ Hzy Hyr)).
      - intros Hp Hr. destruct (A4 Hp Hq) as [Hpq|(u & y & z & v & Hpu & Hx & Hyz & He & Hvq)],
          (B4 Hq Hr) as [Hqr|(u' & y' & z' & v' & Hqu & Hx' & Hyz' & He' & Hvr)].
        + left. by eapply tc_transitive.
        + right. exists u', y', z', v'. split_and!; [|done|done|done|done].
          eapply rtc_trans; [by apply tc_rtc|exact Hqu].
        + right. exists u, y, z, v. split_and!; [done|done|done|done|].
          eapply rtc_trans; [exact Hvq|by apply tc_rtc].
        + pose proof (aw_bridge z v u' y' He (rtc_trans _ _ _ Hvq Hqu) Hx') as Hzy.
          right. exists u, y, z', v'. split_and!; [done|done| |done|done].
          right. exact (aw_le_lt _ _ _ Hyz (aw_lt_le _ _ _ Hzy Hyz')).
      - intros Hp Hr. eapply w_lt_trans; [by apply A1|by apply B1].
      - intros Hp Hr. destruct (B2 Hq Hr) as (z & v & Hqz & He & Hvr).
        exists z, v. split_and!; [|done|done]. right. exact (aw_lt_le _ _ _ (A1 Hp Hq) Hqz).
      - intros Hp Hr. destruct (A3 Hp Hq) as (u & y & Hpu & Hx & Hyq).
        exists u, y. split_and!; [done|done|]. right. exact (aw_le_lt _ _ _ Hyq (B1 Hq Hr)).
      - intros Hp Hr. destruct (A3 Hp Hq) as (u & y & Hpu & Hx & Hyq).
        destruct (B2 Hq Hr) as (z & v & Hqz & He & Hvr).
        right. exists u, y, z, v. split_and!; [done|done| |done|done]. exact (aw_le_trans _ _ _ Hyq Hqz).
    Qed.

    Lemma aw_entry_in z q : aw_entry z q → ¬ aw_in z ∧ aw_in q.
    Proof.
      intros (z0 & v0 & [_ [Hs _]] & Hz0 & Hv0 & -> & ->).
      split; [apply (aw_out z0 Hs Hz0)|apply (aw_tree v0 Hv0)].
    Qed.

    Lemma aw_exit_in p y : aw_exit p y → aw_in p ∧ ¬ aw_in y.
    Proof.
      intros (u0 & y0 & [_ [_ Hs]] & Hu0 & Hy0 & -> & ->).
      split; [apply (aw_tree u0 Hu0)|apply (aw_out y0 Hs Hy0)].
    Qed.

    Lemma aw_step_inv p q : aw_step p q → aw_inv p q.
    Proof.
      intros [(Hp & Hq & H)|[He|[Hx|Ht]]].
      - split_and!; intros; first [done|contradiction].
      - destruct (aw_entry_in p q He) as [Hp Hq]. split_and!; intros; try contradiction.
        exists p, q. split_and!; [by left|done|done].
      - destruct (aw_exit_in p q Hx) as [Hp Hq]. split_and!; intros; try contradiction.
        exists p, q. split_and!; [done|done|by left].
      - pose proof Ht as (Hp & Hq & _). split_and!; intros; try contradiction. left. by apply tc_once.
    Qed.

    Lemma aw_tc_inv p q : tc aw_step p q → aw_inv p q.
    Proof.
      induction 1 as [p q H|p q r H _ IH]; [by apply aw_step_inv|].
      eapply aw_inv_trans; [by apply aw_step_inv|exact IH].
    Qed.

    Lemma aw_inv_irrefl p : ¬ aw_inv p p.
    Proof.
      intros (A1 & _ & _ & A4). destruct (decide (aw_in p)) as [Hp|Hp].
      - destruct (A4 Hp Hp) as [Hc|(u & y & z & v & Hpu & Hx & Hyz & He & Hvp)].
        + apply aw_tc_un in Hc. exact (Hcyc _ (pt_root_unroot a p Hp) Hc).
        + pose proof (aw_bridge z v u y He (rtc_trans _ _ _ Hvp Hpu) Hx) as Hzy.
          exact (w_lt_irrefl W1 z (aw_lt_le _ _ _ Hzy Hyz)).
      - exact (w_lt_irrefl W1 p (A1 Hp Hp)).
    Qed.

    Lemma aw_po p q : aw_in p → po p q → tc aw_t p q.
    Proof.
      intros Hp H. induction H as [x y Hxy|x y z Hxy Hyz IH].
      - apply tc_once. assert (aw_in y) as Hy by (apply (aw_in_po x y); [by apply tc_once|done]).
        split_and!; [done|done|]. split_and!; [exact (pt_root_unroot a x Hp)|exact (pt_root_unroot a y Hy)|].
        right. destruct Hxy as [->| ->]; [left|right]; done.
      - assert (aw_in y) as Hy by (apply (aw_in_po x y); [by apply tc_once|done]).
        eapply tc_l; [|by apply IH].
        split_and!; [done|done|]. split_and!; [exact (pt_root_unroot a x Hp)|exact (pt_root_unroot a y Hy)|].
        right. destruct Hxy as [->| ->]; [left|right]; done.
    Qed.

    Lemma aw_tc_step p q : tc aw_t p q → tc aw_step p q.
    Proof.
      induction 1 as [p q H|p q r H _ IH]; [apply tc_once|eapply tc_l; [|exact IH]]; by do 3 right.
    Qed.

    Definition aw_W : world.
    Proof.
      refine (World ({[NConst a]} ∪ aw_env ∪ w_roots W1) (tc aw_step) _ _ _ None _).
      - intros x y z _ _ _. apply tc_transitive.
      - intros x _ Hx. exact (aw_inv_irrefl x (aw_tc_inv x x Hx)).
      - intros x y _ Hp. destruct (decide (aw_in x)) as [Hx|Hx].
        + by apply aw_tc_step, aw_po.
        + apply tc_once. left. split_and!; [done| |by apply po_lt].
          by rewrite <-(aw_in_po x y Hp).
      - intros ρ x y [=].
    Defined.

    Lemma aw_W_ext : W1 ⊑ aw_W.
    Proof.
      split.
      - simpl. set_solver.
      - intros x y Hx Hy H. apply tc_once. left.
        assert (∀ z, rin W1 z → ¬ aw_in z) as Hn by (intros z Hz Hza; apply Ha1; unfold rin, aw_in in *; congruence).
        split_and!; [by apply Hn|by apply Hn|]. right. by split_and!.
      - unfold wk_ext. by rewrite HS1.
    Qed.

    Lemma aw_W_holds : wholds aw_W C [aw_pt].
    Proof.
      intros x y Hf. pose proof Hf as Hf0.
      apply bcs_at_iff in Hf as ([x0 y0] & Hf & Hsc & Heq). simpl in Heq. injection Heq as -> ->.
      try change (plist ([aw_pt] ++ bc_env C)) with aw_σ in Hf0 |- *.
      try change (plist (aw_pt :: bc_env C)) with aw_σ in Hf0 |- *.
      assert (cfact C x0 y0) as Hcf by (split; [done|exact Hsc]).
      destruct Hsc as [Hsx Hsy].
      assert (∀ p, aw_in p → rin aw_W p) as Hrin by (intros p Hp; unfold rin, aw_in in *; simpl; rewrite Hp; set_solver).
      assert (∀ p, pt_root p ∈ aw_env → rin aw_W p) as Hrout by (intros p Hp; unfold rin; simpl; set_solver).
      destruct (decide (in_tree0 y0)) as [Hy0|Hy0], (decide (in_tree0 x0)) as [Hx0|Hx0].
      - destruct (aw_tree x0 Hx0) as [Hx Ex], (aw_tree y0 Hy0) as [Hy Ey].
        right. split_and!; [by apply Hrin|by apply Hrin|]. apply tc_once. do 3 right.
        split_and!; [done|done|]. rewrite Ex, Ey. split_and!; [done|done|left; exact Hcf].
      - destruct (aw_out x0 Hsx Hx0) as (_ & Hx & Hxr). destruct (aw_tree y0 Hy0) as [Hy _].
        right. split_and!; [by apply Hrout|by apply Hrin|]. apply tc_once. right; left.
        by exists x0, y0.
      - destruct (aw_tree x0 Hx0) as [Hx _]. destruct (aw_out y0 Hsy Hy0) as (_ & Hy & Hyr).
        right. split_and!; [by apply Hrin|by apply Hrout|]. apply tc_once. right; right; left.
        by exists x0, y0.
      - destruct (aw_out x0 Hsx Hx0) as (Ex & _ & _). destruct (aw_out y0 Hsy Hy0) as (Ey & _ & _).
        rewrite Ex, Ey. eapply w_lt_mono; [apply aw_W_ext|]. apply Hbr. split_and!; [done|done|by left].
    Qed.
    Lemma aw_exists : ∃ W', W1 ⊑ W' ∧ wholds W' C [aw_pt].
    Proof. exists aw_W. split; [apply aw_W_ext|apply aw_W_holds]. Qed.
  End acyc_world.

  (** A creation at a fresh base under (acyc-new), in a strict world,
      constructively. *)
  Lemma Erel_new_acyc aq1 aq2 n W C S F mt1 mt2 :
    wstrict W → acyc_new_sem W C →
    Erel κ n W ∅ (TEx LBot 1 C (TProd (TSess S (pvar 0) aq1 mt1) (TSess (dual S) (pvar 0)‾ aq2 mt2))) F ENew.
  Proof.
    intros HSt HA.
    assert (tstep ENew (LNew "") (Pair (Chan ""⁺) (Chan ""⁻))) as Hst
      by (by apply tstep_head, t_act_new).
    apply Erel_S_intro.
    - intros Hi. exact (Hi _ _ Hst).
    - intros W1 _. eapply ready_tau; [exact Hst|done].
    - intros W1 α e' HW1 Hs. destruct (ENew_step _ _ Hs) as (c & -> & ->). simpl. intros _.
      destruct (acyc_new_sem_mono _ _ _ HW1 HA) as (Hcyc & Hbr).
      pose proof (proj1 (wext_strict _ _ HW1) HSt) as HS1.
      destruct (fresh_const W1 (bc_env C)) as (a & Ha1 & Ha2).
      destruct (aw_exists W1 C a Ha1 Ha2 Hcyc Hbr HS1) as (W' & Hext & Hh).
      exists S, (aw_pt a), W'. split; [done|].
      apply at_cost_val. apply Vrel_ex_iff. split; [done|]. exists [aw_pt a]. split_and!; [done|done|].
      + unfold ty_inst. simpl. rewrite pt_inst_dual, !pt_inst_pvar_at. simpl. apply Vrel_newpair.
  Qed.

  (** ** Creation in either kind of world

      A strict world asks (acyc-new), a ranked world (gen-new), which
      implies (acyc-new) ([gen_new_acyc]). Excluded middle enters only
      at a ranked world. *)
  Definition new_sem (W : world) (C : bcs) : Prop :=
    acyc_new_sem W C ∧ (wranked W → gen_new_sem W C).

  Lemma new_sem_mono W W' C : W ⊑ W' → new_sem W C → new_sem W' C.
  Proof.
    intros HW [H1 H2]. split; [by eapply acyc_new_sem_mono|].
    intros Hr. eapply gen_new_sem_mono; [exact HW|]. apply H2. by apply (wext_ranked W W').
  Qed.

  Lemma Erel_new_any aq1 aq2 n W C S F mt1 mt2 :
    (wranked W → excluded_middle) → new_sem W C →
    Erel κ n W ∅ (TEx LBot 1 C (TProd (TSess S (pvar 0) aq1 mt1) (TSess (dual S) (pvar 0)‾ aq2 mt2))) F ENew.
  Proof.
    intros HEM [HA HG]. destruct (wkind_dec W) as [Hr|Hs].
    - apply Erel_new; [by apply HEM|done|by apply HG].
    - by apply Erel_new_acyc.
  Qed.

  (** ** Force *)

  Lemma Erel_force n W m kk C ub c U xs ss F v :
    length xs = m → length ss = kk → Forall contractive ss ∧ Forall sscoped ss → wholds W C xs →
    ub_lt W (pt_inst (plist xs) <$> ub) F →
    Vrel κ n W ∅ (TBox m kk C ub c U) v →
    Erel κ n W ∅ (sinst_ty (slist ss) (ty_inst xs U)) F (EForce v).
  Proof.
    intros Hxs Hss Hsc HC Hub (_ & e & -> & Hfe & H)%Vrel_box_iff.
    apply (Erel_fstep _ _ _ _ _ _ (subst1 (EBox e) e)).
    - intros α e'' Hs. apply op_head_only in Hs; [|done]. inversion Hs; by subst.
    - by apply tstep_head, t_act_force.
    - intros j Hj. apply (H W xs ss j F (wext_refl W) Hxs Hss Hsc HC Hj). by apply ub_ltu_of.
  Qed.
End redex.
