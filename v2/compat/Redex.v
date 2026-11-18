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

(** ** Exact ends and heads of values in V *)

Section values.
  Context (κ : ctable).

  Lemma Vrel_exact n W Θ T v : Vrel κ n W Θ T v → dom Θ = fends v.
  Proof.
    revert W Θ v. induction T as [T IH] using tsize_ind. intros W Θ v.
    destruct T as [|ub lb c t h T1 a1 U a2|T1 a1 U a2|T1 a1 U a2|m kk C ub c t U a|s x|lb m C T1 a].
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

  Lemma Vrel_heads n W Θ T v :
    Vrel κ n W Θ T v → hbot T = false →
    ∀ o S x, Θ !! o = Some (S, x) → ∃ h, h ∈ heads T ∧ w_le W h x‾.
  Proof.
    revert W Θ v. induction T as [T IH] using tsize_ind. intros W Θ v.
    destruct T as [|ub lb c t h T1 a1 U a2|T1 a1 U a2|T1 a1 U a2|m kk C ub c t U a|s x0|lb m C T1 a].
    - intros [-> ->]%Vrel_unit_iff _ o S x Hx. by rewrite lookup_empty in Hx.
    - intros (e & -> & _ & Hlb & _)%Vrel_lolli_iff _ o S x Hx.
      assert (x‾ ∈ senv_heads Θ) as Hh by (apply elem_of_senv_heads; eauto).
      destruct lb as [l|]; simpl in Hlb |- *.
      + exists l. split; [set_solver|by apply Hlb].
      + rewrite Hlb in Hh. set_solver.
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
       Eobl κ (S n) (Vrel κ) (Erel κ) (Vrel κ (S n)) (Erel κ (S n)) W1 Θ T F α e') →
    Erel κ (S n) W Θ T F e.
  Proof.
    intros Hni Hr Hs. apply Erel_S_iff. intros W1 HW1. split_and!.
    - intros Hi. by destruct Hni.
    - intros _. by apply Hr.
    - apply Esteps_iff. intros α e' Hst. by apply Hs.
  Qed.

  (** A value after a step of cost c. *)
  Lemma at_cost_val n c W Θ T F v :
    Vrel κ (S n) W Θ T v → at_cost_E (S n) c (Erel κ) (Erel κ (S n)) W Θ T F v.
  Proof.
    intros HV. split; intros _; apply Vrel_Erel; [done|]. eapply Vrel_down; [|exact HV]. lia.
  Qed.

  Lemma at_cost_payload n c W Θ T T' v :
    teq (ty_df T) (ty_df T') →
    Vrel κ (S n) W Θ T v → at_cost_V (S n) c (Vrel κ) (Vrel κ (S n)) W Θ T' v.
  Proof.
    intros Heq HV. apply (Vrel_teq κ _ _ _ _ _ _ Heq) in HV.
    split; intros _; [done|]. eapply Vrel_down; [|exact HV]. lia.
  Qed.

  (** ** β redexes *)

  Lemma Erel_beta n W Θ T F e e' :
    (∀ α e'', tstep e α e'' → α = LBeta ∧ e'' = e') → tstep e LBeta e' →
    Erel κ (n - c_beta κ) W Θ T F e' → Erel κ n W Θ T F e.
  Proof.
    intros Hdet Hst HE. destruct n as [|n]; [apply Erel_0|].
    apply Erel_S_intro.
    - intros Hi. exact (Hi _ _ Hst).
    - intros W1 _. eapply ready_tau; [exact Hst|done].
    - intros W1 α e'' HW1 Hs. destruct (Hdet _ _ Hs) as [-> ->]. simpl.
      split; intros Hc.
      + rewrite Hc, Nat.sub_0_r in HE. by eapply Erel_mono.
      + by eapply Erel_mono.
  Qed.

  Lemma Erel_app n W Θ1 Θ2 ub lb c t h T1 a1 U a2 F f w :
    Θ1 ##ₘ Θ2 → ub_lt W ub F →
    Vrel κ n W Θ1 (TLolli ub lb c t h T1 a1 U a2) f → Vrel κ n W Θ2 T1 w →
    Erel κ n W (Θ1 ∪ Θ2) U F (App f w).
  Proof.
    intros Hd Hub (e & -> & _ & _ & H)%Vrel_lolli_iff Hw.
    pose proof (Vrel_val κ _ _ _ _ _ Hw) as Hwv.
    apply (Erel_beta _ _ _ _ _ _ (subst1 w e)).
    - intros α e'' Hs. assert (head_step (App (Lam e) w) α e'') as Hh by head_only.
      inversion Hh; by subst.
    - by apply tstep_head, t_act_app.
    - destruct (decide (n ≤ c_beta κ)) as [Hle|Hlt].
      + replace (n - c_beta κ) with 0 by lia. apply Erel_0.
      + apply H; [apply wext_refl|lia|done|done|]. eapply Vrel_down; [|exact Hw]. lia.
  Qed.

  (** ** Session operators *)

  Lemma Erel_send n W Θ m U b S0 S x ap aS F v :
    unfoldS S0 = SSeq (SSnd m U b) S → hbot (payload_at m U x) = false →
    (∀ y, y ∈ heads (payload_at m U x) → W ⊢ x ≺ y) → (∀ y, y ∈ F → W ⊢ x ≺ y) →
    Vrel κ n W Θ (TProd (payload_at m U x) ap (TSess S0 x) aS) v →
    Erel κ n W Θ (TSess S x⁺) F (ESend v).
  Proof.
    intros Hu Hb Hh HF HV. destruct n as [|n]; [apply Erel_0|].
    apply Vrel_prod_iff in HV as (w & vo & Θw & Θo & -> & Hd & -> & Hw & Ho).
    apply Vrel_sess_iff in Ho as (o & s' & -> & -> & Hs').
    destruct (seqv_unfold_snd _ _ _ _ _ _ Hs' Hu) as (U' & b' & S' & Hu' & HU & HS).
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
      exists s', x, m, U', b', S', Θw, ∅. split_and!.
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

  Lemma Erel_recv n W Θ m U b S0 S x b' a' F v :
    unfoldS S0 = SSeq (SRcv m U b) S → (∀ y, y ∈ F → W ⊢ x ≺ y) →
    Vrel κ n W Θ (TSess S0 x) v →
    Erel κ n W Θ (TProd (payload_at m U x) b' (TSess S x⁺) a') F (ERecv v).
  Proof.
    intros Hu HF HV. destruct n as [|n]; [apply Erel_0|].
    apply Vrel_sess_iff in HV as (o & s' & -> & -> & Hs').
    destruct (seqv_unfold_rcv _ _ _ _ _ _ Hs' Hu) as (U' & b'' & S' & Hu' & HU & HS).
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
      exists s', x, m, U', b'', S'. split_and!; [apply lookup_singleton_eq|done|].
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

  Lemma Erel_close n W Θ S0 x F v :
    unfoldS S0 = SEnd → (∀ y, y ∈ F → W ⊢ x ≺ y) →
    Vrel κ n W Θ (TSess S0 x) v → Erel κ n W Θ TUnit F (EClose v).
  Proof.
    intros Hu HF HV. destruct n as [|n]; [apply Erel_0|].
    apply Vrel_sess_iff in HV as (o & s' & -> & -> & Hs').
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

  Lemma Erel_select (i : bool) n W Θ S0 x S1 S2 F v :
    unfoldS S0 = SPlus S1 S2 → (∀ y, y ∈ F → W ⊢ x ≺ y) →
    Vrel κ n W Θ (TSess S0 x) v →
    Erel κ n W Θ (TSess (if i then S2 else S1) (sel_pt x i)) F (ESel i v).
  Proof.
    intros Hu HF HV. destruct n as [|n]; [apply Erel_0|].
    apply Vrel_sess_iff in HV as (o & s' & -> & -> & Hs').
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

  Lemma Erel_branch n W Θ S0 x S1 S2 a1 a2 F v :
    unfoldS S0 = SWith S1 S2 → (∀ y, y ∈ F → W ⊢ x ≺ y) →
    Vrel κ n W Θ (TSess S0 x) v →
    Erel κ n W Θ (TSum (TSess S1 (bra_pt x false)) a1 (TSess S2 (bra_pt x true)) a2) F (EBra v).
  Proof.
    intros Hu HF HV. destruct n as [|n]; [apply Erel_0|].
    apply Vrel_sess_iff in HV as (o & s' & -> & -> & Hs').
    destruct (seqv_unfold_with _ _ _ _ Hs' Hu) as (S1' & S2' & Hu' & H1 & H2).
    assert (tstep (EBra (Chan o)) (LSess (SBra o false)) (inj_of false (Chan o))) as Hst
      by (by apply tstep_head, t_act_branch).
    assert (∀ α e', tstep (EBra (Chan o)) α e' →
              ∃ i, α = LSess (SBra o i) ∧ e' = inj_of i (Chan o)) as Hdet.
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

  Lemma Erel_link n W Θ S x a1 a2 F v :
    Vrel κ n W Θ (TProd (TSess S x) a1 (TSess (dual S) x‾) a2) v → Erel κ n W Θ TUnit F (ELink v).
  Proof.
    intros HV. destruct n as [|n]; [apply Erel_0|].
    apply Vrel_prod_iff in HV as (v1 & v2 & Θ1 & Θ2 & -> & Hd & -> & H1 & H2).
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

  Lemma Vthunk_of_Vrel n W Θ ub lb c t h a1 aU v :
    Vrel κ n W Θ (TLolli ub lb c t h TUnit a1 TUnit aU) v →
    Vthunk κ n (Vrel κ) (Erel κ) (λ _ Θ' w, Θ' = ∅ ∧ w = EUnit)
      (λ W' Θ' F e, Erel κ n W' Θ' TUnit F e) W Θ v.
  Proof.
    intros HV. apply (Vrel_thunk κ _ _ _ ub lb).
    eapply (Vrel_blind κ); [|exact HV]. done.
  Qed.
  Lemma Erel_spawn n W Θ ub lb c t h a1 aU F v :
    Vrel κ n W Θ (TLolli ub lb c t h TUnit a1 TUnit aU) v → Erel κ n W Θ TUnit F (ESpawn v).
  Proof.
    intros HV. destruct n as [|n]; [apply Erel_0|].
    pose proof (Vrel_val κ _ _ _ _ _ HV) as Hv.
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
      + eapply Vthunk_of_Vrel, Vrel_mono; [exact HW1|exact HV].
      + apply at_cost_val. by apply Vrel_unit_iff.
  Qed.

  (** ** Creation *)

  Lemma Erel_new_at (κf : field) n W Θ S0 x S a a1 a2 a3 F v :
    Vrel κ n W Θ (TSess S0 x) v →
    Erel κ n W Θ (TProd (TSess S0 x) a (TProd (TSess S (x·κf)) a1 (TSess (dual S) (x·κf)‾) a2) a3) F
      (ENewAt κf v).
  Proof.
    intros HV. destruct n as [|n]; [apply Erel_0|].
    apply Vrel_sess_iff in HV as (o & s' & -> & -> & Hs').
    assert (tstep (ENewAt κf (Chan o)) (LNewAt κf o "") (Pair (Chan o) (Pair (Chan ""⁺) (Chan ""⁻))))
      as Hst by (by apply tstep_head, t_act_new_at).
    assert (∀ α e', tstep (ENewAt κf (Chan o)) α e' →
              ∃ c, α = LNewAt κf o c ∧ e' = Pair (Chan o) (Pair (Chan c⁺) (Chan c⁻))) as Hdet.
    { intros α e' Hs. apply op_head_only in Hs; [|done]. inversion Hs; subst; eauto. }
    apply Erel_S_intro.
    - intros Hi. exact (Hi _ _ Hst).
    - intros W1 _. eapply ready_tau; [exact Hst|done].
    - intros W1 α e' HW1 Hs. destruct (Hdet _ _ Hs) as (c & -> & ->). simpl.
      intros [Hc1 Hc2]. rewrite dom_singleton_L in Hc1, Hc2.
      exists s', x. split; [apply lookup_singleton_eq|]. exists S. apply at_cost_val.
      assert (o ≠ EPos c ∧ o ≠ ENeg c) as [Ho1 Ho2] by set_solver.
      assert (new_env c S (x·κf) {[o := (s', x)]} = {[o := (s', x)]} ∪ new_env c S (x·κf) ∅) as ->.
      { unfold new_env. rewrite <-(map_union_empty {[o := (s', x)]}) at 1.
        rewrite !insert_union_r; [done| |]; apply lookup_singleton_ne; congruence. }
      unfold new_env. rewrite insert_empty, insert_union_singleton_l.
      apply Vrel_prod_iff. eexists _, _, _, _. split_and!; [done| |done| |].
      + apply map_disjoint_union_r. split; apply map_disjoint_singleton_l, lookup_singleton_ne; congruence.
      + apply Vrel_sess_iff. eexists _, _. done.
      + apply Vrel_prod_iff. eexists _, _, _, _. split_and!; [done| |done| |].
        * apply map_disjoint_singleton_l, lookup_singleton_ne; done.
        * apply Vrel_sess_iff. eexists _, _. split_and!; [done|done|apply seqv_refl].
        * apply Vrel_sess_iff. eexists _, _. split_and!; [done|done|apply seqv_refl].
  Qed.

  (** The constraint may name the laws of ℓ in a smaller world. *)
  Lemma Erel_new_sub (ℓ : family) n W P S a1 a2 a3 F :
    ℓ ∈ w_fams W → (∀ f, P f → w_laws W ℓ f) →
    Erel κ n W ∅
      (TEx LBot 1 (bcs_of P) (TProd (TSess S (pvar 0)) a1 (TSess (dual S) (pvar 0)‾) a2) a3)
      F (ENew ℓ).
  Proof.
    intros Hℓ HP. destruct n as [|n]; [apply Erel_0|].
    assert (tstep (ENew ℓ) (LNew ℓ "") (Pair (Chan ""⁺) (Chan ""⁻))) as Hst
      by (by apply tstep_head, t_act_new).
    assert (∀ α e', tstep (ENew ℓ) α e' → ∃ c, α = LNew ℓ c ∧ e' = Pair (Chan c⁺) (Chan c⁻)) as Hdet.
    { intros α e' Hs. apply tstep_head_only in Hs; [|by intros []]. inversion Hs; subst; eauto. }
    apply Erel_S_intro.
    - intros Hi. exact (Hi _ _ Hst).
    - intros W1 _. eapply ready_tau; [exact Hst|done].
    - intros W1 α e' HW1 Hs. destruct (Hdet _ _ Hs) as (c & -> & ->). simpl.
      intros _ g _. exists S. apply at_cost_val. apply Vrel_ex_iff. split; [done|].
      exists [pgen ℓ g]. split_and!; [done| |].
      + intros y z (g0 & (f & Hf & Hsc & ->) & Heq). simpl in Hf, Hsc.
        destruct f as [a b0]. simpl in Heq, Hsc. injection Heq as -> ->.
        assert (∀ p, pn_vb 1 (pt_name p) →
                  pt_inst (plist [pgen ℓ g]) (pt_inst (pup 1 (plist [])) p) = law_inst ℓ g p) as Hl.
        { intros p Hp. rewrite pt_inst_comp. unfold law_inst. apply pt_inst_ext_root.
          intros a0 Ha0. apply pn_vb_root in Hp as (a1' & Ha1 & Hlt). unfold pt_root in Ha0.
          rewrite Ha0 in Ha1. injection Ha1 as <-. assert (a0 = 0) as -> by lia.
          simpl. unfold pup. rewrite decide_True by lia. by rewrite pt_inst_pvar_at. }
        rewrite !Hl by tauto. eapply w_lt_mono; [exact HW1|]. apply w_lt_law; [done|by apply HP].
      + unfold ty_inst. simpl. rewrite pt_inst_dual, !pt_inst_pvar_at. simpl.
        unfold new_env. rewrite insert_empty, insert_union_singleton_l.
        apply Vrel_prod_iff. eexists _, _, _, _. split_and!; [done| |done| |].
        * apply map_disjoint_singleton_l, lookup_singleton_ne; done.
        * apply Vrel_sess_iff. eexists _, _. split_and!; [done|done|apply seqv_refl].
        * apply Vrel_sess_iff. eexists _, _. split_and!; [done|done|apply seqv_refl].
  Qed.

  Lemma Erel_new (ℓ : family) n W S a1 a2 a3 F :
    ℓ ∈ w_fams W →
    Erel κ n W ∅
      (TEx LBot 1 (bcs_of (w_laws W ℓ)) (TProd (TSess S (pvar 0)) a1 (TSess (dual S) (pvar 0)‾) a2) a3)
      F (ENew ℓ).
  Proof. intros Hℓ. by apply Erel_new_sub. Qed.

  (** ** Force *)

  Lemma Erel_force n W m kk C ub c t U a xs ss F v :
    length xs = m → length ss = kk → Forall hcontractive ss → wholds W C xs →
    ub_lt W (pt_inst (plist xs) <$> ub) F →
    Vrel κ n W ∅ (TBox m kk C ub c t U a) v →
    Erel κ n W ∅ (sinst_ty (slist ss) (ty_inst xs U)) F (EForce v).
  Proof.
    intros Hxs Hss Hsc HC Hub (_ & e & -> & Hfe & H)%Vrel_box_iff.
    specialize (H W xs ss (wext_refl W) Hxs Hss Hsc HC).
    apply (Erel_beta _ _ _ _ _ _ (subst1 (EBox e) e)).
    - intros α e'' Hs. apply op_head_only in Hs; [|done]. inversion Hs; by subst.
    - by apply tstep_head, t_act_force.
    - apply Vrel_lolli_iff in H as (e0 & He0 & _ & _ & H). injection He0 as <-.
      destruct (decide (n ≤ c_beta κ)) as [Hle|Hlt].
      + replace (n - c_beta κ) with 0 by lia. apply Erel_0.
      + rewrite <-(thunk_app EUnit), <-(map_union_empty ∅).
        apply H; [apply wext_refl|lia|apply map_disjoint_empty_l|done|]. by apply Vrel_unit_iff.
  Qed.
End redex.
