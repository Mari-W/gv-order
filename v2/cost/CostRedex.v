(** * Redexes of the cost judgment (stage S7)

    FuelE of each redex the rules build: the application of a closure,
    and the operators send, receive, close, select, branch, link, spawn,
    force, new_κ and new_ℓ, each at a value of [Vfuel]. An action
    returns its end at credit equal to its tickets, a creation starts its
    two ends at their tickets. *)

From GV Require Export cost.CostBind types.Erasure types.Duality.

(** ** Maps *)

Lemma mres_self {Y : Type} (m : gmap cend Y) : mres (dom m) m = m.
Proof.
  apply map_eq. intros o. rewrite lookup_mres. case_decide as H; [done|].
  symmetry. by apply not_elem_of_dom.
Qed.

Lemma mrem_self {Y : Type} (m : gmap cend Y) : mrem (dom m) m = ∅.
Proof.
  apply map_eq. intros o. rewrite lookup_mrem, lookup_empty. case_decide as H; [done|].
  by apply not_elem_of_dom.
Qed.

Lemma mres_union_self {Y : Type} (m1 m2 : gmap cend Y) : m1 ##ₘ m2 → mres (dom m1) (m1 ∪ m2) = m1.
Proof. intros Hd. rewrite mres_union_l; [apply mres_self|by apply map_disjoint_dom]. Qed.

Lemma mrem_union_self {Y : Type} (m1 m2 : gmap cend Y) : m1 ##ₘ m2 → mrem (dom m1) (m1 ∪ m2) = m2.
Proof. intros Hd. rewrite mrem_union_l; [by rewrite mrem_self, map_empty_union|by apply map_disjoint_dom]. Qed.

Lemma fmap_empty_c (h : fuel * fuel → fuel * fuel) : h <$> (∅ : cenv) = ∅.
Proof. apply fmap_empty. Qed.

Lemma ftick_fminus (φ : cenv) : ctick <$> φ = fminus (Some 1) <$> φ.
Proof. done. Qed.

Lemma refill_single o f m : refill o {[o := (f, m)]} = {[o := (m, m)]}.
Proof.
  unfold refill. rewrite lookup_singleton_eq, delete_singleton_eq, fmap_empty_c.
  by rewrite insert_empty.
Qed.

(** ** Sessions up to ≈ *)

Local Ltac hd_inv Hq Hu :=
  apply sequiv_step in Hq; unfold eq_step in Hq; rewrite (hd_of _ _ Hu) in Hq; simpl in Hq.

Lemma sequiv_unfold_snd s S0 m T S :
  sequiv s S0 → unfoldS S0 = SSeq (SSnd m T) S →
  ∃ T' S', unfoldS s = SSeq (SSnd m T') S' ∧ teq T' T ∧ sequiv S' S.
Proof.
  intros Hq Hu. hd_inv Hq Hu.
  destruct (hd s) eqn:Hs; simpl in Hq; try done. destruct_and!; subst.
  eexists _, _. split_and!; [|done|done]. by rewrite unfoldS_unview, Hs.
Qed.

Lemma sequiv_unfold_rcv s S0 m T S :
  sequiv s S0 → unfoldS S0 = SSeq (SRcv m T) S →
  ∃ T' S', unfoldS s = SSeq (SRcv m T') S' ∧ teq T' T ∧ sequiv S' S.
Proof.
  intros Hq Hu. hd_inv Hq Hu.
  destruct (hd s) eqn:Hs; simpl in Hq; try done. destruct_and!; subst.
  eexists _, _. split_and!; [|done|done]. by rewrite unfoldS_unview, Hs.
Qed.

Lemma sequiv_unfold_end s S0 : sequiv s S0 → unfoldS S0 = SEnd → unfoldS s = SEnd.
Proof.
  intros Hq Hu. hd_inv Hq Hu.
  destruct (hd s) eqn:Hs; simpl in Hq; try done. by rewrite unfoldS_unview, Hs.
Qed.

Lemma sequiv_unfold_plus s S0 S1 S2 :
  sequiv s S0 → unfoldS S0 = SPlus S1 S2 →
  ∃ S1' S2', unfoldS s = SPlus S1' S2' ∧ sequiv S1' S1 ∧ sequiv S2' S2.
Proof.
  intros Hq Hu. hd_inv Hq Hu.
  destruct (hd s) eqn:Hs; simpl in Hq; try done. destruct_and!.
  eexists _, _. split_and!; [|done|done]. by rewrite unfoldS_unview, Hs.
Qed.

Lemma sequiv_unfold_with s S0 S1 S2 :
  sequiv s S0 → unfoldS S0 = SWith S1 S2 →
  ∃ S1' S2', unfoldS s = SWith S1' S2' ∧ sequiv S1' S1 ∧ sequiv S2' S2.
Proof.
  intros Hq Hu. hd_inv Hq Hu.
  destruct (hd s) eqn:Hs; simpl in Hq; try done. destruct_and!.
  eexists _, _. split_and!; [|done|done]. by rewrite unfoldS_unview, Hs.
Qed.

Lemma not_idle_single o s : unfoldS s ≠ SSkip → ¬ idle_at {[o := s]} o.
Proof. intros Hs (S' & HS & Hi). rewrite lookup_singleton_eq in HS. injection HS as <-. done. Qed.

(** ** Values *)

Lemma Vfuel_sess_inv N n s x a Π φ v mt :
  v ∈ FV^N _ n⟦RTy (TSess s x a mt)⟧(Π, φ) →
  ∃ o s' f, v = Chan o ∧ Π = {[o := s']} ∧ φ = {[o := (f, mt)]} ∧ sequiv s' s ∧ fle a f.
Proof. rewrite Vfuel_eq. simpl. done. Qed.

Lemma Vfuel_sess_intro N n s x a o s' f mt :
  sequiv s' s → fle a f → Chan o ∈ FV^N _ n⟦RTy (TSess s x a mt)⟧({[o := s']}, {[o := (f, mt)]}).
Proof. intros Hs Hf. rewrite Vfuel_eq. simpl. exists o, s', f. by split_and!. Qed.

Lemma Vfuel_prod_inv N n T1 T2 Π φ v :
  v ∈ FV^N _ n⟦RTy (TProd T1 T2)⟧(Π, φ) →
  ∃ v1 v2 Π1 Π2 φ1 φ2, v = Pair v1 v2 ∧ Π1 ##ₘ Π2 ∧ φ1 ##ₘ φ2 ∧ Π = Π1 ∪ Π2 ∧ φ = φ1 ∪ φ2 ∧
    v1 ∈ FV^N _ n⟦RTy T1⟧(Π1, φ1) ∧ v2 ∈ FV^N _ n⟦RTy T2⟧(Π2, φ2).
Proof. rewrite Vfuel_eq. simpl. setoid_rewrite Vfuel_eq. simpl. done. Qed.

Lemma Vfuel_sum_inv N n T1 T2 Π φ v :
  v ∈ FV^N _ n⟦RTy (TSum T1 T2)⟧(Π, φ) →
  (∃ v', v = Inj false v' ∧ v' ∈ FV^N _ n⟦RTy T1⟧(Π, φ)) ∨
  (∃ v', v = Inj true v' ∧ v' ∈ FV^N _ n⟦RTy T2⟧(Π, φ)).
Proof. rewrite Vfuel_eq. simpl. setoid_rewrite Vfuel_eq. simpl. done. Qed.

Lemma Vfuel_unit_inv N n Π φ v : v ∈ FV^N _ n⟦RTy TUnit⟧(Π, φ) → v = EUnit ∧ Π = ∅ ∧ φ = ∅.
Proof. rewrite Vfuel_eq. simpl. done. Qed.

Lemma Vfuel_lolli_inv N n ub lb c T U a Π φ v :
  v ∈ FV^N _ n⟦RTy (TLolli ub lb c T U a)⟧(Π, φ) →
  ∃ e, v = Lam e ∧ fends e = dom Π ∧ dom Π = dom φ ∧
    (∀ o f, φ !! o = Some f → ¬ idle_at Π o → fle a f.1) ∧
    ∀ j φ' Πu φu u, olt j n → dom φ' = dom φ →
      (∀ o f f', φ !! o = Some f → φ' !! o = Some f' → f'.2 = f.2 ∧ fle (fsub f.1 a) f'.1) →
      Π ##ₘ Πu → φ' ##ₘ φu →
      u ∈ FV^N _ j⟦RTy T⟧(Πu, φu) →
      subst1 u e ∈ F^N _ j⟦RTy U ▷ c⟧(Π ∪ Πu, φ' ∪ φu).
Proof. rewrite Vfuel_eq. simpl. done. Qed.

Lemma Vfuel_box_inv N n m k C ub c U Π φ v :
  v ∈ FV^N _ n⟦RTy (TBox m k C ub c U)⟧(Π, φ) →
  ∃ e, v = EBox e ∧ fends e = ∅ ∧ Π = ∅ ∧ φ = ∅ ∧
    ∀ j ss, olt j n → length ss = k → sinsts N ss →
      subst1 (EBox e) e ∈ F^N _ j⟦RTy (sinst_ty (slist ss) U) ▷ c⟧(∅, ∅).
Proof. rewrite Vfuel_eq. simpl. done. Qed.

(** ** Unfolding at an operator *)

Lemma FuelE_op k N n σ d Π φ v T :
  v ∈ FV^N _ n⟦RTy T⟧(Π, φ) →
  (∀ v' Π' φ', v' ∈ FV^N _ n⟦RTy T⟧(Π', φ') → is_val v' →
     ∀ α e', tstep (Op k v') α e' → Fobl N (λ j N, FuelE N j) (λ j N, Vfuel N j) n σ d Π' φ' α e') →
  Op k v ∈ F^N _ n⟦σ ▷ d⟧(Π, φ).
Proof.
  intros HV H. apply FuelE_eq. intros g Π' φ' Hk1 Hk2 R1 R2. split.
  - intros Hv. done.
  - intros α e' Hst. apply (H (emap g v) Π' φ'); [| |exact Hst].
    + by eapply Vfuel_rename.
    + rewrite is_val_emap. by eapply Vfuel_val.
Qed.

Lemma op_head_only' k v α e' : is_val v → tstep (Op k v) α e' → head_step (Op k v) α e'.
Proof.
  intros Hv Hst. apply tstep_inv in Hst as [Hh|(f & e0 & e0' & Hf & Heq & -> & Hs)]; [done|].
  exfalso. destruct f; simpl in Heq; try discriminate. injection Heq as <- <-.
  exact (val_no_tstep _ _ _ Hs Hv).
Qed.

Local Ltac op_step Hst := apply op_head_only' in Hst; [|simpl; rewrite ?andb_True; eauto using Vfuel_val].

(** ** Application *)

Lemma app_redex N n ub lb c T U a1 Π1 φ1 Π2 φ2 d v1 v2 :
  v1 ∈ FV^N _ n⟦RTy (TLolli ub lb c T U a1)⟧(Π1, φ1) → v2 ∈ FV^N _ n⟦RTy T⟧(Π2, φ2) →
  Π1 ##ₘ Π2 → φ1 ##ₘ φ2 → fle c d →
  App v1 v2 ∈ F^N _ n⟦RTy U ▷ d⟧(Π1 ∪ Π2, φ1 ∪ φ2).
Proof.
  intros HV1 HV2 HdΠ Hdφ Hcd.
  destruct (Vfuel_lolli_inv _ _ _ _ _ _ _ _ _ _ _ HV1) as (e & -> & _ & _ & Hfl & HF).
  apply (FuelE_beta _ _ _ _ _ _ [] _ (subst1 v2 e)); [constructor|by apply t_act_app; eapply Vfuel_val|].
  intros j Hj. simpl. eapply FuelE_frame_mono; [exact Hcd|].
  apply (HF j φ1 Π2 φ2 v2 Hj eq_refl); [|done|done|].
  - intros o f f' Ho Ho'. rewrite Ho in Ho'. injection Ho' as <-. split; [done|apply fsub_le].
  - eapply Vfuel_down; [|exact HV2]. by apply olt_ole.
Qed.

(** ** Session operators *)

Lemma send_redex N n m T S0 S x aS mS Tp Tp' Π φ d v :
  unfoldS S0 = SSeq (SSnd m T) S →
  tage (Some 1) Tp Tp' → tsub Tp' (payload_at m T x) →
  fle (Some 1) d →
  v ∈ FV^N _ n⟦RTy (TProd Tp (TSess S0 x aS mS))⟧(Π, φ) →
  ESend v ∈ F^N _ n⟦RTy (TSess S x⁺ mS mS) ▷ d⟧(Π, φ).
Proof.
  intros Hu Ha Hs Hd HV.
  eapply FuelE_op; [exact HV|]. intros v' Π' φ' HV' Hv' α e' Hst.
  destruct (Vfuel_prod_inv _ _ _ _ _ _ _ HV') as (w & c & Π1 & Π2 & φ1 & φ2 & -> & HdΠ & Hdφ & -> & -> & Hw & Hc).
  destruct (Vfuel_sess_inv _ _ _ _ _ _ _ _ _ Hc) as (o & s' & f & -> & -> & -> & Hq & Hf).
  destruct (sequiv_unfold_snd _ _ _ _ _ Hq Hu) as (T' & S' & Hu' & HT & HS).
  op_step Hst. inversion Hst; subst. cbn [Fobl]. unfold f_send, f_act.
  assert (o ∉ dom φ1) as Ho1 by (apply map_disjoint_dom in Hdφ; rewrite dom_singleton_L in Hdφ; set_solver).
  assert (dom Π1 = dom φ1) as HdΠφ by (by eapply Vfuel_dom).
  assert (fends w = dom φ1) as Hfw by (rewrite (Vfuel_exact _ _ _ _ _ _ Hw); done).
  assert ((Π1 ∪ {[o := s']}) !! o = Some s') as HΠo.
  { apply lookup_union_Some_raw. right. split; [apply not_elem_of_dom; by rewrite HdΠφ|apply lookup_singleton_eq]. }
  assert (∀ o' f', o' ∈ dom (φ1 ∪ {[o := (f, mS)]}) ∖ {[o]} → (φ1 ∪ {[o := (f, mS)]}) !! o' = Some f' →
            ¬ idle_at (Π1 ∪ {[o := s']}) o' → fle (Some 1) f'.1) as Hsp.
  { intros o' f' Ho' Hf' Hn. rewrite dom_union_L, dom_singleton_L in Ho'.
    apply lookup_union_Some_raw in Hf' as [Hf'|[_ Hf']]; [|apply lookup_singleton_Some in Hf'; set_solver].
    apply (Vfuel_age_above _ _ _ _ _ _ _ _ Ha Hw o' f' Hf').
    intros (Sq & HSq & Hiq). apply Hn. exists Sq. split; [by apply lookup_union_Some_l|done]. }
  split.
  { split_and!; [|rewrite dom_union_L, dom_singleton_L; set_solver|intros o' f' Ho' Hf' Hn; exact (Hsp o' f' Ho' Hf' Hn)|done].
    intros (S2 & HS2 & Hi). rewrite HΠo in HS2. injection HS2 as <-. unfold idle in Hi. congruence. }
  exists s', m, T', S'. split_and!.
  - done.
  - done.
  - rewrite Hfw, dom_union_L, dom_singleton_L. set_solver.
  - intros o' f' Ho' Hf' Hn. apply (Hsp o' f'); [|done|done]. rewrite Hfw in Ho'. rewrite dom_union_L, dom_singleton_L. set_solver.
  - rewrite Hfw, <-HdΠφ, mres_union_self by done. unfold fhand. rewrite HdΠφ, mres_union_self by done.
    rewrite ftick_fminus.
    pose proof (Vfuel_age _ _ _ _ _ _ _ _ Ha Hw) as H1.
    pose proof (Vfuel_sub _ _ _ _ _ _ _ Hs H1) as H2.
    unfold payload_at, ty_inst in H2. apply Vfuel_pinst in H2.
    intros j Hj. apply (Vfuel_down _ _ n); [by apply olt_ole|].
    exact (proj1 (Vfuel_teq _ _ T T' _ _ _ (teq_sym _ _ HT)) H2).
  - rewrite Hfw, <-HdΠφ, mrem_union_self by done. rewrite HdΠφ, mrem_union_self by done.
    rewrite refill_single, insert_singleton, decide_True by done.
    intros j Hj. apply FuelE_val; [done|]. apply Vfuel_sess_intro; [done|apply fle_refl].
Qed.

Lemma recv_redex N n m T S0 S x a mS Π φ d v :
  unfoldS S0 = SSeq (SRcv m T) S → fle (Some 1) d →
  v ∈ FV^N _ n⟦RTy (TSess S0 x a mS)⟧(Π, φ) →
  ERecv v ∈ F^N _ n⟦RTy (TProd (payload_at m T x) (TSess S x⁺ mS mS)) ▷ d⟧(Π, φ).
Proof.
  intros Hu Hd HV.
  eapply FuelE_op; [exact HV|]. intros v' Π' φ' HV' Hv' α e' Hst.
  destruct (Vfuel_sess_inv _ _ _ _ _ _ _ _ _ HV') as (o & s' & f & -> & -> & -> & Hq & Hf).
  destruct (sequiv_unfold_rcv _ _ _ _ _ Hq Hu) as (T' & S' & Hu' & HT & HS).
  op_step Hst. inversion Hst; subst. cbn [Fobl]. unfold f_recv, f_act. split.
  { split_and!; [apply not_idle_single; congruence|rewrite dom_singleton_L; set_solver| |done].
    intros o' f' Ho'. rewrite dom_singleton_L in Ho'. set_solver. }
  exists s', m, T', S'. split_and!; [by rewrite lookup_singleton_eq|done|].
  intros j Πi φi Hj HdΠ Hdφ Hw. rewrite refill_single in *. rewrite insert_singleton, decide_True in * by done.
  apply FuelE_val; [simpl; rewrite andb_True; split; [by eapply Vfuel_val|done]|].
  rewrite (map_union_comm {[o := S']}), (map_union_comm {[o := (mS, mS)]}) by (by apply map_disjoint_sym).
  apply Vfuel_pair; [by apply map_disjoint_sym|by apply map_disjoint_sym| |].
  - unfold payload_at, ty_inst. apply (proj2 (Vfuel_pinst _ _ _ _ _ _ _)).
    exact (proj1 (Vfuel_teq _ _ T' T _ _ _ HT) Hw).
  - apply Vfuel_sess_intro; [done|apply fle_refl].
Qed.

Lemma close_redex N n S0 x a Π φ d v mt :
  unfoldS S0 = SEnd → fle (Some 1) d →
  v ∈ FV^N _ n⟦RTy (TSess S0 x a mt)⟧(Π, φ) →
  EClose v ∈ F^N _ n⟦RTy TUnit ▷ d⟧(Π, φ).
Proof.
  intros Hu Hd HV.
  eapply FuelE_op; [exact HV|]. intros v' Π' φ' HV' Hv' α e' Hst.
  destruct (Vfuel_sess_inv _ _ _ _ _ _ _ _ _ HV') as (o & s' & f & -> & -> & -> & Hq & Hf).
  pose proof (sequiv_unfold_end _ _ Hq Hu) as Hu'.
  op_step Hst. inversion Hst; subst. cbn [Fobl]. unfold f_close, f_act. split.
  { split_and!; [apply not_idle_single; congruence|rewrite dom_singleton_L; set_solver| |done].
    intros o' f' Ho'. rewrite dom_singleton_L in Ho'. set_solver. }
  exists s'. split_and!; [by rewrite lookup_singleton_eq|done|].
  rewrite !delete_singleton_eq, fmap_empty_c. intros j Hj. apply FuelE_val; [done|apply Vfuel_unit].
Qed.

Lemma select_redex (i : bool) N n S0 x S1 S2 a mS Π φ d v :
  unfoldS S0 = SPlus S1 S2 → fle (Some 1) d →
  v ∈ FV^N _ n⟦RTy (TSess S0 x a mS)⟧(Π, φ) →
  ESel i v ∈ F^N _ n⟦RTy (TSess (if i then S2 else S1) (sel_pt x i) mS mS) ▷ d⟧(Π, φ).
Proof.
  intros Hu Hd HV.
  eapply FuelE_op; [exact HV|]. intros v' Π' φ' HV' Hv' α e' Hst.
  destruct (Vfuel_sess_inv _ _ _ _ _ _ _ _ _ HV') as (o & s' & f & -> & -> & -> & Hq & Hf).
  destruct (sequiv_unfold_plus _ _ _ _ Hq Hu) as (S1' & S2' & Hu' & H1 & H2).
  op_step Hst. inversion Hst; subst. cbn [Fobl]. unfold f_select, f_act. split.
  { split_and!; [apply not_idle_single; congruence|rewrite dom_singleton_L; set_solver| |done].
    intros o' f' Ho'. rewrite dom_singleton_L in Ho'. set_solver. }
  exists s', S1', S2'. split_and!; [by rewrite lookup_singleton_eq|done|].
  rewrite refill_single, insert_singleton, decide_True by done.
  intros j Hj. apply FuelE_val; [done|]. apply Vfuel_sess_intro; [by destruct i|apply fle_refl].
Qed.

Lemma branch_redex N n S0 x S1 S2 a mS Π φ d v :
  unfoldS S0 = SWith S1 S2 → fle (Some 1) d →
  v ∈ FV^N _ n⟦RTy (TSess S0 x a mS)⟧(Π, φ) →
  EBra v ∈ F^N _ n⟦RTy (TSum (TSess S1 (bra_pt x false) mS mS) (TSess S2 (bra_pt x true) mS mS)) ▷ d⟧(Π, φ).
Proof.
  intros Hu Hd HV.
  eapply FuelE_op; [exact HV|]. intros v' Π' φ' HV' Hv' α e' Hst.
  destruct (Vfuel_sess_inv _ _ _ _ _ _ _ _ _ HV') as (o & s' & f & -> & -> & -> & Hq & Hf).
  destruct (sequiv_unfold_with _ _ _ _ Hq Hu) as (S1' & S2' & Hu' & H1 & H2).
  op_step Hst. inversion Hst; subst. cbn [Fobl]. unfold f_branch, f_act. split.
  { split_and!; [apply not_idle_single; congruence|rewrite dom_singleton_L; set_solver| |done].
    intros o' f' Ho'. rewrite dom_singleton_L in Ho'. set_solver. }
  exists s', S1', S2'. split_and!; [by rewrite lookup_singleton_eq|done|].
  rewrite refill_single, insert_singleton, decide_True by done.
  intros j Hj. apply FuelE_val; [by destruct i|]. destruct i; simpl.
  - apply (Vfuel_inj true). apply Vfuel_sess_intro; [done|apply fle_refl].
  - apply (Vfuel_inj false). apply Vfuel_sess_intro; [done|apply fle_refl].
Qed.

(** A link: the credit of each linked end exceeds what the bound leaves
    the partner of the other ([lgt]), and the counters are above the
    credits. *)
Lemma link_redex N n S x a1 m1 a2 m2 Π φ d v :
  lgt N a1 m2 → lgt N a2 m1 →
  v ∈ FV^N _ n⟦RTy (TProd (TSess S x a1 m1) (TSess (dual S) x‾ a2 m2))⟧(Π, φ) →
  ELink v ∈ F^N _ n⟦RTy TUnit ▷ d⟧(Π, φ).
Proof.
  intros Hl1 Hl2 HV.
  eapply FuelE_op; [exact HV|]. intros v' Π' φ' HV' Hv' α e' Hst.
  destruct (Vfuel_prod_inv _ _ _ _ _ _ _ HV') as (u & w & Π1 & Π2 & φ1 & φ2 & -> & HdΠ & Hdφ & -> & -> & Hu & Hw).
  destruct (Vfuel_sess_inv _ _ _ _ _ _ _ _ _ Hu) as (o1 & s1 & f1 & -> & -> & -> & Hs1 & Hf1).
  destruct (Vfuel_sess_inv _ _ _ _ _ _ _ _ _ Hw) as (o2 & s2 & f2 & -> & -> & -> & Hs2 & Hf2).
  assert (o1 ≠ o2) as Hne.
  { intros ->. apply map_disjoint_singleton_l in HdΠ. by rewrite lookup_singleton_eq in HdΠ. }
  op_step Hst. inversion Hst; subst. cbn [Fobl]. unfold f_link. split_and!.
  - exists o1, o2, s1, s2. split_and!; [done|done| | |].
    + by apply lookup_union_Some_l, lookup_singleton_eq.
    + apply lookup_union_Some_r; [done|]. by apply lookup_singleton_eq.
    + eapply sequiv_trans; [exact Hs2|]. apply sequiv_dual, sequiv_sym, Hs1.
  - rewrite dom_union_L, !dom_singleton_L. set_solver.
  - intros p1 p2 q1 q2 Hos Hne' G1 G2.
    assert (Hl : ∀ o p, ({[o1 := (f1, m1)]} ∪ {[o2 := (f2, m2)]} : cenv) !! o = Some p →
              (o = o1 ∧ p = (f1, m1)) ∨ (o = o2 ∧ p = (f2, m2))).
    { intros o p Ho. apply lookup_union_Some_raw in Ho as [Ho|[_ Ho]];
        apply lookup_singleton_Some in Ho as [<- <-]; auto. }
    assert (p1 = o1 ∧ p2 = o2 ∨ p1 = o2 ∧ p2 = o1) as Hcase.
    { assert (p1 ∈ ({[o1]} ∪ {[o2]} : gset cend)) as A1 by (rewrite Hos; set_solver).
      assert (p2 ∈ ({[o1]} ∪ {[o2]} : gset cend)) as A2 by (rewrite Hos; set_solver).
      set_solver. }
    destruct (Hl _ _ G1) as [[-> ->]|[-> ->]], (Hl _ _ G2) as [[-> ->]|[-> ->]]; simpl; try done.
    + split; [exact (lgt_mono _ _ _ _ _ Hf1 (fle_refl _) Hl1)|exact (lgt_mono _ _ _ _ _ Hf2 (fle_refl _) Hl2)].
    + split; [exact (lgt_mono _ _ _ _ _ Hf2 (fle_refl _) Hl2)|exact (lgt_mono _ _ _ _ _ Hf1 (fle_refl _) Hl1)].
  - assert (∀ {Y} (m : gmap cend Y), dom m = ({[o1]} ∪ {[o2]}) → mrem ({[o1]} ∪ {[o2]}) m = ∅) as Hm.
    { intros Y m Hd. rewrite <-Hd. apply mrem_self. }
    rewrite !Hm by (rewrite dom_union_L, !dom_singleton_L; set_solver).
    intros j Hj. apply FuelE_val; [done|apply Vfuel_unit].
Qed.

Lemma spawn_redex N n ub lb c' a Π φ d v :
  fle (Some 1) a →
  v ∈ FV^N _ n⟦RTy (TLolli ub lb c' TUnit TUnit a)⟧(Π, φ) →
  ESpawn v ∈ F^N _ n⟦RTy TUnit ▷ d⟧(Π, φ).
Proof.
  intros Ha HV.
 
  eapply FuelE_op; [exact HV|]. intros v' Π' φ' HV' Hv' α e' Hst.
  destruct (Vfuel_lolli_inv _ _ _ _ _ _ _ _ _ _ _ HV') as (e & -> & Hfe & Hd & Hfl & HF).
  op_step Hst. inversion Hst; subst. cbn [Fobl]. unfold f_spawn. simpl fends. rewrite Hfe.
  assert (∀ o f, φ' !! o = Some f → ¬ idle_at Π' o → fle (Some 1) f.1) as H1.
  { intros o f Ho Hi. eapply fle_trans; [exact Ha|exact (Hfl o f Ho Hi)]. }
  split_and!.
  - by rewrite Hd.
  - intros o f _ Ho Hi. by apply (H1 o f).
  - rewrite mres_self. unfold fhand. rewrite Hd, mres_self.
   
    intros j Hj.
    apply (FuelE_beta _ _ _ _ _ _ [] _ (subst1 EUnit e)); [constructor|by apply t_act_app|].
    intros i Hi. simpl.
    rewrite <-(map_union_empty Π'), <-(map_union_empty (ctick <$> φ')).
    eapply FuelE_thread; [constructor|].
    apply (HF i (ctick <$> φ') ∅ ∅ EUnit (olt_trans _ _ _ Hi Hj));
      [by rewrite dom_fmap_L| |apply map_disjoint_empty_r|apply map_disjoint_empty_r|apply Vfuel_unit].
    intros o f f' Ho Ho'. rewrite lookup_fmap, Ho in Ho'. injection Ho' as <-.
    split; [done|]. unfold ctick, ftick. destruct a as [[|a']|], f as [[f0|] m]; simpl in *; lia.
  - rewrite mrem_self, Hd, mrem_self. intros j Hj. apply FuelE_val; [done|apply Vfuel_unit].
Qed.

Lemma force_redex N n m k C ub c U xs ss Π φ d v :
  length ss = k → sinsts N ss → fle c d →
  v ∈ FV^N _ n⟦RTy (TBox m k C ub c U)⟧(Π, φ) →
  EForce v ∈ F^N _ n⟦RTy (sinst_ty (slist ss) (ty_inst xs U)) ▷ d⟧(Π, φ).
Proof.
  intros Hl Hs Hcd HV.
  destruct (Vfuel_box_inv _ _ _ _ _ _ _ _ _ _ _ HV) as (e & -> & _ & -> & -> & HF).
  apply (FuelE_beta _ _ _ _ _ _ [] _ (subst1 (EBox e) e)); [constructor|constructor|].
  intros j Hj. simpl. eapply FuelE_frame_mono; [exact Hcd|].
  eapply FuelE_res_mono; [|apply (HF j ss Hj Hl Hs)].
  intros j0 Π0 φ0 w _ Hw. unfold ty_inst. rewrite <-pinst_sinst_comm. by apply Vfuel_pinst.
Qed.

(** ** Creation *)

Lemma pnew_union c S (Π : penv) : pnew c S Π = ({[EPos c := S]} ∪ {[ENeg c := dual S]}) ∪ Π.
Proof. unfold pnew. rewrite !insert_union_singleton_l. by rewrite map_union_assoc. Qed.

Lemma cnew_union m1 m2 c (φ : cenv) : cnew m1 m2 c φ = ({[EPos c := (m1, m1)]} ∪ {[ENeg c := (m2, m2)]}) ∪ φ.
Proof. unfold cnew. rewrite !insert_union_singleton_l. by rewrite map_union_assoc. Qed.

Lemma Vfuel_newpair N n c S y m1 m2 :
  Pair (Chan (EPos c)) (Chan (ENeg c)) ∈ FV^N _ n⟦RTy (TProd (TSess S y m1 m1) (TSess (dual S) y‾ m2 m2))⟧(
    {[EPos c := S]} ∪ {[ENeg c := dual S]}, {[EPos c := (m1, m1)]} ∪ {[ENeg c := (m2, m2)]}).
Proof.
  apply Vfuel_pair.
  - by apply map_disjoint_singleton_l, lookup_singleton_ne.
  - by apply map_disjoint_singleton_l, lookup_singleton_ne.
  - apply Vfuel_sess_intro; [apply sequiv_refl|apply fle_refl].
  - apply Vfuel_sess_intro; [apply sequiv_refl|apply fle_refl].
Qed.

Lemma new_at_redex (κ : field) N n S0 x a m S m1 m2 Π φ d v :
  tsum_ok N m1 m2 →
  v ∈ FV^N _ n⟦RTy (TSess S0 x a m)⟧(Π, φ) →
  ENewAt κ v ∈ F^N _ n⟦RTy (TProd (TSess S0 x a m) (TProd (TSess S (x·κ) m1 m1) (TSess (dual S) (x·κ)‾ m2 m2))) ▷ d⟧(Π, φ).
Proof.
  intros Hm HV.
  eapply FuelE_op; [exact HV|]. intros v' Π' φ' HV' Hv' α e' Hst.
  destruct (Vfuel_sess_inv _ _ _ _ _ _ _ _ _ HV') as (o & s' & f & -> & -> & -> & Hq & Hf).
  op_step Hst. inversion Hst; subst. cbn [Fobl]. unfold f_new_at, f_new.
  split; [rewrite lookup_singleton_eq; by eexists|].
  intros (H1 & H2 & H3 & H4). exists S, m1, m2. split; [done|]. intros j Hj. rewrite pnew_union, cnew_union.
  rewrite dom_singleton_L in H1, H2. rewrite dom_singleton_L in H3, H4.
  rewrite (map_union_comm _ {[o := s']}), (map_union_comm _ {[o := (f, m)]}).
  2,3: apply map_disjoint_union_l; split; apply map_disjoint_singleton_l, lookup_singleton_ne; set_solver.
  apply FuelE_val; [done|]. apply Vfuel_pair.
  - apply map_disjoint_union_r. split; apply map_disjoint_singleton_l, lookup_singleton_ne; set_solver.
  - apply map_disjoint_union_r. split; apply map_disjoint_singleton_l, lookup_singleton_ne; set_solver.
  - by apply Vfuel_sess_intro.
  - apply Vfuel_newpair.
Qed.

Lemma new_redex (ℓ : family) N n lb C S m1 m2 d :
  tsum_ok N m1 m2 →
  ENew ℓ ∈ F^N _ n⟦RTy (TEx lb 1 C (TProd (TSess S (pvar 0) m1 m1) (TSess (dual S) (pvar 0)‾ m2 m2))) ▷ d⟧(∅, ∅).
Proof.
  intros Hm. apply FuelE_eq. intros g Π' φ' _ _ R1 R2.
  rewrite (renk_empty g Π' R1), (renk_empty g φ' R2). simpl. split; [done|].
  intros α e' Hst. apply tstep_inv in Hst as [Hh|(f & e0 & e0' & _ & Heq & _ & _)];
    [|by destruct f].
  inversion Hh; subst. cbn [Fobl]. unfold f_new. intros _. exists S, m1, m2. split; [done|].
  intros j Hj. rewrite pnew_union, cnew_union, !map_union_empty.
  apply FuelE_val; [done|]. apply Vfuel_pack. apply Vfuel_newpair.
Qed.
