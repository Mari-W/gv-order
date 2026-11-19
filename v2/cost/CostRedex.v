(** * Redexes of the cost judgment (stage S7)

    FuelE of each redex the rules build: the application of a closure,
    and the operators send, receive, close, select, branch, link, spawn,
    force, new_κ and new_ℓ, each at a value of [Vfuel]. Nt is the refill
    of the typing judgment, which annotates fresh and refilled ends, and
    N ⊒ Nt the refill of FuelE. *)

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

Lemma fmap_empty_c (h : fuel → fuel) : h <$> (∅ : cenv) = ∅.
Proof. apply fmap_empty. Qed.

Lemma ftick_fminus (φ : cenv) : ftick <$> φ = fminus (Some 1) <$> φ.
Proof. done. Qed.

Lemma rle_sinsts_up N N' ss : rle N N' → sinsts N ss → sinsts N' ss.
Proof. intros H [H1 H2]. split; [done|]. intros ->. destruct N; [done|]. by apply H2. Qed.

(** ** Sessions up to ≈ *)

Local Ltac hd_inv Hq Hu :=
  apply sequiv_step in Hq; unfold eq_step in Hq; rewrite (hd_of _ _ Hu) in Hq; simpl in Hq.

Lemma sequiv_unfold_snd s S0 m T b S :
  sequiv s S0 → unfoldS S0 = SSeq (SSnd m T b) S →
  ∃ T' S', unfoldS s = SSeq (SSnd m T' b) S' ∧ teq T' T ∧ sequiv S' S.
Proof.
  intros Hq Hu. hd_inv Hq Hu.
  destruct (hd s) eqn:Hs; simpl in Hq; try done. destruct_and!; subst.
  eexists _, _. split_and!; [|done|done]. by rewrite unfoldS_unview, Hs.
Qed.

Lemma sequiv_unfold_rcv s S0 m T b S :
  sequiv s S0 → unfoldS S0 = SSeq (SRcv m T b) S →
  ∃ T' S', unfoldS s = SSeq (SRcv m T' b) S' ∧ teq T' T ∧ sequiv S' S.
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

Lemma Vfuel_sess_inv N n s x a Π φ v :
  v ∈ FV^N _ n⟦RTy (TSess s x) a⟧(Π, φ) →
  ∃ o s' f, v = Chan o ∧ Π = {[o := s']} ∧ φ = {[o := f]} ∧ sequiv s' s ∧ fle a f.
Proof. rewrite Vfuel_eq. simpl. done. Qed.

Lemma Vfuel_sess_intro N n s x a o s' f :
  sequiv s' s → fle a f → Chan o ∈ FV^N _ n⟦RTy (TSess s x) a⟧({[o := s']}, {[o := f]}).
Proof. intros Hs Hf. rewrite Vfuel_eq. simpl. exists o, s', f. by split_and!. Qed.

Lemma Vfuel_prod_inv N n T1 a1 T2 a2 a Π φ v :
  v ∈ FV^N _ n⟦RTy (TProd T1 a1 T2 a2) a⟧(Π, φ) →
  ∃ v1 v2 Π1 Π2 φ1 φ2, v = Pair v1 v2 ∧ Π1 ##ₘ Π2 ∧ φ1 ##ₘ φ2 ∧ Π = Π1 ∪ Π2 ∧ φ = φ1 ∪ φ2 ∧
    v1 ∈ FV^N _ n⟦RTy T1 (fadd a a1)⟧(Π1, φ1) ∧ v2 ∈ FV^N _ n⟦RTy T2 (fadd a a2)⟧(Π2, φ2).
Proof. rewrite Vfuel_eq. simpl. setoid_rewrite Vfuel_eq. simpl. done. Qed.

Lemma Vfuel_sum_inv N n T1 a1 T2 a2 a Π φ v :
  v ∈ FV^N _ n⟦RTy (TSum T1 a1 T2 a2) a⟧(Π, φ) →
  (∃ v', v = Inj false v' ∧ v' ∈ FV^N _ n⟦RTy T1 (fadd a a1)⟧(Π, φ)) ∨
  (∃ v', v = Inj true v' ∧ v' ∈ FV^N _ n⟦RTy T2 (fadd a a2)⟧(Π, φ)).
Proof. rewrite Vfuel_eq. simpl. setoid_rewrite Vfuel_eq. simpl. done. Qed.

Lemma Vfuel_unit_inv N n a Π φ v : v ∈ FV^N _ n⟦RTy TUnit a⟧(Π, φ) → v = EUnit ∧ Π = ∅ ∧ φ = ∅.
Proof. rewrite Vfuel_eq. simpl. done. Qed.

Lemma Vfuel_lolli_inv N n ub lb c t h T aT U aU a Π φ v :
  v ∈ FV^N _ n⟦RTy (TLolli ub lb c t h T aT U aU) a⟧(Π, φ) →
  ∃ e, v = Lam e ∧ fends e = dom Π ∧ dom Π = dom φ ∧ (∀ o f, φ !! o = Some f → fle (fadd h a) f) ∧
    ∀ N' j φ' Πu φu u r tk, rle N N' → j < n → dom φ' = dom φ →
      (∀ o f, φ' !! o = Some f → fle h f) → Π ##ₘ Πu → φ' ##ₘ φu →
      u ∈ FV^N' _ j⟦RTy T aT⟧(Πu, φu) → meets t r tk →
      subst1 u e ∈ F^N' _ j⟦RTy U aU ▷ c ; r⟧(Π ∪ Πu, φ' ∪ φu, tk).
Proof. rewrite Vfuel_eq. simpl. done. Qed.

Lemma Vfuel_box_inv N n m k C ub c t U aU a Π φ v :
  v ∈ FV^N _ n⟦RTy (TBox m k C ub c t U aU) a⟧(Π, φ) →
  ∃ e, v = EBox e ∧ fends e = ∅ ∧ Π = ∅ ∧ φ = ∅ ∧
    ∀ N' j ss r tk, rle N N' → j < n → length ss = k → sinsts N' ss → meets t r tk →
      subst1 (EBox e) e ∈ F^N' _ j⟦RTy (sinst_ty (slist ss) U) aU ▷ c ; r⟧(∅, ∅, tk).
Proof. rewrite Vfuel_eq. simpl. done. Qed.

(** ** Unfolding at an operator *)

Lemma FuelE_op k N n σ d r Π φ tk v T a :
  v ∈ FV^N _ (S n)⟦RTy T a⟧(Π, φ) →
  (∀ N' v' Π' φ', rle N N' → v' ∈ FV^N' _ (S n)⟦RTy T a⟧(Π', φ') → is_val v' →
     ∀ α e', tstep (Op k v') α e' → Fobl N' (λ j N, FuelE N j) (λ j N, Vfuel N j) n σ d r Π' φ' tk α e') →
  Op k v ∈ F^N _ (S n)⟦σ ▷ d ; r⟧(Π, φ, tk).
Proof.
  intros HV H. apply FuelE_S. intros N' g Π' φ' HN Hk1 Hk2 R1 R2. split.
  - intros Hv. done.
  - intros α e' Hst. apply (H N' (emap g v) Π' φ'); [done| | |exact Hst].
    + eapply Vfuel_mono; [exact HN|apply cle_refl|]. by eapply Vfuel_rename.
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

Lemma app_redex N n ub lb c t h T aT U aU a1 Π1 φ1 Π2 φ2 tk d r v1 v2 :
  v1 ∈ FV^N _ n⟦RTy (TLolli ub lb c t h T aT U aU) a1⟧(Π1, φ1) → v2 ∈ FV^N _ n⟦RTy T aT⟧(Π2, φ2) →
  Π1 ##ₘ Π2 → φ1 ##ₘ φ2 → meets t r tk → fle c d →
  App v1 v2 ∈ F^N _ n⟦RTy U aU ▷ d ; r⟧(Π1 ∪ Π2, φ1 ∪ φ2, tk).
Proof.
  intros HV1 HV2 HdΠ Hdφ Hm Hcd. destruct n as [|n]; [apply FuelE_0|].
  destruct (Vfuel_lolli_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HV1) as (e & -> & _ & _ & Hfl & HF).
  apply (FuelE_beta _ _ _ _ _ _ _ _ [] _ (subst1 v2 e)); [constructor|by apply t_act_app; eapply Vfuel_val|].
  simpl. eapply FuelE_frame_mono; [exact Hcd|].
  apply (HF N n φ1 Π2 φ2 v2 r tk (rle_refl N) ltac:(lia) eq_refl); [|done|done| |done].
  - intros o f Ho. eapply fle_trans; [|exact (Hfl o f Ho)]. apply fle_fadd_l'.
  - eapply Vfuel_down; [|exact HV2]; lia.
Qed.

(** ** Session operators *)

Lemma send_redex Nt N n m T b S0 S x ap aS a0 Tp' ap' Π φ tk d r v :
  unfoldS S0 = SSeq (SSnd m T b) S →
  tage (Some 1) (payload_at m T x, fadd a0 ap) (Tp', ap') → tsub Tp' ap' (payload_at m T x) b →
  rle Nt N → fle (Some 1) d → r ≤ tk →
  v ∈ FV^N _ n⟦RTy (TProd (payload_at m T x) ap (TSess S0 x) aS) a0⟧(Π, φ) →
  ESend v ∈ F^N _ n⟦RTy (TSess S x⁺) Nt ▷ d ; r⟧(Π, φ, tk).
Proof.
  intros Hu Ha Hs HNt Hd Hr HV. destruct n as [|n]; [apply FuelE_0|].
  eapply FuelE_op; [exact HV|]. intros N' v' Π' φ' HN HV' Hv' α e' Hst.
  destruct (Vfuel_prod_inv _ _ _ _ _ _ _ _ _ _ HV') as (w & c & Π1 & Π2 & φ1 & φ2 & -> & HdΠ & Hdφ & -> & -> & Hw & Hc).
  destruct (Vfuel_sess_inv _ _ _ _ _ _ _ _ Hc) as (o & s' & f & -> & -> & -> & Hq & Hf).
  destruct (sequiv_unfold_snd _ _ _ _ _ _ Hq Hu) as (T' & S' & Hu' & HT & HS).
  op_step Hst. inversion Hst; subst. cbn [Fobl]. unfold f_send, f_act.
  assert (o ∉ dom φ1) as Ho1 by (apply map_disjoint_dom in Hdφ; rewrite dom_singleton_L in Hdφ; set_solver).
  assert (dom Π1 = dom φ1) as HdΠφ by (by eapply Vfuel_dom).
  assert (fends w = dom φ1) as Hfw by (rewrite (Vfuel_exact _ _ _ _ _ _ _ Hw); done).
  assert ((Π1 ∪ {[o := s']}) !! o = Some s') as HΠo.
  { apply lookup_union_Some_raw. right. split; [apply not_elem_of_dom; by rewrite HdΠφ|apply lookup_singleton_eq]. }
  assert (∀ o' f', o' ∈ dom (φ1 ∪ {[o := f]}) ∖ {[o]} → (φ1 ∪ {[o := f]}) !! o' = Some f' →
            ¬ idle_at (Π1 ∪ {[o := s']}) o' → fle (Some 1) f') as Hsp.
  { intros o' f' Ho' Hf' Hn. rewrite dom_union_L, dom_singleton_L in Ho'.
    apply lookup_union_Some_raw in Hf' as [Hf'|[_ Hf']]; [|apply lookup_singleton_Some in Hf'; set_solver].
    apply (Vfuel_age_above _ _ _ _ _ _ _ _ _ _ Ha Hw o' f' Hf').
    intros (Sq & HSq & Hiq). apply Hn. exists Sq. split; [by apply lookup_union_Some_l|done]. }
  split.
  { split_and!; [|rewrite dom_union_L, dom_singleton_L; set_solver|intros o' f' Ho' Hf' Hn; exact (Hsp o' f' Ho' Hf' Hn)|done].
    intros (S2 & HS2 & Hi). rewrite HΠo in HS2. injection HS2 as <-. unfold idle in Hi. congruence. }
  exists s', m, T', b, S'. split_and!.
  - done.
  - done.
  - rewrite Hfw, dom_union_L, dom_singleton_L. set_solver.
  - intros o' f' Ho' Hf' Hn. apply (Hsp o' f'); [|done|done]. rewrite Hfw in Ho'. rewrite dom_union_L, dom_singleton_L. set_solver.
  - rewrite Hfw, <-HdΠφ, mres_union_self by done. unfold fhand. rewrite HdΠφ, mres_union_self by done.
    rewrite ftick_fminus.
    pose proof (Vfuel_age _ _ _ _ _ _ _ _ _ _ Ha Hw) as H1.
    pose proof (Vfuel_sub _ _ _ _ _ _ _ _ _ Hs H1) as H2.
    unfold payload_at, ty_inst in H2. apply Vfuel_pinst in H2.
    apply (Vfuel_down _ _ (Datatypes.S n)); [lia|].
    exact (proj1 (Vfuel_teq _ _ T T' _ _ _ _ (teq_sym _ _ HT)) H2).
  - rewrite Hfw, <-HdΠφ, mrem_union_self by done. rewrite HdΠφ, mrem_union_self by done.
    unfold refill. rewrite delete_singleton_eq, fmap_empty_c, ?insert_empty, insert_singleton, decide_True by done.
    apply FuelE_val; [done|done|]. apply Vfuel_sess_intro; [done|]. apply rle_fle. by eapply rle_trans.
Qed.

Lemma recv_redex Nt N n m T b S0 S x a Π φ tk d r v :
  unfoldS S0 = SSeq (SRcv m T b) S → rle Nt N → fle (Some 1) d → r ≤ tk →
  v ∈ FV^N _ n⟦RTy (TSess S0 x) a⟧(Π, φ) →
  ERecv v ∈ F^N _ n⟦RTy (TProd (payload_at m T x) b (TSess S x⁺) Nt) (Some 0) ▷ d ; r⟧(Π, φ, tk).
Proof.
  intros Hu HNt Hd Hr HV. destruct n as [|n]; [apply FuelE_0|].
  eapply FuelE_op; [exact HV|]. intros N' v' Π' φ' HN HV' Hv' α e' Hst.
  destruct (Vfuel_sess_inv _ _ _ _ _ _ _ _ HV') as (o & s' & f & -> & -> & -> & Hq & Hf).
  destruct (sequiv_unfold_rcv _ _ _ _ _ _ Hq Hu) as (T' & S' & Hu' & HT & HS).
  op_step Hst. inversion Hst; subst. cbn [Fobl]. unfold f_recv, f_act. split.
  { split_and!; [apply not_idle_single; congruence|rewrite dom_singleton_L; set_solver| |done].
    intros o' f' Ho'. rewrite dom_singleton_L in Ho'. set_solver. }
  exists s', m, T', b, S'. split_and!; [by rewrite lookup_singleton_eq|done|].
  intros j Πi φi Hj HdΠ Hdφ Hw. unfold refill in *.
  rewrite delete_singleton_eq, fmap_empty_c, ?insert_empty in *. rewrite insert_singleton, decide_True in * by done.
  apply FuelE_val; [simpl; rewrite andb_True; split; [by eapply Vfuel_val|done]|done|].
  rewrite (map_union_comm {[o := S']}), (map_union_comm {[o := N']}) by (by apply map_disjoint_sym).
  apply Vfuel_pair; [by apply map_disjoint_sym|by apply map_disjoint_sym| |].
  - rewrite fadd_0_l. unfold payload_at, ty_inst. apply (proj2 (Vfuel_pinst _ _ _ _ _ _ _ _)).
    exact (proj1 (Vfuel_teq _ _ T' T _ _ _ _ HT) Hw).
  - rewrite fadd_0_l. apply Vfuel_sess_intro; [done|]. apply rle_fle. by eapply rle_trans.
Qed.

Lemma close_redex N n S0 x a Π φ tk d r v :
  unfoldS S0 = SEnd → fle (Some 1) d → r ≤ tk →
  v ∈ FV^N _ n⟦RTy (TSess S0 x) a⟧(Π, φ) →
  EClose v ∈ F^N _ n⟦RTy TUnit None ▷ d ; r⟧(Π, φ, tk).
Proof.
  intros Hu Hd Hr HV. destruct n as [|n]; [apply FuelE_0|].
  eapply FuelE_op; [exact HV|]. intros N' v' Π' φ' HN HV' Hv' α e' Hst.
  destruct (Vfuel_sess_inv _ _ _ _ _ _ _ _ HV') as (o & s' & f & -> & -> & -> & Hq & Hf).
  pose proof (sequiv_unfold_end _ _ Hq Hu) as Hu'.
  op_step Hst. inversion Hst; subst. cbn [Fobl]. unfold f_close, f_act. split.
  { split_and!; [apply not_idle_single; congruence|rewrite dom_singleton_L; set_solver| |done].
    intros o' f' Ho'. rewrite dom_singleton_L in Ho'. set_solver. }
  exists s'. split_and!; [by rewrite lookup_singleton_eq|done|].
  rewrite !delete_singleton_eq, fmap_empty_c. apply FuelE_val; [done|done|apply Vfuel_unit].
Qed.

Lemma select_redex (i : bool) Nt N n S0 x S1 S2 a Π φ tk d r v :
  unfoldS S0 = SPlus S1 S2 → rle Nt N → fle (Some 1) d → r ≤ tk →
  v ∈ FV^N _ n⟦RTy (TSess S0 x) a⟧(Π, φ) →
  ESel i v ∈ F^N _ n⟦RTy (TSess (if i then S2 else S1) (sel_pt x i)) Nt ▷ d ; r⟧(Π, φ, tk).
Proof.
  intros Hu HNt Hd Hr HV. destruct n as [|n]; [apply FuelE_0|].
  eapply FuelE_op; [exact HV|]. intros N' v' Π' φ' HN HV' Hv' α e' Hst.
  destruct (Vfuel_sess_inv _ _ _ _ _ _ _ _ HV') as (o & s' & f & -> & -> & -> & Hq & Hf).
  destruct (sequiv_unfold_plus _ _ _ _ Hq Hu) as (S1' & S2' & Hu' & H1 & H2).
  op_step Hst. inversion Hst; subst. cbn [Fobl]. unfold f_select, f_act. split.
  { split_and!; [apply not_idle_single; congruence|rewrite dom_singleton_L; set_solver| |done].
    intros o' f' Ho'. rewrite dom_singleton_L in Ho'. set_solver. }
  exists s', S1', S2'. split_and!; [by rewrite lookup_singleton_eq|done|].
  unfold refill. rewrite delete_singleton_eq, fmap_empty_c, ?insert_empty, insert_singleton, decide_True by done.
  apply FuelE_val; [done|done|]. apply Vfuel_sess_intro; [by destruct i|]. apply rle_fle. by eapply rle_trans.
Qed.

Lemma branch_redex Nt N n S0 x S1 S2 a Π φ tk d r v :
  unfoldS S0 = SWith S1 S2 → rle Nt N → fle (Some 1) d → r ≤ tk →
  v ∈ FV^N _ n⟦RTy (TSess S0 x) a⟧(Π, φ) →
  EBra v ∈ F^N _ n⟦RTy (TSum (TSess S1 (bra_pt x false)) Nt (TSess S2 (bra_pt x true)) Nt) (Some 0) ▷ d ; r⟧(Π, φ, tk).
Proof.
  intros Hu HNt Hd Hr HV. destruct n as [|n]; [apply FuelE_0|].
  eapply FuelE_op; [exact HV|]. intros N' v' Π' φ' HN HV' Hv' α e' Hst.
  destruct (Vfuel_sess_inv _ _ _ _ _ _ _ _ HV') as (o & s' & f & -> & -> & -> & Hq & Hf).
  destruct (sequiv_unfold_with _ _ _ _ Hq Hu) as (S1' & S2' & Hu' & H1 & H2).
  op_step Hst. inversion Hst; subst. cbn [Fobl]. unfold f_branch, f_act. split.
  { split_and!; [apply not_idle_single; congruence|rewrite dom_singleton_L; set_solver| |done].
    intros o' f' Ho'. rewrite dom_singleton_L in Ho'. set_solver. }
  exists s', S1', S2'. split_and!; [by rewrite lookup_singleton_eq|done|].
  unfold refill. rewrite delete_singleton_eq, fmap_empty_c, ?insert_empty, insert_singleton, decide_True by done.
  assert (fle Nt N') as HN' by (apply rle_fle; by eapply rle_trans).
  apply FuelE_val; [by destruct i|done|]. destruct i; simpl.
  - apply (Vfuel_inj true). rewrite fadd_0_l. by apply Vfuel_sess_intro.
  - apply (Vfuel_inj false). rewrite fadd_0_l. by apply Vfuel_sess_intro.
Qed.

Lemma link_redex N n S x a1 a2 a0 Π φ tk d r v :
  1 ≤ tk → r ≤ tk - 1 →
  v ∈ FV^N _ n⟦RTy (TProd (TSess S x) a1 (TSess (dual S) x‾) a2) a0⟧(Π, φ) →
  ELink v ∈ F^N _ n⟦RTy TUnit None ▷ d ; r⟧(Π, φ, tk).
Proof.
  intros Htk Hr HV. destruct n as [|n]; [apply FuelE_0|].
  eapply FuelE_op; [exact HV|]. intros N' v' Π' φ' HN HV' Hv' α e' Hst.
  destruct (Vfuel_prod_inv _ _ _ _ _ _ _ _ _ _ HV') as (u & w & Π1 & Π2 & φ1 & φ2 & -> & HdΠ & Hdφ & -> & -> & Hu & Hw).
  destruct (Vfuel_sess_inv _ _ _ _ _ _ _ _ Hu) as (o1 & s1 & f1 & -> & -> & -> & Hs1 & _).
  destruct (Vfuel_sess_inv _ _ _ _ _ _ _ _ Hw) as (o2 & s2 & f2 & -> & -> & -> & Hs2 & _).
  op_step Hst. inversion Hst; subst. cbn [Fobl]. unfold f_link. split_and!.
  - exists o1, o2, s1, s2. split_and!; [done| | | |].
    + intros ->. apply map_disjoint_singleton_l in HdΠ. by rewrite lookup_singleton_eq in HdΠ.
    + by apply lookup_union_Some_l, lookup_singleton_eq.
    + apply lookup_union_Some_r; [done|]. by apply lookup_singleton_eq.
    + eapply sequiv_trans; [exact Hs2|]. apply sequiv_dual, sequiv_sym, Hs1.
  - rewrite dom_union_L, !dom_singleton_L. set_solver.
  - done.
  - assert (∀ {Y} (m : gmap cend Y), dom m = ({[o1]} ∪ {[o2]}) → mrem ({[o1]} ∪ {[o2]}) m = ∅) as Hm.
    { intros Y m Hd. rewrite <-Hd. apply mrem_self. }
    rewrite !Hm by (rewrite dom_union_L, !dom_singleton_L; set_solver).
    apply FuelE_val; [done|done|apply Vfuel_unit].
Qed.

Lemma div2_bounds k : 2 * Nat.div2 k ≤ k ∧ k ≤ 2 * Nat.div2 k + 1.
Proof. pose proof (Nat.div2_odd k) as H. destruct (Nat.odd k); simpl in H; lia. Qed.

Lemma spawn_split_tid bc r tk :
  meets (tspawn bc tid) r tk → r ≤ Nat.div2 tk ∧ ∃ b, bc = Some b ∧ b ≤ Nat.div2 (S tk).
Proof.
  destruct bc as [b|]; unfold meets, tspawn, tid, tapp, fmul; [|simpl; done].
  intros H. simpl in H. pose proof (div2_bounds tk). pose proof (div2_bounds (S tk)). split; [lia|]. exists b. split; [done|lia].
Qed.

Lemma spawn_redex N n ub lb c' t' h a1 aU a Π φ tk d r v :
  fle (Some 1) a → meets (tspawn (tapp t' 0) tid) r tk →
  v ∈ FV^N _ n⟦RTy (TLolli ub lb c' t' h TUnit a1 TUnit aU) a⟧(Π, φ) →
  ESpawn v ∈ F^N _ n⟦RTy TUnit None ▷ d ; r⟧(Π, φ, tk).
Proof.
  intros Ha Hm HV. destruct (spawn_split_tid _ _ _ Hm) as (Hpar & b & Hb & Hch).
  destruct n as [|n]; [apply FuelE_0|].
  eapply FuelE_op; [exact HV|]. intros N' v' Π' φ' HN HV' Hv' α e' Hst.
  destruct (Vfuel_lolli_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HV') as (e & -> & Hfe & Hd & Hfl & HF).
  op_step Hst. inversion Hst; subst. cbn [Fobl]. unfold f_spawn. simpl fends. rewrite Hfe.
  assert (∀ o f, φ' !! o = Some f → fle (Some 1) f) as H1.
  { intros o f Ho. eapply fle_trans; [|exact (Hfl o f Ho)]. eapply fle_trans; [exact Ha|apply fle_fadd_r']. }
  split_and!.
  - by rewrite Hd.
  - intros o f _ Ho _. by apply (H1 o f).
  - rewrite mres_self. unfold fhand. rewrite Hd, mres_self.
    destruct n as [|n]; [apply FuelE_0|].
    apply (FuelE_beta _ _ _ _ _ _ _ _ [] _ (subst1 EUnit e)); [constructor|by apply t_act_app|]. simpl.
    rewrite <-(map_union_empty Π'), <-(map_union_empty (ftick <$> φ')).
    eapply FuelE_thread; [constructor|].
    apply (HF N' n (ftick <$> φ') ∅ ∅ EUnit 0 (Nat.div2 (S tk)) (rle_refl _) ltac:(lia));
      [by rewrite dom_fmap_L| |apply map_disjoint_empty_r|apply map_disjoint_empty_r|apply Vfuel_unit|].
    + intros o f Ho. apply lookup_fmap_Some in Ho as (f0 & <- & Ho). specialize (Hfl o f0 Ho).
      destruct h, a, f0; simpl in *; lia.
    + unfold meets. rewrite Hb. done.
  - rewrite mrem_self, Hd, mrem_self. apply FuelE_val; [done|done|apply Vfuel_unit].
Qed.

Lemma force_redex Nt N n m k C ub c t U aU a xs ss Π φ tk d r v :
  length ss = k → sinsts Nt ss → rle Nt N → meets t r tk → fle c d →
  v ∈ FV^N _ n⟦RTy (TBox m k C ub c t U aU) a⟧(Π, φ) →
  EForce v ∈ F^N _ n⟦RTy (sinst_ty (slist ss) (ty_inst xs U)) aU ▷ d ; r⟧(Π, φ, tk).
Proof.
  intros Hl Hs HNt Hm Hcd HV. destruct n as [|n]; [apply FuelE_0|].
  destruct (Vfuel_box_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ HV) as (e & -> & _ & -> & -> & HF).
  apply (FuelE_beta _ _ _ _ _ _ _ _ [] _ (subst1 (EBox e) e)); [constructor|constructor|]. simpl.
  eapply FuelE_frame_mono; [exact Hcd|].
  eapply FuelE_res_mono; [|apply (HF N n ss r tk (rle_refl _) ltac:(lia) Hl); [by eapply rle_sinsts_up|done]].
  intros N0 j Π0 φ0 w _ Hw. unfold ty_inst. rewrite <-pinst_sinst_comm. by apply Vfuel_pinst.
Qed.

(** ** Creation *)

Lemma pnew_union c S (Π : penv) : pnew c S Π = ({[EPos c := S]} ∪ {[ENeg c := dual S]}) ∪ Π.
Proof. unfold pnew. rewrite !insert_union_singleton_l. by rewrite map_union_assoc. Qed.

Lemma cnew_union N c (φ : cenv) : cnew N c φ = ({[EPos c := N]} ∪ {[ENeg c := N]}) ∪ φ.
Proof. unfold cnew. rewrite !insert_union_singleton_l. by rewrite map_union_assoc. Qed.

Lemma Vfuel_newpair Nt N n c S y :
  fle Nt N →
  Pair (Chan (EPos c)) (Chan (ENeg c)) ∈ FV^N _ n⟦RTy (TProd (TSess S y) Nt (TSess (dual S) y‾) Nt) (Some 0)⟧(
    {[EPos c := S]} ∪ {[ENeg c := dual S]}, {[EPos c := N]} ∪ {[ENeg c := N]}).
Proof.
  intros HN. apply Vfuel_pair.
  - by apply map_disjoint_singleton_l, lookup_singleton_ne.
  - by apply map_disjoint_singleton_l, lookup_singleton_ne.
  - rewrite fadd_0_l. apply Vfuel_sess_intro; [apply sequiv_refl|done].
  - rewrite fadd_0_l. apply Vfuel_sess_intro; [apply sequiv_refl|done].
Qed.

Lemma new_at_redex (κ : field) Nt N n S0 x a S Π φ tk d r v :
  rle Nt N → r ≤ tk →
  v ∈ FV^N _ n⟦RTy (TSess S0 x) a⟧(Π, φ) →
  ENewAt κ v ∈ F^N _ n⟦RTy (TProd (TSess S0 x) a (TProd (TSess S (x·κ)) Nt (TSess (dual S) (x·κ)‾) Nt) (Some 0)) (Some 0) ▷ d ; r⟧(Π, φ, tk).
Proof.
  intros HNt Hr HV. destruct n as [|n]; [apply FuelE_0|].
  eapply FuelE_op; [exact HV|]. intros N' v' Π' φ' HN HV' Hv' α e' Hst.
  destruct (Vfuel_sess_inv _ _ _ _ _ _ _ _ HV') as (o & s' & f & -> & -> & -> & Hq & Hf).
  op_step Hst. inversion Hst; subst. cbn [Fobl]. unfold f_new.
  intros (H1 & H2 & H3 & H4). exists S. rewrite pnew_union, cnew_union.
  rewrite dom_singleton_L in H1, H2. rewrite dom_singleton_L in H3, H4.
  rewrite (map_union_comm _ {[o := s']}), (map_union_comm _ {[o := f]}).
  2,3: apply map_disjoint_union_l; split; apply map_disjoint_singleton_l, lookup_singleton_ne; set_solver.
  apply FuelE_val; [done|done|]. apply Vfuel_pair.
  - apply map_disjoint_union_r. split; apply map_disjoint_singleton_l, lookup_singleton_ne; set_solver.
  - apply map_disjoint_union_r. split; apply map_disjoint_singleton_l, lookup_singleton_ne; set_solver.
  - rewrite fadd_0_l. by apply Vfuel_sess_intro.
  - rewrite fadd_0_l. apply Vfuel_newpair. apply rle_fle. by eapply rle_trans.
Qed.

Lemma new_redex (ℓ : family) Nt N n lb C S tk d r :
  rle Nt N → r ≤ tk →
  ENew ℓ ∈ F^N _ n⟦RTy (TEx lb 1 C (TProd (TSess S (pvar 0)) Nt (TSess (dual S) (pvar 0)‾) Nt) (Some 0)) (Some 0) ▷ d ; r⟧(∅, ∅, tk).
Proof.
  intros HNt Hr. destruct n as [|n]; [apply FuelE_0|].
  apply FuelE_S. intros N' g Π' φ' HN _ _ R1 R2.
  rewrite (renk_empty g Π' R1), (renk_empty g φ' R2). simpl. split; [done|].
  intros α e' Hst. apply tstep_inv in Hst as [Hh|(f & e0 & e0' & _ & Heq & _ & _)];
    [|by destruct f].
  inversion Hh; subst. cbn [Fobl]. unfold f_new. intros _. exists S.
  rewrite pnew_union, cnew_union, !map_union_empty.
  apply FuelE_val; [done|done|]. apply Vfuel_pack. rewrite fadd_0_l.
  apply Vfuel_newpair. apply rle_fle. by eapply rle_trans.
Qed.
