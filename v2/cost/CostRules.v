(** * The rules of the merged judgment are valid for its cost half (stage S7)

    One lemma per rule of static/Typing.v, [cost_e_unit] to
    [cost_e_open], each stating the rule for [csem]. The readiness and
    future premises of the typing rules do not appear: [csem] reads no
    point, world or future. The rules E-Abs, E-Box and E-SpawnLam build
    a closure or a box, and take [tfacts] of the term they build, so
    that the value is exact (Q15). *)

From GV Require Export cost.CostRedex.

(** ** Arithmetic of frames *)

Lemma fle_frame_op i c0 c : fle (Some i) c0 → fle c (fsub (fadd c0 c) (Some i)).
Proof. destruct c0, c; simpl; lia. Qed.

Lemma fle_frame_seq i c1 c2 : fle (Some i) c1 → fle c2 (fsub (fadd c1 c2) (Some i)).
Proof. destruct c1, c2; simpl; lia. Qed.

Lemma fle_frame_0 i c0 : fle (Some i) c0 → fle (Some 0) (fsub c0 (Some i)).
Proof. destruct c0; simpl; lia. Qed.

Lemma fsub_fsub (c : fuel) i j : fsub (fsub c (Some i)) (Some j) = fsub c (Some (i + j)).
Proof. destruct c; simpl; [f_equal; lia|done]. Qed.

Lemma meets_seq_split t1 t2 r tk : tok t1 t2 → meets (tseq t1 t2) r tk →
  ∃ r', meets t1 r' tk ∧ ∀ tk', r' ≤ tk' → meets t2 r tk'.
Proof.
  intros Hok Hm. destruct (seq_sound _ _ _ _ Hok Hm) as (r' & H1 & H2).
  exists r'. split; [done|]. intros tk' Htk. by eapply meets_mono.
Qed.


(** ** Leaves and structure *)

Lemma cost_e_unit N Δ : lenv_empty Δ → csem N ∅ Δ EUnit TUnit None (Some 0) tid.
Proof.
  intros HΔ N' n g γ Π φ r tk HN HE Hm. destruct (envf_empty _ _ _ _ _ _ _ HΔ HE) as [-> ->].
  simpl. apply FuelE_val; [done|by apply meets_tid|apply Vfuel_unit].
Qed.

Lemma cost_e_var N Δ x T a : lenv_only Δ x (T, a) → csem N ∅ Δ (Var x) T a (Some 0) tid.
Proof.
  intros Ho N' n g γ Π φ r tk HN HE Hm. simpl. pose proof (envf_only _ _ _ _ _ _ _ _ _ _ Ho HE) as HV.
  apply FuelE_val; [by eapply Vfuel_val|by apply meets_tid|done].
Qed.

Lemma cost_e_chan N Δ o S x a : lenv_empty Δ → csem N {[o := TE S x a]} Δ (Chan o) (TSess S x) a (Some 0) tid.
Proof.
  intros HΔ N' n g γ Π φ r tk HN HE Hm. destruct (envf_single _ _ _ _ _ _ _ _ _ HΔ HE) as (-> & f & -> & Hf).
  simpl. apply FuelE_val; [done|by apply meets_tid|]. by apply Vfuel_sess_intro; [apply sequiv_refl|].
Qed.

Lemma cost_e_sub N Θ Δ e T a T' a' c c' t t' :
  csem N Θ Δ e T a c t → tsub T a T' a' → fle c c' → tle t t' → csem N Θ Δ e T' a' c' t'.
Proof.
  intros Hcs Hs Hc Ht N' n g γ Π φ r tk HN HE Hm.
  eapply FuelE_sub; [exact Hs|]. eapply FuelE_frame_mono; [exact Hc|]. apply Hcs; [done|done|by apply Ht].
Qed.

Lemma cost_e_weak N Θ Δ' Δ e T a c t : lenv_wk Δ' Δ → csem N Θ Δ' e T a c t → csem N Θ Δ e T a c t.
Proof. intros Hw Hcs N' n g γ Π φ r tk HN HE. apply Hcs; [done|by eapply envf_wk]. Qed.

Lemma cost_e_contract N Θ Δ U aU e T a c t :
  unlimited U → csem N Θ (Some (U, aU) :: Some (U, aU) :: Δ) e T a c t →
  csem N Θ (Some (U, aU) :: Δ) (rename pred e) T a c t.
Proof.
  intros Hu Hcs N' n g γ Π φ r tk HN HE Hm.
  rewrite emap_rename, subst_rename. apply (Hcs N' n g (λ x, γ (pred x))); [done| |done].
  by apply envf_contract.
Qed.

Lemma cost_e_pack N Θ Δ e lb m C T xs a c t :
  csem N Θ Δ e (ty_inst xs T) a c t → csem N Θ Δ e (TEx lb m C T a) (Some 0) c t.
Proof.
  intros Hcs N' n g γ Π φ r tk HN HE Hm. eapply FuelE_res_mono; [|by apply Hcs].
  intros N0 j Π0 φ0 v _ Hv. apply Vfuel_pack. rewrite fadd_0_l. by apply Vfuel_pinst in Hv.
Qed.

Lemma cost_e_open N Θ Δ e i lb m C T aT a U aU c t :
  Δ !! i = Some (Some (TEx lb m C T aT, a)) →
  csem N (tenv_pinst (pshift m) Θ) (<[i := Some (T, fadd a aT)]> (lenv_pinst (pshift m) Δ))
    e (pinst_ty (pshift m) U) aU c t →
  csem N Θ Δ e U aU c t.
Proof.
  intros Hi Hcs N' n g γ Π φ r tk HN HE Hm. eapply FuelE_res_mono; [|apply Hcs; [done|by eapply envf_open|done]].
  intros N0 j Π0 φ0 v _ Hv. by apply Vfuel_pinst in Hv.
Qed.

(** ** Injections *)

Lemma cost_e_inj1 N Θ Δ e T a U b c t :
  csem N Θ Δ e T a c t → csem N Θ Δ (Inj1 e) (TSum T a U b) (Some 0) c t.
Proof.
  intros Hcs N' n g γ Π φ r tk HN HE Hm.
  change (subst γ (emap g (Inj1 e))) with (efill [FInj1] (subst γ (emap g e))).
  eapply (csem_bind0 N Θ Δ e T a c t [FInj1]); [repeat constructor|done|exact Hcs|apply fle_refl|done|done|exact Hm|].
  intros N'' j i v Πv φv tk' _ _ _ Hv Hr HV. simpl.
  apply FuelE_val; [done|done|]. apply Vfuel_inj1. by rewrite fadd_0_l.
Qed.

Lemma cost_e_inj2 N Θ Δ e T a U b c t :
  csem N Θ Δ e U b c t → csem N Θ Δ (Inj2 e) (TSum T a U b) (Some 0) c t.
Proof.
  intros Hcs N' n g γ Π φ r tk HN HE Hm.
  change (subst γ (emap g (Inj2 e))) with (efill [FInj2] (subst γ (emap g e))).
  eapply (csem_bind0 N Θ Δ e U b c t [FInj2]); [repeat constructor|done|exact Hcs|apply fle_refl|done|done|exact Hm|].
  intros N'' j i v Πv φv tk' _ _ _ Hv Hr HV. simpl.
  apply FuelE_val; [done|done|]. apply Vfuel_inj2. by rewrite fadd_0_l.
Qed.

(** ** Operators *)

Lemma cost_op N k Θ Δ e Targ a0 c0 t0 Tres ares c ϑ (top : tix) :
  csem N Θ Δ e Targ a0 c0 t0 → fle c0 c →
  (∀ r tk, meets ϑ r tk → ∃ r', meets t0 r' tk ∧ ∀ tk', r' ≤ tk' → meets top r tk') →
  (∀ N'' j v Πv φv i r tk', rle N N'' → fle (Some i) c0 → meets top r tk' →
     v ∈ FV^N'' _ j⟦RTy Targ a0⟧(Πv, φv) →
     Op k v ∈ F^N'' _ j⟦RTy Tres ares ▷ fsub c (Some i) ; r⟧(Πv, φv, tk')) →
  csem N Θ Δ (Op k e) Tres ares c ϑ.
Proof.
  intros Hcs Hc Hϑ Hred N' n g γ Π φ r tk HN HE Hm.
  destruct (Hϑ r tk Hm) as (r' & Hm' & Htop).
  change (subst γ (emap g (Op k e))) with (efill [FOp k] (subst γ (emap g e))).
  eapply (csem_bind0 N Θ Δ e Targ a0 c0 t0 [FOp k]); [repeat constructor|done|exact Hcs|done|done|done|exact Hm'|].
  intros N'' j i v Πv φv tk' HN' _ Hi Hv Hr HV. simpl.
  apply Hred; [by eapply rle_trans|done|by apply Htop|done].
Qed.

Lemma ϑ_same t r tk : meets t r tk → ∃ r', meets t r' tk ∧ ∀ tk', r' ≤ tk' → meets tid r tk'.
Proof. intros H. exists r. split; [done|]. intros tk' Htk. by apply meets_tid. Qed.

Lemma ϑ_seq t0 t r tk : tok t0 t → meets (tseq t0 t) r tk → ∃ r', meets t0 r' tk ∧ ∀ tk', r' ≤ tk' → meets t r tk'.
Proof. apply meets_seq_split. Qed.

Lemma fle_one_frame i c0 : fle (Some i) c0 → fle (Some 1) (fsub (fadd c0 (Some 1)) (Some i)).
Proof. destruct c0; simpl; lia. Qed.

Lemma cost_e_send N Θ Δ e S0 x m T b S ap aS a0 Tp' ap' c0 t0 :
  unfoldS S0 = SSeq (SSnd m T b) S →
  csem N Θ Δ e (TProd (payload_at m T x) ap (TSess S0 x) aS) a0 c0 t0 →
  tage (Some 1) (payload_at m T x, fadd a0 ap) (Tp', ap') → tsub Tp' ap' (payload_at m T x) b →
  csem N Θ Δ (ESend e) (TSess S x⁺) N (fadd c0 (Some 1)) t0.
Proof.
  intros Hu Hcs Ha Hs. eapply (cost_op _ _ _ _ _ _ _ _ _ _ _ _ _ tid Hcs); [apply fle_fadd_l'|apply ϑ_same|].
  intros N'' j v Πv φv i r tk' HN Hi Hm HV. apply (proj1 (meets_tid _ _)) in Hm.
  eapply send_redex; eauto using fle_one_frame.
Qed.

Lemma cost_e_recv N Θ Δ e S0 x m T b S a c0 t0 :
  unfoldS S0 = SSeq (SRcv m T b) S → csem N Θ Δ e (TSess S0 x) a c0 t0 →
  csem N Θ Δ (ERecv e) (TProd (payload_at m T x) b (TSess S x⁺) N) (Some 0) (fadd c0 (Some 1)) t0.
Proof.
  intros Hu Hcs. eapply (cost_op _ _ _ _ _ _ _ _ _ _ _ _ _ tid Hcs); [apply fle_fadd_l'|apply ϑ_same|].
  intros N'' j v Πv φv i r tk' HN Hi Hm HV. apply (proj1 (meets_tid _ _)) in Hm.
  eapply recv_redex; eauto using fle_one_frame.
Qed.

Lemma cost_e_close N Θ Δ e S0 x a c0 t0 :
  unfoldS S0 = SEnd → csem N Θ Δ e (TSess S0 x) a c0 t0 →
  csem N Θ Δ (EClose e) TUnit None (fadd c0 (Some 1)) t0.
Proof.
  intros Hu Hcs. eapply (cost_op _ _ _ _ _ _ _ _ _ _ _ _ _ tid Hcs); [apply fle_fadd_l'|apply ϑ_same|].
  intros N'' j v Πv φv i r tk' HN Hi Hm HV. apply (proj1 (meets_tid _ _)) in Hm.
  eapply close_redex; eauto using fle_one_frame.
Qed.

Lemma cost_e_select (i0 : bool) N Θ Δ e S0 x S1 S2 a c0 t0 :
  unfoldS S0 = SPlus S1 S2 → csem N Θ Δ e (TSess S0 x) a c0 t0 →
  csem N Θ Δ (ESel i0 e) (TSess (if i0 then S2 else S1) (sel_pt x i0)) N (fadd c0 (Some 1)) t0.
Proof.
  intros Hu Hcs. eapply (cost_op _ _ _ _ _ _ _ _ _ _ _ _ _ tid Hcs); [apply fle_fadd_l'|apply ϑ_same|].
  intros N'' j v Πv φv i r tk' HN Hi Hm HV. apply (proj1 (meets_tid _ _)) in Hm.
  eapply select_redex; eauto using fle_one_frame.
Qed.

Lemma cost_e_branch N Θ Δ e S0 x S1 S2 a c0 t0 :
  unfoldS S0 = SWith S1 S2 → csem N Θ Δ e (TSess S0 x) a c0 t0 →
  csem N Θ Δ (EBra e) (TSum (TSess S1 (bra_pt x false)) N (TSess S2 (bra_pt x true)) N) (Some 0)
    (fadd c0 (Some 1)) t0.
Proof.
  intros Hu Hcs. eapply (cost_op _ _ _ _ _ _ _ _ _ _ _ _ _ tid Hcs); [apply fle_fadd_l'|apply ϑ_same|].
  intros N'' j v Πv φv i r tk' HN Hi Hm HV. apply (proj1 (meets_tid _ _)) in Hm.
  eapply branch_redex; eauto using fle_one_frame.
Qed.

Lemma cost_e_link N Θ Δ e S x a1 a2 a0 c0 t0 :
  csem N Θ Δ e (TProd (TSess S x) a1 (TSess (dual S) x‾) a2) a0 c0 t0 → tok t0 (tlink tid) →
  csem N Θ Δ (ELink e) TUnit None c0 (tseq t0 (tlink tid)).
Proof.
  intros Hcs Hok. eapply (cost_op _ _ _ _ _ _ _ _ _ _ _ _ _ (tlink tid) Hcs); [apply fle_refl|intros ??; by apply ϑ_seq|].
  intros N'' j v Πv φv i r tk' HN Hi Hm HV. destruct (link_split _ _ _ Hm) as [H1 H2].
  apply (proj1 (meets_tid _ _)) in H2. by eapply link_redex.
Qed.

Lemma cost_e_spawn N Θ Δ e ub lb c' t' h a1 aU a c0 t0 :
  csem N Θ Δ e (TLolli ub lb c' t' h TUnit a1 TUnit aU) a c0 t0 → fle (Some 1) a →
  tok t0 (tspawn (tapp t' 0) tid) →
  csem N Θ Δ (ESpawn e) TUnit None c0 (tseq t0 (tspawn (tapp t' 0) tid)).
Proof.
  intros Hcs Ha Hok. eapply (cost_op _ _ _ _ _ _ _ _ _ _ _ _ _ (tspawn (tapp t' 0) tid) Hcs);
    [apply fle_refl|intros ??; by apply ϑ_seq|].
  intros N'' j v Πv φv i r tk' HN Hi Hm HV. by eapply spawn_redex.
Qed.

Lemma cost_e_force N Θ Δ e m k C ub c t U aU a xs ss c0 t0 :
  length ss = k → sinsts N ss → csem N Θ Δ e (TBox m k C ub c t U aU) a c0 t0 → tok t0 t →
  csem N Θ Δ (EForce e) (sinst_ty (slist ss) (ty_inst xs U)) aU (fadd c0 c) (tseq t0 t).
Proof.
  intros Hl Hs Hcs Hok. eapply (cost_op _ _ _ _ _ _ _ _ _ _ _ _ _ t Hcs); [apply fle_fadd_l'|intros ??; by apply ϑ_seq|].
  intros N'' j v Πv φv i r tk' HN Hi Hm HV. eapply force_redex; try done. by apply fle_frame_op.
Qed.

Lemma cost_e_new_at N Θ Δ e (κ : field) S0 x a S c0 t0 :
  csem N Θ Δ e (TSess S0 x) a c0 t0 →
  csem N Θ Δ (ENewAt κ e) (TProd (TSess S0 x) a (TProd (TSess S (x·κ)) N (TSess (dual S) (x·κ)‾) N) (Some 0))
    (Some 0) c0 t0.
Proof.
  intros Hcs. eapply (cost_op _ _ _ _ _ _ _ _ _ _ _ _ _ tid Hcs); [apply fle_refl|apply ϑ_same|].
  intros N'' j v Πv φv i r tk' HN Hi Hm HV. apply (proj1 (meets_tid _ _)) in Hm. by eapply new_at_redex.
Qed.

Lemma cost_e_new N Δ (ℓ : family) lb C S :
  lenv_empty Δ →
  csem N ∅ Δ (ENew ℓ) (TEx lb 1 C (TProd (TSess S (pvar 0)) N (TSess (dual S) (pvar 0)‾) N) (Some 0))
    (Some 0) (Some 0) tid.
Proof.
  intros HΔ N' n g γ Π φ r tk HN HE Hm. destruct (envf_empty _ _ _ _ _ _ _ HΔ HE) as [-> ->].
  simpl. apply (proj1 (meets_tid _ _)) in Hm. by apply new_redex.
Qed.

(** ** Compound terms *)

Lemma emap_subst_g (g' : cend → cend) γ g e :
  emap g' (subst γ (emap g e)) = subst (λ x, emap g' (γ x)) (emap (g' ∘ g) e).
Proof. by rewrite emap_subst, emap_emap. Qed.

Lemma emap_subst_up (g' : cend → cend) γ g e :
  emap g' (subst (up γ) (emap g e)) = subst (up (λ x, emap g' (γ x))) (emap (g' ∘ g) e).
Proof. rewrite emap_subst, emap_emap. apply subst_ext. intros x. apply emap_up. Qed.

Lemma emap_subst_up2 (g' : cend → cend) γ g e :
  emap g' (subst (up (up γ)) (emap g e)) = subst (up (up (λ x, emap g' (γ x)))) (emap (g' ∘ g) e).
Proof.
  rewrite emap_subst, emap_emap. apply subst_ext. intros x. rewrite emap_up.
  apply up_ext. intros y. apply emap_up.
Qed.

Lemma fle_frame_app i i2 c1 c2 c : fle (Some i) c1 → fle (Some i2) c2 →
  fle c (fsub (fsub (fadd c1 (fadd c2 c)) (Some i)) (Some i2)).
Proof. destruct c1, c2, c; simpl; lia. Qed.

Lemma fle_frame_mid i c1 c2 c : fle (Some i) c1 → fle c2 (fsub (fadd c1 (fadd c2 c)) (Some i)).
Proof. destruct c1, c2, c; simpl; lia. Qed.

Lemma fle_frame_pair i i2 c1 c2 : fle (Some i) c1 → fle (Some i2) c2 →
  fle (Some 0) (fsub (fsub (fadd c1 c2) (Some i)) (Some i2)).
Proof. destruct c1, c2; simpl; lia. Qed.

Lemma cost_e_app N Θ Θ1 Θ2 Θ2' Δ Δ1 Δ2 Δ2' e1 e2 ub lb c t h T aT U aU a1 c1 t1 c2 t2 :
  tsplit Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
  csem N Θ1 Δ1 e1 (TLolli ub lb c t h T aT U aU) a1 c1 t1 →
  thage c1 Θ2 Θ2' → lage c1 Δ2 Δ2' →
  csem N Θ2' Δ2' e2 T aT c2 t2 →
  fle c2 a1 → tok t2 t → tok t1 (tseq t2 t) →
  csem N Θ Δ (App e1 e2) U aU (fadd c1 (fadd c2 c)) (tseq t1 (tseq t2 t)).
Proof.
  intros Hs Hl Hc1 HaT HaD Hc2 Hc2a Hok2 Hok1 N' n g γ Π φ r tk HN HE Hm.
  destruct (envf_split _ _ _ _ _ _ _ _ _ _ _ _ Hs Hl HE) as (Π1 & Π2 & φ1 & φ2 & HdΠ & Hdφ & -> & -> & HE1 & HE2).
  destruct (seq_sound _ _ _ _ Hok1 Hm) as (r1 & Hm1 & Hm23).
  change (subst γ (emap g (App e1 e2))) with
    (fill_frame ((λ γ g, FAppL (subst γ (emap g e2))) γ g) (subst γ (emap g e1))).
  eapply (csem_bind1 N Θ1 Δ1 e1 _ a1 c1 t1 Θ2 Θ2' Δ2 Δ2' (λ γ g, FAppL (subst γ (emap g e2))) _ _ r
    N' n g γ Π1 φ1 Π2 φ2 tk r1);
    [intros g' γ0 g0; simpl; by rewrite emap_subst_g|done|exact Hc1|done|done|apply fle_fadd_l'
    |done|done|done|done|done|exact Hm1|].
  intros N'' j g' γ' Π' φ' i v Πv φv tk' HN' Hj Hi Hv Hr HE' HV HdΠ' Hdφ'. simpl.
  rewrite (map_union_comm Πv Π'), (map_union_comm φv φ') by done.
  assert (meets (tseq t2 t) r tk') as Hm23' by (by eapply meets_mono).
  destruct (seq_sound _ _ _ _ Hok2 Hm23') as (r2 & Hm2 & Hm3).
  change (App v (subst γ' (emap g' e2))) with (fill_frame ((λ v, FAppR v) v) (subst γ' (emap g' e2))).
  eapply (csem_bind2 N Θ2' Δ2' e2 T aT c2 t2 (λ v, FAppR v) _ a1 _ (fsub a1 c2) _ _ _ N'' j g' γ' Π' φ'
    v Πv φv tk' r2);
    [done|intros v0 Hv0; done|exact Hc2|by apply age_credit|by apply fle_frame_mid|by eapply rle_trans
    |by eapply Vfuel_val|exact HE'|exact HV|by apply map_disjoint_sym|by apply map_disjoint_sym|exact Hm2|].
  intros N3 j2 v' Πv' φv' u Πu φu i2 tk2 HN3 Hj2 Hi2 Hu Hr2 Hv' HV' HU HdΠ2 Hdφ2. simpl.
  rewrite (map_union_comm Πu Πv'), (map_union_comm φu φv') by done.
  eapply app_redex; [exact HV'|exact HU|by apply map_disjoint_sym|by apply map_disjoint_sym| |].
  - by eapply meets_mono.
  - by apply fle_frame_app.
Qed.

Lemma cost_e_pair N Θ Θ1 Θ2 Θ2' Δ Δ1 Δ2 Δ2' e1 e2 T1 a1 T1' a1' T2 a2 c1 t1 c2 t2 :
  tsplit Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
  csem N Θ1 Δ1 e1 T1 a1 c1 t1 → thage c1 Θ2 Θ2' → lage c1 Δ2 Δ2' →
  csem N Θ2' Δ2' e2 T2 a2 c2 t2 → tage c2 (T1, a1) (T1', a1') → tok t1 t2 →
  csem N Θ Δ (Pair e1 e2) (TProd T1' a1' T2 a2) (Some 0) (fadd c1 c2) (tseq t1 t2).
Proof.
  intros Hs Hl Hc1 HaT HaD Hc2 Hag Hok N' n g γ Π φ r tk HN HE Hm.
  destruct (envf_split _ _ _ _ _ _ _ _ _ _ _ _ Hs Hl HE) as (Π1 & Π2 & φ1 & φ2 & HdΠ & Hdφ & -> & -> & HE1 & HE2).
  destruct (seq_sound _ _ _ _ Hok Hm) as (r1 & Hm1 & Hm2).
  change (subst γ (emap g (Pair e1 e2))) with
    (fill_frame ((λ γ g, FPairL (subst γ (emap g e2))) γ g) (subst γ (emap g e1))).
  eapply (csem_bind1 N Θ1 Δ1 e1 T1 a1 c1 t1 Θ2 Θ2' Δ2 Δ2' (λ γ g, FPairL (subst γ (emap g e2))) _ _ r
    N' n g γ Π1 φ1 Π2 φ2 tk r1);
    [intros g' γ0 g0; simpl; by rewrite emap_subst_g|done|exact Hc1|done|done|apply fle_fadd_l'
    |done|done|done|done|done|exact Hm1|].
  intros N'' j g' γ' Π' φ' i v Πv φv tk' HN' Hj Hi Hv Hr HE' HV HdΠ' Hdφ'. simpl.
  rewrite (map_union_comm Πv Π'), (map_union_comm φv φ') by done.
  change (Pair v (subst γ' (emap g' e2))) with (fill_frame ((λ v, FPairR v) v) (subst γ' (emap g' e2))).
  eapply (csem_bind2 N Θ2' Δ2' e2 T2 a2 c2 t2 (λ v, FPairR v) T1 a1 T1' a1' _ _ _ N'' j g' γ' Π' φ'
    v Πv φv tk' r);
    [done|intros v0 Hv0; done|exact Hc2|exact Hag|by apply fle_frame_seq|by eapply rle_trans
    |by eapply Vfuel_val|exact HE'|exact HV|by apply map_disjoint_sym|by apply map_disjoint_sym
    |by eapply meets_mono|].
  intros N3 j2 v' Πv' φv' u Πu φu i2 tk2 HN3 Hj2 Hi2 Hu Hr2 Hv' HV' HU HdΠ2 Hdφ2. simpl.
  rewrite (map_union_comm Πu Πv'), (map_union_comm φu φv') by done.
  apply FuelE_val; [simpl; by rewrite andb_True|done|].
  apply Vfuel_pair; [by apply map_disjoint_sym|by apply map_disjoint_sym|by rewrite fadd_0_l|by rewrite fadd_0_l].
Qed.

Lemma cost_e_letu N Θ Θ1 Θ2 Θ2' Δ Δ1 Δ2 Δ2' e1 e2 a T aT c1 t1 c2 t2 :
  tsplit Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
  csem N Θ1 Δ1 e1 TUnit a c1 t1 → thage c1 Θ2 Θ2' → lage c1 Δ2 Δ2' →
  csem N Θ2' Δ2' e2 T aT c2 t2 → tok t1 t2 →
  csem N Θ Δ (LetU e1 e2) T aT (fadd c1 c2) (tseq t1 t2).
Proof.
  intros Hs Hl Hc1 HaT HaD Hc2 Hok N' n g γ Π φ r tk HN HE Hm.
  destruct (envf_split _ _ _ _ _ _ _ _ _ _ _ _ Hs Hl HE) as (Π1 & Π2 & φ1 & φ2 & HdΠ & Hdφ & -> & -> & HE1 & HE2).
  destruct (seq_sound _ _ _ _ Hok Hm) as (r1 & Hm1 & Hm2).
  change (subst γ (emap g (LetU e1 e2))) with
    (fill_frame ((λ γ g, FLetU (subst γ (emap g e2))) γ g) (subst γ (emap g e1))).
  eapply (csem_bind1 N Θ1 Δ1 e1 TUnit a c1 t1 Θ2 Θ2' Δ2 Δ2' (λ γ g, FLetU (subst γ (emap g e2))) _ _ r
    N' n g γ Π1 φ1 Π2 φ2 tk r1);
    [intros g' γ0 g0; simpl; by rewrite emap_subst_g|done|exact Hc1|done|done|apply fle_fadd_l'
    |done|done|done|done|done|exact Hm1|].
  intros N'' j g' γ' Π' φ' i v Πv φv tk' HN' Hj Hi Hv Hr HE' HV HdΠ' Hdφ'. simpl.
  destruct (Vfuel_unit_inv _ _ _ _ _ _ HV) as (-> & -> & ->). rewrite !map_empty_union.
  destruct j as [|j]; [apply FuelE_0|].
  apply (FuelE_beta _ _ _ _ _ _ _ _ [] _ (subst γ' (emap g' e2))); [constructor|constructor|]. simpl.
  eapply FuelE_frame_mono; [by apply fle_frame_seq|].
  apply Hc2; [by eapply rle_trans|(eapply envf_down; [|exact HE']; lia)|by eapply meets_mono].
Qed.

Lemma cost_e_letp N Θ Θ1 Θ2 Θ2' Δ Δ1 Δ2 Δ2' e1 e2 T1 a1 T2 a2 a T aT c1 t1 c2 t2 :
  tsplit Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
  csem N Θ1 Δ1 e1 (TProd T1 a1 T2 a2) a c1 t1 → thage c1 Θ2 Θ2' → lage c1 Δ2 Δ2' →
  csem N Θ2' (Some (T2, fadd a a2) :: Some (T1, fadd a a1) :: Δ2') e2 T aT c2 t2 → tok t1 t2 →
  csem N Θ Δ (LetP e1 e2) T aT (fadd c1 c2) (tseq t1 t2).
Proof.
  intros Hs Hl Hc1 HaT HaD Hc2 Hok N' n g γ Π φ r tk HN HE Hm.
  destruct (envf_split _ _ _ _ _ _ _ _ _ _ _ _ Hs Hl HE) as (Π1 & Π2 & φ1 & φ2 & HdΠ & Hdφ & -> & -> & HE1 & HE2).
  destruct (seq_sound _ _ _ _ Hok Hm) as (r1 & Hm1 & Hm2).
  change (subst γ (emap g (LetP e1 e2))) with
    (fill_frame ((λ γ g, FLetP (subst (up (up γ)) (emap g e2))) γ g) (subst γ (emap g e1))).
  eapply (csem_bind1 N Θ1 Δ1 e1 _ a c1 t1 Θ2 Θ2' Δ2 Δ2' (λ γ g, FLetP (subst (up (up γ)) (emap g e2))) _ _ r
    N' n g γ Π1 φ1 Π2 φ2 tk r1);
    [intros g' γ0 g0; simpl; by rewrite emap_subst_up2|done|exact Hc1|done|done|apply fle_fadd_l'
    |done|done|done|done|done|exact Hm1|].
  intros N'' j g' γ' Π' φ' i v Πv φv tk' HN' Hj Hi Hv Hr HE' HV HdΠ' Hdφ'. simpl.
  destruct (Vfuel_prod_inv _ _ _ _ _ _ _ _ _ _ HV) as (u & w & Πu & Πw & φu & φw & -> & Duw & Duw' & -> & -> & HU & HW).
  destruct j as [|j]; [apply FuelE_0|].
  apply (FuelE_beta _ _ _ _ _ _ _ _ [] _ (subst2 u w (subst (up (up γ')) (emap g' e2))));
    [constructor|constructor; by eapply Vfuel_val|]. simpl. rewrite subst2_subst.
  apply map_disjoint_union_l in HdΠ' as [D1 D2]. apply map_disjoint_union_l in Hdφ' as [D1' D2'].
  rewrite (map_union_comm (Πu ∪ Πw) Π'), (map_union_comm (φu ∪ φw) φ'), !map_union_assoc
    by (apply map_disjoint_union_l; split; by apply map_disjoint_sym).
  eapply FuelE_frame_mono; [by apply fle_frame_seq|].
  apply Hc2; [by eapply rle_trans| |by eapply meets_mono].
  apply envf_cons; [apply envf_cons| | |].
  - eapply envf_down; [|exact HE']; lia.
  - eapply Vfuel_down; [|exact HU]; lia.
  - by apply map_disjoint_sym.
  - by apply map_disjoint_sym.
  - eapply Vfuel_down; [|exact HW]; lia.
  - apply map_disjoint_union_l. split; [by apply map_disjoint_sym|done].
  - apply map_disjoint_union_l. split; [by apply map_disjoint_sym|done].
Qed.

Lemma cost_e_let N Θ Θ1 Θ2 Θ2' Δ Δ1 Δ2 Δ2' e1 e2 T1 a1 T aT c1 t1 c2 t2 :
  tsplit Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
  csem N Θ1 Δ1 e1 T1 a1 c1 t1 → thage c1 Θ2 Θ2' → lage c1 Δ2 Δ2' →
  csem N Θ2' (Some (T1, a1) :: Δ2') e2 T aT c2 t2 → tok t1 t2 →
  csem N Θ Δ (ELet e1 e2) T aT (fadd c1 c2) (tseq t1 t2).
Proof.
  intros Hs Hl Hc1 HaT HaD Hc2 Hok N' n g γ Π φ r tk HN HE Hm.
  destruct (envf_split _ _ _ _ _ _ _ _ _ _ _ _ Hs Hl HE) as (Π1 & Π2 & φ1 & φ2 & HdΠ & Hdφ & -> & -> & HE1 & HE2).
  destruct (seq_sound _ _ _ _ Hok Hm) as (r1 & Hm1 & Hm2).
  change (subst γ (emap g (ELet e1 e2))) with
    (fill_frame ((λ γ g, FLet (subst (up γ) (emap g e2))) γ g) (subst γ (emap g e1))).
  eapply (csem_bind1 N Θ1 Δ1 e1 T1 a1 c1 t1 Θ2 Θ2' Δ2 Δ2' (λ γ g, FLet (subst (up γ) (emap g e2))) _ _ r
    N' n g γ Π1 φ1 Π2 φ2 tk r1);
    [intros g' γ0 g0; simpl; by rewrite emap_subst_up|done|exact Hc1|done|done|apply fle_fadd_l'
    |done|done|done|done|done|exact Hm1|].
  intros N'' j g' γ' Π' φ' i v Πv φv tk' HN' Hj Hi Hv Hr HE' HV HdΠ' Hdφ'. simpl.
  destruct j as [|j]; [apply FuelE_0|].
  apply (FuelE_beta _ _ _ _ _ _ _ _ [] _ (subst1 v (subst (up γ') (emap g' e2))));
    [constructor|by constructor|]. simpl. rewrite subst1_subst.
  rewrite (map_union_comm Πv Π'), (map_union_comm φv φ') by done.
  eapply FuelE_frame_mono; [by apply fle_frame_seq|].
  apply Hc2; [by eapply rle_trans| |by eapply meets_mono].
  apply envf_cons; [(eapply envf_down; [|exact HE']; lia)|(eapply Vfuel_down; [|exact HV]; lia)
                   |by apply map_disjoint_sym|by apply map_disjoint_sym].
Qed.

Lemma meets_tmax t1 t2 r tk : meets (tmax t1 t2) r tk → meets t1 r tk ∧ meets t2 r tk.
Proof.
  destruct t1 as [[s1|] [b1|]], t2 as [[s2|] [b2|]]; unfold meets, tmax, tapp, fmax; simpl; try done.
  all: try (destruct (Nat.eqb r 0) eqn:E; simpl; [apply Nat.eqb_eq in E as ->|done]).
  all: try (intros H; split; lia).
  intros H. pose proof (Nat.pow_le_mono_r 2 s1 (Nat.max s1 s2) ltac:(lia) ltac:(lia)).
  pose proof (Nat.pow_le_mono_r 2 s2 (Nat.max s1 s2) ltac:(lia) ltac:(lia)). split; nia.
Qed.

Lemma fle_frame_case i c0 c1 c2 : fle (Some i) c0 →
  fle c1 (fsub (fadd c0 (fmax c1 c2)) (Some i)) ∧ fle c2 (fsub (fadd c0 (fmax c1 c2)) (Some i)).
Proof. destruct c0, c1, c2; simpl; lia. Qed.

Lemma cost_e_case N Θ Θ1 Θ2 Θ2' Δ Δ1 Δ2 Δ2' e e1 e2 T1 a1 T2 a2 a T aT c0 t0 c1 t1 c2 t2 :
  tsplit Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
  csem N Θ1 Δ1 e (TSum T1 a1 T2 a2) a c0 t0 → thage c0 Θ2 Θ2' → lage c0 Δ2 Δ2' →
  csem N Θ2' (Some (T1, fadd a a1) :: Δ2') e1 T aT c1 t1 →
  csem N Θ2' (Some (T2, fadd a a2) :: Δ2') e2 T aT c2 t2 →
  tok t0 (tmax t1 t2) →
  csem N Θ Δ (Case e e1 e2) T aT (fadd c0 (fmax c1 c2)) (tseq t0 (tmax t1 t2)).
Proof.
  intros Hs Hl Hc0 HaT HaD Hc1 Hc2 Hok N' n g γ Π φ r tk HN HE Hm.
  destruct (envf_split _ _ _ _ _ _ _ _ _ _ _ _ Hs Hl HE) as (Π1 & Π2 & φ1 & φ2 & HdΠ & Hdφ & -> & -> & HE1 & HE2).
  destruct (seq_sound _ _ _ _ Hok Hm) as (r1 & Hm1 & Hm2).
  change (subst γ (emap g (Case e e1 e2))) with
    (fill_frame ((λ γ g, FCase (subst (up γ) (emap g e1)) (subst (up γ) (emap g e2))) γ g) (subst γ (emap g e))).
  eapply (csem_bind1 N Θ1 Δ1 e _ a c0 t0 Θ2 Θ2' Δ2 Δ2'
    (λ γ g, FCase (subst (up γ) (emap g e1)) (subst (up γ) (emap g e2))) _ _ r N' n g γ Π1 φ1 Π2 φ2 tk r1);
    [intros g' γ0 g0; simpl; by rewrite !emap_subst_up|done|exact Hc0|done|done|apply fle_fadd_l'
    |done|done|done|done|done|exact Hm1|].
  intros N'' j g' γ' Π' φ' i v Πv φv tk' HN' Hj Hi Hv Hr HE' HV HdΠ' Hdφ'. simpl.
  destruct (fle_frame_case i c0 c1 c2 Hi) as [F1 F2].
  assert (meets (tmax t1 t2) r tk') as Hmx by (by eapply meets_mono).
  destruct (meets_tmax _ _ _ _ Hmx) as [M1 M2].
  rewrite (map_union_comm Πv Π'), (map_union_comm φv φ') by done.
  destruct j as [|j]; [apply FuelE_0|].
  destruct (Vfuel_sum_inv _ _ _ _ _ _ _ _ _ _ HV) as [(v' & -> & HV')|(v' & -> & HV')].
  - apply (FuelE_beta _ _ _ _ _ _ _ _ [] _ (subst1 v' (subst (up γ') (emap g' e1))));
      [constructor|constructor; by eapply Vfuel_val|]. simpl. rewrite subst1_subst.
    eapply FuelE_frame_mono; [exact F1|].
    apply Hc1; [by eapply rle_trans| |done].
    apply envf_cons; [(eapply envf_down; [|exact HE']; lia)|(eapply Vfuel_down; [|exact HV']; lia)
                     |by apply map_disjoint_sym|by apply map_disjoint_sym].
  - apply (FuelE_beta _ _ _ _ _ _ _ _ [] _ (subst1 v' (subst (up γ') (emap g' e2))));
      [constructor|constructor; by eapply Vfuel_val|]. simpl. rewrite subst1_subst.
    eapply FuelE_frame_mono; [exact F2|].
    apply Hc2; [by eapply rle_trans| |done].
    apply envf_cons; [(eapply envf_down; [|exact HE']; lia)|(eapply Vfuel_down; [|exact HV']; lia)
                     |by apply map_disjoint_sym|by apply map_disjoint_sym].
Qed.

(** ** Closures and boxes *)

Lemma cost_e_abs N Θ Θh Δ Δh e T aT U aU ub lb c t h a :
  tfacts Θ Δ (Lam e) → thcap h a Θ Θh → lcap h a Δ Δh →
  csem N Θh (Some (T, aT) :: Δh) e U aU c t →
  csem N Θ Δ (Lam e) (TLolli ub lb c t h T aT U aU) a (Some 0) tid.
Proof.
  intros Hf HcT HcD Hcs N' n g γ Π φ r tk HN HE Hm.
  pose proof (envf_exact _ _ _ _ _ _ _ _ _ Hf HE) as Hx. simpl in Hx |- *.
  apply FuelE_val; [done|by apply (proj1 (meets_tid _ _))|]. apply Vfuel_eq. simpl.
  exists (subst (up γ) (emap g e)). split_and!.
  - done.
  - done.
  - by eapply envf_dom.
  - eapply envf_cap_above; [exact HcT|exact HcD|exact HE].
  - intros N'' j φ' Πu φu u r' tk' HN' Hj Hdφ' Hh HdΠ Hdφ Hu Hm'. rewrite subst1_subst.
    apply Hcs; [by eapply rle_trans| |done].
    apply envf_cons; [|done|done|done].
    apply (envf_mono N' N'' n j _ _ _ _ _ φ'); [exact HN'|lia|apply cle_refl|].
    by eapply envf_cap.
Qed.

Lemma cost_e_box N Δ e m k C ub c t U aU :
  tfacts ∅ Δ (EBox e) → lenv_unl Δ →
  (∀ ss, length ss = k → sinsts N ss →
     csem N ∅ (lenv_pinst (pshift m) (Some (TBox m k C ub c t U aU, None) :: Δ)) e (sinst_ty (slist ss) U) aU c t) →
  csem N ∅ Δ (EBox e) (TBox m k C ub c t U aU) None (Some 0) tid.
Proof.
  intros Hf Hu Hcs N' n g γ Π φ r tk HN HE Hm.
  pose proof (envf_exact _ _ _ _ _ _ _ _ _ Hf HE) as Hx.
  destruct (envf_unl _ _ _ _ _ _ _ Hu HE) as [-> ->]. simpl in Hx |- *. rewrite dom_empty_L in Hx.
  set (eb := subst (up γ) (emap g e)). fold eb in Hx.
  apply FuelE_val; [done|by apply (proj1 (meets_tid _ _))|].
  assert (Hlob : ∀ j, j ≤ n → ∀ N1, rle N' N1 → EBox eb ∈ FV^N1 _ j⟦RTy (TBox m k C ub c t U aU) None⟧(∅, ∅)).
  { induction j as [j IH] using lt_wf_ind. intros Hj N1 HN1. apply Vfuel_eq. simpl.
    exists eb. split_and!; [done|done|done|done|].
    intros N2 j' ss r' tk' HN2 Hj' Hl Hss Hm'. unfold eb. rewrite subst1_subst.
    rewrite <-(map_empty_union (∅ : penv)), <-(map_empty_union (∅ : cenv)).
    assert (rle N N2) as HN2' by (eapply rle_trans; [exact HN|]; by eapply rle_trans).
    apply (Hcs ss Hl (rle_sinsts _ _ _ HN2' Hss) N2 j' g (EBox eb .: γ)); [exact HN2'| |exact Hm'].
    assert (envf N2 j' ∅ (Some (TBox m k C ub c t U aU, None) :: Δ) g (EBox eb .: γ) (∅ ∪ ∅) (∅ ∪ ∅)) as H.
    { apply envf_cons; [|apply IH; [lia|lia|by eapply rle_trans]|apply map_disjoint_empty_l|apply map_disjoint_empty_l].
      apply (envf_mono N' N2 n j' _ _ _ _ _ ∅ ∅); [by eapply rle_trans|lia|apply cle_refl|exact HE]. }
    apply (envf_pinst _ _ (pshift m)) in H. unfold tenv_pinst in H. rewrite fmap_empty in H. exact H. }
  apply Hlob; [lia|apply rle_refl].
Qed.

Lemma cost_e_spawn_lam N Θ Θ' Δ Δ' e a1 aU c' t' :
  tfacts Θ Δ (Lam e) → thage (Some 1) Θ Θ' → lage (Some 1) Δ Δ' →
  csem N Θ' (Some (TUnit, a1) :: Δ') e TUnit aU c' t' →
  csem N Θ Δ (ESpawn (Lam e)) TUnit None (Some 0) (tspawn (tapp t' 0) tid).
Proof.
  intros Hf HaT HaD Hcs N' n g γ Π φ r tk HN HE Hm.
  destruct (spawn_split_tid _ _ _ Hm) as (Hpar & b & Hb & Hch).
  pose proof (envf_exact _ _ _ _ _ _ _ _ _ Hf HE) as Hx. simpl in Hx |- *.
  pose proof (envf_dom _ _ _ _ _ _ _ _ HE) as Hd.
  pose proof (envf_age_above _ _ _ _ _ _ _ _ _ _ _ HaT HaD HE) as Hab.
  destruct n as [|n]; [apply FuelE_0|].
  apply FuelE_S. intros N'' g' Π' φ' HN' Hk1 Hk2 R1 R2. split; [intros Hv; done|].
  intros α e' Hst. cbn [emap] in Hst. apply op_head_only' in Hst; [|done].
  inversion Hst; subst. cbn [Fobl]. unfold f_spawn.
  rewrite emap_subst_up. set (eb := subst (up (λ x, emap g' (γ x))) (emap (g' ∘ g) e)).
  assert (fends (Lam eb) = dom Π') as HM.
  { unfold eb. rewrite <-emap_subst_up. simpl. rewrite fends_emap, Hx. symmetry. by apply renk_dom. }
  assert (dom Π' = dom φ') as Hd'.
  { rewrite (renk_dom _ _ _ R1), (renk_dom _ _ _ R2). by rewrite Hd. }
  rewrite HM. split_and!.
  - by rewrite Hd'.
  - intros o f _ Ho Hn. destruct (proj2 R2 o f Ho) as (o0 & -> & Ho0). apply (Hab o0 f Ho0).
    intros (S0 & HS0 & Hi0). apply Hn. exists S0. split; [by apply (proj1 R1)|done].
  - rewrite mres_self. unfold fhand. rewrite Hd', mres_self.
    destruct n as [|n]; [apply FuelE_0|].
    apply (FuelE_beta _ _ _ _ _ _ _ _ [] _ (subst1 EUnit eb)); [constructor|by constructor|]. simpl.
    unfold eb. rewrite subst1_subst.
    rewrite <-(map_union_empty Π'), <-(map_union_empty (ftick <$> φ')).
    eapply FuelE_thread; [constructor|].
    apply (Hcs N'' n (g' ∘ g) (EUnit .: (λ x, emap g' (γ x))) _ _ 0 (Nat.div2 (S tk)));
      [by eapply rle_trans| |unfold meets; by rewrite Hb].
    apply envf_cons; [|apply Vfuel_unit|apply map_disjoint_empty_r|apply map_disjoint_empty_r].
    rewrite ftick_fminus. apply (envf_age _ _ _ _ _ _ _ _ _ _ _ HaT HaD).
    apply (envf_mono N'' N'' (S (S n)) n _ _ _ _ _ φ'); [apply rle_refl|lia|apply cle_refl|].
    apply (envf_mono N' N'' (S (S n)) (S (S n)) _ _ _ _ _ φ'); [exact HN'|lia|apply cle_refl|by eapply envf_rename].
  - rewrite mrem_self, Hd', mrem_self. apply FuelE_val; [done|done|apply Vfuel_unit].
Qed.
