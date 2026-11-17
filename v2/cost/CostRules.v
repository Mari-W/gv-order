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
