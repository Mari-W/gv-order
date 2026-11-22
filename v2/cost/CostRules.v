(** * The rules of the merged judgment are valid for its cost half (stage S7)

    One lemma per rule of static/Typing.v, [cost_e_unit] to
    [cost_e_open], each stating the rule for [csem]. The readiness and
    future premises of the typing rules do not appear: [csem] reads no
    point, world or future. The rules E-Abs and E-Box build
    a closure or a box, and take [tfacts] of the term they build, so
    that the value is exact (Q15). *)

From GV Require Export cost.CostRedex.

(** ** Arithmetic of frames *)

Lemma fle_frame_op i c0 c : fle (Some i) c0 → fle c (fsub (fadd c0 c) (Some i)).
Proof. destruct c0, c; simpl; lia. Qed.

Lemma fle_frame_seq i c1 c2 : fle (Some i) c1 → fle c2 (fsub (fadd c1 c2) (Some i)).
Proof. destruct c1, c2; simpl; lia. Qed.


(** ** Leaves and structure *)

Lemma cost_e_unit N Δ : lenv_unl Δ → csem N ∅ Δ EUnit TUnit (Some 0).
Proof.
  intros HΔ n g γ Π φ HE. destruct (envf_unl _ _ _ _ _ _ _ HΔ HE) as [-> ->].
  simpl. apply FuelE_val; [done|apply Vfuel_unit].
Qed.

Lemma cost_e_var N Δ x T : lenv_only Δ x T → csem N ∅ Δ (Var x) T (Some 0).
Proof.
  intros Ho n g γ Π φ HE. simpl. pose proof (envf_only _ _ _ _ _ _ _ _ _ Ho HE) as HV.
  apply FuelE_val; [by eapply Vfuel_val|done].
Qed.

Lemma cost_e_chan N Δ o S x a m : lenv_unl Δ → csem N {[o := TE S x a m]} Δ (Chan o) (TSess S x a m) (Some 0).
Proof.
  intros HΔ n g γ Π φ HE. destruct (envf_single _ _ _ _ _ _ _ _ _ HΔ HE) as (-> & [f m'] & -> & Hf & Hm).
  simpl in Hf, Hm. subst m'.
  simpl. apply FuelE_val; [done|]. by apply Vfuel_sess_intro; [apply sequiv_refl|].
Qed.

Lemma cost_e_sub N W Γ Θ Δ e T T' c c' :
  csem N Θ Δ e T c → tsub W Γ T T' → fle c c' → csem N Θ Δ e T' c'.
Proof.
  intros Hcs Hs Hc n g γ Π φ HE.
  eapply FuelE_sub; [exact Hs|]. eapply FuelE_frame_mono; [exact Hc|]. by apply Hcs.
Qed.

Lemma cost_e_pack N Θ Δ e lb m C T xs c :
  csem N Θ Δ e (ty_inst xs T) c → csem N Θ Δ e (TEx lb m C T) c.
Proof.
  intros Hcs n g γ Π φ HE. eapply FuelE_res_mono; [|by apply Hcs].
  intros j Π0 φ0 v _ Hv. apply Vfuel_pack. by apply Vfuel_pinst in Hv.
Qed.

Lemma cost_e_open N Θ Δ e i lb m C T U c :
  Δ !! i = Some (Some (TEx lb m C T)) →
  csem N (tenv_pinst (pshift m) Θ) (<[i := Some T]> (lenv_pinst (pshift m) Δ))
    e (pinst_ty (pshift m) U) c →
  csem N Θ Δ e U c.
Proof.
  intros Hi Hcs n g γ Π φ HE. eapply FuelE_res_mono; [|apply Hcs; by eapply envf_open].
  intros j Π0 φ0 v _ Hv. by apply Vfuel_pinst in Hv.
Qed.

(** ** Injections *)

Lemma cost_e_inj (i : bool) N Θ Δ e T U c :
  csem N Θ Δ e (if i then U else T) c →
  csem N Θ Δ (Inj i e) (TSum T U) c.
Proof.
  intros Hcs n g γ Π φ HE.
  change (subst γ (emap g (Inj i e))) with (efill [FInj i] (subst γ (emap g e))).
  eapply (csem_bind0 N Θ Δ e _ c [FInj i]); [repeat constructor|done|exact Hcs|apply fle_refl|done|].
  intros j i' v Πv φv _ _ Hv HV. simpl.
  apply FuelE_val; [done|]. apply Vfuel_inj. by destruct i.
Qed.

(** ** Operators *)

Lemma cost_op N k Θ Δ e Targ c0 Tres c :
  csem N Θ Δ e Targ c0 → fle c0 c →
  (∀ j v Πv φv i, fle (Some i) c0 →
     v ∈ FV^N _ j⟦RTy Targ⟧(Πv, φv) →
     Op k v ∈ F^N _ j⟦RTy Tres ▷ fsub c (Some i)⟧(Πv, φv)) →
  csem N Θ Δ (Op k e) Tres c.
Proof.
  intros Hcs Hc Hred n g γ Π φ HE.
  change (subst γ (emap g (Op k e))) with (efill [FOp k] (subst γ (emap g e))).
  eapply (csem_bind0 N Θ Δ e Targ c0 [FOp k]); [repeat constructor|done|exact Hcs|done|done|].
  intros j i v Πv φv _ Hi Hv HV. simpl. by apply Hred.
Qed.

Lemma fle_one_frame i c0 : fle (Some i) c0 → fle (Some 1) (fsub (fadd c0 (Some 1)) (Some i)).
Proof. destruct c0; simpl; lia. Qed.

Lemma cost_e_send N W Γ Θ Δ e S0 x m T S aS mS Tp Tp' c0 :
  unfoldS S0 = SSeq (SSnd m T) S →
  csem N Θ Δ e (TProd Tp (TSess S0 x aS mS)) c0 →
  tage (Some 1) Tp Tp' → tsub W Γ Tp' (payload_at m T x) →
  csem N Θ Δ (ESend e) (TSess S x⁺ mS mS) (fadd c0 (Some 1)).
Proof.
  intros Hu Hcs Ha Hs. eapply (cost_op _ _ _ _ _ _ _ _ _ Hcs); [apply fle_fadd_l'|].
  intros j v Πv φv i Hi HV. eapply send_redex; eauto using fle_one_frame.
Qed.

Lemma cost_e_recv N Θ Δ e S0 x m T S a mS c0 :
  unfoldS S0 = SSeq (SRcv m T) S → csem N Θ Δ e (TSess S0 x a mS) c0 →
  csem N Θ Δ (ERecv e) (TProd (payload_at m T x) (TSess S x⁺ mS mS)) (fadd c0 (Some 1)).
Proof.
  intros Hu Hcs. eapply (cost_op _ _ _ _ _ _ _ _ _ Hcs); [apply fle_fadd_l'|].
  intros j v Πv φv i Hi HV. eapply recv_redex; eauto using fle_one_frame.
Qed.

Lemma cost_e_close N Θ Δ e S0 x a mS c0 :
  unfoldS S0 = SEnd → csem N Θ Δ e (TSess S0 x a mS) c0 →
  csem N Θ Δ (EClose e) TUnit (fadd c0 (Some 1)).
Proof.
  intros Hu Hcs. eapply (cost_op _ _ _ _ _ _ _ _ _ Hcs); [apply fle_fadd_l'|].
  intros j v Πv φv i Hi HV. eapply close_redex; eauto using fle_one_frame.
Qed.

Lemma cost_e_select (i0 : bool) N Θ Δ e S0 x S1 S2 a mS c0 :
  unfoldS S0 = SPlus S1 S2 → csem N Θ Δ e (TSess S0 x a mS) c0 →
  csem N Θ Δ (ESel i0 e) (TSess (if i0 then S2 else S1) (sel_pt x i0) mS mS) (fadd c0 (Some 1)).
Proof.
  intros Hu Hcs. eapply (cost_op _ _ _ _ _ _ _ _ _ Hcs); [apply fle_fadd_l'|].
  intros j v Πv φv i Hi HV. eapply select_redex; eauto using fle_one_frame.
Qed.

Lemma cost_e_branch N Θ Δ e S0 x S1 S2 a mS c0 :
  unfoldS S0 = SWith S1 S2 → csem N Θ Δ e (TSess S0 x a mS) c0 →
  csem N Θ Δ (EBra e) (TSum (TSess S1 (bra_pt x false) mS mS) (TSess S2 (bra_pt x true) mS mS))
    (fadd c0 (Some 1)).
Proof.
  intros Hu Hcs. eapply (cost_op _ _ _ _ _ _ _ _ _ Hcs); [apply fle_fadd_l'|].
  intros j v Πv φv i Hi HV. eapply branch_redex; eauto using fle_one_frame.
Qed.

Lemma cost_e_link N Θ Δ e S x a1 m1 a2 m2 c0 :
  csem N Θ Δ e (TProd (TSess S x a1 m1) (TSess (dual S) x‾ a2 m2)) c0 →
  lgt N a1 m2 → lgt N a2 m1 →
  csem N Θ Δ (ELink e) TUnit c0.
Proof.
  intros Hcs H1 H2. eapply (cost_op _ _ _ _ _ _ _ _ _ Hcs); [apply fle_refl|].
  intros j v Πv φv i Hi HV. eapply (link_redex N j S x a1 m1 a2 m2); [exact H1|exact H2|exact HV].
Qed.

Lemma cost_e_spawn N Θ Δ e ub lb c' a c0 :
  csem N Θ Δ e (TLolli ub lb c' TUnit TUnit a) c0 →
  csem N Θ Δ (ESpawn e) TUnit c0.
Proof.
  intros Hcs. eapply (cost_op _ _ _ _ _ _ _ _ _ Hcs); [apply fle_refl|].
  intros j v Πv φv i Hi HV. by eapply spawn_redex.
Qed.

Lemma cost_e_force N Θ Δ e m k C ub c U xs ss c0 :
  length ss = k → sinsts N ss → csem N Θ Δ e (TBox m k C ub c U) c0 →
  csem N Θ Δ (EForce e) (sinst_ty (slist ss) (ty_inst xs U)) (fadd c0 c).
Proof.
  intros Hl Hs Hcs. eapply (cost_op _ _ _ _ _ _ _ _ _ Hcs); [apply fle_fadd_l'|].
  intros j v Πv φv i Hi HV. eapply force_redex; try done. by apply fle_frame_op.
Qed.

Lemma cost_e_new N Δ lb C S m1 m2 :
  lenv_unl Δ → tsum_ok N m1 m2 →
  csem N ∅ Δ ENew (TEx lb 1 C (TProd (TSess S (pvar 0) m1 m1) (TSess (dual S) (pvar 0)‾ m2 m2))) (Some 0).
Proof.
  intros HΔ Hm n g γ Π φ HE. destruct (envf_unl _ _ _ _ _ _ _ HΔ HE) as [-> ->].
  simpl. by eapply new_redex.
Qed.

Lemma cost_e_new_fld N Δ y S m1 m2 :
  lenv_unl Δ → tsum_ok N m1 m2 →
  csem N ∅ Δ ENew (TProd (TSess S y m1 m1) (TSess (dual S) y‾ m2 m2)) (Some 0).
Proof.
  intros HΔ Hm n g γ Π φ HE. destruct (envf_unl _ _ _ _ _ _ _ HΔ HE) as [-> ->].
  simpl. by eapply new_fld_redex.
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

Lemma cost_e_app N Θ Θ1 Θ2 Θ2' Δ Δ1 Δ2 Δ2' e1 e2 ub lb c T U a1 c1 c2 :
  tsplit Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
  csem N Θ1 Δ1 e1 (TLolli ub lb c T U a1) c1 →
  thage c1 Θ2 Θ2' → lage c1 Δ2 Δ2' →
  csem N Θ2' Δ2' e2 T c2 →
  fle c2 a1 →
  csem N Θ Δ (App e1 e2) U (fadd c1 (fadd c2 c)).
Proof.
  intros Hs Hl Hc1 HaT HaD Hc2 Hc2a n g γ Π φ HE.
  destruct (envf_split _ _ _ _ _ _ _ _ _ _ _ _ Hs Hl HE) as (Π1 & Π2 & φ1 & φ2 & HdΠ & Hdφ & -> & -> & HE1 & HE2).
  change (subst γ (emap g (App e1 e2))) with
    (fill_frame ((λ γ g, FAppL (subst γ (emap g e2))) γ g) (subst γ (emap g e1))).
  eapply (csem_bind1 N Θ1 Δ1 e1 _ c1 Θ2 Θ2' Δ2 Δ2' (λ γ g, FAppL (subst γ (emap g e2))) _ _
    n g γ Π1 φ1 Π2 φ2);
    [intros g' γ0 g0; simpl; by rewrite emap_subst_g|done|exact Hc1|done|done|apply fle_fadd_l'
    |done|done|done|done|].
  intros j g' γ' Π' φ' i v Πv φv Hj Hi Hv HE' HV HdΠ' Hdφ'. simpl.
  rewrite (map_union_comm Πv Π'), (map_union_comm φv φ') by done.
  change (App v (subst γ' (emap g' e2))) with (fill_frame ((λ v, FAppR v) v) (subst γ' (emap g' e2))).
  eapply (csem_bind2 N Θ2' Δ2' e2 T c2 (λ v, FAppR v) _ _ _ _ j g' γ' Π' φ'
    v Πv φv);
    [done|intros v0 Hv0; done|exact Hc2|by apply age_arr|by apply fle_frame_mid
    |by eapply Vfuel_val|exact HE'|exact HV|by apply map_disjoint_sym|by apply map_disjoint_sym|].
  intros j2 v' Πv' φv' u Πu φu i2 Hj2 Hi2 Hu Hv' HV' HU HdΠ2 Hdφ2. simpl.
  rewrite (map_union_comm Πu Πv'), (map_union_comm φu φv') by done.
  eapply app_redex; [exact HV'|exact HU|by apply map_disjoint_sym|by apply map_disjoint_sym|].
  by apply fle_frame_app.
Qed.

Lemma cost_e_pair N Θ Θ1 Θ2 Θ2' Δ Δ1 Δ2 Δ2' e1 e2 T1 T1' T2 c1 c2 :
  tsplit Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
  csem N Θ1 Δ1 e1 T1 c1 → thage c1 Θ2 Θ2' → lage c1 Δ2 Δ2' →
  csem N Θ2' Δ2' e2 T2 c2 → tage c2 T1 T1' →
  csem N Θ Δ (Pair e1 e2) (TProd T1' T2) (fadd c1 c2).
Proof.
  intros Hs Hl Hc1 HaT HaD Hc2 Hag n g γ Π φ HE.
  destruct (envf_split _ _ _ _ _ _ _ _ _ _ _ _ Hs Hl HE) as (Π1 & Π2 & φ1 & φ2 & HdΠ & Hdφ & -> & -> & HE1 & HE2).
  change (subst γ (emap g (Pair e1 e2))) with
    (fill_frame ((λ γ g, FPairL (subst γ (emap g e2))) γ g) (subst γ (emap g e1))).
  eapply (csem_bind1 N Θ1 Δ1 e1 T1 c1 Θ2 Θ2' Δ2 Δ2' (λ γ g, FPairL (subst γ (emap g e2))) _ _
    n g γ Π1 φ1 Π2 φ2);
    [intros g' γ0 g0; simpl; by rewrite emap_subst_g|done|exact Hc1|done|done|apply fle_fadd_l'
    |done|done|done|done|].
  intros j g' γ' Π' φ' i v Πv φv Hj Hi Hv HE' HV HdΠ' Hdφ'. simpl.
  rewrite (map_union_comm Πv Π'), (map_union_comm φv φ') by done.
  change (Pair v (subst γ' (emap g' e2))) with (fill_frame ((λ v, FPairR v) v) (subst γ' (emap g' e2))).
  eapply (csem_bind2 N Θ2' Δ2' e2 T2 c2 (λ v, FPairR v) T1 T1' _ _ j g' γ' Π' φ'
    v Πv φv);
    [done|intros v0 Hv0; done|exact Hc2|exact Hag|by apply fle_frame_seq
    |by eapply Vfuel_val|exact HE'|exact HV|by apply map_disjoint_sym|by apply map_disjoint_sym|].
  intros j2 v' Πv' φv' u Πu φu i2 Hj2 Hi2 Hu Hv' HV' HU HdΠ2 Hdφ2. simpl.
  rewrite (map_union_comm Πu Πv'), (map_union_comm φu φv') by done.
  apply FuelE_val; [simpl; by rewrite andb_True|].
  apply Vfuel_pair; [by apply map_disjoint_sym|by apply map_disjoint_sym|done|done].
Qed.

Lemma cost_e_letu N Θ Θ1 Θ2 Θ2' Δ Δ1 Δ2 Δ2' e1 e2 T c1 c2 :
  tsplit Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
  csem N Θ1 Δ1 e1 TUnit c1 → thage c1 Θ2 Θ2' → lage c1 Δ2 Δ2' →
  csem N Θ2' Δ2' e2 T c2 →
  csem N Θ Δ (LetU e1 e2) T (fadd c1 c2).
Proof.
  intros Hs Hl Hc1 HaT HaD Hc2 n g γ Π φ HE.
  destruct (envf_split _ _ _ _ _ _ _ _ _ _ _ _ Hs Hl HE) as (Π1 & Π2 & φ1 & φ2 & HdΠ & Hdφ & -> & -> & HE1 & HE2).
  change (subst γ (emap g (LetU e1 e2))) with
    (fill_frame ((λ γ g, FLetU (subst γ (emap g e2))) γ g) (subst γ (emap g e1))).
  eapply (csem_bind1 N Θ1 Δ1 e1 TUnit c1 Θ2 Θ2' Δ2 Δ2' (λ γ g, FLetU (subst γ (emap g e2))) _ _
    n g γ Π1 φ1 Π2 φ2);
    [intros g' γ0 g0; simpl; by rewrite emap_subst_g|done|exact Hc1|done|done|apply fle_fadd_l'
    |done|done|done|done|].
  intros j g' γ' Π' φ' i v Πv φv Hj Hi Hv HE' HV HdΠ' Hdφ'. simpl.
  destruct (Vfuel_unit_inv _ _ _ _ _ HV) as (-> & -> & ->). rewrite !map_empty_union.
  apply (FuelE_beta _ _ _ _ _ _ [] _ (subst γ' (emap g' e2))); [constructor|constructor|]. intros j0 Hj0. simpl.
  eapply FuelE_frame_mono; [by apply fle_frame_seq|].
  apply Hc2. eapply envf_down; [|exact HE']; by apply olt_ole.
Qed.

Lemma cost_e_letp N Θ Θ1 Θ2 Θ2' Δ Δ1 Δ2 Δ2' e1 e2 T1 T2 T c1 c2 :
  tsplit Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
  csem N Θ1 Δ1 e1 (TProd T1 T2) c1 → thage c1 Θ2 Θ2' → lage c1 Δ2 Δ2' →
  csem N Θ2' (Some T2 :: Some T1 :: Δ2') e2 T c2 →
  csem N Θ Δ (LetP e1 e2) T (fadd c1 c2).
Proof.
  intros Hs Hl Hc1 HaT HaD Hc2 n g γ Π φ HE.
  destruct (envf_split _ _ _ _ _ _ _ _ _ _ _ _ Hs Hl HE) as (Π1 & Π2 & φ1 & φ2 & HdΠ & Hdφ & -> & -> & HE1 & HE2).
  change (subst γ (emap g (LetP e1 e2))) with
    (fill_frame ((λ γ g, FLetP (subst (up (up γ)) (emap g e2))) γ g) (subst γ (emap g e1))).
  eapply (csem_bind1 N Θ1 Δ1 e1 _ c1 Θ2 Θ2' Δ2 Δ2' (λ γ g, FLetP (subst (up (up γ)) (emap g e2))) _ _
    n g γ Π1 φ1 Π2 φ2);
    [intros g' γ0 g0; simpl; by rewrite emap_subst_up2|done|exact Hc1|done|done|apply fle_fadd_l'
    |done|done|done|done|].
  intros j g' γ' Π' φ' i v Πv φv Hj Hi Hv HE' HV HdΠ' Hdφ'. simpl.
  destruct (Vfuel_prod_inv _ _ _ _ _ _ _ HV) as (u & w & Πu & Πw & φu & φw & -> & Duw & Duw' & -> & -> & HU & HW).
  apply (FuelE_beta _ _ _ _ _ _ [] _ (subst2 u w (subst (up (up γ')) (emap g' e2))));
    [constructor|constructor; by eapply Vfuel_val|]. intros j0 Hj0. simpl. rewrite subst2_subst.
  apply map_disjoint_union_l in HdΠ' as [D1 D2]. apply map_disjoint_union_l in Hdφ' as [D1' D2'].
  rewrite (map_union_comm (Πu ∪ Πw) Π'), (map_union_comm (φu ∪ φw) φ'), !map_union_assoc
    by (apply map_disjoint_union_l; split; by apply map_disjoint_sym).
  eapply FuelE_frame_mono; [by apply fle_frame_seq|].
  apply Hc2.
  apply envf_cons; [apply envf_cons| | |].
  - eapply envf_down; [|exact HE']; by apply olt_ole.
  - eapply Vfuel_down; [|exact HU]; by apply olt_ole.
  - by apply map_disjoint_sym.
  - by apply map_disjoint_sym.
  - eapply Vfuel_down; [|exact HW]; by apply olt_ole.
  - apply map_disjoint_union_l. split; [by apply map_disjoint_sym|done].
  - apply map_disjoint_union_l. split; [by apply map_disjoint_sym|done].
Qed.

Lemma fle_frame_case i c0 c1 c2 : fle (Some i) c0 →
  fle c1 (fsub (fadd c0 (fmax c1 c2)) (Some i)) ∧ fle c2 (fsub (fadd c0 (fmax c1 c2)) (Some i)).
Proof. destruct c0, c1, c2; simpl; lia. Qed.

Lemma cost_e_case N Θ Θ1 Θ2 Θ2' Δ Δ1 Δ2 Δ2' e e1 e2 T1 T2 T c0 c1 c2 :
  tsplit Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
  csem N Θ1 Δ1 e (TSum T1 T2) c0 → thage c0 Θ2 Θ2' → lage c0 Δ2 Δ2' →
  csem N Θ2' (Some T1 :: Δ2') e1 T c1 →
  csem N Θ2' (Some T2 :: Δ2') e2 T c2 →
  csem N Θ Δ (Case e e1 e2) T (fadd c0 (fmax c1 c2)).
Proof.
  intros Hs Hl Hc0 HaT HaD Hc1 Hc2 n g γ Π φ HE.
  destruct (envf_split _ _ _ _ _ _ _ _ _ _ _ _ Hs Hl HE) as (Π1 & Π2 & φ1 & φ2 & HdΠ & Hdφ & -> & -> & HE1 & HE2).
  change (subst γ (emap g (Case e e1 e2))) with
    (fill_frame ((λ γ g, FCase (subst (up γ) (emap g e1)) (subst (up γ) (emap g e2))) γ g) (subst γ (emap g e))).
  eapply (csem_bind1 N Θ1 Δ1 e _ c0 Θ2 Θ2' Δ2 Δ2'
    (λ γ g, FCase (subst (up γ) (emap g e1)) (subst (up γ) (emap g e2))) _ _ n g γ Π1 φ1 Π2 φ2);
    [intros g' γ0 g0; simpl; by rewrite !emap_subst_up|done|exact Hc0|done|done|apply fle_fadd_l'
    |done|done|done|done|].
  intros j g' γ' Π' φ' i v Πv φv Hj Hi Hv HE' HV HdΠ' Hdφ'. simpl.
  destruct (fle_frame_case i c0 c1 c2 Hi) as [F1 F2].
  rewrite (map_union_comm Πv Π'), (map_union_comm φv φ') by done.
  destruct (Vfuel_sum_inv _ _ _ _ _ _ _ HV) as [(v' & -> & HV')|(v' & -> & HV')].
  - apply (FuelE_beta _ _ _ _ _ _ [] _ (subst1 v' (subst (up γ') (emap g' e1))));
      [constructor|constructor; by eapply Vfuel_val|]. intros j0 Hj0. simpl. rewrite subst1_subst.
    eapply FuelE_frame_mono; [exact F1|].
    apply Hc1.
    apply envf_cons; [(eapply envf_down; [|exact HE']; by apply olt_ole)|(eapply Vfuel_down; [|exact HV']; by apply olt_ole)
                     |by apply map_disjoint_sym|by apply map_disjoint_sym].
  - apply (FuelE_beta _ _ _ _ _ _ [] _ (subst1 v' (subst (up γ') (emap g' e2))));
      [constructor|constructor; by eapply Vfuel_val|]. intros j0 Hj0. simpl. rewrite subst1_subst.
    eapply FuelE_frame_mono; [exact F2|].
    apply Hc2.
    apply envf_cons; [(eapply envf_down; [|exact HE']; by apply olt_ole)|(eapply Vfuel_down; [|exact HV']; by apply olt_ole)
                     |by apply map_disjoint_sym|by apply map_disjoint_sym].
Qed.

(** ** Closures and boxes *)

(** E-Abs with per-end capture. The body sees the context aged by a,
    at counters at least the counters at creation minus a, at the same
    tickets. *)
Lemma cle_fminus a (φ φ' : cenv) :
  dom φ' = dom φ → (∀ o f f', φ !! o = Some f → φ' !! o = Some f' → f'.2 = f.2 ∧ fle (fsub f.1 a) f'.1) →
  cle (fminus a <$> φ) φ'.
Proof.
  intros Hd Hh o. rewrite lookup_fmap.
  destruct (φ !! o) as [f|] eqn:E; simpl.
  - assert (o ∈ dom φ') as [f' Hf']%elem_of_dom by (rewrite Hd; by eapply elem_of_dom_2).
    rewrite Hf'. destruct (Hh o f f' E Hf') as [E1 E2]. split; [exact E2|done].
  - assert (o ∉ dom φ') as Ho by (rewrite Hd; by apply not_elem_of_dom).
    apply not_elem_of_dom in Ho. by rewrite Ho.
Qed.

Lemma cost_e_abs N Θ Θh Δ Δh e T U ub lb c a :
  tfacts Θ Δ (Lam e) → thage a Θ Θh → lage a Δ Δh →
  csem N Θh (Some T :: Δh) e U c →
  csem N Θ Δ (Lam e) (TLolli ub lb c T U a) (Some 0).
Proof.
  intros Hf HcT HcD Hcs n g γ Π φ HE.
  pose proof (envf_exact _ _ _ _ _ _ _ _ _ Hf HE) as Hx. simpl in Hx |- *.
  apply FuelE_val; [done|]. apply Vfuel_eq. simpl.
  exists (subst (up γ) (emap g e)). split_and!.
  - done.
  - done.
  - by eapply envf_dom.
  - by eapply envf_age_above.
  - intros j φ' Πu φu u Hj Hdφ' Hh HdΠ Hdφ Hu. rewrite subst1_subst.
    apply Hcs.
    apply envf_cons; [|done|done|done].
    apply (envf_mono N n j _ _ _ _ _ (fminus a <$> φ) φ'); [by apply olt_ole|by apply cle_fminus|].
    by eapply envf_age.
Qed.

Lemma cost_e_box N Δ e m k C ub c U :
  tfacts ∅ Δ (EBox e) → lenv_unl Δ →
  (∀ ss, length ss = k → sinsts N ss →
     csem N ∅ (lenv_pinst (pshift m) (Some (TBox m k C ub c U) :: Δ)) e (sinst_ty (slist ss) U) c) →
  csem N ∅ Δ (EBox e) (TBox m k C ub c U) (Some 0).
Proof.
  intros Hf Hu Hcs n g γ Π φ HE.
  pose proof (envf_exact _ _ _ _ _ _ _ _ _ Hf HE) as Hx.
  destruct (envf_unl _ _ _ _ _ _ _ Hu HE) as [-> ->]. simpl in Hx |- *. rewrite dom_empty_L in Hx.
  set (eb := subst (up γ) (emap g e)). fold eb in Hx.
  apply FuelE_val; [done|].
  assert (Hlob : ∀ j, ole j n → EBox eb ∈ FV^N _ j⟦RTy (TBox m k C ub c U)⟧(∅, ∅)).
  { induction j as [j IH] using oind. intros Hj. apply Vfuel_eq. simpl.
    exists eb. split_and!; [done|done|done|done|].
    intros j' ss Hj' Hl Hss. unfold eb. rewrite subst1_subst.
    rewrite <-(map_empty_union (∅ : penv)), <-(map_empty_union (∅ : cenv)).
    apply (Hcs ss Hl Hss j' g (EBox eb .: γ)).
    assert (envf N j' ∅ (Some (TBox m k C ub c U) :: Δ) g (EBox eb .: γ) (∅ ∪ ∅) (∅ ∪ ∅)) as H.
    { assert (ole j' n) as Hj'n by exact (ole_trans _ _ _ (olt_ole _ _ Hj') Hj).
      apply envf_cons; [|apply IH; [exact Hj'|exact Hj'n]|apply map_disjoint_empty_l|apply map_disjoint_empty_l].
      apply (envf_mono N n j' _ _ _ _ _ ∅ ∅); [exact Hj'n|apply cle_refl|exact HE]. }
    apply (envf_pinst _ _ (pshift m)) in H. unfold tenv_pinst in H. rewrite fmap_empty in H. exact H. }
  apply Hlob, ole_refl.
Qed.
