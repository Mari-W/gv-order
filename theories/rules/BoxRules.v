(** * Compositionality of the rules that need the box (spec §11)

    The application of force, hence E-App for every function value, and
    E-Force, E-Exp and E-Contract (sharp edges 52). *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export rules.TermRules.

Set Default Proof Using "All".

(** ** Applying force

    force : □(∀ιs. C. ∗ ⊸^u_⊤ T) ⊸^{u[xs/ιs]}_⊤ T[xs/ιs], at an instance xs
    with C[xs/ιs] in W (sharp edges 58). Its upper point is the box's,
    instantiated, so the frame of the application is one V-Box
    accepts, and the instance meets the box's constraint. *)

Lemma Erel_app_force n W Θ ub lb T U F v2 :
  strict W → Vrel n W ∅ (TLolli ub lb T U) EForce → Vrel n W Θ T v2 → ub_below W ub F →
  Erel n W Θ U F (App EForce v2).
Proof.
  intros HW HV1 HV2 Hub.
  destruct (konst_app_inv _ _ _ _ _ _ _ _ _ _ (proj1 HW) HV1 HV2)
    as (_ & ub0 & lb0 & A & B & Hk & Hu & HB & HV).
  inversion Hk as [| | | | | | | | |m kk C1 ub1 T1 xs ss Hxs HC1 HK1 Hss Hsc]; subst.
  apply Vrel_box_thunk_iff in HV as (-> & eb & -> & Hfc & HK).
  destruct n as [|n']; [apply Erel_0|].
  apply (Erel_det_beta_S _ _ _ _ _ _ (subst1 (EBox eb) eb)).
  - by apply TStepHead, HeadForce.
  - intros α e'' Hst. apply app_val_step in Hst; [|done|done]. by inversion Hst.
  - eapply Erel_tconv; [apply HW|exact HB|].
    apply (HK W n' xs ss F); [by apply wext_refl|lia|done|done|done|done|done|].
    eapply ub_below_conv; [apply HW| |exact Hub]. by apply opt_rel_sym; [apply HW|].
Qed.

(** Every function value. *)
Lemma Erel_app n W Θ Θ1 Θ2 ub lb T U F v1 v2 :
  strict W → tenv_comp (w_eq W) Θ Θ1 Θ2 →
  Vrel n W Θ1 (TLolli ub lb T U) v1 → Vrel n W Θ2 T v2 → ub_below W ub F →
  Erel n W Θ U F (App v1 v2).
Proof.
  intros HW Hc HV1 HV2 Hub.
  destruct (decide (v1 = EForce)) as [->|Hnf]; [|by eapply Erel_app_noforce].
  pose proof (wf_eq_sym _ (proj1 HW)) as Hs.
  destruct (proj1 (Vrel_lolli_iff _ _ _ _ _ _ _ _) HV1) as [(eb & ? & _)|(k & T0 & _ & -> & _)];
    [done|].
  apply (tenv_comp_empty_l_inv _ _ _ Hs) in Hc as ->. by eapply Erel_app_force.
Qed.

Lemma app_good_all ub lb T U : app_good ub lb T U.
Proof. intros n W Θ Θ1 Θ2 F v1 v2 HW Hc HV1 HV2 Hub. by eapply Erel_app. Qed.

(** ** E-App *)

Lemma sem_typed_app W Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 ub lb T U :
  tenv_comp (w_eq W) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 → ub_below W ub F →
  sem_typed W Θ1 Δ1 (F ∪ (tenv_heads Θ2 ∪ lenv_heads Δ2)) e1 (TLolli ub lb T U) →
  sem_typed W Θ2 Δ2 (F ∪ opt_heads lb) e2 T →
  sem_typed W Θ Δ F (App e1 e2) U.
Proof. apply sem_typed_app_gen, app_good_all. Qed.

(** ** E-Force: force applied to a box, at an instance xs whose upper
    point lies below the frame. *)

Definition lenv_nones (Δ : lenv) : lenv := (λ _, None) <$> Δ.

Lemma lenv_empty_nones Δ : lenv_empty (lenv_nones Δ).
Proof. intros o (?&->&?)%list_elem_of_fmap. done. Qed.

Lemma lenv_split_nones_l Δ : lenv_split Δ (lenv_nones Δ) Δ.
Proof.
  induction Δ as [|[T|] Δ IH]; unfold lenv_nones; simpl; constructor; auto.
Qed.

Lemma sem_typed_force W Θ Δ F e m k C ub T xs ss :
  world_wf W → length xs = m → bcs_hold (w_eq W) (w_lt W) C xs → Forall (pt_known W) xs →
  length ss = k → Forall hcontractive ss →
  ub_below W (pt_inst (plist xs) <$> ub) F →
  sem_typed W Θ Δ F e (TBox m k C (TLolli ub None TUnit T)) →
  sem_typed W Θ Δ F (App EForce e) (sinst_ty (slist ss) (ty_inst xs T)).
Proof.
  intros HW Hxs HC HK Hss Hsc Hub He.
  eapply (sem_typed_app W Θ ∅ Θ Δ (lenv_nones Δ) Δ F _ _ _ None).
  - apply tenv_comp_empty_l, (wf_eq_sym _ HW).
  - apply lenv_split_nones_l.
  - exact Hub.
  - apply sem_typed_konst; [apply lenv_empty_nones|]. by constructor.
  - simpl. by rewrite union_empty_r_L.
Qed.

(** ** E-Contract: two copies of an unlimited hypothesis merge
    (t[x/y] = rename pred t). *)

Lemma grounding_contract n W Θ Δ U γ :
  world_wf W → unlimited U → grounding n W Θ (Some U :: Δ) γ →
  grounding n W Θ (Some U :: Some U :: Δ) (λ x, γ (pred x)).
Proof.
  intros HW Hu Hg. pose proof Hg as Hg0. simpl in Hg.
  destruct Hg as (Θ1 & Θ2 & Hc & HV & _).
  pose proof (Vrel_unl_empty _ _ _ _ _ Hu HV) as ->.
  exists ∅, Θ. split_and!.
  - apply tenv_comp_empty_l, (wf_eq_sym _ HW).
  - exact HV.
  - eapply grounding_ext; [|exact Hg0]. by intros [|i].
Qed.

Lemma sem_typed_contract W Θ Δ U F e T :
  unlimited U →
  sem_typed W Θ (Some U :: Some U :: Δ) F e T →
  sem_typed W Θ (Some U :: Δ) F (rename pred e) T.
Proof.
  intros Hu He n W' Θ' Θ'' γ HW Hc Hg. rewrite subst_rename.
  apply (He n W' Θ' Θ'' (λ x, γ (pred x))); [done|done|].
  apply grounding_contract; [exact (wext_wf _ _ HW)|done|done].
Qed.

(** ** E-Exp

    The body is good, in every later world, at every instance xs of the
    box's point variables that meets its constraint C (sharp edges 58),
    and under every frame above the instantiated upper point (sharp
    edges 52). The box is then a value at every
    index, by induction on the index (the recursive occurrence is the
    box itself, one level down). *)

Lemma grounding_unl n W Θ Δ γ : world_wf W → lenv_unl Δ → grounding n W Θ Δ γ → Θ = ∅.
Proof.
  intros HW. revert Θ γ. induction Δ as [|[T|] Δ IH]; intros Θ γ Hu Hg; simpl in *.
  - done.
  - destruct Hg as (Θ1 & Θ2 & Hc & HV & Hg).
    destruct (Hu (Some T)) as [?|(U & [= <-] & HU)]; [by left|done|].
    rewrite (Vrel_unl_empty _ _ _ _ _ HU HV) in Hc.
    apply (tenv_comp_empty_l_inv _ _ _ (wf_eq_sym _ HW)) in Hc as ->.
    apply (IH _ (γ ∘ S)); [|done]. intros o Ho. apply Hu. by right.
  - apply (IH _ (γ ∘ S)); [|done]. intros o Ho. apply Hu. by right.
Qed.

Lemma sem_typed_box W Δ F e m k C ub T :
  lenv_unl Δ → term_wf ∅ (Some (TBox m k C (TLolli ub None TUnit T)) :: Δ) e →
  (∀ W1 xs ss F', wext W W1 → length xs = m → length ss = k → Forall hcontractive ss →
     bcs_hold (w_eq W1) (w_lt W1) C xs →
     Forall (pt_known W1) xs → ub_below W1 (pt_inst (plist xs) <$> ub) F' →
     sem_typed W1 ∅ (Some (TBox m k C (TLolli ub None TUnit T)) :: Δ) F' e
       (sinst_ty (slist ss) (ty_inst xs T))) →
  sem_typed W ∅ Δ F (EBox e) (TBox m k C (TLolli ub None TUnit T)).
Proof.
  intros Hu (Hfc & Hfv & _) He n W' Θ' Θ'' γ HW Hc Hg. simpl.
  pose proof (wext_wf _ _ HW) as HW'.
  pose proof (grounding_unl _ _ _ _ _ HW' Hu Hg) as ->.
  apply tenv_comp_empty_inv in Hc as ->.
  apply Vrel_Erel.
  assert (fchans (subst (up γ) e) = ∅) as Hfc'.
  { assert (fchans (subst (up γ) e) ⊆ fchans e ∪ dom (∅ : tenv)) as Hsub.
    { apply fchans_subst. eapply allfv_mono; [|exact Hfv]. intros [|x]; simpl.
      - intros _. set_solver.
      - intros (T' & Hx). unfold compose. rewrite fchans_rename. by eapply grounding_fchans. }
    rewrite Hfc, dom_empty_L in Hsub. set_solver. }
  assert (∀ j W2, j ≤ n → wext W' W2 →
            Vrel j W2 ∅ (TBox m k C (TLolli ub None TUnit T)) (EBox (subst (up γ) e))) as Hbox.
  { induction j as [j IHj] using lt_wf_ind. intros W2 Hj HW2.
    apply Vrel_box_thunk_iff. split; [done|]. exists (subst (up γ) e). split_and!; [done|done|].
    intros W3 i xs ss F' HW3 Hi Hxs Hss Hsc HC HKn Hub. rewrite subst1_subst.
    pose proof (wext_trans _ _ _ HW2 HW3) as HW23.
    pose proof (wext_trans _ _ _ HW HW23) as HWW3.
    apply (He W3 xs ss F' HWW3 Hxs Hss Hsc HC HKn Hub i W3 ∅ ∅).
    - apply wext_refl, HWW3.
    - apply tenv_comp_empty_r.
    - exists ∅, ∅. split_and!.
      + apply tenv_comp_empty_r.
      + apply (IHj i Hi W3); [lia|exact HW23].
      + eapply grounding_ext;
          [|eapply grounding_down; [|eapply grounding_mono; [exact HW'|exact HW23|exact Hg]]];
          [done|lia]. }
  apply Hbox; [done|]. apply wext_refl, HW.
Qed.

(** ** E-Pack and E-Open (∃ι. C. T, sharp edges 73) *)

Lemma w_le_trans W x y z : world_wf W → w_le W x y → w_le W y z → w_le W x z.
Proof.
  intros HW [H1|H1] [H2|H2].
  - left. by eapply (wf_eq_trans _ HW).
  - right. eapply (wf_lt_eq _ HW); [exact H1|exact H2|apply (wf_eq_refl _ HW)].
  - right. eapply (wf_lt_eq _ HW); [apply (wf_eq_refl _ HW)|exact H1|exact H2].
  - right. by eapply (wf_lt_trans _ HW).
Qed.

(** E is closed under any inclusion of V that holds in every later
    world at every lower index. *)
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
  destruct α as [|[c w|c w|c|cd|c i|c i]|c|w]; simpl in Hstep |- *.
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
  - destruct Hstep as (Θr & s1 & s2 & k & Θ' & ? & ? & HE').
    exists Θr, s1, s2, k, Θ'. split_and!; [done..|]. exact (proj2 HE' T' HW HV).
  - destruct Hstep as (Θr & s1 & s2 & k & Θ' & ? & ? & HE').
    exists Θr, s1, s2, k, Θ'. split_and!; [done..|].
    eapply HEj; [lia|by apply wext_refl|exact HE'].
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
    and lie above the lower point, has type ∃ιs. C. T. *)
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
      destruct (Hab k e0 Hk) as (h & Hh & Hle). eapply w_le_trans; [done| |exact Hle]. by apply Hlb2.
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
