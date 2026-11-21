(** * The semantic composition rules of the lock-free judgment (stage S9,
      proposal §2.14, A.3)

    Σ ⊪^N _ W p : T is the soup alone (soup/Soup.v). Its rules:

      lf_p_term    : R ⊨ W, the premises of P-Term at Some N, a guarded
                     thread
                     ⟹ Σ ⊪^N _ R (C0, {t}) : T
      lf_p_connect : the premises of P-Connect, at ⊪^N ⟹ (Σ1 ∪ Σ2) ⊪^N _R …

    P-Connect is one soup lemma ([lf_soup_connect]) at one ranked world. The world enters only through
    E[live] at P-Term. A closed thread is lock free
    ([lf_soundness_source]). *)

From stdpp Require Import relations.
From GV Require Import soup.LFAdequacy.
From GV Require Export soup.SoupCompose static.Fundamental cost.CostFund.
From GV Require Import compat.Conv.

(** ** Liftings at an interface *)

Lemma soup_lift1 N W Σ T a q n :
  a ∈ S^{N,W} _ n⟦Σ ⊢ T⟧ → erase q = erase (s_q a) →
  ∃ a', s_q a' = q ∧ s_W a' = s_W a ∧ a' ∈ S^{N,W} _ n⟦Σ ⊢ T⟧.
Proof.
  destruct a as [[C1 M1] K Wa], q as [C2 M2]. intros Hs Hq. unfold erase in Hq. simpl in Hq.
  injection Hq as -> HM. destruct (relabel_map M1 M2 (eq_sym HM)) as (f & g & H1 & H2).
  exists (LFState (C1, M2) (krelabel f K) Wa). split; [done|]. split; [done|].
  destruct Hs as (HW & A & Π & U & Hsi). split; [done|]. exists A, Π, (U ∘ g).
  exact (soup_relabel _ _ _ _ _ _ M1 M2 _ _ _ _ _ _ f g H1 H2 Hsi).
Qed.

Lemma soup_lift N W Σ T a q :
  (∀ n, a ∈ S^{N,W} _ n⟦Σ ⊢ T⟧) → erase q = erase (s_q a) →
  ∃ a', s_q a' = q ∧ ∀ n, a' ∈ S^{N,W} _ n⟦Σ ⊢ T⟧.
Proof.
  destruct a as [[C1 M1] K Wa], q as [C2 M2]. intros Hs Hq. unfold erase in Hq. simpl in Hq.
  injection Hq as -> HM. destruct (relabel_map M1 M2 (eq_sym HM)) as (f & g & H1 & H2).
  exists (LFState (C1, M2) (krelabel f K) Wa). split; [done|]. intros n.
  destruct (Hs n) as (HW & A & Π & U & Hsi). split; [done|]. exists A, Π, (U ∘ g).
  exact (soup_relabel _ _ _ _ _ _ M1 M2 _ _ _ _ _ _ f g H1 H2 Hsi).
Qed.

(** Thread identifiers shifted by k. *)
Definition tshift (k : nat) (M : gmap nat expr) : gmap nat expr := kmap (λ t, t + k) M.

Local Instance add_r_inj (k : nat) : base.Inj eq eq (λ t : nat, t + k).
Proof. intros x y H. lia. Qed.

Lemma soup_tshift k M : soup (tshift k M) = soup M.
Proof.
  unfold tshift. induction M as [|i e M Hi IH] using map_ind.
  - by rewrite kmap_empty.
  - assert (kmap (λ t, t + k) M !! (i + k) = None) as Hn by (apply lookup_kmap_None; [apply _|]; intros i' Hi'; assert (i' = i) as -> by lia; done).
    rewrite kmap_insert; [|apply _]. rewrite (soup_insert _ (i + k)), (soup_insert M i); [|done|done]. by rewrite IH.
Qed.

Lemma tshift_disj k (M1 M2 : gmap nat expr) : (∀ t, t ∈ dom M1 → t < k) → M1 ##ₘ tshift k M2.
Proof.
  intros Hk. apply map_disjoint_dom. intros t H1 H2. unfold tshift in H2.
  apply elem_of_dom in H2 as [e He]. apply lookup_kmap_Some in He as (i & -> & _); [|apply _].
  specialize (Hk _ H1). lia.
Qed.

Lemma soup_union_c M1 M2 : M1 ##ₘ M2 → soup (M1 ∪ M2) = soup M1 ⊎ soup M2.
Proof.
  induction M1 as [|i e M1 Hi IH] using map_ind; intros Hd.
  - by rewrite (left_id_L ∅ (∪)), soup_empty, (left_id_L ∅ (⊎)).
  - apply map_disjoint_insert_l in Hd as [Hi2 Hd]. rewrite <-insert_union_l.
    rewrite !soup_insert; [|done|by rewrite lookup_union, Hi, Hi2]. rewrite IH by done. multiset_solver.
Qed.

(** ** P-Connect and P-Join *)

Theorem lf_soup_connect N W Σ1 Σ2 ΣC C1 C2 E1 E2 T :
  (Σ1 ∪ ΣC) ⊪^N _ W (C1, E1) : T → (Σ2 ∪ senv_dual ΣC) ⊪^N _ W (C2, E2) : TUnit →
  (∀ o, o ∈ dom ΣC → edual o ∉ dom ΣC) →
  chans_of Σ1 ## chans_of Σ2 → chans_of Σ1 ## chans_of ΣC → chans_of Σ2 ## chans_of ΣC →
  C1 ## C2 → C1 ## chans_of Σ2 ∪ chans_of ΣC → C2 ## chans_of Σ1 ∪ chans_of ΣC →
  (Σ1 ∪ Σ2) ⊪^N _ W (C1 ∪ C2 ∪ chans_of ΣC, E1 ⊎ E2) : T.
Proof.
  intros Hl1 Hl2 Hf H12 H1C H2C HC HC1 HC2 n.
  destruct (Hl1 n) as ([[C1' M1] K1 Wa1] & He1 & HW1 & Hs1). destruct (Hl2 n) as (a2 & He2 & HW2 & Hs2).
  unfold erase in He1. simpl in He1. injection He1 as -> <-. simpl in HW1. subst Wa1.
  set (k := S (max_list (elements (dom M1)))).
  destruct a2 as [[C2' M2'] K2' Wa2]. unfold erase in He2. simpl in He2. injection He2 as -> <-.
  simpl in HW2. subst Wa2.
  destruct (soup_lift1 N W _ TUnit _ (C2, tshift k M2') n Hs2) as ([[C2'' M2] K2 Wa2] & Hq & HWq & Hs2');
    [unfold erase; simpl; by rewrite soup_tshift|].
  simpl in Hq, HWq. injection Hq as -> ->. subst Wa2.
  assert (M1 ##ₘ tshift k M2') as HM.
  { apply tshift_disj. intros t Ht. subst k. apply Nat.lt_succ_r, max_list_elem_of_le.
    by apply elem_of_elements. }
  exists (LFState (C1 ∪ C2 ∪ chans_of ΣC, M1 ∪ tshift k M2') (K1 ∪ K2) W).
  split; [|split; [done|]].
  - unfold erase. simpl. by rewrite soup_union_c, soup_tshift.
  - destruct Hs1 as (_ & A1 & Π1 & U1 & H1). destruct Hs2' as (_ & A2 & Π2 & U2 & H2).
    simpl in H1, H2. split; [apply wext_refl|].
    eexists _, _, _. eapply soup_connect; [exact H1|exact H2|done..].
Qed.

(** The rule P-Connect, with the premises of [p_connect]. The soup uses
    the channel conditions only. *)
Theorem lf_p_connect N W Σ1 Σ2 ΣC C1 C2 E1 E2 T :
  (Σ1 ∪ ΣC) ⊪^N _ W (C1, E1) : T → (Σ2 ∪ senv_dual ΣC) ⊪^N _ W (C2, E2) : TUnit →
  Σ1 ##ₘ ΣC → Σ2 ##ₘ senv_dual ΣC →
  (∀ o, o ∈ dom ΣC → (o‾)%cend ∉ dom ΣC) →
  chans_of Σ1 ## chans_of Σ2 → chans_of Σ1 ## chans_of ΣC → chans_of Σ2 ## chans_of ΣC →
  C1 ## C2 → C1 ## chans_of Σ2 ∪ chans_of ΣC → C2 ## chans_of Σ1 ∪ chans_of ΣC →
  (Σ1 ∪ Σ2) ⊪^N _ W (C1 ∪ C2 ∪ chans_of ΣC, E1 ⊎ E2) : T.
Proof. intros H1 H2 _ _ Hf H12 H1C H2C HC HC1 HC2. by apply lf_soup_connect. Qed.

(** ** P-Term *)

Theorem lf_soup_term N W Σ ΘB C0 t T :
  tfree T → (∀ o, o ∈ dom ΘB ↔ ech o ∈ C0) → chans_of Σ ## C0 →
  (∀ c, c ∈ C0 → ∃ S (x : point) m m', tsum_ok (Some N) m m' ∧
     ΘB !! (c⁺)%cend = Some (TE S x m m) ∧ ΘB !! (c⁻)%cend = Some (TE (dual S) (pt_dual x) m' m')) →
  (∀ n, t ∈ E[live]^W _ n⟦tenv_erase (tenv_of (fhalf (Some N)) Σ ∪ ΘB) ⊢ T⟧^∅) →
  (∀ n, FuelT (Some N) n (te_sty <$> (tenv_of (fhalf (Some N)) Σ ∪ ΘB))
          (tkenv (tenv_of (fhalf (Some N)) Σ ∪ ΘB)) t) →
  Σ ⊪^N _ W (C0, {[+ t +]}) : T.
Proof.
  intros Hp HB HΣ Hd He Hf n. exists (LFState (C0, {[0 := t]}) (kterm (tenv_of (fhalf (Some N)) Σ ∪ ΘB)) W).
  split; [|split; [done|]].
  - unfold erase. simpl. by rewrite <-insert_empty, soup_insert, soup_empty, (left_id_L ∅ (⊎)).
  - split; [apply wext_refl|]. eexists _, _, _. by apply soup_term.
Qed.

(** The thread of P-Term, typed at a finite N and guarded, in E[live]. *)
Lemma typed_live W R N Θ t T c n :
  sworld_wf W → ∅ ⊢▷ t → Θ ; hc_empty ; [] ⊢^(∅, None) _{W,N} t : T ▷ c → wmodels R W →
  t ∈ E[live]^R _ n⟦tenv_erase Θ ⊢ T⟧^∅.
Proof.
  intros HW Hg Hty HR. pose proof (live_fundamental_typed _ _ _ _ _ _ _ _ _ HW Hty Hg HR ∅ ∅ ltac:(by intros u Hu)
    n R ∅ Var (wext_refl _) (map_disjoint_empty_r _) eq_refl) as H.
  rewrite subst_ids, map_union_empty in H.
  assert (sf_den ∅ ∅ (∅, None) = ∅) as E.
  { unfold sf_den. simpl. destruct (fs_bot None); set_solver. }
  rewrite E in H. apply (Erel_blind _ _ _ _ (ty_df T)); [apply ty_df_idem|].
  refine (Erel_conv _ _ _ _ _ _ _ _ _ H). intros o. unfold tenv_erase, tenv_df. rewrite !lookup_fmap.
  destruct (Θ !! o) as [te|]; constructor. split; [done|]. unfold seqv. simpl. rewrite sty_df_idem. apply sequiv_refl.
Qed.

(** The rule P-Term: the premises of [p_term] at Some N and a guarded
    thread, read at a ranked world R that models the static world W. *)
Theorem lf_p_term W R N Σ ΘB C0 t T c :
  sworld_wf W → wmodels R W → tfree T →
  (∀ o, o ∈ dom ΘB ↔ ech o ∈ C0) → chans_of Σ ## C0 →
  (∀ c, c ∈ C0 → ∃ S (x : point) m m', tsum_ok (Some N) m m' ∧
     ΘB !! (c⁺)%cend = Some (TE S x m m) ∧ ΘB !! (c⁻)%cend = Some (TE (dual S) (pt_dual x) m' m')) →
  tenv_of (fhalf (Some N)) Σ ∪ ΘB ; hc_empty ; [] ⊢^(∅, None) _{W,(Some N)} t : T ▷ c →
  ∅ ⊢▷ t →
  Σ ⊪^N _ R (C0, {[+ t +]}) : T.
Proof.
  intros HW HR Hp HB HΣ Hd Hty Hg.
  assert (cr_tk (tenv_of (fhalf (Some N)) Σ ∪ ΘB)) as Hcr.
  { intros o te Hte. apply lookup_union_Some_raw in Hte as [Hte|[_ Hte]].
    - unfold tenv_of in Hte. apply lookup_fmap_Some in Hte as (y & <- & _). apply fle_refl.
    - assert (ech o ∈ C0) as Hc by (apply HB; by eapply elem_of_dom_2).
      destruct (Hd _ Hc) as (S & x & m & m' & _ & H1 & H2). destruct o as [c'|c']; simpl in *.
      + rewrite H1 in Hte. injection Hte as <-. apply fle_refl.
      + rewrite H2 in Hte. injection Hte as <-. apply fle_refl. }
  pose proof (fsem_of_cost _ _ _ _ _ _ Hty Hp Hcr) as Hf.
  apply (lf_soup_term N R Σ ΘB C0 t T); try done.
  intros n. by eapply (typed_live W).
Qed.

(** ** One closed thread

    A guarded closed thread of primitive type, typed at a finite N, is
    lock free, under excluded middle and functional choice. *)
Theorem lf_soundness_source (EM : excluded_middle) (FC : functional_choice) W N t T c :
  sworld_wf W → swf W → ∅ ⊢▷ t → tfree T →
  ∅ ; hc_empty ; [] ⊢^(∅, None) _{W,(Some N)} t : T ▷ c →
  lock_free (∅, {[+ t +]}).
Proof.
  intros Hwf HW Hg Hp Hty. destruct (wmodels_exists W Hwf HW) as [R HR].
  assert (tenv_of (fhalf (Some N)) ∅ ∪ ∅ = (∅ : tenv)) as E by (unfold tenv_of; by rewrite fmap_empty, map_union_empty).
  rewrite <-E in Hty.
  assert (∀ o, o ∈ dom (∅ : tenv) ↔ ech o ∈ (∅ : gset chan)) as HB by (intros o; rewrite dom_empty_L; set_solver).
  apply (lf_adequacy EM FC N R T).
  exact (lf_p_term W R N ∅ ∅ ∅ t T c Hwf HR Hp HB ltac:(set_solver) ltac:(set_solver) Hty Hg).
Qed.
