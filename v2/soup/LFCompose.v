(** * The semantic composition rules of the lock-free judgment (stage S9,
      proposal §2.14, A.3)

    Σ ⊪_W p : T is the soup alone (soup/Soup.v). Its rules:

      lf_p_term    : strict W, the premises of P-Term at Some N, a guarded
                     thread, a ticket count meeting its transformer
                     ⟹ Σ ⊪_W (C0, {t}) : T
      lf_p_connect : the premises of P-Connect, at ⊪ ⟹ (Σ1 ∪ Σ2) ⊪_{W1 ⊔ W2} …

    P-Connect is one soup lemma ([lf_soup_connect]), which reads no
    strictness of the worlds. P-Join is admissible in ⊩ (soup/LFTyped.v). The world enters only through
    E[live] at P-Term. A closed thread is lock free
    ([lf_soundness_source]). *)

From stdpp Require Import relations.
From GV Require Import soup.LFAdequacy.
From GV Require Export soup.SoupCompose static.Fundamental cost.CostFund.
From GV Require Import compat.Conv.

(** ** Liftings at an interface *)

Lemma soup_lift N W Σ T a q :
  (∀ n, a ∈ S^{N,W} _ n⟦Σ ⊢ T⟧) → erase q = erase (s_q a) →
  ∃ a', s_q a' = q ∧ ∀ n, a' ∈ S^{N,W} _ n⟦Σ ⊢ T⟧.
Proof.
  destruct a as [[C1 M1] K tk], q as [C2 M2]. intros Hs Hq. unfold erase in Hq. simpl in Hq.
  injection Hq as -> HM. destruct (relabel_map M1 M2 (eq_sym HM)) as (f & g & H1 & H2).
  exists (LFState (C1, M2) (krelabel f K) (tk ∘ g)). split; [done|]. intros n.
  destruct (Hs n) as (A & Π & U & Hsi). exists A, Π, (U ∘ g).
  exact (soup_relabel _ _ _ _ _ _ M1 M2 _ _ _ _ _ f g H1 H2 Hsi).
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

Theorem lf_soup_connect W1 W2 Σ1 Σ2 ΣC C1 C2 E1 E2 T :
  (Σ1 ∪ ΣC) ⊪_W1 (C1, E1) : T → (Σ2 ∪ senv_dual ΣC) ⊪_W2 (C2, E2) : TUnit →
  (∀ o, o ∈ dom ΣC → edual o ∉ dom ΣC) →
  chans_of Σ1 ## chans_of Σ2 → chans_of Σ1 ## chans_of ΣC → chans_of Σ2 ## chans_of ΣC →
  C1 ## C2 → C1 ## chans_of Σ2 ∪ chans_of ΣC → C2 ## chans_of Σ1 ∪ chans_of ΣC →
  (Σ1 ∪ Σ2) ⊪_(wjoin W1 W2) (C1 ∪ C2 ∪ chans_of ΣC, E1 ⊎ E2) : T.
Proof.
  intros (N1 & [[C1' M1] K1 tk1] & He1 & Hs1) (N2 & a2 & He2 & Hs2) Hf H12 H1C H2C HC HC1 HC2.
  unfold erase in He1. simpl in He1. injection He1 as -> <-.
  set (k := S (max_list (elements (dom M1)))).
  destruct a2 as [[C2' M2'] K2' tk2']. unfold erase in He2. simpl in He2. injection He2 as -> <-.
  destruct (soup_lift N2 W2 _ TUnit _ (C2, tshift k M2') Hs2) as ([[C2'' M2] K2 tk2] & Hq & Hs2');
    [unfold erase; simpl; by rewrite soup_tshift|].
  simpl in Hq. injection Hq as -> ->.
  assert (M1 ##ₘ tshift k M2') as HM.
  { apply tshift_disj. intros t Ht. subst k. apply Nat.lt_succ_r, max_list_elem_of_le.
    by apply elem_of_elements. }
  exists (N1 `max` N2), (LFState (C1 ∪ C2 ∪ chans_of ΣC, M1 ∪ tshift k M2') (K1 ∪ K2) (tsel (dom M1) tk1 tk2)).
  split.
  - unfold erase. simpl. by rewrite soup_union_c, soup_tshift.
  - intros n. destruct (Hs1 n) as (A1 & Π1 & U1 & H1). destruct (Hs2' n) as (A2 & Π2 & U2 & H2).
    eexists _, _, _. by apply soup_connect.
Qed.

(** The rule P-Connect, with the premises of [p_connect]. The soup uses
    the channel conditions only. *)
Theorem lf_p_connect W1 W2 Σ1 Σ2 ΣC C1 C2 E1 E2 T :
  (Σ1 ∪ ΣC) ⊪_W1 (C1, E1) : T → (Σ2 ∪ senv_dual ΣC) ⊪_W2 (C2, E2) : TUnit →
  Σ1 ##ₘ ΣC → Σ2 ##ₘ senv_dual ΣC →
  (∀ o, o ∈ dom ΣC → (o‾)%cend ∉ dom ΣC) →
  chans_of Σ1 ## chans_of Σ2 → chans_of Σ1 ## chans_of ΣC → chans_of Σ2 ## chans_of ΣC →
  C1 ## C2 → C1 ## chans_of Σ2 ∪ chans_of ΣC → C2 ## chans_of Σ1 ∪ chans_of ΣC →
  world_wf W1 → world_wf W2 → w_fams W1 ## w_fams W2 →
  strict (W1 ⊔ W2) →
  (Σ1 ∪ Σ2) ⊪_(W1 ⊔ W2) (C1 ∪ C2 ∪ chans_of ΣC, E1 ⊎ E2) : T.
Proof. intros H1 H2 _ _ Hf H12 H1C H2C HC HC1 HC2 _ _ _ _. by apply lf_soup_connect. Qed.

(** ** P-Term *)

Theorem lf_soup_term N W Σ ΘB C0 t T tk :
  tfree T → (∀ o, o ∈ dom ΘB ↔ ech o ∈ C0) → chans_of Σ ## C0 →
  (∀ c, c ∈ C0 → ∃ S (x : point), ΘB !! (c⁺)%cend = Some (TE S x (Some N)) ∧
                                   ΘB !! (c⁻)%cend = Some (TE (dual S) (pt_dual x) (Some N))) →
  (∀ n, t ∈ E[live]^W _ n⟦tenv_erase (tenv_of (Some N) Σ ∪ ΘB) ⊢ T⟧^∅) →
  (∀ n, FuelT (Some N) n (te_sty <$> (tenv_of (Some N) Σ ∪ ΘB))
          (const (Some N) <$> (te_sty <$> (tenv_of (Some N) Σ ∪ ΘB))) tk t) →
  Σ ⊪_W (C0, {[+ t +]}) : T.
Proof.
  intros Hp HB HΣ Hd He Hf. exists N, (LFState (C0, {[0 := t]}) (kterm N (tenv_of (Some N) Σ ∪ ΘB)) (λ _, tk)).
  split.
  - unfold erase. simpl. by rewrite <-insert_empty, soup_insert, soup_empty, (left_id_L ∅ (⊎)).
  - intros n. eexists _, _, _. by apply soup_term.
Qed.

(** The thread of P-Term, typed at a finite N and guarded, in E[live]. *)
Lemma typed_live W N Θ t T a c ϑ n :
  strict W → ∅ ⊢▷ t → Θ ; hc_empty ; [] ⊢^(∅, None) _{W,N} t : T^a ▷ c ; ϑ →
  t ∈ E[live]^W _ n⟦tenv_erase Θ ⊢ T⟧^∅.
Proof.
  intros HW Hg Hty. pose proof (live_fundamental_typed _ _ _ _ _ _ _ _ _ _ HW Hty Hg (λ _, ∅) ∅
    n W ∅ Var (wext_refl _) (map_disjoint_empty_r _) eq_refl) as H.
  rewrite subst_ids, map_union_empty in H.
  assert (sf_den (λ _, ∅) ∅ (∅, None) = ∅) as E.
  { unfold sf_den. simpl. destruct (fs_bot None); set_solver. }
  rewrite E in H. apply (Erel_blind _ _ _ _ (ty_df T)); [apply ty_df_idem|].
  refine (Erel_conv _ _ _ _ _ _ _ _ _ H). intros o. unfold tenv_erase, tenv_df. rewrite !lookup_fmap.
  destruct (Θ !! o) as [te|]; constructor. split; [done|]. unfold seqv. simpl. rewrite sty_df_idem. apply sequiv_refl.
Qed.

(** The rule P-Term: the premises of [p_term] at Some N, a guarded
    thread and a ticket count meeting its transformer, in a strict world. *)
Theorem lf_p_term W N Σ ΘB C0 t T a c ϑ tk :
  strict W → tfree T →
  (∀ o, o ∈ dom ΘB ↔ ech o ∈ C0) → chans_of Σ ## C0 →
  (∀ c, c ∈ C0 → ∃ S (x : point), ΘB !! (c⁺)%cend = Some (TE S x (Some N)) ∧
                                   ΘB !! (c⁻)%cend = Some (TE (dual S) (pt_dual x) (Some N))) →
  tenv_of (Some N) Σ ∪ ΘB ; hc_empty ; [] ⊢^(∅, None) _{W,(Some N)} t : T^a ▷ c ; ϑ →
  ∅ ⊢▷ t → meets ϑ 0 tk →
  Σ ⊪_W (C0, {[+ t +]}) : T.
Proof.
  intros HW Hp HB HΣ Hd Hty Hg Hm.
  assert (∀ o te, (tenv_of (Some N) Σ ∪ ΘB) !! o = Some te → fle (te_cr te) (Some N)) as Hcr.
  { intros o te Hte. apply lookup_union_Some_raw in Hte as [Hte|[_ Hte]].
    - unfold tenv_of in Hte. apply lookup_fmap_Some in Hte as (y & <- & _). apply fle_refl.
    - assert (ech o ∈ C0) as Hc by (apply HB; by eapply elem_of_dom_2).
      destruct (Hd _ Hc) as (S & x & H1 & H2). destruct o as [c'|c']; simpl in *.
      + rewrite H1 in Hte. injection Hte as <-. apply fle_refl.
      + rewrite H2 in Hte. injection Hte as <-. apply fle_refl. }
  destruct (fsem_of_cost _ _ _ _ _ _ _ _ tk Hty Hp Hcr Hm) as [tk' Hf].
  apply (lf_soup_term N W Σ ΘB C0 t T tk'); try done.
  intros n. by eapply typed_live.
Qed.

(** ** One closed thread

    A guarded closed thread of primitive type, typed at a finite N, whose
    transformer some ticket count meets, is lock free. *)
Theorem lf_soundness_source W N t T a c ϑ tk :
  strict W → wfworld W → ∅ ⊢▷ t → tfree T →
  ∅ ; hc_empty ; [] ⊢^(∅, None) _{W,(Some N)} t : T^a ▷ c ; ϑ → meets ϑ 0 tk →
  lock_free (∅, {[+ t +]}).
Proof.
  intros HS HW Hg Hp Hty Hm.
  assert (tenv_of (Some N) ∅ ∪ ∅ = (∅ : tenv)) as E by (unfold tenv_of; by rewrite fmap_empty, map_union_empty).
  rewrite <-E in Hty.
  assert (∀ o, o ∈ dom (∅ : tenv) ↔ ech o ∈ (∅ : gset chan)) as HB by (intros o; rewrite dom_empty_L; set_solver).
  destruct (lf_p_term W N ∅ ∅ ∅ t T a c ϑ tk HS Hp HB
    ltac:(set_solver) ltac:(set_solver) Hty Hg Hm) as (N' & a' & He & Hs).
  rewrite <-He. by apply (lf_adequacy_soup N' W T a').
Qed.
