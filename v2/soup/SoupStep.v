(** * The soup along a step (stage S8, proposal §2.12)

    [lfsoup_step]: a closed soup at index n + 1 steps to a closed soup at
    index n at the updated state [lf_next]. One clock suffices: a message
    costs the sender κ(send) = 1 of its own level and the receiver
    κ(recv) = 1 of its own, and the fuel of every thread loses one level
    at every step. The proof reads, for each actor, the obligation of its
    step in E[live] and in FuelE, and keeps every other thread, renamed by
    the link substitution at a link ([Erel_rename], [FuelE_rename]). *)

From stdpp Require Import relations.
From GV Require Export soup.Sessions fuel.FuelSub.

(** ** Levels after a step *)

Lemma at_cost_E_live c n W Θ T F e :
  c ≤ 1 → at_cost_E (S n) c (Erel live) (Erel live (S n)) W Θ T F e → Erel live n W Θ T F e.
Proof.
  intros Hc [H0 H1]. destruct (decide (c = 0)) as [->|Hne].
  - eapply Erel_down; [|exact (H0 eq_refl)]. lia.
  - replace n with (S n - c) by lia. exact (H1 Hne).
Qed.

Lemma at_cost_V_live c n W Θ T v :
  c ≤ 1 → at_cost_V (S n) c (Vrel live) (Vrel live (S n)) W Θ T v → Vrel live n W Θ T v.
Proof.
  intros Hc [H0 H1]. destruct (decide (c = 0)) as [->|Hne].
  - eapply Vrel_down; [|exact (H0 eq_refl)]. lia.
  - replace n with (S n - c) by lia. exact (H1 Hne).
Qed.

(** ** Splitting an environment by a transfer set *)

Lemma split_lookup {Y : Type} (Θ ΘM Θr : gmap cend Y) (M : gset cend) o0 v :
  ΘM ##ₘ Θr → Θ = ΘM ∪ Θr → dom ΘM = M →
  (ΘM !! o0 = Some v ↔ o0 ∈ M ∧ Θ !! o0 = Some v) ∧
  (Θr !! o0 = Some v ↔ (o0 ∉ M) ∧ Θ !! o0 = Some v).
Proof.
  intros Hd -> <-. rewrite lookup_union_Some_raw, elem_of_dom.
  split; split.
  - intros H. split; [by eexists|by left].
  - intros [[w Hw] [H|[H1 H2]]]; [done|]. congruence.
  - intros H. destruct (ΘM !! o0) eqn:E.
    + exfalso. by apply (proj1 (map_disjoint_spec _ _) Hd o0 y v).
    + split; [by intros [? ?]|by right].
  - intros [Hn [H|[_ H]]]; [|done]. exfalso. apply Hn. by eexists.
Qed.

(** ** The ends of an action are held *)

Section soup.
  Context (N n : nat) (W : world) (T : ty) (a : lfstate) (A : senv) (Π : penv) (U : nat → ty).
  Context (Hs : soup_inv N n W ∅ T a A Π U).

  Lemma s_rel t e : (s_q a).2 !! t = Some e → e ∈ E[live]^W _ n⟦kres (s_K a) t A ⊢ U t⟧^∅.
  Proof. apply (sp_rel _ _ _ _ _ _ _ _ Hs). Qed.
  Lemma s_ty t e : (s_q a).2 !! t = Some e → U t = T ∨ U t = TUnit.
  Proof. apply (sp_ty _ _ _ _ _ _ _ _ Hs). Qed.
  Lemma s_fuel t e : (s_q a).2 !! t = Some e →
    e ∈ F^(Some N) _ n⟦RThread ▷ None ; 0⟧(kres (s_K a) t Π, ctrs (s_K a) t, s_tk a t).
  Proof. apply (sp_fuel _ _ _ _ _ _ _ _ Hs). Qed.
  Lemma s_pts o : snd <$> A !! o = h_pt <$> s_K a !! o.
  Proof. rewrite <-!lookup_fmap. f_equal. apply (sp_pts _ _ _ _ _ _ _ _ Hs). Qed.
  Lemma s_dom : dom Π = dom (s_K a).
  Proof. apply (sp_dom _ _ _ _ _ _ _ _ Hs). Qed.
  Lemma s_domA : dom A = dom (s_K a).
  Proof. rewrite <-(dom_fmap_L snd A), <-(dom_fmap_L h_pt (s_K a)). f_equal. apply (sp_pts _ _ _ _ _ _ _ _ Hs). Qed.
  Lemma s_owner o h : s_K a !! o = Some h → is_Some ((s_q a).2 !! h.(h_th)).
  Proof. apply (sp_owner _ _ _ _ _ _ _ _ Hs). Qed.
  Lemma s_closed o : o ∈ dom (s_K a) → ech o ∈ (s_q a).1.
  Proof. intros H. destruct (sp_closed _ _ _ _ _ _ _ _ Hs o H) as [?|Hd]; [done|]. by rewrite dom_empty_L in Hd. Qed.
  Lemma s_pair o : o ∈ dom (s_K a) → (edual o) ∈ dom (s_K a).
  Proof. intros H. apply (sp_pair _ _ _ _ _ _ _ _ Hs o H). by apply s_closed. Qed.
  Lemma s_sdual o S x S' x' : A !! o = Some (S, x) → A !! (edual o) = Some (S', x') → x' = x‾ ∧ sdual S S'.
  Proof.
    intros H1 H2. apply (sp_sdual _ _ _ _ _ _ _ _ Hs o S x S' x' H1 H2). apply s_closed.
    rewrite <-s_domA. by apply elem_of_dom_2 in H1.
  Qed.
  Lemma s_pdual o P P' : Π !! o = Some P → Π !! (edual o) = Some P' → sequiv P' (dual P).
  Proof.
    intros H1 H2. apply (sp_pdual _ _ _ _ _ _ _ _ Hs o P P' H1 H2). apply s_closed.
    rewrite <-s_dom. by apply elem_of_dom_2 in H1.
  Qed.

  (** The entry of an end in its holder's part. *)
  Lemma s_held t o v : kres (s_K a) t A !! o = Some v → ∃ h, s_K a !! o = Some h ∧ h.(h_th) = t ∧ A !! o = Some v.
  Proof. intros H. apply lookup_kres in H as [H (h & Hh & Ht)]. eauto. Qed.

  Lemma s_kpt o S x : A !! o = Some (S, x) → kpt (s_K a) o = x.
  Proof.
    intros H. pose proof (s_pts o) as Hp. rewrite H in Hp. unfold kpt.
    destruct (s_K a !! o); simpl in *; by simplify_eq.
  Qed.

  (** Two parts of different threads are disjoint. *)
  Lemma s_disj {Y : Type} (m m' : gmap cend Y) t s :
    t ≠ s → kres (s_K a) t m ##ₘ kres (s_K a) s m'.
  Proof.
    intros Hts. apply map_disjoint_spec. intros o v w H1 H2.
    apply lookup_kres in H1 as [_ (h & Hh & <-)]. apply lookup_kres in H2 as [_ (h' & Hh' & Ht')].
    rewrite Hh in Hh'. simplify_eq.
  Qed.
End soup.

Arguments s_rel {_ _ _ _ _ _ _ _} _ _ _ _.
Arguments s_ty {_ _ _ _ _ _ _ _} _ _ _ _.
Arguments s_fuel {_ _ _ _ _ _ _ _} _ _ _ _.

(** ** Fresh generated roots *)

Lemma kfresh_spec ℓ K o h : K !! o = Some h → pt_root h.(h_pt) ≠ NGen ℓ (kfresh ℓ K).
Proof.
  intros Ho Heq. apply (is_fresh (kgens ℓ K)). unfold kgens. apply elem_of_list_to_set.
  apply list_elem_of_omap. exists h. split.
  - apply list_elem_of_fmap. exists (o, h). split; [done|]. by apply elem_of_map_to_list.
  - rewrite Heq. by rewrite decide_True.
Qed.

(** ** Lookups of the update *)

Lemma lookup_ktick i j M K o :
  ktick i j M K !! o = (λ h, if decide ((h.(h_th) = i ∨ h.(h_th) = j) ∧ o ∉ M) then htick h else h) <$> K !! o.
Proof. apply lookup_kmod. Qed.

Lemma lookup_khand M j K o :
  khand M j K !! o = (λ h, if decide (o ∈ M) then Hold j h.(h_pt) (ftick h.(h_ctr)) else h) <$> K !! o.
Proof. apply lookup_kmod. Qed.

(** ** One step, case by case *)

Section step.
  Context (N n : nat) (W : world) (T : ty) (C : gset chan) (Mq : gmap nat expr) (K : own)
    (tk : nat → nat) (A : senv) (Π : penv) (U : nat → ty).
  Context (Hs : soup_inv N (S n) W ∅ T (LFState (C, Mq) K tk) A Π U).


  Lemma s_E t e : Mq !! t = Some e → e ∈ E[live]^W _ (S n)⟦kres K t A ⊢ U t⟧^∅.
  Proof. apply (s_rel Hs). Qed.
  Lemma s_F t e : Mq !! t = Some e →
    e ∈ F^(Some N) _ (S n)⟦RThread ▷ None ; 0⟧(kres K t Π, ctrs K t, tk t).
  Proof. apply (s_fuel Hs). Qed.

  (** A thread outside the step. *)
  Lemma s_other t e : Mq !! t = Some e →
    e ∈ E[live]^W _ n⟦kres K t A ⊢ U t⟧^∅ ∧
    e ∈ F^(Some N) _ n⟦RThread ▷ None ; 0⟧(kres K t Π, ctrs K t, tk t).
  Proof.
    intros He. split; [eapply Erel_down; [|exact (s_E t e He)]; lia|].
    eapply FuelE_down; [|exact (s_F t e He)]. lia.
  Qed.

  Lemma s_obl t e α e' : Mq !! t = Some e → tstep e α e' →
    Eobl live (S n) (Vrel live) (Erel live) (Vrel live (S n)) (Erel live (S n)) W (kres K t A) (U t) ∅ α e' ∧
    Fobl (Some N) (λ j N, FuelE N j) (λ j N, Vfuel N j) n RThread None 0 (kres K t Π) (ctrs K t) (tk t) α e'.
  Proof.
    intros He Hst. split; [exact (Erel_S_step live n W W _ _ _ _ _ _ (s_E t e He) (wext_refl W) Hst)|].
    exact (fuel_obl _ _ _ _ _ _ (s_F t e He) _ _ Hst).
  Qed.

  (** The state is kept and the threads are replaced. *)
  Lemma soup_keep C' Mq' tk' U' :
    C' = C →
    (∀ t, is_Some (Mq !! t) → is_Some (Mq' !! t)) →
    (∀ t e', Mq' !! t = Some e' →
       e' ∈ E[live]^W _ n⟦kres K t A ⊢ U' t⟧^∅ ∧ (U' t = T ∨ U' t = TUnit) ∧
       e' ∈ F^(Some N) _ n⟦RThread ▷ None ; 0⟧(kres K t Π, ctrs K t, tk' t)) →
    soup_inv N n W ∅ T (LFState (C', Mq') K tk') A Π U'.
  Proof.
    intros -> Hdom Ht. unfold soup_inv. constructor; simpl.
    - apply (sp_prim _ _ _ _ _ _ _ _ Hs).
    - intros t e He. apply (Ht t e He).
    - intros t e He. apply (Ht t e He).
    - intros t e He. apply (Ht t e He).
    - apply (sp_pts _ _ _ _ _ _ _ _ Hs).
    - apply (sp_dom _ _ _ _ _ _ _ _ Hs).
    - intros o h Ho. apply Hdom. exact (sp_owner _ _ _ _ _ _ _ _ Hs o h Ho).
    - apply (sp_closed _ _ _ _ _ _ _ _ Hs).
    - apply (sp_pair _ _ _ _ _ _ _ _ Hs).
    - apply (sp_sdual _ _ _ _ _ _ _ _ Hs).
    - apply (sp_pdual _ _ _ _ _ _ _ _ Hs).
    - apply (sp_sig _ _ _ _ _ _ _ _ Hs).
  Qed.

  (** P-Act-Beta. *)
  Lemma step_beta i e e' :
    Mq !! i = Some e → tstep e LBeta e' →
    soup_inv N n W ∅ T (LFState (C, <[i := e']> Mq) K tk) A Π U.
  Proof.
    intros He Hst. destruct (s_obl i e _ e' He Hst) as [HE HF]. cbn [Eobl Fobl] in HE, HF.
    unfold o_beta in HE. unfold f_beta in HF.
    apply soup_keep; [done|intros t Ht; rewrite lookup_insert_is_Some'; by right|].
    intros t e0 He0. apply lookup_insert_Some in He0 as [[<- <-]|[Hne He0]].
    - split_and!; [eapply at_cost_E_live; [|exact HE]; cbn; lia|exact (s_ty Hs i e He)|exact HF].
    - destruct (s_other t e0 He0) as [H1 H2]. split_and!; [done|exact (s_ty Hs t e0 He0)|done].
  Qed.
End step.
