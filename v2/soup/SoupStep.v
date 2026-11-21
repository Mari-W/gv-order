(** * The soup along a step (stage S8, proposal §2.12)

    [lfsoup_step]: a closed soup at index n + 1 steps to a closed soup at
    index n at the updated state [lf_next]. One clock suffices: a message
    costs the sender κ(send) = 1 of its own level and the receiver
    κ(recv) = 1 of its own, and the fuel of every thread loses one level
    at every step. The proof reads, for each actor, the obligation of its
    step in E[live] and in FuelE, and keeps every other thread, renamed by
    the link substitution at a link ([Erel_rename], [FuelE_rename]). *)

From stdpp Require Import relations.
From GV Require Export soup.Sessions fuel.FuelSub compat.Redex compat.Rename.

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

(** ** Splitting an environment by the moved ends *)

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

(** The entry of an end in its holder's part. *)
Lemma s_held {Y : Type} (K : own) t (m : gmap cend Y) o v :
  kres K t m !! o = Some v → ∃ h, K !! o = Some h ∧ h.(h_th) = t ∧ m !! o = Some v.
Proof. intros H. apply lookup_kres in H as [H (h & Hh & Ht)]. eauto. Qed.

(** ** The clauses of one soup *)

Section soup.
  Context (N n : nat) (W : world) (T : ty) (a : lfstate) (A : senv) (Π : penv) (U : nat → ty).
  Context (Hs : soup_inv N n W ∅ T a A Π U).

  Lemma s_rel t e : (s_q a).2 !! t = Some e → e ∈ E[live]^W _ n⟦kres (s_K a) t A ⊢ U t⟧^∅.
  Proof. apply (sp_rel _ _ _ _ _ _ _ _ _ Hs). Qed.
  Lemma s_ty t e : (s_q a).2 !! t = Some e → U t = T ∨ U t = TUnit.
  Proof. apply (sp_ty _ _ _ _ _ _ _ _ _ Hs). Qed.
  Lemma s_fuel t e : (s_q a).2 !! t = Some e →
    e ∈ F^(Some N) _ n⟦RThread ▷ None⟧(kres (s_K a) t Π, ctrs (s_K a) t).
  Proof. apply (sp_fuel _ _ _ _ _ _ _ _ _ Hs). Qed.
  Lemma s_pts o : snd <$> A !! o = h_pt <$> s_K a !! o.
  Proof. rewrite <-!lookup_fmap. f_equal. apply (sp_pts _ _ _ _ _ _ _ _ _ Hs). Qed.
  Lemma s_dom : dom Π = dom (s_K a).
  Proof. apply (sp_dom _ _ _ _ _ _ _ _ _ Hs). Qed.
  Lemma s_domA : dom A = dom (s_K a).
  Proof. rewrite <-(dom_fmap_L snd A), <-(dom_fmap_L h_pt (s_K a)). f_equal. apply (sp_pts _ _ _ _ _ _ _ _ _ Hs). Qed.
  Lemma s_owner o h : s_K a !! o = Some h → is_Some ((s_q a).2 !! h.(h_th)).
  Proof. apply (sp_owner _ _ _ _ _ _ _ _ _ Hs). Qed.
  Lemma s_closed o : o ∈ dom (s_K a) → ech o ∈ (s_q a).1.
  Proof. intros H. destruct (sp_closed _ _ _ _ _ _ _ _ _ Hs o H) as [?|Hd]; [done|]. by rewrite dom_empty_L in Hd. Qed.
  Lemma s_pair o : o ∈ dom (s_K a) → (edual o) ∈ dom (s_K a).
  Proof. intros H. apply (sp_pair _ _ _ _ _ _ _ _ _ Hs o H). by apply s_closed. Qed.
  Lemma s_sdual o S x S' x' : A !! o = Some (S, x) → A !! (edual o) = Some (S', x') → x' = pt_dual x ∧ sdual S S'.
  Proof.
    intros H1 H2. apply (sp_sdual _ _ _ _ _ _ _ _ _ Hs o S x S' x' H1 H2). apply s_closed.
    rewrite <-s_domA. by apply elem_of_dom_2 in H1.
  Qed.
  Lemma s_pdual o P P' : Π !! o = Some P → Π !! (edual o) = Some P' → sequiv P' (dual P).
  Proof.
    intros H1 H2. apply (sp_pdual _ _ _ _ _ _ _ _ _ Hs o P P' H1 H2). apply s_closed.
    rewrite <-s_dom. by apply elem_of_dom_2 in H1.
  Qed.


  Lemma s_cap o h : s_K a !! o = Some h → fle h.(h_ctr) h.(h_cap) ∧ fle h.(h_cap) (Some N).
  Proof. apply (sp_cap _ _ _ _ _ _ _ _ _ Hs). Qed.
  Lemma s_tsum o h h' : s_K a !! o = Some h → s_K a !! edual o = Some h' → tsum_ok (Some N) h.(h_cap) h'.(h_cap).
  Proof.
    intros H1 H2. apply (sp_tsum _ _ _ _ _ _ _ _ _ Hs o h h' H1 H2). apply s_closed. by apply elem_of_dom_2 in H1.
  Qed.
  Lemma s_kcfin : kcfin (s_K a).
  Proof. intros o h Ho. destruct (s_cap o h Ho) as [_ H]. destruct (h_cap h); [by eexists|done]. Qed.

  Lemma s_kpt o S x : A !! o = Some (S, x) → kpt (s_K a) o = x.
  Proof.
    intros H. pose proof (s_pts o) as Hp. rewrite H in Hp. unfold kpt.
    destruct (s_K a !! o); simpl in *; by simplify_eq.
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

Lemma lookup_khand M j K o :
  khand M j K !! o = (λ h, if decide (o ∈ M) then Hold j h.(h_pt) (ftick h.(h_ctr)) h.(h_cap) else h) <$> K !! o.
Proof. apply lookup_kmod. Qed.


(** The two invariants on tickets, for a whole map. *)
Definition kcap_ok (N : fuel) (K : own) : Prop :=
  ∀ o h, K !! o = Some h → fle h.(h_ctr) h.(h_cap) ∧ fle h.(h_cap) N.
Definition ktsum_ok (N : fuel) (K : own) : Prop :=
  ∀ o h h', K !! o = Some h → K !! edual o = Some h' → tsum_ok N h.(h_cap) h'.(h_cap).

(** A change of entries that keeps the tickets and lowers no counter
    above them keeps both invariants. *)
Lemma kcap_ok_kmod N f K :
  (∀ o h, (f o h).(h_cap) = h.(h_cap) ∧ fle (f o h).(h_ctr) h.(h_ctr)) → kcap_ok N K → kcap_ok N (kmod f K).
Proof.
  intros Hf HK o h Ho. rewrite lookup_kmod in Ho. apply fmap_Some in Ho as (h0 & Ho & ->).
  destruct (Hf o h0) as [E L]. rewrite E. destruct (HK o h0 Ho) as [H1 H2]. split; [by eapply fle_trans|done].
Qed.

Lemma ktsum_ok_kmod N f K :
  (∀ o h, (f o h).(h_cap) = h.(h_cap)) → ktsum_ok N K → ktsum_ok N (kmod f K).
Proof.
  intros Hf HK o h h' Ho Ho'. rewrite lookup_kmod in Ho, Ho'.
  apply fmap_Some in Ho as (h0 & Ho & ->). apply fmap_Some in Ho' as (h1 & Ho' & ->).
  rewrite !Hf. exact (HK o h0 h1 Ho Ho').
Qed.

Lemma fle_ftick_le f : fle (ftick f) f.
Proof. destruct f; simpl; [lia|done]. Qed.

Lemma kcap_ok_ktick N i j M K : kcap_ok N K → kcap_ok N (ktick i j M K).
Proof. apply kcap_ok_kmod. intros o h. case_decide; simpl; split; auto using fle_refl, fle_ftick_le. Qed.
Lemma ktsum_ok_ktick N i j M K : ktsum_ok N K → ktsum_ok N (ktick i j M K).
Proof. apply ktsum_ok_kmod. intros o h. by case_decide. Qed.
Lemma kcap_ok_khand N M j K : kcap_ok N K → kcap_ok N (khand M j K).
Proof. apply kcap_ok_kmod. intros o h. case_decide; simpl; split; auto using fle_refl, fle_ftick_le. Qed.
Lemma ktsum_ok_khand N M j K : ktsum_ok N K → ktsum_ok N (khand M j K).
Proof. apply ktsum_ok_kmod. intros o h. by case_decide. Qed.

Lemma kcap_ok_delete N o K : kcap_ok N K → kcap_ok N (delete o K).
Proof. intros HK o' h Ho. apply lookup_delete_Some in Ho as [_ Ho]. by apply (HK o'). Qed.
Lemma ktsum_ok_delete N o K : ktsum_ok N K → ktsum_ok N (delete o K).
Proof.
  intros HK o' h h' Ho Ho'. apply lookup_delete_Some in Ho as [_ Ho].
  apply lookup_delete_Some in Ho' as [_ Ho']. exact (HK o' h h' Ho Ho').
Qed.

(** An action sets the counter of its end back to the tickets. *)
Lemma kcap_ok_kact N o i y K : kcap_ok N K → o ∈ dom K → kcap_ok N (kact o i y K).
Proof.
  intros HK Ho o' h Ho'. unfold kact in Ho'. apply elem_of_dom in Ho as [h0 Hh0].
  rewrite (kcap_lookup _ _ _ Hh0) in Ho'.
  apply lookup_insert_Some in Ho' as [[<- <-]|[_ Ho']]; [simpl|by apply (HK o')].
  split; [apply fle_refl|exact (proj2 (HK o h0 Hh0))].
Qed.

Lemma ktsum_ok_kact N o i y K : ktsum_ok N K → o ∈ dom K → ktsum_ok N (kact o i y K).
Proof.
  intros HK Ho o' h h' H1 H2. unfold kact in H1, H2. apply elem_of_dom in Ho as [h0 Hh0].
  rewrite (kcap_lookup _ _ _ Hh0) in H1, H2.
  apply lookup_insert_Some in H1 as [[E1 <-]|[Hn1 H1]];
    apply lookup_insert_Some in H2 as [[E2 <-]|[Hn2 H2]]; simpl.
  - exfalso. apply (edual_ne o'). congruence.
  - subst o'. exact (HK o h0 h' Hh0 H2).
  - exact (HK o' h h0 H1 ltac:(by rewrite <-E2)).
  - exact (HK o' h h' H1 H2).
Qed.

Lemma kcap_ok_ksync N i j o y y' M K : kcap_ok N K → o ∈ dom K → edual o ∈ dom K →
  kcap_ok N (ksync i j o y y' M K).
Proof.
  intros HK Ho Ho'. unfold ksync.
  assert (Hd : ∀ o0, o0 ∈ dom K → o0 ∈ dom (khand M j (ktick i j M K))).
  { intros o0. unfold khand, ktick. by rewrite !dom_kmod. }
  apply kcap_ok_kact; [apply kcap_ok_kact; [by apply kcap_ok_khand, kcap_ok_ktick|by apply Hd]|].
  unfold kact. rewrite dom_insert_L. apply elem_of_union_r. by apply Hd.
Qed.

Lemma ktsum_ok_ksync N i j o y y' M K : ktsum_ok N K → o ∈ dom K → edual o ∈ dom K →
  ktsum_ok N (ksync i j o y y' M K).
Proof.
  intros HT Ho Ho'. unfold ksync.
  assert (Hd : ∀ o0, o0 ∈ dom K → o0 ∈ dom (khand M j (ktick i j M K))).
  { intros o0. unfold khand, ktick. by rewrite !dom_kmod. }
  apply ktsum_ok_kact; [apply ktsum_ok_kact; [by apply ktsum_ok_khand, ktsum_ok_ktick|by apply Hd]|].
  unfold kact. rewrite dom_insert_L. apply elem_of_union_r. by apply Hd.
Qed.

(** ** Parts of an inserted entry *)

Lemma kres_insert {Y : Type} K o h t (m : gmap cend Y) v :
  kres (<[o := h]> K) t (<[o := v]> m) =
  if decide (h.(h_th) = t) then <[o := v]> (kres K t m) else delete o (kres K t m).
Proof.
  apply map_eq_some. intros o0 w. rewrite lookup_kres.
  destruct (decide (o0 = o)) as [->|Hne].
  - rewrite !lookup_insert_eq. case_decide as Ht.
    + rewrite lookup_insert_eq. split; [by intros [? ?]|intros <-; split; [done|by exists h]].
    + rewrite lookup_delete_eq. split; [|done]. intros [_ (h' & Hh' & Ht')]. simplify_eq.
  - rewrite !lookup_insert_ne by done. case_decide.
    + rewrite lookup_insert_ne by done. by rewrite lookup_kres.
    + rewrite lookup_delete_ne by done. by rewrite lookup_kres.
Qed.

Lemma ctrs_insert K o h t :
  ctrs (<[o := h]> K) t = if decide (h.(h_th) = t) then <[o := hctr h]> (ctrs K t) else delete o (ctrs K t).
Proof.
  apply map_eq_some. intros o0 f. rewrite lookup_ctrs.
  destruct (decide (o0 = o)) as [->|Hne].
  - rewrite lookup_insert_eq. case_decide as Ht.
    + rewrite lookup_insert_eq. split; [by intros (h' & ? & ? & ?); simplify_eq|intros [= <-]; by exists h].
    + rewrite lookup_delete_eq. split; [|done]. intros (h' & ? & ? & ?). simplify_eq.
  - rewrite lookup_insert_ne by done. case_decide.
    + rewrite lookup_insert_ne by done. by rewrite lookup_ctrs.
    + rewrite lookup_delete_ne by done. by rewrite lookup_ctrs.
Qed.

Lemma kres_notin {Y : Type} K t (m : gmap cend Y) o : o ∉ dom K → delete o (kres K t m) = kres K t m.
Proof.
  intros Ho. apply delete_id. apply lookup_kres_None. right. intros (h & Hh & _).
  apply Ho. by apply elem_of_dom_2 in Hh.
Qed.

Lemma ctrs_notin K t o : o ∉ dom K → delete o (ctrs K t) = ctrs K t.
Proof.
  intros Ho. apply delete_id. destruct (ctrs K t !! o) eqn:E; [|done].
  apply lookup_ctrs in E as (h & Hh & _). exfalso. apply Ho. by apply elem_of_dom_2 in Hh.
Qed.

(** ** Pairing outside the changed ends *)

Lemma pair_frame {Y : Type} (R : cend → Y → Y → Prop) (m m' : gmap cend Y) (Ch : gset cend) :
  (∀ o, o ∈ Ch ↔ edual o ∈ Ch) →
  (∀ o, o ∉ Ch → m' !! o = m !! o) →
  (∀ o v v', m !! o = Some v → m !! edual o = Some v' → R o v v') →
  (∀ o v v', o ∈ Ch → m' !! o = Some v → m' !! edual o = Some v' → R o v v') →
  ∀ o v v', m' !! o = Some v → m' !! edual o = Some v' → R o v v'.
Proof.
  intros HCh Hout Hold Hin o v v' H1 H2. destruct (decide (o ∈ Ch)) as [Ho|Ho]; [by apply Hin|].
  assert (edual o ∉ Ch) as Ho' by (by rewrite <-HCh).
  rewrite Hout in H1 by done. rewrite Hout in H2 by done. by apply Hold.
Qed.

Lemma cends_dual (c : chan) o : o ∈ ({[EPos c]} ∪ {[ENeg c]} : gset cend) ↔ edual o ∈ ({[EPos c]} ∪ {[ENeg c]} : gset cend).
Proof. destruct o; simpl; set_solver. Qed.

(** ** Parts after a hand-over and a tick *)

Lemma split_mres {Y : Type} (Θ ΘM Θr : gmap cend Y) (M : gset cend) :
  ΘM ##ₘ Θr → Θ = ΘM ∪ Θr → dom ΘM = M → ΘM = mres M Θ ∧ Θr = mrem M Θ.
Proof.
  intros Hd HΘ HM. split; apply map_eq_some; intros o v;
    rewrite ?lookup_mres_Some, ?lookup_mrem_Some; destruct (split_lookup Θ ΘM Θr M o v Hd HΘ HM) as [H1 H2];
    [rewrite H1|rewrite H2]; tauto.
Qed.

Lemma kres_khand_from {Y : Type} M j K t (m : gmap cend Y) :
  j ≠ t → kres (khand M j K) t m = mrem M (kres K t m).
Proof.
  intros Hjt. apply map_eq_some. intros o v. rewrite lookup_mrem_Some, !lookup_kres, lookup_khand.
  destruct (K !! o) as [h|]; simpl; [|naive_solver]. case_decide; naive_solver.
Qed.

Lemma kres_khand_to {Y : Type} M i j K (m : gmap cend Y) :
  (∀ o h, K !! o = Some h → h.(h_th) ≠ j) → M ⊆ dom (kth K i) →
  kres (khand M j K) j m = mres M (kres K i m).
Proof.
  intros Hj HM. apply map_eq_some. intros o v. rewrite lookup_mres_Some, !lookup_kres, lookup_khand.
  destruct (K !! o) as [h|] eqn:E; simpl; [|naive_solver]. case_decide as Ho.
  - pose proof (HM o Ho) as Hi. apply elem_of_dom_kth in Hi as (h0 & Hh0 & Hi). rewrite E in Hh0.
    injection Hh0 as <-. naive_solver.
  - pose proof (Hj o h E). naive_solver.
Qed.

Lemma ctrs_khand_from M j K t : j ≠ t → ctrs (khand M j K) t = mrem M (ctrs K t).
Proof.
  intros Hjt. apply map_eq_some. intros o f. rewrite lookup_mrem_Some, !lookup_ctrs, lookup_khand.
  destruct (K !! o) as [h|]; simpl; [|naive_solver]. case_decide; naive_solver.
Qed.

Lemma ctrs_khand_to M i j K :
  (∀ o h, K !! o = Some h → h.(h_th) ≠ j) → M ⊆ dom (kth K i) →
  ctrs (khand M j K) j = fhand M (ctrs K i).
Proof.
  intros Hj HM. apply map_eq_some. intros o f. unfold fhand.
  rewrite lookup_fmap, lookup_ctrs, lookup_khand. destruct (mres M (ctrs K i) !! o) eqn:E'.
  - apply lookup_mres_Some in E' as [E' Ho]. apply lookup_ctrs in E' as (h & Hh & Hi & <-).
    rewrite Hh. simpl. rewrite decide_True by done. split; [intros (h' & ? & _ & <-); by simplify_eq|].
    intros [= <-]. by eexists.
  - simpl. destruct (K !! o) as [h|] eqn:E; simpl; [|split; [intros (? & ? & _); done|done]].
    case_decide as Ho.
    + exfalso. pose proof (HM o Ho) as Hi. apply elem_of_dom_kth in Hi as (h' & Hh' & Hi).
      rewrite E in Hh'. simplify_eq. assert (mres M (ctrs K h'.(h_th)) !! o = Some (hctr h')) as X.
      { apply lookup_mres_Some. split; [|done]. apply lookup_ctrs. by eexists. }
      congruence.
    + split; [|done]. intros (h' & ? & Ht & _). simplify_eq. by destruct (Hj o h' E).
Qed.

(** ** One step, case by case *)

Section step.
  Context (N n : nat) (W : world) (T : ty) (C : gset chan) (Mq : gmap nat expr) (K : own)
    (A : senv) (Π : penv) (U : nat → ty).
  Context (Hs : soup_inv N (S n) W ∅ T (LFState (C, Mq) K) A Π U).


  Lemma s_E t e : Mq !! t = Some e → e ∈ E[live]^W _ (S n)⟦kres K t A ⊢ U t⟧^∅.
  Proof. apply (s_rel Hs). Qed.
  Lemma s_F t e : Mq !! t = Some e →
    e ∈ F^(Some N) _ (S n)⟦RThread ▷ None⟧(kres K t Π, ctrs K t).
  Proof. apply (s_fuel Hs). Qed.

  (** A thread outside the step. *)
  Lemma s_other t e : Mq !! t = Some e →
    e ∈ E[live]^W _ n⟦kres K t A ⊢ U t⟧^∅ ∧
    e ∈ F^(Some N) _ n⟦RThread ▷ None⟧(kres K t Π, ctrs K t).
  Proof.
    intros He. split; [eapply Erel_down; [|exact (s_E t e He)]; lia|].
    eapply FuelE_down; [|exact (s_F t e He)]. lia.
  Qed.

  Lemma s_obl t e α e' : Mq !! t = Some e → tstep e α e' →
    Eobl live (S n) (Vrel live) (Erel live) (Vrel live (S n)) (Erel live (S n)) W (kres K t A) (U t) ∅ α e' ∧
    Fobl (Some N) (λ j N, FuelE N j) (λ j N, Vfuel N j) n RThread None (kres K t Π) (ctrs K t) α e'.
  Proof.
    intros He Hst. split; [exact (Erel_S_step live n W W _ _ _ _ _ _ (s_E t e He) (wext_refl W) Hst)|].
    exact (fuel_obl _ _ _ _ _ (s_F t e He) _ _ Hst).
  Qed.

  (** The state is kept and the threads are replaced. *)
  Lemma soup_keep C' Mq' U' :
    C' = C →
    (∀ t, is_Some (Mq !! t) → is_Some (Mq' !! t)) →
    (∀ t e', Mq' !! t = Some e' →
       e' ∈ E[live]^W _ n⟦kres K t A ⊢ U' t⟧^∅ ∧ (U' t = T ∨ U' t = TUnit) ∧
       e' ∈ F^(Some N) _ n⟦RThread ▷ None⟧(kres K t Π, ctrs K t)) →
    soup_inv N n W ∅ T (LFState (C', Mq') K) A Π U'.
  Proof.
    intros -> Hdom Ht. unfold soup_inv. constructor; simpl.
    - apply (sp_tfree _ _ _ _ _ _ _ _ _ Hs).
    - intros t e He. apply (Ht t e He).
    - intros t e He. apply (Ht t e He).
    - intros t e He. apply (Ht t e He).
    - apply (sp_pts _ _ _ _ _ _ _ _ _ Hs).
    - apply (sp_dom _ _ _ _ _ _ _ _ _ Hs).
    - intros o h Ho. apply Hdom. exact (sp_owner _ _ _ _ _ _ _ _ _ Hs o h Ho).
    - apply (sp_closed _ _ _ _ _ _ _ _ _ Hs).
    - apply (sp_pair _ _ _ _ _ _ _ _ _ Hs).
    - apply (sp_sdual _ _ _ _ _ _ _ _ _ Hs).
    - apply (sp_pdual _ _ _ _ _ _ _ _ _ Hs).
    - apply (sp_sig _ _ _ _ _ _ _ _ _ Hs).
    - apply (sp_fin _ _ _ _ _ _ _ _ _ Hs).
    - apply (sp_psig _ _ _ _ _ _ _ _ _ Hs).
    - apply (sp_cap _ _ _ _ _ _ _ _ _ Hs).
    - apply (sp_tsum _ _ _ _ _ _ _ _ _ Hs).
    - apply (sp_sigcap _ _ _ _ _ _ _ _ _ Hs).
  Qed.

  (** P-Act-Beta. *)
  Lemma step_beta i e e' :
    Mq !! i = Some e → tstep e LBeta e' →
    soup_inv N n W ∅ T (LFState (C, <[i := e']> Mq) K) A Π U.
  Proof.
    intros He Hst. destruct (s_obl i e _ e' He Hst) as [HE HF]. cbn [Eobl Fobl] in HE, HF.
    unfold o_beta in HE. unfold f_beta in HF.
    apply soup_keep; [done|intros t Ht; rewrite lookup_insert_is_Some'; by right|].
    intros t e0 He0. apply lookup_insert_Some in He0 as [[<- <-]|[Hne He0]].
    - split_and!; [eapply at_cost_E_live; [|exact HE]; cbn; lia|exact (s_ty Hs i e He)|exact HF].
    - destruct (s_other t e0 He0) as [H1 H2]. split_and!; [done|exact (s_ty Hs t e0 He0)|done].
  Qed.
  (** A new state from its clauses. *)
  Lemma soup_build C' Mq' K' A' Π' U' :
    (∀ t e', Mq' !! t = Some e' →
       e' ∈ E[live]^W _ n⟦kres K' t A' ⊢ U' t⟧^∅ ∧ (U' t = T ∨ U' t = TUnit) ∧
       e' ∈ F^(Some N) _ n⟦RThread ▷ None⟧(kres K' t Π', ctrs K' t)) →
    snd <$> A' = h_pt <$> K' → dom Π' = dom K' →
    (∀ o h, K' !! o = Some h → is_Some (Mq' !! h.(h_th))) →
    (∀ o, o ∈ dom K' → ech o ∈ C') →
    (∀ o, o ∈ dom K' → edual o ∈ dom K') →
    (∀ o S x S' x', A' !! o = Some (S, x) → A' !! edual o = Some (S', x') → x' = pt_dual x ∧ sdual S S') →
    (∀ o P P', Π' !! o = Some P → Π' !! edual o = Some P' → sequiv P' (dual P)) →
    kfin K' → kcap_ok (Some N) K' → ktsum_ok (Some N) K' →
    soup_inv N n W ∅ T (LFState (C', Mq') K') A' Π' U'.
  Proof.
    intros Ht Hp Hd Ho Hc Hpr Hsd Hpd Hfin Hcap Hts. unfold soup_inv. constructor; simpl.
    - apply (sp_tfree _ _ _ _ _ _ _ _ _ Hs).
    - intros t e He. apply (Ht t e He).
    - intros t e He. apply (Ht t e He).
    - intros t e He. apply (Ht t e He).
    - done.
    - done.
    - done.
    - intros o Ho'. left. by apply Hc.
    - intros o Ho' _. by apply Hpr.
    - intros o S x S' x' H1 H2 _. by apply (Hsd o S x S' x').
    - intros o P P' H1 H2 _. by apply (Hpd o P P').
    - intros o y Hy. by rewrite lookup_empty in Hy.
    - exact Hfin.
    - intros o S0 x Hy. by rewrite lookup_empty in Hy.
    - exact Hcap.
    - intros o h h' H1 H2 _. exact (Hts o h h' H1 H2).
    - intros o h HoΣ. by rewrite dom_empty_L in HoΣ.
  Qed.

  Lemma s_kcap_ok : kcap_ok (Some N) K.
  Proof. exact (s_cap _ _ _ _ _ _ _ _ Hs). Qed.
  Lemma s_ktsum_ok : ktsum_ok (Some N) K.
  Proof. exact (s_tsum _ _ _ _ _ _ _ _ Hs). Qed.

  Lemma s_notin_K c : c ∉ C → EPos c ∉ dom K ∧ ENeg c ∉ dom K.
  Proof.
    intros Hc. split; intros Hin; apply Hc; exact (s_closed _ _ _ _ _ _ _ _ Hs _ Hin).
  Qed.

  Lemma kres_sub_dom {Y : Type} t (m : gmap cend Y) : dom (kres K t m) ⊆ dom K.
  Proof.
    intros o Ho. rewrite dom_kres in Ho. apply elem_of_intersection in Ho as [_ Ho].
    apply elem_of_dom_kth in Ho as (h & Hh & _). by apply elem_of_dom_2 in Hh.
  Qed.

  Lemma ctrs_sub_dom t : dom (ctrs K t) ⊆ dom K.
  Proof.
    intros o Ho. rewrite dom_ctrs in Ho. apply elem_of_dom_kth in Ho as (h & Hh & _).
    by apply elem_of_dom_2 in Hh.
  Qed.

  (** A new channel at x, given the obligations of the actor. *)
  Lemma step_create i e' c x S S' m1 :
    Mq !! i = Some (default EUnit (Mq !! i)) → c ∉ C → fle m1 (Some N) →
    e' ∈ E[live]^W _ n⟦new_env c S x (kres K i A) ⊢ U i⟧^∅ →
    e' ∈ F^(Some N) _ n⟦RThread ▷ None⟧(pnew c S' (kres K i Π), cnew m1 (ncap (Some N) m1) c (ctrs K i)) →
    soup_inv N n W ∅ T (LFState (C ∪ {[c]}, <[i := e']> Mq) (knew m1 (ncap (Some N) m1) i c x K))
      (new_env c S x A) (pnew c S' Π) U.
  Proof.
    intros Hi Hc Hm1 HE HF. destruct (s_notin_K c Hc) as [Hp Hn].
    assert (∀ {Y} (m : gmap cend Y) t, t ≠ i → delete (EPos c) (delete (ENeg c) (kres K t m)) = kres K t m)
      as Hdel.
    { intros Y m t _. rewrite (kres_notin _ _ _ (ENeg c)) by done. by rewrite kres_notin. }
    unfold knew, new_env, pnew.
    apply soup_build.
    - intros t e0 He0. rewrite !kres_insert, !ctrs_insert. simpl.
      apply lookup_insert_Some in He0 as [[<- <-]|[Hne He0]].
      + rewrite !decide_True by done. split_and!; [exact HE| |exact HF].
        exact (s_ty Hs i _ Hi).
      + rewrite !decide_False by done. rewrite !Hdel by done.
        rewrite (ctrs_notin _ _ (ENeg c)), ctrs_notin by done.
        destruct (s_other t e0 He0) as [H1 H2]. split_and!; [done|exact (s_ty Hs t e0 He0)|done].
    - rewrite !fmap_insert. simpl. f_equal. f_equal. apply (sp_pts _ _ _ _ _ _ _ _ _ Hs).
    - rewrite !dom_insert_L. by rewrite (sp_dom _ _ _ _ _ _ _ _ _ Hs).
    - intros o h Ho. apply lookup_insert_Some in Ho as [[<- <-]|[_ Ho]].
      { simpl. rewrite lookup_insert_eq. by eexists. }
      apply lookup_insert_Some in Ho as [[<- <-]|[_ Ho]].
      { simpl. rewrite lookup_insert_eq. by eexists. }
      rewrite lookup_insert_is_Some'. right. exact (s_owner _ _ _ _ _ _ _ _ Hs o h Ho).
    - intros o. rewrite !dom_insert_L, !elem_of_union, !elem_of_singleton.
      intros [->|[->|Ho]]; [set_solver|set_solver|]. pose proof (s_closed _ _ _ _ _ _ _ _ Hs o Ho). set_solver.
    - intros o. rewrite !dom_insert_L, !elem_of_union, !elem_of_singleton.
      intros [->|[->|Ho]]; [simpl; tauto|simpl; tauto|]. right; right. exact (s_pair _ _ _ _ _ _ _ _ Hs o Ho).
    - intros o S0 x0 S0' x0' H1 H2.
      refine (pair_frame (λ _ (v v' : sty * point), v'.2 = pt_dual v.2 ∧ sdual v.1 v'.1) _ _
        ({[EPos c]} ∪ {[ENeg c]}) (cends_dual c) _ _ _ o (S0, x0) (S0', x0') H1 H2).
      + intros o0 Ho. rewrite !lookup_insert_ne by set_solver. done.
      + intros o0 [S1 x1] [S2 x2] H3 H4. exact (s_sdual _ _ _ _ _ _ _ _ Hs o0 S1 x1 S2 x2 H3 H4).
      + intros o0 [S1 x1] [S2 x2] Ho H3 H4. simpl.
        apply elem_of_union in Ho as [Ho|Ho]; apply elem_of_singleton in Ho as ->; simpl in H4.
        * rewrite lookup_insert_eq in H3. rewrite lookup_insert_ne, lookup_insert_eq in H4 by discriminate.
          simplify_eq. split; [done|apply seqv_refl].
        * rewrite lookup_insert_eq in H4. rewrite lookup_insert_ne, lookup_insert_eq in H3 by discriminate.
          simplify_eq. split; [by rewrite pt_dual_dual|]. unfold sdual. rewrite dual_involutive. apply seqv_refl.
    - intros o P P' H1 H2.
      refine (pair_frame (λ _ v v', sequiv v' (dual v)) _ _ ({[EPos c]} ∪ {[ENeg c]}) (cends_dual c)
        _ _ _ o P P' H1 H2).
      + intros o0 Ho. rewrite !lookup_insert_ne by set_solver. done.
      + intros o0 P1 P2 H3 H4. exact (s_pdual _ _ _ _ _ _ _ _ Hs o0 P1 P2 H3 H4).
      + intros o0 P1 P2 Ho H3 H4.
        apply elem_of_union in Ho as [Ho|Ho]; apply elem_of_singleton in Ho as ->; simpl in H4.
        * rewrite lookup_insert_eq in H3. rewrite lookup_insert_ne, lookup_insert_eq in H4 by discriminate.
          simplify_eq. apply sequiv_refl.
        * rewrite lookup_insert_eq in H4. rewrite lookup_insert_ne, lookup_insert_eq in H3 by discriminate.
          simplify_eq. rewrite dual_involutive. apply sequiv_refl.
    - apply kfin_insert; [destruct m1; [by eexists|done]|].
      apply kfin_insert; [by destruct m1|]. exact (sp_fin _ _ _ _ _ _ _ _ _ Hs).
    - intros o h Ho. apply lookup_insert_Some in Ho as [[<- <-]|[_ Ho]]; [simpl; split; [apply fle_refl|done]|].
      apply lookup_insert_Some in Ho as [[<- <-]|[_ Ho]]; [simpl; split; [apply fle_refl|]|exact (s_kcap_ok o h Ho)].
      destruct m1; simpl in *; lia.
    - intros o h h' H1 H2.
      assert (Hnot : ∀ o', o' ∈ dom K → o' ≠ EPos c ∧ o' ≠ ENeg c) by (intros o' Ho'; split; intros ->; done).
      apply lookup_insert_Some in H1 as [[<- <-]|[Hn1 H1]].
      { simpl in H2. rewrite lookup_insert_ne, lookup_insert_eq in H2 by discriminate. injection H2 as <-.
        simpl. by apply tsum_ncap. }
      apply lookup_insert_Some in H1 as [[<- <-]|[Hn1' H1]].
      { simpl in H2. rewrite lookup_insert_eq in H2. injection H2 as <-. simpl.
        apply tsum_ok_comm. by apply tsum_ncap. }
      assert (edual o ∈ dom K) as Hd2 by (apply (s_pair _ _ _ _ _ _ _ _ Hs); by apply elem_of_dom_2 in H1).
      rewrite !lookup_insert_ne in H2 by (intros Hx; rewrite <-Hx in Hd2; done).
      exact (s_ktsum_ok o h h' H1 H2).
  Qed.
  Lemma s_cfresh i c : c ∉ C → cfresh c (kres K i A).
  Proof.
    intros Hc. destruct (s_notin_K c Hc) as [Hp Hn].
    pose proof (kres_sub_dom i A) as Hd. split; intros Hin; [apply Hp|apply Hn]; by apply Hd.
  Qed.

  Lemma s_ffresh i c : c ∉ C → ffresh c (kres K i Π) (ctrs K i).
  Proof.
    intros Hc. destruct (s_notin_K c Hc) as [Hp Hn].
    pose proof (kres_sub_dom i Π) as Hd. pose proof (ctrs_sub_dom i) as Hd'.
    unfold ffresh. split_and!; intros Hin; [apply Hp|apply Hn|apply Hp|apply Hn]; first [by apply Hd|by apply Hd'].
  Qed.

  (** P-Act-New. *)
  Lemma step_new i e ℓ c e' :
    Mq !! i = Some e → tstep e (LNew ℓ c) e' → c ∉ C →
    ∃ A' Π', soup_inv N n W ∅ T
      (lf_next N (LFState (C, Mq) K) (EvSolo i (LNew ℓ c) PickNone) (C ∪ {[c]}, <[i := e']> Mq)) A' Π' U.
  Proof.
    intros He Hst Hc. destruct (s_obl i e _ e' He Hst) as [HE HF]. cbn [Eobl Fobl] in HE, HF.
    unfold o_new in HE. unfold f_new in HF.
    destruct (HE (s_cfresh i c Hc) (kfresh ℓ K)) as [S HS].
    { intros o S0 x0 Ho Hr. destruct (s_held K i A o _ Ho) as (h & Hh & _ & HA).
      pose proof (s_kpt _ _ _ _ _ _ _ _ Hs o S0 x0 HA) as Hk. cbn [s_K] in Hk. unfold kpt in Hk. rewrite Hh in Hk.
      simpl in Hk. subst x0. exact (kfresh_spec ℓ K o h Hh Hr). }
    destruct (HF (s_ffresh i c Hc)) as [S' HS'].
    eexists _, _. unfold lf_next. cbn [own_next s_K s_q]. apply (step_create i e' c _ S S'); [by rewrite He|done|apply fhalf_le| |exact HS'].
    eapply at_cost_E_live; [|exact HS]. cbn; lia.
  Qed.

  (** P-Act-NewAt. *)
  Lemma step_new_at i e κf o c e' :
    Mq !! i = Some e → tstep e (LNewAt κf o c) e' → c ∉ C →
    ∃ A' Π', soup_inv N n W ∅ T
      (lf_next N (LFState (C, Mq) K) (EvSolo i (LNewAt κf o c) PickNone) (C ∪ {[c]}, <[i := e']> Mq)) A' Π' U.
  Proof.
    intros He Hst Hc. destruct (s_obl i e _ e' He Hst) as [HE HF]. cbn [Eobl Fobl] in HE, HF.
    unfold o_new_at in HE. unfold f_new_at, f_new in HF.
    destruct (HE (s_cfresh i c Hc)) as (S0 & x & Ho & S & HS).
    destruct (s_held K i A o _ Ho) as (h & Hh & Hhi & HA).
    pose proof (s_kpt _ _ _ _ _ _ _ _ Hs o S0 x HA) as Hk. cbn [s_K] in Hk.
    destruct HF as (p & Hp & HF).
    assert (p = hctr h) as ->.
    { assert (ctrs K i !! o = Some (hctr h)) as Hc' by (apply lookup_ctrs; eauto). congruence. }
    destruct (HF (s_ffresh i c Hc)) as [S' HS']. simpl in HS'.
    eexists _, _. unfold lf_next. cbn [own_next s_K s_q]. rewrite Hk, (kcap_lookup _ _ _ Hh).
    apply (step_create i e' c _ S S'); [by rewrite He|done|exact (proj2 (s_kcap_ok o h Hh))| |exact HS'].
    eapply at_cost_E_live; [|exact HS]. cbn; lia.
  Qed.
  Lemma s_threads o h : K !! o = Some h → is_Some (Mq !! h.(h_th)).
  Proof. apply (s_owner _ _ _ _ _ _ _ _ Hs). Qed.

  (** P-Act-Spawn. *)
  Lemma step_spawn i j e v e' :
    Mq !! i = Some e → tstep e (LSpawn v) e' → Mq !! j = None →
    soup_inv N n W ∅ T
      (lf_next N (LFState (C, Mq) K) (EvSolo i (LSpawn v) (PickChild j)) (C, <[j := App v EUnit]> (<[i := e']> Mq)))
      A Π (λ t, if decide (t = j) then TUnit else U t).
  Proof.
    intros He Hst Hj. assert (i ≠ j) as Hij by (intros ->; congruence).
    destruct (s_obl i e _ e' He Hst) as [HE HF]. cbn [Eobl Fobl] in HE, HF.
    unfold o_spawn in HE. unfold f_spawn in HF.
    destruct HE as (ΘM & Θr & Hd & HΘ & Hth & Hpar).
    assert (HM : dom ΘM = fends v) by (destruct Hth as (e1 & -> & Hfe & _); exact Hfe).
    destruct HF as (HMφ & _ & Hch & Hpar').
    destruct (split_mres _ _ _ _ Hd HΘ HM) as [-> ->].
    assert (Hnj : ∀ o h, K !! o = Some h → h.(h_th) ≠ j).
    { intros o h Ho Heq. destruct (s_threads o h Ho) as [? Hx]. congruence. }
    assert (HMi : (fends v) ⊆ dom (kth K i)).
    { rewrite <-HM, dom_mres, dom_kres. set_solver. }
    (* the child *)
    destruct Hth as (e0 & -> & _ & _ & Hb).
    destruct (Hb W n ∅ EUnit ∅ (wext_refl W) ltac:(cbn; lia) (map_disjoint_empty_r _) eq_refl) as [Hb1 _].
    pose proof (Hb1 ltac:(lia) (proj2 (Vrel_unit_iff _ _ _ _ _) (conj eq_refl eq_refl))) as Hbody.
    rewrite map_union_empty in Hbody.
    assert (Erel live n W (mres (fends (Lam e0)) (kres K i A)) TUnit ∅ (App (Lam e0) EUnit)) as Hchild.
    { apply (Erel_beta live n W _ TUnit ∅ _ (subst1 EUnit e0)).
      - intros α e'' Hs'. assert (head_step (App (Lam e0) EUnit) α e'') as Hh by head_only.
        inversion Hh; by subst.
      - by apply tstep_head, t_act_app.
      - cbn. by rewrite Nat.sub_0_r. }
    unfold lf_next. cbn [own_next s_K s_q].
    apply soup_build.
    - intros t e1 He1. apply lookup_insert_Some in He1 as [[<- <-]|[Htj He1]].
      + rewrite decide_True by done. rewrite (kres_khand_to _ i), (kres_khand_to _ i), (ctrs_khand_to _ i) by done.
        split_and!; [exact Hchild|by right|exact Hch].
      + rewrite decide_False by done. rewrite !kres_khand_from, ctrs_khand_from by done.
        apply lookup_insert_Some in He1 as [[<- <-]|[Hti He1]].
        * split_and!; [|exact (s_ty Hs i e He)|exact Hpar'].
          eapply at_cost_E_live; [|exact Hpar]. cbn; lia.
        *
          assert (∀ {Y} (m : gmap cend Y), mrem (fends (Lam e0)) (kres K t m) = kres K t m) as Hm.
          { intros Y m. apply map_eq_some. intros o w. rewrite lookup_mrem_Some. split; [tauto|].
            intros Hw. split; [done|]. intros Ho. pose proof (HMi o Ho) as Hi.
            apply elem_of_dom_kth in Hi as (h & Hh & Hhi). apply lookup_kres in Hw as [_ (h' & Hh' & Ht)].
            simplify_eq. }
          rewrite !Hm. assert (ctrs K t = mrem (fends (Lam e0)) (ctrs K t)) as <-.
          { apply map_eq_some. intros o f. rewrite lookup_mrem_Some. split; [|tauto].
            intros Hf. split; [done|]. intros Ho. pose proof (HMi o Ho) as Hi.
            apply elem_of_dom_kth in Hi as (h & Hh & Hhi). apply lookup_ctrs in Hf as (h' & Hh' & Ht & _).
            simplify_eq. }
          destruct (s_other t e1 He1) as [H1 H2]. split_and!; [done|exact (s_ty Hs t e1 He1)|done].
    - apply map_eq. intros o. rewrite !lookup_fmap, lookup_khand. pose proof (s_pts _ _ _ _ _ _ _ _ Hs o) as Hp.
      cbn [s_K] in Hp. rewrite Hp. destruct (K !! o); simpl; [|done]. by case_decide.
    - unfold khand. rewrite dom_kmod. apply (sp_dom _ _ _ _ _ _ _ _ _ Hs).
    - intros o h Ho. rewrite lookup_khand in Ho. apply fmap_Some in Ho as (h0 & Ho & ->).
      case_decide; simpl; rewrite !lookup_insert_is_Some'; [by left|].
      destruct (decide (h0.(h_th) = i)); [by right; left|]. right; right. exact (s_threads o h0 Ho).
    - intros o Ho. unfold khand in Ho. rewrite dom_kmod in Ho. exact (s_closed _ _ _ _ _ _ _ _ Hs o Ho).
    - intros o Ho. unfold khand in *. rewrite dom_kmod in Ho |- *. exact (s_pair _ _ _ _ _ _ _ _ Hs o Ho).
    - exact (s_sdual _ _ _ _ _ _ _ _ Hs).
    - exact (s_pdual _ _ _ _ _ _ _ _ Hs).
    - apply kfin_khand. exact (sp_fin _ _ _ _ _ _ _ _ _ Hs).
    - apply kcap_ok_khand, s_kcap_ok.
    - apply ktsum_ok_khand, s_ktsum_ok.
  Qed.
End step.
