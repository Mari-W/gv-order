(** * Steps of a run, without the soup (stage S8)

    Facts of the semantics that adequacy reads at one step: a thread
    outside a step other than a link keeps its term, a link renames it,
    an enabled session redex has a partner whose redex fits, and the
    tickets of a configuration. *)

From stdpp Require Import relations.
From GV Require Export soup.LFLocal.

Lemma istep_other_eq q ev q' t e :
  istep q ev q' → t ∉ ev_parts ev → (∀ u o1 o2, ev ≠ EvLink u o1 o2) → q.2 !! t = Some e → q'.2 !! t = Some e.
Proof.
  destruct 1; simpl; intros Ht Hnl He.
  all: try (exfalso; eapply Hnl; reflexivity).
  all: try (rewrite ?lookup_insert_ne; [done|set_solver..]).
  all: rewrite lookup_insert_ne; [|intros ->; congruence]; rewrite lookup_insert_ne; [done|set_solver].
Qed.

Lemma istep_link_other q u o1 o2 q' t e :
  istep q (EvLink u o1 o2) q' → t ≠ u → q.2 !! t = Some e → q'.2 !! t = Some (emap (csub o1 o2) e).
Proof.
  intros Hst Htu He. inversion Hst; subst. simpl. rewrite lookup_fmap, lookup_insert_ne by done.
  simpl in He. by rewrite He.
Qed.

Lemma offers_send a o M v : offers a (LSess (SSend o M v)) → a = ASend o v.
Proof. destruct a; simpl; try done. intros (-> & -> & _). done. Qed.
Lemma offers_recv a o v : offers a (LSess (SRecv o v)) → a = ARecv o.
Proof. destruct a; simpl; try done. intros (-> & _). done. Qed.
Lemma offers_close a o : offers a (LSess (SClose o)) → a = AClose o.
Proof. destruct a; simpl; try done. intros ->. done. Qed.
Lemma offers_sel a o b : offers a (LSess (SSel o b)) → a = ASel o b.
Proof. destruct a; simpl; try done. intros (-> & ->). done. Qed.
Lemma offers_bra a o b : offers a (LSess (SBra o b)) → a = ABra o.
Proof. destruct a; simpl; try done. intros ->. done. Qed.

Lemma step_act e α e' : tstep e α e' → ∃ a, act e = Some a ∧ offers a α.
Proof. apply act_step. Qed.

(** A session redex that takes part in a closed step meets a fitting
    redex. *)
Lemma ev_partner q ev q' t e a1 o :
  istep q ev q' → ev_tau ev → t ∈ ev_parts ev → q.2 !! t = Some e → act e = Some a1 → aend a1 = Some o →
  ∃ s es a2, s ∈ ev_parts ev ∧ s ≠ t ∧ q.2 !! s = Some es ∧ act es = Some a2 ∧
    aend a2 = Some (edual o) ∧ compat a1 a2.
Proof.
  intros Hst Hτ Ht He Ha Ho.
  assert (Hof : ∀ α e', tstep e α e' → offers a1 α).
  { intros α e' Hs. destruct (act_step _ _ _ Hs) as (a' & Ha' & Hoff). rewrite Ha in Ha'. by simplify_eq. }
  destruct Hst as [C M i e0 e0' Hi Hs|C M i e0 ℓ c e0' Hi Hs|C M i e0 κ o' c e0' Hi Hs
    |C M i j e0 Mv v e0' Hi Hs Hj
    |C M i j o' Mv v e0 e0' f f' Hij Hi Hj He0 Hf|C M i j o' e0 e0' f f' Hij Hi Hj He0 Hf HC
    |C M i j o' b e0 e0' f f' Hij Hi Hj He0 Hf|C M i e0 o1 o2 e0' Hi Hs HC
    |C M i e0 σ e0' Hi Hs HC]; simpl in Ht, He |- *.
  - apply elem_of_singleton in Ht as ->. rewrite He in Hi. injection Hi as <-.
    pose proof (Hof _ _ Hs) as Hx. by destruct a1.
  - apply elem_of_singleton in Ht as ->. rewrite He in Hi. injection Hi as <-.
    pose proof (Hof _ _ Hs) as Hx. by destruct a1.
  - apply elem_of_singleton in Ht as ->. rewrite He in Hi. injection Hi as <-.
    pose proof (Hof _ _ Hs) as Hx. by destruct a1.
  - apply elem_of_singleton in Ht as ->. rewrite He in Hi. injection Hi as <-.
    pose proof (Hof _ _ Hs) as Hx. by destruct a1.
  - destruct (step_act _ _ _ He0) as (ai & Hai & Hoi). apply offers_send in Hoi as ->.
    destruct (step_act _ _ _ Hf) as (aj & Haj & Hoj). apply offers_recv in Hoj as ->.
    apply elem_of_union in Ht as [Ht|Ht]; apply elem_of_singleton in Ht as ->.
    + rewrite He in Hi. injection Hi as <-. rewrite Ha in Hai. injection Hai as ->. simpl in Ho. injection Ho as <-.
      exists j, f, (ARecv (edual o')). split_and!; [set_solver|done|done|done|done|done].
    + rewrite He in Hj. injection Hj as <-. rewrite Ha in Haj. injection Haj as ->. simpl in Ho. injection Ho as <-.
      exists i, e0, (ASend o' v). split_and!; [set_solver|done|done|done|by rewrite edual_edual|simpl; by rewrite edual_edual].
  - destruct (step_act _ _ _ He0) as (ai & Hai & Hoi). apply offers_close in Hoi as ->.
    destruct (step_act _ _ _ Hf) as (aj & Haj & Hoj). apply offers_close in Hoj as ->.
    apply elem_of_union in Ht as [Ht|Ht]; apply elem_of_singleton in Ht as ->.
    + rewrite He in Hi. injection Hi as <-. rewrite Ha in Hai. injection Hai as ->. simpl in Ho. injection Ho as <-.
      exists j, f, (AClose (edual o')). split_and!; [set_solver|done|done|done|done|done].
    + rewrite He in Hj. injection Hj as <-. rewrite Ha in Haj. injection Haj as ->. simpl in Ho. injection Ho as <-.
      exists i, e0, (AClose o'). split_and!; [set_solver|done|done|done|by rewrite edual_edual|simpl; by rewrite edual_edual].
  - destruct (step_act _ _ _ He0) as (ai & Hai & Hoi). apply offers_sel in Hoi as ->.
    destruct (step_act _ _ _ Hf) as (aj & Haj & Hoj). apply offers_bra in Hoj as ->.
    apply elem_of_union in Ht as [Ht|Ht]; apply elem_of_singleton in Ht as ->.
    + rewrite He in Hi. injection Hi as <-. rewrite Ha in Hai. injection Hai as ->. simpl in Ho. injection Ho as <-.
      exists j, f, (ABra (edual o')). split_and!; [set_solver|done|done|done|done|done].
    + rewrite He in Hj. injection Hj as <-. rewrite Ha in Haj. injection Haj as ->. simpl in Ho. injection Ho as <-.
      exists i, e0, (ASel o' b). split_and!; [set_solver|done|done|done|by rewrite edual_edual|simpl; by rewrite edual_edual].
  - apply elem_of_singleton in Ht as ->. rewrite He in Hi. injection Hi as <-.
    pose proof (Hof _ _ Hs) as Hx. exfalso. exact (aend_not_link _ _ _ Ho Hx).
  - by unfold ev_tau in Hτ.
Qed.

Lemma compat_amap g a1 a2 o :
  compat a1 a2 → aend a1 = Some o → g o = o → g (edual o) = edual o → compat (amap g a1) (amap g a2).
Proof.
  intros Hc Ho H1 H2. destruct a1; simpl in Ho; simplify_eq; destruct a2; simpl in Hc |- *; try done;
    subst; by rewrite H1, H2.
Qed.

Lemma aend_amap g a o : aend a = Some o → aend (amap g a) = Some (g o).
Proof. destruct a; simpl; intros [= <-]; done. Qed.

(** ** Tickets and counters *)

Definition kval (K : own) (o : cend) : nat :=
  match K !! o with Some h => default 0 h.(h_ctr) | None => 0 end.

Definition ksum (tk : nat → nat) (q : config) : nat := sum_list_with tk (elements (dom q.2)).


Lemma sum_list_with_ext' (f g : nat → nat) (xs : list nat) :
  (∀ x, x ∈ xs → f x = g x) → sum_list_with f xs = sum_list_with g xs.
Proof.
  induction xs as [|x xs IH]; intros H; [done|]. simpl.
  rewrite (H x (list_elem_of_here _ _)), IH; [done|]. intros y Hy. apply H. by apply list_elem_of_further.
Qed.

Lemma ksum_ext tk tk' (q q' : config) :
  dom q'.2 = dom q.2 → (∀ t, t ∈ dom q.2 → tk' t = tk t) → ksum tk' q' = ksum tk q.
Proof.
  intros Hd Ht. unfold ksum. rewrite Hd. apply sum_list_with_ext'. intros t Hin. apply Ht.
  by apply elem_of_elements.
Qed.

Lemma kset_split tk (X : gset nat) t :
  t ∈ X → sum_list_with tk (elements X) = tk t + sum_list_with tk (elements (X ∖ {[t]})).
Proof.
  intros Ht. transitivity (sum_list_with tk (elements ({[t]} ∪ X ∖ {[t]}))).
  - by rewrite <-(union_difference_singleton_L t X Ht).
  - rewrite (elements_union_singleton (X ∖ {[t]}) t) by set_solver. done.
Qed.

Lemma div2_split x : Nat.div2 (S x) + Nat.div2 x = x.
Proof.
  induction x as [x IH] using lt_wf_ind. destruct x as [|[|x]]; [done|done|].
  simpl. pose proof (IH x ltac:(lia)) as H. simpl in H. lia.
Qed.

Lemma ksum_link tk u (q q' : config) :
  u ∈ dom q.2 → dom q'.2 = dom q.2 → 1 ≤ tk u → ksum (tupd tk u (tk u - 1)) q' < ksum tk q.
Proof.
  intros Hu Hd Htk. unfold ksum. rewrite Hd, !(kset_split _ _ u Hu).
  unfold tupd at 1. rewrite decide_True by done.
  rewrite (sum_list_with_ext' (tupd tk u (tk u - 1)) tk); [lia|].
  intros t Ht. apply elem_of_elements in Ht. unfold tupd. rewrite decide_False; [done|set_solver].
Qed.

Lemma ksum_spawn tk u j (q q' : config) :
  u ∈ dom q.2 → j ∉ dom q.2 → dom q'.2 = {[j]} ∪ dom q.2 →
  ksum (tupd (tupd tk u (Nat.div2 (tk u))) j (Nat.div2 (S (tk u)))) q' = ksum tk q.
Proof.
  intros Hu Hj Hd. unfold ksum. rewrite Hd.
  rewrite (kset_split _ ({[j]} ∪ dom q.2) j) by set_solver.
  replace (({[j]} ∪ dom q.2) ∖ {[j]}) with (dom q.2) by set_solver.
  rewrite (kset_split _ (dom q.2) u Hu), (kset_split tk (dom q.2) u Hu).
  assert (u ≠ j) as Huj by (intros ->; done).
  assert (tupd (tupd tk u (Nat.div2 (tk u))) j (Nat.div2 (S (tk u))) j = Nat.div2 (S (tk u))) as -> 
    by (unfold tupd; by rewrite decide_True).
  assert (tupd (tupd tk u (Nat.div2 (tk u))) j (Nat.div2 (S (tk u))) u = Nat.div2 (tk u)) as ->
    by (unfold tupd; by rewrite decide_False, decide_True).
  rewrite (sum_list_with_ext' _ tk (elements (dom q.2 ∖ {[u]}))).
  - pose proof (div2_split (tk u)). lia.
  - intros t Ht. apply elem_of_elements in Ht. unfold tupd.
    rewrite decide_False by set_solver. rewrite decide_False; [done|set_solver].
Qed.

(** ** Inversion of one step, by event *)

Lemma istep_dom q ev q' : istep q ev q' → (∀ u j M, ev ≠ EvSpawn u j M) → dom q'.2 = dom q.2.
Proof.
  destruct 1 as [C M i e e' Hi|C M i e ℓ c e' Hi|C M i e κ o c e' Hi|C M i j e Mv v e' Hi Hs Hj
    |C M i j o Mv v e e' f f' Hij Hi Hj|C M i j o e e' f f' Hij Hi Hj|C M i j o b e e' f f' Hij Hi Hj
    |C M i e o1 o2 e' Hi|C M i e σ e' Hi]; simpl; intros Hns.
  all: try (exfalso; by eapply Hns).
  all: rewrite ?dom_fmap_L, ?dom_insert_L.
  all: apply elem_of_dom_2 in Hi; try (apply elem_of_dom_2 in Hj); set_solver.
Qed.

Lemma istep_spawn_inv q u j M q' : istep q (EvSpawn u j M) q' →
  ∃ eu v e', q.2 !! u = Some eu ∧ tstep eu (LSpawn M v) e' ∧ q.2 !! j = None ∧ dom q'.2 = {[j]} ∪ dom q.2.
Proof.
  intros Hst. inversion Hst; subst. simpl. exists e, v, e'. split_and!; [done|done|done|].
  rewrite !dom_insert_L. apply elem_of_dom_2 in H3. set_solver.
Qed.

Lemma istep_link_inv q u o1 o2 q' : istep q (EvLink u o1 o2) q' →
  ∃ eu e', q.2 !! u = Some eu ∧ tstep eu (LSess (SLink ({[o1]} ∪ {[o2]}))) e'.
Proof. intros Hst. inversion Hst; subst. simpl. eauto. Qed.

(** The actor of an administrative event has an administrative redex. *)
Lemma admin_of_step e α e' : tstep e α e' → admin_lbl α → ∃ a, act e = Some a ∧ is_admin a.
Proof.
  intros Hs Hα. destruct (act_step _ _ _ Hs) as (a & Ha & Hoff). exists a. split; [done|].
  by apply (offers_admin a α Hoff).
Qed.

Lemma istep_admin_actor q ev q' u :
  istep q ev q' → ev_admin ev → u ∈ ev_parts ev → admin_at q u.
Proof.
  intros Hst Had Hu.
  destruct Hst as [C M i e e' Hi Hs|C M i e ℓ c e' Hi Hs|C M i e κ o c e' Hi Hs|C M i j e Mv v e' Hi Hs Hj
    |C M i j o Mv v e e' f f' Hij Hi Hj|C M i j o e e' f f' Hij Hi Hj|C M i j o b e e' f f' Hij Hi Hj
    |C M i e o1 o2 e' Hi Hs|C M i e σ e' Hi]; simpl in Had, Hu; try contradiction;
    apply elem_of_singleton in Hu as ->; destruct (admin_of_step _ _ _ Hs I) as (a & Ha & Had');
    by exists e, a.
Qed.

(** The end an actor of a synchronization acts on. *)
Definition ev_end (ev : event) (s : nat) : option cend :=
  match ev with
  | EvMsg i j o _ | EvClose i j o | EvChoice i j o _ =>
      if decide (s = i) then Some o else if decide (s = j) then Some (edual o) else None
  | _ => None
  end.

Lemma istep_sync_step q ev q' s es p :
  istep q ev q' → ev_end ev s = Some p → q.2 !! s = Some es →
  ∃ σ es', tstep es (LSess σ) es' ∧ act_end σ = Some p.
Proof.
  intros Hst Hp Hes.
  destruct Hst as [C M i e e' Hi|C M i e ℓ c e' Hi|C M i e κ o c e' Hi|C M i j e Mv v e' Hi Hs Hj
    |C M i j o Mv v e e' f f' Hij Hi Hj He Hf|C M i j o e e' f f' Hij Hi Hj He Hf HC
    |C M i j o b e e' f f' Hij Hi Hj He Hf|C M i e o1 o2 e' Hi|C M i e σ e' Hi]; simpl in Hp, Hes; try done.
  all: destruct (decide (s = i)) as [->|Hsi]; [injection Hp as <-; rewrite Hi in Hes; injection Hes as <-; eauto|].
  all: destruct (decide (s = j)) as [->|Hsj]; [injection Hp as <-; rewrite Hj in Hes; injection Hes as <-; eauto|done].
Qed.
