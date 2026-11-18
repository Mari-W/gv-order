(** * Lock freedom gives Padovani's lock freedom (stage S1)

    [lock_free_reach_of]: a lock-free process (every weakly fair maximal
    run serves every pending thread, Fair.v) is lock free in the sense of
    padovani2014deadlock, Definition II.1: from every reachable
    configuration with a pending thread, some continuation lets that
    thread take part in a step. No typing and no τ-divergence premise is
    needed.

    Proof. A configuration reachable from p is the end of a run from a
    lifting of p ([pred_star_back], which lifts process steps backwards
    with the thread names of the end). From it a computable scheduler
    builds a weakly fair maximal run ([sconf]): at position k it fires a
    step of thread [enum k] if that thread is enabled, and every thread
    name occurs infinitely often in [enum]. Lock freedom of the
    concatenated run fires the pending thread after the reachable
    configuration.

    The converse fails in the untyped semantics. Two threads race on a
    free channel c: u receives on c in a loop, s sends on c in a loop,
    and t sends on c once. A weakly fair run may pair u with s forever,
    because t is enabled only while u sits at its receive. *)

From stdpp Require Import relations.
From GV Require Export lockfree.Fair.

(** ** A thread enumeration in which every thread recurs *)

Definition enum_step (bp : nat * nat) : nat * nat :=
  if bool_decide (bp.2 < bp.1) then (bp.1, S bp.2) else (S bp.1, 0).

Fixpoint enum_bp (j : nat) : nat * nat :=
  match j with 0 => (0, 0) | S j => enum_step (enum_bp j) end.

Definition enum (j : nat) : nat := (enum_bp j).2.

Lemma enum_bp_run j b : enum_bp j = (b, 0) → ∀ p, p ≤ b → enum_bp (j + p) = (b, p).
Proof.
  intros Hj p. induction p as [|p IH]; intros Hp; [by rewrite Nat.add_0_r|].
  rewrite Nat.add_succ_r. simpl. rewrite IH by lia. unfold enum_step. simpl.
  by rewrite bool_decide_eq_true_2 by lia.
Qed.

Lemma enum_bp_start b : ∃ j, b ≤ j ∧ enum_bp j = (b, 0).
Proof.
  induction b as [|b (j & Hj & Hb)]; [by exists 0|].
  exists (S (j + b)). split; [lia|]. simpl. rewrite (enum_bp_run j b Hb b) by lia.
  unfold enum_step. simpl. by rewrite bool_decide_eq_false_2 by lia.
Qed.

Lemma enum_inf t i : ∃ j, i ≤ j ∧ enum j = t.
Proof.
  destruct (enum_bp_start (max i t)) as (j & Hj & Hb). exists (j + t). split; [lia|].
  unfold enum. by rewrite (enum_bp_run j _ Hb t) by lia.
Qed.

(** ** The scheduler *)

Definition sched_step (q : config) (k : nat) : option event * config :=
  match try_thread q (enum k) with
  | inleft (exist _ evq _) => (Some evq.1, evq.2)
  | inright _ =>
      match find_enabled q (elements (dom q.2)) with
      | inleft (exist _ evq _) => (Some evq.1, evq.2)
      | inright _ => (None, q)
      end
  end.

Lemma sched_step_spec q k :
  (∃ ev, (sched_step q k).1 = Some ev ∧ itstep q ev (sched_step q k).2) ∨
  (stuck q ∧ (sched_step q k).2 = q ∧ (sched_step q k).1 = None).
Proof.
  unfold sched_step. destruct (try_thread q (enum k)) as [[evq [Hs _]]|_]; [left; eauto|].
  destruct (find_enabled q (elements (dom q.2))) as [[evq Hs]|Hno]; [left; eauto|].
  right. split_and!; [by apply stuck_of|done|done].
Qed.

Lemma sched_fair q k : tenabled q (enum k) → enum k ∈ lparts (sched_step q k).1.
Proof.
  unfold sched_step. destruct (try_thread q (enum k)) as [[evq [_ Ht]]|Hn]; [done|].
  intros Hen. by destruct Hn.
Qed.

Fixpoint sconf (q0 : config) (k : nat) : config :=
  match k with 0 => q0 | S k => (sched_step (sconf q0 k) k).2 end.

Definition slab (q0 : config) (k : nat) : option event := (sched_step (sconf q0 k) k).1.

Lemma srun_max q0 : maximal (sconf q0) (slab q0).
Proof.
  intros k. unfold run_step, slab.
  change (sconf q0 (S k)) with ((sched_step (sconf q0 k) k).2). apply sched_step_spec.
Qed.

Lemma srun_fair q0 : wfair (sconf q0) (slab q0).
Proof.
  intros t i. destruct (enum_inf t i) as (j & Hij & Hj). exists j. split; [done|].
  destruct (try_thread (sconf q0 j) t) as [[evq [Hs Ht]]|Hn]; [left|by right].
  unfold slab. rewrite <-Hj. apply sched_fair. rewrite Hj. by exists evq.1, evq.2.
Qed.

Lemma sconf_isteps q k : itsteps q (sconf q k).
Proof.
  induction k as [|k IH]; [done|]. etrans; [exact IH|].
  change (sconf q (S k)) with ((sched_step (sconf q k) k).2).
  destruct (sched_step_spec (sconf q k) k) as [(ev & _ & Hs)|(_ & -> & _)]; [|done].
  apply rtc_once. by eexists.
Qed.

(** ** Lifting process steps backwards *)

Lemma map_preimage (f : expr → expr) (M : gmap nat expr) (X : gmultiset expr) :
  soup M = gmultiset_map f X → ∃ M0, f <$> M0 = M ∧ soup M0 = X.
Proof.
  revert X. induction M as [|i y M Hi IH] using map_ind; intros X HX.
  - exists ∅. rewrite fmap_empty. split; [done|]. rewrite soup_empty.
    destruct (gmultiset_choose_or_empty X) as [[x Hx]| ->]; [|done].
    exfalso. assert (f x ∈ gmultiset_map f X) as H by (apply elem_of_gmultiset_map; eauto).
    rewrite <-HX, soup_empty in H. multiset_solver.
  - rewrite soup_insert in HX by done.
    assert (y ∈ gmultiset_map f X) as Hy by (rewrite <-HX; multiset_solver).
    apply elem_of_gmultiset_map in Hy as (x & -> & Hx).
    rewrite (gmultiset_disj_union_difference' x X Hx), gmultiset_map_disj_union,
      gmultiset_map_singleton in HX.
    assert (soup M = gmultiset_map f (X ∖ {[+ x +]})) as HM by multiset_solver.
    destruct (IH _ HM) as (M0 & HM0 & HX0).
    assert (M0 !! i = None) as Hi0.
    { rewrite <-HM0, lookup_fmap in Hi. by destruct (M0 !! i). }
    exists (<[i := x]> M0). split.
    + by rewrite fmap_insert, HM0.
    + rewrite soup_insert, HX0 by done. rewrite (comm_L (⊎)). symmetry.
      by apply gmultiset_disj_union_difference'.
Qed.

Lemma map_upd2_back (M : gmap nat expr) i j e f e' f' :
  i ≠ j → M !! i = Some e' → M !! j = Some f' →
  <[j := f']> (<[i := e']> (<[j := f]> (<[i := e]> M))) = M.
Proof.
  intros Hij Hi Hj. apply map_eq. intros k.
  destruct (decide (k = j)) as [->|Hkj]; [by rewrite lookup_insert_eq|].
  rewrite lookup_insert_ne by lia.
  destruct (decide (k = i)) as [->|Hki]; [by rewrite lookup_insert_eq|].
  by rewrite !lookup_insert_ne by lia.
Qed.

Lemma preduction_back q p1 : preduction p1 (erase q) → ∃ ev q1, erase q1 = p1 ∧ itstep q1 ev q.
Proof.
  destruct q as [C' M]. unfold erase, preduction; simpl. rewrite pstep_iff. intros H.
  remember (C', soup M) as p2 eqn:Hp2. remember PTau as π eqn:Hπ.
  destruct H as [C E e σ e' Hst HC|C E e e' Hst|C E e ℓ c e' Hst HC HcE Hce
    |C E e κ o c e' Hst HC HcE Hce|C E e v e' Hst
    |C E o v e e' f f' He Hf|C E o e e' f f' He Hf HC
    |C E o b e e' f f' He Hf|C E e o1 o2 e' Hst HC]; try discriminate;
    injection Hp2 as <- HE; symmetry in HE.
  - destruct (soup_extract M E e' HE) as (i & Hi & HEi).
    exists (EvBeta i), (C, <[i := e]> M). split.
    + unfold erase; simpl. by rewrite (soup_update M i e' e Hi), HEi.
    + replace (C, M) with (C, <[i := e']> (<[i := e]> M)) by (by rewrite insert_insert_eq, insert_id).
      split; [|done]. eapply p_act_beta; [by rewrite lookup_insert_eq|done].
  - destruct (soup_extract M E e' HE) as (i & Hi & HEi).
    exists (EvNew i ℓ c), (C, <[i := e]> M). split.
    + unfold erase; simpl. by rewrite (soup_update M i e' e Hi), HEi.
    + replace (C ∪ {[c]}, M) with (C ∪ {[c]}, <[i := e']> (<[i := e]> M))
        by (by rewrite insert_insert_eq, insert_id).
      split; [|done]. eapply p_act_new; [by rewrite lookup_insert_eq|done|done|].
      rewrite (soup_update M i e' e Hi), HEi, echans_disj_union, echans_singleton. set_solver.
  - destruct (soup_extract M E e' HE) as (i & Hi & HEi).
    exists (EvNewAt i κ o c), (C, <[i := e]> M). split.
    + unfold erase; simpl. by rewrite (soup_update M i e' e Hi), HEi.
    + replace (C ∪ {[c]}, M) with (C ∪ {[c]}, <[i := e']> (<[i := e]> M))
        by (by rewrite insert_insert_eq, insert_id).
      split; [|done]. eapply p_act_new_at; [by rewrite lookup_insert_eq|done|done|].
      rewrite (soup_update M i e' e Hi), HEi, echans_disj_union, echans_singleton. set_solver.
  - destruct (soup_extract M _ (App v EUnit) HE) as (j & Hj & HEj).
    destruct (soup_extract _ E e' HEj) as (i & Hi & HEi).
    assert (i ≠ j) as Hij by (intros ->; by rewrite lookup_delete_eq in Hi).
    assert (M !! i = Some e') as HiM by (by rewrite lookup_delete_ne in Hi).
    exists (EvSpawn i j v), (C, <[i := e]> (delete j M)). split.
    + unfold erase; simpl. by rewrite (soup_update (delete j M) i e' e Hi), HEi.
    + replace (C, M) with (C, <[j := App v EUnit]> (<[i := e']> (<[i := e]> (delete j M)))).
      * split; [|done]. eapply p_act_spawn; [by rewrite lookup_insert_eq|done|].
        rewrite lookup_insert_ne by lia. apply lookup_delete_eq.
      * f_equal. rewrite insert_insert_eq, (insert_id _ i e' Hi). by apply insert_delete_id.
  - destruct (soup_extract M _ f' HE) as (j & Hj & HEj).
    destruct (soup_extract _ E e' HEj) as (i & Hi & HEi).
    assert (i ≠ j) as Hij by (intros ->; by rewrite lookup_delete_eq in Hi).
    rewrite lookup_delete_ne in Hi by done.
    exists (EvMsg i j o v), (C, <[j := f]> (<[i := e]> M)). split.
    + unfold erase; simpl. destruct (soup_update2 M i j e' f' e f Hij Hi Hj) as [_ ->].
      by rewrite delete_delete, HEi.
    + replace (C, M) with (C, <[j := f']> (<[i := e']> (<[j := f]> (<[i := e]> M))))
        by (by rewrite map_upd2_back).
      split; [|done]. eapply p_act_msg; [done| |by rewrite lookup_insert_eq|done|done].
      rewrite lookup_insert_ne by lia. by rewrite lookup_insert_eq.
  - destruct (soup_extract M _ f' HE) as (j & Hj & HEj).
    destruct (soup_extract _ E e' HEj) as (i & Hi & HEi).
    assert (i ≠ j) as Hij by (intros ->; by rewrite lookup_delete_eq in Hi).
    rewrite lookup_delete_ne in Hi by done.
    exists (EvClose i j o), (C, <[j := f]> (<[i := e]> M)). split.
    + unfold erase; simpl. destruct (soup_update2 M i j e' f' e f Hij Hi Hj) as [_ ->].
      by rewrite delete_delete, HEi.
    + replace (C ∖ {[ech o]}, M)
        with (C ∖ {[ech o]}, <[j := f']> (<[i := e']> (<[j := f]> (<[i := e]> M))))
        by (by rewrite map_upd2_back).
      split; [|done]. eapply p_act_close; [done| |by rewrite lookup_insert_eq|done|done|done].
      rewrite lookup_insert_ne by lia. by rewrite lookup_insert_eq.
  - destruct (soup_extract M _ f' HE) as (j & Hj & HEj).
    destruct (soup_extract _ E e' HEj) as (i & Hi & HEi).
    assert (i ≠ j) as Hij by (intros ->; by rewrite lookup_delete_eq in Hi).
    rewrite lookup_delete_ne in Hi by done.
    exists (EvChoice i j o b), (C, <[j := f]> (<[i := e]> M)). split.
    + unfold erase; simpl. destruct (soup_update2 M i j e' f' e f Hij Hi Hj) as [_ ->].
      by rewrite delete_delete, HEi.
    + replace (C, M) with (C, <[j := f']> (<[i := e']> (<[j := f]> (<[i := e]> M))))
        by (by rewrite map_upd2_back).
      split; [|done]. eapply p_act_choice; [done| |by rewrite lookup_insert_eq|done|done].
      rewrite lookup_insert_ne by lia. by rewrite lookup_insert_eq.
  - unfold emapE in HE.
    destruct (map_preimage (emap (csub o1 o2)) M (E ⊎ {[+ e' +]}) HE) as (M0 & HM0 & HX0).
    destruct (soup_extract M0 E e' HX0) as (i & Hi & HEi).
    exists (EvLink i o1 o2), (C, <[i := e]> M0). split.
    + unfold erase; simpl. by rewrite (soup_update M0 i e' e Hi), HEi.
    + replace (C ∖ {[ech o1]}, M)
        with (C ∖ {[ech o1]}, emap (csub o1 o2) <$> (<[i := e']> (<[i := e]> M0)))
        by (by rewrite insert_insert_eq, insert_id, HM0).
      split; [|done]. eapply p_act_link; [by rewrite lookup_insert_eq|done|done].
Qed.

Lemma pred_star_back p p' :
  pred_star p p' → ∀ q, erase q = p' → ∃ q0, erase q0 = p ∧ itsteps q0 q.
Proof.
  induction 1 as [p|p p1 p2 Hst _ IH]; intros q Hq.
  - exists q. by split.
  - destruct (IH q Hq) as (q1 & Hq1 & Hsteps).
    destruct (preduction_back q1 p) as (ev & q0 & Hq0 & Hs); [by rewrite Hq1|].
    exists q0. split; [done|]. eapply rtc_l; [by exists ev|exact Hsteps].
Qed.

Lemma isteps_fun q0 q :
  itsteps q0 q →
  ∃ m (pr : nat → config) (pl : nat → event), pr 0 = q0 ∧ pr m = q ∧
    ∀ i, i < m → itstep (pr i) (pl i) (pr (S i)).
Proof.
  induction 1 as [q|q0 q1 q [ev Hs] _ (m & pr & pl & H0 & Hm & Hst)].
  - exists 0, (λ _, q), (λ _, EvBeta 0). split_and!; [done|done|lia].
  - exists (S m), (λ i, match i with 0 => q0 | S i => pr i end),
      (λ i, match i with 0 => ev | S i => pl i end).
    split_and!; [done|done|]. intros [|i] Hi; simpl; [by rewrite H0|]. apply Hst. lia.
Qed.

(** ** The theorem *)

Theorem lock_free_reach_of p : lock_free p → lock_free_reach p.
Proof.
  intros Hlf q t Hq Hp.
  destruct (pred_star_back p (erase q) Hq q eq_refl) as (q0 & Hq0 & Hsteps).
  destruct (isteps_fun q0 q Hsteps) as (m & pr & pl & H0 & Hm & Hst).
  set (r := λ i, if decide (i < m) then pr i else sconf q (i - m)).
  set (l := λ i, if decide (i < m) then Some (pl i) else slab q (i - m)).
  assert (∀ i, i < m → r i = pr i ∧ l i = Some (pl i)) as Hpre.
  { intros i Hi. unfold r, l. by destruct (decide (i < m)); [|lia]. }
  assert (∀ i, m ≤ i → r i = sconf q (i - m) ∧ l i = slab q (i - m)) as Hsuf.
  { intros i Hi. unfold r, l. by destruct (decide (i < m)); [lia|]. }
  assert (r m = q) as Hrm.
  { destruct (Hsuf m (Nat.le_refl _)) as [-> _]. by rewrite Nat.sub_diag. }
  assert (erase (r 0) = p) as Hr0.
  { destruct (decide (0 < m)) as [Hm0|Hm0].
    - destruct (Hpre 0 Hm0) as [-> _]. by rewrite H0.
    - assert (m = 0) as -> by lia. rewrite Hrm, <-Hm, H0. done. }
  assert (maximal r l) as Hmax.
  { intros i. unfold run_step. destruct (decide (i < m)) as [Him|Him].
    - destruct (Hpre i Him) as [-> ->]. left. exists (pl i). split; [done|].
      destruct (decide (S i < m)) as [HSi|HSi].
      + destruct (Hpre (S i) HSi) as [-> _]. by apply Hst.
      + assert (S i = m) as HSm by lia. rewrite HSm, Hrm, <-Hm, <-HSm. by apply Hst.
    - destruct (Hsuf i) as [-> ->]; [lia|]. destruct (Hsuf (S i)) as [-> _]; [lia|].
      replace (S i - m) with (S (i - m)) by lia. apply (srun_max q (i - m)). }
  assert (wfair r l) as Hfair.
  { intros u i. destruct (srun_fair q u (i - m)) as (j & Hj & Hu). exists (j + m).
    split; [lia|]. destruct (Hsuf (j + m)) as [-> ->]; [lia|]. by rewrite Nat.add_sub. }
  assert (pend (r m) t) as Hpm by (by rewrite Hrm).
  destruct (Hlf r l Hr0 Hmax Hfair m t Hpm) as (j & Hj & Htj).
  destruct (Hsuf j Hj) as [_ Hlj]. rewrite Hlj in Htj.
  destruct (srun_max q (j - m)) as [(ev & Hev & Hs)|(_ & _ & He)].
  - exists (sconf q (j - m)), ev, (sconf q (S (j - m))). split_and!.
    + apply sconf_isteps.
    + done.
    + unfold slab in Htj, Hev. rewrite Hev in Htj. done.
  - unfold slab in Htj, He. rewrite He in Htj. simpl in Htj. set_solver.
Qed.
