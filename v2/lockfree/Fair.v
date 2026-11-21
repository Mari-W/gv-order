(** * Runs, weak fairness and lock freedom (stage S1)

    A run is a sequence of configurations with the event of every step.
    A maximal run is infinite, or finite and ending in a stuck
    configuration. A finite maximal run repeats its stuck end with no
    event forever, so every run is a function on ℕ. Runs take only the
    steps of a closed configuration ([itstep]).

    Weak fairness is per thread: from every position on, every thread
    eventually takes part in a step or is disabled. A thread is pending
    when its redex is a session action, a link included. A run is lock
    free when every pending thread later takes part in a step. A process
    is lock free when every weakly fair maximal run from a lifting of it
    is lock free. *)

From stdpp Require Import relations.
From GV Require Export lang.Safety.

(** ** Renaming and the redex *)

Definition amap (g : cend → cend) (a : action) : action :=
  match a with
  | ABeta => ABeta
  | ANew => ANew
  | ASpawn v => ASpawn (emap g v)
  | ARecv o => ARecv (g o)
  | ASend o v => ASend (g o) (emap g v)
  | AClose o => AClose (g o)
  | ALink o1 o2 => ALink (g o1) (g o2)
  | ASel o i => ASel (g o) i
  | ABra o => ABra (g o)
  end.

Lemma act_op_emap g k v : act_op k (emap g v) = amap g <$> act_op k v.
Proof.
  destruct k, v as [| | | | |v1 v2| | | | | | |]; simpl; try done.
  all: destruct v1, v2; done.
Qed.

Lemma act_emap g e : act (emap g e) = amap g <$> act e.
Proof.
  induction e; simpl; try done; rewrite ?is_val_emap.
  - destruct (is_val e1); [|done]. destruct (is_val e2); [|done]. by destruct e1.
  - by destruct (is_val e1).
  - destruct (is_val e1); [|done]. by destruct e1.
  - destruct (is_val e1); [|done]. by destruct e1.
  - destruct (is_val e1); [|done]. by destruct e1.
  - destruct (is_val e); [|done]. apply act_op_emap.
Qed.

Lemma amap_admin g a : is_admin (amap g a) ↔ is_admin a.
Proof. by destruct a. Qed.

Lemma amap_sess g a : is_sess (amap g a) ↔ is_sess a.
Proof. unfold is_sess. destruct a; simpl; split; eauto. Qed.

(** ** Threads of a configuration *)

Definition pend (q : config) (t : nat) : Prop :=
  ∃ e a, q.2 !! t = Some e ∧ act e = Some a ∧ is_sess a.

Definition admin_at (q : config) (t : nat) : Prop :=
  ∃ e a, q.2 !! t = Some e ∧ act e = Some a ∧ is_admin a.

Lemma istep_other_pend q ev q' t : istep q ev q' → t ∉ ev_parts ev → pend q t → pend q' t.
Proof.
  intros Hst Ht (e & a & He & Ha & Hs).
  destruct (istep_other q ev q' t e Hst Ht He) as [g Hg].
  exists (emap g e), (amap g a). rewrite act_emap, Ha. split_and!; [done|done|].
  by apply amap_sess.
Qed.

Lemma istep_other_admin q ev q' t : istep q ev q' → t ∉ ev_parts ev → admin_at q t → admin_at q' t.
Proof.
  intros Hst Ht (e & a & He & Ha & Hs).
  destruct (istep_other q ev q' t e Hst Ht He) as [g Hg].
  exists (emap g e), (amap g a). rewrite act_emap, Ha. split_and!; [done|done|].
  by apply amap_admin.
Qed.

(** An actor of a closed step acts by a step of its term, and an
    administrative step leaves its continuation, up to the renaming of a
    link. *)
Lemma itstep_actor q ev q' t e :
  itstep q ev q' → t ∈ ev_parts ev → q.2 !! t = Some e →
  ∃ α e', tstep e α e' ∧ (admin_lbl α → ∃ g, q'.2 !! t = Some (emap g e')).
Proof.
  intros [Hst Hτ] Ht Hte.
  destruct Hst; simpl in *; try discriminate.
  all: set_unfold in Ht; destruct_or?; subst.
  all: repeat match goal with
    | H1 : ?M !! ?i = Some ?a, H2 : ?M !! ?i = Some ?b |- _ =>
        rewrite H1 in H2; injection H2 as <-
    end.
  all: eexists _, _; split; [eassumption|]; intros Had; simpl in Had; try contradiction.
  - exists id. rewrite emap_id. by rewrite lookup_insert_eq.
  - exists id. rewrite emap_id. by rewrite lookup_insert_eq.
  - exists id. rewrite emap_id. rewrite lookup_insert_ne by (intros ->; congruence).
    by rewrite lookup_insert_eq.
  - exists (csub o1 o2). by rewrite lookup_fmap, lookup_insert_eq.
Qed.

Lemma admin_step q ev q' t e a :
  itstep q ev q' → t ∈ ev_parts ev → q.2 !! t = Some e → act e = Some a → is_admin a →
  ∃ α e' g, admin_lbl α ∧ tstep e α e' ∧ q'.2 !! t = Some (emap g e').
Proof.
  intros Hst Ht He Ha Had.
  destruct (itstep_actor q ev q' t e Hst Ht He) as (α & e' & Hs & Hq).
  destruct (act_step _ _ _ Hs) as (a' & Ha' & Ho). rewrite Ha in Ha'. simplify_eq.
  assert (admin_lbl α) as Hα by (by apply (offers_admin a')).
  destruct (Hq Hα) as [g Hg]. exists α, e', g. auto.
Qed.

(** An administrative redex is enabled. A link needs a restricted end,
    because P-Act-Link removes one. *)
Lemma admin_enabled q t e a :
  q.2 !! t = Some e → act e = Some a → is_admin a →
  (∀ o1 o2, a = ALink o1 o2 → ech o1 ∈ q.1 ∨ ech o2 ∈ q.1) → tenabled q t.
Proof.
  destruct q as [C M]. intros He Ha Had Hln. simpl in *.
  destruct a as [| |v|o|o v|o|o1 o2|o i|o]; try done.
  - destruct (act_offer e ABeta LBeta Ha I) as [e' Hs].
    eexists _, _. split; [split; [by eapply p_act_beta|done]|set_solver].
  - set (c := fresh (C ∪ echans (soup M))).
    assert (c ∉ C ∪ echans (soup M)) as Hc by apply is_fresh.
    destruct (act_offer e ANew (LNew c) Ha I) as [e' Hs].
    eexists _, _. split; [split; [eapply p_act_new; [done|done|set_solver|set_solver]|done]|set_solver].
  - destruct (act_offer e (ASpawn v) (LSpawn v) Ha eq_refl) as [e' Hs].
    set (j := fresh (dom M)).
    assert (M !! j = None) as Hj by (apply not_elem_of_dom, is_fresh).
    eexists _, _. split; [split; [by eapply p_act_spawn|done]|set_solver].
  - destruct (act_offer e (ALink o1 o2) (LSess (SLink {[o1; o2]})) Ha eq_refl) as [e' Hs].
    destruct (Hln o1 o2 eq_refl) as [Hc|Hd]; simpl in *.
    + eexists _, _. split; [split; [by eapply p_act_link|done]|set_solver].
    + assert (tstep e (LSess (SLink {[o2; o1]})) e') as Hs' by (by rewrite upair_comm).
      eexists _, _. split; [split; [by eapply p_act_link|done]|set_solver].
Qed.

(** ** Runs *)

Definition lparts (l : option event) : gset nat :=
  match l with Some ev => ev_parts ev | None => ∅ end.

Definition run_step (r : nat → config) (l : nat → option event) (i : nat) : Prop :=
  (∃ ev, l i = Some ev ∧ itstep (r i) ev (r (S i))) ∨ (stuck (r i) ∧ r (S i) = r i ∧ l i = None).

Definition maximal (r : nat → config) (l : nat → option event) : Prop := ∀ i, run_step r l i.

(** Weak fairness, in the constructive form the criterion uses. *)
Definition wfair (r : nat → config) (l : nat → option event) : Prop :=
  ∀ t i, ∃ j, i ≤ j ∧ (t ∈ lparts (l j) ∨ ¬ tenabled (r j) t).

Definition lf_run (r : nat → config) (l : nat → option event) : Prop :=
  ∀ i t, pend (r i) t → ∃ j, i ≤ j ∧ t ∈ lparts (l j).

Definition lock_free (p : proc) : Prop :=
  ∀ r l, erase (r 0) = p → maximal r l → wfair r l → lf_run r l.

(** ** Dependencies

    A pending thread t waits for s when s is another thread that mentions
    the partner of an end of t's redex. [local_progress] says that the
    chain of waits from every pending thread reaches an enabled
    thread. *)

(** ** Runs from a process reach reachable states *)

Section runs.
  Context (r : nat → config) (l : nat → option event) (Hmax : maximal r l).

  Lemma run_reach i : pred_star (erase (r 0)) (erase (r i)).
  Proof.
    induction i as [|i IH]; [done|]. etrans; [exact IH|].
    destruct (Hmax i) as [(ev & _ & Hs)|(_ & -> & _)]; [|done].
    apply rtc_once. by eapply itstep_erase.
  Qed.

  Lemma run_other i t e :
    t ∉ lparts (l i) → (r i).2 !! t = Some e → ∃ g, (r (S i)).2 !! t = Some (emap g e).
  Proof.
    intros Ht He. destruct (Hmax i) as [(ev & Hl & Hs)|(_ & -> & _)].
    - rewrite Hl in Ht. by eapply istep_other; [apply Hs|..].
    - exists id. by rewrite emap_id.
  Qed.

  Lemma run_pend i t : t ∉ lparts (l i) → pend (r i) t → pend (r (S i)) t.
  Proof.
    intros Ht Hp. destruct (Hmax i) as [(ev & Hl & Hs)|(_ & -> & _)]; [|done].
    rewrite Hl in Ht. by eapply istep_other_pend; [apply Hs|..].
  Qed.

  Lemma run_admin i t : t ∉ lparts (l i) → admin_at (r i) t → admin_at (r (S i)) t.
  Proof.
    intros Ht Hp. destruct (Hmax i) as [(ev & Hl & Hs)|(_ & -> & _)]; [|done].
    rewrite Hl in Ht. by eapply istep_other_admin; [apply Hs|..].
  Qed.

  Lemma run_admin_step i t e a :
    t ∈ lparts (l i) → (r i).2 !! t = Some e → act e = Some a → is_admin a →
    ∃ α e' g, admin_lbl α ∧ tstep e α e' ∧ (r (S i)).2 !! t = Some (emap g e').
  Proof.
    intros Ht He Ha Had. destruct (Hmax i) as [(ev & Hl & Hs)|(_ & _ & Hl)].
    - rewrite Hl in Ht. by eapply admin_step.
    - rewrite Hl in Ht. set_solver.
  Qed.
End runs.
