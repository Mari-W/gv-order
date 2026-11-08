(** * Lock freedom gives Padovani's lock freedom (lock-freedom plan §11)

    [lock_free_reach_of]: a lock-free process (every weakly fair maximal
    run serves every pending thread, Fair.v) is lock free in the sense
    of padovani2014deadlock, Definition II.1: from every reachable
    configuration with a pending thread, some continuation lets that
    thread take part in a step. No typing and no τ-divergence premise
    is needed.

    Proof. A configuration reachable from p is the end of an
    instrumented run from a lifting of p ([pred_star_back], which lifts
    process steps backwards with the thread names of the end). From it
    a computable scheduler builds a weakly fair maximal run
    ([sconf]): at position k it fires a step of thread [enum k] if that
    thread is enabled, and every thread name occurs infinitely often in
    [enum]. Lock freedom of the concatenated run fires the pending
    thread after the reachable configuration.

    The converse fails in the untyped semantics. Two threads race on a
    free channel c: u receives on c in a loop, s sends on c in a loop,
    and t sends on c once. From every reachable state some continuation
    lets t meet u, so lock_free_reach holds. A weakly fair run may still
    pair u with s forever, because t is enabled only while u sits at its
    receive and u leaves it with β steps in between. So t starves and
    lock_free fails. Typing excludes the race (one holder per end), and
    whether the converse holds for typed processes is left open. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export lockfree.Fair.

(** ** Computed steps

    [act_offer] (Safety.v) with the continuation as data. The proof is
    the same. *)
Lemma act_offer_sig e a α : act e = Some a → offers a α → {e' | tstep e α e'}.
Proof.
  revert a α.
  induction e as [x| |k|c|e0 IHe|e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2
                 |e1 IH1 e2 IH2|e1 IH|e1 IH|e0 IH0 e1 IH1 e2 IH2
                 |e1 IH];
    simpl; intros a α Ha Hoff; try discriminate.
  - (* application *)
    destruct (is_val e1) eqn:Hb1;
      [|destruct (IH1 _ _ Ha Hoff) as [e1' Hst]; exists (App e1' e2);
        by apply TStepAppL].
    destruct (is_val e2) eqn:Hb2;
      [|destruct (IH2 _ _ Ha Hoff) as [e2' Hst]; exists (App e1 e2');
        apply TStepAppR; [by rewrite Hb1|done]].
    destruct e1 as [| |k| |e0 | | | | | | | | ]; try discriminate.
    + (* a concurrency primitive *)
      destruct k; simplify_eq.
      * (* T-Act-New *)
        destruct e2 as [| | | | | | | | | | | | ]; try discriminate.
        simplify_eq. destruct α as [|σ|c|w]; try done.
        exists (Pair (Chan c) (Chan c)). apply TStepHead, HeadNew.
      * (* T-Act-Spawn *)
        destruct α as [|σ|c|w]; try done. simpl in Hoff. simplify_eq.
        exists EUnit. apply TStepHead, HeadSpawn. by rewrite Hb2.
      * (* T-Act-Recv *)
        destruct e2 as [| | |c | | | | | | | | | ]; try discriminate.
        simplify_eq. destruct α as [|σ| | ]; try done.
        destruct σ as [d w|d w|d|cd|d b|d b]; try done.
        destruct Hoff as [-> Hw]. exists (Pair w (Chan d)).
        by apply TStepHead, HeadRecv.
      * (* T-Act-Send *)
        destruct e2 as [| | | | | |v w | | | | | | ]; try discriminate.
        destruct w as [| | |d | | | | | | | | | ]; try discriminate.
        simplify_eq. destruct α as [|σ| | ]; try done.
        destruct σ as [d' w'|d' w'|d'|cd'|d' b|d' b]; try done.
        destruct Hoff as [-> ->].
        pose proof (is_val_of_true _ Hb2) as Hv2. simpl in Hv2.
        apply andb_True in Hv2 as [Hv _].
        exists (Chan d'). by apply TStepHead, HeadSend.
      * (* T-Act-Close *)
        destruct e2 as [| | |c | | | | | | | | | ]; try discriminate.
        simplify_eq. destruct α as [|σ| | ]; try done.
        destruct σ as [d w|d w|d|cd|d b|d b]; try done. simpl in Hoff. simplify_eq.
        exists EUnit. by apply TStepHead, HeadClos.
      * (* T-Act-Link *)
        destruct e2 as [| | | | | |v w | | | | | | ]; try discriminate.
        destruct v as [| | |c' | | | | | | | | | ]; try discriminate.
        destruct w as [| | |d' | | | | | | | | | ]; try discriminate.
        simplify_eq.
        destruct α as [|σ| | ]; try done.
        destruct σ as [| | |cd''| | ]; try done.
        simpl in Hoff. subst cd''.
        exists EUnit. by apply TStepHead, HeadLink.
      * (* T-Act-Force: [EBox _] is unconditionally a value *)
        destruct e2 as [| | | | | | | | | | | |eb ]; try discriminate.
        simplify_eq. destruct α; try done.
        exists (subst1 (EBox eb) eb). by apply TStepHead, HeadForce.
      * (* T-Act-Select₁ *)
        destruct e2 as [| | |c | | | | | | | | | ]; try discriminate.
        simplify_eq. destruct α as [|σ| | ]; try done.
        destruct σ; try done. destruct Hoff as [-> <-].
        exists (Chan c0). by apply TStepHead, HeadSel1.
      * (* T-Act-Select₂ *)
        destruct e2 as [| | |c | | | | | | | | | ]; try discriminate.
        simplify_eq. destruct α as [|σ| | ]; try done.
        destruct σ; try done. destruct Hoff as [-> <-].
        exists (Chan c0). by apply TStepHead, HeadSel2.
      * (* T-Act-Branch *)
        destruct e2 as [| | |c | | | | | | | | | ]; try discriminate.
        simplify_eq. destruct α as [|σ| | ]; try done.
        destruct σ; try done. simpl in Hoff. subst.
        eexists. by apply TStepHead, HeadBra.
    + (* T-Act-App *)
      simplify_eq. destruct α; try done.
      exists (subst1 e2 e0). apply TStepHead, HeadApp. by rewrite Hb2.
  - (* pair *)
    destruct (is_val e1) eqn:Hb1.
    + destruct (IH2 _ _ Ha Hoff) as [e2' Hst]. exists (Pair e1 e2').
      apply TStepPairR; [by rewrite Hb1|done].
    + destruct (IH1 _ _ Ha Hoff) as [e1' Hst]. exists (Pair e1' e2).
      by apply TStepPairL.
  - (* let ∗ = e1 in e2 *)
    destruct (is_val e1) eqn:Hb1;
      [|destruct (IH1 _ _ Ha Hoff) as [e1' Hst]; exists (LetU e1' e2);
        by apply TStepLetU].
    destruct e1; try discriminate. simplify_eq.
    destruct α; try done. exists e2. by apply TStepHead, HeadLetU.
  - (* let ⟨a,b⟩ = e1 in e2 *)
    destruct (is_val e1) eqn:Hb1;
      [|destruct (IH1 _ _ Ha Hoff) as [e1' Hst]; exists (LetP e1' e2);
        by apply TStepLetP].
    destruct e1 as [| | | | | |u w | | | | | | ]; try discriminate.
    simplify_eq. destruct α; try done.
    pose proof (is_val_of_true _ Hb1) as Hv1. simpl in Hv1.
    apply andb_True in Hv1 as [Hu Hw].
    exists (subst2 u w e2). by apply TStepHead, HeadLetP.
  - (* inl *)
    destruct (IH _ _ Ha Hoff) as [e1' Hst]. exists (Inj1 e1').
    by apply TStepInj1.
  - (* inr *)
    destruct (IH _ _ Ha Hoff) as [e1' Hst]. exists (Inj2 e1').
    by apply TStepInj2.
  - (* case *)
    destruct (is_val e0) eqn:Hb0;
      [|destruct (IH0 _ _ Ha Hoff) as [e0' Hst]; exists (Case e0' e1 e2);
        by apply TStepCase].
    destruct e0 as [| | | | | | | | |v |w | | ]; try discriminate.
    + simplify_eq. destruct α; try done. simpl in Hb0.
      exists (subst1 v e1). apply TStepHead, HeadCase1. by rewrite Hb0.
    + simplify_eq. destruct α; try done. simpl in Hb0.
      exists (subst1 w e2). apply TStepHead, HeadCase2. by rewrite Hb0.
Qed.
(** ** Partners of an enabled thread *)

Definition partner_ok (a : action) (b : option action) : Prop :=
  match a, b with
  | ARecv c, Some (ASend c' _) => c' = c
  | ASend c _, Some (ARecv c') => c' = c
  | AClos c, Some (AClos c') => c' = c
  | ASel c _, Some (ABra c') => c' = c
  | ABra c, Some (ASel c' _) => c' = c
  | _, _ => False
  end.

Global Instance partner_ok_dec a b : Decision (partner_ok a b).
Proof. destruct a, b as [[]|]; simpl; apply _. Defined.

Definition partner_need (C : gset chan) (M : gmap nat expr) (t : nat) (a : action) : Prop :=
  match a with
  | ABeta | ANew | ASpawn _ => True
  | ALink c d => c ∈ C ∨ d ∈ C
  | AClos c => c ∈ C ∧ ∃ j f, j ≠ t ∧ M !! j = Some f ∧ partner_ok a (act f)
  | _ => ∃ j f, j ≠ t ∧ M !! j = Some f ∧ partner_ok a (act f)
  end.

Lemma istep_part_some q L q' t : istep q L q' → t ∈ L → is_Some (q.2 !! t).
Proof.
  destruct 1; simpl; intros Ht; rewrite ?elem_of_union, ?elem_of_singleton in Ht;
    destruct_or?; subst; eauto.
Qed.

Lemma istep_nonempty q L q' : istep q L q' → ∃ t, t ∈ L.
Proof. destruct 1; exists i; set_solver. Qed.

Lemma enabled_partner C M t e a :
  enabled (C, M) t → M !! t = Some e → act e = Some a → partner_need C M t a.
Proof.
  intros (L & q' & Hst & Ht) He Ha.
  assert (∀ α e', tstep e α e' → offers a α) as Hoff.
  { intros α e' Hs. destruct (act_step _ _ _ Hs) as (a' & Ha' & Ho). congruence. }
  remember (C, M) as q0 eqn:Hq0.
  destruct Hst as [C0 M0 i e0 e0' Hi Hs|C0 M0 i e0 c e0' Hi Hs HC Hc|C0 M0 i j e0 v e0' Hi Hs Hj
    |C0 M0 i j c v e0 e0' f f' Hij Hi Hj He0 Hf|C0 M0 i j c e0 e0' f f' Hij Hi Hj He0 Hf HC
    |C0 M0 i j c b e0 e0' f f' Hij Hi Hj He0 Hf|C0 M0 i e0 c d e0' Hi Hs HC];
    injection Hq0 as -> ->; simpl in Ht.
  - apply elem_of_singleton in Ht as ->. rewrite He in Hi. injection Hi as <-.
    apply Hoff in Hs. destruct a; simpl in Hs |- *; tauto.
  - apply elem_of_singleton in Ht as ->. rewrite He in Hi. injection Hi as <-.
    apply Hoff in Hs. destruct a; simpl in Hs |- *; tauto.
  - apply elem_of_singleton in Ht as ->. rewrite He in Hi. injection Hi as <-.
    apply Hoff in Hs. destruct a; simpl in Hs |- *; tauto.
  - apply elem_of_union in Ht as [Ht|Ht]; apply elem_of_singleton in Ht as ->.
    + rewrite He in Hi. injection Hi as <-. apply Hoff, offers_send in He0 as ->.
      destruct (act_step _ _ _ Hf) as (b & Hb & Hob). apply offers_recv in Hob as ->.
      simpl. exists j, f. split_and!; [lia|done|by rewrite Hb].
    + rewrite He in Hj. injection Hj as <-. apply Hoff, offers_recv in Hf as ->.
      destruct (act_step _ _ _ He0) as (b & Hb & Hob). apply offers_send in Hob as ->.
      simpl. exists i, e0. split_and!; [lia|done|by rewrite Hb].
  - apply elem_of_union in Ht as [Ht|Ht]; apply elem_of_singleton in Ht as ->.
    + rewrite He in Hi. injection Hi as <-. apply Hoff, offers_clos in He0 as ->.
      destruct (act_step _ _ _ Hf) as (b & Hb & Hob). apply offers_clos in Hob as ->.
      simpl. split; [done|]. exists j, f. split_and!; [lia|done|by rewrite Hb].
    + rewrite He in Hj. injection Hj as <-. apply Hoff, offers_clos in Hf as ->.
      destruct (act_step _ _ _ He0) as (b & Hb & Hob). apply offers_clos in Hob as ->.
      simpl. split; [done|]. exists i, e0. split_and!; [lia|done|by rewrite Hb].
  - apply elem_of_union in Ht as [Ht|Ht]; apply elem_of_singleton in Ht as ->.
    + rewrite He in Hi. injection Hi as <-. apply Hoff, offers_sel in He0 as ->.
      destruct (act_step _ _ _ Hf) as (b' & Hb & Hob). apply offers_bra in Hob as ->.
      simpl. exists j, f. split_and!; [lia|done|by rewrite Hb].
    + rewrite He in Hj. injection Hj as <-. apply Hoff, offers_bra in Hf as ->.
      destruct (act_step _ _ _ He0) as (b' & Hb & Hob). apply offers_sel in Hob as ->.
      simpl. exists i, e0. split_and!; [lia|done|by rewrite Hb].
  - apply elem_of_singleton in Ht as ->. rewrite He in Hi. injection Hi as <-.
    apply Hoff, offers_link in Hs as (c' & d' & -> & Hcd). simpl.
    assert (c ∈ ({[c'; d']} : gset chan)) by (rewrite <-Hcd; set_solver). set_solver.
Qed.

(** ** Deciding whether a thread can take part, with the step *)

Lemma find_in_map {A} (M : gmap nat A) (P : nat → A → Prop) `{∀ j x, Decision (P j x)} :
  {jx : nat * A | M !! jx.1 = Some jx.2 ∧ P jx.1 jx.2} + {∀ j x, M !! j = Some x → ¬ P j x}.
Proof.
  destruct (list_find (λ jx : nat * A, P jx.1 jx.2) (map_to_list M)) as [[k [j x]]|] eqn:Hf.
  - left. exists (j, x). apply list_find_Some in Hf as (Hk & HP & _). split; [|done].
    apply elem_of_map_to_list. by eapply list_elem_of_lookup_2.
  - right. intros j x Hjx HP. apply list_find_None in Hf. rewrite Forall_forall in Hf.
    apply (Hf (j, x)); [|done]. by apply elem_of_map_to_list.
Qed.

Lemma try_thread (q : config) (t : nat) :
  {Lq : gset nat * config | istep q Lq.1 Lq.2 ∧ t ∈ Lq.1} + {¬ enabled q t}.
Proof.
  destruct q as [C M].
  destruct (M !! t) as [e|] eqn:He.
  2:{ right. intros (L & q' & Hst & Ht). destruct (istep_part_some _ _ _ _ Hst Ht) as [? Hx].
      simpl in Hx. congruence. }
  destruct (act e) as [a|] eqn:Ha.
  2:{ right. intros Hen. destruct (enabled_act _ _ _ Hen He) as [a Ha']. congruence. }
  pose proof (enabled_partner C M t e a) as Hneed.
  destruct a as [| |v|c|c v|c|c d|c b|c].
  - left. destruct (act_offer_sig e _ LBeta Ha I) as [e' Hs].
    exists ({[t]}, (C, <[t := e']> M)). split; [by eapply IBeta|simpl; set_solver].
  - left. set (c := fresh (C ∪ echans (soup M))).
    assert (c ∉ C ∪ echans (soup M)) as Hc by apply is_fresh.
    destruct (act_offer_sig e _ (LNew c) Ha I) as [e' Hs].
    exists ({[t]}, (C ∪ {[c]}, <[t := e']> M)).
    split; [eapply INew; [done|done|set_solver|set_solver]|simpl; set_solver].
  - left. destruct (act_offer_sig e _ (LSpawn v) Ha eq_refl) as [e' Hs].
    set (j := fresh (dom M)). assert (M !! j = None) as Hj by (apply not_elem_of_dom, is_fresh).
    exists ({[t]}, (C, <[j := App v EUnit]> (<[t := e']> M))).
    split; [by eapply ISpawn|simpl; set_solver].
  - destruct (find_in_map M (λ j f, j ≠ t ∧ partner_ok (ARecv c) (act f)))
      as [[[j f] [Hj [Hjt Hok]]]|Hno].
    + left. simpl in *. destruct (act f) as [[| | | |c' w| | | |]|] eqn:Hf; simpl in Hok; try done.
      subst c'.
      destruct (act_offer_sig f _ (LSess (SSend c w)) Hf (conj eq_refl eq_refl)) as [f' Hsf].
      destruct (act_offer_sig e _ (LSess (SRecv c w)) Ha (conj eq_refl (act_send_val f c w Hf)))
        as [e' Hse].
      exists ({[j; t]}, (C, <[t := e']> (<[j := f']> M))). split; [|simpl; set_solver].
      by eapply IMsg.
    + right. intros Hen. destruct (Hneed Hen He Ha) as (j & f & Hjt & Hj & Hok).
      by apply (Hno j f Hj).
  - destruct (find_in_map M (λ j f, j ≠ t ∧ partner_ok (ASend c v) (act f)))
      as [[[j f] [Hj [Hjt Hok]]]|Hno].
    + left. simpl in *. destruct (act f) as [[| | |c'| | | | |]|] eqn:Hf; simpl in Hok; try done.
      subst c'.
      destruct (act_offer_sig e _ (LSess (SSend c v)) Ha (conj eq_refl eq_refl)) as [e' Hse].
      destruct (act_offer_sig f _ (LSess (SRecv c v)) Hf (conj eq_refl (act_send_val e c v Ha)))
        as [f' Hsf].
      exists ({[t; j]}, (C, <[j := f']> (<[t := e']> M))). split; [|simpl; set_solver].
      eapply IMsg; [by apply not_eq_sym|done..].
    + right. intros Hen. destruct (Hneed Hen He Ha) as (j & f & Hjt & Hj & Hok).
      by apply (Hno j f Hj).
  - destruct (decide (c ∈ C)) as [HC|HC].
    2:{ right. intros Hen. by destruct (Hneed Hen He Ha) as [? _]. }
    destruct (find_in_map M (λ j f, j ≠ t ∧ partner_ok (AClos c) (act f)))
      as [[[j f] [Hj [Hjt Hok]]]|Hno].
    + left. simpl in *. destruct (act f) as [[| | | | |c'| | |]|] eqn:Hf; simpl in Hok; try done.
      subst c'.
      destruct (act_offer_sig e _ (LSess (SClos c)) Ha eq_refl) as [e' Hse].
      destruct (act_offer_sig f _ (LSess (SClos c)) Hf eq_refl) as [f' Hsf].
      exists ({[t; j]}, (C ∖ {[c]}, <[j := f']> (<[t := e']> M))). split; [|simpl; set_solver].
      eapply IClose; [by apply not_eq_sym|done..].
    + right. intros Hen. destruct (Hneed Hen He Ha) as (_ & j & f & Hjt & Hj & Hok).
      by apply (Hno j f Hj).
  - destruct (act_offer_sig e _ (LSess (SLink {[c; d]})) Ha eq_refl) as [e' Hse].
    destruct (decide (c ∈ C)) as [HC|HC].
    { left. exists ({[t]}, (C ∖ {[c]}, chsubst c d <$> (<[t := e']> M))).
      split; [by eapply ILink|simpl; set_solver]. }
    destruct (decide (d ∈ C)) as [HD|HD].
    { left. exists ({[t]}, (C ∖ {[d]}, chsubst d c <$> (<[t := e']> M))).
      split; [|simpl; set_solver]. eapply ILink; [done| |done].
      by replace ({[d; c]} : gset chan) with ({[c; d]} : gset chan) by set_solver. }
    right. intros Hen. by destruct (Hneed Hen He Ha).
  - destruct (find_in_map M (λ j f, j ≠ t ∧ partner_ok (ASel c b) (act f)))
      as [[[j f] [Hj [Hjt Hok]]]|Hno].
    + left. simpl in *. destruct (act f) as [[| | | | | | | |c']|] eqn:Hf; simpl in Hok; try done.
      subst c'.
      destruct (act_offer_sig e _ (LSess (SSel c b)) Ha (conj eq_refl eq_refl)) as [e' Hse].
      destruct (act_offer_sig f _ (LSess (SBra c b)) Hf eq_refl) as [f' Hsf].
      exists ({[t; j]}, (C, <[j := f']> (<[t := e']> M))). split; [|simpl; set_solver].
      eapply IChoice; [by apply not_eq_sym|done..].
    + right. intros Hen. destruct (Hneed Hen He Ha) as (j & f & Hjt & Hj & Hok).
      by apply (Hno j f Hj).
  - destruct (find_in_map M (λ j f, j ≠ t ∧ partner_ok (ABra c) (act f)))
      as [[[j f] [Hj [Hjt Hok]]]|Hno].
    + left. simpl in *. destruct (act f) as [[| | | | | | |c' b|]|] eqn:Hf; simpl in Hok; try done.
      subst c'.
      destruct (act_offer_sig f _ (LSess (SSel c b)) Hf (conj eq_refl eq_refl)) as [f' Hsf].
      destruct (act_offer_sig e _ (LSess (SBra c b)) Ha eq_refl) as [e' Hse].
      exists ({[j; t]}, (C, <[t := e']> (<[j := f']> M))). split; [|simpl; set_solver].
      by eapply IChoice.
    + right. intros Hen. destruct (Hneed Hen He Ha) as (j & f & Hjt & Hj & Hok).
      by apply (Hno j f Hj).
Qed.

Lemma find_enabled (q : config) (ts : list nat) :
  {Lq : gset nat * config | istep q Lq.1 Lq.2} + {∀ t, t ∈ ts → ¬ enabled q t}.
Proof.
  induction ts as [|t ts IH].
  - right. intros t Ht. by apply elem_of_nil in Ht.
  - destruct (try_thread q t) as [[Lq [Hs _]]|Hn]; [left; by exists Lq|].
    destruct IH as [[Lq Hs]|Hno]; [left; by exists Lq|].
    right. intros u Hu. apply elem_of_cons in Hu as [->|Hu]; auto.
Qed.

Lemma stuck_of q : (∀ t, t ∈ elements (dom q.2) → ¬ enabled q t) → stuck q.
Proof.
  intros Hno L q' Hs. destruct (istep_nonempty _ _ _ Hs) as [t Ht].
  destruct (istep_part_some _ _ _ _ Hs Ht) as [e He].
  apply (Hno t); [apply elem_of_elements, elem_of_dom; by exists e|by exists L, q'].
Qed.

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

Definition sched_step (q : config) (k : nat) : gset nat * config :=
  match try_thread q (enum k) with
  | inleft (exist _ Lq _) => Lq
  | inright _ =>
      match find_enabled q (elements (dom q.2)) with
      | inleft (exist _ Lq _) => Lq
      | inright _ => (∅, q)
      end
  end.

Lemma sched_step_spec q k :
  istep q (sched_step q k).1 (sched_step q k).2 ∨
  (stuck q ∧ (sched_step q k).2 = q ∧ (sched_step q k).1 = ∅).
Proof.
  unfold sched_step. destruct (try_thread q (enum k)) as [[Lq [Hs _]]|_]; [by left|].
  destruct (find_enabled q (elements (dom q.2))) as [[Lq Hs]|Hno]; [by left|].
  right. split_and!; [by apply stuck_of|done|done].
Qed.

Lemma sched_fair q k : enabled q (enum k) → enum k ∈ (sched_step q k).1.
Proof.
  unfold sched_step. destruct (try_thread q (enum k)) as [[Lq [_ Ht]]|Hn]; [done|].
  intros Hen. by destruct Hn.
Qed.

Fixpoint sconf (q0 : config) (k : nat) : config :=
  match k with 0 => q0 | S k => (sched_step (sconf q0 k) k).2 end.

Definition slab (q0 : config) (k : nat) : gset nat := (sched_step (sconf q0 k) k).1.

Lemma srun_max q0 : maximal (sconf q0) (slab q0).
Proof.
  intros k. unfold run_step, slab.
  change (sconf q0 (S k)) with ((sched_step (sconf q0 k) k).2). apply sched_step_spec.
Qed.

Lemma srun_fair q0 : wfair (sconf q0) (slab q0).
Proof.
  intros t i. destruct (enum_inf t i) as (j & Hij & Hj). exists j. split; [done|].
  destruct (try_thread (sconf q0 j) t) as [[Lq [Hs Ht]]|Hn]; [left|by right].
  unfold slab. rewrite <-Hj. apply sched_fair. rewrite Hj. by exists Lq.1, Lq.2.
Qed.

Lemma sconf_isteps q k : isteps q (sconf q k).
Proof.
  induction k as [|k IH]; [done|]. etrans; [exact IH|].
  change (sconf q (S k)) with ((sched_step (sconf q k) k).2).
  destruct (sched_step_spec (sconf q k) k) as [Hs|(_ & -> & _)]; [|done].
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

Lemma preduction_back q p1 : preduction p1 (erase q) → ∃ L q1, erase q1 = p1 ∧ istep q1 L q.
Proof.
  destruct q as [C' M]. unfold erase, preduction; simpl. intros H.
  remember (C', soup M) as p2 eqn:Hp2. remember PTau as π eqn:Hπ.
  destruct H as [|C E e e' Hst|C E e c e' Hst HC HcE Hce|C E e v e' Hst
    |C E c v e e' f f' He Hf|C E c e e' f f' He Hf HC
    |C E c b e e' f f' He Hf|C E e c d e' Hst HC]; try discriminate;
    injection Hp2 as <- HE; symmetry in HE.
  - destruct (soup_extract M E e' HE) as (i & Hi & HEi).
    exists {[i]}, (C, <[i := e]> M). split.
    + unfold erase; simpl. by rewrite (soup_update M i e' e Hi), HEi.
    + replace (C, M) with (C, <[i := e']> (<[i := e]> M)) by (by rewrite insert_insert_eq, insert_id).
      eapply IBeta; [by rewrite lookup_insert_eq|done].
  - destruct (soup_extract M E e' HE) as (i & Hi & HEi).
    exists {[i]}, (C, <[i := e]> M). split.
    + unfold erase; simpl. by rewrite (soup_update M i e' e Hi), HEi.
    + replace (C ∪ {[c]}, M) with (C ∪ {[c]}, <[i := e']> (<[i := e]> M))
        by (by rewrite insert_insert_eq, insert_id).
      eapply INew; [by rewrite lookup_insert_eq|done|done|].
      rewrite (soup_update M i e' e Hi), HEi, echans_disj_union, echans_singleton. set_solver.
  - destruct (soup_extract M _ (App v EUnit) HE) as (j & Hj & HEj).
    destruct (soup_extract _ E e' HEj) as (i & Hi & HEi).
    assert (i ≠ j) as Hij by (intros ->; by rewrite lookup_delete_eq in Hi).
    assert (M !! i = Some e') as HiM by (by rewrite lookup_delete_ne in Hi).
    exists {[i]}, (C, <[i := e]> (delete j M)). split.
    + unfold erase; simpl. by rewrite (soup_update (delete j M) i e' e Hi), HEi.
    + replace (C, M) with (C, <[j := App v EUnit]> (<[i := e']> (<[i := e]> (delete j M)))).
      * eapply ISpawn; [by rewrite lookup_insert_eq|done|].
        rewrite lookup_insert_ne by lia. apply lookup_delete_eq.
      * f_equal. rewrite insert_insert_eq, (insert_id _ i e' Hi). by apply insert_delete_id.
  - destruct (soup_extract M _ f' HE) as (j & Hj & HEj).
    destruct (soup_extract _ E e' HEj) as (i & Hi & HEi).
    assert (i ≠ j) as Hij by (intros ->; by rewrite lookup_delete_eq in Hi).
    rewrite lookup_delete_ne in Hi by done.
    exists {[i; j]}, (C, <[j := f]> (<[i := e]> M)). split.
    + unfold erase; simpl. destruct (soup_update2 M i j e' f' e f Hij Hi Hj) as [_ ->].
      by rewrite delete_delete, HEi.
    + replace (C, M) with (C, <[j := f']> (<[i := e']> (<[j := f]> (<[i := e]> M))))
        by (by rewrite map_upd2_back).
      eapply IMsg; [done| |by rewrite lookup_insert_eq|done|done].
      rewrite lookup_insert_ne by lia. by rewrite lookup_insert_eq.
  - destruct (soup_extract M _ f' HE) as (j & Hj & HEj).
    destruct (soup_extract _ E e' HEj) as (i & Hi & HEi).
    assert (i ≠ j) as Hij by (intros ->; by rewrite lookup_delete_eq in Hi).
    rewrite lookup_delete_ne in Hi by done.
    exists {[i; j]}, (C, <[j := f]> (<[i := e]> M)). split.
    + unfold erase; simpl. destruct (soup_update2 M i j e' f' e f Hij Hi Hj) as [_ ->].
      by rewrite delete_delete, HEi.
    + replace (C ∖ {[c]}, M) with (C ∖ {[c]}, <[j := f']> (<[i := e']> (<[j := f]> (<[i := e]> M))))
        by (by rewrite map_upd2_back).
      eapply IClose; [done| |by rewrite lookup_insert_eq|done|done|done].
      rewrite lookup_insert_ne by lia. by rewrite lookup_insert_eq.
  - destruct (soup_extract M _ f' HE) as (j & Hj & HEj).
    destruct (soup_extract _ E e' HEj) as (i & Hi & HEi).
    assert (i ≠ j) as Hij by (intros ->; by rewrite lookup_delete_eq in Hi).
    rewrite lookup_delete_ne in Hi by done.
    exists {[i; j]}, (C, <[j := f]> (<[i := e]> M)). split.
    + unfold erase; simpl. destruct (soup_update2 M i j e' f' e f Hij Hi Hj) as [_ ->].
      by rewrite delete_delete, HEi.
    + replace (C, M) with (C, <[j := f']> (<[i := e']> (<[j := f]> (<[i := e]> M))))
        by (by rewrite map_upd2_back).
      eapply IChoice; [done| |by rewrite lookup_insert_eq|done|done].
      rewrite lookup_insert_ne by lia. by rewrite lookup_insert_eq.
  - destruct (map_preimage (chsubst c d) M (E ⊎ {[+ e' +]}) HE) as (M0 & HM0 & HX0).
    destruct (soup_extract M0 E e' HX0) as (i & Hi & HEi).
    exists {[i]}, (C, <[i := e]> M0). split.
    + unfold erase; simpl. by rewrite (soup_update M0 i e' e Hi), HEi.
    + replace (C ∖ {[c]}, M) with (C ∖ {[c]}, chsubst c d <$> (<[i := e']> (<[i := e]> M0)))
        by (by rewrite insert_insert_eq, insert_id, HM0).
      eapply ILink; [by rewrite lookup_insert_eq|done|done].
Qed.

Lemma pred_star_back p p' :
  pred_star p p' → ∀ q, erase q = p' → ∃ q0, erase q0 = p ∧ isteps q0 q.
Proof.
  induction 1 as [p|p p1 p2 Hst _ IH]; intros q Hq.
  - exists q. by split.
  - destruct (IH q Hq) as (q1 & Hq1 & Hsteps).
    destruct (preduction_back q1 p) as (L & q0 & Hq0 & Hs); [by rewrite Hq1|].
    exists q0. split; [done|]. eapply rtc_l; [by exists L|exact Hsteps].
Qed.

Lemma isteps_fun q0 q :
  isteps q0 q →
  ∃ m (pr : nat → config) (pl : nat → gset nat), pr 0 = q0 ∧ pr m = q ∧
    ∀ i, i < m → istep (pr i) (pl i) (pr (S i)).
Proof.
  induction 1 as [q|q0 q1 q [L Hs] _ (m & pr & pl & H0 & Hm & Hst)].
  - exists 0, (λ _, q), (λ _, ∅). split_and!; [done|done|lia].
  - exists (S m), (λ i, match i with 0 => q0 | S i => pr i end),
      (λ i, match i with 0 => L | S i => pl i end).
    split_and!; [done|done|]. intros [|i] Hi; simpl; [by rewrite H0|]. apply Hst. lia.
Qed.

(** ** The theorem *)

Theorem lock_free_reach_of p : lock_free p → lock_free_reach p.
Proof.
  intros Hlf q t Hq Hp.
  destruct (pred_star_back p (erase q) Hq q eq_refl) as (q0 & Hq0 & Hsteps).
  destruct (isteps_fun q0 q Hsteps) as (m & pr & pl & H0 & Hm & Hst).
  set (r := λ i, if decide (i < m) then pr i else sconf q (i - m)).
  set (l := λ i, if decide (i < m) then pl i else slab q (i - m)).
  assert (∀ i, i < m → r i = pr i ∧ l i = pl i) as Hpre.
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
    - destruct (Hpre i Him) as [-> ->]. left.
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
  exists (sconf q (j - m)), (slab q (j - m)), (sconf q (S (j - m))). split_and!.
  - apply sconf_isteps.
  - destruct (srun_max q (j - m)) as [Hs|(_ & _ & He)]; [done|]. rewrite He in Htj. set_solver.
  - done.
Qed.
