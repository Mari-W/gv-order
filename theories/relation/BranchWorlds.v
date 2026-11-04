(** * Worlds with pending choices (prototype, docs/extensions/data-dependent-worlds.md)

    A prototype of candidate (d) of the design note: a world W together
    with a list P of pending binary choices. Each choice is a pair of
    alternative sets of ≺ facts. A choice vector ch picks one side of
    every choice, and [at_choice W P ch] is the world W with the picked
    facts added. A pending world is valid when every choice vector gives
    a strict world. A component that branches on data resolves a choice
    ([resolve]): its world gains the facts of the branch it takes, which
    may relate points that existed before.

    The critical lemma is amalgamation. The relation is monotone only
    because a fresh extension made by one component joins with any
    extension made by another and stays strict ([wext_fresh_join],
    relation/Worlds.v). An extension that adds facts between existing
    points breaks it ([unguarded_join_cycle]). Pending choices restore
    it ([pjoin_valid], [pjoin_fresh]): a fresh extension that adds new
    pending choices, joined with an extension that resolves old ones,
    is again a valid pending world and a fresh extension at every
    choice vector. The proof reduces the pending case to
    [wext_fresh_join] at each choice vector.

    What this file does not do. It does not change the logical
    relation, the typing rules or any theorem of the development. It
    defines no ownership of choices and no typing rule that resolves
    one. The design note lists what those need. *)

From stdpp Require Import base gmap.
From LRGV Require Export relation.Worlds.

Set Default Proof Using "All".

(** ** Pending choices *)

Definition pchoice : Type := (prel * prel)%type.

Definition side (c : pchoice) (b : bool) : prel := if b then c.2 else c.1.

(** The facts a choice vector picks. *)
Definition pick (P : list pchoice) (ch : list bool) : prel :=
  λ x y, ∃ i c b, P !! i = Some c ∧ ch !! i = Some b ∧ side c b x y.

Definition at_choice (W : world) (P : list pchoice) (ch : list bool) : world :=
  wgen (w_names W) (w_eq W) (λ x y, w_lt W x y ∨ pick P ch x y).

(** Every alternative relates known points only. *)
Definition supported (N : gset pname) (P : list pchoice) : Prop :=
  ∀ i c b x y, P !! i = Some c → side c b x y → pt_root x ∈ N ∧ pt_root y ∈ N.

Definition pvalid (W : world) (P : list pchoice) : Prop :=
  world_wf W ∧ supported (w_names W) P ∧
  ∀ ch, length ch = length P → strict (at_choice W P ch).

(** ** Basic facts *)

Lemma at_choice_wf W P ch :
  world_wf W → supported (w_names W) P → world_wf (at_choice W P ch).
Proof.
  intros HW HP. apply wgen_wf.
  - apply HW.
  - apply HW.
  - intros x y [H|(i & c & b & Hi & _ & Hs)].
    + by apply HW.
    + right. by eapply HP.
Qed.

Lemma at_choice_names W P ch : w_names (at_choice W P ch) = w_names W.
Proof. done. Qed.

Lemma at_choice_eq W P ch x y : w_eq W x y → w_eq (at_choice W P ch) x y.
Proof. intros H. by apply geq_base. Qed.

Lemma at_choice_lt W P ch x y : w_lt W x y → w_lt (at_choice W P ch) x y.
Proof. intros H. apply glt_base. by left. Qed.

Lemma at_choice_pick W P ch x y : pick P ch x y → w_lt (at_choice W P ch) x y.
Proof. intros H. apply glt_base. by right. Qed.

(** A well-formed world whose ≺ lies in a strict world is strict. *)
Lemma strict_sub W1 W2 :
  world_wf W1 → strict W2 → (∀ x y, w_lt W1 x y → w_lt W2 x y) → strict W1.
Proof. intros HW1 [_ Hi] Hl. split; [done|]. intros x Hx. by apply (Hi x), Hl. Qed.

(** A generated world lies in a well-formed world that contains its
    generators. *)
Lemma wgen_into N E L W :
  world_wf W → (∀ x y, E x y → w_eq W x y) → (∀ x y, L x y → w_lt W x y) →
  ∀ x y, w_lt (wgen N E L) x y → w_lt W x y.
Proof. intros HW HE HL. apply (wgen_in_world W E L HW HE HL). Qed.

Lemma wgen_into_eq N E L W :
  world_wf W → (∀ x y, E x y → w_eq W x y) → (∀ x y, L x y → w_lt W x y) →
  ∀ x y, w_eq (wgen N E L) x y → w_eq W x y.
Proof. intros HW HE HL. apply (wgen_in_world W E L HW HE HL). Qed.

(** ** Resolving a choice

    The component that owns choice i takes side b. Its world gains the
    facts of that side, and the choice becomes trivial: both of its
    sides are the side taken. Choice vectors keep their length. *)

Definition resolve (W : world) (P : list pchoice) (i : nat) (b : bool) : world :=
  wgen (w_names W) (w_eq W)
    (λ x y, w_lt W x y ∨ ∃ c, P !! i = Some c ∧ side c b x y).

Definition resolve_P (P : list pchoice) (i : nat) (b : bool) : list pchoice :=
  match P !! i with
  | Some c => <[i := (side c b, side c b)]> P
  | None => P
  end.

Lemma length_resolve_P P i b : length (resolve_P P i b) = length P.
Proof. unfold resolve_P. destruct (P !! i); [apply length_insert|done]. Qed.

Lemma resolve_P_lookup P i b j :
  resolve_P P i b !! j =
    if decide (j = i) then (λ c, (side c b, side c b)) <$> P !! i else P !! j.
Proof.
  unfold resolve_P. destruct (P !! i) as [c|] eqn:Hi.
  - case_decide as Hj.
    + subst j. rewrite list_lookup_insert_eq; [done|]. by apply lookup_lt_Some in Hi.
    + by rewrite list_lookup_insert_ne.
  - case_decide as Hj; [subst j; simpl; done|done].
Qed.

Lemma resolve_supported W P i b :
  supported (w_names W) P → supported (w_names W) (resolve_P P i b).
Proof.
  intros HP j c b' x y Hj Hs. rewrite resolve_P_lookup in Hj. case_decide as E.
  - subst j. destruct (P !! i) as [c0|] eqn:Hi; [|done]. injection Hj as <-.
    destruct b'; simpl in Hs; by eapply HP.
  - by eapply HP.
Qed.

Lemma resolve_wf W P i b :
  world_wf W → supported (w_names W) P → world_wf (resolve W P i b).
Proof.
  intros HW HP. apply wgen_wf; [apply HW|apply HW|].
  intros x y [H|(c & Hi & Hs)]; [by apply HW|right; by eapply HP].
Qed.

(** The resolved world at ch is the old world at ch with side b at i. *)
Lemma resolve_at_incl W P i b ch :
  world_wf W → supported (w_names W) P → i < length ch →
  ∀ x y, w_lt (at_choice (resolve W P i b) (resolve_P P i b) ch) x y →
         w_lt (at_choice W P (<[i := b]> ch)) x y.
Proof.
  intros HW HP Hlen.
  set (Wt := at_choice W P (<[i := b]> ch)).
  assert (world_wf Wt) as HWt by (by apply at_choice_wf).
  assert (∀ x y, w_eq (resolve W P i b) x y → w_eq Wt x y) as Heq.
  { apply (wgen_into_eq _ _ _ Wt HWt); [apply at_choice_eq|].
    intros x y [H|(c & Hi & Hs)]; [by apply at_choice_lt|].
    apply at_choice_pick. exists i, c, b. split_and!; [done| |done].
    by apply list_lookup_insert_eq. }
  assert (∀ x y, w_lt (resolve W P i b) x y → w_lt Wt x y) as Hlt.
  { apply (wgen_into _ _ _ Wt HWt); [apply at_choice_eq|].
    intros x y [H|(c & Hi & Hs)]; [by apply at_choice_lt|].
    apply at_choice_pick. exists i, c, b. split_and!; [done| |done].
    by apply list_lookup_insert_eq. }
  apply (wgen_into _ _ _ Wt HWt); [done|].
  intros x y [H|(j & c & b' & Hj & Hc & Hs)]; [by apply Hlt|].
  rewrite resolve_P_lookup in Hj. case_decide as E.
  - subst j. destruct (P !! i) as [c0|] eqn:Hi; [|done]. injection Hj as <-.
    apply at_choice_pick. exists i, c0, b. split_and!; [done| |by destruct b'].
    by apply list_lookup_insert_eq.
  - apply at_choice_pick. exists j, c, b'. split_and!; [done| |done].
    by rewrite list_lookup_insert_ne.
Qed.

(** Resolving keeps a pending world valid. *)
Theorem resolve_valid W P i b :
  pvalid W P → pvalid (resolve W P i b) (resolve_P P i b).
Proof.
  intros (HW & HP & Hs). split_and!.
  - by apply resolve_wf.
  - by apply resolve_supported.
  - intros ch Hch. rewrite length_resolve_P in Hch.
    destruct (decide (i < length ch)) as [Hi|Hi].
    + apply (strict_sub _ (at_choice W P (<[i := b]> ch))).
      * apply at_choice_wf; [by apply resolve_wf|by apply resolve_supported].
      * apply Hs. by rewrite length_insert.
      * by apply resolve_at_incl.
    + (* i is out of range: P !! i = None and nothing changes *)
      assert (P !! i = None) as HPi by (apply lookup_ge_None; lia).
      set (Wt := at_choice W P ch).
      assert (world_wf Wt) as HWt by (by apply at_choice_wf).
      assert (∀ x y, w_eq (resolve W P i b) x y → w_eq Wt x y) as Heq.
      { apply (wgen_into_eq _ _ _ Wt HWt); [apply at_choice_eq|].
        intros x y [H|(c & Hc & _)]; [by apply at_choice_lt|congruence]. }
      assert (∀ x y, w_lt (resolve W P i b) x y → w_lt Wt x y) as Hlt.
      { apply (wgen_into _ _ _ Wt HWt); [apply at_choice_eq|].
        intros x y [H|(c & Hc & _)]; [by apply at_choice_lt|congruence]. }
      apply (strict_sub _ Wt).
      * apply at_choice_wf; [by apply resolve_wf|by apply resolve_supported].
      * by apply Hs.
      * apply (wgen_into _ _ _ Wt HWt); [done|].
        intros x y [H|(j & c & b' & Hj & Hc & Hs')]; [by apply Hlt|].
        unfold resolve_P in Hj. rewrite HPi in Hj.
        apply at_choice_pick. by exists j, c, b'.
Qed.

(** ** Extensions of pending worlds

    (W, P) ⊑ (W′, P′): every choice vector of P′ lies above some choice
    vector of P. Resolving choice i to b is such an extension, with the
    choice vector ch′ above <[i := b]> ch′. *)

Definition pext (W : world) (P : list pchoice) (W' : world) (P' : list pchoice) : Prop :=
  length P' = length P ∧
  ∀ ch', length ch' = length P' → ∃ ch, length ch = length P ∧
    wext (at_choice W P ch) (at_choice W' P' ch').

Lemma resolve_at_incl_rev W P i b ch :
  world_wf W → supported (w_names W) P →
  (∀ x y, w_eq (at_choice W P (<[i := b]> ch)) x y →
          w_eq (at_choice (resolve W P i b) (resolve_P P i b) ch) x y) ∧
  (∀ x y, w_lt (at_choice W P (<[i := b]> ch)) x y →
          w_lt (at_choice (resolve W P i b) (resolve_P P i b) ch) x y).
Proof.
  intros HW HP.
  set (Wt := at_choice (resolve W P i b) (resolve_P P i b) ch).
  assert (world_wf Wt) as HWt.
  { apply at_choice_wf; [by apply resolve_wf|by apply resolve_supported]. }
  assert (∀ x y, w_eq W x y → w_eq Wt x y) as Heq.
  { intros x y H. apply at_choice_eq. by apply geq_base. }
  assert (∀ x y, w_lt W x y → w_lt Wt x y) as Hlt.
  { intros x y H. apply at_choice_lt. apply glt_base. by left. }
  split; [apply (wgen_into_eq _ _ _ Wt HWt)|apply (wgen_into _ _ _ Wt HWt)]; try done.
  all: intros x y [H|(j & c & b' & Hj & Hc & Hs)]; [by apply Hlt|].
  all: destruct (decide (j = i)) as [->|Hji].
  all: try (rewrite list_lookup_insert_eq in Hc by (by apply lookup_lt_Some in Hc;
              rewrite length_insert in Hc); injection Hc as <-;
            apply at_choice_lt; apply glt_base; right; by exists c).
  all: rewrite list_lookup_insert_ne in Hc by done;
    apply at_choice_pick; exists j, c, b'; split_and!; [|done|done];
    rewrite resolve_P_lookup; by case_decide.
Qed.

Theorem resolve_pext W P i b :
  pvalid W P → i < length P → pext W P (resolve W P i b) (resolve_P P i b).
Proof.
  intros HV Hi. pose proof HV as (HW & HP & _). split; [apply length_resolve_P|].
  intros ch' Hch. rewrite length_resolve_P in Hch. exists (<[i := b]> ch').
  split; [by rewrite length_insert|].
  destruct (resolve_at_incl_rev W P i b ch' HW HP) as [He Hl].
  split_and!; [done|done|done|]. apply (proj2 (proj2 (resolve_valid _ _ i b HV))).
  by rewrite length_resolve_P.
Qed.

(** A fresh extension of a pending world: new names N and new pending
    choices Pn, fresh at every choice vector. *)
Definition pfresh (W : world) (P : list pchoice) (N : gset pname)
    (W1 : world) (Pn : list pchoice) : Prop :=
  world_wf W1 ∧ supported (w_names W1) (P ++ Pn) ∧
  ∀ ch chn, length ch = length P → length chn = length Pn →
    wext_fresh (at_choice W P ch) N (at_choice W1 (P ++ Pn) (ch ++ chn)).

(** ** Amalgamation

    A fresh extension with new pending choices, joined with any pending
    extension (which may resolve old choices), is a fresh extension at
    every choice vector. *)
Theorem pjoin_fresh W P N W1 Pn W' P' :
  pvalid W P → pfresh W P N W1 Pn → pext W P W' P' → N ## w_names W' →
  ∀ ch' chn, length ch' = length P' → length chn = length Pn →
    ∃ ch, length ch = length P ∧
      wext_fresh (at_choice W' P' ch') N
        (wjoin (at_choice W1 (P ++ Pn) (ch ++ chn)) (at_choice W' P' ch')).
Proof.
  intros (HW & HP & _) (_ & _ & Hfr) [Hlen Hext] HN ch' chn Hch' Hchn.
  destruct (Hext ch' Hch') as (ch & Hch & Hwx).
  exists ch. split; [done|].
  apply (wext_fresh_join (at_choice W P ch)); [by apply at_choice_wf|by apply Hfr|done|done].
Qed.

Lemma pick_app_l P Pn ch chn x y :
  length ch = length P → pick P ch x y → pick (P ++ Pn) (ch ++ chn) x y.
Proof.
  intros Hl (i & c & b & Hi & Hc & Hs). exists i, c, b. split_and!; [|  |done].
  - by apply lookup_app_l_Some.
  - by apply lookup_app_l_Some.
Qed.

(** The joined pending world is valid. *)
Theorem pjoin_valid W P N W1 Pn W' P' :
  pvalid W P → pfresh W P N W1 Pn → pext W P W' P' → pvalid W' P' → N ## w_names W' →
  pvalid (wjoin W1 W') (P' ++ Pn).
Proof.
  intros HV Hf Hx HV' HN.
  pose proof Hf as (HW1 & HP1 & _). pose proof HV' as (HW' & HP' & _).
  pose proof Hx as [Hlen _].
  split_and!.
  - by apply wjoin_wf.
  - intros i c b x y Hi Hs. simpl. destruct (decide (i < length P')) as [Hl|Hl].
    + rewrite lookup_app_l in Hi by done. destruct (HP' i c b x y Hi Hs). set_solver.
    + rewrite lookup_app_r in Hi by lia.
      assert ((P ++ Pn) !! (length P + (i - length P')) = Some c) as Hi'.
      { rewrite lookup_app_r by lia. by replace (length P + (i - length P') - length P)
          with (i - length P') by lia. }
      destruct (HP1 _ c b x y Hi' Hs). set_solver.
  - intros chh Hchh. rewrite length_app in Hchh.
    set (ch' := take (length P') chh). set (chn := drop (length P') chh).
    assert (chh = ch' ++ chn) as E by (symmetry; apply take_drop).
    assert (length ch' = length P') as Hch' by (unfold ch'; rewrite length_take; lia).
    assert (length chn = length Pn) as Hchn by (unfold chn; rewrite length_drop; lia).
    destruct (pjoin_fresh W P N W1 Pn W' P' HV Hf Hx HN ch' chn Hch' Hchn) as (ch & Hch & Hj).
    set (J := wjoin (at_choice W1 (P ++ Pn) (ch ++ chn)) (at_choice W' P' ch')).
    assert (strict J) as HJ by apply Hj.
    apply (strict_sub _ J).
    { apply at_choice_wf; [by apply wjoin_wf|].
      intros i c b x y Hi Hs. simpl. destruct (decide (i < length P')) as [Hl|Hl].
      - rewrite lookup_app_l in Hi by done. destruct (HP' i c b x y Hi Hs). set_solver.
      - rewrite lookup_app_r in Hi by lia.
        assert ((P ++ Pn) !! (length P + (i - length P')) = Some c) as Hi'.
        { rewrite lookup_app_r by lia. by replace (length P + (i - length P') - length P)
            with (i - length P') by lia. }
        destruct (HP1 _ c b x y Hi' Hs). set_solver. }
    { done. }
    destruct (wjoin_l (at_choice W1 (P ++ Pn) (ch ++ chn)) (at_choice W' P' ch')) as [Hl1e Hl1l].
    destruct (wjoin_r (at_choice W1 (P ++ Pn) (ch ++ chn)) (at_choice W' P' ch')) as [Hr1e Hr1l].
    pose proof (proj1 HJ) as HJw.
    assert (∀ x y, w_eq (wjoin W1 W') x y → w_eq J x y) as Heq.
    { apply (wgen_into_eq _ _ _ J HJw).
      - intros x y [H|H]; [apply Hl1e, at_choice_eq, H|apply Hr1e, at_choice_eq, H].
      - intros x y [H|H]; [apply Hl1l, at_choice_lt, H|apply Hr1l, at_choice_lt, H]. }
    assert (∀ x y, w_lt (wjoin W1 W') x y → w_lt J x y) as Hlt.
    { apply (wgen_into _ _ _ J HJw).
      - intros x y [H|H]; [apply Hl1e, at_choice_eq, H|apply Hr1e, at_choice_eq, H].
      - intros x y [H|H]; [apply Hl1l, at_choice_lt, H|apply Hr1l, at_choice_lt, H]. }
    apply (wgen_into _ _ _ J HJw); [done|].
    intros x y [H|(i & c & b & Hi & Hc & Hs)]; [by apply Hlt|].
    rewrite E in Hc. destruct (decide (i < length P')) as [Hl|Hl].
    + rewrite lookup_app_l in Hi by done. rewrite lookup_app_l in Hc by lia.
      apply Hr1l, at_choice_pick. by exists i, c, b.
    + rewrite lookup_app_r in Hi by lia. rewrite lookup_app_r in Hc by lia.
      apply Hl1l, at_choice_pick. exists (length P + (i - length P')), c, b. split_and!.
      * rewrite lookup_app_r by lia. by replace (length P + (i - length P') - length P)
          with (i - length P') by lia.
      * rewrite lookup_app_r by lia. replace (length P + (i - length P') - length ch)
          with (i - length P') by lia. by replace (i - length ch') with (i - length P') in Hc by lia.
      * done.
Qed.
