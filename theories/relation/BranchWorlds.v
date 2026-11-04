(** * Worlds with pending choices (prototype, docs/extensions/data-dependent-worlds.md)

    A prototype of section 4.4 of the design note. A world W comes together
    with a list P of pending binary choices. Each choice is a pair of
    alternative sets of ≺ facts. A choice vector ch picks one side of
    every choice, and [at_choice W P ch] is the world W with the picked
    facts added. A pending world is valid when every choice vector gives
    a strict world. A component that branches on data resolves a choice
    ([resolve]). Its world gains the facts of the branch it takes, which
    may relate points that existed before.

    The critical lemma is amalgamation. The relation is monotone only
    because a fresh extension made by one component joins with any
    extension made by another and stays strict ([wext_fresh_join],
    relation/Worlds.v). An extension that adds facts between existing
    points breaks it ([unguarded_join_cycle]). Pending choices restore
    it ([pjoin_valid], [pjoin_fresh]). A fresh extension that adds new
    pending choices, joined with an extension that resolves old ones,
    is again a valid pending world and a fresh extension at every
    choice vector. The proof reduces the pending case to
    [wext_fresh_join] at each choice vector.

    What this file does not do. It does not change the logical
    relation, the typing rules or any theorem of the development. It
    defines no ownership of choices and no typing rule that resolves
    one. The design note lists what those need. *)

From stdpp Require Import base gmap.
From LRGV Require Export relation.Worlds relation.Creation.

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
    facts of that side, and the choice becomes trivial. Both of its
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
    + (* i is out of range, so P !! i = None and nothing changes *)
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

    (W, P) ⊑ (W′, P′) when every choice vector of P′ lies above some choice
    vector of P. Resolving choice i to b is such an extension, with the
    choice vector ch′ above <[i := b]> ch′ ([resolve_pext]). So is a
    fresh extension that adds choices ([pfresh_pext]). *)

Definition pext (W : world) (P : list pchoice) (W' : world) (P' : list pchoice) : Prop :=
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
  intros HV Hi. pose proof HV as (HW & HP & _).
  intros ch' Hch. rewrite length_resolve_P in Hch. exists (<[i := b]> ch').
  split; [by rewrite length_insert|].
  destruct (resolve_at_incl_rev W P i b ch' HW HP) as [He Hl].
  split_and!; [done|done|done|]. apply (proj2 (proj2 (resolve_valid _ _ i b HV))).
  by rewrite length_resolve_P.
Qed.

(** A fresh extension of a pending world places new names N and new pending
    choices Pn, fresh at every choice vector. *)
Definition pfresh (W : world) (P : list pchoice) (N : gset pname)
    (W1 : world) (Pn : list pchoice) : Prop :=
  world_wf W1 ∧ supported (w_names W1) (P ++ Pn) ∧
  ∀ ch chn, length ch = length P → length chn = length Pn →
    wext_fresh (at_choice W P ch) N (at_choice W1 (P ++ Pn) (ch ++ chn)).

(** Another component's creation is a pending extension, so the join
    below covers a future that creates choices of its own. *)
Lemma pfresh_pext W P N W1 Pn : pfresh W P N W1 Pn → pext W P W1 (P ++ Pn).
Proof.
  intros (_ & _ & Hfr) ch Hl. rewrite length_app in Hl.
  exists (take (length P) ch). split; [rewrite length_take; lia|].
  rewrite <-(take_drop (length P) ch) at 2.
  apply (Hfr (take (length P) ch) (drop (length P) ch)).
  - rewrite length_take. lia.
  - rewrite length_drop. lia.
Qed.

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
  intros (HW & HP & _) (_ & _ & Hfr) Hext HN ch' chn Hch' Hchn.
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

(** ** Why the choice has to be pending

    Two names c = 0 and d = 1 with no facts beyond program order. One
    component adds (0,0) ≺ (1,0) to its world, another adds
    (1,0) ≺ (0,0). Each is an extension of the common world, and their
    join is not strict. This is the step of section 4.2 of the design
    note without the pending choice, and the reason the monotonicity
    proof needs fresh extensions ([wext_fresh_join]). Declared as one
    pending choice, both alternatives are valid and each component
    resolves it ([db_pending_valid]). *)

Definition N2 : gset pname := {[NConst 0; NConst 1]}.
Definition xc : point := Pt (NConst 0) 0.
Definition xd : point := Pt (NConst 1) 0.

Definition only (a b : point) : prel := λ x y, x = a ∧ y = b.
Definition nof : prel := λ _ _, False.

Definition W0 : world := wgen N2 nof nof.
Definition Wcd : world := wgen N2 nof (only xc xd).
Definition Wdc : world := wgen N2 nof (only xd xc).

Lemma geq_eqonly E x y : (∀ x y, E x y → x = y) → geq E x y → x = y.
Proof. intros HE. induction 1; subst; eauto. Qed.

Lemma glt_rank E L (r : point → nat) x y :
  (∀ x y, E x y → x = y) → (∀ x y, L x y → r x < r y) → (∀ x, r x < r (pt_shift 1 x)) →
  glt E L x y → r x < r y.
Proof.
  intros HE HL Hp. induction 1 as [| |x x' y y' Hx _ IH Hy|]; [auto|auto| |lia].
  apply (geq_eqonly E) in Hx, Hy; [|done..]. by subst.
Qed.

Definition rk (a : nat) (x : point) : nat :=
  2 * pt_off x + if decide (pt_name x = NConst a) then 1 else 0.

Lemma rk_po a x : rk a x < rk a (pt_shift 1 x).
Proof. unfold rk, pt_shift. simpl. case_decide; lia. Qed.

Lemma N2_wf L : (∀ x y, L x y → pt_root x ∈ N2 ∧ pt_root y ∈ N2) → world_wf (wgen N2 nof L).
Proof.
  intros HL. apply wgen_wf; [|by intros ?? []|intros x y H; right; by apply HL].
  intros p Hp. unfold N2 in Hp. apply elem_of_union in Hp as [Hp|Hp];
    apply elem_of_singleton in Hp as ->; eauto.
Qed.

Lemma only_supp a b :
  pt_root a ∈ N2 → pt_root b ∈ N2 → ∀ x y, only a b x y → pt_root x ∈ N2 ∧ pt_root y ∈ N2.
Proof. intros Ha Hb x y [-> ->]. done. Qed.

Lemma xc_N2 : pt_root xc ∈ N2.
Proof. unfold N2, xc, pt_root. simpl. set_solver. Qed.
Lemma xd_N2 : pt_root xd ∈ N2.
Proof. unfold N2, xd, pt_root. simpl. set_solver. Qed.

Lemma Wcd_strict : strict Wcd.
Proof.
  split; [apply N2_wf, only_supp; [apply xc_N2|apply xd_N2]|].
  intros x Hx. apply (glt_rank nof (only xc xd) (rk 1)) in Hx; [lia|by intros ?? []| |apply rk_po].
  intros ?? [-> ->]. unfold rk. simpl. repeat case_decide; simplify_eq; lia.
Qed.

Lemma Wdc_strict : strict Wdc.
Proof.
  split; [apply N2_wf, only_supp; [apply xd_N2|apply xc_N2]|].
  intros x Hx. apply (glt_rank nof (only xd xc) (rk 0)) in Hx; [lia|by intros ?? []| |apply rk_po].
  intros ?? [-> ->]. unfold rk. simpl. repeat case_decide; simplify_eq; lia.
Qed.

Lemma W0_ext L : strict (wgen N2 nof L) → wext W0 (wgen N2 nof L).
Proof.
  intros HS. split_and!.
  - done.
  - intros x y H. exact H.
  - apply (proj2 (wgen_incl nof nof nof L (λ x y H, geq_base _ _ _ H) (λ x y H, False_ind _ H))).
  - done.
Qed.

Theorem unguarded_extensions_conflict :
  wext W0 Wcd ∧ wext W0 Wdc ∧ ¬ strict (wjoin Wcd Wdc).
Proof.
  split_and!; [apply W0_ext, Wcd_strict|apply W0_ext, Wdc_strict|].
  intros [HJ Hi]. apply (Hi xc). apply (wf_lt_trans _ HJ _ xd).
  - apply (proj2 (wjoin_l Wcd Wdc)). apply glt_base. by split.
  - apply (proj2 (wjoin_r Wcd Wdc)). apply glt_base. by split.
Qed.

(** The two orders as one pending choice. It is valid, and resolved either
    way by the component that branches. *)
Definition Pcd : list pchoice := [(only xc xd, only xd xc)].

Lemma W0_wf : world_wf W0.
Proof. apply N2_wf. by intros ?? []. Qed.

Theorem db_pending_valid : pvalid W0 Pcd.
Proof.
  split_and!; [apply W0_wf| |].
  - intros i c b x y Hi Hs. destruct i as [|[]]; [|done|done]. injection Hi as <-.
    destruct b; simpl in Hs; destruct Hs as [-> ->];
      split; first [apply xc_N2|apply xd_N2].
  - intros ch Hch. destruct ch as [|b [|]]; try discriminate Hch.
    assert (∀ x y, pick Pcd [b] x y ↔ only (if b then xd else xc) (if b then xc else xd) x y) as Hp.
    { intros x y. split.
      - intros (i & c & b' & Hi & Hc & Hs). destruct i as [|[]]; try done.
        injection Hi as <-. injection Hc as <-. by destruct b.
      - intros H. exists 0, (only xc xd, only xd xc), b. by destruct b. }
    split; [apply at_choice_wf; [apply W0_wf|]|].
    { intros i c b' x y Hi Hs. destruct i as [|[]]; [|done|done]. injection Hi as <-.
      destruct b'; simpl in Hs; destruct Hs as [-> ->]; split; first [apply xc_N2|apply xd_N2]. }
    intros x Hx.
    apply (glt_rank (w_eq W0) _ (rk (if b then 0 else 1))) in Hx; [lia| | |apply rk_po].
    + intros ?? H. by apply (geq_eqonly nof) in H; [|intros ?? []].
    + intros x0 y0 [H|H].
      * apply (glt_rank nof nof (rk (if b then 0 else 1)) x0 y0) in H; [done|by intros ?? []|by intros ?? []|apply rk_po].
      * apply Hp in H. destruct H as [-> ->]. unfold rk. destruct b; simpl;
          repeat case_decide; simplify_eq; lia.
Qed.

(** ** Creating a channel with a pending choice

    new places a fresh name a under one of two creation constraints C₀
    and C₁, chosen later by the owner. Both constraints state ≺ facts
    only. The base world places a with no fact, and the choice holds the
    facts of C₀ and of C₁ at a. If each Cᵢ is a creation constraint at
    every choice vector of the old choices, the result is a fresh
    extension at every choice vector ([pfresh_new]). The proof calls
    [wext_cc] once per choice vector and alternative, so the creation
    check costs 2^k calls for k pending choices. *)

Definition Dlt (a : nat) (C : bcs) : prel :=
  λ x y, ∃ x0 y0, bcs_open 1 C (FLt x0 y0) ∧
    x = pt_inst (plist [pconst a]) x0 ∧ y = pt_inst (plist [pconst a]) y0.

Definition Wnew (W : world) (a : nat) : world :=
  wgen (w_names W ∪ {[NConst a]}) (w_eq W) (w_lt W).

Lemma pn_root_inst' σ p :
  pt_root (pn_inst σ p) = match pn_root p with NVar a => pt_root (σ a) | q => q end.
Proof. induction p as [a|a|p IH b i]; simpl; [done|done|exact IH..]. Qed.

Lemma pt_root_inst' σ x :
  pt_root (pt_inst σ x) = match pt_root x with NVar a => pt_root (σ a) | q => q end.
Proof. destruct x as [p o]. exact (pn_root_inst' σ p). Qed.

Lemma Dlt_supp W a C x y :
  world_wf W → Forall (pt_known W) (bc_env C) → Dlt a C x y →
  pt_root x ∈ w_names W ∪ {[NConst a]} ∧ pt_root y ∈ w_names W ∪ {[NConst a]}.
Proof.
  intros HW HK (x0 & y0 & Hg & -> & ->).
  assert (∀ z, pt_root z = NVar 0 ∨ pt_root z ∈ w_names W →
            pt_root (pt_inst (plist [pconst a]) z) ∈ w_names W ∪ {[NConst a]}) as Hz.
  { intros z [Hr|Hr]; rewrite pt_root_inst'.
    - rewrite Hr. cbn. set_solver.
    - destruct (wf_names_const _ HW _ Hr) as [c Hc]. rewrite Hc in Hr |- *. set_solver. }
  split; apply Hz; eapply bcs_open1_root; [done|done|exact Hg|by left|done|done|exact Hg|by right].
Qed.

Lemma Wnew_wf W a : world_wf W → NConst a ∉ w_names W → world_wf (Wnew W a).
Proof.
  intros HW Ha. apply wgen_wf.
  - intros p Hp. apply elem_of_union in Hp as [Hp|Hp]; [by apply HW|].
    apply elem_of_singleton in Hp as ->. by exists a.
  - intros x y H. eapply eq_or_supp_mono; [|by apply HW]. set_solver.
  - intros x y H. eapply po_or_supp_mono; [|by apply HW]. set_solver.
Qed.

Theorem pfresh_new W P a C0 C1 :
  pvalid W P → NConst a ∉ w_names W →
  Forall (pt_known W) (bc_env C0) → Forall (pt_known W) (bc_env C1) →
  (∀ ch (b : bool), length ch = length P →
     cc_ok (w_eq (at_choice W P ch)) (w_lt (at_choice W P ch)) (if b then C1 else C0)) →
  pfresh W P {[NConst a]} (Wnew W a) [(Dlt a C0, Dlt a C1)].
Proof.
  intros (HW & HP & Hs) Ha HK0 HK1 Hcc.
  assert (supported (w_names W ∪ {[NConst a]}) (P ++ [(Dlt a C0, Dlt a C1)])) as Hsup.
  { intros i c b x y Hi Hside. destruct (decide (i < length P)) as [Hl|Hl].
    - rewrite lookup_app_l in Hi by done. destruct (HP i c b x y Hi Hside). set_solver.
    - rewrite lookup_app_r in Hi by lia. destruct (i - length P) as [|j]; [|by destruct j].
      injection Hi as <-. destruct b; simpl in Hside;
        [apply (Dlt_supp W a C1 x y HW HK1 Hside)|apply (Dlt_supp W a C0 x y HW HK0 Hside)]. }
  split_and!; [by apply Wnew_wf|exact Hsup|].
  intros ch chn Hch Hchn. destruct chn as [|b [|]]; try discriminate Hchn.
  set (Wc := at_choice W P ch).
  assert (strict Wc) as HWc by (by apply Hs).
  destruct (wext_cc Wc a (if b then C1 else C0) HWc (Hcc ch b Hch))
    as (W2 & [(Hn2 & He2 & Hl2 & HS2) [HN [Hnames Hold]]] & Hhold).
  { destruct b; [exact HK1|exact HK0]. }
  { exact Ha. }
  set (Wt := at_choice (Wnew W a) (P ++ [(Dlt a C0, Dlt a C1)]) (ch ++ [b])).
  pose proof (proj1 HS2) as HW2.
  assert (world_wf Wt) as HWt by (apply at_choice_wf; [by apply Wnew_wf|exact Hsup]).
  (* Wt lies in W2 *)
  assert (∀ x y, w_eq W x y → w_eq W2 x y) as HeW.
  { intros x y H. apply He2, at_choice_eq, H. }
  assert (∀ x y, w_lt W x y → w_lt W2 x y) as HlW.
  { intros x y H. apply Hl2, at_choice_lt, H. }
  assert (∀ x y, w_eq (Wnew W a) x y → w_eq W2 x y) as HeN.
  { apply (wgen_into_eq _ _ _ W2 HW2); [exact HeW|exact HlW]. }
  assert (∀ x y, w_lt (Wnew W a) x y → w_lt W2 x y) as HlN.
  { apply (wgen_into _ _ _ W2 HW2); [exact HeW|exact HlW]. }
  assert (∀ x y, pick (P ++ [(Dlt a C0, Dlt a C1)]) (ch ++ [b]) x y → w_lt W2 x y) as Hpk.
  { intros x y (i & c & b' & Hi & Hc & Hside). destruct (decide (i < length P)) as [Hl|Hl].
    - rewrite lookup_app_l in Hi by done. rewrite lookup_app_l in Hc by lia.
      apply Hl2, at_choice_pick. by exists i, c, b'.
    - rewrite lookup_app_r in Hi by lia. rewrite lookup_app_r in Hc by lia.
      rewrite Hch in Hc. destruct (i - length P) as [|j]; [|by destruct j].
      injection Hi as <-. injection Hc as <-.
      destruct b; simpl in Hside; destruct Hside as (x0 & y0 & Hg & -> & ->);
        exact (Hhold (FLt x0 y0) Hg). }
  assert (∀ x y, w_eq Wt x y → w_eq W2 x y) as HeT.
  { apply (wgen_into_eq _ _ _ W2 HW2); [exact HeN|]. intros x y [H|H]; [by apply HlN|by apply Hpk]. }
  assert (∀ x y, w_lt Wt x y → w_lt W2 x y) as HlT.
  { apply (wgen_into _ _ _ W2 HW2); [exact HeN|]. intros x y [H|H]; [by apply HlN|by apply Hpk]. }
  assert (strict Wt) as HSt by (apply (strict_sub _ W2); done).
  (* Wc lies in Wt *)
  assert (∀ x y, w_eq W x y → w_eq Wt x y) as HeWt.
  { intros x y H. apply at_choice_eq. by apply geq_base. }
  assert (∀ x y, w_lt W x y → w_lt Wt x y) as HlWt.
  { intros x y H. apply at_choice_lt. apply glt_base. done. }
  assert (∀ x y, pick P ch x y → w_lt Wt x y) as HpWt.
  { intros x y H. apply at_choice_pick. by apply pick_app_l. }
  split_and!.
  - split_and!.
    + simpl. set_solver.
    + apply (wgen_into_eq _ _ _ Wt HWt); [exact HeWt|]. intros x y [H|H]; [by apply HlWt|by apply HpWt].
    + apply (wgen_into _ _ _ Wt HWt); [exact HeWt|]. intros x y [H|H]; [by apply HlWt|by apply HpWt].
    + exact HSt.
  - exact HN.
  - done.
  - intros x y Hx Hy. split; intros H; apply (Hold x y Hx Hy); [by apply HeT|by apply HlT].
Qed.

(** ** Two creations at once

    A fresh extension with new choices is valid, and two of them, made by
    two components from one pending world, join to a valid pending world.
    This is the case of the monotonicity proof where the other
    component's future creates choices too. *)

Lemma pfresh_valid W P N W1 Pn : pvalid W P → pfresh W P N W1 Pn → pvalid W1 (P ++ Pn).
Proof.
  intros _ (HW1 & HP1 & Hfr). split_and!; [done|done|].
  intros ch Hl. rewrite length_app in Hl.
  rewrite <-(take_drop (length P) ch).
  apply (Hfr (take (length P) ch) (drop (length P) ch)).
  - rewrite length_take. lia.
  - rewrite length_drop. lia.
Qed.

Theorem pcreate_join W P N1 W1 Pn1 N2 W2 Pn2 :
  pvalid W P → pfresh W P N1 W1 Pn1 → pfresh W P N2 W2 Pn2 → N1 ## w_names W2 →
  pvalid (wjoin W1 W2) ((P ++ Pn2) ++ Pn1).
Proof.
  intros HV H1 H2 HN.
  apply (pjoin_valid W P N1 W1 Pn1 W2 (P ++ Pn2)); [done|done| |by eapply pfresh_valid|done].
  by eapply pfresh_pext.
Qed.
