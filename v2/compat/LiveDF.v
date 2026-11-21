(** * live ⊆ DF for closed processes (stage S4, quirk G2)

      ∅ ⊫_W p : T  ⟹  ∅ ⊨_W p : T        when T is tfree and box-free

    [live_sub_df]. A closed process has a [tfree] result, and without □
    it is built from ∗, ⊗ and ⊕. For such T the value relation reads no
    E, so V at T is the same for both cost tables and every level
    ([Vrel_boxfree]). A closed process takes τ steps only, so
    the proof reads no value from outside. A τ step costs at least as
    much in κ_DF as in κ_L, except a link, which costs 0 in both and is
    read inside the level of κ_DF by induction on the size of the soup
    ([psize_link]).

    What does not hold by this argument (docs/redesign/progress.md,
    S4.7). For an open interface or a higher-order T, V of κ_DF must be
    read at the argument of an arrow and at a received payload, in a
    negative position, and V of κ_DF is not included in V of κ_L (a
    divergent closure is in the first only). *)

From GV Require Export relation.Adequacy compat.Blind.

(** ** Sizes *)

Fixpoint esize (e : expr) : nat :=
  match e with
  | Var _ | EUnit | Chan _ | ENew _ => 1
  | Lam e | Inj _ e | EBox e | Op _ e => S (esize e)
  | App a b | Pair a b | LetU a b | LetP a b => S (esize a + esize b)
  | Case a b c => S (esize a + esize b + esize c)
  end.

Lemma esize_emap g e : esize (emap g e) = esize e.
Proof. induction e; simpl; lia. Qed.

Lemma tstep_link_size e os e' : tstep e (LSess (SLink os)) e' → esize e' < esize e.
Proof.
  remember (LSess (SLink os)) as α eqn:Hα. induction 1 as [e α e' Hh|f e α e' Hf Hs IH]; subst.
  - inversion Hh; subst; simpl; lia.
  - specialize (IH eq_refl). destruct f; simpl; lia.
Qed.

Definition msize (E : gmultiset expr) : nat := sum_list_with esize (elements E).

Lemma sum_list_with_perm (l k : list expr) : l ≡ₚ k → sum_list_with esize l = sum_list_with esize k.
Proof. induction 1; simpl; lia. Qed.

Lemma msize_disj_union X Y : msize (X ⊎ Y) = msize X + msize Y.
Proof.
  unfold msize. rewrite (sum_list_with_perm _ _ (gmultiset_elements_disj_union X Y)).
  apply sum_list_with_app.
Qed.

Lemma msize_singleton e : msize {[+ e +]} = esize e.
Proof. unfold msize. rewrite gmultiset_elements_singleton. simpl. lia. Qed.

Lemma msize_emap g E : msize (gmultiset_map (emap g) E) = msize E.
Proof.
  induction E as [|e E IH] using gmultiset_ind; [done|].
  rewrite gmultiset_map_disj_union, gmultiset_map_singleton, !msize_disj_union, !msize_singleton.
  by rewrite esize_emap, IH.
Qed.

Definition psize (p : proc) : nat := msize p.2.

(** A link step makes the soup smaller. *)
Lemma psize_link q i o1 o2 q' : istep q (EvSolo i (LSess (SLink ({[o1]} ∪ {[o2]}))) (PickLink o1 o2)) q' → psize (erase q') < psize (erase q).
Proof.
  intros Hst. inversion Hst as [| | | | | | |C M i' e o1' o2' e' Hi Hs HC| ]; subst.
  unfold psize, erase. simpl. rewrite soup_fmap, msize_emap.
  rewrite (soup_update _ _ _ _ Hi), (soup_delete _ _ _ Hi), !msize_disj_union, !msize_singleton.
  apply tstep_link_size in Hs. lia.
Qed.

(** ** Box-free results

    A process result is [tfree] (types/Types.v), built from ∗, ⊗, ⊕ and □.
    [boxfree] rules out □. *)

Fixpoint boxfree (T : ty) : Prop :=
  match T with
  | TBox _ _ _ _ _ _ => False
  | TProd A B | TSum A B => boxfree A ∧ boxfree B
  | _ => True
  end.

Lemma Vrel_boxfree κ κ' T : tfree T → boxfree T → ∀ i i' W Θ v, Vrel κ i W Θ T v ↔ Vrel κ' i' W Θ T v.
Proof.
  induction 1 as [| |T1 U _ IH1 _ IH2|T1 U _ IH1 _ IH2]; simpl; intros Hb i i' W Θ v.
  - by rewrite !Vrel_unit_iff.
  - done.
  - destruct Hb as [Hb1 Hb2]. rewrite !Vrel_prod_iff.
    setoid_rewrite (IH1 Hb1 i i'). by setoid_rewrite (IH2 Hb2 i i').
  - destruct Hb as [Hb1 Hb2]. rewrite !Vrel_sum_iff.
    setoid_rewrite (IH1 Hb1 i i'). by setoid_rewrite (IH2 Hb2 i i').
Qed.

(** ** The inclusion *)

(** A step of cost c at every level gives every level. *)
Lemma at_cost_all κ c W Σ T p :
  (∀ m, olt ozero m → at_cost_P m c (Prel κ) (Prel κ m) W Σ T p) → ∀ m, Prel κ m W Σ T p.
Proof.
  intros H m. destruct (decide (c = 0)) as [->|Hc].
  - destruct (H (osucc m) I) as [H1 _]. eapply Prel_down; [|exact (H1 eq_refl)]. by apply olt_ole, olt_succ.
  - assert (olt m (oadd m c)) as Hm by exact (oadd_lt m c _ Hc (ole_refl _)).
    destruct (H (oadd m c) (ole_trans_lt ozero m _ I Hm)) as [_ H2]. apply (H2 Hc). apply ole_refl.
Qed.

Lemma live_sub_df_n n : ∀ W T p, tfree T → boxfree T → (∀ m, Prel κ_L m W ∅ T p) → Prel κ_DF n W ∅ T p.
Proof.
  induction n as [n IHn] using oind. intros W T p HT Hb.
  revert W.
  induction p as [p IHp] using (well_founded_induction (well_founded_ltof _ psize)).
  intros W HL. apply Prel_iff. intros Hn0 W1 HW1 h D Hh.
  assert (∀ m, olt ozero m → Pbody κ_L m (Vrel κ_L) (Prel κ_L) (Vrel κ_L m) (Prel κ_L m) W ∅ T p) as HB
    by (intros m Hm; by apply Prel_iff).
  pose proof (λ m Hm, HB m Hm W1 HW1 h D Hh) as HC.
  rewrite (fuse_ok_empty _ _ _ Hh), pfuse_empty, kren_empty, sdrop_empty in HC |- *.
  destruct (HC (onat 1) (onat_lt 0 1 ltac:(lia))) as (Hs & Hr & H1 & H2 & H3 & H4 & H5 & H6 & H7).
  split; [|split; [|unfold Psteps; split_and!]].
  - intros Hirr. destruct (Hs Hirr) as (v & E & -> & Hv & HE). exists v, E.
    split_and!; [done| |done]. by apply (Vrel_boxfree κ_L κ_DF T HT Hb (onat 1) n).
  - done.
  - intros q ev q' Hq Hst Hτ Hd.
    assert (∀ m, Prel κ_L m W1 ∅ T (erase q')) as HL'.
    { apply (at_cost_all κ_L (ev_cost κ_L ev)). intros m Hm.
      destruct (HC m Hm) as (_ & _ & A & _). exact (A q ev q' Hq Hst Hτ Hd). }
    split.
    + intros Hc. assert (∃ i o1 o2, ev = EvSolo i (LSess (SLink ({[o1]} ∪ {[o2]}))) (PickLink o1 o2)) as (i & o1 & o2 & ->).
      { clear -Hst Hc Hτ. destruct Hst; simpl in Hc, Hτ; try discriminate; eauto; by unfold ev_tau in Hτ. }
      apply (IHp (erase q')); [|exact HL'].
      unfold ltof. replace (psize p) with (psize (pmap h p)) by (unfold psize, pmap, emapE; simpl; apply msize_emap).
      rewrite <-Hq. by eapply psize_link.
    + intros Hc j Hj. eapply (IHn j (oadd_lt _ _ _ Hc Hj)); [done|done|]. intros m. apply HL'.
  - intros q i o w q' Hq Hst. exfalso.
    destruct (H2 q i o w q' Hq Hst) as (? & ? & ? & ? & ? & ? & ? & ? & ? & A & _).
    by rewrite lookup_empty in A.
  - intros q i o w q' Hq Hst. exfalso.
    destruct (H3 q i o w q' Hq Hst) as (? & ? & ? & ? & ? & A & _). by rewrite lookup_empty in A.
  - intros q i o q' Hq Hst. exfalso.
    destruct (H4 q i o q' Hq Hst) as (? & ? & A & _). by rewrite lookup_empty in A.
  - intros q i o b q' Hq Hst. exfalso.
    destruct (H5 q i o b q' Hq Hst) as (? & ? & ? & ? & A & _). by rewrite lookup_empty in A.
  - intros q i o b q' Hq Hst. exfalso.
    destruct (H6 q i o b q' Hq Hst) as (? & ? & ? & ? & A & _). by rewrite lookup_empty in A.
  - intros q i os q' Hq Hst. exfalso.
    destruct (H7 q i os q' Hq Hst) as (? & ? & ? & ? & ? & _ & _ & A & _). by rewrite lookup_empty in A.
Qed.

(** live ⊆ DF, for a closed process at a box-free result. *)
Theorem live_sub_df W T p : tfree T → boxfree T → ∅ ⊫_W p : T → ∅ ⊨_W p : T.
Proof. intros HT Hb HL n. by apply live_sub_df_n. Qed.
