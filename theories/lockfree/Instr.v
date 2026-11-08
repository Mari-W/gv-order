(** * Instrumented semantics with thread identities (lock-freedom plan §4.1)

    A configuration is a set of restricted channels and a finite map
    from thread identifiers to terms. Every step is labelled with the
    identifiers of the threads that take part: one for β, new, spawn
    and a link, two for a message, a close and a choice. The erasure
    forgets the identifiers and gives the process of Syntax.v. The two
    simulation lemmas [istep_erase] and [preduction_lift] relate the
    instrumented steps to the τ steps of the process semantics, in both
    directions. Nothing of the existing development changes.

    A link (P-Act-Link) renames the removed end in every thread. Only
    the thread that runs the link takes part in that step. The thread
    holding the peer of the removed end is renamed and does not act. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export lang.Safety.

Definition config : Type := gset chan * gmap nat expr.

(** ** Erasure *)

Definition soup (M : gmap nat expr) : gmultiset expr :=
  list_to_set_disj ((map_to_list M).*2).

Definition erase (q : config) : proc := (q.1, soup q.2).

Lemma soup_empty : soup ∅ = ∅.
Proof. unfold soup. by rewrite map_to_list_empty. Qed.

Lemma soup_insert M i e : M !! i = None → soup (<[i := e]> M) = soup M ⊎ {[+ e +]}.
Proof.
  intros Hi. unfold soup.
  rewrite (list_to_set_disj_perm _ (e :: (map_to_list M).*2)).
  - rewrite list_to_set_disj_cons. by rewrite (comm_L (⊎)).
  - rewrite (map_to_list_insert M i e Hi). done.
Qed.

Lemma soup_delete M i e : M !! i = Some e → soup M = soup (delete i M) ⊎ {[+ e +]}.
Proof.
  intros Hi. rewrite <-(soup_insert (delete i M) i e) by apply lookup_delete_eq.
  by rewrite insert_delete_id.
Qed.

Lemma soup_update M i e e' :
  M !! i = Some e → soup (<[i := e']> M) = soup (delete i M) ⊎ {[+ e' +]}.
Proof.
  intros Hi. rewrite <-insert_delete_eq. apply soup_insert, lookup_delete_eq.
Qed.

Lemma elem_of_soup e M : e ∈ soup M ↔ ∃ i, M !! i = Some e.
Proof.
  unfold soup. rewrite elem_of_list_to_set_disj, list_elem_of_fmap. split.
  - intros ([i e'] & -> & H). apply elem_of_map_to_list in H. by exists i.
  - intros (i & H). exists (i, e). split; [done|]. by apply elem_of_map_to_list.
Qed.

Lemma soup_extract M E e :
  soup M = E ⊎ {[+ e +]} → ∃ i, M !! i = Some e ∧ soup (delete i M) = E.
Proof.
  intros H. assert (e ∈ soup M) as He by (rewrite H; multiset_solver).
  apply elem_of_soup in He as [i Hi]. exists i. split; [done|].
  rewrite (soup_delete M i e Hi) in H. multiset_solver.
Qed.

Lemma soup_fmap (f : expr → expr) M : soup (f <$> M) = gmultiset_map f (soup M).
Proof.
  induction M as [|i e M Hi IH] using map_ind.
  - by rewrite fmap_empty, soup_empty, gmultiset_map_empty.
  - rewrite fmap_insert, !soup_insert; [|done|by rewrite lookup_fmap, Hi].
    by rewrite gmultiset_map_disj_union, gmultiset_map_singleton, IH.
Qed.

(** Two distinct threads updated at once. *)
Lemma soup_update2 M i j e f e' f' :
  i ≠ j → M !! i = Some e → M !! j = Some f →
  soup M = soup (delete j (delete i M)) ⊎ {[+ e +]} ⊎ {[+ f +]} ∧
  soup (<[j := f']> (<[i := e']> M)) = soup (delete j (delete i M)) ⊎ {[+ e' +]} ⊎ {[+ f' +]}.
Proof.
  intros Hij Hi Hj.
  assert (delete i M !! j = Some f) as Hj' by (rewrite lookup_delete_ne; done).
  split.
  - rewrite (soup_delete M i e Hi), (soup_delete (delete i M) j f Hj'). multiset_solver.
  - rewrite (soup_update _ j f f') by (rewrite lookup_insert_ne; done).
    rewrite delete_insert_ne by done.
    rewrite (soup_update _ i e e') by (rewrite lookup_delete_ne; done).
    rewrite delete_delete. multiset_solver.
Qed.

(** ** Steps *)

Inductive istep : config → gset nat → config → Prop :=
  | IBeta C M i e e' :
      M !! i = Some e → tstep e LBeta e' →
      istep (C, M) {[i]} (C, <[i := e']> M)
  | INew C M i e c e' :
      M !! i = Some e → tstep e (LNew c) e' →
      c ∉ C → c ∉ echans (soup M) →
      istep (C, M) {[i]} (C ∪ {[c]}, <[i := e']> M)
  | ISpawn C M i j e v e' :
      M !! i = Some e → tstep e (LSpawn v) e' → M !! j = None →
      istep (C, M) {[i]} (C, <[j := App v EUnit]> (<[i := e']> M))
  | IMsg C M i j c v e e' f f' :
      i ≠ j → M !! i = Some e → M !! j = Some f →
      tstep e (LSess (SSend c v)) e' → tstep f (LSess (SRecv c v)) f' →
      istep (C, M) {[i; j]} (C, <[j := f']> (<[i := e']> M))
  | IClose C M i j c e e' f f' :
      i ≠ j → M !! i = Some e → M !! j = Some f →
      tstep e (LSess (SClos c)) e' → tstep f (LSess (SClos c)) f' → c ∈ C →
      istep (C, M) {[i; j]} (C ∖ {[c]}, <[j := f']> (<[i := e']> M))
  | IChoice C M i j c b e e' f f' :
      i ≠ j → M !! i = Some e → M !! j = Some f →
      tstep e (LSess (SSel c b)) e' → tstep f (LSess (SBra c b)) f' →
      istep (C, M) {[i; j]} (C, <[j := f']> (<[i := e']> M))
  | ILink C M i e c d e' :
      M !! i = Some e → tstep e (LSess (SLink {[c; d]})) e' → c ∈ C →
      istep (C, M) {[i]} (C ∖ {[c]}, chsubst c d <$> (<[i := e']> M)).

Definition istep' (q q' : config) : Prop := ∃ L, istep q L q'.
Abbreviation isteps := (rtc istep').

(** ** Simulation, instrumented to plain *)

Theorem istep_erase q L q' : istep q L q' → preduction (erase q) (erase q').
Proof.
  destruct 1 as [C M i e e' Hi Hst|C M i e c e' Hi Hst HC Hc|C M i j e v e' Hi Hst Hj
    |C M i j c v e e' f f' Hij Hi Hj He Hf|C M i j c e e' f f' Hij Hi Hj He Hf HC
    |C M i j c b e e' f f' Hij Hi Hj He Hf|C M i e c d e' Hi Hst HC]; unfold erase; simpl.
  - rewrite (soup_delete M i e Hi), (soup_update M i e e' Hi). by apply PStepBeta.
  - rewrite (soup_update M i e e' Hi). rewrite (soup_delete M i e Hi) in Hc |- *.
    rewrite echans_disj_union, echans_singleton in Hc.
    apply PStepNew; [done|done|set_solver|set_solver].
  - assert (i ≠ j) by (intros ->; congruence).
    rewrite soup_insert by (rewrite lookup_insert_ne; done).
    rewrite (soup_update M i e e' Hi), (soup_delete M i e Hi). by eapply PStepSpawn.
  - destruct (soup_update2 M i j e f e' f' Hij Hi Hj) as [-> ->]. by eapply PStepMsg.
  - destruct (soup_update2 M i j e f e' f' Hij Hi Hj) as [-> ->]. by eapply PStepClose.
  - destruct (soup_update2 M i j e f e' f' Hij Hi Hj) as [-> ->]. by eapply PStepChoice.
  - rewrite soup_fmap, (soup_update M i e e' Hi), (soup_delete M i e Hi).
    by apply PStepLink.
Qed.

Corollary isteps_erase q q' : isteps q q' → pred_star (erase q) (erase q').
Proof.
  induction 1 as [|q1 q2 q3 [L H] _ IH]; [done|].
  eapply rtc_l; [|exact IH]. by eapply istep_erase.
Qed.

(** ** Simulation, plain to instrumented *)

Theorem preduction_lift q p' :
  preduction (erase q) p' → ∃ L q', istep q L q' ∧ erase q' = p'.
Proof.
  destruct q as [C M]. unfold erase, preduction; simpl. intros H.
  remember (C, soup M) as p0 eqn:Hp0. remember PTau as π eqn:Hπ.
  destruct H as [|C0 E e e' Hst|C0 E e c e' Hst HC HcE Hce|C0 E e v e' Hst
    |C0 E c v e e' f f' He Hf|C0 E c e e' f f' He Hf HC
    |C0 E c b e e' f f' He Hf|C0 E e c d e' Hst HC]; try discriminate;
    injection Hp0 as <- HE; symmetry in HE.
  - destruct (soup_extract M E e HE) as (i & Hi & HEi).
    eexists _, _. split; [by eapply IBeta|].
    unfold erase; simpl. by rewrite (soup_update M i e e' Hi), HEi.
  - destruct (soup_extract M E e HE) as (i & Hi & HEi).
    eexists _, _. split.
    + eapply INew; [done|done|done|]. rewrite HE, echans_disj_union, echans_singleton.
      set_solver.
    + unfold erase; simpl. by rewrite (soup_update M i e e' Hi), HEi.
  - destruct (soup_extract M E e HE) as (i & Hi & HEi).
    set (j := fresh (dom M)).
    assert (M !! j = None) as Hj by (apply not_elem_of_dom, is_fresh).
    assert (i ≠ j) by (intros ->; congruence).
    eexists _, _. split; [by eapply ISpawn|].
    unfold erase; simpl. rewrite soup_insert by (rewrite lookup_insert_ne; done).
    by rewrite (soup_update M i e e' Hi), HEi.
  - destruct (soup_extract M _ f HE) as (j & Hj & HEj).
    destruct (soup_extract _ E e HEj) as (i & Hi & HEi).
    assert (i ≠ j) as Hij by (intros ->; by rewrite lookup_delete_eq in Hi).
    rewrite lookup_delete_ne in Hi by done.
    eexists _, _. split; [by eapply IMsg|].
    unfold erase; simpl. destruct (soup_update2 M i j e f e' f' Hij Hi Hj) as [_ ->].
    by rewrite delete_delete, HEi.
  - destruct (soup_extract M _ f HE) as (j & Hj & HEj).
    destruct (soup_extract _ E e HEj) as (i & Hi & HEi).
    assert (i ≠ j) as Hij by (intros ->; by rewrite lookup_delete_eq in Hi).
    rewrite lookup_delete_ne in Hi by done.
    eexists _, _. split; [by eapply IClose|].
    unfold erase; simpl. destruct (soup_update2 M i j e f e' f' Hij Hi Hj) as [_ ->].
    by rewrite delete_delete, HEi.
  - destruct (soup_extract M _ f HE) as (j & Hj & HEj).
    destruct (soup_extract _ E e HEj) as (i & Hi & HEi).
    assert (i ≠ j) as Hij by (intros ->; by rewrite lookup_delete_eq in Hi).
    rewrite lookup_delete_ne in Hi by done.
    eexists _, _. split; [by eapply IChoice|].
    unfold erase; simpl. destruct (soup_update2 M i j e f e' f' Hij Hi Hj) as [_ ->].
    by rewrite delete_delete, HEi.
  - destruct (soup_extract M E e HE) as (i & Hi & HEi).
    eexists _, _. split; [by eapply ILink|].
    unfold erase; simpl. by rewrite soup_fmap, (soup_update M i e e' Hi), HEi.
Qed.

Corollary pred_star_lift q p' :
  pred_star (erase q) p' → ∃ q', isteps q q' ∧ erase q' = p'.
Proof.
  intros H. remember (erase q) as p eqn:Hp. revert q Hp.
  induction H as [p|p p1 p2 Hst _ IH]; intros q ->.
  - by exists q.
  - destruct (preduction_lift q p1 Hst) as (L & q1 & Hq & <-).
    destruct (IH q1 eq_refl) as (q2 & Hq2 & <-).
    exists q2. split; [|done]. eapply rtc_l; [by exists L|done].
Qed.

(** ** Channel renaming of terms and the redex

    [emap g] renames every channel name by g. The renaming of a link
    ([chsubst]) and the erasure of all names ([TauThread.v]) are
    instances. A renaming leaves the redex in place and renames its
    channels. *)

Fixpoint emap (g : chan → chan) (e : expr) : expr :=
  match e with
  | Var x => Var x
  | EUnit => EUnit
  | Konst k => Konst k
  | Chan c => Chan (g c)
  | Lam e => Lam (emap g e)
  | App e1 e2 => App (emap g e1) (emap g e2)
  | Pair e1 e2 => Pair (emap g e1) (emap g e2)
  | LetU e1 e2 => LetU (emap g e1) (emap g e2)
  | LetP e1 e2 => LetP (emap g e1) (emap g e2)
  | Inj1 e => Inj1 (emap g e)
  | Inj2 e => Inj2 (emap g e)
  | Case e e1 e2 => Case (emap g e) (emap g e1) (emap g e2)
  | EBox e => EBox (emap g e)
  end.

Definition csub (c d x : chan) : chan := if decide (x = c) then d else x.

Lemma chsubst_emap c d e : chsubst c d e = emap (csub c d) e.
Proof. induction e; simpl; f_equal; auto. Qed.

Lemma emap_emap g h e : emap g (emap h e) = emap (g ∘ h) e.
Proof. induction e; simpl; f_equal; auto. Qed.

Lemma is_val_emap g e : is_val (emap g e) = is_val e.
Proof. induction e; simpl; try done; by rewrite ?IHe1, ?IHe2, ?IHe. Qed.

Definition amap (g : chan → chan) (a : action) : action :=
  match a with
  | ABeta => ABeta
  | ANew => ANew
  | ASpawn v => ASpawn (emap g v)
  | ARecv c => ARecv (g c)
  | ASend c v => ASend (g c) (emap g v)
  | AClos c => AClos (g c)
  | ALink c d => ALink (g c) (g d)
  | ASel c b => ASel (g c) b
  | ABra c => ABra (g c)
  end.

Lemma act_emap g e : act (emap g e) = amap g <$> act e.
Proof.
  induction e as [| | |c|e IH|e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2|e1 IH1 e2 IH2
    |e IH|e IH|e IH e1 IH1 e2 IH2|e IH]; simpl; try done; rewrite ?is_val_emap.
  - destruct (is_val e1) eqn:H1; [|done]. destruct (is_val e2) eqn:H2; [|done].
    destruct e1; simpl; try done.
    destruct k; destruct e2; simpl; try done.
    all: try (destruct e2_2; done).
    destruct e2_1; simpl; try done. destruct e2_2; done.
  - by destruct (is_val e1).
  - destruct (is_val e1); [|done]. by destruct e1.
  - destruct (is_val e1); [|done]. by destruct e1.
  - destruct (is_val e); [|done]. by destruct e.
Qed.

Lemma act_chsubst c d e : act (chsubst c d e) = amap (csub c d) <$> act e.
Proof. rewrite chsubst_emap. apply act_emap. Qed.

(** ** Kinds of actions *)

Definition is_admin (a : action) : Prop :=
  match a with ABeta | ANew | ASpawn _ => True | _ => False end.

Definition is_sess (a : action) : Prop := is_Some (asubjs a).

Lemma admin_or_sess a : is_admin a ∨ is_sess a.
Proof. destruct a; simpl; unfold is_sess; simpl; eauto. Qed.

Lemma admin_not_sess a : is_admin a → is_sess a → False.
Proof. destruct a; simpl; unfold is_sess; simpl; try done; by intros _ [? ?]. Qed.

Lemma amap_admin g a : is_admin (amap g a) ↔ is_admin a.
Proof. by destruct a. Qed.

Lemma amap_sess g a : is_sess (amap g a) ↔ is_sess a.
Proof. unfold is_sess. destruct a; simpl; split; eauto. Qed.

Definition admin_lbl (α : tlabel) : Prop :=
  match α with LBeta | LNew _ | LSpawn _ => True | LSess _ => False end.

Lemma offers_admin a α : offers a α → is_admin a ↔ admin_lbl α.
Proof. destruct a, α; simpl; try done; by destruct σ. Qed.

(** ** Threads of a configuration *)

Definition pend (q : config) (t : nat) : Prop :=
  ∃ e a, q.2 !! t = Some e ∧ act e = Some a ∧ is_sess a.

Definition admin_at (q : config) (t : nat) : Prop :=
  ∃ e a, q.2 !! t = Some e ∧ act e = Some a ∧ is_admin a.

Definition enabled (q : config) (t : nat) : Prop := ∃ L q', istep q L q' ∧ t ∈ L.

(** A thread that does not take part keeps its term, up to the
    renaming of a link. *)
Lemma istep_other q L q' t e :
  istep q L q' → t ∉ L → q.2 !! t = Some e →
  ∃ g, q'.2 !! t = Some (emap g e).
Proof.
  intros Hst Ht Hte. assert (q'.2 !! t = Some e → ∃ g, q'.2 !! t = Some (emap g e)) as Hid.
  { intros H. exists id. rewrite H. f_equal. clear. induction e; simpl; f_equal; auto. }
  destruct Hst; simpl in *.
  - apply Hid. rewrite lookup_insert_ne; set_solver.
  - apply Hid. rewrite lookup_insert_ne; set_solver.
  - apply Hid. rewrite lookup_insert_ne; [|intros ->; congruence].
    rewrite lookup_insert_ne; set_solver.
  - apply Hid. rewrite !lookup_insert_ne; set_solver.
  - apply Hid. rewrite !lookup_insert_ne; set_solver.
  - apply Hid. rewrite !lookup_insert_ne; set_solver.
  - (* the link renames every thread *)
    clear Hid. exists (csub c d). rewrite lookup_fmap, lookup_insert_ne by set_solver.
    rewrite Hte. simpl. by rewrite chsubst_emap.
Qed.

Lemma istep_other_pend q L q' t : istep q L q' → t ∉ L → pend q t → pend q' t.
Proof.
  intros Hst Ht (e & a & He & Ha & Hs).
  destruct (istep_other q L q' t e Hst Ht He) as [g Hg].
  exists (emap g e), (amap g a). rewrite act_emap, Ha. split_and!; [done|done|].
  by apply amap_sess.
Qed.

Lemma istep_other_admin q L q' t : istep q L q' → t ∉ L → admin_at q t → admin_at q' t.
Proof.
  intros Hst Ht (e & a & He & Ha & Hs).
  destruct (istep_other q L q' t e Hst Ht He) as [g Hg].
  exists (emap g e), (amap g a). rewrite act_emap, Ha. split_and!; [done|done|].
  by apply amap_admin.
Qed.

(** A thread that takes part acts with its redex. A thread whose
    redex is administrative takes part alone, with that redex. *)
Lemma istep_actor q L q' t e :
  istep q L q' → t ∈ L → q.2 !! t = Some e →
  ∃ α e', tstep e α e' ∧
    (admin_lbl α → q'.2 !! t = Some e').
Proof.
  destruct 1; simpl; intros Ht Hte.
  - apply elem_of_singleton in Ht as ->. simplify_eq. eexists _, _. split; [done|].
    intros _. by rewrite lookup_insert_eq.
  - apply elem_of_singleton in Ht as ->. simplify_eq. eexists _, _. split; [done|].
    intros _. by rewrite lookup_insert_eq.
  - apply elem_of_singleton in Ht as ->. simplify_eq. eexists _, _. split; [done|].
    intros _. rewrite lookup_insert_ne by (intros ->; congruence).
    by rewrite lookup_insert_eq.
  - apply elem_of_union in Ht as [Ht|Ht]; apply elem_of_singleton in Ht as ->;
      simplify_eq; (eexists _, _; split; [done|done]).
  - apply elem_of_union in Ht as [Ht|Ht]; apply elem_of_singleton in Ht as ->;
      simplify_eq; (eexists _, _; split; [done|done]).
  - apply elem_of_union in Ht as [Ht|Ht]; apply elem_of_singleton in Ht as ->;
      simplify_eq; (eexists _, _; split; [done|done]).
  - apply elem_of_singleton in Ht as ->. simplify_eq. eexists _, _. split; [done|done].
Qed.

Lemma enabled_act q t e : enabled q t → q.2 !! t = Some e → ∃ a, act e = Some a.
Proof.
  intros (L & q' & Hst & Ht) He.
  destruct (istep_actor q L q' t e Hst Ht He) as (α & e' & Hs & _).
  destruct (act_step _ _ _ Hs) as (a & Ha & _). by exists a.
Qed.

Lemma admin_step q L q' t e a :
  istep q L q' → t ∈ L → q.2 !! t = Some e → act e = Some a → is_admin a →
  ∃ α e', admin_lbl α ∧ tstep e α e' ∧ q'.2 !! t = Some e'.
Proof.
  intros Hst Ht He Ha Had.
  destruct (istep_actor q L q' t e Hst Ht He) as (α & e' & Hs & Hq).
  destruct (act_step _ _ _ Hs) as (a' & Ha' & Ho). rewrite Ha in Ha'. simplify_eq.
  assert (admin_lbl α) as Hα by (by apply (offers_admin a')).
  exists α, e'. auto.
Qed.

Lemma admin_enabled q t : admin_at q t → enabled q t.
Proof.
  destruct q as [C M]. intros (e & a & He & Ha & Had). simpl in *.
  destruct a; try done.
  - destruct (act_offer e ABeta LBeta Ha I) as [e' Hs].
    eexists _, _. split; [by eapply IBeta|set_solver].
  - set (c := fresh (C ∪ echans (soup M))).
    assert (c ∉ C ∪ echans (soup M)) as Hc by apply is_fresh.
    destruct (act_offer e ANew (LNew c) Ha I) as [e' Hs].
    eexists _, _. split; [eapply INew; [done|done|set_solver|set_solver]|set_solver].
  - destruct (act_offer e (ASpawn v) (LSpawn v) Ha eq_refl) as [e' Hs].
    set (j := fresh (dom M)).
    assert (M !! j = None) as Hj by (apply not_elem_of_dom, is_fresh).
    eexists _, _. split; [by eapply ISpawn|set_solver].
Qed.
