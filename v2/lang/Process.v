(** * Process steps: one instrumented semantics (stage S1, proposal §2.7)

    A configuration is a set C of restricted channels and a finite map
    from thread identifiers to terms. A step [istep q ev q'] carries an
    event ev that names the threads taking part and what happened: the
    family or the field and anchor of a creation, the transfer set of a
    spawn and of a message, the ends of a close, a choice and a link, and
    the session label of an external offer. The rules are named after
    the paper's P-Act rules.

    This is the only definition of process steps. The plain semantics on
    soups (C, E), with E a multiset of terms, is its erasure [pstep]. The
    multiset view [pspec] is a theorem about the erasure ([pstep_iff]),
    and every lifting of a soup replays a step of it ([pstep_lift]). *)

From stdpp Require Import relations.
From GV Require Export lang.Semantics.

(** ** Configurations and erasure *)

Definition config : Type := gset chan * gmap nat expr.

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

(** Every soup has a lifting. *)
Lemma soup_surj (E : gmultiset expr) : ∃ M, soup M = E.
Proof.
  induction E as [|e E (M & HM)] using gmultiset_ind.
  - exists ∅. apply soup_empty.
  - set (i := fresh (dom M)). assert (M !! i = None) as Hi by (apply not_elem_of_dom, is_fresh).
    exists (<[i := e]> M). rewrite soup_insert by done. rewrite HM. multiset_solver.
Qed.

Lemma erase_surj (p : proc) : ∃ q, erase q = p.
Proof. destruct p as [C E]. destruct (soup_surj E) as [M HM]. exists (C, M). by rewrite <-HM. Qed.

(** ** Events *)

Inductive event :=
  | EvBeta (i : nat)                                (* P-Act-Beta *)
  | EvNew (i : nat) (ℓ : family) (c : chan)         (* P-Act-New *)
  | EvNewAt (i : nat) (κ : field) (o : cend) (c : chan)  (* P-Act-NewAt *)
  | EvSpawn (i j : nat) (M : gset cend)             (* P-Act-Spawn: i spawns j, moving M *)
  | EvMsg (i j : nat) (o : cend) (M : gset cend)    (* P-Act-Msg: i sends on o to j, moving M *)
  | EvClose (i j : nat) (o : cend)                  (* P-Act-Close: i closes o, j closes o‾ *)
  | EvChoice (i j : nat) (o : cend) (b : bool)      (* P-Act-Choice: i selects b on o *)
  | EvLink (i : nat) (o1 o2 : cend)                 (* P-Act-Link: the channel of o1 goes *)
  | EvSess (i : nat) (σ : slabel).                  (* P-Act-Session: an external offer *)

Global Instance event_eq_dec : EqDecision event.
Proof. solve_decision. Defined.

(** The threads that take part. A spawn involves only its parent, a
    link only the thread that runs it. *)
Definition ev_parts (ev : event) : gset nat :=
  match ev with
  | EvBeta i | EvNew i _ _ | EvNewAt i _ _ _ | EvSpawn i _ _ | EvLink i _ _ | EvSess i _ => {[i]}
  | EvMsg i j _ _ | EvClose i j _ | EvChoice i j _ _ => {[i; j]}
  end.

(** Process labels π ::= τ | σ. *)
Inductive plabel :=
  | PTau
  | PSess (σ : slabel).

Definition ev_plabel (ev : event) : plabel :=
  match ev with EvSess _ σ => PSess σ | _ => PTau end.

(** The events of a closed configuration, all but external offers. *)
Definition ev_tau (ev : event) : Prop := ev_plabel ev = PTau.

Global Instance plabel_eq_dec : EqDecision plabel.
Proof. solve_decision. Defined.
Global Instance ev_tau_dec ev : Decision (ev_tau ev).
Proof. unfold ev_tau. apply _. Defined.

(** Administrative events: they cost nothing in the live table (§2.8). *)
Definition ev_admin (ev : event) : Prop :=
  match ev with EvBeta _ | EvNew _ _ _ | EvNewAt _ _ _ _ | EvSpawn _ _ _ | EvLink _ _ _ => True
              | _ => False end.

(** ** Process steps (the P-Act rules) *)

Inductive istep : config → event → config → Prop :=
  | p_act_beta C M i e e' :                            (* P-Act-Beta *)
      M !! i = Some e → tstep e LBeta e' →
      istep (C, M) (EvBeta i) (C, <[i := e']> M)
  | p_act_new C M i e ℓ c e' :                         (* P-Act-New *)
      (* the new channel is globally fresh *)
      M !! i = Some e → tstep e (LNew ℓ c) e' →
      c ∉ C → c ∉ echans (soup M) →
      istep (C, M) (EvNew i ℓ c) (C ∪ {[c]}, <[i := e']> M)
  | p_act_new_at C M i e κ o c e' :                    (* P-Act-NewAt *)
      M !! i = Some e → tstep e (LNewAt κ o c) e' →
      c ∉ C → c ∉ echans (soup M) →
      istep (C, M) (EvNewAt i κ o c) (C ∪ {[c]}, <[i := e']> M)
  | p_act_spawn C M i j e Mv v e' :                    (* P-Act-Spawn *)
      M !! i = Some e → tstep e (LSpawn Mv v) e' → M !! j = None →
      istep (C, M) (EvSpawn i j Mv) (C, <[j := App v EUnit]> (<[i := e']> M))
  | p_act_msg C M i j o Mv v e e' f f' :               (* P-Act-Msg *)
      (* a send on o meets a receive on o‾; the channel may be free *)
      i ≠ j → M !! i = Some e → M !! j = Some f →
      tstep e (LSess (SSend o Mv v)) e' → tstep f (LSess (SRecv o‾ v)) f' →
      istep (C, M) (EvMsg i j o Mv) (C, <[j := f']> (<[i := e']> M))
  | p_act_close C M i j o e e' f f' :                  (* P-Act-Close *)
      i ≠ j → M !! i = Some e → M !! j = Some f →
      tstep e (LSess (SClose o)) e' → tstep f (LSess (SClose o‾)) f' → ech o ∈ C →
      istep (C, M) (EvClose i j o) (C ∖ {[ech o]}, <[j := f']> (<[i := e']> M))
  | p_act_choice C M i j o b e e' f f' :               (* P-Act-Choice *)
      i ≠ j → M !! i = Some e → M !! j = Some f →
      tstep e (LSess (SSel o b)) e' → tstep f (LSess (SBra o‾ b)) f' →
      istep (C, M) (EvChoice i j o b) (C, <[j := f']> (<[i := e']> M))
  | p_act_link C M i e o1 o2 e' :                      (* P-Act-Link *)
      (* the channel of o1 is restricted and goes; every thread is
         renamed, the actor's continuation included, so the holder of
         o1‾ now holds o2 (csub). The label is unordered, so the same
         rule removes either channel. *)
      M !! i = Some e → tstep e (LSess (SLink {[o1; o2]})) e' → ech o1 ∈ C →
      istep (C, M) (EvLink i o1 o2) (C ∖ {[ech o1]}, emap (csub o1 o2) <$> (<[i := e']> M))
  | p_act_session C M i e σ e' :                       (* P-Act-Session *)
      (* an offer on free channels; a send extrudes its transfer set *)
      M !! i = Some e → tstep e (LSess σ) e' → subjs σ ## C →
      istep (C, M) (EvSess i σ) (C ∖ sentc σ, <[i := e']> M).

(** The steps of a closed configuration. *)
Definition itstep (q : config) (ev : event) (q' : config) : Prop := istep q ev q' ∧ ev_tau ev.
Definition itstep' (q q' : config) : Prop := ∃ ev, itstep q ev q'.
Abbreviation itsteps := (rtc itstep').

(** ** The plain semantics: the erasure *)

Definition pstep (p : proc) (π : plabel) (p' : proc) : Prop :=
  ∃ q ev q', erase q = p ∧ istep q ev q' ∧ erase q' = p' ∧ ev_plabel ev = π.

(** Process reduction p → p' is a τ step. *)
Definition preduction (p p' : proc) : Prop := pstep p PTau p'.
Abbreviation pred_star := (rtc preduction).

Definition pirred (p : proc) : Prop := ∀ π p', ¬ pstep p π p'.

(** ** The multiset view of the erasure *)

Inductive pspec : proc → plabel → proc → Prop :=
  | ps_session C E e σ e' :
      tstep e (LSess σ) e' → subjs σ ## C →
      pspec (C, E ⊎ {[+ e +]}) (PSess σ) (C ∖ sentc σ, E ⊎ {[+ e' +]})
  | ps_beta C E e e' :
      tstep e LBeta e' →
      pspec (C, E ⊎ {[+ e +]}) PTau (C, E ⊎ {[+ e' +]})
  | ps_new C E e ℓ c e' :
      tstep e (LNew ℓ c) e' → c ∉ C → c ∉ echans E → c ∉ fchans e →
      pspec (C, E ⊎ {[+ e +]}) PTau (C ∪ {[c]}, E ⊎ {[+ e' +]})
  | ps_new_at C E e κ o c e' :
      tstep e (LNewAt κ o c) e' → c ∉ C → c ∉ echans E → c ∉ fchans e →
      pspec (C, E ⊎ {[+ e +]}) PTau (C ∪ {[c]}, E ⊎ {[+ e' +]})
  | ps_spawn C E e Mv v e' :
      tstep e (LSpawn Mv v) e' →
      pspec (C, E ⊎ {[+ e +]}) PTau (C, E ⊎ {[+ e' +]} ⊎ {[+ App v EUnit +]})
  | ps_msg C E o Mv v e e' f f' :
      tstep e (LSess (SSend o Mv v)) e' → tstep f (LSess (SRecv o‾ v)) f' →
      pspec (C, E ⊎ {[+ e +]} ⊎ {[+ f +]}) PTau (C, E ⊎ {[+ e' +]} ⊎ {[+ f' +]})
  | ps_close C E o e e' f f' :
      tstep e (LSess (SClose o)) e' → tstep f (LSess (SClose o‾)) f' → ech o ∈ C →
      pspec (C, E ⊎ {[+ e +]} ⊎ {[+ f +]}) PTau (C ∖ {[ech o]}, E ⊎ {[+ e' +]} ⊎ {[+ f' +]})
  | ps_choice C E o b e e' f f' :
      tstep e (LSess (SSel o b)) e' → tstep f (LSess (SBra o‾ b)) f' →
      pspec (C, E ⊎ {[+ e +]} ⊎ {[+ f +]}) PTau (C, E ⊎ {[+ e' +]} ⊎ {[+ f' +]})
  | ps_link C E e o1 o2 e' :
      tstep e (LSess (SLink {[o1; o2]})) e' → ech o1 ∈ C →
      pspec (C, E ⊎ {[+ e +]}) PTau (C ∖ {[ech o1]}, emapE (csub o1 o2) (E ⊎ {[+ e' +]})).

(** A step erases to its multiset view. *)
Theorem istep_pspec q ev q' : istep q ev q' → pspec (erase q) (ev_plabel ev) (erase q').
Proof.
  destruct 1 as [C M i e e' Hi Hst|C M i e ℓ c e' Hi Hst HC Hc|C M i e κ o c e' Hi Hst HC Hc
    |C M i j e Mv v e' Hi Hst Hj
    |C M i j o Mv v e e' f f' Hij Hi Hj He Hf|C M i j o e e' f f' Hij Hi Hj He Hf HC
    |C M i j o b e e' f f' Hij Hi Hj He Hf|C M i e o1 o2 e' Hi Hst HC
    |C M i e σ e' Hi Hst HC]; unfold erase; simpl.
  - rewrite (soup_delete M i e Hi), (soup_update M i e e' Hi). by apply ps_beta.
  - rewrite (soup_update M i e e' Hi). rewrite (soup_delete M i e Hi) in Hc |- *.
    rewrite echans_disj_union, echans_singleton in Hc.
    eapply ps_new; [done|done|set_solver|set_solver].
  - rewrite (soup_update M i e e' Hi). rewrite (soup_delete M i e Hi) in Hc |- *.
    rewrite echans_disj_union, echans_singleton in Hc.
    eapply ps_new_at; [done|done|set_solver|set_solver].
  - assert (i ≠ j) by (intros ->; congruence).
    rewrite soup_insert by (rewrite lookup_insert_ne; done).
    rewrite (soup_update M i e e' Hi), (soup_delete M i e Hi). by eapply ps_spawn.
  - destruct (soup_update2 M i j e f e' f' Hij Hi Hj) as [-> ->]. by eapply ps_msg.
  - destruct (soup_update2 M i j e f e' f' Hij Hi Hj) as [-> ->]. by eapply ps_close.
  - destruct (soup_update2 M i j e f e' f' Hij Hi Hj) as [-> ->]. by eapply ps_choice.
  - rewrite soup_fmap, (soup_update M i e e' Hi), (soup_delete M i e Hi).
    by eapply ps_link.
  - rewrite (soup_delete M i e Hi), (soup_update M i e e' Hi). by apply ps_session.
Qed.

(** Every lifting of a soup replays a step of its multiset view. *)
Theorem pspec_lift q π p' :
  pspec (erase q) π p' → ∃ ev q', istep q ev q' ∧ ev_plabel ev = π ∧ erase q' = p'.
Proof.
  destruct q as [C M]. unfold erase; simpl. intros H.
  remember (C, soup M) as p0 eqn:Hp0.
  destruct H as [C0 E e σ e' Hst HC|C0 E e e' Hst|C0 E e ℓ c e' Hst HC HcE Hce
    |C0 E e κ o c e' Hst HC HcE Hce|C0 E e Mv v e' Hst
    |C0 E o Mv v e e' f f' He Hf|C0 E o e e' f f' He Hf HC
    |C0 E o b e e' f f' He Hf|C0 E e o1 o2 e' Hst HC];
    injection Hp0 as <- HE; symmetry in HE.
  - destruct (soup_extract M E e HE) as (i & Hi & HEi).
    eexists _, _. split_and!; [by eapply p_act_session|done|].
    unfold erase; simpl. by rewrite (soup_update M i e e' Hi), HEi.
  - destruct (soup_extract M E e HE) as (i & Hi & HEi).
    eexists _, _. split_and!; [by eapply p_act_beta|done|].
    unfold erase; simpl. by rewrite (soup_update M i e e' Hi), HEi.
  - destruct (soup_extract M E e HE) as (i & Hi & HEi).
    eexists _, _. split_and!.
    + eapply p_act_new; [done|done|done|]. rewrite HE, echans_disj_union, echans_singleton.
      set_solver.
    + done.
    + unfold erase; simpl. by rewrite (soup_update M i e e' Hi), HEi.
  - destruct (soup_extract M E e HE) as (i & Hi & HEi).
    eexists _, _. split_and!.
    + eapply p_act_new_at; [done|done|done|]. rewrite HE, echans_disj_union, echans_singleton.
      set_solver.
    + done.
    + unfold erase; simpl. by rewrite (soup_update M i e e' Hi), HEi.
  - destruct (soup_extract M E e HE) as (i & Hi & HEi).
    set (j := fresh (dom M)).
    assert (M !! j = None) as Hj by (apply not_elem_of_dom, is_fresh).
    assert (i ≠ j) by (intros ->; congruence).
    eexists _, _. split_and!; [by eapply p_act_spawn|done|].
    unfold erase; simpl. rewrite soup_insert by (rewrite lookup_insert_ne; done).
    by rewrite (soup_update M i e e' Hi), HEi.
  - destruct (soup_extract M _ f HE) as (j & Hj & HEj).
    destruct (soup_extract _ E e HEj) as (i & Hi & HEi).
    assert (i ≠ j) as Hij by (intros ->; by rewrite lookup_delete_eq in Hi).
    rewrite lookup_delete_ne in Hi by done.
    eexists _, _. split_and!; [by eapply p_act_msg|done|].
    unfold erase; simpl. destruct (soup_update2 M i j e f e' f' Hij Hi Hj) as [_ ->].
    by rewrite delete_delete, HEi.
  - destruct (soup_extract M _ f HE) as (j & Hj & HEj).
    destruct (soup_extract _ E e HEj) as (i & Hi & HEi).
    assert (i ≠ j) as Hij by (intros ->; by rewrite lookup_delete_eq in Hi).
    rewrite lookup_delete_ne in Hi by done.
    eexists _, _. split_and!; [by eapply p_act_close|done|].
    unfold erase; simpl. destruct (soup_update2 M i j e f e' f' Hij Hi Hj) as [_ ->].
    by rewrite delete_delete, HEi.
  - destruct (soup_extract M _ f HE) as (j & Hj & HEj).
    destruct (soup_extract _ E e HEj) as (i & Hi & HEi).
    assert (i ≠ j) as Hij by (intros ->; by rewrite lookup_delete_eq in Hi).
    rewrite lookup_delete_ne in Hi by done.
    eexists _, _. split_and!; [by eapply p_act_choice|done|].
    unfold erase; simpl. destruct (soup_update2 M i j e f e' f' Hij Hi Hj) as [_ ->].
    by rewrite delete_delete, HEi.
  - destruct (soup_extract M E e HE) as (i & Hi & HEi).
    eexists _, _. split_and!; [by eapply p_act_link|done|].
    unfold erase; simpl. unfold emapE. by rewrite soup_fmap, (soup_update M i e e' Hi), HEi.
Qed.

Theorem pstep_iff p π p' : pstep p π p' ↔ pspec p π p'.
Proof.
  split.
  - intros (q & ev & q' & <- & Hst & <- & <-). by apply istep_pspec.
  - intros H. destruct (erase_surj p) as [q <-].
    destruct (pspec_lift q π p' H) as (ev & q' & Hst & Hπ & <-). by exists q, ev, q'.
Qed.

Theorem pstep_lift q π p' :
  pstep (erase q) π p' → ∃ ev q', istep q ev q' ∧ ev_plabel ev = π ∧ erase q' = p'.
Proof. intros H. apply pspec_lift. by apply pstep_iff. Qed.

Corollary istep_erase q ev q' : istep q ev q' → pstep (erase q) (ev_plabel ev) (erase q').
Proof. intros H. by exists q, ev, q'. Qed.

Corollary itstep_erase q ev q' : itstep q ev q' → preduction (erase q) (erase q').
Proof. intros [H Hτ]. unfold preduction. rewrite <-Hτ. by apply istep_erase. Qed.

Corollary preduction_lift q p' :
  preduction (erase q) p' → ∃ ev q', itstep q ev q' ∧ erase q' = p'.
Proof.
  intros H. destruct (pstep_lift q PTau p' H) as (ev & q' & Hst & Hπ & <-).
  by exists ev, q'.
Qed.

Corollary pred_star_lift q p' :
  pred_star (erase q) p' → ∃ q', itsteps q q' ∧ erase q' = p'.
Proof.
  intros H. remember (erase q) as p eqn:Hp. revert q Hp.
  induction H as [p|p p1 p2 Hst _ IH]; intros q ->.
  - by exists q.
  - destruct (preduction_lift q p1 Hst) as (ev & q1 & Hq & <-).
    destruct (IH q1 eq_refl) as (q2 & Hq2 & <-).
    exists q2. split; [|done]. eapply rtc_l; [by exists ev|done].
Qed.

(** Session-labelled steps come from P-Act-Session only. *)
Lemma pstep_sess_inv C E σ p' :
  pstep (C, E) (PSess σ) p' →
  ∃ E0 e e', E = E0 ⊎ {[+ e +]} ∧ tstep e (LSess σ) e' ∧ subjs σ ## C ∧
    p' = (C ∖ sentc σ, E0 ⊎ {[+ e' +]}).
Proof. rewrite pstep_iff. intros H. inversion H; simplify_eq. eauto 10. Qed.

(** ** Threads under a step *)

(** A thread that does not take part keeps its term, up to the renaming
    of a link. *)
Lemma istep_other q ev q' t e :
  istep q ev q' → t ∉ ev_parts ev → q.2 !! t = Some e →
  ∃ g, q'.2 !! t = Some (emap g e).
Proof.
  intros Hst Ht Hte. assert (q'.2 !! t = Some e → ∃ g, q'.2 !! t = Some (emap g e)) as Hid.
  { intros H. exists id. by rewrite emap_id. }
  destruct Hst; simpl in *.
  - apply Hid. rewrite lookup_insert_ne; set_solver.
  - apply Hid. rewrite lookup_insert_ne; set_solver.
  - apply Hid. rewrite lookup_insert_ne; set_solver.
  - apply Hid. rewrite lookup_insert_ne; [|intros ->; congruence].
    rewrite lookup_insert_ne; set_solver.
  - apply Hid. rewrite !lookup_insert_ne; set_solver.
  - apply Hid. rewrite !lookup_insert_ne; set_solver.
  - apply Hid. rewrite !lookup_insert_ne; set_solver.
  - exists (csub o1 o2). rewrite lookup_fmap, lookup_insert_ne by set_solver.
    by rewrite Hte.
  - apply Hid. rewrite lookup_insert_ne; set_solver.
Qed.

Lemma istep_parts_some q ev q' t : istep q ev q' → t ∈ ev_parts ev → is_Some (q.2 !! t).
Proof.
  destruct 1; simpl; intros Ht; rewrite ?elem_of_union, ?elem_of_singleton in Ht;
    destruct_or?; subst; eauto.
Qed.

Lemma istep_parts_nonempty q ev q' : istep q ev q' → ∃ t, t ∈ ev_parts ev.
Proof. destruct 1; simpl; exists i; set_solver. Qed.

(** A thread that takes part acts by a step of its term. An
    administrative actor takes part alone, and a link renames its
    continuation. *)
Lemma istep_actor q ev q' t e :
  istep q ev q' → t ∈ ev_parts ev → q.2 !! t = Some e →
  ∃ α e', tstep e α e' ∧ (ev_admin ev → ∃ g, q'.2 !! t = Some (emap g e')).
Proof.
  destruct 1; simpl; intros Ht Hte.
  all: set_unfold in Ht; destruct_or?; subst.
  all: repeat match goal with
    | H1 : ?M !! ?i = Some ?a, H2 : ?M !! ?i = Some ?b |- _ =>
        rewrite H1 in H2; injection H2 as <-
    end.
  all: eexists _, _; split; [eassumption|].
  all: intros Had; simpl in Had; try contradiction.
  - exists id. rewrite emap_id. by rewrite lookup_insert_eq.
  - exists id. rewrite emap_id. by rewrite lookup_insert_eq.
  - exists id. rewrite emap_id. by rewrite lookup_insert_eq.
  - exists id. rewrite emap_id. rewrite lookup_insert_ne by (intros ->; congruence).
    by rewrite lookup_insert_eq.
  - exists (csub o1 o2). by rewrite lookup_fmap, lookup_insert_eq.
Qed.
