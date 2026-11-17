(** * P is invariant under renaming channels (stage S4)

    The transposition a ↔ b of compat/Swap.v on configurations with
    thread identifiers ([qswap]) and on events ([evswap]). An
    instrumented step of a configuration is the renamed step of the
    renamed configuration ([istep_qswap]), the erasure commutes with the
    renaming ([erase_qswap]), and the external clauses of P move along
    it ([send_split_swap], [recv_ok_swap], [recv_env_swap],
    [recv_back_swap]). P is invariant ([Prel_swap]), an instance of
    [Prel_rename]. *)

From GV Require Export compat.Rename.
(* lang.ChannelSwap again, so that its [sren] shadows the one of types/Types.v *)
From GV Require Export lang.ChannelSwap.

Section qswap.
  Context (a b : chan).
  Local Abbreviation ow := (oswap a b).
  Local Abbreviation ew := (eswap a b).
  Local Abbreviation cw := (cswap a b).

  Definition qswap (q : config) : config := (gswap a b q.1, ew <$> q.2).

  Definition evswap (ev : event) : event :=
    match ev with
    | EvBeta i => EvBeta i
    | EvNew i ℓ c => EvNew i ℓ (cw c)
    | EvNewAt i κ o c => EvNewAt i κ (ow o) (cw c)
    | EvSpawn i j M => EvSpawn i j (set_map ow M)
    | EvMsg i j o M => EvMsg i j (ow o) (set_map ow M)
    | EvClose i j o => EvClose i j (ow o)
    | EvChoice i j o bb => EvChoice i j (ow o) bb
    | EvLink i o1 o2 => EvLink i (ow o1) (ow o2)
    | EvSess i σ => EvSess i (sren cw σ)
    end.

  Lemma erase_qswap q : erase (qswap q) = pswap a b (erase q).
  Proof. destruct q as [C M]. unfold erase, qswap, pswap. simpl. by rewrite soup_fmap. Qed.

  Lemma echans_soup_swap M : echans (soup (ew <$> M)) = gswap a b (echans (soup M)).
  Proof. rewrite soup_fmap. apply echans_eswapE. Qed.

  Lemma ev_tau_swap ev : ev_tau (evswap ev) ↔ ev_tau ev.
  Proof. unfold ev_tau. destruct ev as [| | | | | | | |i []]; done. Qed.

  Lemma ev_cost_swap κ ev : ev_cost κ (evswap ev) = ev_cost κ ev.
  Proof. destruct ev as [| | | | | | | |i []]; done. Qed.

  Lemma sren_upair o1 o2 : sren cw (SLink ({[o1]} ∪ {[o2]})) = SLink ({[ow o1]} ∪ {[ow o2]}).
  Proof. simpl. f_equal. apply set_map_upair. Qed.

  Lemma istep_qswap q ev q' : istep q ev q' → istep (qswap q) (evswap ev) (qswap q').
  Proof.
    destruct 1 as [C M i e e' Hi Hst|C M i e ℓ c e' Hi Hst HC Hc|C M i e κ o c e' Hi Hst HC Hc
      |C M i j e Mv v e' Hi Hst Hj
      |C M i j o Mv v e e' f f' Hij Hi Hj He Hf|C M i j o e e' f f' Hij Hi Hj He Hf HC
      |C M i j o bb e e' f f' Hij Hi Hj He Hf|C M i e o1 o2 e' Hi Hst HC
      |C M i e σ e' Hi Hst HC]; unfold qswap; simpl; rewrite ?fmap_insert.
    - eapply p_act_beta; [by rewrite lookup_fmap, Hi|by apply (tstep_eswap a b) in Hst].
    - rewrite gswap_union, gswap_singleton.
      eapply p_act_new; [by rewrite lookup_fmap, Hi|by apply (tstep_eswap a b) in Hst
        |by rewrite elem_of_gswap|by rewrite echans_soup_swap, elem_of_gswap].
    - rewrite gswap_union, gswap_singleton.
      eapply p_act_new_at; [by rewrite lookup_fmap, Hi|by apply (tstep_eswap a b) in Hst
        |by rewrite elem_of_gswap|by rewrite echans_soup_swap, elem_of_gswap].
    - eapply p_act_spawn; [by rewrite lookup_fmap, Hi|by apply (tstep_eswap a b) in Hst
        |by rewrite lookup_fmap, Hj].
    - eapply p_act_msg; [done|by rewrite lookup_fmap, Hi|by rewrite lookup_fmap, Hj
        |by apply (tstep_eswap a b) in He|].
      apply (tstep_eswap a b) in Hf. simpl in Hf. by rewrite cmap_edual in Hf.
    - rewrite gswap_difference, gswap_singleton, <-(ech_cmap cw).
      eapply p_act_close; [done|by rewrite lookup_fmap, Hi|by rewrite lookup_fmap, Hj
        |by apply (tstep_eswap a b) in He| |by rewrite ech_cmap, elem_of_gswap].
      apply (tstep_eswap a b) in Hf. simpl in Hf. by rewrite cmap_edual in Hf.
    - eapply p_act_choice; [done|by rewrite lookup_fmap, Hi|by rewrite lookup_fmap, Hj
        |by apply (tstep_eswap a b) in He|].
      apply (tstep_eswap a b) in Hf. simpl in Hf. by rewrite cmap_edual in Hf.
    - rewrite gswap_difference, gswap_singleton, <-(ech_cmap cw).
      match goal with |- istep _ _ (_, ?X) =>
        replace X with (emap (csub (ow o1) (ow o2)) <$> (<[i := ew e']> (ew <$> M))) end.
      + eapply p_act_link; [by rewrite lookup_fmap, Hi| |by rewrite ech_cmap, elem_of_gswap].
        apply (tstep_eswap a b) in Hst. simpl in Hst. by rewrite set_map_upair in Hst.
      + rewrite !fmap_insert, eswap_csub, <-!map_fmap_compose. f_equal.
        apply map_fmap_ext. intros k x _. simpl. symmetry. apply eswap_csub.
    - rewrite gswap_difference, <-sentc_sren.
      eapply p_act_session; [by rewrite lookup_fmap, Hi|by apply (tstep_eswap a b) in Hst|].
      rewrite subjs_sren. by apply gswap_disjoint_iff.
  Qed.

  Lemma qswap_involutive q : qswap (qswap q) = q.
  Proof.
    destruct q as [C M]. unfold qswap. simpl. rewrite gswap_involutive, <-map_fmap_compose.
    f_equal. etrans; [|apply map_fmap_id]. apply map_fmap_ext. intros. apply eswap_involutive.
  Qed.

  Lemma evswap_involutive ev : evswap (evswap ev) = ev.
  Proof.
    destruct ev as [| | | | | | | |i σ]; simpl; rewrite ?oswap_involutive, ?cswap_involutive,
      ?set_map_oswap_inv; try done.
    destruct σ; simpl; rewrite ?oswap_involutive, ?set_map_oswap_inv, ?eswap_involutive; done.
  Qed.

  (** A step of the renamed configuration is the renamed step. *)
  Lemma istep_unswap q ev q' :
    istep (qswap q) ev q' → istep q (evswap ev) (qswap q').
  Proof.
    intros H. apply istep_qswap in H. by rewrite qswap_involutive in H.
  Qed.
End qswap.

(** ** The external clauses along a transposition *)

Section clauses.
  Context (a b : chan).
  Local Abbreviation ow := (oswap a b).
  Local Abbreviation sw := (sswap a b).

  Lemma dom_swap_elem Θ o : ow o ∈ dom (sw Θ) ↔ o ∈ dom Θ.
  Proof. rewrite !elem_of_dom. by rewrite sswap_lookup. Qed.

  Lemma dom_swap_elem' Θ o : o ∈ dom (sw Θ) ↔ ow o ∈ dom Θ.
  Proof. rewrite !elem_of_dom. by rewrite sswap_lookup'. Qed.

  Lemma sdual_refl_swap S S' : sdual S S' → sdual S S'.
  Proof. done. Qed.

  Lemma send_split_swap Σ Σe Θe : send_split Σ Σe Θe → send_split (sw Σ) (sw Σe) (sw Θe).
  Proof.
    intros (H1 & H2 & H3). split_and!.
    - intros o Ho. apply dom_swap_elem' in Ho. destruct (H1 _ Ho) as [A B].
      rewrite !dom_swap_elem', cmap_edual. done.
    - intros o. rewrite !dom_swap_elem', cmap_edual. apply H2.
    - intros o S y Ho. rewrite sswap_lookup' in Ho. destruct (H3 _ _ _ Ho) as (S' & A & B).
      exists S'. split; [|done]. by rewrite <-sswap_union, sswap_lookup', cmap_edual.
  Qed.

  Lemma recv_ok_swap Σ Θ2 : recv_ok Σ Θ2 → recv_ok (sw Σ) (sw Θ2).
  Proof.
    intros [H1 H2]. split.
    - intros o Ho. rewrite dom_swap_elem' in Ho |- *. by apply H1.
    - intros o S y S' y' Ho Hp. rewrite sswap_lookup' in Ho.
      rewrite <-sswap_union, sswap_lookup', cmap_edual in Hp. by apply (H2 (ow o)).
  Qed.

  Lemma recv_env_swap Σ Θ2 : recv_env (sw Σ) (sw Θ2) = sw (recv_env Σ Θ2).
  Proof.
    apply map_eq. intros o. unfold recv_env. rewrite sswap_lookup'.
    rewrite !lookup_union, !map_lookup_filter, !sswap_lookup'.
    destruct (Σ !! ow o), (Θ2 !! ow o); simpl; try done.
    all: repeat (case_guard; simpl); try done; exfalso.
    all: repeat match goal with
      | H : context [dom (sw _)] |- _ => setoid_rewrite dom_swap_elem' in H
      end; rewrite ?cmap_edual in *; tauto.
  Qed.

  Lemma recv_back_swap Σ Θ2 : recv_back (sw Σ) (sw Θ2) = gswap a b (recv_back Σ Θ2).
  Proof.
    unfold recv_back. rewrite <-set_map_ech_oswap. f_equal.
    apply set_eq. intros o. rewrite elem_of_filter, !elem_of_map. split.
    - intros [Hp Ho]. exists (ow o). rewrite oswap_involutive. split; [done|].
      apply elem_of_filter. rewrite dom_swap_elem' in Ho. split; [|done].
      rewrite !dom_swap_elem', !cmap_edual in Hp. done.
    - intros (o' & -> & Ho'). apply elem_of_filter in Ho' as [Hp Ho'].
      rewrite !dom_swap_elem', !cmap_edual, !oswap_involutive. done.
  Qed.

  Lemma chans_of_swap Σ : chans_of (sw Σ) = gswap a b (chans_of Σ).
  Proof. unfold chans_of. by rewrite sswap_dom, set_map_ech_oswap. Qed.
End clauses.

(** ** Readiness of processes along a transposition *)

Section readiness.
  Context (a b : chan).
  Local Abbreviation ow := (oswap a b).
  Local Abbreviation sw := (sswap a b).
  Local Abbreviation pw := (pswap a b).

  Lemma pstep_unswap p π p' : pstep (pw p) π p' → pstep p (pren (cswap a b) π) (pw p').
  Proof. intros H. apply (pstep_pswap a b) in H. by rewrite pswap_involutive in H. Qed.

  Lemma pirred_unswap p : pirred (pw p) → pirred p.
  Proof. intros H π p' Hs. by apply (H _ _ (pstep_pswap a b _ _ _ Hs)). Qed.

  Lemma offered_p_swap Σ p o : offered_p (sw Σ) (pw p) o ↔ offered_p Σ p (ow o).
  Proof.
    unfold offered_p. rewrite dom_swap_elem'. split.
    - intros [Hd (σ & p' & Hs & Ho)]. split; [done|].
      apply pstep_unswap in Hs. exists (sren (cswap a b) σ), (pw p'). split; [done|].
      rewrite sends_sren. by apply elem_of_map_2.
    - intros [Hd (σ & p' & Hs & Ho)]. split; [done|].
      apply (pstep_pswap a b) in Hs. exists (sren (cswap a b) σ), (pw p'). split; [done|].
      rewrite sends_sren. apply elem_of_map. exists (ow o). by rewrite oswap_involutive.
  Qed.

  Lemma ready_p_swap W Σ p : ready _ W(Σ, p) → ready _ W(sw Σ, pw p).
  Proof.
    intros H Hs. assert (stable_p p) as Hs'.
    { intros p' Hr. apply (Hs (pw p')). by apply preduction_pswap. }
    destruct (H Hs') as [(os & p' & Hl)|[H1 H2]]; [left|right].
    - apply (pstep_pswap a b) in Hl. by eexists _, _.
    - split.
      + intros Hno. apply terminated_pswap, H1. intros o Ho. apply (Hno (ow o)), offered_p_swap.
        by rewrite oswap_involutive.
      + intros o S x Hx Hno. rewrite sswap_lookup' in Hx.
        destruct (H2 _ _ _ Hx) as (o' & S' & x' & Ho' & Hx' & Hlt).
        { intros Hoff. apply Hno, offered_p_swap. done. }
        exists (ow o'), S', x'. split_and!; [|by rewrite sswap_lookup|done].
        apply offered_p_swap. by rewrite oswap_involutive.
  Qed.
End readiness.

(** ** P along a transposition

    A transposition commutes with duality and is injective, so P is
    invariant by the clause (rename) ([Prel_rename]). *)

Lemma pswap_pmap a b p : pswap a b p = pmap (oswap a b) p.
Proof.
  destruct p as [C E]. unfold pswap, pmap, gswap. simpl. done.
Qed.

Lemma pren_ok_swap a b Σ p : pren_ok (oswap a b) Σ p.
Proof. split; [intros o; apply cmap_edual|]. intros o1 o2 _ _. apply oswap_inj. Qed.

Lemma Prel_swap κ a b n W Σ T p : Prel κ n W Σ T p ↔ Prel κ n W (sswap a b Σ) T (pswap a b p).
Proof.
  assert (∀ Σ p, Prel κ n W Σ T p → Prel κ n W (sswap a b Σ) T (pswap a b p)) as H1.
  { intros Σ0 p0 H. unfold sswap. rewrite <-kren_kmap by apply _. rewrite pswap_pmap.
    by apply Prel_rename; [apply pren_ok_swap|]. }
  split; [apply H1|]. intros H.
  rewrite <-(sswap_inv a b Σ), <-(pswap_involutive a b p). by apply H1.
Qed.

(** ** The link substitution is no bijection

    [csub o1 o2] sends o1‾ and o2 to o2. A thread that holds o1‾ may
    still mention o2 in code it never runs, so the renaming of the other
    component at a link is not the restriction of a bijection of ends to
    the ends that component mentions (docs/redesign/progress.md, S4.10). *)
Lemma csub_fuses o1 o2 : o2 ≠ o1 → o2 ≠ o1‾ → csub o1 o2 o1‾ = csub o1 o2 o2 ∧ o1‾ ≠ o2.
Proof.
  intros H1 H2. unfold csub. rewrite decide_True by done.
  rewrite decide_False by done. rewrite decide_False by done. by split.
Qed.
