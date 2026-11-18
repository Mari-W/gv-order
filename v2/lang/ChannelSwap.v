(** * Channel renamings in the semantics (stage S1)

    A renaming h of channel names acts on ends by [cmap h], which keeps
    the sign of each end, and on terms by the one renaming [emap]. Thread
    steps are equivariant under every h ([tstep_cmap]). A transposition of
    two names maps process steps to process steps ([pstep_pswap]) and
    preserves safety ([safe_pswap_iff]). *)

From stdpp Require Import relations.
From GV Require Export lang.Safety.

(** ** Renaming of labels *)

Definition sren (h : chan → chan) (σ : slabel) : slabel :=
  match σ with
  | SSend o v => SSend (cmap h o) (emap (cmap h) v)
  | SRecv o v => SRecv (cmap h o) (emap (cmap h) v)
  | SClose o => SClose (cmap h o)
  | SSel o i => SSel (cmap h o) i
  | SBra o i => SBra (cmap h o) i
  | SLink os => SLink (set_map (cmap h) os)
  end.

Definition lren (h : chan → chan) (α : tlabel) : tlabel :=
  match α with
  | LBeta => LBeta
  | LNew ℓ c => LNew ℓ (h c)
  | LNewAt κ o c => LNewAt κ (cmap h o) (h c)
  | LSpawn v => LSpawn (emap (cmap h) v)
  | LSess σ => LSess (sren h σ)
  end.

Definition pren (h : chan → chan) (π : plabel) : plabel :=
  match π with PTau => PTau | PSess σ => PSess (sren h σ) end.

Lemma set_map_upair (g : cend → cend) o1 o2 :
  set_map g ({[o1; o2]} : gset cend) = ({[g o1; g o2]} : gset cend).
Proof. by rewrite set_map_union_L, !set_map_singleton_L. Qed.

(** ** Thread steps are equivariant *)

Lemma head_step_cmap h e α e' :
  head_step e α e' → head_step (emap (cmap h) e) (lren h α) (emap (cmap h) e').
Proof.
  destruct 1; simpl; rewrite ?emap_subst1, ?emap_subst2, ?set_map_upair, <-?fends_emap.
  all: try (constructor; by rewrite ?is_val_emap).
  all: try (match goal with |- context [inj_of ?i] => destruct i; constructor end).
Qed.

Lemma tstep_cmap h e α e' :
  tstep e α e' → tstep (emap (cmap h) e) (lren h α) (emap (cmap h) e').
Proof.
  induction 1 as [e α e' Hh|f e α e' Hf Hs IH].
  - apply tstep_head. by apply head_step_cmap.
  - assert (∀ e0, emap (cmap h) (fill_frame f e0) =
                  fill_frame (match f with
                    | FAppL e2 => FAppL (emap (cmap h) e2) | FAppR v => FAppR (emap (cmap h) v)
                    | FPairL e2 => FPairL (emap (cmap h) e2) | FPairR v => FPairR (emap (cmap h) v)
                    | FLetU e2 => FLetU (emap (cmap h) e2) | FLetP e2 => FLetP (emap (cmap h) e2)
                    | FInj1 => FInj1 | FInj2 => FInj2
                    | FCase e1 e2 => FCase (emap (cmap h) e1) (emap (cmap h) e2)
                    | FOp k => FOp k end) (emap (cmap h) e0)) as Hfill
      by (intros; destruct f; done).
    rewrite !Hfill. apply t_act_ctx; [|done].
    destruct f; simpl in *; rewrite ?is_val_emap; done.
Qed.

(** ** Transpositions *)

Definition cswap (a b c : chan) : chan :=
  if decide (c = a) then b else if decide (c = b) then a else c.

Lemma cswap_involutive a b c : cswap a b (cswap a b c) = c.
Proof. unfold cswap. repeat case_decide; congruence. Qed.
Lemma cswap_l a b : cswap a b a = b.
Proof. unfold cswap. repeat case_decide; congruence. Qed.
Lemma cswap_r a b : cswap a b b = a.
Proof. unfold cswap. repeat case_decide; congruence. Qed.
Lemma cswap_ne a b c : c ≠ a → c ≠ b → cswap a b c = c.
Proof. unfold cswap. repeat case_decide; congruence. Qed.
Lemma cswap_inj a b c c' : cswap a b c = cswap a b c' → c = c'.
Proof. unfold cswap. repeat case_decide; congruence. Qed.

Abbreviation oswap a b := (cmap (cswap a b)).
Abbreviation eswap a b := (emap (cmap (cswap a b))).

Lemma oswap_involutive a b o : oswap a b (oswap a b o) = o.
Proof. destruct o; simpl; by rewrite cswap_involutive. Qed.
Lemma oswap_inj a b o o' : oswap a b o = oswap a b o' → o = o'.
Proof. intros H. by rewrite <-(oswap_involutive a b o), H, oswap_involutive. Qed.

Lemma eswap_involutive a b e : eswap a b (eswap a b e) = e.
Proof.
  rewrite emap_emap. etrans; [|apply emap_id]. apply emap_ext.
  intros o. apply oswap_involutive.
Qed.

Definition gswap (a b : chan) (C : gset chan) : gset chan := set_map (cswap a b) C.

Lemma elem_of_gswap a b c C : cswap a b c ∈ gswap a b C ↔ c ∈ C.
Proof.
  unfold gswap. rewrite elem_of_map. split.
  - intros (c' & Heq & Hc'). apply cswap_inj in Heq. by subst.
  - intros Hc. by exists c.
Qed.

Lemma elem_of_gswap' a b c C : c ∈ gswap a b C ↔ cswap a b c ∈ C.
Proof.
  split.
  - intros (c1 & -> & Hc1)%elem_of_map. by rewrite cswap_involutive.
  - intros Hc. rewrite <-(cswap_involutive a b c). by apply elem_of_gswap.
Qed.

Lemma gswap_involutive a b C : gswap a b (gswap a b C) = C.
Proof. apply set_eq. intros c. by rewrite !elem_of_gswap', cswap_involutive. Qed.
Lemma gswap_union a b C1 C2 : gswap a b (C1 ∪ C2) = gswap a b C1 ∪ gswap a b C2.
Proof. unfold gswap. apply set_map_union_L. Qed.
Lemma gswap_singleton a b c : gswap a b ({[c]} : gset chan) = {[cswap a b c]}.
Proof. unfold gswap. apply set_map_singleton_L. Qed.
Lemma gswap_empty a b : gswap a b (∅ : gset chan) = ∅.
Proof. unfold gswap. apply set_eq; intros c. set_solver. Qed.
Lemma gswap_difference a b C1 C2 : gswap a b (C1 ∖ C2) = gswap a b C1 ∖ gswap a b C2.
Proof.
  apply set_eq; intros c. by rewrite elem_of_difference, !elem_of_gswap', elem_of_difference.
Qed.
Lemma gswap_disjoint_iff a b C1 C2 : gswap a b C1 ## gswap a b C2 ↔ C1 ## C2.
Proof.
  split; intros Hd; apply elem_of_disjoint; intros c H1 H2.
  - assert (cswap a b c ∈ gswap a b C1) by (by apply elem_of_gswap).
    assert (cswap a b c ∈ gswap a b C2) by (by apply elem_of_gswap).
    set_solver.
  - apply elem_of_gswap' in H1. apply elem_of_gswap' in H2. set_solver.
Qed.

Lemma set_map_ech_oswap a b (M : gset cend) :
  set_map ech (set_map (oswap a b) M : gset cend) = gswap a b (set_map ech M).
Proof.
  apply set_eq. intros c. unfold gswap. rewrite !elem_of_map. split.
  - intros (o' & -> & (o & -> & Ho)%elem_of_map). exists (ech o).
    split; [apply ech_cmap|]. apply elem_of_map. eauto.
  - intros (c' & -> & (o & -> & Ho)%elem_of_map). exists (oswap a b o).
    split; [symmetry; apply ech_cmap|]. apply elem_of_map. eauto.
Qed.

Lemma fchans_eswap a b e : fchans (eswap a b e) = gswap a b (fchans e).
Proof. unfold fchans. rewrite fends_emap. apply set_map_ech_oswap. Qed.

Lemma subjs_sren a b σ : subjs (sren (cswap a b) σ) = gswap a b (subjs σ).
Proof.
  destruct σ; simpl; rewrite ?ech_cmap, ?gswap_singleton; try done.
  apply set_map_ech_oswap.
Qed.

Lemma sentc_sren a b σ : sentc (sren (cswap a b) σ) = gswap a b (sentc σ).
Proof. destruct σ; simpl; rewrite ?gswap_empty; try done. apply fchans_eswap. Qed.

(** The link substitution commutes with a transposition. *)
Lemma oswap_csub a b o1 o2 o :
  oswap a b (csub o1 o2 o) = csub (oswap a b o1) (oswap a b o2) (oswap a b o).
Proof.
  unfold csub. rewrite <-!cmap_edual.
  repeat case_decide; subst; try done; exfalso.
  all: match goal with H : cmap _ _ ≠ cmap _ _ |- _ => by apply H end
     || (match goal with H : cmap ?h ?x = cmap ?h ?y |- _ =>
           apply (oswap_inj a b) in H; subst; congruence end).
Qed.

Lemma eswap_csub a b o1 o2 e :
  eswap a b (emap (csub o1 o2) e) = emap (csub (oswap a b o1) (oswap a b o2)) (eswap a b e).
Proof.
  rewrite !emap_emap. apply emap_ext. intros o. apply oswap_csub.
Qed.

(** ** Soups and processes *)

Definition pswap (a b : chan) (p : proc) : proc := (gswap a b p.1, emapE (oswap a b) p.2).

Lemma emapE_empty g : emapE g ∅ = ∅.
Proof. apply gmultiset_map_empty. Qed.

Lemma emapE_emapE g h E : emapE g (emapE h E) = emapE (g ∘ h) E.
Proof.
  induction E as [|e E IH] using gmultiset_ind; [by rewrite !emapE_empty|].
  by rewrite !emapE_disj_union, !emapE_singleton, IH, emap_emap.
Qed.

Lemma emapE_id E : emapE id E = E.
Proof.
  induction E as [|e E IH] using gmultiset_ind; [by rewrite !emapE_empty|].
  by rewrite !emapE_disj_union, !emapE_singleton, IH, emap_id.
Qed.

Lemma emapE_ext g h E : (∀ o, g o = h o) → emapE g E = emapE h E.
Proof.
  intros Hgh. induction E as [|e E IH] using gmultiset_ind; [by rewrite !emapE_empty|].
  by rewrite !emapE_disj_union, !emapE_singleton, IH, (emap_ext g h).
Qed.

Lemma echans_eswapE a b E : echans (emapE (oswap a b) E) = gswap a b (echans E).
Proof.
  induction E as [|e E IH] using gmultiset_ind.
  - by rewrite emapE_empty, !echans_empty, gswap_empty.
  - rewrite emapE_disj_union, emapE_singleton, !echans_disj_union, !echans_singleton, IH.
    by rewrite (fchans_eswap a b e), gswap_union.
Qed.

Lemma pswap_involutive a b p : pswap a b (pswap a b p) = p.
Proof.
  destruct p as [C E]. unfold pswap; simpl. rewrite gswap_involutive, emapE_emapE.
  f_equal. etrans; [|apply emapE_id]. apply emapE_ext. apply oswap_involutive.
Qed.

(** ** Process steps are equivariant under a transposition *)

Lemma tstep_eswap a b e α e' :
  tstep e α e' → tstep (eswap a b e) (lren (cswap a b) α) (eswap a b e').
Proof. apply tstep_cmap. Qed.

Lemma pspec_pswap a b p π p' :
  pspec p π p' → pspec (pswap a b p) (pren (cswap a b) π) (pswap a b p').
Proof.
  destruct 1; unfold pswap; simpl; rewrite ?emapE_disj_union, ?emapE_singleton.
  - rewrite gswap_difference, <-sentc_sren. apply ps_session.
    + by apply (tstep_eswap a b) in H.
    + rewrite subjs_sren. by apply gswap_disjoint_iff.
  - apply ps_beta. by apply (tstep_eswap a b) in H.
  - rewrite gswap_union, gswap_singleton. eapply ps_new.
    + by apply (tstep_eswap a b) in H.
    + by rewrite elem_of_gswap.
    + rewrite echans_eswapE. by rewrite elem_of_gswap.
    + rewrite fchans_eswap. by rewrite elem_of_gswap.
  - rewrite gswap_union, gswap_singleton. eapply ps_new_at.
    + by apply (tstep_eswap a b) in H.
    + by rewrite elem_of_gswap.
    + rewrite echans_eswapE. by rewrite elem_of_gswap.
    + rewrite fchans_eswap. by rewrite elem_of_gswap.
  - eapply ps_spawn. by apply (tstep_eswap a b) in H.
  - eapply ps_msg.
    + by apply (tstep_eswap a b) in H.
    + apply (tstep_eswap a b) in H0. simpl in H0. by rewrite cmap_edual in H0.
  - rewrite gswap_difference, gswap_singleton, <-(ech_cmap (cswap a b)). eapply ps_close.
    + by apply (tstep_eswap a b) in H.
    + apply (tstep_eswap a b) in H0. simpl in H0. by rewrite cmap_edual in H0.
    + rewrite ech_cmap. by rewrite elem_of_gswap.
  - eapply ps_choice.
    + by apply (tstep_eswap a b) in H.
    + apply (tstep_eswap a b) in H0. simpl in H0. by rewrite cmap_edual in H0.
  - rewrite gswap_difference, gswap_singleton, emapE_emapE, eswap_csub.
    rewrite (emapE_ext (oswap a b ∘ csub o1 o2)
               (csub (oswap a b o1) (oswap a b o2) ∘ oswap a b)) by (intros; apply oswap_csub).
    rewrite <-emapE_emapE.
    rewrite <-(emapE_singleton (csub (oswap a b o1) (oswap a b o2)) (eswap a b e')),
      <-emapE_disj_union.
    rewrite <-(ech_cmap (cswap a b) o1). eapply ps_link.
    + apply (tstep_eswap a b) in H. simpl in H. by rewrite set_map_upair in H.
    + rewrite ech_cmap. by rewrite elem_of_gswap.
Qed.

Lemma pstep_pswap a b p π p' :
  pstep p π p' → pstep (pswap a b p) (pren (cswap a b) π) (pswap a b p').
Proof. rewrite !pstep_iff. apply pspec_pswap. Qed.

Lemma preduction_pswap a b p q : preduction p q → preduction (pswap a b p) (pswap a b q).
Proof. intros H. exact (pstep_pswap a b _ _ _ H). Qed.

(** ** Safety is equivariant *)

Lemma terminated_pswap a b p : terminated p → terminated (pswap a b p).
Proof.
  intros (v & E & -> & Hv & HE). unfold pswap; simpl.
  assert (emapE (oswap a b) E = E) as HEq.
  { clear -HE. induction E as [|e E IH] using gmultiset_ind; [by rewrite emapE_empty|].
    rewrite emapE_disj_union, emapE_singleton, IH by multiset_solver.
    by rewrite (HE e) by multiset_solver. }
  exists (eswap a b v), E. split_and!; [|by rewrite is_val_emap|done].
  by rewrite gswap_empty, emapE_disj_union, emapE_singleton, HEq.
Qed.

Lemma safe_pswap a b p : safe p → safe (pswap a b p).
Proof.
  intros [Ht|[q Hq]]; [left; by apply terminated_pswap|right].
  exists (pswap a b q). by apply preduction_pswap.
Qed.

Lemma safe_pswap_iff a b p : safe (pswap a b p) ↔ safe p.
Proof.
  split; [|apply safe_pswap].
  intros H. rewrite <-(pswap_involutive a b p). by apply safe_pswap.
Qed.
