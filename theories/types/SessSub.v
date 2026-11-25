(** * Session subtyping against the type operations

    S ⊑ S′ ([ssub], types/Types.v) is ≈ except that a received payload
    may fall in credit and a sent payload may rise. This file shows that
    ⊑ contains ≈, absorbs ≈ on both sides, turns around under duality,
    collapses to ≈ at the annotations of N = ∞ and is closed under
    contractive instances. *)

From GV Require Export types.Contractive.

(** ** ⊑ contains ≈ *)

Lemma sequiv_ssub s r : sequiv s r → ssub s r.
Proof.
  intros H. apply (ssub_coind sequiv); [|done]. clear.
  intros s r H. apply sequiv_hd in H. unfold eq_step, sub_step in *.
  hd_cases s; hd_cases r; try done.
  all: destruct_and?; subst; split_and?; auto using teq_crT, teq_sym.
Qed.

Lemma ssub_sequiv_l s s' r : sequiv s s' → ssub s' r → ssub s r.
Proof. intros H1 H2. eapply ssub_trans; [apply sequiv_ssub, H1|exact H2]. Qed.

Lemma ssub_sequiv_r s r r' : ssub s r → sequiv r r' → ssub s r'.
Proof. intros H1 H2. eapply ssub_trans; [exact H1|apply sequiv_ssub, H2]. Qed.

(** ** Duality turns ⊑ around *)

Lemma ssub_dual s r : ssub s r → ssub (dual r) (dual s).
Proof.
  intros H. apply (ssub_coind (λ x y, ∃ s r, x = dual r ∧ y = dual s ∧ ssub s r)); [|eauto].
  clear. intros x y (s & r & -> & -> & H). apply ssub_hd in H.
  unfold sub_step in *. rewrite !hd_dual.
  hd_cases s; hd_cases r; simpl in *; try done; try congruence.
  all: destruct_and?; subst; split_and?; eauto.
Qed.

(** ** At N = ∞, ⊑ is ≈ *)

Lemma crT_df (ρ : sty → sty → Prop) T : ∀ U,
  (∀ s r, sequiv s r → ρ (sty_df s) (sty_df r)) → crT T U → eqT ρ (ty_df T) (ty_df U).
Proof.
  induction T; intros [] Hρ H; try (exact (eqT_df sequiv ρ _ _ Hρ H)); simpl in *; try done.
  all: destruct_and?; subst; split_and?; eauto; by apply (eqT_df sequiv ρ).
Qed.

Lemma ssub_df s r : ssub s r → sequiv (sty_df s) (sty_df r).
Proof.
  intros H.
  apply (sequiv_coind (λ x y, ∃ s r, x = sty_df s ∧ y = sty_df r ∧ (ssub s r ∨ ssub r s)));
    [|eauto 10].
  clear. intros x y (s & r & -> & -> & H).
  set (τ := λ x y, ∃ s r, x = sty_df s ∧ y = sty_df r ∧ (ssub s r ∨ ssub r s)).
  assert (Hτ : ∀ a b, sequiv a b → τ (sty_df a) (sty_df b))
    by (intros a b Hab; exists a, b; split_and!; [done|done|left; by apply sequiv_ssub]).
  assert (Hsym : ∀ a b, τ a b → τ b a)
    by (intros a b (a0 & b0 & -> & -> & Hab); exists b0, a0; split_and!; [done|done|tauto]).
  unfold eq_step. rewrite !hd_df.
  destruct H as [H|H]; apply ssub_hd in H; unfold sub_step in H;
    hd_cases s; hd_cases r; simpl in *; try done.
  all: destruct_and?; subst; split_and?; try done.
  all: try (by apply (crT_df τ)).
  all: try (apply (eqT_sym τ); [exact Hsym|by apply (crT_df τ)]).
  all: try (exists s', s'0; split_and!; [done|done|tauto]).
  all: try (exists s'0, s'; split_and!; [done|done|tauto]).
  all: try (eexists _, _; split_and!; [reflexivity|reflexivity|tauto]).
Qed.

(** ** ⊑ through views of heads *)

Definition sub_view (τ : sty → sty → Prop) (v w : hview) : Prop :=
  match v, w with
  | HSkip, HSkip | HEnd, HEnd => True
  | HRcv m T s', HRcv m' U r' => m = m' ∧ crT T U ∧ τ s' r'
  | HSnd m T s', HSnd m' U r' => m = m' ∧ crT U T ∧ τ s' r'
  | HVar a s', HVar a' r' | HVarD a s', HVarD a' r' => a = a' ∧ τ s' r'
  | HPlus s1 s2, HPlus r1 r2 | HWith s1 s2, HWith r1 r2 => τ s1 r1 ∧ τ s2 r2
  | HStuck u, HStuck v => u = v
  | _, _ => False
  end.

Lemma sub_step_view τ s r : sub_step τ s r = sub_view τ (hd s) (hd r).
Proof. done. Qed.

Lemma sub_view_mono τ τ' v w : (∀ a b, τ a b → τ' a b) → sub_view τ v w → sub_view τ' v w.
Proof. intros Hτ. destruct v, w; simpl; try done; intuition eauto. Qed.

Lemma sub_view_refl τ v : (∀ s, τ s s) → sub_view τ v v.
Proof. intros Hτ. destruct v; simpl; try done; split_and?; auto using crT_refl. Qed.

Definition uptoS (τ : sty → sty → Prop) (a b : sty) : Prop :=
  ssub a b ∨ ∃ a' b', sequiv a a' ∧ τ a' b' ∧ sequiv b' b.

Lemma uptoS_refl τ s : uptoS τ s s.
Proof. left. apply ssub_refl. Qed.

Lemma uptoS_in τ s r : τ s r → uptoS τ s r.
Proof. intros H. right. exists s, r. split_and!; auto using sequiv_refl. Qed.

Lemma uptoS_equiv τ s s' r' r : sequiv s s' → τ s' r' → sequiv r' r → uptoS τ s r.
Proof. intros. right. eauto. Qed.

Lemma uptoS_comp τ x y w z : sequiv x y → uptoS τ y w → sequiv w z → uptoS τ x z.
Proof.
  intros H1 [H2|(y' & w' & G1 & G2 & G3)] H3.
  - left. eapply ssub_sequiv_l; [exact H1|]. by eapply ssub_sequiv_r.
  - right. exists y', w'. split_and!; [by eapply sequiv_trans|done|by eapply sequiv_trans].
Qed.

(** ≈ on both sides of a [uptoS] pair stays in [uptoS]. *)
Lemma sub_view_upto_comp τ v1 v2 v3 v4 :
  eq_view sequiv v1 v2 → sub_view (uptoS τ) v2 v3 → eq_view sequiv v3 v4 → sub_view (uptoS τ) v1 v4.
Proof.
  intros H1 H2 H3.
  destruct v1, v2; try done; destruct v3; try done; destruct v4; try done; simpl in *.
  all: destruct_and?; subst; split_and?; try done.
  all: try (eapply uptoS_comp; eauto).
  all: try (eapply crT_trans; [apply teq_crT; eassumption|];
            eapply crT_trans; [eassumption|apply teq_crT; eassumption]).
  all: try (eapply crT_trans; [apply teq_crT, teq_sym; eassumption|];
            eapply crT_trans; [eassumption|apply teq_crT, teq_sym; eassumption]).
Qed.

Lemma ssub_upto τ : (∀ s r, τ s r → sub_step (uptoS τ) s r) → ∀ s r, τ s r → ssub s r.
Proof.
  intros Hτ s r H. apply (ssub_coind (uptoS τ)); [|by apply uptoS_in].
  intros a b [Hab|(a' & b' & H1 & H2 & H3)].
  - eapply sub_step_mono; [|apply ssub_hd, Hab]. intros; by left.
  - rewrite sub_step_view. eapply sub_view_upto_comp;
      [rewrite <-eq_step_view; apply (sequiv_hd _ _ H1)|apply (Hτ _ _ H2)
      |rewrite <-eq_step_view; apply (sequiv_hd _ _ H3)].
Qed.

Lemma cong_contS (τ : sty → sty → Prop) r r' b b' : scontr r → scontr r' → scontr b → scontr b' →
  τ (SSeq r b) (SSeq r' b') → uptoS τ (sseq' r b) (sseq' r' b').
Proof. intros. eapply uptoS_equiv; [apply sseq'_sequiv|done|apply sequiv_sym, sseq'_sequiv]; done. Qed.

(** ** ⊑ is closed under contractive instances *)

Section ssub_sinst.
  Context (σ : nat → sty) (Hσ : ∀ a, scontr (σ a)).

  Definition τS (x y : sty) : Prop :=
    ∃ u s r, scontr u ∧ scontr s ∧ scontr r ∧ ssub s r ∧
      x = SSeq u (sinst σ s) ∧ y = SSeq u (sinst σ r).

  Lemma HscS t : scontr t → scontr (sinst σ t).
  Proof. intros. by apply scontr_sinst. Qed.

  Lemma τS_base s r : scontr s → scontr r → ssub s r → uptoS τS (sinst σ s) (sinst σ r).
  Proof.
    intros Hs Hr H. eapply uptoS_equiv; [apply sequiv_sym, seq_skip_l, HscS, Hs| |apply seq_skip_l, HscS, Hr].
    exists SSkip, s, r. by split_and!.
  Qed.

  Lemma crT_sinst T : ∀ U, tcontr T → tcontr U → crT T U → crT (sinst_ty σ T) (sinst_ty σ U).
  Proof.
    induction T as [|ub lb c T1 IH1 T2 IH2 a|T1 IH1 T2 IH2|T1 IH1 T2 IH2|n k C ub c T1 IH1|s x a mt|lb n C T1 IH1];
      intros [|ub' lb' c' U1 U2 a'|U1 U2|U1 U2|n' k' C' ub' c' U1|r y a' mt'|lb' n' C' U1] HT HU H;
      try done; try (exact (teq_sinst σ Hσ _ _ HT HU H)); simpl in *; contr_simpl.
    - destruct H as (-> & -> & -> & ? & ? & ?). split_and!; try done; by apply teq_sinst.
    - destruct H as [? ?]. split; auto.
    - destruct H as [? ?]. split; auto.
    - destruct H as (-> & ? & -> & ?). split_and!; try done. by apply sequiv_sinst.
    - destruct H as (-> & -> & -> & ?). split_and!; auto.
  Qed.

  Lemma τS_nonskip u s r : scontr u → scontr s → scontr r → ssub s r → hd u ≠ HSkip →
    sub_view (uptoS τS) (hseqv (hd u) (sinst σ s)) (hseqv (hd u) (sinst σ r)).
  Proof.
    intros Hu Hs Hr H Hne. pose proof (hd_contr u Hu) as Hv.
    destruct (hd u) as [|m T u'|m T u'|v u'|v u'|x y|x y| |w]; simpl in *; try done.
    1-2: destruct Hv as [HT Hu']; split_and!; [done|apply crT_refl|].
    3-4: split; [done|].
    1-4: apply cong_contS; auto using HscS; exists u', s, r; by split_and!.
    all: destruct Hv as [Hx Hy]; split; apply uptoS_in; [exists x, s, r|exists y, s, r]; by split_and!.
  Qed.

  Lemma τS_hd n : ∀ s r, uc s < n → scontr s → scontr r → ssub s r →
    sub_view (uptoS τS) (hd (sinst σ s)) (hd (sinst σ r)).
  Proof.
    induction n as [|n IH]; intros s r Hn Hs Hr H; [lia|].
    eapply sub_view_upto_comp;
      [rewrite <-eq_step_view; apply sequiv_hd, sinst_unfoldS; auto
      |
      |rewrite <-eq_step_view; apply sequiv_hd, sequiv_sym, sinst_unfoldS; auto].
    rewrite !unfoldS_unview.
    pose proof (ssub_hd _ _ H) as Hh. rewrite sub_step_view in Hh.
    pose proof (hd_contr s Hs) as Hvs. pose proof (hd_contr r Hr) as Hvr.
    assert (∀ o s', isvar o → hd s = view (SSeq o s') → uc s' < n) as Hdec.
    { intros o s' Ho E. destruct (unrN_sfuel s Hs) as [h Eh].
      assert (h = SSeq o s') as ->.
      { assert (unfoldS s = h) as Eu by (unfold unfoldS; by rewrite Eh).
        rewrite <-Eu, unfoldS_unview, E. apply unview_view. }
      destruct (unrN_var_uc _ _ _ _ Hs Ho Eh). lia. }
    destruct (hd s) as [|m T s'|m T s'|v s'|v s'|s1 s2|s1 s2| |w] eqn:Es,
      (hd r) as [|m' T' r'|m' T' r'|v' r'|v' r'|r1 r2|r1 r2| |w'] eqn:Er; simpl in *; try done.
    - destruct Hh as (-> & HT & Hc), Hvs, Hvr.
      split_and!; [done|by apply crT_sinst|by apply τS_base].
    - destruct Hh as (-> & HT & Hc), Hvs, Hvr.
      split_and!; [done|by apply crT_sinst|by apply τS_base].
    - destruct Hh as (-> & Hc). rewrite !hd_seq by sc.
      destruct (hskip_dec (hd (σ v'))) as [E|E].
      + rewrite E. simpl. apply IH; try done. eapply (Hdec (SVar v')); [done|reflexivity].
      + by apply τS_nonskip.
    - destruct Hh as (-> & Hc). rewrite !hd_seq by sc.
      destruct (hskip_dec (hd (dual (σ v')))) as [E|E].
      + rewrite E. simpl. apply IH; try done. eapply (Hdec (SVarD v')); [done|reflexivity].
      + apply τS_nonskip; try done. by rewrite scontr_dual.
    - destruct Hh, Hvs, Hvr. split; by apply τS_base.
    - destruct Hh, Hvs, Hvr. split; by apply τS_base.
  Qed.

  Lemma ssub_sinst s r : scontr s → scontr r → ssub s r → ssub (sinst σ s) (sinst σ r).
  Proof.
    intros Hs Hr H.
    eapply ssub_sequiv_l; [apply sequiv_sym, seq_skip_l, HscS, Hs|].
    eapply ssub_sequiv_r; [|apply seq_skip_l, HscS, Hr].
    apply (ssub_upto τS); [|exists SSkip, s, r; by split_and!].
    clear dependent s r. intros x y (u & s & r & Hu & Hs & Hr & H & -> & ->).
    rewrite sub_step_view, !hd_seq by auto using HscS.
    destruct (hskip_dec (hd u)) as [E|E].
    - rewrite E. cbn [hseqv]. apply (τS_hd (S (uc s))); auto.
    - by apply τS_nonskip.
  Qed.
End ssub_sinst.
