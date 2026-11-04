(** * Primitive choice translates into sums plus delegation

    The core has select₁, select₂ and branch as constants (K4, K11):

      selectᵢ : ⊕(S₁, S₂)@x ⊸^x Sᵢ@x[i]               asks x ≺ x[i]
      branch  : &(S₁, S₂)@x ⊸^x S₁@x[0] + S₂@x[1]      asks x ≺ x[0], x ≺ x[1]

    examples/ChoiceEnc.v encodes ⊕(S₁, S₂) as Sch S₁ S₂ and &(T₁, T₂) as
    Sbr T₁ T₂. This file translates programs that use the constants into
    programs that use the encoding, and proves that the translation
    preserves typing ([choice_translate]).

    The terms. A selection sends the injection of a fresh continuation
    and hands the closing of the carrier to a thread of its own, so its
    upper point stays x. A branch receives the sum and closes the
    carrier in a thread of its own as well:

      selᵢ = λc. let (k, k′) = new ∗ at x[i] in
                 let (c, ()) = ⟨send ⟨injᵢ k′, c⟩, ∗⟩ in
                 let () = spawn (λu. let () = u in close c) in k
      bra  = λc. let (p, c) = recv c in
                 let () = spawn (λu. let () = u in close c) in p

    [selE_typed] and [braE_typed] give them the translated types of the
    constants. selᵢ asks x known, x ≺ x[0] and x ≺ x[1], because the send
    orders the carrier below both points of the payload. bra asks no
    fact.

    The fragment ([fstyped]). Every rule of [styped] except three
    restrictions.
    - E-Conv compares session types syntactically ([hsteq0]). Points
      still convert by ≡. The translation does not commute with the
      session equivalence ⊕(S₁, S₂);S ≈ ⊕(S₁;S, S₂;S).
    - □ and force bind no session variable (k = 0). A box with session
      variables is typed at every instance, and most instances are no
      translation of a source type.
    - selectᵢ at x asks x known and both x ≺ x[0] and x ≺ x[1], the two
      facts branch asks.
    [fstyped_styped] embeds the fragment in [styped]. The translation
    keeps the hypotheses Ψ, so the creation constraint of a program in
    the fragment is the creation constraint of its translation. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.ChoiceEnc.

Set Default Proof Using "All".

(** ** The translation of types *)

Fixpoint tr_ty (T : ty) : ty :=
  match T with
  | TUnit => TUnit
  | TLolli ub lb T1 U => TLolli ub lb (tr_ty T1) (tr_ty U)
  | TProd T1 U => TProd (tr_ty T1) (tr_ty U)
  | TSum T1 U => TSum (tr_ty T1) (tr_ty U)
  | TBox n k C T1 => TBox n k C (tr_ty T1)
  | TSess s x => TSess (tr_sty s) x
  | TEx lb n C T1 => TEx lb n C (tr_ty T1)
  end
with tr_sty (s : sty) : sty :=
  match s with
  | SRcv m T => SRcv m (tr_ty T)
  | SSnd m T => SSnd m (tr_ty T)
  | SEnd => SEnd
  | SMu s' => SMu (tr_sty s')
  | SVar a => SVar a
  | SVarD a => SVarD a
  | SSkip => SSkip
  | SSeq s1 s2 => SSeq (tr_sty s1) (tr_sty s2)
  | SPlus s1 s2 => Sch (tr_sty s1) (tr_sty s2)
  | SWith s1 s2 => Sbr (tr_sty s1) (tr_sty s2)
  end.

Definition tr_lenv (Δ : lenv) : lenv := fmap (M:=option) tr_ty <$> Δ.

Lemma tr_sflip_mut :
  (∀ T k, tr_ty (sflip_ty k T) = sflip_ty k (tr_ty T)) ∧
  (∀ s k, tr_sty (sflip k s) = sflip k (tr_sty s)).
Proof.
  apply ty_sty_mut_ind; intros; simpl; try (f_equal; auto; done).
  - repeat case_decide; done.
  - repeat case_decide; done.
  - unfold Sch. simpl. rewrite H, H0, !sflip_dual. done.
  - unfold Sbr. simpl. rewrite H, H0. done.
Qed.

Lemma tr_dual s : tr_sty (dual s) = dual (tr_sty s).
Proof.
  induction s as [m T|m T| |s IH|a|a| |s1 IH1 s2 IH2|s1 IH1 s2 IH2|s1 IH1 s2 IH2]; simpl; try done.
  - by rewrite (proj2 tr_sflip_mut), IH.
  - by rewrite IH1, IH2.
  - unfold Sbr, Sch. simpl. by rewrite IH1, IH2.
  - unfold Sbr, Sch. simpl. by rewrite IH1, IH2, !dual_involutive.
Qed.

Lemma tr_pinst T : ∀ σ, tr_ty (pinst_ty σ T) = pinst_ty σ (tr_ty T).
Proof. induction T; intros σ; simpl; f_equal; auto. Qed.

Lemma tr_ty_inst xs T : tr_ty (ty_inst xs T) = ty_inst xs (tr_ty T).
Proof. apply tr_pinst. Qed.

Lemma tr_heads T : heads (tr_ty T) = heads T.
Proof. induction T; simpl; congruence. Qed.

Lemma tr_hbot T : hbot (tr_ty T) = hbot T.
Proof. induction T; simpl; try congruence. Qed.

Lemma tr_unlimited T : unlimited (tr_ty T) ↔ unlimited T.
Proof. by destruct T. Qed.

Lemma tr_pscoped T : ∀ j, pscoped j (tr_ty T) ↔ pscoped j T.
Proof.
  induction T; intros j; simpl; try done; try (by rewrite IHT1, IHT2); try (by rewrite IHT).
Qed.

Lemma tr_lenv_heads Δ : lenv_heads (tr_lenv Δ) = lenv_heads Δ.
Proof. induction Δ as [|[T|] Δ IH]; simpl; [done| |done]. by rewrite tr_heads, IH. Qed.

Lemma tr_lenv_bot Δ : lenv_bot (tr_lenv Δ) = lenv_bot Δ.
Proof. induction Δ as [|[T|] Δ IH]; simpl; [done| |done]. by rewrite tr_hbot, IH. Qed.

Lemma tr_lenv_empty Δ : lenv_empty Δ → lenv_empty (tr_lenv Δ).
Proof.
  intros H o Ho. apply list_elem_of_fmap in Ho as (o' & -> & Ho). by rewrite (H o' Ho).
Qed.

Lemma tr_lenv_lookup Δ i : tr_lenv Δ !! i = fmap (M:=option) tr_ty <$> Δ !! i.
Proof. revert i. induction Δ as [|o Δ IH]; intros [|i]; simpl; auto. Qed.

Lemma tr_lenv_only Δ x T : lenv_only Δ x T → lenv_only (tr_lenv Δ) x (tr_ty T).
Proof.
  intros [H1 H2]. split; [by rewrite tr_lenv_lookup, H1|].
  intros y T' Hy. rewrite tr_lenv_lookup in Hy.
  destruct (Δ !! y) as [[U|]|] eqn:E; simpl in Hy; try done.
  injection Hy as <-. destruct (H2 y U E) as [-> ->]. done.
Qed.

Lemma tr_lenv_split Δ Δ1 Δ2 : lenv_split Δ Δ1 Δ2 → lenv_split (tr_lenv Δ) (tr_lenv Δ1) (tr_lenv Δ2).
Proof. induction 1; simpl; constructor; try done. by apply tr_unlimited. Qed.

Lemma tr_lenv_wk Δ' Δ : lenv_wk Δ' Δ → lenv_wk (tr_lenv Δ') (tr_lenv Δ).
Proof. induction 1; simpl; constructor; try done. by apply tr_unlimited. Qed.

Lemma tr_lenv_unl Δ : lenv_unl Δ → lenv_unl (tr_lenv Δ).
Proof.
  intros H o Ho. apply list_elem_of_fmap in Ho as (o' & -> & Ho).
  destruct (H o' Ho) as [->|(U & -> & HU)]; [by left|right].
  exists (tr_ty U). split; [done|by apply tr_unlimited].
Qed.

Lemma tr_lenv_pinst σ Δ : tr_lenv (lenv_pinst σ Δ) = lenv_pinst σ (tr_lenv Δ).
Proof.
  induction Δ as [|[T|] Δ IH]; simpl; [done| |by rewrite IH]. by rewrite tr_pinst, IH.
Qed.

Lemma tr_lenv_insert Δ i o : tr_lenv (<[i := o]> Δ) = <[i := fmap (M:=option) tr_ty o]> (tr_lenv Δ).
Proof.
  revert i. induction Δ as [|o' Δ IH]; intros [|i]; simpl; try done. by rewrite IH.
Qed.

(** ** The translation of terms *)

Definition selE (inj : expr → expr) : expr :=
  Lam (let_new (LetP (Pair (App ESend (Pair (inj (Var 0)) (Var 4))) EUnit)
    (LetU (Var 0) (LetU (App ESpawn (Lam (LetU (Var 0) (App EClos (Var 2))))) (Var 3))))).

Definition braE : expr :=
  Lam (LetP (App ERecv (Var 0)) (LetU (App ESpawn (Lam (LetU (Var 0) (App EClos (Var 1))))) (Var 1))).

Definition tr_konst (k : konst) : expr :=
  match k with
  | KSel1 => selE Inj1
  | KSel2 => selE Inj2
  | KBra => braE
  | _ => Konst k
  end.

Fixpoint tr_e (e : expr) : expr :=
  match e with
  | Var x => Var x
  | EUnit => EUnit
  | Konst k => tr_konst k
  | Chan c => Chan c
  | Lam e => Lam (tr_e e)
  | App e1 e2 => App (tr_e e1) (tr_e e2)
  | Pair e1 e2 => Pair (tr_e e1) (tr_e e2)
  | LetU e1 e2 => LetU (tr_e e1) (tr_e e2)
  | LetP e1 e2 => LetP (tr_e e1) (tr_e e2)
  | Inj1 e => Inj1 (tr_e e)
  | Inj2 e => Inj2 (tr_e e)
  | Case e e1 e2 => Case (tr_e e) (tr_e e1) (tr_e e2)
  | EBox e => EBox (tr_e e)
  end.

Lemma tr_e_rename e : ∀ r, tr_e (rename r e) = rename r (tr_e e).
Proof. induction e; intros r; simpl; f_equal; auto. by destruct k. Qed.

Lemma tr_e_let_new e : tr_e (let_new e) = let_new (tr_e e).
Proof. done. Qed.

(** ** The fragment *)

(** E-Conv with session types compared syntactically. *)
Fixpoint hsteq0 (Ψ : hyps) (T U : ty) : Prop :=
  match T, U with
  | TUnit, TUnit => True
  | TLolli ub lb T1 T2, TLolli ub' lb' U1 U2 =>
      opt_rel (heqs Ψ) ub ub' ∧ opt_rel (heqs Ψ) lb lb' ∧
      hsteq0 Ψ T1 U1 ∧ hsteq0 Ψ T2 U2
  | TProd T1 T2, TProd U1 U2 => hsteq0 Ψ T1 U1 ∧ hsteq0 Ψ T2 U2
  | TSum T1 T2, TSum U1 U2 => hsteq0 Ψ T1 U1 ∧ hsteq0 Ψ T2 U2
  | TBox _ _ _ _, TBox _ _ _ _ => T = U
  | TSess s x, TSess r y => heqs Ψ x y ∧ s = r
  | TEx _ _ _ _, TEx _ _ _ _ => T = U
  | _, _ => False
  end.

Lemma hsteq0_hsteq Ψ T : ∀ U, hsteq0 Ψ T U → hsteq Ψ T U.
Proof.
  induction T; intros [] H; simpl in *; try done.
  - destruct H as (? & ? & ? & ?). split_and!; auto.
  - destruct H. split; auto.
  - destruct H. split; auto.
  - rewrite <-H. apply teq_refl.
  - destruct H as [? <-]. split; [done|apply seq_refl].
  - injection H as -> -> -> ->. split_and!; [done|done|done|apply teq_refl].
Qed.

Lemma hsteq0_tr Ψ T : ∀ U, hsteq0 Ψ T U → hsteq Ψ (tr_ty T) (tr_ty U).
Proof.
  induction T; intros [] H; simpl in *; try done.
  - destruct H as (? & ? & ? & ?). split_and!; auto.
  - destruct H. split; auto.
  - destruct H. split; auto.
  - injection H as -> -> -> ->. apply teq_refl.
  - destruct H as [? <-]. split; [done|apply seq_refl].
  - injection H as -> -> -> ->. split_and!; [done|done|done|apply teq_refl].
Qed.

(** E-Conv needs the restriction. ⊕(Skip, Skip);!∗.Close ≈ ⊕(Skip;!∗.Close, Skip;!∗.Close),
    and their translations differ in the payload of the first message. *)
Lemma seq_of_hd a b : hd a = hd b → seq a b.
Proof.
  intros H n. destruct n as [|n]; [done|]. simpl. unfold eq_step. rewrite H.
  destruct (hd b); try done; repeat split; try (apply eqT_refl; intros s0; apply seq_refl); try apply seq_refl.
Qed.

Lemma tr_breaks_seq :
  seq (SSeq (SPlus SSkip SSkip) Sd) (SPlus (SSeq SSkip Sd) (SSeq SSkip Sd)) ∧
  ¬ seq (tr_sty (SSeq (SPlus SSkip SSkip) Sd)) (tr_sty (SPlus (SSeq SSkip Sd) (SSeq SSkip Sd))).
Proof.
  split; [by apply seq_of_hd|].
  intros H. apply seq_step in H. unfold eq_step in H.
  change (hd (tr_sty (SSeq (SPlus SSkip SSkip) Sd)))
    with (HSnd 2 (TSum (TSess SSkip (pvar 0)) (TSess SSkip (pvar 1))) (SSeq SEnd Sd)) in H.
  change (hd (tr_sty (SPlus (SSeq SSkip Sd) (SSeq SSkip Sd))))
    with (HSnd 2 (TSum (TSess (SSeq SSkip (SSeq (SRcv 0 TUnit) SEnd)) (pvar 0))
                       (TSess (SSeq SSkip (SSeq (SRcv 0 TUnit) SEnd)) (pvar 1))) SEnd) in H.
  destruct H as (_ & [[_ Hs] _] & _).
  apply seq_step in Hs. unfold eq_step in Hs.
  change (hd SSkip) with HSkip in Hs.
  change (hd (SSeq SSkip (SSeq (SRcv 0 TUnit) SEnd))) with (HRcv 0 TUnit SEnd) in Hs.
  exact Hs.
Qed.

(** The constants other than selection, branch and force. *)
Definition kplain (k : konst) : Prop :=
  match k with KSel1 | KSel2 | KBra | KForce => False | _ => True end.

Inductive fstyped : fhyps → hyps → lenv → sfuture → expr → ty → Prop :=
  | f_unit Φ Ψ Δ F :
      lenv_empty Δ →
      fstyped Φ Ψ Δ F EUnit TUnit
  | f_konst Φ Ψ Δ F k T :
      kplain k → lenv_empty Δ → konst_ty (heqs Ψ) (hlt Ψ) (hyp_known Ψ) k T → kscoped k T →
      fstyped Φ Ψ Δ F (Konst k) T
  | f_sel1 Φ Ψ Δ F S1 S2 x :
      lenv_empty Δ → hyp_known Ψ x → hlt Ψ x (pt_payload x 0) → hlt Ψ x (pt_payload x 1) →
      fstyped Φ Ψ Δ F (Konst KSel1)
        (TLolli (Some x) None (TSess (SPlus S1 S2) x) (TSess S1 (pt_payload x 0)))
  | f_sel2 Φ Ψ Δ F S1 S2 x :
      lenv_empty Δ → hyp_known Ψ x → hlt Ψ x (pt_payload x 0) → hlt Ψ x (pt_payload x 1) →
      fstyped Φ Ψ Δ F (Konst KSel2)
        (TLolli (Some x) None (TSess (SPlus S1 S2) x) (TSess S2 (pt_payload x 1)))
  | f_bra Φ Ψ Δ F S1 S2 x :
      lenv_empty Δ → hlt Ψ x (pt_payload x 0) → hlt Ψ x (pt_payload x 1) →
      fstyped Φ Ψ Δ F (Konst KBra)
        (TLolli (Some x) None (TSess (SWith S1 S2) x)
           (TSum (TSess S1 (pt_payload x 0)) (TSess S2 (pt_payload x 1))))
  | f_force Φ Ψ Δ F n C ub T xs :
      lenv_empty Δ → length xs = n → bcs_hold (heqs Ψ) (hlt Ψ) C xs → Forall (hyp_known Ψ) xs →
      fstyped Φ Ψ Δ F (Konst KForce)
        (TLolli (pt_inst (plist xs) <$> ub) None (TBox n 0 C (TLolli ub None TUnit T)) (ty_inst xs T))
  | f_var Φ Ψ Δ F x T :
      lenv_only Δ x T →
      fstyped Φ Ψ Δ F (Var x) T
  | f_lam Φ Ψ Δ F e T U ub lb φ :
      φ ∉ dom Φ →
      hlb_below_hb Ψ lb (lenv_heads Δ) (lenv_bot Δ) →
      fstyped (<[φ := ub]> Φ) Ψ (Some T :: Δ) (∅, Some (FVar φ)) e U →
      fstyped Φ Ψ Δ F (Lam e) (TLolli ub lb T U)
  | f_app Φ Ψ Δ Δ1 Δ2 F e1 e2 ub lb T U :
      lenv_split Δ Δ1 Δ2 → hub_below_s Ψ Φ ub F →
      fstyped Φ Ψ Δ1 (sf_unionb F (lenv_heads Δ2) (lenv_bot Δ2)) e1 (TLolli ub lb T U) →
      fstyped Φ Ψ Δ2 (sf_union F (opt_heads lb)) e2 T →
      fstyped Φ Ψ Δ F (App e1 e2) U
  | f_pair Φ Ψ Δ Δ1 Δ2 F e1 e2 T U :
      lenv_split Δ Δ1 Δ2 →
      fstyped Φ Ψ Δ1 (sf_unionb F (lenv_heads Δ2) (lenv_bot Δ2)) e1 T →
      fstyped Φ Ψ Δ2 (sf_unionb F (heads T) (hbot T)) e2 U →
      fstyped Φ Ψ Δ F (Pair e1 e2) (TProd T U)
  | f_letu Φ Ψ Δ Δ1 Δ2 F e1 e2 T :
      lenv_split Δ Δ1 Δ2 →
      fstyped Φ Ψ Δ1 (sf_unionb F (lenv_heads Δ2) (lenv_bot Δ2)) e1 TUnit →
      fstyped Φ Ψ Δ2 F e2 T →
      fstyped Φ Ψ Δ F (LetU e1 e2) T
  | f_letp Φ Ψ Δ Δ1 Δ2 F e1 e2 T1 T2 T :
      lenv_split Δ Δ1 Δ2 →
      fstyped Φ Ψ Δ1 (sf_unionb F (lenv_heads Δ2) (lenv_bot Δ2)) e1 (TProd T1 T2) →
      fstyped Φ Ψ (Some T2 :: Some T1 :: Δ2) F e2 T →
      fstyped Φ Ψ Δ F (LetP e1 e2) T
  | f_inj1 Φ Ψ Δ F e T U :
      fstyped Φ Ψ Δ F e T → fstyped Φ Ψ Δ F (Inj1 e) (TSum T U)
  | f_inj2 Φ Ψ Δ F e T U :
      fstyped Φ Ψ Δ F e U → fstyped Φ Ψ Δ F (Inj2 e) (TSum T U)
  | f_case Φ Ψ Δ Δ1 Δ2 F e e1 e2 T1 T2 T :
      lenv_split Δ Δ1 Δ2 →
      fstyped Φ Ψ Δ1 (sf_unionb F (lenv_heads Δ2) (lenv_bot Δ2)) e (TSum T1 T2) →
      fstyped Φ Ψ (Some T1 :: Δ2) F e1 T →
      fstyped Φ Ψ (Some T2 :: Δ2) F e2 T →
      fstyped Φ Ψ Δ F (Case e e1 e2) T
  | f_box Φ Ψ Δ F e m C ub T φ :
      lenv_unl Δ → φ ∉ dom Φ →
      fstyped (<[φ := ub]> (fhyps_pinst (pshift m) Φ))
        (hyps_inst (pshift m) Ψ ++ [(bcs_inst (pshift m) C, ids m)])
        (lenv_pinst (pshift m) (Some (TBox m 0 C (TLolli ub None TUnit T)) :: Δ))
        (∅, Some (FVar φ)) e T →
      fstyped Φ Ψ Δ F (EBox e) (TBox m 0 C (TLolli ub None TUnit T))
  | f_wk Φ Ψ Δ' Δ F e T :
      lenv_wk Δ' Δ → fstyped Φ Ψ Δ' F e T → fstyped Φ Ψ Δ F e T
  | f_contract Φ Ψ Δ U F e T :
      unlimited U →
      fstyped Φ Ψ (Some U :: Some U :: Δ) F e T →
      fstyped Φ Ψ (Some U :: Δ) F (rename pred e) T
  | f_conv Φ Ψ Δ F e T T' :
      hsteq0 Ψ T T' → fstyped Φ Ψ Δ F e T → fstyped Φ Ψ Δ F e T'
  | f_pack Φ Ψ Δ F e lb m C T xs :
      length xs = m → Forall (hyp_known Ψ) xs → bcs_hold (heqs Ψ) (hlt Ψ) C xs →
      hlbx_below_h Ψ lb (heads (ty_inst xs T)) (hbot (ty_inst xs T)) →
      fstyped Φ Ψ Δ F e (ty_inst xs T) → fstyped Φ Ψ Δ F e (TEx lb m C T)
  | f_open Φ Ψ Δ F e i lb m C T U :
      Δ !! i = Some (Some (TEx lb m C T)) → ¬ unlimited T →
      fstyped (fhyps_pinst (pshift m) Φ)
        (hyps_inst (pshift m) Ψ ++ [(bcs_inst (pshift m) C, ids m)])
        (<[i := Some T]> (lenv_pinst (pshift m) Δ))
        (sf_pinst (pshift m) F) e (pinst_ty (pshift m) U) →
      fstyped Φ Ψ Δ F e U.

(** ** The fragment lies in [styped] *)

Theorem fstyped_styped Φ Ψ Δ F e T : fstyped Φ Ψ Δ F e T → styped Φ Ψ Δ F e T.
Proof.
  induction 1.
  - by apply st_unit.
  - by apply st_konst.
  - apply st_konst; [done| |done]. apply KTSel1. done.
  - apply st_konst; [done| |done]. apply KTSel2. done.
  - apply st_konst; [done| |done]. by apply KTBra.
  - apply st_konst; [done| |done].
    rewrite <-(sinst_slist_nil (ty_inst xs T)).
    by apply (KTForce _ _ _ n 0 C ub T xs []).
  - by apply st_var.
  - eapply st_lam; eassumption.
  - eapply st_app; eassumption.
  - eapply st_pair; eassumption.
  - eapply st_letu; eassumption.
  - eapply st_letp; eassumption.
  - by apply st_inj1.
  - by apply st_inj2.
  - eapply st_case; eassumption.
  - eapply (st_box _ _ _ _ _ _ _ _ _ _ φ); [done|done|]. intros ss Hss _. destruct ss; [|done].
    by rewrite sinst_slist_nil.
  - eapply st_wk; eassumption.
  - by apply st_contract.
  - eapply st_conv; [by apply hsteq0_hsteq|done].
  - eapply st_pack; eassumption.
  - eapply st_open; eassumption.
Qed.

(** ** The encoded constants are typed *)

Lemma lenv_empty_allunl Δ : lenv_empty Δ → allunl Δ = true.
Proof.
  induction Δ as [|o Δ IH]; intros H; [done|].
  rewrite (H o (list_elem_of_here _ _)). simpl. apply IH.
  intros o' Ho'. apply H. by apply list_elem_of_further.
Qed.

Section enc.
  Context (W : world) (HWs : strict W).

  Local Ltac unl Hu :=
    cbn; repeat first [rewrite (allunl_lp _ _ _ Hu)|rewrite (allunl_sok _ _ _ _ _ Hu)
      |rewrite (allunl_heads _ Hu)|rewrite (allunl_bot _ Hu)|rewrite Hu]; cbn.

  Lemma selE_typed (i : nat) (inj : expr → expr) Φ Ψ Δ F S1 S2 S x :
    (i = 0 ∧ inj = Inj1 ∧ S = S1) ∨ (i = 1 ∧ inj = Inj2 ∧ S = S2) →
    skn W Ψ x → allunl Δ = true →
    slt W Ψ x (sl0 x) → slt W Ψ x (sl1 x) →
    typed W Φ Ψ ∅ Δ F (selE inj)
      (TLolli (Some x) None (TSess (Sch S1 S2) x) (TSess S (pt_payload x i))).
  Proof.
    intros Hi Hx Hu H0 H1. pose proof (proj1 HWs) as HW.
    set (φ := fresh (dom Φ)).
    apply (tv_lam W HW _ _ _ _ _ _ _ _ _ φ); [apply is_fresh|unl Hu; done|].
    apply (t_new_at W _ _ _ _ _ _ _ S (pt_payload x i) HWs); [by apply skn_payload|].
    assert (slt W Ψ x (pt_payload x i)) as Hxi by (destruct Hi as [(-> & _)|(-> & _)]; done).
    assert (∀ y, y ∈ heads (payload_at 2 (TSum (TSess (dual S1) (pvar 0)) (TSess (dual S2) (pvar 1))) x) →
              slt W Ψ x y) as Hpay.
    { intros y Hy. mem_cases Hy; done. }
    destruct Hi as [(-> & -> & ->)|(-> & -> & ->)].
    all: eapply tv_letp; [exact HW|unl Hu; reflexivity| |].
    (* ⟨send ⟨injᵢ k′, c⟩, ∗⟩ *)
    1, 3: unl Hu; eapply tv_pair; [exact HW|unl Hu; reflexivity|apply tv_unit; [exact HW|unl Hu; reflexivity]|];
      unl Hu; eapply tv_appk;
        [exact HW| |apply (KTSend _ _ _ 2 (TSum (TSess (dual S1) (pvar 0)) (TSess (dual S2) (pvar 1))) SEnd x)| |];
      [unl Hu; eapply tv_pair; [exact HW|unl Hu; reflexivity|apply tv_var; [exact HW|unl Hu; reflexivity|unl Hu; reflexivity]|];
         unl Hu; first [apply t_inj1|apply t_inj2]; apply tv_var; [exact HW|unl Hu; reflexivity|unl Hu; reflexivity]
      |cbn; intros h Hh; mem_cases Hh; assumption
      |kscope
      |apply ubs_intro; [intros y Hy; cbn in Hy; rewrite ?(allunl_lp _ _ _ Hu), ?(allunl_heads _ Hu) in Hy; mem_cases Hy; assumption|cbn; eexists; rewrite lookup_insert_eq; split; [done|]; apply sle_refl, HW]].
    (* let () = u in let () = spawn (λu. let () = u in close c) in k *)
    all: apply tv_letu; [exact HW|unl Hu; reflexivity|apply tv_var; [exact HW|unl Hu; reflexivity|unl Hu; reflexivity]|];
      unl Hu; apply tv_letu; [exact HW|unl Hu; reflexivity| |apply tv_var; [exact HW|unl Hu; reflexivity|unl Hu; reflexivity]];
      unl Hu; eapply tv_appk; [exact HW| |apply KTSpawn|done|apply ubs_none];
      eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pt_shift 1 x)) (Some (pt_shift 1 x))
                (fresh (dom (<[φ:=Some x]> Φ)))); [apply is_fresh|unl Hu; intros y Hy; mem_cases Hy; apply sle_refl, HW|];
      unl Hu; apply tv_letu; [exact HW|unl Hu; reflexivity|apply tv_var; [exact HW|unl Hu; reflexivity|unl Hu; reflexivity]|];
      unl Hu; eapply tv_appk; [exact HW|apply tv_var; [exact HW|unl Hu; reflexivity|unl Hu; reflexivity]|apply KTClos|done|];
      apply ubs_intro; [intros y Hy; cbn in Hy; rewrite ?(allunl_lp _ _ _ Hu), ?(allunl_heads _ Hu) in Hy; mem_cases Hy|cbn; eexists; rewrite lookup_insert_eq; split; [done|]; apply sle_refl, HW].
  Qed.

  Lemma braE_typed Φ Ψ Δ F T1 T2 x :
    allunl Δ = true →
    typed W Φ Ψ ∅ Δ F braE
      (TLolli (Some x) None (TSess (Sbr T1 T2) x) (TSum (TSess T1 (sl0 x)) (TSess T2 (sl1 x)))).
  Proof.
    intros Hu. pose proof (proj1 HWs) as HW.
    set (φ := fresh (dom Φ)).
    apply (tv_lam W HW _ _ _ _ _ _ _ _ _ φ); [apply is_fresh|unl Hu; done|].
    eapply tv_letp; [exact HW|unl Hu; reflexivity| |].
    - unl Hu. eapply tv_appk; [exact HW| | | |].
      + apply tv_var; [exact HW|unl Hu; reflexivity|unl Hu; reflexivity].
      + apply (KTRecv _ _ _ 2 (TSum (TSess T1 (pvar 0)) (TSess T2 (pvar 1))) SEnd x).
      + kscope.
      + apply ubs_intro; [intros y Hy; cbn in Hy; rewrite ?(allunl_lp _ _ _ Hu), ?(allunl_heads _ Hu) in Hy;
                          mem_cases Hy|].
        cbn. eexists. rewrite lookup_insert_eq. split; [done|]. apply sle_refl, HW.
    - unl Hu. apply tv_letu; [exact HW|unl Hu; reflexivity| |].
      + unl Hu. eapply tv_appk; [exact HW| |apply KTSpawn|done|apply ubs_none].
        eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pt_shift 1 x)) (Some (pt_shift 1 x))
                  (fresh (dom (<[φ:=Some x]> Φ)))); [apply is_fresh| |].
        { unl Hu. intros y Hy. mem_cases Hy. apply sle_refl, HW. }
        unl Hu. apply tv_letu; [exact HW|unl Hu; reflexivity| |].
        * apply tv_var; [exact HW|unl Hu; reflexivity|unl Hu; reflexivity].
        * unl Hu. eapply tv_appk; [exact HW| |apply KTClos|done|].
          -- apply tv_var; [exact HW|unl Hu; reflexivity|unl Hu; reflexivity].
          -- apply ubs_intro; [intros y Hy; cbn in Hy; rewrite ?(allunl_lp _ _ _ Hu), ?(allunl_heads _ Hu) in Hy;
                              mem_cases Hy|].
             cbn. eexists. rewrite lookup_insert_eq. split; [done|]. apply sle_refl, HW.
      + apply tv_var; [exact HW|unl Hu; reflexivity|unl Hu; reflexivity].
  Qed.
End enc.

(** ** The plain constants under the translation *)

Lemma tr_payload m T x : tr_ty (payload_at m T x) = payload_at m (tr_ty T) x.
Proof. apply tr_ty_inst. Qed.

Lemma tr_konst_plain Ψ k T :
  kplain k → konst_ty (heqs Ψ) (hlt Ψ) (hyp_known Ψ) k T →
  konst_ty (heqs Ψ) (hlt Ψ) (hyp_known Ψ) k (tr_ty T).
Proof.
  intros Hk H. revert Hk. pattern k, T. revert k T H.
  apply konst_ty_case; intros; simpl; try contradiction.
  - apply KTSpawn.
  - rewrite tr_payload. apply KTSend. rewrite tr_hbot.
    destruct (hbot T); [done|]. intros h Hh. apply H. by rewrite <-tr_payload, tr_heads in Hh.
  - rewrite tr_payload. apply KTRecv.
  - apply KTClos.
  - rewrite tr_dual. by apply KTLink.
  - rewrite tr_dual. by apply KTNewEx.
Qed.

Lemma tr_kscoped k T : kscoped k T → kscoped k (tr_ty T).
Proof.
  destruct k; simpl; try done.
  - destruct T as [|ub lb T1 U| | | | |]; simpl; try done.
    destruct T1 as [| | | | |s x|]; simpl; try done.
    destruct s as [| | | | | | |s1 s2|s1 s2|s1 s2]; simpl; try done.
    all: try (destruct s1; simpl; try done; apply tr_pscoped).
    all: intros _; unfold Sch, Sbr; kscope.
  - destruct T as [|ub lb T1 U| | | | |]; simpl; try done.
    destruct T1 as [| |A B| | | |]; simpl; try done.
    destruct B as [| | | | |s x|]; simpl; try done.
    destruct s as [| | | | | | |s1 s2|s1 s2|s1 s2]; simpl; try done.
    all: try (destruct s1; simpl; try done; apply tr_pscoped).
    all: intros _; unfold Sch, Sbr; kscope.
Qed.

Lemma tr_prim T : prim T → prim (tr_ty T).
Proof. induction 1; simpl; constructor; done. Qed.

(** ** The translation preserves typing *)

Theorem choice_translate Φ Ψ Δ F e T :
  fstyped Φ Ψ Δ F e T → styped Φ Ψ (tr_lenv Δ) F (tr_e e) (tr_ty T).
Proof.
  induction 1; simpl.
  - apply st_unit, tr_lenv_empty, H.
  - replace (tr_konst k) with (Konst k) by (destruct k; done || contradiction).
    apply st_konst; [by apply tr_lenv_empty|by apply tr_konst_plain|by apply tr_kscoped].
  - apply styped_wnil.
    apply (selE_typed wnil wnil_strict 0 Inj1); [by left|by right|by apply lenv_empty_allunl, tr_lenv_empty
      |by apply hlt_slt|by apply hlt_slt].
  - apply styped_wnil.
    apply (selE_typed wnil wnil_strict 1 Inj2); [by right|by right|by apply lenv_empty_allunl, tr_lenv_empty
      |by apply hlt_slt|by apply hlt_slt].
  - apply styped_wnil. apply (braE_typed wnil wnil_strict). by apply lenv_empty_allunl, tr_lenv_empty.
  - rewrite tr_ty_inst. apply st_konst; [by apply tr_lenv_empty| |done].
    rewrite <-(sinst_slist_nil (ty_inst xs (tr_ty T))).
    by apply (KTForce _ _ _ n 0 C ub (tr_ty T) xs []).
  - by apply st_var, tr_lenv_only.
  - eapply (st_lam _ _ _ _ _ _ _ _ _ φ); [done| |exact IHfstyped]. by rewrite tr_lenv_heads, tr_lenv_bot.
  - eapply (st_app _ _ _ (tr_lenv Δ1) (tr_lenv Δ2)); [by apply tr_lenv_split|done| |exact IHfstyped2].
    by rewrite tr_lenv_heads, tr_lenv_bot.
  - eapply (st_pair _ _ _ (tr_lenv Δ1) (tr_lenv Δ2)); [by apply tr_lenv_split| |].
    + by rewrite tr_lenv_heads, tr_lenv_bot.
    + by rewrite tr_heads, tr_hbot.
  - eapply (st_letu _ _ _ (tr_lenv Δ1) (tr_lenv Δ2)); [by apply tr_lenv_split| |exact IHfstyped2].
    by rewrite tr_lenv_heads, tr_lenv_bot.
  - eapply (st_letp _ _ _ (tr_lenv Δ1) (tr_lenv Δ2)); [by apply tr_lenv_split| |exact IHfstyped2].
    by rewrite tr_lenv_heads, tr_lenv_bot.
  - by apply st_inj1.
  - by apply st_inj2.
  - eapply (st_case _ _ _ (tr_lenv Δ1) (tr_lenv Δ2)); [by apply tr_lenv_split| |exact IHfstyped2|exact IHfstyped3].
    by rewrite tr_lenv_heads, tr_lenv_bot.
  - apply (st_box _ _ _ _ _ _ _ _ _ _ φ); [by apply tr_lenv_unl|done|]. intros ss Hss _. destruct ss; [|done].
    rewrite sinst_slist_nil. rewrite tr_lenv_pinst in IHfstyped. exact IHfstyped.
  - eapply (st_wk _ _ (tr_lenv Δ')); [by apply tr_lenv_wk|done].
  - rewrite tr_e_rename. apply st_contract; [by apply tr_unlimited|exact IHfstyped].
  - eapply st_conv; [by apply hsteq0_tr|done].
  - eapply st_pack; [done|done|done| |].
    + by rewrite <-tr_ty_inst, tr_heads, tr_hbot.
    + by rewrite <-tr_ty_inst.
  - eapply st_open; [by rewrite tr_lenv_lookup, H|by rewrite tr_unlimited|].
    rewrite tr_lenv_insert, tr_lenv_pinst, tr_pinst in IHfstyped. exact IHfstyped.
Qed.

(** A closed program of the fragment translates into a deadlock-free
    program under the same top-level constraint. *)
Corollary choice_translate_df n C0 t T :
  creation_ok n nofact nofact (λ _, False) C0 → prim T →
  fstyped ∅ [(C0, ids n)] [] (∅, None) t T →
  deadlock_free (∅, {[+ tr_e t +]}).
Proof.
  intros HC HT Ht. apply (soundness_source n C0 _ (tr_ty T) HC); [by apply tr_prim|].
  apply (choice_translate _ _ _ _ _ _ Ht).
Qed.
