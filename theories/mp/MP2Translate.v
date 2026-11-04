(** * From derivations of Mordido and Pérez to the static system, version 2

    A derivation Θ | Γ ⊢ e : T ⋄ σs ⇝ e′ becomes a derivation of [typed]
    at the priority world [Wmp] ([mp2_translate]). The lemma holds at
    every instance ss of the session type variables, every anchor B
    whose facts the context Ψ provides for every valuation of Θ
    ([good]), every map pts of end points whose walks lie between the
    floor and the ceiling of B ([pts_ok]), and every frame F above the
    upper point of σs. [soundness] then makes every closed program of
    type unit deadlock free ([mp2_deadlock_free]). *)

From stdpp Require Import base gmap numbers.
From LRGV Require Export mp.MP2Typing.

Set Default Proof Using "All".

(** ** Renaming past inserted entries *)

Fixpoint ren_of (ins : list bool) (x : nat) : nat :=
  match ins with
  | [] => x
  | false :: ins => match x with 0 => 0 | S x => S (ren_of ins x) end
  | true :: ins => S (ren_of ins x)
  end.

Lemma rename_id e : rename (λ x, x) e = e.
Proof.
  induction e; simpl; f_equal; try done;
    (etransitivity; [|eassumption]); apply rename_ext; by intros [|[|x]].
Qed.

Lemma ren_up ins e : rename (upren (ren_of ins)) e = rename (ren_of (false :: ins)) e.
Proof. apply rename_ext. by intros [|x]. Qed.

Lemma ren_up2 ins e :
  rename (upren (upren (ren_of ins))) e = rename (ren_of (false :: false :: ins)) e.
Proof. apply rename_ext. by intros [|[|x]]. Qed.

(** ** Linear environments *)

Section lenv.
  Lemma unl_wk Δ : lenv_unl Δ → lenv_wk (lenv_nones Δ) Δ.
  Proof.
    induction Δ as [|o Δ IH]; intros H; simpl; [constructor|].
    destruct (H o) as [->|(T & -> & HT)]; [by left| |].
    - constructor. apply IH. intros o' Ho'. apply H. by right.
    - apply lwk_drop; [done|]. apply IH. intros o' Ho'. apply H. by right.
  Qed.

  Lemma unl_heads Δ : lenv_unl Δ → lenv_heads Δ = ∅.
  Proof.
    induction Δ as [|o Δ IH]; intros H; simpl; [done|].
    destruct (H o) as [->|(T & -> & HT)]; [by left| |].
    - apply IH. intros o' Ho'. apply H. by right.
    - destruct T; try done. simpl. rewrite IH; [set_solver|]. intros o' Ho'. apply H. by right.
  Qed.

  Lemma unl_pinst σ Δ : lenv_unl Δ → lenv_unl (lenv_pinst σ Δ).
  Proof.
    intros H o Ho. apply list_elem_of_fmap in Ho as (o' & -> & Ho').
    destruct (H o' Ho') as [->|(T & -> & HT)]; [by left|right].
    eexists. split; [done|]. by apply unlimited_pinst.
  Qed.

  Lemma nones_heads Δ : lenv_heads (lenv_nones Δ) = ∅.
  Proof. induction Δ; simpl; done. Qed.

  Lemma nones_unl Δ : lenv_unl (lenv_nones Δ).
  Proof. intros o Ho. left. by apply lenv_empty_nones in Ho. Qed.

  Lemma lenv_split_nones_r Δ : lenv_split Δ Δ (lenv_nones Δ).
  Proof. apply lenv_split_comm, lenv_split_nones_l. Qed.

  Lemma lonly_wk_unl x Δ :
    (∀ y T, y ≠ x → Δ !! y = Some (Some T) → unlimited T) → lenv_wk (lonly x Δ) Δ.
  Proof.
    revert x. induction Δ as [|o Δ IH]; intros [|x] H; simpl; [constructor|constructor| |].
    - constructor. apply unl_wk. intros o' Ho'. apply list_elem_of_lookup_1 in Ho' as [y Hy].
      destruct o' as [T|]; [|by left]. right. exists T. split; [done|]. by apply (H (S y)).
    - destruct o as [T|].
      + apply lwk_drop; [by apply (H 0)|]. apply IH. intros y T' Hy HyT. apply (H (S y)); [lia|done].
      + constructor. apply IH. intros y T' Hy HyT. apply (H (S y)); [lia|done].
  Qed.

  Lemma empty_heads Δ : lenv_empty Δ → lenv_heads Δ = ∅.
  Proof. intros H. apply unl_heads. intros o Ho. left. by apply H. Qed.

  Lemma empty_lookup Δ y T : lenv_empty Δ → Δ !! y = Some (Some T) → False.
  Proof. intros H Hy. apply list_elem_of_lookup_2 in Hy. by apply H in Hy. Qed.

  Lemma lenv_split_empty' Δ : lenv_empty Δ → lenv_split Δ Δ Δ.
  Proof.
    induction Δ as [|o Δ IH]; intros H; [constructor|].
    rewrite (H o) by set_solver. constructor. apply IH. intros o' Ho'. apply H. set_solver.
  Qed.
End lenv.

Lemma lenv_bot_empty Δ : lenv_empty Δ → lenv_bot Δ = false.
Proof.
  induction Δ as [|o Δ IH]; intros H; [done|]. rewrite (H o) by set_solver. simpl.
  apply IH. intros o' Ho'. apply H. set_solver.
Qed.

Lemma sf_unionb_false F X b : b = false → sf_unionb F X b = sf_union F X.
Proof. by intros ->. Qed.

Lemma lenv_bot_nones Δ : lenv_bot (lenv_nones Δ) = false.
Proof. induction Δ; simpl; done. Qed.

Lemma lenv_bot_cons_none Δ : lenv_bot (None :: Δ) = lenv_bot Δ.
Proof. done. Qed.

Lemma lenv_bot_cons_some T Δ : lenv_bot (Some T :: Δ) = hbot T || lenv_bot Δ.
Proof. done. Qed.

Lemma hbot_payload m T x : hbot (payload_at m T x) = hbot T.
Proof. unfold payload_at, ty_inst. apply hbot_pinst. Qed.

Ltac bot_extra := fail.

Ltac bot_false :=
  repeat (match goal with H := _ |- _ => subst H end);
  rewrite ?lenv_bot_pinst, ?hbot_pinst, ?lenv_bot_nones, ?lenv_bot_cons_none, ?lenv_bot_cons_some, ?hbot_payload,
    ?lenv_bot_nones, ?orb_false_l;
  first [done|by apply lenv_bot_empty|bot_extra
        |simpl; first [done|by apply lenv_bot_empty|bot_extra]].

Ltac lbhb := unfold lb_below_hb;
  try match goal with |- context [lenv_bot ?D] =>
    replace (lenv_bot D) with false by (symmetry; bot_false) end; simpl.

(** Drop the flag of every frame whose flag is false. *)
Ltac bclean :=
  repeat match goal with |- context [sf_unionb ?F ?X ?b] =>
    rewrite (sf_unionb_false F X b) by bot_false end.

Section rules.
  Context (W : world) (HW : world_wf W).

  Lemma tv_var_unl Φ Ψ Δ F x T :
    Δ !! x = Some (Some T) → (∀ y T', y ≠ x → Δ !! y = Some (Some T') → unlimited T') →
    typed W Φ Ψ ∅ Δ F (Var x) T.
  Proof. intros H1 H2. eapply t_wk; [by apply lonly_wk_unl|]. apply t_var. by apply lonly_only. Qed.

  Lemma tv_unit_unl Φ Ψ Δ F : lenv_unl Δ → typed W Φ Ψ ∅ Δ F EUnit TUnit.
  Proof. intros H. eapply t_wk; [by apply unl_wk|]. apply t_unit, lenv_empty_nones. Qed.

  (** E-Exp for a closed constraint and no session variable. *)
  Lemma tv_box Φ Ψ Δ F e m C ub T :
    lenv_unl Δ → bc_env C = [] →
    (∀ φ, φ ∉ dom Φ →
      typed W (<[φ := ub]> (fhyps_pinst (pshift m) Φ)) (hyps_inst (pshift m) Ψ ++ [(C, ids m)]) ∅
        (lenv_pinst (pshift m) (Some (TBox m 0 C (TLolli ub None TUnit T)) :: Δ)) (∅, Some (FVar φ)) e T) →
    typed W Φ Ψ ∅ Δ F (EBox e) (TBox m 0 C (TLolli ub None TUnit T)).
  Proof.
    intros HΔ HC H. set (φ := fresh (dom Φ)). apply (t_box W Φ Ψ Δ F e m 0 C ub T φ); [done|apply is_fresh|].
    assert (bcs_inst (pshift m) C = C) as -> by (destruct C; simpl in *; by subst).
    box_k0. apply H, is_fresh.
  Qed.

  Lemma tv_unitv Φ Ψ Δ F : lenv_unl Δ → typed W Φ Ψ ∅ Δ F unitv U.
  Proof.
    intros HΔ. apply tv_box; [done|done|]. intros φ _. apply tv_unit_unl.
    apply unl_pinst. intros o [->|Ho]%elem_of_cons; [right; by eexists|by apply HΔ].
  Qed.

  Lemma tv_app_closed Φ Ψ Δ F f e ub T U' :
    lenv_bot Δ = false →
    typed W Φ Ψ ∅ (lenv_nones Δ) (sf_union F (lenv_heads Δ)) f (TLolli ub None T U') →
    typed W Φ Ψ ∅ Δ F e T →
    ub_below_s W Ψ Φ ub F →
    typed W Φ Ψ ∅ Δ F (App f e) U'.
  Proof.
    intros Hb Hf He Hub. eapply (t_app W Φ Ψ ∅ ∅ ∅ Δ (lenv_nones Δ) Δ F _ _ ub None).
    - by apply comp0.
    - apply lenv_split_nones_l.
    - done.
    - by rewrite Hb, (tenv_heads0 W HW), union_empty_l_L.
    - destruct F as [P o]. unfold sf_union. simpl. by rewrite union_empty_r_L.
  Qed.

  Lemma ubs_fresh Ψ Φ φ u : ub_below_s W Ψ (<[φ := u]> Φ) u (∅, Some (FVar φ)).
  Proof.
    destruct u as [u|]; [|done]. split_and!; simpl; [set_solver| |done].
    intros φ' [=<-]. apply (fl_v (FCtx _ _ _)). simpl. by rewrite lookup_insert_eq.
  Qed.

  Lemma ubs_union Ψ Φ u F X :
    ub_below_s W Ψ Φ u F → (∀ x, u = Some x → ∀ h, h ∈ X → slt W Ψ x h) →
    ub_below_s W Ψ Φ u (sf_union F X).
  Proof.
    destruct u as [x|]; [|done]. intros (H1 & H2 & H3) HX. split_and!; [|done|done]. simpl.
    intros y [Hy|Hy]%elem_of_union; [by apply H1|]. apply fl_points. by apply (HX x).
  Qed.

  Lemma ubs_lower Ψ Φ a b F :
    (∀ x, a = Some x → ∃ y, b = Some y ∧ sle W Ψ x y) →
    ub_below_s W Ψ Φ b F → ub_below_s W Ψ Φ a F.
  Proof.
    intros Hab Hb. destruct a as [x|]; [|done].
    destruct (Hab x eq_refl) as (y & -> & Hxy). destruct Hb as (H1 & H2 & H3).
    destruct Hxy as [Hxy|Hxy]; (split; [|split; [|done]]).
    - intros z Hz. eapply (fl_eql (FCtx W Ψ Φ)); [exact Hxy|by apply H1].
    - intros φ Hφ. eapply (fl_eql (FCtx W Ψ Φ)); [exact Hxy|by apply H2].
    - intros z Hz. eapply (fl_trans (FCtx W Ψ Φ)); [apply fl_points; exact Hxy|by apply H1].
    - intros φ Hφ. eapply (fl_trans (FCtx W Ψ Φ)); [apply fl_points; exact Hxy|by apply H2].
  Qed.
End rules.

Lemma sf_union_empty F : sf_union F ∅ = F.
Proof. destruct F as [P o]. unfold sf_union. simpl. by rewrite union_empty_r_L. Qed.

Lemma slt_seqs_r W Ψ x y z : slt W Ψ x y → seqs W Ψ y z → slt W Ψ x z.
Proof. intros H1 H2. by eapply (fl_eqr (FCtx W Ψ ∅)). Qed.

Lemma slt_seqs_l W Ψ x y z : seqs W Ψ x y → slt W Ψ y z → slt W Ψ x z.
Proof. intros H1 H2. by eapply (fl_eql (FCtx W Ψ ∅)). Qed.

Lemma steq_lolli W Ψ ub lb T T' U U' :
  steq W Ψ T T' → steq W Ψ U U' → steq W Ψ (TLolli ub lb T U) (TLolli ub lb T' U').
Proof.
  intros H1 H2. simpl. split_and!; [destruct ub; [apply se_refl|done]|destruct lb; [apply se_refl|done]|done|done].
Qed.

Lemma steq_sess W Ψ s s' x x' : seqs W Ψ x x' → seq s s' → steq W Ψ (TSess s x) (TSess s' x').
Proof. intros H1 H2. by split. Qed.

Lemma steq_prod W Ψ T T' U U' : steq W Ψ T T' → steq W Ψ U U' → steq W Ψ (TProd T U) (TProd T' U').
Proof. intros H1 H2. by split. Qed.

Lemma steq_sum W Ψ T T' U U' : steq W Ψ T T' → steq W Ψ U U' → steq W Ψ (TSum T U) (TSum T' U').
Proof. intros H1 H2. by split. Qed.

Lemma steq_refl W Ψ T : steq W Ψ T T.
Proof. apply teq_steq, teq_refl. Qed.

(** ** Session substitutions *)

Lemma heads_sinst σ T : heads (sinst_ty σ T) = heads T.
Proof. revert σ. induction T; intros σ; simpl; try done; by rewrite ?IHT1, ?IHT2. Qed.

Lemma unlimited_sinst σ T : unlimited T → unlimited (sinst_ty σ T).
Proof. destruct T; simpl; done. Qed.

Lemma lenv_heads_sinst σ Δ : lenv_heads (fmap (M:=option) (sinst_ty σ) <$> Δ) = lenv_heads Δ.
Proof. induction Δ as [|[T|] Δ IH]; simpl; [done| |exact IH]. rewrite heads_sinst. by f_equal. Qed.

Lemma polS_sinst σ p s : sinst σ (polS p s) = polS p (sinst σ s).
Proof. destruct p; simpl; [by rewrite dual_sinst|done]. Qed.

(** A closed session type has no variable. *)

Fixpoint rclosed_sinst_mut (Q : msty) : ∀ σ, rclosed Q → sinst σ (ers Q) = ers Q
with rclosedp_sinst_mut (P : mpay) : ∀ σ, match P with MPUnit => True | MPChan _ Q _ _ => rclosed Q end →
  sinst_ty σ (ersp P) = ersp P.
Proof.
  - destruct Q as [| A B | a P | a P | a A B | a A B | a w | Q0 | | j]; intros σ HQ; simpl in *; try done.
    + destruct HQ. by rewrite !rclosed_sinst_mut.
    + by rewrite rclosedp_sinst_mut.
    + by rewrite rclosedp_sinst_mut.
    + destruct HQ. by rewrite !rclosed_sinst_mut.
    + destruct HQ. by rewrite !rclosed_sinst_mut.
  - destruct P as [|pp Qp hp dp]; intros σ HP; simpl; [done|]. by rewrite polS_sinst, rclosed_sinst_mut.
Qed.

(** The body of a µ has the µ's own variable only. *)
Fixpoint rbody_sinst (Q : msty) : ∀ σ, rbody Q → σ 0 = SVar 0 → sinst σ (ers Q) = ers Q.
Proof.
  destruct Q as [| A B | a P | a P | a A B | a A B | a w | Q0 | | j]; intros σ HQ H0; simpl in *; try done.
  - destruct HQ. by rewrite !rbody_sinst.
  - by rewrite rclosedp_sinst_mut.
  - by rewrite rclosedp_sinst_mut.
  - destruct HQ. by rewrite !rbody_sinst.
  - destruct HQ. by rewrite !rbody_sinst.
Qed.

Lemma mrec_sinst σ S0 : rbody S0 → sinst σ (ers (MRec S0)) = ers (MRec S0).
Proof. intros H. simpl. f_equal. by apply rbody_sinst. Qed.

(** A scoped session type depends on the instance below its scope only. *)
Fixpoint msc_sinst_ext (Q : msty) : ∀ k σ σ', msc k Q → (∀ j, j < k → σ j = σ' j) →
  sinst σ (ers Q) = sinst σ' (ers Q)
with mscp_sinst_ext (P : mpay) : ∀ k σ σ', match P with MPUnit => True | MPChan _ Q _ _ => msc k Q end →
  (∀ j, j < k → σ j = σ' j) → sinst_ty σ (ersp P) = sinst_ty σ' (ersp P).
Proof.
  - destruct Q as [| A B | a P | a P | a A B | a A B | a w | Q0 | | j]; intros k σ σ' HQ H; simpl in *; try done.
    + destruct HQ. by rewrite !(msc_sinst_ext _ k σ σ').
    + by rewrite (mscp_sinst_ext P k σ σ').
    + by rewrite (mscp_sinst_ext P k σ σ').
    + destruct HQ. by rewrite !(msc_sinst_ext _ k σ σ').
    + destruct HQ. by rewrite !(msc_sinst_ext _ k σ σ').
    + f_equal. rewrite !rbody_sinst; done.
    + by apply H.
  - destruct P as [|pp Qp hp dp]; intros k σ σ' HP H; simpl; [done|].
    by rewrite !polS_sinst, (msc_sinst_ext Qp k σ σ').
Qed.

Lemma tsub_rbody τ Q : rbody Q → tsub τ Q = Q.
Proof.
  assert (∀ Q, rclosed Q → tsub τ Q = Q) as Hc.
  { fix IH 1. intros [| A B | a P | a P | a A B | a A B | a w | Q0 | | j] HQ; simpl in *; try done;
      repeat match goal with H : _ ∧ _ |- _ => destruct H end; try (by rewrite !IH).
    - destruct P as [|pp Qp hp dp]; [done|]. simpl. by rewrite IH.
    - destruct P as [|pp Qp hp dp]; [done|]. simpl. by rewrite IH. }
  revert Q. fix IH 1. intros [| A B | a P | a P | a A B | a A B | a w | Q0 | | j] HQ; simpl in *; try done;
    repeat match goal with H : _ ∧ _ |- _ => destruct H end; try (by rewrite !IH).
  - destruct P as [|pp Qp hp dp]; [done|]. simpl. by rewrite Hc.
  - destruct P as [|pp Qp hp dp]; [done|]. simpl. by rewrite Hc.
Qed.

(** Instantiating the variables by τ, then by σ, is instantiating them
    by the instances of τ under σ. *)
Fixpoint ers_tsub (Q : msty) : ∀ τ σ, msc (length τ) Q →
  sinst σ (ers (tsub τ Q)) = sinst (slist ((λ q, sinst σ (ers q)) <$> τ)) (ers Q)
with ersp_tsub (P : mpay) : ∀ τ σ, match P with MPUnit => True | MPChan _ Q _ _ => msc (length τ) Q end →
  sinst_ty σ (ersp (tsubp τ P)) = sinst_ty (slist ((λ q, sinst σ (ers q)) <$> τ)) (ersp P).
Proof.
  - destruct Q as [| A B | a P | a P | a A B | a A B | a w | Q0 | | j]; intros τ σ HQ; simpl in *; try done.
    + destruct HQ. by rewrite !ers_tsub.
    + rewrite ersp_tsub by done. f_equal. by destruct P.
    + rewrite ersp_tsub by done. f_equal. by destruct P.
    + destruct HQ. by rewrite !ers_tsub.
    + destruct HQ. by rewrite !ers_tsub.
    + rewrite tsub_rbody by done. rewrite !rbody_sinst; done.
    + unfold slist. rewrite list_lookup_fmap.
      destruct (lookup_lt_is_Some_2 τ j HQ) as [q Hq]. by rewrite Hq.
  - destruct P as [|pp Qp hp dp]; intros τ σ HP; simpl; [done|].
    by rewrite !polS_sinst, ers_tsub.
Qed.

Lemma iter_sty_up_lt k σ j : j < k → Nat.iter k sty_up σ j = SVar j.
Proof.
  revert j. induction k as [|k IH]; intros j Hj; [lia|]. simpl.
  destruct j as [|j]; [done|]. unfold sty_up. simpl. unfold compose. rewrite IH by lia. done.
Qed.

Lemma msc_sinst_id Q k σ : msc k Q → (∀ j, j < k → σ j = SVar j) → sinst σ (ers Q) = ers Q.
Proof.
  intros HQ H. rewrite (msc_sinst_ext Q k σ SVar); [|done|done].
  apply sinst_id_mut. done.
Qed.

(** ** Translated types under a session substitution *)

Definition trs (ss : list sty) (B : point) (pts : nat → point) (T : mty) : ty :=
  sinst_ty (slist ss) (tr B pts T).

(** A type scoped below k is fixed by an instance that fixes the
    variables below k. Closed abstractions are fixed by every instance. *)
Lemma tr_sinst_id k σ B pts T :
  tpure k T → (∀ j, j < k → σ j = SVar j) → sinst_ty σ (tr B pts T) = tr B pts T.
Proof.
  revert k σ B pts. induction T as [|p Q [h d|n w]| p Q |T IH1 lo ef V IH2|Θ T IH1 ef V IH2|p k' Qa Qr];
    intros k σ B pts HT Hσ; simpl in *; try done.
  - by rewrite polS_sinst, (msc_sinst_id Q k).
  - destruct HT as (H1 & H2 & _). by rewrite (IH1 k), (IH2 k).
  - destruct HT as [H1 H2]. do 4 f_equal; [apply (IH1 (pc_nt Θ))|apply (IH2 (pc_nt Θ))]; try done;
      intros j Hj; by apply iter_sty_up_lt.
  - destruct HT as [H1 H2]. rewrite !polS_sinst.
    rewrite !(msc_sinst_id _ k'); try done; intros j Hj; by apply iter_sty_up_lt.
Qed.

Lemma tr_closed σ B pts T : mun T → tpure 0 T → sinst_ty σ (tr B pts T) = tr B pts T.
Proof. intros _ HT. apply (tr_sinst_id 0); [done|lia]. Qed.

Lemma trs_un ss ss' B B' pts pts' T : mun T → tpure 0 T → trs ss B pts T = trs ss' B' pts' T.
Proof. intros H1 H2. unfold trs. rewrite !tr_closed by done. by apply tr_un. Qed.

Lemma trs_unlimited ss B pts T : mun T → unlimited (trs ss B pts T).
Proof. intros H. apply unlimited_sinst. by apply tr_unlimited. Qed.

Lemma heads_trs ss B pts T : heads (trs ss B pts T) = heads (tr B pts T).
Proof. apply heads_sinst. Qed.

(** ** The environment relation *)

Inductive erel (B : point) (ss : list sty) (pts : nat → point) : list bool → menv → lenv → Prop :=
  | er_nil : erel B ss pts [] [] []
  | er_keep o ins Γ Δ : erel B ss pts ins Γ Δ →
      erel B ss pts (false :: ins) (o :: Γ) (fmap (trs ss B pts) o :: Δ)
  | er_skip o ins Γ Δ :
      (o = None ∨ ∃ T, o = Some T ∧ unlimited T) →
      erel B ss pts ins Γ Δ → erel B ss pts (true :: ins) Γ (o :: Δ).

(** Translated types hold no existential with lower bound ⊥, so no ⊥
    flag arises (sharp edges 103). *)
Lemma hbot_trs ss B pts T : hbot (trs ss B pts T) = false.
Proof. unfold trs. destruct T as [|p Q []|p Q|T lo ef V|Θ T ef V|p k Qa Qr]; done. Qed.

Lemma erel_bot B ss pts ins Γ Δ : erel B ss pts ins Γ Δ → lenv_bot Δ = false.
Proof.
  induction 1 as [|o ins Γ Δ _ IH|o ins Γ Δ Ho _ IH]; simpl; [done| |].
  - destruct o; simpl; [by rewrite hbot_trs|done].
  - destruct Ho as [->|(T & -> & HT)]; simpl; [done|]. destruct T; done.
Qed.

Lemma hbot_sersp ss P : hbot (sinst_ty (slist ss) (ersp P)) = false.
Proof. by destruct P. Qed.

Ltac bot_extra ::= first [by eapply erel_bot|rewrite ?hbot_trs, ?hbot_sersp, ?orb_false_l; first [done|by eapply erel_bot]].

Section erel.
  Context (B : point) (ss : list sty) (pts : nat → point).

  Lemma erel_split ins Γ Δ Γ1 Γ2 :
    erel B ss pts ins Γ Δ → msplit Γ Γ1 Γ2 →
    ∃ Δ1 Δ2, lenv_split Δ Δ1 Δ2 ∧ erel B ss pts ins Γ1 Δ1 ∧ erel B ss pts ins Γ2 Δ2.
  Proof.
    intros H. revert Γ1 Γ2. induction H as [|o ins Γ Δ H IH|o ins Γ Δ Ho H IH]; intros Γ1 Γ2 Hs.
    - inversion Hs; subst. exists [], []. split_and!; constructor.
    - inversion Hs as [|? ? ? Hs'|t ? ? ? Hs'|t ? ? ? Hs'|t ? ? ? Ht Hs']; subst;
        destruct (IH _ _ Hs') as (Δ1 & Δ2 & Hd & H1 & H2).
      + exists (None :: Δ1), (None :: Δ2). split_and!; [simpl; by constructor|apply (er_keep _ _ _ None)..]; done.
      + exists (Some (trs ss B pts t) :: Δ1), (None :: Δ2). split_and!; [simpl; by constructor
          |apply (er_keep _ _ _ (Some t))|apply (er_keep _ _ _ None)]; done.
      + exists (None :: Δ1), (Some (trs ss B pts t) :: Δ2). split_and!; [simpl; by constructor
          |apply (er_keep _ _ _ None)|apply (er_keep _ _ _ (Some t))]; done.
      + exists (Some (trs ss B pts t) :: Δ1), (Some (trs ss B pts t) :: Δ2). split_and!;
          [apply lsplit_unl; [by apply trs_unlimited|done]|apply (er_keep _ _ _ (Some t))..]; done.
    - destruct (IH _ _ Hs) as (Δ1 & Δ2 & Hd & H1 & H2). exists (o :: Δ1), (o :: Δ2).
      split_and!; [|by constructor..].
      destruct Ho as [->|(T & -> & HT)]; [by constructor|by apply lsplit_unl].
  Qed.

  Lemma erel_lookup ins Γ Δ x o :
    erel B ss pts ins Γ Δ → Γ !! x = Some o → Δ !! ren_of ins x = Some (fmap (trs ss B pts) o).
  Proof.
    intros H. revert x. induction H as [|o' ins Γ Δ H IH|o' ins Γ Δ Ho H IH]; intros x Hx; simpl.
    - done.
    - destruct x; simpl in *; [by simplify_eq|by apply IH].
    - by apply IH.
  Qed.

  Lemma erel_inv ins Γ Δ y T :
    erel B ss pts ins Γ Δ → Δ !! y = Some (Some T) →
    (∃ x t, y = ren_of ins x ∧ Γ !! x = Some (Some t) ∧ T = trs ss B pts t) ∨ unlimited T.
  Proof.
    intros H. revert y. induction H as [|o' ins Γ Δ H IH|o' ins Γ Δ Ho H IH]; intros y Hy; simpl.
    - done.
    - destruct y; simpl in *.
      + destruct o' as [t|]; simpl in Hy; simplify_eq. left. by exists 0, t.
      + destruct (IH y Hy) as [(x & t & -> & Hx & ->)|]; [|by right]. left. by exists (S x), t.
    - destruct y; simpl in *.
      + simplify_eq. destruct Ho as [|(T' & ? & ?)]; [done|]. simplify_eq. by right.
      + destruct (IH y Hy) as [(x & t & -> & Hx & ->)|]; [|by right]. left. by exists x, t.
  Qed.

  Lemma erel_var ins Γ Δ W Φ Ψ F x t :
    world_wf W → erel B ss pts ins Γ Δ → menv_only_un Γ x t →
    typed W Φ Ψ ∅ Δ F (Var (ren_of ins x)) (trs ss B pts t).
  Proof.
    intros HW H [Hx Hun]. apply tv_var_unl; [done|by apply (erel_lookup _ Γ _ _ (Some t))|].
    intros y T Hy HyT. destruct (erel_inv _ _ _ _ _ H HyT) as [(x' & t' & -> & Hx' & ->)|]; [|done].
    apply trs_unlimited, (Hun x'); [|done]. intros ->. done.
  Qed.

  Lemma erel_unl ins Γ Δ : erel B ss pts ins Γ Δ → menv_un Γ → lenv_unl Δ.
  Proof.
    intros H HΓ o Ho. apply list_elem_of_lookup_1 in Ho as [y Hy].
    destruct o as [T|]; [|by left]. right. exists T. split; [done|].
    destruct (erel_inv _ _ _ _ _ H Hy) as [(x & t & -> & Hx & ->)|]; [|done].
    apply trs_unlimited, HΓ. by eapply list_elem_of_lookup_2.
  Qed.

  Lemma erel_heads ins Γ Δ h :
    erel B ss pts ins Γ Δ → h ∈ lenv_heads Δ → ∃ t, Some t ∈ Γ ∧ h ∈ heads (tr B pts t).
  Proof.
    intros H. induction H as [|o ins Γ Δ H IH|o ins Γ Δ Ho H IH]; simpl; intros Hh.
    - set_solver.
    - destruct o as [t|]; simpl in Hh.
      + apply elem_of_union in Hh as [Hh|Hh].
        * exists t. split; [by left|]. by rewrite <-(heads_trs ss).
        * destruct (IH Hh) as (t' & ? & ?). exists t'. split; [by right|done].
      + destruct (IH Hh) as (t' & ? & ?). exists t'. split; [by right|done].
    - destruct Ho as [->|(T & -> & HT)]; simpl in Hh; [by apply IH|].
      destruct T; try done. simpl in Hh. apply IH. set_solver.
  Qed.
End erel.

(** ** Points of a good anchor *)

Lemma rpt_root B r : isroot B → pt_root (rpt B r) = pt_name B.
Proof. intros [_ Hr]. unfold rpt, pt_root, pt_slot. simpl. exact Hr. Qed.

Section facts.
  Context (Ψ : hyps) (Θ : pctx) (B : point) (HB : good Ψ Θ B).

  Lemma den_rpt v ts r : den (ianc B v ts) (rpt B r) = dsl (DAnc v ts) (encode_nat r).
  Proof. unfold rpt. rewrite den_slot, den_ianc; [done|apply HB]. Qed.

  Lemma den_anc v ts σ τ : den (ianc B v ts) (rpt B (RAnc σ τ)) = DAnc (evalZ v <$> σ) (mclose v ts <$> τ).
  Proof. rewrite den_rpt. simpl. by rewrite decode_encode_nat. Qed.
  Lemma den_ch v ts Q h d : den (ianc B v ts) (rpt B (RCh Q h d)) = DCh (mclose v ts Q) (pclose v h) d.
  Proof. rewrite den_rpt. simpl. by rewrite decode_encode_nat. Qed.
  Lemma den_lo v ts l : den (ianc B v ts) (rpt B (RLo l)) = DLo (xminlb v ts l) (length l).
  Proof. rewrite den_rpt. simpl. by rewrite decode_encode_nat. Qed.
  Lemma den_hi v ts l : den (ianc B v ts) (rpt B (RHi l)) = DHi (xmaxl v l) (hlen l).
  Proof. rewrite den_rpt. simpl. by rewrite decode_encode_nat. Qed.

  Lemma rank_ch v ts Q h d :
    rank (den (ianc B v ts) (rpt B (RCh Q h d))) = xrk (cprio v ts Q h d) 1 (KT 1).
  Proof. by rewrite den_ch. Qed.

  Lemma slt_rpt r r' :
    (∀ v ts, models Θ v ts → rlt (rank (den (ianc B v ts) (rpt B r))) (rank (den (ianc B v ts) (rpt B r')))) →
    slt Wmp Ψ (rpt B r) (rpt B r').
  Proof. intros H. apply (gd_lt _ _ _ HB); [by apply rpt_root, HB|by apply rpt_root, HB|done]. Qed.

  Lemma seqs_rpt r r' :
    (∀ v ts, models Θ v ts → oeq (den (ianc B v ts) (rpt B r)) (den (ianc B v ts) (rpt B r'))) →
    seqs Wmp Ψ (rpt B r) (rpt B r').
  Proof. intros H. apply (gd_eq _ _ _ HB); [by apply rpt_root, HB|by apply rpt_root, HB|done]. Qed.

  Lemma rpt_known r : skn Wmp Ψ (rpt B r).
  Proof. apply (gd_kn _ _ _ HB). by apply rpt_root, HB. Qed.
End facts.

(** ** Walks of a channel stay between the floor and the ceiling *)

Definition low (d : dn) : Prop := match d with DCh _ _ _ | DJ _ => True | _ => False end.

Lemma low_jnk d : low d → low (jnk (rank d)).
Proof. destruct d as [| Q h dd | | | j |]; simpl; try done; intros _; by destruct (hext _). Qed.

Lemma low_guard d d' : low d → low d' → low (guard d d').
Proof. intros H H'. unfold guard. case_decide; [done|]. by apply low_jnk. Qed.

Lemma low_dsl d i : low d → low (dsl d i).
Proof.
  intros Hd. destruct d as [| Q h dd | | | j |]; simpl in Hd; try done; apply low_guard; try done;
    cbn [dsl0 dbr0]; repeat case_match; done.
Qed.

Lemma low_walk d u : low d → low (dwalk d u).
Proof.
  revert d. induction u as [|[|b|i] u IH]; intros d Hd; simpl; [done| | |]; apply IH.
  - apply low_guard; [done|]. destruct d; simpl; try done. destruct (hdt _ _ _) as [[[]|] ?]; done.
  - by apply low_dsl.
  - by apply low_dsl.
Qed.

Lemma low_ceil d : low d → rlt (rank d) KH.
Proof. destruct d as [| Q h dd | | | j |]; simpl; try done. intros _. by destruct (hext _). Qed.

Lemma low_floor d : low d → rlt (KB (-1)) (rank d).
Proof. destruct d as [| Q h dd | | | j |]; simpl; try done. intros _. destruct (hext _); simpl; lia. Qed.

Definition ceil (B : point) : point := rpt B (RHi [PTop]).
Definition floor (B : point) : point := rpt B (RLo [LP PBot]).

Section ceil.
  Context (Ψ : hyps) (Θ : pctx) (B : point) (HB : good Ψ Θ B).

  Lemma rank_ceil v ts : rank (den (ianc B v ts) (ceil B)) = KH.
  Proof. unfold ceil. by rewrite (den_hi Ψ Θ B HB). Qed.

  Lemma rank_floor v ts : rank (den (ianc B v ts) (floor B)) = KB (-1).
  Proof. unfold floor. by rewrite (den_lo Ψ Θ B HB). Qed.

  Lemma ch_ceil Q h d u :
    slt Wmp Ψ (mwalk (rpt B (RCh Q h d)) u) (ceil B) ∧ slt Wmp Ψ (floor B) (mwalk (rpt B (RCh Q h d)) u).
  Proof.
    assert (pt_root (mwalk (rpt B (RCh Q h d)) u) = pt_name B) as Hr.
    { rewrite <-(rpt_root B (RCh Q h d)) by apply HB.
      generalize (rpt B (RCh Q h d)). clear. induction u as [|[] u IH]; intros x; simpl; [done|..];
        rewrite IH; done. }
    assert (∀ v ts, low (den (ianc B v ts) (mwalk (rpt B (RCh Q h d)) u))) as Hl.
    { intros v ts. rewrite den_mwalk, (den_ch Ψ Θ B HB). by apply low_walk. }
    split; [apply (gd_lt _ _ _ HB); [done|by apply rpt_root, HB|]|apply (gd_lt _ _ _ HB); [by apply rpt_root, HB|done|]];
      intros v ts _; [rewrite rank_ceil; by apply low_ceil|rewrite rank_floor; by apply low_floor].
  Qed.

  (** Every upper point with ⊤ is the ceiling. *)
  Lemma ceil_top ef : PTop ∈ ef → seqs Wmp Ψ (ceil B) (rpt B (RHi ef)).
  Proof.
    intros Ht. apply (seqs_rpt Ψ Θ B HB). intros v ts _. rewrite !(den_hi Ψ Θ B HB).
    assert (xmaxl v ef = XT) as ->.
    { clear -Ht. induction ef as [|ρ ef IH]; [by apply elem_of_nil in Ht|].
      apply elem_of_cons in Ht as [<-|Ht]; simpl; [by destruct (xmaxl v ef)|].
      rewrite IH by done. by destruct (evalp v ρ). }
    unfold hlen. rewrite (bool_decide_eq_true_2 (PTop ∈ ef)) by done. simpl. apply oeq_refl.
  Qed.
End ceil.

Lemma pt_root_mwalk x u : pt_root (mwalk x u) = pt_root x.
Proof. revert x. induction u as [|[] u IH]; intros x; simpl; [done|..]; by rewrite IH. Qed.

(** Every walk from a channel rises at a slot: its slots are no
    anchor slots ([dsl_rise]). This gives x ≺ x[i] at a choice (K11). *)
Section rise.
  Context (Ψ : hyps) (Θ : pctx) (B : point) (HB : good Ψ Θ B).

  Lemma ch_rise Q h d u i :
    slt Wmp Ψ (mwalk (rpt B (RCh Q h d)) u) (pt_slot (mwalk (rpt B (RCh Q h d)) u) i).
  Proof.
    apply (gd_lt _ _ _ HB); [rewrite pt_root_mwalk; by apply rpt_root, HB|rewrite pt_root_slot, pt_root_mwalk; by apply rpt_root, HB|].
    intros v ts _. rewrite den_slot, den_mwalk, (den_ch Ψ Θ B HB). apply dsl_rise.
    pose proof (low_walk (DCh (mclose v ts Q) (pclose v h) d) u I) as Hl.
    revert Hl. destruct (dwalk _ u); simpl; tauto.
  Qed.

End rise.

(** End points: known, between the floor and the ceiling, and rising
    at every slot. *)
Definition pts_ok (Ψ : hyps) (B : point) (pts : nat → point) : Prop :=
  ∀ n, skn Wmp Ψ (pts n) ∧
       (∀ u, slt Wmp Ψ (mwalk (pts n) u) (ceil B) ∧ slt Wmp Ψ (floor B) (mwalk (pts n) u)) ∧
       (∀ u i, slt Wmp Ψ (mwalk (pts n) u) (pt_slot (mwalk (pts n) u) i)).

(** ** Comparisons of ranks *)

Lemma xmaxl_app v l1 l2 : xmaxl v (l1 ++ l2) = xmax (xmaxl v l1) (xmaxl v l2).
Proof.
  induction l1 as [|ρ l1 IH]; simpl; [by destruct (xmaxl v l2)|].
  rewrite IH. destruct (evalp v ρ), (xmaxl v l1), (xmaxl v l2); simpl; f_equal; lia.
Qed.

Lemma xminlb_app v ts l1 l2 : xminlb v ts (l1 ++ l2) = xmin (xminlb v ts l1) (xminlb v ts l2).
Proof.
  induction l1 as [|ρ l1 IH]; simpl; [by destruct (xminlb v ts l2)|].
  rewrite IH. destruct (evlb v ts ρ), (xminlb v ts l1), (xminlb v ts l2); simpl; f_equal; lia.
Qed.

Lemma xmaxl_top v l : PTop ∈ l → xmaxl v l = XT.
Proof.
  induction l as [|ρ l IH]; intros H; [by apply elem_of_nil in H|].
  apply elem_of_cons in H as [<-|H]; simpl; [by destruct (xmaxl v l)|].
  rewrite IH by done. by destruct (evalp v ρ).
Qed.

Lemma xmaxl_notop v l : PTop ∉ l → xmaxl v l ≠ XT.
Proof.
  induction l as [|ρ l IH]; intros H; simpl; [done|].
  assert (ρ ≠ PTop) by set_solver. assert (xmaxl v l ≠ XT) by set_solver.
  destruct ρ, (xmaxl v l); simpl; done.
Qed.

Lemma xle_max_l a b : xle a (xmax a b).
Proof. destruct a, b; simpl; lia. Qed.
Lemma xle_max_r a b : xle b (xmax a b).
Proof. destruct a, b; simpl; lia. Qed.
Lemma xmin_le_l a b : xle (xmin a b) a.
Proof. destruct a, b; simpl; lia. Qed.
Lemma xmin_le_r a b : xle (xmin a b) b.
Proof. destruct a, b; simpl; lia. Qed.
Lemma xle_trans a b c : xle a b → xle b c → xle a c.
Proof. destruct a, b, c; simpl; lia. Qed.

Lemma xminlb_le v ts l i : i ∈ l → xle (xminlb v ts l) (evlb v ts i).
Proof.
  induction l as [|i' l IH]; intros Hi; [by apply elem_of_nil in Hi|].
  apply elem_of_cons in Hi as [->|Hi]; simpl; [apply xmin_le_l|].
  eapply xle_trans; [apply xmin_le_r|by apply IH].
Qed.

Lemma xlt_minlb v ts a l : (∀ i, i ∈ l → xlt a (evlb v ts i)) → l = [] ∨ xlt a (xminlb v ts l).
Proof.
  induction l as [|i l IH]; intros H; [by left|right]. simpl.
  assert (xlt a (evlb v ts i)) as H1 by (apply H; by left).
  destruct (IH (λ i' Hi', H i' (list_elem_of_further _ _ _ Hi'))) as [->|H2].
  - simpl. by destruct (evlb v ts i).
  - destruct a, (evlb v ts i), (xminlb v ts l); simpl in *; lia.
Qed.

Lemma xmaxl_in v a l : a ∈ l → xle (evalp v a) (xmaxl v l).
Proof.
  induction l as [|b l IH]; intros H; [by apply elem_of_nil in H|].
  apply elem_of_cons in H as [->|H]; simpl; [apply xle_max_l|].
  eapply xle_trans; [by apply IH|apply xle_max_r].
Qed.

Lemma xlt_bot x : ¬ xlt x XB.
Proof. destruct x; simpl; tauto. Qed.

Lemma xmaxl_single v a : xmaxl v [a] = evalp v a.
Proof. simpl. by destruct (evalp v a). Qed.

Lemma hlen_top l : PTop ∈ l → hlen l = 0.
Proof. intros H. unfold hlen. by rewrite bool_decide_eq_true_2. Qed.
Lemma hlen_notop l : PTop ∉ l → hlen l = length l.
Proof. intros H. unfold hlen. by rewrite bool_decide_eq_false_2. Qed.

Lemma hi_hi a b n n' : xle a b → b ≠ XT → n < n' → rlt (rank (DHi a n)) (rank (DHi b n')).
Proof. destruct a, b; simpl; try done; lia. Qed.

Lemma hi_hi_lt a b n n' : xlt a b → rlt (rank (DHi a n)) (rank (DHi b n')).
Proof. destruct a, b; simpl; try done; lia. Qed.

Lemma hi_chan a n e : xlt a e → rlt (rank (DHi a n)) (xrk e 1 (KT 1)).
Proof. destruct a, e; simpl; lia. Qed.

Lemma hi_lo v ts a n l : (∀ i, i ∈ l → xlt a (evlb v ts i)) →
  rlt (rank (DHi a n)) (rank (DLo (xminlb v ts l) (length l))).
Proof.
  intros H. destruct (xlt_minlb v ts a l H) as [->|H2]; [destruct a; simpl; lia|].
  destruct a, (xminlb v ts l), (length l); simpl in *; lia.
Qed.

Lemma lo_chan m n e : xle m e → rlt (rank (DLo m (S n))) (xrk e 1 (KT 1)).
Proof. destruct m, e; simpl; lia. Qed.

Lemma lo_lo m m' n n' : xle m m' → n' < n → rlt (rank (DLo m n)) (rank (DLo m' n')).
Proof. destruct m, m', n, n'; simpl; lia. Qed.

Lemma xrk_lt a e : xlt a e → rlt (xrk a 1 (KT 1)) (xrk e 1 (KT 1)).
Proof. destruct a, e; simpl; lia. Qed.

Lemma ch_hi a x n : pfin a → xle (evalp [] a) x → rlt (xrk (evalp [] a) 1 (KT 1)) (rank (DHi x n)).
Proof. destruct a; simpl; try done; destruct x; simpl; lia. Qed.

Lemma evalp_pclose v ρ : evalp [] (pclose v ρ) = evalp v ρ.
Proof. by destruct ρ. Qed.

(** ** Effects, lower bounds and the environment *)

Section heads.
  Context (Ψ : hyps) (Θ : pctx) (B : point) (HB : good Ψ Θ B).

  Lemma hi_le ef ef' x :
    hle Θ ef ef' → hiz B ef = Some x → ∃ y, hiz B ef' = Some y ∧ sle Wmp Ψ x y.
  Proof.
    intros Hle Hx. destruct ef as [|ρ ef0]; [done|]. injection Hx as <-. set (ef := ρ :: ef0).
    assert (∀ l, l ≠ [] → hiz B l = Some (rpt B (RHi l))) as Hz by (by intros [|??]).
    assert (∀ e2, PTop ∈ e2 → e2 ≠ [] → sle Wmp Ψ (rpt B (RHi ef)) (rpt B (RHi e2))) as Htop.
    { intros e2 Ht Hne. destruct (decide (PTop ∈ ef)) as [Ht'|Ht'].
      - left. apply (seqs_rpt Ψ Θ B HB). intros v ts _. rewrite !(den_hi Ψ Θ B HB).
        rewrite !xmaxl_top, !hlen_top by done. apply oeq_refl.
      - right. apply (slt_rpt Ψ Θ B HB). intros v ts _. rewrite !(den_hi Ψ Θ B HB).
        rewrite (xmaxl_top v e2) by done. pose proof (xmaxl_notop v ef Ht').
        destruct (xmaxl v ef); simpl; done. }
    destruct Hle as [Hn|[Ht|[(l1 & l2 & ->)|[Hne Hs]]]]; [done| | |].
    - assert (ef' ≠ []) as Hne by (intros ->; by apply elem_of_nil in Ht).
      exists (rpt B (RHi ef')). split; [by apply Hz|]. by apply Htop.
    - exists (rpt B (RHi (l1 ++ ef ++ l2))). split; [apply Hz; by destruct l1|].
      destruct (decide (l1 = [] ∧ l2 = [])) as [[-> ->]|Hl].
      { rewrite app_nil_r. left. apply se_refl. }
      destruct (decide (PTop ∈ l1 ++ ef ++ l2)) as [Ht|Ht]; [apply Htop; [done|by destruct l1]|].
      right. apply (slt_rpt Ψ Θ B HB). intros v ts _. rewrite !(den_hi Ψ Θ B HB).
      rewrite !hlen_notop by set_solver. apply hi_hi.
      + rewrite !xmaxl_app. eapply xle_trans; [apply xle_max_l|apply xle_max_r].
      + by apply xmaxl_notop.
      + rewrite !length_app. destruct l1, l2; simpl in *; try lia. naive_solver.
    - exists (rpt B (RHi ef')). split; [by apply Hz|]. right.
      apply (slt_rpt Ψ Θ B HB). intros v ts Hv. rewrite !(den_hi Ψ Θ B HB).
      apply hi_hi_lt. by apply (Hs v ts).
  Qed.

  Lemma ubs_hle Φ ef ef' F :
    hle Θ ef ef' → ub_below_s Wmp Ψ Φ (hiz B ef') F → ub_below_s Wmp Ψ Φ (hiz B ef) F.
  Proof. intros Hle. apply (ubs_lower Wmp Wmp_wf). intros x Hx. by apply (hi_le ef ef' x). Qed.

  Lemma hle_seg ef l1 l2 : hle Θ ef (l1 ++ ef ++ l2).
  Proof. right; right; left. by exists l1, l2. Qed.

  Lemma envp_seg Γ t : Some t ∈ Γ → ∃ l1 l2, envp Γ = l1 ++ tprios t ++ l2.
  Proof.
    induction Γ as [|o Γ IH]; intros Ht; [by apply elem_of_nil in Ht|].
    apply elem_of_cons in Ht as [<-|Ht]; simpl.
    - by exists [], (envp Γ).
    - destruct (IH Ht) as (l1 & l2 & ->). destruct o as [t'|].
      + exists (tprios t' ++ l1), l2. by rewrite app_assoc.
      + by exists l1, l2.
  Qed.

  Lemma envp_in Γ t i : Some t ∈ Γ → i ∈ tprios t → i ∈ envp Γ.
  Proof. intros Ht Hi. destruct (envp_seg Γ t Ht) as (l1 & l2 & ->). set_solver. Qed.

  (** An upper point below every head of the environment. *)
  Lemma env_hi_below ss pts ins Γ Δ ef x h :
    erel B ss pts ins Γ Δ → plt Θ ef (envp Γ) → hiz B ef = Some x → h ∈ lenv_heads Δ → slt Wmp Ψ x h.
  Proof.
    intros H Hlt Hx Hh. destruct (erel_heads _ _ _ _ _ _ _ H Hh) as (t & Ht & Hh').
    destruct ef as [|ρ0 ef0]; [done|]. injection Hx as <-.
    destruct Hlt as [Hn|Hlt]; [done|].
    assert (∀ i, i ∈ tprios t → ∀ v ts, models Θ v ts → xlt (xmaxl v (ρ0 :: ef0)) (evlb v ts i)) as Hl.
    { intros i Hi v ts Hv. apply (Hlt v ts Hv). by apply (envp_in Γ t). }
    destruct t as [|p Q [hh d|n w]|p Q|T lo ef' V|Θ' T ef' V|p k Qa Qr]; simpl in Hh'; try set_solver.
    - apply elem_of_singleton in Hh' as ->. apply (slt_rpt Ψ Θ B HB).
      intros v ts Hv. rewrite (den_hi Ψ Θ B HB), (rank_ch Ψ Θ B HB). apply hi_chan.
      apply (Hl (LC Q hh d)); [by left|done].
    - exfalso. destruct (gd_inh _ _ _ HB) as (v & ts & Hv).
      specialize (Hl (LP PBot) (list_elem_of_here _ _) v ts Hv). exact (xlt_bot _ Hl).
    - exfalso. destruct (gd_inh _ _ _ HB) as (v & ts & Hv).
      specialize (Hl (LP PBot) (list_elem_of_here _ _) v ts Hv). exact (xlt_bot _ Hl).
    - apply elem_of_singleton in Hh' as ->. apply (slt_rpt Ψ Θ B HB).
      intros v ts Hv. rewrite (den_hi Ψ Θ B HB), (den_lo Ψ Θ B HB). apply hi_lo.
      intros i Hi. by apply Hl.
  Qed.
End heads.

Section heads2.
  Context (Ψ : hyps) (Θ : pctx) (B : point) (HB : good Ψ Θ B).

  Lemma hi_below_lo ef lo x :
    plt Θ ef lo → hiz B ef = Some x → slt Wmp Ψ x (rpt B (RLo lo)).
  Proof.
    intros Hlt Hx. destruct ef as [|ρ0 ef0]; [done|]. injection Hx as <-.
    destruct Hlt as [Hn|Hlt]; [done|].
    apply (slt_rpt Ψ Θ B HB). intros v ts Hv.
    rewrite (den_hi Ψ Θ B HB), (den_lo Ψ Θ B HB). apply hi_lo. by apply Hlt.
  Qed.

  Lemma hi_below_ch ef Q h d x :
    plt Θ ef [LC Q h d] → hiz B ef = Some x → slt Wmp Ψ x (rpt B (RCh Q h d)).
  Proof.
    intros Hlt Hx. destruct ef as [|ρ0 ef0]; [done|]. injection Hx as <-.
    destruct Hlt as [Hn|Hlt]; [done|].
    apply (slt_rpt Ψ Θ B HB). intros v ts Hv.
    rewrite (den_hi Ψ Θ B HB), (rank_ch Ψ Θ B HB). apply hi_chan. exact (Hlt v ts Hv (LC Q h d) (list_elem_of_here _ _)).
  Qed.

  Lemma lo_floor l : LP PBot ∈ l → sle Wmp Ψ (rpt B (RLo l)) (floor B).
  Proof.
    intros Hl. assert (∀ v ts, xminlb v ts l = XB) as Hm.
    { intros v ts. pose proof (xminlb_le v ts l _ Hl) as H. simpl in H. by destruct (xminlb v ts l). }
    destruct l as [|i [|i' l']]; [by apply elem_of_nil in Hl| |].
    - apply list_elem_of_singleton in Hl as <-. left. apply se_refl.
    - right. apply (slt_rpt Ψ Θ B HB). intros v ts _. rewrite !(den_lo Ψ Θ B HB), Hm. simpl. lia.
  Qed.

  Lemma sle_slt x y z : sle Wmp Ψ x y → slt Wmp Ψ y z → slt Wmp Ψ x z.
  Proof. intros [H|H] H'; [by eapply slt_seqs_l|by eapply sl_trans]. Qed.

  Lemma env_lo_below ss pts ins Γ Δ h :
    pts_ok Ψ B pts → erel B ss pts ins Γ Δ → h ∈ lenv_heads Δ → sle Wmp Ψ (rpt B (RLo (envp Γ))) h.
  Proof.
    intros Hp H Hh. destruct (erel_heads _ _ _ _ _ _ _ H Hh) as (t & Ht & Hh').
    destruct t as [|p Q [hh d|n w]|p Q|T lo ef' V|Θ' T ef' V|p k Qa Qr]; simpl in Hh'; try set_solver.
    - apply elem_of_singleton in Hh' as ->. right. apply (slt_rpt Ψ Θ B HB). intros v ts Hv.
      rewrite (den_lo Ψ Θ B HB), (rank_ch Ψ Θ B HB).
      assert (LC Q hh d ∈ envp Γ) as Hi by (apply (envp_in Ψ Θ B HB Γ (MCh p Q (PR hh d))); [done|by left]).
      destruct (envp Γ) as [|i0 l0] eqn:E; [by apply elem_of_nil in Hi|]. simpl length.
      apply lo_chan. by apply (xminlb_le v ts (i0 :: l0) (LC Q hh d)).
    - apply elem_of_singleton in Hh' as ->. right. eapply sle_slt; [apply lo_floor|apply (Hp n)].
      apply (envp_in Ψ Θ B HB Γ (MCh p Q (PX n w))); [done|by left].
    - apply elem_of_singleton in Hh' as ->. apply lo_floor.
      apply (envp_in Ψ Θ B HB Γ (MEx p Q)); [done|by left].
    - apply elem_of_singleton in Hh' as ->.
      destruct (envp_seg Ψ Θ B HB Γ _ Ht) as (l1 & l2 & E). simpl in E.
      destruct (decide (l1 = [] ∧ l2 = [])) as [[-> ->]|Hl].
      { rewrite E, app_nil_r. left. apply se_refl. }
      right. apply (slt_rpt Ψ Θ B HB). intros v ts Hv.
      rewrite !(den_lo Ψ Θ B HB). rewrite E. apply lo_lo.
      + rewrite !xminlb_app. eapply xle_trans; [apply xmin_le_r|apply xmin_le_l].
      + rewrite !length_app. destruct l1, l2; simpl in *; try lia. naive_solver.
  Qed.

  Lemma ubs_part Φ F l1 l2 ef1 ss pts ins Γ2 Δ2 :
    ub_below_s Wmp Ψ Φ (hiz B (l1 ++ ef1 ++ l2)) F → plt Θ ef1 (envp Γ2) → erel B ss pts ins Γ2 Δ2 →
    ub_below_s Wmp Ψ Φ (hiz B ef1) (sf_union F (lenv_heads Δ2)).
  Proof.
    intros HF Hl HΔ. apply (ubs_union _ Wmp_wf).
    - by apply (ubs_hle Ψ Θ B HB _ _ _ _ (hle_seg Ψ Θ B HB ef1 l1 l2)).
    - intros x Hx h Hh. by apply (env_hi_below Ψ Θ B HB ss pts ins Γ2 Δ2 ef1 x h).
  Qed.

  Lemma ubs_seg Φ F ef l1 l2 :
    ub_below_s Wmp Ψ Φ (hiz B (l1 ++ ef ++ l2)) F → ub_below_s Wmp Ψ Φ (hiz B ef) F.
  Proof. apply (ubs_hle Ψ Θ B HB), (hle_seg Ψ Θ B HB). Qed.

  (** A point below the ceiling lies below the frame of an effect with ⊤. *)
  Lemma ubs_ceil Φ F ef x :
    PTop ∈ ef → slt Wmp Ψ x (ceil B) → ub_below_s Wmp Ψ Φ (hiz B ef) F → ub_below_s Wmp Ψ Φ (Some x) F.
  Proof.
    intros Ht Hx. apply (ubs_lower Wmp Wmp_wf). intros y [=<-].
    exists (rpt B (RHi ef)). split; [destruct ef; [by apply elem_of_nil in Ht|done]|].
    right. eapply slt_seqs_r; [exact Hx|]. by apply (ceil_top Ψ Θ B HB).
  Qed.
End heads2.

(** ** Channels at a sequence *)

Definition mclosep (v : val) (ts : list msty) (P : mpay) : mpay := tsubp ts (mmapp (pclose v) P).

Lemma rank_dch Q h d : rank (DCh Q h d) = xrk (hext (vprio (hdt h d Q).1)) 1 (KT 1).
Proof. done. Qed.

Lemma hdt_snd v ts h d a P K :
  hdt h d (mclose v ts (MSeq (MSnd a P) K)) = (Some (VSnd (pclose v a) (mclosep v ts P) (mclose v ts K)), h).
Proof. done. Qed.
Lemma hdt_rcv v ts h d a P K :
  hdt h d (mclose v ts (MSeq (MRcv a P) K)) = (Some (VRcv (pclose v a) (mclosep v ts P) (mclose v ts K)), h).
Proof. done. Qed.
Lemma hdt_sel v ts h d a K1 K2 :
  hdt h d (mclose v ts (MSel a K1 K2)) = (Some (VSel (pclose v a) (mclose v ts K1) (mclose v ts K2)), h).
Proof. done. Qed.
Lemma hdt_bra v ts h d a K1 K2 :
  hdt h d (mclose v ts (MBra a K1 K2)) = (Some (VBra (pclose v a) (mclose v ts K1) (mclose v ts K2)), h).
Proof. done. Qed.
Lemma hdt_end v ts h d a w :
  hdt h d (mclose v ts (MEnd a w)) = (Some (VEnd (pclose v a)), h).
Proof. done. Qed.

(** The head shapes and their priority. *)
Definition hshape (Q : msty) (a : prio) : Prop :=
  ∀ v ts h d, vprio (hdt h d (mclose v ts Q)).1 = Some (pclose v a).

Lemma hshape_snd pol a P K : hshape (sndQ pol a P K) a.
Proof. intros v ts h d. destruct pol; done. Qed.
Lemma hshape_rcv pol a P K : hshape (rcvQ pol a P K) a.
Proof. intros v ts h d. destruct pol; done. Qed.
Lemma hshape_sel pol a K1 K2 : hshape (selQ pol a K1 K2) a.
Proof. intros v ts h d. destruct pol; done. Qed.
Lemma hshape_bra pol a K1 K2 : hshape (braQ pol a K1 K2) a.
Proof. intros v ts h d. destruct pol; done. Qed.
Lemma hshape_end a w : hshape (MEnd a w) a.
Proof. intros v ts h d. done. Qed.

Lemma pt_root_shift x n : pt_root (pt_shift n x) = pt_root x.
Proof. done. Qed.
Lemma pt_root_slot x i : pt_root (pt_slot x i) = pt_root x.
Proof. done. Qed.

Lemma plt_single Θ a l v ts : plt Θ [a] [l] → models Θ v ts → xlt (evalp v a) (evlb v ts l).
Proof.
  intros [H|H] Hv; [done|]. specialize (H v ts Hv l (list_elem_of_here _ _)).
  by rewrite xmaxl_single in H.
Qed.

Section chan.
  Context (Ψ : hyps) (Θ : pctx) (B : point) (HB : good Ψ Θ B).

  Lemma rank_x Q a h d v ts : hshape Q a →
    rank (den (ianc B v ts) (rpt B (RCh Q h d))) = xrk (evalp v a) 1 (KT 1).
  Proof. intros Ha. rewrite (den_ch Ψ Θ B HB), rank_dch, Ha. simpl. by rewrite evalp_pclose. Qed.

  Lemma ch_next pol a P K Q h d :
    (Q = sndQ pol a P K ∨ Q = rcvQ pol a P K) → plt Θ [a] [LC K h d] →
    seqs Wmp Ψ (pt_shift 1 (rpt B (RCh Q h d))) (rpt B (RCh K h d)).
  Proof.
    intros HQ Hr. apply (gd_eq _ _ _ HB); [rewrite pt_root_shift; by apply rpt_root, HB|by apply rpt_root, HB|].
    intros v ts Hv. rewrite den_shift, !(den_ch Ψ Θ B HB). unfold dsh, guard.
    assert (dnext (DCh (mclose v ts Q) (pclose v h) d) = DCh (mclose v ts K) (pclose v h) d) as ->.
    { destruct HQ as [->| ->]; destruct pol; done. }
    rewrite decide_True; [apply oeq_refl|].
    assert (hshape Q a) as Ha by (destruct HQ as [->| ->]; [apply hshape_snd|apply hshape_rcv]).
    rewrite <-(den_ch Ψ Θ B HB), (rank_x Q a) by done. rewrite rank_dch.
    apply xrk_lt. exact (plt_single Θ a (LC K h d) v ts Hr Hv).
  Qed.

  Lemma ch_branch pol a K1 K2 Q h d b :
    (Q = selQ pol a K1 K2 ∨ Q = braQ pol a K1 K2) → plt Θ [a] [LC K1 h d; LC K2 h d] →
    seqs Wmp Ψ (pt_slot (rpt B (RCh Q h d)) (bidx b)) (rpt B (RCh (if b then K2 else K1) h d)).
  Proof.
    intros HQ Hr. apply (gd_eq _ _ _ HB); [rewrite pt_root_slot; by apply rpt_root, HB|by apply rpt_root, HB|].
    intros v ts Hv. rewrite den_slot, !(den_ch Ψ Θ B HB).
    assert (dsl (DCh (mclose v ts Q) (pclose v h) d) (bidx b) =
            guard (DCh (mclose v ts Q) (pclose v h) d) (DCh (mclose v ts (if b then K2 else K1)) (pclose v h) d)) as ->.
    { destruct HQ as [->| ->]; destruct pol, b; done. }
    unfold guard.
    rewrite decide_True; [apply oeq_refl|].
    assert (hshape Q a) as Ha by (destruct HQ as [->| ->]; [apply hshape_sel|apply hshape_bra]).
    rewrite <-(den_ch Ψ Θ B HB), (rank_x Q a) by done. rewrite rank_dch.
    apply xrk_lt. destruct Hr as [Hn|Hr]; [done|].
    specialize (Hr v ts Hv (LC (if b then K2 else K1) h d)). rewrite xmaxl_single in Hr.
    apply Hr. destruct b; set_solver.
  Qed.

  (** The payload lies above its message, so the payload slot is the
      point of the payload channel. *)
  Lemma ch_pay pol a pp Qp hp dp K Q h d :
    (Q = sndQ pol a (MPChan pp Qp hp dp) K ∨ Q = rcvQ pol a (MPChan pp Qp hp dp) K) →
    plt Θ [a] [LC Qp hp dp] →
    seqs Wmp Ψ (pt_slot (rpt B (RCh Q h d)) 0) (rpt B (RCh Qp hp dp)).
  Proof.
    intros HQ Hl. apply (gd_eq _ _ _ HB); [rewrite pt_root_slot; by apply rpt_root, HB|by apply rpt_root, HB|].
    intros v ts Hv. rewrite den_slot, !(den_ch Ψ Θ B HB).
    assert (dsl (DCh (mclose v ts Q) (pclose v h) d) 0 =
            guard (DCh (mclose v ts Q) (pclose v h) d) (DCh (mclose v ts Qp) (pclose v hp) dp)) as ->.
    { destruct HQ as [->| ->]; destruct pol; done. }
    unfold guard. rewrite decide_True; [apply oeq_refl|].
    assert (hshape Q a) as Ha by (destruct HQ as [->| ->]; [apply hshape_snd|apply hshape_rcv]).
    rewrite <-!(den_ch Ψ Θ B HB), (rank_x Q a), (rank_ch Ψ Θ B HB) by done. apply xrk_lt.
    exact (plt_single Θ a (LC Qp hp dp) v ts Hl Hv).
  Qed.

  Lemma ch_below_hi Q a h d ef :
    hshape Q a → pfin a → a ∈ ef → slt Wmp Ψ (rpt B (RCh Q h d)) (rpt B (RHi ef)).
  Proof.
    intros Ha Hf Hin. apply (slt_rpt Ψ Θ B HB). intros v ts Hv.
    rewrite (rank_x Q a) by done. rewrite (den_hi Ψ Θ B HB). rewrite <-(evalp_pclose v a).
    apply ch_hi; [by destruct a|]. rewrite evalp_pclose. by apply xmaxl_in.
  Qed.

  Lemma ch_ub Φ Q a h d ef F :
    hshape Q a → pfin a → a ∈ ef → ub_below_s Wmp Ψ Φ (hiz B ef) F →
    ub_below_s Wmp Ψ Φ (Some (rpt B (RCh Q h d))) F.
  Proof.
    intros Ha Hf Hin. apply (ubs_lower Wmp Wmp_wf). intros y [=<-].
    exists (rpt B (RHi ef)). split; [by destruct ef; [by apply elem_of_nil in Hin|]|].
    right. by apply (ch_below_hi Q a).
  Qed.

  Lemma ch_below_ch Q a h d Qp hp dp :
    hshape Q a → plt Θ [a] [LC Qp hp dp] → slt Wmp Ψ (rpt B (RCh Q h d)) (rpt B (RCh Qp hp dp)).
  Proof.
    intros Ha Hl. apply (slt_rpt Ψ Θ B HB). intros v ts Hv.
    rewrite (rank_x Q a), (rank_ch Ψ Θ B HB) by done. apply xrk_lt.
    exact (plt_single Θ a (LC Qp hp dp) v ts Hl Hv).
  Qed.
End chan.

(** ** Forcing at an anchor *)

Lemma evalp_psub v σ ρ : Forall pfin σ → evalp (evalZ v <$> σ) ρ = evalp v (psub σ ρ).
Proof.
  intros Hσ. destruct ρ as [| | |j n|]; simpl; try done.
  rewrite list_lookup_fmap. destruct (σ !! j) as [s|] eqn:E; simpl; [|done].
  apply (Forall_lookup_1 _ _ _ _ Hσ) in E. destruct s; simpl in E; try done; unfold evalZ; cbn; f_equal; lia.
Qed.

Lemma pclose_psub v σ ρ : Forall pfin σ → pclose (evalZ v <$> σ) ρ = pclose v (psub σ ρ).
Proof.
  intros Hσ. destruct ρ as [| | |j n|]; simpl; try done.
  rewrite list_lookup_fmap. destruct (σ !! j) as [s|] eqn:E; simpl; [|done].
  apply (Forall_lookup_1 _ _ _ _ Hσ) in E. destruct s; simpl in E; try done; unfold evalZ; cbn; f_equal; lia.
Qed.

Lemma psub_top σ ρ : Forall pfin σ → psub σ ρ = PTop ↔ ρ = PTop.
Proof.
  intros Hσ. destruct ρ as [| | |j n|]; simpl; try done.
  destruct (σ !! j) as [s|] eqn:E; simpl; [|done].
  apply (Forall_lookup_1 _ _ _ _ Hσ) in E. by destruct s.
Qed.

Lemma xmaxl_psub v σ l : Forall pfin σ → xmaxl (evalZ v <$> σ) l = xmaxl v (psub σ <$> l).
Proof. intros Hσ. induction l; simpl; [done|]. by rewrite IHl, evalp_psub. Qed.

Lemma hlen_psub σ l : Forall pfin σ → hlen (psub σ <$> l) = hlen l.
Proof.
  intros Hσ. unfold hlen. rewrite length_fmap.
  assert (PTop ∈ psub σ <$> l ↔ PTop ∈ l) as E.
  { rewrite list_elem_of_fmap. split; [intros (ρ & Hρ & Hin); symmetry in Hρ;
      apply (psub_top σ ρ Hσ) in Hρ; by subst|intros Hin; by exists PTop]. }
  by rewrite (bool_decide_ext _ _ E).
Qed.

Lemma mmap_comp f g : (∀ Q, mmap f (mmap g Q) = mmap (f ∘ g) Q) ∧
                      (∀ P, mmapp f (mmapp g P) = mmapp (f ∘ g) P).
Proof. apply msty_mpay_mut; intros; simpl; congruence. Qed.

Lemma mmap_ext f g : (∀ ρ, f ρ = g ρ) →
  (∀ Q, mmap f Q = mmap g Q) ∧ (∀ P, mmapp f P = mmapp g P).
Proof. intros H. apply msty_mpay_mut; intros; simpl; congruence. Qed.

Fixpoint rclosed_mmap f (Q : msty) : rclosed Q → rclosed (mmap f Q).
Proof.
  destruct Q as [| A B | a [|pp Qp hp dp] | a [|pp Qp hp dp] | a A B | a A B | a w | Q0 | | j];
    simpl; try done; intros H; repeat match goal with H : _ ∧ _ |- _ => destruct H end;
    try split; by apply rclosed_mmap.
Qed.

Fixpoint rbody_mmap f (Q : msty) : rbody Q → rbody (mmap f Q).
Proof.
  destruct Q as [| A B | a [|pp Qp hp dp] | a [|pp Qp hp dp] | a A B | a A B | a w | Q0 | | j];
    simpl; try done; intros H; repeat match goal with H : _ ∧ _ |- _ => destruct H end;
    try split; try by apply rbody_mmap. all: by apply rclosed_mmap.
Qed.

Fixpoint msc_mmap f k (Q : msty) : msc k Q → msc k (mmap f Q).
Proof.
  destruct Q as [| A B | a [|pp Qp hp dp] | a [|pp Qp hp dp] | a A B | a A B | a w | Q0 | | j];
    simpl; try done; intros H; repeat match goal with H : _ ∧ _ |- _ => destruct H end;
    try split; try by apply msc_mmap. by apply rbody_mmap.
Qed.

(** Closing an instance is instantiating the closed caller. *)
Fixpoint mclose_msq (Q : msty) : ∀ v ts σ τ, Forall pfin σ → msc (length τ) Q →
  mclose (evalZ v <$> σ) (mclose v ts <$> τ) Q = mclose v ts (msq σ τ Q).
Proof.
  intros v ts σ τ Hσ HQ. unfold mclose, msq.
  destruct Q as [| A B | a P | a P | a A B | a A B | a w | S0 | | j]; simpl in *.
  - done.
  - destruct HQ. f_equal; by apply mclose_msq.
  - rewrite pclose_psub by done. f_equal. destruct P as [|pp Qp hp dp]; [done|]. simpl.
    rewrite pclose_psub by done. f_equal. by apply mclose_msq.
  - rewrite pclose_psub by done. f_equal. destruct P as [|pp Qp hp dp]; [done|]. simpl.
    rewrite pclose_psub by done. f_equal. by apply mclose_msq.
  - destruct HQ. rewrite pclose_psub by done. f_equal; by apply mclose_msq.
  - destruct HQ. rewrite pclose_psub by done. f_equal; by apply mclose_msq.
  - by rewrite pclose_psub.
  - rewrite (tsub_rbody τ (mmap (psub σ) S0)) by (by apply rbody_mmap).
    rewrite !tsub_rbody by (by repeat apply rbody_mmap). f_equal.
    rewrite (proj1 (mmap_comp _ _)). apply mmap_ext. intros ρ. simpl. by rewrite pclose_psub.
  - done.
  - rewrite list_lookup_fmap. destruct (lookup_lt_is_Some_2 τ j HQ) as [q Hq]. by rewrite Hq.
Qed.

Section anc.
  Context (Ψ : hyps) (Θ : pctx) (B : point) (HB : good Ψ Θ B) (σ : list prio) (τ : list msty).
  Context (Hσ : Forall pfin σ).
  Abbreviation X := (rpt B (RAnc σ τ)).

  Lemma rpt_X_root r : pt_root (rpt X r) = pt_name B.
  Proof. unfold rpt. rewrite pt_root_slot. by apply rpt_root, HB. Qed.

  Lemma den_X_slot v ts r : den (ianc B v ts) (rpt X r) = dsl (DAnc (evalZ v <$> σ) (mclose v ts <$> τ)) (encode_nat r).
  Proof. unfold rpt at 1. by rewrite den_slot, (den_anc Ψ Θ B HB). Qed.

  Lemma seqs_X r r' :
    (∀ v ts, models Θ v ts → oeq (den (ianc B v ts) (rpt X r)) (den (ianc B v ts) (rpt B r'))) →
    seqs Wmp Ψ (rpt X r) (rpt B r').
  Proof. intros H. apply (gd_eq _ _ _ HB); [apply rpt_X_root|by apply rpt_root, HB|done]. Qed.

  Lemma hiz_anc ef : opt_rel (seqs Wmp Ψ) (hiz X ef) (hiz B (psub σ <$> ef)).
  Proof.
    destruct ef as [|ρ ef]; simpl; [done|]. apply seqs_X. intros v ts _.
    rewrite den_X_slot, (den_hi Ψ Θ B HB). simpl. rewrite decode_encode_nat.
    rewrite xmaxl_psub by done. pose proof (hlen_psub σ (ρ :: ef) Hσ) as E. simpl in E. rewrite E.
    apply oeq_refl.
  Qed.

  Lemma anc_ch Q h d : msc (length τ) Q → seqs Wmp Ψ (rpt X (RCh Q h d)) (rpt B (RCh (msq σ τ Q) (psub σ h) d)).
  Proof.
    intros HQ. apply seqs_X. intros v ts _. rewrite den_X_slot, (den_ch Ψ Θ B HB). simpl.
    rewrite decode_encode_nat, mclose_msq, pclose_psub by done. apply oeq_refl.
  Qed.

  Lemma evlb_lsub v ts l :
    (match l with LC Q _ _ => msc (length τ) Q | _ => True end) →
    evlb (evalZ v <$> σ) (mclose v ts <$> τ) l = evlb v ts (lsub σ τ l).
  Proof.
    destruct l as [ρ|Q h d]; simpl; intros HQ; [by apply evalp_psub|].
    unfold cprio. by rewrite mclose_msq, pclose_psub.
  Qed.

  Lemma anc_lo lo : Forall (λ l, match l with LC Q _ _ => msc (length τ) Q | _ => True end) lo →
    seqs Wmp Ψ (rpt X (RLo lo)) (rpt B (RLo (lsub σ τ <$> lo))).
  Proof.
    intros Hl. apply seqs_X. intros v ts _. rewrite den_X_slot, (den_lo Ψ Θ B HB). simpl.
    rewrite decode_encode_nat, length_fmap.
    assert (xminlb (evalZ v <$> σ) (mclose v ts <$> τ) lo = xminlb v ts (lsub σ τ <$> lo)) as ->; [|apply oeq_refl].
    induction Hl as [|l lo Hl1 Hl2 IH]; simpl; [done|]. by rewrite IH, evlb_lsub.
  Qed.

  Lemma tr_anc ss pts pts' T : tpure (length τ) T →
    steq Wmp Ψ (sinst_ty (slist ((λ q, sinst (slist ss) (ers q)) <$> τ)) (tr X pts' T)) (trs ss B pts (msub σ τ T)) ∧
    steq Wmp Ψ (trs ss B pts (msub σ τ T)) (sinst_ty (slist ((λ q, sinst (slist ss) (ers q)) <$> τ)) (tr X pts' T)).
  Proof.
    unfold trs. induction T as [|p Q [h d|n w]| p Q |T IH1 lo ef V IH2|Θ' T IH1 ef V IH2|p k Qa Qr];
      simpl; intros HT; try done.
    - assert (sinst (slist ((λ q, sinst (slist ss) (ers q)) <$> τ)) (polS p (ers Q)) =
              sinst (slist ss) (polS p (ers (msq σ τ Q)))) as E.
      { rewrite !polS_sinst. f_equal. unfold msq. rewrite ers_tsub by (by apply msc_mmap).
        by rewrite (proj1 (ers_mmap _)). }
      rewrite E. pose proof (anc_ch Q h d HT). split; (split; [|apply seq_refl]); [done|by apply se_sym].
    - destruct HT as (H1 & H2 & H3). destruct (IH1 H1) as [A1 A2], (IH2 H2) as [B1 B2].
      pose proof (hiz_anc ef) as Eh. pose proof (anc_lo lo H3) as El.
      split; split_and!; try done.
      + destruct (hiz X ef), (hiz B (psub σ <$> ef)); simpl in *; try done. by apply se_sym.
      + by apply se_sym.
    - pose proof (tr_closed (slist ((λ q, sinst (slist ss) (ers q)) <$> τ)) X pts' (MPoly Θ' T ef V) I HT) as E1.
      pose proof (tr_closed (slist ss) B pts (MPoly Θ' T ef V) I HT) as E2.
      simpl in E1, E2. rewrite E1, E2. split; apply teq_refl.
    - pose proof (tr_closed (slist ((λ q, sinst (slist ss) (ers q)) <$> τ)) X pts' (MSeg p k Qa Qr) I HT) as E1.
      pose proof (tr_closed (slist ss) B pts (MSeg p k Qa Qr) I HT) as E2.
      simpl in E1, E2. rewrite E1, E2. split; apply teq_refl.
  Qed.

  (** A box forced at X meets its constraint when the instance meets Θ′. *)
  Lemma crel_hold Θ' : (∀ v ts, models Θ v ts → models Θ' (evalZ v <$> σ) (mclose v ts <$> τ)) →
    bcs_hold (seqs Wmp Ψ) (slt Wmp Ψ) (Crel Θ') [X].
  Proof.
    intros Hm g Hg. apply bcs_open_nil in Hg as [Hg _].
    assert (∀ x, pt_root x = NVar 0 → pt_root (pt_inst (plist [X]) x) = pt_name B) as Hr.
    { intros x Hx. rewrite pt_root_inst, Hx. change (pt_root (rpt B (RAnc σ τ)) = pt_name B). by apply rpt_root, HB. }
    assert (∀ v ts x, pt_root x = NVar 0 →
      den (ianc B v ts) (pt_inst (plist [X]) x) = den (ianc (Pt (NVar 0) 0) (evalZ v <$> σ) (mclose v ts <$> τ)) x) as Hd.
    { intros v ts x Hx. apply (den_inst _ _ _ 0); [done|].
      change (plist [X] 0) with X. rewrite (den_anc Ψ Θ B HB).
      unfold ianc. by rewrite decide_True. }
    destruct g as [x y|x y]; simpl in *; destruct Hg as (Hx & Hy & E).
    - apply (gd_lt _ _ _ HB); [by apply Hr|by apply Hr|]. intros v ts Hv.
      rewrite !Hd by done. by apply E, Hm.
    - apply (gd_eq _ _ _ HB); [by apply Hr|by apply Hr|]. intros v ts Hv.
      rewrite !Hd by done. by apply E, Hm.
  Qed.

  Lemma anc_known : Forall (skn Wmp Ψ) [X].
  Proof. apply Forall_singleton. by apply (rpt_known Ψ Θ B HB). Qed.
End anc.

(** ** Forcing at a segment *)

Lemma pt_inst_plist2_0 x B : pt_inst (plist [x; B]) (pvar 0) = x.
Proof. apply pt_inst_pvar_at. Qed.
Lemma pt_inst_plist2_1 x B : pt_inst (plist [x; B]) (pvar 1) = B.
Proof. apply pt_inst_pvar_at. Qed.

Lemma cseg_hold Ψ Θ B k x : good Ψ Θ B →
  (∀ u, slt Wmp Ψ (mwalk x u) (ceil B) ∧ slt Wmp Ψ (floor B) (mwalk x u)) →
  (∀ u i, slt Wmp Ψ (mwalk x u) (pt_slot (mwalk x u) i)) →
  bcs_hold (seqs Wmp Ψ) (slt Wmp Ψ) (Cseg k) [x; B].
Proof.
  intros HB Hx Hx' g Hg. apply bcs_open_nil in Hg as [Hg _]. destruct Hg as [[(u & ->)|[(u & ->)|(u & i & ->)]]|Hc].
  - simpl. rewrite pt_inst_mwalk, pt_inst_plist2_0, pt_inst_rpt, pt_inst_plist2_1. apply Hx.
  - simpl. rewrite pt_inst_mwalk, pt_inst_plist2_0, pt_inst_rpt, pt_inst_plist2_1. apply Hx.
  - simpl. rewrite pt_inst_slot, pt_inst_mwalk, pt_inst_plist2_0. apply Hx'.
  - assert (∀ y, pt_root y = NVar 1 → pt_root (pt_inst (plist [x; B]) y) = pt_name B) as Hr.
    { intros y Hy. rewrite pt_root_inst, Hy. simpl. destruct (gd_isroot _ _ _ HB) as [Ho Hrt].
      unfold pt_root. done. }
    assert (∀ v ts y, pt_root y = NVar 1 →
      den (ianc B v ts) (pt_inst (plist [x; B]) y) = den (ianc (Pt (NVar 1) 0) v ts) y) as Hd.
    { intros v ts y Hy. apply (den_inst _ _ _ 1); [done|].
      change (plist [x; B] 1) with B. rewrite den_ianc by apply HB.
      unfold ianc. by rewrite decide_True. }
    destruct g as [y z|y z]; simpl in *; destruct Hc as (Hy & Hz & E).
    + apply (gd_lt _ _ _ HB); [by apply Hr|by apply Hr|]. intros v ts _.
      rewrite !Hd by done. by apply E.
    + apply (gd_eq _ _ _ HB); [by apply Hr|by apply Hr|]. intros v ts _.
      rewrite !Hd by done. by apply E.
Qed.

(** ** fork *)

Lemma rename_fork r : rename r fork_tr = fork_tr.
Proof. done. Qed.
Lemma rename_unitv r : rename r unitv = unitv.
Proof. done. Qed.

Lemma fork_tr_typed Φ Ψ Δ0 F ub lb :
  lenv_empty Δ0 →
  typed Wmp Φ Ψ ∅ Δ0 F fork_tr (TLolli None None (TLolli ub lb U U) U).
Proof.
  intros HΔ. pose proof Wmp_wf as HW. set (φ0 := fresh (dom Φ)).
  apply (t_lam Wmp Φ Ψ ∅ Δ0 F _ _ _ None None φ0); [apply is_fresh|lbhb|].
  { simpl. by bclean; rewrite (tenv_heads0 Wmp HW), empty_heads, union_empty_l_L. }
  set (Φ1 := <[φ0 := None]> Φ).
  set (fT := TLolli ub lb U U).
  set (E := Some fT :: Δ0).
  eapply (t_letu Wmp Φ1 Ψ ∅ ∅ ∅ E E (lenv_nones E)); [by apply comp0|apply lenv_split_nones_r| |].
  2:{ apply tv_unitv; [done|apply nones_unl]. }
  eapply (t_app Wmp Φ1 Ψ ∅ ∅ ∅ E (lenv_nones E) E _ _ _ None None (TLolli ub lb TUnit TUnit)).
  { by apply comp0. } { apply lenv_split_nones_l. } { done. }
  { apply t_konst; [apply lenv_empty_nones|apply KTSpawn|done]. }
  set (φ := fresh (dom Φ1)).
  apply (t_lam Wmp Φ1 Ψ ∅ E _ _ _ _ ub lb φ); [apply is_fresh|lbhb|].
  { simpl. bclean; rewrite (tenv_heads0 Wmp HW), empty_heads by done. destruct lb as [l|]; simpl; [|set_solver].
    intros y Hy. assert (y = l) as -> by set_solver. left. apply se_refl. }
  set (Φ2 := <[φ := ub]> Φ1).
  eapply (t_letu Wmp Φ2 Ψ ∅ ∅ ∅ _ (Some TUnit :: None :: Δ0) (None :: Some fT :: Δ0));
    [by apply comp0| | |].
  { constructor. constructor. by apply lenv_split_empty'. }
  { apply tv_var_unl; [done|done|]. intros y T Hne Hy. destruct y as [|[|y]]; simpl in Hy; try done.
    exfalso. by eapply empty_lookup. }
  assert (ub_below_s Wmp Ψ Φ2 ub (∅, Some (FVar φ))) as Hub by apply (ubs_fresh _ HW).
  eapply (typed_force0 Wmp Φ2 Ψ ∅ _ _ _ 0 (BCs [] (λ _, False)) None TUnit []); [done|done| |done|done|].
  { intros g Hg. apply bcs_open_nil in Hg as [[] _]. }
  eapply (t_app Wmp Φ2 Ψ ∅ ∅ ∅ _ (None :: Some fT :: Δ0) (lenv_nones (None :: Some fT :: Δ0))
            _ _ _ ub lb U U).
  { by apply comp0. } { apply lenv_split_nones_r. } { done. }
  { apply tv_var_unl; [done|done|]. intros y T Hne Hy. destruct y as [|[|y]]; simpl in Hy; try done.
    exfalso. by eapply empty_lookup. }
  { apply tv_unitv; [done|apply nones_unl]. }
Qed.

(** ** Opening the end point of a segment *)

Lemma hyps_hold_sub W Ψ0 Ψ' :
  (∀ h, h ∈ Ψ0 → h ∈ Ψ') → hyps_hold (seqs W Ψ') (slt W Ψ') (skn W Ψ') Ψ0.
Proof.
  intros Hs C xs Hin. specialize (Hs _ Hin). split.
  - intros g Hg. destruct g as [x y|x y]; simpl; [apply sl_h|apply se_h];
      exists C, xs; (split; [done|]); [exists (FLt x y)|exists (FEq x y)]; by split.
  - apply Forall_forall. intros y Hy%list_elem_of_In. right. exists C, xs, y. split; [exact Hs|]. split; [exact Hy|done].
Qed.

Section shift.
  Context (Ψ Ψ' : hyps) (Θ : pctx) (B : point) (HB : good Ψ Θ B).
  Context (HΨ : hyps_hold (seqs Wmp Ψ') (slt Wmp Ψ') (skn Wmp Ψ') (hyps_inst (pshift 1) Ψ)).

  Lemma wext_mp : wext Wmp Wmp.
  Proof. apply wext_refl, Wmp_strict. Qed.

  Lemma slt_up x y : slt Wmp Ψ x y → slt Wmp Ψ' (pt_inst (pshift 1) x) (pt_inst (pshift 1) y).
  Proof. apply (slt_pinst_s Wmp Wmp (pshift 1) Wmp_wf wext_mp Ψ Ψ' x y HΨ). Qed.
  Lemma seqs_up x y : seqs Wmp Ψ x y → seqs Wmp Ψ' (pt_inst (pshift 1) x) (pt_inst (pshift 1) y).
  Proof. apply (seqs_pinst_s Wmp Wmp (pshift 1) Wmp_wf wext_mp Ψ Ψ' x y HΨ). Qed.
  Lemma skn_up x : skn Wmp Ψ x → skn Wmp Ψ' (pt_inst (pshift 1) x).
  Proof. apply (skn_pinst_s Wmp Wmp (pshift 1) Wmp_wf wext_mp Ψ Ψ' x HΨ). Qed.

  (** Every point of the shifted root is the shift of a point of the root. *)
  Lemma unshift x : pt_root x = pt_name (pt_inst (pshift 1) B) →
    ∃ x0, x = pt_inst (pshift 1) x0 ∧ pt_root x0 = pt_name B ∧
      ∀ v ts, den (ianc (pt_inst (pshift 1) B) v ts) x = den (ianc B v ts) x0.
  Proof.
    destruct (gd_isroot _ _ _ HB) as [Ho Hr]. destruct B as [r o]. simpl in *. subst o.
    destruct (pn_root_cases r) as [a [Ha|Ha]]; rewrite Ha in Hr; subst r.
    - change (pt_inst (pshift 1) (Pt (NConst a) 0)) with (Pt (NConst a) 0). simpl. intros Hx.
      exists x. split; [symmetry; by apply (pt_inst_const _ _ a)|]. split; [done|]. done.
    - change (pt_inst (pshift 1) (Pt (NVar a) 0)) with (pvar (a + 1)). simpl. intros Hx.
      exists (pt_inst (λ b, pvar (pred b)) x). split_and!.
      + rewrite pt_inst_comp, <-(pt_inst_pvar x) at 1. apply pt_inst_ext_root.
        intros b Hb. rewrite Hx in Hb. injection Hb as <-. simpl. rewrite Nat.add_1_r. simpl. rewrite pt_inst_pvar_at.
        unfold pshift. f_equal. lia.
      + rewrite pt_root_inst, Hx. simpl. by rewrite Nat.add_1_r.
      + intros v ts. symmetry. apply (den_inst _ _ _ (a + 1)); [done|].
        simpl. rewrite Nat.add_1_r. simpl. unfold ianc, pvar. simpl.
        rewrite !decide_True by done. unfold den. simpl. by rewrite decide_True.
  Qed.

  Lemma good_shift : good Ψ' Θ (pt_inst (pshift 1) B).
  Proof.
    destruct (gd_isroot _ _ _ HB) as [Ho Hr].
    split.
    - destruct B as [r o]. simpl in *. subst o.
      destruct (pn_root_cases r) as [a [Ha|Ha]]; rewrite Ha in Hr; subst r; done.
    - apply HB.
    - intros x y Hx Hy E. destruct (unshift x Hx) as (x0 & -> & Hx0 & Dx).
      destruct (unshift y Hy) as (y0 & -> & Hy0 & Dy). apply seqs_up, (gd_eq _ _ _ HB); [done|done|].
      intros v ts Hv. rewrite <-Dx, <-Dy. by apply E.
    - intros x y Hx Hy E. destruct (unshift x Hx) as (x0 & -> & Hx0 & Dx).
      destruct (unshift y Hy) as (y0 & -> & Hy0 & Dy). apply slt_up, (gd_lt _ _ _ HB); [done|done|].
      intros v ts Hv. rewrite <-Dx, <-Dy. by apply E.
    - intros x Hx. destruct (unshift x Hx) as (x0 & -> & Hx0 & _). apply skn_up, (gd_kn _ _ _ HB), Hx0.
  Qed.
End shift.

Lemma tr_names B pts pts' T : (∀ m, m ∈ tnames T → pts m = pts' m) → tr B pts T = tr B pts' T.
Proof.
  induction T as [|p Q [h d|n w]| p Q |T IH1 lo ef V IH2|Θ T IH1 ef V IH2|p k Qa Qr];
    simpl; intros H; try done.
  - rewrite H; [done|by left].
  - rewrite IH1, IH2; [done| |]; intros m Hm; apply H; set_solver.
Qed.

Lemma trs_pinst σ ss B pts T : pinst_ty σ (trs ss B pts T) = trs ss (pt_inst σ B) (pt_inst σ ∘ pts) T.
Proof. unfold trs. by rewrite pinst_sinst, tr_pinst. Qed.

Definition pts_open (n : nat) (pts : nat → point) : nat → point :=
  λ m, if decide (m = n) then pvar 0 else pt_inst (pshift 1) (pts m).

Lemma pinst_trs_open ss B pts n o :
  (∀ t, o = Some t → n ∉ tnames t) →
  fmap (pinst_ty (pshift 1)) (fmap (trs ss B pts) o) =
  fmap (trs ss (pt_inst (pshift 1) B) (pts_open n pts)) o.
Proof.
  intros Ho. destruct o as [t|]; simpl; [|done]. f_equal. rewrite trs_pinst. unfold trs. f_equal.
  apply tr_names. intros m Hm. unfold pts_open. simpl. rewrite decide_False; [done|].
  intros ->. by apply (Ho t).
Qed.

Lemma erel_shift B ss pts ins Γ Δ n :
  erel B ss pts ins Γ Δ → n ∉ menames Γ →
  erel (pt_inst (pshift 1) B) ss (pts_open n pts) ins Γ (lenv_pinst (pshift 1) Δ).
Proof.
  induction 1 as [|o ins Γ Δ H IH|o ins Γ Δ Ho H IH]; intros Hn; simpl.
  - constructor.
  - change (lenv_pinst (pshift 1) (fmap (trs ss B pts) o :: Δ))
      with (fmap (pinst_ty (pshift 1)) (fmap (trs ss B pts) o) :: lenv_pinst (pshift 1) Δ).
    rewrite (pinst_trs_open ss B pts n); [apply er_keep, IH|]; destruct o as [t|]; simpl in Hn; try set_solver.
    all: intros ? [=<-]; set_solver.
  - change (lenv_pinst (pshift 1) (o :: Δ)) with (fmap (pinst_ty (pshift 1)) o :: lenv_pinst (pshift 1) Δ).
    apply er_skip; [|by apply IH].
    destruct Ho as [->|(T & -> & HT)]; [by left|right]. eexists. split; [done|]. by apply unlimited_pinst.
Qed.

Lemma erel_open B ss pts ins Γ Δ i pol Q n :
  erel B ss pts ins Γ Δ → Γ !! i = Some (Some (MEx pol Q)) → n ∉ menames Γ →
  erel (pt_inst (pshift 1) B) ss (pts_open n pts) ins (<[i := Some (MCh pol Q (PX n []))]> Γ)
    (<[ren_of ins i := Some (TSess (sinst (slist ss) (polS pol (ers Q))) (pvar 0))]> (lenv_pinst (pshift 1) Δ)).
Proof.
  intros H. revert i. induction H as [|o ins Γ Δ H IH|o ins Γ Δ Ho H IH]; intros i Hi Hn; simpl.
  - done.
  - assert (n ∉ menames Γ) as Hn'.
    { destruct o as [t|]; simpl in Hn; [set_solver|done]. }
    change (lenv_pinst (pshift 1) (fmap (trs ss B pts) o :: Δ))
      with (fmap (pinst_ty (pshift 1)) (fmap (trs ss B pts) o) :: lenv_pinst (pshift 1) Δ).
    destruct i as [|i]; simpl in *.
    + injection Hi as ->. simpl.
      assert (Some (TSess (sinst (slist ss) (polS pol (ers Q))) (pvar 0)) =
        fmap (trs ss (pt_inst (pshift 1) B) (pts_open n pts)) (Some (MCh pol Q (PX n [])))) as ->.
      { simpl. unfold trs, pts_open. simpl. by rewrite decide_True. }
      apply er_keep. by apply erel_shift.
    + rewrite (pinst_trs_open ss B pts n); [apply er_keep; by apply IH|].
      intros t ->. simpl in Hn. set_solver.
  - change (lenv_pinst (pshift 1) (o :: Δ)) with (fmap (pinst_ty (pshift 1)) o :: lenv_pinst (pshift 1) Δ).
    simpl. apply er_skip; [|by apply IH].
    destruct Ho as [->|(T & -> & HT)]; [by left|right]. eexists. split; [done|]. by apply unlimited_pinst.
Qed.

Lemma mwalk_vb k x u : pn_vb k (pt_name x) → pn_vb k (pt_name (mwalk x u)).
Proof. revert x. induction u as [|[] u IH]; intros x Hx; simpl; [done|..]; by apply IH. Qed.

Lemma pts_ok_open Ψ Θ B pts n :
  good Ψ Θ B → pts_ok Ψ B pts →
  pts_ok (hyps_inst (pshift 1) Ψ ++ [(Cex (pt_inst (pshift 1) B), ids 1)]) (pt_inst (pshift 1) B) (pts_open n pts).
Proof.
  intros HB Hp. set (Ψ' := hyps_inst (pshift 1) Ψ ++ [(Cex (pt_inst (pshift 1) B), ids 1)]).
  assert (hyps_hold (seqs Wmp Ψ') (slt Wmp Ψ') (skn Wmp Ψ') (hyps_inst (pshift 1) Ψ)) as HΨ.
  { apply hyps_hold_sub. intros h Hh. unfold Ψ'. set_solver. }
  intros m. unfold pts_open. case_decide as Hm.
  - split; [right; exists (Cex (pt_inst (pshift 1) B)), (ids 1), (pvar 0); split_and!; [unfold Ψ'; set_solver|by left|done]|].
    split; [intros u; split|intros u i].
    + eapply (sl_hyp _ _ [pt_inst (pshift 1) B] (pex_fact 0 1) (ids 1) (FLt (mwalk (pvar 0) u) (rpt (pvar 1) (RHi [PTop]))));
        [unfold Ψ'; set_solver|left; by exists u| |].
      * split; [apply mwalk_vb; simpl; lia|simpl; lia].
      * cbn [fact_map]. rewrite pt_inst_mwalk, pt_inst_rpt, !pt_inst_pvar_at. reflexivity.
    + eapply (sl_hyp _ _ [pt_inst (pshift 1) B] (pex_fact 0 1) (ids 1) (FLt (rpt (pvar 1) (RLo [LP PBot])) (mwalk (pvar 0) u)));
        [unfold Ψ'; set_solver|right; left; by exists u| |].
      * split; [simpl; lia|apply mwalk_vb; simpl; lia].
      * cbn [fact_map]. rewrite pt_inst_mwalk, pt_inst_rpt, !pt_inst_pvar_at. reflexivity.
    + eapply (sl_hyp _ _ [pt_inst (pshift 1) B] (pex_fact 0 1) (ids 1) (FLt (mwalk (pvar 0) u) (pt_slot (mwalk (pvar 0) u) i)));
        [unfold Ψ'; set_solver|right; right; by exists u, i| |].
      * split; apply mwalk_vb; simpl; lia.
      * cbn [fact_map]. rewrite pt_inst_slot, pt_inst_mwalk, !pt_inst_pvar_at. reflexivity.
  - destruct (Hp m) as (Hk & Hw & Hr). split; [by apply (skn_up Ψ Ψ' Θ B HB HΨ)|]. split.
    { intros u. destruct (Hw u) as [H1 H2]. unfold ceil, floor in *. rewrite <-!pt_inst_rpt, <-pt_inst_mwalk.
      split; by apply (slt_up Ψ Ψ' Θ B HB HΨ). }
    intros u i. rewrite <-pt_inst_mwalk, <-pt_inst_slot. by apply (slt_up Ψ Ψ' Θ B HB HΨ).
Qed.

(** ** Translated types, unfolded *)

Definition chpt (B : point) (pts : nat → point) (Q : msty) (p : mpos) : point :=
  match p with PR h d => rpt B (RCh Q h d) | PX n w => mwalk (pts n) w end.

Lemma trs_unit ss B pts : trs ss B pts MUnit = U.
Proof. done. Qed.
Lemma trs_arr ss B pts T lo ef V :
  trs ss B pts (MArr T lo ef V) = TLolli (hiz B ef) (Some (rpt B (RLo lo))) (trs ss B pts T) (trs ss B pts V).
Proof. done. Qed.
Lemma trs_ch ss B pts pol Q p :
  trs ss B pts (MCh pol Q p) = TSess (sinst (slist ss) (polS pol (ers Q))) (chpt B pts Q p).
Proof. by destruct p. Qed.
Lemma trs_ex ss B pts pol Q :
  trs ss B pts (MEx pol Q) = TEx (LPt (floor B)) 1 (Cex B) (TSess (sinst (slist ss) (polS pol (ers Q))) (pvar 0)).
Proof. done. Qed.
Lemma trs_snd ss B pts pol a P K p :
  trs ss B pts (MCh pol (sndQ pol a P K) p) =
  TSess (SSeq (SSnd (pm P) (sinst_ty (slist ss) (ersp P))) (sinst (slist ss) (polS pol (ers K)))) (chpt B pts (sndQ pol a P K) p).
Proof. destruct pol, p; done. Qed.
Lemma trs_rcv ss B pts pol a P K p :
  trs ss B pts (MCh pol (rcvQ pol a P K) p) =
  TSess (SSeq (SRcv (pm P) (sinst_ty (slist ss) (ersp P))) (sinst (slist ss) (polS pol (ers K)))) (chpt B pts (rcvQ pol a P K) p).
Proof. destruct pol, p; done. Qed.
Lemma trs_sel ss B pts pol a K1 K2 p :
  trs ss B pts (MCh pol (selQ pol a K1 K2) p) =
  TSess (SPlus (sinst (slist ss) (polS pol (ers K1))) (sinst (slist ss) (polS pol (ers K2)))) (chpt B pts (selQ pol a K1 K2) p).
Proof. destruct pol, p; done. Qed.
Lemma trs_bra ss B pts pol a K1 K2 p :
  trs ss B pts (MCh pol (braQ pol a K1 K2) p) =
  TSess (SWith (sinst (slist ss) (polS pol (ers K1))) (sinst (slist ss) (polS pol (ers K2)))) (chpt B pts (braQ pol a K1 K2) p).
Proof. destruct pol, p; done. Qed.
Lemma trs_end ss B pts pol a w p :
  trs ss B pts (MCh pol (MEnd a w) p) = TSess SEnd (chpt B pts (MEnd a w) p).
Proof. destruct pol, p; done. Qed.

Section chpt.
  Context (Ψ : hyps) (Θ : pctx) (B : point) (HB : good Ψ Θ B) (pts : nat → point) (Hp : pts_ok Ψ B pts).

  Lemma chpt_ok Q p u : slt Wmp Ψ (mwalk (chpt B pts Q p) u) (ceil B) ∧ slt Wmp Ψ (floor B) (mwalk (chpt B pts Q p) u).
  Proof. destruct p as [h d|n w]; simpl; [by apply (ch_ceil Ψ Θ B HB)|]. rewrite <-mwalk_app. apply Hp. Qed.

  Lemma chpt_rise Q p u i : slt Wmp Ψ (mwalk (chpt B pts Q p) u) (pt_slot (mwalk (chpt B pts Q p) u) i).
  Proof.
    destruct p as [h d|n w]; simpl; [apply (ch_rise Ψ Θ B HB)|]. rewrite <-mwalk_app.
    apply (proj2 (proj2 (Hp n))).
  Qed.

  (** A choice point lies below the point x[i] of each branch (K11). *)
  Lemma chpt_br Q p b : slt Wmp Ψ (chpt B pts Q p) (pt_slot (chpt B pts Q p) (bidx b)).
  Proof. apply (chpt_rise Q p [] (bidx b)). Qed.

  Lemma chpt_known Q p : skn Wmp Ψ (chpt B pts Q p).
  Proof.
    destruct p as [h d|n w]; simpl; [by apply (rpt_known Ψ Θ B HB)|].
    eapply skn_root; [|apply (Hp n)]. by rewrite pt_root_mwalk.
  Qed.

  Lemma B_known : skn Wmp Ψ B.
  Proof. apply (gd_kn _ _ _ HB). destruct (gd_isroot _ _ _ HB) as [_ Hr]. exact Hr. Qed.
End chpt.

Definition pts0 (B : point) : nat → point := λ _, rpt B (RCh MSkip (PZ 0) 0).

Lemma pts0_ok Ψ Θ B : good Ψ Θ B → pts_ok Ψ B (pts0 B).
Proof.
  intros HB n. split; [apply (rpt_known Ψ Θ B HB)|].
  split; [intros u; apply (ch_ceil Ψ Θ B HB)|intros u i; apply (ch_rise Ψ Θ B HB)].
Qed.

Lemma hiz_le_ceil Ψ Θ B ef x : good Ψ Θ B → hiz B ef = Some x → sle Wmp Ψ x (ceil B).
Proof.
  intros HB Hx. destruct ef as [|ρ ef0]; [done|]. injection Hx as <-.
  destruct (decide (PTop ∈ ρ :: ef0)) as [Ht|Ht].
  - left. apply se_sym. by apply (ceil_top Ψ Θ B HB).
  - right. apply (slt_rpt Ψ Θ B HB). intros v ts _. rewrite (rank_ceil Ψ Θ B HB), (den_hi Ψ Θ B HB).
    pose proof (xmaxl_notop v (ρ :: ef0) Ht). destruct (xmaxl v (ρ :: ef0)); simpl; done.
Qed.

Lemma tpure_names k T : tpure k T → tnames T = [].
Proof.
  induction T as [|p Q [h d|n w]| p Q |T IH1 lo ef V IH2|Θ T IH1 ef V IH2|p k' Qa Qr];
    simpl; try done. intros (H1 & H2 & _). by rewrite IH1, IH2.
Qed.

Lemma erel_poly B ss pts B' ss' pts' σ ins Γ Δ :
  erel B ss pts ins Γ Δ → menv_poly Γ → erel B' ss' pts' ins Γ (lenv_pinst σ Δ).
Proof.
  intros H. induction H as [|o ins Γ Δ H IH|o ins Γ Δ Ho H IH]; intros HΓ; simpl.
  - constructor.
  - assert (menv_poly Γ) as HΓ' by (intros t Ht; apply HΓ; by right).
    change (lenv_pinst σ (fmap (trs ss B pts) o :: Δ)) with (fmap (pinst_ty σ) (fmap (trs ss B pts) o) :: lenv_pinst σ Δ).
    destruct o as [t|]; simpl.
    + destruct (HΓ t (list_elem_of_here _ _)) as [Hu Ht].
      rewrite trs_pinst, (trs_un ss ss' _ B' _ pts') by done.
      apply (er_keep _ _ _ (Some t)). by apply IH.
    + apply (er_keep _ _ _ None). by apply IH.
  - change (lenv_pinst σ (o :: Δ)) with (fmap (pinst_ty σ) o :: lenv_pinst σ Δ).
    apply er_skip; [|by apply IH]. destruct Ho as [->|(T & -> & HT)]; [by left|right].
    eexists. split; [done|]. by apply unlimited_pinst.
Qed.
Lemma pscoped_sinst kk σ T : pscoped kk T → pscoped kk (sinst_ty σ T).
Proof. revert kk σ. induction T; intros kk σ HT; simpl in *; naive_solver. Qed.

Lemma ersp_scoped ss P : pscoped (pm P) (sinst_ty (slist ss) (ersp P)).
Proof.
  apply pscoped_sinst. destruct P; simpl.
  - split; [unfold bcs_scoped; simpl; constructor|]. repeat split.
  - intros a Ha. injection Ha as <-. lia.
Qed.

(** ** Payloads *)

Lemma payload_unit x : payload_at 0 U x = U.
Proof. done. Qed.

Lemma payload_chan s x : payload_at 1 (TSess s (pvar 0)) x = TSess s (pt_slot x 0).
Proof. unfold payload_at, ty_inst. simpl. by rewrite pt_inst_pvar_at. Qed.

Lemma pay_conv Ψ ss B pts x P :
  (∀ pp Qp hp dp, P = MPChan pp Qp hp dp → seqs Wmp Ψ (pt_slot x 0) (rpt B (RCh Qp hp dp))) →
  steq Wmp Ψ (trs ss B pts (payty P)) (payload_at (pm P) (sinst_ty (slist ss) (ersp P)) x) ∧
  steq Wmp Ψ (payload_at (pm P) (sinst_ty (slist ss) (ersp P)) x) (trs ss B pts (payty P)) ∧
  (∀ y, y ∈ heads (payload_at (pm P) (sinst_ty (slist ss) (ersp P)) x) →
     ∃ pp Qp hp dp, P = MPChan pp Qp hp dp ∧ y = pt_slot x 0).
Proof.
  intros Hp. destruct P as [|pp Qp hp dp].
  - change (payload_at (pm MPUnit) (sinst_ty (slist ss) (ersp MPUnit)) x) with (payload_at 0 U x).
    rewrite payload_unit. change (trs ss B pts (payty MPUnit)) with U.
    split_and!; [apply steq_refl|apply steq_refl|]. intros y Hy. by apply elem_of_empty in Hy.
  - specialize (Hp pp Qp hp dp eq_refl).
    change (payload_at (pm (MPChan pp Qp hp dp)) (sinst_ty (slist ss) (ersp (MPChan pp Qp hp dp))) x)
      with (payload_at 1 (TSess (sinst (slist ss) (polS pp (ers Qp))) (pvar 0)) x).
    change (trs ss B pts (payty (MPChan pp Qp hp dp))) with (TSess (sinst (slist ss) (polS pp (ers Qp))) (rpt B (RCh Qp hp dp))).
    rewrite payload_chan. split_and!.
    + split; [by apply se_sym|apply seq_refl].
    + split; [done|apply seq_refl].
    + intros y Hy. simpl in Hy. apply elem_of_singleton in Hy as ->. by eexists _, _, _, _.
Qed.

Lemma pay_px ss B pts n w P :
  trs ss B pts (rpayty (PX n w) P) = payload_at (pm P) (sinst_ty (slist ss) (ersp P)) (mwalk (pts n) w).
Proof.
  destruct P as [|pp Qp hp dp]; [done|].
  change (payload_at (pm (MPChan pp Qp hp dp)) (sinst_ty (slist ss) (ersp (MPChan pp Qp hp dp))) (mwalk (pts n) w))
    with (payload_at 1 (TSess (sinst (slist ss) (polS pp (ers Qp))) (pvar 0)) (mwalk (pts n) w)).
  rewrite payload_chan. unfold trs. simpl. by rewrite mwalk_app.
Qed.

(** ** The translation lemma *)

Theorem mp2_translate Θ Γ e T ef e' :
  mtyped Θ Γ e T ef e' →
  ∀ ss Ψ B pts ins Δ Φ F, length ss = pc_nt Θ → Forall hcontractive ss →
  good Ψ Θ B → pts_ok Ψ B pts → erel B ss pts ins Γ Δ → ub_below_s Wmp Ψ Φ (hiz B ef) F →
  typed Wmp Φ Ψ ∅ Δ F (rename (ren_of ins) e') (trs ss B pts T).
Proof.
  pose proof Wmp_wf as HW.
  induction 1 as [Θ Γ x t Hx
    |Θ Γ HΓ
    |Θ Γ e e' T V ef He IH
    |Θ Γ Γ1 Γ2 e1 e2 e1' e2' T lo σ V ef1 ef2 Hs H1 IH1 H2 IH2 Hl1 Hl2
    |Θ Γ Γ1 Γ2 e1 e2 e1' e2' Θ' T σ V ef1 ef2 σs τs Hs H1 IH1 Hok HT HV H2 IH2 Hl1 Hnt
    |Θ Γ e e' Θ' T σ V ef Hpoly HT HV Hinh He IH Hle
    |Θ Γ e e' pol k Qa Qr ef Hpoly HQa HQr He IH
    |Θ Γ Γ1 Γ2 e1 e2 e1' e2' pol k Qa Qr τs p ef1 ef2 Hs H1 IH1 Hlen Hsc Hhc HQa HQr H2 IH2 Hl1 Hnt
    |Θ Γ e e' i pol Q n V ef Hi Hn HnV He IH
    |Θ Γ e e' pol Q p ef He IH
    |Θ Γ Γ1 Γ2 e1 e2 e1' e2' T V ef1 ef2 Hs H1 IH1 H2 IH2 Hl
    |Θ Γ Γ1 Γ2 e1 e2 e1' e2' V ef1 ef2 Hs H1 IH1 H2 IH2 Hl
    |Θ Γ e e' Q n d V ef He IH
    |Θ Γ Γ1 Γ2 e1 e2 e1' e2' pol a P K p ef1 ef2 Hs H1 IH1 H2 IH2 Hok Hl1 Hl2
    |Θ Γ Γ1 Γ2 e e2 e' e2' pol a P K p V ef1 ef2 Hs H1 IH1 Hok H2 IH2 Hl
    |Θ Γ e e' pol a w p ef H IH Hok
    |Θ Γ e e' pol a K1 K2 p ef b H IH Hok
    |Θ Γ Γ1 Γ2 e e1 e2 e' e1' e2' pol a K1 K2 p V ef1 ef2 Hs H1 IH Hok HA IHA HB' IHB Hl
    |Θ Γ e e' lo σ ef H IH
    |Θ Γ e e' pol Q Q' p p' ef H IH Heq
    |Θ Γ e e' T ef ef' H IH Hle];
    intros ss Ψ B pts ins Δ Φ F Hlss Hss HB Hp HΔ HF.
  - (* T-Var *)
    by apply (erel_var B ss pts ins Γ Δ Wmp Φ Ψ F x t HW HΔ Hx).
  - (* () *)
    rewrite rename_unitv, trs_unit. apply (tv_unitv Wmp HW). by apply (erel_unl B ss pts ins Γ Δ).
  - (* T-AbsLin *)
    cbn [rename]. rewrite ren_up, trs_arr. set (φ := fresh (dom Φ)).
    apply (t_lam Wmp Φ Ψ ∅ Δ F _ _ _ (hiz B ef) (Some (rpt B (RLo (envp Γ)))) φ); [apply is_fresh|lbhb|].
    + simpl. bclean; rewrite (tenv_heads0 _ HW), union_empty_l_L. intros y Hy.
      apply (env_lo_below Ψ Θ B HB ss pts ins Γ Δ y Hp HΔ Hy).
    + apply IH; [done|done|done|done|by apply (er_keep _ _ _ (Some T))|apply (ubs_fresh _ HW)].
  - (* T-App *)
    cbn [rename]. destruct (erel_split B ss pts ins Γ Δ Γ1 Γ2 HΔ Hs) as (Δ1 & Δ2 & Hd & HΔ1 & HΔ2).
    eapply (t_app Wmp Φ Ψ ∅ ∅ ∅ Δ Δ1 Δ2 F _ _ (hiz B σ) (Some (rpt B (RLo lo))) (trs ss B pts T)).
    + by apply comp0.
    + done.
    + apply (ubs_seg Ψ Θ B HB Φ F σ (ef1 ++ ef2) []). by rewrite app_nil_r, <-app_assoc.
    + bclean; rewrite (tenv_heads0 _ HW), union_empty_l_L, <-trs_arr. apply (IH1 ss Ψ B pts ins Δ1); try done.
      by apply (ubs_part Ψ Θ B HB Φ F [] (ef2 ++ σ) ef1 ss pts ins Γ2 Δ2).
    + apply (IH2 ss Ψ B pts ins Δ2); try done. apply (ubs_union _ HW).
      * apply (ubs_seg Ψ Θ B HB Φ F ef2 ef1 σ). done.
      * intros x Hx h Hh. simpl in Hh. apply elem_of_singleton in Hh as ->.
        by apply (hi_below_lo Ψ Θ B HB ef2 lo x).
  - (* T-PApp, T-TApp, T-App *)
    cbn [rename]. destruct (erel_split B ss pts ins Γ Δ Γ1 Γ2 HΔ Hs) as (Δ1 & Δ2 & Hd & HΔ1 & HΔ2).
    destruct Hok as (Hlσ & Hlτ & Hfin & Hsc & Hhc & Hmod).
    set (X := rpt B (RAnc σs τs)).
    set (ssf := (λ q, sinst (slist ss) (ers q)) <$> τs).
    set (Tb := TLolli (hiz (pvar 0) σ) None (tr (pvar 0) (ptsb (pvar 0)) T) (tr (pvar 0) (ptsb (pvar 0)) V)).
    assert (trs ss B pts (MPoly Θ' T σ V) = TBox 1 (pc_nt Θ') (Crel Θ') (TLolli None None TUnit Tb)) as Ebox.
    { unfold trs. rewrite tr_closed; [done|done|by split]. }
    eapply (t_app Wmp Φ Ψ ∅ ∅ ∅ Δ Δ1 Δ2 F _ _ (hiz B (psub σs <$> σ)) None (trs ss B pts (msub σs τs T))).
    + by apply comp0.
    + done.
    + apply (ubs_seg Ψ Θ B HB Φ F (psub σs <$> σ) (ef1 ++ ef2) []). by rewrite app_nil_r, <-app_assoc.
    + bclean; rewrite (tenv_heads0 _ HW), union_empty_l_L.
      apply (t_conv _ _ _ _ _ _ _ (sinst_ty (slist ssf) (ty_inst [X] Tb))).
      { unfold ty_inst, Tb. simpl. rewrite hiz_pinst, !tr_pinst, pt_inst_pvar_at. simpl.
        rewrite <-Hlτ in HT, HV.
        destruct (tr_anc Ψ Θ B HB σs τs Hfin ss pts (pt_inst (plist [X]) ∘ ptsb (pvar 0)) T HT) as [E1 _].
        destruct (tr_anc Ψ Θ B HB σs τs Hfin ss pts (pt_inst (plist [X]) ∘ ptsb (pvar 0)) V HV) as [E2 _].
        split_and!; [|done|done|done].
        pose proof (hiz_anc Ψ Θ B HB σs τs Hfin σ) as Eh. exact Eh. }
      eapply (typed_force Wmp Φ Ψ ∅ Δ1 _ _ 1 (pc_nt Θ') (Crel Θ') None Tb [X] ssf);
        [done|done|by apply (crel_hold Ψ Θ B HB σs τs Hfin)|apply (anc_known Ψ Θ B HB σs τs Hfin)| | |done|].
      { unfold ssf. by rewrite length_fmap. }
      { unfold ssf. apply Forall_fmap. by apply Hhc. }
      rewrite <-Ebox. apply (IH1 ss Ψ B pts ins Δ1); try done.
      by apply (ubs_part Ψ Θ B HB Φ F [] (ef2 ++ (psub σs <$> σ)) ef1 ss pts ins Γ2 Δ2).
    + rewrite sf_union_empty. apply (IH2 ss Ψ B pts ins Δ2); try done.
      apply (ubs_seg Ψ Θ B HB Φ F ef2 ef1 (psub σs <$> σ)). done.
  - (* rec f. Λιs αs. λx.e *)
    cbn [rename]. rewrite ren_up2.
    set (Tb := TLolli (hiz (pvar 0) σ) None (tr (pvar 0) (ptsb (pvar 0)) T) (tr (pvar 0) (ptsb (pvar 0)) V)).
    assert (trs ss B pts (MPoly Θ' T σ V) = TBox 1 (pc_nt Θ') (Crel Θ') (TLolli None None TUnit Tb)) as Ebox.
    { unfold trs. rewrite tr_closed; [done|done|by split]. }
    assert (menv_un Γ) as HΓ by (intros t Ht; apply Hpoly, Ht).
    rewrite Ebox. set (φ := fresh (dom Φ)).
    apply (t_box Wmp Φ Ψ Δ F _ 1 (pc_nt Θ') (Crel Θ') None Tb φ); [by apply (erel_unl B ss pts ins Γ Δ)|apply is_fresh|].
    intros ss' Hss' Hhc'. change (bcs_inst (pshift 1) (Crel Θ')) with (Crel Θ').
    set (Ψ' := hyps_inst (pshift 1) Ψ ++ [(Crel Θ', ids 1)]).
    assert (good Ψ' Θ' (pvar 0)) as HB' by (apply good_box; [done|unfold Ψ'; set_solver]).
    set (Φ1 := <[φ := None]> (fhyps_pinst (pshift 1) Φ)). set (φ' := fresh (dom Φ1)).
    assert (sinst_ty (slist ss') Tb = TLolli (hiz (pvar 0) σ) None (trs ss' (pvar 0) (pts0 (pvar 0)) T)
                                        (trs ss' (pvar 0) (pts0 (pvar 0)) V)) as ETb.
    { unfold Tb, trs. simpl. rewrite !(tr_names (pvar 0) (ptsb (pvar 0)) (pts0 (pvar 0))); [done| |];
        intros m Hm; [rewrite (tpure_names _ V HV) in Hm|rewrite (tpure_names _ T HT) in Hm]; by apply elem_of_nil in Hm. }
    rewrite ETb.
    apply (t_lam Wmp Φ1 Ψ' ∅ _ _ _ _ _ (hiz (pvar 0) σ) None φ'); [apply is_fresh|lbhb|].
    + simpl. bclean; rewrite (tenv_heads0 _ HW), !union_empty_l_L. apply unl_heads, unl_pinst.
      by apply (erel_unl B ss pts ins Γ Δ HΔ HΓ).
    + apply IH; [done|done|done|by apply (pts0_ok Ψ' Θ')| |].
      * apply (er_keep _ _ _ (Some T)).
        change (lenv_pinst (pshift 1) (Some (TBox 1 (pc_nt Θ') (Crel Θ') (TLolli None None TUnit Tb)) :: Δ))
          with (Some (pinst_ty (pshift 1) (TBox 1 (pc_nt Θ') (Crel Θ') (TLolli None None TUnit Tb))) :: lenv_pinst (pshift 1) Δ).
        rewrite <-Ebox, trs_pinst, (trs_un ss ss' _ (pvar 0) _ (pts0 (pvar 0))) by (done || by split).
        apply (er_keep _ _ _ (Some (MPoly Θ' T σ V))). by apply (erel_poly B ss pts).
      * apply (ubs_hle Ψ' Θ' (pvar 0) HB' _ ef σ); [done|]. apply (ubs_fresh _ HW).
  - (* rec f. Λαs. λx.e over a segment *)
    cbn [rename]. rewrite ren_up2.
    set (Tseg := TLolli (Some (rpt (pvar 1) (RHi [PTop]))) None (TSess (polS pol (ers Qa)) (pvar 0))
                   (TEx (LPt (rpt (pvar 1) (RLo [LP PBot]))) 1 (Cex (pvar 1)) (TSess (polS pol (ers Qr)) (pvar 0)))).
    assert (trs ss B pts (MSeg pol k Qa Qr) = TBox 2 k (Cseg k) (TLolli None None TUnit Tseg)) as Eseg.
    { unfold trs. rewrite tr_closed; [done|done|by split]. }
    assert (menv_un Γ) as HΓ by (intros t Ht; apply Hpoly, Ht).
    rewrite Eseg. set (φ := fresh (dom Φ)).
    apply (t_box Wmp Φ Ψ Δ F _ 2 k (Cseg k) None Tseg φ); [by apply (erel_unl B ss pts ins Γ Δ)|apply is_fresh|].
    intros ss' Hss' Hhc'. change (bcs_inst (pshift 2) (Cseg k)) with (Cseg k).
    set (Ψ' := hyps_inst (pshift 2) Ψ ++ [(Cseg k, ids 2)]).
    assert (good Ψ' (Θany k) (pvar 1)) as HB' by (apply good_seg; unfold Ψ'; set_solver).
    set (pts' := λ _ : nat, pvar 0).
    set (Φ1 := <[φ := None]> (fhyps_pinst (pshift 2) Φ)). set (φ' := fresh (dom Φ1)).
    assert (sinst_ty (slist ss') Tseg = TLolli (Some (ceil (pvar 1))) None
              (trs ss' (pvar 1) pts' (MCh pol Qa (PX 0 []))) (trs ss' (pvar 1) pts' (MEx pol Qr))) as ET by done.
    rewrite ET.
    apply (t_lam Wmp Φ1 Ψ' ∅ _ _ _ _ _ (Some (ceil (pvar 1))) None φ'); [apply is_fresh|lbhb|].
    + simpl. bclean; rewrite (tenv_heads0 _ HW), !union_empty_l_L. apply unl_heads, unl_pinst.
      by apply (erel_unl B ss pts ins Γ Δ HΔ HΓ).
    + apply IH; [done|done|done| | |].
      * intros m. split; [right; exists (Cseg k), (ids 2), (pvar 0); split_and!; [unfold Ψ'; set_solver|unfold ids; simpl; by left|done]|].
        split; [intros u; split|intros u i].
        -- eapply (sl_hyp _ _ [] (λ g, pex_fact 0 1 g ∨ crel_fact (Θany k) (NVar 1) g) (ids 2) (FLt (mwalk (pvar 0) u) (rpt (pvar 1) (RHi [PTop]))));
             [unfold Ψ'; set_solver|left; left; by exists u|split; [apply mwalk_vb; simpl; lia|simpl; lia]|].
           cbn [fact_map]. rewrite pt_inst_mwalk, pt_inst_rpt, !pt_inst_pvar_at. reflexivity.
        -- eapply (sl_hyp _ _ [] (λ g, pex_fact 0 1 g ∨ crel_fact (Θany k) (NVar 1) g) (ids 2) (FLt (rpt (pvar 1) (RLo [LP PBot])) (mwalk (pvar 0) u)));
             [unfold Ψ'; set_solver|left; right; left; by exists u|split; [simpl; lia|apply mwalk_vb; simpl; lia]|].
           cbn [fact_map]. rewrite pt_inst_mwalk, pt_inst_rpt, !pt_inst_pvar_at. reflexivity.
        -- eapply (sl_hyp _ _ [] (λ g, pex_fact 0 1 g ∨ crel_fact (Θany k) (NVar 1) g) (ids 2) (FLt (mwalk (pvar 0) u) (pt_slot (mwalk (pvar 0) u) i)));
             [unfold Ψ'; set_solver|left; right; right; by exists u, i|split; apply mwalk_vb; simpl; lia|].
           cbn [fact_map]. rewrite pt_inst_slot, pt_inst_mwalk, !pt_inst_pvar_at. reflexivity.
      * apply (er_keep _ _ _ (Some (MCh pol Qa (PX 0 [])))).
        change (lenv_pinst (pshift 2) (Some (TBox 2 k (Cseg k) (TLolli None None TUnit Tseg)) :: Δ))
          with (Some (pinst_ty (pshift 2) (TBox 2 k (Cseg k) (TLolli None None TUnit Tseg))) :: lenv_pinst (pshift 2) Δ).
        rewrite <-Eseg, trs_pinst, (trs_un ss ss' _ (pvar 1) _ pts') by (done || by split).
        apply (er_keep _ _ _ (Some (MSeg pol k Qa Qr))). by apply (erel_poly B ss pts).
      * apply (ubs_lower Wmp HW _ _ _ (Some (ceil (pvar 1)))); [|apply (ubs_fresh _ HW)].
        intros x Hx. exists (ceil (pvar 1)). split; [done|]. by apply (hiz_le_ceil Ψ' (Θany k) (pvar 1) ef).
  - (* T-TApp, T-App at a segment *)
    cbn [rename]. destruct (erel_split B ss pts ins Γ Δ Γ1 Γ2 HΔ Hs) as (Δ1 & Δ2 & Hd & HΔ1 & HΔ2).
    set (x := chpt B pts (tsub τs Qa) p).
    set (ssf := (λ q, sinst (slist ss) (ers q)) <$> τs).
    set (Tseg := TLolli (Some (rpt (pvar 1) (RHi [PTop]))) None (TSess (polS pol (ers Qa)) (pvar 0))
                   (TEx (LPt (rpt (pvar 1) (RLo [LP PBot]))) 1 (Cex (pvar 1)) (TSess (polS pol (ers Qr)) (pvar 0)))).
    assert (trs ss B pts (MSeg pol k Qa Qr) = TBox 2 k (Cseg k) (TLolli None None TUnit Tseg)) as Eseg.
    { unfold trs. rewrite tr_closed; [done|done|by split]. }
    assert (sinst_ty (slist ssf) (ty_inst [x; B] Tseg) =
            TLolli (Some (ceil B)) None (trs ss B pts (MCh pol (tsub τs Qa) p)) (trs ss B pts (MEx pol (tsub τs Qr)))) as Ef.
    { rewrite trs_ch, trs_ex. unfold ty_inst, Tseg. simpl pinst_ty.
      rewrite !pt_inst_rpt, pt_inst_plist2_0, pt_inst_plist2_1, pup1_0.
      unfold Cex, bcs_inst. simpl fmap. rewrite pt_inst_plist2_1. simpl sinst_ty.
      rewrite <-Hlen in HQa, HQr. unfold ssf. rewrite !polS_sinst, !ers_tsub by done. done. }
    eapply (t_app Wmp Φ Ψ ∅ ∅ ∅ Δ Δ1 Δ2 F _ _ (Some (ceil B)) None (trs ss B pts (MCh pol (tsub τs Qa) p))).
    + by apply comp0.
    + done.
    + apply (ubs_lower Wmp HW _ _ _ (hiz B (ef1 ++ ef2 ++ [PTop]))); [|done].
      intros y [=<-]. eexists. split; [destruct ef1; [destruct ef2|]; done|].
      left. apply (ceil_top Ψ Θ B HB). set_solver.
    + bclean; rewrite (tenv_heads0 _ HW), union_empty_l_L, <-Ef.
      eapply (typed_force Wmp Φ Ψ ∅ Δ1 _ _ 2 k (Cseg k) None Tseg [x; B] ssf); [done|done| | | | |done|].
      { apply (cseg_hold Ψ Θ B k x HB); [intros u; apply (chpt_ok Ψ Θ B HB pts Hp)|].
        intros u i. apply (chpt_rise Ψ Θ B HB pts Hp). }
      { constructor; [apply (chpt_known Ψ Θ B HB pts Hp)|apply Forall_singleton, (B_known Ψ Θ B HB pts Hp)]. }
      { unfold ssf. by rewrite length_fmap. }
      { unfold ssf. apply Forall_fmap. by apply Hhc. }
      rewrite <-Eseg. apply (IH1 ss Ψ B pts ins Δ1); try done.
      by apply (ubs_part Ψ Θ B HB Φ F [] (ef2 ++ [PTop]) ef1 ss pts ins Γ2 Δ2).
    + rewrite sf_union_empty. apply (IH2 ss Ψ B pts ins Δ2); try done.
      apply (ubs_seg Ψ Θ B HB Φ F ef2 ef1 [PTop]). done.
  - (* the end point of a segment *)
    set (sQ := sinst (slist ss) (polS pol (ers Q))).
    set (Ψ' := hyps_inst (pshift 1) Ψ ++ [(Cex (pt_inst (pshift 1) B), ids 1)]).
    assert (hyps_hold (seqs Wmp Ψ') (slt Wmp Ψ') (skn Wmp Ψ') (hyps_inst (pshift 1) Ψ)) as HΨ.
    { apply hyps_hold_sub. intros h Hh. unfold Ψ'. set_solver. }
    pose proof (erel_lookup B ss pts ins Γ Δ i _ HΔ Hi) as Hl. simpl in Hl.
    apply (tv_open Wmp Φ Ψ Δ F _ (ren_of ins i) (LPt (floor B)) 1 (Cex B) (TSess sQ (pvar 0)) (trs ss B pts V)
             (fhyps_pinst (pshift 1) Φ) Ψ'
             (<[ren_of ins i := Some (TSess sQ (pvar 0))]> (lenv_pinst (pshift 1) Δ))
             (sf_pinst (pshift 1) F) (trs ss (pt_inst (pshift 1) B) (pts_open n pts) V));
      [exact Hl|intros []|done|done|done|done| |].
    { rewrite trs_pinst. unfold trs. f_equal. apply tr_names. intros m Hm. unfold pts_open. simpl.
      rewrite decide_False; [done|]. intros ->. done. }
    apply IH; try done.
    + by apply (good_shift Ψ Ψ' Θ B HB HΨ).
    + by apply (pts_ok_open Ψ Θ B pts n HB Hp).
    + by apply erel_open.
    + rewrite <-hiz_pinst. by apply (ub_below_s_pinst Wmp Wmp (pshift 1) Ψ Ψ' Φ (hiz B ef) F HW (wext_mp Ψ Ψ' Θ B HB HΨ) HΨ).
  - (* a later end point *)
    rewrite trs_ex. set (x := chpt B pts Q p).
    apply (t_pack Wmp Φ Ψ ∅ Δ F _ (LPt (floor B)) 1 (Cex B) (TSess (sinst (slist ss) (polS pol (ers Q))) (pvar 0)) [x]).
    + done.
    + apply Forall_singleton, (chpt_known Ψ Θ B HB pts Hp).
    + apply bcs_hold_env. intros f [(u & ->)|[(u & ->)|(u & i & ->)]] _; cbn [fact_map fact_holds];
        rewrite ?pt_inst_slot, ?pt_inst_mwalk, ?pt_inst_rpt; change (pt_inst (plist ([x] ++ [B])) (pvar 0)) with (pt_shift 0 x);
        try change (pt_inst (plist ([x] ++ [B])) (pvar 1)) with (pt_shift 0 B); rewrite !pt_shift_0;
        [apply (chpt_ok Ψ Θ B HB pts Hp Q p u)..|apply (chpt_rise Ψ Θ B HB pts Hp)].
    + assert (ty_inst [x] (TSess (sinst (slist ss) (polS pol (ers Q))) (pvar 0)) = trs ss B pts (MCh pol Q p)) as ->.
      { rewrite trs_ch. unfold ty_inst. simpl pinst_ty. by rewrite pt_inst_pvar_at. }
      rewrite trs_ch. simpl. split; [|done]. intros y Hy. apply elem_of_singleton in Hy as ->.
      right. apply (chpt_ok Ψ Θ B HB pts Hp Q p []).
    + assert (ty_inst [x] (TSess (sinst (slist ss) (polS pol (ers Q))) (pvar 0)) = trs ss B pts (MCh pol Q p)) as ->.
      { rewrite trs_ch. unfold ty_inst. simpl pinst_ty. by rewrite pt_inst_pvar_at. }
      by apply IH.
  - (* T-Let *)
    cbn [rename]. rewrite ren_up.
    destruct (erel_split B ss pts ins Γ Δ Γ1 Γ2 HΔ Hs) as (Δ1 & Δ2 & Hd & HΔ1 & HΔ2).
    set (lb := Some (rpt B (RLo (envp Γ2)))).
    eapply (t_app Wmp Φ Ψ ∅ ∅ ∅ Δ Δ2 Δ1 F _ _ (hiz B ef2) lb (trs ss B pts T)).
    + by apply comp0.
    + by apply lenv_split_comm.
    + apply (ubs_seg Ψ Θ B HB Φ F ef2 ef1 []). by rewrite app_nil_r.
    + set (φ := fresh (dom Φ)).
      apply (t_lam Wmp Φ Ψ ∅ Δ2 _ _ _ _ (hiz B ef2) lb φ); [apply is_fresh|lbhb|].
      * simpl. bclean; rewrite (tenv_heads0 _ HW), union_empty_l_L. intros y Hy.
        apply (env_lo_below Ψ Θ B HB ss pts ins Γ2 Δ2 y Hp HΔ2 Hy).
      * apply IH2; [done|done|done|done|by apply (er_keep _ _ _ (Some T))|apply (ubs_fresh _ HW)].
    + apply (IH1 ss Ψ B pts ins Δ1); try done. apply (ubs_union _ HW).
      * apply (ubs_seg Ψ Θ B HB Φ F ef1 [] ef2). done.
      * intros x Hx h Hh. simpl in Hh. apply elem_of_singleton in Hh as ->.
        by apply (hi_below_lo Ψ Θ B HB ef1 _ x).
  - (* e₁; e₂ *)
    cbn [rename]. destruct (erel_split B ss pts ins Γ Δ Γ1 Γ2 HΔ Hs) as (Δ1 & Δ2 & Hd & HΔ1 & HΔ2).
    eapply (t_letu Wmp Φ Ψ ∅ ∅ ∅ Δ Δ1 Δ2); [by apply comp0|done| |].
    + bclean; rewrite (tenv_heads0 _ HW), union_empty_l_L.
      change TUnit with (ty_inst [] TUnit).
      eapply (typed_force0 Wmp Φ Ψ ∅ Δ1 _ _ 0 (BCs [] (λ _, False)) None TUnit []);
        [done|done| |done|done|].
      { intros g Hg. apply bcs_open_nil in Hg as [[] _]. }
      apply (IH1 ss Ψ B pts ins Δ1); try done.
      by apply (ubs_part Ψ Θ B HB Φ F [] ef2 ef1 ss pts ins Γ2 Δ2).
    + apply (IH2 ss Ψ B pts ins Δ2); try done. apply (ubs_seg Ψ Θ B HB Φ F ef2 ef1 []).
      by rewrite app_nil_r.
  - (* new *)
    (* new at the point of the channel by the alias ι ≡ x ([t_new_at]).
       The body skips the spent pair and unit. *)
    rewrite rename_let_new_pair, ren_up2. unfold let_new_pair.
    assert (rename (upren (upren (λ x, 2 + x))) (rename (ren_of (false :: false :: ins)) e')
            = rename (ren_of (false :: false :: true :: true :: ins)) e') as ->.
    { rewrite rename_rename. apply rename_ext. by intros [|[|x]]. }
    set (S := sinst (slist ss) (ers Q)). set (x := rpt B (RCh Q n d)).
    assert (trs ss B pts (MCh false Q (PR n d)) = TSess S x) as E1 by done.
    assert (trs ss B pts (MCh true Q (PR n d)) = TSess (dual S) x) as E2.
    { rewrite trs_ch. simpl. unfold S. by rewrite dual_sinst. }
    apply (t_new_at Wmp _ _ _ _ _ _ _ S x); [apply Wmp_strict|by apply (rpt_known Ψ Θ B HB)|].
    apply IH; try done. rewrite <-E1, <-E2. apply (er_keep _ _ _ (Some _)), (er_keep _ _ _ (Some _)).
    apply er_skip; [by left|]. apply er_skip; [by left|]. exact HΔ.
  - (* send *)
    cbn [rename]. destruct (erel_split B ss pts ins Γ Δ Γ1 Γ2 HΔ Hs) as (Δ1 & Δ2 & Hd & HΔ1 & HΔ2).
    set (S := sinst (slist ss) (polS pol (ers K))). set (Tp := sinst_ty (slist ss) (ersp P)).
    destruct p as [h d|n w].
    + destruct Hok as (Hfin & Hpay & Hrise). simpl aeff. rewrite trs_ch. simpl chpt.
      set (x := rpt B (RCh (sndQ pol a P K) h d)).
      assert (∀ pp Qp hp dp, P = MPChan pp Qp hp dp → seqs Wmp Ψ (pt_slot x 0) (rpt B (RCh Qp hp dp))) as Hsl.
      { intros pp Qp hp dp ->. apply (ch_pay Ψ Θ B HB pol a pp Qp hp dp K); [by left|exact Hpay]. }
      destruct (pay_conv Ψ ss B pts x P Hsl) as (Hp1 & _ & Hp3).
      apply (tv_app_closed Wmp HW _ _ _ _ _ _ (Some x) (TProd (payload_at (pm P) Tp x) (TSess (SSeq (SSnd (pm P) Tp) S) x))); [bot_false|..].
      * eapply t_conv; [|apply t_konst; [apply lenv_empty_nones|apply (KTSend _ _ _ (pm P) Tp S x)|apply ersp_scoped]].
        -- apply steq_lolli; [apply steq_refl|]. apply steq_sess; [|apply seq_refl].
           by apply (ch_next Ψ Θ B HB pol a P K); [left|].
        -- unfold Tp. rewrite hbot_sersp. intros y Hy. destruct (Hp3 y Hy) as (pp & Qp & hp & dp & -> & ->).
           eapply slt_seqs_r; [|apply se_sym, (Hsl pp Qp hp dp eq_refl)].
           apply (ch_below_ch Ψ Θ B HB _ a); [apply hshape_snd|exact Hpay].
      * eapply (t_pair Wmp Φ Ψ ∅ ∅ ∅ Δ Δ1 Δ2); [by apply comp0|done| |].
        -- bclean; rewrite (tenv_heads0 _ HW), union_empty_l_L. eapply t_conv; [exact Hp1|].
           apply (IH1 ss Ψ B pts ins Δ1); try done.
           by apply (ubs_part Ψ Θ B HB Φ F [] (ef2 ++ [a]) ef1 ss pts ins Γ2 Δ2).
        -- assert (TSess (SSeq (SSnd (pm P) Tp) S) x = trs ss B pts (MCh pol (sndQ pol a P K) (PR h d))) as -> by
             (by rewrite trs_snd).
           apply (IH2 ss Ψ B pts ins Δ2); try done. bclean. apply (ubs_union _ HW); [by apply (ubs_seg Ψ Θ B HB Φ F ef2 ef1 [a])|].
           intros z Hz y Hy. destruct (Hp3 y Hy) as (pp & Qp & hp & dp & -> & ->).
           eapply slt_seqs_r; [|apply se_sym, (Hsl pp Qp hp dp eq_refl)].
           by apply (hi_below_ch Ψ Θ B HB ef2 Qp hp dp z).
      * apply (ch_ub Ψ Θ B HB Φ _ a h d (ef1 ++ ef2 ++ [a])); [apply hshape_snd|done|set_solver|done].
    + simpl in Hok. subst P. simpl aeff. set (x := mwalk (pts n) w).
      apply (tv_app_closed Wmp HW _ _ _ _ _ _ (Some x) (TProd U (TSess (SSeq (SSnd 0 U) S) x))); [bot_false|..].
      * eapply t_conv; [|apply t_konst; [apply lenv_empty_nones|apply (KTSend _ _ _ 0 U S x)|apply (ersp_scoped [] MPUnit)]].
        -- rewrite trs_ch. simpl chpt. rewrite mwalk_app. apply steq_refl.
        -- intros y Hy. by apply elem_of_empty in Hy.
      * eapply (t_pair Wmp Φ Ψ ∅ ∅ ∅ Δ Δ1 Δ2); [by apply comp0|done| |].
        -- bclean; rewrite (tenv_heads0 _ HW), union_empty_l_L. change U with (trs ss B pts (payty MPUnit)).
           apply (IH1 ss Ψ B pts ins Δ1); try done.
           by apply (ubs_part Ψ Θ B HB Φ F [] (ef2 ++ [PTop]) ef1 ss pts ins Γ2 Δ2).
        -- assert (TSess (SSeq (SSnd 0 U) S) x = trs ss B pts (MCh pol (sndQ pol a MPUnit K) (PX n w))) as -> by
             (by rewrite trs_snd).
           bclean. change (heads U) with (∅ : gset point). rewrite sf_union_empty.
           apply (IH2 ss Ψ B pts ins Δ2); try done. by apply (ubs_seg Ψ Θ B HB Φ F ef2 ef1 [PTop]).
      * apply (ubs_ceil Ψ Θ B HB Φ F (ef1 ++ ef2 ++ [PTop])); [set_solver| |done].
        apply (chpt_ok Ψ Θ B HB pts Hp (sndQ pol a MPUnit K) (PX n w) []).
  - (* receive *)
    cbn [rename]. rewrite ren_up2.
    destruct (erel_split B ss pts ins Γ Δ Γ1 Γ2 HΔ Hs) as (Δ1 & Δ2 & Hd & HΔ1 & HΔ2).
    set (S := sinst (slist ss) (polS pol (ers K))). set (Tp := sinst_ty (slist ss) (ersp P)).
    assert (ub_below_s Wmp Ψ Φ (hiz B (ef1 ++ [aeff p a])) (sf_union F (lenv_heads Δ2))) as Hpart.
    { apply (ubs_part Ψ Θ B HB Φ F [] ef2 (ef1 ++ [aeff p a]) ss pts ins Γ2 Δ2); [|done|done].
      by rewrite <-app_assoc. }
    eapply (t_letp Wmp Φ Ψ ∅ ∅ ∅ Δ Δ1 Δ2 F _ _ (trs ss B pts (rpayty p P)) (trs ss B pts (MCh pol K (pnext p))));
      [by apply comp0|done| |].
    + bclean; rewrite (tenv_heads0 _ HW), union_empty_l_L.
      set (x := chpt B pts (rcvQ pol a P K) p).
      apply (tv_app_closed Wmp HW _ _ _ _ _ _ (Some x) (trs ss B pts (MCh pol (rcvQ pol a P K) p))); [bot_false|..].
      * eapply t_conv; [|apply t_konst; [apply lenv_empty_nones|apply (KTRecv _ _ _ (pm P) Tp S x)|apply ersp_scoped]].
        rewrite trs_rcv. apply steq_lolli; [apply steq_refl|]. destruct p as [h d|n w].
        -- destruct Hok as (Hfin & Hpay & Hrise).
           assert (∀ pp Qp hp dp, P = MPChan pp Qp hp dp → seqs Wmp Ψ (pt_slot x 0) (rpt B (RCh Qp hp dp))) as Hsl.
           { intros pp Qp hp dp ->. apply (ch_pay Ψ Θ B HB pol a pp Qp hp dp K); [by right|exact Hpay]. }
           destruct (pay_conv Ψ ss B pts x P Hsl) as (_ & Hp2 & _).
           apply steq_prod; [done|]. rewrite trs_ch. apply steq_sess; [|apply seq_refl].
           by apply (ch_next Ψ Θ B HB pol a P K); [right|].
        -- rewrite pay_px, trs_ch. simpl chpt. rewrite mwalk_app. apply steq_refl.
      * apply (IH1 ss Ψ B pts ins Δ1); try done. by apply (ubs_seg Ψ Θ B HB _ _ ef1 [] [aeff p a]).
      * destruct p as [h d|n w].
        -- destruct Hok as (Hfin & _). by apply (ch_ub Ψ Θ B HB Φ _ a h d (ef1 ++ [a])); [apply hshape_rcv|done|set_solver|].
        -- apply (ubs_ceil Ψ Θ B HB Φ _ (ef1 ++ [PTop])); [set_solver| |done].
           apply (chpt_ok Ψ Θ B HB pts Hp (rcvQ pol a P K) (PX n w) []).
    + apply (IH2 ss Ψ B pts _ _ _ _ Hlss Hss HB Hp).
      * apply (er_keep _ _ _ (Some _)), (er_keep _ _ _ (Some _)), HΔ2.
      * apply (ubs_seg Ψ Θ B HB Φ F ef2 (ef1 ++ [aeff p a]) []). by rewrite app_nil_r, <-app_assoc.
  - (* close, wait *)
    cbn [rename]. set (x := chpt B pts (MEnd a w) p).
    eapply (t_letu Wmp Φ Ψ ∅ ∅ ∅ Δ Δ (lenv_nones Δ)); [by apply comp0|apply lenv_split_nones_r| |].
    + bclean; rewrite (tenv_heads0 _ HW), nones_heads, union_empty_l_L, sf_union_empty.
      apply (tv_app_closed Wmp HW _ _ _ _ _ _ (Some x) (TSess SEnd x)); [bot_false|..].
      * apply t_konst; [apply lenv_empty_nones|apply KTClos|done].
      * unfold x. rewrite <-(trs_end ss B pts pol a w p). apply (IH ss Ψ B pts ins Δ); try done.
        by apply (ubs_seg Ψ Θ B HB _ _ ef [] [aeff p a]).
      * destruct p as [h d|n w'].
        -- by apply (ch_ub Ψ Θ B HB Φ _ a h d (ef ++ [a])); [apply hshape_end|done|set_solver|].
        -- apply (ubs_ceil Ψ Θ B HB Φ _ (ef ++ [PTop])); [set_solver| |done].
           apply (chpt_ok Ψ Θ B HB pts Hp (MEnd a w) (PX n w') []).
    + rewrite trs_unit. apply (tv_unitv Wmp HW). apply nones_unl.
  - (* T-Sel *)
    set (x := chpt B pts (selQ pol a K1 K2) p).
    set (S1 := sinst (slist ss) (polS pol (ers K1))). set (S2 := sinst (slist ss) (polS pol (ers K2))).
    assert (steq Wmp Ψ (TSess (if b then S2 else S1) (pt_slot x (bidx b))) (trs ss B pts (MCh pol (if b then K2 else K1) (pbr p b)))) as Er.
    { rewrite trs_ch. destruct p as [h d|n w].
      - apply steq_sess; [|destruct b; apply seq_refl]. simpl chpt. by apply (ch_branch Ψ Θ B HB pol a K1 K2); [left|apply Hok].
      - simpl chpt. rewrite mwalk_app. destruct b; apply steq_refl. }
    cbn [rename]. apply (tv_app_closed Wmp HW _ _ _ _ _ _ (Some x) (TSess (SPlus S1 S2) x)); [bot_false|..].
    + eapply t_conv; [apply steq_lolli; [apply steq_refl|exact Er]|].
      destruct b; (apply t_konst; [apply lenv_empty_nones| |done]);
        [apply KTSel2, (chpt_br Ψ Θ B HB pts Hp _ p true)|apply KTSel1, (chpt_br Ψ Θ B HB pts Hp _ p false)].
    + unfold x, S1, S2. rewrite <-(trs_sel ss B pts pol a K1 K2 p). apply (IH ss Ψ B pts ins Δ); try done.
      by apply (ubs_seg Ψ Θ B HB _ _ ef [] [aeff p a]).
    + destruct p as [h d|n w].
      * destruct Hok as (Hfin & _). by apply (ch_ub Ψ Θ B HB Φ _ a h d (ef ++ [a])); [apply hshape_sel|done|set_solver|].
      * apply (ubs_ceil Ψ Θ B HB Φ _ (ef ++ [PTop])); [set_solver| |done].
        apply (chpt_ok Ψ Θ B HB pts Hp (selQ pol a K1 K2) (PX n w) []).
  - (* match *)
    cbn [rename]. rewrite !ren_up.
    destruct (erel_split B ss pts ins Γ Δ Γ1 Γ2 HΔ Hs) as (Δ1 & Δ2 & Hd & HΔ1 & HΔ2).
    set (x := chpt B pts (braQ pol a K1 K2) p).
    set (S1 := sinst (slist ss) (polS pol (ers K1))). set (S2 := sinst (slist ss) (polS pol (ers K2))).
    assert (ub_below_s Wmp Ψ Φ (hiz B (ef1 ++ [aeff p a])) (sf_union F (lenv_heads Δ2))) as Hpart.
    { apply (ubs_part Ψ Θ B HB Φ F [] ef2 (ef1 ++ [aeff p a]) ss pts ins Γ2 Δ2); [|done|done].
      by rewrite <-app_assoc. }
    assert (∀ b : bool, steq Wmp Ψ (TSess (if b then S2 else S1) (pt_slot x (bidx b))) (trs ss B pts (MCh pol (if b then K2 else K1) (pbr p b)))) as Er.
    { intros b. rewrite trs_ch. destruct p as [h d|n w].
      - apply steq_sess; [|destruct b; apply seq_refl]. simpl chpt. by apply (ch_branch Ψ Θ B HB pol a K1 K2); [right|apply Hok].
      - simpl chpt. rewrite mwalk_app. destruct b; apply steq_refl. }
    eapply (t_case Wmp Φ Ψ ∅ ∅ ∅ Δ Δ1 Δ2 F _ _ _ (trs ss B pts (MCh pol K1 (pbr p false)))
              (trs ss B pts (MCh pol K2 (pbr p true)))); [by apply comp0|done| | |].
    + bclean; rewrite (tenv_heads0 _ HW), union_empty_l_L.
      apply (tv_app_closed Wmp HW _ _ _ _ _ _ (Some x) (trs ss B pts (MCh pol (braQ pol a K1 K2) p))); [bot_false|..].
      * eapply t_conv; [|apply t_konst; [apply lenv_empty_nones|apply KTBra;
          [apply (chpt_br Ψ Θ B HB pts Hp (braQ pol a K1 K2) p false)|apply (chpt_br Ψ Θ B HB pts Hp (braQ pol a K1 K2) p true)]|done]].
        rewrite trs_bra. apply steq_lolli; [apply steq_refl|]. apply steq_sum; [apply (Er false)|apply (Er true)].
      * apply (IH ss Ψ B pts ins Δ1); try done. by apply (ubs_seg Ψ Θ B HB _ _ ef1 [] [aeff p a]).
      * destruct p as [h d|n w].
        -- destruct Hok as (Hfin & _). by apply (ch_ub Ψ Θ B HB Φ _ a h d (ef1 ++ [a])); [apply hshape_bra|done|set_solver|].
        -- apply (ubs_ceil Ψ Θ B HB Φ _ (ef1 ++ [PTop])); [set_solver| |done].
           apply (chpt_ok Ψ Θ B HB pts Hp (braQ pol a K1 K2) (PX n w) []).
    + apply IHA; try done; [by apply (er_keep _ _ _ (Some _))|].
      apply (ubs_seg Ψ Θ B HB Φ F ef2 (ef1 ++ [aeff p a]) []). by rewrite app_nil_r, <-app_assoc.
    + apply IHB; try done; [by apply (er_keep _ _ _ (Some _))|].
      apply (ubs_seg Ψ Θ B HB Φ F ef2 (ef1 ++ [aeff p a]) []). by rewrite app_nil_r, <-app_assoc.
  - (* fork *)
    cbn [rename]. rewrite rename_fork, trs_unit.
    apply (tv_app_closed Wmp HW _ _ _ _ _ _ None (trs ss B pts (MArr MUnit lo σ MUnit))); [bot_false|..].
    + rewrite trs_arr, trs_unit. apply fork_tr_typed. apply lenv_empty_nones.
    + by apply IH.
    + done.
  - (* T-Eq *)
    destruct Heq as [Hseq Hpos]. eapply t_conv; [|apply IH; done]. rewrite !trs_ch.
    assert (seq (sinst (slist ss) (polS pol (ers Q))) (sinst (slist ss) (polS pol (ers Q')))) as Es.
    { rewrite !polS_sinst. destruct pol; simpl; [apply seq_dual|]; by apply Hseq. }
    destruct p as [h d|n w], p' as [h' d'|n' w']; simpl in Hpos; try done.
    + destruct Hpos as [<- Ho]. apply steq_sess; [|done]. simpl.
      apply (seqs_rpt Ψ Θ B HB). intros v ts Hv. rewrite !(den_ch Ψ Θ B HB). by apply Ho.
    + destruct Hpos as [<- <-]. apply steq_sess; [apply se_refl|done].
  - (* a larger effect *)
    apply IH; try done. by apply (ubs_hle Ψ Θ B HB _ ef ef').
Qed.

(** ** Deadlock freedom *)

(** A closed program of unit type translates to a typed closed thread
    at the strict world [Wmp], so it is deadlock free. *)
Theorem mp2_deadlock_free e ef e' :
  mtyped pc0 [] e MUnit ef e' → deadlock_free (∅, {[+ e' +]}).
Proof.
  intros H. apply (soundness Wmp _ U Wmp_strict). apply ptyped_closed; [repeat constructor|].
  rewrite <-(rename_id e'), (rename_ext e' (λ x, x) (ren_of [])) by done.
  apply (mp2_translate pc0 [] e MUnit ef e' H [] [] proot (pts0 proot) [] [] ∅ (∅, None));
    [done|constructor|apply good_root|apply (pts0_ok [] pc0), good_root|constructor|].
  destruct (hiz proot ef); [|done]. split; simpl; [set_solver|done].
Qed.
