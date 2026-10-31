(** * From derivations of Mordido and Pérez to the static system

    A derivation Θ | Γ ⊢ e : T ⋄ σs ⇝ e′ becomes a derivation of [typed]
    at the priority world [Wmp] ([mp_translate]). The lemma holds at
    every anchor B whose facts the context Ψ provides for every
    valuation of Θ ([good]) and at every frame F above the upper point
    of σs. As for Padovani and Novara (pn/PNTranslate.v on branch
    orders-lr), it quantifies over the places [ins] where the
    environment Δ has extra unlimited or spent entries, and types e′
    renamed past them ([erel]). [soundness] then makes every closed
    program of type unit deadlock free ([mp_deadlock_free]). *)

From stdpp Require Import base gmap numbers.
From LRGV Require Export mp.MPWorld.

Set Default Proof Using "All".

Set Default Proof Using "All".

(** ** Renaming past inserted entries *)

Fixpoint ren_of (ins : list bool) (x : nat) : nat :=
  match ins with
  | [] => x
  | false :: ins => match x with 0 => 0 | S x => S (ren_of ins x) end
  | true :: ins => S (ren_of ins x)
  end.

Lemma ren_of_inj ins x y : ren_of ins x = ren_of ins y → x = y.
Proof.
  revert x y. induction ins as [|[] ins IH]; intros x y; simpl; [done| |].
  - intros [=]. by apply IH.
  - destruct x, y; simpl; try done. intros [=]. f_equal. by apply IH.
Qed.

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

Lemma ren_box ins e :
  rename (upren (upren (ren_of ins))) (rename (upren S) e)
  = rename (ren_of (false :: true :: ins)) e.
Proof. rewrite rename_rename. apply rename_ext. by intros [|x]. Qed.

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

  Lemma nones_nones Δ : lenv_nones (lenv_nones Δ) = lenv_nones Δ.
  Proof. induction Δ; simpl; congruence. Qed.

  Lemma lenv_split_nones_r Δ : lenv_split Δ Δ (lenv_nones Δ).
  Proof. apply lenv_split_comm, lenv_split_nones_l. Qed.

  (** A variable whose other entries are unlimited. *)
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
End lenv.

Section rules.
  Context (W : world) (HW : world_wf W).

  Lemma tv_var_unl Φ Ψ Δ F x T :
    Δ !! x = Some (Some T) → (∀ y T', y ≠ x → Δ !! y = Some (Some T') → unlimited T') →
    typed W Φ Ψ ∅ Δ F (Var x) T.
  Proof. intros H1 H2. eapply t_wk; [by apply lonly_wk_unl|]. apply t_var. by apply lonly_only. Qed.

  Lemma tv_unit_unl Φ Ψ Δ F : lenv_unl Δ → typed W Φ Ψ ∅ Δ F EUnit TUnit.
  Proof. intros H. eapply t_wk; [by apply unl_wk|]. apply t_unit, lenv_empty_nones. Qed.

  (** E-Exp for a closed constraint. *)
  Lemma tv_box Φ Ψ Δ F e m C ub T :
    lenv_unl Δ → bc_env C = [] →
    (∀ φ, φ ∉ dom Φ →
      typed W (<[φ := ub]> (fhyps_pinst (pshift m) Φ)) (hyps_inst (pshift m) Ψ ++ [(C, ids m)]) ∅
        (lenv_pinst (pshift m) (Some (TBox m 0 C (TLolli ub None TUnit T)) :: Δ)) (∅, Some φ) e T) →
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

  (** A closed function applied to an argument. *)
  Lemma tv_app_closed Φ Ψ Δ F f e ub T U' :
    typed W Φ Ψ ∅ (lenv_nones Δ) (sf_union F (lenv_heads Δ)) f (TLolli ub None T U') →
    typed W Φ Ψ ∅ Δ F e T →
    ub_below_s W Ψ Φ ub F →
    typed W Φ Ψ ∅ Δ F (App f e) U'.
  Proof.
    intros Hf He Hub. eapply (t_app W Φ Ψ ∅ ∅ ∅ Δ (lenv_nones Δ) Δ F _ _ ub None).
    - by apply comp0.
    - apply lenv_split_nones_l.
    - done.
    - by rewrite (tenv_heads0 W HW), union_empty_l_L.
    - destruct F as [P o]. unfold sf_union. simpl. by rewrite union_empty_r_L.
  Qed.

  Lemma ubs_fresh Ψ Φ φ u : ub_below_s W Ψ (<[φ := u]> Φ) u (∅, Some φ).
  Proof.
    destruct u as [u|]; [|done]. split; simpl; [set_solver|].
    intros φ' [=<-]. apply (fl_v (FCtx _ _ _)). simpl. by rewrite lookup_insert_eq.
  Qed.

  Lemma ubs_union Ψ Φ u F X :
    ub_below_s W Ψ Φ u F → (∀ x, u = Some x → ∀ h, h ∈ X → slt W Ψ x h) →
    ub_below_s W Ψ Φ u (sf_union F X).
  Proof.
    destruct u as [x|]; [|done]. intros [H1 H2] HX. split; [|done]. simpl.
    intros y [Hy|Hy]%elem_of_union; [by apply H1|]. apply fl_points. by apply (HX x).
  Qed.

  Lemma ubs_lower Ψ Φ a b F :
    (∀ x, a = Some x → ∃ y, b = Some y ∧ sle W Ψ x y) →
    ub_below_s W Ψ Φ b F → ub_below_s W Ψ Φ a F.
  Proof.
    intros Hab Hb. destruct a as [x|]; [|done].
    destruct (Hab x eq_refl) as (y & -> & Hxy). destruct Hb as [H1 H2].
    destruct Hxy as [Hxy|Hxy]; split.
    - intros z Hz. eapply (fl_eql (FCtx W Ψ Φ)); [exact Hxy|by apply H1].
    - intros φ Hφ. eapply (fl_eql (FCtx W Ψ Φ)); [exact Hxy|by apply H2].
    - intros z Hz. eapply (fl_trans (FCtx W Ψ Φ)); [apply fl_points; exact Hxy|by apply H1].
    - intros φ Hφ. eapply (fl_trans (FCtx W Ψ Φ)); [apply fl_points; exact Hxy|by apply H2].
  Qed.

  (** The upper point of a frame variable's own hypothesis. *)
  Lemma ubs_hyp Ψ Φ φ x u :
    Φ !! φ = Some (Some u) → sle W Ψ x u → ub_below_s W Ψ Φ (Some x) (∅, Some φ).
  Proof.
    intros Hφ Hx. apply ub_below_s_intro; [set_solver|]. by exists u.
  Qed.
End rules.

Inductive erel (B : point) : list bool → menv → lenv → Prop :=
  | er_nil : erel B [] [] []
  | er_keep o ins Γ Δ : erel B ins Γ Δ → erel B (false :: ins) (o :: Γ) (fmap (tr B) o :: Δ)
  | er_skip o ins Γ Δ :
      (o = None ∨ ∃ T, o = Some T ∧ unlimited T) →
      erel B ins Γ Δ → erel B (true :: ins) Γ (o :: Δ).

Section erel.
  Context (B : point).

  Lemma erel_split ins Γ Δ Γ1 Γ2 :
    erel B ins Γ Δ → msplit Γ Γ1 Γ2 →
    ∃ Δ1 Δ2, lenv_split Δ Δ1 Δ2 ∧ erel B ins Γ1 Δ1 ∧ erel B ins Γ2 Δ2.
  Proof.
    intros H. revert Γ1 Γ2. induction H as [|o ins Γ Δ H IH|o ins Γ Δ Ho H IH]; intros Γ1 Γ2 Hs.
    - inversion Hs; subst. exists [], []. split_and!; constructor.
    - inversion Hs as [|? ? ? Hs'|t ? ? ? Hs'|t ? ? ? Hs'|t ? ? ? Ht Hs']; subst;
        destruct (IH _ _ Hs') as (Δ1 & Δ2 & Hd & H1 & H2).
      + exists (None :: Δ1), (None :: Δ2). split_and!; [simpl; by constructor|apply (er_keep _ None)..]; done.
      + exists (Some (tr B t) :: Δ1), (None :: Δ2). split_and!; [simpl; by constructor
          |apply (er_keep _ (Some t))|apply (er_keep _ None)]; done.
      + exists (None :: Δ1), (Some (tr B t) :: Δ2). split_and!; [simpl; by constructor
          |apply (er_keep _ None)|apply (er_keep _ (Some t))]; done.
      + exists (Some (tr B t) :: Δ1), (Some (tr B t) :: Δ2). split_and!;
          [apply lsplit_unl; [by apply tr_unlimited|done]|apply (er_keep _ (Some t))..]; done.
    - destruct (IH _ _ Hs) as (Δ1 & Δ2 & Hd & H1 & H2). exists (o :: Δ1), (o :: Δ2).
      split_and!; [|by constructor..].
      destruct Ho as [->|(T & -> & HT)]; [by constructor|by apply lsplit_unl].
  Qed.

  Lemma erel_lookup ins Γ Δ x o :
    erel B ins Γ Δ → Γ !! x = Some o → Δ !! ren_of ins x = Some (fmap (tr B) o).
  Proof.
    intros H. revert x. induction H as [|o' ins Γ Δ H IH|o' ins Γ Δ Ho H IH]; intros x Hx; simpl.
    - done.
    - destruct x; simpl in *; [by simplify_eq|by apply IH].
    - by apply IH.
  Qed.

  Lemma erel_inv ins Γ Δ y T :
    erel B ins Γ Δ → Δ !! y = Some (Some T) →
    (∃ x t, y = ren_of ins x ∧ Γ !! x = Some (Some t) ∧ T = tr B t) ∨ unlimited T.
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
    world_wf W → erel B ins Γ Δ → menv_only_un Γ x t →
    typed W Φ Ψ ∅ Δ F (Var (ren_of ins x)) (tr B t).
  Proof.
    intros HW H [Hx Hun]. apply tv_var_unl; [done|by apply (erel_lookup _ Γ _ _ (Some t))|].
    intros y T Hy HyT. destruct (erel_inv _ _ _ _ _ H HyT) as [(x' & t' & -> & Hx' & ->)|]; [|done].
    apply tr_unlimited, (Hun x'); [|done]. intros ->. done.
  Qed.

  Lemma erel_unl ins Γ Δ : erel B ins Γ Δ → menv_un Γ → lenv_unl Δ.
  Proof.
    intros H HΓ o Ho. apply list_elem_of_lookup_1 in Ho as [y Hy].
    destruct o as [T|]; [|by left]. right. exists T. split; [done|].
    destruct (erel_inv _ _ _ _ _ H Hy) as [(x & t & -> & Hx & ->)|]; [|done].
    apply tr_unlimited, HΓ. by eapply list_elem_of_lookup_2.
  Qed.

  Lemma erel_heads ins Γ Δ h :
    erel B ins Γ Δ → h ∈ lenv_heads Δ → ∃ t, Some t ∈ Γ ∧ h ∈ heads (tr B t).
  Proof.
    intros H. induction H as [|o ins Γ Δ H IH|o ins Γ Δ Ho H IH]; simpl; intros Hh.
    - set_solver.
    - destruct o as [t|]; simpl in Hh.
      + apply elem_of_union in Hh as [Hh|Hh]; [exists t; split; [by left|done]|].
        destruct (IH Hh) as (t' & ? & ?). exists t'. split; [by right|done].
      + destruct (IH Hh) as (t' & ? & ?). exists t'. split; [by right|done].
    - destruct Ho as [->|(T & -> & HT)]; simpl in Hh; [by apply IH|].
      destruct T; try done. simpl in Hh. apply IH. set_solver.
  Qed.

  Lemma erel_pinst ins Γ Δ σ B' :
    erel B ins Γ Δ → menv_un Γ → erel B' ins Γ (lenv_pinst σ Δ).
  Proof.
    intros H. induction H as [|o ins Γ Δ H IH|o ins Γ Δ Ho H IH]; intros HΓ; simpl.
    - constructor.
    - assert (menv_un Γ) as HΓ' by (intros t Ht; apply HΓ; by right).
      destruct o as [t|]; simpl.
      + rewrite tr_pinst, (tr_un _ B'); [|apply HΓ; by left].
        apply (er_keep _ (Some t)). by apply IH.
      + apply (er_keep _ None). by apply IH.
    - apply er_skip; [|by apply IH]. destruct Ho as [->|(T & -> & HT)]; [by left|right].
      eexists. split; [done|]. by apply unlimited_pinst.
  Qed.
End erel.

Lemma sf_union_empty F : sf_union F ∅ = F.
Proof. destruct F as [P o]. unfold sf_union. simpl. by rewrite union_empty_r_L. Qed.

(** ** Scoping and empty environments *)

Lemma empty_heads Δ : lenv_empty Δ → lenv_heads Δ = ∅.
Proof. intros H. apply unl_heads. intros o Ho. left. by apply H. Qed.

Lemma empty_lookup Δ y T : lenv_empty Δ → Δ !! y = Some (Some T) → False.
Proof. intros H Hy. apply list_elem_of_lookup_2 in Hy. by apply H in Hy. Qed.

Lemma lenv_split_empty' Δ : lenv_empty Δ → lenv_split Δ Δ Δ.
Proof.
  induction Δ as [|o Δ IH]; intros H; [constructor|].
  rewrite (H o) by set_solver. constructor. apply IH. intros o' Ho'. apply H. set_solver.
Qed.

Lemma empty_unl Δ : lenv_empty Δ → lenv_unl Δ.
Proof. intros H o Ho. left. by apply H. Qed.

Ltac var_others HΔ :=
  let y := fresh "y" in let T := fresh "T" in let Hne := fresh in let Hy := fresh in
  intros y T Hne Hy; destruct y as [|[|y]]; simpl in Hy; try done;
  exfalso; by eapply empty_lookup; [exact HΔ|exact Hy].

(** ** The terms of the translation *)


(** ** Effects *)

Lemma xmaxl_app v l1 l2 : xmaxl v (l1 ++ l2) = xmax (xmaxl v l1) (xmaxl v l2).
Proof.
  induction l1 as [|ρ l1 IH]; simpl; [by destruct (xmaxl v l2)|].
  rewrite IH. destruct (evalp v ρ), (xmaxl v l1), (xmaxl v l2); simpl; f_equal; lia.
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

Lemma hlen_top l : PTop ∈ l → hlen l = 0.
Proof. intros H. unfold hlen. by rewrite bool_decide_eq_true_2. Qed.
Lemma hlen_notop l : PTop ∉ l → hlen l = length l.
Proof. intros H. unfold hlen. by rewrite bool_decide_eq_false_2. Qed.

Lemma hi_hi a b n n' : xle a b → b ≠ XT → n < n' → rlt (rank (DHi a n)) (rank (DHi b n')).
Proof. destruct a, b; simpl; try done; lia. Qed.

Lemma hi_hi_lt a b n n' : xlt a b → rlt (rank (DHi a n)) (rank (DHi b n')).
Proof. destruct a, b; simpl; try done; lia. Qed.

Section heads.
  Context (Ψ : hyps) (Θ : pctx) (B : point) (HB : good Ψ Θ B).

  (** The upper point of a smaller effect lies at or below. *)
  Lemma hi_le ef ef' x :
    hle Θ ef ef' → hiz B ef = Some x → ∃ y, hiz B ef' = Some y ∧ sle Wmp Ψ x y.
  Proof.
    intros Hle Hx. destruct ef as [|ρ ef0]; [done|]. injection Hx as <-. set (ef := ρ :: ef0).
    assert (∀ l, l ≠ [] → hiz B l = Some (rpt B (RHi l))) as Hz by (by intros [|??]).
    assert (∀ e2, PTop ∈ e2 → e2 ≠ [] → sle Wmp Ψ (rpt B (RHi ef)) (rpt B (RHi e2))) as Htop.
    { intros e2 Ht Hne. destruct (decide (PTop ∈ ef)) as [Ht'|Ht'].
      - left. apply (gd_eq _ _ _ HB); [done|done|]. intros v Hv. rewrite !(den_hi _ _ _ HB) by done.
        by rewrite !xmaxl_top, !hlen_top by done.
      - right. apply (gd_lt _ _ _ HB); [done|done|]. intros v Hv. rewrite !(den_hi _ _ _ HB) by done.
        rewrite (xmaxl_top v e2) by done. pose proof (xmaxl_notop v ef Ht').
        destruct (xmaxl v ef); simpl; done. }
    destruct Hle as [Hn|[Ht|[(l1 & l2 & ->)|[Hne Hs]]]]; [done| | |].
    - assert (ef' ≠ []) as Hne by (intros ->; by apply elem_of_nil in Ht).
      exists (rpt B (RHi ef')). split; [by apply Hz|]. by apply Htop.
    - exists (rpt B (RHi (l1 ++ ef ++ l2))). split; [apply Hz; by destruct l1|].
      destruct (decide (l1 = [] ∧ l2 = [])) as [[-> ->]|Hl].
      { rewrite app_nil_r. left. apply se_refl. }
      destruct (decide (PTop ∈ l1 ++ ef ++ l2)) as [Ht|Ht]; [apply Htop; [done|by destruct l1]|].
      right. apply (gd_lt _ _ _ HB); [done|done|]. intros v Hv. rewrite !(den_hi _ _ _ HB) by done.
      rewrite !hlen_notop by set_solver. apply hi_hi.
      + rewrite !xmaxl_app. eapply xle_trans; [apply xle_max_l|apply xle_max_r].
      + by apply xmaxl_notop.
      + rewrite !length_app. destruct l1, l2; simpl in *; try lia. naive_solver.
    - exists (rpt B (RHi ef')). split; [by apply Hz|]. right.
      apply (gd_lt _ _ _ HB); [done|done|]. intros v Hv. rewrite !(den_hi _ _ _ HB) by done.
      apply hi_hi_lt. by apply Hs.
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

  Lemma envp_in Γ t ρ : Some t ∈ Γ → ρ ∈ tprios t → ρ ∈ envp Γ.
  Proof. intros Ht Hρ. destruct (envp_seg Γ t Ht) as (l1 & l2 & ->). set_solver. Qed.

  (** An upper point below every head of the environment. *)
  Lemma env_hi_below ins Γ Δ ef x h :
    erel B ins Γ Δ → plt Θ ef (envp Γ) → hiz B ef = Some x → h ∈ lenv_heads Δ → slt Wmp Ψ x h.
  Proof.
    intros H Hlt Hx Hh. destruct (erel_heads _ _ _ _ _ H Hh) as (t & Ht & Hh').
    destruct ef as [|ρ0 ef0]; [done|]. injection Hx as <-.
    destruct t as [|p Q hh d|T lo ef' V|]; simpl in Hh'; try set_solver.
    - apply elem_of_singleton in Hh' as ->. apply (gd_lt _ _ _ HB); [done|done|].
      intros v Hv. rewrite (den_hi _ _ _ HB), (rank_ch _ _ _ HB) by done. apply hi_chan.
      apply (Hlt v Hv). apply (envp_in Γ (MChan p Q hh d)); [done|by left].
    - apply elem_of_singleton in Hh' as ->. apply (gd_lt _ _ _ HB); [done|done|].
      intros v Hv. rewrite (den_hi _ _ _ HB), (den_lo _ _ _ HB) by done. apply hi_lo.
      intros ρ Hρ. apply (Hlt v Hv). by apply (envp_in Γ (MArr T lo ef' V)).
  Qed.

  Lemma hi_below_lo ef lo x :
    plt Θ ef lo → hiz B ef = Some x → slt Wmp Ψ x (rpt B (RLo lo)).
  Proof.
    intros Hlt Hx. destruct ef as [|ρ0 ef0]; [done|]. injection Hx as <-.
    apply (gd_lt _ _ _ HB); [done|done|]. intros v Hv.
    rewrite (den_hi _ _ _ HB), (den_lo _ _ _ HB) by done. apply hi_lo. by apply Hlt.
  Qed.

  Lemma hi_below_ch ef Q h d x :
    plt Θ ef [chead Q h d] → hiz B ef = Some x → slt Wmp Ψ x (rpt B (RCh Q h d)).
  Proof.
    intros Hlt Hx. destruct ef as [|ρ0 ef0]; [done|]. injection Hx as <-.
    apply (gd_lt _ _ _ HB); [done|done|]. intros v Hv.
    rewrite (den_hi _ _ _ HB), (rank_ch _ _ _ HB) by done. apply hi_chan. apply Hlt; [done|by left].
  Qed.

  (** The lower point of the environment lies at or below its heads. *)
  Lemma env_lo_below ins Γ Δ h :
    erel B ins Γ Δ → h ∈ lenv_heads Δ → sle Wmp Ψ (rpt B (RLo (envp Γ))) h.
  Proof.
    intros H Hh. destruct (erel_heads _ _ _ _ _ H Hh) as (t & Ht & Hh').
    destruct t as [|p Q hh d|T lo ef' V|]; simpl in Hh'; try set_solver.
    - apply elem_of_singleton in Hh' as ->. right. apply (gd_lt _ _ _ HB); [done|done|].
      intros v Hv. rewrite (den_lo _ _ _ HB), (rank_ch _ _ _ HB) by done. apply lo_chan.
      apply xminl_le. apply (envp_in Γ (MChan p Q hh d)); [done|by left].
    - apply elem_of_singleton in Hh' as ->.
      destruct (envp_seg Γ _ Ht) as (l1 & l2 & E). simpl in E.
      destruct (decide (l1 = [] ∧ l2 = [])) as [[-> ->]|Hl].
      { rewrite E, app_nil_r. left. apply se_refl. }
      right. apply (gd_lt _ _ _ HB); [done|done|]. intros v Hv.
      rewrite !(den_lo _ _ _ HB) by done. rewrite E. apply lo_lo.
      + rewrite !xminl_app. eapply xle_trans; [apply xmin_le_r|apply xmin_le_l].
      + rewrite !length_app. destruct l1, l2; simpl in *; try lia. naive_solver.
  Qed.
End heads.
