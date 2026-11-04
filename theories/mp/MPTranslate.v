(** * From derivations of Mordido and Pérez to the static system

    A derivation Θ | Γ ⊢ e : T ⋄ σs ⇝ e′ becomes a derivation of [typed]
    at the priority world [Wmp] ([mp_translate]). The lemma holds at
    every anchor B whose facts the context Ψ provides for every
    valuation of Θ ([good]) and at every future F above the upper point
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

(** Translated types hold no existential, so no ⊥ flag arises
    (sharp edges 103). *)
Lemma hbot_tr B T : hbot (tr B T) = false.
Proof. by destruct T. Qed.

Lemma hbot_ersp P : hbot (ersp P) = false.
Proof. by destruct P. Qed.

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
    ?hbot_tr, ?hbot_ersp, ?lenv_bot_nones, ?orb_false_l;
  first [done|by apply lenv_bot_empty|bot_extra
        |simpl; first [done|by apply lenv_bot_empty|bot_extra]].

Ltac lbhb := unfold lb_below_hb;
  try match goal with |- context [lenv_bot ?D] =>
    replace (lenv_bot D) with false by (symmetry; bot_false) end; simpl.

(** Drop the flag of every future whose flag is false. *)
Ltac bclean :=
  repeat match goal with |- context [sf_unionb ?F ?X ?b] =>
    rewrite (sf_unionb_false F X b) by bot_false end.

Section rules.
  Context (W : world) (HW : world_wf W).

  Lemma tv_var_unl Φ Ψ Δ F x T :
    Δ !! x = Some (Some T) → (∀ y T', y ≠ x → Δ !! y = Some (Some T') → unlimited T') →
    typed W Φ Ψ ∅ Δ F (Var x) T.
  Proof. intros H1 H2. eapply t_weak; [by apply lonly_wk_unl|]. apply t_var. by apply lonly_only. Qed.

  Lemma tv_unit_unl Φ Ψ Δ F : lenv_unl Δ → typed W Φ Ψ ∅ Δ F EUnit TUnit.
  Proof. intros H. eapply t_weak; [by apply unl_wk|]. apply t_unit, lenv_empty_nones. Qed.

  (** E-Exp for a closed constraint. *)
  Lemma tv_box Φ Ψ Δ F e m C ub T :
    lenv_unl Δ → bc_env C = [] →
    (∀ φ, φ ∉ dom Φ →
      typed W (<[φ := ub]> (fhyps_pinst (pshift m) Φ)) (hyps_inst (pshift m) Ψ ++ [(C, ids m)]) ∅
        (lenv_pinst (pshift m) (Some (TBox m 0 C (TLolli ub None TUnit T)) :: Δ)) (∅, Some (FVar φ)) e T) →
    typed W Φ Ψ ∅ Δ F (EBox e) (TBox m 0 C (TLolli ub None TUnit T)).
  Proof.
    intros HΔ HC H. set (φ := fresh (dom Φ)). apply (t_exp W Φ Ψ Δ F e m 0 C ub T φ); [done|apply is_fresh|].
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

  (** The upper point of a future variable's own hypothesis. *)
  Lemma ubs_hyp Ψ Φ φ x u :
    Φ !! φ = Some (Some u) → sle W Ψ x u → ub_below_s W Ψ Φ (Some x) (∅, Some (FVar φ)).
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

Lemma erel_bot B ins Γ Δ : erel B ins Γ Δ → lenv_bot Δ = false.
Proof.
  induction 1 as [|o ins Γ Δ _ IH|o ins Γ Δ Ho _ IH]; simpl; [done| |].
  - destruct o; simpl; [by rewrite hbot_tr|done].
  - destruct Ho as [->|(T & -> & HT)]; simpl; [done|]. destruct T; done.
Qed.

Ltac bot_extra ::= by eapply erel_bot.

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

(** ** Channels *)

Lemma mact_mhd Q h d : mact Q → mhd Q h d = (Q, h).
Proof. by destruct Q. Qed.

Lemma mact_mmap f Q : mact Q → mact (mmap f Q).
Proof. by destruct Q. Qed.

Lemma mact_subV X Q : mact Q → mact (msubV X Q).
Proof. by destruct Q. Qed.

Lemma mact_munf S0 h : mact S0 → mact (munf S0 h).
Proof. intros H. apply mact_subV, mact_mmap, H. Qed.

Lemma xrk_lt a e : xlt a e → rlt (xrk a 1 (KT 1)) (xrk e 1 (KT 1)).
Proof. destruct a, e; simpl; lia. Qed.

Lemma xmaxl_single v a : xmaxl v [a] = evalp v a.
Proof. simpl. by destruct (evalp v a). Qed.

Lemma xmaxl_in v a l : a ∈ l → xle (evalp v a) (xmaxl v l).
Proof.
  induction l as [|b l IH]; intros H; [by apply elem_of_nil in H|].
  apply elem_of_cons in H as [->|H]; simpl; [apply xle_max_l|].
  eapply xle_trans; [by apply IH|apply xle_max_r].
Qed.

Lemma ch_hi a x n : pfin a → xle (evalp [] a) x → rlt (xrk (evalp [] a) 1 (KT 1)) (rank (DHi x n)).
Proof. destruct a; simpl; try done; destruct x; simpl; lia. Qed.

Section chan.
  Context (Ψ : hyps) (Θ : pctx) (B : point) (HB : good Ψ Θ B).
  Context (pol : bool) (Q : msty) (h : prio) (d : Z) (Hw : mwf Q).
  Abbreviation Q1 := (mhd Q h d).1.
  Abbreviation h1 := (mhd Q h d).2.
  Abbreviation x := (rpt B (RCh Q h d)).

  Lemma ch_conv :
    steq Wmp Ψ (tr B (MChan pol Q h d)) (TSess (polS pol (ers Q1)) x) ∧
    steq Wmp Ψ (TSess (polS pol (ers Q1)) x) (tr B (MChan pol Q h d)).
  Proof.
    pose proof (ers_mhd Q h d Hw) as E. simpl.
    assert (seq (polS pol (ers Q)) (polS pol (ers Q1))) as E'
      by (destruct pol; simpl; [by apply seq_dual|done]).
    split; (split; [apply se_refl|]); [done|by apply seq_sym].
  Qed.

  Lemma den_x v : models Θ v → den v x = DCh (mmap (pclose v) Q1) (pclose v h1) d.
  Proof. intros Hv. rewrite (den_ch _ _ _ HB) by done. unfold dch. by rewrite mhd_pclose. Qed.

  Lemma rank_x v : models Θ v → rank (den v x) = xrk (evalp v (hprio Q1)) 1 (KT 1).
  Proof. intros Hv. rewrite den_x by done. simpl. rewrite hprio_mmap by done. by rewrite evalp_pclose. Qed.

  (** The point after a message is the point of the continuation. *)
  Lemma ch_next a P K :
    (Q1 = MSnd a P K ∨ Q1 = MRcv a P K) → plt Θ [a] [chead K h1 d] →
    seqs Wmp Ψ (pt_shift 1 x) (rpt B (RCh K h1 d)).
  Proof.
    intros HQ Hr. apply (gd_eq _ _ _ HB); [done|done|]. intros v Hv.
    rewrite den_shift, den_x, (den_ch _ _ _ HB) by done. unfold dsh, guard.
    assert (dnext (DCh (mmap (pclose v) Q1) (pclose v h1) d) = dch (mmap (pclose v) K) (pclose v h1) d) as En
      by (destruct HQ as [-> | ->]; done).
    rewrite En. rewrite decide_True; [done|]. rewrite dch_rank.
    destruct HQ as [-> | ->]; simpl; rewrite evalp_pclose; apply xrk_lt;
      specialize (Hr v Hv _ (list_elem_of_here _ _)); by rewrite xmaxl_single in Hr.
  Qed.

  (** The point after a choice of branch b. *)
  Lemma ch_branch a K1 K2 b :
    (Q1 = MSel a K1 K2 ∨ Q1 = MBra a K1 K2) → plt Θ [a] [chead K1 h1 d; chead K2 h1 d] →
    seqs Wmp Ψ (pt_payload x (bidx b)) (rpt B (RCh (if b then K2 else K1) h1 d)).
  Proof.
    intros HQ Hr. apply (gd_eq _ _ _ HB); [done|done|]. intros v Hv.
    rewrite den_br, den_x, (den_ch _ _ _ HB) by (try done; rewrite den_x by done; by destruct HQ as [-> | ->]).
    unfold dbr, guard.
    assert (∀ K, K = K1 ∨ K = K2 → xlt (evalp v a) (evalp v (chead K h1 d))) as HK.
    { intros K HK. rewrite <-xmaxl_single. apply Hr; [done|]. destruct HK as [->| ->]; set_solver. }
    destruct HQ as [-> | ->], b; simpl; (rewrite decide_True; [done|]);
      rewrite mhd_pclose; simpl; rewrite hprio_mmap by done; rewrite !evalp_pclose; apply xrk_lt, HK; auto.
  Qed.

  (** A choice point lies below the point x[i] of each branch (K11). *)
  Lemma ch_branch_lt a K1 K2 b :
    (Q1 = MSel a K1 K2 ∨ Q1 = MBra a K1 K2) → slt Wmp Ψ x (pt_payload x (bidx b)).
  Proof.
    intros HQ. apply (gd_lt _ _ _ HB); [done|done|]. intros v Hv.
    rewrite den_br by (rewrite den_x by done; by destruct HQ as [-> | ->]). apply rank_dbr.
  Qed.

  (** The payload point x[0] is the point of the payload channel. *)
  Lemma ch_pay a pp Qp hp dp K :
    (Q1 = MSnd a (MPChan pp Qp hp dp) K ∨ Q1 = MRcv a (MPChan pp Qp hp dp) K) →
    seqs Wmp Ψ (pt_payload x 0) (rpt B (RCh Qp hp dp)).
  Proof.
    intros HQ. apply (gd_eq _ _ _ HB); [done|done|]. intros v Hv.
    rewrite den_payload, den_x, (den_ch _ _ _ HB) by done. by destruct HQ as [-> | ->].
  Qed.

  (** The action lies below the upper point of an effect that holds it. *)
  Lemma ch_below_hi a ef :
    hprio Q1 = a → pfin a → a ∈ ef → slt Wmp Ψ x (rpt B (RHi ef)).
  Proof.
    intros Ha Hf Hin. apply (gd_lt _ _ _ HB); [done|done|]. intros v Hv.
    rewrite rank_x, (den_hi _ _ _ HB), Ha by done. rewrite <-(evalp_pclose v a).
    apply ch_hi; [by destruct a|]. rewrite evalp_pclose. by apply xmaxl_in.
  Qed.

  Lemma ch_ub Φ a ef F :
    hprio Q1 = a → pfin a → a ∈ ef → ub_below_s Wmp Ψ Φ (hiz B ef) F → ub_below_s Wmp Ψ Φ (Some x) F.
  Proof.
    intros Ha Hf Hin. apply (ubs_lower Wmp Wmp_wf). intros y [=<-].
    exists (rpt B (RHi ef)). split; [by destruct ef; [by apply elem_of_nil in Hin|]|].
    right. by apply (ch_below_hi a).
  Qed.

  (** The action lies below the heads of what it carries and of what
      the thread still holds. *)
  Lemma ch_below_lt a l y :
    hprio Q1 = a → pfin a → plt Θ [a] l →
    pt_root y = pt_root B →
    (∀ v, models Θ v → ∃ ρ, ρ ∈ l ∧ xle (evalp v ρ) XT ∧ rank (den v y) = xrk (evalp v ρ) 1 (KT 1)) →
    slt Wmp Ψ x y.
  Proof.
    intros Ha Hf Hl Hy Hd. apply (gd_lt _ _ _ HB); [done|done|]. intros v Hv.
    destruct (Hd v Hv) as (ρ & Hρ & _ & ->). rewrite rank_x, Ha by done. apply xrk_lt.
    specialize (Hl v Hv ρ Hρ). by rewrite xmaxl_single in Hl.
  Qed.
End chan.

Lemma ch_inst Ψ Θ B pol S0 h d :
  good Ψ Θ B → rbody S0 → mact S0 →
  steq Wmp Ψ (tr B (MChan pol (MRec S0) h d)) (tr B (MChan pol (munf S0 h) (padd h d) d)) ∧
  steq Wmp Ψ (tr B (MChan pol (munf S0 h) (padd h d) d)) (tr B (MChan pol (MRec S0) h d)).
Proof.
  intros HB Hb Ha.
  assert (seqs Wmp Ψ (rpt B (RCh (MRec S0) h d)) (rpt B (RCh (munf S0 h) (padd h d) d))) as Hx.
  { apply (gd_eq _ _ _ HB); [done|done|]. intros v Hv. rewrite !(den_ch _ _ _ HB) by done.
    unfold dch. rewrite !mhd_pclose. rewrite (mact_mhd (munf S0 h)) by by apply mact_munf. done. }
  pose proof (ers_mhd (MRec S0) h d (conj Hb Ha)) as E. simpl in E.
  assert (seq (polS pol (SMu (ers S0))) (polS pol (ers (munf S0 h)))) as E'
    by (destruct pol; unfold polS; [by apply seq_dual|done]).
  split; simpl; split; [done|done|by apply se_sym|by apply seq_sym].
Qed.

(** ** The head action, erased *)

Lemma view_snd pol Q a P K : mview pol Q = ASnd a P K →
  polS pol (ers Q) = SSeq (SSnd (pm P) (ersp P)) (polS pol (ers K)) ∧ hprio Q = a ∧
  (Q = MSnd a P K ∨ Q = MRcv a P K).
Proof. destruct pol, Q; simpl; intros H; try discriminate; injection H as <- <- <-; auto. Qed.

Lemma view_rcv pol Q a P K : mview pol Q = ARcv a P K →
  polS pol (ers Q) = SSeq (SRcv (pm P) (ersp P)) (polS pol (ers K)) ∧ hprio Q = a ∧
  (Q = MSnd a P K ∨ Q = MRcv a P K).
Proof. destruct pol, Q; simpl; intros H; try discriminate; injection H as <- <- <-; auto. Qed.

Lemma view_end pol Q a : mview pol Q = AEnd a → polS pol (ers Q) = SEnd ∧ hprio Q = a.
Proof. destruct pol, Q; simpl; intros H; try discriminate; injection H as <-; auto. Qed.

Lemma view_sel pol Q a K1 K2 : mview pol Q = ASel a K1 K2 →
  polS pol (ers Q) = SPlus (polS pol (ers K1)) (polS pol (ers K2)) ∧ hprio Q = a ∧
  (Q = MSel a K1 K2 ∨ Q = MBra a K1 K2).
Proof. destruct pol, Q; simpl; intros H; try discriminate; injection H as <- <- <-; auto. Qed.

Lemma view_bra pol Q a K1 K2 : mview pol Q = ABra a K1 K2 →
  polS pol (ers Q) = SWith (polS pol (ers K1)) (polS pol (ers K2)) ∧ hprio Q = a ∧
  (Q = MSel a K1 K2 ∨ Q = MBra a K1 K2).
Proof. destruct pol, Q; simpl; intros H; try discriminate; injection H as <- <- <-; auto. Qed.

(** ** Forcing at an anchor

    The type of a priority abstraction read at B[RAnc σs] is its
    instance T[σs/ιs] read at B. *)

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
Lemma xminl_psub v σ l : Forall pfin σ → xminl (evalZ v <$> σ) l = xminl v (psub σ <$> l).
Proof. intros Hσ. induction l; simpl; [done|]. by rewrite IHl, evalp_psub. Qed.

Lemma hlen_psub σ l : Forall pfin σ → hlen (psub σ <$> l) = hlen l.
Proof.
  intros Hσ. unfold hlen. rewrite length_fmap.
  assert (PTop ∈ psub σ <$> l ↔ PTop ∈ l) as E.
  { rewrite list_elem_of_fmap. split; [intros (ρ & Hρ & Hin); symmetry in Hρ;
      apply (psub_top σ ρ Hσ) in Hρ; by subst|intros Hin; by exists PTop]. }
  by rewrite (bool_decide_ext _ _ E).
Qed.

Section anc.
  Context (Ψ : hyps) (Θ : pctx) (B : point) (HB : good Ψ Θ B) (σ : list prio) (Hσ : Forall pfin σ).
  Abbreviation X := (rpt B (RAnc σ)).

  Lemma den_X_payload v r : models Θ v → den v (rpt X r) = dsl (DAnc (evalZ v <$> σ)) (encode_nat r).
  Proof. intros Hv. unfold rpt at 1. by rewrite den_payload, (den_anc _ _ _ HB). Qed.

  Lemma hiz_anc ef : opt_rel (seqs Wmp Ψ) (hiz X ef) (hiz B (psub σ <$> ef)).
  Proof.
    destruct ef as [|ρ ef]; simpl; [done|]. apply (gd_eq _ _ _ HB); [done|done|]. intros v Hv.
    rewrite den_X_payload, (den_hi _ _ _ HB) by done. unfold dsl. rewrite decode_encode_nat.
    rewrite xmaxl_psub by done. f_equal. symmetry. by apply (hlen_psub σ (ρ :: ef)).
  Qed.

  Lemma tr_anc T : steq Wmp Ψ (tr X T) (tr B (msub σ T)) ∧ steq Wmp Ψ (tr B (msub σ T)) (tr X T).
  Proof.
    induction T as [|p Q h d|T IH1 lo ef V IH2|nv cs T IH1 ef V IH2]; simpl.
    - done.
    - assert (seqs Wmp Ψ (rpt X (RCh Q h d)) (rpt B (RCh (mmap (psub σ) Q) (psub σ h) d))) as E.
      { apply (gd_eq _ _ _ HB); [done|done|]. intros v Hv.
        rewrite den_X_payload, (den_ch _ _ _ HB) by done. simpl. rewrite decode_encode_nat.
        rewrite (proj1 (mmap_comp _ _)), (pclose_psub v σ h Hσ).
        by rewrite (proj1 (mmap_ext _ (pclose v ∘ psub σ) (λ ρ, pclose_psub v σ ρ Hσ)) Q). }
      rewrite (proj1 (ers_mmap _)). split; (split; [|apply seq_refl]); [done|by apply se_sym].
    - assert (seqs Wmp Ψ (rpt X (RLo lo)) (rpt B (RLo (psub σ <$> lo)))) as E.
      { apply (gd_eq _ _ _ HB); [done|done|]. intros v Hv.
        rewrite den_X_payload, (den_lo _ _ _ HB) by done. simpl. rewrite decode_encode_nat.
        by rewrite xminl_psub, length_fmap. }
      pose proof (hiz_anc ef) as Eh.
      destruct IH1 as [IH1 IH1'], IH2 as [IH2 IH2']. split; split_and!; try done.
      + destruct (hiz X ef), (hiz B (psub σ <$> ef)); simpl in *; try done. by apply se_sym.
      + by apply se_sym.
    - split; simpl; apply teq_refl.
  Qed.
End anc.

(** ** fork *)

Lemma rename_fork r : rename r fork_tr = fork_tr.
Proof. done. Qed.
Lemma rename_unitv r : rename r unitv = unitv.
Proof. done. Qed.

Section fork.
  Context (Ψ : hyps) (Θ : pctx) (B : point) (HB : good Ψ Θ B).

  Lemma fork_tr_typed Φ Δ0 F lo σ :
    lenv_empty Δ0 →
    typed Wmp Φ Ψ ∅ Δ0 F fork_tr (TLolli None None (tr B (MArr MUnit lo σ MUnit)) U).
  Proof.
    intros HΔ. pose proof Wmp_wf as HW. set (φ0 := fresh (dom Φ)).
    apply (t_abs Wmp Φ Ψ ∅ Δ0 F _ _ _ None None φ0); [apply is_fresh|lbhb|].
    { simpl. by bclean; rewrite (tenv_heads0 Wmp HW), empty_heads, union_empty_l_L. }
    set (Φ1 := <[φ0 := None]> Φ).
    set (fT := tr B (MArr MUnit lo σ MUnit)).
    set (E := Some fT :: Δ0).
    eapply (t_letstar Wmp Φ1 Ψ ∅ ∅ ∅ E E (lenv_nones E)); [by apply comp0|apply lenv_split_nones_r| |].
    2:{ apply tv_unitv; [done|apply nones_unl]. }
    set (ub := hiz B σ). set (lb := Some (rpt B (RLo lo))).
    eapply (t_app Wmp Φ1 Ψ ∅ ∅ ∅ E (lenv_nones E) E _ _ _ None None (TLolli ub lb TUnit TUnit)).
    { by apply comp0. } { apply lenv_split_nones_l. } { done. }
    { apply t_const; [apply lenv_empty_nones|apply KTSpawn|done]. }
    set (φ := fresh (dom Φ1)).
    apply (t_abs Wmp Φ1 Ψ ∅ E _ _ _ _ ub lb φ); [apply is_fresh|lbhb|].
    { simpl. bclean; rewrite (tenv_heads0 Wmp HW), empty_heads, union_empty_l_L, union_empty_r_L by done.
      intros y Hy. apply elem_of_singleton in Hy as ->. left. apply se_refl. }
    set (Φ2 := <[φ := ub]> Φ1).
    eapply (t_letstar Wmp Φ2 Ψ ∅ ∅ ∅ _ (Some TUnit :: None :: Δ0) (None :: Some fT :: Δ0));
      [by apply comp0| | |].
    { constructor. constructor. by apply lenv_split_empty'. }
    { apply tv_var_unl; [done|done|var_others HΔ]. }
    assert (ub_below_s Wmp Ψ Φ2 ub (∅, Some (FVar φ))) as Hub by apply (ubs_fresh Wmp HW).
    eapply (typed_force0 Wmp Φ2 Ψ ∅ _ _ _ 0 (BCs [] (λ _, False)) None TUnit []); [done|done| |done|done|].
    { intros g Hg. apply bcs_open_nil in Hg as [[] _]. }
    eapply (t_app Wmp Φ2 Ψ ∅ ∅ ∅ _ (None :: Some fT :: Δ0) (lenv_nones (None :: Some fT :: Δ0))
              _ _ _ ub lb U U).
    { by apply comp0. } { apply lenv_split_nones_r. } { done. }
    { apply tv_var_unl; [done|done|var_others HΔ]. }
    { apply tv_unitv; [done|apply nones_unl]. }
  Qed.
End fork.

(** ** Futures *)

Section futures.
  Context (Ψ : hyps) (Θ : pctx) (B : point) (HB : good Ψ Θ B).

  (** The effect of a part, inside the future of the whole and below the
      heads that the rest of the thread holds. *)
  Lemma ubs_part Φ F l1 l2 ef1 ins Γ2 Δ2 :
    ub_below_s Wmp Ψ Φ (hiz B (l1 ++ ef1 ++ l2)) F → plt Θ ef1 (envp Γ2) → erel B ins Γ2 Δ2 →
    ub_below_s Wmp Ψ Φ (hiz B ef1) (sf_union F (lenv_heads Δ2)).
  Proof.
    intros HF Hl HΔ. apply (ubs_union _ Wmp_wf).
    - by apply (ubs_hle Ψ Θ B HB _ _ _ _ (hle_seg Ψ Θ B HB ef1 l1 l2)).
    - intros x Hx h Hh. by apply (env_hi_below Ψ Θ B HB ins Γ2 Δ2 ef1 x h).
  Qed.

  Lemma ubs_seg Φ F ef l1 l2 :
    ub_below_s Wmp Ψ Φ (hiz B (l1 ++ ef ++ l2)) F → ub_below_s Wmp Ψ Φ (hiz B ef) F.
  Proof. apply (ubs_hle Ψ Θ B HB), (hle_seg Ψ Θ B HB). Qed.

  (** The payload of a message at x. *)
  Lemma pay_conv (x : point) a P K Q1 :
    (Q1 = MSnd a P K ∨ Q1 = MRcv a P K) →
    (∀ pp Qp hp dp, P = MPChan pp Qp hp dp → seqs Wmp Ψ (pt_payload x 0) (rpt B (RCh Qp hp dp))) →
    steq Wmp Ψ (tr B (payty P)) (payload_at (pm P) (ersp P) x) ∧
    steq Wmp Ψ (payload_at (pm P) (ersp P) x) (tr B (payty P)) ∧
    (∀ y, y ∈ heads (payload_at (pm P) (ersp P) x) →
       ∃ pp Qp hp dp, P = MPChan pp Qp hp dp ∧ y = pt_payload x 0).
  Proof.
    intros _ Hp. destruct P as [|pp Qp hp dp].
    - unfold payload_at, ty_inst. simpl. split_and!; [apply teq_refl..|set_solver].
    - specialize (Hp pp Qp hp dp eq_refl).
      assert (payload_at 1 (TSess (polS pp (ers Qp)) (pvar 0)) x = TSess (polS pp (ers Qp)) (pt_payload x 0))
        as Ep by (unfold payload_at, ty_inst; simpl; by rewrite pt_inst_pvar_at).
      cbn [payty tr pm ersp]. rewrite Ep. split_and!.
      + split; [by apply se_sym|apply seq_refl].
      + split; [done|apply seq_refl].
      + intros y Hy. simpl in Hy. apply elem_of_singleton in Hy as ->. by eexists _, _, _, _.
  Qed.
End futures.

Lemma slt_seqs_r W Ψ x y z : slt W Ψ x y → seqs W Ψ y z → slt W Ψ x z.
Proof. intros H1 H2. by eapply (fl_eqr (FCtx W Ψ ∅)). Qed.

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

Lemma ersp_scoped P : pscoped (pm P) (ersp P).
Proof.
  destruct P; simpl.
  - split; [unfold bcs_scoped; simpl; constructor|]. repeat split.
  - intros a Ha. injection Ha as <-. lia.
Qed.

(** ** The translation lemma *)

Theorem mp_translate Θ Γ e T ef e' :
  mtyped Θ Γ e T ef e' →
  ∀ Ψ B ins Δ Φ F, good Ψ Θ B → erel B ins Γ Δ → ub_below_s Wmp Ψ Φ (hiz B ef) F →
  typed Wmp Φ Ψ ∅ Δ F (rename (ren_of ins) e') (tr B T).
Proof.
  pose proof Wmp_wf as HW.
  induction 1 as [Θ Γ x t Hx
    |Θ Γ HΓ
    |Θ Γ e e' T V ef Hne He IH
    |Θ Γ Γ1 Γ2 e1 e2 e1' e2' T lo σ V ef1 ef2 Hs H1 IH1 H2 IH2 Hl1 Hl2
    |Θ Γ Γ1 Γ2 e1 e2 e1' e2' nv cs T σ V ef1 ef2 σs Hs H1 IH1 Hok H2 IH2 Hl1 Hnt
    |Θ Γ e e' nv cs T σ V ef Hp He IH Hle
    |Θ Γ Γ1 Γ2 e1 e2 e1' e2' T V ef1 ef2 Hs H1 IH1 H2 IH2 Hl
    |Θ Γ Γ1 Γ2 e1 e2 e1' e2' V ef1 ef2 Hs H1 IH1 H2 IH2 Hl
    |Θ Γ e e' Q n d V ef Hw Hn He IH
    |Θ Γ Γ1 Γ2 e1 e2 e1' e2' pol Q h d a P K ef1 ef2 Hs H1 IH1 H2 IH2 Hv Hw Ha Hl1 Hl2 Hpa Hr
    |Θ Γ Γ1 Γ2 e e2 e' e2' pol Q h d a P K V ef1 ef2 Hs H1 IH1 Hv Hw Ha H2 IH2 Hl Hpa Hr
    |Θ Γ e e' pol Q h d a ef H IH Hv Hw Ha
    |Θ Γ e e' pol Q h d a K1 K2 ef H IH Hv Hw Ha Hr
    |Θ Γ e e' pol Q h d a K1 K2 ef H IH Hv Hw Ha Hr
    |Θ Γ Γ1 Γ2 e e1 e2 e' e1' e2' pol Q h d a K1 K2 V ef1 ef2 Hs H1 IH Hv Hw Ha HA IHA HB' IHB Hl Hr
    |Θ Γ e e' lo σ ef H IH
    |Θ Γ e e' pol S0 h d ef H IH Hb Ha
    |Θ Γ e e' pol S0 h d ef H IH Hb Ha
    |Θ Γ e e' T ef ef' H IH Hle];
    intros Ψ B ins Δ Φ F HB HΔ HF.
  - (* T-Var *)
    by apply (erel_var B ins Γ Δ Wmp Φ Ψ F x t HW HΔ Hx).
  - (* () *)
    rewrite rename_unitv. apply (tv_unitv Wmp HW). by apply (erel_unl B ins Γ Δ).
  - (* T-AbsLin *)
    cbn [rename]. rewrite ren_up. set (φ := fresh (dom Φ)).
    apply (t_abs Wmp Φ Ψ ∅ Δ F _ _ _ (hiz B ef) (Some (rpt B (RLo (envp Γ)))) φ); [apply is_fresh|lbhb|].
    + simpl. bclean; rewrite (tenv_heads0 _ HW), union_empty_l_L. intros y Hy.
      apply (env_lo_below Ψ Θ B HB ins Γ Δ y HΔ Hy).
    + apply IH; [done|by apply (er_keep _ (Some T))|apply (ubs_fresh _ HW)].
  - (* T-App *)
    cbn [rename]. destruct (erel_split B ins Γ Δ Γ1 Γ2 HΔ Hs) as (Δ1 & Δ2 & Hd & HΔ1 & HΔ2).
    eapply (t_app Wmp Φ Ψ ∅ ∅ ∅ Δ Δ1 Δ2 F _ _ (hiz B σ) (Some (rpt B (RLo lo))) (tr B T)).
    + by apply comp0.
    + done.
    + apply (ubs_seg Ψ Θ B HB Φ F σ (ef1 ++ ef2) []). by rewrite app_nil_r, <-app_assoc.
    + bclean; rewrite (tenv_heads0 _ HW), union_empty_l_L. apply (IH1 Ψ B ins Δ1); [done|done|].
      by apply (ubs_part Ψ Θ B HB Φ F [] (ef2 ++ σ) ef1 ins Γ2 Δ2).
    + apply (IH2 Ψ B ins Δ2); [done|done|]. apply (ubs_union _ HW).
      * apply (ubs_seg Ψ Θ B HB Φ F ef2 ef1 σ). done.
      * intros x Hx h Hh. simpl in Hh. apply elem_of_singleton in Hh as ->.
        by apply (hi_below_lo Ψ Θ B HB ef2 lo x).
  - (* T-PApp, T-App *)
    cbn [rename]. destruct (erel_split B ins Γ Δ Γ1 Γ2 HΔ Hs) as (Δ1 & Δ2 & Hd & HΔ1 & HΔ2).
    destruct Hok as (Hlen & Hfin & Hmod) eqn:Hok'.
    set (X := rpt B (RAnc σs)).
    set (Tb := TLolli (hiz (pvar 0) σ) None (tr (pvar 0) T) (tr (pvar 0) V)).
    eapply (t_app Wmp Φ Ψ ∅ ∅ ∅ Δ Δ1 Δ2 F _ _ (hiz B (psub σs <$> σ)) None (tr B (msub σs T))).
    + by apply comp0.
    + done.
    + apply (ubs_seg Ψ Θ B HB Φ F (psub σs <$> σ) (ef1 ++ ef2) []). by rewrite app_nil_r, <-app_assoc.
    + bclean; rewrite (tenv_heads0 _ HW), union_empty_l_L.
      apply (t_conv _ _ _ _ _ _ _ (ty_inst [X] Tb)).
      { unfold ty_inst, Tb. simpl. rewrite hiz_pinst, !tr_pinst, pt_inst_pvar_at. simpl.
        destruct (tr_anc Ψ Θ B HB σs Hfin T) as [E1 _], (tr_anc Ψ Θ B HB σs Hfin V) as [E2 _].
        split_and!; [apply (hiz_anc Ψ Θ B HB σs Hfin)|done|done|done]. }
      eapply (typed_force0 Wmp Φ Ψ ∅ Δ1 _ _ 1 (Crel (PCtx nv cs)) None Tb [X]);
        [done|done|by apply (crel_hold Ψ Θ B HB)|apply (anc_known Ψ Θ B HB)|done|].
      apply (IH1 Ψ B ins Δ1); [done|done|].
      by apply (ubs_part Ψ Θ B HB Φ F [] (ef2 ++ (psub σs <$> σ)) ef1 ins Γ2 Δ2).
    + rewrite sf_union_empty. apply (IH2 Ψ B ins Δ2); [done|done|].
      apply (ubs_seg Ψ Θ B HB Φ F ef2 ef1 (psub σs <$> σ)). done.
  - (* rec f. Λιs. λx.e *)
    cbn [rename]. rewrite ren_up2.
    set (Θ' := PCtx nv cs).
    set (Tb := TLolli (hiz (pvar 0) σ) None (tr (pvar 0) T) (tr (pvar 0) V)).
    assert (menv_un Γ) as HΓ.
    { intros t Ht. destruct (Hp t Ht) as [->|(? & ? & ? & ? & ? & ->)]; done. }
    apply (tv_box Wmp HW _ _ _ _ _ 1 (Crel Θ') None Tb); [by apply (erel_unl B ins Γ Δ)|done|].
    intros φ Hφ.
    set (Ψ' := hyps_inst (pshift 1) Ψ ++ [(Crel Θ', ids 1)]).
    assert (good Ψ' Θ' (pvar 0)) as HB' by (apply good_box; unfold Ψ'; set_solver).
    set (Φ1 := <[φ := None]> (fhyps_pinst (pshift 1) Φ)). set (φ' := fresh (dom Φ1)).
    apply (t_abs Wmp Φ1 Ψ' ∅ _ _ _ _ _ (hiz (pvar 0) σ) None φ'); [apply is_fresh|lbhb|].
    + simpl. bclean; rewrite (tenv_heads0 _ HW), !union_empty_l_L. apply unl_heads, unl_pinst.
      by apply (erel_unl B ins Γ Δ).
    + apply IH; [done| |].
      * apply (er_keep _ (Some T)).
        change (lenv_pinst (pshift 1) (Some (TBox 1 0 (Crel Θ') (TLolli None None TUnit Tb)) :: Δ))
          with (Some (pinst_ty (pshift 1) (tr B (MPoly nv cs T σ V))) :: lenv_pinst (pshift 1) Δ).
        rewrite tr_pinst, (tr_un _ (pvar 0)) by done.
        apply (er_keep _ (Some (MPoly nv cs T σ V))). by apply (erel_pinst B).
      * apply (ubs_hle Ψ' Θ' (pvar 0) HB' _ ef σ); [done|]. apply (ubs_fresh _ HW).
  - (* T-Let *)
    cbn [rename]. rewrite ren_up.
    destruct (erel_split B ins Γ Δ Γ1 Γ2 HΔ Hs) as (Δ1 & Δ2 & Hd & HΔ1 & HΔ2).
    set (lb := Some (rpt B (RLo (envp Γ2)))).
    eapply (t_app Wmp Φ Ψ ∅ ∅ ∅ Δ Δ2 Δ1 F _ _ (hiz B ef2) lb (tr B T)).
    + by apply comp0.
    + by apply lenv_split_comm.
    + apply (ubs_seg Ψ Θ B HB Φ F ef2 ef1 []). by rewrite app_nil_r.
    + set (φ := fresh (dom Φ)).
      apply (t_abs Wmp Φ Ψ ∅ Δ2 _ _ _ _ (hiz B ef2) lb φ); [apply is_fresh|lbhb|].
      * simpl. bclean; rewrite (tenv_heads0 _ HW), union_empty_l_L. intros y Hy.
        apply (env_lo_below Ψ Θ B HB ins Γ2 Δ2 y HΔ2 Hy).
      * apply IH2; [done|by apply (er_keep _ (Some T))|apply (ubs_fresh _ HW)].
    + apply (IH1 Ψ B ins Δ1); [done|done|]. apply (ubs_union _ HW).
      * apply (ubs_seg Ψ Θ B HB Φ F ef1 [] ef2). done.
      * intros x Hx h Hh. simpl in Hh. apply elem_of_singleton in Hh as ->.
        by apply (hi_below_lo Ψ Θ B HB ef1 _ x).
  - (* e₁; e₂ *)
    cbn [rename]. destruct (erel_split B ins Γ Δ Γ1 Γ2 HΔ Hs) as (Δ1 & Δ2 & Hd & HΔ1 & HΔ2).
    eapply (t_letstar Wmp Φ Ψ ∅ ∅ ∅ Δ Δ1 Δ2); [by apply comp0|done| |].
    + bclean; rewrite (tenv_heads0 _ HW), union_empty_l_L.
      change TUnit with (ty_inst [] TUnit).
      eapply (typed_force0 Wmp Φ Ψ ∅ Δ1 _ _ 0 (BCs [] (λ _, False)) None TUnit []);
        [done|done| |done|done|].
      { intros g Hg. apply bcs_open_nil in Hg as [[] _]. }
      apply (IH1 Ψ B ins Δ1); [done|done|].
      by apply (ubs_part Ψ Θ B HB Φ F [] ef2 ef1 ins Γ2 Δ2).
    + apply (IH2 Ψ B ins Δ2); [done|done|]. apply (ubs_seg Ψ Θ B HB Φ F ef2 ef1 []).
      by rewrite app_nil_r.
  - (* let (x, y) = new S n₁ n₂ in e *)
    (* new at the point of the channel by the alias ι ≡ x ([t_new_at]).
       The body skips the spent pair and unit. *)
    rewrite rename_let_new_pair, ren_up2. unfold let_new_pair.
    assert (rename (upren (upren (λ x, 2 + x))) (rename (ren_of (false :: false :: ins)) e')
            = rename (ren_of (false :: false :: true :: true :: ins)) e') as ->.
    { rewrite rename_rename. apply rename_ext. by intros [|[|x]]. }
    apply (t_new_at Wmp _ _ _ _ _ _ _ (ers Q) (rpt B (RCh Q n d)));
      [apply Wmp_strict|by apply (rpt_known Ψ Θ B HB)|].
    apply IH; [done| |done].
    apply (er_keep _ (Some (MChan true Q n d))), (er_keep _ (Some (MChan false Q n d))).
    apply er_skip; [by left|]. apply er_skip; [by left|]. exact HΔ.
  - (* send *)
    cbn [rename]. destruct (erel_split B ins Γ Δ Γ1 Γ2 HΔ Hs) as (Δ1 & Δ2 & Hd & HΔ1 & HΔ2).
    destruct (view_snd pol _ a P K Hv) as (Es & Eh & HQ).
    set (x := rpt B (RCh Q h d)). set (S := polS pol (ers K)).
    assert (∀ pp Qp hp dp, P = MPChan pp Qp hp dp → seqs Wmp Ψ (pt_payload x 0) (rpt B (RCh Qp hp dp))) as Hsl.
    { intros pp Qp hp dp ->. by apply (ch_pay Ψ Θ B HB pol Q h d Hw a pp Qp hp dp K). }
    destruct (pay_conv Ψ Θ B HB x a P K _ HQ Hsl) as (Hp1 & _ & Hp3).
    apply (tv_app_closed Wmp HW _ _ _ _ _ _ (Some x)
             (TProd (payload_at (pm P) (ersp P) x) (TSess (SSeq (SSnd (pm P) (ersp P)) S) x))); [bot_false|..].
    + eapply t_conv; [|apply t_const; [apply lenv_empty_nones|apply (KTSend _ _ _ (pm P) (ersp P) S x)|apply ersp_scoped]].
      * apply steq_lolli; [apply teq_steq, teq_refl|]. apply steq_sess; [|apply seq_refl].
        by apply (ch_next Ψ Θ B HB pol Q h d Hw a P K).
      * rewrite hbot_ersp. intros y Hy. destruct (Hp3 y Hy) as (pp & Qp & hp & dp & -> & ->).
        eapply slt_seqs_r; [|apply se_sym, (Hsl pp Qp hp dp eq_refl)].
        apply (ch_below_lt Ψ Θ B HB pol Q h d Hw a [chead Qp hp dp]); [done|done|done|done|].
        intros v Hv'. exists (chead Qp hp dp). split; [by left|]. split; [by destruct (evalp v _)|].
        by apply (rank_ch Ψ Θ B HB).
    + eapply (t_pair Wmp Φ Ψ ∅ ∅ ∅ Δ Δ1 Δ2); [by apply comp0|done| |].
      * bclean; rewrite (tenv_heads0 _ HW), union_empty_l_L. eapply t_conv; [exact Hp1|].
        apply (IH1 Ψ B ins Δ1); [done|done|].
        by apply (ubs_part Ψ Θ B HB Φ F [] (ef2 ++ [a]) ef1 ins Γ2 Δ2).
      * eapply t_conv; [|apply (IH2 Ψ B ins Δ2); [done|done|]].
        { destruct (ch_conv Ψ Θ B HB pol Q h d Hw) as [E _]. by rewrite Es in E. }
        bclean. apply (ubs_union _ HW); [by apply (ubs_seg Ψ Θ B HB Φ F ef2 ef1 [a])|].
        intros z Hz y Hy. destruct (Hp3 y Hy) as (pp & Qp & hp & dp & -> & ->).
        eapply slt_seqs_r; [|apply se_sym, (Hsl pp Qp hp dp eq_refl)].
        by apply (hi_below_ch Ψ Θ B HB ef2 Qp hp dp z).
    + apply (ch_ub Ψ Θ B HB pol Q h d Hw Φ a (ef1 ++ ef2 ++ [a])); [done|done|set_solver|done].
  - (* receive *)
    cbn [rename]. rewrite ren_up2.
    destruct (erel_split B ins Γ Δ Γ1 Γ2 HΔ Hs) as (Δ1 & Δ2 & Hd & HΔ1 & HΔ2).
    destruct (view_rcv pol _ a P K Hv) as (Es & Eh & HQ).
    set (x := rpt B (RCh Q h d)). set (S := polS pol (ers K)).
    assert (∀ pp Qp hp dp, P = MPChan pp Qp hp dp → seqs Wmp Ψ (pt_payload x 0) (rpt B (RCh Qp hp dp))) as Hsl.
    { intros pp Qp hp dp ->. by apply (ch_pay Ψ Θ B HB pol Q h d Hw a pp Qp hp dp K). }
    destruct (pay_conv Ψ Θ B HB x a P K _ HQ Hsl) as (_ & Hp2 & _).
    assert (ub_below_s Wmp Ψ Φ (hiz B (ef1 ++ [a])) (sf_union F (lenv_heads Δ2))) as Hpart.
    { apply (ubs_part Ψ Θ B HB Φ F [] ef2 (ef1 ++ [a]) ins Γ2 Δ2); [|done|done].
      by rewrite <-app_assoc. }
    eapply (t_letpair Wmp Φ Ψ ∅ ∅ ∅ Δ Δ1 Δ2 F _ _ (tr B (payty P)) (tr B (MChan pol K (mhd Q h d).2 d)));
      [by apply comp0|done| |].
    + bclean; rewrite (tenv_heads0 _ HW), union_empty_l_L.
      apply (tv_app_closed Wmp HW _ _ _ _ _ _ (Some x) (tr B (MChan pol Q h d))); [bot_false|..].
      * eapply t_conv; [|apply t_const; [apply lenv_empty_nones|apply (KTRecv _ _ _ (pm P) (ersp P) S x)|apply ersp_scoped]].
        apply steq_lolli.
        { destruct (ch_conv Ψ Θ B HB pol Q h d Hw) as [_ E]. by rewrite Es in E. }
        apply steq_prod; [done|]. apply steq_sess; [|apply seq_refl].
        by apply (ch_next Ψ Θ B HB pol Q h d Hw a P K).
      * apply (IH1 Ψ B ins Δ1); [done|done|]. by apply (ubs_seg Ψ Θ B HB _ _ ef1 [] [a]).
      * by apply (ch_ub Ψ Θ B HB pol Q h d Hw Φ a (ef1 ++ [a])); [done|done|set_solver|].
    + apply (IH2 Ψ B _ _ _ _ HB).
      * apply (er_keep _ (Some _)), (er_keep _ (Some _)), HΔ2.
      * apply (ubs_seg Ψ Θ B HB Φ F ef2 (ef1 ++ [a]) []). by rewrite app_nil_r, <-app_assoc.
  - (* close, wait *)
    cbn [rename]. destruct (view_end pol _ a Hv) as (Es & Eh).
    set (x := rpt B (RCh Q h d)).
    eapply (t_letstar Wmp Φ Ψ ∅ ∅ ∅ Δ Δ (lenv_nones Δ)); [by apply comp0|apply lenv_split_nones_r| |].
    + bclean; rewrite (tenv_heads0 _ HW), nones_heads, union_empty_l_L, sf_union_empty.
      apply (tv_app_closed Wmp HW _ _ _ _ _ _ (Some x) (TSess SEnd x)); [bot_false|..].
      * apply t_const; [apply lenv_empty_nones|apply KTClos|done].
      * eapply t_conv; [|apply (IH Ψ B ins Δ); [done|done|]].
        { destruct (ch_conv Ψ Θ B HB pol Q h d Hw) as [E _]. by rewrite Es in E. }
        by apply (ubs_seg Ψ Θ B HB _ _ ef [] [a]).
      * by apply (ch_ub Ψ Θ B HB pol Q h d Hw Φ a (ef ++ [a])); [done|done|set_solver|].
    + apply (tv_unitv Wmp HW). apply nones_unl.
  - (* select 1 *)
    cbn [rename]. destruct (view_sel pol _ a K1 K2 Hv) as (Es & Eh & HQ).
    set (x := rpt B (RCh Q h d)).
    apply (tv_app_closed Wmp HW _ _ _ _ _ _ (Some x)
             (TSess (SPlus (polS pol (ers K1)) (polS pol (ers K2))) x)); [bot_false|..].
    + eapply t_conv; [|apply t_const; [apply lenv_empty_nones|apply KTSel1; exact (ch_branch_lt Ψ Θ B HB pol Q h d Hw a K1 K2 false HQ)|done]].
      apply steq_lolli; [apply teq_steq, teq_refl|]. apply steq_sess; [|apply seq_refl].
      by apply (ch_branch Ψ Θ B HB pol Q h d Hw a K1 K2 false).
    + eapply t_conv; [|apply (IH Ψ B ins Δ); [done|done|]].
      { destruct (ch_conv Ψ Θ B HB pol Q h d Hw) as [E _]. by rewrite Es in E. }
      by apply (ubs_seg Ψ Θ B HB _ _ ef [] [a]).
    + by apply (ch_ub Ψ Θ B HB pol Q h d Hw Φ a (ef ++ [a])); [done|done|set_solver|].
  - (* select 2 *)
    cbn [rename]. destruct (view_sel pol _ a K1 K2 Hv) as (Es & Eh & HQ).
    set (x := rpt B (RCh Q h d)).
    apply (tv_app_closed Wmp HW _ _ _ _ _ _ (Some x)
             (TSess (SPlus (polS pol (ers K1)) (polS pol (ers K2))) x)); [bot_false|..].
    + eapply t_conv; [|apply t_const; [apply lenv_empty_nones|apply KTSel2; exact (ch_branch_lt Ψ Θ B HB pol Q h d Hw a K1 K2 true HQ)|done]].
      apply steq_lolli; [apply teq_steq, teq_refl|]. apply steq_sess; [|apply seq_refl].
      by apply (ch_branch Ψ Θ B HB pol Q h d Hw a K1 K2 true).
    + eapply t_conv; [|apply (IH Ψ B ins Δ); [done|done|]].
      { destruct (ch_conv Ψ Θ B HB pol Q h d Hw) as [E _]. by rewrite Es in E. }
      by apply (ubs_seg Ψ Θ B HB _ _ ef [] [a]).
    + by apply (ch_ub Ψ Θ B HB pol Q h d Hw Φ a (ef ++ [a])); [done|done|set_solver|].
  - (* match *)
    cbn [rename]. rewrite !ren_up.
    destruct (erel_split B ins Γ Δ Γ1 Γ2 HΔ Hs) as (Δ1 & Δ2 & Hd & HΔ1 & HΔ2).
    destruct (view_bra pol _ a K1 K2 Hv) as (Es & Eh & HQ).
    set (x := rpt B (RCh Q h d)).
    assert (ub_below_s Wmp Ψ Φ (hiz B (ef1 ++ [a])) (sf_union F (lenv_heads Δ2))) as Hpart.
    { apply (ubs_part Ψ Θ B HB Φ F [] ef2 (ef1 ++ [a]) ins Γ2 Δ2); [|done|done].
      by rewrite <-app_assoc. }
    eapply (t_case Wmp Φ Ψ ∅ ∅ ∅ Δ Δ1 Δ2 F _ _ _ (tr B (MChan pol K1 (mhd Q h d).2 d))
              (tr B (MChan pol K2 (mhd Q h d).2 d))); [by apply comp0|done| | |].
    + bclean; rewrite (tenv_heads0 _ HW), union_empty_l_L.
      apply (tv_app_closed Wmp HW _ _ _ _ _ _ (Some x) (tr B (MChan pol Q h d))); [bot_false|..].
      * eapply t_conv; [|apply t_const; [apply lenv_empty_nones|apply KTBra; [exact (ch_branch_lt Ψ Θ B HB pol Q h d Hw a K1 K2 false HQ)|exact (ch_branch_lt Ψ Θ B HB pol Q h d Hw a K1 K2 true HQ)]|done]].
        apply steq_lolli.
        { destruct (ch_conv Ψ Θ B HB pol Q h d Hw) as [_ E]. by rewrite Es in E. }
        apply steq_sum; (apply steq_sess; [|apply seq_refl]).
        { by apply (ch_branch Ψ Θ B HB pol Q h d Hw a K1 K2 false). }
        { by apply (ch_branch Ψ Θ B HB pol Q h d Hw a K1 K2 true). }
      * apply (IH Ψ B ins Δ1); [done|done|]. by apply (ubs_seg Ψ Θ B HB _ _ ef1 [] [a]).
      * by apply (ch_ub Ψ Θ B HB pol Q h d Hw Φ a (ef1 ++ [a])); [done|done|set_solver|].
    + apply IHA; [done|by apply (er_keep _ (Some _))|].
      apply (ubs_seg Ψ Θ B HB Φ F ef2 (ef1 ++ [a]) []). by rewrite app_nil_r, <-app_assoc.
    + apply IHB; [done|by apply (er_keep _ (Some _))|].
      apply (ubs_seg Ψ Θ B HB Φ F ef2 (ef1 ++ [a]) []). by rewrite app_nil_r, <-app_assoc.
  - (* fork *)
    cbn [rename]. rewrite rename_fork.
    apply (tv_app_closed Wmp HW _ _ _ _ _ _ None (tr B (MArr MUnit lo σ MUnit))); [bot_false|..].
    + apply (fork_tr_typed Ψ Θ B HB). apply lenv_empty_nones.
    + by apply IH.
    + done.
  - (* inst *)
    eapply t_conv; [apply (ch_inst Ψ Θ B pol S0 h d HB Hb Ha)|]. by apply IH.
  - (* fold *)
    eapply t_conv; [apply (ch_inst Ψ Θ B pol S0 h d HB Hb Ha)|]. by apply IH.
  - (* a larger effect *)
    apply IH; [done|done|]. by apply (ubs_hle Ψ Θ B HB _ ef ef').
Qed.

(** ** Deadlock freedom *)

(** A closed program of unit type translates to a typed closed thread
    at the strict world [Wmp], so it is deadlock free. *)
Theorem mp_deadlock_free e ef e' :
  mtyped pc0 [] e MUnit ef e' → deadlock_free (∅, {[+ e' +]}).
Proof.
  intros H. apply (soundness Wmp _ U Wmp_strict). apply ptyped_closed; [repeat constructor|].
  rewrite <-(rename_id e'), (rename_ext e' (λ x, x) (ren_of [])) by done.
  apply (mp_translate pc0 [] e MUnit ef e' H [] proot [] [] ∅ (∅, None)); [apply good_root|constructor|].
  destruct (hiz proot ef); [|done]. split; simpl; [set_solver|done].
Qed.
