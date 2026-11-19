(** * Tools for example derivations (stage S2)

    Examples are typed in the deadlock-freedom projection [dftyped] and
    lifted to the merged judgment at N = ∞ by [dftyped_typed]
    (static/Conservativity.v). Programs create every channel with
    [new_ℓ] or [new_κ], so Θ is empty throughout. *)

From GV Require Export static.Conservativity static.Weakening.

(** let (a, b) = new_ℓ in e, the ∃ of new bound at index 2 and opened. *)
Definition let_new (ℓ : family) (e : expr) : expr := ELet (ENew ℓ) (LetP (Var 0) e).

(** Occurrence of a variable, decidable. *)
Fixpoint occ (i : nat) (e : expr) : bool :=
  match e with
  | Var x => Nat.eqb x i
  | EUnit | Chan _ | ENew _ => false
  | Lam e | EBox e => occ (S i) e
  | App e1 e2 | Pair e1 e2 | LetU e1 e2 => occ i e1 || occ i e2
  | LetP e1 e2 => occ i e1 || occ (S (S i)) e2
  | Inj1 e | Inj2 e | Op _ e => occ i e
  | Case e e1 e2 => occ i e || occ (S i) e1 || occ (S i) e2
  end.

Lemma tsplit_empty : tsplit ∅ ∅ ∅.
Proof. split; [apply map_disjoint_empty_l|by rewrite map_empty_union]. Qed.

Lemma tenv_heads_empty : tenv_heads ∅ = ∅.
Proof. apply set_eq. intros y. rewrite elem_of_tenv_heads. setoid_rewrite lookup_empty. set_solver. Qed.

(** An entry that the term does not need: absent or unlimited. *)
Definition spare (o : option (ty * fuel)) : Prop :=
  match o with None => True | Some (U, _) => unlimited U end.

Lemma lenv_all_spare_empty Δ : (∀ y o, Δ !! y = Some o → spare o) → lenv_wk ((λ _, None) <$> Δ) Δ.
Proof.
  induction Δ as [|o Δ IH]; intros H; simpl; [constructor|].
  destruct o as [[U a]|].
  - apply lwk_drop; [apply (H 0 _ eq_refl)|]. apply IH. intros y o Hy. apply (H (S y) o Hy).
  - constructor. apply IH. intros y o Hy. apply (H (S y) o Hy).
Qed.

(** Weaken every spare entry except x. *)
Fixpoint drop_but (x : nat) (Δ : lenv) {struct Δ} : lenv :=
  match Δ with
  | [] => []
  | o :: Δ' => match x with 0 => o :: ((λ _, None) <$> Δ') | S x' => None :: drop_but x' Δ' end
  end.

Lemma drop_but_wk x Δ : (∀ y o, y ≠ x → Δ !! y = Some o → spare o) → lenv_wk (drop_but x Δ) Δ.
Proof.
  revert x. induction Δ as [|o Δ IH]; intros x H; simpl; [constructor|].
  destruct x as [|x].
  - constructor. apply lenv_all_spare_empty. intros y o' Ho. apply (H (S y)); [lia|done].
  - destruct o as [[U a]|].
    + apply lwk_drop; [apply (H 0 _ ltac:(lia) eq_refl)|]. apply IH. intros y o' Hy Ho.
      apply (H (S y)); [lia|done].
    + constructor. apply IH. intros y o' Hy Ho. apply (H (S y)); [lia|done].
Qed.

Lemma drop_but_only x Δ σ : Δ !! x = Some (Some σ) → lenv_only (drop_but x Δ) x σ.
Proof.
  revert x. induction Δ as [|o Δ IH]; intros x Hx; [done|].
  destruct x as [|x]; simpl in *.
  - injection Hx as ->. split; [done|]. intros y σ' Hy.
    destruct y as [|y]; simpl in Hy; [by injection Hy as ->|].
    rewrite list_lookup_fmap in Hy. by destruct (Δ !! y).
  - destruct (IH x Hx) as [H1 H2]. split; [done|]. intros [|y] σ' Hy; simpl in Hy; [done|].
    destruct (H2 y σ' Hy) as [-> ->]. done.
Qed.

Lemma d_var' W Γ Δ F x T a :
  Δ !! x = Some (Some (T, a)) → (∀ y o, y ≠ x → Δ !! y = Some o → spare o) →
  dftyped W ∅ Γ Δ F (Var x) T.
Proof.
  intros Hx Hs. eapply d_weak; [by apply drop_but_wk|]. eapply d_var. by apply drop_but_only.
Qed.

Lemma lenv_empty_nones Δ : lenv_empty ((λ _ : option (ty * fuel), None) <$> Δ).
Proof. intros o Ho. by apply list_elem_of_fmap in Ho as (? & -> & _). Qed.

Lemma d_unit' W Γ Δ F : (∀ y o, Δ !! y = Some o → spare o) → dftyped W ∅ Γ Δ F EUnit TUnit.
Proof. intros H. eapply d_weak; [by apply lenv_all_spare_empty|]. apply d_unit, lenv_empty_nones. Qed.

Lemma d_new' W Γ Δ F ℓ S a1 a2 a3 :
  (∀ y o, Δ !! y = Some o → spare o) → ℓ ∈ w_fams W →
  dftyped W ∅ Γ Δ F (ENew ℓ)
    (TEx LBot 1 (bcs_of (w_laws W ℓ)) (TProd (TSess S (pvar 0)) a1 (TSess (dual S) (pvar 0)‾) a2) a3).
Proof. intros H Hℓ. eapply d_weak; [by apply lenv_all_spare_empty|]. apply d_new; [apply lenv_empty_nones|done]. Qed.

(** A tail of absent entries. *)
Abbreviation nones n := (replicate n (@None (ty * fuel))).

Lemma lsplit_nones n : lenv_split (nones n) (nones n) (nones n).
Proof. induction n; simpl; constructor; done. Qed.

Lemma lenv_pinst_nones σ n : lenv_pinst σ (nones n) = nones n.
Proof. unfold lenv_pinst. by rewrite fmap_replicate. Qed.

Lemma lage_nones c n : lage c (nones n) (nones n).
Proof. induction n; simpl; constructor; done. Qed.

Lemma nones_spare n y o : nones n !! y = Some o → spare o.
Proof. intros H. apply lookup_replicate_1 in H as [-> _]. done. Qed.

Lemma spare_nil y o : ([] : lenv) !! y = Some o → spare o.
Proof. done. Qed.

Lemma spare_cons o0 Δ : spare o0 → (∀ y o, Δ !! y = Some o → spare o) →
  ∀ y o, (o0 :: Δ) !! y = Some o → spare o.
Proof. intros H0 H [|y] o Hy; simpl in Hy; [by injection Hy as <-|by apply (H y)]. Qed.

Ltac spare_all :=
  cbn [insert list_insert];
  repeat (apply spare_cons; [simpl; first [exact I|done]|]);
  first [apply spare_nil | apply nones_spare].

Lemma spare_but x (Δ : lenv) : (∀ y o, <[x := None]> Δ !! y = Some o → spare o) →
  ∀ y o, y ≠ x → Δ !! y = Some o → spare o.
Proof. intros H y o Hyx Hy. apply (H y). by rewrite list_lookup_insert_ne. Qed.

Ltac spare_tac :=
  first [ spare_all | apply spare_but; spare_all ].

(** Split by occurrence. An unlimited entry goes to both sides. *)
Ltac lsplit_go i e1 e2 :=
  lazymatch goal with
  | |- lenv_split [] _ _ => apply lsplit_nil
  | |- lenv_split (replicate _ None) _ _ => apply lsplit_nones
  | |- lenv_split (None :: _) _ _ => apply lsplit_none; lsplit_go (S i) e1 e2
  | |- lenv_split (Some (?U, ?a) :: _) _ _ =>
      first [ apply lsplit_unl; [exact I|lsplit_go (S i) e1 e2]
            | let b := eval vm_compute in (occ i e1) in
              lazymatch b with
              | true => apply lsplit_l; lsplit_go (S i) e1 e2
              | false => apply lsplit_r; lsplit_go (S i) e1 e2
              end ]
  end.
Ltac lsplit_tac e1 e2 := lsplit_go 0 e1 e2.

Lemma pt_inst_pup_nil n x : pn_vb n (pt_name x) → pt_inst (pup n (plist [])) x = x.
Proof.
  intros H. rewrite (pt_inst_ext_root _ pvar); [apply pt_inst_pvar|]. intros a Ha.
  apply pn_vb_root in H as (a' & Ha' & Hlt). unfold pt_root in Ha. rewrite Ha in Ha'.
  injection Ha' as ->. unfold pup. by rewrite decide_True.
Qed.

(** The fact x ≺ y of a hypothesis whose constraint has no outer points. *)
Lemma slt_hyp W Γ P xs f x y :
  (BCs [] P, xs) ∈ hc_hyps Γ → P f → fact_scoped (length xs) f →
  fact_map (pt_inst (plist xs)) f = FLt x y → slt W Γ x y.
Proof.
  intros Hin Hf Hs Hxy. apply fl_h. exists (BCs [] P), xs. split; [done|].
  exists f. split; [|by rewrite Hxy].
  exists f. split; [done|]. split; [simpl; by rewrite Nat.add_0_r|].
  destruct f as [u v]. simpl in Hs |- *. destruct Hs as [Hu Hv].
  by rewrite !pt_inst_pup_nil.
Qed.

(** C holds at xs when every fact of C at xs is derivable. *)
Lemma hold_at_nil W Γ P xs :
  (∀ f, P f → fact_scoped (length xs) f →
     match fact_map (pt_inst (plist xs)) f with FLt x y => slt W Γ x y end) →
  hold_at W Γ (BCs [] P) xs.
Proof.
  intros H x y (g0 & (f & Hf & Hs & ->) & Hxy). simpl in Hs.
  rewrite Nat.add_0_r in Hs. specialize (H f Hf Hs).
  destruct f as [u v]. simpl in Hs. destruct Hs as [Hu Hv].
  simpl in Hxy |- *. rewrite !pt_inst_pup_nil in Hxy by done. injection Hxy as -> ->. done.
Qed.

(** Points as records, for comparing instances of facts. *)
Ltac pt_norm := cbn [fact_map pt_inst pt_polar pt_shift pt_dual pt_field pn_inst plist pvar
                     pt_name pt_pol pt_off lookup list_lookup length negb pred] in *.

Ltac fact_eq := pt_norm; repeat f_equal; lia.

Lemma tenv_pinst_empty σ : tenv_pinst σ ∅ = ∅.
Proof. apply fmap_empty. Qed.

Lemma sf_pinst_empty σ : sf_pinst σ (∅, None) = (∅, None).
Proof. unfold sf_pinst. simpl. by rewrite set_map_empty. Qed.

(** {x} ≺ F for a future with no points and no future variable. *)
Lemma ub_below_empty W Γ x : ub_below_s W Γ x (∅, None).
Proof. destruct x; simpl; [split_and!; [set_solver|done|done]|done]. Qed.

Lemma spare_heads Δ : (∀ y o, Δ !! y = Some o → spare o) → lenv_heads Δ = ∅ ∧ lenv_bot Δ = false.
Proof.
  induction Δ as [|[[U a]|] Δ IH]; intros H; simpl; [done| |].
  - pose proof (H 0 _ eq_refl) as HU. destruct U; try done. simpl.
    destruct IH as [-> ->]; [intros y o Hy; apply (H (S y) o Hy)|]. split; [set_solver|done].
  - apply IH. intros y o Hy. apply (H (S y) o Hy).
Qed.

Lemma lb_below_none W Γ Δ : (∀ y o, Δ !! y = Some o → spare o) →
  lb_below_hb W Γ None (tenv_heads ∅ ∪ lenv_heads Δ) (lenv_bot Δ).
Proof.
  intros H. destruct (spare_heads Δ H) as [-> ->]. rewrite tenv_heads_empty.
  unfold lb_below_hb, lb_below_h. set_solver.
Qed.

Lemma sinst_id_mut :
  (∀ T σ, (∀ a, σ a = SVar a) → sinst_ty σ T = T) ∧
  (∀ s σ, (∀ a, σ a = SVar a) → sinst σ s = s).
Proof.
  assert (∀ σ, (∀ a, σ a = SVar a) → ∀ a, sty_up σ a = SVar a) as Hup
    by (intros σ H [|a]; simpl; [done|]; unfold compose; by rewrite H).
  assert (∀ k σ, (∀ a, σ a = SVar a) → ∀ a, Nat.iter k sty_up σ a = SVar a) as Hit.
  { induction k as [|k IH]; intros σ H; simpl; [done|]. apply Hup. by apply IH. }
  apply ty_sty_mut_ind; intros; simpl; f_equal; eauto.
  all: by rewrite H.
Qed.

Lemma sinst_nil T : sinst_ty (slist []) T = T.
Proof. apply sinst_id_mut. intros a. unfold slist. simpl. f_equal. lia. Qed.



Lemma lenv_heads_nones n : lenv_heads (nones n) = ∅.
Proof. induction n; simpl; done. Qed.
Lemma lenv_bot_nones n : lenv_bot (nones n) = false.
Proof. induction n; simpl; done. Qed.

(** Unfold the heads of a concrete context into point equations. *)
Ltac heads_simpl H :=
  rewrite ?tenv_heads_empty in H; cbn [lenv_heads heads opt_heads lb_heads] in H;
  rewrite ?lenv_heads_nones in H; set_unfold in H.

(** A future (X, φ) under the hypothesis u ≺ φ for an upper point. *)
Lemma ub_below_var W Γ x u X φ :
  hc_fv Γ !! φ = Some (Some u) → (∀ y, y ∈ X → slt W Γ x y) → sle W Γ x u →
  ub_below_s W Γ (Some x) (X, Some (FVar φ)).
Proof.
  intros Hφ HX Hu. split_and!; [done| |done]. simpl. intros φ' [= <-].
  destruct Hu as [->|Hu]; [by apply fl_v|]. eapply fl_trans; [exact Hu|by apply fl_v].
Qed.

Lemma ub_below_varb W Γ x u X b φ :
  b = false → hc_fv Γ !! φ = Some (Some u) → (∀ y, y ∈ X → slt W Γ x y) → sle W Γ x u →
  ub_below_s W Γ (Some x) (sf_unionb (∅, Some (FVar φ)) X b).
Proof.
  intros -> Hφ HX Hu. apply ub_below_var with u; [done| |done].
  intros y Hy. apply HX. set_solver.
Qed.

Ltac bot_false := cbn [lenv_bot hbot orb]; rewrite ?lenv_bot_nones; reflexivity.
