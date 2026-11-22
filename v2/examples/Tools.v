(** * Tools for example derivations (stage S2)

    Examples are typed in the deadlock-freedom projection [dftyped] and
    lifted to the merged judgment at N = ∞ by [dftyped_typed]
    (static/Conservativity.v). Programs create every channel with plain
    [new], so Θ is empty throughout. A creation at a field reads
    ⟨y, new⟩ for the end y it extends ([d_new_at]). *)

From GV Require Export static.Conservativity static.Weakening static.PointSubst.

(** let (a, b) = new in e, the ∃ of new bound at index 2 and opened. *)
Definition let_new (e : expr) : expr := ELet ENew (LetP (Var 0) e).

(** Occurrence of a variable, decidable. *)
Fixpoint occ (i : nat) (e : expr) : bool :=
  match e with
  | Var x => Nat.eqb x i
  | EUnit | Chan _ | ENew => false
  | Lam e | EBox e => occ (S i) e
  | App e1 e2 | Pair e1 e2 | LetU e1 e2 => occ i e1 || occ i e2
  | LetP e1 e2 => occ i e1 || occ (S (S i)) e2
  | Inj _ e | Op _ e => occ i e
  | Case e e1 e2 => occ i e || occ (S i) e1 || occ (S i) e2
  end.

Lemma tsplit_empty : tsplit ∅ ∅ ∅.
Proof. split; [apply map_disjoint_empty_l|by rewrite map_empty_union]. Qed.

Lemma tenv_heads_empty : tenv_heads ∅ = ∅.
Proof. apply set_eq. intros y. rewrite elem_of_tenv_heads. setoid_rewrite lookup_empty. set_solver. Qed.

(** An entry that the term does not need: absent or unlimited. *)
Definition spare (o : option ty) : Prop :=
  match o with None => True | Some U => unlimited U end.

Lemma spare_unl Δ : (∀ y o, Δ !! y = Some o → spare o) → lenv_unl Δ.
Proof.
  intros H o Ho. apply list_elem_of_lookup in Ho as [y Hy]. specialize (H y o Hy).
  destruct o as [U|]; [right; by exists U|by left].
Qed.

Lemma spare_only Δ x T :
  Δ !! x = Some (Some T) → (∀ y o, y ≠ x → Δ !! y = Some o → spare o) → lenv_only Δ x T.
Proof. intros Hx Hs. split; [done|]. intros y U Hne Hy. exact (Hs y _ Hne Hy). Qed.

Lemma d_var' W Γ Δ F x T :
  Δ !! x = Some (Some T) → (∀ y o, y ≠ x → Δ !! y = Some o → spare o) →
  dftyped W ∅ Γ Δ F (Var x) T.
Proof.
  intros Hx Hs. eapply d_var. by apply spare_only.
Qed.

Lemma d_unit' W Γ Δ F : (∀ y o, Δ !! y = Some o → spare o) → dftyped W ∅ Γ Δ F EUnit TUnit.
Proof. intros H. by apply d_unit, spare_unl. Qed.

Lemma d_new' W Γ Δ F (L : fact → Prop) S a1 a2 mt :
  (∀ y o, Δ !! y = Some o → spare o) → wf_new (bcs_of L) → scontr S →
  dftyped W ∅ Γ Δ F ENew
    (TEx LBot 1 (bcs_of L) (TProd (TSess S (pvar 0) a1 mt) (TSess (dual S) (pvar 0)‾ a2 mt))).
Proof. intros H HL HS. apply d_new; [by apply spare_unl|by apply wf_new_gen|done]. Qed.

(** A session type of the examples is contractive by computation. *)
Ltac contr_tac := vm_compute; exact I.

(** The split of a context whose only linear entry is y: everything to
    the left, the unlimited entries to both sides. *)
Lemma lsplit_only y (Δ : lenv) : (∀ z o, z ≠ y → Δ !! z = Some o → spare o) →
  lenv_split Δ Δ (<[y := None]> Δ).
Proof.
  revert y. induction Δ as [|o Δ IH]; intros y H; [apply lsplit_nil|].
  destruct y as [|y]; simpl.
  - destruct o as [U|]; [apply lsplit_l|apply lsplit_none].
    all: clear IH; induction Δ as [|o' Δ IH'] in H |- *; [apply lsplit_nil|].
    all: assert (spare o') as Ho' by (apply (H 1); done).
    all: destruct o' as [U'|]; [apply lsplit_unl; [done|]|apply lsplit_none];
      apply IH'; intros [|z] o Hz Hzo; [done|by apply (H (S (S z)))| |by apply (H (S (S z)))];
      try done.
  - assert (spare o) as Ho by (apply (H 0); done).
    destruct o as [U|]; [apply lsplit_unl; [done|]|apply lsplit_none];
      apply IH; intros z o' Hz Hzo; apply (H (S z)); [lia|done|lia|done].
Qed.

Lemma lenv_unl_only y (Δ : lenv) : (∀ z o, z ≠ y → Δ !! z = Some o → spare o) →
  lenv_unl (<[y := None]> Δ).
Proof.
  intros H. apply spare_unl. intros z o Hz. destruct (decide (z = y)) as [->|Hne].
  - apply list_lookup_insert_Some in Hz as [(_ & <- & _)|[? _]]; [done|done].
  - rewrite list_lookup_insert_ne in Hz by done. by apply (H z).
Qed.

(** A creation at the field κ of the point x of the end y, ⟨y, new⟩. *)
Lemma d_new_at W (Θ : tenv) Γ Δ F (y : nat) κ S0 x S a a1 a2 m m1 m2 :
  Θ = ∅ → Δ !! y = Some (Some (TSess S0 x a m)) → (∀ z o, z ≠ y → Δ !! z = Some o → spare o) →
  scontr S →
  dftyped W Θ Γ Δ F (Pair (Var y) ENew)
    (TProd (TSess S0 x a m) (TProd (TSess S (x·κ) a1 m1) (TSess (dual S) (x·κ)‾ a2 m2))).
Proof.
  intros -> Hy Hs HS. eapply d_pair; [apply tsplit_empty|apply (lsplit_only y), Hs| |].
  - eapply d_var'; [exact Hy|exact Hs].
  - apply d_new_fld; [by apply lenv_unl_only|done].
Qed.

(** The lexicographic order on triples of natural numbers. *)
Definition lex3 (a b : nat * nat * nat) : Prop :=
  let '(a1, a2, a3) := a in let '(b1, b2, b3) := b in
  a1 < b1 ∨ (a1 = b1 ∧ (a2 < b2 ∨ (a2 = b2 ∧ a3 < b3))).

Lemma lex3_wf : well_founded lex3.
Proof.
  intros [[a1 a2] a3]. revert a2 a3. induction a1 as [a1 IH1] using lt_wf_ind.
  intros a2. induction a2 as [a2 IH2] using lt_wf_ind.
  intros a3. induction a3 as [a3 IH3] using lt_wf_ind.
  constructor. intros [[b1 b2] b3] H. simpl in H.
  destruct H as [H|[<- [H|[<- H]]]]; eauto.
Qed.

Global Instance lex3_trans : Transitive lex3.
Proof. intros [[a1 a2] a3] [[b1 b2] b3] [[c1 c2] c3]; simpl; lia. Qed.

(** The number of fields of a name and the sum of their labels. *)
Fixpoint pn_depth (p : pname) : nat :=
  match p with NField q _ _ => S (pn_depth q) | _ => 0 end.
Fixpoint pn_fsum (p : pname) : nat :=
  match p with NField q _ κ => κ + pn_fsum q | _ => 0 end.

Definition pt_depth (x : point) : nat := pn_depth (pt_name x).
Definition pt_fsum (x : point) : nat := pn_fsum (pt_name x).

(** (wf-new) for a constraint on the new root alone, by a measure that
    rises along its facts and along program order. *)
Lemma wf_new_lex3 (L : fact → Prop) (m : point → nat * nat * nat) :
  (∀ x y, L (FLt x y) → in_tree0 x ∧ in_tree0 y) →
  (∀ x, lex3 (m x) (m x⁺) ∧ lex3 (m x) (m x‾⁺)) →
  (∀ x y, L (FLt x y) → lex3 (m x) (m y)) →
  wf_new (bcs_of L).
Proof.
  intros HL Hpo Hm. split.
  - intros x y Hf _. apply (HL x y Hf).
  - assert (∀ a x, m x = a → Acc (new_step (bcs_of L)) x) as Hacc.
    { intros a. induction (lex3_wf a) as [a _ IH]. intros x <-. constructor.
      intros y (_ & _ & [[Hf _]|[->| ->]]); eapply IH; try reflexivity.
      - by apply Hm.
      - apply Hpo.
      - apply Hpo. }
    intros x. by apply (Hacc (m x)).
Qed.

#[global] Hint Extern 1 (facts_const _) => (by intros ?? []) : core.

(** A tail of absent entries. *)
Abbreviation nones n := (replicate n (@None ty)).

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

(** The conservativity premise of E-Open at the existential of E-New, in
    a world without facts, from (wf-new) in the hint base [wfnew]. *)
Create HintDb wfnew.
Ltac cons_tac := apply cons_new; solve [eauto with wfnew].

(** Split by occurrence. An unlimited entry goes to both sides. *)
Ltac lsplit_go i e1 e2 :=
  lazymatch goal with
  | |- lenv_split [] _ _ => apply lsplit_nil
  | |- lenv_split (replicate _ None) _ _ => apply lsplit_nones
  | |- lenv_split (None :: _) _ _ => apply lsplit_none; lsplit_go (S i) e1 e2
  | |- lenv_split (Some ?U :: _) _ _ =>
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

Lemma sf_pinst_empty σ : sf_pinst σ (∅, None) = (∅, None).
Proof. unfold sf_pinst. simpl. by rewrite set_map_empty. Qed.

(** {x} ≺ F for a future with no points and no rest. *)
Lemma ub_below_empty W Γ x : ub_below_s W Γ x (∅, None).
Proof. destruct x; simpl; [split_and!; [set_solver|done|done]|done]. Qed.

(** The same for the upper point of an arrow, ⊤ included. *)
Lemma ubu_below_empty W Γ ub : ub_below_u W Γ ub (∅, None).
Proof. destruct ub; simpl; [done|apply (ub_below_empty W Γ (Some x))|done]. Qed.

Lemma ubu_pt W Γ x F : ub_below_s W Γ (Some x) F → ub_below_u W Γ (UPt x) F.
Proof. done. Qed.

Lemma spare_heads Δ : (∀ y o, Δ !! y = Some o → spare o) → lenv_heads Δ = ∅ ∧ lenv_bot Δ = false.
Proof.
  induction Δ as [|[U|] Δ IH]; intros H; simpl; [done| |].
  - pose proof (H 0 _ eq_refl) as HU. destruct U; try done. simpl.
    destruct IH as [-> ->]; [intros y o Hy; apply (H (S y) o Hy)|]. split; [set_solver|done].
  - apply IH. intros y o Hy. apply (H (S y) o Hy).
Qed.

Lemma lb_below_none W Γ Δ : (∀ y o, Δ !! y = Some o → spare o) →
  lbx_below_h W Γ LNone (tenv_heads ∅ ∪ lenv_heads Δ) (lenv_bot Δ).
Proof.
  intros H. destruct (spare_heads Δ H) as [-> ->]. rewrite tenv_heads_empty.
  simpl. split; [set_solver|done].
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

(** A future (X, everything above u) for an upper point u. *)
Lemma ub_below_var W Γ x u X :
  (∀ y, y ∈ X → slt W Γ x y) → sle W Γ x u →
  ub_below_s W Γ (Some x) (X, Some (FRest (RAbove u))).
Proof. intros HX Hu. split_and!; [done| |done]. simpl. by intros r [= <-]. Qed.

Lemma ub_below_varb W Γ x u X b :
  b = false → (∀ y, y ∈ X → slt W Γ x y) → sle W Γ x u →
  ub_below_s W Γ (Some x) (sf_unionb (∅, Some (FRest (RAbove u))) X b).
Proof.
  intros -> HX Hu. apply ub_below_var; [|done].
  intros y Hy. apply HX. set_solver.
Qed.

Ltac bot_false := cbn [lenv_bot hbot orb]; rewrite ?lenv_bot_nones; reflexivity.
