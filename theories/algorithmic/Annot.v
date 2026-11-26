(** * Annotated terms and the split by occurrence

    The algorithmic layer types annotated terms [aexpr]. An annotation
    records a choice that the declarative judgment [typed] makes and the
    term does not show. [erase] removes every annotation and gives the
    term of lang/Syntax.v that [typed] reads. Annotations live only here.
    No program, no rule of [typed] and no theorem outside
    theories/algorithmic mentions them.

    - [ANew C S m1 m2] is plain [new] at a fresh base with constraint C,
      protocol S and tickets m1, m2 (E-New).
    - [ANewF x κ S m1 m2] is plain [new] at the field x·κ (E-New-Field).
    - [AForce xs ss t] is [force t] at the point instance xs and the
      session instance ss (E-Force).
    - [AAsc T c t] is t at the type T and the cost c (E-Sub).
    - [APack lb m C T xs t] packs t at the witness xs (E-Pack).
    - [AOpen i U t] opens the existential of the variable i around t,
      with the result type U (E-Open). Inside t the opened point
      variables are 0, …, m − 1 and every other point variable is
      shifted by m, as in the premise of E-Open, so annotations in t can
      name the opened points.

    The other forms are those of [expr]. A λ, an injection, a case and a
    box carry no annotation and are typed against an expected type.

    The split of a binary rule is computed from the first subterm
    ([tpart], [lpart]). An end goes to the first premise when the first
    subterm mentions it. A linear variable goes to the first premise when
    the first subterm mentions it. An unlimited variable goes to both. *)

From GV Require Export static.Sinst cost.Exact.

Inductive aexpr :=
  | AVar (x : nat)
  | AUnit
  | AChan (o : cend)
  | ALam (t : aexpr)
  | AApp (t1 t2 : aexpr)
  | APair (t1 t2 : aexpr)
  | ALetU (t1 t2 : aexpr)
  | ALetP (t1 t2 : aexpr)
  | AInj (b : bool) (t : aexpr)
  | ACase (t t1 t2 : aexpr)
  | ABox (t : aexpr)
  | ANew (C : bcs) (S : sty) (m1 m2 : fuel)
  | ANewF (x : point) (κ : field) (S : sty) (m1 m2 : fuel)
  | AOp (k : prim) (t : aexpr)
  | AForce (xs : list point) (ss : list sty) (t : aexpr)
  | AAsc (T : ty) (c : fuel) (t : aexpr)
  | APack (lb : lbound) (m : nat) (C : bcs) (T : ty) (xs : list point) (t : aexpr)
  | AOpen (i : nat) (U : ty) (t : aexpr).

Fixpoint erase (t : aexpr) : expr :=
  match t with
  | AVar x => Var x
  | AUnit => EUnit
  | AChan o => Chan o
  | ALam t => Lam (erase t)
  | AApp t1 t2 => App (erase t1) (erase t2)
  | APair t1 t2 => Pair (erase t1) (erase t2)
  | ALetU t1 t2 => LetU (erase t1) (erase t2)
  | ALetP t1 t2 => LetP (erase t1) (erase t2)
  | AInj b t => Inj b (erase t)
  | ACase t t1 t2 => Case (erase t) (erase t1) (erase t2)
  | ABox t => EBox (erase t)
  | ANew _ _ _ _ | ANewF _ _ _ _ _ => ENew
  | AOp k t => Op k (erase t)
  | AForce _ _ t => EForce (erase t)
  | AAsc _ _ t | APack _ _ _ _ _ t | AOpen _ _ t => erase t
  end.

(** ** Free variables, decided *)

Fixpoint occb (x : nat) (e : expr) : bool :=
  match e with
  | Var y => bool_decide (x = y)
  | EUnit | Chan _ | ENew => false
  | Lam e | EBox e => occb (S x) e
  | App e1 e2 | Pair e1 e2 | LetU e1 e2 => occb x e1 || occb x e2
  | LetP e1 e2 => occb x e1 || occb (S (S x)) e2
  | Inj _ e | Op _ e => occb x e
  | Case e e1 e2 => occb x e || occb (S x) e1 || occb (S x) e2
  end.

Lemma occb_spec e : ∀ x, occb x e = true ↔ freevar x e.
Proof.
  induction e; intros n; simpl;
    rewrite ?orb_true_iff, ?IHe, ?IHe1, ?IHe2, ?IHe3; try done.
  - by rewrite bool_decide_eq_true.
  - tauto.
Qed.

(** ** The split by occurrence *)

Definition tpart (e : expr) (Θ : tenv) : tenv * tenv :=
  (filter (λ oe : cend * tentry, oe.1 ∈ fends e) Θ,
   filter (λ oe : cend * tentry, oe.1 ∉ fends e) Θ).

Definition unlb (T : ty) : bool :=
  match T with TBox _ _ _ _ _ _ => true | _ => false end.

Lemma unlb_spec T : unlb T = true ↔ unlimited T.
Proof. destruct T; simpl; done. Qed.

Fixpoint lpart_at (e : expr) (n : nat) (Δ : lenv) : lenv * lenv :=
  match Δ with
  | [] => ([], [])
  | None :: Δ' => let p := lpart_at e (S n) Δ' in (None :: p.1, None :: p.2)
  | Some T :: Δ' =>
      let p := lpart_at e (S n) Δ' in
      if unlb T then (Some T :: p.1, Some T :: p.2)
      else if occb n e then (Some T :: p.1, None :: p.2)
      else (None :: p.1, Some T :: p.2)
  end.

Definition lpart (e : expr) (Δ : lenv) : lenv * lenv := lpart_at e 0 Δ.

Lemma tpart_split e Θ : tsplit Θ (tpart e Θ).1 (tpart e Θ).2.
Proof.
  unfold tpart; simpl. split.
  - apply map_disjoint_spec. intros o x y. rewrite !map_lookup_filter_Some. simpl. naive_solver.
  - symmetry. apply map_filter_union_complement.
Qed.

(** A split whose first part has the ends of e is the computed one. *)
Lemma tpart_eq e Θ Θ1 Θ2 : tsplit Θ Θ1 Θ2 → dom Θ1 = fends e → tpart e Θ = (Θ1, Θ2).
Proof.
  intros [Hd ->] Hdom. unfold tpart. f_equal; apply map_eq; intros o.
  - destruct (Θ1 !! o) as [x|] eqn:E1.
    + apply map_lookup_filter_Some. split; [by apply lookup_union_Some_l|].
      simpl. rewrite <-Hdom. by eapply elem_of_dom_2.
    + apply map_lookup_filter_None. right. intros x Hx. simpl. rewrite <-Hdom.
      rewrite not_elem_of_dom. done.
  - destruct (Θ2 !! o) as [x|] eqn:E2.
    + assert (Θ1 !! o = None) as E1 by (by eapply map_disjoint_Some_r).
      apply map_lookup_filter_Some. split; [by rewrite lookup_union_r|].
      simpl. rewrite <-Hdom. by apply not_elem_of_dom.
    + apply map_lookup_filter_None. right. intros x Hx. simpl. rewrite <-Hdom.
      apply lookup_union_Some_raw in Hx as [Hx|[_ Hx]]; [|congruence].
      intros Hn. apply Hn. by eapply elem_of_dom_2.
Qed.

Lemma lpart_at_split e n Δ : lenv_split Δ (lpart_at e n Δ).1 (lpart_at e n Δ).2.
Proof.
  revert n. induction Δ as [|[T|] Δ IH]; intros n; simpl; [constructor| |constructor; apply IH].
  destruct (unlb T) eqn:Eu; [apply lsplit_unl; [by apply unlb_spec|apply IH]|].
  destruct (occb n e); [apply lsplit_l, IH|apply lsplit_r, IH].
Qed.

Lemma lpart_split e Δ : lenv_split Δ (lpart e Δ).1 (lpart e Δ).2.
Proof. apply lpart_at_split. Qed.

Lemma tpart_tsplit e Θ Θ1 Θ2 : tpart e Θ = (Θ1, Θ2) → tsplit Θ Θ1 Θ2.
Proof. intros E. pose proof (tpart_split e Θ) as H. by rewrite E in H. Qed.

Lemma lpart_lsplit e Δ Δ1 Δ2 : lpart e Δ = (Δ1, Δ2) → lenv_split Δ Δ1 Δ2.
Proof. intros E. pose proof (lpart_split e Δ) as H. by rewrite E in H. Qed.

(** ** Weakening by unlimited entries *)

Lemma lenv_wk_refl Δ : lenv_wk Δ Δ.
Proof. induction Δ; constructor; done. Qed.

Lemma lenv_wk_heads Δ Δ' : lenv_wk Δ Δ' → lenv_heads Δ' = lenv_heads Δ ∧ lenv_bot Δ' = lenv_bot Δ.
Proof.
  induction 1 as [|[T|] Δ Δ' _ [IH1 IH2]|U Δ Δ' HU _ [IH1 IH2]]; simpl; try done.
  - by rewrite IH1, IH2.
  - rewrite unlimited_heads, unlimited_hbot by done. rewrite IH1, IH2. split; [set_solver|done].
Qed.

Lemma lenv_wk_unl Δ Δ' : lenv_wk Δ Δ' → lenv_unl Δ → lenv_unl Δ'.
Proof.
  induction 1 as [|o Δ Δ' _ IH|U Δ Δ' HU _ IH]; intros H o' Ho'.
  - by apply H.
  - apply elem_of_cons in Ho' as [->|Ho'].
    + apply H, list_elem_of_here.
    + apply IH; [intros o'' Ho''; apply H, list_elem_of_further, Ho''|done].
  - apply elem_of_cons in Ho' as [->|Ho'].
    + right. eauto.
    + apply IH; [intros o'' Ho''; apply H, list_elem_of_further, Ho''|done].
Qed.

Lemma lenv_wk_only Δ Δ' x T : lenv_wk Δ Δ' → lenv_only Δ x T → lenv_only Δ' x T.
Proof.
  intros Hw [Hx Hy]. split; [by eapply lenv_wk_sub|]. intros y σ Hne Hσ.
  destruct (unlb σ) eqn:E; [by apply unlb_spec|].
  apply (Hy y σ Hne). eapply lenv_wk_lin; [exact Hw|exact Hσ|].
  rewrite <-unlb_spec, E. done.
Qed.

Lemma lenv_wk_contr Δ Δ' : lenv_wk Δ Δ' → lenv_contr Δ' → lenv_contr Δ.
Proof. intros Hw H i T Hi. apply (H i). by eapply lenv_wk_sub. Qed.

Lemma lenv_wk_pinst σ Δ Δ' : lenv_wk Δ Δ' → lenv_wk (lenv_pinst σ Δ) (lenv_pinst σ Δ').
Proof. induction 1; simpl; constructor; try done. by apply unlimited_pinst. Qed.

Lemma lenv_wk_insert Δ Δ' i X T :
  lenv_wk Δ Δ' → Δ !! i = Some (Some X) → lenv_wk (<[i := Some T]> Δ) (<[i := Some T]> Δ').
Proof.
  intros Hw. revert i. induction Hw as [|o Δ Δ' Hw0 IH|U Δ Δ' HU Hw0 IH]; intros [|i] Hi; simpl in *.
  - done.
  - done.
  - by constructor.
  - constructor. by apply IH.
  - done.
  - constructor; [done|by apply IH].
Qed.

Lemma lenv_wk_lage c Δ Δa Δ' :
  lenv_wk Δ Δ' → lage c Δ Δa → ∃ Δa', lage c Δ' Δa' ∧ lenv_wk Δa Δa'.
Proof.
  intros Hw. revert Δa. induction Hw as [|o Δ Δ' _ IH|U Δ Δ' HU _ IH]; intros Δa Ha.
  - inversion Ha; subst. exists []. split; constructor.
  - inversion Ha as [|? Δa0 Ha'|σ σ' ? Δa0 Hσ Ha']; subst;
      destruct (IH _ Ha') as (Δa' & H1 & H2).
    + exists (None :: Δa'). split; constructor; done.
    + exists (Some σ' :: Δa'). split; constructor; done.
  - inversion Ha as [|? Δa0 Ha'|]; subst. destruct (IH _ Ha') as (Δa' & H1 & H2).
    exists (Some U :: Δa'). split; [constructor; [by apply age_free, unlimited_tfree|done]|].
    by constructor.
Qed.

(** The computed split of a weakened context weakens the declarative
    split, when the first part holds exactly the variables that its
    term mentions, up to unlimited ones. *)
Lemma lpart_at_wk e n Δ Δ' Δ1 Δ2 :
  lenv_wk Δ Δ' → lenv_split Δ Δ1 Δ2 →
  (∀ x U, Δ1 !! x = Some (Some U) → ¬ unlimited U → freevar (n + x) e) →
  (∀ x, freevar (n + x) e → ∃ σ, Δ1 !! x = Some (Some σ)) →
  lenv_wk Δ1 (lpart_at e n Δ').1 ∧ lenv_wk Δ2 (lpart_at e n Δ').2.
Proof.
  intros Hw. revert n Δ1 Δ2. induction Hw as [|o Δ Δ' _ IH|U Δ Δ' HU _ IH];
    intros n Δ1 Δ2 Hs Hl Hf.
  - inversion Hs; subst. split; constructor.
  - assert (∀ o1 Δ1', (∀ x U, (o1 :: Δ1') !! x = Some (Some U) → ¬ unlimited U → freevar (n + x) e) →
              ∀ x U, Δ1' !! x = Some (Some U) → ¬ unlimited U → freevar (S n + x) e) as Hl'.
    { intros o1 Δ1' H x U' Hx Hu. replace (S n + x) with (n + S x) by lia. by apply (H (S x) U'). }
    assert (∀ (o1 : option ty) Δ1', (∀ x, freevar (n + x) e → ∃ σ, (o1 :: Δ1') !! x = Some (Some σ)) →
              ∀ x, freevar (S n + x) e → ∃ σ, Δ1' !! x = Some (Some σ)) as Hf'.
    { intros o1 Δ1' H x Hx. replace (S n + x) with (n + S x) in Hx by lia. by apply (H (S x)). }
    inversion Hs as [|Δ0 Δ10 Δ20 Hs'|σ Δ0 Δ10 Δ20 Hs'|σ Δ0 Δ10 Δ20 Hs'|U' Δ0 Δ10 Δ20 HU' Hs']; subst; simpl.
    + destruct (IH (S n) _ _ Hs' (Hl' _ _ Hl) (Hf' _ _ Hf)) as [H1 H2]. split; by constructor.
    + destruct (IH (S n) _ _ Hs' (Hl' _ _ Hl) (Hf' _ _ Hf)) as [H1 H2].
      destruct (unlb σ) eqn:Eu; [split; [by constructor|by apply lwk_drop; [apply unlb_spec|]]|].
      assert (occb n e = true) as ->.
      { apply occb_spec. replace n with (n + 0) by lia. apply (Hl 0 σ); [done|].
        rewrite <-unlb_spec, Eu. done. }
      split; by constructor.
    + destruct (IH (S n) _ _ Hs' (Hl' _ _ Hl) (Hf' _ _ Hf)) as [H1 H2].
      destruct (unlb σ) eqn:Eu; [split; [by apply lwk_drop; [apply unlb_spec|]|by constructor]|].
      assert (occb n e = false) as ->.
      { apply not_true_iff_false. rewrite occb_spec. intros Hx.
        replace n with (n + 0) in Hx by lia. destruct (Hf 0 Hx) as [? ?]. done. }
      split; by constructor.
    + destruct (IH (S n) _ _ Hs' (Hl' _ _ Hl) (Hf' _ _ Hf)) as [H1 H2].
      apply unlb_spec in HU'. rewrite HU'. split; by constructor.
  - inversion Hs as [|Δ0 Δ10 Δ20 Hs'| | |]; subst; simpl.
    assert (∀ x U, Δ10 !! x = Some (Some U) → ¬ unlimited U → freevar (S n + x) e) as Hl'.
    { intros x U' Hx Hu. replace (S n + x) with (n + S x) by lia. by apply (Hl (S x) U'). }
    assert (∀ x, freevar (S n + x) e → ∃ σ, Δ10 !! x = Some (Some σ)) as Hf'.
    { intros x Hx. replace (S n + x) with (n + S x) in Hx by lia. by apply (Hf (S x)). }
    destruct (IH (S n) _ _ Hs' Hl' Hf') as [H1 H2].
    apply unlb_spec in HU as HU'. rewrite HU'. split; by apply lwk_drop.
Qed.

Lemma lpart_wk e Δ Δ' Δ1 Δ2 :
  lenv_wk Δ Δ' → lenv_split Δ Δ1 Δ2 → vfacts Δ1 (λ x, freevar x e) →
  lenv_wk Δ1 (lpart e Δ').1 ∧ lenv_wk Δ2 (lpart e Δ').2.
Proof. intros Hw Hs [Hf Hl]. apply lpart_at_wk with (Δ := Δ); [done|done|exact Hl|exact Hf]. Qed.

(** ** Session variables of a box body

    A box body is checked at one instance, the k box variables at the
    fresh variables M, …, M + k − 1 above every free session variable of
    the box context. *)
Definition box_inst (M k : nat) : list sty := (λ i, SVar (M + i)) <$> seq 0 k.

Definition box_base (k : nat) (U : ty) (Δ : lenv) : nat := (tfv U - k) `max` lfv Δ.

Lemma box_inst_length M k : length (box_inst M k) = k.
Proof. unfold box_inst. by rewrite length_fmap, length_seq. Qed.

Lemma box_inst_lookup M k i : i < k → box_inst M k !! i = Some (SVar (M + i)).
Proof. intros Hi. unfold box_inst. rewrite list_lookup_fmap, lookup_seq_lt by done. done. Qed.

Lemma sinsts_box_inst N M k : sinsts N (box_inst M k).
Proof.
  unfold box_inst. split; [split|intros _]; apply Forall_fmap, Forall_forall; intros i _; done.
Qed.
