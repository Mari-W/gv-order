(** * Syntax (stage S1, proposal §2.2, §3.2)

    Terms use de Bruijn indices for variables. Channels are names, and a
    channel c has two ends c⁺ and c⁻. A value [Chan o] names one end o.
    The name of an end never depends on a point, and no term mentions a
    point.

    Primitives are saturated operators [Op k e] and the nullary [ENew ℓ].
    The constants of GV are derived λ-values ([k_send] := λx. send x and
    so on), so every value of arrow type is a λ (§3.2). [ENew ℓ] carries
    a family label ℓ and [Op (PNewAt κ) e] a field label κ. The runtime
    erases both labels into the step label, where the relation reads
    them (§2.5). *)

From stdpp Require Export base strings gmap gmultiset countable.

Definition chan := string.

(** ** Ends *)

Inductive cend := EPos (c : chan) | ENeg (c : chan).

Global Instance cend_eq_dec : EqDecision cend.
Proof. solve_decision. Defined.

Global Instance cend_countable : Countable cend.
Proof.
  apply (inj_countable'
    (λ o, match o with EPos c => inl c | ENeg c => inr c end)
    (λ s, match s with inl c => EPos c | inr c => ENeg c end)).
  by intros [].
Qed.

(** The channel of an end. *)
Definition ech (o : cend) : chan := match o with EPos c | ENeg c => c end.

(** The partner end ō: the other end of the same channel. *)
Definition edual (o : cend) : cend :=
  match o with EPos c => ENeg c | ENeg c => EPos c end.

Lemma edual_edual o : edual (edual o) = o.
Proof. by destruct o. Qed.
Lemma edual_ne o : edual o ≠ o.
Proof. by destruct o. Qed.
Lemma ech_edual o : ech (edual o) = ech o.
Proof. by destruct o. Qed.
Lemma edual_inj o o' : edual o = edual o' → o = o'.
Proof. destruct o, o'; simpl; congruence. Qed.
(** Two ends of one channel are equal or partners. *)
Lemma ech_eq o o' : ech o = ech o' → o' = o ∨ o' = edual o.
Proof. destruct o, o'; simpl; intros ->; auto. Qed.

(** ** Labels

    A family label ℓ of [new_ℓ] and a field label κ of [new_κ]. Both are
    names drawn from a countable set, like a branch label. *)
Definition family := nat.
Definition field := nat.

(** ** Saturated primitive operators *)

Inductive prim :=
  | PSend                 (* send ⟨v, o⟩ *)
  | PRecv                 (* recv o *)
  | PClose                (* close o *)
  | PSel (i : bool)       (* select_i o, i = false for the first branch *)
  | PBra                  (* branch o *)
  | PLink                 (* link ⟨o1, o2⟩ *)
  | PSpawn                (* spawn v, v a thunk *)
  | PForce                (* force !e *)
  | PNewAt (κ : field).   (* new_κ o, anchored creation at the field κ of o *)

Global Instance prim_eq_dec : EqDecision prim.
Proof. solve_decision. Defined.

Global Instance prim_countable : Countable prim.
Proof.
  apply (inj_countable'
    (λ k, match k with
          | PSend => inl 0 | PRecv => inl 1 | PClose => inl 2
          | PSel false => inl 3 | PSel true => inl 4 | PBra => inl 5
          | PLink => inl 6 | PSpawn => inl 7 | PForce => inl 8
          | PNewAt κ => inr κ
          end)
    (λ n, match n with
          | inl 0 => PSend | inl 1 => PRecv | inl 2 => PClose
          | inl 3 => PSel false | inl 4 => PSel true | inl 5 => PBra
          | inl 6 => PLink | inl 7 => PSpawn | inl _ => PForce
          | inr κ => PNewAt κ
          end)).
  by intros [| | |[]| | | | |].
Qed.

(** ** Terms *)

Inductive expr :=
  | Var (x : nat)
  | EUnit                          (* the unit value ∗ *)
  | Chan (o : cend)                (* the end o *)
  | Lam (e : expr)                 (* λa.e, binds 1 *)
  | App (e1 e2 : expr)
  | Pair (e1 e2 : expr)            (* ⟨e1,e2⟩ *)
  | LetU (e1 e2 : expr)            (* let ∗ = e1 in e2 *)
  | LetP (e1 e2 : expr)            (* let ⟨a,b⟩ = e1 in e2, binds 2 in e2:
                                      index 1 = a, index 0 = b *)
  | Inj1 (e : expr)
  | Inj2 (e : expr)
  | Case (e e1 e2 : expr)          (* case e (a.e1) (a.e2), each branch
                                      binds the payload at index 0 *)
  | EBox (e : expr)                (* !e, a recursive thunk value; binds
                                      the thunk itself at index 0 *)
  | ENew (ℓ : family)              (* new_ℓ *)
  | Op (k : prim) (e : expr).      (* a saturated primitive *)

Abbreviation ESend e := (Op PSend e).
Abbreviation ERecv e := (Op PRecv e).
Abbreviation EClose e := (Op PClose e).
Abbreviation ESel i e := (Op (PSel i) e).
Abbreviation EBra e := (Op PBra e).
Abbreviation ELink e := (Op PLink e).
Abbreviation ESpawn e := (Op PSpawn e).
Abbreviation EForce e := (Op PForce e).
Abbreviation ENewAt κ e := (Op (PNewAt κ) e).

(** [new] for a program with one family. *)
Abbreviation ENew0 := (ENew 0).

(** The injection of a branch: inj₁ for false, inj₂ for true. *)
Definition inj_of (b : bool) (e : expr) : expr := if b then Inj2 e else Inj1 e.

(** ** Values *)

Fixpoint is_val (e : expr) : bool :=
  match e with
  | EUnit | Chan _ | Lam _ | EBox _ => true
  | Pair e1 e2 => is_val e1 && is_val e2
  | Inj1 e | Inj2 e => is_val e
  | _ => false
  end.

Lemma is_val_true e : is_val e → is_val e = true.
Proof. by destruct (is_val e). Qed.

Lemma is_val_of_true e : is_val e = true → is_val e.
Proof. by intros ->. Qed.

Global Instance expr_eq_dec : EqDecision expr.
Proof. solve_decision. Defined.

Global Instance expr_countable : Countable expr.
Proof.
  set (enc := fix go e : gen_tree (nat + cend + prim) :=
    match e with
    | Var x => GenLeaf (inl (inl x))
    | EUnit => GenNode 0 []
    | Chan o => GenLeaf (inl (inr o))
    | Lam e => GenNode 1 [go e]
    | App e1 e2 => GenNode 2 [go e1; go e2]
    | Pair e1 e2 => GenNode 3 [go e1; go e2]
    | LetU e1 e2 => GenNode 4 [go e1; go e2]
    | LetP e1 e2 => GenNode 5 [go e1; go e2]
    | Inj1 e => GenNode 6 [go e]
    | Inj2 e => GenNode 7 [go e]
    | Case e e1 e2 => GenNode 8 [go e; go e1; go e2]
    | EBox e => GenNode 9 [go e]
    | ENew ℓ => GenNode 10 [GenLeaf (inl (inl ℓ))]
    | Op k e => GenNode 11 [GenLeaf (inr k); go e]
    end).
  set (dec := fix go t : expr :=
    match t with
    | GenLeaf (inl (inl x)) => Var x
    | GenNode 0 [] => EUnit
    | GenLeaf (inl (inr o)) => Chan o
    | GenNode 1 [t] => Lam (go t)
    | GenNode 2 [t1; t2] => App (go t1) (go t2)
    | GenNode 3 [t1; t2] => Pair (go t1) (go t2)
    | GenNode 4 [t1; t2] => LetU (go t1) (go t2)
    | GenNode 5 [t1; t2] => LetP (go t1) (go t2)
    | GenNode 6 [t] => Inj1 (go t)
    | GenNode 7 [t] => Inj2 (go t)
    | GenNode 8 [t; t1; t2] => Case (go t) (go t1) (go t2)
    | GenNode 9 [t] => EBox (go t)
    | GenNode 10 [GenLeaf (inl (inl ℓ))] => ENew ℓ
    | GenNode 11 [GenLeaf (inr k); t] => Op k (go t)
    | _ => EUnit
    end).
  apply (inj_countable' enc dec).
  intros e; induction e; simpl; congruence.
Qed.

(** ** Renaming and parallel substitution *)

Definition scons {A} (a : A) (σ : nat → A) : nat → A :=
  λ x, match x with 0 => a | S x' => σ x' end.
Infix ".:" := scons (at level 55, right associativity).

Definition upren (r : nat → nat) : nat → nat := 0 .: (S ∘ r).

Fixpoint rename (r : nat → nat) (e : expr) : expr :=
  match e with
  | Var x => Var (r x)
  | EUnit | Chan _ | ENew _ => e
  | Lam e => Lam (rename (upren r) e)
  | App e1 e2 => App (rename r e1) (rename r e2)
  | Pair e1 e2 => Pair (rename r e1) (rename r e2)
  | LetU e1 e2 => LetU (rename r e1) (rename r e2)
  | LetP e1 e2 => LetP (rename r e1) (rename (upren (upren r)) e2)
  | Inj1 e => Inj1 (rename r e)
  | Inj2 e => Inj2 (rename r e)
  | Case e e1 e2 =>
      Case (rename r e) (rename (upren r) e1) (rename (upren r) e2)
  | EBox e => EBox (rename (upren r) e)
  | Op k e => Op k (rename r e)
  end.

Definition up (σ : nat → expr) : nat → expr := Var 0 .: (rename S ∘ σ).

Fixpoint subst (σ : nat → expr) (e : expr) : expr :=
  match e with
  | Var x => σ x
  | EUnit | Chan _ | ENew _ => e
  | Lam e => Lam (subst (up σ) e)
  | App e1 e2 => App (subst σ e1) (subst σ e2)
  | Pair e1 e2 => Pair (subst σ e1) (subst σ e2)
  | LetU e1 e2 => LetU (subst σ e1) (subst σ e2)
  | LetP e1 e2 => LetP (subst σ e1) (subst (up (up σ)) e2)
  | Inj1 e => Inj1 (subst σ e)
  | Inj2 e => Inj2 (subst σ e)
  | Case e e1 e2 => Case (subst σ e) (subst (up σ) e1) (subst (up σ) e2)
  | EBox e => EBox (subst (up σ) e)
  | Op k e => Op k (subst σ e)
  end.

(** β-substitutions: [subst1 v e] is e[v/a] for a Lam-bound a, and
    [subst2 u v e] instantiates the two binders of LetP, e[u/a][v/b]. *)
Definition subst1 (v : expr) (e : expr) : expr := subst (v .: Var) e.
Definition subst2 (u v : expr) (e : expr) : expr := subst (v .: u .: Var) e.

(** ** The constants of GV as derived λ-values (§3.2) *)

Definition k_send : expr := Lam (ESend (Var 0)).
Definition k_recv : expr := Lam (ERecv (Var 0)).
Definition k_close : expr := Lam (EClose (Var 0)).
Definition k_select (i : bool) : expr := Lam (ESel i (Var 0)).
Definition k_branch : expr := Lam (EBra (Var 0)).
Definition k_link : expr := Lam (ELink (Var 0)).
Definition k_spawn : expr := Lam (ESpawn (Var 0)).
Definition k_force : expr := Lam (EForce (Var 0)).
Definition k_new (ℓ : family) : expr := Lam (LetU (Var 0) (ENew ℓ)).
Definition k_new_at (κ : field) : expr := Lam (ENewAt κ (Var 0)).

(** ** Closedness, free channels and free ends *)

Fixpoint closed_at (n : nat) (e : expr) : bool :=
  match e with
  | Var x => bool_decide (x < n)
  | EUnit | Chan _ | ENew _ => true
  | Lam e => closed_at (S n) e
  | App e1 e2 | Pair e1 e2 | LetU e1 e2 => closed_at n e1 && closed_at n e2
  | LetP e1 e2 => closed_at n e1 && closed_at (S (S n)) e2
  | Inj1 e | Inj2 e | Op _ e => closed_at n e
  | Case e e1 e2 => closed_at n e && closed_at (S n) e1 && closed_at (S n) e2
  | EBox e => closed_at (S n) e
  end.

(** The ends a term mentions. Terms bind no channel. *)
Fixpoint fends (e : expr) : gset cend :=
  match e with
  | Var _ | EUnit | ENew _ => ∅
  | Chan o => {[o]}
  | Lam e | Inj1 e | Inj2 e | EBox e | Op _ e => fends e
  | App e1 e2 | Pair e1 e2 | LetU e1 e2 | LetP e1 e2 => fends e1 ∪ fends e2
  | Case e e1 e2 => fends e ∪ fends e1 ∪ fends e2
  end.

(** The channels a term mentions. *)
Definition fchans (e : expr) : gset chan := set_map ech (fends e).

Lemma closed_k_constants :
  closed_at 0 k_send ∧ closed_at 0 k_recv ∧ closed_at 0 k_close ∧
  (∀ i, closed_at 0 (k_select i)) ∧ closed_at 0 k_branch ∧ closed_at 0 k_link ∧
  closed_at 0 k_spawn ∧ closed_at 0 k_force ∧ (∀ ℓ, closed_at 0 (k_new ℓ)) ∧
  (∀ κ, closed_at 0 (k_new_at κ)).
Proof. done. Qed.

(** ** Basic lemmas about substitution *)

Lemma upren_ext r r' : (∀ x, r x = r' x) → ∀ x, upren r x = upren r' x.
Proof. intros H [|x]; simpl; [done|]. unfold compose. by rewrite H. Qed.

Lemma rename_ext e : ∀ r r', (∀ x, r x = r' x) → rename r e = rename r' e.
Proof. induction e; intros r r' H; simpl; f_equal; eauto using upren_ext. Qed.

Lemma up_ext σ σ' : (∀ x, σ x = σ' x) → ∀ x, up σ x = up σ' x.
Proof. intros H [|x]; simpl; [done|]. unfold compose. by rewrite H. Qed.

Lemma subst_ext e : ∀ σ σ', (∀ x, σ x = σ' x) → subst σ e = subst σ' e.
Proof. induction e; intros σ σ' H; simpl; f_equal; eauto using up_ext. Qed.

Lemma subst_ids e : subst Var e = e.
Proof.
  induction e; simpl; f_equal; auto.
  all: first [ rewrite (subst_ext _ (up Var) Var); [done|by intros [|x]]
             | rewrite (subst_ext _ (up (up Var)) Var); [done|by intros [|[|x]]] ].
Qed.

Lemma rename_rename e : ∀ r r',
  rename r (rename r' e) = rename (λ x, r (r' x)) e.
Proof.
  induction e; intros r r'; simpl; f_equal; auto.
  all: match goal with IH : ∀ r r', rename r (rename r' ?e) = _ |- _ =>
         rewrite IH; apply rename_ext; by intros [|[|x]] end.
Qed.

Lemma subst_rename e : ∀ σ r,
  subst σ (rename r e) = subst (λ x, σ (r x)) e.
Proof.
  induction e; intros σ r; simpl; f_equal; auto.
  all: match goal with IH : ∀ σ r, subst σ (rename r ?e) = _ |- _ =>
         rewrite IH; apply subst_ext; by intros [|[|x]] end.
Qed.

Lemma rename_subst e : ∀ r σ,
  rename r (subst σ e) = subst (λ x, rename r (σ x)) e.
Proof.
  induction e; intros r σ; simpl; f_equal; auto.
  all: match goal with IH : ∀ r σ, rename r (subst σ ?e) = _ |- _ =>
         rewrite IH; apply subst_ext; intros [|[|x]]; simpl; try done;
         unfold compose; by rewrite !rename_rename end.
Qed.

Lemma subst_subst e : ∀ σ τ,
  subst σ (subst τ e) = subst (λ x, subst σ (τ x)) e.
Proof.
  induction e; intros σ τ; simpl; f_equal; auto.
  all: match goal with IH : ∀ σ τ, subst σ (subst τ ?e) = _ |- _ =>
         rewrite IH; apply subst_ext; intros [|[|x]]; simpl; try done;
         unfold compose; rewrite ?subst_rename, ?rename_subst;
         apply subst_ext; by intros y end.
Qed.

(** β-substitution after substitution under one or two binders. *)
Lemma subst1_subst w γ e : subst1 w (subst (up γ) e) = subst (w .: γ) e.
Proof.
  unfold subst1. rewrite subst_subst. apply subst_ext.
  intros [|x]; simpl; [done|]. unfold compose. rewrite subst_rename.
  etrans; [apply subst_ext; by intros y|]. apply subst_ids.
Qed.

Lemma subst2_subst u w γ e :
  subst2 u w (subst (up (up γ)) e) = subst (w .: u .: γ) e.
Proof.
  unfold subst2. rewrite subst_subst. apply subst_ext.
  intros [|[|x]]; simpl; [done..|]. unfold compose.
  rewrite !subst_rename.
  etrans; [apply subst_ext; by intros y|]. apply subst_ids.
Qed.

(** ** Free-variable predicates *)

Definition upP (P : nat → Prop) : nat → Prop :=
  λ x, match x with 0 => True | S x' => P x' end.

Fixpoint allfv (P : nat → Prop) (e : expr) : Prop :=
  match e with
  | Var x => P x
  | EUnit | Chan _ | ENew _ => True
  | Lam e => allfv (upP P) e
  | App e1 e2 | Pair e1 e2 | LetU e1 e2 => allfv P e1 ∧ allfv P e2
  | LetP e1 e2 => allfv P e1 ∧ allfv (upP (upP P)) e2
  | Inj1 e | Inj2 e | Op _ e => allfv P e
  | Case e e1 e2 => allfv P e ∧ allfv (upP P) e1 ∧ allfv (upP P) e2
  | EBox e => allfv (upP P) e
  end.

Lemma upP_mono (P Q : nat → Prop) :
  (∀ x, P x → Q x) → ∀ x, upP P x → upP Q x.
Proof. intros H [|x]; simpl; auto. Qed.

Lemma allfv_mono e : ∀ (P Q : nat → Prop),
  (∀ x, P x → Q x) → allfv P e → allfv Q e.
Proof.
  induction e; simpl; intros P Q H HP; auto; destruct_and?; split_and?;
    eauto using upP_mono.
Qed.

Lemma allfv_forall (P : nat → Prop) e : (∀ x, P x) → allfv P e.
Proof.
  revert P. induction e; simpl; intros P HP; split_and?; auto.
  all: first [apply IHe|apply IHe1|apply IHe2|apply IHe3];
    intros [|[|x]]; simpl; auto.
Qed.

(** Occurrence of a free variable. *)
Fixpoint freevar (x : nat) (e : expr) : Prop :=
  match e with
  | Var y => x = y
  | EUnit | Chan _ | ENew _ => False
  | Lam e => freevar (S x) e
  | App e1 e2 | Pair e1 e2 | LetU e1 e2 => freevar x e1 ∨ freevar x e2
  | LetP e1 e2 => freevar x e1 ∨ freevar (S (S x)) e2
  | Inj1 e | Inj2 e | Op _ e => freevar x e
  | Case e e1 e2 => freevar x e ∨ freevar (S x) e1 ∨ freevar (S x) e2
  | EBox e => freevar (S x) e
  end.

Lemma upP_upren (P : nat → Prop) r x :
  upP (λ y, P (r y)) x → upP P (upren r x).
Proof. destruct x; simpl; auto. Qed.

Lemma allfv_rename e : ∀ (P : nat → Prop) r,
  allfv (λ x, P (r x)) e → allfv P (rename r e).
Proof.
  induction e; simpl; intros P r H; auto; destruct_and?; split_and?; auto.
  all: first [apply IHe|apply IHe1|apply IHe2|apply IHe3];
    eapply allfv_mono; [|eassumption]; intros x Hx;
    first [ by apply upP_upren
          | apply upP_upren; eapply upP_mono; [|exact Hx]; apply upP_upren ].
Qed.

(** ** Ends under renaming and substitution *)

Lemma fends_rename e : ∀ r, fends (rename r e) = fends e.
Proof. induction e; intros r; simpl; auto; by rewrite ?IHe1, ?IHe2, ?IHe3. Qed.

Lemma fends_subst_super e : ∀ γ, fends e ⊆ fends (subst γ e).
Proof. induction e; intros γ; simpl; set_solver. Qed.

Lemma fends_subst_free e : ∀ y γ,
  freevar y e → fends (γ y) ⊆ fends (subst γ e).
Proof.
  induction e; simpl; intros y γ Hf; try done.
  all: try (by subst).
  all: repeat match goal with
    | H : _ ∨ _ |- _ => destruct H as [H|H]
    end.
  all: repeat match goal with
    | IH : ∀ y γ, freevar y ?e → _, H : freevar ?z ?e |- _ =>
        let H' := fresh in
        lazymatch z with
        | S (S y) => pose proof (IH z (up (up γ)) H) as H'
        | S y => pose proof (IH z (up γ) H) as H'
        | _ => pose proof (IH z γ H) as H'
        end;
        simpl in H'; unfold compose in H'; rewrite ?fends_rename in H';
        clear H
    end.
  all: set_solver.
Qed.

Lemma fends_subst e : ∀ γ (D : gset cend),
  allfv (λ x, fends (γ x) ⊆ D) e →
  fends (subst γ e) ⊆ fends e ∪ D.
Proof.
  induction e; simpl; intros γ D HP; destruct_and?; try set_solver.
  all: repeat match goal with
    | IH : ∀ γ D, allfv _ ?e → fends (subst γ ?e) ⊆ _, H : allfv _ ?e |- _ =>
        let H' := fresh in
        first [ unshelve epose proof (IH γ D H) as H'
              | unshelve epose proof (IH (up γ) D _) as H';
                [eapply allfv_mono; [|exact H]; intros [|x]; simpl;
                 [intros _; set_solver|intros Hc; unfold compose; by rewrite fends_rename]|]
              | unshelve epose proof (IH (up (up γ)) D _) as H';
                [eapply allfv_mono; [|exact H]; intros [|[|x]]; simpl;
                 [intros _; set_solver|intros _; set_solver
                 |intros Hc; unfold compose; by rewrite !fends_rename]|] ];
        clear H
    end.
  all: set_solver.
Qed.

Lemma fends_subst1_sub v e : fends (subst1 v e) ⊆ fends e ∪ fends v.
Proof. apply fends_subst. apply allfv_forall. intros [|x]; simpl; set_solver. Qed.

Lemma fends_subst2_sub u v e :
  fends (subst2 u v e) ⊆ fends e ∪ (fends u ∪ fends v).
Proof. apply fends_subst. apply allfv_forall. intros [|[|x]]; simpl; set_solver. Qed.

Lemma fchans_rename e r : fchans (rename r e) = fchans e.
Proof. unfold fchans. by rewrite fends_rename. Qed.

Lemma elem_of_fchans c e : c ∈ fchans e ↔ ∃ o, o ∈ fends e ∧ ech o = c.
Proof. unfold fchans. rewrite elem_of_map. naive_solver. Qed.

Lemma fchans_subst1_sub v e : fchans (subst1 v e) ⊆ fchans e ∪ fchans v.
Proof.
  intros c. rewrite elem_of_union, !elem_of_fchans. intros (o & Ho & <-).
  apply fends_subst1_sub in Ho. set_solver.
Qed.

Lemma fchans_subst2_sub u v e :
  fchans (subst2 u v e) ⊆ fchans e ∪ (fchans u ∪ fchans v).
Proof.
  intros c. rewrite !elem_of_union, !elem_of_fchans. intros (o & Ho & <-).
  apply fends_subst2_sub in Ho. set_solver.
Qed.

(** ** The one channel renaming

    [emap g] renames every end by g. A renaming of channel names
    ([cmap h], which keeps the sign of each end), the substitution of a
    link ([csub]) and the erasure of all names are instances. *)

Fixpoint emap (g : cend → cend) (e : expr) : expr :=
  match e with
  | Var x => Var x
  | EUnit => EUnit
  | Chan o => Chan (g o)
  | Lam e => Lam (emap g e)
  | App e1 e2 => App (emap g e1) (emap g e2)
  | Pair e1 e2 => Pair (emap g e1) (emap g e2)
  | LetU e1 e2 => LetU (emap g e1) (emap g e2)
  | LetP e1 e2 => LetP (emap g e1) (emap g e2)
  | Inj1 e => Inj1 (emap g e)
  | Inj2 e => Inj2 (emap g e)
  | Case e e1 e2 => Case (emap g e) (emap g e1) (emap g e2)
  | EBox e => EBox (emap g e)
  | ENew ℓ => ENew ℓ
  | Op k e => Op k (emap g e)
  end.

(** A renaming of channel names, applied to ends. *)
Definition cmap (h : chan → chan) (o : cend) : cend :=
  match o with EPos c => EPos (h c) | ENeg c => ENeg (h c) end.

Lemma ech_cmap h o : ech (cmap h o) = h (ech o).
Proof. by destruct o. Qed.
Lemma cmap_edual h o : cmap h (edual o) = edual (cmap h o).
Proof. by destruct o. Qed.
Lemma cmap_id o : cmap id o = o.
Proof. by destruct o. Qed.

(** The one substitution, of a link of o1 and o2 that removes the
    channel of o1 (P-Act-Link). The holder of ō1 now talks to the holder
    of ō2, so ō1 becomes o2, and o1 becomes ō2. Every other end stays. *)
Definition csub (o1 o2 : cend) (o : cend) : cend :=
  if decide (o = edual o1) then o2
  else if decide (o = o1) then edual o2 else o.

Lemma csub_ne o1 o2 o : ech o ≠ ech o1 → csub o1 o2 o = o.
Proof.
  intros H. unfold csub. case_decide as H1; [subst; by rewrite ech_edual in H|].
  case_decide; [subst; done|done].
Qed.

Lemma emap_ext g h e : (∀ o, g o = h o) → emap g e = emap h e.
Proof. intros H. induction e; simpl; f_equal; auto. Qed.

Lemma emap_emap g h e : emap g (emap h e) = emap (g ∘ h) e.
Proof. induction e; simpl; f_equal; auto. Qed.

Lemma emap_id e : emap id e = e.
Proof. induction e; simpl; f_equal; auto. Qed.

Lemma is_val_emap g e : is_val (emap g e) = is_val e.
Proof. induction e; simpl; try done; by rewrite ?IHe1, ?IHe2, ?IHe. Qed.

Lemma emap_rename g r e : emap g (rename r e) = rename r (emap g e).
Proof. revert r. induction e; intros r; simpl; f_equal; auto. Qed.

Lemma emap_up g σ x : emap g (up σ x) = up (λ y, emap g (σ y)) x.
Proof. destruct x; simpl; [done|]. unfold compose. apply emap_rename. Qed.

Lemma emap_subst g σ e : emap g (subst σ e) = subst (λ x, emap g (σ x)) (emap g e).
Proof.
  revert σ. induction e; intros σ; simpl; f_equal; auto.
  all: rewrite ?IHe, ?IHe1, ?IHe2, ?IHe3.
  all: apply subst_ext; intros x;
    first [apply emap_up
          |etrans; [apply emap_up|]; apply up_ext; intros ?; apply emap_up].
Qed.

Lemma emap_subst1 g v e : emap g (subst1 v e) = subst1 (emap g v) (emap g e).
Proof. unfold subst1. rewrite emap_subst. apply subst_ext. by intros [|x]. Qed.

Lemma emap_subst2 g u v e : emap g (subst2 u v e) = subst2 (emap g u) (emap g v) (emap g e).
Proof. unfold subst2. rewrite emap_subst. apply subst_ext. by intros [|[|x]]. Qed.

Lemma fends_emap g e : fends (emap g e) = set_map g (fends e).
Proof.
  induction e; simpl; rewrite ?set_map_union_L, ?set_map_empty, ?set_map_singleton_L;
    try congruence.
Qed.

(** A renaming that fixes every end of a term fixes the term. *)
Lemma emap_id_on g e : (∀ o, o ∈ fends e → g o = o) → emap g e = e.
Proof. induction e; simpl; intros H; f_equal; auto; set_solver. Qed.

Lemma emap_csub_fresh o1 o2 e : ech o1 ∉ fchans e → emap (csub o1 o2) e = e.
Proof.
  intros H. apply emap_id_on. intros o Ho. apply csub_ne. intros Heq.
  apply H. apply elem_of_fchans. eauto.
Qed.

Lemma fchans_emap_csub o1 o2 e :
  fchans (emap (csub o1 o2) e) ⊆ (fchans e ∖ {[ech o1]}) ∪ {[ech o2]}.
Proof.
  intros c. rewrite elem_of_fchans, fends_emap. intros (o' & Ho' & <-).
  apply elem_of_map in Ho' as (o & -> & Ho). unfold csub.
  case_decide; [set_solver|]. case_decide; [rewrite ech_edual; set_solver|].
  destruct (decide (ech o = ech o1)) as [Heq|Hne].
  - apply ech_eq in Heq as [->| ->]; [done|]. by rewrite edual_edual in *.
  - apply elem_of_union_l, elem_of_difference. split; [|set_solver].
    apply elem_of_fchans. eauto.
Qed.

(** ** Processes: soups of threads over a set of restricted channels *)

Definition proc : Type := gset chan * gmultiset expr.

(** Channels occurring free in some thread. *)
Definition echans (E : gmultiset expr) : gset chan :=
  ⋃ (fchans <$> elements E).

Lemma elem_of_echans x E : x ∈ echans E ↔ ∃ e, e ∈ E ∧ x ∈ fchans e.
Proof.
  unfold echans. rewrite elem_of_union_list. split.
  - intros (X & HX & Hx). apply list_elem_of_fmap in HX as (e & -> & He).
    exists e. split; [|done]. by apply gmultiset_elem_of_elements.
  - intros (e & He & Hx). exists (fchans e). split; [|done].
    apply list_elem_of_fmap. exists e. split; [done|].
    by apply gmultiset_elem_of_elements.
Qed.

Lemma echans_disj_union E1 E2 : echans (E1 ⊎ E2) = echans E1 ∪ echans E2.
Proof.
  apply set_eq. intros x. rewrite elem_of_union, !elem_of_echans.
  setoid_rewrite gmultiset_elem_of_disj_union. naive_solver.
Qed.

Lemma echans_empty : echans ∅ = ∅.
Proof. unfold echans. by rewrite gmultiset_elements_empty. Qed.

Lemma echans_singleton e : echans {[+ e +]} = fchans e.
Proof. unfold echans. rewrite gmultiset_elements_singleton. simpl. set_solver. Qed.

(** The renaming of every thread. *)
Definition emapE (g : cend → cend) (E : gmultiset expr) : gmultiset expr :=
  gmultiset_map (emap g) E.

Lemma emapE_disj_union g E1 E2 : emapE g (E1 ⊎ E2) = emapE g E1 ⊎ emapE g E2.
Proof. apply gmultiset_map_disj_union. Qed.

Lemma emapE_singleton g e : emapE g {[+ e +]} = {[+ emap g e +]}.
Proof. apply gmultiset_map_singleton. Qed.

Lemma emapE_csub_fresh o1 o2 E : ech o1 ∉ echans E → emapE (csub o1 o2) E = E.
Proof.
  induction E as [|e E IH] using gmultiset_ind; intros Hc.
  - unfold emapE. by rewrite gmultiset_map_empty.
  - rewrite echans_disj_union, echans_singleton in Hc.
    rewrite emapE_disj_union, emapE_singleton, emap_csub_fresh by set_solver.
    rewrite IH by set_solver. done.
Qed.

Lemma echans_emapE_csub o1 o2 E :
  echans (emapE (csub o1 o2) E) ⊆ (echans E ∖ {[ech o1]}) ∪ {[ech o2]}.
Proof.
  induction E as [|e E IH] using gmultiset_ind.
  - unfold emapE. rewrite gmultiset_map_empty, echans_empty. set_solver.
  - rewrite emapE_disj_union, emapE_singleton, !echans_disj_union, !echans_singleton.
    pose proof (fchans_emap_csub o1 o2 e). set_solver.
Qed.
