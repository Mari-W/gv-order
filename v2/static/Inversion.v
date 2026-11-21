(** * Inversion of the typing judgment (next run, stage 4)

    The rules E-Sub, E-Pack and E-Open apply to every term, so a
    derivation of a term of a given form ends with the rule of that form
    under a stack of them. E-Sub and E-Pack change only the type, and the
    lemmas below forget the type of the conclusion. E-Open changes the
    context: it instantiates the point variables by [pshift m], opens an
    existential entry of Δ and adds its constraint to Γ. [opened] records
    a sequence of such steps, and each lemma states the premises of the
    rule of its form in a context [opened] from the given one.

    - [inv_close], [inv_case], [inv_letu], [inv_letp], [inv_pair] and
      [inv_let] for E-Close, E-Case, E-LetU, E-LetP, E-Pair and the
      derived E-Let.
    - [ptyped_one] and [ptyped_two]: a typed process of one thread ends
      with P-Term, a typed process of two threads ends with P-Connect
      over one thread on each side. *)

From GV Require Export static.Weakening.

(** ** Contexts reached by E-Open *)

Inductive opened : tenv → hctx → lenv → sfuture → tenv → hctx → lenv → sfuture → Prop :=
  | op_refl Θ Γ Δ F : opened Θ Γ Δ F Θ Γ Δ F
  | op_step Θ Γ Δ F Θ' Γ' Δ' F' i lb m C T :
      Δ !! i = Some (Some (TEx lb m C T)) → ¬ unlimited T →
      opened (tenv_pinst (pshift m) Θ) (hc_open m C Γ)
        (<[i := Some T]> (lenv_pinst (pshift m) Δ)) (sf_pinst (pshift m) F) Θ' Γ' Δ' F' →
      opened Θ Γ Δ F Θ' Γ' Δ' F'.

(** ** Term forms *)

Section inversion.
  Context (W : world) (N : fuel).

  Lemma inv_close Θ Γ Δ F e T c t :
    typed W N Θ Γ Δ F (EClose e) T c t →
    ∃ Θ' Γ' Δ' F' S0 x a c0 t0, opened Θ Γ Δ F Θ' Γ' Δ' F' ∧
      unfoldS S0 = SEnd ∧ ub_below_s W Γ' (Some x) F' ∧
      typed W N Θ' Γ' Δ' F' e (TSess S0 x a) c0 t0.
  Proof.
    remember (EClose e) as e0 eqn:He. induction 1; try discriminate.
    - injection He as ->. eexists _, _, _, _, _, _, _, _, _. split_and!; [constructor|done..].
    - by apply IHtyped.
    - by apply IHtyped.
    - destruct (IHtyped He) as (Θ' & Γ' & Δ' & F' & S0 & x & a & c0 & t0 & Ho & Hrest).
      exists Θ', Γ', Δ', F', S0, x, a, c0, t0. split; [|done]. by eapply op_step.
  Qed.

  Lemma inv_case Θ Γ Δ F e e1 e2 T c t :
    typed W N Θ Γ Δ F (Case e e1 e2) T c t →
    ∃ Θ' Γ' Δ' F' Θ1 Θ2 Θ2' Δ1 Δ2 Δ2' T1 T2 T' c0 t0 c1 t1 c2 t2,
      opened Θ Γ Δ F Θ' Γ' Δ' F' ∧ tsplit Θ' Θ1 Θ2 ∧ lenv_split Δ' Δ1 Δ2 ∧
      typed W N Θ1 Γ' Δ1 (sf_unionb F' (tenv_heads Θ2 ∪ lenv_heads Δ2) (lenv_bot Δ2)) e
        (TSum T1 T2) c0 t0 ∧
      thage c0 Θ2 Θ2' ∧ lage c0 Δ2 Δ2' ∧
      typed W N Θ2' Γ' (Some T1 :: Δ2') F' e1 T' c1 t1 ∧
      typed W N Θ2' Γ' (Some T2 :: Δ2') F' e2 T' c2 t2.
  Proof.
    remember (Case e e1 e2) as e0 eqn:He. induction 1; try discriminate.
    - injection He as -> -> ->.
      do 19 eexists. split_and!; [constructor|done..].
    - by apply IHtyped.
    - by apply IHtyped.
    - destruct (IHtyped He) as (Θ' & Γ' & Δ' & F' & Hrest).
      exists Θ', Γ', Δ', F'. destruct Hrest as (Θ1 & Θ2 & Θ2' & Δ1 & Δ2 & Δ2' & T1 & T2 & T' & c0 & t0
        & c1 & t1 & c2 & t2 & Ho & Hr).
      exists Θ1, Θ2, Θ2', Δ1, Δ2, Δ2', T1, T2, T', c0, t0, c1, t1, c2, t2.
      split; [|done]. by eapply op_step.
  Qed.

  Lemma inv_letu Θ Γ Δ F e1 e2 T c t :
    typed W N Θ Γ Δ F (LetU e1 e2) T c t →
    ∃ Θ' Γ' Δ' F' Θ1 Θ2 Θ2' Δ1 Δ2 Δ2' T' c1 t1 c2 t2,
      opened Θ Γ Δ F Θ' Γ' Δ' F' ∧ tsplit Θ' Θ1 Θ2 ∧ lenv_split Δ' Δ1 Δ2 ∧
      typed W N Θ1 Γ' Δ1 (sf_unionb F' (tenv_heads Θ2 ∪ lenv_heads Δ2) (lenv_bot Δ2)) e1 TUnit c1 t1 ∧
      thage c1 Θ2 Θ2' ∧ lage c1 Δ2 Δ2' ∧
      typed W N Θ2' Γ' Δ2' F' e2 T' c2 t2.
  Proof.
    remember (LetU e1 e2) as e0 eqn:He. induction 1; try discriminate.
    - injection He as -> ->. do 15 eexists. split_and!; [constructor|done..].
    - by apply IHtyped.
    - by apply IHtyped.
    - destruct (IHtyped He) as (Θ' & Γ' & Δ' & F' & Θ1 & Θ2 & Θ2' & Δ1 & Δ2 & Δ2' & T' & c1 & t1
        & c2 & t2 & Ho & Hr).
      exists Θ', Γ', Δ', F', Θ1, Θ2, Θ2', Δ1, Δ2, Δ2', T', c1, t1, c2, t2.
      split; [|done]. by eapply op_step.
  Qed.

  Lemma inv_letp Θ Γ Δ F e1 e2 T c t :
    typed W N Θ Γ Δ F (LetP e1 e2) T c t →
    ∃ Θ' Γ' Δ' F' Θ1 Θ2 Θ2' Δ1 Δ2 Δ2' T1 T2 T' c1 t1 c2 t2,
      opened Θ Γ Δ F Θ' Γ' Δ' F' ∧ tsplit Θ' Θ1 Θ2 ∧ lenv_split Δ' Δ1 Δ2 ∧
      typed W N Θ1 Γ' Δ1 (sf_unionb F' (tenv_heads Θ2 ∪ lenv_heads Δ2) (lenv_bot Δ2)) e1
        (TProd T1 T2) c1 t1 ∧
      thage c1 Θ2 Θ2' ∧ lage c1 Δ2 Δ2' ∧
      typed W N Θ2' Γ' (Some T2 :: Some T1 :: Δ2') F' e2 T' c2 t2.
  Proof.
    remember (LetP e1 e2) as e0 eqn:He. induction 1; try discriminate.
    - injection He as -> ->. do 17 eexists. split_and!; [constructor|done..].
    - by apply IHtyped.
    - by apply IHtyped.
    - destruct (IHtyped He) as (Θ' & Γ' & Δ' & F' & Hrest).
      exists Θ', Γ', Δ', F'. destruct Hrest as (Θ1 & Θ2 & Θ2' & Δ1 & Δ2 & Δ2' & T1 & T2 & T' & c1 & t1
        & c2 & t2 & Ho & Hr).
      exists Θ1, Θ2, Θ2', Δ1, Δ2, Δ2', T1, T2, T', c1, t1, c2, t2.
      split; [|done]. by eapply op_step.
  Qed.

  Lemma inv_pair Θ Γ Δ F e1 e2 T c t :
    typed W N Θ Γ Δ F (Pair e1 e2) T c t →
    ∃ Θ' Γ' Δ' F' Θ1 Θ2 Θ2' Δ1 Δ2 Δ2' T1 T2 c1 t1 c2 t2,
      opened Θ Γ Δ F Θ' Γ' Δ' F' ∧ tsplit Θ' Θ1 Θ2 ∧ lenv_split Δ' Δ1 Δ2 ∧
      typed W N Θ1 Γ' Δ1 (sf_unionb F' (tenv_heads Θ2 ∪ lenv_heads Δ2) (lenv_bot Δ2)) e1 T1 c1 t1 ∧
      thage c1 Θ2 Θ2' ∧ lage c1 Δ2 Δ2' ∧
      typed W N Θ2' Γ' Δ2' (sf_unionb F' (heads T1) (hbot T1)) e2 T2 c2 t2.
  Proof.
    remember (Pair e1 e2) as e0 eqn:He. induction 1; try discriminate.
    - injection He as -> ->. do 16 eexists. split_and!; [constructor|done..].
    - by apply IHtyped.
    - by apply IHtyped.
    - destruct (IHtyped He) as (Θ' & Γ' & Δ' & F' & Hrest).
      exists Θ', Γ', Δ', F'. destruct Hrest as (Θ1 & Θ2 & Θ2' & Δ1 & Δ2 & Δ2' & T1 & T2 & c1 & t1
        & c2 & t2 & Ho & Hr).
      exists Θ1, Θ2, Θ2', Δ1, Δ2, Δ2', T1, T2, c1, t1, c2, t2.
      split; [|done]. by eapply op_step.
  Qed.

  (** E-Let is the derived form [ELet] of lang/Syntax.v: a pair with the
      unit, unpacked, and the unit eliminated. Its first operand is typed
      in a context opened twice from the given one. *)
  Lemma inv_let Θ Γ Δ F e1 e2 T c t :
    typed W N Θ Γ Δ F (ELet e1 e2) T c t →
    ∃ Θ' Γ' Δ' F' Θ1 Θ2 Θ2' Δ1 Δ2 Δ2' T1 T2 T' c1 c2 t2,
      opened Θ Γ Δ F Θ' Γ' Δ' F' ∧ tsplit Θ' Θ1 Θ2 ∧ lenv_split Δ' Δ1 Δ2 ∧
      (∃ Θ'' Γ'' Δ'' F'' Θ3 Θ4 Θ4' Δ3 Δ4 Δ4' T3 T4 c3 t3 c4 t4,
         opened Θ1 Γ' Δ1 (sf_unionb F' (tenv_heads Θ2 ∪ lenv_heads Δ2) (lenv_bot Δ2))
           Θ'' Γ'' Δ'' F'' ∧ tsplit Θ'' Θ3 Θ4 ∧ lenv_split Δ'' Δ3 Δ4 ∧
         typed W N Θ3 Γ'' Δ3 (sf_unionb F'' (tenv_heads Θ4 ∪ lenv_heads Δ4) (lenv_bot Δ4)) e1 T3 c3 t3 ∧
         thage c3 Θ4 Θ4' ∧ lage c3 Δ4 Δ4' ∧
         typed W N Θ4' Γ'' Δ4' (sf_unionb F'' (heads T3) (hbot T3)) EUnit T4 c4 t4) ∧
      thage c1 Θ2 Θ2' ∧ lage c1 Δ2 Δ2' ∧
      typed W N Θ2' Γ' (Some T2 :: Some T1 :: Δ2') F' (LetU (Var 0) (rename S e2)) T' c2 t2.
  Proof.
    unfold ELet. intros H. apply inv_letp in H as (Θ' & Γ' & Δ' & F' & Θ1 & Θ2 & Θ2' & Δ1 & Δ2 & Δ2'
      & T1 & T2 & T' & c1 & t1 & c2 & t2 & Ho & Hs & Hl & H1 & Ha & Hla & H2).
    exists Θ', Γ', Δ', F', Θ1, Θ2, Θ2', Δ1, Δ2, Δ2', T1, T2, T', c1, c2, t2.
    split_and!; try done. by apply inv_pair in H1.
  Qed.
End inversion.

(** ** Processes *)

Lemma gms_size_1 (X : gmultiset expr) : size X = 1 → ∃ x, X = {[+ x +]}.
Proof.
  intros H. destruct (gmultiset_size_pos_elem_of X) as [x Hx]; [lia|]. exists x.
  rewrite (gmultiset_disj_union_difference' x X Hx) in H |- *.
  rewrite gmultiset_size_disj_union, gmultiset_size_singleton in H.
  assert (X ∖ {[+ x +]} = ∅) as -> by (apply gmultiset_size_empty_iff; lia).
  by rewrite gmultiset_disj_union_right_id.
Qed.

Lemma ptyped_nonempty N W Σ p T : ptyped N W Σ p T → p.2 ≠ ∅.
Proof. induction 1; simpl; multiset_solver. Qed.

(** A process of one thread ends with P-Term. *)
Lemma ptyped_one N W Σ C0 t T :
  ptyped N W Σ (C0, {[+ t +]}) T →
  ∃ ΘB c ϑ, tfree T ∧ (∀ o, o ∈ dom ΘB ↔ ech o ∈ C0) ∧ chans_of Σ ## C0 ∧ pfree Σ ∧
    (∀ ch, ch ∈ C0 → ∃ S x, ΘB !! (ch⁺)%cend = Some (TE S x N) ∧ ΘB !! (ch⁻)%cend = Some (TE (dual S) x‾ N)) ∧
    typed W N (tenv_of N Σ ∪ ΘB) hc_empty [] (∅, None) t T c ϑ ∧
    (N = None ∨ tfin ϑ) ∧ strict W.
Proof.
  intros H. remember (C0, {[+ t +]}) as p eqn:Hp. destruct H as [W' Σ' ΘB C0' t' T' c ϑ Hf HB HC Hpf HBs Ht Hn Hs|
    W1 W2 Σ1 Σ2 ΣC C1 C2 E1 E2 T' H1 H2].
  - pose proof (f_equal fst Hp) as H1. pose proof (f_equal snd Hp) as Ht'. simpl in H1, Ht'. subst C0'.
    apply (inj (singletonMS (B := gmultiset expr))) in Ht' as ->.
    exists ΘB, c, ϑ. split_and!; done.
  - exfalso. pose proof (f_equal snd Hp) as HE. simpl in HE.
    apply ptyped_nonempty in H1, H2. simpl in *.
    assert (size (E1 ⊎ E2) = 1) as Hsz by (by rewrite HE, gmultiset_size_singleton).
    rewrite gmultiset_size_disj_union in Hsz.
    apply gmultiset_size_non_empty_iff in H1. apply gmultiset_size_non_empty_iff in H2. lia.
Qed.

(** A process of two threads ends with P-Connect over one thread on each
    side. *)
Lemma ptyped_two N W Σ C t1 t2 T :
  ptyped N W Σ (C, ({[+ t1 +]} ⊎ {[+ t2 +]})) T →
  ∃ W1 W2 Σ1 Σ2 ΣC C1 C2 u1 u2,
    W = W1 ⊔ W2 ∧ Σ = Σ1 ∪ Σ2 ∧ C = C1 ∪ C2 ∪ chans_of ΣC ∧
    (({[+ u1 +]} ⊎ {[+ u2 +]}) : gmultiset expr) = ({[+ t1 +]} ⊎ {[+ t2 +]}) ∧
    ptyped N W1 (Σ1 ∪ ΣC) (C1, {[+ u1 +]}) T ∧
    ptyped N W2 (Σ2 ∪ senv_dual ΣC) (C2, {[+ u2 +]}) TUnit ∧
    strict (wrestrict W1 (wshared W1 W2) ⊔ wrestrict W2 (wshared W1 W2)).
Proof.
  intros H. remember (C, ({[+ t1 +]} ⊎ {[+ t2 +]})) as p eqn:Hp. destruct H as [W' Σ' ΘB C0' t' T' c ϑ|
    W1 W2 Σ1 Σ2 ΣC C1 C2 E1 E2 T' H1 H2 _ _ _ _ _ _ _ _ _ _ HS].
  - exfalso. pose proof (f_equal snd Hp) as HE. simpl in HE.
    assert (size (({[+ t1 +]} ⊎ {[+ t2 +]}) : gmultiset expr) = 1) as Hsz by (by rewrite <-HE, gmultiset_size_singleton).
    rewrite gmultiset_size_disj_union, !gmultiset_size_singleton in Hsz. lia.
  - pose proof (f_equal fst Hp) as HC0. pose proof (f_equal snd Hp) as HE. simpl in HC0, HE. subst C.
    pose proof (ptyped_nonempty _ _ _ _ _ H1) as N1. pose proof (ptyped_nonempty _ _ _ _ _ H2) as N2.
    simpl in N1, N2.
    assert (size E1 = 1 ∧ size E2 = 1) as [S1 S2].
    { assert (size (E1 ⊎ E2) = 2) as Hsz by (by rewrite HE, gmultiset_size_disj_union, !gmultiset_size_singleton).
      rewrite gmultiset_size_disj_union in Hsz.
      apply gmultiset_size_non_empty_iff in N1. apply gmultiset_size_non_empty_iff in N2. lia. }
    apply gms_size_1 in S1 as [u1 ->]. apply gms_size_1 in S2 as [u2 ->].
    exists W1, W2, Σ1, Σ2, ΣC, C1, C2, u1, u2. split_and!; done.
Qed.
