(** * The semantic term judgment (stage S4, Appendix A.2)

      Θ ; Δ ⊨^F _ W t : T    [sem_typed κ_DF W Θ Δ F t T]    deadlock freedom
      Θ ; Δ ⊫^F _ W t : T    [sem_typed κ_L W Θ Δ F t T]     liveness

    Θ is a typing environment ([tenv]) and Δ a context of types,
    as in the static judgment. The relation reads neither credits nor
    annotations, so Θ enters through [tenv_erase] and Δ through the types
    of its entries.

    A grounding substitution γ for Δ at level n ([Grel]) maps every
    variable of Δ to a value in V at its type and splits an environment
    among them. [sem_typed_at] is the judgment at a future that is a set
    of points, the relation's future: in every W' ⊒ W, at every level,
    for every grounding with an environment disjoint from Θ, the
    instance of t is in E at the union of the environments.

    The static future F of S2 is a set of points with a future variable
    or the ⊥ flag. [sem_typed] interprets it ([sf_den]): the future
    variable φ stands for an arbitrary set ρ φ, and the ⊥ flag for an
    arbitrary set B. A term typed under the ⊥ flag may not block (its
    context holds ends whose points are hidden), so it must be ready
    under every future, and a future variable without hypotheses is
    unconstrained. With Γ = ∅, as in the fundamental theorem of A.3,
    both readings are exact. A body under a future hypothesis u ≺ φ is
    stated at the set form, over every future above u, as the old
    semantic rules did (theories/rules/SemanticRules.v). *)

From GV Require Export relation.Adequacy compat.Blind compat.Bind.

(** ** Grounding substitutions *)

Fixpoint Grel (κ : ctable) (n : nat) (W : world) (Θ : senv) (Δ : lenv) (γ : nat → expr) : Prop :=
  match Δ with
  | [] => Θ = ∅
  | None :: Δ' => Grel κ n W Θ Δ' (λ x, γ (S x))
  | Some T :: Δ' =>
      ∃ Θ1 Θ2, Θ1 ##ₘ Θ2 ∧ Θ = Θ1 ∪ Θ2 ∧
        Vrel κ n W Θ1 T (γ 0) ∧ Grel κ n W Θ2 Δ' (λ x, γ (S x))
  end.

(** ** The judgment at a set of points *)

Definition sem_typed_at (κ : ctable) (W : world) (Θ : tenv) (Δ : lenv) (F : gset point)
    (t : expr) (T : ty) : Prop :=
  ∀ n W' Θ' γ, W ⊑ W' → tenv_erase Θ ##ₘ Θ' → Grel κ n W' Θ' Δ γ →
    subst γ t ∈ E[κ]^W' _ n⟦tenv_erase Θ ∪ Θ' ⊢ T⟧^F.

(** ** Static futures *)

(** The points a static future denotes, with ρ φ for the future
    variable φ and B for the ⊥ flag. *)
Definition sf_den (ρ : nat → gset point) (B : gset point) (F : sfuture) : gset point :=
  F.1 ∪ from_option ρ ∅ (fs_var F.2) ∪ (if fs_bot F.2 then B else ∅).

Definition sem_typed (κ : ctable) (W : world) (Θ : tenv) (Δ : lenv) (F : sfuture)
    (t : expr) (T : ty) : Prop :=
  ∀ ρ B, sem_typed_at κ W Θ Δ (sf_den ρ B F) t T.

Notation "Θ ; Δ ⊨^ F '_' W t : T" := (sem_typed κ_DF W Θ Δ F t T)
  (at level 74, Δ at level 60, F at level 0, W at level 0, t at level 60, T at level 60,
   format "Θ  ;  Δ  ⊨^ F  '_'  W  t  :  T").
Notation "Θ ; Δ ⊫^ F '_' W t : T" := (sem_typed κ_L W Θ Δ F t T)
  (at level 74, Δ at level 60, F at level 0, W at level 0, t at level 60, T at level 60,
   format "Θ  ;  Δ  ⊫^ F  '_'  W  t  :  T").

Lemma sf_den_unionb ρ B F X b :
  sf_den ρ B (sf_unionb F X b) = sf_den ρ B F ∪ X ∪ (if b then B else ∅).
Proof.
  destruct F as [P o]. unfold sf_den, sf_unionb. destruct b; simpl; [|set_solver].
  destruct o as [[φ|o]|]; simpl; set_solver.
Qed.

(** ** Facts about groundings *)

Section grel.
  Context (κ : ctable).

  Lemma Grel_mono n W W' Θ Δ γ : W ⊑ W' → Grel κ n W Θ Δ γ → Grel κ n W' Θ Δ γ.
  Proof.
    intros HW. revert Θ γ. induction Δ as [|[T|] Δ IH]; intros Θ γ; simpl; [done| |auto].
    intros (Θ1 & Θ2 & Hd & -> & HV & HG). exists Θ1, Θ2. split_and!; try done; [|auto].
    by eapply Vrel_mono.
  Qed.

  Lemma Grel_down n m W Θ Δ γ : m ≤ n → Grel κ n W Θ Δ γ → Grel κ m W Θ Δ γ.
  Proof.
    intros Hm. revert Θ γ. induction Δ as [|[T|] Δ IH]; intros Θ γ; simpl; [done| |auto].
    intros (Θ1 & Θ2 & Hd & -> & HV & HG). exists Θ1, Θ2. split_and!; try done; [|auto].
    by eapply Vrel_down.
  Qed.

  (** A value of a box holds no end. *)
  Lemma Vrel_unl_empty n W Θ U v : unlimited U → Vrel κ n W Θ U v → Θ = ∅.
  Proof. destruct U; try done. intros _ H. by apply Vrel_box_iff in H as [-> _]. Qed.

End grel.

(** ** Facts about the judgment *)

Section sem.
  Context (κ : ctable).

End sem.
