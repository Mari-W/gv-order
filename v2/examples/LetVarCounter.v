(** * e and let x = e in x differ (fx-open, 2026-11-22)

    f : □(∃ι. Unit), the box of an existential, is unlimited, and
    force f types at ∃ι. Unit. The let puts that value into Δ, where
    E-Open opens it, so let x = force f in x types at Unit
    ([let_force_typed]). The term force f types only at existentials
    ([force_types_ex]): E-Force reads the result of the box, E-Sub keeps
    an existential an existential, and E-Pack makes one. No rule opens
    the result of a term that is no variable. So e : T does not follow
    from let x = e in x : T ([let_var_counter]), although Δ holds no
    existential and every context is contractive, the setting of
    [let_elim] (static/LetVar.v). There the type T1 of the binder is
    the existential ∃ι. Unit. *)

From GV Require Export static.LetVar examples.Tools.

Definition Cnil : bcs := BCs [] (λ _, False).
Definition Ucx : ty := TEx LBot 1 Cnil TUnit.
Definition Bcx : ty := TBox 0 0 Cnil None (Some 0) Ucx.
Definition Δcx : lenv := [Some Bcx].
Definition ecx : expr := EForce (Var 0).

Lemma hold_cnil W Γ xs : hold_at W Γ Cnil xs.
Proof. apply hold_at_nil. by intros f []. Qed.

Lemma force_typed N : typed sw_empty N ∅ hc_empty Δcx (∅, None) ecx Ucx (Some 0).
Proof.
  assert (Ucx = sinst_ty (slist []) (ty_inst [] Ucx)) as E by reflexivity.
  unfold ecx. rewrite E. change (Some 0) with (fadd (Some 0) (Some 0)).
  eapply (e_force _ _ _ _ _ _ _ 0 0 Cnil None (Some 0) Ucx [] []); [done|apply hold_cnil|done| |done|].
  - split; [split; constructor|]. intros _. constructor.
  - apply e_var. split; [done|]. intros [|y] σ Hne Hy; [done|]. destruct y; discriminate.
Qed.

Theorem let_force_typed N : typed sw_empty N ∅ hc_empty Δcx (∅, None) (ELet ecx (Var 0)) TUnit (Some 0).
Proof.
  change (Some 0) with (fadd (Some 0) (Some 0)).
  eapply (e_let _ _ ∅ ∅ ∅ ∅ _ Δcx Δcx [None] [None]).
  - split; [apply map_disjoint_empty_r|by rewrite map_union_empty].
  - repeat constructor.
  - change (tenv_heads ∅ ∪ lenv_heads [None]) with (tenv_heads ∅ ∪ ∅).
    rewrite tenv_heads_empty', (right_id_L ∅ (∪)).
    change (lenv_bot [None]) with false. rewrite sf_unionb_nil. apply force_typed.
  - apply thage_nil'.
  - repeat constructor.
  - eapply (e_open _ _ _ _ _ _ _ 0 LBot 1 Cnil TUnit TUnit); [done|by intros []| |].
    + intros z y (_ & _ & [[Hf _]|(v & u & [Hf _] & _)]); destruct Hf.
    + apply e_var. split; [done|]. intros [|y] σ Hne Hy; [done|]. destruct y as [|y]; [discriminate|].
      destruct y; discriminate.
Qed.

(** *** force f types only at existentials *)

Definition box_or_ex (T : ty) : Prop :=
  (∃ c U, T = TBox 0 0 Cnil None c U ∧ is_ex U) ∨ is_ex T.

Lemma eqT_is_ex ρ T U : eqT ρ T U → is_ex T → is_ex U.
Proof. destruct T, U; simpl; tauto. Qed.

Lemma tsub_is_ex W Γ T U : tsub W Γ T U → is_ex T → is_ex U.
Proof. destruct 1; simpl; tauto. Qed.

Lemma var_box_types W N Θ Γ F T c :
  typed W N Θ Γ Δcx F (Var 0) T c → box_or_ex T.
Proof.
  remember (Var 0) as e0 eqn:He. remember Δcx as Δ0 eqn:HΔ. induction 1; try discriminate.
  - subst Δ. injection He as ->. destruct H as [Hx _]. simpl in Hx. injection Hx as <-.
    left. exists (Some 0), Ucx. done.
  - destruct (IHtyped He HΔ) as [(c0 & U & -> & HU)|Hx].
    + inversion H0 as [| | | |? ? ? ? ? ? ? U2 c2 Hc2 Heq| |]; subst. left. eexists _, _. split; [done|].
      eapply eqT_is_ex; [exact Heq|exact HU].
    + right. by eapply tsub_is_ex.
  - by right.
  - exfalso. subst Δ. destruct i as [|[|i]]; simpl in H; discriminate.
Qed.

Lemma is_ex_inst σ xs U : is_ex U → is_ex (sinst_ty σ (ty_inst xs U)).
Proof. destruct U; simpl; tauto. Qed.

Theorem force_types_ex W N Θ Γ F T c : typed W N Θ Γ Δcx F ecx T c → is_ex T.
Proof.
  remember ecx as e0 eqn:He. remember Δcx as Δ0 eqn:HΔ. induction 1; try discriminate.
  - injection He as ->. subst Δ. destruct (var_box_types _ _ _ _ _ _ _ H4) as [(c1 & U1 & E & HU)|Hx];
      [|done]. injection E as -> -> -> -> -> ->. by apply is_ex_inst.
  - eapply tsub_is_ex; [exact H0|by apply IHtyped].
  - done.
  - exfalso. subst Δ. destruct i as [|[|i]]; simpl in H; discriminate.
Qed.

(** The converse of [let_intro] fails. *)
Theorem let_var_counter N :
  typed sw_empty N ∅ hc_empty Δcx (∅, None) (ELet ecx (Var 0)) TUnit (Some 0) ∧
  ∀ Θ c, ¬ typed sw_empty N Θ hc_empty Δcx (∅, None) ecx TUnit c.
Proof.
  split; [apply let_force_typed|]. intros Θ c H. exact (force_types_ex _ _ _ _ _ _ _ H).
Qed.

(** The setting of [let_elim]: Δ holds no existential and is contractive. *)
Lemma Δcx_noex : lenv_noex Δcx.
Proof. intros [|i] T Hi; simpl in Hi; [injection Hi as <-; simpl; tauto|destruct i; discriminate]. Qed.

Lemma Δcx_contr : lenv_contr Δcx.
Proof. intros [|i] T Hi; simpl in Hi; [injection Hi as <-; done|destruct i; discriminate]. Qed.
