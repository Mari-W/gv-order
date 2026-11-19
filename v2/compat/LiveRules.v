(** * The semantic rules, for every cost table (stage S5)

    The semantic judgment with marks L, [sem_later κ W Θ Δ L F t T],
    reads a grounding that holds a marked variable of Δ only below the
    current level ([GrelL]): at level n a marked value is in V at every
    level j < n, with no ends. Marks are the selves of boxes. At L = ∅
    it is [sem_typed_at] ([sem_later_empty]).

    Every typing rule holds with marks ([later_*]), for every cost
    table, stated at the set form with the facts of the rule read in W.
    The fundamental theorems (static/Fundamental.v) reach these forms
    by instantiating the point variables and the future variables of Γ.

    - A rule that splits its context binds the first premise in a frame
      that holds the other part ([later_bind]). The hole runs with the
      heads of that part in its future ([GrelL_heads], [Erel_cover]).
    - E-Abs and E-Box build values. A typing derivation gives the ends
      of the term and an entry for every free variable ([tfacts]), and
      the values of a grounding are exact ([Vrel_exact]), so the
      instance of the term mentions exactly the ends of its environment
      ([GrelL_fends]).
    - A marked variable is not a term of the judgment ([later_var] asks
      the mark off).
    - A box marks its self ([later_box]). The thunk of the box at level
      n reads the body at levels j ≤ n − κ(β), where the self is in V
      below j by induction on the level. A box that leaves its self
      unmarked needs a positive cost of β ([gen_e_box]), true of κ_DF.
    - A hole that acts before it returns clears the marks of its frame
      ([later_bind_acts]). The frame then meets the value strictly below
      n ([Erel_bind_acts], compat/BindActs.v), where every marked value
      is in V ([GrelL_clear]). It needs send, select and close to cost
      one or more, true of κ_L and false of κ_DF.
    - E-SpawnLam builds the thunk of O-Spawn, which reads the body at
      the empty future ([later_spawn_lam]). *)

From GV Require Export static.Guard compat.SemTyped compat.Redex compat.EFacts cost.Exact compat.BindActs.

(** ** Environments *)

Lemma senv_heads_erase Θ : senv_heads (tenv_erase Θ) = tenv_heads Θ.
Proof.
  apply set_eq. intros y. rewrite elem_of_senv_heads, elem_of_tenv_heads. unfold tenv_erase.
  setoid_rewrite lookup_fmap. split.
  - intros (o & S & x & Ho & ->). destruct (Θ !! o) as [e|] eqn:E; simplify_eq/=. eauto.
  - intros (o & e & Ho & ->). exists o, (te_sty e), (te_pt e). by rewrite Ho.
Qed.

Lemma dom_tenv_erase Θ : dom (tenv_erase Θ) = dom Θ.
Proof. unfold tenv_erase. apply dom_fmap_L. Qed.

Lemma tenv_erase_empty : tenv_erase ∅ = ∅.
Proof. apply fmap_empty. Qed.

Lemma tenv_erase_singleton o S x a : tenv_erase {[o := TE S x a]} = {[o := (S, x)]}.
Proof. unfold tenv_erase. by rewrite map_fmap_singleton. Qed.

Lemma senv_heads_union Θ1 Θ2 y :
  y ∈ senv_heads (Θ1 ∪ Θ2) → y ∈ senv_heads Θ1 ∨ y ∈ senv_heads Θ2.
Proof.
  rewrite !elem_of_senv_heads. intros (o & S & x & Ho & ->).
  apply lookup_union_Some_raw in Ho as [Ho|[_ Ho]]; [left|right]; eauto.
Qed.

Lemma senv_heads_empty_iff Θ : senv_heads Θ = ∅ ↔ Θ = ∅.
Proof.
  split; [|intros ->; apply senv_heads_empty].
  intros H. apply map_empty. intros o. destruct (Θ !! o) as [[S x]|] eqn:E; [|done].
  exfalso. assert (x‾ ∈ senv_heads Θ) as Hy by (apply elem_of_senv_heads; eauto). set_solver.
Qed.

(** The two parts of a split typing environment beside the two parts
    of a split grounding environment. *)
Lemma env_split Θ Θ1 Θ2 (Θ' Θ1' Θ2' : senv) :
  tsplit Θ Θ1 Θ2 → Θ1' ##ₘ Θ2' → Θ' = Θ1' ∪ Θ2' → tenv_erase Θ ##ₘ Θ' →
  tenv_erase Θ1 ##ₘ Θ1' ∧ tenv_erase Θ2 ##ₘ Θ2' ∧
  (tenv_erase Θ1 ∪ Θ1') ##ₘ (tenv_erase Θ2 ∪ Θ2') ∧
  tenv_erase Θ ∪ Θ' = (tenv_erase Θ1 ∪ Θ1') ∪ (tenv_erase Θ2 ∪ Θ2').
Proof.
  intros [Hd ->] Hd' -> HdΘ. unfold tenv_erase in *. rewrite map_fmap_union in HdΘ |- *.
  apply map_disjoint_union_l in HdΘ as [Ha Hb].
  apply map_disjoint_union_r in Ha as [Ha1 Ha2]. apply map_disjoint_union_r in Hb as [Hb1 Hb2].
  assert ((λ e, (te_sty e, te_pt e)) <$> Θ1 ##ₘ (λ e, (te_sty e, te_pt e)) <$> Θ2) as Hd2
    by by apply map_disjoint_fmap.
  split_and!; [done|done| |].
  - apply map_disjoint_union_l. split; apply map_disjoint_union_r; split; try done; by symmetry.
  - rewrite !map_union_assoc. f_equal. rewrite <-!map_union_assoc. f_equal.
    by apply map_union_comm.
Qed.

Section rules0.
  Context (κ : ctable).

  (** A spawn of a thunk, in every later world. *)
  Lemma Erel_spawn_thunk n W Θ F v :
    is_val v →
    (∀ W1, W ⊑ W1 → Vthunk κ n (Vrel κ) (Erel κ) (λ _ Θ' w, Θ' = ∅ ∧ w = EUnit)
                      (λ W' Θ' F e, Erel κ n W' Θ' TUnit F e) W1 Θ v) →
    Erel κ n W Θ TUnit F (ESpawn v).
  Proof.
    intros Hv HT. destruct n as [|n]; [apply Erel_0|].
    assert (tstep (ESpawn v) (LSpawn v) EUnit) as Hst by (by apply tstep_head, t_act_spawn).
    assert (∀ α e', tstep (ESpawn v) α e' → α = LSpawn v ∧ e' = EUnit) as Hdet.
    { intros α e' Hs. apply op_head_only in Hs; [|done]. inversion Hs; by subst. }
    apply Erel_S_intro.
    - intros Hi. exact (Hi _ _ Hst).
    - intros W1 _. eapply ready_tau; [exact Hst|done].
    - intros W1 α e' HW1 Hs. destruct (Hdet _ _ Hs) as [-> ->]. simpl.
      pose proof (HT W1 HW1) as HT1.
      exists Θ, ∅. split_and!.
      + apply map_disjoint_empty_r.
      + by rewrite map_union_empty.
      + exact HT1.
      + apply at_cost_val. by apply Vrel_unit_iff.
  Qed.

  (** V is monotone along subtyping. *)
  Lemma Vrel_tsub T a T' a' : tsub T a T' a' → ∀ n W Θ v, Vrel κ n W Θ T v → Vrel κ n W Θ T' v.
  Proof.
    induction 1 as [a a' _
      |ub lb c t h T1 a1 U a2 c' t' h' T1' a1' U' a2' a a' _ _ _ _ _ IH1 _ IH2
      |T1 a1 U a2 T1' a1' U' a2' a a' _ IH1 _ IH2
      |T1 a1 U a2 T1' a1' U' a2' a a' _ IH1 _ IH2
      |m kk C ub c t U U' aU c' t' a a' _ _ HU
      |s s' x a a' Hs _
      |lb m C C' T T' aT aT' a a' Henv Hf Heq _]; intros n W Θ v.
    - done.
    - rewrite !Vrel_lolli_iff. intros (e & -> & Hfe & Hlb & H). exists e. split_and!; [done|done|done|].
      intros W' j Θ' w F HW Hj Hd Hub Hw. eapply Erel_ty_mono; [|apply H; [done..|by apply IH1]].
      intros m' W2 Θ2 v' _ _. apply IH2.
    - rewrite !Vrel_prod_iff. intros (v1 & v2 & Θ1 & Θ2 & -> & Hd & -> & H1 & H2).
      exists v1, v2, Θ1, Θ2. split_and!; auto.
    - rewrite !Vrel_sum_iff. intros [(v' & -> & H)|(v' & -> & H)]; [left|right]; eauto.
    - rewrite !Vrel_box_iff. intros (-> & e & -> & Hfe & H). split; [done|]. exists e. split_and!; [done|done|].
      intros W' xs ss HW Hxs Hss Hsc HC. specialize (H W' xs ss HW Hxs Hss Hsc HC).
      destruct kk as [|kk]; simpl in HU; [|by subst].
      destruct ss; [|simpl in Hss; lia]. rewrite !sinst_ty_slist_nil in H |- *.
      eapply Vrel_teq; [|exact H]. apply teq_thunk. rewrite <-!ty_inst_df. apply teq_pinst. apply teq_df. first [done|by apply teq_sym].
    - rewrite !Vrel_sess_iff. intros (o & s0 & -> & -> & Hs0). exists o, s0. split_and!; [done|done|].
      unfold seqv in *. eapply sequiv_trans; [exact Hs0|]. by apply sequiv_df.
    - rewrite !Vrel_ex_iff. intros (Hlb & xs & Hxs & HC & H). split; [done|].
      exists xs. split_and!; [done| |].
      + intros x y (g0 & (f & Hf' & Hsc & ->) & Hg). apply HC.
        exists (fact_map (pt_inst (pup (length xs) (plist (bc_env C)))) f). split; [|by rewrite Henv].
        exists f. split_and!; [by apply Hf|by rewrite Henv|by rewrite Henv].
      + eapply Vrel_teq; [|exact H]. rewrite <-!ty_inst_df. apply teq_pinst. apply teq_df. first [done|by apply teq_sym].
  Qed.

  (** The lower bound of an existential, read in W. *)
  Definition lbx_ok (W : world) (lb : lbound) (X : ty) : Prop :=
    match lb with
    | LBot => True
    | LNone => heads X = ∅ ∧ hbot X = false
    | LPt x => (∀ y, y ∈ heads X → w_le W x y) ∧ hbot X = false
    end.

  Lemma lbx_ok_mono W W' lb X : W ⊑ W' → lbx_ok W lb X → lbx_ok W' lb X.
  Proof.
    intros HW. destruct lb; simpl; try done. intros [H ->]. split; [|done].
    intros y Hy. eapply w_le_mono; [exact HW|]. by apply H.
  Qed.

  Lemma beta_det e e' :
    (∀ α e'', tstep e α e'' → α = LBeta ∧ e'' = e') → tstep e LBeta e' →
    ∀ n W Θ T F, Erel κ (n - c_beta κ) W Θ T F e' → Erel κ n W Θ T F e.
  Proof. intros Hd Hs n W Θ T F H. by eapply Erel_beta. Qed.

End rules0.


(** ** Acting terms *)

Lemma acts_not_val e : acts e → ¬ is_val e.
Proof.
  induction 1; simpl; intros Hv; rewrite ?andb_True in Hv; destruct_and?; first [done|auto].
Qed.

Lemma acts_subst e : acts e → ∀ σ, acts (subst σ e).
Proof. induction 1; intros σ; simpl; first [by constructor; auto|by apply acts_branches]. Qed.

Lemma acts_stable κ e α e' : 1 ≤ c_give κ → acts e → tstep e α e' → tcost κ α = 0 → acts e'.
Proof.
  intros Hg Ha Hst. revert Ha. induction Hst as [e α e' Hh|f e α e' Hf Hs IH]; intros Ha Hc.
  - pose proof (c_take_pos κ).
    destruct Hh; simpl in Hc; try lia; inversion Ha; subst; try done.
    all: try (match goal with H : sprim _ |- _ => simpl in H; done end).
    all: try (by exfalso; eapply acts_not_val; [eassumption|]; simpl; rewrite ?andb_True; auto).
    all: try (by apply acts_subst).
    all: try (match goal with H : acts (EBox _) |- _ => inversion H end).
    all: try (match goal with H : acts (Chan _) |- _ => inversion H end).
    all: try (match goal with H : acts (Lam _) |- _ => inversion H end).
  - destruct f; simpl in *; inversion Ha; subst; try (by constructor; auto).
    all: try (by exfalso; eapply acts_not_val; eauto).
    all: try (by apply acts_op).
    all: try (by apply acts_branches).
Qed.

(** ** Groundings with marks *)

Fixpoint GrelL (κ : ctable) (n : nat) (W : world) (Θ : senv) (Δ : lenv) (L : nat → bool)
    (γ : nat → expr) : Prop :=
  match Δ with
  | [] => Θ = ∅
  | None :: Δ' => GrelL κ n W Θ Δ' (λ x, L (S x)) (λ x, γ (S x))
  | Some (T, _) :: Δ' =>
      if L 0 then
        (unlimited T ∧ fends (γ 0) = ∅ ∧ ∀ j, j < n → Vrel κ j W ∅ T (γ 0)) ∧
        GrelL κ n W Θ Δ' (λ x, L (S x)) (λ x, γ (S x))
      else
        ∃ Θ1 Θ2, Θ1 ##ₘ Θ2 ∧ Θ = Θ1 ∪ Θ2 ∧
          Vrel κ n W Θ1 T (γ 0) ∧ GrelL κ n W Θ2 Δ' (λ x, L (S x)) (λ x, γ (S x))
  end.

Definition sem_later (κ : ctable) (W : world) (Θ : tenv) (Δ : lenv) (L : nat → bool)
    (F : gset point) (t : expr) (T : ty) : Prop :=
  ∀ n W' Θ' γ, W ⊑ W' → tenv_erase Θ ##ₘ Θ' → GrelL κ n W' Θ' Δ L γ →
    subst γ t ∈ E[κ]^W' _ n⟦tenv_erase Θ ∪ Θ' ⊢ T⟧^F.

Section groundL.
  Context (κ : ctable).

  Lemma GrelL_ext n W Θ Δ : ∀ L L' γ γ', (∀ x, L x = L' x) → (∀ x, γ x = γ' x) →
    GrelL κ n W Θ Δ L γ → GrelL κ n W Θ Δ L' γ'.
  Proof.
    revert Θ. induction Δ as [|[[T a]|] Δ IH]; intros Θ L L' γ γ' HL Hγ; simpl; [done| |].
    - rewrite <-HL, <-Hγ. destruct (L 0).
      + intros [HV HG]. split; [done|]. eapply IH; [| |exact HG]; intros; simpl; auto.
      + intros (Θ1 & Θ2 & Hd & -> & HV & HG). exists Θ1, Θ2. split_and!; [done|done|done|].
        eapply IH; [| |exact HG]; intros; simpl; auto.
    - apply IH; intros; simpl; auto.
  Qed.

  Lemma GrelL_unmarked n W Θ Δ γ : GrelL κ n W Θ Δ ∅ γ ↔ Grel κ n W Θ Δ γ.
  Proof.
    revert Θ γ. induction Δ as [|[[T a]|] Δ IH]; intros Θ γ; simpl; [done| |apply IH].
    split; intros (Θ1 & Θ2 & Hd & -> & HV & HG); exists Θ1, Θ2; split_and!; try done; by apply IH.
  Qed.

  Lemma GrelL_mono n W W' Θ Δ L γ : W ⊑ W' → GrelL κ n W Θ Δ L γ → GrelL κ n W' Θ Δ L γ.
  Proof.
    intros HW. revert Θ L γ. induction Δ as [|[[T a]|] Δ IH]; intros Θ L γ; simpl; [done| |auto].
    destruct (L 0).
    - intros [(Hu & Hf & HV) HG]. split; [|auto]. split_and!; [done|done|]. intros j Hj. eapply Vrel_mono; [done|auto].
    - intros (Θ1 & Θ2 & Hd & -> & HV & HG). exists Θ1, Θ2. split_and!; try done; [|auto].
      by eapply Vrel_mono.
  Qed.

  Lemma GrelL_down n m W Θ Δ L γ : m ≤ n → GrelL κ n W Θ Δ L γ → GrelL κ m W Θ Δ L γ.
  Proof.
    intros Hm. revert Θ L γ. induction Δ as [|[[T a]|] Δ IH]; intros Θ L γ; simpl; [done| |auto].
    destruct (L 0).
    - intros [(Hu & Hf & HV) HG]. split; [|auto]. split_and!; [done|done|]. intros j Hj. apply HV. lia.
    - intros (Θ1 & Θ2 & Hd & -> & HV & HG). exists Θ1, Θ2. split_and!; try done; [|auto].
      by eapply Vrel_down.
  Qed.

  (** Below the level, a marked value is in V. *)
  Lemma GrelL_clear n j W Θ Δ L γ : j < n → GrelL κ n W Θ Δ L γ → GrelL κ j W Θ Δ ∅ γ.
  Proof.
    intros Hj. revert Θ L γ. induction Δ as [|[[T a]|] Δ IH]; intros Θ L γ; simpl; [done| |].
    - destruct (L 0).
      + intros [(Hu & Hf & HV) HG]. exists ∅, Θ. split_and!; [apply map_disjoint_empty_l
          |by rewrite map_empty_union|by apply HV|]. eapply IH, HG.
      + intros (Θ1 & Θ2 & Hd & -> & HV & HG). exists Θ1, Θ2. split_and!; try done.
        * eapply Vrel_down; [|exact HV]. lia.
        * eapply IH, HG.
    - intros HG. eapply IH, HG.
  Qed.

  Lemma GrelL_empty n W Θ Δ L γ : lenv_empty Δ → GrelL κ n W Θ Δ L γ → Θ = ∅.
  Proof.
    revert Θ L γ. induction Δ as [|o Δ IH]; intros Θ L γ HΔ; simpl; [done|].
    assert (o = None) as -> by (apply HΔ; left).
    apply IH. intros o' Ho'. apply HΔ. by right.
  Qed.

  Lemma GrelL_unl n W Θ Δ L γ : lenv_unl Δ → GrelL κ n W Θ Δ L γ → Θ = ∅.
  Proof.
    revert Θ L γ. induction Δ as [|o Δ IH]; intros Θ L γ HΔ; simpl; [done|].
    assert (lenv_unl Δ) as HΔ' by (intros o' Ho'; apply HΔ; by right).
    destruct (HΔ o ltac:(left)) as [->|(U & a & -> & HU)]; simpl.
    - apply IH, HΔ'.
    - destruct (L 0).
      + intros [_ HG]. exact (IH _ _ _ HΔ' HG).
      + intros (Θ1 & Θ2 & _ & -> & HV & HG).
        rewrite (Vrel_unl_empty κ _ _ _ _ _ HU HV), (IH _ _ _ HΔ' HG). apply map_empty_union.
  Qed.

  Lemma GrelL_split n W Θ Δ Δ1 Δ2 L γ :
    lenv_split Δ Δ1 Δ2 → GrelL κ n W Θ Δ L γ →
    ∃ Θ1 Θ2, Θ1 ##ₘ Θ2 ∧ Θ = Θ1 ∪ Θ2 ∧ GrelL κ n W Θ1 Δ1 L γ ∧ GrelL κ n W Θ2 Δ2 L γ.
  Proof.
    intros Hs. revert Θ L γ. induction Hs as [|Δ Δ1 Δ2 Hs IH|[T a] Δ Δ1 Δ2 Hs IH|[T a] Δ Δ1 Δ2 Hs IH
      |U a Δ Δ1 Δ2 Hu Hs IH]; intros Θ L γ; simpl.
    - intros ->. exists ∅, ∅. split_and!; try done; apply map_disjoint_empty_l.
    - apply IH.
    - destruct (L 0).
      + intros [(Hu' & Hf & HV) HG]. destruct (IH _ _ _ HG) as (Θ1 & Θ2 & Hd & -> & H1 & H2).
        exists Θ1, Θ2. split_and!; done.
      + intros (Θa & Θb & Hd & -> & HV & HG).
        destruct (IH _ _ _ HG) as (Θ1 & Θ2 & Hd' & -> & H1 & H2).
        apply map_disjoint_union_r in Hd as [Hd1 Hd2].
        exists (Θa ∪ Θ1), Θ2. split_and!.
        * apply map_disjoint_union_l. split; done.
        * by rewrite map_union_assoc.
        * exists Θa, Θ1. split_and!; done.
        * done.
    - destruct (L 0).
      + intros [(Hu' & Hf & HV) HG]. destruct (IH _ _ _ HG) as (Θ1 & Θ2 & Hd & -> & H1 & H2).
        exists Θ1, Θ2. split_and!; done.
      + intros (Θa & Θb & Hd & -> & HV & HG).
        destruct (IH _ _ _ HG) as (Θ1 & Θ2 & Hd' & -> & H1 & H2).
        apply map_disjoint_union_r in Hd as [Hd1 Hd2].
        exists Θ1, (Θa ∪ Θ2). split_and!.
        * apply map_disjoint_union_r. split; [by symmetry|done].
        * rewrite map_union_assoc, (map_union_comm Θa Θ1) by done. by rewrite map_union_assoc.
        * done.
        * exists Θa, Θ2. split_and!; done.
    - destruct (L 0).
      + intros [(Hu' & Hf & HV) HG]. destruct (IH _ _ _ HG) as (Θ1 & Θ2 & Hd & -> & H1 & H2).
        exists Θ1, Θ2. split_and!; done.
      + intros (Θa & Θb & Hd & -> & HV & HG).
        pose proof (Vrel_unl_empty κ _ _ _ _ _ Hu HV) as ->.
        destruct (IH _ _ _ HG) as (Θ1 & Θ2 & Hd' & -> & H1 & H2).
        exists Θ1, Θ2. split_and!; [done|by rewrite map_empty_union| |].
        * exists ∅, Θ1. split_and!; [apply map_disjoint_empty_l|by rewrite map_empty_union|done|done].
        * exists ∅, Θ2. split_and!; [apply map_disjoint_empty_l|by rewrite map_empty_union|done|done].
  Qed.

  Lemma GrelL_heads n W Θ Δ L γ :
    GrelL κ n W Θ Δ L γ → lenv_bot Δ = false →
    ∀ o S x, Θ !! o = Some (S, x) → ∃ h, h ∈ lenv_heads Δ ∧ w_le W h x‾.
  Proof.
    revert Θ L γ. induction Δ as [|[[T a]|] Δ IH]; intros Θ L γ; simpl.
    - intros -> _ o S x Hx. by rewrite lookup_empty in Hx.
    - intros HG Hb o S x Hx. apply orb_false_iff in Hb as [Hb1 Hb2]. destruct (L 0).
      + destruct HG as [_ HG]. destruct (IH _ _ _ HG Hb2 o S x Hx) as (h & ? & ?). exists h. set_solver.
      + destruct HG as (Θ1 & Θ2 & _ & -> & HV & HG).
        apply lookup_union_Some_raw in Hx as [Hx|[_ Hx]].
        * destruct (Vrel_heads κ _ _ _ _ _ HV Hb1 o S x Hx) as (h & ? & ?). exists h. set_solver.
        * destruct (IH _ _ _ HG Hb2 o S x Hx) as (h & ? & ?). exists h. set_solver.
    - intros HG Hb. by apply (IH _ _ _ HG Hb).
  Qed.

  Lemma GrelL_ends n W Θ Δ L γ : GrelL κ n W Θ Δ L γ →
    (∀ x σ, Δ !! x = Some (Some σ) → fends (γ x) ⊆ dom Θ) ∧
    (∀ o, o ∈ dom Θ → ∃ x T a, Δ !! x = Some (Some (T, a)) ∧ ¬ unlimited T ∧ o ∈ fends (γ x)).
  Proof.
    revert Θ L γ. induction Δ as [|[[T a]|] Δ IH]; intros Θ L γ; simpl.
    - intros ->. split; [intros x σ; by rewrite lookup_nil|intros o; rewrite dom_empty_L; set_solver].
    - destruct (L 0).
      + intros [(Hu & Hf & HV) HG]. destruct (IH _ _ _ HG) as [A B]. split.
        * intros [|x] σ Hx'; simpl in Hx'; [rewrite Hf; set_solver|by apply (A x σ)].
        * intros o Ho. destruct (B o Ho) as (x & T' & a' & ? & ? & ?). by exists (S x), T', a'.
      + intros (Θ1 & Θ2 & Hd & -> & HV & HG).
        destruct (IH _ _ _ HG) as [A B]. pose proof (Vrel_exact κ _ _ _ _ _ HV) as Hx. split.
        * intros [|x] σ Hx'; simpl in Hx'; rewrite dom_union_L; [rewrite <-Hx; set_solver|].
          specialize (A x σ Hx'). set_solver.
        * intros o. rewrite dom_union_L. intros [Ho|Ho]%elem_of_union.
          { exists 0, T, a. split_and!; [done| |by rewrite <-Hx].
            intros Hu. rewrite (Vrel_unl_empty κ _ _ _ _ _ Hu HV) in Ho. set_solver. }
          destruct (B o Ho) as (x & T' & a' & ? & ? & ?). by exists (S x), T', a'.
    - intros HG. destruct (IH _ _ _ HG) as [A B]. split.
      + intros [|x] σ Hx'; simpl in Hx'; [done|]. by apply (A x σ).
      + intros o Ho. destruct (B o Ho) as (x & T' & a' & ? & ? & ?). by exists (S x), T', a'.
  Qed.

  Lemma GrelL_fends n W Θ0 Θ Δ L γ e :
    tfacts Θ0 Δ e → GrelL κ n W Θ Δ L γ → fends (subst γ e) = dom Θ0 ∪ dom Θ.
  Proof.
    intros (Hf & Hv1 & Hv2) HG. destruct (GrelL_ends _ _ _ _ _ _ HG) as [A B].
    rewrite <-Hf. apply fends_subst_eq.
    - intros x Hx. destruct (Hv1 x Hx) as [σ Hσ]. exact (A x σ Hσ).
    - intros o Ho. destruct (B o Ho) as (x & T & a & Hx & Hu & Ho'). exists x. split; [|done].
      by apply (Hv2 x T a).
  Qed.

  Lemma GrelL_only n W Θ Δ L γ x T a :
    lenv_only Δ x (T, a) → L x = false → GrelL κ n W Θ Δ L γ → Vrel κ n W Θ T (γ x).
  Proof.
    revert Θ L γ x. induction Δ as [|o Δ IH]; intros Θ L γ x [Hx Hy] HL; [done|].
    destruct x as [|x]; simpl in Hx.
    - injection Hx as ->. simpl. rewrite HL. intros (Θ1 & Θ2 & _ & -> & HV & HG).
      assert (lenv_empty Δ) as He.
      { intros o Ho. destruct o as [σ|]; [|done]. apply list_elem_of_lookup in Ho as [i Hi].
        by destruct (Hy (S i) σ Hi). }
      rewrite (GrelL_empty _ _ _ _ _ _ He HG), map_union_empty. done.
    - destruct o as [[T' a']|]; simpl.
      + by destruct (Hy 0 (T', a') eq_refl).
      + intros HG. apply (IH Θ (λ y, L (S y)) (λ y, γ (S y)) x); [|done|done]. split; [done|].
        intros y σ' Hσ. destruct (Hy (S y) σ' Hσ) as [[= ->] ->]. done.
  Qed.

  Lemma GrelL_wk n W Θ Δ' Δ L γ : lenv_wk Δ' Δ → GrelL κ n W Θ Δ L γ → GrelL κ n W Θ Δ' L γ.
  Proof.
    intros Hwk. revert Θ L γ. induction Hwk as [|o Δ' Δ Hwk IH|U a Δ' Δ Hu Hwk IH]; intros Θ L γ; simpl.
    - done.
    - destruct o as [[T a]|]; [|apply IH]. destruct (L 0).
      + intros [HV HG]. split; [done|auto].
      + intros (Θ1 & Θ2 & Hd & -> & HV & HG). exists Θ1, Θ2. split_and!; auto.
    - destruct (L 0).
      + intros [_ HG]. by apply IH.
      + intros (Θ1 & Θ2 & Hd & -> & HV & HG).
        rewrite (Vrel_unl_empty κ _ _ _ _ _ Hu HV), map_empty_union. by apply IH.
  Qed.

  Lemma GrelL_contract n W Θ U a Δ L γ :
    unlimited U → GrelL κ n W Θ (Some (U, a) :: Δ) L γ →
    GrelL κ n W Θ (Some (U, a) :: Some (U, a) :: Δ) (λ x, L (pred x)) (λ x, γ (pred x)).
  Proof.
    intros Hu HG. simpl in HG |- *. destruct (L 0) eqn:HL0.
    - destruct HG as [HV HG]. split; [done|]. split; [done|].
      eapply GrelL_ext; [| |exact HG]; by intros [|x].
    - destruct HG as (Θ1 & Θ2 & Hd & -> & HV & HG).
      pose proof (Vrel_unl_empty κ _ _ _ _ _ Hu HV) as ->.
      rewrite map_empty_union.
      exists ∅, Θ2. split_and!; [apply map_disjoint_empty_l|by rewrite map_empty_union|done|].
      exists ∅, Θ2. split_and!; [apply map_disjoint_empty_l|by rewrite map_empty_union|done|].
      eapply GrelL_ext; [| |exact HG]; by intros [|x].
  Qed.

  Lemma GrelL_pick n W Θ Δ L γ i T1 a :
    Δ !! i = Some (Some (T1, a)) → ¬ unlimited T1 → GrelL κ n W Θ Δ L γ →
    ∃ Θi, Vrel κ n W Θi T1 (γ i) ∧
      ∀ T2 b, Vrel κ n W Θi T2 (γ i) → GrelL κ n W Θ (<[i := Some (T2, b)]> Δ) L γ.
  Proof.
    revert Θ L γ i. induction Δ as [|o Δ IH]; intros Θ L γ i Hi Hnu; [done|].
    destruct i as [|i]; simpl in Hi |- *.
    - injection Hi as ->. destruct (L 0).
      + by intros [[Hu _] _].
      + intros (Θ1 & Θ2 & Hd & -> & HV & HG).
        exists Θ1. split; [done|]. intros T2 b HV2. exists Θ1, Θ2. split_and!; done.
    - destruct o as [[U c]|]; simpl.
      + destruct (L 0).
        * intros [HV HG]. destruct (IH _ _ _ i Hi Hnu HG) as (Θi & HVi & Hk). exists Θi.
          split; [done|]. intros T2 b HV2. split; [done|]. by apply Hk.
        * intros (Θ1 & Θ2 & Hd & -> & HV & HG).
          destruct (IH _ _ _ i Hi Hnu HG) as (Θi & HVi & Hk). exists Θi. split; [done|].
          intros T2 b HV2. exists Θ1, Θ2. split_and!; auto.
      + intros HG. destruct (IH _ _ _ i Hi Hnu HG) as (Θi & HVi & Hk). exists Θi. split; [done|].
        intros T2 b HV2. by apply Hk.
  Qed.
End groundL.

Lemma sem_later_empty κ W Θ Δ F t T : sem_later κ W Θ Δ ∅ F t T ↔ sem_typed_at κ W Θ Δ F t T.
Proof.
  split; intros H n W' Θ' γ HW Hd HG; apply H; try done; by apply GrelL_unmarked.
Qed.

(** A box at a positive cost of β, unmarked. *)
Lemma gen_e_box κ W Δ F e m kk C ub c t U aU a :
  1 ≤ c_beta κ → tfacts ∅ Δ (EBox e) → lenv_unl Δ →
  (∀ W1 xs ss F', W ⊑ W1 → length xs = m → length ss = kk → Forall hcontractive ss →
     wholds W1 C xs → ub_lt W1 (pt_inst (plist xs) <$> ub) F' →
     sem_typed_at κ W1 ∅ (Some (TBox m kk C ub c t U aU, a) :: Δ) F' e
       (sinst_ty (slist ss) (ty_inst xs U))) →
  sem_typed_at κ W ∅ Δ F (EBox e) (TBox m kk C ub c t U aU).
Proof.
  intros Hβ Htf Hu Hbody n W' Θ' γ HW Hd HG.
  pose proof (GrelL_fends κ _ _ _ _ _ _ _ _ Htf (proj2 (GrelL_unmarked κ _ _ _ _ _) HG)) as Hx.
  pose proof (GrelL_unl κ _ _ _ _ _ _ Hu (proj2 (GrelL_unmarked κ _ _ _ _ _) HG)) as ->.
  rewrite tenv_erase_empty, map_union_empty. simpl in Hx. rewrite !dom_empty_L, union_empty_r_L in Hx.
  set (eb := subst (up γ) e). fold eb in Hx.
  apply Vrel_Erel.
  assert (∀ j W2, j ≤ n → W' ⊑ W2 → Vrel κ j W2 ∅ (TBox m kk C ub c t U aU) (EBox eb)) as Hlob.
  { induction j as [j IH] using lt_wf_ind. intros W2 Hj HW2. apply Vrel_box_iff.
    split; [done|]. exists eb. split_and!; [done|done|].
    intros W3 xs ss HW3 Hxs Hss Hsc HC. apply Vrel_lolli_iff.
    exists (rename S (subst1 (EBox eb) eb)). split_and!.
    - done.
    - rewrite dom_empty_L, fends_rename. unfold subst1.
      assert (fends (subst (EBox eb .: Var) eb) ⊆ fends eb ∪ ∅) as Hsub.
      { apply fends_subst, allfv_forall. intros [|y]; simpl; [rewrite Hx|]; set_solver. }
      set_solver.
    - done.
    - intros W4 j' Θ'' w F' HW4 Hj' _ Hub Hw.
      apply Vrel_unit_iff in Hw as [-> ->]. rewrite map_union_empty, thunk_app.
      unfold eb. rewrite subst1_subst.
      assert (W ⊑ W4) as HW04.
      { eapply wext_trans; [exact HW|]. eapply wext_trans; [exact HW2|]. by eapply wext_trans. }
      assert (W' ⊑ W4) as HW'4.
      { eapply wext_trans; [exact HW2|]. by eapply wext_trans. }
      assert (Grel κ j' W4 ∅ (Some (TBox m kk C ub c t U aU, a) :: Δ) (EBox eb .: γ)) as HG'.
      { exists ∅, ∅. split_and!; [apply map_disjoint_empty_l|by rewrite map_union_empty| |].
        - apply IH; [lia|lia|done].
        - eapply Grel_down; [|eapply Grel_mono; [exact HW'4|exact HG]]. lia. }
      pose proof (Hbody W4 xs ss F' HW04 Hxs Hss Hsc (wholds_mono _ _ _ _ HW4 HC) Hub
                    j' W4 ∅ (EBox eb .: γ) (wext_refl _)
                    ltac:(rewrite tenv_erase_empty; apply map_disjoint_empty_l) HG') as Hb.
      by rewrite tenv_erase_empty, map_union_empty in Hb. }
  apply Hlob; [lia|apply wext_refl].
Qed.


(** ** The rules *)

Section later.
  Context (κ : ctable).

  Lemma sem_later_future W Θ Δ L F F' t T :
    F' ⊆ F → sem_later κ W Θ Δ L F t T → sem_later κ W Θ Δ L F' t T.
  Proof. intros HF H n W' Θ' γ HW Hd HG. eapply Erel_future; [exact HF|]. by apply H. Qed.

  Lemma sem_later_blind W Θ Δ L F t T T' :
    ty_df T = ty_df T' → sem_later κ W Θ Δ L F t T → sem_later κ W Θ Δ L F t T'.
  Proof. intros H He n W' Θ' γ HW Hd HG. eapply (Erel_blind κ); [|by apply He]. done. Qed.

  Lemma later_bind (mk : (nat → expr) → frame) W Θ Θ1 Θ2 Δ Δ1 Δ2 L F e t T U :
    tsplit Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
    (∀ γ, subst γ t = fill_frame (mk γ) (subst γ e)) → (∀ γ, frame_val (mk γ)) →
    (∀ B, sem_later κ W Θ1 Δ1 L (F ∪ tenv_heads Θ2 ∪ lenv_heads Δ2 ∪ (if lenv_bot Δ2 then B else ∅)) e T) →
    (∀ W' j Θv v Θ2' γ, W ⊑ W' → tenv_erase Θ2 ##ₘ Θ2' → GrelL κ j W' Θ2' Δ2 L γ →
       Θv ##ₘ tenv_erase Θ2 ∪ Θ2' → Vrel κ j W' Θv T v →
       fill_frame (mk γ) v ∈ E[κ]^W' _ j⟦Θv ∪ (tenv_erase Θ2 ∪ Θ2') ⊢ U⟧^F) →
    sem_later κ W Θ Δ L F t U.
  Proof.
    intros Hs Hl Ht Hf He Hk n W' Θ' γ HW Hd HG.
    destruct (GrelL_split κ _ _ _ _ _ _ _ _ Hl HG) as (Θ1' & Θ2' & Hd' & -> & HG1 & HG2).
    destruct (env_split _ _ _ _ _ _ Hs Hd' eq_refl Hd) as (Hd1 & Hd2 & Hd12 & ->).
    rewrite Ht. apply (Erel_bind κ n (mk γ) W' _ _ T); [done|done| |].
    - eapply Erel_cover; [|exact (He (senv_heads (tenv_erase Θ2 ∪ Θ2')) n W' Θ1' γ HW Hd1 HG1)].
      intros y [Hy|Hy]%elem_of_union.
      { exists y. split; [set_solver|by left]. }
      destruct (lenv_bot Δ2) eqn:Hb.
      { exists y. split; [set_solver|by left]. }
      apply senv_heads_union in Hy as [Hy|Hy].
      + exists y. split; [|by left]. rewrite senv_heads_erase in Hy. set_solver.
      + apply elem_of_senv_heads in Hy as (o & S & x & Ho & ->).
        destruct (GrelL_heads κ _ _ _ _ _ _ HG2 Hb o S x Ho) as (h & Hh & Hle).
        exists h. split; [set_solver|done].
    - intros W'' j Θv v HW' Hj Hdv HV. apply (Hk W'' j Θv v Θ2' γ); [by eapply wext_trans|done| |done|done].
      eapply GrelL_down; [exact Hj|]. by eapply GrelL_mono.
  Qed.

  (** The hole acts, so its frame runs below the level, with no marks. *)
  Lemma later_bind_acts (mk : (nat → expr) → frame) W Θ Θ1 Θ2 Δ Δ1 Δ2 L F e t T U :
    1 ≤ c_give κ → acts e →
    tsplit Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
    (∀ γ, subst γ t = fill_frame (mk γ) (subst γ e)) → (∀ γ, frame_val (mk γ)) →
    (∀ B, sem_later κ W Θ1 Δ1 L (F ∪ tenv_heads Θ2 ∪ lenv_heads Δ2 ∪ (if lenv_bot Δ2 then B else ∅)) e T) →
    (∀ W' j Θv v Θ2' γ, W ⊑ W' → tenv_erase Θ2 ##ₘ Θ2' → GrelL κ j W' Θ2' Δ2 ∅ γ →
       Θv ##ₘ tenv_erase Θ2 ∪ Θ2' → Vrel κ j W' Θv T v →
       fill_frame (mk γ) v ∈ E[κ]^W' _ j⟦Θv ∪ (tenv_erase Θ2 ∪ Θ2') ⊢ U⟧^F) →
    sem_later κ W Θ Δ L F t U.
  Proof.
    intros Hg Ha Hs Hl Ht Hf He Hk n W' Θ' γ HW Hd HG.
    destruct (GrelL_split κ _ _ _ _ _ _ _ _ Hl HG) as (Θ1' & Θ2' & Hd' & -> & HG1 & HG2).
    destruct (env_split _ _ _ _ _ _ Hs Hd' eq_refl Hd) as (Hd1 & Hd2 & Hd12 & ->).
    rewrite Ht. apply (Erel_bind_acts κ acts n (mk γ) W' _ _ T); [apply acts_not_val
      |intros ???; by apply acts_stable|by apply acts_subst|done|done| |].
    - eapply Erel_cover; [|exact (He (senv_heads (tenv_erase Θ2 ∪ Θ2')) n W' Θ1' γ HW Hd1 HG1)].
      intros y [Hy|Hy]%elem_of_union.
      { exists y. split; [set_solver|by left]. }
      destruct (lenv_bot Δ2) eqn:Hb.
      { exists y. split; [set_solver|by left]. }
      apply senv_heads_union in Hy as [Hy|Hy].
      + exists y. split; [|by left]. rewrite senv_heads_erase in Hy. set_solver.
      + apply elem_of_senv_heads in Hy as (o & S & x & Ho & ->).
        destruct (GrelL_heads κ _ _ _ _ _ _ HG2 Hb o S x Ho) as (h & Hh & Hle).
        exists h. split; [set_solver|done].
    - intros W'' j Θv v HW' Hj Hdv HV. apply (Hk W'' j Θv v Θ2' γ); [by eapply wext_trans|done| |done|done].
      eapply GrelL_clear; [exact Hj|]. by eapply GrelL_mono.
  Qed.

  Lemma later_frame0 (f : frame) W Θ Δ L F e t Targ Tres :
    frame_val f → (∀ γ, subst γ t = fill_frame f (subst γ e)) →
    (∀ W' j Θv v, W ⊑ W' → Vrel κ j W' Θv Targ v → Erel κ j W' Θv Tres F (fill_frame f v)) →
    sem_later κ W Θ Δ L F e Targ → sem_later κ W Θ Δ L F t Tres.
  Proof.
    intros Hf Ht Hred He n W' Θ' γ HW Hd HG. rewrite Ht.
    rewrite <-(map_union_empty (tenv_erase Θ ∪ Θ')).
    apply (Erel_bind κ n f W' _ ∅ Targ Tres F (subst γ e)); [done|apply map_disjoint_empty_r| |].
    - rewrite senv_heads_empty, union_empty_r_L. by apply He.
    - intros W'' j Θv v HW' _ _ Hv. rewrite map_union_empty. apply Hred; [by eapply wext_trans|done].
  Qed.

  (** *** Values *)

  Lemma later_unit W Δ L F : lenv_empty Δ → sem_later κ W ∅ Δ L F EUnit TUnit.
  Proof.
    intros HΔ n W' Θ' γ HW Hd HG. rewrite (GrelL_empty κ _ _ _ _ _ _ HΔ HG), tenv_erase_empty, map_union_empty.
    apply Vrel_Erel. by apply Vrel_unit_iff.
  Qed.

  Lemma later_var W Δ L F x T a :
    lenv_only Δ x (T, a) → L x = false → sem_later κ W ∅ Δ L F (Var x) T.
  Proof.
    intros HΔ HL n W' Θ' γ HW Hd HG. rewrite tenv_erase_empty, map_empty_union.
    apply Vrel_Erel. by eapply GrelL_only.
  Qed.

  Lemma later_chan W Δ L F o S x a :
    lenv_empty Δ → sem_later κ W {[o := TE S x a]} Δ L F (Chan o) (TSess S x).
  Proof.
    intros HΔ n W' Θ' γ HW Hd HG. rewrite (GrelL_empty κ _ _ _ _ _ _ HΔ HG), map_union_empty, tenv_erase_singleton.
    apply Vrel_Erel. apply Vrel_sess_iff. exists o, S. split_and!; [done|done|apply seqv_refl].
  Qed.

  Lemma later_new_ext (ℓ : family) W0 W Δ L F S a1 a2 a3 :
    W0 ⊑ W → lenv_empty Δ → ℓ ∈ w_fams W0 →
    sem_later κ W ∅ Δ L F (ENew ℓ)
      (TEx LBot 1 (bcs_of (w_laws W0 ℓ)) (TProd (TSess S (pvar 0)) a1 (TSess (dual S) (pvar 0)‾) a2) a3).
  Proof.
    intros HW0 HΔ Hℓ n W' Θ' γ HW Hd HG. simpl.
    rewrite (GrelL_empty κ _ _ _ _ _ _ HΔ HG), tenv_erase_empty, map_union_empty.
    assert (W0 ⊑ W') as HW0' by by eapply wext_trans.
    apply Erel_new_sub.
    - by apply (wext_fams _ _ HW0').
    - intros f Hf. by apply (wext_laws _ _ HW0').
  Qed.

  Lemma later_abs W Θ Δ L F e T aT U aU ub lb c t h :
    tfacts Θ Δ (Lam e) → lenv_bot Δ = false → lb_le W lb (tenv_heads Θ ∪ lenv_heads Δ) →
    (∀ W1 F', W ⊑ W1 → ub_lt W1 ub F' → sem_later κ W1 Θ (Some (T, aT) :: Δ) (false .: L) F' e U) →
    sem_later κ W Θ Δ L F (Lam e) (TLolli ub lb c t h T aT U aU).
  Proof.
    intros Htf Hb Hlb Hbody n W' Θ' γ HW Hd HG. apply Vrel_Erel, Vrel_lolli_iff.
    exists (subst (up γ) e). split_and!.
    - done.
    - pose proof (GrelL_fends κ _ _ _ _ _ _ _ _ Htf HG) as Hx. simpl in Hx.
      by rewrite Hx, dom_union_L, dom_tenv_erase.
    - destruct lb as [l|]; simpl in Hlb |- *.
      + intros y Hy. apply senv_heads_union in Hy as [Hy|Hy].
        * rewrite senv_heads_erase in Hy. eapply w_le_mono; [exact HW|]. apply Hlb. set_solver.
        * apply elem_of_senv_heads in Hy as (o & S & x & Ho & ->).
          destruct (GrelL_heads κ _ _ _ _ _ _ HG Hb o S x Ho) as (h0 & Hh & Hle).
          eapply w_le_trans; [|exact Hle]. eapply w_le_mono; [exact HW|]. apply Hlb. set_solver.
      + apply senv_heads_empty_iff.
        assert (tenv_heads Θ = ∅ ∧ lenv_heads Δ = ∅) as [H1 H2] by set_solver.
        assert (Θ' = ∅) as ->.
        { apply map_empty. intros o. destruct (Θ' !! o) as [[S x]|] eqn:E; [|done].
          destruct (GrelL_heads κ _ _ _ _ _ _ HG Hb o S x E) as (h0 & Hh & _). set_solver. }
        rewrite map_union_empty. apply senv_heads_empty_iff. by rewrite senv_heads_erase.
    - intros W'' j Θ'' w F' HW' Hj Hd'' Hub Hw. rewrite subst1_subst.
      apply map_disjoint_union_l in Hd'' as [Hd1 Hd2].
      rewrite <-map_union_assoc, (map_union_comm Θ' Θ'') by done.
      apply (Hbody W'' F' (wext_trans _ _ _ HW HW') Hub j W'' (Θ'' ∪ Θ') (w .: γ) (wext_refl _)).
      + apply map_disjoint_union_r. split; [done|done].
      + exists Θ'', Θ'. split_and!; [by symmetry|done|done|].
        eapply GrelL_down; [|by eapply GrelL_mono]. lia.
  Qed.

  (** A box marks its self, at every cost table. *)
  Lemma later_box W Δ L F e m kk C ub c t U aU a :
    tfacts ∅ Δ (EBox e) → lenv_unl Δ →
    (∀ W1 xs ss F', W ⊑ W1 → length xs = m → length ss = kk → Forall hcontractive ss →
       wholds W1 C xs → ub_lt W1 (pt_inst (plist xs) <$> ub) F' →
       sem_later κ W1 ∅ (Some (TBox m kk C ub c t U aU, a) :: Δ) (true .: L) F' e
         (sinst_ty (slist ss) (ty_inst xs U))) →
    sem_later κ W ∅ Δ L F (EBox e) (TBox m kk C ub c t U aU).
  Proof.
    intros Htf Hu Hbody n W' Θ' γ HW Hd HG.
    pose proof (GrelL_fends κ _ _ _ _ _ _ _ _ Htf HG) as Hx.
    pose proof (GrelL_unl κ _ _ _ _ _ _ Hu HG) as ->.
    rewrite tenv_erase_empty, map_union_empty. simpl in Hx. rewrite !dom_empty_L, union_empty_r_L in Hx.
    set (eb := subst (up γ) e). fold eb in Hx.
    apply Vrel_Erel.
    assert (∀ j W2, j ≤ n → W' ⊑ W2 → Vrel κ j W2 ∅ (TBox m kk C ub c t U aU) (EBox eb)) as Hlob.
    { induction j as [j IH] using lt_wf_ind. intros W2 Hj HW2. apply Vrel_box_iff.
      split; [done|]. exists eb. split_and!; [done|done|].
      intros W3 xs ss HW3 Hxs Hss Hsc HC. apply Vrel_lolli_iff.
      exists (rename S (subst1 (EBox eb) eb)). split_and!.
      - done.
      - rewrite dom_empty_L, fends_rename. unfold subst1.
        assert (fends (subst (EBox eb .: Var) eb) ⊆ fends eb ∪ ∅) as Hsub.
        { apply fends_subst, allfv_forall. intros [|y]; simpl; [rewrite Hx|]; set_solver. }
        set_solver.
      - done.
      - intros W4 j' Θ'' w F' HW4 Hj' _ Hub Hw.
        apply Vrel_unit_iff in Hw as [-> ->]. rewrite map_union_empty, thunk_app.
        unfold eb. rewrite subst1_subst.
        assert (W ⊑ W4) as HW04.
        { eapply wext_trans; [exact HW|]. eapply wext_trans; [exact HW2|]. by eapply wext_trans. }
        assert (W' ⊑ W4) as HW'4.
        { eapply wext_trans; [exact HW2|]. by eapply wext_trans. }
        assert (GrelL κ j' W4 ∅ (Some (TBox m kk C ub c t U aU, a) :: Δ) (true .: L) (EBox eb .: γ)) as HG'.
        { simpl. split; [split_and!|].
          - done.
          - done.
          - intros i Hi. apply IH; [lia|lia|done].
          - eapply GrelL_down; [|eapply GrelL_mono; [exact HW'4|exact HG]]. lia. }
        pose proof (Hbody W4 xs ss F' HW04 Hxs Hss Hsc (wholds_mono _ _ _ _ HW4 HC) Hub
                      j' W4 ∅ (EBox eb .: γ) (wext_refl _)
                      ltac:(rewrite tenv_erase_empty; apply map_disjoint_empty_l) HG') as Hb.
        by rewrite tenv_erase_empty, map_union_empty in Hb. }
    apply Hlob; [lia|apply wext_refl].
  Qed.


  (** *** Frames, with or without clearing the marks *)

  (** The marks of the frame: L itself, or none when the hole acts. *)
  Definition kmarks (L L' : nat → bool) (e : expr) : Prop :=
    L' = L ∨ (L' = ∅ ∧ 1 ≤ c_give κ ∧ acts e).

  Lemma later_bind_gen (mk : (nat → expr) → frame) W Θ Θ1 Θ2 Δ Δ1 Δ2 L L' F e t T U :
    kmarks L L' e →
    tsplit Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
    (∀ γ, subst γ t = fill_frame (mk γ) (subst γ e)) → (∀ γ, frame_val (mk γ)) →
    (∀ B, sem_later κ W Θ1 Δ1 L (F ∪ tenv_heads Θ2 ∪ lenv_heads Δ2 ∪ (if lenv_bot Δ2 then B else ∅)) e T) →
    (∀ W' j Θv v Θ2' γ, W ⊑ W' → tenv_erase Θ2 ##ₘ Θ2' → GrelL κ j W' Θ2' Δ2 L' γ →
       Θv ##ₘ tenv_erase Θ2 ∪ Θ2' → Vrel κ j W' Θv T v →
       fill_frame (mk γ) v ∈ E[κ]^W' _ j⟦Θv ∪ (tenv_erase Θ2 ∪ Θ2') ⊢ U⟧^F) →
    sem_later κ W Θ Δ L F t U.
  Proof.
    intros [->|(-> & Hg & Ha)].
    - apply later_bind.
    - by apply later_bind_acts.
  Qed.

  Lemma later_app W Θ Θ1 Θ2 Δ Δ1 Δ2 L L' F e1 e2 ub lb c t h T aT U aU :
    kmarks L L' e1 → tsplit Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 → ub_lt W ub F →
    (∀ B, sem_later κ W Θ1 Δ1 L (F ∪ tenv_heads Θ2 ∪ lenv_heads Δ2 ∪ (if lenv_bot Δ2 then B else ∅)) e1
            (TLolli ub lb c t h T aT U aU)) →
    sem_later κ W Θ2 Δ2 L' (F ∪ opt_heads lb) e2 T →
    sem_later κ W Θ Δ L F (App e1 e2) U.
  Proof.
    intros Hk Hs Hl Hub He1 He2.
    eapply (later_bind_gen (λ γ, FAppL (subst γ e2)) W Θ Θ1 Θ2 Δ Δ1 Δ2 L L' F e1 _
              (TLolli ub lb c t h T aT U aU) U Hk Hs Hl); [done|done|exact He1|].
    intros W' j Θv v Θ2' γ HW Hd2 HG2 Hdv HV. simpl.
    pose proof (Vrel_val κ _ _ _ _ _ HV) as Hvv.
    pose proof HV as (eb & -> & _ & Hlbv & _)%Vrel_lolli_iff.
    rewrite (map_union_comm Θv) by done.
    change (App (Lam eb) (subst γ e2)) with (fill_frame (FAppR (Lam eb)) (subst γ e2)).
    apply (Erel_bind κ j _ W' _ _ T); [done|by symmetry| |].
    - eapply Erel_cover; [|exact (He2 j W' Θ2' γ HW Hd2 HG2)].
      intros y [Hy|Hy]%elem_of_union; [exists y; split; [set_solver|by left]|].
      destruct lb as [l|]; simpl in Hlbv.
      + exists l. split; [set_solver|by apply Hlbv].
      + rewrite Hlbv in Hy. set_solver.
    - intros W'' j' Θw w HW' Hj' Hdw Hw. simpl. rewrite map_union_comm by done.
      apply (Erel_app κ j' W'' Θv Θw ub lb c t h T aT U aU); [by symmetry| | |done].
      + eapply ub_lt_mono; [eapply wext_trans; [exact HW|exact HW']|exact Hub].
      + eapply Vrel_down; [exact Hj'|]. by eapply Vrel_mono.
  Qed.

  Lemma later_pair W Θ Θ1 Θ2 Δ Δ1 Δ2 L L' F e1 e2 T1 a1 T2 a2 :
    kmarks L L' e1 → tsplit Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
    (∀ B, sem_later κ W Θ1 Δ1 L (F ∪ tenv_heads Θ2 ∪ lenv_heads Δ2 ∪ (if lenv_bot Δ2 then B else ∅)) e1 T1) →
    (∀ B, sem_later κ W Θ2 Δ2 L' (F ∪ heads T1 ∪ (if hbot T1 then B else ∅)) e2 T2) →
    sem_later κ W Θ Δ L F (Pair e1 e2) (TProd T1 a1 T2 a2).
  Proof.
    intros Hk Hs Hl He1 He2.
    eapply (later_bind_gen (λ γ, FPairL (subst γ e2)) W Θ Θ1 Θ2 Δ Δ1 Δ2 L L' F e1 _ T1 _ Hk Hs Hl);
      [done|done|exact He1|].
    intros W' j Θv v Θ2' γ HW Hd2 HG2 Hdv HV. simpl.
    pose proof (Vrel_val κ _ _ _ _ _ HV) as Hvv.
    rewrite (map_union_comm Θv) by done.
    change (Pair v (subst γ e2)) with (fill_frame (FPairR v) (subst γ e2)).
    apply (Erel_bind κ j _ W' _ _ T2); [done|by symmetry| |].
    - eapply Erel_cover; [|exact (He2 (senv_heads Θv) j W' Θ2' γ HW Hd2 HG2)].
      intros y [Hy|Hy]%elem_of_union; [exists y; split; [set_solver|by left]|].
      destruct (hbot T1) eqn:Hb; [exists y; split; [set_solver|by left]|].
      apply elem_of_senv_heads in Hy as (o & S & x & Ho & ->).
      destruct (Vrel_heads κ _ _ _ _ _ HV Hb o S x Ho) as (h0 & ? & ?).
      exists h0. split; [set_solver|done].
    - intros W'' j' Θw w HW' Hj' Hdw Hw. simpl. rewrite map_union_comm by done.
      apply Vrel_Erel, Vrel_prod_iff. exists v, w, Θv, Θw. split_and!; [done|by symmetry|done| |done].
      eapply Vrel_down; [exact Hj'|]. by eapply Vrel_mono.
  Qed.

  Lemma later_letu W Θ Θ1 Θ2 Δ Δ1 Δ2 L L' F e1 e2 T :
    kmarks L L' e1 → tsplit Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
    (∀ B, sem_later κ W Θ1 Δ1 L (F ∪ tenv_heads Θ2 ∪ lenv_heads Δ2 ∪ (if lenv_bot Δ2 then B else ∅)) e1 TUnit) →
    sem_later κ W Θ2 Δ2 L' F e2 T →
    sem_later κ W Θ Δ L F (LetU e1 e2) T.
  Proof.
    intros Hk Hs Hl He1 He2.
    eapply (later_bind_gen (λ γ, FLetU (subst γ e2)) W Θ Θ1 Θ2 Δ Δ1 Δ2 L L' F e1 _ TUnit _ Hk Hs Hl);
      [done|done|exact He1|].
    intros W' j Θv v Θ2' γ HW Hd2 HG2 Hdv HV. simpl.
    apply Vrel_unit_iff in HV as [-> ->]. rewrite map_empty_union.
    apply (beta_det κ _ (subst γ e2)).
    - intros α e'' Hst. assert (head_step (LetU EUnit (subst γ e2)) α e'') as Hh by head_only.
      inversion Hh; by subst.
    - apply tstep_head, t_act_let_unit.
    - apply He2; [done|done|]. eapply GrelL_down; [|exact HG2]. lia.
  Qed.

  Lemma later_letp W Θ Θ1 Θ2 Δ Δ1 Δ2 L L' F e1 e2 T1 a1 T2 a2 b1 b2 T :
    kmarks L L' e1 → tsplit Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
    (∀ B, sem_later κ W Θ1 Δ1 L (F ∪ tenv_heads Θ2 ∪ lenv_heads Δ2 ∪ (if lenv_bot Δ2 then B else ∅)) e1
            (TProd T1 a1 T2 a2)) →
    sem_later κ W Θ2 (Some (T2, b2) :: Some (T1, b1) :: Δ2) (false .: false .: L') F e2 T →
    sem_later κ W Θ Δ L F (LetP e1 e2) T.
  Proof.
    intros Hk Hs Hl He1 He2.
    eapply (later_bind_gen (λ γ, FLetP (subst (up (up γ)) e2)) W Θ Θ1 Θ2 Δ Δ1 Δ2 L L' F e1 _
              (TProd T1 a1 T2 a2) _ Hk Hs Hl); [done|done|exact He1|].
    intros W' j Θv v Θ2' γ HW Hd2 HG2 Hdv HV. simpl.
    apply Vrel_prod_iff in HV as (v1 & v2 & Θa & Θb & -> & Hdab & -> & H1 & H2).
    pose proof (Vrel_val κ _ _ _ _ _ H1) as Hv1. pose proof (Vrel_val κ _ _ _ _ _ H2) as Hv2.
    apply (beta_det κ _ (subst (v2 .: v1 .: γ) e2)).
    - intros α e'' Hst. assert (head_step (LetP (Pair v1 v2) (subst (up (up γ)) e2)) α e'') as Hh
        by head_only.
      inversion Hh; subst. split; [done|]. by rewrite subst2_subst.
    - rewrite <-(subst2_subst v1 v2 γ e2). by apply tstep_head, t_act_let_pair.
    - apply map_disjoint_union_l in Hdv as [Hda Hdb].
      apply map_disjoint_union_r in Hda as [Hda1 Hda2]. apply map_disjoint_union_r in Hdb as [Hdb1 Hdb2].
      assert ((Θa ∪ Θb) ∪ (tenv_erase Θ2 ∪ Θ2') = tenv_erase Θ2 ∪ (Θb ∪ (Θa ∪ Θ2'))) as ->.
      { rewrite (map_union_comm Θa Θb) by done.
        rewrite <-(map_union_assoc Θb Θa), (map_union_assoc Θa (tenv_erase Θ2) Θ2').
        rewrite (map_union_comm Θa (tenv_erase Θ2)) by done.
        rewrite <-(map_union_assoc (tenv_erase Θ2) Θa Θ2'), (map_union_assoc Θb (tenv_erase Θ2)).
        rewrite (map_union_comm Θb (tenv_erase Θ2)) by done.
        by rewrite <-(map_union_assoc (tenv_erase Θ2) Θb). }
      apply He2; [done| |].
      + apply map_disjoint_union_r. split; [by symmetry|].
        apply map_disjoint_union_r. split; [by symmetry|done].
      + simpl. exists Θb, (Θa ∪ Θ2'). split_and!.
        * apply map_disjoint_union_r. split; [by symmetry|done].
        * done.
        * eapply Vrel_down; [|exact H2]. lia.
        * exists Θa, Θ2'. split_and!; [done|done| |].
          { eapply Vrel_down; [|exact H1]. lia. }
          { eapply GrelL_down; [|exact HG2]. lia. }
  Qed.

  Lemma later_case W Θ Θ1 Θ2 Δ Δ1 Δ2 L L' F e e1 e2 T1 a1 T2 a2 b1 b2 T :
    kmarks L L' e → tsplit Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
    (∀ B, sem_later κ W Θ1 Δ1 L (F ∪ tenv_heads Θ2 ∪ lenv_heads Δ2 ∪ (if lenv_bot Δ2 then B else ∅)) e
            (TSum T1 a1 T2 a2)) →
    sem_later κ W Θ2 (Some (T1, b1) :: Δ2) (false .: L') F e1 T →
    sem_later κ W Θ2 (Some (T2, b2) :: Δ2) (false .: L') F e2 T →
    sem_later κ W Θ Δ L F (Case e e1 e2) T.
  Proof.
    intros Hk Hs Hl He He1 He2.
    eapply (later_bind_gen (λ γ, FCase (subst (up γ) e1) (subst (up γ) e2)) W Θ Θ1 Θ2 Δ Δ1 Δ2 L L' F e _
              (TSum T1 a1 T2 a2) _ Hk Hs Hl); [done|done|exact He|].
    intros W' j Θv v Θ2' γ HW Hd2 HG2 Hdv HV. simpl.
    apply map_disjoint_union_r in Hdv as [Hdv1 Hdv2].
    rewrite map_union_assoc, (map_union_comm Θv (tenv_erase Θ2)), <-map_union_assoc by done.
    apply Vrel_sum_iff in HV as [(v' & -> & HV)|(v' & -> & HV)];
      pose proof (Vrel_val κ _ _ _ _ _ HV) as Hv.
    - apply (beta_det κ _ (subst (v' .: γ) e1)).
      + intros α e'' Hst. assert (head_step (Case (Inj1 v') (subst (up γ) e1) (subst (up γ) e2)) α e'')
          as Hh by head_only.
        inversion Hh; subst. split; [done|]. by rewrite subst1_subst.
      + rewrite <-(subst1_subst v' γ e1). by apply tstep_head, t_act_case_inl.
      + apply He1; [done| |].
        * apply map_disjoint_union_r. split; [by symmetry|done].
        * simpl. exists Θv, Θ2'. split_and!; [done|done| |].
          { eapply Vrel_down; [|exact HV]. lia. }
          { eapply GrelL_down; [|exact HG2]. lia. }
    - apply (beta_det κ _ (subst (v' .: γ) e2)).
      + intros α e'' Hst. assert (head_step (Case (Inj2 v') (subst (up γ) e1) (subst (up γ) e2)) α e'')
          as Hh by head_only.
        inversion Hh; subst. split; [done|]. by rewrite subst1_subst.
      + rewrite <-(subst1_subst v' γ e2). by apply tstep_head, t_act_case_inr.
      + apply He2; [done| |].
        * apply map_disjoint_union_r. split; [by symmetry|done].
        * simpl. exists Θv, Θ2'. split_and!; [done|done| |].
          { eapply Vrel_down; [|exact HV]. lia. }
          { eapply GrelL_down; [|exact HG2]. lia. }
  Qed.

  Lemma later_inj1 W Θ Δ L F e T a U b :
    sem_later κ W Θ Δ L F e T → sem_later κ W Θ Δ L F (Inj1 e) (TSum T a U b).
  Proof.
    apply (later_frame0 FInj1); [done|done|]. intros W' j Θv v _ HV.
    apply Vrel_Erel, Vrel_sum_iff. left. eauto.
  Qed.

  Lemma later_inj2 W Θ Δ L F e T a U b :
    sem_later κ W Θ Δ L F e U → sem_later κ W Θ Δ L F (Inj2 e) (TSum T a U b).
  Proof.
    apply (later_frame0 FInj2); [done|done|]. intros W' j Θv v _ HV.
    apply Vrel_Erel, Vrel_sum_iff. right. eauto.
  Qed.

  (** *** Structure *)

  Lemma later_weak W Θ Δ' Δ L F e T :
    lenv_wk Δ' Δ → sem_later κ W Θ Δ' L F e T → sem_later κ W Θ Δ L F e T.
  Proof. intros Hwk He n W' Θ' γ HW Hd HG. apply He; [done|done|]. by eapply GrelL_wk. Qed.

  Lemma later_contract W Θ Δ U aU L F e T :
    unlimited U → sem_later κ W Θ (Some (U, aU) :: Some (U, aU) :: Δ) (λ x, L (pred x)) F e T →
    sem_later κ W Θ (Some (U, aU) :: Δ) L F (rename pred e) T.
  Proof.
    intros Hu He n W' Θ' γ HW Hd HG. rewrite subst_rename.
    apply He; [done|done|]. by apply GrelL_contract.
  Qed.

  Lemma later_conv W Θ Δ L F e T T' a a' :
    tsub (ty_df T) a (ty_df T') a' → sem_later κ W Θ Δ L F e T → sem_later κ W Θ Δ L F e T'.
  Proof.
    intros Hsub He n W' Θ' γ HW Hd HG. specialize (He n W' Θ' γ HW Hd HG).
    rewrite (Erel_blind κ _ _ _ T' (ty_df T')) by (by rewrite ty_df_idem).
    rewrite (Erel_blind κ _ _ _ T (ty_df T)) in He by (by rewrite ty_df_idem).
    eapply Erel_ty_mono; [|exact He]. intros m W2 Θ2 v _ _. by apply (Vrel_tsub κ _ _ _ _ Hsub).
  Qed.

  Lemma later_pack W Θ Δ L F e lb m C T aT xs :
    length xs = m → wholds W C xs → lbx_ok W lb (ty_inst xs T) →
    sem_later κ W Θ Δ L F e (ty_inst xs T) → sem_later κ W Θ Δ L F e (TEx lb m C T aT).
  Proof.
    intros Hxs HC Hlb He n W' Θ' γ HW Hd HG. specialize (He n W' Θ' γ HW Hd HG).
    eapply Erel_ty_mono; [|exact He]. intros m' W2 Θ2 v HW2 _ HV.
    assert (W ⊑ W2) as HW02 by by eapply wext_trans.
    apply Vrel_ex_iff. split; [|exists xs; split_and!; [done|by eapply wholds_mono|done]].
    pose proof (lbx_ok_mono _ _ _ _ HW02 Hlb) as Hlb2.
    destruct lb as [| |l]; simpl in Hlb2 |- *; [|done|].
    - destruct Hlb2 as [Hh Hb]. apply senv_heads_empty_iff. apply map_empty. intros o.
      destruct (Θ2 !! o) as [[S x]|] eqn:E; [|done].
      destruct (Vrel_heads κ _ _ _ _ _ HV Hb o S x E) as (h0 & Hh0 & _). set_solver.
    - destruct Hlb2 as [Hh Hb]. intros y Hy. apply elem_of_senv_heads in Hy as (o & S & x & Ho & ->).
      destruct (Vrel_heads κ _ _ _ _ _ HV Hb o S x Ho) as (h0 & Hh0 & Hle).
      eapply w_le_trans; [by apply Hh|exact Hle].
  Qed.

  (** *** Operators *)

  Lemma later_op k W Θ Δ L F e Targ Tres :
    (∀ W' j Θv v, W ⊑ W' → Vrel κ j W' Θv Targ v → Erel κ j W' Θv Tres F (Op k v)) →
    sem_later κ W Θ Δ L F e Targ → sem_later κ W Θ Δ L F (Op k e) Tres.
  Proof. intros H. by apply (later_frame0 (FOp k)). Qed.

  Local Ltac lt_mono := intros; eapply w_lt_mono; [eassumption|]; auto.

  Lemma later_send W Θ Δ L F e S0 x m U b S ap aS :
    unfoldS S0 = SSeq (SSnd m U b) S → hbot (payload_at m U x) = false →
    (∀ y, y ∈ heads (payload_at m U x) → W ⊢ x ≺ y) → (∀ y, y ∈ F → W ⊢ x ≺ y) →
    sem_later κ W Θ Δ L F e (TProd (payload_at m U x) ap (TSess S0 x) aS) →
    sem_later κ W Θ Δ L F (ESend e) (TSess S x⁺).
  Proof.
    intros Hu Hb Hh HF. apply later_op. intros W' j Θv v HW Hv.
    eapply Erel_send; [done|done| | |exact Hv]; lt_mono.
  Qed.

  Lemma later_recv W Θ Δ L F e S0 x m U b S b' a' :
    unfoldS S0 = SSeq (SRcv m U b) S → (∀ y, y ∈ F → W ⊢ x ≺ y) →
    sem_later κ W Θ Δ L F e (TSess S0 x) →
    sem_later κ W Θ Δ L F (ERecv e) (TProd (payload_at m U x) b' (TSess S x⁺) a').
  Proof.
    intros Hu HF. apply later_op. intros W' j Θv v HW Hv.
    eapply Erel_recv; [done| |exact Hv]; lt_mono.
  Qed.

  Lemma later_close W Θ Δ L F e S0 x :
    unfoldS S0 = SEnd → (∀ y, y ∈ F → W ⊢ x ≺ y) →
    sem_later κ W Θ Δ L F e (TSess S0 x) → sem_later κ W Θ Δ L F (EClose e) TUnit.
  Proof.
    intros Hu HF. apply later_op. intros W' j Θv v HW Hv.
    eapply Erel_close; [done| |exact Hv]; lt_mono.
  Qed.

  Lemma later_select (i : bool) W Θ Δ L F e S0 x S1 S2 :
    unfoldS S0 = SPlus S1 S2 → (∀ y, y ∈ F → W ⊢ x ≺ y) →
    sem_later κ W Θ Δ L F e (TSess S0 x) →
    sem_later κ W Θ Δ L F (ESel i e) (TSess (if i then S2 else S1) (sel_pt x i)).
  Proof.
    intros Hu HF. apply later_op. intros W' j Θv v HW Hv.
    eapply Erel_select; [done| |exact Hv]; lt_mono.
  Qed.

  Lemma later_branch W Θ Δ L F e S0 x S1 S2 a1 a2 :
    unfoldS S0 = SWith S1 S2 → (∀ y, y ∈ F → W ⊢ x ≺ y) →
    sem_later κ W Θ Δ L F e (TSess S0 x) →
    sem_later κ W Θ Δ L F (EBra e) (TSum (TSess S1 (bra_pt x false)) a1 (TSess S2 (bra_pt x true)) a2).
  Proof.
    intros Hu HF. apply later_op. intros W' j Θv v HW Hv.
    eapply Erel_branch; [done| |exact Hv]; lt_mono.
  Qed.

  Lemma later_link W Θ Δ L F e S x a1 a2 :
    sem_later κ W Θ Δ L F e (TProd (TSess S x) a1 (TSess (dual S) x‾) a2) →
    sem_later κ W Θ Δ L F (ELink e) TUnit.
  Proof. apply later_op. intros W' j Θv v HW Hv. by eapply Erel_link. Qed.

  Lemma later_spawn W Θ Δ L F e ub lb c t h a1 aU :
    sem_later κ W Θ Δ L F e (TLolli ub lb c t h TUnit a1 TUnit aU) →
    sem_later κ W Θ Δ L F (ESpawn e) TUnit.
  Proof. apply later_op. intros W' j Θv v HW Hv. by eapply Erel_spawn. Qed.

  Lemma later_new_at (κf : field) W Θ Δ L F e S0 x S a a1 a2 a3 :
    sem_later κ W Θ Δ L F e (TSess S0 x) →
    sem_later κ W Θ Δ L F (ENewAt κf e)
      (TProd (TSess S0 x) a (TProd (TSess S (x·κf)) a1 (TSess (dual S) (x·κf)‾) a2) a3).
  Proof. apply later_op. intros W' j Θv v HW Hv. by eapply Erel_new_at. Qed.

  Lemma later_force W Θ Δ L F e m kk C ub c t U a xs ss :
    length xs = m → length ss = kk → Forall hcontractive ss → wholds W C xs →
    ub_lt W (pt_inst (plist xs) <$> ub) F →
    sem_later κ W Θ Δ L F e (TBox m kk C ub c t U a) →
    sem_later κ W Θ Δ L F (EForce e) (sinst_ty (slist ss) (ty_inst xs U)).
  Proof.
    intros Hxs Hss Hsc HC Hub. apply later_op. intros W' j Θv v HW Hv.
    pose proof Hv as Hv'. apply Vrel_box_iff in Hv' as [-> _].
    eapply Erel_force; [done|done|done| | |exact Hv].
    - by eapply wholds_mono.
    - by eapply ub_lt_mono.
  Qed.

  Lemma later_spawn_lam W Θ Δ L F e a1 :
    tfacts Θ Δ (Lam e) →
    (∀ W1, W ⊑ W1 → sem_later κ W1 Θ (Some (TUnit, a1) :: Δ) (false .: L) ∅ e TUnit) →
    sem_later κ W Θ Δ L F (ESpawn (Lam e)) TUnit.
  Proof.
    intros Htf Hbody n W' Θ' γ HW Hd HG. simpl. apply Erel_spawn_thunk; [done|].
    intros W1 HW1. exists (subst (up γ) e). split_and!.
    - done.
    - pose proof (GrelL_fends κ _ _ _ _ _ _ _ _ Htf HG) as Hx. simpl in Hx.
      by rewrite Hx, dom_union_L, dom_tenv_erase.
    - intros W'' j Θ'' w HW'' Hj Hd''.
      assert (Θ'' = ∅ ∧ w = EUnit → Erel κ j W'' ((tenv_erase Θ ∪ Θ') ∪ Θ'') TUnit ∅
                (subst1 w (subst (up γ) e))) as Hcase.
      { intros [-> ->]. rewrite map_union_empty, subst1_subst.
        rewrite <-(map_empty_union Θ') at 1.
        apply (Hbody W'' (wext_trans _ _ _ HW (wext_trans _ _ _ HW1 HW'')) j W'' (∅ ∪ Θ') (EUnit .: γ)
                 (wext_refl _)); [by rewrite map_empty_union|].
        simpl. exists ∅, Θ'. split_and!; [apply map_disjoint_empty_l|done|by apply Vrel_unit_iff|].
        eapply GrelL_down; [|eapply GrelL_mono; [eapply wext_trans; [exact HW1|exact HW'']|exact HG]]. lia. }
      split.
      + intros _ Hw. apply Hcase. by apply Vrel_unit_iff in Hw.
      + intros -> Hw. by apply Hcase.
  Qed.
End later.

