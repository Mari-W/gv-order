(** * A thread that computes its own flag (semantic examples)

    The component computes a flag by negating inj₂ ∗ and orders two
    channels c and d by it.

      not   = λz. case z of inl w ⇒ inj₂ w | inr w ⇒ inj₁ w
      sf    = case not (inj₂ ∗) of inl _ ⇒ close c; close d
                                 | inr _ ⇒ close d; close c

    The flag is always inj₁ ∗, so every run closes c first. Both arms
    discard their payload.

    - [sf_underivable] : sf has no [styped] derivation in a plain
      context that holds c and d, under hypotheses whose order is
      irreflexive. E-Case types both arms under one Ψ. The first arm
      asks x ≺ y for the points x of c and y of d, the second asks
      y ≺ x. An arm that never mentions its payload can only bind it at
      an unlimited type (relevance, [typed_term_wf_s]). An unlimited
      type is a box, and a box has nothing to open, so the dead arm
      learns no fact. [sf_underivable_top] instantiates the theorem at
      the hypotheses a source program starts with.

    - [sf_sem_typed] : the same open term, in the context c : Close@x,
      d : Close@y, is semantically typed in every strict world with
      x ≺ y. The proof runs the two β-steps of the flag and the β-step
      of the case ([sem_typed_det_beta]) and ends in the first arm, which
      the static system types.

    - [sf_deadlock_free] : the configuration of the thread sf, with c
      and d as channel constants, and the partner close c; close d on
      the other ends, is deadlock free. The partner is typed by the
      static system, the thread by [sf_sem_typed], and P-Connect joins
      them in a mixed derivation ([mixed_soundness], static/Mixed.v).

    END POINTS. The gates now compare with partner points: the first
    arm asks x ≺ ȳ, the second y ≺ x̄, and the partner, which holds the
    other ends at x̄ and ȳ, asks x̄ ≺ y. The two arms no longer form a
    cycle, so the last step of [sf_underivable] fails and the theorem
    and its corollary are commented out (open, see the report of the
    end-points port). The closed configuration still needs y ≺ x̄ for
    the dead arm and x̄ ≺ y for the partner, a cycle. The semantic part
    is ported: [sf_sem_typed] and [sf_thread_sem] assume x ≺ ȳ, and
    [sf_mixed] assumes x ≺ ȳ and x̄ ≺ y, which [sf_W] provides. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.ChoiceNegative examples.DataBranch static.Mixed.
From LRGV Require Import static.SourceRules.

Set Default Proof Using "All".

(** ** The program *)

Definition sf_not : expr := Lam (Case (Var 0) (Inj2 (Var 0)) (Inj1 (Var 0))).
Definition sf_flag : expr := App sf_not (Inj2 EUnit).

(** close i; close j *)
Definition sf_arm (i j : nat) : expr := LetU (App EClos (Var i)) (App EClos (Var j)).

(** The component with c at i and d at j. Inside an arm the payload is
    variable 0, so c and d are S i and S j. *)
Definition sf_body (i j : nat) : expr :=
  Case sf_flag (sf_arm (S i) (S j)) (sf_arm (S j) (S i)).

(** ** Underivability

    [plainb]: every binding is unlimited or not an existential. E-Open
    cannot fire in such a context, and E-Weak, E-Contract and the
    splits of the rules keep it. *)

Definition plainb (Δ : lenv) : Prop :=
  ∀ k U, Δ !! k = Some (Some U) → unlimited U ∨ ¬ is_ex U.

Lemma plain_plainb Δ : plain Δ → plainb Δ.
Proof. intros H k U Hk. right. apply (H k U Hk). Qed.

Lemma plainb_split Δ Δ1 Δ2 : lenv_split Δ Δ1 Δ2 → plainb Δ → plainb Δ1 ∧ plainb Δ2.
Proof.
  intros Hs H. split; intros k U Hk; apply (H k).
  - by eapply lenv_split_lookup_l.
  - by eapply lenv_split_lookup_r.
Qed.

Lemma wk_lookup_some Δ' Δ k U : lenv_wk Δ' Δ → Δ' !! k = Some (Some U) → Δ !! k = Some (Some U).
Proof.
  intros Hw. revert k. induction Hw as [|o Δ' Δ Hw IH|V Δ' Δ Hu Hw IH]; intros [|k] Hk;
    simpl in *; try done; by apply IH.
Qed.

Lemma wk_lookup_lin Δ' Δ k U :
  lenv_wk Δ' Δ → Δ !! k = Some (Some U) → ¬ unlimited U → Δ' !! k = Some (Some U).
Proof.
  intros Hw. revert k. induction Hw as [|o Δ' Δ Hw IH|V Δ' Δ Hu Hw IH]; intros [|k] Hk Hn;
    simpl in *; try done.
  - by apply IH.
  - injection Hk as <-. by exfalso.
  - by apply IH.
Qed.

Lemma plainb_wk Δ' Δ : lenv_wk Δ' Δ → plainb Δ → plainb Δ'.
Proof. intros Hw H k U Hk. apply (H k). by eapply wk_lookup_some. Qed.

Lemma plainb_contract U Δ : plainb (Some U :: Δ) → plainb (Some U :: Some U :: Δ).
Proof. intros H [|k] V Hk; [by apply (H 0)|]. by apply (H k). Qed.

Lemma plainb_open Δ i lb m C T : plainb Δ → Δ !! i = Some (Some (TEx lb m C T)) → False.
Proof. intros H Hi. destruct (H i _ Hi) as [Hu|Hn]; [done|by apply Hn]. Qed.

Lemma unlimited_dec U : unlimited U ∨ ¬ unlimited U.
Proof. destruct U; simpl; tauto. Qed.

(** The linear bindings of Δ sit at i only. *)
Definition lin_only (Δ : lenv) (i : nat) : Prop :=
  ∀ y W, Δ !! y = Some (Some W) → ¬ unlimited W → y = i.

Lemma wk_transfer Δ' Δ i V :
  lenv_wk Δ' Δ → Δ' !! i = Some (Some V) → lin_only Δ' i →
  Δ !! i = Some (Some V) ∧ lin_only Δ i.
Proof.
  intros Hw Hi Ho. split; [by eapply wk_lookup_some|].
  intros y W Hy Hn. apply (Ho y W); [by eapply wk_lookup_lin|done].
Qed.

Lemma contract_transfer U Δ i V :
  unlimited U →
  (Some U :: Some U :: Δ) !! i = Some (Some V) → lin_only (Some U :: Some U :: Δ) i →
  (Some U :: Δ) !! pred i = Some (Some V) ∧ lin_only (Some U :: Δ) (pred i).
Proof.
  intros Hu Hi Ho. split.
  - destruct i as [|[|i]]; simpl in *; done.
  - intros [|y] W Hy Hn; simpl in Hy.
    + injection Hy as <-. by exfalso.
    + rewrite <-(Ho (S (S y)) W Hy Hn). done.
Qed.

Lemma rename_pred_var e i : rename pred e = Var i → ∃ i', e = Var i' ∧ pred i' = i.
Proof. destruct e; simpl; try discriminate. intros [= <-]. by eexists. Qed.

Lemma rename_pred_konst e k : rename pred e = Konst k → e = Konst k.
Proof. destruct e; simpl; try discriminate. by intros [= ->]. Qed.

Lemma rename_pred_kv e k i :
  rename pred e = App (Konst k) (Var i) → ∃ i', e = App (Konst k) (Var i') ∧ pred i' = i.
Proof.
  destruct e as [| | | | |e1 e2| | | | | | |]; simpl; try discriminate. intros [= H1 H2].
  apply rename_pred_konst in H1 as ->. apply rename_pred_var in H2 as (i' & -> & <-).
  by eexists.
Qed.

Lemma rename_pred_arm e i j :
  rename pred e = sf_arm i j →
  ∃ i' j', e = sf_arm i' j' ∧ pred i' = i ∧ pred j' = j.
Proof.
  destruct e as [| | | | | | |e1 e2| | | | |]; simpl; try discriminate. intros [= H1 H2].
  apply rename_pred_kv in H1 as (i' & -> & <-). apply rename_pred_kv in H2 as (j' & -> & <-).
  by eexists _, _.
Qed.

(** A constant: every binding is unlimited. *)
Lemma konst_inv Φ Ψ Δ F e T :
  sderiv Φ Ψ Δ F e T → ∀ k, e = Konst k → plainb Δ →
  (∃ K, konst_ty (heqs Ψ) (hlt Ψ) (hyp_known Ψ) k K ∧ (hsteq Ψ K T ∨ is_ex T)) ∧
  (∀ y W, Δ !! y = Some (Some W) → unlimited W).
Proof.
  induction 1 as [| Φ Ψ Δ F k0 T HΔ Hk _ | | | | | | | | | |
                 | Φ Ψ Δ' Δ F e T Hw H IH | Φ Ψ Δ U F e T Hu H IH
                 | Φ Ψ Δ F e T T' Hq H IH | Φ Ψ Δ F e lb m C T xs _ _ _ _ H IH
                 | Φ Ψ Δ F e i lb m C T U Hi _ H IH ];
    intros kq Ek Hp; try discriminate.
  - injection Ek as ->. split; [exists T; split; [done|left; apply hsteq_refl]|].
    intros y W Hy. exfalso. apply list_elem_of_lookup_2, HΔ in Hy. discriminate.
  - destruct (IH kq Ek (plainb_wk _ _ Hw Hp)) as [HK Hall]. split; [done|].
    intros y W Hy. destruct (unlimited_dec W) as [?|Hn]; [done|].
    apply (Hall y). by eapply wk_lookup_lin.
  - apply rename_pred_konst in Ek as ->.
    destruct (IH kq eq_refl (plainb_contract _ _ Hp)) as [HK Hall]. split; [done|].
    intros [|y] W Hy; simpl in Hy; [injection Hy as <-; done|]. by apply (Hall (S (S y))).
  - destruct (IH kq Ek Hp) as [(K & HK & HT) Hall]. split; [|done].
    exists K. split; [done|]. destruct HT as [HT|HT]; [left; by eapply hsteq_trans|right; by eapply hsteq_ex].
  - destruct (IH kq Ek Hp) as [(K & HK & _) Hall]. split; [|done]. exists K. split; [done|by right].
  - exfalso. by eapply plainb_open.
Qed.

(** A variable: the variable is the only linear binding. *)
Lemma var_inv Φ Ψ Δ F e T :
  sderiv Φ Ψ Δ F e T → ∀ i, e = Var i → plainb Δ →
  ∃ V, Δ !! i = Some (Some V) ∧ (hsteq Ψ V T ∨ is_ex T) ∧ lin_only Δ i.
Proof.
  induction 1 as [| | Φ Ψ Δ F x T Ho | | | | | | | | |
                 | Φ Ψ Δ' Δ F e T Hw H IH | Φ Ψ Δ U F e T Hu H IH
                 | Φ Ψ Δ F e T T' Hq H IH | Φ Ψ Δ F e lb m C T xs _ _ _ _ H IH
                 | Φ Ψ Δ F e i lb m C T U Hi _ H IH ];
    intros i0 Ei Hp; try discriminate.
  - injection Ei as ->. destruct Ho as [Hx Ho]. exists T. split_and!; [done|left; apply hsteq_refl|].
    intros y W Hy _. by destruct (Ho y W Hy).
  - destruct (IH i0 Ei (plainb_wk _ _ Hw Hp)) as (V & HV & HT & Ho).
    destruct (wk_transfer _ _ _ _ Hw HV Ho) as [HV' Ho']. eauto.
  - destruct (rename_pred_var _ _ Ei) as (i' & -> & <-).
    destruct (IH i' eq_refl (plainb_contract _ _ Hp)) as (V & HV & HT & Ho).
    destruct (contract_transfer _ _ _ _ Hu HV Ho) as [HV' Ho']. eauto.
  - destruct (IH i0 Ei Hp) as (V & HV & HT & Ho). exists V. split_and!; [done| |done].
    destruct HT as [HT|HT]; [left; by eapply hsteq_trans|right; by eapply hsteq_ex].
  - destruct (IH i0 Ei Hp) as (V & HV & _ & Ho). exists V. split_and!; [done|by right|done].
  - exfalso. by eapply plainb_open.
Qed.

(** A constant applied to a variable. *)
Lemma kv_inv Φ Ψ Δ F e T :
  sderiv Φ Ψ Δ F e T → ∀ k i, e = App (Konst k) (Var i) → plainb Δ →
  ∃ ub lb A U K V,
    hub_below_s Ψ Φ ub F ∧
    konst_ty (heqs Ψ) (hlt Ψ) (hyp_known Ψ) k K ∧ hsteq Ψ K (TLolli ub lb A U) ∧
    Δ !! i = Some (Some V) ∧ (hsteq Ψ V A ∨ is_ex A) ∧ lin_only Δ i.
Proof.
  induction 1 as [| | | | Φ Ψ Δ Δ1 Δ2 F e1 e2 ub lb T U Hs Hub H1 _ H2 _ | | | | | | |
                 | Φ Ψ Δ' Δ F e T Hw H IH | Φ Ψ Δ U F e T Hu H IH
                 | Φ Ψ Δ F e T T' Hq H IH | Φ Ψ Δ F e lb m C T xs _ _ _ _ H IH
                 | Φ Ψ Δ F e i lb m C T U Hi _ H IH ];
    intros kq i0 Ei Hp; try discriminate.
  - injection Ei as -> ->. destruct (plainb_split _ _ _ Hs Hp) as [Hp1 Hp2].
    destruct (konst_inv _ _ _ _ _ _ H1 kq eq_refl Hp1) as [(K & HK & HKT) Hall].
    destruct HKT as [HKT|[]].
    destruct (var_inv _ _ _ _ _ _ H2 i0 eq_refl Hp2) as (V & HV & HVT & Ho).
    exists ub, lb, T, U, K, V. split_and!; [done|done|done| |done|].
    + by eapply lenv_split_lookup_r.
    + intros y W Hy Hn. destruct (lenv_split_lookup_inv _ _ _ _ _ Hs Hy) as [Hy1|Hy2].
      * exfalso. by apply Hn, (Hall y).
      * by apply (Ho y W).
  - destruct (IH kq i0 Ei (plainb_wk _ _ Hw Hp)) as (ub & lb & A & U & K & V & Hub & HK & HKA & HV & HVA & Ho).
    destruct (wk_transfer _ _ _ _ Hw HV Ho) as [HV' Ho'].
    exists ub, lb, A, U, K, V. by split_and!.
  - destruct (rename_pred_kv _ _ _ Ei) as (i' & -> & <-).
    destruct (IH kq i' eq_refl (plainb_contract _ _ Hp))
      as (ub & lb & A & U' & K & V & Hub & HK & HKA & HV & HVA & Ho).
    destruct (contract_transfer _ _ _ _ Hu HV Ho) as [HV' Ho'].
    exists ub, lb, A, U', K, V. by split_and!.
  - by apply (IH kq i0 Ei Hp).
  - by apply (IH kq i0 Ei Hp).
  - exfalso. by eapply plainb_open.
Qed.

Lemma hsteq_sess_inv Ψ s x A : hsteq Ψ (TSess s x) A → ∃ s' x', A = TSess s' x' ∧ heqs Ψ x x'.
Proof. destruct A; simpl; try done. intros [Hx _]. by eexists _, _. Qed.

(** close i; close j holding i at x and j at y asks x ≺ ȳ, the partner
    point of j (end points). *)
Lemma arm_inv Φ Ψ Δ F e T :
  sderiv Φ Ψ Δ F e T → ∀ i j, e = sf_arm i j → plainb Δ → ∀ s1 x s2 y,
  Δ !! i = Some (Some (TSess s1 x)) → Δ !! j = Some (Some (TSess s2 y)) → i ≠ j →
  hlt Ψ x (pt_dual y).
Proof.
  induction 1 as [| | | | | | Φ Ψ Δ Δ1 Δ2 F e1 e2 T Hs H1 _ H2 _ | | | | |
                 | Φ Ψ Δ' Δ F e T Hw H IH | Φ Ψ Δ U F e T Hu H IH
                 | Φ Ψ Δ F e T T' Hq H IH | Φ Ψ Δ F e lb m C T xs _ _ _ _ H IH
                 | Φ Ψ Δ F e i lb m C T U Hi _ H IH ];
    intros i0 j0 Ee Hp sq1 xq sq2 yq Hi0 Hj0 Hij; try discriminate.
  - injection Ee as -> ->. destruct (plainb_split _ _ _ Hs Hp) as [Hp1 Hp2].
    destruct (kv_inv _ _ _ _ _ _ H1 KClos i0 eq_refl Hp1)
      as (ub & lb & A & U & K & V & Hub & HK & HKA & HV & HVA & Ho).
    destruct (clos_shape _ _ HK) as (xc & ->).
    destruct ub as [xc'|]; cbn [hsteq opt_rel] in HKA; [|by destruct HKA].
    destruct HKA as (Hxc & _ & HA & _).
    destruct (hsteq_sess_inv _ _ _ _ HA) as (s & w & -> & Hxw).
    rewrite (lenv_split_lookup_l _ _ _ _ _ Hs HV) in Hi0. injection Hi0 as ->.
    destruct HVA as [HVA|[]]. destruct HVA as [Hxw' _].
    assert (Δ2 !! j0 = Some (Some (TSess sq2 yq))) as Hj2.
    { destruct (lenv_split_lookup_inv _ _ _ _ _ Hs Hj0) as [Hj1|Hj2]; [|done].
      exfalso. apply Hij. symmetry. apply (Ho j0 _ Hj1). intros []. }
    assert (hlt Ψ xc' (pt_dual yq)) as Hlt.
    { eapply hub_fact; [exact Hub|]. apply sf_unionb_fst.
      eapply lenv_heads_lookup; [exact Hj2|]. simpl. set_solver. }
    eapply hlt_eqs; [|apply he_refl|exact Hlt].
    eapply he_trans; [exact Hxw'|]. eapply he_trans; [apply he_sym, Hxw|exact Hxc].
  - eapply IH; [done|by eapply plainb_wk| | |done].
    + eapply wk_lookup_lin; [exact Hw|exact Hi0|intros []].
    + eapply wk_lookup_lin; [exact Hw|exact Hj0|intros []].
  - destruct (rename_pred_arm _ _ _ Ee) as (i' & j' & -> & Ei & Ej).
    assert (i0 ≠ 0) as Hi0n by (intros ->; simpl in Hi0; injection Hi0 as ->; done).
    assert (j0 ≠ 0) as Hj0n by (intros ->; simpl in Hj0; injection Hj0 as ->; done).
    destruct i' as [|[|i']]; [simpl in Ei; lia|simpl in Ei; lia|].
    destruct j' as [|[|j']]; [simpl in Ej; lia|simpl in Ej; lia|].
    simpl in Ei, Ej. subst i0 j0.
    eapply (IH (S (S i')) (S (S j'))); [done|by apply plainb_contract|..]; simpl; [done|done|lia].
  - eapply IH; done.
  - eapply IH; done.
  - exfalso. by eapply plainb_open.
Qed.

Lemma freevar_flag x : ¬ freevar x sf_flag.
Proof. simpl. lia. Qed.

(** A source derivation is a derivation of [typed] at Θ = ∅, so it
    satisfies relevance. *)
Lemma styped_relevant Φ Ψ Δ F e T x :
  styped Φ Ψ Δ F e T → lenv_avail_lin Δ x → freevar x e.
Proof. intros H Hx. apply (typed_term_wf_s _ _ _ _ _ _ _ _ H). done. Qed.

(** An arm that discards its payload binds it at an unlimited type, so
    its context is [plainb]. *)
Lemma arm_ctx Φ Ψ Δ F T1 T i j :
  plain Δ → styped Φ Ψ (Some T1 :: Δ) F (sf_arm (S i) (S j)) T → plainb (Some T1 :: Δ).
Proof.
  intros Hp H [|k] U Hk; simpl in Hk; [|right; apply (Hp k U Hk)].
  injection Hk as <-.
  destruct T1 as [| | | | | |lb m C T1]; try (left; exact I); try (right; intros []; done).
  exfalso. assert (freevar 0 (sf_arm (S i) (S j))) as Hf.
  { eapply styped_relevant; [exact H|]. exists (TEx lb m C T1). split; [done|intros []]. }
  simpl in Hf. lia.
Qed.

Lemma split_off_flag Φ Ψ Δ Δ1 Δ2 F T i U :
  lenv_split Δ Δ1 Δ2 → styped Φ Ψ Δ1 F sf_flag T →
  Δ !! i = Some (Some U) → ¬ unlimited U → Δ2 !! i = Some (Some U).
Proof.
  intros Hs H Hi Hn. destruct (lenv_split_lookup_inv _ _ _ _ _ Hs Hi) as [H1|H2]; [|done].
  exfalso. apply (freevar_flag i). eapply styped_relevant; [exact H|]. by exists U.
Qed.

(* END POINTS: open, see report.
Theorem sf_underivable Φ Ψ Δ F T i j s1 x s2 y :
  (∀ p, ¬ hlt Ψ p p) → plain Δ →
  Δ !! i = Some (Some (TSess s1 x)) → Δ !! j = Some (Some (TSess s2 y)) → i ≠ j →
  ¬ styped Φ Ψ Δ F (sf_body i j) T.
Proof.
  intros Hacy Hp Hi Hj Hij H. unfold sf_body in H.
  destruct (inv_case _ _ _ _ _ _ _ _ H Hp) as (Δ1 & Δ2 & T1 & T2 & T0 & Hs & Hf & Ha1 & Ha2).
  destruct (plain_split _ _ _ Hs Hp) as [_ Hp2].
  pose proof (split_off_flag _ _ _ _ _ _ _ _ _ Hs Hf Hi ltac:(intros [])) as Hi2.
  pose proof (split_off_flag _ _ _ _ _ _ _ _ _ Hs Hf Hj ltac:(intros [])) as Hj2.
  pose proof (arm_ctx _ _ _ _ _ _ _ _ Hp2 Ha1) as Hb1.
  pose proof (arm_ctx _ _ _ _ _ _ _ _ Hp2 Ha2) as Hb2.
  pose proof (arm_inv _ _ _ _ _ _ (styped_sderiv _ _ _ _ _ _ Ha1) (S i) (S j) eq_refl Hb1
                s1 x s2 y Hi2 Hj2 ltac:(lia)) as Hxy.
  pose proof (arm_inv _ _ _ _ _ _ (styped_sderiv _ _ _ _ _ _ Ha2) (S j) (S i) eq_refl Hb2
                s2 y s1 x Hj2 Hi2 ltac:(lia)) as Hyx.
  apply (Hacy x). by eapply hlt_trans.
Qed.

(** A source program starts under an acyclic constraint C₀ over n
    point variables, the hypotheses [soundness_source] accepts. *)
Corollary sf_underivable_top n C Φ Δ F T i j s1 x s2 y :
  c0_acyclic n C → plain Δ →
  Δ !! i = Some (Some (TSess s1 x)) → Δ !! j = Some (Some (TSess s2 y)) → i ≠ j →
  ¬ styped Φ [(C, ids n)] Δ F (sf_body i j) T.
Proof. intros HC. apply sf_underivable. by apply c0_irrefl. Qed.
*)

(** ** Semantic typing

    A term that takes a deterministic β-step to a semantically typed
    term is semantically typed ([Erel_det_beta]). *)

Definition det_beta (e e' : expr) : Prop :=
  tstep e LBeta e' ∧ ∀ α e'', tstep e α e'' → α = LBeta ∧ e'' = e'.

Lemma sem_typed_det_beta W Θ Δ F e e' T :
  (∀ γ, det_beta (subst γ e) (subst γ e')) →
  sem_typed W Θ Δ F e' T → sem_typed W Θ Δ F e T.
Proof.
  intros Hd He n W' Θ' Θ'' γ HW Hc Hg. destruct (Hd γ) as [Hs Hdet].
  eapply Erel_det_beta; [exact Hs|exact Hdet|]. by apply (He n W' Θ' Θ'' γ).
Qed.

Lemma det_beta_case e e' a b : det_beta e e' → det_beta (Case e a b) (Case e' a b).
Proof.
  intros [Hs Hd]. split; [by apply TStepCase|].
  intros α e'' H. apply tstep_case_inv in H as [(f & Hf & ->)|[(v & -> & Hv & _)|(v & -> & Hv & _)]].
  - by destruct (Hd _ _ Hf) as [-> ->].
  - exfalso. eapply val_no_tstep; [exact Hs|exact Hv].
  - exfalso. eapply val_no_tstep; [exact Hs|exact Hv].
Qed.

Lemma det_beta_app_lam e v e' : is_val v → e' = subst1 v e → det_beta (App (Lam e) v) e'.
Proof.
  intros Hv ->. split; [by apply TStepHead, HeadApp|].
  intros α e'' H. apply app_val_step in H; [|done|done]. by inversion H; subst.
Qed.

Lemma det_beta_case1 v a b e' : is_val v → e' = subst1 v a → det_beta (Case (Inj1 v) a b) e'.
Proof.
  intros Hv ->. split; [by apply TStepHead, HeadCase1|].
  intros α e'' H. apply tstep_case_inv in H as [(f & Hf & _)|[(u & Hu & _ & -> & ->)|(u & Hu & _)]].
  - exfalso. by eapply val_no_tstep.
  - by injection Hu as ->.
  - done.
Qed.

Lemma det_beta_case2 v a b e' : is_val v → e' = subst1 v b → det_beta (Case (Inj2 v) a b) e'.
Proof.
  intros Hv ->. split; [by apply TStepHead, HeadCase2|].
  intros α e'' H. apply tstep_case_inv in H as [(f & Hf & _)|[(u & Hu & _)|(u & Hu & _ & -> & ->)]].
  - exfalso. by eapply val_no_tstep.
  - done.
  - by injection Hu as ->.
Qed.

(** The context of the component: c : Close@x at 0, d : Close@y at 1. *)
Definition sf_ctx (x y : point) : lenv := [Some (TSess SEnd x); Some (TSess SEnd y)].

(** The first arm is typed by the static system when x ≺ ȳ (end points). *)
Lemma sf_arm_typed W x y :
  world_wf W → w_lt W x (pt_dual y) → typed W ∅ [] ∅ (sf_ctx x y) (∅, None) (sf_arm 0 1) TUnit.
Proof.
  intros HW Hxy. unfold sf_arm, sf_ctx.
  apply tv_letu; [exact HW|reflexivity| |].
  - eapply (tv_appk W HW _ _ _ _ _ _ (Some x) (TSess SEnd x)).
    + apply tv_var; [exact HW|done|reflexivity].
    + apply KTClos.
    + done.
    + apply ubs_intro; [|done]. intros z Hz. mem_cases Hz. by apply sl_w.
  - eapply (tv_appk W HW _ _ _ _ _ _ (Some y) (TSess SEnd y)).
    + apply tv_var; [exact HW|done|reflexivity].
    + apply KTClos.
    + done.
    + apply ubs_intro; [|done]. intros z Hz. mem_cases Hz.
Qed.

Lemma sf_arm_sem W x y :
  strict W → w_lt W x (pt_dual y) → sem_typed W ∅ (sf_ctx x y) ∅ (sf_arm 0 1) TUnit.
Proof. intros HW Hxy. apply fundamental; [|done]. by apply sf_arm_typed; [apply HW|]. Qed.

(** The component is semantically typed: the flag reduces to inj₁ ∗ in
    two β-steps, and a third step takes the first arm. *)
Theorem sf_sem_typed W x y :
  strict W → w_lt W x (pt_dual y) → sem_typed W ∅ (sf_ctx x y) ∅ (sf_body 0 1) TUnit.
Proof.
  intros HW Hxy.
  apply (sem_typed_det_beta _ _ _ _ _
           (Case (Case (Inj2 EUnit) (Inj2 (Var 0)) (Inj1 (Var 0))) (sf_arm 1 2) (sf_arm 2 1))).
  { intros γ. apply det_beta_case, det_beta_app_lam; done. }
  apply (sem_typed_det_beta _ _ _ _ _ (Case (Inj1 EUnit) (sf_arm 1 2) (sf_arm 2 1))).
  { intros γ. apply det_beta_case, det_beta_case2; done. }
  apply (sem_typed_det_beta _ _ _ _ _ (sf_arm 0 1)); [|by apply sf_arm_sem].
  intros γ. apply det_beta_case1; [done|]. cbn [subst]. rewrite subst1_subst. done.
Qed.

(** ** The closed configuration

    The thread holds c and d as channel constants, c at x and d at y.
    The partner holds the other ends and closes c, then d. *)

Definition sf_thread : expr := Case sf_flag (cc2 chc chd) (cc2 chd chc).

Definition sf_γ : nat → expr := Chan chc .: Chan chd .: Var.

Lemma sf_thread_subst : subst sf_γ (sf_body 0 1) = sf_thread.
Proof. reflexivity. Qed.

Lemma sf_ground n W x y :
  world_wf W → grounding n W (db_Θ x y) (sf_ctx x y) sf_γ.
Proof.
  intros HW. cbn [grounding sf_ctx].
  exists {[chc := One (SEnd, x)]}, {[chd := One (SEnd, y)]}. split.
  { apply comp_comm; [apply (wf_rdsym _ HW)|apply db_comp_cd]. }
  split.
  { apply Vrel_sess_iff. eexists _, _, _. split_and!; [done|done|apply seq_refl|apply (wf_eq_refl _ HW)]. }
  exists {[chd := One (SEnd, y)]}, ∅. split; [apply tenv_comp_empty_r|]. split.
  { apply Vrel_sess_iff. eexists _, _, _. split_and!; [done|done|apply seq_refl|apply (wf_eq_refl _ HW)]. }
  done.
Qed.

Lemma sf_thread_closed γ : subst γ sf_thread = sf_thread.
Proof. reflexivity. Qed.

Theorem sf_thread_sem W x y :
  strict W → w_lt W x (pt_dual y) → sem_typed W (db_Θ x y) [] ∅ sf_thread TUnit.
Proof.
  intros HW Hxy n W' Θ' Θ'' γ HW' Hc Hg. cbn [grounding] in Hg. subst Θ'.
  apply tenv_comp_empty_r_inv in Hc as ->. rewrite sf_thread_closed, <-sf_thread_subst.
  apply (sf_sem_typed W x y HW Hxy n W' (db_Θ x y) (db_Θ x y) sf_γ HW').
  - apply tenv_comp_empty_l, (wf_rdsym _ (proj1 (proj2 (proj2 (proj2 HW'))))).
  - apply sf_ground, (proj1 (proj2 (proj2 (proj2 HW')))).
Qed.

(** The partner close c; close d is typed by the static system. It
    holds c at x̄ and d at ȳ (end points), so it asks x̄ ≺ y. The lemma
    below is stated for any two points. *)
Lemma tenv_heads_one c e : tenv_heads {[c := One e]} = {[pt_dual e.2]}.
Proof. unfold tenv_heads. rewrite map_fold_singleton. simpl. set_solver. Qed.

Lemma cc2_typed W x y :
  world_wf W → w_lt W x (pt_dual y) → typed W ∅ [] (db_Θ x y) [] (∅, None) (cc2 chc chd) TUnit.
Proof.
  intros HW Hxy. unfold cc2.
  eapply (t_letstar W ∅ [] (db_Θ x y) {[chc := One (SEnd, x)]} {[chd := One (SEnd, y)]}
            [] [] []).
  - apply comp_comm; [apply se_dsym|apply db_comp_cd].
  - constructor.
  - eapply (t_app W ∅ [] _ ∅ {[chc := One (SEnd, x)]} [] [] [] _ _ _ (Some x) None (TSess SEnd x)).
    + apply tenv_comp_empty_l, se_dsym.
    + constructor.
    + apply ubs_intro; [|done]. intros z Hz. rewrite tenv_heads_one in Hz. mem_cases Hz.
      by apply sl_w.
    + apply t_const; [intros o Ho; by apply elem_of_nil in Ho|apply KTClos|done].
    + apply t_ch; [intros o Ho; by apply elem_of_nil in Ho|apply seq_refl|apply se_refl].
  - eapply (t_app W ∅ [] _ ∅ {[chd := One (SEnd, y)]} [] [] [] _ _ _ (Some y) None (TSess SEnd y)).
    + apply tenv_comp_empty_l, se_dsym.
    + constructor.
    + apply ubs_intro; [|done]. intros z Hz. mem_cases Hz.
    + apply t_const; [intros o Ho; by apply elem_of_nil in Ho|apply KTClos|done].
    + apply t_ch; [intros o Ho; by apply elem_of_nil in Ho|apply seq_refl|apply se_refl].
Qed.

(** The interface of each side: c at x and d at y, both Close. *)
Definition sf_Σ (x y : point) : senv := <[chd := (SEnd, y)]> {[chc := (SEnd, x)]}.

Lemma sf_Σ_tenv x y : tenv_of (sf_Σ x y) ∪ ∅ = db_Θ x y.
Proof.
  rewrite (right_id_L ∅ (∪)). unfold tenv_of, sf_Σ, db_Θ.
  by rewrite fmap_insert, map_fmap_singleton.
Qed.

(** The partner holds the other ends, at x̄ and ȳ. *)
Lemma sf_Σ_dual W x y c e e' :
  world_wf W → sf_Σ x y !! c = Some e → sf_Σ (pt_dual x) (pt_dual y) !! c = Some e' →
  w_eq W e.2 (pt_dual e'.2) ∧ sdual e.1 e'.1.
Proof.
  intros HW He He'. unfold sf_Σ in He, He'.
  apply lookup_insert_Some in He as [(<- & <-)|(Hne & He)].
  - rewrite lookup_insert_eq in He'. injection He' as <-. cbn. rewrite pt_dual_dual.
    split; [apply (wf_eq_refl _ HW)|apply (sdual_dual SEnd)].
  - rewrite lookup_insert_ne in He' by done. apply lookup_singleton_Some in He as [<- <-].
    rewrite lookup_singleton_eq in He'. injection He' as <-. cbn. rewrite pt_dual_dual.
    split; [apply (wf_eq_refl _ HW)|apply (sdual_dual SEnd)].
Qed.

(** The configuration: the thread and the partner over the cut {c, d}. *)
Definition sf_config : proc := ({[chc; chd]}, {[+ sf_thread; cc2 chc chd +]}).

(** A mixed derivation of the configuration. The thread is a semantic
    leaf, the partner a syntactic one. *)
Theorem sf_mixed W x y :
  strict W → w_lt W x (pt_dual y) → w_lt W (pt_dual x) y → mptyped W ∅ sf_config TUnit.
Proof.
  intros HW Hxy Hxy'. pose proof (proj1 HW) as HWf.
  assert (sf_config = (∅ ∪ ∅ ∪ dom (sf_Σ x y), {[+ sf_thread +]} ⊎ {[+ cc2 chc chd +]})) as ->.
  { unfold sf_config, sf_Σ. f_equal. all: rewrite !dom_insert_L, dom_singleton_L; set_solver. }
  assert ((∅ : senv) = ∅ ∪ ∅) as E by by rewrite (left_id_L ∅ (∪)).
  rewrite E at 1.
  apply (mp_connect W ∅ ∅ (sf_Σ x y) (sf_Σ (pt_dual x) (pt_dual y)) (dom (sf_Σ x y)) ∅ ∅
           {[+ sf_thread +]} {[+ cc2 chc chd +]} TUnit); try done.
  - rewrite (left_id_L ∅ (∪)).
    apply (mp_sem_thread W (sf_Σ x y) ∅ ∅); [constructor|done|done|set_solver| | |].
    + intros c o Ho. by rewrite lookup_empty in Ho.
    + intros c e1 e2 He. by rewrite lookup_empty in He.
    + rewrite sf_Σ_tenv. by apply sf_thread_sem.
  - rewrite (left_id_L ∅ (∪)). apply mp_syn.
    apply (pt_term W (sf_Σ (pt_dual x) (pt_dual y)) ∅ ∅); [constructor|done|set_solver| | |].
    + intros c o Ho. by rewrite lookup_empty in Ho.
    + intros c e1 e2 He. by rewrite lookup_empty in He.
    + rewrite sf_Σ_tenv. apply cc2_typed; [done|]. by rewrite pt_dual_dual.
  - intros c e e' He He'. by apply (sf_Σ_dual W x y c).
  - apply map_disjoint_empty_l.
  - apply map_disjoint_empty_l.
Qed.

(** A strict world with x ≺ ȳ and x̄ ≺ y: c at the constant point 0, d
    at 1. *)
Definition sf_W : world := Wfacts [0; 1] [(pc 0 0, pt_dual (pc 1 0)); (pt_dual (pc 0 0), pc 1 0)].

Lemma sf_W_strict : strict sf_W.
Proof.
  apply (Wfacts_strict _ _ (λ _, 1) id (λ _ _ _, 0)); [lia| |].
  - repeat constructor; cbn; set_solver.
  - repeat constructor; cbn; lia.
Qed.

Lemma sf_W_lt : w_lt sf_W (pc 0 0) (pt_dual (pc 1 0)).
Proof. apply Wfacts_lt. by left. Qed.

Lemma sf_W_lt' : w_lt sf_W (pt_dual (pc 0 0)) (pc 1 0).
Proof. apply Wfacts_lt. by right; left. Qed.

(** The configuration is deadlock free, by the mixed derivation. *)
Theorem sf_deadlock_free : deadlock_free sf_config.
Proof.
  apply (mixed_soundness sf_W sf_config TUnit sf_W_strict).
  apply (sf_mixed sf_W (pc 0 0) (pc 1 0) sf_W_strict sf_W_lt sf_W_lt').
Qed.
