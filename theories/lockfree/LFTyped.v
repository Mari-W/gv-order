(** * The lock-free judgment on processes (lock-freedom plan §19.7, stage H5)

    [lfptyped W Σ p T] is [ptyped] with each thread also guarded
    ([glive], liveness/GuardRules.v) and cost typed ([ctyped],
    static/CostTyping.v). The ends a thread holds sit at points the
    world knows, and each one fits the cost type the thread's derivation
    gives it ([cfits]). Rank, a well-founded ≺, is a premise of
    [lf_soundness], as strictness is of [live_soundness].

    [lf_fundamental] is induction on [lfptyped]. A thread goes through
    [LFP_term]. Its live part comes from [live_fundamental_guarded], its
    fuel from [ctyped_fsem], the fundamental theorem of the cost
    judgment. Composition goes through [LFP_connect], and [lfptyped_join]
    restates the rule with the premises of [LFP_join]. [lf_soundness] is
    [lf_fundamental] with [lf_adequacy].

    Stage H4 proves [ctyped_fsem] in lockfree/CostFund.v. Until then it
    is the hypothesis of the section below, stated as [ctyped_fsem_stmt],
    and the theorems take it as an explicit premise once the section
    closes.

    Deviation from plan §19.7. P-Connect of [ptyped] composes two
    processes in one world W. [LFP_connect] lands in [wjoin W1 W2], and
    [LFP] has no lemma from [wjoin W W] back to W. So [lfptyped] has one
    composition rule, [lf_connect], in the form of P-Join with two
    worlds and the budget agreement [wbud_agree] at the shared names.
    Two processes typed in one world W compose in [wjoin W W]. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Import lockfree.Rank.
From LRGV Require Import liveness.LiveGuardFund liveness.GuardRules static.CostTyping.
From LRGV Require Import lockfree.LFFuel lockfree.LFCompose lockfree.LFAdequacy.

Set Default Proof Using "All".

(** ** Ends that fit their cost types *)

(** The cost environment Θc of a thread speaks of exactly the ends at the
    points π. Each end has an end type whose protocol its point fits, at
    a credit no larger than the budget at the point, the counter it
    starts with. *)
Definition cfits (W : world) (Θc : cthe) (π : gmap cend point) : Prop :=
  dom Θc = dom π ∧
  ∀ o σ, Θc !! o = Some σ → ∃ x P a, π !! o = Some x ∧ σ = CTa (CEnd P) a ∧
    pfits W x P ∧ fle a (w_bud W x).

(** ** The judgment *)

Inductive lfptyped : world → senv → proc → ty → Prop :=
  | lf_term W Σ ΘB C0 t T Θc σ c t0 :                       (* P-Term *)
      prim T → dom ΘB = C0 → dom Σ ## C0 →
      (∀ c o, ΘB !! c = Some o → ∃ e1 e2, o = Both e1 e2) → tenv_dual (w_eq W) ΘB →
      typed W ∅ [] (tenv_of Σ ∪ ΘB) [] (∅, None) t T → glive noL t →
      ctyped W Θc [] t σ c t0 →
      (∀ o x, tenv_points (tenv_of Σ ∪ ΘB) !! o = Some x → pt_known W x) →
      cfits W Θc (tenv_points (tenv_of Σ ∪ ΘB)) →
      lfptyped W Σ (C0, {[+ t +]}) T
  | lf_connect W1 W2 Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 T :         (* P-Join *)
      lfptyped W1 (Σ1 ∪ ΣC) (C1, E1) T → lfptyped W2 (Σ2 ∪ ΣC') (C2, E2) TUnit →
      dom ΣC = C0 → dom ΣC' = C0 →
      (∀ c e e', ΣC !! c = Some e → ΣC' !! c = Some e' →
         w_eq (wjoin W1 W2) e.2 (pt_dual e'.2) ∧ sdual e.1 e'.1) →
      C1 ## dom Σ2 → C2 ## dom Σ1 →
      Σ1 ##ₘ ΣC → Σ2 ##ₘ ΣC' → Σ1 ##ₘ Σ2 →
      C1 ## dom Σ1 → C2 ## dom Σ2 → C1 ## C0 → C2 ## C0 → C1 ## C2 →
      world_wf W1 → world_wf W2 → strict (wjoin W1 W2) → wbud_agree W1 W2 →
      lfptyped (wjoin W1 W2) (Σ1 ∪ Σ2) (C1 ∪ C2 ∪ C0, E1 ⊎ E2) T.

Lemma lfptyped_prim W Σ p T : lfptyped W Σ p T → prim T.
Proof. induction 1; auto. Qed.

(** The judgment forgets to [gptyped]. *)
Lemma lfptyped_gptyped W Σ p T : lfptyped W Σ p T → gptyped W Σ p T.
Proof.
  induction 1 as [W Σ ΘB C0 t T Θc σ c t0 HT Hd Hdj Hb Hdu Ht Hg
                 |W1 W2 Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 T _ [IH1 Hg1] _ [IH2 Hg2] HdC HdC' Hcut
                    ? ? ? ? ? ? ? ? ? ? HW1 HW2 HJ _].
  - split; [by econstructor|]. intros e ->%gmultiset_elem_of_singleton. by apply guarded_iff.
  - split; [by eapply pt_join|]. intros e He. simpl in He.
    apply gmultiset_elem_of_disj_union in He as [He|He]; [by apply Hg1|by apply Hg2].
Qed.

(** P-Join with the premises of [LFP_join]. The two worlds are strict,
    and so is the join of their restrictions to the shared names. *)
Lemma lfptyped_join W1 W2 Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 T :
  lfptyped W1 (Σ1 ∪ ΣC) (C1, E1) T → lfptyped W2 (Σ2 ∪ ΣC') (C2, E2) TUnit →
  dom ΣC = C0 → dom ΣC' = C0 →
  (∀ c e e', ΣC !! c = Some e → ΣC' !! c = Some e' →
     w_eq (wjoin W1 W2) e.2 (pt_dual e'.2) ∧ sdual e.1 e'.1) →
  C1 ## dom Σ2 → C2 ## dom Σ1 →
  Σ1 ##ₘ ΣC → Σ2 ##ₘ ΣC' → Σ1 ##ₘ Σ2 →
  C1 ## dom Σ1 → C2 ## dom Σ2 → C1 ## C0 → C2 ## C0 → C1 ## C2 →
  strict W1 → strict W2 →
  strict (wjoin (wrestrict W1 (w_names W1 ∩ w_names W2))
                (wrestrict W2 (w_names W1 ∩ w_names W2))) →
  wbud_agree W1 W2 →
  lfptyped (wjoin W1 W2) (Σ1 ∪ Σ2) (C1 ∪ C2 ∪ C0, E1 ⊎ E2) T.
Proof.
  intros H1 H2 HC0 HC0' Hcut HC1Σ2 HC2Σ1 Hd1 Hd2 Hd12 HC1Σ1 HC2Σ2 HC10 HC20 HC12 HS1 HS2 HA Hag.
  apply (lf_connect W1 W2 Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 T); try done;
    [apply HS1|apply HS2|by apply amalgamation].
Qed.

(** ** The fundamental theorem *)

(** The fundamental theorem of the cost judgment for a closed thread, as
    [LFP_term] reads it. Stage H4 proves it (lockfree/CostFund.v). *)
Definition ctyped_fsem_stmt : Prop :=
  ∀ W Θc π t σ c t0,
    strict W → ctyped W Θc [] t σ c t0 → cfits W Θc π →
    (∀ o x, π !! o = Some x → pt_known W x) → fsem W π t.

Section fundamental.
  Hypothesis ctyped_fsem : ctyped_fsem_stmt.

  Theorem lf_fundamental W Σ p T : lfptyped W Σ p T → strict W → LFP W Σ T p.
  Proof.
    induction 1 as [W Σ ΘB C0 t T Θc σ c t0 HT Hd Hdj Hb Hdu Ht Hg Hc Hkn Hfit
                   |W1 W2 Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 T H1 IH1 H2 IH2 HdC HdC' Hcut
                      ? ? ? ? ? ? ? ? ? ? HW1 HW2 HJ Hag]; intros HW.
    - apply (LFP_term W Σ ΘB C0); try done.
      + apply live_fundamental_guarded; [|done]. split; [done|]. by apply guarded_iff.
      + by apply (ctyped_fsem W Θc _ t σ c t0).
    - assert (strict W1) as HS1.
      { split; [done|]. intros x Hx. apply (proj2 HJ x), (proj2 (wjoin_l W1 W2)), Hx. }
      assert (strict W2) as HS2.
      { split; [done|]. intros x Hx. apply (proj2 HJ x), (proj2 (wjoin_r W1 W2)), Hx. }
      apply (LFP_connect W1 W2 Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 T); try done.
      + exact (lfptyped_prim _ _ _ _ H1).
      + by apply IH1.
      + by apply IH2.
  Qed.

  (** A closed process of the judgment in a world with Rank is lock free. *)
  Theorem lf_soundness W T p :
    lfptyped W ∅ p T → world_wf W → well_founded (w_lt W) → lock_free p.
  Proof.
    intros Hp Hwf Hwfo. apply (lf_adequacy W T p Hwf Hwfo).
    apply lf_fundamental; [done|]. by apply strict_of.
  Qed.
End fundamental.

(** ** Ends outside the support of the world

    FuelE is closed under every extension of the budgets ([wbext]), and
    an extension keeps the budgets only at the points the smaller world
    knows ([wext_bud]). A counter at a point the world does not know is
    therefore 0 ([fuel_unknown_zero]). This is why [lfptyped] asks the
    held ends at known points, and why the receive clause admits only
    incoming ends at known points ([fin_ok], quirk A13c). *)

(** W with the budget b at the point k. *)
Definition wbud_set (W : world) (k : point) (b : option nat) : world :=
  World (w_names W) (w_lt W) (λ x, if decide (x = k) then b else w_bud W x) (w_pc W).

(** Outside the support, that is an extension. *)
Lemma wbud_set_ext W k b : ¬ pt_known W k → wbext W (wbud_set W k b).
Proof.
  intros Hk. split; [done|]. intros x Hx. simpl.
  destruct (decide (x = k)) as [->|]; [contradiction|done].
Qed.

(** A counter at a point outside the support is 0 at every index
    above 0. *)
Lemma fuel_unknown_zero n W σ r π φ tk d e o k m :
  FuelE (S n) W σ r π φ tk d e → π !! o = Some k → φ !! o = Some (Some m) → ¬ pt_known W k → m = 0.
Proof.
  intros HF Hk Hm Hu.
  apply (FuelE_wbext _ _ (wbud_set W k (Some 0))) in HF; [|by apply wbud_set_ext].
  destruct (fuel_cap _ _ _ _ _ _ HF o _ Hm) as (k' & Hk' & Hle).
  rewrite Hk in Hk'. simplify_eq. simpl in Hle. rewrite decide_True in Hle by done. simpl in Hle. lia.
Qed.
