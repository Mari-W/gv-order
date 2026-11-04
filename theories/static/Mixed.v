(** * Mixed typing: semantic components inside syntactic programs

    The logical relation is a typing judgment of its own. A component
    that the static system rejects can still be proved semantically
    typed by hand, and this file plugs such components into programs
    that are typed syntactically.

    Two forms.

    - Processes. [mptyped] is [ptyped] with one more leaf: any process
      that is semantically typed at a prim type. P-Connect joins
      syntactic and semantic components alike. [mptyped_sem] sends a
      mixed derivation to the logical relation, and [mixed_soundness]
      concludes deadlock freedom for a closed configuration.
      [mp_sem_thread] is the leaf for a single thread, the semantic
      counterpart of P-Term.

    - Terms. [sem_plug] applies a syntactically typed function to a
      semantically typed argument, and [plug_soundness] runs the result
      as a closed program. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export static.Fundamental.

Set Default Proof Using "All".

(** ** Processes *)

Inductive mptyped (W : world) : senv → proc → ty → Prop :=
  | mp_syn Σ p T :                                      (* a typed process *)
      ptyped W Σ p T → mptyped W Σ p T
  | mp_sem Σ p T :                                      (* a semantic process *)
      prim T → sem_ptyped W Σ p T → mptyped W Σ p T
  | mp_connect Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 T :         (* P-Connect *)
      mptyped W (Σ1 ∪ ΣC) (C1, E1) T → mptyped W (Σ2 ∪ ΣC') (C2, E2) TUnit →
      dom ΣC = C0 → dom ΣC' = C0 →
      (∀ c e e', ΣC !! c = Some e → ΣC' !! c = Some e' → w_eq W e.2 e'.2 ∧ sdual e.1 e'.1) →
      C1 ## dom Σ2 → C2 ## dom Σ1 →
      Σ1 ##ₘ ΣC → Σ2 ##ₘ ΣC' → Σ1 ##ₘ Σ2 →
      C1 ## dom Σ1 → C2 ## dom Σ2 → C1 ## C0 → C2 ## C0 → C1 ## C2 →
      mptyped W (Σ1 ∪ Σ2) (C1 ∪ C2 ∪ C0, E1 ⊎ E2) T.

Lemma mptyped_prim W Σ p T : mptyped W Σ p T → prim T.
Proof. induction 1; [by eapply ptyped_prim|done|done]. Qed.

(** A thread that is semantically typed is a semantic leaf. The side
    conditions are those of P-Term. *)
Lemma mp_sem_thread W Σ ΘB C0 t T :
  prim T → strict W → dom ΘB = C0 → dom Σ ## C0 →
  (∀ c o, ΘB !! c = Some o → ∃ e1 e2, o = Both e1 e2) → tenv_dual (w_eq W) ΘB →
  sem_typed W (tenv_of Σ ∪ ΘB) [] ∅ t T →
  mptyped W Σ (C0, {[+ t +]}) T.
Proof. intros HT HW Hd Hdj Hb Hdu Ht. apply mp_sem; [done|]. by eapply Prel_term. Qed.

(** Every mixed derivation lies in the logical relation. *)
Theorem mptyped_sem W Σ p T : mptyped W Σ p T → strict W → sem_ptyped W Σ p T.
Proof.
  induction 1 as [Σ p T Hp|Σ p T _ Hp
                 |Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 T H1 IH1 H2 IH2 HdC HdC' Hcut
                    ? ? ? ? ? ? ? ? ? ?]; intros HW.
  - by apply fundamental_proc.
  - done.
  - assert (strict (wjoin W W)) as HWW by (by apply wjoin_sub_strict, wext_refl).
    intros n. eapply Prel_mono; [apply HWW|by apply wext_join_self|].
    revert n. apply (Prel_connect W W Σ1 Σ2 ΣC ΣC' C0 C1 C2 E1 E2 T); try done.
    + exact (mptyped_prim _ _ _ _ H1).
    + by apply IH1.
    + by apply IH2.
    + intros c e e' He He'. destruct (Hcut c e e' He He') as [Heq Hs].
      split; [by apply wjoin_l|done].
    + apply HW.
    + apply HW.
Qed.

(** Closed mixed configurations are deadlock free. *)
Corollary mixed_soundness W p T : strict W → mptyped W ∅ p T → deadlock_free p.
Proof. intros HW Hp. apply (adequacy W T p). by apply mptyped_sem. Qed.

(** ** Terms *)

(** A syntactically typed function applied to a semantically typed
    argument. The premises are those of E-App, with the function typed
    by the static system. *)
Theorem sem_plug W Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 ub lb T U :
  strict W →
  tenv_comp (w_eq W) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 → ub_below W ub F →
  typed W ∅ [] Θ1 Δ1 (F ∪ (tenv_heads Θ2 ∪ lenv_heads Δ2 ∪ bot_pts (lenv_bot Δ2)), None)
    e1 (TLolli ub lb T U) →
  sem_typed W Θ2 Δ2 (F ∪ opt_heads lb) e2 T →
  sem_typed W Θ Δ F (App e1 e2) U.
Proof.
  intros HW Hc Hs Hub H1 H2. eapply sem_typed_app; [exact Hc|exact Hs|exact Hub| |exact H2].
  by apply fundamental.
Qed.

(** The closed program e₁ e₂: e₁ typed by the static system, e₂ by
    the logical relation. *)
Corollary plug_soundness W e1 e2 ub lb T U :
  strict W → prim U → ub_below W ub ∅ →
  typed W ∅ [] ∅ [] (∅, None) e1 (TLolli ub lb T U) →
  sem_typed W ∅ [] (opt_heads lb) e2 T →
  deadlock_free (∅, {[+ App e1 e2 +]}).
Proof.
  intros HW HU Hub H1 H2.
  apply (adequacy W U).
  apply (Prel_term W ∅ ∅ ∅); [done|done|done|set_solver| | |].
  - intros c o Ho. by rewrite lookup_empty in Ho.
  - intros c e1' e2' He. by rewrite lookup_empty in He.
  - unfold tenv_of. rewrite fmap_empty, (left_id_L ∅ (∪)).
    eapply (sem_plug W ∅ ∅ ∅ [] [] []); [done|apply tenv_comp_empty_r|constructor|done| |].
    + assert (((∅ : gset point) ∪ (tenv_heads ∅ ∪ lenv_heads [] ∪ bot_pts (lenv_bot []))) = ∅) as ->.
      { unfold tenv_heads. rewrite map_fold_empty. simpl. set_solver. }
      exact H1.
    + by rewrite (left_id_L ∅ (∪)).
Qed.
