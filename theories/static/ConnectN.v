(** * The n-ary P-Connect, admissible from the binary rule (2026-11-22)

      Σ_1 ⊢_{W_1} p_1 : T,  Σ_i ∪ Σ̄_{C,i} ⊢_{W_i} p_i : ∗  (i = 2 … n),
      each Σ_{C,i} a cut of the composite of p_1 … p_{i-1},
      wf (W_1 ⊔ … ⊔ W_n)
      ⇒  Σ ⊢_W (C_1 ∪ … ∪ C_n ∪ C_0, E_1 ⊎ … ⊎ E_n) : T

    [pcomps N Ws Σ p T] collects the n component derivations at their
    worlds Ws and the side conditions of each binary step, with no
    condition on worlds. It reads the composition as a sequence. The
    i-th component connects to the composite of the components before
    it over the cut Σ_{C,i}, which may hold ends of several earlier
    components. [p_connect_n] asks one check, the join of the n
    component worlds ([sw_joins]) acyclic at N = ∞ and well-founded at
    a finite N ([wok]), and gives a derivation at a world with the
    constants and the facts of that join.

    The proof folds the binary P-Connect. At each step the world of the
    composite so far has the constants and the facts of the join of its
    component worlds, so every binary premise follows from the one
    n-ary premise. The fold needs no amalgamation lemma.

    The condition is no conjunction of pairwise conditions. Milner's
    ring (examples/Ring.v) is pairwise consistent and cyclic as a whole.

    Soundness for both relations follows through the binary results
    ([connect_n_soundness], [connect_n_live_soundness], and
    [connect_n_lf_soundness] in soup/LFConnectN.v). *)

From GV Require Export static.FundamentalProc.

(** ** The join of a list of static worlds *)

Definition sw_joins (Ws : list sworld) : sworld :=
  SWorld (⋃ (sw_consts <$> Ws)) (λ g, ∃ W, W ∈ Ws ∧ sw_facts W g).

Lemma swext_joins W Ws : W ∈ Ws → W ⊑ₛ sw_joins Ws.
Proof.
  intros HW. split; simpl.
  - intros a Ha. apply elem_of_union_list. exists (sw_consts W). split; [|done].
    by apply list_elem_of_fmap_2.
  - intros g Hg. by exists W.
Qed.

Lemma swext_joins_app Ws Ws' : sw_joins Ws ⊑ₛ sw_joins (Ws ++ Ws').
Proof.
  split; simpl.
  - rewrite fmap_app, union_list_app_L. set_solver.
  - intros g (W & HW & Hg). exists W. split; [by apply elem_of_app; left|done].
Qed.

(** ** The components of an n-ary composition *)

Inductive pcomps (N : fuel) (η : iann) : list sworld → senv → proc → ty → Prop :=
  | pc_one W Σ p T :
      ptyped N η W Σ p T → pcomps N η [W] Σ p T
  | pc_snoc Ws W Σ1 Σ2 ΣC C1 C2 E1 E2 T :
      pcomps N η Ws (Σ1 ∪ ΣC) (C1, E1) T →
      ptyped N η W (Σ2 ∪ senv_dual ΣC) (C2, E2) TUnit →
      chans_of Σ1 ## chans_of Σ2 → chans_of Σ1 ## chans_of ΣC → chans_of Σ2 ## chans_of ΣC →
      C1 ## C2 → C1 ## chans_of Σ2 ∪ chans_of ΣC → C2 ## chans_of Σ1 ∪ chans_of ΣC →
      (∀ o, o ∈ dom ΣC → tsum_ok N (η o).2 (η (edual o)).2) →
      pcomps N η (Ws ++ [W]) (Σ1 ∪ Σ2) (C1 ∪ C2 ∪ chans_of ΣC, E1 ⊎ E2) T.

(** The fold. The world of the composite has the constants and the
    facts of the join of its component worlds. *)
Lemma pcomps_fold N η Ws Σ p T :
  pcomps N η Ws Σ p T → wok N (sw_joins Ws) →
  ∃ W, ptyped N η W Σ p T ∧ W ⊑ₛ sw_joins Ws ∧ sw_joins Ws ⊑ₛ W.
Proof.
  induction 1 as [W Σ p T Hty|Ws W Σ1 Σ2 ΣC C1 C2 E1 E2 T _ IH Hty H12 H1C H2C HC HC1 HC2 Hts];
    intros HS.
  - exists W. split_and!; [done|apply swext_joins; set_solver|].
    split; cbn [sw_joins sw_consts sw_facts].
    + intros a. rewrite elem_of_union_list. intros (A & HA & Ha).
      apply list_elem_of_fmap in HA as (W' & -> & HW'). apply list_elem_of_singleton in HW' as ->. done.
    + intros g (W' & HW' & Hg). apply list_elem_of_singleton in HW' as ->. done.
  - destruct IH as (Wa & Hta & Hle & Hge).
    { eapply (wok_sub N); [|exact HS]. intros x y. apply sw_lt_mono, swext_joins_app. }
    assert (Wa ⊔ W ⊑ₛ sw_joins (Ws ++ [W])) as Hj.
    { split; simpl.
      - pose proof (swext_consts _ _ Hle) as K0.
        pose proof (swext_consts _ _ (swext_joins_app Ws [W])) as K1.
        pose proof (swext_consts _ _ (swext_joins W (Ws ++ [W]) ltac:(set_solver))) as K2. set_solver.
      - intros g [Hg|Hg].
        + by apply (swext_facts _ _ (swext_joins_app Ws [W])), (swext_facts _ _ Hle).
        + apply (swext_facts _ _ (swext_joins W (Ws ++ [W]) ltac:(set_solver))), Hg. }
    exists (Wa ⊔ W). split_and!; [|exact Hj|].
    + apply p_connect; try done. apply (wok_sub N _ (sw_joins (Ws ++ [W]))); [|exact HS].
      intros x y. by apply sw_lt_mono.
    + split; cbn [sw_joins sw_consts sw_facts swjoin].
      * intros a Ha. rewrite fmap_app, union_list_app_L in Ha. simpl in Ha.
        pose proof (swext_consts _ _ Hge) as K. cbn [sw_joins sw_consts] in K. set_solver.
      * intros g (W' & HW' & Hg). apply elem_of_app in HW' as [HW'|HW'].
        -- left. apply (swext_facts _ _ Hge). by exists W'.
        -- apply list_elem_of_singleton in HW' as ->. by right.
Qed.

(** ** The n-ary rule

    One check, [wok] of the join of the n component worlds. The result
    world has the constants and the facts of that join. *)
Theorem p_connect_n N η Ws Σ p T :
  pcomps N η Ws Σ p T → wok N (sw_joins Ws) →
  ∃ W, ptyped N η W Σ p T ∧ W ⊑ₛ sw_joins Ws ∧ sw_joins Ws ⊑ₛ W.
Proof. apply pcomps_fold. Qed.

(** ** Soundness through the binary results *)

Theorem connect_n_soundness Ws p T :
  pcomps None (khalf None) Ws ∅ p T → sacyc (sw_joins Ws) → deadlock_free p.
Proof.
  intros Hp HS. destruct (p_connect_n None (khalf None) Ws ∅ p T Hp HS) as (W & Hty & _).
  exact (soundness W p T Hty).
Qed.

Theorem connect_n_live_soundness Ws p T :
  pcomps None (khalf None) Ws ∅ p T → sacyc (sw_joins Ws) → deadlock_free p ∧ no_free_divergence p.
Proof.
  intros Hp HS. destruct (p_connect_n None (khalf None) Ws ∅ p T Hp HS) as (W & Hty & _).
  exact (live_soundness W p T Hty).
Qed.
