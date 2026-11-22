(** * The n-ary P-Connect, admissible from the binary rule (2026-11-22)

      Σ_1 ⊢_{W_1} p_1 : T,  Σ_i ∪ Σ̄_{C,i} ⊢_{W_i} p_i : ∗  (i = 2 … n),
      each Σ_{C,i} a cut of the composite of p_1 … p_{i-1},
      wf (W_1 ⊔ … ⊔ W_n)
      ⇒  Σ ⊢_W (C_1 ∪ … ∪ C_n ∪ C_0, E_1 ⊎ … ⊎ E_n) : T

    [pcomps N Ws Σ p T] collects the n component derivations at their
    hidden worlds Ws and the side conditions of each binary step, with
    no condition on worlds. It reads the composition as a sequence. The
    i-th component connects to the composite of the components before
    it over the cut Σ_{C,i}, which may hold ends of several earlier
    components. [p_connect_n] asks one interface check, the join of the
    n hidden component worlds ([sw_joins]) acyclic at N = ∞ and
    well-founded at a finite N ([wok]), and gives a hidden
    derivation at a world whose facts are facts of that join restricted
    to the final interface.

    The proof folds the binary P-Connect. At each step the hidden world
    of the composite so far derives only facts of the join of its
    component worlds, so every binary premise follows from the one n-ary
    premise. The fold needs no amalgamation lemma. Its result world may
    derive fewer facts than the restricted join, because a constant the
    composite hides at an earlier step drops out of the later checks.

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

Inductive pcomps (N : fuel) : list sworld → senv → proc → ty → Prop :=
  | pc_one W Σ p T :
      ptyped N W Σ p T → pcomps N [W] Σ p T
  | pc_snoc Ws W Σ1 Σ2 ΣC C1 C2 E1 E2 T :
      pcomps N Ws (Σ1 ∪ ΣC) (C1, E1) T →
      ptyped N W (Σ2 ∪ senv_dual ΣC) (C2, E2) TUnit →
      chans_of Σ1 ## chans_of Σ2 → chans_of Σ1 ## chans_of ΣC → chans_of Σ2 ## chans_of ΣC →
      C1 ## C2 → C1 ## chans_of Σ2 ∪ chans_of ΣC → C2 ## chans_of Σ1 ∪ chans_of ΣC →
      pcomps N (Ws ++ [W]) (Σ1 ∪ Σ2) (C1 ∪ C2 ∪ chans_of ΣC, E1 ⊎ E2) T.

(** The fold. The world of the composite derives only facts of the join
    of its component worlds and holds only their constants. *)
Lemma pcomps_fold N Ws Σ p T :
  pcomps N Ws Σ p T → wok N (sw_joins Ws) →
  ∃ W, ptyped N W Σ p T ∧ (∀ x y, W ⊢ₛ x ≺ y → sw_joins Ws ⊢ₛ x ≺ y) ∧ sw_consts W ⊆ sw_consts (sw_joins Ws).
Proof.
  induction 1 as [W Σ p T Hty|Ws W Σ1 Σ2 ΣC C1 C2 E1 E2 T _ IH Hty H12 H1C H2C HC HC1 HC2];
    intros HS.
  - exists W. split_and!; [done| |].
    + intros x y. apply sw_lt_mono, swext_joins. set_solver.
    + apply swext_consts, swext_joins. set_solver.
  - destruct IH as (Wa & Hta & Hlt & Hc).
    { eapply (wok_sub N); [|exact HS]. intros x y. apply sw_lt_mono, swext_joins_app. }
    assert (∀ x y, Wa ⊔ W ⊢ₛ x ≺ y → sw_joins (Ws ++ [W]) ⊢ₛ x ≺ y) as Hj.
    { intros x y H. eapply sw_lt_mono; [|eapply (join_sub Wa (sw_joins Ws) W W); [exact Hlt|done|exact H]].
      split; simpl.
      - pose proof (swext_consts _ _ (swext_joins_app Ws [W])) as K1.
        pose proof (swext_consts _ _ (swext_joins W (Ws ++ [W]) ltac:(set_solver))) as K2. set_solver.
      - intros g [Hg|Hg].
        + by apply (swext_facts _ _ (swext_joins_app Ws [W])).
        + apply (swext_facts _ _ (swext_joins W (Ws ++ [W]) ltac:(set_solver))), Hg. }
    exists (swrestrict (Wa ⊔ W) (iface (Σ1 ∪ Σ2) T)). split_and!.
    + apply p_connect; try done. apply (wok_sub N _ (sw_joins (Ws ++ [W]))); [exact Hj|exact HS].
    + intros x y H. by apply Hj, (swrestrict_lt _ (iface (Σ1 ∪ Σ2) T)).
    + simpl. pose proof (swext_consts _ _ (swext_joins_app Ws [W])) as K1.
      pose proof (swext_consts _ _ (swext_joins W (Ws ++ [W]) ltac:(set_solver))) as K2. set_solver.
Qed.

(** ** The n-ary rule

    One interface check, [wok] of the join of the n hidden component
    worlds. The result world says nothing the join, restricted to the
    final interface, does not. *)
Theorem p_connect_n N Ws Σ p T :
  pcomps N Ws Σ p T → wok N (sw_joins Ws) →
  ∃ W, ptyped N W Σ p T ∧ ∀ g, sw_facts W g → sw_facts (swrestrict (sw_joins Ws) (iface Σ T)) g.
Proof.
  intros Hp HS. destruct (pcomps_fold N Ws Σ p T Hp HS) as (W & Hty & Hlt & Hc).
  exists W. split; [done|]. intros [x y] Hg.
  pose proof (ptyped_consts _ _ _ _ _ Hty) as Hi.
  destruct (wf_facts _ (proj1 (ptyped_wf _ _ _ _ _ Hty)) x y Hg) as [(a & Ha & Hax) (b & Hb & Hby)].
  simpl. split_and!.
  - by apply Hlt, sw_lt_fact.
  - exists a. split; [done|]. apply elem_of_intersection. split; [by apply Hc|by apply Hi].
  - exists b. split; [done|]. apply elem_of_intersection. split; [by apply Hc|by apply Hi].
Qed.

(** ** Soundness through the binary results *)

Theorem connect_n_soundness Ws p T :
  pcomps None Ws ∅ p T → sacyc (sw_joins Ws) → deadlock_free p.
Proof.
  intros Hp HS. destruct (p_connect_n None Ws ∅ p T Hp HS) as (W & Hty & _).
  exact (soundness_h W p T Hty).
Qed.

Theorem connect_n_live_soundness Ws p T :
  pcomps None Ws ∅ p T → sacyc (sw_joins Ws) → deadlock_free p ∧ no_free_divergence p.
Proof.
  intros Hp HS. destruct (p_connect_n None Ws ∅ p T Hp HS) as (W & Hty & _).
  exact (live_soundness_h W p T Hty).
Qed.
