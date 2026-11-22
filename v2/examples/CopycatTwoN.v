(** * Two-sided identity expansion at a finite bound (fx-gap, 2026-11-22)

    [fwdp_expand2_fin]: the two-sided expansion of examples/CopycatTwo.v
    holds at every finite bound N ≥ 4, with no rule change. Two pieces
    were missing at a finite N.

    - The world. The collapse of the constant 1 onto 0 maps each step of
      the new world to a strict step of the old one or to an equality,
      and no two equalities follow each other. So an infinite
      descending chain of the new world maps to one of the old world,
      and the new world is well-founded when the old one is
      ([collapse_swf], [J_wok] in examples/CopycatTwo.v). The proof
      follows accessibility and needs no excluded middle.
    - The forwarder at N. Every end of the interface starts at credit
      and tickets N/2. An action returns its end at credit N/2 and costs
      1, so the end the forwarder holds across it loses 1. In the
      schema an end waits for at most two actions before it acts, so
      N/2 ≥ 2 suffices ([fb_typed], [fwdq_term_fin]). *)

From GV Require Export examples.CopycatTwo examples.LFTools.

(** ** The forwarder schema at a finite bound

    o1 : S(p)@x at credit a1 and o2 : S(p)‾@y at credit a2, both with
    k tickets. Every step keeps a1, a2 ≥ 1 and k ≥ 2. *)

Lemma fb_typed W Γ N p : ∀ n x y (a1 a2 k : nat), ffp W Γ p x y → 1 ≤ a1 → 1 ≤ a2 → 2 ≤ k →
  ∃ c, typed W N ∅ Γ (Some (TSess (pS (pdual p)) y (Some a2) (Some k)) ::
                      Some (TSess (pS p) x (Some a1) (Some k)) :: nones n)
    (∅, None) (fb p) TUnit c.
Proof.
  induction p as [|p IH|p IH]; intros n x y a1 a2 k Hf H1 H2 Hk; cbn [fb pS pdual ffp] in *.
  - eexists. eapply e_letu_; [lsplit_tac (EClose (Var 1)) EUnit| | |].
    { eapply e_close with (S0 := SEnd) (x := x); [reflexivity| |eapply e_var'; [reflexivity|spare_tac]].
      apply ub_below_nil; [bot_false|]. intros z Hz.
      rewrite tenv_heads_empty in Hz. cbn in Hz. rewrite lenv_heads_nones in Hz. set_unfold in Hz. hz_go. done. }
    { lage_tac. }
    eapply e_close with (S0 := SEnd) (x := y); [reflexivity|apply ub_below_empty|].
    eapply e_var'; [reflexivity|spare_tac].
  - destruct Hf as (H0 & H1' & Hq).
    destruct (IH (3 + n) (x⁺) (y⁺) (k - 1) k k Hq ltac:(lia) ltac:(lia) Hk) as [cq Hcq].
    eexists. eapply e_letp_; [lsplit_tac (ERecv (Var 1)) EUnit| | |].
    { eapply e_recv with (S0 := SSeq (SRcv 0 TUnit) (pS p)) (x := x) (m := 0) (T := TUnit) (S := pS p);
        [reflexivity|exact I| |eapply e_var'; [reflexivity|spare_tac]].
      apply ub_below_nil; [bot_false|]. intros z Hz.
      rewrite tenv_heads_empty in Hz. cbn in Hz. rewrite lenv_heads_nones in Hz. set_unfold in Hz. hz_go. done. }
    { lage_tac. }
    eapply e_let_; [lsplit_tac (ESend (Pair (Var 1) (Var 2))) EUnit| | |].
    { eapply e_send with (S0 := SSeq (SSnd 0 TUnit) (pS (pdual p))) (x := y) (m := 0) (T := TUnit) (S := pS (pdual p))
        (Tp := TUnit) (Tp' := TUnit);
        [reflexivity|exact I|split; [reflexivity|cbn; set_solver]| | |apply age_free; constructor|apply sub_unit].
      - apply ub_below_nil; [bot_false|]. intros z Hz.
        rewrite tenv_heads_empty in Hz. cbn in Hz. rewrite lenv_heads_nones in Hz. set_unfold in Hz. hz_go. done.
      - eapply e_pair_; [lsplit_tac (Var 1) (Var 2)| | | |apply age_free; constructor].
        + eapply e_var'; [reflexivity|]. spare_tac.
        + lage_tac.
        + eapply e_var'; [reflexivity|]. spare_tac. }
    { lage_tac. }
    exact Hcq.
  - destruct Hf as (H0 & H1' & Hq).
    destruct (IH (5 + n) (x⁺) (y⁺) k (k - 1) k Hq ltac:(lia) ltac:(lia) Hk) as [cq Hcq].
    eexists. eapply e_letp_; [lsplit_tac (ERecv (Var 0)) EUnit| | |].
    { eapply e_recv with (S0 := SSeq (SRcv 0 TUnit) (pS (pdual p))) (x := y) (m := 0) (T := TUnit) (S := pS (pdual p));
        [reflexivity|exact I| |eapply e_var'; [reflexivity|spare_tac]].
      apply ub_below_nil; [bot_false|]. intros z Hz.
      rewrite tenv_heads_empty in Hz. cbn in Hz. rewrite lenv_heads_nones in Hz. set_unfold in Hz. hz_go. done. }
    { lage_tac. }
    eapply e_let_; [lsplit_tac (ESend (Pair (Var 1) (Var 3))) EUnit| | |].
    { eapply e_send with (S0 := SSeq (SSnd 0 TUnit) (pS p)) (x := x) (m := 0) (T := TUnit) (S := pS p)
        (Tp := TUnit) (Tp' := TUnit);
        [reflexivity|exact I|split; [reflexivity|cbn; set_solver]| | |apply age_free; constructor|apply sub_unit].
      - apply ub_below_nil; [bot_false|]. intros z Hz.
        rewrite tenv_heads_empty in Hz. cbn in Hz. rewrite lenv_heads_nones in Hz. set_unfold in Hz. hz_go. done.
      - eapply e_pair_; [lsplit_tac (Var 1) (Var 3)| | | |apply age_free; constructor].
        + eapply e_var'; [reflexivity|]. spare_tac.
        + lage_tac.
        + eapply e_var'; [reflexivity|]. spare_tac. }
    { lage_tac. }
    eapply e_letp_; [lsplit_tac (Pair (Var 0) (Var 1)) EUnit| | |].
    { eapply e_pair_; [lsplit_tac (Var 0) (Var 1)| | | |].
      + eapply e_var'; [reflexivity|]. spare_tac.
      + lage_tac.
      + eapply e_var'; [reflexivity|]. spare_tac.
      + apply age_sess. simpl. lia. }
    { lage_tac. }
    simpl. rewrite !Nat.sub_0_r. exact Hcq.
  Unshelve. all: exact None.
Qed.

(** ** The forwarder as a thread at N ≥ 4 *)

Lemma thage_single c o S x a t : fle c a → fle a t → thage c {[o := TE S x a t]} {[o := TE S x (fsub a c) t]}.
Proof.
  intros Hc Ht o'. destruct (decide (o' = o)) as [->|Hne].
  - rewrite !lookup_singleton. cbn. rewrite !decide_True by done. cbn. repeat split; auto.
  - by rewrite !lookup_singleton_ne by done.
Qed.

Lemma div2_ge K : 4 ≤ K → 2 ≤ Nat.div2 K.
Proof. intros HK. pose proof (Nat.div2_odd K) as E. destruct (Nat.odd K); simpl in E; lia. Qed.

Theorem fwdq_term_fin K p : 4 ≤ K → fptyped (Some K) (W_q p) (Σq p) (∅, {[+ fwdq_t p +]}) TUnit.
Proof.
  intros HK. pose proof (div2_ge K HK) as Hh. set (h := Nat.div2 K) in Hh.
  destruct (fb_typed (W_q p) hc_empty (Some K) p 0 px pyn (h - 0) (h - 0) h (W_q_facts p) ltac:(lia) ltac:(lia) Hh)
    as [c Hc].
  apply (fp_term (Some K) (W_q p) (Σq p) ∅ ∅ _ TUnit (fadd (fadd (Some 0) (Some 0)) c)).
  - constructor.
  - intros o. rewrite dom_empty_L. set_solver.
  - set_solver.
  - apply Σq_pfree.
  - intros o e He. unfold Σq in He. apply lookup_union_Some_raw in He as [He|[_ He]];
      apply lookup_singleton_Some in He as [_ <-]; apply pS_contr.
  - set_solver.
  - assert (tenv_of (fhalf (Some K)) (Σq p) ∪ ∅ =
      {[o1 := TE (pS p) px (Some h) (Some h)]} ∪ {[ob := TE (pS (pdual p)) pyn (Some h) (Some h)]}) as ->.
    { rewrite map_union_empty. unfold tenv_of, Σq. by rewrite !map_fmap_union, !map_fmap_singleton. }
    unfold fwdq_t, fwdp_t.
    eapply e_letp with (Θ2 := ∅) (Θ2' := ∅);
      [split; [apply map_disjoint_empty_r|by rewrite map_union_empty]|apply lsplit_nil| | |apply lage_nil|exact Hc].
    + eapply e_pair with (Θ1 := {[o1 := TE (pS p) px (Some h) (Some h)]})
        (Θ2 := {[ob := TE (pS (pdual p)) pyn (Some h) (Some h)]})
        (Θ2' := {[ob := TE (pS (pdual p)) pyn (fsub (Some h) (Some 0)) (Some h)]});
        [split; [by apply map_disjoint_singleton_l_2; rewrite lookup_singleton_ne|reflexivity]
        |apply lsplit_nil| |apply thage_single; simpl; lia|apply lage_nil| |apply (age_sess (Some 0) (pS p) px (Some h) (Some h)); simpl; lia];
        (apply e_chan; [intros o Ho; by apply elem_of_nil in Ho|simpl; lia]).
    + apply thage_empty.
  - split; [apply W_q_wf|apply W_q_wok].
Qed.

(** ** Two-sided expansion at a finite bound *)

Theorem fwdp_expand2_fin K p W1 W2 Σ1 Σ2 C1 C2 E1 E2 T : 4 ≤ K →
  fptyped (Some K) W1 (Σ1 ∪ Σxp p) (C1, E1) T →
  fptyped (Some K) W2 (Σ2 ∪ senv_dual (Σxp p)) (C2, E2) TUnit →
  Σ1 ##ₘ Σxp p → Σ2 ##ₘ senv_dual (Σxp p) →
  chans_of Σ1 ## chans_of Σ2 → "a" ∉ chans_of Σ1 → "a" ∉ chans_of Σ2 →
  C1 ## C2 → C1 ## chans_of Σ2 ∪ {["a"]} → C2 ## chans_of Σ1 ∪ {["a"]} →
  wok (Some K) (swrestrict W1 (swshared W1 W2) ⊔ swrestrict W2 (swshared W1 W2)) →
  "b" ∉ chans_of Σ1 → "b" ∉ chans_of Σ2 → "b" ∉ C1 → "b" ∉ C2 →
  1 ∉ sw_consts W1 → 1 ∉ sw_consts W2 →
  fptyped (Some K) (W1 ⊔ (W_q p ⊔ sw_ren sw01 W2)) (Σ1 ∪ senv_ren (cswap 0 1) Σ2)
    (C1 ∪ (∅ ∪ C2 ∪ {["b"]}) ∪ {["a"]},
     E1 ⊎ ({[+ fwdq_t p +]} ⊎ emapE (cmap (sswap "a" "b")) E2)) T.
Proof. intros HK. apply fwdp_expand2_N, fwdq_term_fin, HK. Qed.
