(** * A link that types once creations choose their tickets (stage 2)

    E-Link asks a1 + m2 > N and a2 + m1 > N of the two linked ends. With
    the creation tickets fixed at N/2 and N − N/2 it types for no even N
    (.claude/notes/redesign/algorithmic-plan.md, finding 6.12). A creation now
    chooses its tickets m1 + m2 ≤ N ([e_new_tk]), so the forwarding end of
    each of two channels can hold all N tickets and its dual end none.

    - [lk_new]: E-New gives the ends of a channel at N and 0 tickets.
    - [lk_typed]: a thread that holds c⁺ at x and d⁻ at x‾, both at N
      tickets and full credit, types ELink ⟨c⁺, d⁻⟩ at every N ≥ 1.
    - [lk_ok]: the four ends meet the bound, N + 0 ≤ N per channel. *)

From GV Require Import examples.LFTools.

Section link.
  Context (W : sworld) (N : nat) (HN : 1 ≤ N) (S : sty) (HS : scontr S) (x : point).

  Definition lc : cend := EPos "c".
  Definition ld : cend := ENeg "d".

  Lemma lk_new Γ (L : fact → Prop) : wf_new (bcs_of L) →
    typed W (Some N) ∅ Γ [] (∅, None) ENew (TEx LBot 1 (bcs_of L)
      (TProd (TSess S (pvar 0) (Some N) (Some N)) (TSess (dual S) (pvar 0)‾ (Some 0) (Some 0)))) (Some 0).
  Proof.
    intros HL. apply e_new_tk; [intros y o Hy; by rewrite lookup_nil in Hy|done| |exact HS].
    unfold tsum_ok. simpl. lia.
  Qed.

  Lemma lk_ok : tsum_ok (Some N) (Some N) (Some 0).
  Proof. unfold tsum_ok. simpl. lia. Qed.

  Definition Θl : tenv := {[lc := TE S x (Some N) (Some N)]} ∪ {[ld := TE (dual S) x‾ (Some N) (Some N)]}.

  Lemma lk_disj : ({[lc := TE S x (Some N) (Some N)]} : tenv) ##ₘ {[ld := TE (dual S) x‾ (Some N) (Some N)]}.
  Proof. apply map_disjoint_singleton_l, lookup_singleton_ne. discriminate. Qed.

  Lemma lk_typed : typed W (Some N) Θl hc_empty [] (∅, None) (ELink (Pair (Chan lc) (Chan ld))) TUnit (fadd (Some 0) (Some 0)).
  Proof.
    eapply e_link.
    - eapply (e_pair W (Some N) Θl {[lc := TE S x (Some N) (Some N)]} {[ld := TE (dual S) x‾ (Some N) (Some N)]}
        {[ld := TE (dual S) x‾ (Some N) (Some N)]} hc_empty [] [] [] [] _ _ _ _ _ _ (Some 0) (Some 0)).
      + split; [exact lk_disj|done].
      + constructor.
      + apply e_chan; [apply spare_unl; intros y o Hy; by rewrite lookup_nil in Hy|solve [done|apply fle_refl|cbn; lia]].
      + intros o. destruct (decide (o = ld)) as [->|Hne].
        * rewrite lookup_singleton_eq. simpl. split_and!; [done|done|done|lia|f_equal; lia|lia].
        * by rewrite lookup_singleton_ne.
      + constructor.
      + apply e_chan; [apply spare_unl; intros y o Hy; by rewrite lookup_nil in Hy|solve [done|apply fle_refl|cbn; lia]].
      + apply age_sess. simpl. lia.
    - simpl. lia.
    - simpl. lia.
  Qed.
End link.

(** ** The link closed over its interface

    The interface annotations η give the two linked ends c⁺ and d⁻ credit
    and tickets N and their dual ends c⁻ and d⁺ none. Each cut then meets
    the bound, N + 0 ≤ N, and E-Link holds, N + N > N. Each dual end
    closes its end. The three threads form a closed process at every
    N ≥ 1 ([lk_closed_typed]), which is lock free ([lk_closed_lock_free]).
    With every interface end at N/2 the link asks N/2 + N/2 > N, which
    no N meets. *)

From GV Require Import examples.LFClose.

Section closed.
  Context (N : nat) (HN : 1 ≤ N) (x : point).

  Definition lk_eta : iann :=
    λ o, if decide (o = lc ∨ o = ld) then (Some N, Some N) else (Some 0, Some 0).

  Definition lk_link : expr := ELink (Pair (Chan lc) (Chan ld)).

  Definition Σl : senv := {[ld := (SEnd, x‾)]} ∪ {[lc := (SEnd, x)]}.

  Lemma lk_tenv : tenv_ofk lk_eta Σl ∪ ∅ = Θl N SEnd x.
  Proof.
    rewrite map_union_empty. apply map_eq. intros o. rewrite lookup_tenv_ofk. unfold Σl, Θl.
    destruct (decide (o = lc)) as [->|H1]; [|destruct (decide (o = ld)) as [->|H2]].
    - rewrite lookup_union_r by (by rewrite lookup_singleton_ne).
      rewrite lookup_union_l' by (by rewrite lookup_singleton_eq). rewrite !lookup_singleton_eq. simpl.
      unfold lk_eta. repeat case_decide; try done; exfalso; tauto.
    - rewrite lookup_union_l' by (by rewrite lookup_singleton_eq).
      rewrite lookup_union_r by (by rewrite lookup_singleton_ne). rewrite !lookup_singleton_eq. simpl.
      unfold lk_eta. repeat case_decide; try done; exfalso; tauto.
    - rewrite !lookup_union_r by (by rewrite lookup_singleton_ne). by rewrite !lookup_singleton_ne.
  Qed.

  Lemma lk_term :
    ptyped (Some N) lk_eta sw_empty Σl (∅, {[+ lk_link +]}) TUnit.
  Proof.
    apply (p_term (Some N) lk_eta sw_empty Σl ∅ ∅ _ TUnit (fadd (Some 0) (Some 0))).
    - constructor.
    - intros o. rewrite dom_empty_L. set_solver.
    - set_solver.
    - intros o Ho Hd. unfold Σl in Ho, Hd. rewrite dom_union_L, !dom_singleton_L in Ho, Hd.
      apply elem_of_union in Ho as [Ho|Ho]; apply elem_of_singleton in Ho as ->;
        apply elem_of_union in Hd as [Hd|Hd]; apply elem_of_singleton in Hd; discriminate Hd.
    - intros o e He. unfold Σl in He. apply lookup_union_Some_raw in He as [He|[_ He]];
        apply lookup_singleton_Some in He as [_ <-]; exact I.
    - set_solver.
    - intros o _. unfold lk_eta. case_decide; simpl; lia.
    - rewrite lk_tenv. exact (lk_typed sw_empty N HN SEnd x).
    - apply sw_empty_ok.
  Qed.

  Lemma lk_partner o y : lk_eta o = (Some 0, Some 0) →
    ptyped (Some N) lk_eta W_cl {[o := (SEnd, y)]}
      (∅, {[+ cl o +]}) TUnit.
  Proof.
    intros Ho. apply (p_term (Some N) lk_eta W_cl _ ∅ ∅ _ TUnit (fadd (Some 0) (Some 1))).
    - constructor.
    - intros o'. rewrite dom_empty_L. set_solver.
    - set_solver.
    - apply pfree_singleton.
    - intros o' e' He. apply lookup_singleton_Some in He as [_ <-]. done.
    - set_solver.
    - intros o' Ho'. rewrite dom_singleton_L, elem_of_singleton in Ho'. subst o'. rewrite Ho. simpl. lia.
    - rewrite map_union_empty.
      assert (tenv_ofk lk_eta {[o := (SEnd, y)]} = {[o := TE SEnd y (Some 0) (Some 0)]}) as ->.
      { apply map_eq. intros o'. rewrite lookup_tenv_ofk. destruct (decide (o' = o)) as [->|Hne].
        - rewrite !lookup_singleton_eq. simpl. by rewrite Ho.
        - by rewrite !lookup_singleton_ne. }
      apply cl_typed, fle_refl.
    - apply sw_empty_ok.
  Qed.

  Lemma chans_of_single o v : chans_of ({[o := v]} : senv) = {[ech o]}.
  Proof. unfold chans_of. by rewrite dom_singleton_L, set_map_singleton_L. Qed.

  Lemma chans_of_none : chans_of (∅ : senv) = ∅.
  Proof. unfold chans_of. by rewrite dom_empty_L, set_map_empty. Qed.

  Lemma senv_dual_single o S y : senv_dual {[o := (S, y)]} = {[edual o := (dual S, y‾)]}.
  Proof. unfold senv_dual. by rewrite map_fmap_singleton, kmap_singleton. Qed.

  (** link ⟨c⁺, d⁻⟩ ∥ close c⁻ ∥ close d⁺, closed at N. *)
  Theorem lk_closed_typed :
    ∃ W, ptyped (Some N) lk_eta W ∅ ({["c"]} ∪ {["d"]}, ({[+ lk_link +]} ⊎ {[+ cl (ENeg "c") +]}) ⊎ {[+ cl (EPos "d") +]}) TUnit.
  Proof.
    pose proof (p_connect (Some N) lk_eta sw_empty
      W_cl {[ld := (SEnd, x‾)]} ∅ {[lc := (SEnd, x)]}
      ∅ ∅ {[+ lk_link +]} {[+ cl (ENeg "c") +]} TUnit) as H1.
    rewrite senv_dual_single, !chans_of_single, chans_of_none, !(right_id_L ∅ (∪)), (left_id_L ∅ (∪)) in H1.
    simpl in H1.
    pose proof (H1 lk_term (lk_partner (ENeg "c") x‾ eq_refl) ltac:(set_solver) ltac:(set_solver)
      ltac:(set_solver) ltac:(set_solver) ltac:(set_solver) ltac:(set_solver)) as H1'. clear H1.
    assert (Hts : ∀ o, o ∈ dom ({[lc := (SEnd, x)]} : senv) → tsum_ok (Some N) (lk_eta o).2 (lk_eta (edual o)).2).
    { intros o Ho. rewrite dom_singleton_L, elem_of_singleton in Ho. subst o. unfold tsum_ok. simpl. lia. }
    pose proof (H1' Hts) as H1''. clear H1'.
    assert (Hwk : wok (Some N) (sw_empty ⊔ W_cl)).
    { apply swf_wok, swf_bare. intros g [Hg|Hg]; destruct Hg. }
    pose proof (H1'' Hwk) as H1. clear H1''.
    pose proof (p_connect (Some N) lk_eta (sw_empty ⊔ W_cl)
      W_cl
      ∅ ∅ {[ld := (SEnd, x‾)]} (∅ ∪ {["c"]}) ∅ ({[+ lk_link +]} ⊎ {[+ cl (ENeg "c") +]}) {[+ cl (EPos "d") +]} TUnit) as H2.
    rewrite senv_dual_single, !chans_of_single, chans_of_none, !(left_id_L ∅ (∪)), pt_dual_dual in H2.
    simpl in H2. eexists. rewrite <-(left_id_L ∅ (∪) (∅ : senv)). apply H2; clear H2.
    - exact H1.
    - apply (lk_partner (EPos "d") x eq_refl).
    - set_solver.
    - set_solver.
    - set_solver.
    - set_solver.
    - set_solver.
    - set_solver.
    - intros o Ho. rewrite dom_singleton_L, elem_of_singleton in Ho. subst o. unfold tsum_ok. simpl. lia.
    - exact (wok_join_bare_r (Some N) _ W_cl ltac:(intros g Hg; exact Hg) (proj2 (ptyped_wf _ _ _ _ _ _ H1))).
  Qed.

  Theorem lk_closed_lock_free : excluded_middle → functional_choice →
    lock_free ({["c"]} ∪ {["d"]}, ({[+ lk_link +]} ⊎ {[+ cl (ENeg "c") +]}) ⊎ {[+ cl (EPos "d") +]}).
  Proof.
    intros EM FC. destruct lk_closed_typed as [W H]. exact (lf_soundness N lk_eta W _ TUnit EM FC H).
  Qed.
End closed.
