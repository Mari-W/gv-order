(** * A link that types once creations choose their tickets (stage 2)

    E-Link asks a1 + m2 > N and a2 + m1 > N of the two linked ends. With
    the creation tickets fixed at N/2 and N − N/2 it types for no even N
    (docs/redesign/algorithmic-plan.md, finding 6.12). A creation now
    chooses its tickets m1 + m2 ≤ N ([e_new_tk]), so the forwarding end of
    each of two channels can hold all N tickets and its partner none.

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
      + apply e_chan, spare_unl. intros y o Hy. by rewrite lookup_nil in Hy.
      + intros o. destruct (decide (o = ld)) as [->|Hne].
        * rewrite lookup_singleton_eq. simpl. split_and!; [done|done|done|lia|f_equal; lia].
        * by rewrite lookup_singleton_ne.
      + constructor.
      + apply e_chan, spare_unl. intros y o Hy. by rewrite lookup_nil in Hy.
      + apply age_sess. simpl. lia.
    - simpl. lia.
    - simpl. lia.
  Qed.
End link.
