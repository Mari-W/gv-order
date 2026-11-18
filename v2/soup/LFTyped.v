(** * The lock-free judgment Σ ⊩^N _ W p : T and its soundness (stage S9,
      proposal §2.12, A.3)

      lf_fundamental : strict W → Σ ⊩^N _ W p : T → Σ ⊪_W p : T
      lf_soundness   : lfworld W → ∅ ⊩^N _ W p : T → lock_free p

    The rules are those of Σ ⊢_W p : T ([ptyped]) with every premise
    static. P-Term types the thread by the merged judgment at Some N with
    the empty future, and adds [guarded t] and [meets ϑ 0 tk] for some
    ticket count tk. P-Connect types the cut at exactly dual types
    ([senv_dual]), and P-Join is P-Connect with the strictness of the join
    replaced as in [ptyped]. No rule renames families. The proof reads
    fsem^N off the typing through [fsem_of_cost] and the live relation
    through [live_fundamental_typed], inside [lf_p_term]. *)

From GV Require Import soup.LFAdequacy.
From GV Require Export soup.LFCompose.

Inductive lfptyped (N : nat) : world → senv → proc → ty → Prop :=
  | p_term W Σ ΘB C0 t T a c ϑ tk :
      types.Types.prim T →
      (∀ o, o ∈ dom ΘB ↔ ech o ∈ C0) → chans_of Σ ## C0 → pfree Σ →
      (∀ c, c ∈ C0 → ∃ S x, ΘB !! (c⁺)%cend = Some (TE S x (Some N)) ∧
                            ΘB !! (c⁻)%cend = Some (TE (dual S) x‾ (Some N))) →
      typed W (Some N) (tenv_of (Some N) Σ ∪ ΘB) hc_empty [] (∅, None) t T a c ϑ →
      guarded t → meets ϑ 0 tk →
      lfptyped N W Σ (C0, {[+ t +]}) T
  | p_connect W1 W2 Σ1 Σ2 ΣC C1 C2 E1 E2 T :
      lfptyped N W1 (Σ1 ∪ ΣC) (C1, E1) T →
      lfptyped N W2 (Σ2 ∪ senv_dual ΣC) (C2, E2) TUnit →
      Σ1 ##ₘ ΣC → Σ2 ##ₘ senv_dual ΣC →
      (∀ o, o ∈ dom ΣC → (o‾)%cend ∉ dom ΣC) →
      chans_of Σ1 ## chans_of Σ2 → chans_of Σ1 ## chans_of ΣC → chans_of Σ2 ## chans_of ΣC →
      C1 ## C2 → C1 ## chans_of Σ2 ∪ chans_of ΣC → C2 ## chans_of Σ1 ∪ chans_of ΣC →
      world_wf W1 → world_wf W2 → w_fams W1 ## w_fams W2 →
      types.Worlds.strict (W1 ⊔ W2) →
      lfptyped N (W1 ⊔ W2) (Σ1 ∪ Σ2) (C1 ∪ C2 ∪ chans_of ΣC, E1 ⊎ E2) T
  | p_join W1 W2 Σ1 Σ2 ΣC C1 C2 E1 E2 T :
      lfptyped N W1 (Σ1 ∪ ΣC) (C1, E1) T →
      lfptyped N W2 (Σ2 ∪ senv_dual ΣC) (C2, E2) TUnit →
      Σ1 ##ₘ ΣC → Σ2 ##ₘ senv_dual ΣC →
      (∀ o, o ∈ dom ΣC → (o‾)%cend ∉ dom ΣC) →
      chans_of Σ1 ## chans_of Σ2 → chans_of Σ1 ## chans_of ΣC → chans_of Σ2 ## chans_of ΣC →
      C1 ## C2 → C1 ## chans_of Σ2 ∪ chans_of ΣC → C2 ## chans_of Σ1 ∪ chans_of ΣC →
      world_wf W1 → world_wf W2 → w_fams W1 ## w_fams W2 →
      types.Worlds.strict W1 → types.Worlds.strict W2 →
      types.Worlds.strict (wrestrict W1 (wshared W1 W2) ⊔ wrestrict W2 (wshared W1 W2)) →
      lfptyped N (W1 ⊔ W2) (Σ1 ∪ Σ2) (C1 ∪ C2 ∪ chans_of ΣC, E1 ⊎ E2) T.

Notation "Σ ⊩^ N '_' W p : T" := (lfptyped N W Σ p T)
  (at level 74, N at level 0, W at level 0, p at level 60, T at level 60,
   format "Σ  ⊩^ N  '_'  W  p  :  T").

(** ** The fundamental theorem *)

Theorem lf_fundamental N W Σ p T : types.Worlds.strict W → Σ ⊩^N _ W p : T → Σ ⊪_W p : T.
Proof.
  intros HW Hty. revert HW. induction Hty as
    [W Σ ΘB C0 t T a c ϑ tk Hp HB HΣ Hpf Hd Ht Hg Hm
    |W1 W2 Σ1 Σ2 ΣC C1 C2 E1 E2 T _ IH1 _ IH2 HD1 HD2 Hf H12 H1C H2C HC HC1 HC2 Hw1 Hw2 Hfam HJ
    |W1 W2 Σ1 Σ2 ΣC C1 C2 E1 E2 T _ IH1 _ IH2 HD1 HD2 Hf H12 H1C H2C HC HC1 HC2 Hw1 Hw2 Hfam HS1 HS2 HJ];
    intros HW.
  - by eapply lf_p_term.
  - destruct (proj1 (p_join_iff_connect W1 W2 Hw1 Hw2 Hfam) HJ) as (HS1 & HS2 & _).
    apply lf_p_connect; auto.
  - apply lf_p_join; auto.
Qed.

(** ** Soundness *)

Theorem lf_soundness N W p T : lfworld W → ∅ ⊩^N _ W p : T → lock_free p.
Proof.
  intros HW Hty. apply (lf_adequacy W T p HW). exact (lf_fundamental N W ∅ p T (proj1 HW) Hty).
Qed.
