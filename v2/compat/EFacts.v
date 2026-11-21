(** * Two facts about E for the fundamental theorems (stage S5)

    Both unfold E once and follow every clause, as [Erel_weaken]
    (relation/Closure.v) and [Erel_teq_1] (compat/Blind.v) do. They live
    in a file of their own, so a change of the definition of E has to
    re-prove only this file.

    - [Erel_cover]. The future of E is closed upwards. A point y′ that
      lies at or above a point y of F asks less of a blocked end than y
      does, because x ≺ y and y ≼ y′ give x ≺ y′. The bind lemma puts
      the heads of the frame's environment into the hole's future, and
      a value of a typed grounding holds its ends at or above the static of its type ([Vrel_heads]), so S5 needs E at the static
      heads to give E at the heads of the grounding.
    - [Erel_ty_mono]. E reads its type only through the (stop) clause,
      so V at T included in V at T′ in every world above W gives E at T
      included in E at T′. It is [Erel_teq_1] with the inclusion asked
      only above W, which E-Pack needs, because the facts of its
      constraint hold in W and its extensions only. *)

From GV Require Export relation.Closure.

(** Every point of F′ lies at or above a point of F. *)
Definition fcover (W : world) (F' F : gset point) : Prop :=
  ∀ y', y' ∈ F' → ∃ y, y ∈ F ∧ w_le W y y'.

Lemma fcover_mono W W' F' F : W ⊑ W' → fcover W F' F → fcover W' F' F.
Proof. intros HW H y' Hy. destruct (H y' Hy) as (y & ? & ?). eauto using w_le_mono. Qed.

Lemma w_le_lt_trans W x y z : W ⊢ x ≺ y → w_le W y z → W ⊢ x ≺ z.
Proof. intros H [->|H']; [done|by eapply w_lt_trans]. Qed.

Lemma w_le_trans W x y z : w_le W x y → w_le W y z → w_le W x z.
Proof. intros [->|H] H'; [done|right; by eapply w_le_lt_trans]. Qed.

Lemma ready_t_cover W Θ t F F' : fcover W F' F → ready _ W(Θ ∣ F, t) → ready _ W(Θ ∣ F', t).
Proof.
  intros HF H Hs. destruct (H Hs) as [? [?|Hb]]; split; [done|by left|done|].
  right. intros o S x Ho Hx. destruct (Hb o S x Ho Hx) as [H1 H2]. split; [done|].
  intros y' Hy'. destruct (HF y' Hy') as (y & Hy & Hle). eapply w_le_lt_trans; [|exact Hle]. by apply H2.
Qed.

Section efacts.
  Context (κ : ctable).

  Lemma Erel_cover n : ∀ W Θ T F F' e,
    fcover W F' F → Erel κ n W Θ T F e → Erel κ n W Θ T F' e.
  Proof.
    induction n as [n IHn] using oind. intros W Θ T F F' e HF HE.
    revert W Θ T F e HE F' HF.
    refine (Erel_ind κ n (λ W Θ T F e, ∀ F', fcover W F' F → Erel κ n W Θ T F' e) _).
    intros W Θ T F e H F' HF. apply Erel_iff. intros W1 HW1.
    pose proof (fcover_mono _ _ _ _ HW1 HF) as HF1.
    destruct (H W1 HW1) as (Hs & Hr & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
    assert (∀ c Θ0 T0 e',
      at_cost_E n c (Erel κ) (λ W Θ T F e, Erel κ n W Θ T F e ∧
                                     ∀ F', fcover W F' F → Erel κ n W Θ T F' e) W1 Θ0 T0 F e' →
      at_cost_E n c (Erel κ) (Erel κ n) W1 Θ0 T0 F' e') as Hac.
    { intros c Θ0 T0 e' [A1 A2]. split.
      - intros Hc. by apply A1.
      - intros Hc j Hj. apply (IHn j (oadd_lt _ _ _ Hc Hj) W1 Θ0 T0 F F' e'); [done|by apply A2]. }
    split; [|split; [|unfold Esteps; split_and!]].
    - done.
    - intros Hirr. eapply ready_t_cover; [exact HF1|by apply Hr].
    - intros e' Hst. by apply Hac, H1.
    - intros ℓ c e' Hst Hc g Hg. destruct (H2 ℓ c e' Hst Hc g Hg) as [S HS]. exists S. by apply Hac.
    - intros κf o c e' Hst Hc. destruct (H3 κf o c e' Hst Hc) as (S0 & x & Ho & S & HS).
      exists S0, x. split; [done|]. exists S. by apply Hac.
    - intros v e' Hst. destruct (H4 v e' Hst) as (ΘM & Θr & A1 & A2 & A4 & A5).
      exists ΘM, Θr. split_and!; [done|done| |by apply Hac].
      revert A4. apply Varr_mono; [by intros|by intros|by intros|]. by intros _ ? ? ? ? ? ? [? _].
    - intros o w e' Hst.
      destruct (H5 o w e' Hst) as (S0 & x & m' & U & S & ΘM & Θr & A1 & A2 & A3 & A4 & A6 & A7).
      exists S0, x, m', U, S, ΘM, Θr. split_and!; [done..|by apply Hac].
    - intros o w e' Hst. destruct (H6 o w e' Hst) as (S0 & x & m' & U & S & A1 & A2 & A3).
      exists S0, x, m', U, S. split_and!; [done|done|].
      intros j Θin Hj Hd Hw. pose proof (c_take_pos κ).
      apply (IHn j (c_take_lt κ n j Hj) W1 _ T F F'); [done|by apply A3].
    - intros o e' Hst. destruct (H7 o e' Hst) as (S0 & x & A1 & A2 & A3).
      exists S0, x. split_and!; [done|done|by apply Hac].
    - intros o i e' Hst. destruct (H8 o i e' Hst) as (S0 & x & S1 & S2 & A1 & A2 & A3).
      exists S0, x, S1, S2. split_and!; [done|done|by apply Hac].
    - intros o i e' Hst. destruct (H9 o i e' Hst) as (S0 & x & S1 & S2 & A1 & A2 & A3).
      exists S0, x, S1, S2. split_and!; [done|done|by apply Hac].
    - intros os e' Hst. destruct (H10 os e' Hst) as (o1 & o2 & S1 & S2 & x & A1 & A2 & A3 & A4 & A5 & A6).
      exists o1, o2, S1, S2, x. split_and!; [done..|by apply Hac].
  Qed.

  Lemma Erel_ty_mono n : ∀ W0 T T',
    (∀ m W Θ v, W0 ⊑ W → ole m n → Vrel κ m W Θ T v → Vrel κ m W Θ T' v) →
    ∀ Θ F e, Erel κ n W0 Θ T F e → Erel κ n W0 Θ T' F e.
  Proof.
    induction n as [n IHn] using oind. intros W0 T T' HV Θ F e HE.
    revert Θ F e HE.
    cut (∀ W Θ T0 F e, Erel κ n W Θ T0 F e → W0 ⊑ W → T0 = T → Erel κ n W Θ T' F e).
    { intros H Θ F e HE. eapply H; [exact HE|apply wext_refl|done]. }
    refine (Erel_ind κ n _ _). intros W Θ T0 F e H HW ->. apply Erel_iff. intros W1 HW1.
    assert (W0 ⊑ W1) as HW01 by (by eapply wext_trans).
    destruct (H W1 HW1) as (Hs & Hr & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
    assert (∀ c Θ0 F0 e',
      at_cost_E n c (Erel κ) (λ W Θ T0 F e, Erel κ n W Θ T0 F e ∧
                                     (W0 ⊑ W → T0 = T → Erel κ n W Θ T' F e)) W1 Θ0 T F0 e' →
      at_cost_E n c (Erel κ) (Erel κ n) W1 Θ0 T' F0 e') as Hac.
    { intros c Θ0 F0 e' [A1 A2]. split.
      - intros Hc. by apply A1.
      - intros Hc j Hj. apply (IHn j (oadd_lt _ _ _ Hc Hj) W1 T T'); [|by apply A2].
        intros m W2 Θ2 v HW2 Hm. apply HV; [by eapply wext_trans|exact (ole_trans _ _ _ Hm (oadd_le_l _ _ _ Hj))]. }
    split; [|split; [|unfold Esteps; split_and!]].
    - intros Hirr. apply HV; [done|apply ole_refl|]. by apply Hs.
    - done.
    - intros e' Hst. by apply Hac, H1.
    - intros ℓ c e' Hst Hc g Hg. destruct (H2 ℓ c e' Hst Hc g Hg) as [S HS]. exists S. by apply Hac.
    - intros κf o c e' Hst Hc. destruct (H3 κf o c e' Hst Hc) as (S0 & x & Ho & S & HS).
      exists S0, x. split; [done|]. exists S. by apply Hac.
    - intros v e' Hst. destruct (H4 v e' Hst) as (ΘM & Θr & A1 & A2 & A4 & A5).
      exists ΘM, Θr. split_and!; [done|done| |by apply Hac].
      revert A4. apply Varr_mono; [by intros|by intros|by intros|]. by intros _ ? ? ? ? ? ? [? _].
    - intros o w e' Hst.
      destruct (H5 o w e' Hst) as (S0 & x & m' & U & S & ΘM & Θr & A1 & A2 & A3 & A4 & A6 & A7).
      exists S0, x, m', U, S, ΘM, Θr. split_and!; [done..|by apply Hac].
    - intros o w e' Hst. destruct (H6 o w e' Hst) as (S0 & x & m' & U & S & A1 & A2 & A3).
      exists S0, x, m', U, S. split_and!; [done|done|].
      intros j Θin Hj Hd Hw. pose proof (c_take_pos κ).
      apply (IHn j (c_take_lt κ n j Hj) W1 T T'); [|by apply A3].
      intros m W2 Θ2 v HW2 Hm. apply HV; [by eapply wext_trans|exact (ole_trans _ _ _ Hm (oadd_le_l _ _ _ Hj))].
    - intros o e' Hst. destruct (H7 o e' Hst) as (S0 & x & A1 & A2 & A3).
      exists S0, x. split_and!; [done|done|by apply Hac].
    - intros o i e' Hst. destruct (H8 o i e' Hst) as (S0 & x & S1 & S2 & A1 & A2 & A3).
      exists S0, x, S1, S2. split_and!; [done|done|by apply Hac].
    - intros o i e' Hst. destruct (H9 o i e' Hst) as (S0 & x & S1 & S2 & A1 & A2 & A3).
      exists S0, x, S1, S2. split_and!; [done|done|by apply Hac].
    - intros os e' Hst. destruct (H10 os e' Hst) as (o1 & o2 & S1 & S2 & x & A1 & A2 & A3 & A4 & A5 & A6).
      exists o1, o2, S1, S2, x. split_and!; [done..|by apply Hac].
  Qed.
End efacts.
