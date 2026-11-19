(** * Duality commutes with unfolding (stage S4, ported)

    The flip algebra, duality against renaming, substitution and
    unrolling, [dual_unfoldS], and ≈ as a congruence for [dual]
    ([sequiv_dual]), ported from theories/types/Types.v and
    theories/types/SessionEquiv.v. O-Link and Q-Link compare the two ends
    of a channel by duality up to ≈, so the link redex needs it. *)

From GV Require Export types.Erasure.


Lemma sflip_sflip_mut :
  (∀ T k, sflip_ty k (sflip_ty k T) = T) ∧
  (∀ s k, sflip k (sflip k s) = s).
Proof.
  apply ty_sty_mut_ind; intros; simpl; f_equal; auto;
    repeat (case_decide; simpl); congruence.
Qed.

Definition sflip_sflip := proj2 sflip_sflip_mut.

Lemma sflip_comm_mut :
  (∀ T j k, j ≠ k → sflip_ty j (sflip_ty k T) = sflip_ty k (sflip_ty j T)) ∧
  (∀ s j k, j ≠ k → sflip j (sflip k s) = sflip k (sflip j s)).
Proof.
  apply ty_sty_mut_ind; intros; simpl; try (f_equal; auto with lia; done);
    try (f_equal; apply H; lia);
    repeat (case_decide; simpl); congruence.
Qed.

Definition sflip_comm := proj2 sflip_comm_mut.

Lemma sflip_dual s : ∀ j, sflip j (dual s) = dual (sflip j s).
Proof.
  induction s as [m T|m T| |s IH|a|a| |s1 IH1 s2 IH2|s1 IH1 s2 IH2|s1 IH1 s2 IH2]; intros j; simpl; f_equal;
    auto.
  - rewrite <-IH. apply sflip_comm. lia.
  - repeat (case_decide; simpl); congruence.
  - repeat (case_decide; simpl); congruence.
Qed.

Lemma sfuel_sflip s : ∀ k, sfuel (sflip k s) = sfuel s.
Proof.
  induction s as [m T|m T| |s IH|a|a| |s1 IH1 s2 IH2|s1 IH1 s2 IH2|s1 IH1 s2 IH2]; intros k; simpl; auto;
    try case_decide; done.
Qed.

Lemma dual_involutive s : dual (dual s) = s.
Proof.
  induction s as [m T|m T| |s IH|a|a| |s1 IH1 s2 IH2|s1 IH1 s2 IH2|s1 IH1 s2 IH2]; simpl; f_equal; auto.
  rewrite <-sflip_dual, sflip_sflip. exact IH.
Qed.

Lemma sfuel_dual s : sfuel (dual s) = sfuel s.
Proof.
  induction s as [m T|m T| |s IH|a|a| |s1 IH1 s2 IH2|s1 IH1 s2 IH2|s1 IH1 s2 IH2]; simpl; auto.
  by rewrite sfuel_sflip, IH.
Qed.

(** ** Flip versus renaming and substitution

    [sflip k ∘ sren r] pushes through as [sren r ∘ sflip j] when r
    maps exactly the preimage of k to k ([sflip_sren_iff_mut]) and
    vanishes when nothing maps to k ([sflip_sren_ne_mut]). *)

Lemma upren_iff r j k : (∀ a, r a = k ↔ a = j) → ∀ a, upren r a = S k ↔ a = S j.
Proof.
  intros H0 [|a]; simpl; unfold compose.
  - split; intros Heq; exfalso; lia.
  - destruct (H0 a) as [Hf Hb]. split; intros Heq.
    + f_equal. apply Hf. lia.
    + f_equal. apply Hb. lia.
Qed.

Lemma iter_upren_iff kk r j k :
  (∀ a, r a = k ↔ a = j) → ∀ a, Nat.iter kk upren r a = kk + k ↔ a = kk + j.
Proof.
  revert r. induction kk as [|kk IH]; intros r H; simpl; [done|].
  apply (upren_iff (Nat.iter kk upren r) (kk + j) (kk + k)). by apply IH.
Qed.

Lemma upren_ne r k : (∀ a, r a ≠ k) → ∀ a, upren r a ≠ S k.
Proof. intros H0 [|a]; simpl; [lia|]. unfold compose. specialize (H0 a). lia. Qed.

Lemma iter_upren_ne kk r k : (∀ a, r a ≠ k) → ∀ a, Nat.iter kk upren r a ≠ kk + k.
Proof.
  revert r. induction kk as [|kk IH]; intros r H; simpl; [done|].
  apply (upren_ne (Nat.iter kk upren r) (kk + k)). by apply IH.
Qed.

Lemma sflip_sren_iff_mut :
  (∀ T j k r, (∀ a, r a = k ↔ a = j) →
     sflip_ty k (sren_ty r T) = sren_ty r (sflip_ty j T)) ∧
  (∀ s j k r, (∀ a, r a = k ↔ a = j) →
     sflip k (sren r s) = sren r (sflip j s)).
Proof.
  apply ty_sty_mut_ind; intros; simpl; f_equal; eauto.
  - apply H. by apply iter_upren_iff.
  - apply H. by apply upren_iff.
  - destruct (H a) as [Hf Hb].
    repeat (case_decide; simpl); try done; exfalso; naive_solver.
  - destruct (H a) as [Hf Hb].
    repeat (case_decide; simpl); try done; exfalso; naive_solver.
Qed.

Lemma sflip_sren_ne_mut :
  (∀ T k r, (∀ a, r a ≠ k) → sflip_ty k (sren_ty r T) = sren_ty r T) ∧
  (∀ s k r, (∀ a, r a ≠ k) → sflip k (sren r s) = sren r s).
Proof.
  apply ty_sty_mut_ind; intros; simpl; f_equal; eauto.
  - apply H. by apply iter_upren_ne.
  - apply H. by apply upren_ne.
  - case_decide; [naive_solver|done].
  - case_decide; [naive_solver|done].
Qed.

Lemma dual_sren s : ∀ r, dual (sren r s) = sren r (dual s).
Proof.
  induction s as [m T|m T| |s IH|a|a| |s1 IH1 s2 IH2|s1 IH1 s2 IH2|s1 IH1 s2 IH2]; intros r; simpl; f_equal;
    auto.
  rewrite IH. apply (proj2 sflip_sren_iff_mut).
  intros [|a]; simpl; unfold compose; split; intros; simplify_eq; done.
Qed.

(** [sflip k] slides through a substitution that is the identity at k
    and flip-invariant elsewhere — [sty_up]-lifted substitutions are. *)

Lemma sty_up_flip σ k :
  σ k = SVar k → (∀ a, a ≠ k → sflip k (σ a) = σ a) →
  sty_up σ (S k) = SVar (S k) ∧ ∀ a, a ≠ S k → sflip (S k) (sty_up σ a) = sty_up σ a.
Proof.
  intros H0 H1. split.
  - simpl. unfold compose. by rewrite H0.
  - intros [|a] Ha; simpl; [done|]. unfold compose.
    rewrite (proj2 sflip_sren_iff_mut _ k) by (intros; lia).
    rewrite H1; [done|lia].
Qed.

Lemma iter_sty_up_flip kk σ k :
  σ k = SVar k → (∀ a, a ≠ k → sflip k (σ a) = σ a) →
  Nat.iter kk sty_up σ (kk + k) = SVar (kk + k) ∧
  ∀ a, a ≠ kk + k → sflip (kk + k) (Nat.iter kk sty_up σ a) = Nat.iter kk sty_up σ a.
Proof.
  intros H0 H1. induction kk as [|kk [IH0 IH1]]; simpl; [done|].
  exact (sty_up_flip _ _ IH0 IH1).
Qed.

Lemma sflip_sinst_mut :
  (∀ T k σ, σ k = SVar k → (∀ a, a ≠ k → sflip k (σ a) = σ a) →
     sflip_ty k (sinst_ty σ T) = sinst_ty σ (sflip_ty k T)) ∧
  (∀ s k σ, σ k = SVar k → (∀ a, a ≠ k → sflip k (σ a) = σ a) →
     sflip k (sinst σ s) = sinst σ (sflip k s)).
Proof.
  apply ty_sty_mut_ind; intros; simpl; f_equal; eauto.
  - destruct (iter_sty_up_flip k σ k0 H0 H1). by apply H.
  - destruct (sty_up_flip σ k H0 H1). by apply H.
  - case_decide; simplify_eq; simpl.
    + rewrite H. simpl. case_decide; [done|lia].
    + by rewrite H0.
  - case_decide; simplify_eq; simpl.
    + rewrite H. simpl. case_decide; [done|lia].
    + rewrite sflip_dual. by rewrite H0.
Qed.

(** ** Duality versus substitution and unfolding

    With polarized variables, duality commutes with substitution on
    the nose — same σ on both sides, no closedness needed. *)

Lemma dual_sinst s : ∀ σ, dual (sinst σ s) = sinst σ (dual s).
Proof.
  induction s as [m T|m T| |s IH|a|a| |s1 IH1 s2 IH2|s1 IH1 s2 IH2|s1 IH1 s2 IH2]; intros σ; simpl; f_equal;
    auto.
  - rewrite IH. apply (proj2 sflip_sinst_mut); [done|].
    intros [|a] Ha; simpl; [lia|]. unfold compose.
    apply (proj2 sflip_sren_ne_mut). intros; lia.
  - apply dual_involutive.
Qed.

(** Flipping the head variable of the term matches dualizing what the
    substitution feeds it. *)

Lemma sty_up_dual σ σ' k :
  σ' k = dual (σ k) → (∀ a, a ≠ k → σ' a = σ a) →
  sty_up σ' (S k) = dual (sty_up σ (S k)) ∧ ∀ a, a ≠ S k → sty_up σ' a = sty_up σ a.
Proof.
  intros H0 H1. split.
  - simpl. unfold compose. by rewrite H0, dual_sren.
  - intros [|a] Ha; simpl; [done|]. unfold compose. rewrite H1; [done|lia].
Qed.

Lemma iter_sty_up_dual kk σ σ' k :
  σ' k = dual (σ k) → (∀ a, a ≠ k → σ' a = σ a) →
  Nat.iter kk sty_up σ' (kk + k) = dual (Nat.iter kk sty_up σ (kk + k)) ∧
  ∀ a, a ≠ kk + k → Nat.iter kk sty_up σ' a = Nat.iter kk sty_up σ a.
Proof.
  intros H0 H1. induction kk as [|kk [IH0 IH1]]; simpl; [done|].
  exact (sty_up_dual _ _ _ IH0 IH1).
Qed.

Lemma sinst_sflip_dual_mut :
  (∀ T k σ σ', σ' k = dual (σ k) → (∀ a, a ≠ k → σ' a = σ a) →
     sinst_ty σ T = sinst_ty σ' (sflip_ty k T)) ∧
  (∀ s k σ σ', σ' k = dual (σ k) → (∀ a, a ≠ k → σ' a = σ a) →
     sinst σ s = sinst σ' (sflip k s)).
Proof.
  apply ty_sty_mut_ind; intros; simpl; f_equal; eauto.
  - destruct (iter_sty_up_dual k σ σ' k0 H0 H1). by apply H.
  - destruct (sty_up_dual σ σ' k H0 H1). by apply H.
  - case_decide; simplify_eq; simpl.
    + by rewrite H, dual_involutive.
    + by rewrite H0.
  - case_decide; simplify_eq; simpl.
    + by rewrite H.
    + by rewrite H0.
Qed.

(** The two ends of a µ unroll in lockstep: unrolling substitutes
    µα.s at α and dual (µα.s) at α̅, which is exactly the reading
    [dual] gave the two polarities. *)

Lemma dual_unroll s : dual (unroll s) = unroll (sflip 0 (dual s)).
Proof.
  unfold unroll. rewrite dual_sinst.
  apply (proj2 sinst_sflip_dual_mut); [done|].
  intros [|a] Ha; [lia|done].
Qed.

Lemma dual_unrN k : ∀ s, unrN k (dual s) = dual <$> unrN k s.
Proof.
  induction k as [|k IH]; intros s; simpl; [done|].
  destruct s as [m T|m T| |b|a|a| |s1 s2|s1 s2|s1 s2]; simpl; try done.
  - by rewrite <-dual_unroll, IH.
  - rewrite IH. destruct (unrN k s1) as [h|]; simpl; [|done].
    destruct h as [| | | | | | |h1 h2| |]; simpl; try apply IH; try done.
    destruct h2; done.
Qed.

(** The property CONNECT needs: the two ends of a session unfold in
    lockstep — unconditionally, thanks to the polarized dual. *)
Lemma dual_unfoldS s : dual (unfoldS s) = unfoldS (dual s).
Proof.
  unfold unfoldS. rewrite sfuel_dual, dual_unrN.
  by destruct (unrN (sfuel s) s).
Qed.

(** ** ≈ is a congruence for [dual] *)

Definition vdual (h : hview) : hview :=
  match h with
  | HSkip => HSkip
  | HRcv m T s => HSnd m T (dual s)
  | HSnd m T s => HRcv m T (dual s)
  | HVar a s => HVarD a (dual s)
  | HVarD a s => HVar a (dual s)
  | HPlus a b => HWith (dual a) (dual b)
  | HWith a b => HPlus (dual a) (dual b)
  | HEnd => HEnd
  | HStuck u => HStuck (dual u)
  end.

Lemma view_dual u : view (dual u) = vdual (view u).
Proof. destruct u as [| | | | | | |o r| |]; try done. by destruct o. Qed.

Lemma hd_dual s : hd (dual s) = vdual (hd s).
Proof. unfold hd. by rewrite <-dual_unfoldS, view_dual. Qed.

Lemma aeq_dual n : ∀ s r, aeq n s r → aeq n (dual s) (dual r).
Proof.
  induction n as [|n IH]; intros s r H; [done|].
  unfold aeq in *; fold aeq in *. unfold eq_step in *.
  rewrite !hd_dual.
  hd_cases s; hd_cases r; simpl in *; try done; try congruence;
    intuition (subst; auto).
Qed.

Lemma sequiv_dual s r : sequiv s r → sequiv (dual s) (dual r).
Proof. intros H n. by apply aeq_dual. Qed.
