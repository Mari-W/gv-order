(** * Contractive session types (item 1 of 2026-11-21)

    A session type is contractive ([scontr]) when every recursion
    variable sits behind an action, a choice or Close, and every
    payload is contractive in turn ([tcontr]). A session variable does
    not guard, because an instance may set it to Skip. µβ.α;β is not
    contractive, and its instance at α := Skip would be µβ.Skip;β.

    The facts here are the ones [typed_sinst] needs.

    - [unrN_sfuel]. [sfuel s] is enough fuel for [unrN] on every
      contractive s, so [hd] reads the head of s at any larger fuel.
    - [scontr_sinst]. Contractive instances keep a type contractive.
    - [sequiv_sinst]. ≈ is closed under [sinst] for contractive types
      and contractive instances.
    - [unfoldS_sinst_*]. Unfolding commutes with [sinst] when the head
      is an action, a choice, Close or Skip.

    Contractivity is the premise that makes [sequiv_sinst] true.
    examples/SinstStuck.v shows two equivalent types that are not
    contractive whose instances are not equivalent. *)

From GV Require Export types.Duality.

(** ** Session renaming and substitution compose *)

Lemma upren_comp r1 r2 a : upren r2 (upren r1 a) = upren (r2 ∘ r1) a.
Proof. by destruct a. Qed.

Lemma iter_upren_comp k r1 r2 a :
  Nat.iter k upren r2 (Nat.iter k upren r1 a) = Nat.iter k upren (r2 ∘ r1) a.
Proof.
  revert r1 r2 a. induction k as [|k IH]; intros r1 r2 a; simpl; [done|].
  rewrite upren_comp. apply upren_ext. intros b. apply IH.
Qed.

Lemma iter_upren_ext k r r' : (∀ a, r a = r' a) → ∀ a, Nat.iter k upren r a = Nat.iter k upren r' a.
Proof. revert r r'. induction k as [|k IH]; intros r r' H a; simpl; [done|]. by apply upren_ext, IH. Qed.

Lemma sren_ext_mut :
  (∀ T r r', (∀ a, r a = r' a) → sren_ty r T = sren_ty r' T) ∧
  (∀ s r r', (∀ a, r a = r' a) → sren r s = sren r' s).
Proof.
  apply ty_sty_mut_ind; intros; simpl; f_equal; auto.
  all: try (apply H; by apply iter_upren_ext).
  all: try (apply H; by apply upren_ext).
Qed.

Lemma sren_sren_mut :
  (∀ T r1 r2, sren_ty r2 (sren_ty r1 T) = sren_ty (r2 ∘ r1) T) ∧
  (∀ s r1 r2, sren r2 (sren r1 s) = sren (r2 ∘ r1) s).
Proof.
  apply ty_sty_mut_ind; intros; simpl; f_equal; auto.
  - rewrite H. apply sren_ext_mut. intros a. apply iter_upren_comp.
  - rewrite H. apply sren_ext_mut. intros a. apply upren_comp.
Qed.

Lemma sren_sren r1 r2 s : sren r2 (sren r1 s) = sren (r2 ∘ r1) s.
Proof. apply sren_sren_mut. Qed.

Lemma sty_up_upren σ r a : sty_up σ (upren r a) = sty_up (σ ∘ r) a.
Proof. by destruct a. Qed.

Lemma iter_sty_up_upren k σ r a :
  Nat.iter k sty_up σ (Nat.iter k upren r a) = Nat.iter k sty_up (σ ∘ r) a.
Proof.
  revert σ r a. induction k as [|k IH]; intros σ r a; simpl; [done|].
  rewrite sty_up_upren. apply sty_up_ext. intros b. apply IH.
Qed.

Lemma sinst_sren_mut :
  (∀ T r σ, sinst_ty σ (sren_ty r T) = sinst_ty (σ ∘ r) T) ∧
  (∀ s r σ, sinst σ (sren r s) = sinst (σ ∘ r) s).
Proof.
  apply ty_sty_mut_ind; intros; simpl; f_equal; auto.
  - rewrite H. apply sinst_ext_mut. intros a. apply iter_sty_up_upren.
  - rewrite H. apply sinst_ext_mut. intros a. apply sty_up_upren.
Qed.

Lemma sinst_sren r σ s : sinst σ (sren r s) = sinst (σ ∘ r) s.
Proof. apply sinst_sren_mut. Qed.

Lemma sren_sty_up r σ a : sren (upren r) (sty_up σ a) = sty_up (sren r ∘ σ) a.
Proof.
  destruct a; simpl; [done|]. unfold compose. rewrite !sren_sren. by apply sren_ext_mut.
Qed.

Lemma iter_sren_sty_up k r σ a :
  sren (Nat.iter k upren r) (Nat.iter k sty_up σ a) = Nat.iter k sty_up (sren r ∘ σ) a.
Proof.
  revert r σ a. induction k as [|k IH]; intros r σ a; simpl; [done|].
  rewrite sren_sty_up. apply sty_up_ext. intros b. apply IH.
Qed.

Lemma sren_sinst_mut :
  (∀ T r σ, sren_ty r (sinst_ty σ T) = sinst_ty (sren r ∘ σ) T) ∧
  (∀ s r σ, sren r (sinst σ s) = sinst (sren r ∘ σ) s).
Proof.
  apply ty_sty_mut_ind; intros; simpl; f_equal; auto.
  - rewrite H. apply sinst_ext_mut. intros a. apply iter_sren_sty_up.
  - rewrite H. apply sinst_ext_mut. intros a. apply sren_sty_up.
  - symmetry. apply dual_sren.
Qed.

Lemma sren_sinst r σ s : sren r (sinst σ s) = sinst (sren r ∘ σ) s.
Proof. apply sren_sinst_mut. Qed.

Lemma sinst_sty_up τ σ a : sinst (sty_up τ) (sty_up σ a) = sty_up (sinst τ ∘ σ) a.
Proof.
  destruct a; simpl; [done|]. unfold compose. rewrite sinst_sren, sren_sinst.
  by apply sinst_ext.
Qed.

Lemma iter_sinst_sty_up k τ σ a :
  sinst (Nat.iter k sty_up τ) (Nat.iter k sty_up σ a) = Nat.iter k sty_up (sinst τ ∘ σ) a.
Proof.
  revert τ σ a. induction k as [|k IH]; intros τ σ a; simpl; [done|].
  rewrite sinst_sty_up. apply sty_up_ext. intros b. apply IH.
Qed.

Lemma sinst_sinst_mut :
  (∀ T σ τ, sinst_ty τ (sinst_ty σ T) = sinst_ty (sinst τ ∘ σ) T) ∧
  (∀ s σ τ, sinst τ (sinst σ s) = sinst (sinst τ ∘ σ) s).
Proof.
  apply ty_sty_mut_ind; intros; simpl; f_equal; auto.
  - rewrite H. apply sinst_ext_mut. intros a. apply iter_sinst_sty_up.
  - rewrite H. apply sinst_ext_mut. intros a. apply sinst_sty_up.
  - unfold compose. by rewrite dual_sinst.
Qed.

Lemma sinst_ty_sinst σ τ T : sinst_ty τ (sinst_ty σ T) = sinst_ty (sinst τ ∘ σ) T.
Proof. apply sinst_sinst_mut. Qed.
Lemma sinst_sinst σ τ s : sinst τ (sinst σ s) = sinst (sinst τ ∘ σ) s.
Proof. apply sinst_sinst_mut. Qed.

Lemma sinst_id_mut :
  (∀ T σ, (∀ a, σ a = SVar a) → sinst_ty σ T = T) ∧
  (∀ s σ, (∀ a, σ a = SVar a) → sinst σ s = s).
Proof.
  assert (∀ σ, (∀ a, σ a = SVar a) → ∀ a, sty_up σ a = SVar a) as Hup
    by (intros σ H [|a]; simpl; [done|]; unfold compose; by rewrite H).
  assert (∀ k σ, (∀ a, σ a = SVar a) → ∀ a, Nat.iter k sty_up σ a = SVar a) as Hit.
  { induction k as [|k IH]; intros σ H; simpl; [done|]. apply Hup. by apply IH. }
  apply ty_sty_mut_ind; intros; simpl; f_equal; eauto.
  all: by rewrite H.
Qed.

Lemma sinst_ids s : sinst SVar s = s.
Proof. by apply sinst_id_mut. Qed.

(** Unrolling commutes with instantiation. *)
Lemma sinst_unroll σ b : sinst σ (unroll b) = unroll (sinst (sty_up σ) b).
Proof.
  unfold unroll. rewrite !sinst_sinst. apply sinst_ext. intros [|a]; simpl; [done|].
  unfold compose. rewrite sinst_sren. rewrite <-(sinst_ids (σ a)) at 1. by apply sinst_ext.
Qed.

(** ** Contractivity *)

(** [sk s]: s may unfold to Skip with no action, reading a variable
    as Skip. *)
Fixpoint sk (s : sty) : bool :=
  match s with
  | SSkip | SVar _ | SVarD _ => true
  | SSeq a b => sk a && sk b
  | SMu b => sk b
  | _ => false
  end.

(** [ugv a s]: the variable a occurs in s with no action before it. *)
Fixpoint ugv (a : nat) (s : sty) : bool :=
  match s with
  | SVar b | SVarD b => bool_decide (b = a)
  | SSeq s1 s2 => ugv a s1 || (sk s1 && ugv a s2)
  | SMu b => ugv (S a) b
  | _ => false
  end.

(** [uc s]: the number of variable occurrences with no action before
    them. Each variable head of an unfolding lowers it. *)
Fixpoint uc (s : sty) : nat :=
  match s with
  | SVar _ | SVarD _ => 1
  | SSeq a b => uc a + (if sk a then uc b else 0)
  | SMu b => uc b
  | _ => 0
  end.

Fixpoint tcontr (T : ty) : bool :=
  match T with
  | TUnit => true
  | TLolli _ _ _ T1 U _ | TProd T1 U | TSum T1 U => tcontr T1 && tcontr U
  | TBox _ _ _ _ _ U => tcontr U
  | TSess s _ _ _ => scontr s
  | TEx _ _ _ T1 => tcontr T1
  end
with scontr (s : sty) : bool :=
  match s with
  | SRcv _ T | SSnd _ T => tcontr T
  | SEnd | SVar _ | SVarD _ | SSkip => true
  | SMu b => negb (ugv 0 b) && scontr b
  | SSeq a b | SPlus a b | SWith a b => scontr a && scontr b
  end.

Lemma Is_true_andb (a b : bool) : (a && b) ↔ a ∧ b.
Proof. destruct a, b; simpl; naive_solver. Qed.

Lemma Is_true_negb (a : bool) : negb a ↔ ¬ a.
Proof. destruct a; simpl; naive_solver. Qed.

Ltac contr_simpl :=
  repeat match goal with
  | H : Is_true (_ && _) |- _ => apply Is_true_andb in H as [? ?]
  | H : Is_true (negb _) |- _ => apply Is_true_negb in H
  | |- Is_true (_ && _) => apply Is_true_andb; split
  | |- Is_true (negb _) => apply Is_true_negb
  end.

(** *** Renaming *)

Lemma sk_sren r s : sk (sren r s) = sk s.
Proof. revert r. induction s; intros r; simpl; try done; by rewrite ?IHs1, ?IHs2, ?IHs. Qed.

Lemma ugv_sren s : ∀ r a, ugv a (sren r s) → ∃ b, r b = a ∧ ugv b s.
Proof.
  induction s; intros r a' H; simpl in *; try done.
  - apply IHs in H as ([|b] & Hb & H); [done|]. exists b. simpl in Hb. split; [lia|done].
  - apply bool_decide_unpack in H. exists a. split; [done|]. by apply bool_decide_pack.
  - apply bool_decide_unpack in H. exists a. split; [done|]. by apply bool_decide_pack.
  - rewrite sk_sren in H. destruct (ugv a' (sren r s1)) eqn:E1.
    + destruct (IHs1 r a') as (b & Hb & H1); [by rewrite E1|]. exists b. split; [done|]. simpl. by destruct (ugv b s1).
    + simpl in H. destruct (sk s1); [|done]. destruct (IHs2 r a' H) as (b & Hb & H2).
      exists b. split; [done|]. destruct (ugv b s1); done.
Qed.

Lemma uc_sren r s : uc (sren r s) = uc s.
Proof. revert r. induction s; intros r; simpl; try done; by rewrite ?IHs1, ?IHs2, ?IHs, ?sk_sren. Qed.

Lemma contr_sren_mut :
  (∀ T r, tcontr T → tcontr (sren_ty r T)) ∧ (∀ s r, scontr s → scontr (sren r s)).
Proof.
  apply ty_sty_mut_ind; intros; simpl in *; contr_simpl; auto.
  intros Hu. apply ugv_sren in Hu as ([|b] & Hb & Hu); [done|]. simpl in Hb. lia.
Qed.

Lemma scontr_sren r s : scontr s → scontr (sren r s).
Proof. apply contr_sren_mut. Qed.

(** *** Flipping and duality *)

Lemma sk_sflip s : ∀ k, sk (sflip k s) = sk s.
Proof. induction s; intros k; simpl; try (by destruct (decide (a = k))); try done; try (by rewrite IHs); by rewrite IHs1, IHs2. Qed.

Lemma ugv_sflip s : ∀ k a, ugv a (sflip k s) = ugv a s.
Proof.
  induction s; intros k a'; simpl; try (by destruct (decide (a = k))); try done; try apply IHs.
  by rewrite IHs1, IHs2, sk_sflip.
Qed.

Lemma uc_sflip s : ∀ k, uc (sflip k s) = uc s.
Proof. induction s; intros k; simpl; try (by destruct (decide (a = k))); try done; try (by rewrite IHs); by rewrite IHs1, IHs2, ?sk_sflip. Qed.

Lemma contr_sflip_mut :
  (∀ T k, tcontr (sflip_ty k T) = tcontr T) ∧ (∀ s k, scontr (sflip k s) = scontr s).
Proof.
  apply ty_sty_mut_ind; intros; simpl in *; try (by destruct (decide (a = k))); try done; try congruence.
  by rewrite ugv_sflip, H.
Qed.

Lemma sk_dual s : sk (dual s) = sk s.
Proof. induction s; simpl; try done; try (by rewrite sk_sflip, IHs); by rewrite IHs1, IHs2. Qed.

Lemma ugv_dual s : ∀ a, ugv a (dual s) = ugv a s.
Proof.
  induction s; intros a'; simpl; try done.
  - by rewrite ugv_sflip, IHs.
  - by rewrite IHs1, IHs2, sk_dual.
Qed.

Lemma uc_dual s : uc (dual s) = uc s.
Proof. induction s; simpl; try done; try (by rewrite uc_sflip, IHs); by rewrite IHs1, IHs2, ?sk_dual. Qed.

Lemma scontr_dual s : scontr (dual s) = scontr s.
Proof.
  induction s; simpl; try done; try congruence.
  by rewrite (proj2 contr_sflip_mut), ugv_sflip, ugv_dual, IHs.
Qed.

(** *** Instantiation *)

Lemma sk_sinst σ s : sk (sinst σ s) → sk s.
Proof.
  revert σ. induction s; intros σ H; cbn [sinst sk] in *; try done.
  - by apply IHs in H.
  - apply Is_true_andb in H as [H1 H2]. apply Is_true_andb. split; eauto.
Qed.

Lemma ugv_sinst s : ∀ σ a, ugv a (sinst σ s) → ∃ b, ugv b s ∧ ugv a (σ b).
Proof.
  induction s; intros σ a' H; simpl in *; try done.
  - apply IHs in H as ([|b] & Hb & H); [done|]. simpl in H. unfold compose in H.
    apply ugv_sren in H as (c & Hc & H). injection Hc as ->. exists b. done.
  - exists a. split; [by apply bool_decide_pack|done].
  - rewrite ugv_dual in H. exists a. split; [by apply bool_decide_pack|done].
  - destruct (ugv a' (sinst σ s1)) eqn:E1.
    + destruct (IHs1 σ a') as (b & Hb & H1); [by rewrite E1|]. exists b. split; [|done]. simpl. by destruct (ugv b s1).
    + simpl in H. destruct (sk (sinst σ s1)) eqn:Es; [|done].
      destruct (IHs2 σ a' H) as (b & Hb & H2). exists b. split; [|done].
      assert (sk s1) as Hs by (apply (sk_sinst σ); by rewrite Es).
      destruct (ugv b s1), (sk s1); simpl; done.
Qed.

Lemma scontr_sty_up σ : (∀ a, scontr (σ a)) → ∀ a, scontr (sty_up σ a).
Proof. intros H [|a]; simpl; [done|]. by apply scontr_sren. Qed.

Lemma scontr_iter_sty_up k σ : (∀ a, scontr (σ a)) → ∀ a, scontr (Nat.iter k sty_up σ a).
Proof. revert σ. induction k as [|k IH]; intros σ H; simpl; [done|]. by apply scontr_sty_up, IH. Qed.

Lemma contr_sinst_mut :
  (∀ T σ, (∀ a, scontr (σ a)) → tcontr T → tcontr (sinst_ty σ T)) ∧
  (∀ s σ, (∀ a, scontr (σ a)) → scontr s → scontr (sinst σ s)).
Proof.
  apply ty_sty_mut_ind; intros; simpl in *; contr_simpl; eauto using scontr_iter_sty_up.
  - intros Hu. apply ugv_sinst in Hu as ([|b] & Hb & Hu); [done|]. simpl in Hu.
    unfold compose in Hu. apply ugv_sren in Hu as (c & Hc & _). done.
  - apply H; [by apply scontr_sty_up|done].
  - by rewrite scontr_dual.
Qed.

Lemma tcontr_sinst σ T : (∀ a, scontr (σ a)) → tcontr T → tcontr (sinst_ty σ T).
Proof. intros. by apply contr_sinst_mut. Qed.
Lemma scontr_sinst σ s : (∀ a, scontr (σ a)) → scontr s → scontr (sinst σ s).
Proof. intros. by apply contr_sinst_mut. Qed.

Lemma scontr_unroll b : scontr (SMu b) → scontr (unroll b).
Proof.
  intros H. apply scontr_sinst; [intros [|a]; [exact H|done]|].
  cbn [scontr] in H. by apply Is_true_andb in H as [_ ?].
Qed.

Lemma scontr_slist ss : Forall (λ s, scontr s) ss → ∀ a, scontr (slist ss a).
Proof.
  intros H a. unfold slist. destruct (ss !! a) eqn:E; [|done].
  by apply (Forall_lookup_1 _ _ _ _ H E).
Qed.

(** *** Point instantiation and erasure *)

Lemma tcontr_pinst σ T : tcontr (pinst_ty σ T) = tcontr T.
Proof. revert σ. induction T; intros σ; simpl; try done; congruence. Qed.

Lemma tcontr_ty_inst xs T : tcontr (ty_inst xs T) = tcontr T.
Proof. apply tcontr_pinst. Qed.

Lemma sk_df s : sk (sty_df s) = sk s.
Proof. induction s; simpl; try done; congruence. Qed.

Lemma ugv_df s : ∀ a, ugv a (sty_df s) = ugv a s.
Proof. induction s; intros a'; simpl; try done; try (by rewrite IHs); by rewrite IHs1, IHs2, ?sk_df. Qed.

Lemma contr_df_mut :
  (∀ T, tcontr (ty_df T) = tcontr T) ∧ (∀ s, scontr (sty_df s) = scontr s).
Proof. apply ty_sty_mut_ind; intros; simpl in *; try done; try congruence. by rewrite ugv_df, H. Qed.

Lemma tcontr_df T : tcontr (ty_df T) = tcontr T.
Proof. apply contr_df_mut. Qed.
Lemma scontr_df s : scontr (sty_df s) = scontr s.
Proof. apply contr_df_mut. Qed.

(** ** Fuel *)

Lemma unrN_mono k : ∀ s h, unrN k s = Some h → unrN (S k) s = Some h.
Proof.
  induction k as [|k IH]; intros s h H; [done|].
  destruct s as [?m ?T|?m ?T| |b|?a|?a| |s1 s2|s1 s2|s1 s2]; cbn [unrN] in *; try done.
  - by apply IH.
  - destruct (unrN k s1) as [h1|] eqn:E1; [|done]. rewrite (IH _ _ E1).
    destruct h1; try done. by apply IH.
Qed.

Lemma unrN_mono_le k k' s h : k ≤ k' → unrN k s = Some h → unrN k' s = Some h.
Proof. intros Hk H. induction Hk; [done|]. by apply unrN_mono. Qed.

(** What [unrN] returns has a head. *)
Definition hok (h : sty) : Prop :=
  match view h with HStuck _ => False | _ => True end.

Lemma hseq_hok h s2 : hok h → h ≠ SSkip → hok (hseq h s2).
Proof.
  unfold hok. destruct h as [| | | | | | |o r| |]; simpl; try done.
  destruct o, r; simpl; done.
Qed.

Lemma unrN_hok k : ∀ s h, unrN k s = Some h → hok h.
Proof.
  induction k as [|k IH]; intros s h H; [done|].
  destruct s as [?m ?T|?m ?T| |b|?a|?a| |s1 s2|s1 s2|s1 s2]; cbn [unrN] in H; try (injection H as <-; unfold hok; simpl; done).
  - by eapply IH.
  - destruct (unrN k s1) as [h1|] eqn:E1; [|done].
    pose proof (IH _ _ E1) as Hh.
    destruct h1 as [| | | | | | |o r| |]; try (unfold hok in Hh; simpl in Hh; done); try (by eapply IH).
    all: injection H as <-; try done; unfold hok in *; simpl in *; try done; destruct o, r; simpl in *; done.
Qed.

Lemma unrN_skip_sk k : ∀ s, unrN k s = Some SSkip → sk s.
Proof.
  induction k as [|k IH]; intros s H; [done|].
  destruct s as [?m ?T|?m ?T| |b|?a|?a| |s1 s2|s1 s2|s1 s2]; cbn [unrN] in H; try done.
  - apply IH in H. by apply (sk_sinst _ _ H).
  - destruct (unrN k s1) as [h1|] eqn:E1; [|done].
    destruct h1 as [| | | | | | |o r| |]; simpl in H; try discriminate H; try (destruct r; discriminate H).
    cbn [sk]. apply Is_true_andb. split; by apply IH.
Qed.

Definition isvar (s : sty) : Prop :=
  match s with SVar _ | SVarD _ => True | _ => False end.

Lemma isvar_dual s : isvar s → isvar (dual s).
Proof. by destruct s. Qed.

Lemma sfuel_pos s : 1 ≤ sfuel s.
Proof. destruct s; simpl; lia. Qed.

(** The fuel of a contractive type suffices, also under an instance
    that sets the unguarded variables to variables. *)
Lemma unrN_sinst_var s : ∀ σ k, scontr s → (∀ a, ugv a s → isvar (σ a)) → sfuel s ≤ k →
  is_Some (unrN k (sinst σ s)).
Proof.
  induction s; intros σ k Hc Hv Hk; (destruct k as [|k]; [exfalso; cbn [sfuel] in Hk; lia|]);
    cbn [sinst unrN]; try by eauto.
  - cbn [scontr] in Hc. apply Is_true_andb in Hc as [Hu Hc]. apply Is_true_negb in Hu.
    rewrite <-sinst_unroll. unfold unroll. rewrite sinst_sinst.
    apply IHs; [done| |simpl in Hk; lia].
    intros [|a] Ha; [done|]. simpl. unfold compose. simpl. by apply Hv.
  - specialize (Hv a). simpl in Hv. destruct (σ a); try done; exfalso; apply Hv; by apply bool_decide_pack.
  - specialize (Hv a). simpl in Hv. destruct (σ a); simpl; try done; exfalso; apply Hv; by apply bool_decide_pack.
  - cbn [scontr] in Hc. apply Is_true_andb in Hc as [Hc1 Hc2]. simpl in Hk.
    destruct (IHs1 σ k Hc1) as [h1 E1]; [intros a Ha; apply Hv; cbn [ugv]; by destruct (ugv a s1)|lia|].
    rewrite E1. destruct h1; try by eauto.
    apply IHs2; [done| |lia]. intros a Ha. apply Hv. simpl.
    pose proof (sk_sinst _ _ (unrN_skip_sk _ _ E1)) as Hs.
    destruct (ugv a s1), (sk s1); simpl; done.
Qed.

Lemma unrN_sfuel s : scontr s → ∃ h, unrN (sfuel s) s = Some h.
Proof.
  intros Hc. destruct (unrN_sinst_var s SVar (sfuel s) Hc) as [h E]; [done|done|].
  rewrite sinst_ids in E. eauto.
Qed.

(** At any fuel above [sfuel s], [unrN] gives [unfoldS s]. *)
Lemma unrN_unfoldS s k : scontr s → sfuel s ≤ k → unrN k s = Some (unfoldS s).
Proof.
  intros Hc Hk. destruct (unrN_sfuel s Hc) as [h E]. unfold unfoldS. rewrite E.
  by apply (unrN_mono_le (sfuel s)).
Qed.

Lemma unrN_det k k' s h h' : unrN k s = Some h → unrN k' s = Some h' → h = h'.
Proof.
  intros H H'. destruct (decide (k ≤ k')).
  - apply (unrN_mono_le _ k') in H; [|done]. congruence.
  - apply (unrN_mono_le _ k) in H'; [|lia]. congruence.
Qed.

Lemma unrN_unfoldS' s k h : scontr s → unrN k s = Some h → unfoldS s = h.
Proof.
  intros Hc H. eapply unrN_det; [|exact H]. by apply unrN_unfoldS.
Qed.

(** Unfolding keeps contractivity. *)
Lemma hseq_scontr h s2 : scontr h → scontr s2 → scontr (hseq h s2).
Proof.
  intros H1 H2. destruct h as [| | | | | | |o r| |]; simpl; try done.
  - destruct r; cbn [scontr] in *; apply Is_true_andb in H1 as [? ?]; contr_simpl; done.
  - cbn [scontr] in *. apply Is_true_andb in H1 as [? ?]. contr_simpl; done.
  - cbn [scontr] in *. apply Is_true_andb in H1 as [? ?]. contr_simpl; done.
Qed.

Lemma unrN_scontr k : ∀ s h, unrN k s = Some h → scontr s → scontr h.
Proof.
  induction k as [|k IH]; intros s h H Hc; [done|].
  destruct s as [?m ?T|?m ?T| |b|?a|?a| |s1 s2|s1 s2|s1 s2]; cbn [unrN] in H;
    try (injection H as <-; first [exact Hc|cbn [scontr] in *; repeat (apply Is_true_andb; split); done]).
  - eapply IH; [exact H|]. by apply scontr_unroll.
  - cbn [scontr] in Hc. apply Is_true_andb in Hc as [Hc1 Hc2].
    destruct (unrN k s1) as [h1|] eqn:E1; [|done].
    pose proof (hseq_scontr h1 s2 (IH _ _ E1 Hc1) Hc2) as Hh.
    destruct h1; first [by eapply IH|injection H as <-; exact Hh].
Qed.

Lemma unfoldS_scontr s : scontr s → scontr (unfoldS s).
Proof. intros Hc. destruct (unrN_sfuel s Hc) as [h E]. unfold unfoldS. rewrite E. by eapply unrN_scontr. Qed.

Lemma unfoldS_hok s : scontr s → hok (unfoldS s).
Proof. intros Hc. destruct (unrN_sfuel s Hc) as [h E]. unfold unfoldS. rewrite E. by eapply unrN_hok. Qed.

(** The parts of the head of a contractive type are contractive. *)
Definition hv_contr (v : hview) : Prop :=
  match v with
  | HRcv _ T s' | HSnd _ T s' => tcontr T ∧ scontr s'
  | HVar _ s' | HVarD _ s' => scontr s'
  | HPlus a b | HWith a b => scontr a ∧ scontr b
  | HSkip | HEnd => True
  | HStuck _ => False
  end.

Lemma hd_contr s : scontr s → hv_contr (hd s).
Proof.
  intros Hc. pose proof (unfoldS_scontr s Hc) as H1. pose proof (unfoldS_hok s Hc) as H2.
  unfold hd, hok in *. destruct (unfoldS s) as [| | | | | | |o r| |]; simpl in *; try done;
    contr_simpl; try done.
  destruct o; simpl in *; contr_simpl; done.
Qed.

(** Contractive types are contractive in the sense of [hcontractive]. *)
Lemma scontr_hcontractive s : scontr s → hcontractive s.
Proof.
  intros Hc n. revert s Hc. induction n as [|n IH]; intros s Hc; [done|].
  simpl. unfold hc_step. pose proof (hd_contr s Hc) as H.
  destruct (hd s); simpl in *; intuition auto.
Qed.

(** ** Bisimulation up to ≈ *)

Definition eq_view (τ : sty → sty → Prop) (v w : hview) : Prop :=
  match v, w with
  | HSkip, HSkip | HEnd, HEnd => True
  | HRcv m T s', HRcv m' U r' | HSnd m T s', HSnd m' U r' =>
      m = m' ∧ eqT τ T U ∧ τ s' r'
  | HVar a s', HVar a' r' | HVarD a s', HVarD a' r' => a = a' ∧ τ s' r'
  | HPlus s1 s2, HPlus r1 r2 | HWith s1 s2, HWith r1 r2 => τ s1 r1 ∧ τ s2 r2
  | HStuck u, HStuck v => u = v
  | _, _ => False
  end.

Lemma eq_step_view τ s r : eq_step τ s r = eq_view τ (hd s) (hd r).
Proof. done. Qed.

Lemma eq_view_mono τ τ' v w : (∀ a b, τ a b → τ' a b) → eq_view τ v w → eq_view τ' v w.
Proof. intros Hτ. destruct v, w; simpl; try done; intuition eauto using eqT_mono. Qed.

Lemma eq_view_refl τ v : (∀ s, τ s s) → eq_view τ v v.
Proof. intros Hτ. destruct v; simpl; try done; split_and?; auto using eqT_refl. Qed.

Lemma eqT_lim (ρ : nat → sty → sty → Prop) T : ∀ U,
  (∀ n, eqT (ρ n) T U) → eqT (λ s r, ∀ n, ρ n s r) T U.
Proof.
  induction T as [|ub lb c T1 IH1 T2 IH2 a|T1 IH1 T2 IH2|T1 IH1 T2 IH2|n k C ub c T1 IH1|s x a mt|lb n C T1 IH1];
    intros [|ub' lb' c' U1 U2 a'|U1 U2|U1 U2|n' k' C' ub' c' U1|r y a' mt'|lb' n' C' U1] H;
    try (by destruct (H 0)); simpl in *.
  - destruct (H 0) as (-> & -> & -> & -> & _). split_and!; try done.
    + apply IH1. intros j. apply (H j).
    + apply IH2. intros j. apply (H j).
  - split; [apply IH1|apply IH2]; intros j; apply (H j).
  - split; [apply IH1|apply IH2]; intros j; apply (H j).
  - destruct (H 0) as (-> & -> & -> & -> & -> & H0). split_and!; try done.
    destruct k'; [|done]. apply IH1. intros j. apply (H j).
  - destruct (H 0) as (-> & -> & -> & _). split_and!; try done. intros j. apply (H j).
  - destruct (H 0) as (-> & -> & -> & _). split_and!; try done. apply IH1. intros j. apply (H j).
Qed.

Lemma sequiv_hd s r : sequiv s r → eq_step sequiv s r.
Proof.
  intros H. assert (∀ n, eq_step (aeq n) s r) as Hn by (intros n; apply (H (S n))).
  rewrite eq_step_view. unfold eq_step in Hn. destruct (hd s), (hd r); try (by destruct (Hn 0)); simpl.
  - destruct (Hn 0) as (-> & _). split_and!; [done|apply eqT_lim; intros j; apply (Hn j)|intros j; apply (Hn j)].
  - destruct (Hn 0) as (-> & _). split_and!; [done|apply eqT_lim; intros j; apply (Hn j)|intros j; apply (Hn j)].
  - destruct (Hn 0) as (-> & _). split; [done|intros j; apply (Hn j)].
  - destruct (Hn 0) as (-> & _). split; [done|intros j; apply (Hn j)].
  - split; intros j; apply (Hn j).
  - split; intros j; apply (Hn j).
Qed.

Lemma eqT_comp ρ1 ρ2 T : ∀ U V, eqT ρ1 T U → eqT ρ2 U V → eqT (λ x z, ∃ y, ρ1 x y ∧ ρ2 y z) T V.
Proof.
  induction T; intros [] []; simpl; try done; try naive_solver.
  intros (-> & -> & -> & -> & -> & H1) (-> & -> & -> & -> & -> & H2). split_and!; try done.
  match goal with |- match ?k with _ => _ end => destruct k end; [by eapply IHT|congruence].
Qed.

Lemma eq_view_comp τ1 τ2 v1 : ∀ v2 v3, eq_view τ1 v1 v2 → eq_view τ2 v2 v3 →
  eq_view (λ x z, ∃ y, τ1 x y ∧ τ2 y z) v1 v3.
Proof.
  intros v2 v3. destruct v1, v2; try done; destruct v3; try done; simpl; try congruence;
    intuition (subst; eauto using eqT_comp).
Qed.

Definition upto (τ : sty → sty → Prop) (a b : sty) : Prop :=
  sequiv a b ∨ ∃ a' b', sequiv a a' ∧ τ a' b' ∧ sequiv b' b.

Lemma upto_refl τ s : upto τ s s.
Proof. left. apply sequiv_refl. Qed.

Lemma upto_in τ s r : τ s r → upto τ s r.
Proof. intros H. right. exists s, r. split_and!; auto using sequiv_refl. Qed.

Lemma upto_equiv τ s s' r' r : sequiv s s' → τ s' r' → sequiv r' r → upto τ s r.
Proof. intros. right. eauto. Qed.

(** ≈ on both sides of an [upto] pair stays in [upto]. *)
Lemma eq_view_upto_comp τ v1 v2 v3 v4 :
  eq_view sequiv v1 v2 → eq_view (upto τ) v2 v3 → eq_view sequiv v3 v4 → eq_view (upto τ) v1 v4.
Proof.
  intros H1 H2 H3. eapply eq_view_mono; [|exact (eq_view_comp _ _ _ _ _ H1 (eq_view_comp _ _ _ _ _ H2 H3))].
  intros x z (y & Hxy & (w & Hyw & Hwz)).
  destruct Hyw as [Hyw|(y' & w' & G1 & G2 & G3)].
  - left. eapply sequiv_trans; [exact Hxy|]. by eapply sequiv_trans.
  - right. exists y', w'. split_and!; [by eapply sequiv_trans|done|by eapply sequiv_trans].
Qed.

Lemma sequiv_upto τ : (∀ s r, τ s r → eq_step (upto τ) s r) → ∀ s r, τ s r → sequiv s r.
Proof.
  intros Hτ s r H. apply (sequiv_coind (upto τ)); [|by apply upto_in].
  intros a b [Hab|(a' & b' & H1 & H2 & H3)].
  - eapply eq_step_mono; [|apply sequiv_hd, Hab]. intros; by left.
  - rewrite eq_step_view. eapply eq_view_upto_comp; [apply (sequiv_hd _ _ H1)|apply (Hτ _ _ H2)|apply (sequiv_hd _ _ H3)].
Qed.

Lemma sequiv_hd_eq s r : hd s = hd r → sequiv s r.
Proof.
  intros H. apply (sequiv_upto (λ s r, hd s = hd r)); [|done].
  intros x y Hxy. rewrite eq_step_view, Hxy. apply eq_view_refl, upto_refl.
Qed.

(** ** The head of a sequence *)

Definition sseq' (r b : sty) : sty := match r with SSkip => b | _ => SSeq r b end.

Definition hseqv (v : hview) (b : sty) : hview :=
  match v with
  | HSkip => hd b
  | HRcv m T r => HRcv m T (sseq' r b)
  | HSnd m T r => HSnd m T (sseq' r b)
  | HVar a r => HVar a (sseq' r b)
  | HVarD a r => HVarD a (sseq' r b)
  | HPlus x y => HPlus (SSeq x b) (SSeq y b)
  | HWith x y => HWith (SSeq x b) (SSeq y b)
  | HEnd => HEnd
  | HStuck u => HStuck (SSeq u b)
  end.

Lemma hd_seq a b : scontr a → scontr b → hd (SSeq a b) = hseqv (hd a) b.
Proof.
  intros Ha Hb. pose proof (unfoldS_hok a Ha) as Hok.
  unfold hd at 1 2. unfold unfoldS at 1. cbn [sfuel unrN].
  rewrite (unrN_unfoldS a (sfuel a + sfuel b)) by (done||lia).
  unfold hok in Hok. destruct (unfoldS a) as [| | | | | | |o r| |]; simpl in Hok; try done.
  - simpl. unfold hd. by rewrite (unrN_unfoldS b (sfuel a + sfuel b)) by (done||lia).
  - destruct o; try done; destruct r; done.
Qed.

Lemma hd_skip : hd SSkip = HSkip.
Proof. done. Qed.
Lemma hd_end : hd SEnd = HEnd.
Proof. done. Qed.
Lemma hd_plus x y : hd (SPlus x y) = HPlus x y.
Proof. done. Qed.
Lemma hd_with x y : hd (SWith x y) = HWith x y.
Proof. done. Qed.
Lemma hd_rcv m T : hd (SRcv m T) = HRcv m T SSkip.
Proof. done. Qed.
Lemma hd_snd m T : hd (SSnd m T) = HSnd m T SSkip.
Proof. done. Qed.

Lemma scontr_sseq' r b : scontr r → scontr b → scontr (sseq' r b).
Proof. intros. destruct r; try done; cbn [sseq' scontr]; apply Is_true_andb; split; done. Qed.

Ltac sc :=
  repeat match goal with
  | |- Is_true (scontr (SSeq _ _)) => cbn [scontr]; apply Is_true_andb; split
  | |- Is_true (scontr (SPlus _ _)) => cbn [scontr]; apply Is_true_andb; split
  | |- Is_true (scontr (SWith _ _)) => cbn [scontr]; apply Is_true_andb; split
  | |- Is_true (scontr SSkip) => exact I
  | |- Is_true (scontr SEnd) => exact I
  | |- Is_true (scontr (sinst _ _)) => apply scontr_sinst
  | |- Is_true (tcontr (sinst_ty _ _)) => apply tcontr_sinst
  | |- Is_true (scontr (dual _)) => rewrite scontr_dual
  | |- Is_true (scontr (sseq' _ _)) => apply scontr_sseq'
  end; try done.

Lemma sseq'_cases r : r = SSkip ∨ ∀ b, sseq' r b = SSeq r b.
Proof. destruct r; first [by left|right; done]. Qed.

Lemma seq_skip_l b : scontr b → sequiv (SSeq SSkip b) b.
Proof. intros Hb. apply sequiv_hd_eq. by rewrite hd_seq. Qed.

Lemma sseq'_sequiv r b : scontr r → scontr b → sequiv (sseq' r b) (SSeq r b).
Proof. intros Hr Hb. destruct r; try apply sequiv_refl. apply sequiv_sym. by apply seq_skip_l. Qed.

Lemma seq_skip_r a : scontr a → sequiv (SSeq a SSkip) a.
Proof.
  intros Ha. apply (sequiv_upto (λ x y, ∃ a, scontr a ∧ x = SSeq a SSkip ∧ y = a)); [|eauto].
  intros x y (a' & Ha' & -> & ->). rewrite eq_step_view, hd_seq by done.
  pose proof (hd_contr a' Ha') as Hv. destruct (hd a'); simpl in *; try done.
  all: split_and?; try done; try (apply eqT_refl; intros; apply upto_refl).
  all: try (eapply upto_equiv; [apply sseq'_sequiv; first [done|apply Hv]|by eauto 10|apply sequiv_refl]).
  all: try (apply upto_in; eexists; split_and!; [apply Hv|done|done]).
  all: destruct Hv as [? ?].
  all: try (eapply upto_equiv; [apply sseq'_sequiv; done|by eauto 10|apply sequiv_refl]).
  all: apply upto_in; eauto.
Qed.

Lemma seq_assoc a b c : scontr a → scontr b → scontr c →
  sequiv (SSeq (SSeq a b) c) (SSeq a (SSeq b c)).
Proof.
  intros Ha Hb Hc.
  apply (sequiv_upto (λ x y, ∃ a b c, scontr a ∧ scontr b ∧ scontr c ∧
    x = SSeq (SSeq a b) c ∧ y = SSeq a (SSeq b c))); [|by eauto 10].
  intros x y (a' & b' & c' & Ha' & Hb' & Hc' & -> & ->).
  rewrite eq_step_view, !hd_seq by sc.
  pose proof (hd_contr a' Ha') as Hv. destruct (hd a') as [|m T r|m T r|v r|v r|x1 x2|x1 x2| |u]; simpl in *; try done.
  1: rewrite hd_seq by done; apply eq_view_refl, upto_refl.
  1-4: split_and?; try done; try (apply eqT_refl; intros; apply upto_refl);
    (destruct (sseq'_cases r) as [->|Hr];
      [simpl; left; by apply sseq'_sequiv
      |rewrite !Hr; cbn [sseq'];
       apply upto_in; exists r, b', c'; split_and!; try done; apply Hv]).
  all: destruct Hv; split; apply upto_in; eauto 10.
Qed.

Lemma cong_cont (τ : sty → sty → Prop) r r' b b' : scontr r → scontr r' → scontr b → scontr b' →
  τ (SSeq r b) (SSeq r' b') → upto τ (sseq' r b) (sseq' r' b').
Proof. intros. eapply upto_equiv; [apply sseq'_sequiv|done|apply sequiv_sym, sseq'_sequiv]; done. Qed.

Lemma seq_cong a a' b b' : scontr a → scontr a' → scontr b → scontr b' →
  sequiv a a' → sequiv b b' → sequiv (SSeq a b) (SSeq a' b').
Proof.
  intros. apply (sequiv_upto (λ x y, ∃ a a' b b', scontr a ∧ scontr a' ∧ scontr b ∧ scontr b' ∧
    sequiv a a' ∧ sequiv b b' ∧ x = SSeq a b ∧ y = SSeq a' b')); [|by eauto 20].
  clear dependent a a' b b'.
  intros x y (a & a' & b & b' & Ha & Ha' & Hb & Hb' & Haa & Hbb & -> & ->).
  rewrite eq_step_view, !hd_seq by done.
  pose proof (sequiv_hd _ _ Haa) as Hh. rewrite eq_step_view in Hh.
  pose proof (hd_contr a Ha) as Hv. pose proof (hd_contr a' Ha') as Hv'.
  destruct (hd a) as [|m T r|m T r|v r|v r|x1 x2|x1 x2| |u],
    (hd a') as [|m' T' r'|m' T' r'|v' r'|v' r'|x1' x2'|x1' x2'| |u']; simpl in *; try done.
  1: eapply eq_view_mono; [|apply (sequiv_hd _ _ Hbb)]; intros; by left.
  1-2: destruct Hh as (-> & HT & Hr), Hv, Hv'; split_and!; [done|eapply eqT_mono; [|exact HT]; intros; (by left)|];
    apply cong_cont; try done; exists r, r', b, b'; split_and!; done.
  1-2: destruct Hh as (-> & Hr); split; [done|];
    apply cong_cont; try done; exists r, r', b, b'; split_and!; done.
  all: destruct Hh, Hv, Hv'; split; apply upto_in; by eauto 20.
Qed.

Lemma seq_fold b : scontr (SMu b) → sequiv (SMu b) (unroll b).
Proof.
  intros Hc. apply sequiv_hd_eq. destruct (unrN_sfuel _ Hc) as [h E].
  cbn [sfuel unrN] in E. unfold hd, unfoldS at 1. cbn [sfuel unrN]. rewrite E.
  by rewrite (unrN_unfoldS' (unroll b) _ h (scontr_unroll _ Hc) E).
Qed.

Lemma seq_end X : scontr X → sequiv (SSeq SEnd X) SEnd.
Proof. intros. apply sequiv_hd_eq. by rewrite hd_seq. Qed.

Lemma seq_plus a b X : scontr a → scontr b → scontr X →
  sequiv (SSeq (SPlus a b) X) (SPlus (SSeq a X) (SSeq b X)).
Proof. intros. apply sequiv_hd_eq. rewrite hd_seq by sc. done. Qed.

Lemma seq_with a b X : scontr a → scontr b → scontr X →
  sequiv (SSeq (SWith a b) X) (SWith (SSeq a X) (SSeq b X)).
Proof. intros. apply sequiv_hd_eq. rewrite hd_seq by sc. done. Qed.

(** ** Instantiation commutes with unfolding up to ≈ *)

Section inst.
  Context (σ : nat → sty) (Hσ : ∀ a, scontr (σ a)).

  Lemma scontr_seq a b : scontr a → scontr b → scontr (SSeq a b).
  Proof. intros. cbn [scontr]. by apply Is_true_andb. Qed.

  Lemma sinst_unrN k : ∀ s h, scontr s → unrN k s = Some h → sequiv (sinst σ s) (sinst σ h).
  Proof.
    induction k as [|k IH]; intros s h Hc H; [done|].
    destruct s as [m T|m T| |b|a|a| |s1 s2|s1 s2|s1 s2]; cbn [unrN] in H;
      try (injection H as <-; apply sequiv_refl).
    - injection H as <-. cbn [sinst]. apply sequiv_sym, seq_skip_r. cbn [scontr] in *. by apply tcontr_sinst.
    - injection H as <-. cbn [sinst]. apply sequiv_sym, seq_skip_r. cbn [scontr] in *. by apply tcontr_sinst.
    - eapply sequiv_trans; [|apply (IH _ _ (scontr_unroll _ Hc) H)].
      rewrite sinst_unroll. cbn [sinst]. apply seq_fold.
      apply (scontr_sinst σ (SMu b)); done.
    - injection H as <-. cbn [sinst]. apply sequiv_sym, seq_skip_r. done.
    - injection H as <-. cbn [sinst]. apply sequiv_sym, seq_skip_r. by rewrite scontr_dual.
    - cbn [scontr] in Hc. apply Is_true_andb in Hc as [Hc1 Hc2].
      destruct (unrN k s1) as [h1|] eqn:E1; [|done].
      pose proof (unrN_scontr _ _ _ E1 Hc1) as Hh1. pose proof (unrN_hok _ _ _ E1) as Hok.
      pose proof (IH _ _ Hc1 E1) as IH1.
      assert (∀ t, scontr t → scontr (sinst σ t)) as Hs by (intros; by apply scontr_sinst).
      destruct h1 as [| | | | | | |o r|x y|x y]; unfold hok in Hok; simpl in Hok; try done.
      + injection H as <-. cbn [sinst].
        eapply sequiv_trans; [apply (seq_cong _ SEnd _ (sinst σ s2)); auto using sequiv_refl|].
        by apply seq_end, Hs.
      + pose proof (IH _ _ Hc2 H) as IH2. cbn [sinst].
        eapply sequiv_trans; [apply (seq_cong _ SSkip _ (sinst σ h)); auto|].
        { apply Hs. by eapply unrN_scontr. }
        apply seq_skip_l, Hs. by eapply unrN_scontr.
      + assert (h = hseq (SSeq o r) s2) as -> by congruence.
        cbn [scontr] in Hh1. apply Is_true_andb in Hh1 as [Ho Hr].
        eapply sequiv_trans; [cbn [sinst]; apply (seq_cong _ (sinst σ (SSeq o r)) _ (sinst σ s2)); auto using sequiv_refl|].
        { by apply Hs, scontr_seq. }
        destruct (sseq'_cases r) as [->|Er].
        * cbn [hseq sinst]. apply seq_cong; auto using sequiv_refl.
          { apply (Hs (SSeq o SSkip)). by apply scontr_seq. }
          by apply seq_skip_r, Hs.
        * assert (hseq (SSeq o r) s2 = SSeq o (SSeq r s2)) as -> by (destruct r; try done; specialize (Er SEnd); discriminate Er).
          cbn [sinst]. by apply seq_assoc; apply Hs.
      + injection H as <-. cbn [scontr] in Hh1. apply Is_true_andb in Hh1 as [Hx Hy].
        eapply sequiv_trans; [cbn [sinst]; apply (seq_cong _ (sinst σ (SPlus x y)) _ (sinst σ s2)); auto using sequiv_refl|].
        { apply Hs. cbn [scontr]. by apply Is_true_andb. }
        cbn [hseq sinst]. by apply seq_plus; apply Hs.
      + injection H as <-. cbn [scontr] in Hh1. apply Is_true_andb in Hh1 as [Hx Hy].
        eapply sequiv_trans; [cbn [sinst]; apply (seq_cong _ (sinst σ (SWith x y)) _ (sinst σ s2)); auto using sequiv_refl|].
        { apply Hs. cbn [scontr]. by apply Is_true_andb. }
        cbn [hseq sinst]. by apply seq_with; apply Hs.
  Qed.

  Lemma sinst_unfoldS s : scontr s → sequiv (sinst σ s) (sinst σ (unfoldS s)).
  Proof. intros Hc. destruct (unrN_sfuel s Hc) as [h E]. unfold unfoldS. rewrite E. by eapply sinst_unrN. Qed.
End inst.

(** ** Variable heads lower [uc] *)

Lemma uc_sinst_var s : ∀ τ, (∀ a, ugv a s → isvar (τ a)) → uc (sinst τ s) = uc s ∧ sk (sinst τ s) = sk s.
Proof.
  induction s as [m T|m T| |b IH|a|a| |s1 IH1 s2 IH2|s1 IH1 s2 IH2|s1 IH1 s2 IH2]; intros τ Hv; try done.
  - cbn [sinst uc sk]. apply IH. intros [|a] Ha; simpl; [done|]. unfold compose.
    specialize (Hv a Ha). by destruct (τ a).
  - cbn [sinst]. specialize (Hv a). simpl in Hv. destruct (τ a); try done; exfalso; apply Hv; by apply bool_decide_pack.
  - cbn [sinst]. specialize (Hv a). simpl in Hv. destruct (τ a); try done; exfalso; apply Hv; by apply bool_decide_pack.
  - cbn [sinst uc sk].
    destruct (IH1 τ) as [E1 S1]; [intros a Ha; apply Hv; cbn [ugv]; by destruct (ugv a s1)|].
    rewrite E1, S1. destruct (sk s1) eqn:Es; simpl; [|done].
    destruct (IH2 τ) as [E2 S2]; [|by rewrite E2, S2].
    intros a Ha. apply Hv. cbn [ugv]. rewrite Es. by destruct (ugv a s1).
Qed.

Lemma uc_unroll b : scontr (SMu b) → uc (unroll b) = uc b.
Proof.
  intros Hc. cbn [scontr] in Hc. apply Is_true_andb in Hc as [Hu _]. apply Is_true_negb in Hu.
  apply uc_sinst_var. intros [|a] Ha; done.
Qed.

Lemma unrN_var_uc k : ∀ s o s', scontr s → isvar o → unrN k s = Some (SSeq o s') →
  uc s' < uc s ∧ (sk s' → sk s).
Proof.
  induction k as [|k IH]; intros s o s' Hc Ho H; [done|].
  destruct s as [m T|m T| |b|a|a| |s1 s2|s1 s2|s1 s2]; cbn [unrN] in H; try done.
  - injection H as <- <-. done.
  - injection H as <- <-. done.
  - destruct (IH _ _ _ (scontr_unroll _ Hc) Ho H) as [H1 H2]. rewrite uc_unroll in H1 by done.
    split; [done|]. intros Hs. apply H2 in Hs. by apply sk_sinst in Hs.
  - injection H as <- <-. cbn. split; [lia|done].
  - injection H as <- <-. cbn. split; [lia|done].
  - cbn [scontr] in Hc. apply Is_true_andb in Hc as [Hc1 Hc2].
    destruct (unrN k s1) as [h1|] eqn:E1; [|done].
    destruct h1 as [| | | | | | |o1 r|x y|x y]; try (destruct o; done).
    + destruct (IH _ _ _ Hc2 Ho H) as [H1 H2]. pose proof (unrN_skip_sk _ _ E1) as Hs1.
      cbn [uc sk]. destruct (sk s1); [|done]. split; [lia|]. intros Hs. by apply H2 in Hs.
    + assert (o1 = o ∧ s' = sseq' r s2) as [-> ->].
      { destruct r; cbn [hseq sseq'] in H; injection H as <- <-; done. }
      destruct (IH _ _ _ Hc1 Ho E1) as [H1 H2]. cbn [uc sk].
      destruct (sseq'_cases r) as [->|Er].
      * cbn [sseq']. assert (sk s1) as Hs1 by (by apply H2). destruct (sk s1); [|done].
        cbn in H1. split; [lia|]. intros Hs. done.
      * rewrite Er. cbn [uc sk].
        destruct (sk r) eqn:Er'; [assert (sk s1) as Hs1 by (apply H2; done)|];
          destruct (sk s1); simpl; split; try lia; try done; by destruct (sk s2).
Qed.

(** ** ≈ is closed under contractive instances *)

Lemma hskip_dec v : v = HSkip ∨ v ≠ HSkip.
Proof. destruct v; [left|right..]; done. Qed.

Section sequiv_sinst.
  Context (σ : nat → sty) (Hσ : ∀ a, scontr (σ a)).

  Definition τI (x y : sty) : Prop :=
    ∃ u s r, scontr u ∧ scontr s ∧ scontr r ∧ sequiv s r ∧
      x = SSeq u (sinst σ s) ∧ y = SSeq u (sinst σ r).

  Lemma Hsc t : scontr t → scontr (sinst σ t).
  Proof. intros. by apply scontr_sinst. Qed.

  Lemma τI_base s r : scontr s → scontr r → sequiv s r → upto τI (sinst σ s) (sinst σ r).
  Proof.
    intros Hs Hr H. eapply upto_equiv; [apply sequiv_sym, seq_skip_l, Hsc, Hs| |apply seq_skip_l, Hsc, Hr].
    exists SSkip, s, r. by split_and!.
  Qed.

  Lemma eqT_sinst_upto T : ∀ U, tcontr T → tcontr U → eqT sequiv T U →
    eqT (upto τI) (sinst_ty σ T) (sinst_ty σ U).
  Proof.
    induction T as [|ub lb c T1 IH1 T2 IH2 a|T1 IH1 T2 IH2|T1 IH1 T2 IH2|n k C ub c T1 IH1|s x a mt|lb n C T1 IH1];
      intros [|ub' lb' c' U1 U2 a'|U1 U2|U1 U2|n' k' C' ub' c' U1|r y a' mt'|lb' n' C' U1] HT HU H;
      simpl in *; try done; contr_simpl.
    - destruct H as (-> & -> & -> & -> & ? & ?). split_and!; auto.
    - destruct H as [? ?]. split; auto.
    - destruct H as [? ?]. split; auto.
    - destruct H as (-> & -> & -> & -> & -> & ?). split_and!; try done.
      destruct k'; [by apply IH1|by subst].
    - destruct H as (-> & -> & -> & ?). split_and!; try done. by apply τI_base.
    - destruct H as (-> & -> & -> & ?). split_and!; auto.
  Qed.

  Lemma τI_nonskip u s r : scontr u → scontr s → scontr r → sequiv s r → hd u ≠ HSkip →
    eq_view (upto τI) (hseqv (hd u) (sinst σ s)) (hseqv (hd u) (sinst σ r)).
  Proof.
    intros Hu Hs Hr H Hne. pose proof (hd_contr u Hu) as Hv.
    destruct (hd u) as [|m T u'|m T u'|v u'|v u'|x y|x y| |w]; simpl in *; try done.
    1-2: destruct Hv as [HT Hu']; split_and!; [done|apply eqT_refl, upto_refl|].
    3-4: split; [done|].
    1-4: apply cong_cont; auto using Hsc; exists u', s, r; by split_and!.
    all: destruct Hv as [Hx Hy]; split; apply upto_in; [exists x, s, r|exists y, s, r]; by split_and!.
  Qed.

  Lemma τI_hd n : ∀ s r, uc s < n → scontr s → scontr r → sequiv s r →
    eq_view (upto τI) (hd (sinst σ s)) (hd (sinst σ r)).
  Proof.
    induction n as [|n IH]; intros s r Hn Hs Hr H; [lia|].
    eapply eq_view_upto_comp;
      [rewrite <-eq_step_view; apply sequiv_hd, sinst_unfoldS; auto
      |
      |rewrite <-eq_step_view; apply sequiv_hd, sequiv_sym, sinst_unfoldS; auto].
    rewrite !unfoldS_unview.
    pose proof (sequiv_hd _ _ H) as Hh. rewrite eq_step_view in Hh.
    pose proof (hd_contr s Hs) as Hvs. pose proof (hd_contr r Hr) as Hvr.
    assert (∀ o s', isvar o → hd s = view (SSeq o s') → uc s' < n) as Hdec.
    { intros o s' Ho E. destruct (unrN_sfuel s Hs) as [h Eh].
      assert (h = SSeq o s') as ->.
      { assert (unfoldS s = h) as Eu by (unfold unfoldS; by rewrite Eh).
        rewrite <-Eu, unfoldS_unview, E. apply unview_view. }
      destruct (unrN_var_uc _ _ _ _ Hs Ho Eh). lia. }
    destruct (hd s) as [|m T s'|m T s'|v s'|v s'|s1 s2|s1 s2| |w] eqn:Es,
      (hd r) as [|m' T' r'|m' T' r'|v' r'|v' r'|r1 r2|r1 r2| |w'] eqn:Er; simpl in *; try done.
    - destruct Hh as (-> & HT & Hc), Hvs, Hvr.
      split_and!; [done|by apply eqT_sinst_upto|by apply τI_base].
    - destruct Hh as (-> & HT & Hc), Hvs, Hvr.
      split_and!; [done|by apply eqT_sinst_upto|by apply τI_base].
    - destruct Hh as (-> & Hc). rewrite !hd_seq by sc.
      destruct (hskip_dec (hd (σ v'))) as [E|E].
      + rewrite E. simpl. apply IH; try done. eapply (Hdec (SVar v')); [done|reflexivity].
      + by apply τI_nonskip.
    - destruct Hh as (-> & Hc). rewrite !hd_seq by sc.
      destruct (hskip_dec (hd (dual (σ v')))) as [E|E].
      + rewrite E. simpl. apply IH; try done. eapply (Hdec (SVarD v')); [done|reflexivity].
      + apply τI_nonskip; try done. by rewrite scontr_dual.
    - destruct Hh, Hvs, Hvr. split; by apply τI_base.
    - destruct Hh, Hvs, Hvr. split; by apply τI_base.
  Qed.

  Lemma sequiv_sinst s r : scontr s → scontr r → sequiv s r → sequiv (sinst σ s) (sinst σ r).
  Proof.
    intros Hs Hr H.
    eapply sequiv_trans; [apply sequiv_sym, seq_skip_l, Hsc, Hs|].
    eapply sequiv_trans; [|apply seq_skip_l, Hsc, Hr].
    apply (sequiv_upto τI); [|exists SSkip, s, r; by split_and!].
    clear dependent s r. intros x y (u & s & r & Hu & Hs & Hr & H & -> & ->).
    rewrite eq_step_view, !hd_seq by auto using Hsc.
    destruct (hskip_dec (hd u)) as [E|E].
    - rewrite E. cbn [hseqv]. apply (τI_hd (S (uc s))); auto.
    - by apply τI_nonskip.
  Qed.

  Lemma teq_sinst T U : tcontr T → tcontr U → teq T U → teq (sinst_ty σ T) (sinst_ty σ U).
  Proof.
    revert U.
    induction T as [|ub lb c T1 IH1 T2 IH2 a|T1 IH1 T2 IH2|T1 IH1 T2 IH2|n k C ub c T1 IH1|s x a mt|lb n C T1 IH1];
      intros [|ub' lb' c' U1 U2 a'|U1 U2|U1 U2|n' k' C' ub' c' U1|r y a' mt'|lb' n' C' U1] HT HU H;
      unfold teq in *; simpl in *; try done; contr_simpl.
    - destruct H as (-> & -> & -> & -> & ? & ?). split_and!; auto.
    - destruct H as [? ?]. split; auto.
    - destruct H as [? ?]. split; auto.
    - destruct H as (-> & -> & -> & -> & -> & ?). split_and!; try done.
      destruct k'; [by apply IH1|by subst].
    - destruct H as (-> & -> & -> & ?). split_and!; try done. by apply sequiv_sinst.
    - destruct H as (-> & -> & -> & ?). split_and!; auto.
  Qed.
End sequiv_sinst.

(** ** Unfolding of an instance *)

Definition isact (o : sty) : Prop :=
  match o with SRcv _ _ | SSnd _ _ => True | _ => False end.

Section unfold_inst.
  Context (σ : nat → sty) (Hσ : ∀ a, scontr (σ a)).

  Lemma unrN_sinst_skip k : ∀ s, unrN k s = Some SSkip → unrN k (sinst σ s) = Some SSkip.
  Proof.
    induction k as [|k IH]; intros s H; [done|].
    destruct s as [m T|m T| |b|a|a| |s1 s2|s1 s2|s1 s2]; cbn [unrN] in H; try done.
    - cbn [sinst unrN]. rewrite <-sinst_unroll. by apply IH.
    - cbn [sinst unrN]. destruct (unrN k s1) as [h1|] eqn:E1; [|done].
      destruct h1 as [| | | | | | |o r|x y|x y]; cbn [hseq] in H; try done; try (destruct r; done).
      rewrite (IH _ E1). by apply IH.
  Qed.

  Lemma unrN_sinst_act k : ∀ s o r, unrN k s = Some (SSeq o r) → isact o →
    ∃ r', unrN k (sinst σ s) = Some (SSeq (sinst σ o) r').
  Proof.
    induction k as [|k IH]; intros s o r H Ho; [done|].
    destruct s as [m T|m T| |b|a|a| |s1 s2|s1 s2|s1 s2]; cbn [unrN] in H; try done.
    - injection H as <- <-. by eexists.
    - injection H as <- <-. by eexists.
    - cbn [sinst unrN]. rewrite <-sinst_unroll. by eapply IH.
    - injection H as <- <-. done.
    - injection H as <- <-. done.
    - cbn [sinst unrN]. destruct (unrN k s1) as [h1|] eqn:E1; [|done].
      destruct h1 as [| | | | | | |o1 r1|x y|x y]; cbn [hseq] in H; try done.
      + rewrite (unrN_sinst_skip _ _ E1). by eapply IH.
      + assert (o1 = o) as ->. { destruct r1; injection H as -> _; done. }
        destruct (IH _ _ _ E1 Ho) as [r' E']. rewrite E'.
        destruct r'; eexists; done.
  Qed.

  Lemma sinst_hd_equiv s : scontr s →
    eq_view sequiv (hd (sinst σ s)) (hd (sinst σ (unfoldS s))).
  Proof. intros Hc. rewrite <-eq_step_view. by apply sequiv_hd, sinst_unfoldS. Qed.

  Lemma unfoldS_sinst_skip s : scontr s → unfoldS s = SSkip → unfoldS (sinst σ s) = SSkip.
  Proof.
    intros Hc E. pose proof (sinst_hd_equiv s Hc) as H. rewrite E in H.
    rewrite unfoldS_unview. destruct (hd (sinst σ s)); done.
  Qed.

  Lemma idle_sinst s : scontr s → idle s → idle (sinst σ s).
  Proof. apply unfoldS_sinst_skip. Qed.

  Lemma unfoldS_sinst_end s : scontr s → unfoldS s = SEnd → unfoldS (sinst σ s) = SEnd.
  Proof.
    intros Hc E. pose proof (sinst_hd_equiv s Hc) as H. rewrite E in H.
    rewrite unfoldS_unview. destruct (hd (sinst σ s)); done.
  Qed.

  Lemma unfoldS_sinst_plus s S1 S2 : scontr s → unfoldS s = SPlus S1 S2 →
    ∃ S1' S2', unfoldS (sinst σ s) = SPlus S1' S2' ∧ sequiv S1' (sinst σ S1) ∧ sequiv S2' (sinst σ S2).
  Proof.
    intros Hc E. pose proof (sinst_hd_equiv s Hc) as H. rewrite E in H.
    rewrite unfoldS_unview. destruct (hd (sinst σ s)); try done. destruct H. eauto.
  Qed.

  Lemma unfoldS_sinst_with s S1 S2 : scontr s → unfoldS s = SWith S1 S2 →
    ∃ S1' S2', unfoldS (sinst σ s) = SWith S1' S2' ∧ sequiv S1' (sinst σ S1) ∧ sequiv S2' (sinst σ S2).
  Proof.
    intros Hc E. pose proof (sinst_hd_equiv s Hc) as H. rewrite E in H.
    rewrite unfoldS_unview. destruct (hd (sinst σ s)); try done. destruct H. eauto.
  Qed.

  Lemma unfoldS_sinst_act s o S : scontr s → isact o → unfoldS s = SSeq o S →
    ∃ S', unfoldS (sinst σ s) = SSeq (sinst σ o) S' ∧ sequiv S' (sinst σ S).
  Proof.
    intros Hc Ho E. destruct (unrN_sfuel s Hc) as [h Eh].
    assert (h = SSeq o S) as -> by (unfold unfoldS in E; rewrite Eh in E; done).
    destruct (unrN_sinst_act _ _ _ _ Eh Ho) as [r' E'].
    assert (unfoldS (sinst σ s) = SSeq (sinst σ o) r') as Eu.
    { eapply unrN_unfoldS'; [by apply scontr_sinst|exact E']. }
    exists r'. split; [done|].
    pose proof (sinst_hd_equiv s Hc) as H. rewrite E in H. unfold hd at 1 in H. rewrite Eu in H.
    destruct o; try done; simpl in H; by destruct H as (_ & _ & H).
  Qed.
End unfold_inst.
