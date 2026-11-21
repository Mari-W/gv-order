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
