(** * Types of constants (map block "Types of constants")

    A constant k of GV is the value λy. k y, the eta-expansion of the
    saturated primitive [Op k]. Each lemma types the eta-expansion at
    the schema of k by E-Abs over the rule of k, in two forms: [k_*_df]
    for deadlock-freedom typing and [k_*] for the merged judgment with
    the annotations of the rule of k. The closure captures no end, so
    its lower point is absent and the context Δ is unlimited. An action
    on x and a force run below the future of their caller, so the arrow
    has upper point x, or the instantiated upper point of the box. *)

From GV Require Export static.Conservativity.

(** ** Helpers *)

Lemma lenv_unl_heads Δ : lenv_unl Δ → lenv_heads Δ = ∅ ∧ lenv_bot Δ = false.
Proof.
  induction Δ as [|o Δ IH]; intros HΔ; [done|].
  assert (lenv_unl Δ) as HΔ' by (intros o' Ho'; apply HΔ; by right).
  destruct (HΔ o (list_elem_of_here _ _)) as [->|(U & -> & HU)]; simpl; [by apply IH|].
  destruct U; try done. simpl. destruct (IH HΔ') as [-> ->]. split; [set_solver|done].
Qed.

Lemma lenv_only_unl Δ σ : lenv_unl Δ → lenv_only (Some σ :: Δ) 0 σ.
Proof.
  intros HΔ. split; [done|]. intros [|y] σ' Hy Hσ; [done|]. simpl in Hσ.
  destruct (HΔ (Some σ') (list_elem_of_lookup_2 _ _ _ Hσ)) as [?|(U & [= ->] & HU)]; [done|exact HU].
Qed.

(** The body of an eta-expansion with upper point u runs below
    everything above u. *)
Lemma ub_fvar W Γ u : ub_below_s W Γ u (∅, Some (FRest (rest_of u))).
Proof.
  destruct u as [x|]; [|done]. simpl. split; [set_solver|split; [|done]].
  intros r [= <-]. by left.
Qed.

Lemma lage_unl a Δ : lenv_unl Δ → lage a Δ Δ.
Proof.
  induction Δ as [|o Δ IH]; intros HΔ; [constructor|].
  assert (lenv_unl Δ) as HΔ' by (intros o' Ho'; apply HΔ; by right).
  destruct (HΔ o (list_elem_of_here _ _)) as [->|(U & -> & HU)]; constructor; auto.
  apply age_free, unlimited_tfree, HU.
Qed.

(** E-Abs for a closure that captures nothing. *)
Lemma eta_df W Γ Δ F ub e T U c a :
  lenv_unl Δ → tcontr T →
  dftyped W ∅ Γ (Some T :: Δ) (abs_fut ub) e U →
  dftyped W ∅ Γ Δ F (Lam e) (TLolli ub LNone c T U a).
Proof.
  intros HΔ HT H.
  apply (d_abs _ _ _ _ _ _ _ _ _ _ _ _); [|exact HT|exact H].
  destruct (lenv_unl_heads Δ HΔ) as [-> ->]. simpl. split; [|done].
  unfold tenv_heads. rewrite map_to_list_empty. set_solver.
Qed.

Lemma eta W N Γ Δ F ub e T U c a :
  lenv_unl Δ → tcontr T →
  typed W N ∅ Γ (Some T :: Δ) (abs_fut ub) e U c →
  typed W N ∅ Γ Δ F (Lam e) (TLolli ub LNone c T U a) (Some 0).
Proof.
  intros HΔ HT H.
  apply (e_abs _ _ ∅ ∅ _ _ Δ _ _ _ _ _ _ _ _); [| |by apply lage_unl|exact HT|exact H].
  - destruct (lenv_unl_heads Δ HΔ) as [-> ->]. simpl. split; [|done].
    unfold tenv_heads. rewrite map_to_list_empty. set_solver.
  - intros o. by rewrite !lookup_empty.
Qed.

Local Ltac var_df HΔ := eapply d_var, lenv_only_unl, HΔ.
Local Ltac var HΔ := eapply e_var, lenv_only_unl, HΔ.

(** ** Deadlock-freedom typing *)

(** send : T[x·i] ⊗ S₀@x ⊸^x S@x⁺ under the conditions of E-Send. *)
Lemma k_send_df W Γ Δ F x S0 m T S aS mS mS' c a :
  lenv_unl Δ → unfoldS S0 = SSeq (SSnd m T) S → pscoped m T → hbot T = false →
  (∀ y, y ∈ heads (payload_at m T x) → slt W Γ x y) → scontr S0 →
  dftyped W ∅ Γ Δ F (Lam (ESend (Var 0)))
    (TLolli (UPt x) LNone c (TProd (payload_at m T x) (TSess S0 x aS mS)) (TSess S x⁺ aS mS') a).
Proof.
  intros HΔ Hu Hsc Hb Hh HA. apply eta_df; [done|cbn [tcontr]; apply Is_true_andb; split; [|exact HA]; unfold payload_at; rewrite tcontr_ty_inst; apply (unfoldS_seq_contr _ _ _ HA Hu)|].
  eapply d_send; [done|done|done| |apply (ub_fvar _ _ (Some x))|var_df HΔ].
  intros y Hy. by apply Hh.
Qed.

(** recv : S₀@x ⊸^x T[x·i] ⊗ S@x⁺. *)
Lemma k_recv_df W Γ Δ F x S0 m T S aS aS' mS mS' c a :
  lenv_unl Δ → unfoldS S0 = SSeq (SRcv m T) S → pscoped m T → scontr S0 →
  dftyped W ∅ Γ Δ F (Lam (ERecv (Var 0)))
    (TLolli (UPt x) LNone c (TSess S0 x aS mS) (TProd (payload_at m T x) (TSess S x⁺ aS' mS')) a).
Proof.
  intros HΔ Hu Hsc HA. apply eta_df; [done|exact HA|].
  eapply d_recv; [done|done|apply (ub_fvar _ _ (Some x))|var_df HΔ].
Qed.

(** close : S₀@x ⊸^x ∗. *)
Lemma k_close_df W Γ Δ F x S0 aS mS c a :
  lenv_unl Δ → unfoldS S0 = SEnd → scontr S0 →
  dftyped W ∅ Γ Δ F (Lam (EClose (Var 0))) (TLolli (UPt x) LNone c (TSess S0 x aS mS) TUnit a).
Proof.
  intros HΔ Hu HA. apply eta_df; [done|exact HA|].
  eapply d_close; [done|apply (ub_fvar _ _ (Some x))|var_df HΔ].
Qed.

(** select_i : S₀@x ⊸^x S_i@(x·κ_i)‾. *)
Lemma k_select_df W (i : bool) Γ Δ F x S0 S1 S2 aS aS' mS mS' c a :
  lenv_unl Δ → unfoldS S0 = SPlus S1 S2 → scontr S0 →
  dftyped W ∅ Γ Δ F (Lam (ESel i (Var 0)))
    (TLolli (UPt x) LNone c (TSess S0 x aS mS) (TSess (if i then S2 else S1) (sel_pt x i) aS' mS') a).
Proof.
  intros HΔ Hu HA. apply eta_df; [done|exact HA|].
  eapply d_select; [done|apply (ub_fvar _ _ (Some x))|var_df HΔ].
Qed.

(** branch : S₀@x ⊸^x S₁@x·κ₁ ⊕ S₂@x·κ₂. *)
Lemma k_branch_df W Γ Δ F x S0 S1 S2 aS a1 a2 mS m1 m2 c a :
  lenv_unl Δ → unfoldS S0 = SWith S1 S2 → scontr S0 →
  dftyped W ∅ Γ Δ F (Lam (EBra (Var 0)))
    (TLolli (UPt x) LNone c (TSess S0 x aS mS) (TSum (TSess S1 (bra_pt x false) a1 m1) (TSess S2 (bra_pt x true) a2 m2)) a).
Proof.
  intros HΔ Hu HA. apply eta_df; [done|exact HA|].
  eapply d_branch; [done|apply (ub_fvar _ _ (Some x))|var_df HΔ].
Qed.

(** link : S@x ⊗ S̄@x̄ ⊸ ∗. *)
Lemma k_link_df W Γ Δ F S x a1 a2 m1 m2 c a :
  lenv_unl Δ → scontr S →
  dftyped W ∅ Γ Δ F (Lam (ELink (Var 0)))
    (TLolli UNone LNone c (TProd (TSess S x a1 m1) (TSess (dual S) x‾ a2 m2)) TUnit a).
Proof.
  intros HΔ HA. apply eta_df; [done|cbn [tcontr]; apply Is_true_andb; split; [exact HA|change (scontr (dual S)); by rewrite scontr_dual]|].
  eapply d_link; var_df HΔ.
Qed.

(** spawn : (∗ ⊸^u_l ∗) ⊸ ∗. *)
Lemma k_spawn_df W Γ Δ F ub lb c' a' c a :
  lenv_unl Δ →
  dftyped W ∅ Γ Δ F (Lam (ESpawn (Var 0)))
    (TLolli UNone LNone c (TLolli ub lb c' TUnit TUnit a') TUnit a).
Proof.
  intros HΔ. apply eta_df; [done|done|].
  eapply d_spawn; var_df HΔ.
Qed.

(** force : □(∀ιs αs. C. ∗ ⊸^u U) ⊸^{u[xs]} U[ss][xs] under Γ ⊢ C[xs]. *)
Lemma k_force_df W Γ Δ F m k C ub c0 U xs ss c a :
  lenv_unl Δ → length xs = m → hold_at W Γ C xs → length ss = k → sinsts None ss → tcontr U →
  dftyped W ∅ Γ Δ F (Lam (EForce (Var 0)))
    (TLolli (ubound_of (pt_inst (plist xs) <$> ub)) LNone c (TBox m k C ub c0 U) (sinst_ty (slist ss) (ty_inst xs U)) a).
Proof.
  intros HΔ Hxs HC Hk Hss HA. apply eta_df; [done|exact HA|].
  rewrite abs_fut_of.
  eapply d_force; [done| |done|done|apply ub_fvar|var_df HΔ].
  intros y z Hg. by apply HC.
Qed.

(** ** The merged judgment

    Each constant at the annotations of the rule of its primitive: cost
    1 for an action, the cost of one force for force, and the ends an
    action returns at credit equal to their tickets. The
    argument of send is a payload Tp that ages by one hop below the
    payload of the session type. *)

Lemma k_send W N Γ Δ F x S0 m T S aS mS Tp Tp' a :
  lenv_unl Δ → unfoldS S0 = SSeq (SSnd m T) S → pscoped m T → hbot T = false →
  (∀ y, y ∈ heads (payload_at m T x) → slt W Γ x y) →
  tage (Some 1) Tp Tp' → tsub Tp' (payload_at m T x) → tcontr Tp → scontr S0 →
  typed W N ∅ Γ Δ F (Lam (ESend (Var 0)))
    (TLolli (UPt x) LNone (Some 1) (TProd Tp (TSess S0 x aS mS)) (TSess S x⁺ mS mS) a) (Some 0).
Proof.
  intros HΔ Hu Hsc Hb Hh Ha Hs HT HA. apply eta; [done|cbn [tcontr]; apply Is_true_andb; split; [|exact HA]; exact HT|].
  change (Some 1) with (fadd (Some 0) (Some 1)). eapply e_send; [done|done|done| |apply (ub_fvar _ _ (Some x))|var HΔ|exact Ha|exact Hs].
  intros y Hy. by apply Hh.
Qed.

Lemma k_recv W N Γ Δ F x S0 m T S aS mS a :
  lenv_unl Δ → unfoldS S0 = SSeq (SRcv m T) S → pscoped m T → scontr S0 →
  typed W N ∅ Γ Δ F (Lam (ERecv (Var 0)))
    (TLolli (UPt x) LNone (Some 1) (TSess S0 x aS mS) (TProd (payload_at m T x) (TSess S x⁺ mS mS)) a)
    (Some 0).
Proof.
  intros HΔ Hu Hsc HA. apply eta; [done|exact HA|].
  change (Some 1) with (fadd (Some 0) (Some 1)). eapply e_recv; [done|done|apply (ub_fvar _ _ (Some x))|var HΔ].
Qed.

Lemma k_close W N Γ Δ F x S0 aS mS a :
  lenv_unl Δ → unfoldS S0 = SEnd → scontr S0 →
  typed W N ∅ Γ Δ F (Lam (EClose (Var 0)))
    (TLolli (UPt x) LNone (Some 1) (TSess S0 x aS mS) TUnit a) (Some 0).
Proof.
  intros HΔ Hu HA. apply eta; [done|exact HA|].
  change (Some 1) with (fadd (Some 0) (Some 1)). eapply e_close; [done|apply (ub_fvar _ _ (Some x))|var HΔ].
Qed.

Lemma k_select W N (i : bool) Γ Δ F x S0 S1 S2 aS mS a :
  lenv_unl Δ → unfoldS S0 = SPlus S1 S2 → scontr S0 →
  typed W N ∅ Γ Δ F (Lam (ESel i (Var 0)))
    (TLolli (UPt x) LNone (Some 1) (TSess S0 x aS mS) (TSess (if i then S2 else S1) (sel_pt x i) mS mS) a)
    (Some 0).
Proof.
  intros HΔ Hu HA. apply eta; [done|exact HA|].
  change (Some 1) with (fadd (Some 0) (Some 1)). eapply e_select; [done|apply (ub_fvar _ _ (Some x))|var HΔ].
Qed.

Lemma k_branch W N Γ Δ F x S0 S1 S2 aS mS a :
  lenv_unl Δ → unfoldS S0 = SWith S1 S2 → scontr S0 →
  typed W N ∅ Γ Δ F (Lam (EBra (Var 0)))
    (TLolli (UPt x) LNone (Some 1) (TSess S0 x aS mS) (TSum (TSess S1 (bra_pt x false) mS mS) (TSess S2 (bra_pt x true) mS mS)) a)
    (Some 0).
Proof.
  intros HΔ Hu HA. apply eta; [done|exact HA|].
  change (Some 1) with (fadd (Some 0) (Some 1)). eapply e_branch; [done|apply (ub_fvar _ _ (Some x))|var HΔ].
Qed.

Lemma k_link W N Γ Δ F S x a1 m1 a2 m2 a :
  lenv_unl Δ → lgt N a1 m2 → lgt N a2 m1 → scontr S →
  typed W N ∅ Γ Δ F (Lam (ELink (Var 0)))
    (TLolli UNone LNone (Some 0) (TProd (TSess S x a1 m1) (TSess (dual S) x‾ a2 m2)) TUnit a)
    (Some 0).
Proof.
  intros HΔ H1 H2 HA. apply eta; [done|cbn [tcontr]; apply Is_true_andb; split; [exact HA|change (scontr (dual S)); by rewrite scontr_dual]|].
  eapply e_link; [var HΔ|done|done].
Qed.

Lemma k_spawn W N Γ Δ F ub lb c' a' a :
  lenv_unl Δ → fle (Some 1) a' →
  typed W N ∅ Γ Δ F (Lam (ESpawn (Var 0)))
    (TLolli UNone LNone (Some 0) (TLolli ub lb c' TUnit TUnit a') TUnit a)
    (Some 0).
Proof.
  intros HΔ Ha. apply eta; [done|done|].
  eapply e_spawn; [var HΔ|done].
Qed.

Lemma k_force W N Γ Δ F m k C ub c0 U xs ss a :
  lenv_unl Δ → length xs = m → hold_at W Γ C xs → length ss = k → sinsts N ss → tcontr U →
  typed W N ∅ Γ Δ F (Lam (EForce (Var 0)))
    (TLolli (ubound_of (pt_inst (plist xs) <$> ub)) LNone (fadd (Some 0) c0) (TBox m k C ub c0 U) (sinst_ty (slist ss) (ty_inst xs U)) a)
    (Some 0).
Proof.
  intros HΔ Hxs HC Hk Hss HA. apply eta; [done|exact HA|].
  rewrite abs_fut_of.
  eapply e_force; [done| |done|done|apply ub_fvar|var HΔ].
  intros y z Hg. by apply HC.
Qed.
