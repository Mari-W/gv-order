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
Lemma eta_df W Γ Δ F ub e T U c t a :
  lenv_unl Δ →
  dftyped W ∅ Γ (Some T :: Δ) (abs_fut ub) e U →
  dftyped W ∅ Γ Δ F (Lam e) (TLolli ub LNone c t T U a).
Proof.
  intros HΔ H.
  apply (d_abs _ _ _ _ _ _ _ _ _ _ _ _ _); [|exact H].
  destruct (lenv_unl_heads Δ HΔ) as [-> ->]. simpl. split; [|done].
  unfold tenv_heads. rewrite map_to_list_empty. set_solver.
Qed.

Lemma eta W N Γ Δ F ub e T U c t a :
  lenv_unl Δ →
  typed W N ∅ Γ (Some T :: Δ) (abs_fut ub) e U c t →
  typed W N ∅ Γ Δ F (Lam e) (TLolli ub LNone c t T U a) (Some 0) tid.
Proof.
  intros HΔ H.
  apply (e_abs _ _ ∅ ∅ _ _ Δ _ _ _ _ _ _ _ _ _); [| |by apply lage_unl|exact H].
  - destruct (lenv_unl_heads Δ HΔ) as [-> ->]. simpl. split; [|done].
    unfold tenv_heads. rewrite map_to_list_empty. set_solver.
  - intros o. by rewrite !lookup_empty.
Qed.

Local Ltac var_df HΔ := eapply d_var, lenv_only_unl, HΔ.
Local Ltac var HΔ := eapply e_var, lenv_only_unl, HΔ.

(** ** Deadlock-freedom typing *)

(** send : T[x·i] ⊗ S₀@x ⊸^x S@x⁺ under the conditions of E-Send. *)
Lemma k_send_df W Γ Δ F x S0 m T S aS c t a :
  lenv_unl Δ → unfoldS S0 = SSeq (SSnd m T) S → pscoped m T → hbot T = false →
  (∀ y, y ∈ heads (payload_at m T x) → slt W Γ x y) →
  dftyped W ∅ Γ Δ F (Lam (ESend (Var 0)))
    (TLolli (UPt x) LNone c t (TProd (payload_at m T x) (TSess S0 x aS)) (TSess S x⁺ aS) a).
Proof.
  intros HΔ Hu Hsc Hb Hh. apply eta_df; [done|].
  eapply d_send; [done|done|done| |apply (ub_fvar _ _ (Some x))|var_df HΔ].
  intros y Hy. by apply Hh.
Qed.

(** recv : S₀@x ⊸^x T[x·i] ⊗ S@x⁺. *)
Lemma k_recv_df W Γ Δ F x S0 m T S aS aS' c t a :
  lenv_unl Δ → unfoldS S0 = SSeq (SRcv m T) S → pscoped m T →
  dftyped W ∅ Γ Δ F (Lam (ERecv (Var 0)))
    (TLolli (UPt x) LNone c t (TSess S0 x aS) (TProd (payload_at m T x) (TSess S x⁺ aS')) a).
Proof.
  intros HΔ Hu Hsc. apply eta_df; [done|].
  eapply d_recv; [done|done|apply (ub_fvar _ _ (Some x))|var_df HΔ].
Qed.

(** close : S₀@x ⊸^x ∗. *)
Lemma k_close_df W Γ Δ F x S0 aS c t a :
  lenv_unl Δ → unfoldS S0 = SEnd →
  dftyped W ∅ Γ Δ F (Lam (EClose (Var 0))) (TLolli (UPt x) LNone c t (TSess S0 x aS) TUnit a).
Proof.
  intros HΔ Hu. apply eta_df; [done|].
  eapply d_close; [done|apply (ub_fvar _ _ (Some x))|var_df HΔ].
Qed.

(** select_i : S₀@x ⊸^x S_i@(x·κ_i)‾. *)
Lemma k_select_df W (i : bool) Γ Δ F x S0 S1 S2 aS aS' c t a :
  lenv_unl Δ → unfoldS S0 = SPlus S1 S2 →
  dftyped W ∅ Γ Δ F (Lam (ESel i (Var 0)))
    (TLolli (UPt x) LNone c t (TSess S0 x aS) (TSess (if i then S2 else S1) (sel_pt x i) aS') a).
Proof.
  intros HΔ Hu. apply eta_df; [done|].
  eapply d_select; [done|apply (ub_fvar _ _ (Some x))|var_df HΔ].
Qed.

(** branch : S₀@x ⊸^x S₁@x·κ₁ ⊕ S₂@x·κ₂. *)
Lemma k_branch_df W Γ Δ F x S0 S1 S2 aS a1 a2 c t a :
  lenv_unl Δ → unfoldS S0 = SWith S1 S2 →
  dftyped W ∅ Γ Δ F (Lam (EBra (Var 0)))
    (TLolli (UPt x) LNone c t (TSess S0 x aS)
       (TSum (TSess S1 (bra_pt x false) a1) (TSess S2 (bra_pt x true) a2)) a).
Proof.
  intros HΔ Hu. apply eta_df; [done|].
  eapply d_branch; [done|apply (ub_fvar _ _ (Some x))|var_df HΔ].
Qed.

(** link : S@x ⊗ S̄@x̄ ⊸ ∗. *)
Lemma k_link_df W Γ Δ F S x a1 a2 c t a :
  lenv_unl Δ →
  dftyped W ∅ Γ Δ F (Lam (ELink (Var 0)))
    (TLolli UNone LNone c t (TProd (TSess S x a1) (TSess (dual S) x‾ a2)) TUnit a).
Proof.
  intros HΔ. apply eta_df; [done|].
  eapply d_link; var_df HΔ.
Qed.

(** spawn : (∗ ⊸^u_l ∗) ⊸ ∗. *)
Lemma k_spawn_df W Γ Δ F ub lb c' t' a' c t a :
  lenv_unl Δ →
  dftyped W ∅ Γ Δ F (Lam (ESpawn (Var 0)))
    (TLolli UNone LNone c t (TLolli ub lb c' t' TUnit TUnit a') TUnit a).
Proof.
  intros HΔ. apply eta_df; [done|].
  eapply d_spawn; var_df HΔ.
Qed.

(** force : □(∀ιs αs. C. ∗ ⊸^u U) ⊸^{u[xs]} U[ss][xs] under Γ ⊢ C[xs]. *)
Lemma k_force_df W Γ Δ F m k C ub c0 t0 U xs ss c t a :
  lenv_unl Δ → length xs = m → hold_at W Γ C xs → length ss = k → sinsts None ss →
  dftyped W ∅ Γ Δ F (Lam (EForce (Var 0)))
    (TLolli (ubound_of (pt_inst (plist xs) <$> ub)) LNone c t (TBox m k C ub c0 t0 U)
       (sinst_ty (slist ss) (ty_inst xs U)) a).
Proof.
  intros HΔ Hxs HC Hk Hss. apply eta_df; [done|].
  rewrite abs_fut_of.
  eapply d_force; [done| |done|done|apply ub_fvar|var_df HΔ].
  intros y z Hg. by apply HC.
Qed.

(** ** The merged judgment

    Each constant at the annotations of the rule of its primitive: cost
    1 for an action, the cost of one force for force, the identity
    ticket need, the refill N on the ends an action returns. The
    argument of send is a payload Tp that ages by one hop below the
    payload of the session type. *)

Lemma k_send W N Γ Δ F x S0 m T S aS Tp Tp' a :
  lenv_unl Δ → unfoldS S0 = SSeq (SSnd m T) S → pscoped m T → hbot T = false →
  (∀ y, y ∈ heads (payload_at m T x) → slt W Γ x y) →
  tage (Some 1) Tp Tp' → tsub Tp' (payload_at m T x) →
  typed W N ∅ Γ Δ F (Lam (ESend (Var 0)))
    (TLolli (UPt x) LNone (Some 1) tid (TProd Tp (TSess S0 x aS)) (TSess S x⁺ N) a) (Some 0) tid.
Proof.
  intros HΔ Hu Hsc Hb Hh Ha Hs. apply eta; [done|].
  change (Some 1) with (fadd (Some 0) (Some 1)). eapply e_send; [done|done|done| |apply (ub_fvar _ _ (Some x))|var HΔ|exact Ha|exact Hs].
  intros y Hy. by apply Hh.
Qed.

Lemma k_recv W N Γ Δ F x S0 m T S aS a :
  lenv_unl Δ → unfoldS S0 = SSeq (SRcv m T) S → pscoped m T →
  typed W N ∅ Γ Δ F (Lam (ERecv (Var 0)))
    (TLolli (UPt x) LNone (Some 1) tid (TSess S0 x aS) (TProd (payload_at m T x) (TSess S x⁺ N)) a)
    (Some 0) tid.
Proof.
  intros HΔ Hu Hsc. apply eta; [done|].
  change (Some 1) with (fadd (Some 0) (Some 1)). eapply e_recv; [done|done|apply (ub_fvar _ _ (Some x))|var HΔ].
Qed.

Lemma k_close W N Γ Δ F x S0 aS a :
  lenv_unl Δ → unfoldS S0 = SEnd →
  typed W N ∅ Γ Δ F (Lam (EClose (Var 0)))
    (TLolli (UPt x) LNone (Some 1) tid (TSess S0 x aS) TUnit a) (Some 0) tid.
Proof.
  intros HΔ Hu. apply eta; [done|].
  change (Some 1) with (fadd (Some 0) (Some 1)). eapply e_close; [done|apply (ub_fvar _ _ (Some x))|var HΔ].
Qed.

Lemma k_select W N (i : bool) Γ Δ F x S0 S1 S2 aS a :
  lenv_unl Δ → unfoldS S0 = SPlus S1 S2 →
  typed W N ∅ Γ Δ F (Lam (ESel i (Var 0)))
    (TLolli (UPt x) LNone (Some 1) tid (TSess S0 x aS) (TSess (if i then S2 else S1) (sel_pt x i) N) a)
    (Some 0) tid.
Proof.
  intros HΔ Hu. apply eta; [done|].
  change (Some 1) with (fadd (Some 0) (Some 1)). eapply e_select; [done|apply (ub_fvar _ _ (Some x))|var HΔ].
Qed.

Lemma k_branch W N Γ Δ F x S0 S1 S2 aS a :
  lenv_unl Δ → unfoldS S0 = SWith S1 S2 →
  typed W N ∅ Γ Δ F (Lam (EBra (Var 0)))
    (TLolli (UPt x) LNone (Some 1) tid (TSess S0 x aS)
       (TSum (TSess S1 (bra_pt x false) N) (TSess S2 (bra_pt x true) N)) a)
    (Some 0) tid.
Proof.
  intros HΔ Hu. apply eta; [done|].
  change (Some 1) with (fadd (Some 0) (Some 1)). eapply e_branch; [done|apply (ub_fvar _ _ (Some x))|var HΔ].
Qed.

Lemma k_link W N Γ Δ F S x a1 a2 a :
  lenv_unl Δ →
  typed W N ∅ Γ Δ F (Lam (ELink (Var 0)))
    (TLolli UNone LNone (Some 0) (tseq tid (tlink tid)) (TProd (TSess S x a1) (TSess (dual S) x‾ a2))
       TUnit a)
    (Some 0) tid.
Proof.
  intros HΔ. apply eta; [done|].
  eapply e_link; [var HΔ|right; left; discriminate].
Qed.

Lemma k_spawn W N Γ Δ F ub lb c' t' a' a :
  lenv_unl Δ → fle (Some 1) a' →
  typed W N ∅ Γ Δ F (Lam (ESpawn (Var 0)))
    (TLolli UNone LNone (Some 0) (tseq tid (tspawn (tapp t' 0) tid))
       (TLolli ub lb c' t' TUnit TUnit a') TUnit a)
    (Some 0) tid.
Proof.
  intros HΔ Ha. apply eta; [done|].
  eapply e_spawn; [var HΔ|done|right; left; discriminate].
Qed.

Lemma k_force W N Γ Δ F m k C ub c0 t0 U xs ss a :
  lenv_unl Δ → length xs = m → hold_at W Γ C xs → length ss = k → sinsts N ss →
  typed W N ∅ Γ Δ F (Lam (EForce (Var 0)))
    (TLolli (ubound_of (pt_inst (plist xs) <$> ub)) LNone (fadd (Some 0) c0) (tseq tid t0) (TBox m k C ub c0 t0 U)
       (sinst_ty (slist ss) (ty_inst xs U)) a)
    (Some 0) tid.
Proof.
  intros HΔ Hxs HC Hk Hss. apply eta; [done|].
  rewrite abs_fut_of.
  eapply e_force; [done| |done|done|apply ub_fvar|var HΔ|right; left; discriminate].
  intros y z Hg. by apply HC.
Qed.
