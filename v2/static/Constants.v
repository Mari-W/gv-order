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
  destruct (HΔ o (list_elem_of_here _ _)) as [->|(U & a & -> & HU)]; simpl; [by apply IH|].
  destruct U; try done. simpl. destruct (IH HΔ') as [-> ->]. split; [set_solver|done].
Qed.

Lemma lenv_only_unl Δ σ : lenv_unl Δ → lenv_only (Some σ :: Δ) 0 σ.
Proof.
  intros HΔ. split; [done|]. intros [|y] σ' Hy Hσ; [done|]. simpl in Hσ.
  destruct (HΔ (Some σ') (list_elem_of_lookup_2 _ _ _ Hσ)) as [?|(U & a & [= ->] & HU)]; [done|exact HU].
Qed.

Lemma fl_fvar W Γ φ u a b : φ ∉ dom (hc_fv Γ) → fl W Γ a b → fl W (hc_fvar φ u Γ) a b.
Proof.
  intros Hφ. induction 1 as [x y H|x y H|φ' u' H|a y b _ IH1 _ IH2].
  - by apply fl_w.
  - by apply fl_h.
  - apply fl_v. simpl. rewrite lookup_insert_ne; [done|]. intros ->. apply Hφ. by eapply elem_of_dom_2.
  - by eapply fl_trans.
Qed.

Lemma slt_fvar W Γ φ u x y : φ ∉ dom (hc_fv Γ) → slt W Γ x y → slt W (hc_fvar φ u Γ) x y.
Proof. apply fl_fvar. Qed.

(** The body of an eta-expansion with upper point u runs below its
    future φ. *)
Lemma ub_fvar W Γ φ u : ub_below_s W (hc_fvar φ u Γ) u (∅, Some (FVar φ)).
Proof.
  destruct u as [x|]; [|done]. simpl. split; [set_solver|split; [|done]].
  intros φ' [= <-]. apply fl_v. simpl. by rewrite lookup_insert_eq.
Qed.

Lemma lcap_unl h a Δ : lenv_unl Δ → lcap h a Δ Δ.
Proof.
  induction Δ as [|o Δ IH]; intros HΔ; [constructor|].
  assert (lenv_unl Δ) as HΔ' by (intros o' Ho'; apply HΔ; by right).
  destruct (HΔ o (list_elem_of_here _ _)) as [->|(U & b & -> & HU)]; constructor; auto.
  apply cap_free, unlimited_tfree, HU.
Qed.

(** E-Abs for a closure that captures nothing. *)
Lemma eta_df W Γ Δ F ub e T aT U aU c t h :
  lenv_unl Δ →
  (∀ φ, φ ∉ dom (hc_fv Γ) → dftyped W ∅ (hc_fvar φ ub Γ) (Some (T, aT) :: Δ) (∅, Some (FVar φ)) e U) →
  dftyped W ∅ Γ Δ F (Lam e) (TLolli ub None c t h T aT U aU).
Proof.
  intros HΔ H. set (φ := fresh (dom (hc_fv Γ))).
  assert (φ ∉ dom (hc_fv Γ)) as Hφ by apply is_fresh.
  apply (d_abs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ φ Hφ); [|by apply H].
  destruct (lenv_unl_heads Δ HΔ) as [-> ->]. simpl. split; [|done].
  unfold tenv_heads. rewrite map_to_list_empty. set_solver.
Qed.

Lemma eta W N Γ Δ F ub e T aT U aU c t h a :
  lenv_unl Δ →
  (∀ φ, φ ∉ dom (hc_fv Γ) → typed W N ∅ (hc_fvar φ ub Γ) (Some (T, aT) :: Δ) (∅, Some (FVar φ)) e U aU c t) →
  typed W N ∅ Γ Δ F (Lam e) (TLolli ub None c t h T aT U aU) a (Some 0) tid.
Proof.
  intros HΔ H. set (φ := fresh (dom (hc_fv Γ))).
  assert (φ ∉ dom (hc_fv Γ)) as Hφ by apply is_fresh.
  apply (e_abs _ _ ∅ ∅ _ _ Δ _ _ _ _ _ _ _ _ _ _ _ _ φ Hφ); [| |by apply lcap_unl|by apply H].
  - destruct (lenv_unl_heads Δ HΔ) as [-> ->]. simpl. split; [|done].
    unfold tenv_heads. rewrite map_to_list_empty. set_solver.
  - intros o. by rewrite !lookup_empty.
Qed.

Local Ltac var_df HΔ := eapply d_var, lenv_only_unl, HΔ.
Local Ltac var HΔ := eapply e_var, lenv_only_unl, HΔ.

(** ** Deadlock-freedom typing *)

(** send : T[x·i] ⊗ S₀@x ⊸^x S@x⁺ under the conditions of E-Send. *)
Lemma k_send_df W Γ Δ F x S0 m T b S ap aS aT aU c t h :
  lenv_unl Δ → unfoldS S0 = SSeq (SSnd m T b) S → pscoped m T → hbot T = false →
  (∀ y, y ∈ heads (payload_at m T x) → slt W Γ x y) →
  dftyped W ∅ Γ Δ F (Lam (ESend (Var 0)))
    (TLolli (Some x) None c t h (TProd (payload_at m T x) ap (TSess S0 x) aS) aT (TSess S x⁺) aU).
Proof.
  intros HΔ Hu Hsc Hb Hh. apply eta_df; [done|]. intros φ Hφ.
  eapply d_send; [done|done|done| |apply ub_fvar|var_df HΔ].
  intros y Hy. apply slt_fvar; [done|by apply Hh].
Qed.

(** recv : S₀@x ⊸^x T[x·i] ⊗ S@x⁺. *)
Lemma k_recv_df W Γ Δ F x S0 m T b S aT b' a' aU c t h :
  lenv_unl Δ → unfoldS S0 = SSeq (SRcv m T b) S → pscoped m T →
  dftyped W ∅ Γ Δ F (Lam (ERecv (Var 0)))
    (TLolli (Some x) None c t h (TSess S0 x) aT (TProd (payload_at m T x) b' (TSess S x⁺) a') aU).
Proof.
  intros HΔ Hu Hsc. apply eta_df; [done|]. intros φ Hφ.
  eapply d_recv; [done|done|apply ub_fvar|var_df HΔ].
Qed.

(** close : S₀@x ⊸^x ∗. *)
Lemma k_close_df W Γ Δ F x S0 aT aU c t h :
  lenv_unl Δ → unfoldS S0 = SEnd →
  dftyped W ∅ Γ Δ F (Lam (EClose (Var 0))) (TLolli (Some x) None c t h (TSess S0 x) aT TUnit aU).
Proof.
  intros HΔ Hu. apply eta_df; [done|]. intros φ Hφ.
  eapply d_close; [done|apply ub_fvar|var_df HΔ].
Qed.

(** select_i : S₀@x ⊸^x S_i@(x·κ_i)‾. *)
Lemma k_select_df W (i : bool) Γ Δ F x S0 S1 S2 aT aU c t h :
  lenv_unl Δ → unfoldS S0 = SPlus S1 S2 →
  dftyped W ∅ Γ Δ F (Lam (ESel i (Var 0)))
    (TLolli (Some x) None c t h (TSess S0 x) aT (TSess (if i then S2 else S1) (sel_pt x i)) aU).
Proof.
  intros HΔ Hu. apply eta_df; [done|]. intros φ Hφ.
  eapply d_select; [done|apply ub_fvar|var_df HΔ].
Qed.

(** branch : S₀@x ⊸^x S₁@x·κ₁ ⊕ S₂@x·κ₂. *)
Lemma k_branch_df W Γ Δ F x S0 S1 S2 aT a1 a2 aU c t h :
  lenv_unl Δ → unfoldS S0 = SWith S1 S2 →
  dftyped W ∅ Γ Δ F (Lam (EBra (Var 0)))
    (TLolli (Some x) None c t h (TSess S0 x) aT
       (TSum (TSess S1 (bra_pt x false)) a1 (TSess S2 (bra_pt x true)) a2) aU).
Proof.
  intros HΔ Hu. apply eta_df; [done|]. intros φ Hφ.
  eapply d_branch; [done|apply ub_fvar|var_df HΔ].
Qed.

(** link : S@x ⊗ S̄@x̄ ⊸ ∗. *)
Lemma k_link_df W Γ Δ F S x a1 a2 aT aU c t h :
  lenv_unl Δ →
  dftyped W ∅ Γ Δ F (Lam (ELink (Var 0)))
    (TLolli None None c t h (TProd (TSess S x) a1 (TSess (dual S) x‾) a2) aT TUnit aU).
Proof.
  intros HΔ. apply eta_df; [done|]. intros φ Hφ.
  eapply d_link; var_df HΔ.
Qed.

(** spawn : (∗ ⊸^u_l ∗) ⊸ ∗. *)
Lemma k_spawn_df W Γ Δ F ub lb c' t' h' a1 aU' aT aU c t h :
  lenv_unl Δ →
  dftyped W ∅ Γ Δ F (Lam (ESpawn (Var 0)))
    (TLolli None None c t h (TLolli ub lb c' t' h' TUnit a1 TUnit aU') aT TUnit aU).
Proof.
  intros HΔ. apply eta_df; [done|]. intros φ Hφ.
  eapply d_spawn; var_df HΔ.
Qed.

(** force : □(∀ιs αs. C. ∗ ⊸^u U) ⊸^{u[xs]} U[ss][xs] under Γ ⊢ C[xs]. *)
Lemma k_force_df W Γ Δ F m k C ub c0 t0 U aU0 xs ss aT aU c t h :
  lenv_unl Δ → length xs = m → hold_at W Γ C xs → length ss = k → sinsts None ss →
  dftyped W ∅ Γ Δ F (Lam (EForce (Var 0)))
    (TLolli (pt_inst (plist xs) <$> ub) None c t h (TBox m k C ub c0 t0 U aU0) aT
       (sinst_ty (slist ss) (ty_inst xs U)) aU).
Proof.
  intros HΔ Hxs HC Hk Hss. apply eta_df; [done|]. intros φ Hφ.
  eapply d_force; [done| |done|done|apply ub_fvar|var_df HΔ].
  intros y z Hg. apply slt_fvar; [done|by apply HC].
Qed.

(** ** The merged judgment

    Each constant at the annotations of the rule of its primitive: cost
    1 for an action, the cost of one force for force, the identity
    ticket need, the refill N on the ends an action returns. *)

Lemma k_send W N Γ Δ F x S0 m T b S ap aS aT Tp' ap' h a :
  lenv_unl Δ → unfoldS S0 = SSeq (SSnd m T b) S → pscoped m T → hbot T = false →
  (∀ y, y ∈ heads (payload_at m T x) → slt W Γ x y) →
  tage (Some 1) (payload_at m T x, fadd aT ap) (Tp', ap') → tsub Tp' ap' (payload_at m T x) b →
  typed W N ∅ Γ Δ F (Lam (ESend (Var 0)))
    (TLolli (Some x) None (Some 1) tid h (TProd (payload_at m T x) ap (TSess S0 x) aS) aT (TSess S x⁺) N)
    a (Some 0) tid.
Proof.
  intros HΔ Hu Hsc Hb Hh Ha Hs. apply eta; [done|]. intros φ Hφ.
  change (Some 1) with (fadd (Some 0) (Some 1)). eapply e_send; [done|done|done| |apply ub_fvar|var HΔ|exact Ha|exact Hs].
  intros y Hy. apply slt_fvar; [done|by apply Hh].
Qed.

Lemma k_recv W N Γ Δ F x S0 m T b S aT h a :
  lenv_unl Δ → unfoldS S0 = SSeq (SRcv m T b) S → pscoped m T →
  typed W N ∅ Γ Δ F (Lam (ERecv (Var 0)))
    (TLolli (Some x) None (Some 1) tid h (TSess S0 x) aT (TProd (payload_at m T x) b (TSess S x⁺) N) (Some 0))
    a (Some 0) tid.
Proof.
  intros HΔ Hu Hsc. apply eta; [done|]. intros φ Hφ.
  change (Some 1) with (fadd (Some 0) (Some 1)). eapply e_recv; [done|done|apply ub_fvar|var HΔ].
Qed.

Lemma k_close W N Γ Δ F x S0 aT h a :
  lenv_unl Δ → unfoldS S0 = SEnd →
  typed W N ∅ Γ Δ F (Lam (EClose (Var 0)))
    (TLolli (Some x) None (Some 1) tid h (TSess S0 x) aT TUnit None) a (Some 0) tid.
Proof.
  intros HΔ Hu. apply eta; [done|]. intros φ Hφ.
  change (Some 1) with (fadd (Some 0) (Some 1)). eapply e_close; [done|apply ub_fvar|var HΔ].
Qed.

Lemma k_select W N (i : bool) Γ Δ F x S0 S1 S2 aT h a :
  lenv_unl Δ → unfoldS S0 = SPlus S1 S2 →
  typed W N ∅ Γ Δ F (Lam (ESel i (Var 0)))
    (TLolli (Some x) None (Some 1) tid h (TSess S0 x) aT (TSess (if i then S2 else S1) (sel_pt x i)) N)
    a (Some 0) tid.
Proof.
  intros HΔ Hu. apply eta; [done|]. intros φ Hφ.
  change (Some 1) with (fadd (Some 0) (Some 1)). eapply e_select; [done|apply ub_fvar|var HΔ].
Qed.

Lemma k_branch W N Γ Δ F x S0 S1 S2 aT h a :
  lenv_unl Δ → unfoldS S0 = SWith S1 S2 →
  typed W N ∅ Γ Δ F (Lam (EBra (Var 0)))
    (TLolli (Some x) None (Some 1) tid h (TSess S0 x) aT
       (TSum (TSess S1 (bra_pt x false)) N (TSess S2 (bra_pt x true)) N) (Some 0))
    a (Some 0) tid.
Proof.
  intros HΔ Hu. apply eta; [done|]. intros φ Hφ.
  change (Some 1) with (fadd (Some 0) (Some 1)). eapply e_branch; [done|apply ub_fvar|var HΔ].
Qed.

Lemma k_link W N Γ Δ F S x a1 a2 aT h a :
  lenv_unl Δ →
  typed W N ∅ Γ Δ F (Lam (ELink (Var 0)))
    (TLolli None None (Some 0) (tseq tid (tlink tid)) h (TProd (TSess S x) a1 (TSess (dual S) x‾) a2) aT
       TUnit None)
    a (Some 0) tid.
Proof.
  intros HΔ. apply eta; [done|]. intros φ Hφ.
  eapply e_link; [var HΔ|right; left; discriminate].
Qed.

Lemma k_spawn W N Γ Δ F ub lb c' t' h' a1 aU' aT h a :
  lenv_unl Δ → fle (Some 1) aT →
  typed W N ∅ Γ Δ F (Lam (ESpawn (Var 0)))
    (TLolli None None (Some 0) (tseq tid (tspawn (tapp t' 0) tid)) h
       (TLolli ub lb c' t' h' TUnit a1 TUnit aU') aT TUnit None)
    a (Some 0) tid.
Proof.
  intros HΔ Ha. apply eta; [done|]. intros φ Hφ.
  eapply e_spawn; [var HΔ|done|right; left; discriminate].
Qed.

Lemma k_force W N Γ Δ F m k C ub c0 t0 U aU0 xs ss aT h a :
  lenv_unl Δ → length xs = m → hold_at W Γ C xs → length ss = k → sinsts N ss →
  typed W N ∅ Γ Δ F (Lam (EForce (Var 0)))
    (TLolli (pt_inst (plist xs) <$> ub) None (fadd (Some 0) c0) (tseq tid t0) h (TBox m k C ub c0 t0 U aU0) aT
       (sinst_ty (slist ss) (ty_inst xs U)) aU0)
    a (Some 0) tid.
Proof.
  intros HΔ Hxs HC Hk Hss. apply eta; [done|]. intros φ Hφ.
  eapply e_force; [done| |done|done|apply ub_fvar|var HΔ|right; left; discriminate].
  intros y z Hg. apply slt_fvar; [done|by apply HC].
Qed.
