(** * Readiness and frames (§6)

    The gate of the logical relation's step clauses. A stable term or
    process (no internal step left) must either be done, or offer some
    of the entries it holds, and every entry it holds but does not
    offer must lie strictly above some offered one in the world's
    order. Entries, not names, are compared: a thread holding both ends
    of c and blocking on one of them holds the other entry unoffered and
    would need head(c) ≺ head(c).

    The frame condition says the offered entries lie below the frame F,
    the points the context of the term still has to use. *)

From stdpp Require Import base strings gmap gmultiset.
From LRGV Require Export Safety Worlds.

(** ** Offered entries

    The entry of Θ a session label selects: c!v the entry of c whose
    type unfolds to !…, c?v the one with ?…, c! one Close entry (the
    first, when both ends of c are Close: closing consumes only one),
    c↔d the entries of c and d (both entries of c for a self-link). *)

Definition selects (Θ : tenv) (σ : slabel) (k : ekey) : Prop :=
  match σ with
  | SSend c _ =>
      k.1 = c ∧ ∃ e m T s, tenv_entry Θ k = Some e ∧ unfoldS e.1 = SSnd m T s
  | SRecv c _ =>
      k.1 = c ∧ ∃ e m T s, tenv_entry Θ k = Some e ∧ unfoldS e.1 = SRcv m T s
  | SClos c =>
      k.1 = c ∧ ∃ e, tenv_entry Θ k = Some e ∧ unfoldS e.1 = SEnd ∧
        (k.2 = true →
           ∀ e', tenv_entry Θ (c, false) = Some e' → unfoldS e'.1 ≠ SEnd)
  | SLink cd => k.1 ∈ cd ∧ is_Some (tenv_entry Θ k)
  end.

Definition offered_t (Θ : tenv) (t : expr) (k : ekey) : Prop :=
  ∃ σ t', tstep t (LSess σ) t' ∧ selects Θ σ k.

Definition offered_p (Σ : senv) (p : proc) (k : ekey) : Prop :=
  ∃ σ p', proc_step p (PSess σ) p' ∧ selects (tenv_of Σ) σ k.

(** ** Stability *)

(** No β, (νc) or ⇑v step. *)
Definition stable_t (t : expr) : Prop :=
  ∀ α t', tstep t α t' → match α with LSess _ => True | _ => False end.

(** No τ step. *)
Definition stable_p (p : proc) : Prop := ∀ p', ¬ proc_step p PTau p'.

(** ** ready_W and frame_W *)

(** Every held entry not offered lies strictly above an offered one. *)
Definition above_offered (W : world) (Θ : tenv) (off : ekey → Prop) : Prop :=
  ∀ k e, tenv_entry Θ k = Some e → ¬ off k →
    ∃ k' e', off k' ∧ tenv_entry Θ k' = Some e' ∧
      w_lt W (entry_head k' e') (entry_head k e).

Definition ready_t (W : world) (Θ : tenv) (t : expr) : Prop :=
  stable_t t →
    ((∀ k, ¬ offered_t Θ t k) → is_val t) ∧
    above_offered W Θ (offered_t Θ t).

Definition ready_p (W : world) (Σ : senv) (p : proc) : Prop :=
  stable_p p →
    ((∀ k, ¬ offered_p Σ p k) → terminated p) ∧
    above_offered W (tenv_of Σ) (offered_p Σ p).

(** The offered entries lie below the frame. *)
Definition frame_t (W : world) (Θ : tenv) (t : expr) (F : gset point) : Prop :=
  stable_t t →
    ∀ k e, offered_t Θ t k → tenv_entry Θ k = Some e →
      ∀ y, y ∈ F → w_lt W (entry_head k e) y.

(** ** Basic facts *)

Lemma frame_t_empty W Θ t : frame_t W Θ t ∅.
Proof. intros _ k e _ _ y Hy. set_solver. Qed.

Lemma frame_t_mono W Θ t F F' : F' ⊆ F → frame_t W Θ t F → frame_t W Θ t F'.
Proof. intros HF H Hs k e Ho He y Hy. apply (H Hs k e); [done..|set_solver]. Qed.

(** Values have no transitions, so they are stable and offer nothing. *)
Lemma val_stable_t v : is_val v → stable_t v.
Proof. intros Hv α t' Hst. exfalso. by eapply val_no_tstep. Qed.

Lemma val_not_offered Θ v k : is_val v → ¬ offered_t Θ v k.
Proof. intros Hv (σ & t' & Hst & _). by eapply val_no_tstep. Qed.
