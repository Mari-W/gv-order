(** * Readiness and futures (stage S3, proposal §2.6)

    Readiness ready_W excludes circular waiting. It is the readiness of
    theories/relation/Readiness.v with one entry per end. A term with
    future F that is stable and reducible offers some held ends, and every
    offered end lies below the partner point of every held end it does not
    offer, and below every point of F. A process offers some interface
    end, and every interface end it holds and does not offer has an
    offered end below its partner point. A link redex compares nothing.

    The environments of the relation map an end to a session type at a
    point, S@x, with no credit: Θ and Σ share the type [senv] of
    static/Contexts.v. Ends have their own names, so an end offered by a
    label is the subject of the label, and no polarity test picks an
    entry. *)

From GV Require Export lang.Safety static.Typing.

(** ** Heads, lower and upper points

    heads(o : S@x) = {x‾}. The lower point of a closure bounds its heads
    from below, l ≼ heads Θ, and its upper point bounds the future of
    its caller from below, u ≺ F. *)

Definition senv_heads (Θ : senv) : gset point :=
  list_to_set ((λ oe : cend * (sty * point), (oe.2.2)‾) <$> map_to_list Θ).

Lemma elem_of_senv_heads Θ y : y ∈ senv_heads Θ ↔ ∃ o S x, Θ !! o = Some (S, x) ∧ y = x‾.
Proof.
  unfold senv_heads. rewrite elem_of_list_to_set, list_elem_of_fmap. split.
  - intros ([o [S x]] & -> & Ho). apply elem_of_map_to_list in Ho. eauto.
  - intros (o & S & x & Ho & ->). exists (o, (S, x)). split; [done|].
    by apply elem_of_map_to_list.
Qed.

Lemma senv_heads_empty : senv_heads ∅ = ∅.
Proof. unfold senv_heads. by rewrite map_to_list_empty. Qed.

Definition lb_le (W : world) (lb : option point) (H : gset point) : Prop :=
  match lb with None => H = ∅ | Some x => ∀ y, y ∈ H → w_le W x y end.

Definition ub_lt (W : world) (ub : option point) (F : gset point) : Prop :=
  match ub with None => True | Some x => ∀ y, y ∈ F → W ⊢ x ≺ y end.

Definition lbx_le (W : world) (lb : lbound) (H : gset point) : Prop :=
  match lb with LBot => True | LNone => H = ∅ | LPt x => ∀ y, y ∈ H → w_le W x y end.

(** C holds at the instance xs in W. *)
Definition wholds (W : world) (C : bcs) (xs : list point) : Prop :=
  ∀ x y, bcs_at C xs (FLt x y) → W ⊢ x ≺ y.

Lemma w_le_mono W W' x y : W ⊑ W' → w_le W x y → w_le W' x y.
Proof. intros HW [->|H]; [by left|right; by eapply w_lt_mono]. Qed.

Lemma lb_le_mono W W' lb H : W ⊑ W' → lb_le W lb H → lb_le W' lb H.
Proof. intros HW. destruct lb; simpl; [|done]. intros Hl y Hy. eauto using w_le_mono. Qed.

Lemma ub_lt_mono W W' ub F : W ⊑ W' → ub_lt W ub F → ub_lt W' ub F.
Proof. intros HW. destruct ub; simpl; [|done]. intros Hl y Hy. eauto using w_lt_mono. Qed.

Lemma ub_lt_future W ub F F' : F' ⊆ F → ub_lt W ub F → ub_lt W ub F'.
Proof. intros HF. destruct ub; simpl; [|done]. intros Hl y Hy. apply Hl. set_solver. Qed.

Lemma lbx_le_mono W W' lb H : W ⊑ W' → lbx_le W lb H → lbx_le W' lb H.
Proof. intros HW. destruct lb; simpl; try done. intros Hl y Hy. eauto using w_le_mono. Qed.

Lemma wholds_mono W W' C xs : W ⊑ W' → wholds W C xs → wholds W' C xs.
Proof. intros HW H x y Hxy. eapply w_lt_mono; [done|]. by apply H. Qed.

(** ** Offered ends *)

(** The ends a session label acts on. *)
Definition sends (σ : slabel) : gset cend :=
  match σ with
  | SSend o _ _ | SRecv o _ | SClose o | SSel o _ | SBra o _ => {[o]}
  | SLink os => os
  end.

Definition offered_t (Θ : senv) (t : expr) (o : cend) : Prop :=
  o ∈ dom Θ ∧ ∃ σ t', tstep t (LSess σ) t' ∧ o ∈ sends σ.

Definition offered_p (Σ : senv) (p : proc) (o : cend) : Prop :=
  o ∈ dom Σ ∧ ∃ σ p', pstep p (PSess σ) p' ∧ o ∈ sends σ.

(** ** Stability and links *)

(** No step but an offer. *)
Definition stable_t (t : expr) : Prop := ∀ α t', tstep t α t' → ∃ σ, α = LSess σ.

(** No τ step. *)
Definition stable_p (p : proc) : Prop := ∀ p', ¬ preduction p p'.

(** A link redex. A link never waits, so it compares nothing. *)
Definition link_t (t : expr) : Prop := ∃ os t', tstep t (LSess (SLink os)) t'.
Definition link_p (p : proc) : Prop := ∃ os p', pstep p (PSess (SLink os)) p'.

(** ** ready_W *)

(** Every offered end at u lies below x‾ for every held end at x it
    does not offer, and below every point of F. *)
Definition below_rest (W : world) (Θ : senv) (off : cend → Prop) (F : gset point) : Prop :=
  ∀ o S x, off o → Θ !! o = Some (S, x) →
    (∀ o' S' x', Θ !! o' = Some (S', x') → ¬ off o' → W ⊢ x ≺ x'‾) ∧
    (∀ y, y ∈ F → W ⊢ x ≺ y).

(** Every held end at x that is not offered has an offered end below
    x‾. *)
Definition above_offered (W : world) (Σ : senv) (off : cend → Prop) : Prop :=
  ∀ o S x, Σ !! o = Some (S, x) → ¬ off o →
    ∃ o' S' x', off o' ∧ Σ !! o' = Some (S', x') ∧ W ⊢ x' ≺ x‾.

(** ready_W(Θ ∣ F, t). *)
Definition ready_t (W : world) (Θ : senv) (F : gset point) (t : expr) : Prop :=
  stable_t t →
    ((∀ o, ¬ offered_t Θ t o) → is_val t) ∧
    (link_t t ∨ below_rest W Θ (offered_t Θ t) F).

(** ready_W(Σ, p). *)
Definition ready_p (W : world) (Σ : senv) (p : proc) : Prop :=
  stable_p p →
    link_p p ∨
    (((∀ o, ¬ offered_p Σ p o) → terminated p) ∧ above_offered W Σ (offered_p Σ p)).

Notation "'ready' '_' W ( Θ ∣ F , t )" := (ready_t W Θ F t)
  (at level 10, W at level 0, format "'ready'  '_'  W ( Θ  ∣  F ,  t )").
Notation "'ready' '_' W ( Σ , p )" := (ready_p W Σ p)
  (at level 10, W at level 0, format "'ready'  '_'  W ( Σ ,  p )").

(** ** Basic facts *)

Lemma below_rest_future W Θ off F F' :
  F' ⊆ F → below_rest W Θ off F → below_rest W Θ off F'.
Proof.
  intros HF H o S x Ho Hx. destruct (H o S x Ho Hx) as [H1 H2].
  split; [done|]. intros y Hy. apply H2. set_solver.
Qed.

Lemma below_rest_mono W W' Θ off F :
  W ⊑ W' → below_rest W Θ off F → below_rest W' Θ off F.
Proof.
  intros HW H o S x Ho Hx. destruct (H o S x Ho Hx) as [H1 H2].
  split; intros; eapply w_lt_mono; eauto.
Qed.

Lemma above_offered_mono W W' Σ off :
  W ⊑ W' → above_offered W Σ off → above_offered W' Σ off.
Proof.
  intros HW H o S x Ho Hn. destruct (H o S x Ho Hn) as (o' & S' & x' & ? & ? & ?).
  exists o', S', x'. split_and!; [done|done|]. by eapply w_lt_mono.
Qed.

Lemma ready_t_future W Θ t F F' : F' ⊆ F → ready _ W(Θ ∣ F, t) → ready _ W(Θ ∣ F', t).
Proof.
  intros HF H Hs. destruct (H Hs) as [? [?|?]]; split; [done|by left|done|].
  right. by eapply below_rest_future.
Qed.

Lemma ready_t_mono W W' Θ F t : W ⊑ W' → ready _ W(Θ ∣ F, t) → ready _ W'(Θ ∣ F, t).
Proof.
  intros HW H Hs. destruct (H Hs) as [? [?|?]]; split; [done|by left|done|].
  right. by eapply below_rest_mono.
Qed.

Lemma ready_p_mono W W' Σ p : W ⊑ W' → ready _ W(Σ, p) → ready _ W'(Σ, p).
Proof.
  intros HW H Hs. destruct (H Hs) as [?|[? ?]]; [by left|right].
  split; [done|]. by eapply above_offered_mono.
Qed.

(** With an offered end, below_rest gives above_offered. *)
Lemma below_rest_above W Θ (off : cend → Prop) F o0 S0 x0 :
  off o0 → Θ !! o0 = Some (S0, x0) →
  below_rest W Θ off F → above_offered W Θ off.
Proof.
  intros Ho Hx H o S x Hy Hn. exists o0, S0, x0. split_and!; [done|done|].
  exact (proj1 (H o0 S0 x0 Ho Hx) o S x Hy Hn).
Qed.
