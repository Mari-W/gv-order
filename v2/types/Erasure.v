(** * The annotations of N = ∞ commute with the type operations (stage S2)

    [ty_df] and [sty_df] set every cost annotation to its value at
    N = ∞. They commute with point instantiation, session renaming,
    flipping, duality, substitution, unrolling and the head normal form,
    and they preserve ≈. The conservativity lemma of
    static/Conservativity.v reads these facts. *)

From GV Require Export types.Types.

Lemma cr_df_pinst σ T : cr_df (pinst_ty σ T) = cr_df T.
Proof. by destruct T. Qed.
Lemma cr_df_sinst σ T : cr_df (sinst_ty σ T) = cr_df T.
Proof. by destruct T. Qed.
Lemma cr_df_sren r T : cr_df (sren_ty r T) = cr_df T.
Proof. by destruct T. Qed.
Lemma cr_df_sflip k T : cr_df (sflip_ty k T) = cr_df T.
Proof. by destruct T. Qed.

Lemma heads_df T : heads (ty_df T) = heads T.
Proof. induction T; simpl; congruence. Qed.

Lemma hbot_df T : hbot (ty_df T) = hbot T.
Proof. induction T; simpl; try congruence; by destruct lb. Qed.

Lemma unlimited_df T : unlimited (ty_df T) ↔ unlimited T.
Proof. by destruct T. Qed.

Lemma tfree_df T : tfree T → tfree (ty_df T).
Proof. induction 1; simpl; constructor; auto. Qed.

Lemma tfree_df_inv T : tfree (ty_df T) → tfree T.
Proof.
  induction T; simpl; intros H; inversion H; subst; constructor; auto.
Qed.

Lemma prim_df T : prim T → prim (ty_df T).
Proof. induction 1; simpl; constructor; auto. Qed.

(** ** Point instantiation *)

Lemma df_pinst_mut :
  (∀ T σ, ty_df (pinst_ty σ T) = pinst_ty σ (ty_df T)) ∧
  (∀ s σ, sty_df (pinst_sty σ s) = pinst_sty σ (sty_df s)).
Proof.
  split; [|done]. intros T. induction T; intros σ; simpl; rewrite ?cr_df_pinst; congruence.
Qed.

Lemma ty_df_pinst σ T : ty_df (pinst_ty σ T) = pinst_ty σ (ty_df T).
Proof. apply df_pinst_mut. Qed.
Lemma sty_df_pinst σ s : sty_df (pinst_sty σ s) = pinst_sty σ (sty_df s).
Proof. apply df_pinst_mut. Qed.

Lemma df_pscoped_mut :
  (∀ T k, pscoped k (ty_df T) ↔ pscoped k T) ∧ (∀ s, sscoped (sty_df s) ↔ sscoped s).
Proof.
  apply ty_sty_mut_ind; intros; simpl; try done; naive_solver.
Qed.

Lemma pscoped_df k T : pscoped k (ty_df T) ↔ pscoped k T.
Proof. apply df_pscoped_mut. Qed.

Lemma payload_at_df m T x : payload_at m (ty_df T) x = ty_df (payload_at m T x).
Proof. unfold payload_at, ty_inst. by rewrite ty_df_pinst. Qed.

Lemma ty_inst_df xs T : ty_inst xs (ty_df T) = ty_df (ty_inst xs T).
Proof. unfold ty_inst. by rewrite ty_df_pinst. Qed.

(** ** Session operations *)

Lemma df_sren_mut :
  (∀ T r, ty_df (sren_ty r T) = sren_ty r (ty_df T)) ∧
  (∀ s r, sty_df (sren r s) = sren r (sty_df s)).
Proof. apply ty_sty_mut_ind; intros; simpl; rewrite ?cr_df_sren; congruence. Qed.

Lemma sty_df_sren r s : sty_df (sren r s) = sren r (sty_df s).
Proof. apply df_sren_mut. Qed.

Lemma df_sflip_mut :
  (∀ T k, ty_df (sflip_ty k T) = sflip_ty k (ty_df T)) ∧
  (∀ s k, sty_df (sflip k s) = sflip k (sty_df s)).
Proof.
  apply ty_sty_mut_ind; intros; simpl; rewrite ?cr_df_sflip; try congruence.
  all: by case_decide.
Qed.

Lemma sty_df_sflip k s : sty_df (sflip k s) = sflip k (sty_df s).
Proof. apply df_sflip_mut. Qed.

Lemma sty_df_dual s : sty_df (dual s) = dual (sty_df s).
Proof.
  induction s; simpl; try congruence.
  by rewrite sty_df_sflip, IHs.
Qed.

Lemma sty_up_ext σ σ' : (∀ a, σ a = σ' a) → ∀ a, sty_up σ a = sty_up σ' a.
Proof. intros H [|a]; simpl; [done|]. unfold compose. by rewrite H. Qed.

Lemma iter_sty_up_ext k σ σ' :
  (∀ a, σ a = σ' a) → ∀ a, Nat.iter k sty_up σ a = Nat.iter k sty_up σ' a.
Proof. revert σ σ'. induction k as [|k IH]; intros σ σ' H; simpl; [done|]. by apply sty_up_ext, IH. Qed.

Lemma sinst_ext_mut :
  (∀ T σ σ', (∀ a, σ a = σ' a) → sinst_ty σ T = sinst_ty σ' T) ∧
  (∀ s σ σ', (∀ a, σ a = σ' a) → sinst σ s = sinst σ' s).
Proof.
  apply ty_sty_mut_ind; intros; simpl; f_equal; auto.
  all: try (apply H; by apply iter_sty_up_ext).
  all: try (apply H; by apply sty_up_ext).
Qed.

Lemma sinst_ty_ext T σ σ' : (∀ a, σ a = σ' a) → sinst_ty σ T = sinst_ty σ' T.
Proof. apply sinst_ext_mut. Qed.
Lemma sinst_ext s σ σ' : (∀ a, σ a = σ' a) → sinst σ s = sinst σ' s.
Proof. apply sinst_ext_mut. Qed.

Lemma sty_up_df σ a : sty_df (sty_up σ a) = sty_up (sty_df ∘ σ) a.
Proof. destruct a; simpl; [done|]. unfold compose. apply sty_df_sren. Qed.

Lemma iter_sty_up_df k σ a :
  sty_df (Nat.iter k sty_up σ a) = Nat.iter k sty_up (sty_df ∘ σ) a.
Proof.
  revert σ a. induction k as [|k IH]; intros σ a; simpl; [done|].
  rewrite sty_up_df. apply sty_up_ext. intros b. apply IH.
Qed.

Lemma df_sinst_mut :
  (∀ T σ, ty_df (sinst_ty σ T) = sinst_ty (sty_df ∘ σ) (ty_df T)) ∧
  (∀ s σ, sty_df (sinst σ s) = sinst (sty_df ∘ σ) (sty_df s)).
Proof.
  apply ty_sty_mut_ind; intros; simpl; rewrite ?cr_df_sinst; try congruence.
  all: try apply sty_df_dual.
  all: try (rewrite H; f_equal; apply sinst_ty_ext; intros a; apply iter_sty_up_df).
  all: try (rewrite H; f_equal; apply sinst_ext; intros a; apply sty_up_df).
Qed.

Lemma ty_df_sinst σ T : ty_df (sinst_ty σ T) = sinst_ty (sty_df ∘ σ) (ty_df T).
Proof. apply df_sinst_mut. Qed.
Lemma sty_df_sinst σ s : sty_df (sinst σ s) = sinst (sty_df ∘ σ) (sty_df s).
Proof. apply df_sinst_mut. Qed.

(** At instances that already carry the annotations of N = ∞. *)
Lemma ty_df_sinst_slist ss T :
  Forall (λ s, sty_df s = s) ss →
  ty_df (sinst_ty (slist ss) T) = sinst_ty (slist ss) (ty_df T).
Proof.
  intros Hss. rewrite ty_df_sinst. apply sinst_ty_ext. intros a. unfold compose, slist.
  destruct (ss !! a) as [s|] eqn:E; [|done].
  by apply (Forall_lookup_1 _ _ _ _ Hss E).
Qed.

Lemma sty_df_unroll b : sty_df (unroll b) = unroll (sty_df b).
Proof.
  unfold unroll. rewrite sty_df_sinst. apply sinst_ext. by intros [|a].
Qed.

Lemma sty_df_skip s : sty_df s = SSkip ↔ s = SSkip.
Proof. by destruct s. Qed.

Lemma sty_df_hseq h s2 : sty_df (hseq h s2) = hseq (sty_df h) (sty_df s2).
Proof.
  destruct h as [| | | | | | |o r| |]; try done.
  destruct r; done.
Qed.

Lemma sfuel_df s : sfuel (sty_df s) = sfuel s.
Proof. induction s; simpl; auto. Qed.

Lemma unrN_df k : ∀ s, unrN k (sty_df s) = sty_df <$> unrN k s.
Proof.
  induction k as [|k IH]; intros s; [done|].
  destruct s; cbn [sty_df unrN]; try done.
  - by rewrite <-sty_df_unroll, IH.
  - rewrite IH. destruct (unrN k s1) as [h|]; cbn [fmap option_fmap option_map]; [|done].
    destruct h; cbn [sty_df]; [| |..]; try apply IH.
    all: match goal with |- _ = _ <$> Some (hseq ?h ?s) => exact (f_equal Some (eq_sym (sty_df_hseq h s))) end.
Qed.

Lemma unfoldS_df s : unfoldS (sty_df s) = sty_df (unfoldS s).
Proof.
  unfold unfoldS. rewrite sfuel_df, unrN_df. by destruct (unrN (sfuel s) s).
Qed.

Definition hview_df (h : hview) : hview :=
  match h with
  | HRcv m T _ s => HRcv m (ty_df T) (cr_df T) (sty_df s)
  | HSnd m T _ s => HSnd m (ty_df T) (cr_df T) (sty_df s)
  | HVar a s => HVar a (sty_df s)
  | HVarD a s => HVarD a (sty_df s)
  | HPlus a b => HPlus (sty_df a) (sty_df b)
  | HWith a b => HWith (sty_df a) (sty_df b)
  | HStuck u => HStuck (sty_df u)
  | h => h
  end.

Lemma view_df u : view (sty_df u) = hview_df (view u).
Proof. destruct u as [| | | | | | |o r| |]; try done. by destruct o. Qed.

Lemma hd_df s : hd (sty_df s) = hview_df (hd s).
Proof. unfold hd. by rewrite unfoldS_df, view_df. Qed.

(** ** ≈ is preserved *)

Lemma eqT_cr_df ρ T U : eqT ρ T U → cr_df T = cr_df U.
Proof. destruct T, U; simpl; naive_solver. Qed.

Lemma eqT_df (ρ ρ' : sty → sty → Prop) T : ∀ U,
  (∀ s r, ρ s r → ρ' (sty_df s) (sty_df r)) → eqT ρ T U → eqT ρ' (ty_df T) (ty_df U).
Proof.
  induction T; intros [] Hρ H; simpl in *; try done.
  all: destruct_and?; subst; split_and?; eauto using eqT_cr_df.
  all: repeat case_match; subst; eauto using eqT_cr_df.
Qed.

(** One observation of ≈ at every depth gives ≈ one step down. *)
Lemma eqT_forall T : ∀ U, (∀ n, eqT (aeq n) T U) → eqT sequiv T U.
Proof.
  induction T; intros [] H; simpl in *; try (by specialize (H 0)).
  all: try (pose proof (H 0) as H0; destruct_and?; subst).
  all: split_and?; try done.
  all: try ((apply IHT1 || apply IHT2 || apply IHT); intros n; specialize (H n); naive_solver).
  all: try (intros n; specialize (H n); naive_solver).
  all: case_match; [apply IHT; intros n; specialize (H n); simpl in H; naive_solver
                   |specialize (H 0); simpl in H; naive_solver].
Qed.

Lemma sequiv_step s r : sequiv s r → eq_step sequiv s r.
Proof.
  intros H. assert (∀ n, eq_step (aeq n) s r) as Hn by (intros n; exact (H (S n))).
  clear H. unfold eq_step in *.
  destruct (hd s), (hd r); try (by specialize (Hn 0)).
  all: pose proof (Hn 0) as H0; destruct_and?; subst; split_and?; try done.
  all: first [ intros n; specialize (Hn n); naive_solver
             | apply eqT_forall; intros n; specialize (Hn n); naive_solver ].
Qed.

Lemma sequiv_df s r : sequiv s r → sequiv (sty_df s) (sty_df r).
Proof.
  intros H. apply (sequiv_coind (λ s r, ∃ s0 r0, s = sty_df s0 ∧ r = sty_df r0 ∧ sequiv s0 r0));
    [|eauto].
  clear. intros s r (s0 & r0 & -> & -> & H). apply sequiv_step in H.
  unfold eq_step in *. rewrite !hd_df.
  hd_cases s0; hd_cases r0; simpl; try done.
  all: destruct_and?; subst; split_and?; eauto using eqT_cr_df.
  all: try (eapply eqT_df; [|done]; intros a b Hab; eauto).
  all: congruence.
Qed.

Lemma teq_df T U : teq T U → teq (ty_df T) (ty_df U).
Proof. apply eqT_df. apply sequiv_df. Qed.
