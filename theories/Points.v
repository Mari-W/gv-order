(** * Renaming points (§10)

    A transposition a ↔ b of point constants, applied to a world, to
    the points and session types of an environment, to a type and to
    a frame, maps the logical relation to itself ([rel_psw]). Terms
    and processes mention no points, so they stay as they are.

    Consequences: the point a term or a process creates at [new] can
    be renamed away from any finite set of names, which is what
    monotonicity in the world and P-Connect's new case need.

    The file builds the transport bottom-up: points, types and session
    types, worlds, environments, readiness, and finally the three
    relations by induction on the step index. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export Relation.

(** ** The transposition on constants, names and points *)

Definition nswap (a b x : nat) : nat :=
  if decide (x = a) then b else if decide (x = b) then a else x.

Lemma nswap_involutive a b x : nswap a b (nswap a b x) = x.
Proof. unfold nswap. repeat case_decide; congruence. Qed.

Lemma nswap_inj a b x y : nswap a b x = nswap a b y → x = y.
Proof.
  intros H. rewrite <-(nswap_involutive a b x), <-(nswap_involutive a b y).
  by rewrite H.
Qed.

Lemma nswap_ne a b x : x ≠ a → x ≠ b → nswap a b x = x.
Proof. unfold nswap. repeat case_decide; congruence. Qed.

Lemma nswap_l a b : nswap a b a = b.
Proof. unfold nswap. by case_decide. Qed.

Fixpoint pnsw (a b : nat) (p : pname) : pname :=
  match p with
  | NConst x => NConst (nswap a b x)
  | NVar x => NVar x
  | NSlot q o i => NSlot (pnsw a b q) o i
  end.

Definition ptsw (a b : nat) (x : point) : point :=
  Pt (pnsw a b (pt_name x)) (pt_off x).

Fixpoint tysw (a b : nat) (T : ty) : ty :=
  match T with
  | TUnit => TUnit
  | TLolli ub lb T1 U =>
      TLolli (ptsw a b <$> ub) (ptsw a b <$> lb) (tysw a b T1) (tysw a b U)
  | TProd T1 U => TProd (tysw a b T1) (tysw a b U)
  | TSum T1 U => TSum (tysw a b T1) (tysw a b U)
  | TBox n T1 => TBox n (tysw a b T1)
  | TSess s x => TSess (stysw a b s) (ptsw a b x)
  end
with stysw (a b : nat) (s : sty) : sty :=
  match s with
  | SRcv m T s' => SRcv m (tysw a b T) (stysw a b s')
  | SSnd m T s' => SSnd m (tysw a b T) (stysw a b s')
  | SEnd => SEnd
  | SMu s' => SMu (stysw a b s')
  | SVar x => SVar x
  | SVarD x => SVarD x
  end.

Section points.
  Context (a b : nat).

  Lemma pnsw_involutive p : pnsw a b (pnsw a b p) = p.
  Proof. induction p; simpl; f_equal; auto using nswap_involutive. Qed.

  Lemma ptsw_involutive x : ptsw a b (ptsw a b x) = x.
  Proof. destruct x. unfold ptsw. simpl. by rewrite pnsw_involutive. Qed.

  Lemma pnsw_inj p q : pnsw a b p = pnsw a b q → p = q.
  Proof.
    intros H. rewrite <-(pnsw_involutive p), <-(pnsw_involutive q). by rewrite H.
  Qed.

  Lemma ptsw_inj x y : ptsw a b x = ptsw a b y → x = y.
  Proof.
    intros H. rewrite <-(ptsw_involutive x), <-(ptsw_involutive y). by rewrite H.
  Qed.

  Lemma ptsw_shift n x : ptsw a b (pt_shift n x) = pt_shift n (ptsw a b x).
  Proof. done. Qed.

  Lemma ptsw_slot x i : ptsw a b (pt_slot x i) = pt_slot (ptsw a b x) i.
  Proof. done. Qed.

  Lemma ptsw_pvar x : ptsw a b (pvar x) = pvar x.
  Proof. done. Qed.

  Lemma ptsw_pconst x : ptsw a b (pconst x) = pconst (nswap a b x).
  Proof. done. Qed.

  Lemma pn_root_sw p : pn_root (pnsw a b p) = pnsw a b (pn_root p).
  Proof. induction p; simpl; auto. Qed.

  Lemma pt_root_sw x : pt_root (ptsw a b x) = pnsw a b (pt_root x).
  Proof. apply pn_root_sw. Qed.

  Lemma pt_ground_sw x : pt_ground (ptsw a b x) ↔ pt_ground x.
  Proof.
    unfold pt_ground. destruct x as [p o]. unfold ptsw. simpl.
    rewrite pn_root_sw. split; intros [c Hc].
    - destruct (pn_root p) eqn:E; simpl in Hc; try discriminate. eauto.
    - rewrite Hc. simpl. eauto.
  Qed.

  Lemma ptsw_fmap_involutive (o : option point) :
    ptsw a b <$> (ptsw a b <$> o) = o.
  Proof. destruct o; simpl; by rewrite ?ptsw_involutive. Qed.

  Lemma tysw_involutive_mut :
    (∀ T, tysw a b (tysw a b T) = T) ∧ (∀ s, stysw a b (stysw a b s) = s).
  Proof.
    apply ty_sty_mut_ind; intros; simpl; f_equal;
      rewrite ?ptsw_fmap_involutive, ?ptsw_involutive; done.
  Qed.

  Lemma tysw_involutive T : tysw a b (tysw a b T) = T.
  Proof. apply tysw_involutive_mut. Qed.

  Lemma stysw_involutive s : stysw a b (stysw a b s) = s.
  Proof. apply tysw_involutive_mut. Qed.

  (** Session-variable operations ignore points. *)
  Lemma sren_sw_mut :
    (∀ T r, tysw a b (sren_ty r T) = sren_ty r (tysw a b T)) ∧
    (∀ s r, stysw a b (sren r s) = sren r (stysw a b s)).
  Proof. apply ty_sty_mut_ind; intros; simpl; f_equal; auto. Qed.

  Lemma sflip_sw_mut :
    (∀ T k, tysw a b (sflip_ty k T) = sflip_ty k (tysw a b T)) ∧
    (∀ s k, stysw a b (sflip k s) = sflip k (stysw a b s)).
  Proof.
    apply ty_sty_mut_ind; intros; simpl; f_equal; auto;
      repeat case_decide; done.
  Qed.

  Lemma dual_sw s : stysw a b (dual s) = dual (stysw a b s).
  Proof.
    induction s; simpl; f_equal; auto.
    by rewrite (proj2 sflip_sw_mut), IHs.
  Qed.

  Lemma sinst_sw_mut :
    (∀ T σ, tysw a b (sinst_ty σ T) = sinst_ty (stysw a b ∘ σ) (tysw a b T)) ∧
    (∀ s σ, stysw a b (sinst σ s) = sinst (stysw a b ∘ σ) (stysw a b s)).
  Proof.
    apply ty_sty_mut_ind; intros; simpl; f_equal; auto.
    - rewrite H. apply sinst_ext. intros [|i]; simpl; [done|].
      unfold compose. by rewrite (proj2 sren_sw_mut).
    - by rewrite dual_sw.
  Qed.

  Lemma unroll_sw s : stysw a b (unroll s) = unroll (stysw a b s).
  Proof.
    unfold unroll. rewrite (proj2 sinst_sw_mut). apply sinst_ext.
    by intros [|i].
  Qed.

  Lemma mu_depth_sw s : mu_depth (stysw a b s) = mu_depth s.
  Proof. induction s; simpl; auto. Qed.

  Lemma unfoldN_sw k : ∀ s, stysw a b (unfoldN k s) = unfoldN k (stysw a b s).
  Proof.
    induction k as [|k IH]; intros s; [done|].
    destruct s; simpl; try done. by rewrite IH, unroll_sw.
  Qed.

  Lemma unfoldS_sw s : stysw a b (unfoldS s) = unfoldS (stysw a b s).
  Proof. unfold unfoldS. by rewrite mu_depth_sw, unfoldN_sw. Qed.

  (** Type equivalence and duality are invariant. *)
  Lemma eqT_sw (ρ ρ' : sty → sty → Prop) T : ∀ U,
    (∀ s r, ρ s r → ρ' (stysw a b s) (stysw a b r)) →
    eqT ρ T U → eqT ρ' (tysw a b T) (tysw a b U).
  Proof.
    induction T; intros [] Hρ; simpl; try done; try naive_solver.
  Qed.

  Lemma aeq_sw n : ∀ s r, aeq n s r → aeq n (stysw a b s) (stysw a b r).
  Proof.
    induction n as [|n IH]; intros s r; [done|]. simpl. unfold eq_step.
    rewrite <-!unfoldS_sw.
    destruct (unfoldS s), (unfoldS r); simpl; try done;
      try (intros (-> & ? & ?); split_and!; [done|by eapply eqT_sw|auto]);
      try (intros H; by inversion H).
  Qed.

  Lemma adual_sw n : ∀ s r, adual n s r → adual n (stysw a b s) (stysw a b r).
  Proof.
    induction n as [|n IH]; intros s r; [done|]. simpl. unfold dual_step.
    rewrite <-!unfoldS_sw.
    destruct (unfoldS s) eqn:E1, (unfoldS r) eqn:E2; simpl; try done;
      try (intros (-> & ? & ?); split_and!;
           [done|eapply eqT_sw; [apply aeq_sw|done]|auto]);
      try (intros H; by inversion H);
      try (intros H; simplify_eq; simpl;
           by rewrite ?(proj2 sflip_sw_mut), ?dual_sw).
  Qed.

  Lemma seq_sw s r : seq s r → seq (stysw a b s) (stysw a b r).
  Proof. intros H n. by apply aeq_sw. Qed.

  Lemma sdual_sw s r : sdual s r → sdual (stysw a b s) (stysw a b r).
  Proof. intros H n. by apply adual_sw. Qed.

  Lemma teq_sw T U : teq T U → teq (tysw a b T) (tysw a b U).
  Proof. apply eqT_sw. apply seq_sw. Qed.

  (** Point instantiation commutes. *)
  Lemma pn_inst_sw σ p :
    ptsw a b (pn_inst σ p) = pn_inst (ptsw a b ∘ σ) (pnsw a b p).
  Proof. induction p; simpl; try done. by rewrite ptsw_slot, ptsw_shift, IHp. Qed.

  Lemma pt_inst_sw σ x :
    ptsw a b (pt_inst σ x) = pt_inst (ptsw a b ∘ σ) (ptsw a b x).
  Proof. unfold pt_inst. by rewrite ptsw_shift, pn_inst_sw. Qed.

  Lemma pn_inst_ext σ τ p : (∀ i, σ i = τ i) → pn_inst σ p = pn_inst τ p.
  Proof. intros H. induction p; simpl; by rewrite ?IHp. Qed.

  Lemma pt_inst_ext σ τ x : (∀ i, σ i = τ i) → pt_inst σ x = pt_inst τ x.
  Proof. intros H. unfold pt_inst. by rewrite (pn_inst_ext σ τ). Qed.

  Lemma pup_ext m σ τ : (∀ i, σ i = τ i) → ∀ i, pup m σ i = pup m τ i.
  Proof. intros H i. unfold pup. case_decide; [done|]. by rewrite H. Qed.

  Lemma pinst_ty_ext T : ∀ σ τ, (∀ i, σ i = τ i) → pinst_ty σ T = pinst_ty τ T.
  Proof.
    induction T; intros σ τ H; simpl; try done; f_equal; auto using pup_ext.
    - destruct ub; simpl; [by rewrite (pt_inst_ext σ τ)|done].
    - destruct lb; simpl; [by rewrite (pt_inst_ext σ τ)|done].
    - by apply pt_inst_ext.
  Qed.

  Lemma pup_sw m σ i : ptsw a b (pup m σ i) = pup m (ptsw a b ∘ σ) i.
  Proof.
    unfold pup. case_decide; [done|]. rewrite pt_inst_sw. unfold compose.
    by apply pt_inst_ext.
  Qed.

  Lemma pinst_sw T : ∀ σ, tysw a b (pinst_ty σ T) = pinst_ty (ptsw a b ∘ σ) (tysw a b T).
  Proof.
    induction T; intros σ; simpl; try done; f_equal; auto.
    - destruct ub; simpl; [by rewrite pt_inst_sw|done].
    - destruct lb; simpl; [by rewrite pt_inst_sw|done].
    - rewrite IHT. apply pinst_ty_ext. intros i. apply pup_sw.
    - by rewrite pt_inst_sw.
  Qed.

  Lemma plist_sw xs i : ptsw a b (plist xs i) = plist (ptsw a b <$> xs) i.
  Proof.
    unfold plist. rewrite list_lookup_fmap, length_fmap.
    by destruct (xs !! i).
  Qed.

  Lemma ty_inst_sw xs T : tysw a b (ty_inst xs T) = ty_inst (ptsw a b <$> xs) (tysw a b T).
  Proof.
    unfold ty_inst. rewrite pinst_sw. apply pinst_ty_ext. intros i. apply plist_sw.
  Qed.

  Lemma slots_sw x m : ptsw a b <$> slots x m = slots (ptsw a b x) m.
  Proof. unfold slots. rewrite <-list_fmap_compose. by apply list_fmap_ext. Qed.

  Lemma payload_at_sw m T x :
    tysw a b (payload_at m T x) = payload_at m (tysw a b T) (ptsw a b x).
  Proof. unfold payload_at. by rewrite ty_inst_sw, slots_sw. Qed.

  Lemma heads_sw T : heads (tysw a b T) = set_map (ptsw a b) (heads T).
  Proof.
    induction T; simpl; rewrite ?IHT1, ?IHT2; try set_solver.
    all: destruct lb; simpl; set_solver.
  Qed.

  Lemma roots_sw_mut :
    (∀ T, ty_roots (tysw a b T) = set_map (pnsw a b) (ty_roots T)) ∧
    (∀ s, sty_roots (stysw a b s) = set_map (pnsw a b) (sty_roots s)).
  Proof.
    apply ty_sty_mut_ind; intros; simpl; rewrite ?H, ?H0, ?pt_root_sw;
      try set_solver.
    all: destruct ub, lb; simpl; rewrite ?pt_root_sw; set_solver.
  Qed.
End points.

(** ** Worlds up to equivalence, and the transposition of a world *)

Definition wsame (W1 W2 : world) : Prop :=
  w_names W1 = w_names W2 ∧
  (∀ x y, w_eq W1 x y ↔ w_eq W2 x y) ∧ (∀ x y, w_lt W1 x y ↔ w_lt W2 x y).

Lemma wsame_refl W : wsame W W.
Proof. done. Qed.

Lemma wsame_sym W1 W2 : wsame W1 W2 → wsame W2 W1.
Proof. intros (? & He & Hl). split_and!; [done|..]; intros; [by rewrite He|by rewrite Hl]. Qed.

Lemma wsame_trans W1 W2 W3 : wsame W1 W2 → wsame W2 W3 → wsame W1 W3.
Proof.
  intros (H1 & He1 & Hl1) (H2 & He2 & Hl2). split_and!; [congruence|..];
    intros; [by rewrite He1|by rewrite Hl1].
Qed.

Lemma wsame_wf W1 W2 : wsame W1 W2 → world_wf W1 → world_wf W2.
Proof.
  intros (Hn & He & Hl) HW. split.
  - intros x. apply He, HW.
  - intros x y. rewrite <-!He. apply HW.
  - intros x y z. rewrite <-!He. apply HW.
  - intros x y. rewrite <-!He. apply HW.
  - intros x y i. rewrite <-!He. apply HW.
  - intros x y z. rewrite <-!Hl. apply HW.
  - intros x x' y y'. rewrite <-!He, <-!Hl. apply HW.
  - intros x. apply Hl, HW.
  - intros x y. rewrite <-He, <-Hn. apply HW.
  - intros x y. rewrite <-Hl, <-Hn. apply HW.
  - intros p. rewrite <-Hn. apply HW.
Qed.

Lemma wsame_strict W1 W2 : wsame W1 W2 → strict W1 → strict W2.
Proof.
  intros HS [HW Hi]. split; [by eapply wsame_wf|].
  intros x. destruct HS as (_ & _ & Hl). rewrite <-Hl. apply Hi.
Qed.

Lemma wext_wsame W1 W1' W2 W2' :
  wsame W1 W1' → wsame W2 W2' → wext W1 W2 → wext W1' W2'.
Proof.
  intros (Hn1 & He1 & Hl1) HS2 (Hn & He & Hl & Hs).
  split_and!; [|..|by eapply wsame_strict].
  - destruct HS2 as (Hn2 & _). by rewrite <-Hn1, <-Hn2.
  - intros x y Hxy. apply HS2, He, He1, Hxy.
  - intros x y Hxy. apply HS2, Hl, Hl1, Hxy.
Qed.

Lemma wext_fresh_wsame W1 W1' N W2 W2' :
  wsame W1 W1' → wsame W2 W2' → wext_fresh W1 N W2 → wext_fresh W1' N W2'.
Proof.
  intros HS1 HS2 (Hx & HN & Hn & Hold). split_and!.
  - by eapply wext_wsame.
  - by destruct HS1 as (<- & _).
  - destruct HS1 as (<- & _), HS2 as (<- & _). done.
  - intros x y Hx' Hy'. destruct (Hold x y Hx' Hy') as [H1 H2].
    destruct HS1 as (_ & He1 & Hl1), HS2 as (_ & He2 & Hl2).
    split; intros H; [apply He1, H1, He2, H|apply Hl1, H2, Hl2, H].
Qed.

Definition wsw (a b : nat) (W : world) : world :=
  World (set_map (pnsw a b) (w_names W))
    (λ x y, w_eq W (ptsw a b x) (ptsw a b y))
    (λ x y, w_lt W (ptsw a b x) (ptsw a b y)).

Section wsw.
  Context (a b : nat).

  Lemma elem_of_names_sw p (N : gset pname) :
    pnsw a b p ∈ (set_map (pnsw a b) N : gset pname) ↔ p ∈ N.
  Proof.
    rewrite elem_of_map. split; [|eauto].
    intros (q & Heq & Hq). apply (pnsw_inj a b) in Heq. by subst.
  Qed.

  Lemma elem_of_names_sw' p (N : gset pname) :
    p ∈ (set_map (pnsw a b) N : gset pname) ↔ pnsw a b p ∈ N.
  Proof.
    rewrite <-(elem_of_names_sw (pnsw a b p)), pnsw_involutive. done.
  Qed.

  Lemma wsw_eq W x y :
    w_eq (wsw a b W) (ptsw a b x) (ptsw a b y) ↔ w_eq W x y.
  Proof. simpl. by rewrite !ptsw_involutive. Qed.

  Lemma wsw_lt W x y :
    w_lt (wsw a b W) (ptsw a b x) (ptsw a b y) ↔ w_lt W x y.
  Proof. simpl. by rewrite !ptsw_involutive. Qed.

  Lemma wsw_wf W : world_wf W → world_wf (wsw a b W).
  Proof.
    intros HW. split; simpl; intros *.
    - apply HW.
    - apply HW.
    - apply HW.
    - rewrite !ptsw_shift. apply HW.
    - rewrite !ptsw_slot. apply HW.
    - apply HW.
    - apply HW.
    - rewrite ptsw_shift. apply HW.
    - intros H. apply (wf_eq_supp _ HW) in H as [H|[Hx Hy]].
      + left. by apply (ptsw_inj a b).
      + right. rewrite !elem_of_names_sw', <-!pt_root_sw. done.
    - intros H. apply (wf_lt_supp _ HW) in H as [[Hn Ho]|[Hx Hy]].
      + left. split; [|done]. by apply (pnsw_inj a b).
      + right. rewrite !elem_of_names_sw', <-!pt_root_sw. done.
    - intros Hp. apply elem_of_names_sw' in Hp.
      destruct (wf_names_const _ HW _ Hp) as [c Hc].
      exists (nswap a b c). rewrite <-(pnsw_involutive a b p), Hc. done.
  Qed.

  Lemma wsw_strict W : strict W → strict (wsw a b W).
  Proof. intros [HW Hi]. split; [by apply wsw_wf|]. intros x. apply Hi. Qed.

  Lemma wsw_wsw W : wsame (wsw a b (wsw a b W)) W.
  Proof.
    split_and!; simpl.
    - apply set_eq. intros p. rewrite !elem_of_names_sw', pnsw_involutive.
      done.
    - intros. by rewrite !ptsw_involutive.
    - intros. by rewrite !ptsw_involutive.
  Qed.

  Lemma wsw_wsame W1 W2 : wsame W1 W2 → wsame (wsw a b W1) (wsw a b W2).
  Proof.
    intros (Hn & He & Hl). split_and!; simpl; [by rewrite Hn|..]; intros; auto.
  Qed.

  Lemma wext_wsw W W' : wext W W' → wext (wsw a b W) (wsw a b W').
  Proof.
    intros (Hn & He & Hl & Hs). split_and!; simpl; auto.
    - intros p. simpl. rewrite !elem_of_names_sw'. set_solver.
    - by apply wsw_strict.
  Qed.

  Lemma wext_fresh_wsw W N W' :
    wext_fresh W N W' →
    wext_fresh (wsw a b W) (set_map (pnsw a b) N) (wsw a b W').
  Proof.
    intros (Hx & HN & Hn & Hold). split_and!.
    - by apply wext_wsw.
    - apply elem_of_disjoint. intros p H1 H2. simpl in H2.
      apply elem_of_names_sw' in H1, H2. set_solver.
    - simpl. apply set_eq. intros p.
      rewrite elem_of_union, !elem_of_names_sw', Hn. set_solver.
    - intros x y Hx' Hy'. simpl.
      rewrite elem_of_names_sw', <-pt_root_sw in Hx', Hy'.
      by apply Hold.
  Qed.

  Lemma lb_below_sw W lb H :
    lb_below W lb H →
    lb_below (wsw a b W) (ptsw a b <$> lb) (set_map (ptsw a b) H).
  Proof.
    destruct lb as [x|]; simpl.
    - intros Hb y Hy. apply elem_of_map in Hy as (y0 & -> & Hy0).
      unfold w_le. simpl. rewrite !ptsw_involutive. by apply Hb.
    - intros ->. set_solver.
  Qed.

  Lemma ub_below_sw W ub F :
    ub_below W ub F →
    ub_below (wsw a b W) (ptsw a b <$> ub) (set_map (ptsw a b) F).
  Proof.
    destruct ub as [x|]; simpl; [|done].
    intros Hb y Hy. apply elem_of_map in Hy as (y0 & -> & Hy0).
    rewrite !ptsw_involutive. by apply Hb.
  Qed.
End wsw.

(** Points and frames moved by a transposition. *)
Lemma lb_below_wsame W1 W2 lb H :
  wsame W1 W2 → lb_below W1 lb H → lb_below W2 lb H.
Proof.
  intros (_ & He & Hl). destruct lb; simpl; [|done].
  intros Hb y Hy. destruct (Hb y Hy); [left; by apply He|right; by apply Hl].
Qed.

Lemma ub_below_wsame W1 W2 ub F :
  wsame W1 W2 → ub_below W1 ub F → ub_below W2 ub F.
Proof.
  intros (_ & _ & Hl). destruct ub; simpl; [|done]. intros Hb y Hy. apply Hl. auto.
Qed.


(** ** Environments *)

Definition esw (a b : nat) (e : sty * point) : sty * point :=
  (stysw a b e.1, ptsw a b e.2).

Definition endsw (a b : nat) (o : ends) : ends :=
  match o with
  | One e => One (esw a b e)
  | Both e1 e2 => Both (esw a b e1) (esw a b e2)
  end.

Definition tenvsw (a b : nat) (Θ : tenv) : tenv := endsw a b <$> Θ.
Definition senvsw (a b : nat) (Σ : senv) : senv := esw a b <$> Σ.

Section envs.
  Context (a b : nat).

  Lemma esw_involutive e : esw a b (esw a b e) = e.
  Proof. destruct e. unfold esw. simpl. by rewrite stysw_involutive, ptsw_involutive. Qed.

  Lemma endsw_involutive o : endsw a b (endsw a b o) = o.
  Proof. destruct o; simpl; by rewrite ?esw_involutive. Qed.

  Lemma esw_inj e e' : esw a b e = esw a b e' → e = e'.
  Proof. intros H. by rewrite <-(esw_involutive e), H, esw_involutive. Qed.

  Lemma endsw_inj o o' : endsw a b o = endsw a b o' → o = o'.
  Proof. intros H. by rewrite <-(endsw_involutive o), H, endsw_involutive. Qed.

  Lemma lookup_tenvsw Θ c : tenvsw a b Θ !! c = endsw a b <$> Θ !! c.
  Proof. apply lookup_fmap. Qed.

  Lemma lookup_senvsw Σ c : senvsw a b Σ !! c = esw a b <$> Σ !! c.
  Proof. apply lookup_fmap. Qed.

  Lemma tenvsw_involutive Θ : tenvsw a b (tenvsw a b Θ) = Θ.
  Proof.
    apply map_eq. intros c. rewrite !lookup_tenvsw.
    destruct (Θ !! c); simpl; by rewrite ?endsw_involutive.
  Qed.

  Lemma senvsw_involutive Σ : senvsw a b (senvsw a b Σ) = Σ.
  Proof.
    apply map_eq. intros c. rewrite !lookup_senvsw.
    destruct (Σ !! c); simpl; by rewrite ?esw_involutive.
  Qed.

  Lemma dom_tenvsw Θ : dom (tenvsw a b Θ) = dom Θ.
  Proof. apply dom_fmap_L. Qed.

  Lemma dom_senvsw Σ : dom (senvsw a b Σ) = dom Σ.
  Proof. apply dom_fmap_L. Qed.

  Lemma tenvsw_empty : tenvsw a b ∅ = ∅.
  Proof. apply fmap_empty. Qed.

  Lemma senvsw_empty : senvsw a b ∅ = ∅.
  Proof. apply fmap_empty. Qed.

  Lemma tenvsw_insert Θ c o :
    tenvsw a b (<[c := o]> Θ) = <[c := endsw a b o]> (tenvsw a b Θ).
  Proof. apply fmap_insert. Qed.

  Lemma senvsw_insert Σ c e :
    senvsw a b (<[c := e]> Σ) = <[c := esw a b e]> (senvsw a b Σ).
  Proof. apply fmap_insert. Qed.

  Lemma tenvsw_singleton c o : tenvsw a b {[c := o]} = {[c := endsw a b o]}.
  Proof. apply map_fmap_singleton. Qed.

  Lemma tenvsw_union Θ1 Θ2 : tenvsw a b (Θ1 ∪ Θ2) = tenvsw a b Θ1 ∪ tenvsw a b Θ2.
  Proof. apply map_fmap_union. Qed.

  Lemma senvsw_union Σ1 Σ2 : senvsw a b (Σ1 ∪ Σ2) = senvsw a b Σ1 ∪ senvsw a b Σ2.
  Proof. apply map_fmap_union. Qed.

  Lemma senvsw_difference Σ1 Σ2 :
    senvsw a b (Σ1 ∖ Σ2) = senvsw a b Σ1 ∖ senvsw a b Σ2.
  Proof.
    apply map_eq. intros c.
    rewrite lookup_difference, !lookup_senvsw, lookup_difference.
    by destruct (Σ1 !! c), (Σ2 !! c).
  Qed.

  Lemma senvsw_disjoint Σ1 Σ2 : Σ1 ##ₘ Σ2 → senvsw a b Σ1 ##ₘ senvsw a b Σ2.
  Proof.
    intros Hd c. rewrite !lookup_senvsw. specialize (Hd c).
    by destruct (Σ1 !! c), (Σ2 !! c).
  Qed.

  Lemma tenvsw_disjoint Θ1 Θ2 : Θ1 ##ₘ Θ2 → tenvsw a b Θ1 ##ₘ tenvsw a b Θ2.
  Proof.
    intros Hd c. rewrite !lookup_tenvsw. specialize (Hd c).
    by destruct (Θ1 !! c), (Θ2 !! c).
  Qed.

  Lemma tenvsw_of Σ : tenvsw a b (tenv_of Σ) = tenv_of (senvsw a b Σ).
  Proof.
    apply map_eq. intros c. unfold tenv_of.
    rewrite lookup_tenvsw, !lookup_fmap, lookup_senvsw. by destruct (Σ !! c).
  Qed.

  Lemma tenv_ones_sw Θ : tenv_ones (tenvsw a b Θ) = senvsw a b (tenv_ones Θ).
  Proof.
    apply map_eq. intros c. unfold tenv_ones.
    rewrite lookup_omap, lookup_tenvsw, lookup_senvsw, lookup_omap.
    by destruct (Θ !! c) as [[]|].
  Qed.

  Lemma tenv_entry_sw Θ k :
    tenv_entry (tenvsw a b Θ) k = esw a b <$> tenv_entry Θ k.
  Proof.
    destruct k as [c s]. unfold tenv_entry. simpl.
    rewrite lookup_tenvsw. by destruct (Θ !! c) as [[]|], s.
  Qed.

  Lemma entry_head_sw k e : entry_head k (esw a b e) = ptsw a b (entry_head k e).
  Proof. done. Qed.

  Lemma elem_of_tenv_heads Θ x :
    x ∈ tenv_heads Θ ↔ ∃ c o, Θ !! c = Some o ∧ x ∈ ends_heads c o.
  Proof.
    unfold tenv_heads. revert x.
    apply (map_fold_weak_ind (λ r m, ∀ x, x ∈ r ↔ ∃ c o, m !! c = Some o ∧
                                   x ∈ ends_heads c o)).
    - intros x. split; [set_solver|]. intros (c & o & H & _).
      by rewrite lookup_empty in H.
    - intros i o m r Hi IH x. rewrite elem_of_union, IH. split.
      + intros [Hx|(c & o' & Hc & Hx)].
        * exists i, o. by rewrite lookup_insert_eq.
        * exists c, o'. rewrite lookup_insert_ne; [done|]. intros ->. congruence.
      + intros (c & o' & Hc & Hx). destruct (decide (c = i)) as [->|Hne].
        * rewrite lookup_insert_eq in Hc. injection Hc as ->. by left.
        * right. rewrite lookup_insert_ne in Hc by done. eauto.
  Qed.

  Lemma ends_heads_sw c o :
    ends_heads c (endsw a b o) = set_map (ptsw a b) (ends_heads c o).
  Proof. destruct o; simpl; set_solver. Qed.

  Lemma tenv_heads_sw Θ :
    tenv_heads (tenvsw a b Θ) = set_map (ptsw a b) (tenv_heads Θ).
  Proof.
    apply set_eq. intros x. rewrite elem_of_map, elem_of_tenv_heads. split.
    - intros (c & o & Hc & Hx). rewrite lookup_tenvsw in Hc.
      destruct (Θ !! c) as [o0|] eqn:Ho; [|done]. injection Hc as <-.
      rewrite ends_heads_sw in Hx.
      apply elem_of_map in Hx as (x0 & -> & Hx0). exists x0. split; [done|].
      apply elem_of_tenv_heads. eauto.
    - intros (x0 & -> & Hx0). apply elem_of_tenv_heads in Hx0 as (c & o & Hc & Hx).
      exists c, (endsw a b o). split.
      + by rewrite lookup_tenvsw, Hc.
      + rewrite ends_heads_sw. by apply elem_of_map_2.
  Qed.

  Lemma elem_of_tenv_roots Θ p :
    p ∈ tenv_roots Θ ↔ ∃ c o, Θ !! c = Some o ∧ p ∈ ends_roots o.
  Proof.
    unfold tenv_roots. revert p.
    apply (map_fold_weak_ind (λ r m, ∀ p, p ∈ r ↔ ∃ c o, m !! c = Some o ∧
                                   p ∈ ends_roots o)).
    - intros p. split; [set_solver|]. intros (c & o & H & _).
      by rewrite lookup_empty in H.
    - intros i o m r Hi IH p. rewrite elem_of_union, IH. split.
      + intros [Hx|(c & o' & Hc & Hx)].
        * exists i, o. by rewrite lookup_insert_eq.
        * exists c, o'. rewrite lookup_insert_ne; [done|]. intros ->. congruence.
      + intros (c & o' & Hc & Hx). destruct (decide (c = i)) as [->|Hne].
        * rewrite lookup_insert_eq in Hc. injection Hc as ->. by left.
        * right. rewrite lookup_insert_ne in Hc by done. eauto.
  Qed.

  Lemma entry_roots_sw e : entry_roots (esw a b e) = set_map (pnsw a b) (entry_roots e).
  Proof.
    destruct e as [s x]. unfold entry_roots, esw. simpl.
    by rewrite (proj2 (roots_sw_mut a b)), pt_root_sw, set_map_union_L,
      set_map_singleton_L.
  Qed.

  Lemma ends_roots_sw o : ends_roots (endsw a b o) = set_map (pnsw a b) (ends_roots o).
  Proof.
    destruct o; simpl; rewrite ?entry_roots_sw; [done|]. by rewrite set_map_union_L.
  Qed.

  Lemma tenv_roots_sw Θ : tenv_roots (tenvsw a b Θ) = set_map (pnsw a b) (tenv_roots Θ).
  Proof.
    apply set_eq. intros x. rewrite elem_of_map, elem_of_tenv_roots. split.
    - intros (c & o & Hc & Hx). rewrite lookup_tenvsw in Hc.
      destruct (Θ !! c) as [o0|] eqn:Ho; [|done]. injection Hc as <-.
      rewrite ends_roots_sw in Hx.
      apply elem_of_map in Hx as (x0 & -> & Hx0). exists x0. split; [done|].
      apply elem_of_tenv_roots. eauto.
    - intros (x0 & -> & Hx0). apply elem_of_tenv_roots in Hx0 as (c & o & Hc & Hx).
      exists c, (endsw a b o). split.
      + by rewrite lookup_tenvsw, Hc.
      + rewrite ends_roots_sw. by apply elem_of_map_2.
  Qed.

  Lemma senv_roots_sw Σ : senv_roots (senvsw a b Σ) = set_map (pnsw a b) (senv_roots Σ).
  Proof. unfold senv_roots. by rewrite <-tenvsw_of, tenv_roots_sw. Qed.

  (** The relations between environments. *)

  Lemma tenv_join_sw Θ Θ1 Θ2 :
    tenv_join Θ Θ1 Θ2 → tenv_join (tenvsw a b Θ) (tenvsw a b Θ1) (tenvsw a b Θ2).
  Proof.
    intros H c. rewrite !lookup_tenvsw. specialize (H c).
    inversion H; simpl; constructor.
  Qed.

  Lemma tenv_comp_sw W Θ Θ1 Θ2 :
    tenv_comp (w_eq W) Θ Θ1 Θ2 →
    tenv_comp (w_eq (wsw a b W)) (tenvsw a b Θ) (tenvsw a b Θ1) (tenvsw a b Θ2).
  Proof.
    intros [Hj Hd]. split; [by apply tenv_join_sw|].
    intros c e1 e2 H1 H2. rewrite lookup_tenvsw in H1, H2.
    destruct (Θ1 !! c) as [[]|] eqn:E1; try done.
    destruct (Θ2 !! c) as [[]|] eqn:E2; try done.
    injection H1 as <-. injection H2 as <-.
    destruct (Hd _ _ _ E1 E2) as [Hx Hs]. simpl. rewrite !ptsw_involutive.
    split; [done|]. by apply sdual_sw.
  Qed.

  Lemma tenv_ext_sw Θ1 c e Θ :
    tenv_ext Θ1 c e Θ → tenv_ext (tenvsw a b Θ1) c (esw a b e) (tenvsw a b Θ).
  Proof.
    intros [[H1 ->]|(e' & H1 & [->| ->])].
    - left. rewrite lookup_tenvsw, H1. split; [done|]. by rewrite tenvsw_insert.
    - right. exists (esw a b e'). rewrite lookup_tenvsw, H1.
      split; [done|]. left. by rewrite tenvsw_insert.
    - right. exists (esw a b e'). rewrite lookup_tenvsw, H1.
      split; [done|]. right. by rewrite tenvsw_insert.
  Qed.

  Lemma tenv_hd_sw Θ c u k Θ1 :
    tenv_hd Θ c u k Θ1 →
    tenv_hd (tenvsw a b Θ) c (stysw a b u) (ptsw a b k) (tenvsw a b Θ1).
  Proof.
    intros (s & Hext & Hu). exists (stysw a b s). split.
    - apply (tenv_ext_sw _ _ (s, k)). done.
    - by rewrite <-unfoldS_sw, Hu.
  Qed.

  Lemma tenv_dual_sw W Θ :
    tenv_dual (w_eq W) Θ → tenv_dual (w_eq (wsw a b W)) (tenvsw a b Θ).
  Proof.
    intros H c e1 e2 He. rewrite lookup_tenvsw in He.
    destruct (Θ !! c) as [[]|] eqn:E; try done. injection He as <- <-.
    destruct (H _ _ _ E) as [Hx Hs]. simpl. rewrite !ptsw_involutive.
    split; [done|]. by apply sdual_sw.
  Qed.

  Lemma senv_hd_sw Σ c u k Σ1 :
    senv_hd Σ c u k Σ1 →
    senv_hd (senvsw a b Σ) c (stysw a b u) (ptsw a b k) (senvsw a b Σ1).
  Proof.
    intros (s & -> & Hu). exists (stysw a b s).
    rewrite senvsw_insert. split; [done|]. by rewrite <-unfoldS_sw, Hu.
  Qed.

  Lemma senv_dual_on_sw W Σ1 Σ2 :
    senv_dual_on (w_eq W) Σ1 Σ2 →
    senv_dual_on (w_eq (wsw a b W)) (senvsw a b Σ1) (senvsw a b Σ2).
  Proof.
    intros H c e1 e2 H1 H2. rewrite lookup_senvsw in H1, H2.
    destruct (Σ1 !! c) eqn:E1, (Σ2 !! c) eqn:E2; try done.
    injection H1 as <-. injection H2 as <-.
    destruct (H _ _ _ E1 E2) as [Hx Hs]. simpl. rewrite !ptsw_involutive.
    split; [done|]. by apply sdual_sw.
  Qed.

  Lemma recv_back_sw Σr Θ2 :
    recv_back (senvsw a b Σr) (tenvsw a b Θ2) = recv_back Σr Θ2.
  Proof.
    unfold recv_back. by rewrite tenv_ones_sw, dom_tenvsw, !dom_senvsw.
  Qed.

  Lemma recv_env_sw Σr Θ2 :
    recv_env (senvsw a b Σr) (tenvsw a b Θ2) = senvsw a b (recv_env Σr Θ2).
  Proof.
    unfold recv_env. by rewrite tenv_ones_sw, senvsw_union, !senvsw_difference.
  Qed.

  Lemma recv_ok_sw W Σr Θ2 :
    recv_ok W Σr Θ2 → recv_ok (wsw a b W) (senvsw a b Σr) (tenvsw a b Θ2).
  Proof.
    intros (Hd & Ht & Hb). split_and!.
    - rewrite tenv_ones_sw. by apply senv_dual_on_sw.
    - by apply tenv_dual_sw.
    - by rewrite tenv_ones_sw, dom_tenvsw, !dom_senvsw.
  Qed.

  Lemma send_split_sw W Σe Θe :
    send_split W Σe Θe → send_split (wsw a b W) (senvsw a b Σe) (tenvsw a b Θe).
  Proof.
    intros [Hsub H]. split.
    - by rewrite dom_senvsw, dom_tenvsw.
    - intros r o Hr. rewrite lookup_tenvsw in Hr.
      destruct (Θe !! r) as [o0|] eqn:E; [|done]. injection Hr as <-.
      specialize (H _ _ E). destruct o0 as [e'|e1 e2]; simpl.
      + destruct H as (e & He & Hx & Hs). exists (esw a b e).
        rewrite lookup_senvsw, He. simpl. rewrite !ptsw_involutive.
        split_and!; [done|done|]. by apply sdual_sw.
      + destruct H as (He & Hx & Hs). rewrite lookup_senvsw, He. simpl.
        rewrite !ptsw_involutive. split_and!; [done|done|]. by apply sdual_sw.
  Qed.
End envs.

(** ** Readiness, frames, constants *)

Section ready.
  Context (a b : nat).

  Lemma selects_sw Θ σ k : selects (tenvsw a b Θ) σ k ↔ selects Θ σ k.
  Proof.
    destruct σ as [c w|c w|c|cd]; simpl; rewrite ?tenv_entry_sw.
    - split; intros [Hk (e & m & T & s & He & Hu)]; split; [done| |done|].
      + destruct (tenv_entry Θ k) as [e0|] eqn:E; [|done]. injection He as <-.
        simpl in Hu. rewrite <-unfoldS_sw in Hu.
        destruct (unfoldS e0.1) eqn:Eu; try done.
        injection Hu as <- <- <-. eexists _, _, _, _. split; [done|exact Eu].
      + exists (esw a b e), m, (tysw a b T), (stysw a b s). rewrite He.
        split; [done|]. simpl. by rewrite <-unfoldS_sw, Hu.
    - split; intros [Hk (e & m & T & s & He & Hu)]; split; [done| |done|].
      + destruct (tenv_entry Θ k) as [e0|] eqn:E; [|done]. injection He as <-.
        simpl in Hu. rewrite <-unfoldS_sw in Hu.
        destruct (unfoldS e0.1) eqn:Eu; try done.
        injection Hu as <- <- <-. eexists _, _, _, _. split; [done|exact Eu].
      + exists (esw a b e), m, (tysw a b T), (stysw a b s). rewrite He.
        split; [done|]. simpl. by rewrite <-unfoldS_sw, Hu.
    - assert (∀ s, unfoldS (stysw a b s) = SEnd ↔ unfoldS s = SEnd) as HE.
      { intros s. rewrite <-unfoldS_sw. split; [|by intros ->].
        by destruct (unfoldS s). }
      split; intros [Hk (e & He & Hu & H2)]; split; try done.
      + destruct (tenv_entry Θ k) as [e0|] eqn:E; [|done]. injection He as <-.
        exists e0. split_and!; [done|by apply HE|].
        intros Ht e' He'. specialize (H2 Ht (esw a b e')).
        rewrite He' in H2. simpl in H2. rewrite HE in H2. auto.
      + exists (esw a b e). rewrite He. split_and!; [done|by apply HE|].
        intros Ht e' He'. destruct (tenv_entry Θ (c, false)) as [e0|] eqn:E;
          [|done]. injection He' as <-. simpl. rewrite HE. auto.
    - split; intros [Hk Hs]; split; try done.
      + destruct (tenv_entry Θ k); [done|by destruct Hs].
      + by destruct (tenv_entry Θ k).
  Qed.

  Lemma offered_t_sw Θ t k : offered_t (tenvsw a b Θ) t k ↔ offered_t Θ t k.
  Proof.
    unfold offered_t. split; intros (σ & t' & Hs & Hk); exists σ, t';
      (split; [done|]); [exact (proj1 (selects_sw _ _ _) Hk)|exact (proj2 (selects_sw _ _ _) Hk)].
  Qed.

  Lemma offered_p_sw Σ p k : offered_p (senvsw a b Σ) p k ↔ offered_p Σ p k.
  Proof.
    unfold offered_p. rewrite <-tenvsw_of. split; intros (σ & p' & Hs & Hk);
      exists σ, p'; (split; [done|]); [exact (proj1 (selects_sw _ _ _) Hk)|exact (proj2 (selects_sw _ _ _) Hk)].
  Qed.

  Lemma above_offered_sw W Θ off :
    above_offered W Θ off → above_offered (wsw a b W) (tenvsw a b Θ) off.
  Proof.
    intros H k e He Hk. rewrite tenv_entry_sw in He.
    destruct (tenv_entry Θ k) as [e0|] eqn:E; [|done]. injection He as <-.
    destruct (H k e0 E Hk) as (k' & e' & Ho & He' & Hlt).
    exists k', (esw a b e'). rewrite tenv_entry_sw, He'. split_and!; [done|done|].
    simpl. unfold entry_head in *. simpl. by rewrite !ptsw_involutive.
  Qed.

  Lemma ready_t_sw W Θ t : ready_t W Θ t → ready_t (wsw a b W) (tenvsw a b Θ) t.
  Proof.
    intros H Hs. destruct (H Hs) as [H1 H2]. split.
    - intros Hn. apply H1. intros k Hk. apply (Hn k).
      exact (proj2 (offered_t_sw _ _ _) Hk).
    - eapply above_offered_sw in H2. intros k e He Hk.
      destruct (H2 k e He) as (k' & e' & Ho & ? & ?).
      { intros Ho. apply Hk. exact (proj2 (offered_t_sw _ _ _) Ho). }
      exists k', e'. split_and!; [exact (proj2 (offered_t_sw _ _ _) Ho)|done|done].
  Qed.

  Lemma ready_p_sw W Σ p : ready_p W Σ p → ready_p (wsw a b W) (senvsw a b Σ) p.
  Proof.
    intros H Hs. destruct (H Hs) as [H1 H2]. split.
    - intros Hn. apply H1. intros k Hk. apply (Hn k).
      exact (proj2 (offered_p_sw _ _ _) Hk).
    - rewrite <-tenvsw_of. eapply above_offered_sw in H2. intros k e He Hk.
      destruct (H2 k e He) as (k' & e' & Ho & ? & ?).
      { intros Ho. apply Hk. exact (proj2 (offered_p_sw _ _ _) Ho). }
      exists k', e'. split_and!; [|done|done].
      exact (proj2 (offered_p_sw _ _ _) Ho).
  Qed.

  Lemma frame_t_sw W Θ t F :
    frame_t W Θ t F → frame_t (wsw a b W) (tenvsw a b Θ) t (set_map (ptsw a b) F).
  Proof.
    intros H Hs k e Ho He y Hy. apply (proj1 (offered_t_sw _ _ _)) in Ho.
    rewrite tenv_entry_sw in He.
    destruct (tenv_entry Θ k) as [e0|] eqn:E; [|done]. injection He as <-.
    apply elem_of_map in Hy as (y0 & -> & Hy0). simpl. unfold entry_head. simpl.
    rewrite !ptsw_involutive. by apply (H Hs k e0).
  Qed.

  Lemma konst_ty_sw W k T :
    konst_ty (w_eq W) (w_lt W) k T →
    konst_ty (w_eq (wsw a b W)) (w_lt (wsw a b W)) k (tysw a b T).
  Proof.
    destruct 1; simpl; rewrite ?dual_sw.
    - constructor.
    - constructor.
    - rewrite payload_at_sw. constructor. intros h Hh.
      rewrite <-payload_at_sw, heads_sw in Hh.
      apply elem_of_map in Hh as (h0 & -> & Hh0). simpl.
      rewrite !ptsw_involutive. auto.
    - rewrite payload_at_sw. constructor.
    - constructor.
    - constructor. simpl. by rewrite !ptsw_involutive.
    - rewrite ty_inst_sw. constructor. by rewrite length_fmap.
  Qed.

  Lemma pteqW_sw W x y : pteqW W x y → pteqW (wsw a b W) (ptsw a b x) (ptsw a b y).
  Proof.
    intros [->|(Hx & Hy & H)]; [by left|right].
    rewrite !pt_ground_sw. split_and!; [done|done|]. simpl.
    by rewrite !ptsw_involutive.
  Qed.

  Lemma teqW_sw W T : ∀ U, teqW W T U → teqW (wsw a b W) (tysw a b T) (tysw a b U).
  Proof.
    induction T; intros [] H; simpl in *; try done; try naive_solver.
    - destruct H as (Hu & Hl & ? & ?). split_and!; auto.
      + destruct ub, ub0; simpl in *; try done. by apply pteqW_sw.
      + destruct lb, lb0; simpl in *; try done. by apply pteqW_sw.
    - destruct H as [? ?]. split; [by apply pteqW_sw|by apply seq_sw].
  Qed.
End ready.

(** World equivalence leaves readiness, frames and constants alone. *)
Lemma above_offered_wsame W1 W2 Θ off :
  wsame W1 W2 → above_offered W1 Θ off → above_offered W2 Θ off.
Proof.
  intros (_ & _ & Hl) H k e He Hk. destruct (H k e He Hk) as (k' & e' & ? & ? & ?).
  exists k', e'. split_and!; [done|done|]. by apply Hl.
Qed.

Lemma ready_t_wsame W1 W2 Θ t : wsame W1 W2 → ready_t W1 Θ t → ready_t W2 Θ t.
Proof.
  intros HS H Hs. destruct (H Hs). split; [done|]. by eapply above_offered_wsame.
Qed.

Lemma ready_p_wsame W1 W2 Σ p : wsame W1 W2 → ready_p W1 Σ p → ready_p W2 Σ p.
Proof.
  intros HS H Hs. destruct (H Hs). split; [done|]. by eapply above_offered_wsame.
Qed.

Lemma frame_t_wsame W1 W2 Θ t F : wsame W1 W2 → frame_t W1 Θ t F → frame_t W2 Θ t F.
Proof.
  intros (_ & _ & Hl) H Hs k e Ho He y Hy. apply Hl. by eapply H.
Qed.

Lemma konst_ty_mono (peq plt peq' plt' : point → point → Prop) k T :
  (∀ x y, peq x y → peq' x y) → (∀ x y, plt x y → plt' x y) →
  konst_ty peq plt k T → konst_ty peq' plt' k T.
Proof. intros He Hl. destruct 1; econstructor; eauto. Qed.

Lemma teqW_mono W1 W2 T : ∀ U,
  (∀ x y, w_eq W1 x y → w_eq W2 x y) → teqW W1 T U → teqW W2 T U.
Proof.
  assert (∀ x y, (∀ x y, w_eq W1 x y → w_eq W2 x y) →
            pteqW W1 x y → pteqW W2 x y) as Hp.
  { intros x y He [->|(? & ? & ?)]; [by left|right; auto]. }
  induction T; intros [] He; simpl; try done; try naive_solver.
  intros (Hu & Hl & ? & ?). split_and!; auto.
  - destruct ub, ub0; simpl in *; try done. eauto.
  - destruct lb, lb0; simpl in *; try done. eauto.
Qed.

Lemma wext_swap_back a b W W' W'' :
  wsame (wsw a b W) W' → wext W' W'' → wext W (wsw a b W'').
Proof.
  intros HS Hx. apply (wext_wsw a b) in Hx.
  eapply wext_wsame; [|apply wsame_refl|exact Hx].
  eapply wsame_trans; [apply wsw_wsame, wsame_sym, HS|apply wsw_wsw].
Qed.

Section misc.
  Context (a b : nat).

  Lemma list_ptsw_involutive (xs : list point) : ptsw a b <$> (ptsw a b <$> xs) = xs.
  Proof.
    rewrite <-list_fmap_compose. rewrite <-(list_fmap_id xs) at 2.
    apply list_fmap_ext. intros. apply ptsw_involutive.
  Qed.

  Lemma set_ptsw_involutive (F : gset point) :
    set_map (ptsw a b) (set_map (ptsw a b) F : gset point) = F.
  Proof.
    apply set_eq. intros x. rewrite !elem_of_map. split.
    - intros (y & -> & Hy). apply elem_of_map in Hy as (z & -> & Hz).
      by rewrite ptsw_involutive.
    - intros Hx. exists (ptsw a b x). split; [by rewrite ptsw_involutive|].
      apply elem_of_map. exists x. done.
  Qed.

  Lemma set_ptsw_empty : set_map (ptsw a b) (∅ : gset point) = (∅ : gset point).
  Proof. apply set_map_empty. Qed.

  Lemma frame_roots_sw F :
    frame_roots (set_map (ptsw a b) F) = set_map (pnsw a b) (frame_roots F).
  Proof.
    unfold frame_roots. apply set_eq. intros p. rewrite !elem_of_map. split.
    - intros (x & -> & Hx). apply elem_of_map in Hx as (y & -> & Hy).
      exists (pt_root y). rewrite pt_root_sw. split; [done|]. by apply elem_of_map_2.
    - intros (q & -> & Hq). apply elem_of_map in Hq as (y & -> & Hy).
      exists (ptsw a b y). rewrite pt_root_sw. split; [done|]. by apply elem_of_map_2.
  Qed.

  Lemma not_elem_of_names_sw p (N : gset pname) :
    p ∉ N → pnsw a b p ∉ (set_map (pnsw a b) N : gset pname).
  Proof. intros Hp Hin. by apply elem_of_names_sw in Hin. Qed.

  Lemma disjoint_names_sw (N M : gset pname) :
    N ## M → (set_map (pnsw a b) N : gset pname) ## set_map (pnsw a b) M.
  Proof.
    intros H. apply elem_of_disjoint. intros p H1 H2.
    apply elem_of_names_sw' in H1, H2. set_solver.
  Qed.
End misc.

(** ** The relations are invariant

    One induction on the step index carries all three relations. The
    target world is any world equivalent to the transposed one, so that
    the round trip through a transposition (which is the identity only
    up to equivalence) closes. *)

Lemma rel_psw a b n :
  (∀ W W' Θ T v, wsame (wsw a b W) W' → Vrel n W Θ T v →
     Vrel n W' (tenvsw a b Θ) (tysw a b T) v) ∧
  (∀ W W' Θ T F e, wsame (wsw a b W) W' → Erel n W Θ T F e →
     Erel n W' (tenvsw a b Θ) (tysw a b T) (set_map (ptsw a b) F) e) ∧
  (∀ W W' Σ T p, wsame (wsw a b W) W' → Prel n W Σ T p →
     Prel n W' (senvsw a b Σ) (tysw a b T) p).
Proof.
  induction n as [n IHn] using lt_wf_ind.
  assert (∀ j, j < n → ∀ W W' Θ T v, wsame (wsw a b W) W' → Vrel j W Θ T v →
            Vrel j W' (tenvsw a b Θ) (tysw a b T) v) as IHV
    by (intros j Hj; apply (IHn j Hj)).
  assert (∀ j, j < n → ∀ W W' Θ T F e, wsame (wsw a b W) W' →
            Erel j W Θ T F e →
            Erel j W' (tenvsw a b Θ) (tysw a b T) (set_map (ptsw a b) F) e) as IHE
    by (intros j Hj; apply (IHn j Hj)).
  assert (∀ j, j < n → ∀ W W' Σ T p, wsame (wsw a b W) W' → Prel j W Σ T p →
            Prel j W' (senvsw a b Σ) (tysw a b T) p) as IHP
    by (intros j Hj; apply (IHn j Hj)).
  assert (∀ W'', wsame (wsw a b (wsw a b W'')) W'') as Hrt
    by (intros; apply wsw_wsw).
  assert (∀ W W' Θ T v, wsame (wsw a b W) W' → Vrel n W Θ T v →
            Vrel n W' (tenvsw a b Θ) (tysw a b T) v) as HV.
  { intros W W' Θ T. revert Θ.
    induction T as [|ub lb T1 IHT1 U IHU|T1 IHT1 U IHU|T1 IHT1 U IHU|m T1 IHT1|s x];
      intros Θ v HS HVv; simpl.
    - apply Vrel_unit_iff in HVv as [-> ->].
      apply Vrel_unit_iff. by rewrite tenvsw_empty.
    - apply Vrel_lolli_iff in HVv
        as [(eb & -> & Hfc & Hlb & H)|(k & T0 & -> & -> & Hk & Ht)].
      + apply Vrel_lolli_iff. left. exists eb. split_and!.
        * done.
        * by rewrite dom_tenvsw.
        * rewrite tenv_heads_sw. eapply lb_below_wsame; [exact HS|].
          by apply lb_below_sw.
        * intros W'' j Θ' Θ'' w F Hx Hj Hc HVw Hub.
          assert (wext W (wsw a b W'')) as Hx' by (by eapply wext_swap_back).
          apply (tenv_comp_sw a b) in Hc. rewrite tenvsw_involutive in Hc.
          apply (IHV j Hj W'' (wsw a b W'')) in HVw; [|apply wsame_refl].
          rewrite tysw_involutive in HVw.
          apply (ub_below_sw a b) in Hub. rewrite ptsw_fmap_involutive in Hub.
          specialize (H _ _ _ _ _ _ Hx' Hj Hc HVw Hub).
          apply (IHE j Hj (wsw a b W'') W'') in H; [|apply Hrt].
          by rewrite tenvsw_involutive, set_ptsw_involutive in H.
      + apply Vrel_lolli_iff. right. exists k, (tysw a b T0). split_and!.
        * done.
        * by rewrite tenvsw_empty.
        * eapply konst_ty_mono; [| |by apply konst_ty_sw];
            intros; destruct HS as (_ & He & Hl); [by apply He|by apply Hl].
        * eapply teqW_mono; [|by apply (teqW_sw a b W T0 (TLolli ub lb T1 U))].
          intros. by apply HS.
    - apply Vrel_prod_iff in HVv as (v1 & v2 & Θ1 & Θ2 & -> & Hc & H1 & H2).
      apply Vrel_prod_iff.
      exists v1, v2, (tenvsw a b Θ1), (tenvsw a b Θ2).
      split_and!; [done|eapply tenv_comp_mono; [|by apply tenv_comp_sw]; intros ? ? ?; by apply HS|by apply IHT1|by apply IHU].
    - apply Vrel_sum_iff in HVv as [(v' & -> & H)|(v' & -> & H)];
        apply Vrel_sum_iff; [left|right]; eexists; (split; [done|]).
      + by apply IHT1.
      + by apply IHU.
    - apply Vrel_box_iff in HVv as (-> & eb & -> & Hfc & H).
      apply Vrel_box_iff. rewrite tenvsw_empty. split; [done|].
      exists eb. split_and!; [done|done|].
      intros W'' j xs Hx Hj Hxs.
      assert (wext W (wsw a b W'')) as Hx' by (by eapply wext_swap_back).
      specialize (H _ j (ptsw a b <$> xs) Hx' Hj ltac:(by rewrite length_fmap)).
      apply (IHE j Hj (wsw a b W'') W'') in H; [|apply Hrt].
      by rewrite tenvsw_empty, set_ptsw_empty, ty_inst_sw,
        list_ptsw_involutive in H.
    - apply Vrel_sess_iff in HVv as (c & s0 & k & -> & -> & Hs & Hx).
      apply Vrel_sess_iff. exists c, (stysw a b s0), (ptsw a b k).
      split_and!.
      + done.
      + by rewrite tenvsw_singleton.
      + by apply seq_sw.
      + destruct HS as (_ & He & _). apply He. by apply wsw_eq. }
  split_and!; [exact HV| |].
  - (* term relation *)
    destruct n as [|n']; [intros; apply Erel_0|].
    intros W W' Θ T F e HS HE. revert W' HS.
    induction HE as [W Θ T F e Hval Hrdy Hstep] using Erel_S_ind.
    intros W' HS.
    apply Erel_S_iff. split_and!.
    { intros Hirr. apply (HV W); [done|]. by apply Hval. }
    { intros Hirr. destruct (Hrdy Hirr) as [Hr Hf]. split.
      - eapply ready_t_wsame; [exact HS|]. by apply ready_t_sw.
      - eapply frame_t_wsame; [exact HS|]. by apply frame_t_sw. }
    intros α e'' Hst. specialize (Hstep _ _ Hst).
    destruct α as [|[c w|c w|c|cd]|c|w]; simpl in Hstep |- *.
    + apply (IHE n' ltac:(lia) W); done.
    + (* recv *)
      destruct Hstep as (Θ1 & m & U & s & k & Hhd & H).
      exists (tenvsw a b Θ1), m, (tysw a b U), (stysw a b s), (ptsw a b k).
      split; [by apply (tenv_hd_sw a b _ _ (SRcv m U s))|].
      intros W'' j Θ2 Θ1c Θ' Hx Hj Hext Hc HVw.
      assert (wext W (wsw a b W'')) as Hx' by (by eapply wext_swap_back).
      apply (tenv_comp_sw a b) in Hc.
      apply (tenv_ext_sw a b) in Hext. rewrite tenvsw_involutive in Hext.
      unfold esw in Hext. simpl in Hext.
      rewrite stysw_involutive, ptsw_shift, ptsw_involutive in Hext.
      apply (IHV j ltac:(lia) W'' (wsw a b W'')) in HVw; [|apply wsame_refl].
      rewrite payload_at_sw, tysw_involutive, ptsw_involutive in HVw.
      pose proof (H _ _ _ _ _ Hx' Hj Hext Hc HVw) as HE'.
      apply (IHE j ltac:(lia) (wsw a b W'') W'') in HE'; [|apply Hrt].
      by rewrite tenvsw_involutive in HE'.
    + (* send *)
      destruct Hstep as (Θr & Θ1 & Θ2 & m & U & s & k & Θ' &
                         Hhd & Hc & HVw & Hext & HE').
      exists (tenvsw a b Θr), (tenvsw a b Θ1), (tenvsw a b Θ2), m,
        (tysw a b U), (stysw a b s), (ptsw a b k), (tenvsw a b Θ').
      split_and!.
      * by apply (tenv_hd_sw a b _ _ (SSnd m U s)).
      * eapply tenv_comp_mono; [|by apply tenv_comp_sw]; intros ? ? ?; by apply HS.
      * rewrite <-payload_at_sw. by apply (HV W W') in HVw.
      * by apply (tenv_ext_sw a b _ _ (s, pt_shift 1 k)).
      * by apply (proj2 HE').
    + (* close *)
      destruct Hstep as (Θ1 & k & Hhd & HE').
      exists (tenvsw a b Θ1), (ptsw a b k). split.
      * by apply (tenv_hd_sw a b _ _ SEnd).
      * by apply (proj2 HE').
    + (* link *)
      destruct Hstep as (c & d & Θ1 & Θm & sc & sd & kc & kd &
                         -> & H1 & H2 & Hdu & Hal & HE').
      exists c, d, (tenvsw a b Θ1), (tenvsw a b Θm),
        (stysw a b sc), (stysw a b sd), (ptsw a b kc), (ptsw a b kd).
      split_and!.
      * done.
      * by apply (tenv_ext_sw a b _ _ (sd, kd)).
      * by apply (tenv_ext_sw a b _ _ (sc, kc)).
      * by apply sdual_sw.
      * destruct HS as (_ & He & _). apply He. by apply wsw_eq.
      * by apply (proj2 HE').
    + (* new *)
      intros Hc. rewrite dom_tenvsw in Hc.
      destruct (Hstep Hc) as (a0 & s & s' & W1 & Ha & Hdu & Hfr & HE').
      exists (nswap a b a0), (stysw a b s), (stysw a b s'), (wsw a b W1). split_and!.
      * rewrite tenv_roots_sw, (proj1 (roots_sw_mut a b)), frame_roots_sw,
          <-!set_map_union_L.
        apply (not_elem_of_names_sw a b (NConst a0)). done.
      * by apply sdual_sw.
      * apply (wext_fresh_wsw a b) in Hfr.
        rewrite set_map_singleton_L in Hfr.
        eapply wext_fresh_wsame; [exact HS|apply wsame_refl|exact Hfr].
      * apply (IHE n' ltac:(lia) W1 (wsw a b W1)) in HE'; [|apply wsame_refl].
        by rewrite tenvsw_insert in HE'.
    + (* spawn *)
      destruct Hstep as (Θ1 & Θ2 & ub & lb & Hc & HVw & HE').
      exists (tenvsw a b Θ1), (tenvsw a b Θ2), (ptsw a b <$> ub), (ptsw a b <$> lb).
      split_and!.
      * eapply tenv_comp_mono; [|by apply tenv_comp_sw]; intros ? ? ?; by apply HS.
      * apply (HV W W' _ (TLolli ub lb TUnit TUnit)) in HVw; [|done]. exact HVw.
      * by apply (IHE n' ltac:(lia) W).
  - (* process relation *)
    destruct n as [|n']; [intros; apply Prel_0|].
    intros W W' Σ T p HS HP. revert W' HS.
    induction HP as [W Σ T p Hirr Hrdy Hstep] using Prel_S_ind.
    intros W' HS.
    apply Prel_S_iff. split_and!.
    { intros Hpirr.
      destruct (Hirr Hpirr) as (v & E & -> & Hv & HVv & HE).
      exists v, E. split_and!; [done|done| |done].
      apply (HV W W') in HVv; [|done]. by rewrite tenvsw_of in HVv. }
    { intros Hpirr. eapply ready_p_wsame; [exact HS|]. apply ready_p_sw.
      by apply Hrdy. }
    intros π q Hst. specialize (Hstep _ _ Hst).
    destruct π as [|[c w|c w|c|cd]]; simpl in Hstep |- *.
    + (* τ *)
      destruct Hstep as [Htau Hlink]. split.
      { intros Hd. rewrite dom_senvsw in Hd.
        destruct (Htau Hd) as (N & W1 & HN & Hfr & HP').
        exists (set_map (pnsw a b) N), (wsw a b W1). split_and!.
        * rewrite senv_roots_sw, (proj1 (roots_sw_mut a b)), <-set_map_union_L.
          by apply disjoint_names_sw.
        * apply (wext_fresh_wsw a b) in Hfr.
          eapply wext_fresh_wsame; [exact HS|apply wsame_refl|exact Hfr].
        * by apply (IHP n' ltac:(lia) W1). }
      intros Hl Hd. rewrite dom_senvsw in Hd.
      destruct (Hlink Hl Hd) as (N & W1 & HN & Hfr & HP').
      exists (set_map (pnsw a b) N), (wsw a b W1). split_and!.
      * rewrite senv_roots_sw, (proj1 (roots_sw_mut a b)), <-set_map_union_L.
        by apply disjoint_names_sw.
      * apply (wext_fresh_wsw a b) in Hfr.
        eapply wext_fresh_wsame; [exact HS|apply wsame_refl|exact Hfr].
      * apply (proj2 HP'). apply wsame_refl.
    + (* recv *)
      destruct Hstep as (Σ1 & m & U & s & k & Hhd & Hc & H).
      exists (senvsw a b Σ1), m, (tysw a b U), (stysw a b s), (ptsw a b k).
      split_and!.
      * by apply (senv_hd_sw a b _ _ (SRcv m U s)).
      * by rewrite dom_senvsw.
      * intros W'' j Θ2 Hx Hj Hfr Hok HVw.
        assert (wext W (wsw a b W'')) as Hx' by (by eapply wext_swap_back).
        assert (dom (tenvsw a b Θ2) ## p.1) as Hfr' by (by rewrite dom_tenvsw).
        assert (recv_ok (wsw a b W'') (<[c := (s, pt_shift 1 k)]> Σ1) (tenvsw a b Θ2)) as Hok'.
        { apply (recv_ok_sw a b) in Hok.
          rewrite senvsw_insert, senvsw_involutive in Hok.
          unfold esw in Hok. simpl in Hok.
          by rewrite stysw_involutive, ptsw_shift, ptsw_involutive in Hok. }
        apply (IHV j ltac:(lia) W'' (wsw a b W'')) in HVw; [|apply wsame_refl].
        rewrite payload_at_sw, tysw_involutive, ptsw_involutive in HVw.
        specialize (H _ _ _ Hx' Hj Hfr' Hok' HVw).
        apply (IHP j ltac:(lia) (wsw a b W'') W'') in H; [|apply Hrt].
        rewrite <-recv_env_sw, tenvsw_involutive, senvsw_insert in H.
        unfold esw in H. simpl in H. rewrite ptsw_shift in H.
        rewrite <-(recv_back_sw a b), tenvsw_involutive, senvsw_insert in H.
        unfold esw in H. simpl in H. rewrite ptsw_shift in H.
        exact H.
    + (* send *)
      destruct Hstep as (Σ0 & Σv & m & U & s & k & Σe & Θe & Hhd &
                         Hd0v & Hc0 & Hcv & Hdom & Hsplit & HdΣ & HVw & HP').
      exists (senvsw a b Σ0), (senvsw a b Σv), m, (tysw a b U),
        (stysw a b s), (ptsw a b k), (senvsw a b Σe), (tenvsw a b Θe).
      split_and!.
      * rewrite <-senvsw_union. by apply (senv_hd_sw a b _ _ (SSnd m U s)).
      * by apply senvsw_disjoint.
      * by rewrite dom_senvsw.
      * by rewrite dom_senvsw.
      * by rewrite dom_tenvsw.
      * eapply send_split_mono; [|by apply send_split_sw]. intros ? ? ?. by apply HS.
      * by rewrite dom_tenvsw, dom_senvsw.
      * apply (HV W W') in HVw; [|done].
        by rewrite tenvsw_union, tenvsw_of, payload_at_sw in HVw.
      * apply (proj2 HP' W') in HS.
        by rewrite senvsw_insert, senvsw_union in HS.
    + (* close *)
      destruct Hstep as (Σ1 & k & Hhd & Hc & HP').
      exists (senvsw a b Σ1), (ptsw a b k). split_and!.
      * by apply (senv_hd_sw a b _ _ SEnd).
      * by rewrite dom_senvsw.
      * by apply (proj2 HP').
    + (* link *)
      destruct Hstep as (c & d & Σ1 & sc & sd & kc & kd &
                         -> & Hne & -> & Hc1 & Hd1 & Hdu & Hal & HP').
      exists c, d, (senvsw a b Σ1), (stysw a b sc), (stysw a b sd),
        (ptsw a b kc), (ptsw a b kd).
      split_and!.
      * done.
      * done.
      * by rewrite !senvsw_insert.
      * by rewrite dom_senvsw.
      * by rewrite dom_senvsw.
      * by apply sdual_sw.
      * destruct HS as (_ & He & _). apply He. by apply wsw_eq.
      * by apply (proj2 HP').
Qed.

Lemma Vrel_psw a b n W Θ T v :
  Vrel n W Θ T v → Vrel n (wsw a b W) (tenvsw a b Θ) (tysw a b T) v.
Proof. apply (rel_psw a b n). apply wsame_refl. Qed.

Lemma Erel_psw a b n W Θ T F e :
  Erel n W Θ T F e →
  Erel n (wsw a b W) (tenvsw a b Θ) (tysw a b T) (set_map (ptsw a b) F) e.
Proof. apply (rel_psw a b n). apply wsame_refl. Qed.

Lemma Prel_psw a b n W Σ T p :
  Prel n W Σ T p → Prel n (wsw a b W) (senvsw a b Σ) (tysw a b T) p.
Proof. apply (rel_psw a b n). apply wsame_refl. Qed.

(** ** Transpositions of names nobody mentions *)

Lemma nswap_r a b : nswap a b b = a.
Proof. unfold nswap. repeat case_decide; congruence. Qed.

Section fixed.
  Context (a b : nat).

  Lemma pnsw_fix p :
    pn_root p ≠ NConst a → pn_root p ≠ NConst b → pnsw a b p = p.
  Proof.
    induction p; simpl; intros Ha Hb; try done.
    - f_equal. apply nswap_ne; congruence.
    - f_equal. by apply IHp.
  Qed.

  Lemma ptsw_fix x :
    pt_root x ≠ NConst a → pt_root x ≠ NConst b → ptsw a b x = x.
  Proof. intros. destruct x. unfold ptsw. simpl. by rewrite pnsw_fix. Qed.

  Lemma tysw_fix_mut :
    (∀ T, NConst a ∉ ty_roots T → NConst b ∉ ty_roots T → tysw a b T = T) ∧
    (∀ s, NConst a ∉ sty_roots s → NConst b ∉ sty_roots s → stysw a b s = s).
  Proof.
    apply ty_sty_mut_ind; simpl; intros; try done; f_equal;
      try (apply H; set_solver); try (apply H0; set_solver);
      try (apply ptsw_fix; set_solver).
    - destruct ub; simpl; [|done]. f_equal. apply ptsw_fix; set_solver.
    - destruct lb; simpl; [|done]. f_equal. apply ptsw_fix; set_solver.
  Qed.

  Lemma tysw_fix T : NConst a ∉ ty_roots T → NConst b ∉ ty_roots T → tysw a b T = T.
  Proof. apply tysw_fix_mut. Qed.

  Lemma esw_fix e :
    NConst a ∉ entry_roots e → NConst b ∉ entry_roots e → esw a b e = e.
  Proof.
    destruct e as [s x]. unfold entry_roots, esw. simpl. intros Ha Hb.
    rewrite (proj2 tysw_fix_mut), ptsw_fix; set_solver.
  Qed.

  Lemma endsw_fix o :
    NConst a ∉ ends_roots o → NConst b ∉ ends_roots o → endsw a b o = o.
  Proof. destruct o; simpl; intros; by rewrite !esw_fix by set_solver. Qed.

  Lemma tenvsw_fix Θ :
    NConst a ∉ tenv_roots Θ → NConst b ∉ tenv_roots Θ → tenvsw a b Θ = Θ.
  Proof.
    intros Ha Hb. apply map_eq. intros c. rewrite lookup_tenvsw.
    destruct (Θ !! c) as [o|] eqn:E; simpl; [|done]. f_equal.
    apply endsw_fix; intros Hin; [apply Ha|apply Hb];
      apply elem_of_tenv_roots; eauto.
  Qed.

  Lemma senvsw_fix Σ :
    NConst a ∉ senv_roots Σ → NConst b ∉ senv_roots Σ → senvsw a b Σ = Σ.
  Proof.
    intros Ha Hb. apply map_eq. intros c. rewrite lookup_senvsw.
    destruct (Σ !! c) as [e|] eqn:E; simpl; [|done]. f_equal.
    apply esw_fix; intros Hin; [apply Ha|apply Hb]; apply elem_of_tenv_roots;
      exists c, (One e); unfold tenv_of; by rewrite lookup_fmap, E.
  Qed.

  Lemma set_ptsw_fix F :
    NConst a ∉ frame_roots F → NConst b ∉ frame_roots F → set_map (ptsw a b) F = F.
  Proof.
    intros Ha Hb. apply set_eq. intros x. rewrite elem_of_map. split.
    - intros (y & -> & Hy). rewrite ptsw_fix; [done| |];
        intros E; [apply Ha|apply Hb]; rewrite <-E; by apply elem_of_map_2.
    - intros Hx. exists x. rewrite ptsw_fix; [done| |];
        intros E; [apply Ha|apply Hb]; rewrite <-E; by apply elem_of_map_2.
  Qed.

  (** A world that knows neither constant is fixed by their
      transposition. *)
  Lemma wsw_fix W :
    world_wf W → NConst a ∉ w_names W → NConst b ∉ w_names W →
    wsame (wsw a b W) W.
  Proof.
    intros HW Ha Hb.
    assert (∀ x, pt_root x = NConst a ∨ pt_root x = NConst b → pt_root x ∉ w_names W)
      as Hout by (intros x [-> | ->]; done).
    assert (∀ x, (pt_root x ≠ NConst a ∧ pt_root x ≠ NConst b) ∨
                 pt_root x = NConst a ∨ pt_root x = NConst b) as Hcase.
    { intros x. destruct (decide (pt_root x = NConst a)); [by right; left|].
      destruct (decide (pt_root x = NConst b)); [by right; right|by left]. }
    assert (∀ x, pt_root x = NConst a ∨ pt_root x = NConst b →
              pt_root (ptsw a b x) = NConst a ∨ pt_root (ptsw a b x) = NConst b)
      as Hsw.
    { intros x [Hx|Hx]; rewrite pt_root_sw, Hx; simpl;
        [rewrite nswap_l; by right|rewrite nswap_r; by left]. }
    assert (∀ p, p ∈ w_names W → pnsw a b p = p) as Hfixn.
    { intros p Hp. pose proof (wf_names_root _ p HW Hp) as Hr.
      apply pnsw_fix; rewrite Hr; intros ->; done. }
    split_and!.
    - apply set_eq. intros p. simpl. rewrite elem_of_names_sw'. split; intros Hp.
      + assert (pnsw a b (pnsw a b p) = pnsw a b p) as E by (by apply Hfixn).
        rewrite pnsw_involutive in E. by rewrite E.
      + by rewrite Hfixn.
    - intros x y. simpl.
      destruct (Hcase x) as [[Hxa Hxb]|Hx];
        [destruct (Hcase y) as [[Hya Hyb]|Hy]|].
      + by rewrite !ptsw_fix.
      + split; intros H.
        * apply (wf_eq_supp _ HW) in H as [H|[_ H]];
            [|by destruct (Hout _ (Hsw _ Hy))].
          apply (ptsw_inj a b) in H as ->. apply HW.
        * apply (wf_eq_supp _ HW) in H as [->|[_ H]]; [apply HW|].
          by destruct (Hout _ Hy).
      + split; intros H.
        * apply (wf_eq_supp _ HW) in H as [H|[H _]];
            [|by destruct (Hout _ (Hsw _ Hx))].
          apply (ptsw_inj a b) in H as ->. apply HW.
        * apply (wf_eq_supp _ HW) in H as [->|[H _]]; [apply HW|].
          by destruct (Hout _ Hx).
    - intros x y. simpl.
      destruct (Hcase x) as [[Hxa Hxb]|Hx];
        [destruct (Hcase y) as [[Hya Hyb]|Hy]|].
      + by rewrite !ptsw_fix.
      + split; intros H.
        * apply (wf_lt_supp _ HW) in H as [[Hn Ho]|[_ H]];
            [|by destruct (Hout _ (Hsw _ Hy))].
          apply wf_lt_same; [done| |done]. by apply (pnsw_inj a b).
        * apply (wf_lt_supp _ HW) in H as [[Hn Ho]|[_ H]]; [|by destruct (Hout _ Hy)].
          apply wf_lt_same; [done|simpl; by rewrite Hn|done].
      + split; intros H.
        * apply (wf_lt_supp _ HW) in H as [[Hn Ho]|[H _]];
            [|by destruct (Hout _ (Hsw _ Hx))].
          apply wf_lt_same; [done| |done]. by apply (pnsw_inj a b).
        * apply (wf_lt_supp _ HW) in H as [[Hn Ho]|[H _]]; [|by destruct (Hout _ Hx)].
          apply wf_lt_same; [done|simpl; by rewrite Hn|done].
  Qed.
End fixed.

(** The point a term creates at [new] can be renamed to any constant
    that is fresh for the world and for the points of Θ, T and F. *)
Lemma Erel_new_rename n W W1 Θ T F e c s s' a0 a1 :
  world_wf W → wext_fresh W {[NConst a0]} W1 →
  NConst a0 ∉ tenv_roots Θ ∪ ty_roots T ∪ frame_roots F →
  NConst a1 ∉ w_names W ∪ tenv_roots Θ ∪ ty_roots T ∪ frame_roots F →
  Erel n W1 (<[c := Both (s, pconst a0) (s', pconst a0)]> Θ) T F e →
  ∃ W1', wext_fresh W {[NConst a1]} W1' ∧
    Erel n W1' (<[c := Both (stysw a0 a1 s, pconst a1) (stysw a0 a1 s', pconst a1)]> Θ)
      T F e.
Proof.
  intros HW Hfr Ha0 Ha1 HE.
  assert (NConst a0 ∉ w_names W) as Ha0W by (destruct Hfr as (_ & HN & _); set_solver).
  exists (wsw a0 a1 W1). split.
  - apply (wext_fresh_wsw a0 a1) in Hfr. rewrite set_map_singleton_L in Hfr.
    simpl in Hfr. rewrite nswap_l in Hfr.
    eapply wext_fresh_wsame; [|apply wsame_refl|exact Hfr].
    apply wsw_fix; [done|done|set_solver].
  - apply (Erel_psw a0 a1) in HE.
    rewrite tenvsw_insert, tenvsw_fix, tysw_fix, set_ptsw_fix in HE by set_solver.
    assert (∀ s0, esw a0 a1 (s0, pconst a0) = (stysw a0 a1 s0, pconst a1)) as Hes.
    { intros s0. unfold esw. simpl. by rewrite ptsw_pconst, nswap_l. }
    cbn [endsw] in HE. by rewrite !Hes in HE.
Qed.

(** There is always a constant outside a finite set of names. *)
Lemma fresh_const (X : gset pname) : ∃ a, NConst a ∉ X.
Proof.
  set (C := list_to_set (omap (λ p, match p with NConst a => Some a | _ => None end)
                                (elements X)) : gset nat).
  exists (fresh C). intros Hin. apply (is_fresh C). subst C.
  apply elem_of_list_to_set, list_elem_of_omap. eexists. split; [by apply elem_of_elements|]. done.
Qed.

(** The points a τ step places can be renamed away from any finite set
    of names X. *)
Lemma Prel_tau_rename n X : ∀ m W N W1 Σ T p,
  size (N ∩ X) = m →
  world_wf W → wext_fresh W N W1 → N ## senv_roots Σ ∪ ty_roots T →
  Prel n W1 Σ T p →
  ∃ N' W1', N' ## X ∧ N' ## senv_roots Σ ∪ ty_roots T ∧
    wext_fresh W N' W1' ∧ Prel n W1' Σ T p.
Proof.
  intros m. induction m as [m IH] using lt_wf_ind.
  intros W N W1 Σ T p Hm HW Hfr HN HP.
  destruct (decide (N ∩ X = ∅)) as [Hemp|Hne].
  { exists N, W1. split_and!; [set_solver|done|done|done]. }
  apply set_choose_L in Hne as [q Hq].
  assert (world_wf W1) as HW1 by (destruct Hfr as ((_ & _ & _ & [? _]) & _); done).
  destruct Hfr as [Hx [HNW [Hnames Hold]]].
  assert (q ∈ w_names W1) as HqW1 by (rewrite Hnames; set_solver).
  destruct (wf_names_const _ HW1 q HqW1) as [a ->].
  destruct (fresh_const (w_names W1 ∪ X ∪ senv_roots Σ ∪ ty_roots T ∪ N)) as [a1 Ha1].
  set (N'' := set_map (pnsw a a1) N : gset pname).
  assert (∀ r, r ∈ N → ∃ c, r = NConst c) as HNc.
  { intros r Hr. apply (wf_names_const _ HW1). rewrite Hnames. set_solver. }
  assert (N'' ∩ X ⊆ (N ∩ X) ∖ {[NConst a]}) as Hsub.
  { intros r. subst N''. rewrite elem_of_intersection, elem_of_map, elem_of_difference,
      elem_of_intersection, elem_of_singleton.
    intros [(r0 & -> & Hr0) HrX]. destruct (HNc r0 Hr0) as [c ->]. simpl in *.
    unfold nswap in *. repeat case_decide; subst; simpl in *; [set_solver| |].
    - exfalso. apply Ha1. set_solver.
    - split; [split; done|congruence]. }
  assert (size (N'' ∩ X) < m) as Hlt.
  { rewrite <-Hm. eapply Nat.le_lt_trans; [apply subseteq_size, Hsub|].
    rewrite size_difference by set_solver. rewrite size_singleton.
    assert (size (N ∩ X) ≠ 0) by (intros ?%size_empty_inv; set_solver). lia. }
  assert (NConst a ∉ senv_roots Σ ∪ ty_roots T) as Ha by set_solver.
  assert (wext_fresh W N'' (wsw a a1 W1)) as Hfr''.
  { pose proof (wext_fresh_wsw a a1 W N W1 (conj Hx (conj HNW (conj Hnames Hold))))
      as H.
    eapply wext_fresh_wsame; [|apply wsame_refl|exact H].
    apply wsw_fix; [done|set_solver|set_solver]. }
  assert (N'' ## senv_roots Σ ∪ ty_roots T) as HN''.
  { apply elem_of_disjoint. intros r Hr Hr'. subst N''.
    apply elem_of_map in Hr as (r0 & -> & Hr0). destruct (HNc r0 Hr0) as [c ->].
    simpl in Hr'. unfold nswap in Hr'. repeat case_decide; subst;
      [set_solver..|]. set_solver. }
  apply (Prel_psw a a1) in HP.
  rewrite senvsw_fix, tysw_fix in HP by set_solver.
  exact (IH _ Hlt W N'' (wsw a a1 W1) Σ T p eq_refl HW Hfr'' HN'' HP).
Qed.
