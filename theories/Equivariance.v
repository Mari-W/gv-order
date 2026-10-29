(** * Renaming restricted names: equivariance with worlds (§10)

    Restricted names are bound. A transposition of two channel names
    a ↔ b, applied to terms and processes ([Swap.v]), to the points of
    types, to the keys and entries of environments, and to the facts
    and support of worlds alike, maps the logical relation to itself
    ([rel_swap]). Consequences:

    - a process can rename its restricted names away from any finite
      set of names, e.g. the names a given world mentions
      ([Prel_rename_away]);
    - P is monotone in the world up to such a renaming
      ([Prel_mono_rename]).

    The file builds the transport bottom-up: points, types and
    session types (generically for any map on points, then for the
    transposition), worlds, environments, readiness, and finally the
    three relations by induction on the step index. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export Monotone Swap.

(** ** Mapping the points of a type *)

Fixpoint tmap (f : point → point) (T : ty) : ty :=
  match T with
  | TUnit => TUnit
  | TLolli ub lb T1 U => TLolli (f <$> ub) (f <$> lb) (tmap f T1) (tmap f U)
  | TProd T1 U => TProd (tmap f T1) (tmap f U)
  | TSum T1 U => TSum (tmap f T1) (tmap f U)
  | TBox n T1 => TBox n (tmap f T1)
  | TSess s x => TSess (smap f s) (f x)
  end
with smap (f : point → point) (s : sty) : sty :=
  match s with
  | SRcv m T s' => SRcv m (tmap f T) (smap f s')
  | SSnd m T s' => SSnd m (tmap f T) (smap f s')
  | SEnd => SEnd
  | SMu s' => SMu (smap f s')
  | SVar a => SVar a
  | SVarD a => SVarD a
  end.

Section tmap.
  Context (f : point → point).

  Lemma smap_sren_mut :
    (∀ T r, tmap f (sren_ty r T) = sren_ty r (tmap f T)) ∧
    (∀ s r, smap f (sren r s) = sren r (smap f s)).
  Proof. apply ty_sty_mut_ind; intros; simpl; f_equal; auto. Qed.

  Lemma smap_sflip_mut :
    (∀ T k, tmap f (sflip_ty k T) = sflip_ty k (tmap f T)) ∧
    (∀ s k, smap f (sflip k s) = sflip k (smap f s)).
  Proof.
    apply ty_sty_mut_ind; intros; simpl; f_equal; auto;
      repeat case_decide; done.
  Qed.

  Lemma smap_dual s : smap f (dual s) = dual (smap f s).
  Proof.
    induction s; simpl; f_equal; auto.
    by rewrite (proj2 smap_sflip_mut), IHs.
  Qed.

  Lemma smap_sinst_mut :
    (∀ T σ, tmap f (sinst_ty σ T) = sinst_ty (smap f ∘ σ) (tmap f T)) ∧
    (∀ s σ, smap f (sinst σ s) = sinst (smap f ∘ σ) (smap f s)).
  Proof.
    apply ty_sty_mut_ind; intros; simpl; f_equal; auto.
    - rewrite H. apply sinst_ext. intros [|a]; simpl; [done|].
      unfold compose. apply (proj2 smap_sren_mut).
    - apply smap_dual.
  Qed.

  Lemma smap_unroll s : smap f (unroll s) = unroll (smap f s).
  Proof.
    unfold unroll. rewrite (proj2 smap_sinst_mut). apply sinst_ext.
    by intros [|a].
  Qed.

  Lemma smap_mu_depth s : mu_depth (smap f s) = mu_depth s.
  Proof. induction s; simpl; auto. Qed.

  Lemma smap_unfoldN k : ∀ s, smap f (unfoldN k s) = unfoldN k (smap f s).
  Proof.
    induction k as [|k IH]; intros s; [done|].
    destruct s; simpl; try done. by rewrite IH, smap_unroll.
  Qed.

  Lemma smap_unfoldS s : smap f (unfoldS s) = unfoldS (smap f s).
  Proof. unfold unfoldS. by rewrite smap_mu_depth, smap_unfoldN. Qed.

  Lemma eqT_tmap (ρ ρ' : sty → sty → Prop) T : ∀ U,
    (∀ s r, ρ s r → ρ' (smap f s) (smap f r)) →
    eqT ρ T U → eqT ρ' (tmap f T) (tmap f U).
  Proof. induction T; intros [] Hρ; simpl; try done; naive_solver. Qed.

  Lemma aeq_smap n : ∀ s r, aeq n s r → aeq n (smap f s) (smap f r).
  Proof.
    induction n as [|n IH]; intros s r H; [done|].
    simpl in *. unfold eq_step in *. rewrite <-!smap_unfoldS.
    destruct (unfoldS s), (unfoldS r); simpl in *; try done;
      try congruence;
      try (destruct H as (-> & ? & ?); split_and!; eauto using eqT_tmap).
  Qed.

  Lemma adual_smap n : ∀ s r, adual n s r → adual n (smap f s) (smap f r).
  Proof.
    induction n as [|n IH]; intros s r H; [done|].
    simpl in *. unfold dual_step in *. rewrite <-!smap_unfoldS.
    destruct (unfoldS s) eqn:Es, (unfoldS r) eqn:Er; simpl in *; try done;
      try (destruct H as (-> & ? & ?); split_and!; eauto using eqT_tmap, aeq_smap);
      try (rewrite H; simpl; done);
      try (rewrite <-smap_dual, <-H; done);
      try (injection H as ->; f_equal;
           by rewrite (proj2 smap_sflip_mut), smap_dual).
  Qed.

  Lemma seq_smap s r : seq s r → seq (smap f s) (smap f r).
  Proof. intros H n. by apply aeq_smap. Qed.

  Lemma sdual_smap s r : sdual s r → sdual (smap f s) (smap f r).
  Proof. intros H n. by apply adual_smap. Qed.

  Lemma teq_tmap T U : teq T U → teq (tmap f T) (tmap f U).
  Proof. apply eqT_tmap. intros. by apply seq_smap. Qed.
End tmap.

(** ** The transposition on points *)

Fixpoint pnswap (a b : chan) (p : pname) : pname :=
  match p with
  | NChan c => NChan (cswap a b c)
  | NVar x => NVar x
  | NSlot q o i => NSlot (pnswap a b q) o i
  end.

Definition ptswap (a b : chan) (x : point) : point :=
  Pt (pnswap a b (pt_name x)) (pt_off x).

Notation tyswap a b := (tmap (ptswap a b)).
Notation styswap a b := (smap (ptswap a b)).

Section points.
  Context (a b : chan).

  Lemma pnswap_involutive p : pnswap a b (pnswap a b p) = p.
  Proof. induction p; simpl; f_equal; auto using cswap_involutive. Qed.

  Lemma ptswap_involutive x : ptswap a b (ptswap a b x) = x.
  Proof. destruct x. unfold ptswap. simpl. by rewrite pnswap_involutive. Qed.

  Lemma pnswap_inj p q : pnswap a b p = pnswap a b q → p = q.
  Proof.
    intros H. rewrite <-(pnswap_involutive p), <-(pnswap_involutive q).
    by rewrite H.
  Qed.

  Lemma ptswap_inj x y : ptswap a b x = ptswap a b y → x = y.
  Proof.
    intros H. rewrite <-(ptswap_involutive x), <-(ptswap_involutive y).
    by rewrite H.
  Qed.

  Lemma ptswap_shift n x : ptswap a b (pt_shift n x) = pt_shift n (ptswap a b x).
  Proof. done. Qed.

  Lemma ptswap_slot x i : ptswap a b (pt_slot x i) = pt_slot (ptswap a b x) i.
  Proof. done. Qed.

  Lemma ptswap_chan c k : ptswap a b (pt_chan c k) = pt_chan (cswap a b c) k.
  Proof. done. Qed.

  Lemma ptswap_pvar x : ptswap a b (pvar x) = pvar x.
  Proof. done. Qed.

  Lemma pn_root_swap p : pn_root (pnswap a b p) = pnswap a b (pn_root p).
  Proof. induction p; simpl; auto. Qed.

  Lemma pt_root_swap x : pt_root (ptswap a b x) = pnswap a b (pt_root x).
  Proof. apply pn_root_swap. Qed.

  Lemma pn_inst_swap σ p :
    ptswap a b (pn_inst σ p) = pn_inst (ptswap a b ∘ σ) (pnswap a b p).
  Proof. induction p; simpl; [done|done|]. by rewrite <-IHp. Qed.

  Lemma pt_inst_swap σ x :
    ptswap a b (pt_inst σ x) = pt_inst (ptswap a b ∘ σ) (ptswap a b x).
  Proof. unfold pt_inst. by rewrite ptswap_shift, pn_inst_swap. Qed.
End points.

(** Instantiation of point variables, extensionally. *)
Lemma pn_inst_ext σ σ' p :
  (∀ x, σ x = σ' x) → pn_inst σ p = pn_inst σ' p.
Proof. intros H. induction p; simpl; [done|apply H|by rewrite IHp]. Qed.

Lemma pt_inst_ext σ σ' x :
  (∀ y, σ y = σ' y) → pt_inst σ x = pt_inst σ' x.
Proof. intros H. unfold pt_inst. by rewrite (pn_inst_ext σ σ'). Qed.

Lemma pup_ext m σ σ' : (∀ x, σ x = σ' x) → ∀ x, pup m σ x = pup m σ' x.
Proof. intros H x. unfold pup. case_decide; [done|]. by rewrite H. Qed.

Lemma pinst_ty_ext T : ∀ σ σ', (∀ x, σ x = σ' x) → pinst_ty σ T = pinst_ty σ' T.
Proof.
  induction T; intros σ σ' H; simpl; f_equal; auto.
  - destruct ub; simpl; [|done]. f_equal. by apply pt_inst_ext.
  - destruct lb; simpl; [|done]. f_equal. by apply pt_inst_ext.
  - apply IHT. by apply pup_ext.
  - by apply pt_inst_ext.
Qed.

Section types.
  Context (a b : chan).

  Lemma pup_swap m σ x :
    ptswap a b (pup m σ x) = pup m (ptswap a b ∘ σ) x.
  Proof.
    unfold pup. case_decide; [done|].
    rewrite pt_inst_swap. apply pt_inst_ext. done.
  Qed.

  Lemma tyswap_pinst T : ∀ σ,
    tyswap a b (pinst_ty σ T) = pinst_ty (ptswap a b ∘ σ) (tyswap a b T).
  Proof.
    induction T; intros σ; simpl; f_equal; auto.
    - destruct ub; simpl; [|done]. by rewrite pt_inst_swap.
    - destruct lb; simpl; [|done]. by rewrite pt_inst_swap.
    - rewrite IHT. apply pinst_ty_ext. intros x. apply pup_swap.
    - apply pt_inst_swap.
  Qed.

  Lemma plist_swap xs x :
    ptswap a b (plist xs x) = plist (ptswap a b <$> xs) x.
  Proof.
    unfold plist. rewrite list_lookup_fmap, length_fmap.
    by destruct (xs !! x).
  Qed.

  Lemma tyswap_ty_inst xs T :
    tyswap a b (ty_inst xs T) = ty_inst (ptswap a b <$> xs) (tyswap a b T).
  Proof.
    unfold ty_inst. rewrite tyswap_pinst. apply pinst_ty_ext.
    intros x. apply plist_swap.
  Qed.

  Lemma slots_swap x m : ptswap a b <$> slots x m = slots (ptswap a b x) m.
  Proof. unfold slots. rewrite <-list_fmap_compose. done. Qed.

  Lemma tyswap_payload_at m T x :
    tyswap a b (payload_at m T x) = payload_at m (tyswap a b T) (ptswap a b x).
  Proof. unfold payload_at. by rewrite tyswap_ty_inst, slots_swap. Qed.

  Lemma heads_swap T : heads (tyswap a b T) = set_map (ptswap a b) (heads T).
  Proof.
    induction T; simpl.
    - set_solver.
    - destruct lb; simpl; set_solver.
    - rewrite IHT1, IHT2. set_solver.
    - rewrite IHT1, IHT2. set_solver.
    - set_solver.
    - set_solver.
  Qed.

  Lemma tmap_involutive_mut :
    (∀ T, tyswap a b (tyswap a b T) = T) ∧
    (∀ s, styswap a b (styswap a b s) = s).
  Proof.
    apply ty_sty_mut_ind; intros; simpl; f_equal; auto using ptswap_involutive.
    - destruct ub; simpl; [|done]. by rewrite ptswap_involutive.
    - destruct lb; simpl; [|done]. by rewrite ptswap_involutive.
  Qed.

  Lemma tyswap_involutive T : tyswap a b (tyswap a b T) = T.
  Proof. apply tmap_involutive_mut. Qed.

  Lemma styswap_involutive s : styswap a b (styswap a b s) = s.
  Proof. apply tmap_involutive_mut. Qed.

  Lemma prim_swap T : prim T → prim (tyswap a b T).
  Proof. induction 1; simpl; constructor; auto. Qed.

  Lemma unlimited_swap T : unlimited T → unlimited (tyswap a b T).
  Proof. by destruct T. Qed.
End types.

(** Constants are typed in a world; their signatures transport along
    a transposition of the world's points. *)
Lemma konst_ty_swap a b (peq plt : point → point → Prop) k T :
  konst_ty peq plt k T →
  konst_ty (λ x y, peq (ptswap a b x) (ptswap a b y))
           (λ x y, plt (ptswap a b x) (ptswap a b y)) k (tyswap a b T).
Proof.
  destruct 1 as [S x|ub lb|m T S x xs Hl Hxs Hh|m T S x|x|S x x' Hx|n T xs Hl];
    simpl.
  - rewrite smap_dual. constructor.
  - constructor.
  - rewrite tyswap_ty_inst, ptswap_shift. constructor.
    + by rewrite length_fmap.
    + intros i y Hy. apply list_lookup_fmap_Some in Hy as (y0 & -> & Hy0).
      rewrite ptswap_slot, !ptswap_involutive. by apply Hxs.
    + intros h Hh'. rewrite <-tyswap_ty_inst, heads_swap in Hh'.
      apply elem_of_map in Hh' as (h0 & -> & Hh0).
      rewrite !ptswap_involutive. by apply Hh.
  - rewrite tyswap_payload_at, ptswap_shift. constructor.
  - constructor.
  - rewrite smap_dual. constructor. by rewrite !ptswap_involutive.
  - rewrite tyswap_ty_inst. constructor. by rewrite length_fmap.
Qed.

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

Lemma wext_inv_wsame W1 W1' N W2 W2' :
  wsame W1 W1' → wsame W2 W2' → wext_inv W1 N W2 → wext_inv W1' N W2'.
Proof.
  intros HS1 HS2 (Hx & Hn & Hold). split_and!.
  - by eapply wext_wsame.
  - destruct HS1 as (<- & _), HS2 as (<- & _). done.
  - intros x y Hx' Hy'. destruct (Hold x y Hx' Hy') as [H1 H2].
    destruct HS1 as (_ & He1 & Hl1), HS2 as (_ & He2 & Hl2).
    split; intros H; [apply He1, H1, He2, H|apply Hl1, H2, Hl2, H].
Qed.

Definition wswap (a b : chan) (W : world) : world :=
  World (set_map (pnswap a b) (w_names W))
    (λ x y, w_eq W (ptswap a b x) (ptswap a b y))
    (λ x y, w_lt W (ptswap a b x) (ptswap a b y)).

Section wswap.
  Context (a b : chan).

  Lemma elem_of_names_swap p (N : gset pname) :
    pnswap a b p ∈ (set_map (pnswap a b) N : gset pname) ↔ p ∈ N.
  Proof.
    rewrite elem_of_map. split; [|eauto].
    intros (q & Heq & Hq). apply (pnswap_inj a b) in Heq. by subst.
  Qed.

  Lemma elem_of_names_swap' p (N : gset pname) :
    p ∈ (set_map (pnswap a b) N : gset pname) ↔ pnswap a b p ∈ N.
  Proof.
    rewrite <-(elem_of_names_swap (pnswap a b p)), pnswap_involutive. done.
  Qed.

  Lemma wswap_eq W x y :
    w_eq (wswap a b W) (ptswap a b x) (ptswap a b y) ↔ w_eq W x y.
  Proof. simpl. by rewrite !ptswap_involutive. Qed.

  Lemma wswap_lt W x y :
    w_lt (wswap a b W) (ptswap a b x) (ptswap a b y) ↔ w_lt W x y.
  Proof. simpl. by rewrite !ptswap_involutive. Qed.

  Lemma wswap_wf W : world_wf W → world_wf (wswap a b W).
  Proof.
    intros HW. split; simpl; intros *.
    - apply HW.
    - apply HW.
    - apply HW.
    - rewrite !ptswap_shift. apply HW.
    - rewrite !ptswap_slot. apply HW.
    - apply HW.
    - apply HW.
    - rewrite ptswap_shift. apply HW.
    - intros H. apply (wf_eq_supp _ HW) in H as [H|[Hx Hy]].
      + left. by apply (ptswap_inj a b).
      + right. rewrite !elem_of_names_swap', <-!pt_root_swap. done.
    - intros H. apply (wf_lt_supp _ HW) in H as [[Hn Ho]|[Hx Hy]].
      + left. split; [|done]. by apply (pnswap_inj a b).
      + right. rewrite !elem_of_names_swap', <-!pt_root_swap. done.
  Qed.

  Lemma wswap_strict W : strict W → strict (wswap a b W).
  Proof. intros [HW Hi]. split; [by apply wswap_wf|]. intros x. apply Hi. Qed.

  Lemma wswap_wswap W : wsame (wswap a b (wswap a b W)) W.
  Proof.
    split_and!; simpl.
    - apply set_eq. intros p. rewrite !elem_of_names_swap', pnswap_involutive.
      done.
    - intros. by rewrite !ptswap_involutive.
    - intros. by rewrite !ptswap_involutive.
  Qed.

  Lemma wswap_wsame W1 W2 : wsame W1 W2 → wsame (wswap a b W1) (wswap a b W2).
  Proof.
    intros (Hn & He & Hl). split_and!; simpl; [by rewrite Hn|..]; intros; auto.
  Qed.

  Lemma wext_wswap W W' : wext W W' → wext (wswap a b W) (wswap a b W').
  Proof.
    intros (Hn & He & Hl & Hs). split_and!; simpl; auto.
    - intros p. simpl. rewrite !elem_of_names_swap'. set_solver.
    - by apply wswap_strict.
  Qed.

  Lemma wext_fresh_wswap W N W' :
    wext_fresh W N W' →
    wext_fresh (wswap a b W) (set_map (pnswap a b) N) (wswap a b W').
  Proof.
    intros (Hx & HN & Hn & Hold). split_and!.
    - by apply wext_wswap.
    - apply elem_of_disjoint. intros p H1 H2. simpl in H2.
      apply elem_of_names_swap' in H1, H2. set_solver.
    - simpl. apply set_eq. intros p.
      rewrite elem_of_union, !elem_of_names_swap', Hn. set_solver.
    - intros x y Hx' Hy'. simpl.
      rewrite elem_of_names_swap', <-pt_root_swap in Hx', Hy'.
      by apply Hold.
  Qed.

  Lemma wext_inv_wswap W N W' :
    wext_inv W N W' →
    wext_inv (wswap a b W) (set_map (pnswap a b) N) (wswap a b W').
  Proof.
    intros (Hx & Hn & Hold). split_and!.
    - by apply wext_wswap.
    - simpl. intros p. rewrite elem_of_union, !elem_of_names_swap'.
      intros Hp. apply Hn in Hp. set_solver.
    - intros x y Hx' Hy'. simpl.
      rewrite elem_of_names_swap', <-pt_root_swap in Hx', Hy'.
      by apply Hold.
  Qed.

  Lemma lb_below_swap W lb H :
    lb_below W lb H →
    lb_below (wswap a b W) (ptswap a b <$> lb) (set_map (ptswap a b) H).
  Proof.
    destruct lb as [x|]; simpl.
    - intros Hb y Hy. apply elem_of_map in Hy as (y0 & -> & Hy0).
      unfold w_le. simpl. rewrite !ptswap_involutive. by apply Hb.
    - intros ->. set_solver.
  Qed.

  Lemma ub_below_swap W ub F :
    ub_below W ub F →
    ub_below (wswap a b W) (ptswap a b <$> ub) (set_map (ptswap a b) F).
  Proof.
    destruct ub as [x|]; simpl; [|done].
    intros Hb y Hy. apply elem_of_map in Hy as (y0 & -> & Hy0).
    rewrite !ptswap_involutive. by apply Hb.
  Qed.
End wswap.

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

Lemma gswap_intersection a b C1 C2 :
  gswap a b (C1 ∩ C2) = gswap a b C1 ∩ gswap a b C2.
Proof.
  apply set_eq; intros c.
  rewrite elem_of_intersection, !elem_of_gswap', elem_of_intersection. done.
Qed.

Global Instance cswap_inj_inst a b : Inj (=) (=) (cswap a b).
Proof. intros x y. apply cswap_inj. Qed.

Definition entswap (a b : chan) (e : sty * nat) : sty * nat :=
  (styswap a b e.1, e.2).

Definition endsswap (a b : chan) (o : ends) : ends :=
  match o with
  | One e => One (entswap a b e)
  | Both e1 e2 => Both (entswap a b e1) (entswap a b e2)
  end.

Definition tenvswap (a b : chan) (Θ : tenv) : tenv :=
  kmap (cswap a b) (endsswap a b <$> Θ).

Definition senvswap (a b : chan) (Σ : senv) : senv :=
  kmap (cswap a b) (entswap a b <$> Σ).

Definition kswap (a b : chan) (k : ekey) : ekey := (cswap a b k.1, k.2).

Section envs.
  Context (a b : chan).

  Lemma entswap_involutive e : entswap a b (entswap a b e) = e.
  Proof. destruct e. unfold entswap. simpl. by rewrite styswap_involutive. Qed.

  Lemma endsswap_involutive o : endsswap a b (endsswap a b o) = o.
  Proof. destruct o; simpl; by rewrite !entswap_involutive. Qed.

  Lemma lookup_tenvswap Θ c :
    tenvswap a b Θ !! cswap a b c = endsswap a b <$> Θ !! c.
  Proof. unfold tenvswap. by rewrite (lookup_kmap (cswap a b)), lookup_fmap. Qed.

  Lemma lookup_tenvswap' Θ c :
    tenvswap a b Θ !! c = endsswap a b <$> Θ !! cswap a b c.
  Proof.
    rewrite <-(cswap_involutive a b c) at 1. by rewrite lookup_tenvswap.
  Qed.

  Lemma lookup_senvswap Σ c :
    senvswap a b Σ !! cswap a b c = entswap a b <$> Σ !! c.
  Proof. unfold senvswap. by rewrite (lookup_kmap (cswap a b)), lookup_fmap. Qed.

  Lemma lookup_senvswap' Σ c :
    senvswap a b Σ !! c = entswap a b <$> Σ !! cswap a b c.
  Proof.
    rewrite <-(cswap_involutive a b c) at 1. by rewrite lookup_senvswap.
  Qed.

  Lemma tenvswap_involutive Θ : tenvswap a b (tenvswap a b Θ) = Θ.
  Proof.
    apply map_eq. intros c. rewrite !lookup_tenvswap', cswap_involutive.
    destruct (Θ !! c); simpl; [by rewrite endsswap_involutive|done].
  Qed.

  Lemma senvswap_involutive Σ : senvswap a b (senvswap a b Σ) = Σ.
  Proof.
    apply map_eq. intros c. rewrite !lookup_senvswap', cswap_involutive.
    destruct (Σ !! c); simpl; [by rewrite entswap_involutive|done].
  Qed.

  Lemma dom_tenvswap Θ : dom (tenvswap a b Θ) = gswap a b (dom Θ).
  Proof.
    apply set_eq. intros c. rewrite elem_of_gswap', !elem_of_dom.
    rewrite lookup_tenvswap'. by destruct (Θ !! _).
  Qed.

  Lemma dom_senvswap Σ : dom (senvswap a b Σ) = gswap a b (dom Σ).
  Proof.
    apply set_eq. intros c. rewrite elem_of_gswap', !elem_of_dom.
    rewrite lookup_senvswap'. by destruct (Σ !! _).
  Qed.

  Lemma tenvswap_empty : tenvswap a b ∅ = ∅.
  Proof. apply map_eq. intros c. by rewrite lookup_tenvswap', !lookup_empty. Qed.

  Lemma senvswap_empty : senvswap a b ∅ = ∅.
  Proof. apply map_eq. intros c. by rewrite lookup_senvswap', !lookup_empty. Qed.

  Lemma tenvswap_insert Θ c o :
    tenvswap a b (<[c := o]> Θ) = <[cswap a b c := endsswap a b o]> (tenvswap a b Θ).
  Proof.
    apply map_eq. intros d. rewrite lookup_tenvswap'.
    destruct (decide (d = cswap a b c)) as [->|Hd].
    - by rewrite cswap_involutive, !lookup_insert_eq.
    - rewrite !lookup_insert_ne; [by rewrite lookup_tenvswap'|done|].
      intros ->. apply Hd. by rewrite cswap_involutive.
  Qed.

  Lemma senvswap_insert Σ c e :
    senvswap a b (<[c := e]> Σ) = <[cswap a b c := entswap a b e]> (senvswap a b Σ).
  Proof.
    apply map_eq. intros d. rewrite lookup_senvswap'.
    destruct (decide (d = cswap a b c)) as [->|Hd].
    - by rewrite cswap_involutive, !lookup_insert_eq.
    - rewrite !lookup_insert_ne; [by rewrite lookup_senvswap'|done|].
      intros ->. apply Hd. by rewrite cswap_involutive.
  Qed.

  Lemma tenvswap_singleton c o :
    tenvswap a b {[c := o]} = {[cswap a b c := endsswap a b o]}.
  Proof. by rewrite <-!insert_empty, tenvswap_insert, tenvswap_empty. Qed.

  Lemma senvswap_union Σ1 Σ2 :
    senvswap a b (Σ1 ∪ Σ2) = senvswap a b Σ1 ∪ senvswap a b Σ2.
  Proof.
    apply map_eq. intros c. rewrite lookup_union, !lookup_senvswap', lookup_union.
    by destruct (Σ1 !! _), (Σ2 !! _).
  Qed.

  Lemma tenvswap_union Θ1 Θ2 :
    tenvswap a b (Θ1 ∪ Θ2) = tenvswap a b Θ1 ∪ tenvswap a b Θ2.
  Proof.
    apply map_eq. intros c. rewrite lookup_union, !lookup_tenvswap', lookup_union.
    by destruct (Θ1 !! _), (Θ2 !! _).
  Qed.

  Lemma senvswap_difference Σ1 Σ2 :
    senvswap a b (Σ1 ∖ Σ2) = senvswap a b Σ1 ∖ senvswap a b Σ2.
  Proof.
    apply map_eq. intros c. rewrite lookup_difference, !lookup_senvswap',
      lookup_difference.
    by destruct (Σ1 !! _), (Σ2 !! _).
  Qed.

  Lemma senvswap_disjoint Σ1 Σ2 :
    Σ1 ##ₘ Σ2 → senvswap a b Σ1 ##ₘ senvswap a b Σ2.
  Proof.
    intros Hd c. rewrite !lookup_senvswap'. specialize (Hd (cswap a b c)).
    by destruct (Σ1 !! _), (Σ2 !! _).
  Qed.

  Lemma tenvswap_disjoint Θ1 Θ2 :
    Θ1 ##ₘ Θ2 → tenvswap a b Θ1 ##ₘ tenvswap a b Θ2.
  Proof.
    intros Hd c. rewrite !lookup_tenvswap'. specialize (Hd (cswap a b c)).
    by destruct (Θ1 !! _), (Θ2 !! _).
  Qed.

  Lemma tenvswap_of Σ : tenvswap a b (tenv_of Σ) = tenv_of (senvswap a b Σ).
  Proof.
    apply map_eq. intros c. unfold tenv_of.
    rewrite lookup_tenvswap', !lookup_fmap, lookup_senvswap'.
    by destruct (Σ !! _).
  Qed.

  Lemma tenv_ones_swap Θ : tenv_ones (tenvswap a b Θ) = senvswap a b (tenv_ones Θ).
  Proof.
    apply map_eq. intros c. unfold tenv_ones.
    rewrite lookup_omap, lookup_tenvswap', lookup_senvswap', lookup_omap.
    by destruct (Θ !! _) as [[]|].
  Qed.

  Lemma tenv_entry_swap Θ k :
    tenv_entry (tenvswap a b Θ) (kswap a b k) = entswap a b <$> tenv_entry Θ k.
  Proof.
    destruct k as [c s]. unfold tenv_entry, kswap. simpl.
    rewrite lookup_tenvswap. by destruct (Θ !! c) as [[]|], s.
  Qed.

  Lemma tenv_entry_swap' Θ k :
    tenv_entry (tenvswap a b Θ) k = entswap a b <$> tenv_entry Θ (kswap a b k).
  Proof.
    destruct k as [c s]. rewrite <-(cswap_involutive a b c) at 1.
    apply (tenv_entry_swap Θ (cswap a b c, s)).
  Qed.

  Lemma kswap_involutive k : kswap a b (kswap a b k) = k.
  Proof. destruct k. unfold kswap. simpl. by rewrite cswap_involutive. Qed.

  Lemma entry_head_swap k e :
    entry_head (kswap a b k) (entswap a b e) = ptswap a b (entry_head k e).
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

  Lemma ends_heads_swap c o :
    ends_heads (cswap a b c) (endsswap a b o) = set_map (ptswap a b) (ends_heads c o).
  Proof.
    apply set_eq. intros x. rewrite elem_of_map.
    destruct o as [e|e1 e2]; simpl; split.
    - intros ->%elem_of_singleton. exists (pt_chan c e.2).
      split; [done|by apply elem_of_singleton].
    - intros (y & -> & ->%elem_of_singleton). by apply elem_of_singleton.
    - rewrite elem_of_union, !elem_of_singleton. intros [->| ->].
      + exists (pt_chan c e1.2). split; [done|]. apply elem_of_union; left.
        by apply elem_of_singleton.
      + exists (pt_chan c e2.2). split; [done|]. apply elem_of_union; right.
        by apply elem_of_singleton.
    - intros (y & -> & Hy). apply elem_of_union in Hy as [->%elem_of_singleton| ->%elem_of_singleton];
        apply elem_of_union; [left|right]; by apply elem_of_singleton.
  Qed.

  Lemma tenv_heads_swap Θ :
    tenv_heads (tenvswap a b Θ) = set_map (ptswap a b) (tenv_heads Θ).
  Proof.
    apply set_eq. intros x. rewrite elem_of_map, elem_of_tenv_heads. split.
    - intros (c & o & Hc & Hx). rewrite lookup_tenvswap' in Hc.
      destruct (Θ !! cswap a b c) as [o0|] eqn:Ho; [|done]. injection Hc as <-.
      rewrite <-(cswap_involutive a b c), ends_heads_swap in Hx.
      apply elem_of_map in Hx as (x0 & -> & Hx0). exists x0. split; [done|].
      apply elem_of_tenv_heads. eauto.
    - intros (x0 & -> & Hx0). apply elem_of_tenv_heads in Hx0 as (c & o & Hc & Hx).
      exists (cswap a b c), (endsswap a b o). split.
      + by rewrite lookup_tenvswap, Hc.
      + rewrite ends_heads_swap. by apply elem_of_map_2.
  Qed.

  (** The relations between environments. *)

  Lemma unfoldS_swap s : unfoldS (styswap a b s) = styswap a b (unfoldS s).
  Proof. by rewrite smap_unfoldS. Qed.

  Lemma tenv_join_swap Θ Θ1 Θ2 :
    tenv_join Θ Θ1 Θ2 → tenv_join (tenvswap a b Θ) (tenvswap a b Θ1) (tenvswap a b Θ2).
  Proof.
    intros H c. rewrite !lookup_tenvswap'. specialize (H (cswap a b c)).
    inversion H; simpl; constructor.
  Qed.

  Lemma tenv_comp_swap Θ Θ1 Θ2 :
    tenv_comp Θ Θ1 Θ2 → tenv_comp (tenvswap a b Θ) (tenvswap a b Θ1) (tenvswap a b Θ2).
  Proof.
    intros [Hj Hd]. split; [by apply tenv_join_swap|].
    intros c e1 e2 H1 H2. rewrite lookup_tenvswap' in H1, H2.
    destruct (Θ1 !! _) as [[]|] eqn:E1; try done.
    destruct (Θ2 !! _) as [[]|] eqn:E2; try done.
    injection H1 as <-. injection H2 as <-.
    destruct (Hd _ _ _ E1 E2) as [? ?]. simpl. split; [done|]. by apply sdual_smap.
  Qed.

  Lemma tenv_ext_swap Θ1 c e Θ :
    tenv_ext Θ1 c e Θ →
    tenv_ext (tenvswap a b Θ1) (cswap a b c) (entswap a b e) (tenvswap a b Θ).
  Proof.
    intros [[H1 ->]|(e' & H1 & [->| ->])].
    - left. rewrite lookup_tenvswap, H1. split; [done|]. by rewrite tenvswap_insert.
    - right. exists (entswap a b e'). rewrite lookup_tenvswap, H1.
      split; [done|]. left. by rewrite tenvswap_insert.
    - right. exists (entswap a b e'). rewrite lookup_tenvswap, H1.
      split; [done|]. right. by rewrite tenvswap_insert.
  Qed.

  Lemma tenv_hd_swap Θ c u k Θ1 :
    tenv_hd Θ c u k Θ1 →
    tenv_hd (tenvswap a b Θ) (cswap a b c) (styswap a b u) k (tenvswap a b Θ1).
  Proof.
    intros (s & Hext & Hu). exists (styswap a b s). split.
    - apply (tenv_ext_swap _ _ (s, k)). done.
    - by rewrite unfoldS_swap, Hu.
  Qed.

  Lemma tenv_dual_swap Θ : tenv_dual Θ → tenv_dual (tenvswap a b Θ).
  Proof.
    intros H c e1 e2 He. rewrite lookup_tenvswap' in He.
    destruct (Θ !! _) as [[]|] eqn:E; try done. injection He as <- <-.
    destruct (H _ _ _ E). simpl. split; [done|]. by apply sdual_smap.
  Qed.

  Lemma senv_hd_swap Σ c u k Σ1 :
    senv_hd Σ c u k Σ1 →
    senv_hd (senvswap a b Σ) (cswap a b c) (styswap a b u) k (senvswap a b Σ1).
  Proof.
    intros (s & -> & Hu). exists (styswap a b s).
    rewrite senvswap_insert. split; [done|]. by rewrite unfoldS_swap, Hu.
  Qed.

  Lemma senv_dual_on_swap Σ1 Σ2 :
    senv_dual_on Σ1 Σ2 → senv_dual_on (senvswap a b Σ1) (senvswap a b Σ2).
  Proof.
    intros H c e1 e2 H1 H2. rewrite lookup_senvswap' in H1, H2.
    destruct (Σ1 !! _) eqn:E1, (Σ2 !! _) eqn:E2; try done.
    injection H1 as <-. injection H2 as <-.
    destruct (H _ _ _ E1 E2). simpl. split; [done|]. by apply sdual_smap.
  Qed.

  Lemma recv_back_swap Σr Θ2 :
    recv_back (senvswap a b Σr) (tenvswap a b Θ2) = gswap a b (recv_back Σr Θ2).
  Proof.
    unfold recv_back. rewrite tenv_ones_swap, dom_tenvswap, !dom_senvswap.
    by rewrite gswap_union, gswap_intersection, gswap_difference.
  Qed.

  Lemma recv_env_swap Σr Θ2 :
    recv_env (senvswap a b Σr) (tenvswap a b Θ2) = senvswap a b (recv_env Σr Θ2).
  Proof.
    unfold recv_env. by rewrite tenv_ones_swap, senvswap_union, !senvswap_difference.
  Qed.

  Lemma recv_ok_swap W Σr Θ2 :
    recv_ok W Σr Θ2 → recv_ok (wswap a b W) (senvswap a b Σr) (tenvswap a b Θ2).
  Proof.
    intros (Hd & Ht & Hb & Hf). split_and!.
    - rewrite tenv_ones_swap. by apply senv_dual_on_swap.
    - by apply tenv_dual_swap.
    - rewrite tenv_ones_swap, dom_tenvswap, !dom_senvswap, <-gswap_difference.
      by apply gswap_disjoint_iff.
    - intros c. rewrite tenv_ones_swap, !dom_senvswap, !elem_of_gswap'.
      intros H1 H2 H3. simpl in H3. apply elem_of_names_swap' in H3.
      simpl in H3. by apply (Hf _ H1 H2).
  Qed.

  Lemma send_split_swap Σe Θe :
    send_split Σe Θe → send_split (senvswap a b Σe) (tenvswap a b Θe).
  Proof.
    intros [Hsub H]. split.
    - rewrite dom_senvswap, dom_tenvswap. intros c. rewrite !elem_of_gswap'. auto.
    - intros r o Hr. rewrite lookup_tenvswap' in Hr.
      destruct (Θe !! _) as [o0|] eqn:E; [|done]. injection Hr as <-.
      specialize (H _ _ E). destruct o0 as [e'|e1 e2]; simpl.
      + destruct H as (e & He & ? & ?). exists (entswap a b e).
        rewrite lookup_senvswap', He. split_and!; [done|done|]. by apply sdual_smap.
      + destruct H as (He & ? & ?). rewrite lookup_senvswap', He.
        split_and!; [done|done|]. by apply sdual_smap.
  Qed.
End envs.

(** ** Readiness and frames *)

Section ready.
  Context (a b : chan).

  Lemma slswap_involutive σ : slswap a b (slswap a b σ) = σ.
  Proof.
    destruct σ; simpl; by rewrite ?cswap_involutive, ?eswap_involutive,
      ?gswap_involutive.
  Qed.

  Lemma tlswap_involutive α : tlswap a b (tlswap a b α) = α.
  Proof.
    destruct α; simpl; by rewrite ?slswap_involutive, ?cswap_involutive,
      ?eswap_involutive.
  Qed.

  Lemma selects_swap Θ σ k :
    selects Θ σ k → selects (tenvswap a b Θ) (slswap a b σ) (kswap a b k).
  Proof.
    destruct σ as [c v|c v|c|cd]; simpl.
    - intros (Hk & e & m & T & s & He & Hu). split; [by rewrite Hk|].
      exists (entswap a b e), m, (tyswap a b T), (styswap a b s).
      rewrite tenv_entry_swap, He. split; [done|]. simpl.
      by rewrite unfoldS_swap, Hu.
    - intros (Hk & e & m & T & s & He & Hu). split; [by rewrite Hk|].
      exists (entswap a b e), m, (tyswap a b T), (styswap a b s).
      rewrite tenv_entry_swap, He. split; [done|]. simpl.
      by rewrite unfoldS_swap, Hu.
    - intros (Hk & e & He & Hu & Ht). split; [by rewrite Hk|].
      exists (entswap a b e). rewrite tenv_entry_swap, He.
      split_and!; [done|simpl; by rewrite unfoldS_swap, Hu|].
      intros Hk2 e' He'. simpl in Hk2.
      pose proof (tenv_entry_swap a b Θ (c, false)) as Hs. unfold kswap in Hs.
      simpl in Hs. rewrite He' in Hs.
      destruct (tenv_entry Θ (c, false)) as [e0|] eqn:E0; [|done].
      injection Hs as ->. simpl. rewrite unfoldS_swap. intros Hend.
      apply (Ht Hk2 e0); [done|].
      rewrite <-(styswap_involutive a b (unfoldS e0.1)), Hend. done.
    - intros (Hk & He). split.
      + by apply elem_of_gswap.
      + rewrite tenv_entry_swap. destruct He as [e He]. rewrite He. by eexists.
  Qed.

  Lemma offered_t_swap Θ t k :
    offered_t Θ t k → offered_t (tenvswap a b Θ) (eswap a b t) (kswap a b k).
  Proof.
    intros (σ & t' & Hst & Hs). exists (slswap a b σ), (eswap a b t').
    split; [exact (tstep_eswap a b _ _ _ Hst)|]. by apply selects_swap.
  Qed.

  Lemma offered_t_swap_iff Θ t k :
    offered_t (tenvswap a b Θ) (eswap a b t) k ↔ offered_t Θ t (kswap a b k).
  Proof.
    split.
    - intros H. apply offered_t_swap in H.
      by rewrite tenvswap_involutive, eswap_involutive in H.
    - intros H. apply offered_t_swap in H. by rewrite kswap_involutive in H.
  Qed.

  Lemma offered_p_swap Σ p k :
    offered_p Σ p k → offered_p (senvswap a b Σ) (pswap a b p) (kswap a b k).
  Proof.
    intros (σ & p' & Hst & Hs). exists (slswap a b σ), (pswap a b p').
    split; [exact (proc_step_pswap a b _ _ _ Hst)|].
    rewrite <-tenvswap_of. by apply selects_swap.
  Qed.

  Lemma offered_p_swap_iff Σ p k :
    offered_p (senvswap a b Σ) (pswap a b p) k ↔ offered_p Σ p (kswap a b k).
  Proof.
    split.
    - intros H. apply offered_p_swap in H.
      by rewrite senvswap_involutive, pswap_involutive in H.
    - intros H. apply offered_p_swap in H. by rewrite kswap_involutive in H.
  Qed.

  Lemma stable_t_swap t : stable_t t → stable_t (eswap a b t).
  Proof.
    intros H α t' Hst. apply (tstep_eswap a b) in Hst.
    rewrite eswap_involutive in Hst. specialize (H _ _ Hst).
    by destruct α.
  Qed.

  Lemma stable_p_swap p : stable_p p → stable_p (pswap a b p).
  Proof.
    intros H p' Hst. apply (proc_step_pswap a b) in Hst.
    rewrite pswap_involutive in Hst. exact (H _ Hst).
  Qed.

  Lemma irred_swap e : irred e → irred (eswap a b e).
  Proof.
    intros H α e' Hst. apply (tstep_eswap a b) in Hst.
    rewrite eswap_involutive in Hst. exact (H _ _ Hst).
  Qed.

  Lemma pirred_swap p : pirred p → pirred (pswap a b p).
  Proof.
    intros H π p' Hst. apply (proc_step_pswap a b) in Hst.
    rewrite pswap_involutive in Hst. exact (H _ _ Hst).
  Qed.

  Lemma above_offered_swap W Θ (off off' : ekey → Prop) :
    (∀ k, off' k ↔ off (kswap a b k)) →
    above_offered W Θ off →
    above_offered (wswap a b W) (tenvswap a b Θ) off'.
  Proof.
    intros Hoff H k e He Hk. rewrite tenv_entry_swap' in He.
    destruct (tenv_entry Θ (kswap a b k)) as [e0|] eqn:E0; [|done].
    injection He as <-. rewrite Hoff in Hk.
    destruct (H _ _ E0 Hk) as (k' & e' & Ho & He' & Hlt).
    exists (kswap a b k'), (entswap a b e'). split_and!.
    - by rewrite Hoff, kswap_involutive.
    - by rewrite tenv_entry_swap, He'.
    - rewrite <-(kswap_involutive a b k). rewrite !entry_head_swap.
      by apply wswap_lt.
  Qed.

  Lemma ready_t_swap W Θ t :
    ready_t W Θ t → ready_t (wswap a b W) (tenvswap a b Θ) (eswap a b t).
  Proof.
    intros H Hs. apply (stable_t_swap) in Hs. rewrite eswap_involutive in Hs.
    destruct (H Hs) as [Hv Ha]. split.
    - intros Hno. rewrite is_val_eswap. apply Hv. intros k Hk.
      apply (Hno (kswap a b k)). by rewrite offered_t_swap_iff, kswap_involutive.
    - apply (above_offered_swap _ _ (offered_t Θ t)); [|done].
      intros k. apply offered_t_swap_iff.
  Qed.

  Lemma ready_p_swap W Σ p :
    ready_p W Σ p → ready_p (wswap a b W) (senvswap a b Σ) (pswap a b p).
  Proof.
    intros H Hs. apply stable_p_swap in Hs. rewrite pswap_involutive in Hs.
    destruct (H Hs) as [Hv Ha]. split.
    - intros Hno. apply terminated_pswap. apply Hv. intros k Hk.
      apply (Hno (kswap a b k)). by rewrite offered_p_swap_iff, kswap_involutive.
    - rewrite <-tenvswap_of.
      apply (above_offered_swap _ _ (offered_p Σ p)); [|done].
      intros k. apply offered_p_swap_iff.
  Qed.

  Lemma frame_t_swap W Θ t F :
    frame_t W Θ t F →
    frame_t (wswap a b W) (tenvswap a b Θ) (eswap a b t) (set_map (ptswap a b) F).
  Proof.
    intros H Hs k e Ho He y Hy. apply stable_t_swap in Hs.
    rewrite eswap_involutive in Hs.
    rewrite offered_t_swap_iff in Ho. rewrite tenv_entry_swap' in He.
    destruct (tenv_entry Θ (kswap a b k)) as [e0|] eqn:E0; [|done].
    injection He as <-. apply elem_of_map in Hy as (y0 & -> & Hy0).
    rewrite <-(kswap_involutive a b k), entry_head_swap. apply wswap_lt.
    by apply (H Hs _ _ Ho E0).
  Qed.

  Lemma tau_link_alias_swap W' Σ p p' :
    tau_link_alias W' Σ p p' →
    tau_link_alias (wswap a b W') (senvswap a b Σ) (pswap a b p) (pswap a b p').
  Proof.
    intros H E e c d e' Hp Hst Hc Hd Hp'.
    assert (p.2 = msswap a b E ⊎ {[+ eswap a b e +]}) as Hp0.
    { rewrite <-(msswap_involutive a b p.2). destruct p; simpl in *.
      by rewrite Hp, msswap_disj_union, msswap_singleton. }
    apply (tstep_eswap a b) in Hst. simpl in Hst. rewrite gswap_upair in Hst.
    rewrite dom_senvswap, elem_of_gswap' in Hc.
    destruct p as [C0 E0]; simpl in *. rewrite elem_of_gswap' in Hd.
    assert (p' = (C0 ∖ {[cswap a b d]},
                  echsubst (cswap a b d) (cswap a b c)
                    (msswap a b E ⊎ {[+ eswap a b e' +]}))) as Hp''.
    { rewrite <-(pswap_involutive a b p'), Hp'. unfold pswap; simpl.
      rewrite gswap_difference, gswap_singleton, gswap_involutive,
        echsubst_msswap, msswap_disj_union, msswap_singleton. done. }
    destruct (H _ _ _ _ _ Hp0 Hst Hc Hd Hp'') as (s & k & j & Hs & Hw).
    exists (styswap a b s), k, j. split.
    - by rewrite lookup_senvswap', Hs.
    - simpl. by rewrite !ptswap_chan.
  Qed.
End ready.

(** World equivalence leaves readiness, frames and aliases alone. *)
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

Lemma tau_link_alias_wsame W1 W2 Σ p p' :
  wsame W1 W2 → tau_link_alias W1 Σ p p' → tau_link_alias W2 Σ p p'.
Proof.
  intros (_ & He & _) H E e c d e' ? ? ? ? ?.
  destruct (H E e c d e') as (s & k & j & ? & ?); [done..|].
  exists s, k, j. split; [done|]. by apply He.
Qed.

(** ** Small transport facts used by the main lemma *)

Section misc.
  Context (a b : chan).

  Lemma opt_ptswap_involutive (o : option point) :
    ptswap a b <$> (ptswap a b <$> o) = o.
  Proof. destruct o; simpl; by rewrite ?ptswap_involutive. Qed.

  Lemma list_ptswap_involutive (xs : list point) :
    ptswap a b <$> (ptswap a b <$> xs) = xs.
  Proof.
    rewrite <-list_fmap_compose. rewrite <-(list_fmap_id xs) at 2.
    apply list_fmap_ext. intros. apply ptswap_involutive.
  Qed.

  Lemma set_ptswap_involutive (F : gset point) :
    set_map (ptswap a b) (set_map (ptswap a b) F : gset point) = F.
  Proof.
    apply set_eq. intros x. rewrite !elem_of_map. split.
    - intros (y & -> & Hy). apply elem_of_map in Hy as (z & -> & Hz).
      by rewrite ptswap_involutive.
    - intros Hx. exists (ptswap a b x). split; [by rewrite ptswap_involutive|].
      apply elem_of_map. exists x. done.
  Qed.

  Lemma set_ptswap_empty : set_map (ptswap a b) (∅ : gset point) = (∅ : gset point).
  Proof. apply set_eq. intros x. rewrite elem_of_map. set_solver. Qed.

  Lemma names_nchan_swap (X : gset chan) :
    (set_map (pnswap a b) (set_map NChan X : gset pname) : gset pname)
    = set_map NChan (gswap a b X).
  Proof.
    apply set_eq. intros p. rewrite !elem_of_map. split.
    - intros (q & -> & Hq). apply elem_of_map in Hq as (c & -> & Hc).
      exists (cswap a b c). split; [done|]. by apply elem_of_gswap.
    - intros (c & -> & Hc). exists (NChan (cswap a b c)).
      split; [simpl; by rewrite cswap_involutive|].
      apply elem_of_map. exists (cswap a b c). split; [done|].
      by apply elem_of_gswap'.
  Qed.

  Lemma nchan_names_swap W c :
    NChan (cswap a b c) ∈ w_names (wswap a b W) ↔ NChan c ∈ w_names W.
  Proof. apply (elem_of_names_swap a b (NChan c)). Qed.

  Lemma names_singleton_swap c :
    (set_map (pnswap a b) ({[NChan c]} : gset pname) : gset pname)
    = {[NChan (cswap a b c)]}.
  Proof. rewrite set_map_singleton_L. done. Qed.

  Lemma msswap_elem e E : e ∈ msswap a b E → ∃ e0, e = eswap a b e0 ∧ e0 ∈ E.
  Proof. apply elem_of_gmultiset_map. Qed.

  Lemma tstep_eswap_inv' e α e'' :
    tstep (eswap a b e) α e'' →
    tstep e (tlswap a b α) (eswap a b e'').
  Proof.
    intros H. apply (tstep_eswap a b) in H. by rewrite eswap_involutive in H.
  Qed.

  Lemma proc_step_pswap_inv' p π q :
    proc_step (pswap a b p) π q → proc_step p (plswap a b π) (pswap a b q).
  Proof.
    intros H. apply (proc_step_pswap a b) in H. by rewrite pswap_involutive in H.
  Qed.
End misc.

Lemma recv_ok_wsame W1 W2 Σr Θ2 :
  wsame W1 W2 → recv_ok W1 Σr Θ2 → recv_ok W2 Σr Θ2.
Proof.
  intros (Hn & _) (? & ? & ? & Hf). split_and!; [done..|].
  rewrite <-Hn. done.
Qed.

Lemma konst_ty_wsame W1 W2 k T :
  wsame W1 W2 → konst_ty (w_eq W1) (w_lt W1) k T → konst_ty (w_eq W2) (w_lt W2) k T.
Proof.
  intros (_ & He & Hl). apply konst_ty_mono; intros; [by apply He|by apply Hl].
Qed.

Lemma wext_swap_back a b W W' W'' :
  wsame (wswap a b W) W' → wext W' W'' → wext W (wswap a b W'').
Proof.
  intros HS Hx. apply (wext_wswap a b) in Hx.
  eapply wext_wsame; [|apply wsame_refl|exact Hx].
  eapply wsame_trans; [apply wswap_wsame, wsame_sym, HS|apply wswap_wswap].
Qed.

(** ** The relations are equivariant

    One induction on the step index carries all three relations. The
    target world is any world equivalent to the transposed one, so that
    the round trip through a transposition (which is the identity only
    up to equivalence) closes. *)

Lemma rel_swap a b n :
  (∀ W W' Θ T v, wsame (wswap a b W) W' → Vrel n W Θ T v →
     Vrel n W' (tenvswap a b Θ) (tyswap a b T) (eswap a b v)) ∧
  (∀ W W' Θ T F e, wsame (wswap a b W) W' → Erel n W Θ T F e →
     Erel n W' (tenvswap a b Θ) (tyswap a b T) (set_map (ptswap a b) F)
       (eswap a b e)) ∧
  (∀ W W' Σ T p, wsame (wswap a b W) W' → Prel n W Σ T p →
     Prel n W' (senvswap a b Σ) (tyswap a b T) (pswap a b p)).
Proof.
  induction n as [n IHn] using lt_wf_ind.
  assert (∀ j, j < n → ∀ W W' Θ T v, wsame (wswap a b W) W' → Vrel j W Θ T v →
            Vrel j W' (tenvswap a b Θ) (tyswap a b T) (eswap a b v)) as IHV
    by (intros j Hj; apply (IHn j Hj)).
  assert (∀ j, j < n → ∀ W W' Θ T F e, wsame (wswap a b W) W' →
            Erel j W Θ T F e →
            Erel j W' (tenvswap a b Θ) (tyswap a b T) (set_map (ptswap a b) F)
              (eswap a b e)) as IHE
    by (intros j Hj; apply (IHn j Hj)).
  assert (∀ j, j < n → ∀ W W' Σ T p, wsame (wswap a b W) W' → Prel j W Σ T p →
            Prel j W' (senvswap a b Σ) (tyswap a b T) (pswap a b p)) as IHP
    by (intros j Hj; apply (IHn j Hj)).
  (* the round trip: back to the source of a transposition *)
  assert (∀ W'', wsame (wswap a b (wswap a b W'')) W'') as Hrt
    by (intros; apply wswap_wswap).
  assert (∀ W W' Θ T v, wsame (wswap a b W) W' → Vrel n W Θ T v →
            Vrel n W' (tenvswap a b Θ) (tyswap a b T) (eswap a b v)) as HV.
  { intros W W' Θ T. revert Θ.
    induction T as [|ub lb T1 IHT1 U IHU|T1 IHT1 U IHU|T1 IHT1 U IHU|m T1 IHT1|s x];
      intros Θ v HS HVv; simpl.
    - apply Vrel_unit_iff in HVv as [-> ->].
      apply Vrel_unit_iff. by rewrite tenvswap_empty.
    - apply Vrel_lolli_iff in HVv
        as [(eb & -> & Hfc & Hlb & H)|(k & T0 & -> & -> & Hk & Ht)].
      + apply Vrel_lolli_iff. left. exists (eswap a b eb). split_and!.
        * done.
        * by rewrite fchans_eswap, dom_tenvswap, Hfc.
        * rewrite tenv_heads_swap. eapply lb_below_wsame; [exact HS|].
          by apply lb_below_swap.
        * intros W'' j Θ' Θ'' w F Hx Hj Hc HVw Hub.
          assert (wext W (wswap a b W'')) as Hx' by (by eapply wext_swap_back).
          apply (tenv_comp_swap a b) in Hc. rewrite tenvswap_involutive in Hc.
          apply (IHV j Hj W'' (wswap a b W'')) in HVw; [|apply wsame_refl].
          rewrite tyswap_involutive in HVw.
          apply (ub_below_swap a b) in Hub. rewrite opt_ptswap_involutive in Hub.
          specialize (H _ _ _ _ _ _ Hx' Hj Hc HVw Hub).
          apply (IHE j Hj (wswap a b W'') W'') in H; [|apply Hrt].
          rewrite tenvswap_involutive, set_ptswap_involutive, eswap_subst1,
            eswap_involutive in H.
          exact H.
      + apply Vrel_lolli_iff. right. exists k, (tyswap a b T0). split_and!.
        * done.
        * by rewrite tenvswap_empty.
        * eapply konst_ty_wsame; [exact HS|]. by apply konst_ty_swap.
        * by apply (teq_tmap (ptswap a b) _ (TLolli ub lb T1 U)).
    - apply Vrel_prod_iff in HVv as (v1 & v2 & Θ1 & Θ2 & -> & Hc & H1 & H2).
      apply Vrel_prod_iff.
      exists (eswap a b v1), (eswap a b v2), (tenvswap a b Θ1), (tenvswap a b Θ2).
      split_and!; [done|by apply tenv_comp_swap|by apply IHT1|by apply IHU].
    - apply Vrel_sum_iff in HVv as [(v' & -> & H)|(v' & -> & H)];
        apply Vrel_sum_iff; [left|right]; eexists; (split; [done|]).
      + by apply IHT1.
      + by apply IHU.
    - apply Vrel_box_iff in HVv as (-> & eb & -> & Hfc & H).
      apply Vrel_box_iff. rewrite tenvswap_empty. split; [done|].
      exists (eswap a b eb). split_and!; [done|by rewrite fchans_eswap, Hfc, gswap_empty|].
      intros W'' j xs Hx Hj Hxs.
      assert (wext W (wswap a b W'')) as Hx' by (by eapply wext_swap_back).
      specialize (H _ j (ptswap a b <$> xs) Hx' Hj ltac:(by rewrite length_fmap)).
      apply (IHE j Hj (wswap a b W'') W'') in H; [|apply Hrt].
      rewrite tenvswap_empty, set_ptswap_empty, tyswap_ty_inst,
        list_ptswap_involutive, eswap_subst1 in H.
      exact H.
    - apply Vrel_sess_iff in HVv as (c & s0 & k & -> & -> & Hs & Hx).
      apply Vrel_sess_iff. exists (cswap a b c), (styswap a b s0), k.
      split_and!.
      + done.
      + by rewrite tenvswap_singleton.
      + by apply seq_smap.
      + destruct HS as (_ & He & _). apply He. rewrite <-ptswap_chan.
        by apply wswap_eq. }
  split_and!; [exact HV| |].
  - (* term relation *)
    intros W W' Θ T F e HS HE.
    destruct n as [|n']; [apply Erel_0|].
    apply Erel_S_iff in HE as (Hval & Hrdy & Hstep).
    apply Erel_S_iff. split_and!.
    { intros Hirr. apply (HV W); [done|]. apply Hval.
      apply (irred_swap a b) in Hirr. by rewrite eswap_involutive in Hirr. }
    { intros Hirr. destruct Hrdy as [Hr Hf].
      { intros Hirr0. apply Hirr. by apply irred_swap. }
      split.
      - eapply ready_t_wsame; [exact HS|]. by apply ready_t_swap.
      - eapply frame_t_wsame; [exact HS|]. by apply frame_t_swap. }
    intros α e'' Hst. apply tstep_eswap_inv' in Hst.
    specialize (Hstep _ _ Hst).
    rewrite <-(tlswap_involutive a b α), <-(eswap_involutive a b e'').
    destruct (tlswap a b α) as [|[c w|c w|c|cd]|c|w]; simpl in Hstep |- *.
    + apply (IHE n' ltac:(lia) W); done.
    + (* recv *)
      destruct Hstep as (Θ1 & m & U & s & k & Hhd & H).
      exists (tenvswap a b Θ1), m, (tyswap a b U), (styswap a b s), k.
      split; [by apply (tenv_hd_swap a b _ _ (SRcv m U s))|].
      intros W'' j Θ2 Θ12 Hx Hj Hc HVw.
      assert (wext W (wswap a b W'')) as Hx' by (by eapply wext_swap_back).
      apply (tenv_comp_swap a b) in Hc. rewrite tenvswap_involutive in Hc.
      apply (IHV j ltac:(lia) W'' (wswap a b W'')) in HVw; [|apply wsame_refl].
      rewrite tyswap_payload_at, tyswap_involutive, ptswap_chan,
        cswap_involutive, eswap_involutive in HVw.
      destruct (H _ _ _ _ Hx' Hj Hc HVw) as (Θ' & Hext & HE').
      exists (tenvswap a b Θ'). split.
      * apply (tenv_ext_swap a b) in Hext. by rewrite tenvswap_involutive in Hext.
      * by apply (IHE j ltac:(lia) (wswap a b W'') W'').
    + (* send *)
      destruct Hstep as (Θr & Θ1 & Θ2 & m & U & s & k & Θ' &
                         Hhd & Hc & HVw & Hext & HE').
      exists (tenvswap a b Θr), (tenvswap a b Θ1), (tenvswap a b Θ2), m,
        (tyswap a b U), (styswap a b s), k, (tenvswap a b Θ').
      split_and!.
      * by apply (tenv_hd_swap a b _ _ (SSnd m U s)).
      * by apply tenv_comp_swap.
      * apply (HV W W') in HVw; [|done].
        by rewrite tyswap_payload_at, ptswap_chan in HVw.
      * by apply (tenv_ext_swap a b _ _ (s, S k)).
      * by apply (IHE n' ltac:(lia) W).
    + (* close *)
      destruct Hstep as (Θ1 & k & Hhd & HE').
      exists (tenvswap a b Θ1), k. split.
      * by apply (tenv_hd_swap a b _ _ SEnd).
      * by apply (IHE n' ltac:(lia) W).
    + (* link *)
      destruct Hstep as (c & d & Θ1 & Θm & sc & sd & kc & kd &
                         -> & H1 & H2 & Hdu & Hal & HE').
      exists (cswap a b c), (cswap a b d), (tenvswap a b Θ1), (tenvswap a b Θm),
        (styswap a b sc), (styswap a b sd), kc, kd.
      split_and!.
      * apply gswap_upair.
      * by apply (tenv_ext_swap a b _ _ (sd, kd)).
      * by apply (tenv_ext_swap a b _ _ (sc, kc)).
      * by apply sdual_smap.
      * destruct HS as (_ & He & _). apply He. rewrite <-!ptswap_chan.
        by apply wswap_eq.
      * by apply (IHE n' ltac:(lia) W).
    + (* new *)
      intros Hc Hn.
      assert (c ∉ dom Θ) as Hc0.
      { rewrite dom_tenvswap, elem_of_gswap', cswap_involutive in Hc. done. }
      assert (NChan c ∉ w_names W) as Hn0.
      { intros Hin. apply Hn. destruct HS as (<- & _).
        rewrite <-(cswap_involutive a b c) at 1. apply nchan_names_swap.
        by rewrite cswap_involutive. }
      destruct (Hstep Hc0 Hn0) as (s & s' & W1 & Hdu & Hfr & HE').
      exists (styswap a b s), (styswap a b s'), (wswap a b W1). split_and!.
      * by apply sdual_smap.
      * apply (wext_fresh_wswap a b) in Hfr.
        rewrite names_singleton_swap in Hfr.
        eapply wext_fresh_wsame; [exact HS|apply wsame_refl|exact Hfr].
      * apply (IHE n' ltac:(lia) W1 (wswap a b W1)) in HE'; [|apply wsame_refl].
        by rewrite tenvswap_insert in HE'.
    + (* spawn *)
      destruct Hstep as (Θ1 & Θ2 & ub & lb & Hc & HVw & HE').
      exists (tenvswap a b Θ1), (tenvswap a b Θ2), (ptswap a b <$> ub),
        (ptswap a b <$> lb).
      split_and!.
      * by apply tenv_comp_swap.
      * apply (HV W W' _ (TLolli ub lb TUnit TUnit)) in HVw; [|done]. exact HVw.
      * by apply (IHE n' ltac:(lia) W).
  - (* process relation *)
    intros W W' Σ T p HS HP.
    destruct n as [|n']; [apply Prel_0|].
    apply Prel_S_iff in HP as (Hirr & Hrdy & Hstep).
    apply Prel_S_iff. split_and!.
    { intros Hpirr.
      destruct Hirr as (v & E & -> & Hv & HVv & HE).
      { apply (pirred_swap a b) in Hpirr. by rewrite pswap_involutive in Hpirr. }
      unfold pswap; simpl.
      rewrite gswap_empty, msswap_disj_union, msswap_singleton.
      exists (eswap a b v), (msswap a b E). split_and!.
      + done.
      + by rewrite is_val_eswap.
      + apply (HV W W') in HVv; [|done]. by rewrite tenvswap_of in HVv.
      + intros e He. apply msswap_elem in He as (e0 & -> & He0).
        by rewrite (HE e0 He0). }
    { intros Hpirr. eapply ready_p_wsame; [exact HS|]. apply ready_p_swap.
      apply Hrdy. intros Hp0. apply Hpirr. by apply pirred_swap. }
    intros π q' Hst. apply proc_step_pswap_inv' in Hst.
    specialize (Hstep _ _ Hst).
    rewrite <-(pswap_involutive a b q').
    set (q := pswap a b q') in *. clearbody q.
    assert (π = plswap a b (plswap a b π)) as ->.
    { destruct π; simpl; by rewrite ?slswap_involutive. }
    destruct (plswap a b π) as [|[c w|c w|c|cd]]; simpl in Hstep |- *.
    + (* τ *)
      intros Hd Hf.
      destruct p as [C E], q as [Cq Eq]; simpl in *.
      destruct Hstep as (W1 & Hinv & Hal & HP').
      { rewrite dom_senvswap in Hd. by apply gswap_disjoint_iff in Hd. }
      { intros c Hc Hc' HcW. apply (Hf (cswap a b c)).
        - by apply elem_of_gswap.
        - by rewrite elem_of_gswap.
        - destruct HS as (<- & _). by apply nchan_names_swap. }
      exists (wswap a b W1). split_and!.
      * apply (wext_inv_wswap a b) in Hinv.
        rewrite names_nchan_swap, gswap_union in Hinv.
        eapply wext_inv_wsame; [exact HS|apply wsame_refl|exact Hinv].
      * apply (tau_link_alias_swap a b) in Hal. exact Hal.
      * by apply (IHP n' ltac:(lia) W1).
    + (* recv *)
      destruct Hstep as (Σ1 & m & U & s & k & Hhd & Hc & H).
      exists (senvswap a b Σ1), m, (tyswap a b U), (styswap a b s), k.
      split_and!.
      * by apply (senv_hd_swap a b _ _ (SRcv m U s)).
      * rewrite dom_senvswap. by rewrite elem_of_gswap.
      * intros W'' j Θ2 Hx Hj Hfr Hok HVw.
        assert (wext W (wswap a b W'')) as Hx' by (by eapply wext_swap_back).
        assert (dom (tenvswap a b Θ2) ## p.1) as Hfr'.
        { rewrite dom_tenvswap. destruct p as [C E]; simpl in *.
          rewrite <-(gswap_involutive a b C). by apply gswap_disjoint_iff. }
        assert (recv_ok W (<[c := (s, S k)]> Σ1) (tenvswap a b Θ2)) as Hok'.
        { apply (recv_ok_swap a b) in Hok.
          rewrite senvswap_insert, senvswap_involutive, cswap_involutive in Hok.
          unfold entswap in Hok; simpl in Hok. rewrite styswap_involutive in Hok.
          eapply recv_ok_wsame; [|exact Hok].
          eapply wsame_trans; [apply wswap_wsame, wsame_sym, HS|apply wswap_wswap]. }
        apply (IHV j ltac:(lia) W'' (wswap a b W'')) in HVw; [|apply wsame_refl].
        rewrite tyswap_payload_at, tyswap_involutive, ptswap_chan,
          cswap_involutive, eswap_involutive in HVw.
        destruct (H _ _ _ Hx' Hj Hfr' Hok' HVw) as (q0 & Hal & HP0).
        apply (IHP j ltac:(lia) (wswap a b W'') W'') in HP0; [|apply Hrt].
        rewrite <-recv_env_swap, tenvswap_involutive, senvswap_insert in HP0.
        exists (pswap a b q0). split; [|exact HP0].
        apply (alpha_pswap a b) in Hal. unfold pswap at 1 in Hal; simpl in Hal.
        rewrite gswap_union, <-recv_back_swap, tenvswap_involutive,
          senvswap_insert in Hal.
        exact Hal.
    + (* send *)
      destruct Hstep as (Σ0 & Σv & m & U & s & k & Σe & Θe & Hhd &
                         Hd0v & Hc0 & Hcv & Hdom & Hsplit & HdΣ & HVw & HP').
      exists (senvswap a b Σ0), (senvswap a b Σv), m, (tyswap a b U),
        (styswap a b s), k, (senvswap a b Σe), (tenvswap a b Θe).
      split_and!.
      * rewrite <-senvswap_union. by apply (senv_hd_swap a b _ _ (SSnd m U s)).
      * by apply senvswap_disjoint.
      * rewrite dom_senvswap. by rewrite elem_of_gswap.
      * rewrite dom_senvswap. by rewrite elem_of_gswap.
      * destruct p as [C E]; simpl in *.
        by rewrite dom_tenvswap, fchans_eswap, Hdom, gswap_intersection.
      * by apply send_split_swap.
      * rewrite dom_tenvswap, dom_senvswap. by apply gswap_disjoint_iff.
      * apply (HV W W') in HVw; [|done].
        by rewrite tenvswap_union, tenvswap_of, tyswap_payload_at, ptswap_chan in HVw.
      * apply (IHP n' ltac:(lia) W W') in HP'; [|done].
        by rewrite senvswap_insert, senvswap_union in HP'.
    + (* close *)
      destruct Hstep as (Σ1 & k & Hhd & Hc & HP').
      exists (senvswap a b Σ1), k. split_and!.
      * by apply (senv_hd_swap a b _ _ SEnd).
      * rewrite dom_senvswap. by rewrite elem_of_gswap.
      * by apply (IHP n' ltac:(lia) W).
    + (* link *)
      destruct Hstep as (c & d & Σ1 & sc & sd & kc & kd &
                         -> & Hne & -> & Hc1 & Hd1 & Hdu & Hal & HP').
      exists (cswap a b c), (cswap a b d), (senvswap a b Σ1), (styswap a b sc),
        (styswap a b sd), kc, kd.
      split_and!.
      * apply gswap_upair.
      * intros Heq. by apply cswap_inj in Heq.
      * by rewrite !senvswap_insert.
      * rewrite dom_senvswap. by rewrite elem_of_gswap.
      * rewrite dom_senvswap. by rewrite elem_of_gswap.
      * by apply sdual_smap.
      * destruct HS as (_ & He & _). apply He. rewrite <-!ptswap_chan.
        by apply wswap_eq.
      * by apply (IHP n' ltac:(lia) W).
Qed.

Lemma Vrel_swap a b n W Θ T v :
  Vrel n W Θ T v → Vrel n (wswap a b W) (tenvswap a b Θ) (tyswap a b T) (eswap a b v).
Proof. apply (rel_swap a b n). apply wsame_refl. Qed.

Lemma Erel_swap a b n W Θ T F e :
  Erel n W Θ T F e →
  Erel n (wswap a b W) (tenvswap a b Θ) (tyswap a b T) (set_map (ptswap a b) F)
    (eswap a b e).
Proof. apply (rel_swap a b n). apply wsame_refl. Qed.

Lemma Prel_swap a b n W Σ T p :
  Prel n W Σ T p → Prel n (wswap a b W) (senvswap a b Σ) (tyswap a b T) (pswap a b p).
Proof. apply (rel_swap a b n). apply wsame_refl. Qed.
