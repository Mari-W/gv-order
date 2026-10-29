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
