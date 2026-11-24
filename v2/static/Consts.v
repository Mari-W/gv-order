(** * Constants of the syntax and their renaming (2026-11-22)

    The interface constants of a process judgment ([iface]) are the
    constants that occur in the interface Σ and in the type T. The
    constants of its derivation outside them are private. A renaming of
    constants renames a derivation (static/Hiding.v), so two components
    can be renamed apart, and this file gives the renaming on the
    syntax.

    [cbij] is a bijection of constants. [pt_ren f] renames the constant
    at the root of a point, and [ty_ren], [sty_ren] and the maps on
    contexts rename every point of a type or a context. Renaming
    commutes with every operation the typing rules apply to points and
    types (instantiation, shift, dual, field, unfolding, session
    substitution, heads). [sw_ren π W] renames a static world and keeps
    its order up to the renaming ([sw_lt_ren], [sw_lt_ren_inv]). A
    renaming that fixes the constants of a type or an interface leaves
    it alone ([ty_ren_fix], [senv_ren_fix]). *)

From GV Require Export static.Contexts.

(** ** Bijections of constants *)

Record cbij := CBij {
  cb_f : nat → nat;
  cb_g : nat → nat;
  cb_fg a : cb_f (cb_g a) = a;
  cb_gf a : cb_g (cb_f a) = a
}.

Definition cb_inv (π : cbij) : cbij := CBij (cb_g π) (cb_f π) (cb_gf π) (cb_fg π).

Definition cswap (a b c : nat) : nat := if decide (c = a) then b else if decide (c = b) then a else c.

Lemma cswap_inv a b c : cswap a b (cswap a b c) = c.
Proof. unfold cswap. repeat case_decide; subst; congruence. Qed.

Definition cb_swap (a b : nat) : cbij := CBij (cswap a b) (cswap a b) (cswap_inv a b) (cswap_inv a b).

Definition cb_comp (π1 π2 : cbij) : cbij.
Proof.
  refine (CBij (cb_f π1 ∘ cb_f π2) (cb_g π2 ∘ cb_g π1) _ _); intros a; simpl.
  - by rewrite cb_fg, cb_fg.
  - by rewrite cb_gf, cb_gf.
Defined.

Lemma cb_f_inj π a b : cb_f π a = cb_f π b → a = b.
Proof. intros H. by rewrite <-(cb_gf π a), H, cb_gf. Qed.

(** ** Points *)

Fixpoint pn_ren (f : nat → nat) (p : pname) : pname :=
  match p with
  | NConst a => NConst (f a)
  | NVar a => NVar a
  | NField q b κ => NField (pn_ren f q) b κ
  end.

Definition pt_ren (f : nat → nat) (x : point) : point :=
  MkPt (pn_ren f (pt_name x)) (pt_pol x) (pt_off x).

Lemma pt_ren_shift f n x : pt_ren f (pt_shift n x) = pt_shift n (pt_ren f x).
Proof. done. Qed.
Lemma pt_ren_dual f x : pt_ren f x‾ = (pt_ren f x)‾.
Proof. done. Qed.
Lemma pt_ren_field f x κ : pt_ren f (x·κ) = (pt_ren f x)·κ.
Proof. done. Qed.
Lemma pt_ren_polar f b x : pt_ren f (pt_polar b x) = pt_polar b (pt_ren f x).
Proof. by destruct b. Qed.
Lemma pt_ren_pvar f a : pt_ren f (pvar a) = pvar a.
Proof. done. Qed.
Lemma pt_ren_sel f x i : pt_ren f (sel_pt x i) = sel_pt (pt_ren f x) i.
Proof. done. Qed.
Lemma pt_ren_bra f x i : pt_ren f (bra_pt x i) = bra_pt (pt_ren f x) i.
Proof. done. Qed.

Lemma pn_ren_root f p : pn_root (pn_ren f p) = pn_ren f (pn_root p).
Proof. induction p; simpl; done. Qed.

Lemma pt_ren_root f x : pt_root (pt_ren f x) = pn_ren f (pt_root x).
Proof. apply pn_ren_root. Qed.

Lemma pn_ren_comp f g p : pn_ren f (pn_ren g p) = pn_ren (f ∘ g) p.
Proof. induction p; simpl; congruence. Qed.

Lemma pn_ren_inv f g p : (∀ a, f (g a) = a) → pn_ren f (pn_ren g p) = p.
Proof. intros H. induction p; simpl; rewrite ?H; congruence. Qed.

Lemma pt_ren_inv f g x : (∀ a, f (g a) = a) → pt_ren f (pt_ren g x) = x.
Proof. intros H. destruct x. unfold pt_ren. simpl. by rewrite pn_ren_inv. Qed.

Lemma pt_ren_comp f g x : pt_ren f (pt_ren g x) = pt_ren (f ∘ g) x.
Proof. unfold pt_ren. simpl. by rewrite pn_ren_comp. Qed.

Lemma pt_ren_cb π x : pt_ren (cb_f π) (pt_ren (cb_g π) x) = x.
Proof. apply pt_ren_inv, cb_fg. Qed.
Lemma pt_ren_cb' π x : pt_ren (cb_g π) (pt_ren (cb_f π) x) = x.
Proof. apply pt_ren_inv, cb_gf. Qed.

Lemma pt_ren_inj π x y : pt_ren (cb_f π) x = pt_ren (cb_f π) y → x = y.
Proof. intros H. by rewrite <-(pt_ren_cb' π x), H, pt_ren_cb'. Qed.

(** The constants of a point: the constant at its root, if any. *)
Definition pn_consts (p : pname) : gset nat :=
  match pn_root p with NConst a => {[a]} | _ => ∅ end.
Definition pt_consts (x : point) : gset nat := pn_consts (pt_name x).

Lemma pn_ren_fix f p : (∀ a, a ∈ pn_consts p → f a = a) → pn_ren f p = p.
Proof.
  unfold pn_consts. induction p as [a|a|q IH b κ]; simpl; intros H.
  - rewrite H; [done|set_solver].
  - done.
  - by rewrite IH.
Qed.

Lemma pt_ren_fix f x : (∀ a, a ∈ pt_consts x → f a = a) → pt_ren f x = x.
Proof. intros H. destruct x. unfold pt_ren. simpl. by rewrite pn_ren_fix. Qed.

Lemma pt_consts_root x a : pt_root x = NConst a → pt_consts x = {[a]}.
Proof. unfold pt_consts, pn_consts. fold (pt_root x). by intros ->. Qed.

Lemma pn_inst_ren f σ p : pt_ren f (pn_inst σ p) = pn_inst (pt_ren f ∘ σ) (pn_ren f p).
Proof. induction p as [a|a|q IH b κ]; simpl; try done. by rewrite pt_ren_field, pt_ren_shift, IH. Qed.

Lemma pt_inst_ren f σ x : pt_ren f (pt_inst σ x) = pt_inst (pt_ren f ∘ σ) (pt_ren f x).
Proof. destruct x as [p b o]. unfold pt_inst. simpl. by rewrite pt_ren_polar, pt_ren_shift, pn_inst_ren. Qed.

(** A name rooted at a variable has no constant. *)
Lemma pn_ren_vb f k p : pn_vb k p → pn_ren f p = p.
Proof. induction p; simpl; try done. intros H. by rewrite IHp. Qed.

Lemma pup_ren f m σ a : pt_ren f (pup m σ a) = pup m (pt_ren f ∘ σ) a.
Proof.
  unfold pup. destruct (decide (a < m)); [done|]. rewrite pt_inst_ren. by apply pt_inst_ext.
Qed.

Lemma plist_ren f xs a : pt_ren f (plist xs a) = plist (pt_ren f <$> xs) a.
Proof. unfold plist. rewrite list_lookup_fmap, length_fmap. by destruct (xs !! a). Qed.

Lemma payload_pts_ren f x m : pt_ren f <$> payload_pts x m = payload_pts (pt_ren f x) m.
Proof. unfold payload_pts. rewrite <-list_fmap_compose. by apply list_fmap_ext. Qed.

Lemma pt_inst_pshift_ren f m x : pt_ren f (pt_inst (pshift m) x) = pt_inst (pshift m) (pt_ren f x).
Proof. rewrite pt_inst_ren. by apply pt_inst_ext. Qed.

Lemma pt_inst_plist_ren f xs x : pt_ren f (pt_inst (plist xs) x) = pt_inst (plist (pt_ren f <$> xs)) (pt_ren f x).
Proof. rewrite pt_inst_ren. apply pt_inst_ext. intros a. apply plist_ren. Qed.

Lemma list_fmap_fix {A} (h : A → A) (l : list A) : (∀ x, h x = x) → h <$> l = l.
Proof. intros H. induction l as [|x l IH]; [done|]. rewrite fmap_cons. by rewrite H, IH. Qed.

(** ** Facts and box constraints

    The facts of a constraint speak of variables only, so renaming acts
    on its environment. *)

Definition fact_ren (f : nat → nat) (g : fact) : fact := fact_map (pt_ren f) g.

Lemma fact_ren_inv f g h : (∀ a, f (g a) = a) → fact_ren f (fact_ren g h) = h.
Proof. intros H. destruct h. simpl. by rewrite !pt_ren_inv. Qed.

Definition bcs_ren (f : nat → nat) (C : bcs) : bcs := BCs (pt_ren f <$> bc_env C) (bc_facts C).

Lemma bcs_ren_inv f g C : (∀ a, f (g a) = a) → bcs_ren f (bcs_ren g C) = C.
Proof.
  intros H. destruct C as [env P]. unfold bcs_ren. simpl. f_equal.
  rewrite <-list_fmap_compose. apply list_fmap_fix. intros. simpl. by apply pt_ren_inv.
Qed.

Lemma bcs_inst_ren f σ C : bcs_ren f (bcs_inst σ C) = bcs_inst (pt_ren f ∘ σ) (bcs_ren f C).
Proof.
  destruct C as [env P]. unfold bcs_ren, bcs_inst. simpl. f_equal.
  rewrite <-!list_fmap_compose. apply list_fmap_ext. intros. simpl. apply pt_inst_ren.
Qed.

Lemma bcs_inst_pshift_ren f m C : bcs_ren f (bcs_inst (pshift m) C) = bcs_inst (pshift m) (bcs_ren f C).
Proof. rewrite bcs_inst_ren. by apply bcs_inst_ext. Qed.

Local Lemma fact_scoped_ren f k g σ :
  fact_scoped k g → fact_ren f (fact_map (pt_inst σ) g) = fact_map (pt_inst (pt_ren f ∘ σ)) g.
Proof.
  destruct g as [x y]. intros [Hx Hy]. simpl. rewrite !pt_inst_ren.
  destruct x as [p b o], y as [q b' o']. unfold pt_ren. simpl in *. by rewrite (pn_ren_vb f k p), (pn_ren_vb f k q).
Qed.

Lemma bcs_open_ren f n C g : bcs_open n C g → bcs_open n (bcs_ren f C) (fact_ren f g).
Proof.
  intros (g0 & Hf & Hs & ->). exists g0. unfold bcs_ren. simpl. rewrite length_fmap. split_and!; [done|done|].
  rewrite (fact_scoped_ren _ _ _ _ Hs). apply fact_map_ext. intros x. apply pt_inst_ext. intros a. simpl.
  rewrite pup_ren. apply pup_ext. intros. apply plist_ren.
Qed.

Lemma bcs_open_ren_inv f n C g : bcs_open n (bcs_ren f C) g → ∃ g0, bcs_open n C g0 ∧ g = fact_ren f g0.
Proof.
  intros (g0 & Hf & Hs & ->). unfold bcs_ren in *. simpl in *. rewrite length_fmap in Hs.
  exists (fact_map (pt_inst (pup n (plist (bc_env C)))) g0). split; [by exists g0|].
  rewrite (fact_scoped_ren _ _ _ _ Hs). apply fact_map_ext. intros x. apply pt_inst_ext. intros a.
  unfold compose. rewrite pup_ren. apply pup_ext. intros b. unfold compose. by rewrite plist_ren.
Qed.

Lemma bcs_at_ren f C xs g : bcs_at C xs g → bcs_at (bcs_ren f C) (pt_ren f <$> xs) (fact_ren f g).
Proof.
  intros (g0 & Ho & ->). exists (fact_ren f g0). rewrite length_fmap. split; [by apply bcs_open_ren|].
  destruct g0. simpl. by rewrite !pt_inst_plist_ren.
Qed.

Lemma bcs_at_ren_inv f C xs g : bcs_at (bcs_ren f C) (pt_ren f <$> xs) g → ∃ g0, bcs_at C xs g0 ∧ g = fact_ren f g0.
Proof.
  intros (g1 & Ho & ->). rewrite length_fmap in Ho. destruct (bcs_open_ren_inv _ _ _ _ Ho) as (g0 & Ho0 & ->).
  exists (fact_map (pt_inst (plist xs)) g0). split; [by exists g0|]. destruct g0. simpl. by rewrite !pt_inst_plist_ren.
Qed.

(** ** Types *)

Fixpoint ty_ren (f : nat → nat) (T : ty) : ty :=
  match T with
  | TUnit => TUnit
  | TLolli ub lb c T1 U a => TLolli (ub_map (pt_ren f) ub) (lb_map (pt_ren f) lb) c (ty_ren f T1) (ty_ren f U) a
  | TProd T1 U => TProd (ty_ren f T1) (ty_ren f U)
  | TSum T1 U => TSum (ty_ren f T1) (ty_ren f U)
  | TBox n k C ub c U => TBox n k (bcs_ren f C) (pt_ren f <$> ub) c (ty_ren f U)
  | TSess s x a mt => TSess (sty_ren f s) (pt_ren f x) a mt
  | TEx lb n C T1 => TEx (lb_map (pt_ren f) lb) n (bcs_ren f C) (ty_ren f T1)
  end
with sty_ren (f : nat → nat) (s : sty) : sty :=
  match s with
  | SRcv m T => SRcv m (ty_ren f T)
  | SSnd m T => SSnd m (ty_ren f T)
  | SMu s' => SMu (sty_ren f s')
  | SSeq s1 s2 => SSeq (sty_ren f s1) (sty_ren f s2)
  | SPlus s1 s2 => SPlus (sty_ren f s1) (sty_ren f s2)
  | SWith s1 s2 => SWith (sty_ren f s1) (sty_ren f s2)
  | s => s
  end.

Lemma ren_inv_mut f g : (∀ a, f (g a) = a) →
  (∀ T, ty_ren f (ty_ren g T) = T) ∧ (∀ s, sty_ren f (sty_ren g s) = s).
Proof.
  intros H. apply ty_sty_mut_ind; intros; simpl; try congruence.
  - rewrite ub_map_comp, lb_map_comp, ub_map_id, lb_map_id by (intros; by apply pt_ren_inv). congruence.
  - rewrite bcs_ren_inv, <-option_fmap_compose by done. f_equal; [|done].
    destruct ub; simpl; [by rewrite pt_ren_inv|done].
  - by rewrite pt_ren_inv, H0.
  - rewrite lb_map_comp, lb_map_id, bcs_ren_inv by first [done|intros; by apply pt_ren_inv]. congruence.
Qed.

Lemma ty_ren_inv f g T : (∀ a, f (g a) = a) → ty_ren f (ty_ren g T) = T.
Proof. intros H. by apply ren_inv_mut. Qed.
Lemma sty_ren_inv f g s : (∀ a, f (g a) = a) → sty_ren f (sty_ren g s) = s.
Proof. intros H. by apply ren_inv_mut. Qed.

Lemma ty_ren_pinst f σ T : ty_ren f (pinst_ty σ T) = pinst_ty (pt_ren f ∘ σ) (ty_ren f T).
Proof.
  revert σ. induction T; intros σ; simpl; try done.
  - rewrite IHT1, IHT2, ub_map_comp, lb_map_comp, ub_map_comp, lb_map_comp.
    rewrite (ub_map_ext (pt_ren f ∘ pt_inst σ) (pt_inst (pt_ren f ∘ σ) ∘ pt_ren f)),
      (lb_map_ext (pt_ren f ∘ pt_inst σ) (pt_inst (pt_ren f ∘ σ) ∘ pt_ren f)) by (intros; apply pt_inst_ren). done.
  - by rewrite IHT1, IHT2.
  - by rewrite IHT1, IHT2.
  - rewrite IHT, bcs_inst_ren, <-!option_fmap_compose.
    rewrite (pinst_ty_ext _ (pt_ren f ∘ pup n σ) (pup n (pt_ren f ∘ σ))) by (intros; apply pup_ren).
    f_equal. apply option_fmap_ext. intros x. simpl. rewrite pt_inst_ren. apply pt_inst_ext. intros; apply pup_ren.
  - by rewrite pt_inst_ren.
  - rewrite IHT, bcs_inst_ren, !lb_map_comp.
    rewrite (pinst_ty_ext _ (pt_ren f ∘ pup n σ) (pup n (pt_ren f ∘ σ))) by (intros; apply pup_ren).
    rewrite (lb_map_ext (pt_ren f ∘ pt_inst σ) (pt_inst (pt_ren f ∘ σ) ∘ pt_ren f)) by (intros; apply pt_inst_ren).
    done.
Qed.

Lemma ty_ren_inst f xs T : ty_ren f (ty_inst xs T) = ty_inst (pt_ren f <$> xs) (ty_ren f T).
Proof. unfold ty_inst. rewrite ty_ren_pinst. apply pinst_ty_ext. intros. apply plist_ren. Qed.

Lemma ty_ren_pshift f m T : ty_ren f (pinst_ty (pshift m) T) = pinst_ty (pshift m) (ty_ren f T).
Proof. rewrite ty_ren_pinst. by apply pinst_ty_ext. Qed.

Lemma ty_ren_payload f m T x : ty_ren f (payload_at m T x) = payload_at m (ty_ren f T) (pt_ren f x).
Proof. unfold payload_at. by rewrite ty_ren_inst, payload_pts_ren. Qed.

Lemma opt_heads_ren f o : opt_heads (pt_ren f <$> o) = set_map (pt_ren f) (opt_heads o).
Proof. destruct o; simpl; set_solver. Qed.

Lemma lb_heads_ren f lb : lb_heads (lb_map (pt_ren f) lb) = set_map (pt_ren f) (lb_heads lb).
Proof. destruct lb; simpl; set_solver. Qed.

Lemma heads_ren f T : heads (ty_ren f T) = set_map (pt_ren f) (heads T).
Proof.
  induction T; simpl; rewrite ?set_map_union_L, ?IHT1, ?IHT2; try set_solver.
  - apply lb_heads_ren.
  - rewrite set_map_singleton_L. done.
  - apply lb_heads_ren.
Qed.

Lemma hbot_ren f T : hbot (ty_ren f T) = hbot T.
Proof. induction T; simpl; try done; try congruence; by destruct lb. Qed.

Lemma unlimited_ren f T : unlimited (ty_ren f T) ↔ unlimited T.
Proof. by destruct T. Qed.

Lemma tfree_ren f T : tfree T → tfree (ty_ren f T).
Proof. induction 1; simpl; constructor; auto. Qed.

(** *** Session operations *)

Lemma sren_ren_mut f :
  (∀ T r, ty_ren f (sren_ty r T) = sren_ty r (ty_ren f T)) ∧
  (∀ s r, sty_ren f (sren r s) = sren r (sty_ren f s)).
Proof. apply ty_sty_mut_ind; intros; simpl; try congruence. Qed.

Lemma sflip_ren_mut f :
  (∀ T k, ty_ren f (sflip_ty k T) = sflip_ty k (ty_ren f T)) ∧
  (∀ s k, sty_ren f (sflip k s) = sflip k (sty_ren f s)).
Proof. apply ty_sty_mut_ind; intros; simpl; try congruence; by repeat case_decide. Qed.

Lemma dual_ren f s : sty_ren f (dual s) = dual (sty_ren f s).
Proof. induction s; simpl; try congruence. by rewrite (proj2 (sflip_ren_mut f)), IHs. Qed.

Lemma sty_up_ext σ τ : (∀ a, σ a = τ a) → ∀ a, sty_up σ a = sty_up τ a.
Proof. intros H [|a]; simpl; [done|]. unfold compose. by rewrite H. Qed.

Lemma iter_sty_up_ext k σ τ : (∀ a, σ a = τ a) → ∀ a, Nat.iter k sty_up σ a = Nat.iter k sty_up τ a.
Proof. induction k; simpl; [done|]. intros H. apply sty_up_ext. by apply IHk. Qed.

Lemma sinst_ext_mut :
  (∀ T σ τ, (∀ a, σ a = τ a) → sinst_ty σ T = sinst_ty τ T) ∧
  (∀ s σ τ, (∀ a, σ a = τ a) → sinst σ s = sinst τ s).
Proof.
  apply ty_sty_mut_ind; intros; simpl; try (f_equal; eauto using sty_up_ext, iter_sty_up_ext); by rewrite H.
Qed.

Lemma sty_up_ren f σ a : sty_ren f (sty_up σ a) = sty_up (sty_ren f ∘ σ) a.
Proof. destruct a; simpl; [done|]. unfold compose. apply (proj2 (sren_ren_mut f)). Qed.

Lemma iter_sty_up_ren f k σ a : sty_ren f (Nat.iter k sty_up σ a) = Nat.iter k sty_up (sty_ren f ∘ σ) a.
Proof.
  revert a. induction k; intros a; simpl; [done|]. rewrite sty_up_ren.
  apply sty_up_ext. intros b. apply IHk.
Qed.

Lemma sinst_ren_mut f :
  (∀ T σ, ty_ren f (sinst_ty σ T) = sinst_ty (sty_ren f ∘ σ) (ty_ren f T)) ∧
  (∀ s σ, sty_ren f (sinst σ s) = sinst (sty_ren f ∘ σ) (sty_ren f s)).
Proof.
  apply ty_sty_mut_ind; intros; simpl; try (f_equal; congruence).
  - rewrite H. f_equal. apply sinst_ext_mut. intros a. apply iter_sty_up_ren.
  - rewrite H. f_equal. apply sinst_ext_mut. intros a. apply sty_up_ren.
  - apply dual_ren.
Qed.

Lemma ty_ren_sinst f σ T : ty_ren f (sinst_ty σ T) = sinst_ty (sty_ren f ∘ σ) (ty_ren f T).
Proof. apply sinst_ren_mut. Qed.

Lemma slist_ren f ss a : sty_ren f (slist ss a) = slist (sty_ren f <$> ss) a.
Proof. unfold slist. rewrite list_lookup_fmap, length_fmap. by destruct (ss !! a). Qed.

Lemma ty_ren_sinst_slist f ss T : ty_ren f (sinst_ty (slist ss) T) = sinst_ty (slist (sty_ren f <$> ss)) (ty_ren f T).
Proof. rewrite ty_ren_sinst. apply sinst_ext_mut. intros. apply slist_ren. Qed.

Lemma unroll_ren f s : sty_ren f (unroll s) = unroll (sty_ren f s).
Proof.
  unfold unroll. rewrite (proj2 (sinst_ren_mut f)). apply sinst_ext_mut. by intros [|a].
Qed.

Lemma hseq_ren f h s2 : sty_ren f (hseq h s2) = hseq (sty_ren f h) (sty_ren f s2).
Proof. destruct h; simpl; try done. destruct h2; done. Qed.

Lemma unrN_ren f k : ∀ s, unrN k (sty_ren f s) = sty_ren f <$> unrN k s.
Proof.
  induction k as [|k IH]; intros s; [done|]. destruct s; simpl; try done.
  - by rewrite <-unroll_ren, IH.
  - rewrite IH. destruct (unrN k s1) as [h|]; simpl; [|done].
    destruct h; simpl; try done; try apply IH; try (by rewrite <-hseq_ren).
    by destruct h2.
Qed.

Lemma sfuel_ren f s : sfuel (sty_ren f s) = sfuel s.
Proof. induction s; simpl; congruence. Qed.

Lemma unfoldS_ren f s : unfoldS (sty_ren f s) = sty_ren f (unfoldS s).
Proof. unfold unfoldS. rewrite sfuel_ren, unrN_ren. by destruct (unrN (sfuel s) s). Qed.

Lemma idle_ren f s : idle s → idle (sty_ren f s).
Proof. unfold idle. rewrite unfoldS_ren. by intros ->. Qed.

Definition hview_ren (f : nat → nat) (h : hview) : hview :=
  match h with
  | HSkip => HSkip
  | HRcv m T s => HRcv m (ty_ren f T) (sty_ren f s)
  | HSnd m T s => HSnd m (ty_ren f T) (sty_ren f s)
  | HVar a s => HVar a (sty_ren f s)
  | HVarD a s => HVarD a (sty_ren f s)
  | HPlus a b => HPlus (sty_ren f a) (sty_ren f b)
  | HWith a b => HWith (sty_ren f a) (sty_ren f b)
  | HEnd => HEnd
  | HStuck u => HStuck (sty_ren f u)
  end.

Lemma view_ren f u : view (sty_ren f u) = hview_ren f (view u).
Proof. destruct u; simpl; try done. destruct u1; done. Qed.

Lemma hd_ren f s : hd (sty_ren f s) = hview_ren f (hd s).
Proof. unfold hd. by rewrite unfoldS_ren, view_ren. Qed.

Lemma eqT_ren f (ρ ρ' : sty → sty → Prop) T : ∀ U,
  (∀ s r, ρ s r → ρ' (sty_ren f s) (sty_ren f r)) → eqT ρ T U → eqT ρ' (ty_ren f T) (ty_ren f U).
Proof.
  induction T; intros [] Hρ; simpl; try done; try naive_solver.
  intros (-> & -> & -> & -> & -> & H). split_and!; try done. destruct k0; [by apply IHT|by subst].
Qed.

Lemma aeq_ren f n : ∀ s r, aeq n s r → aeq n (sty_ren f s) (sty_ren f r).
Proof.
  induction n as [|n IH]; intros s r; simpl; [done|]. unfold eq_step. rewrite !hd_ren.
  destruct (hd s), (hd r); simpl; try done;
    try (intros (-> & HT & Hs); split_and!; [done|by eapply eqT_ren|by apply IH]); try (by intros ->); naive_solver.
Qed.

Lemma sequiv_ren f s r : sequiv s r → sequiv (sty_ren f s) (sty_ren f r).
Proof. intros H n. by apply aeq_ren. Qed.

Lemma teq_ren f T U : teq T U → teq (ty_ren f T) (ty_ren f U).
Proof. apply eqT_ren, sequiv_ren. Qed.

Lemma crT_ren f T : ∀ U, crT T U → crT (ty_ren f T) (ty_ren f U).
Proof.
  induction T; intros [] H; try (exact (teq_ren f _ _ H)); simpl in *; try done.
  all: destruct_and?; subst; split_and?; auto using teq_ren, sequiv_ren.
Qed.

Lemma asub_ren f n : ∀ s r, asub n s r → asub n (sty_ren f s) (sty_ren f r).
Proof.
  induction n as [|n IH]; intros s r; simpl; [done|]. unfold sub_step. rewrite !hd_ren.
  destruct (hd s), (hd r); simpl; try done;
    try (intros (-> & HT & Hs); split_and!; [done|by apply crT_ren|by apply IH]); try (by intros ->); naive_solver.
Qed.

Lemma ssub_ren f s r : ssub s r → ssub (sty_ren f s) (sty_ren f r).
Proof. intros H n. by apply asub_ren. Qed.

Lemma ahc_ren f n : ∀ s, ahc n s → ahc n (sty_ren f s).
Proof.
  induction n as [|n IH]; intros s; simpl; [done|]. unfold hc_step. rewrite hd_ren.
  destruct (hd s); simpl; naive_solver.
Qed.

Lemma hcontractive_ren f s : hcontractive s → hcontractive (sty_ren f s).
Proof. intros H n. by apply ahc_ren. Qed.

Lemma pt_pscoped_ren f k x : pt_pscoped k (pt_ren f x) ↔ pt_pscoped k x.
Proof.
  unfold pt_pscoped. rewrite pt_ren_root. split; intros H a Ha; apply H.
  - by rewrite Ha.
  - by destruct (pt_root x).
Qed.

Lemma pscoped_ren_mut f :
  (∀ T k, pscoped k T → pscoped k (ty_ren f T)) ∧ (∀ s, sscoped s → sscoped (sty_ren f s)).
Proof.
  apply ty_sty_mut_ind; intros; simpl in *; try naive_solver.
  - destruct H1 as (Hu & Hl & H1 & H2). split_and!; [|intros x Hx|auto|auto].
    + intros x Hx. destruct ub; simpl in Hx; try done. injection Hx as <-. apply pt_pscoped_ren. by apply Hu.
    + destruct lb; simpl in Hx; try done. injection Hx as <-. apply pt_pscoped_ren. by apply Hl.
  - destruct H0 as (He & Hu & H1). split_and!; [|intros x Hx|auto].
    + apply Forall_fmap; eapply Forall_impl; [|exact He]; intros x Hx. by apply pt_pscoped_ren.
    + destruct ub; simpl in Hx; try done. injection Hx as <-. apply pt_pscoped_ren. by apply Hu.
  - destruct H0. split; [auto|]. by apply pt_pscoped_ren.
  - destruct H0 as (Hl & He & H1). split_and!; [|auto|auto].
    + intros x Hx. destruct lb; simpl in Hx; try done. injection Hx as <-. apply pt_pscoped_ren. by apply Hl.
    + apply Forall_fmap; eapply Forall_impl; [|exact He]; intros x Hx. by apply pt_pscoped_ren.
Qed.

Lemma df_ren_mut f :
  (∀ T, ty_df (ty_ren f T) = ty_ren f (ty_df T)) ∧ (∀ s, sty_df (sty_ren f s) = sty_ren f (sty_df s)).
Proof. apply ty_sty_mut_ind; intros; simpl; congruence. Qed.

(** Renaming constants keeps contractivity, which reads no point. *)
Lemma sk_ren f s : sk (sty_ren f s) = sk s.
Proof. induction s; simpl; try done; by rewrite ?IHs1, ?IHs2, ?IHs. Qed.

Lemma ugv_ren f s : ∀ a, ugv a (sty_ren f s) = ugv a s.
Proof. induction s; intros a'; simpl; try done; by rewrite ?IHs1, ?IHs2, ?IHs, ?sk_ren. Qed.

Lemma contr_ren_mut f :
  (∀ T, tcontr (ty_ren f T) = tcontr T) ∧ (∀ s, scontr (sty_ren f s) = scontr s).
Proof. apply ty_sty_mut_ind; intros; simpl; rewrite ?ugv_ren; congruence. Qed.

Lemma tcontr_ren f T : tcontr (ty_ren f T) = tcontr T.
Proof. apply contr_ren_mut. Qed.
Lemma scontr_ren f s : scontr (sty_ren f s) = scontr s.
Proof. apply contr_ren_mut. Qed.

Lemma sinsts_ren f N ss : sinsts N ss → sinsts N (sty_ren f <$> ss).
Proof.
  intros [[Hc Hs] Hd]. split; [split|].
  - apply Forall_fmap; eapply Forall_impl; [|exact Hc]; intros s0 Hs0. unfold compose, contractive in *. by rewrite scontr_ren.
  - apply Forall_fmap; eapply Forall_impl; [|exact Hs]; intros. by apply pscoped_ren_mut.
  - intros HN. apply Forall_fmap; eapply Forall_impl; [|exact (Hd HN)]; intros s Hs'; simpl.
    by rewrite (proj2 (df_ren_mut f)), Hs'.
Qed.

(** *** Constants of a type *)

Definition opt_consts (o : option point) : gset nat := match o with Some x => pt_consts x | None => ∅ end.
Definition lb_consts (lb : lbound) : gset nat := match lb with LPt x => pt_consts x | _ => ∅ end.
Definition ub_consts (ub : ubound) : gset nat := match ub with UPt x => pt_consts x | _ => ∅ end.
Definition env_consts (xs : list point) : gset nat := ⋃ (pt_consts <$> xs).

Fixpoint ty_consts (T : ty) : gset nat :=
  match T with
  | TUnit => ∅
  | TLolli ub lb _ T1 U _ => ub_consts ub ∪ lb_consts lb ∪ ty_consts T1 ∪ ty_consts U
  | TProd T1 U | TSum T1 U => ty_consts T1 ∪ ty_consts U
  | TBox _ _ C ub _ U => env_consts (bc_env C) ∪ opt_consts ub ∪ ty_consts U
  | TSess s x _ _ => sty_consts s ∪ pt_consts x
  | TEx lb _ C T1 => lb_consts lb ∪ env_consts (bc_env C) ∪ ty_consts T1
  end
with sty_consts (s : sty) : gset nat :=
  match s with
  | SRcv _ T | SSnd _ T => ty_consts T
  | SMu s' => sty_consts s'
  | SSeq s1 s2 | SPlus s1 s2 | SWith s1 s2 => sty_consts s1 ∪ sty_consts s2
  | _ => ∅
  end.

Lemma env_ren_fix f xs : (∀ a, a ∈ env_consts xs → f a = a) → pt_ren f <$> xs = xs.
Proof.
  intros H. induction xs as [|x xs IH]; simpl; [done|]. unfold env_consts in H. simpl in H.
  f_equal; [apply pt_ren_fix|apply IH]; intros a Ha; apply H; set_solver.
Qed.

Lemma ren_fix_mut f :
  (∀ T, (∀ a, a ∈ ty_consts T → f a = a) → ty_ren f T = T) ∧
  (∀ s, (∀ a, a ∈ sty_consts s → f a = a) → sty_ren f s = s).
Proof.
  apply ty_sty_mut_ind; intros; simpl in *; try done; try (f_equal; first [apply H|apply H0]; set_solver).
  - rewrite H, H0 by set_solver. f_equal.
    + destruct ub; simpl; try done. f_equal. apply pt_ren_fix. intros; apply H1; set_solver.
    + destruct lb; simpl; try done. f_equal. apply pt_ren_fix. intros; apply H1; set_solver.
  - rewrite H by set_solver. f_equal.
    + destruct C as [env P]. unfold bcs_ren. simpl in *. f_equal. apply env_ren_fix. intros; apply H0; set_solver.
    + destruct ub; simpl; try done. f_equal. apply pt_ren_fix. intros; apply H0; set_solver.
  - rewrite H by set_solver. f_equal. apply pt_ren_fix. intros; apply H0; set_solver.
  - rewrite H by set_solver. f_equal.
    + destruct lb; simpl; try done. f_equal. apply pt_ren_fix. intros; apply H0; set_solver.
    + destruct C as [env P]. unfold bcs_ren. simpl in *. f_equal. apply env_ren_fix. intros; apply H0; set_solver.
Qed.

Lemma ty_ren_fix f T : (∀ a, a ∈ ty_consts T → f a = a) → ty_ren f T = T.
Proof. apply ren_fix_mut. Qed.

(** ** Interfaces and their constants *)

Definition senv_ren (f : nat → nat) (Σ : senv) : senv := (λ e : sty * point, (sty_ren f e.1, pt_ren f e.2)) <$> Σ.

Definition senv_consts (Σ : senv) : gset nat :=
  ⋃ ((λ oe : cend * (sty * point), sty_consts oe.2.1 ∪ pt_consts oe.2.2) <$> map_to_list Σ).

Lemma elem_of_senv_consts Σ a :
  a ∈ senv_consts Σ ↔ ∃ o s x, Σ !! o = Some (s, x) ∧ (a ∈ sty_consts s ∨ a ∈ pt_consts x).
Proof.
  unfold senv_consts. rewrite elem_of_union_list. split.
  - intros (X & HX & Ha). apply list_elem_of_fmap in HX as ([o [s x]] & -> & Hoe).
    apply elem_of_map_to_list in Hoe. exists o, s, x. set_solver.
  - intros (o & s & x & Ho & Ha). exists (sty_consts s ∪ pt_consts x). split; [|set_solver].
    apply list_elem_of_fmap. exists (o, (s, x)). split; [done|]. by apply elem_of_map_to_list.
Qed.

Lemma senv_consts_union Σ1 Σ2 : senv_consts (Σ1 ∪ Σ2) ⊆ senv_consts Σ1 ∪ senv_consts Σ2.
Proof.
  intros a. rewrite elem_of_union, !elem_of_senv_consts. intros (o & s & x & Ho & Ha).
  apply lookup_union_Some_raw in Ho as [Ho|[_ Ho]]; [left|right]; eauto.
Qed.

Lemma senv_consts_union_l Σ1 Σ2 : senv_consts Σ1 ⊆ senv_consts (Σ1 ∪ Σ2).
Proof.
  intros a. rewrite !elem_of_senv_consts. intros (o & s & x & Ho & Ha).
  exists o, s, x. split; [by apply lookup_union_Some_l|done].
Qed.

Lemma senv_ren_fix f Σ : (∀ a, a ∈ senv_consts Σ → f a = a) → senv_ren f Σ = Σ.
Proof.
  intros H. apply map_eq. intros o. unfold senv_ren. rewrite lookup_fmap.
  destruct (Σ !! o) as [[s x]|] eqn:Ho; simpl; [|done]. f_equal. f_equal.
  - apply ren_fix_mut. intros a Ha. apply H, elem_of_senv_consts. exists o, s, x. by split; [|left].
  - apply pt_ren_fix. intros a Ha. apply H, elem_of_senv_consts. exists o, s, x. by split; [|right].
Qed.

(** The constants of an interface Σ with type T. *)
Definition iface (Σ : senv) (T : ty) : gset nat := senv_consts Σ ∪ ty_consts T.

(** ** Contexts *)

Definition tentry_ren (f : nat → nat) (e : tentry) : tentry :=
  TE (sty_ren f (te_sty e)) (pt_ren f (te_pt e)) (te_cr e) (te_tk e).
Definition tenv_ren (f : nat → nat) (Θ : tenv) : tenv := tentry_ren f <$> Θ.
Definition lenv_ren (f : nat → nat) (Δ : lenv) : lenv := fmap (M:=option) (ty_ren f) <$> Δ.
Definition hyps_ren (f : nat → nat) (Ψ : hyps) : hyps :=
  (λ h : bcs * list point, (bcs_ren f h.1, pt_ren f <$> h.2)) <$> Ψ.
Definition hctx_ren (f : nat → nat) (Γ : hctx) : hctx := HCtx (hyps_ren f (hc_hyps Γ)).
Definition frest_ren (f : nat → nat) (r : frest) : frest :=
  match r with RAbove u => RAbove (pt_ren f u) | RAll => RAll end.
Definition sf_ren (f : nat → nat) (F : sfuture) : sfuture := (set_map (pt_ren f) F.1, frest_ren f <$> F.2).

Lemma tenv_ren_empty f : tenv_ren f ∅ = ∅.
Proof. apply fmap_empty. Qed.

Lemma tenv_ren_union f Θ1 Θ2 : tenv_ren f (Θ1 ∪ Θ2) = tenv_ren f Θ1 ∪ tenv_ren f Θ2.
Proof. apply map_fmap_union. Qed.

Lemma tenv_of_ren f a Σ : tenv_ren f (tenv_of a Σ) = tenv_of a (senv_ren f Σ).
Proof. unfold tenv_ren, tenv_of, senv_ren. rewrite <-!map_fmap_compose. by apply map_fmap_ext. Qed.

Lemma tenv_ofk_ren f η Σ : tenv_ren f (tenv_ofk η Σ) = tenv_ofk η (senv_ren f Σ).
Proof.
  apply map_eq. intros o. unfold tenv_ren, senv_ren. rewrite lookup_fmap, !lookup_tenv_ofk, lookup_fmap.
  by destruct (Σ !! o).
Qed.

Lemma dom_senv_ren f Σ : dom (senv_ren f Σ) = dom Σ.
Proof. apply dom_fmap_L. Qed.

Lemma tsplit_ren f Θ Θ1 Θ2 : tsplit Θ Θ1 Θ2 → tsplit (tenv_ren f Θ) (tenv_ren f Θ1) (tenv_ren f Θ2).
Proof. intros [Hd ->]. split; [by apply map_disjoint_fmap|apply tenv_ren_union]. Qed.

Lemma tenv_heads_ren f Θ : tenv_heads (tenv_ren f Θ) = set_map (pt_ren f) (tenv_heads Θ).
Proof.
  apply set_eq. intros y. rewrite elem_of_map, elem_of_tenv_heads. setoid_rewrite elem_of_tenv_heads. split.
  - intros (o & e & Ho & ->). unfold tenv_ren in Ho. apply lookup_fmap_Some in Ho as (e' & <- & Ho).
    exists (te_pt e')‾. split; [done|]. eauto.
  - intros (z & -> & o & e & Ho & ->). exists o, (tentry_ren f e). split; [|done].
    unfold tenv_ren. by rewrite lookup_fmap, Ho.
Qed.

Lemma lenv_heads_ren f Δ : lenv_heads (lenv_ren f Δ) = set_map (pt_ren f) (lenv_heads Δ).
Proof.
  induction Δ as [|[T|] Δ IH]; simpl; [set_solver| |done]. by rewrite set_map_union_L, heads_ren, IH.
Qed.

Lemma lenv_bot_ren f Δ : lenv_bot (lenv_ren f Δ) = lenv_bot Δ.
Proof. induction Δ as [|[T|] Δ IH]; simpl; [done| |done]. by rewrite hbot_ren, IH. Qed.

Lemma lenv_unl_ren f Δ : lenv_unl Δ → lenv_unl (lenv_ren f Δ).
Proof.
  intros H o Ho. apply list_elem_of_fmap in Ho as (o' & -> & Ho). destruct (H o' Ho) as [->|(U & -> & HU)].
  - by left.
  - right. exists (ty_ren f U). split; [done|]. by apply unlimited_ren.
Qed.

Lemma lenv_only_ren f Δ x T : lenv_only Δ x T → lenv_only (lenv_ren f Δ) x (ty_ren f T).
Proof.
  intros [Hx Hy]. split; [unfold lenv_ren; by rewrite list_lookup_fmap, Hx|].
  intros y U Hne Hl. unfold lenv_ren in Hl. rewrite list_lookup_fmap in Hl.
  destruct (Δ !! y) as [[U'|]|] eqn:Hy'; simpl in Hl; try done. injection Hl as <-.
  apply unlimited_ren. by eapply Hy.
Qed.

Lemma lenv_split_ren f Δ Δ1 Δ2 : lenv_split Δ Δ1 Δ2 → lenv_split (lenv_ren f Δ) (lenv_ren f Δ1) (lenv_ren f Δ2).
Proof. induction 1; simpl; constructor; auto. by apply unlimited_ren. Qed.

Lemma tage_ren f c T T' : tage c T T' → tage c (ty_ren f T) (ty_ren f T').
Proof.
  induction 1; simpl; [apply age_free|apply age_sess|apply age_idle|apply age_arr|apply age_prod|apply age_sum|apply age_ex];
    auto using tfree_ren, idle_ren.
Qed.

Lemma lage_ren f c Δ Δ' : lage c Δ Δ' → lage c (lenv_ren f Δ) (lenv_ren f Δ').
Proof. induction 1; simpl; constructor; auto using tage_ren. Qed.

Lemma thage_ren f c Θ Θ' : thage c Θ Θ' → thage c (tenv_ren f Θ) (tenv_ren f Θ').
Proof.
  intros H o. specialize (H o). unfold tenv_ren. rewrite !lookup_fmap.
  destruct (Θ !! o), (Θ' !! o); simpl in *; try done. destruct H as (E1 & E2 & E3 & E4 & E5 & E6).
  simpl. rewrite E1, E2, E3, E5. split_and!; try done. destruct E4 as [E4|E4]; [by left|right; by apply idle_ren].
Qed.

Lemma sf_unionb_ren f F X b : sf_ren f (sf_unionb F X b) = sf_unionb (sf_ren f F) (set_map (pt_ren f) X) b.
Proof.
  destruct F as [X0 o], b; unfold sf_unionb, sf_ren; simpl; by rewrite set_map_union_L.
Qed.

Lemma abs_fut_ren f ub : sf_ren f (abs_fut ub) = abs_fut (ub_map (pt_ren f) ub).
Proof. destruct ub; unfold sf_ren; simpl; by rewrite set_map_empty. Qed.

Lemma lenv_pinst_ren f σ Δ : lenv_ren f (lenv_pinst σ Δ) = lenv_pinst (pt_ren f ∘ σ) (lenv_ren f Δ).
Proof.
  unfold lenv_ren, lenv_pinst. rewrite <-!list_fmap_compose. apply list_fmap_ext. intros _ [T|] _; simpl; [|done].
  by rewrite ty_ren_pinst.
Qed.

Lemma lenv_pinst_pshift_ren f m Δ : lenv_ren f (lenv_pinst (pshift m) Δ) = lenv_pinst (pshift m) (lenv_ren f Δ).
Proof.
  rewrite lenv_pinst_ren. unfold lenv_pinst. apply list_fmap_ext. intros _ [T|] _; simpl; [f_equal; by apply pinst_ty_ext|done].
Qed.

Lemma tenv_pinst_pshift_ren f m Θ : tenv_ren f (tenv_pinst (pshift m) Θ) = tenv_pinst (pshift m) (tenv_ren f Θ).
Proof.
  unfold tenv_ren, tenv_pinst. rewrite <-!map_fmap_compose. apply map_fmap_ext. intros _ e _.
  unfold tentry_ren, tentry_pinst. simpl. f_equal. apply pt_inst_pshift_ren.
Qed.

Lemma sf_pinst_pshift_ren f m F : sf_ren f (sf_pinst (pshift m) F) = sf_pinst (pshift m) (sf_ren f F).
Proof.
  destruct F as [X o]. unfold sf_ren, sf_pinst. simpl. f_equal.
  - apply set_eq. intros y. split.
    + intros (z & -> & Hz)%elem_of_map. apply elem_of_map in Hz as (w & -> & Hw). apply elem_of_map.
      exists (pt_ren f w). split; [apply pt_inst_pshift_ren|]. apply elem_of_map. by exists w.
    + intros (z & -> & Hz)%elem_of_map. apply elem_of_map in Hz as (w & -> & Hw). apply elem_of_map.
      exists (pt_inst (pshift m) w). split; [symmetry; apply pt_inst_pshift_ren|]. apply elem_of_map. by exists w.
  - rewrite <-!option_fmap_compose. apply option_fmap_ext. intros [u|]; simpl; try done;
      by rewrite pt_inst_pshift_ren.
Qed.

Lemma hc_open_ren f m C Γ : hctx_ren f (hc_open m C Γ) = hc_open m (bcs_ren f C) (hctx_ren f Γ).
Proof.
  unfold hctx_ren, hc_open, hyps_ren, hyps_inst. simpl. f_equal. rewrite fmap_app. f_equal.
  - rewrite <-!list_fmap_compose. apply list_fmap_ext. intros _ [C0 xs] _. simpl. f_equal.
    + apply bcs_inst_pshift_ren.
    + rewrite <-!list_fmap_compose. apply list_fmap_ext. intros. apply pt_inst_pshift_ren.
  - simpl. f_equal. f_equal; [apply bcs_inst_pshift_ren|]. unfold ids. rewrite <-list_fmap_compose. done.
Qed.

Lemma hctx_ren_inv f g Γ : (∀ a, f (g a) = a) → hctx_ren f (hctx_ren g Γ) = Γ.
Proof.
  intros H. destruct Γ as [Ψ]. unfold hctx_ren, hyps_ren. simpl. f_equal. rewrite <-list_fmap_compose.
  apply list_fmap_fix. intros [C xs]. simpl. rewrite bcs_ren_inv, <-list_fmap_compose by done. f_equal.
  apply list_fmap_fix. intros. simpl. by apply pt_ren_inv.
Qed.

(** ** Static worlds *)

Definition sw_ren (π : cbij) (W : sworld) : sworld :=
  SWorld (set_map (cb_f π) (sw_consts W)) (λ g, sw_facts W (fact_ren (cb_g π) g)).

Lemma sw_ren_join π W1 W2 : sw_ren π (W1 ⊔ W2) = sw_ren π W1 ⊔ sw_ren π W2.
Proof. unfold sw_ren, swjoin. simpl. by rewrite set_map_union_L. Qed.

Lemma sw_lt_ren π W x y : W ⊢ₛ x ≺ y → sw_ren π W ⊢ₛ pt_ren (cb_f π) x ≺ pt_ren (cb_f π) y.
Proof.
  assert (∀ x y, swstep W x y → swstep (sw_ren π W) (pt_ren (cb_f π) x) (pt_ren (cb_f π) y)) as Hs.
  { intros a b [a' b' H|a'|a']; [apply ws_fact; simpl; by rewrite !pt_ren_cb'|apply ws_po|apply ws_dpo]. }
  induction 1 as [x y H|x y z H _ IH]; [by apply tc_once, Hs|]. eapply tc_l; [by apply Hs|done].
Qed.

Lemma sw_lt_ren_inv π W x y : sw_ren π W ⊢ₛ x ≺ y → W ⊢ₛ pt_ren (cb_g π) x ≺ pt_ren (cb_g π) y.
Proof.
  assert (∀ x y, swstep (sw_ren π W) x y → swstep W (pt_ren (cb_g π) x) (pt_ren (cb_g π) y)) as Hs.
  { intros a b [a' b' H|a'|a']; [by apply ws_fact|apply ws_po|apply ws_dpo]. }
  induction 1 as [x y H|x y z H _ IH]; [by apply tc_once, Hs|]. eapply tc_l; [by apply Hs|done].
Qed.

Lemma croot_in_ren π S x : croot_in S x → croot_in (set_map (cb_f π) S) (pt_ren (cb_f π) x).
Proof.
  intros (a & Ha & HS). exists (cb_f π a). rewrite pt_ren_root, Ha. split; [done|]. set_solver.
Qed.

Lemma croot_in_ren_inv π S x : croot_in (set_map (cb_f π) S) x → croot_in S (pt_ren (cb_g π) x).
Proof.
  intros (a & Ha & HS). apply elem_of_map in HS as (b & -> & Hb). exists b.
  rewrite pt_ren_root, Ha. simpl. by rewrite cb_gf.
Qed.

Lemma sworld_wf_ren π W : sworld_wf W → sworld_wf (sw_ren π W).
Proof.
  intros Hwf. split. intros x y Hf. simpl in Hf. destruct (wf_facts _ Hwf _ _ Hf) as [Hx Hy].
  apply (croot_in_ren π) in Hx, Hy. rewrite !pt_ren_cb in Hx, Hy. done.
Qed.

Lemma swf_ren π W : swf W → swf (sw_ren π W).
Proof.
  intros [ρ Hρ]. exists (λ x, ρ (pt_ren (cb_g π) x)). intros x y H. apply Hρ. by apply sw_lt_ren_inv.
Qed.

Lemma sacyc_ren π W : sacyc W → sacyc (sw_ren π W).
Proof. intros H x Hx. exact (H _ (sw_lt_ren_inv π W x x Hx)). Qed.

Lemma wok_ren π N W : wok N W → wok N (sw_ren π W).
Proof. destruct N; [apply swf_ren|apply sacyc_ren]. Qed.

(** ** The fact theory *)

Lemma slt_world W1 W2 Γ x y : (∀ x y, W1 ⊢ₛ x ≺ y → W2 ⊢ₛ x ≺ y) → slt W1 Γ x y → slt W2 Γ x y.
Proof.
  intros HW. induction 1 as [x y H|x y H|x y z _ IH1 _ IH2]; [apply fl_w; auto|by apply fl_h|by eapply fl_trans].
Qed.

Lemma slt_ren π W Γ x y :
  slt W Γ x y → slt (sw_ren π W) (hctx_ren (cb_f π) Γ) (pt_ren (cb_f π) x) (pt_ren (cb_f π) y).
Proof.
  induction 1 as [x y H|x y (C & xs & Hin & Hat)|x y z _ IH1 _ IH2].
  - apply fl_w. by apply sw_lt_ren.
  - apply fl_h. exists (bcs_ren (cb_f π) C), (pt_ren (cb_f π) <$> xs). split.
    + unfold hctx_ren, hyps_ren. simpl. apply list_elem_of_fmap. by exists (C, xs).
    + exact (bcs_at_ren _ _ _ _ Hat).
  - by eapply fl_trans.
Qed.

Lemma slt_ren_inv π W Γ x y :
  slt (sw_ren π W) (hctx_ren (cb_f π) Γ) x y → slt W Γ (pt_ren (cb_g π) x) (pt_ren (cb_g π) y).
Proof.
  intros H. apply (slt_ren (cb_inv π)) in H. simpl in H.
  rewrite hctx_ren_inv in H by apply cb_gf. eapply slt_world; [|exact H].
  intros a b Hab. apply (sw_lt_ren_inv (cb_inv π)) in Hab. simpl in Hab. apply sw_lt_ren_inv in Hab.
  by rewrite !pt_ren_cb' in Hab.
Qed.

Lemma sle_ren π W Γ x y :
  sle W Γ x y → sle (sw_ren π W) (hctx_ren (cb_f π) Γ) (pt_ren (cb_f π) x) (pt_ren (cb_f π) y).
Proof. intros [->|H]; [by left|right; by apply slt_ren]. Qed.

Lemma hold_at_ren π W Γ C xs :
  hold_at W Γ C xs → hold_at (sw_ren π W) (hctx_ren (cb_f π) Γ) (bcs_ren (cb_f π) C) (pt_ren (cb_f π) <$> xs).
Proof.
  intros H x y Hxy. apply bcs_at_ren_inv in Hxy as ([x0 y0] & Hg & E). injection E as -> ->.
  by apply slt_ren, H.
Qed.

Lemma ub_below_s_ren π W Γ ub F :
  ub_below_s W Γ ub F → ub_below_s (sw_ren π W) (hctx_ren (cb_f π) Γ) (pt_ren (cb_f π) <$> ub) (sf_ren (cb_f π) F).
Proof.
  destruct ub as [x|]; simpl; [|done]. destruct F as [X o]. unfold sf_ren. simpl. intros (H1 & H2). split.
  - intros y Hy. apply elem_of_map in Hy as (y0 & -> & Hy0). by apply slt_ren, H1.
  - intros r Hr. destruct o as [r0|]; simpl in Hr; try done; injection Hr as <-;
      specialize (H2 r0 eq_refl); destruct r0; simpl in *; try done; by apply sle_ren.
Qed.

Lemma ub_below_u_ren π W Γ ub F :
  ub_below_u W Γ ub F → ub_below_u (sw_ren π W) (hctx_ren (cb_f π) Γ) (ub_map (pt_ren (cb_f π)) ub) (sf_ren (cb_f π) F).
Proof.
  destruct ub as [|x|]; simpl; try done.
  - apply (ub_below_s_ren π W Γ (Some x)).
  - intros ->. unfold sf_ren. simpl. by rewrite set_map_empty.
Qed.

Lemma lbx_below_h_ren π W Γ lb H b :
  lbx_below_h W Γ lb H b → lbx_below_h (sw_ren π W) (hctx_ren (cb_f π) Γ) (lb_map (pt_ren (cb_f π)) lb)
    (set_map (pt_ren (cb_f π)) H) b.
Proof.
  destruct lb as [| |x]; simpl; try done.
  - intros [-> ->]. by rewrite set_map_empty.
  - intros [H1 ->]. split; [|done]. intros y Hy. apply elem_of_map in Hy as (y0 & -> & Hy0). by apply sle_ren, H1.
Qed.

Lemma ex_wf_ren π W Γ lb m C T :
  ex_wf W Γ lb m C T → ex_wf (sw_ren π W) (hctx_ren (cb_f π) Γ) (lb_map (pt_ren (cb_f π)) lb) m
    (bcs_ren (cb_f π) C) (ty_ren (cb_f π) T).
Proof.
  unfold ex_wf. intros H. apply (lbx_below_h_ren π) in H. rewrite hc_open_ren, <-heads_ren in H.
  rewrite hbot_ren. rewrite lb_map_comp in H |- *.
  rewrite (lb_map_ext (pt_ren (cb_f π) ∘ pt_inst (pshift m)) (pt_inst (pshift m) ∘ pt_ren (cb_f π))) in H
    by (intros; apply pt_inst_pshift_ren). done.
Qed.

Lemma wf_new_ren f C : wf_new C → wf_new (bcs_ren f C).
Proof. unfold wf_new, new_step, bcs_ren. simpl. by rewrite length_fmap. Qed.

Lemma ids_ren f n : pt_ren f <$> ids n = ids n.
Proof. unfold ids. rewrite <-list_fmap_compose. apply list_fmap_ext. intros. apply pt_ren_pvar. Qed.

(** The bridge condition renames with the environment of C. Its facts
    speak of variables only. *)
Lemma outer_pt_ren f m C x : pn_vb (m + length (bc_env C)) (pt_name x) →
  outer_pt m (bcs_ren f C) x = pt_ren f (outer_pt m C x).
Proof.
  intros Hx. unfold outer_pt. rewrite pt_inst_plist_ren, fmap_app, ids_ren.
  assert (pt_ren f x = x) as ->; [|done].
  destruct x as [p b o]. unfold pt_ren. simpl in *. by rewrite (pn_ren_vb f _ p Hx).
Qed.

Lemma bridge_at_ren f m C z y : bridge_at m (bcs_ren f C) z y ↔ bridge_at m C z y.
Proof. unfold bridge_at, tree_step, cfact_at, bcs_ren. simpl. by rewrite length_fmap. Qed.

Lemma cons_open_ren π W Γ m C :
  cons_open W Γ m C → cons_open (sw_ren π W) (hctx_ren (cb_f π) Γ) m (bcs_ren (cb_f π) C).
Proof.
  intros H z y Hb. apply (proj1 (bridge_at_ren (cb_f π) m C z y)) in Hb.
  assert (pn_vb (m + length (bc_env C)) (pt_name z) ∧ pn_vb (m + length (bc_env C)) (pt_name y)) as [Hsz Hsy].
  { destruct Hb as (_ & _ & [[_ [? ?]]|(v & u & [_ [? _]] & _ & _ & [_ [_ ?]])]); by split. }
  rewrite !outer_pt_ren by done. by apply slt_ren, H.
Qed.

Lemma tsub_ren π W Γ T T' :
  tsub W Γ T T' → tsub (sw_ren π W) (hctx_ren (cb_f π) Γ) (ty_ren (cb_f π) T) (ty_ren (cb_f π) T').
Proof.
  induction 1; simpl.
  - apply sub_unit.
  - by apply sub_arr.
  - by apply sub_prod.
  - by apply sub_sum.
  - apply sub_box; [done|]. destruct k; [by apply teq_ren|].
    destruct H0 as [->|(He & H1 & H2)]; [by left|right]. rewrite !tcontr_ren. split_and!; [by apply teq_ren|done|done].
  - apply sub_sess; [by apply ssub_ren|done].
  - apply sub_ex; [| |by rewrite <-hc_open_ren].
    + apply (hold_at_ren π) in H. by rewrite hc_open_ren, bcs_inst_pshift_ren, ids_ren in H.
    + destruct H0 as [->|H0]; [by left|right]. exact (ex_wf_ren π W Γ lb' n C T H0).
Qed.

(** The constraint of a creation renames with its environment. Its facts
    speak of variables only. *)
Lemma ctx_pt_ren f C x : pn_vb (1 + length (bc_env C)) (pt_name x) →
  ctx_pt (bcs_ren f C) x = pt_ren f (ctx_pt C x).
Proof.
  intros Hx. unfold ctx_pt. rewrite pt_inst_plist_ren, fmap_cons, pt_ren_pvar.
  assert (pt_ren f x = x) as ->; [|done].
  destruct x as [p b o]. unfold pt_ren. simpl in *. by rewrite (pn_ren_vb f _ p Hx).
Qed.

Lemma gen_new_ren π W Γ C :
  gen_new W Γ C → gen_new (sw_ren π W) (hctx_ren (cb_f π) Γ) (bcs_ren (cb_f π) C).
Proof.
  assert (∀ x y, cfact (bcs_ren (cb_f π) C) x y ↔ cfact C x y) as Hc.
  { intros x y. unfold cfact, bcs_ren. simpl. by rewrite length_fmap. }
  assert (∀ x y, new_step (bcs_ren (cb_f π) C) x y ↔ new_step C x y) as Hn.
  { intros x y. unfold new_step, bcs_ren. simpl. by rewrite length_fmap. }
  assert (∀ x y, cfact C x y → ctx_pt (bcs_ren (cb_f π) C) x = pt_ren (cb_f π) (ctx_pt C x) ∧
    ctx_pt (bcs_ren (cb_f π) C) y = pt_ren (cb_f π) (ctx_pt C y)) as Hp.
  { intros x y [_ [Hx Hy]]. split; by apply ctx_pt_ren. }
  intros (Hwf & Hctx & Sr & H0 & H1 & H2 & H3). split_and!.
  - intros a. induction (Hwf a) as [a _ IH]. constructor. intros b Hb. by apply IH, Hn.
  - intros x y Hf Hx Hy. apply Hc in Hf. destruct (Hp _ _ Hf) as [-> ->]. by apply slt_ren, Hctx.
  - exists (λ s T', ∃ T, Sr s T ∧ T' = pt_ren (cb_f π) <$> T). split_and!.
    + intros s T' (T & HS & ->). destruct T as [|t T]; [exfalso; by apply (H0 s [] HS)|simpl; congruence].
    + intros u y Hf Hu Hy. apply Hc in Hf. destruct (H1 u y Hf Hu Hy) as (T & HS & Hlt).
      exists (pt_ren (cb_f π) <$> T). split; [by exists T|]. destruct (Hp _ _ Hf) as [_ ->].
      intros t' Ht'. apply list_elem_of_fmap in Ht' as (t & -> & Ht). by apply slt_ren, Hlt.
    + intros s T' s' (T & HS & ->) Hst. apply Hn in Hst. destruct (H2 s T s' HS Hst) as (T2 & HS2 & Hlt).
      exists (pt_ren (cb_f π) <$> T2). split; [by exists T2|].
      intros t2' Ht2'. apply list_elem_of_fmap in Ht2' as (t2 & -> & Ht2). destruct (Hlt t2 Ht2) as (t & Ht & Hl).
      exists (pt_ren (cb_f π) t). split; [by apply list_elem_of_fmap_2|by apply slt_ren].
    + intros s T' z (T & HS & ->) Hf Hz. apply Hc in Hf. destruct (H3 s T z HS Hf Hz) as (t & Ht & Hl).
      destruct (Hp _ _ Hf) as [-> _]. exists (pt_ren (cb_f π) t). split; [by apply list_elem_of_fmap_2|by apply slt_ren].
Qed.

Lemma acyc_new_ren π W Γ C :
  acyc_new W Γ C → acyc_new (sw_ren π W) (hctx_ren (cb_f π) Γ) (bcs_ren (cb_f π) C).
Proof.
  assert (∀ x y, cfact (bcs_ren (cb_f π) C) x y ↔ cfact C x y) as Hc.
  { intros x y. unfold cfact, bcs_ren. simpl. by rewrite length_fmap. }
  assert (∀ x y, new_step (bcs_ren (cb_f π) C) x y ↔ new_step C x y) as Hn.
  { intros x y. unfold new_step, bcs_ren. simpl. by rewrite length_fmap. }
  intros [Hcyc Hbr]. split.
  - assert (∀ p q, tc (new_step (bcs_ren (cb_f π) C)) p q → tc (new_step C) p q) as Ht.
    { intros p q H. induction H as [p q H|p q r H _ IH]; [apply tc_once; by apply Hn|].
      eapply tc_l; [apply Hn; exact H|exact IH]. }
    intros x Hx Hc'. exact (Hcyc x Hx (Ht x x Hc')).
  - by apply cons_open_ren.
Qed.

Lemma new_ok_ren π N W Γ C :
  new_ok N W Γ C → new_ok N (sw_ren π W) (hctx_ren (cb_f π) Γ) (bcs_ren (cb_f π) C).
Proof.
  intros [Ha Hr]. destruct N as [n|].
  - apply gen_new_ok, gen_new_ren, (new_ok_gen (Some n)); [done|by split].
  - by apply acyc_new_ok, acyc_new_ren.
Qed.
