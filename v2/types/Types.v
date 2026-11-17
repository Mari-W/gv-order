(** * Types with points, credits and costs (stage S2, proposal §2.5, §2.17)

    T, U ::= ∗ | T^a ⊸^u_l[c ; ϑ ; h] U^b | T^a ⊗ U^b | T^a ⊕ U^b | S@x
           | □(∀ιs αs. C. ∗ ⊸^u[c ; ϑ] U^b) | ∃^lb ιs. C. T^a
    S    ::= Skip | S;S | ?(∃ιs. T^b) | !(∃ιs. T^b) | ⊕(S, S) | &(S, S)
           | Close | µα.S | α | α‾

    Session types are the context-free session types of the old
    development, read through their head normal form [unfoldS]. There is
    no point type: programs never mention a point (decision Q1).

    Decision Q11 puts the cost annotations of the cost judgment into the
    types. A credit a (a lower bound on the counters of the ends a value
    holds) annotates the argument and result of an arrow, the components
    of a product and a sum, the body of an existential and every payload.
    The arrow carries a cost c, a ticket transformer ϑ and a floor h,
    and the box the cost and transformer of one force. The credit of the
    value a judgment types is the a of T^a in the judgment. The credit of
    a product, a sum or an existential is added to its parts. The
    deadlock-freedom relations ignore every annotation. [ty_df] sets them
    to the values of the instance N = ∞. *)

From GV Require Export types.Costs types.Worlds.

Inductive ty :=
  | TUnit
  | TLolli (ub lb : option point) (c : fuel) (t : tix) (h : fuel)
      (T : ty) (aT : fuel) (U : ty) (aU : fuel)
  | TProd (T : ty) (a : fuel) (U : ty) (b : fuel)
  | TSum (T : ty) (a : fuel) (U : ty) (b : fuel)
  | TBox (n k : nat) (C : bcs) (ub : option point) (c : fuel) (t : tix)
      (U : ty) (aU : fuel)
  | TSess (S : sty) (x : point)
  | TEx (lb : lbound) (n : nat) (C : bcs) (T : ty) (aT : fuel)
with sty :=
  | SRcv (m : nat) (T : ty) (b : fuel)   (* ?(∃ι₀…ιₘ₋₁. T^b) *)
  | SSnd (m : nat) (T : ty) (b : fuel)   (* !(∃ι₀…ιₘ₋₁. T^b) *)
  | SEnd                                 (* Close *)
  | SMu (S : sty)                        (* µα.S *)
  | SVar (a : nat)                       (* α *)
  | SVarD (a : nat)                      (* α‾, enters through [dual] *)
  | SSkip
  | SSeq (S1 S2 : sty)
  | SPlus (S1 S2 : sty)
  | SWith (S1 S2 : sty).

Scheme ty_mut_ind := Induction for ty Sort Prop
  with sty_mut_ind := Induction for sty Sort Prop.
Combined Scheme ty_sty_mut_ind from ty_mut_ind, sty_mut_ind.

Notation "S @ x" := (TSess S x) (at level 20, format "S @ x").

(** ** Point instantiation

    Session types are instantiated too, because a payload ∃ιs.T may
    mention outer points. *)

Fixpoint pinst_ty (σ : nat → point) (T : ty) : ty :=
  match T with
  | TUnit => TUnit
  | TLolli ub lb c t h T1 a1 U a2 =>
      TLolli (pt_inst σ <$> ub) (pt_inst σ <$> lb) c t h (pinst_ty σ T1) a1 (pinst_ty σ U) a2
  | TProd T1 a1 U a2 => TProd (pinst_ty σ T1) a1 (pinst_ty σ U) a2
  | TSum T1 a1 U a2 => TSum (pinst_ty σ T1) a1 (pinst_ty σ U) a2
  | TBox n k C ub c t U a =>
      TBox n k (bcs_inst σ C) (pt_inst (pup n σ) <$> ub) c t (pinst_ty (pup n σ) U) a
  | TSess s x => TSess (pinst_sty σ s) (pt_inst σ x)
  | TEx lb n C T1 a =>
      TEx (lb_map (pt_inst σ) lb) n (bcs_inst σ C) (pinst_ty (pup n σ) T1) a
  end
with pinst_sty (σ : nat → point) (s : sty) : sty :=
  match s with
  | SRcv m T b => SRcv m (pinst_ty (pup m σ) T) b
  | SSnd m T b => SSnd m (pinst_ty (pup m σ) T) b
  | SMu s' => SMu (pinst_sty σ s')
  | SSeq s1 s2 => SSeq (pinst_sty σ s1) (pinst_sty σ s2)
  | SPlus s1 s2 => SPlus (pinst_sty σ s1) (pinst_sty σ s2)
  | SWith s1 s2 => SWith (pinst_sty σ s1) (pinst_sty σ s2)
  | s => s
  end.

(** T[xs/ιs]. *)
Definition ty_inst (xs : list point) (T : ty) : ty := pinst_ty (plist xs) T.

(** The payload ∃ι₀…ιₘ₋₁. T at the carrier x: T[x·i/ιᵢ]. *)
Definition payload_at (m : nat) (T : ty) (x : point) : ty :=
  ty_inst (payload_pts x m) T.

Lemma payload_at_dual m T x : payload_at m T x‾ = payload_at m T x.
Proof. done. Qed.

Lemma pinst_mut_ext :
  (∀ T σ τ, (∀ a, σ a = τ a) → pinst_ty σ T = pinst_ty τ T) ∧
  (∀ s σ τ, (∀ a, σ a = τ a) → pinst_sty σ s = pinst_sty τ s).
Proof.
  apply ty_sty_mut_ind; intros; simpl; try done.
  - rewrite (H σ τ), (H0 σ τ) by done.
    rewrite !(option_fmap_ext (pt_inst σ) (pt_inst τ)) by (intros; by apply pt_inst_ext). done.
  - by rewrite (H σ τ), (H0 σ τ).
  - by rewrite (H σ τ), (H0 σ τ).
  - rewrite (H (pup n σ) (pup n τ)) by (intros; by apply pup_ext).
    rewrite (bcs_inst_ext σ τ) by done.
    rewrite !(option_fmap_ext (pt_inst (pup n σ)) (pt_inst (pup n τ)))
      by (intros; apply pt_inst_ext; intros; by apply pup_ext). done.
  - by rewrite (H σ τ), (pt_inst_ext σ τ).
  - rewrite (H (pup n σ) (pup n τ)) by (intros; by apply pup_ext).
    rewrite (bcs_inst_ext σ τ), (lb_map_ext _ (pt_inst τ)) by first [done|intros; by apply pt_inst_ext]. done.
  - by rewrite (H (pup m σ) (pup m τ)) by (intros; by apply pup_ext).
  - by rewrite (H (pup m σ) (pup m τ)) by (intros; by apply pup_ext).
  - by rewrite (H σ τ).
  - by rewrite (H σ τ), (H0 σ τ).
  - by rewrite (H σ τ), (H0 σ τ).
  - by rewrite (H σ τ), (H0 σ τ).
Qed.

Lemma pinst_ty_ext T σ τ : (∀ a, σ a = τ a) → pinst_ty σ T = pinst_ty τ T.
Proof. apply pinst_mut_ext. Qed.
Lemma pinst_sty_ext s σ τ : (∀ a, σ a = τ a) → pinst_sty σ s = pinst_sty τ s.
Proof. apply pinst_mut_ext. Qed.

Lemma pinst_mut_comp :
  (∀ T σ τ, pinst_ty τ (pinst_ty σ T) = pinst_ty (pt_inst τ ∘ σ) T) ∧
  (∀ s σ τ, pinst_sty τ (pinst_sty σ s) = pinst_sty (pt_inst τ ∘ σ) s).
Proof.
  apply ty_sty_mut_ind; intros; simpl; try done.
  - rewrite H, H0, <-!option_fmap_compose.
    rewrite !(option_fmap_ext (pt_inst τ ∘ pt_inst σ) (pt_inst (pt_inst τ ∘ σ)))
      by (intros; apply pt_inst_comp). done.
  - by rewrite H, H0.
  - by rewrite H, H0.
  - rewrite H, bcs_inst_comp, <-option_fmap_compose.
    rewrite (pinst_ty_ext U _ (pup n (pt_inst τ ∘ σ))) by (intros; apply pup_comp).
    rewrite (option_fmap_ext (pt_inst (pup n τ) ∘ pt_inst (pup n σ)) (pt_inst (pup n (pt_inst τ ∘ σ))))
      by (intros; simpl; rewrite pt_inst_comp; apply pt_inst_ext; intros; apply pup_comp). done.
  - by rewrite H, pt_inst_comp.
  - rewrite H, bcs_inst_comp, lb_map_comp.
    rewrite (pinst_ty_ext T _ (pup n (pt_inst τ ∘ σ))) by (intros; apply pup_comp).
    rewrite (lb_map_ext (pt_inst τ ∘ pt_inst σ) (pt_inst (pt_inst τ ∘ σ))) by (intros; apply pt_inst_comp).
    done.
  - rewrite H. by rewrite (pinst_ty_ext T _ (pup m (pt_inst τ ∘ σ))) by (intros; apply pup_comp).
  - rewrite H. by rewrite (pinst_ty_ext T _ (pup m (pt_inst τ ∘ σ))) by (intros; apply pup_comp).
  - by rewrite H.
  - by rewrite H, H0.
  - by rewrite H, H0.
  - by rewrite H, H0.
Qed.

Lemma pinst_ty_comp T σ τ : pinst_ty τ (pinst_ty σ T) = pinst_ty (pt_inst τ ∘ σ) T.
Proof. apply pinst_mut_comp. Qed.
Lemma pinst_sty_comp s σ τ : pinst_sty τ (pinst_sty σ s) = pinst_sty (pt_inst τ ∘ σ) s.
Proof. apply pinst_mut_comp. Qed.

Lemma pinst_mut_pvar :
  (∀ T, pinst_ty pvar T = T) ∧ (∀ s, pinst_sty pvar s = s).
Proof.
  apply ty_sty_mut_ind; intros; simpl; try done.
  - rewrite H, H0. destruct ub, lb; simpl; by rewrite ?pt_inst_pvar.
  - by rewrite H, H0.
  - by rewrite H, H0.
  - rewrite (pinst_ty_ext U _ pvar), H by apply pup_pvar. rewrite bcs_inst_pvar.
    destruct ub; simpl; [|done]. rewrite (pt_inst_ext _ pvar), pt_inst_pvar by apply pup_pvar. done.
  - by rewrite H, pt_inst_pvar.
  - rewrite (pinst_ty_ext T _ pvar), H by apply pup_pvar. rewrite bcs_inst_pvar.
    by rewrite lb_map_id by apply pt_inst_pvar.
  - by rewrite (pinst_ty_ext T _ pvar), H by apply pup_pvar.
  - by rewrite (pinst_ty_ext T _ pvar), H by apply pup_pvar.
  - by rewrite H.
  - by rewrite H, H0.
  - by rewrite H, H0.
  - by rewrite H, H0.
Qed.

Lemma pinst_ty_pvar T : pinst_ty pvar T = T.
Proof. apply pinst_mut_pvar. Qed.
Lemma pinst_sty_pvar s : pinst_sty pvar s = s.
Proof. apply pinst_mut_pvar. Qed.

(** ** Heads and the ⊥ flag

    heads(S@x) = {x‾}: a thread blocked at u that holds an end at v owes
    u ≺ v‾. The lower point of an arrow and of an existential are heads.
    The ⊥ flag says a value may hold an unopened existential whose ends
    sit at points not known from outside. *)

Definition opt_heads (o : option point) : gset point :=
  match o with Some x => {[x]} | None => ∅ end.

Definition lb_heads (lb : lbound) : gset point :=
  match lb with LPt x => {[x]} | _ => ∅ end.

Fixpoint heads (T : ty) : gset point :=
  match T with
  | TUnit | TBox _ _ _ _ _ _ _ _ => ∅
  | TLolli _ lb _ _ _ _ _ _ _ => opt_heads lb
  | TProd T1 _ U _ | TSum T1 _ U _ => heads T1 ∪ heads U
  | TSess _ x => {[x‾]}
  | TEx lb _ _ _ _ => lb_heads lb
  end.

Fixpoint hbot (T : ty) : bool :=
  match T with
  | TProd T1 _ U _ | TSum T1 _ U _ => hbot T1 || hbot U
  | TEx LBot _ _ _ _ => true
  | _ => false
  end.

Lemma hbot_pinst σ T : hbot (pinst_ty σ T) = hbot T.
Proof. induction T; simpl; try done; try congruence. by destruct lb. Qed.

Lemma opt_heads_pinst σ o : opt_heads (pt_inst σ <$> o) = set_map (pt_inst σ) (opt_heads o).
Proof. destruct o; simpl; set_solver. Qed.

Lemma heads_pinst σ T : heads (pinst_ty σ T) = set_map (pt_inst σ) (heads T).
Proof.
  induction T; simpl; rewrite ?set_map_union_L, ?IHT1, ?IHT2; try set_solver.
  - apply opt_heads_pinst.
  - rewrite set_map_singleton_L. by rewrite pt_inst_dual.
  - destruct lb; simpl; set_solver.
Qed.

(** ** Session substitution, duality, unfolding (ported) *)

Fixpoint sren_ty (r : nat → nat) (T : ty) : ty :=
  match T with
  | TUnit => TUnit
  | TLolli ub lb c t h T1 a1 U a2 => TLolli ub lb c t h (sren_ty r T1) a1 (sren_ty r U) a2
  | TProd T1 a1 U a2 => TProd (sren_ty r T1) a1 (sren_ty r U) a2
  | TSum T1 a1 U a2 => TSum (sren_ty r T1) a1 (sren_ty r U) a2
  | TBox n k C ub c t U a => TBox n k C ub c t (sren_ty (Nat.iter k upren r) U) a
  | TSess s x => TSess (sren r s) x
  | TEx lb n C T1 a => TEx lb n C (sren_ty r T1) a
  end
with sren (r : nat → nat) (s : sty) : sty :=
  match s with
  | SRcv m T b => SRcv m (sren_ty r T) b
  | SSnd m T b => SSnd m (sren_ty r T) b
  | SEnd => SEnd
  | SMu s' => SMu (sren (upren r) s')
  | SVar a => SVar (r a)
  | SVarD a => SVarD (r a)
  | SSkip => SSkip
  | SSeq s1 s2 => SSeq (sren r s1) (sren r s2)
  | SPlus s1 s2 => SPlus (sren r s1) (sren r s2)
  | SWith s1 s2 => SWith (sren r s1) (sren r s2)
  end.

(** [sflip k] swaps α ↔ α‾ at level k. *)
Fixpoint sflip_ty (k : nat) (T : ty) : ty :=
  match T with
  | TUnit => TUnit
  | TLolli ub lb c t h T1 a1 U a2 => TLolli ub lb c t h (sflip_ty k T1) a1 (sflip_ty k U) a2
  | TProd T1 a1 U a2 => TProd (sflip_ty k T1) a1 (sflip_ty k U) a2
  | TSum T1 a1 U a2 => TSum (sflip_ty k T1) a1 (sflip_ty k U) a2
  | TBox n kk C ub c t U a => TBox n kk C ub c t (sflip_ty (kk + k) U) a
  | TSess s x => TSess (sflip k s) x
  | TEx lb n C T1 a => TEx lb n C (sflip_ty k T1) a
  end
with sflip (k : nat) (s : sty) : sty :=
  match s with
  | SRcv m T b => SRcv m (sflip_ty k T) b
  | SSnd m T b => SSnd m (sflip_ty k T) b
  | SEnd => SEnd
  | SMu s' => SMu (sflip (S k) s')
  | SVar a => if decide (a = k) then SVarD a else SVar a
  | SVarD a => if decide (a = k) then SVar a else SVarD a
  | SSkip => SSkip
  | SSeq s1 s2 => SSeq (sflip k s1) (sflip k s2)
  | SPlus s1 s2 => SPlus (sflip k s1) (sflip k s2)
  | SWith s1 s2 => SWith (sflip k s1) (sflip k s2)
  end.

(** Polarized duality (Gay, Thiemann and Vasconcelos). Payloads stay. *)
Fixpoint dual (s : sty) : sty :=
  match s with
  | SRcv m T b => SSnd m T b
  | SSnd m T b => SRcv m T b
  | SEnd => SEnd
  | SMu s' => SMu (sflip 0 (dual s'))
  | SVar a => SVarD a
  | SVarD a => SVar a
  | SSkip => SSkip
  | SSeq s1 s2 => SSeq (dual s1) (dual s2)
  | SPlus s1 s2 => SWith (dual s1) (dual s2)
  | SWith s1 s2 => SPlus (dual s1) (dual s2)
  end.

Definition sty_up (σ : nat → sty) : nat → sty := SVar 0 .: (sren S ∘ σ).

Fixpoint sinst_ty (σ : nat → sty) (T : ty) : ty :=
  match T with
  | TUnit => TUnit
  | TLolli ub lb c t h T1 a1 U a2 => TLolli ub lb c t h (sinst_ty σ T1) a1 (sinst_ty σ U) a2
  | TProd T1 a1 U a2 => TProd (sinst_ty σ T1) a1 (sinst_ty σ U) a2
  | TSum T1 a1 U a2 => TSum (sinst_ty σ T1) a1 (sinst_ty σ U) a2
  | TBox n k C ub c t U a => TBox n k C ub c t (sinst_ty (Nat.iter k sty_up σ) U) a
  | TSess s x => TSess (sinst σ s) x
  | TEx lb n C T1 a => TEx lb n C (sinst_ty σ T1) a
  end
with sinst (σ : nat → sty) (s : sty) : sty :=
  match s with
  | SRcv m T b => SRcv m (sinst_ty σ T) b
  | SSnd m T b => SSnd m (sinst_ty σ T) b
  | SEnd => SEnd
  | SMu s' => SMu (sinst (sty_up σ) s')
  | SVar a => σ a
  | SVarD a => dual (σ a)
  | SSkip => SSkip
  | SSeq s1 s2 => SSeq (sinst σ s1) (sinst σ s2)
  | SPlus s1 s2 => SPlus (sinst σ s1) (sinst σ s2)
  | SWith s1 s2 => SWith (sinst σ s1) (sinst σ s2)
  end.

Definition unroll (s : sty) : sty := sinst (SMu s .: SVar) s.

Definition slist (ss : list sty) : nat → sty :=
  λ a, match ss !! a with Some s => s | None => SVar (a - length ss) end.

Definition hseq (h s2 : sty) : sty :=
  match h with
  | SSeq o SSkip => SSeq o s2
  | SSeq o r => SSeq o (SSeq r s2)
  | SPlus a b => SPlus (SSeq a s2) (SSeq b s2)
  | SWith a b => SWith (SSeq a s2) (SSeq b s2)
  | _ => h
  end.

Fixpoint unrN (k : nat) (s : sty) : option sty :=
  match k with
  | 0 => None
  | S k' =>
      match s with
      | SSkip => Some SSkip
      | SSeq s1 s2 =>
          match unrN k' s1 with
          | Some SSkip => unrN k' s2
          | Some h => Some (hseq h s2)
          | None => None
          end
      | SRcv m T b => Some (SSeq (SRcv m T b) SSkip)
      | SSnd m T b => Some (SSeq (SSnd m T b) SSkip)
      | SVar a => Some (SSeq (SVar a) SSkip)
      | SVarD a => Some (SSeq (SVarD a) SSkip)
      | SMu b => unrN k' (unroll b)
      | SEnd => Some SEnd
      | SPlus a b => Some (SPlus a b)
      | SWith a b => Some (SWith a b)
      end
  end.

Fixpoint sfuel (s : sty) : nat :=
  match s with
  | SSeq a b => S (sfuel a + sfuel b)
  | SMu b => S (sfuel b)
  | _ => 1
  end.

(** unr(S), the head normal form, or S itself when none appears. *)
Definition unfoldS (s : sty) : sty :=
  match unrN (sfuel s) s with Some h => h | None => s end.

Inductive hview :=
  | HSkip
  | HRcv (m : nat) (T : ty) (b : fuel) (s : sty)
  | HSnd (m : nat) (T : ty) (b : fuel) (s : sty)
  | HVar (a : nat) (s : sty)
  | HVarD (a : nat) (s : sty)
  | HPlus (s1 s2 : sty)
  | HWith (s1 s2 : sty)
  | HEnd
  | HStuck (u : sty).

Definition view (u : sty) : hview :=
  match u with
  | SSkip => HSkip
  | SSeq (SRcv m T b) s => HRcv m T b s
  | SSeq (SSnd m T b) s => HSnd m T b s
  | SSeq (SVar a) s => HVar a s
  | SSeq (SVarD a) s => HVarD a s
  | SPlus a b => HPlus a b
  | SWith a b => HWith a b
  | SEnd => HEnd
  | u => HStuck u
  end.

Definition unview (h : hview) : sty :=
  match h with
  | HSkip => SSkip
  | HRcv m T b s => SSeq (SRcv m T b) s
  | HSnd m T b s => SSeq (SSnd m T b) s
  | HVar a s => SSeq (SVar a) s
  | HVarD a s => SSeq (SVarD a) s
  | HPlus a b => SPlus a b
  | HWith a b => SWith a b
  | HEnd => SEnd
  | HStuck u => u
  end.

Lemma unview_view u : unview (view u) = u.
Proof. destruct u as [| | | | | | |o r| |]; try done. by destruct o. Qed.

Definition hd (s : sty) : hview := view (unfoldS s).

Lemma unfoldS_unview s : unfoldS s = unview (hd s).
Proof. unfold hd. by rewrite unview_view. Qed.

Lemma hd_of s u : unfoldS s = u → hd s = view u.
Proof. unfold hd. by intros ->. Qed.

Definition hc_step (τ : sty → Prop) (s : sty) : Prop :=
  match hd s with
  | HSkip | HEnd => True
  | HRcv _ _ _ s' | HSnd _ _ _ s' | HVar _ s' | HVarD _ s' => τ s'
  | HPlus a b | HWith a b => τ a ∧ τ b
  | HStuck _ => False
  end.

Fixpoint ahc (n : nat) (s : sty) : Prop :=
  match n with 0 => True | S n' => hc_step (ahc n') s end.

Definition hcontractive (s : sty) : Prop := ∀ n, ahc n s.

(** ** Session equivalence, coinductive through heads (ported)

    Annotations compare on the nose, sessions by the parameter. *)

Fixpoint eqT (ρ : sty → sty → Prop) (T U : ty) : Prop :=
  match T, U with
  | TUnit, TUnit => True
  | TLolli ub lb c t h T1 a1 T2 a2, TLolli ub' lb' c' t' h' U1 a1' U2 a2' =>
      ub = ub' ∧ lb = lb' ∧ c = c' ∧ t = t' ∧ h = h' ∧ a1 = a1' ∧ a2 = a2' ∧
      eqT ρ T1 U1 ∧ eqT ρ T2 U2
  | TProd T1 a1 T2 a2, TProd U1 a1' U2 a2' | TSum T1 a1 T2 a2, TSum U1 a1' U2 a2' =>
      a1 = a1' ∧ a2 = a2' ∧ eqT ρ T1 U1 ∧ eqT ρ T2 U2
  | TBox n k C ub c t T1 a, TBox n' k' C' ub' c' t' U1 a' =>
      n = n' ∧ k = k' ∧ C = C' ∧ ub = ub' ∧ c = c' ∧ t = t' ∧ a = a' ∧
      match k with 0 => eqT ρ T1 U1 | S _ => T1 = U1 end
  | TSess s x, TSess r y => x = y ∧ ρ s r
  | TEx lb n C T1 a, TEx lb' n' C' U1 a' => lb = lb' ∧ n = n' ∧ C = C' ∧ a = a' ∧ eqT ρ T1 U1
  | _, _ => False
  end.

Definition eq_step (τ : sty → sty → Prop) (s r : sty) : Prop :=
  match hd s, hd r with
  | HSkip, HSkip | HEnd, HEnd => True
  | HRcv m T b s', HRcv m' U b' r' | HSnd m T b s', HSnd m' U b' r' =>
      m = m' ∧ b = b' ∧ eqT τ T U ∧ τ s' r'
  | HVar a s', HVar a' r' | HVarD a s', HVarD a' r' => a = a' ∧ τ s' r'
  | HPlus s1 s2, HPlus r1 r2 | HWith s1 s2, HWith r1 r2 => τ s1 r1 ∧ τ s2 r2
  | HStuck u, HStuck v => u = v
  | _, _ => False
  end.

Fixpoint aeq (n : nat) (s r : sty) : Prop :=
  match n with 0 => True | S n' => eq_step (aeq n') s r end.

(** S ≈ R. *)
Definition sequiv (s r : sty) : Prop := ∀ n, aeq n s r.
Definition teq (T U : ty) : Prop := eqT sequiv T U.

Lemma eqT_mono ρ ρ' T : ∀ U,
  (∀ s r, ρ s r → ρ' s r) → eqT ρ T U → eqT ρ' T U.
Proof. induction T; intros [] Hρ; simpl; repeat case_match; naive_solver. Qed.

Lemma eqT_refl ρ T : (∀ s, ρ s s) → eqT ρ T T.
Proof. intros Hρ. induction T; simpl; repeat case_match; split_and?; auto. Qed.

Lemma eqT_sym ρ T : ∀ U, (∀ s r, ρ s r → ρ r s) → eqT ρ T U → eqT ρ U T.
Proof. induction T; intros [] Hρ; simpl; repeat case_match; naive_solver. Qed.

Lemma eqT_trans ρ T : ∀ U V,
  (∀ s r t, ρ s r → ρ r t → ρ s t) → eqT ρ T U → eqT ρ U V → eqT ρ T V.
Proof. induction T; intros [] []; simpl; repeat case_match; naive_solver. Qed.

Ltac hd_cases s := destruct (hd s) as [|?m ?T ?b ?s'|?m ?T ?b ?s'|?a ?s'|?a ?s'|?s1 ?s2|?s1 ?s2| |?u].

Lemma eq_step_mono τ τ' s r : (∀ a b, τ a b → τ' a b) → eq_step τ s r → eq_step τ' s r.
Proof.
  unfold eq_step. intros Hτ. hd_cases s; hd_cases r; try done; intuition eauto using eqT_mono.
Qed.

Lemma sequiv_coind (τ : sty → sty → Prop) :
  (∀ s r, τ s r → eq_step τ s r) → ∀ s r, τ s r → sequiv s r.
Proof.
  intros Hτ s r Hsr n. revert s r Hsr.
  induction n as [|n IH]; intros s r Hsr; [done|].
  eapply eq_step_mono; [exact IH|by apply Hτ].
Qed.

Lemma aeq_refl n : ∀ s, aeq n s s.
Proof.
  induction n as [|n IH]; intros s; [done|].
  unfold aeq; fold aeq. unfold eq_step.
  hd_cases s; try done; split_and!; auto using eqT_refl.
Qed.

Lemma aeq_sym n : ∀ s r, aeq n s r → aeq n r s.
Proof.
  induction n as [|n IH]; intros s r H; [done|].
  unfold aeq in *; fold aeq in *. unfold eq_step in *.
  hd_cases s; hd_cases r; try done; try (by symmetry);
    intuition (subst; eauto using eqT_sym).
Qed.

Lemma aeq_trans n : ∀ s r t, aeq n s r → aeq n r t → aeq n s t.
Proof.
  induction n as [|n IH]; intros s r t H1 H2; [done|].
  unfold aeq in *; fold aeq in *. unfold eq_step in *.
  hd_cases s; hd_cases r; try done; hd_cases t; try done; try congruence;
    intuition (subst; eauto using eqT_trans).
Qed.

Lemma sequiv_refl s : sequiv s s.
Proof. intros n. apply aeq_refl. Qed.
Lemma sequiv_sym s r : sequiv s r → sequiv r s.
Proof. intros H n. by apply aeq_sym. Qed.
Lemma sequiv_trans s r t : sequiv s r → sequiv r t → sequiv s t.
Proof. intros H1 H2 n. by eapply aeq_trans. Qed.

Lemma teq_refl T : teq T T.
Proof. apply eqT_refl, sequiv_refl. Qed.
Lemma teq_sym T U : teq T U → teq U T.
Proof. apply eqT_sym, sequiv_sym. Qed.
Lemma teq_trans T U V : teq T U → teq U V → teq T V.
Proof. apply eqT_trans. intros ???. apply sequiv_trans. Qed.

(** ** Kinds of types *)

Inductive prim : ty → Prop :=
  | prim_unit : prim TUnit
  | prim_prod U a V b : prim U → prim V → prim (TProd U a V b)
  | prim_sum U a V b : prim U → prim V → prim (TSum U a V b)
  | prim_box n k C ub c t U a : prim U → prim (TBox n k C ub c t U a).

(** The types whose variables admit contraction and weakening. *)
Definition unlimited (T : ty) : Prop :=
  match T with TBox _ _ _ _ _ _ _ _ => True | _ => False end.

(** Finite evidence that a type holds no end. Its credit says nothing,
    so aging and capture leave it alone. *)
Inductive tfree : ty → Prop :=
  | tfree_unit : tfree TUnit
  | tfree_box n k C ub c t U a : tfree (TBox n k C ub c t U a)
  | tfree_prod T a U b : tfree T → tfree U → tfree (TProd T a U b)
  | tfree_sum T a U b : tfree T → tfree U → tfree (TSum T a U b).

Lemma unlimited_tfree T : unlimited T → tfree T.
Proof. destruct T; try done. intros _. constructor. Qed.

Lemma unlimited_pinst σ U : unlimited U → unlimited (pinst_ty σ U).
Proof. by destruct U. Qed.

Lemma tfree_pinst σ T : tfree T → tfree (pinst_ty σ T).
Proof. induction 1; simpl; constructor; auto. Qed.

(** ** The annotations of the instance N = ∞

    [cr_df T] is the credit of a value of T in a derivation at N = ∞:
    0 for a product, a sum and an existential, whose parts carry ∞, and
    ∞ otherwise. [ty_df] sets every annotation inside a type to these
    values, every cost to ∞, every transformer to (∞, ∞) and every floor
    to ∞. *)

Definition cr_df (T : ty) : fuel :=
  match T with TProd _ _ _ _ | TSum _ _ _ _ | TEx _ _ _ _ _ => Some 0 | _ => None end.

Fixpoint ty_df (T : ty) : ty :=
  match T with
  | TUnit => TUnit
  | TLolli ub lb _ _ _ T1 _ U _ =>
      TLolli ub lb None tinf None (ty_df T1) (cr_df T1) (ty_df U) (cr_df U)
  | TProd T1 _ U _ => TProd (ty_df T1) (cr_df T1) (ty_df U) (cr_df U)
  | TSum T1 _ U _ => TSum (ty_df T1) (cr_df T1) (ty_df U) (cr_df U)
  | TBox n k C ub _ _ U _ => TBox n k C ub None tinf (ty_df U) (cr_df U)
  | TSess s x => TSess (sty_df s) x
  | TEx lb n C T1 _ => TEx lb n C (ty_df T1) (cr_df T1)
  end
with sty_df (s : sty) : sty :=
  match s with
  | SRcv m T _ => SRcv m (ty_df T) (cr_df T)
  | SSnd m T _ => SSnd m (ty_df T) (cr_df T)
  | SMu s' => SMu (sty_df s')
  | SSeq s1 s2 => SSeq (sty_df s1) (sty_df s2)
  | SPlus s1 s2 => SPlus (sty_df s1) (sty_df s2)
  | SWith s1 s2 => SWith (sty_df s1) (sty_df s2)
  | s => s
  end.

Lemma cr_df_df T : cr_df (ty_df T) = cr_df T.
Proof. by destruct T. Qed.

Lemma df_mut_idem : (∀ T, ty_df (ty_df T) = ty_df T) ∧ (∀ s, sty_df (sty_df s) = sty_df s).
Proof. apply ty_sty_mut_ind; intros; simpl; rewrite ?cr_df_df; congruence. Qed.

Lemma ty_df_idem T : ty_df (ty_df T) = ty_df T.
Proof. apply df_mut_idem. Qed.
Lemma sty_df_idem s : sty_df (sty_df s) = sty_df s.
Proof. apply df_mut_idem. Qed.
