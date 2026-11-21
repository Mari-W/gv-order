(** * Types with points, credits and costs (stage S2, proposal §2.5, §2.17)

    T, U ::= ∗ | (T ⊸^u_l[c ; ϑ] U)^a | T ⊗ U | T ⊕ U | (S@x)^a
           | □(∀ιs αs. C. ∗ ⊸^u[c ; ϑ] U) | ∃^lb ιs. C. T
    S    ::= Skip | S;S | ?(∃ιs. T) | !(∃ιs. T) | ⊕(S, S) | &(S, S)
           | Close | µα.S | α | α‾

    Session types are the context-free session types of the old
    development, read through their head normal form [unfoldS]. There is
    no point type: programs never mention a point (decision Q1).

    Decision Q11 puts the cost annotations of the cost judgment into the
    types. A credit a sits only where ends sit (decision of 2026-11-19):
    on an end (S@x)^a, a lower bound on its counter, and on a closure
    (T ⊸ U)^a, a lower bound on the counters of the ends it captured
    and the most those counters may lose before a call (decision of
    2026-11-20, per-end capture). Products, sums, existentials, box results and
    payloads carry no credit, their ends carry their own. The arrow
    carries a cost c and a ticket transformer ϑ, and the box
    the cost and transformer of one force. The deadlock-freedom
    relations ignore every annotation. [ty_df] sets them to the values
    of the instance N = ∞. *)

From GV Require Export types.Costs types.Worlds.

Inductive ty :=
  | TUnit
  | TLolli (ub lb : option point) (c : fuel) (t : tix)
      (T U : ty) (a : fuel)
  | TProd (T U : ty)
  | TSum (T U : ty)
  | TBox (n k : nat) (C : bcs) (ub : option point) (c : fuel) (t : tix) (U : ty)
  | TSess (S : sty) (x : point) (a : fuel)
  | TEx (lb : lbound) (n : nat) (C : bcs) (T : ty)
with sty :=
  | SRcv (m : nat) (T : ty)   (* ?(∃ι₀…ιₘ₋₁. T) *)
  | SSnd (m : nat) (T : ty)   (* !(∃ι₀…ιₘ₋₁. T) *)
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

Notation "S @ x ^ a" := (TSess S x a) (at level 20, x at level 2, a at level 0, format "S @ x ^ a").

(** ** Point instantiation

    Session types carry no free point variable (see [pinst_sty]). *)

Fixpoint pinst_ty (σ : nat → point) (T : ty) : ty :=
  match T with
  | TUnit => TUnit
  | TLolli ub lb c t T1 U a =>
      TLolli (pt_inst σ <$> ub) (pt_inst σ <$> lb) c t (pinst_ty σ T1) (pinst_ty σ U) a
  | TProd T1 U => TProd (pinst_ty σ T1) (pinst_ty σ U)
  | TSum T1 U => TSum (pinst_ty σ T1) (pinst_ty σ U)
  | TBox n k C ub c t U =>
      TBox n k (bcs_inst σ C) (pt_inst (pup n σ) <$> ub) c t (pinst_ty (pup n σ) U)
  | TSess s x a => TSess s (pt_inst σ x) a
  | TEx lb n C T1 =>
      TEx (lb_map (pt_inst σ) lb) n (bcs_inst σ C) (pinst_ty (pup n σ) T1)
  end.

(** Point instantiation leaves session types alone. A payload ∃ιs.T is
    point-closed below its own binder ([sscoped], checked where a payload
    is read, at E-Send and E-Recv), so no outer point occurs in a session
    type. Instantiation then commutes with unfolding and with session
    substitution, which pass no point binder. *)
Definition pinst_sty (σ : nat → point) (s : sty) : sty := s.

(** T[xs/ιs]. *)
Definition ty_inst (xs : list point) (T : ty) : ty := pinst_ty (plist xs) T.

(** The payload ∃ι₀…ιₘ₋₁. T at the carrier x: T[x·i/ιᵢ]. *)
Definition payload_at (m : nat) (T : ty) (x : point) : ty :=
  ty_inst (payload_pts x m) T.

Lemma payload_at_dual m T x : payload_at m T x‾ = payload_at m T x.
Proof. done. Qed.

Lemma pinst_ty_ext T : ∀ σ τ, (∀ a, σ a = τ a) → pinst_ty σ T = pinst_ty τ T.
Proof.
  induction T; intros σ τ H1; simpl; try done.
  - rewrite (IHT1 σ τ), (IHT2 σ τ) by done.
    rewrite !(option_fmap_ext (pt_inst σ) (pt_inst τ)) by (intros; by apply pt_inst_ext). done.
  - by rewrite (IHT1 σ τ), (IHT2 σ τ).
  - by rewrite (IHT1 σ τ), (IHT2 σ τ).
  - rewrite (IHT (pup n σ) (pup n τ)) by (intros; by apply pup_ext).
    rewrite (bcs_inst_ext σ τ) by done.
    rewrite !(option_fmap_ext (pt_inst (pup n σ)) (pt_inst (pup n τ)))
      by (intros; apply pt_inst_ext; intros; by apply pup_ext). done.
  - by rewrite (pt_inst_ext σ τ).
  - rewrite (IHT (pup n σ) (pup n τ)) by (intros; by apply pup_ext).
    rewrite (bcs_inst_ext σ τ), (lb_map_ext _ (pt_inst τ)) by first [done|intros; by apply pt_inst_ext]. done.
Qed.
Lemma pinst_ty_comp T : ∀ σ τ, pinst_ty τ (pinst_ty σ T) = pinst_ty (pt_inst τ ∘ σ) T.
Proof.
  induction T; intros σ τ; simpl; try done.
  - rewrite IHT1, IHT2, <-!option_fmap_compose.
    rewrite !(option_fmap_ext (pt_inst τ ∘ pt_inst σ) (pt_inst (pt_inst τ ∘ σ)))
      by (intros; apply pt_inst_comp). done.
  - by rewrite IHT1, IHT2.
  - by rewrite IHT1, IHT2.
  - rewrite IHT, bcs_inst_comp, <-option_fmap_compose.
    rewrite (pinst_ty_ext T _ (pup n (pt_inst τ ∘ σ))) by (intros; apply pup_comp).
    rewrite (option_fmap_ext (pt_inst (pup n τ) ∘ pt_inst (pup n σ)) (pt_inst (pup n (pt_inst τ ∘ σ))))
      by (intros; simpl; rewrite pt_inst_comp; apply pt_inst_ext; intros; apply pup_comp). done.
  - by rewrite pt_inst_comp.
  - rewrite IHT, bcs_inst_comp, lb_map_comp.
    rewrite (pinst_ty_ext T _ (pup n (pt_inst τ ∘ σ))) by (intros; apply pup_comp).
    rewrite (lb_map_ext (pt_inst τ ∘ pt_inst σ) (pt_inst (pt_inst τ ∘ σ))) by (intros; apply pt_inst_comp).
    done.
Qed.
Lemma pinst_ty_pvar T : pinst_ty pvar T = T.
Proof.
  induction T; simpl; try done.
  - rewrite IHT1, IHT2. destruct ub, lb; simpl; by rewrite ?pt_inst_pvar.
  - by rewrite IHT1, IHT2.
  - by rewrite IHT1, IHT2.
  - rewrite (pinst_ty_ext T _ pvar), IHT by apply pup_pvar. rewrite bcs_inst_pvar.
    destruct ub; simpl; [|done]. rewrite (pt_inst_ext _ pvar), pt_inst_pvar by apply pup_pvar. done.
  - by rewrite pt_inst_pvar.
  - rewrite (pinst_ty_ext T _ pvar), IHT by apply pup_pvar. rewrite bcs_inst_pvar.
    by rewrite lb_map_id by apply pt_inst_pvar.
Qed.
(** ** Point-closed payloads

    [pscoped k T]: every point variable of T is below k (binders of T
    raise k), and every payload of every session type in T is
    point-closed below its own binder. *)
Definition pt_pscoped (k : nat) (x : point) : Prop :=
  ∀ a, pt_root x = NVar a → a < k.

Fixpoint pscoped (k : nat) (T : ty) : Prop :=
  match T with
  | TUnit => True
  | TLolli ub lb _ _ T1 U _ =>
      (∀ x, ub = Some x → pt_pscoped k x) ∧ (∀ x, lb = Some x → pt_pscoped k x) ∧
      pscoped k T1 ∧ pscoped k U
  | TProd T1 U | TSum T1 U => pscoped k T1 ∧ pscoped k U
  | TBox n _ C ub _ _ U =>
      Forall (pt_pscoped k) (bc_env C) ∧ (∀ x, ub = Some x → pt_pscoped (n + k) x) ∧ pscoped (n + k) U
  | TSess s x _ => sscoped s ∧ pt_pscoped k x
  | TEx lb n C T1 =>
      (∀ x, lb = LPt x → pt_pscoped k x) ∧ Forall (pt_pscoped k) (bc_env C) ∧ pscoped (n + k) T1
  end
with sscoped (s : sty) : Prop :=
  match s with
  | SRcv m T | SSnd m T => pscoped m T
  | SMu s' => sscoped s'
  | SSeq s1 s2 | SPlus s1 s2 | SWith s1 s2 => sscoped s1 ∧ sscoped s2
  | _ => True
  end.

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
  | TUnit | TBox _ _ _ _ _ _ _ => ∅
  | TLolli _ lb _ _ _ _ _ => opt_heads lb
  | TProd T1 U | TSum T1 U => heads T1 ∪ heads U
  | TSess _ x _ => {[x‾]}
  | TEx lb _ _ _ => lb_heads lb
  end.

Fixpoint hbot (T : ty) : bool :=
  match T with
  | TProd T1 U | TSum T1 U => hbot T1 || hbot U
  | TEx LBot _ _ _ => true
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
  | TLolli ub lb c t T1 U a => TLolli ub lb c t (sren_ty r T1) (sren_ty r U) a
  | TProd T1 U => TProd (sren_ty r T1) (sren_ty r U)
  | TSum T1 U => TSum (sren_ty r T1) (sren_ty r U)
  | TBox n k C ub c t U => TBox n k C ub c t (sren_ty (Nat.iter k upren r) U)
  | TSess s x a => TSess (sren r s) x a
  | TEx lb n C T1 => TEx lb n C (sren_ty r T1)
  end
with sren (r : nat → nat) (s : sty) : sty :=
  match s with
  | SRcv m T => SRcv m (sren_ty r T)
  | SSnd m T => SSnd m (sren_ty r T)
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
  | TLolli ub lb c t T1 U a => TLolli ub lb c t (sflip_ty k T1) (sflip_ty k U) a
  | TProd T1 U => TProd (sflip_ty k T1) (sflip_ty k U)
  | TSum T1 U => TSum (sflip_ty k T1) (sflip_ty k U)
  | TBox n kk C ub c t U => TBox n kk C ub c t (sflip_ty (kk + k) U)
  | TSess s x a => TSess (sflip k s) x a
  | TEx lb n C T1 => TEx lb n C (sflip_ty k T1)
  end
with sflip (k : nat) (s : sty) : sty :=
  match s with
  | SRcv m T => SRcv m (sflip_ty k T)
  | SSnd m T => SSnd m (sflip_ty k T)
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
  | SRcv m T => SSnd m T
  | SSnd m T => SRcv m T
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
  | TLolli ub lb c t T1 U a => TLolli ub lb c t (sinst_ty σ T1) (sinst_ty σ U) a
  | TProd T1 U => TProd (sinst_ty σ T1) (sinst_ty σ U)
  | TSum T1 U => TSum (sinst_ty σ T1) (sinst_ty σ U)
  | TBox n k C ub c t U => TBox n k C ub c t (sinst_ty (Nat.iter k sty_up σ) U)
  | TSess s x a => TSess (sinst σ s) x a
  | TEx lb n C T1 => TEx lb n C (sinst_ty σ T1)
  end
with sinst (σ : nat → sty) (s : sty) : sty :=
  match s with
  | SRcv m T => SRcv m (sinst_ty σ T)
  | SSnd m T => SSnd m (sinst_ty σ T)
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
      | SRcv m T => Some (SSeq (SRcv m T) SSkip)
      | SSnd m T => Some (SSeq (SSnd m T) SSkip)
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

(** An idle end: its session type is Skip, so no thread acts on it. *)
Definition idle (S : sty) : Prop := unfoldS S = SSkip.

Inductive hview :=
  | HSkip
  | HRcv (m : nat) (T : ty) (s : sty)
  | HSnd (m : nat) (T : ty) (s : sty)
  | HVar (a : nat) (s : sty)
  | HVarD (a : nat) (s : sty)
  | HPlus (s1 s2 : sty)
  | HWith (s1 s2 : sty)
  | HEnd
  | HStuck (u : sty).

Definition view (u : sty) : hview :=
  match u with
  | SSkip => HSkip
  | SSeq (SRcv m T) s => HRcv m T s
  | SSeq (SSnd m T) s => HSnd m T s
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
  | HRcv m T s => SSeq (SRcv m T) s
  | HSnd m T s => SSeq (SSnd m T) s
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
  | HRcv _ _ s' | HSnd _ _ s' | HVar _ s' | HVarD _ s' => τ s'
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
  | TLolli ub lb c t T1 T2 a, TLolli ub' lb' c' t' U1 U2 a' =>
      ub = ub' ∧ lb = lb' ∧ c = c' ∧ t = t' ∧ a = a' ∧
      eqT ρ T1 U1 ∧ eqT ρ T2 U2
  | TProd T1 T2, TProd U1 U2 | TSum T1 T2, TSum U1 U2 =>
      eqT ρ T1 U1 ∧ eqT ρ T2 U2
  | TBox n k C ub c t T1, TBox n' k' C' ub' c' t' U1 =>
      n = n' ∧ k = k' ∧ C = C' ∧ ub = ub' ∧ c = c' ∧ t = t' ∧
      match k with 0 => eqT ρ T1 U1 | S _ => T1 = U1 end
  | TSess s x a, TSess r y a' => x = y ∧ a = a' ∧ ρ s r
  | TEx lb n C T1, TEx lb' n' C' U1 => lb = lb' ∧ n = n' ∧ C = C' ∧ eqT ρ T1 U1
  | _, _ => False
  end.

Definition eq_step (τ : sty → sty → Prop) (s r : sty) : Prop :=
  match hd s, hd r with
  | HSkip, HSkip | HEnd, HEnd => True
  | HRcv m T s', HRcv m' U r' | HSnd m T s', HSnd m' U r' =>
      m = m' ∧ eqT τ T U ∧ τ s' r'
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

Ltac hd_cases s := destruct (hd s) as [|?m ?T ?s'|?m ?T ?s'|?a ?s'|?a ?s'|?s1 ?s2|?s1 ?s2| |?u].

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

Lemma idle_hd S : idle S ↔ hd S = HSkip.
Proof.
  unfold idle, hd. split; [by intros ->|].
  intros H. rewrite <-(unview_view (unfoldS S)), H. done.
Qed.

Lemma idle_sequiv S S' : sequiv S S' → idle S ↔ idle S'.
Proof.
  intros H. specialize (H 1). simpl in H. unfold eq_step in H. rewrite !idle_hd.
  destruct (hd S), (hd S'); naive_solver.
Qed.

Lemma teq_refl T : teq T T.
Proof. apply eqT_refl, sequiv_refl. Qed.
Lemma teq_sym T U : teq T U → teq U T.
Proof. apply eqT_sym, sequiv_sym. Qed.
(** ** Kinds of types *)

(** The types whose variables admit contraction and weakening. *)
Definition unlimited (T : ty) : Prop :=
  match T with TBox _ _ _ _ _ _ _ => True | _ => False end.

(** Finite evidence that a type holds no end. It carries no credit, so
    aging and capture leave it alone. *)
Inductive tfree : ty → Prop :=
  | tfree_unit : tfree TUnit
  | tfree_box n k C ub c t U : tfree (TBox n k C ub c t U)
  | tfree_prod T U : tfree T → tfree U → tfree (TProd T U)
  | tfree_sum T U : tfree T → tfree U → tfree (TSum T U).

Lemma unlimited_tfree T : unlimited T → tfree T.
Proof. destruct T; try done. intros _. constructor. Qed.

Lemma unlimited_pinst σ U : unlimited U → unlimited (pinst_ty σ U).
Proof. by destruct U. Qed.

(** ** The annotations of the instance N = ∞

    [ty_df] sets every credit inside a type to ∞, every cost to ∞, every
    transformer to (∞, ∞). *)

Fixpoint ty_df (T : ty) : ty :=
  match T with
  | TUnit => TUnit
  | TLolli ub lb _ _ T1 U _ => TLolli ub lb None tinf (ty_df T1) (ty_df U) None
  | TProd T1 U => TProd (ty_df T1) (ty_df U)
  | TSum T1 U => TSum (ty_df T1) (ty_df U)
  | TBox n k C ub _ _ U => TBox n k C ub None tinf (ty_df U)
  | TSess s x _ => TSess (sty_df s) x None
  | TEx lb n C T1 => TEx lb n C (ty_df T1)
  end
with sty_df (s : sty) : sty :=
  match s with
  | SRcv m T => SRcv m (ty_df T)
  | SSnd m T => SSnd m (ty_df T)
  | SMu s' => SMu (sty_df s')
  | SSeq s1 s2 => SSeq (sty_df s1) (sty_df s2)
  | SPlus s1 s2 => SPlus (sty_df s1) (sty_df s2)
  | SWith s1 s2 => SWith (sty_df s1) (sty_df s2)
  | s => s
  end.

Lemma df_mut_idem : (∀ T, ty_df (ty_df T) = ty_df T) ∧ (∀ s, sty_df (sty_df s) = sty_df s).
Proof. apply ty_sty_mut_ind; intros; simpl; congruence. Qed.

Lemma ty_df_idem T : ty_df (ty_df T) = ty_df T.
Proof. apply df_mut_idem. Qed.
Lemma sty_df_idem s : sty_df (sty_df s) = sty_df s.
Proof. apply df_mut_idem. Qed.
