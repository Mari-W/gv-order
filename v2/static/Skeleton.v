(** * The credit skeleton of a derivation (fx-rejects, 2026-11-22)

    A rejection of a program that names no point reads credits, tickets
    and session types, and never a point, a fact or a future. The
    skeleton [skel T] of a type keeps exactly these. It drops every
    point, every bound of an arrow, the constraint of a box and every
    existential. [sktyped] is the typing judgment over skeletons. It keeps
    the cost premises of every rule, aging, the payload premise of E-Send,
    the tickets of E-Link and E-New, and drops Θ, Γ, the future and every
    premise on facts. E-Pack and E-Open leave the skeleton of their
    conclusion as it is, so [sktyped] has no rule for them, and E-Sub
    becomes [sk_sub] over [skle], the skeleton of [tsub].

    - [typed_skel]: a derivation erases to a skeleton derivation.
    - [sk_occ]: an entry of Δ that is not unlimited occurs in the term.
    - the inversions [sk_*_inv]: a skeleton derivation of a term ends
      with the rule of its form under a stack of [sk_sub], which
      [skle_trans] folds into one step. *)

From GV Require Export static.Inversion.

(** ** Skeletons *)

Definition pd : point := pvar 0.
Definition bcs0 : bcs := BCs [] (λ _, False).

Fixpoint skel (T : ty) : ty :=
  match T with
  | TUnit => TUnit
  | TLolli _ _ c T1 U a => TLolli UNone LNone c (skel T1) (skel U) a
  | TProd T1 U => TProd (skel T1) (skel U)
  | TSum T1 U => TSum (skel T1) (skel U)
  | TBox _ k _ _ c U => TBox 0 k bcs0 None c (skel U)
  | TSess s _ a m => TSess s pd a m
  | TEx _ _ _ T1 => skel T1
  end.

Lemma skel_pinst σ T : skel (pinst_ty σ T) = skel T.
Proof. revert σ. induction T; intros σ; simpl; by rewrite ?IHT1, ?IHT2, ?IHT. Qed.

Lemma skel_ty_inst xs T : skel (ty_inst xs T) = skel T.
Proof. apply skel_pinst. Qed.

Lemma skel_payload m T x : skel (payload_at m T x) = skel T.
Proof. apply skel_pinst. Qed.

Lemma skel_sinst σ T : skel (sinst_ty σ T) = sinst_ty σ (skel T).
Proof. revert σ. induction T; intros σ; simpl; by rewrite ?IHT1, ?IHT2, ?IHT. Qed.

Lemma tcontr_skel T : tcontr (skel T) = tcontr T.
Proof. induction T; simpl; try done; congruence. Qed.

Lemma unlimited_skel T : unlimited T → unlimited (skel T).
Proof. by destruct T. Qed.

Lemma tfree_skel T : tfree T → tfree (skel T).
Proof. induction 1; simpl; constructor; auto. Qed.

Lemma eqT_skel ρ T : ∀ U, eqT ρ T U → eqT ρ (skel T) (skel U).
Proof.
  induction T as [|ub lb c T1 IH1 T2 IH2 a|T1 IH1 T2 IH2|T1 IH1 T2 IH2|n k C ub c T1 IH1|s x a m|lb n C T1 IH1];
    intros [|ub' lb' c' U1 U2 a'|U1 U2|U1 U2|n' k' C' ub' c' U1|r y a' m'|lb' n' C' U1] H; simpl in *; try done.
  - naive_solver.
  - naive_solver.
  - naive_solver.
  - destruct H as (-> & -> & -> & -> & -> & H). split_and!; try done.
    destruct k'; [by apply IH1|by subst].
  - naive_solver.
  - naive_solver.
Qed.

(** ** Subtyping on skeletons *)

Definition boxeq (k : nat) (U U' : ty) : Prop :=
  match k with 0 => teq U U' | S _ => U = U' ∨ (teq U U' ∧ tcontr U ∧ tcontr U') end.

Inductive skle : ty → ty → Prop :=
  | skl_unit : skle TUnit TUnit
  | skl_arr ub lb c T1 U a c' T1' U' a' :
      fle c c' → fle a' a → skle T1' T1 → skle U U' →
      skle (TLolli ub lb c T1 U a) (TLolli ub lb c' T1' U' a')
  | skl_prod T1 U T1' U' : skle T1 T1' → skle U U' → skle (TProd T1 U) (TProd T1' U')
  | skl_sum T1 U T1' U' : skle T1 T1' → skle U U' → skle (TSum T1 U) (TSum T1' U')
  | skl_box n k C ub c U U' c' :
      fle c c' → boxeq k U U' → skle (TBox n k C ub c U) (TBox n k C ub c' U')
  | skl_sess s s' x a a' m : sequiv s s' → fle a' a → skle (TSess s x a m) (TSess s' x a' m)
  | skl_ex lb n C T T' : skle T T' → skle (TEx lb n C T) (TEx lb n C T').

Lemma teq_trans T U V : teq T U → teq U V → teq T V.
Proof. apply eqT_trans, sequiv_trans. Qed.

Lemma boxeq_refl k U : boxeq k U U.
Proof. destruct k; [apply teq_refl|by left]. Qed.

Lemma boxeq_trans k U U' U'' : boxeq k U U' → boxeq k U' U'' → boxeq k U U''.
Proof.
  destruct k; simpl; [apply teq_trans|].
  intros [<-|(H1 & HU & HU')] [<-|(H2 & HU2 & HU'')]; auto.
  right. split_and!; [by eapply teq_trans|done|done].
Qed.

Lemma skle_refl T : skle T T.
Proof.
  induction T; constructor; auto using fle_refl, sequiv_refl, boxeq_refl.
Qed.

Lemma skle_trans T U V : skle T U → skle U V → skle T V.
Proof.
  revert T V. induction U; intros T0 V H1 H2; inversion H1; subst; inversion H2; subst; constructor;
    eauto using fle_trans, sequiv_trans, boxeq_trans.
Qed.

Lemma tsub_skle W Γ T T' : tsub W Γ T T' → skle (skel T) (skel T').
Proof.
  induction 1 as [|Γ ub lb c T1 U a c' T1' U' a' Hc Ha _ IH1 _ IH2|Γ T1 U T1' U' _ IH1 _ IH2
    |Γ T1 U T1' U' _ IH1 _ IH2|Γ n k C ub c U U' c' Hc HU|Γ s s' x a a' mt Hs Ha|Γ lb lb' n C C' T T' _ _ _ IH];
    simpl.
  - constructor.
  - by constructor.
  - by constructor.
  - by constructor.
  - apply skl_box; [done|]. destruct k; simpl in *.
    + by apply eqT_skel.
    + destruct HU as [->|(HU & H1 & H2)]; [by left|right].
      rewrite !tcontr_skel. split_and!; [by apply eqT_skel|done|done].
  - by constructor.
  - exact IH.
Qed.

Lemma tage_skle c T T' : tage c T T' → skle T T'.
Proof.
  induction 1; try (constructor; auto using fsub_le, fle_refl, sequiv_refl, skle_refl; done).
  apply skle_refl.
Qed.

Lemma tage_skel c T T' : tage c T T' → tage c (skel T) (skel T').
Proof.
  induction 1; simpl.
  - apply age_free. by apply tfree_skel.
  - by apply age_sess.
  - by apply age_idle.
  - by apply age_arr.
  - by apply age_prod.
  - by apply age_sum.
  - done.
Qed.

(** *** Views of [skle] *)

Lemma skle_sess_l s x a m T :
  skle (TSess s x a m) T → ∃ s' a', T = TSess s' x a' m ∧ sequiv s s' ∧ fle a' a.
Proof. inversion 1; subst. eauto. Qed.

Lemma skle_sess_r s' x a' m T :
  skle T (TSess s' x a' m) → ∃ s a, T = TSess s x a m ∧ sequiv s s' ∧ fle a' a.
Proof. inversion 1; subst. eauto. Qed.

Lemma skle_prod_l T1 U T :
  skle (TProd T1 U) T → ∃ T1' U', T = TProd T1' U' ∧ skle T1 T1' ∧ skle U U'.
Proof. inversion 1; subst. eauto. Qed.

Lemma skle_prod_r T1' U' T :
  skle T (TProd T1' U') → ∃ T1 U, T = TProd T1 U ∧ skle T1 T1' ∧ skle U U'.
Proof. inversion 1; subst. eauto. Qed.

Lemma skle_arr_l ub lb c T1 U a T :
  skle (TLolli ub lb c T1 U a) T → ∃ c' T1' U' a', T = TLolli ub lb c' T1' U' a' ∧
    fle c c' ∧ fle a' a ∧ skle T1' T1 ∧ skle U U'.
Proof. inversion 1; subst. eauto 10. Qed.

Lemma skle_arr_r ub lb c' T1' U' a' T :
  skle T (TLolli ub lb c' T1' U' a') → ∃ c T1 U a, T = TLolli ub lb c T1 U a ∧
    fle c c' ∧ fle a' a ∧ skle T1' T1 ∧ skle U U'.
Proof. inversion 1; subst. eauto 10. Qed.

Lemma skle_box_l n k C ub c U T :
  skle (TBox n k C ub c U) T → ∃ c' U', T = TBox n k C ub c' U' ∧ fle c c' ∧ boxeq k U U'.
Proof. inversion 1; subst. eauto. Qed.

Lemma skle_box_r n k C ub c' U' T :
  skle T (TBox n k C ub c' U') → ∃ c U, T = TBox n k C ub c U ∧ fle c c' ∧ boxeq k U U'.
Proof. inversion 1; subst. eauto. Qed.

Lemma skle_unit_r T : skle T TUnit → T = TUnit.
Proof. by inversion 1. Qed.

(** ** Skeletons of contexts *)

Definition lskel (Δ : lenv) : lenv := fmap (M:=option) skel <$> Δ.

Lemma lskel_lookup Δ i : lskel Δ !! i = fmap (M:=option) skel <$> Δ !! i.
Proof. unfold lskel. by rewrite list_lookup_fmap. Qed.

Lemma lskel_pinst σ Δ : lskel (lenv_pinst σ Δ) = lskel Δ.
Proof. induction Δ as [|[T|] Δ IH]; simpl; [done| |by f_equal]. by rewrite skel_pinst, IH. Qed.

Lemma lenv_only_skel Δ x T : lenv_only Δ x T → lenv_only (lskel Δ) x (skel T).
Proof.
  intros [Hx Hy]. split; [by rewrite lskel_lookup, Hx|].
  intros y σ' Hne Hσ. rewrite lskel_lookup in Hσ.
  destruct (Δ !! y) as [[U|]|] eqn:E; simplify_eq/=. apply unlimited_skel. exact (Hy y U Hne E).
Qed.

Lemma lenv_split_skel Δ Δ1 Δ2 : lenv_split Δ Δ1 Δ2 → lenv_split (lskel Δ) (lskel Δ1) (lskel Δ2).
Proof.
  induction 1 as [|? ? ? _ IH|T ? ? ? _ IH|T ? ? ? _ IH|U ? ? ? HU _ IH];
    simpl; constructor; try done. by apply unlimited_skel.
Qed.

Lemma lenv_unl_skel Δ : lenv_unl Δ → lenv_unl (lskel Δ).
Proof.
  intros H o Ho. unfold lskel in Ho. apply list_elem_of_fmap in Ho as (o' & -> & Ho').
  destruct (H o' Ho') as [->|(U & -> & HU)]; [by left|right].
  eexists _. split; [done|]. by apply unlimited_skel.
Qed.

Lemma lage_skel c Δ Δ' : lage c Δ Δ' → lage c (lskel Δ) (lskel Δ').
Proof. induction 1; simpl; constructor; auto using tage_skel. Qed.

Lemma lskel_insert_ex Δ i lb m C T :
  Δ !! i = Some (Some (TEx lb m C T)) →
  lskel (<[i := Some T]> (lenv_pinst (pshift m) Δ)) = lskel Δ.
Proof.
  intros Hi. unfold lskel at 1. rewrite list_fmap_insert. fold (lskel (lenv_pinst (pshift m) Δ)).
  rewrite lskel_pinst. apply list_insert_id. by rewrite lskel_lookup, Hi.
Qed.

(** ** The skeleton judgment *)

Inductive sktyped (N : fuel) : lenv → expr → ty → fuel → Prop :=
  | sk_unit Δ : lenv_unl Δ → sktyped N Δ EUnit TUnit (Some 0)
  | sk_var Δ x T : lenv_only Δ x T → sktyped N Δ (Var x) T (Some 0)
  | sk_chan Δ o S a m : lenv_unl Δ → sktyped N Δ (Chan o) (TSess S pd a m) (Some 0)
  | sk_abs Δ Δh e T U c a :
      lage a Δ Δh → sktyped N (Some T :: Δh) e U c →
      sktyped N Δ (Lam e) (TLolli UNone LNone c T U a) (Some 0)
  | sk_app Δ Δ1 Δ2 Δ2' e1 e2 c T U a1 c1 c2 :
      lenv_split Δ Δ1 Δ2 → sktyped N Δ1 e1 (TLolli UNone LNone c T U a1) c1 →
      lage c1 Δ2 Δ2' → sktyped N Δ2' e2 T c2 → fle c2 a1 →
      sktyped N Δ (App e1 e2) U (fadd c1 (fadd c2 c))
  | sk_pair Δ Δ1 Δ2 Δ2' e1 e2 T1 T1' T2 c1 c2 :
      lenv_split Δ Δ1 Δ2 → sktyped N Δ1 e1 T1 c1 → lage c1 Δ2 Δ2' →
      sktyped N Δ2' e2 T2 c2 → tage c2 T1 T1' →
      sktyped N Δ (Pair e1 e2) (TProd T1' T2) (fadd c1 c2)
  | sk_letu Δ Δ1 Δ2 Δ2' e1 e2 T c1 c2 :
      lenv_split Δ Δ1 Δ2 → sktyped N Δ1 e1 TUnit c1 → lage c1 Δ2 Δ2' →
      sktyped N Δ2' e2 T c2 → sktyped N Δ (LetU e1 e2) T (fadd c1 c2)
  | sk_letp Δ Δ1 Δ2 Δ2' e1 e2 T1 T2 T c1 c2 :
      lenv_split Δ Δ1 Δ2 → sktyped N Δ1 e1 (TProd T1 T2) c1 → lage c1 Δ2 Δ2' →
      sktyped N (Some T2 :: Some T1 :: Δ2') e2 T c2 → sktyped N Δ (LetP e1 e2) T (fadd c1 c2)
  | sk_inj (i : bool) Δ e T U c :
      sktyped N Δ e (if i then U else T) c → sktyped N Δ (Inj i e) (TSum T U) c
  | sk_case Δ Δ1 Δ2 Δ2' e e1 e2 T1 T2 T c0 c1 c2 :
      lenv_split Δ Δ1 Δ2 → sktyped N Δ1 e (TSum T1 T2) c0 → lage c0 Δ2 Δ2' →
      sktyped N (Some T1 :: Δ2') e1 T c1 → sktyped N (Some T2 :: Δ2') e2 T c2 →
      sktyped N Δ (Case e e1 e2) T (fadd c0 (fmax c1 c2))
  | sk_box Δ e k c U :
      lenv_unl Δ →
      (∀ ss, length ss = k → sinsts N ss →
         sktyped N (Some (TBox 0 k bcs0 None c U) :: Δ) e (sinst_ty (slist ss) U) c) →
      sktyped N Δ (EBox e) (TBox 0 k bcs0 None c U) (Some 0)
  | sk_force Δ e k c U ss c0 :
      length ss = k → sinsts N ss →
      sktyped N Δ e (TBox 0 k bcs0 None c U) c0 →
      sktyped N Δ (EForce e) (sinst_ty (slist ss) U) (fadd c0 (fadd (Some 1) c))
  | sk_send Δ e S0 m T S aS mS Tp Tp' c0 :
      unfoldS S0 = SSeq (SSnd m T) S →
      sktyped N Δ e (TProd Tp (TSess S0 pd aS mS)) c0 →
      tage (Some 1) Tp Tp' → skle Tp' (skel T) →
      sktyped N Δ (ESend e) (TSess S pd mS mS) (fadd c0 (Some 1))
  | sk_recv Δ e S0 m T S a mS c0 :
      unfoldS S0 = SSeq (SRcv m T) S →
      sktyped N Δ e (TSess S0 pd a mS) c0 →
      sktyped N Δ (ERecv e) (TProd (skel T) (TSess S pd mS mS)) (fadd c0 (Some 1))
  | sk_close Δ e S0 a mS c0 :
      unfoldS S0 = SEnd → sktyped N Δ e (TSess S0 pd a mS) c0 →
      sktyped N Δ (EClose e) TUnit (fadd c0 (Some 1))
  | sk_select (i : bool) Δ e S0 S1 S2 a mS c0 :
      unfoldS S0 = SPlus S1 S2 → sktyped N Δ e (TSess S0 pd a mS) c0 →
      sktyped N Δ (ESel i e) (TSess (if i then S2 else S1) pd mS mS) (fadd c0 (Some 1))
  | sk_branch Δ e S0 S1 S2 a mS c0 :
      unfoldS S0 = SWith S1 S2 → sktyped N Δ e (TSess S0 pd a mS) c0 →
      sktyped N Δ (EBra e) (TSum (TSess S1 pd mS mS) (TSess S2 pd mS mS)) (fadd c0 (Some 1))
  | sk_link Δ e S a1 m1 a2 m2 c0 :
      sktyped N Δ e (TProd (TSess S pd a1 m1) (TSess (dual S) pd a2 m2)) c0 →
      lgt N a1 m2 → lgt N a2 m1 → sktyped N Δ (ELink e) TUnit c0
  | sk_spawn Δ e c' a c0 :
      sktyped N Δ e (TLolli UNone LNone c' TUnit TUnit a) c0 → sktyped N Δ (ESpawn e) TUnit c0
  | sk_new Δ S m1 m2 :
      lenv_unl Δ → tsum_ok N m1 m2 →
      sktyped N Δ ENew (TProd (TSess S pd m1 m1) (TSess (dual S) pd m2 m2)) (Some 0)
  | sk_sub Δ e T T' c c' :
      sktyped N Δ e T c → skle T T' → fle c c' → sktyped N Δ e T' c'.

(** ** Erasure *)

Theorem typed_skel W N Θ Γ Δ F e T c :
  typed W N Θ Γ Δ F e T c → sktyped N (lskel Δ) e (skel T) c.
Proof.
  induction 1; simpl.
  - by apply sk_unit, lenv_unl_skel.
  - by apply sk_var, lenv_only_skel.
  - by apply sk_chan, lenv_unl_skel.
  - eapply sk_abs; [by apply lage_skel|exact IHtyped].
  - eapply sk_app; [by apply lenv_split_skel|exact IHtyped1|by apply lage_skel|exact IHtyped2|done].
  - eapply sk_pair; [by apply lenv_split_skel|exact IHtyped1|by apply lage_skel|exact IHtyped2|by apply tage_skel].
  - eapply sk_letu; [by apply lenv_split_skel|exact IHtyped1|by apply lage_skel|exact IHtyped2].
  - eapply sk_letp; [by apply lenv_split_skel|exact IHtyped1|by apply lage_skel|exact IHtyped2].
  - apply sk_inj. by destruct i.
  - eapply sk_case; [by apply lenv_split_skel|exact IHtyped1|by apply lage_skel|exact IHtyped2|exact IHtyped3].
  - apply sk_box; [by apply lenv_unl_skel|]. intros ss Hl Hs.
    specialize (H2 ss Hl Hs). rewrite lskel_pinst, skel_sinst in H2. exact H2.
  - rewrite skel_sinst, skel_ty_inst. by eapply sk_force.
  - eapply sk_send; [done|exact IHtyped|by apply tage_skel|].
    rewrite <-(skel_payload m T x). by eapply tsub_skle.
  - rewrite skel_payload. by eapply sk_recv.
  - by eapply sk_close.
  - by eapply sk_select.
  - by eapply sk_branch.
  - simpl in IHtyped. eapply sk_link; [exact IHtyped|done|done].
  - simpl in IHtyped. eapply sk_spawn. exact IHtyped.
  - apply sk_new; [by apply lenv_unl_skel|done].
  - apply sk_new; [by apply lenv_unl_skel|done].
  - eapply sk_sub; [exact IHtyped|by eapply tsub_skle|done].
  - rewrite skel_ty_inst in IHtyped. exact IHtyped.
  - rewrite (lskel_insert_ex _ _ _ _ _ _ H), skel_pinst in IHtyped. exact IHtyped.
Qed.

(** ** Linearity: an entry that is not unlimited occurs *)

Fixpoint occurs (i : nat) (e : expr) : bool :=
  match e with
  | Var x => Nat.eqb x i
  | EUnit | Chan _ | ENew => false
  | Lam e | EBox e => occurs (S i) e
  | App e1 e2 | Pair e1 e2 | LetU e1 e2 => occurs i e1 || occurs i e2
  | LetP e1 e2 => occurs i e1 || occurs (S (S i)) e2
  | Inj _ e | Op _ e => occurs i e
  | Case e e1 e2 => occurs i e || occurs (S i) e1 || occurs (S i) e2
  end.

Lemma lenv_unl_lin Δ i T : lenv_unl Δ → Δ !! i = Some (Some T) → ¬ unlimited T → False.
Proof.
  intros H Hi HT. destruct (H (Some T)) as [?|(U & [= <-] & HU)]; [|done|done].
  by eapply list_elem_of_lookup_2.
Qed.

Lemma split_lin Δ Δ1 Δ2 i T : lenv_split Δ Δ1 Δ2 → Δ !! i = Some (Some T) → ¬ unlimited T →
  (Δ1 !! i = Some (Some T) ∧ Δ2 !! i = Some None) ∨ (Δ1 !! i = Some None ∧ Δ2 !! i = Some (Some T)).
Proof.
  intros H. revert i. induction H as [|Δ Δ1 Δ2 _ IH|σ Δ Δ1 Δ2 _ IH|σ Δ Δ1 Δ2 _ IH|U Δ Δ1 Δ2 HU _ IH];
    intros [|i] Hi HT; simpl in *; simplify_eq; auto; exfalso; by apply HT.
Qed.

Lemma lage_lin c Δ Δ' i T : lage c Δ Δ' → Δ !! i = Some (Some T) →
  ∃ T', Δ' !! i = Some (Some T') ∧ tage c T T'.
Proof.
  intros H. revert i. induction H as [|Δ Δ' _ IH|σ σ' Δ Δ' Hs _ IH]; intros [|i] Hi; simpl in *; simplify_eq; eauto.
Qed.

Lemma lage_none c Δ Δ' i : lage c Δ Δ' → Δ !! i = Some None → Δ' !! i = Some None.
Proof.
  intros H. revert i. induction H as [|Δ Δ' _ IH|σ σ' Δ Δ' Hs _ IH]; intros [|i] Hi; simpl in *; simplify_eq; eauto.
Qed.

Lemma tage_lin c T T' : tage c T T' → ¬ unlimited T → ¬ unlimited T'.
Proof. intros H HT HT'. apply HT. by eapply tage_unl_r. Qed.

Local Ltac occ_split j T0 Hi HT :=
  match goal with Hs : lenv_split _ _ _, Ha : lage _ _ _ |- _ =>
    destruct (split_lin _ _ _ j T0 Hs Hi HT) as [[?Hl _]|[_ ?Hr]];
    [|destruct (lage_lin _ _ _ _ _ Ha Hr) as (?T' & ?Hi' & ?Ha')] end.

Theorem sk_occ N Δ e T c : sktyped N Δ e T c →
  ∀ i T0, Δ !! i = Some (Some T0) → ¬ unlimited T0 → occurs i e = true.
Proof.
  induction 1; intros j T0 Hi HT; simpl.
  - exfalso. by eapply lenv_unl_lin.
  - destruct H as [Hx Hy]. destruct (decide (j = x)) as [->|Hne]; [by apply Nat.eqb_refl|].
    exfalso. by apply HT, (Hy j T0).
  - exfalso. by eapply lenv_unl_lin.
  - destruct (lage_lin _ _ _ _ _ H Hi) as (T' & Hi' & Ha). apply (IHsktyped (S j) T'); [done|by eapply tage_lin].
  - apply orb_true_iff. occ_split j T0 Hi HT; [left; by eapply IHsktyped1|right].
    eapply IHsktyped2; [exact Hi'|by eapply tage_lin].
  - apply orb_true_iff. occ_split j T0 Hi HT; [left; by eapply IHsktyped1|right].
    eapply IHsktyped2; [exact Hi'|by eapply tage_lin].
  - apply orb_true_iff. occ_split j T0 Hi HT; [left; by eapply IHsktyped1|right].
    eapply IHsktyped2; [exact Hi'|by eapply tage_lin].
  - apply orb_true_iff. occ_split j T0 Hi HT; [left; by eapply IHsktyped1|right].
    apply (IHsktyped2 (S (S j)) T'); [exact Hi'|by eapply tage_lin].
  - by eapply IHsktyped.
  - apply orb_true_iff. occ_split j T0 Hi HT.
    + left. apply orb_true_iff. left. by eapply IHsktyped1.
    + right. apply (IHsktyped3 (S j) T'); [exact Hi'|by eapply tage_lin].
  - exfalso. by eapply lenv_unl_lin.
  - by eapply IHsktyped.
  - by eapply IHsktyped.
  - by eapply IHsktyped.
  - by eapply IHsktyped.
  - by eapply IHsktyped.
  - by eapply IHsktyped.
  - by eapply IHsktyped.
  - by eapply IHsktyped.
  - exfalso. by eapply lenv_unl_lin.
  - by eapply IHsktyped.
Qed.

(** An entry that is not unlimited and does not occur in the first
    operand of a split goes to the second, aged by the cost of the
    first. *)
Lemma pass_r N Δ Δ1 Δ2 Δ2' e1 T1 c1 c i X :
  lenv_split Δ Δ1 Δ2 → sktyped N Δ1 e1 T1 c1 → occurs i e1 = false → lage c Δ2 Δ2' →
  Δ !! i = Some (Some X) → ¬ unlimited X →
  ∃ X', Δ2' !! i = Some (Some X') ∧ tage c X X'.
Proof.
  intros Hs H1 Ho Ha Hi HX. destruct (split_lin _ _ _ _ _ Hs Hi HX) as [[Hl _]|[_ Hr]].
  - exfalso. rewrite (sk_occ _ _ _ _ _ H1 i X Hl HX) in Ho. done.
  - by eapply lage_lin.
Qed.

(** An entry that is not unlimited and does not occur in the second
    operand, typed under [k] more binders, goes to the first. *)
Lemma pass_l N Δ Δ1 Δ2 Δ2' e2 T2 c2 c i X (Δx : lenv) :
  lenv_split Δ Δ1 Δ2 → lage c Δ2 Δ2' → sktyped N (Δx ++ Δ2') e2 T2 c2 →
  occurs (length Δx + i) e2 = false → Δ !! i = Some (Some X) → ¬ unlimited X →
  Δ1 !! i = Some (Some X).
Proof.
  intros Hs Ha H2 Ho Hi HX. destruct (split_lin _ _ _ _ _ Hs Hi HX) as [[Hl _]|[_ Hr]]; [done|].
  exfalso. destruct (lage_lin _ _ _ _ _ Ha Hr) as (X' & Hi' & Hx).
  rewrite (sk_occ _ _ _ _ _ H2 (length Δx + i) X') in Ho; [done| |by eapply tage_lin].
  by rewrite lookup_app_r, Nat.add_comm, Nat.add_sub by lia.
Qed.

(** ** Inversion of the skeleton judgment *)

Section sk_inversion.
  Context (N : fuel).

  Lemma sk_var_inv Δ i T c : sktyped N Δ (Var i) T c →
    ∃ T0, Δ !! i = Some (Some T0) ∧ skle T0 T.
  Proof.
    remember (Var i) as e0 eqn:He. induction 1; try discriminate.
    - injection He as <-. destruct H as [Hx _]. eexists. split; [done|apply skle_refl].
    - destruct (IHsktyped He) as (T0 & Hi & Hl). exists T0. split; [done|by eapply skle_trans].
  Qed.

  Lemma sk_abs_inv Δ e T c : sktyped N Δ (Lam e) T c →
    ∃ Δh T1 U c1 a, lage a Δ Δh ∧ sktyped N (Some T1 :: Δh) e U c1 ∧
      skle (TLolli UNone LNone c1 T1 U a) T.
  Proof.
    remember (Lam e) as e0 eqn:He. induction 1; try discriminate.
    - injection He as <-. do 5 eexists. split_and!; [done|done|apply skle_refl].
    - destruct (IHsktyped He) as (Δh & T1 & U & c1 & a & Ha & Hb & Hl).
      do 5 eexists. split_and!; [done|done|by eapply skle_trans].
  Qed.

  Lemma sk_app_inv Δ e1 e2 T c : sktyped N Δ (App e1 e2) T c →
    ∃ Δ1 Δ2 Δ2' c0 T1 U a1 c1 c2, lenv_split Δ Δ1 Δ2 ∧
      sktyped N Δ1 e1 (TLolli UNone LNone c0 T1 U a1) c1 ∧ lage c1 Δ2 Δ2' ∧
      sktyped N Δ2' e2 T1 c2 ∧ fle c2 a1 ∧ skle U T.
  Proof.
    remember (App e1 e2) as e0 eqn:He. induction 1; try discriminate.
    - injection He as <- <-. do 9 eexists. split_and!; try done. apply skle_refl.
    - destruct (IHsktyped He) as (Δ1 & Δ2 & Δ2' & cz & T1 & U & a1 & c1 & c2 & Hr).
      do 9 eexists. destruct_and! Hr. split_and!; try done. by eapply skle_trans.
  Qed.

  Lemma sk_pair_inv Δ e1 e2 T c : sktyped N Δ (Pair e1 e2) T c →
    ∃ Δ1 Δ2 Δ2' T1 T1' T2 c1 c2, lenv_split Δ Δ1 Δ2 ∧ sktyped N Δ1 e1 T1 c1 ∧
      lage c1 Δ2 Δ2' ∧ sktyped N Δ2' e2 T2 c2 ∧ tage c2 T1 T1' ∧ skle (TProd T1' T2) T.
  Proof.
    remember (Pair e1 e2) as e0 eqn:He. induction 1; try discriminate.
    - injection He as <- <-. do 8 eexists. split_and!; try done. apply skle_refl.
    - destruct (IHsktyped He) as (Δ1 & Δ2 & Δ2' & T1 & T1' & T2 & c1 & c2 & Hr).
      do 8 eexists. destruct_and! Hr. split_and!; try done. by eapply skle_trans.
  Qed.

  Lemma sk_letu_inv Δ e1 e2 T c : sktyped N Δ (LetU e1 e2) T c →
    ∃ Δ1 Δ2 Δ2' T' c1 c2, lenv_split Δ Δ1 Δ2 ∧ sktyped N Δ1 e1 TUnit c1 ∧
      lage c1 Δ2 Δ2' ∧ sktyped N Δ2' e2 T' c2 ∧ skle T' T.
  Proof.
    remember (LetU e1 e2) as e0 eqn:He. induction 1; try discriminate.
    - injection He as <- <-. do 6 eexists. split_and!; try done. apply skle_refl.
    - destruct (IHsktyped He) as (Δ1 & Δ2 & Δ2' & Tz & c1 & c2 & Hr).
      do 6 eexists. destruct_and! Hr. split_and!; try done. by eapply skle_trans.
  Qed.

  Lemma sk_letp_inv Δ e1 e2 T c : sktyped N Δ (LetP e1 e2) T c →
    ∃ Δ1 Δ2 Δ2' T1 T2 T' c1 c2, lenv_split Δ Δ1 Δ2 ∧ sktyped N Δ1 e1 (TProd T1 T2) c1 ∧
      lage c1 Δ2 Δ2' ∧ sktyped N (Some T2 :: Some T1 :: Δ2') e2 T' c2 ∧ skle T' T.
  Proof.
    remember (LetP e1 e2) as e0 eqn:He. induction 1; try discriminate.
    - injection He as <- <-. do 8 eexists. split_and!; try done. apply skle_refl.
    - destruct (IHsktyped He) as (Δ1 & Δ2 & Δ2' & T1 & T2 & Tz & c1 & c2 & Hr).
      do 8 eexists. destruct_and! Hr. split_and!; try done. by eapply skle_trans.
  Qed.

  Lemma sk_box_inv Δ e T c : sktyped N Δ (EBox e) T c →
    ∃ k cb U, lenv_unl Δ ∧
      (∀ ss, length ss = k → sinsts N ss →
         sktyped N (Some (TBox 0 k bcs0 None cb U) :: Δ) e (sinst_ty (slist ss) U) cb) ∧
      skle (TBox 0 k bcs0 None cb U) T.
  Proof.
    remember (EBox e) as e0 eqn:He. induction 1; try discriminate.
    - injection He as <-. do 3 eexists. split_and!; [done|done|apply skle_refl].
    - destruct (IHsktyped He) as (k & cb & U & Hr). do 3 eexists. destruct_and! Hr.
      split_and!; try done. by eapply skle_trans.
  Qed.

  Lemma sk_force_inv Δ e T c : sktyped N Δ (EForce e) T c →
    ∃ k cb U ss c0, length ss = k ∧ sinsts N ss ∧
      sktyped N Δ e (TBox 0 k bcs0 None cb U) c0 ∧ skle (sinst_ty (slist ss) U) T.
  Proof.
    remember (EForce e) as e0 eqn:He. induction 1; try discriminate.
    - injection He as <-. do 5 eexists. split_and!; try done. apply skle_refl.
    - destruct (IHsktyped He) as (k & cb & U & ss & cz & Hr). do 5 eexists. destruct_and! Hr.
      split_and!; try done. by eapply skle_trans.
  Qed.

  Lemma sk_send_inv Δ e T c : sktyped N Δ (ESend e) T c →
    ∃ S0 m T0 S aS mS Tp Tp' c0, unfoldS S0 = SSeq (SSnd m T0) S ∧
      sktyped N Δ e (TProd Tp (TSess S0 pd aS mS)) c0 ∧ tage (Some 1) Tp Tp' ∧ skle Tp' (skel T0) ∧
      skle (TSess S pd mS mS) T ∧ fle (fadd c0 (Some 1)) c.
  Proof.
    remember (ESend e) as e0 eqn:He. induction 1; try discriminate.
    - injection He as <-. do 9 eexists. split_and!; try done; [apply skle_refl|apply fle_refl].
    - destruct (IHsktyped He) as (S0 & m & T0 & S & aS & mS & Tp & Tp' & cz & Hr). do 9 eexists.
      destruct_and! Hr. split_and!; try done; [by eapply skle_trans|by eapply fle_trans].
  Qed.

  Lemma sk_recv_inv Δ e T c : sktyped N Δ (ERecv e) T c →
    ∃ S0 m T0 S a mS c0, unfoldS S0 = SSeq (SRcv m T0) S ∧
      sktyped N Δ e (TSess S0 pd a mS) c0 ∧
      skle (TProd (skel T0) (TSess S pd mS mS)) T ∧ fle (fadd c0 (Some 1)) c.
  Proof.
    remember (ERecv e) as e0 eqn:He. induction 1; try discriminate.
    - injection He as <-. do 7 eexists. split_and!; try done; [apply skle_refl|apply fle_refl].
    - destruct (IHsktyped He) as (S0 & m & T0 & S & a & mS & cz & Hr). do 7 eexists.
      destruct_and! Hr. split_and!; try done; [by eapply skle_trans|by eapply fle_trans].
  Qed.

  Lemma sk_close_inv Δ e T c : sktyped N Δ (EClose e) T c →
    ∃ S0 a mS c0, unfoldS S0 = SEnd ∧ sktyped N Δ e (TSess S0 pd a mS) c0 ∧ fle (fadd c0 (Some 1)) c.
  Proof.
    remember (EClose e) as e0 eqn:He. induction 1; try discriminate.
    - injection He as <-. do 4 eexists. split_and!; try done. apply fle_refl.
    - destruct (IHsktyped He) as (S0 & a & mS & cz & Hr). do 4 eexists.
      destruct_and! Hr. split_and!; try done. by eapply fle_trans.
  Qed.

  Lemma sk_link_inv Δ e T c : sktyped N Δ (ELink e) T c →
    ∃ S a1 m1 a2 m2 c0, sktyped N Δ e (TProd (TSess S pd a1 m1) (TSess (dual S) pd a2 m2)) c0 ∧
      lgt N a1 m2 ∧ lgt N a2 m1.
  Proof.
    remember (ELink e) as e0 eqn:He. induction 1; try discriminate.
    - injection He as <-. do 6 eexists. split_and!; done.
    - by apply IHsktyped.
  Qed.

  Lemma sk_spawn_inv Δ e T c : sktyped N Δ (ESpawn e) T c →
    ∃ c' a c0, sktyped N Δ e (TLolli UNone LNone c' TUnit TUnit a) c0.
  Proof.
    remember (ESpawn e) as e0 eqn:He. induction 1; try discriminate.
    - injection He as <-. by do 3 eexists.
    - by apply IHsktyped.
  Qed.

  Lemma sk_new_inv Δ T c : sktyped N Δ ENew T c →
    ∃ S m1 m2, lenv_unl Δ ∧ tsum_ok N m1 m2 ∧
      skle (TProd (TSess S pd m1 m1) (TSess (dual S) pd m2 m2)) T.
  Proof.
    remember ENew as e0 eqn:He. induction 1; try discriminate.
    - do 3 eexists. split_and!; [done|done|apply skle_refl].
    - destruct (IHsktyped He) as (S & m1 & m2 & Hr). do 3 eexists. destruct_and! Hr.
      split_and!; try done. by eapply skle_trans.
  Qed.

  Lemma sk_unit_inv Δ T c : sktyped N Δ EUnit T c → lenv_unl Δ ∧ skle TUnit T.
  Proof.
    remember EUnit as e0 eqn:He. induction 1; try discriminate.
    - split; [done|apply skle_refl].
    - destruct (IHsktyped He). split; [done|by eapply skle_trans].
  Qed.
End sk_inversion.

(** ** Sessions up to ≈ *)

Lemma sequiv_unfold_snd' s S0 m T S :
  sequiv s S0 → unfoldS S0 = SSeq (SSnd m T) S →
  ∃ T' S', unfoldS s = SSeq (SSnd m T') S' ∧ teq T' T.
Proof.
  intros Hq Hu. apply sequiv_step in Hq. unfold eq_step in Hq. rewrite (hd_of _ _ Hu) in Hq. simpl in Hq.
  destruct (hd s) eqn:Hs; simpl in Hq; try done. destruct_and!; subst.
  eexists _, _. split; [|done]. by rewrite unfoldS_unview, Hs.
Qed.

Lemma sequiv_unfold_rcv' s S0 m T S :
  sequiv s S0 → unfoldS S0 = SSeq (SRcv m T) S →
  ∃ T' S', unfoldS s = SSeq (SRcv m T') S' ∧ teq T' T.
Proof.
  intros Hq Hu. apply sequiv_step in Hq. unfold eq_step in Hq. rewrite (hd_of _ _ Hu) in Hq. simpl in Hq.
  destruct (hd s) eqn:Hs; simpl in Hq; try done. destruct_and!; subst.
  eexists _, _. split; [|done]. by rewrite unfoldS_unview, Hs.
Qed.

Lemma idle_dual_iff S : idle (dual S) ↔ idle S.
Proof.
  rewrite !idle_hd, hd_dual. destruct (hd S); done.
Qed.

Lemma end_not_idle S : unfoldS S = SEnd → ¬ idle S.
Proof. unfold idle. by intros ->. Qed.

(** Two box results related by [boxeq] stay related at an instance. *)
Lemma boxeq_sinst N k U U' ss : boxeq k U U' → length ss = k → sinsts N ss →
  teq (sinst_ty (slist ss) U) (sinst_ty (slist ss) U').
Proof.
  intros Hb Hl [[Hc _] _]. destruct k as [|k]; simpl in Hb.
  - destruct ss; [|done]. rewrite !(proj1 sinst_id_mut _ (slist [])); [done| |];
      intros a; unfold slist; simpl; by rewrite Nat.sub_0_r.
  - destruct Hb as [->|(Ht & H1 & H2)]; [apply teq_refl|].
    apply teq_sinst; [|done|done|done].
    intros a. unfold slist. destruct (ss !! a) as [s|] eqn:E; [|done].
    eapply Forall_lookup_1 in Hc; [exact Hc|exact E].
Qed.

(** ** Ancestors of an entry

    [anc Δ i X]: the entry i of Δ lies below X in [skle]. An entry of a
    context in a derivation goes back to an entry of each enclosing
    context, through splits, which copy it, and agings, which lower it
    ([anc_split_l], [anc_split_r], [anc_lage]). A use of a variable
    gives an ancestor at its own context ([sk_var_anc]), and [climb]
    walks it out to the context where the variable is bound. *)

Definition anc (Δ : lenv) (i : nat) (X : ty) : Prop := ∃ X0, Δ !! i = Some (Some X0) ∧ skle X0 X.

Lemma anc_le Δ i X Y : anc Δ i X → skle X Y → anc Δ i Y.
Proof. intros (X0 & Hi & Hl) H. exists X0. split; [done|by eapply skle_trans]. Qed.

Lemma split_back_l Δ Δ1 Δ2 i X : lenv_split Δ Δ1 Δ2 → Δ1 !! i = Some (Some X) → Δ !! i = Some (Some X).
Proof.
  intros H. revert i. induction H; intros [|i] Hi; simpl in *; simplify_eq; eauto.
Qed.

Lemma split_back_r Δ Δ1 Δ2 i X : lenv_split Δ Δ1 Δ2 → Δ2 !! i = Some (Some X) → Δ !! i = Some (Some X).
Proof.
  intros H. revert i. induction H; intros [|i] Hi; simpl in *; simplify_eq; eauto.
Qed.

Lemma lage_back c Δ Δ' i X' : lage c Δ Δ' → Δ' !! i = Some (Some X') →
  ∃ X, Δ !! i = Some (Some X) ∧ tage c X X'.
Proof.
  intros H. revert i. induction H as [|Δ Δ' _ IH|σ σ' Δ Δ' Hs _ IH]; intros [|i] Hi; simpl in *; simplify_eq; eauto.
Qed.

Lemma anc_split_l Δ Δ1 Δ2 i X : lenv_split Δ Δ1 Δ2 → anc Δ1 i X → anc Δ i X.
Proof. intros Hs (X0 & Hi & Hl). exists X0. split; [by eapply split_back_l|done]. Qed.

Lemma anc_split_r Δ Δ1 Δ2 i X : lenv_split Δ Δ1 Δ2 → anc Δ2 i X → anc Δ i X.
Proof. intros Hs (X0 & Hi & Hl). exists X0. split; [by eapply split_back_r|done]. Qed.

Lemma anc_lage c Δ Δ' i X : lage c Δ Δ' → anc Δ' i X → anc Δ i X.
Proof.
  intros Ha (X0 & Hi & Hl). destruct (lage_back _ _ _ _ _ Ha Hi) as (X1 & Hi1 & Hx).
  exists X1. split; [done|]. eapply skle_trans; [by eapply tage_skle|done].
Qed.

Lemma anc_cons o Δ i X : anc (o :: Δ) (S i) X → anc Δ i X.
Proof. done. Qed.

Lemma anc_top X0 Δ X : anc (Some X0 :: Δ) 0 X → skle X0 X.
Proof. intros (X1 & [= ->] & Hl). done. Qed.

Lemma sk_var_anc N Δ i T c : sktyped N Δ (Var i) T c → anc Δ i T.
Proof. intros H. by apply sk_var_inv in H. Qed.

Ltac climb1 H :=
  lazymatch type of H with
  | anc ?G _ _ =>
      first
        [ match goal with Hs : lenv_split _ G _ |- _ => apply (anc_split_l _ _ _ _ _ Hs) in H end
        | match goal with Hs : lenv_split _ _ G |- _ => apply (anc_split_r _ _ _ _ _ Hs) in H end
        | match goal with Ha : lage _ _ G |- _ => apply (anc_lage _ _ _ _ _ Ha) in H end
        | lazymatch G with _ :: _ => idtac end;
          lazymatch type of H with anc _ (S _) _ => apply anc_cons in H end ]
  end.

Ltac climb H := repeat climb1 H.

(** [climb_to H G] stops at the context G. *)
Ltac climb_to H G :=
  repeat (lazymatch type of H with anc G _ _ => fail | _ => climb1 H end).

(** ** Views of [teq] and of instances *)

Lemma teq_lolli_l ub lb c A B a U :
  teq (TLolli ub lb c A B a) U → ∃ A' B', U = TLolli ub lb c A' B' a ∧ teq A A' ∧ teq B B'.
Proof.
  intros H. destruct U; simpl in H; try done. destruct H as (-> & -> & -> & -> & HA & HB). eauto.
Qed.

Lemma teq_prod_l A B U : teq (TProd A B) U → ∃ A' B', U = TProd A' B' ∧ teq A A' ∧ teq B B'.
Proof. intros H. destruct U; simpl in H; try done. destruct H as [HA HB]. eauto. Qed.

Lemma teq_sess_l s x a m U : teq (TSess s x a m) U → ∃ s', U = TSess s' x a m ∧ sequiv s s'.
Proof. intros H. destruct U; simpl in H; try done. destruct H as (-> & -> & -> & Hs). eauto. Qed.

Lemma boxeq_teq k U U' : boxeq k U U' → teq U U'.
Proof. destruct k; simpl; [done|]. intros [->|[H _]]; [apply teq_refl|done]. Qed.

Lemma sinst_inv_lolli σ U ub lb c A B a : sinst_ty σ U = TLolli ub lb c A B a →
  ∃ A0 B0, U = TLolli ub lb c A0 B0 a ∧ A = sinst_ty σ A0 ∧ B = sinst_ty σ B0.
Proof. destruct U; simpl; intros H; simplify_eq. eauto. Qed.

Lemma sinst_inv_prod σ U A B : sinst_ty σ U = TProd A B →
  ∃ A0 B0, U = TProd A0 B0 ∧ A = sinst_ty σ A0 ∧ B = sinst_ty σ B0.
Proof. destruct U; simpl; intros H; simplify_eq. eauto. Qed.

Lemma sinst_inv_sess σ U s x a m : sinst_ty σ U = TSess s x a m →
  ∃ s0, U = TSess s0 x a m ∧ s = sinst σ s0.
Proof. destruct U; simpl; intros H; simplify_eq. eauto. Qed.

Lemma sinsts_repeat_end N k : sinsts N (repeat SEnd k).
Proof.
  split; [split|intros _]; induction k; simpl; constructor; auto; done.
Qed.

(** [teq] is [skle] both ways. *)
Lemma teq_skle_both A : ∀ B, teq A B → skle A B ∧ skle B A.
Proof.
  induction A as [|ub lb c A1 IH1 A2 IH2 a|A1 IH1 A2 IH2|A1 IH1 A2 IH2|n k C ub c A1 IH1|s x a m|lb n C A1 IH1];
    intros [|ub' lb' c' B1 B2 a'|B1 B2|B1 B2|n' k' C' ub' c' B1|s' x' a' m'|lb' n' C' B1] H;
    unfold teq in H; simpl in H; try done.
  - split; constructor.
  - destruct H as (-> & -> & -> & -> & H1 & H2).
    destruct (IH1 _ H1), (IH2 _ H2). split; constructor; auto using fle_refl.
  - destruct H as [H1 H2]. destruct (IH1 _ H1), (IH2 _ H2). split; constructor; auto.
  - destruct H as [H1 H2]. destruct (IH1 _ H1), (IH2 _ H2). split; constructor; auto.
  - destruct H as (-> & -> & -> & -> & -> & H). split; constructor; try apply fle_refl.
    + destruct k'; simpl in *; [done|by left].
    + destruct k'; simpl in *; [by apply teq_sym|by left].
  - destruct H as (-> & -> & -> & H). split; constructor; auto using fle_refl, sequiv_sym.
  - destruct H as (-> & -> & -> & H). destruct (IH1 _ H). split; constructor; auto.
Qed.

Lemma teq_skle A B : teq A B → skle A B.
Proof. intros H. exact (proj1 (teq_skle_both A B H)). Qed.
