(** * The negative control of the choice encoding is underivable

    docs/extensions/choice-encoding.md types c with

      Sch₀ = !(∃ι₀. (?∗.Close)@ι₀ ⊕ (?∗.Close)@ι₀).Close

    so that both arms of the sum lie at one payload point. The thread

      T2 = branch c′ { k ⇒ close d; recv k; close k | k ⇒ recv k; close d; close k }

    then asks δ ≺ x[0] in the first arm and x[0] ≺ δ in the second, for
    the point x of the receive on c′ and the point δ of d. This file
    proves that no [styped] derivation of T2 exists in a context whose
    order is irreflexive ([t2_underivable]), and that the same holds for
    the body of [choice_main] after the two [new]s ([body0_underivable])
    and for every top-level constraint that [soundness_source] accepts
    ([body0_underivable_top]).

    The proof is an inversion over the derivation. E-Weak, E-Contract,
    E-Open, E-Conv and E-Pack are the rules whose conclusion does not
    fix the term. In a context whose bindings are neither unlimited nor
    existential ([plain]) the first three cannot fire, and E-Conv and
    E-Pack only change the type of the conclusion ([sd_of]).

    END POINTS: the inversion still runs, but with end points the two
    arms ask δ ≺ x[0]‾ (the partner point of k) and x[0] ≺ δ̄ (the
    partner point of d). These name four points and close no cycle, so
    the final step fails, and the underivability theorems are commented
    out ([t2i_underivable] to [negative_new_at]). The inversion lemmas
    above them still compile. Whether the shared-point program now
    types is open, see the report of the end-points port. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.ChoiceEnc.
From LRGV Require Import static.SourceRules.

Set Default Proof Using "All".

(** ** Plain contexts *)

Definition is_ex (T : ty) : Prop := match T with TEx _ _ _ _ => True | _ => False end.

Definition plain (Δ : lenv) : Prop :=
  ∀ i T, Δ !! i = Some (Some T) → ¬ unlimited T ∧ ¬ is_ex T.

Lemma plain_cons_inv o Δ : plain (o :: Δ) → plain Δ.
Proof. intros H i T Hi. by apply (H (S i)). Qed.

Lemma plain_none Δ : plain Δ → plain (None :: Δ).
Proof. intros H [|i] T Hi; [done|by apply (H i)]. Qed.

Lemma plain_some T Δ : ¬ unlimited T → ¬ is_ex T → plain Δ → plain (Some T :: Δ).
Proof. intros Hu He H [|i] U Hi; [by injection Hi as <-|by apply (H i)]. Qed.

Lemma plain_split Δ Δ1 Δ2 : lenv_split Δ Δ1 Δ2 → plain Δ → plain Δ1 ∧ plain Δ2.
Proof.
  intros Hs H. split; intros i T Hi; apply (H i).
  - by eapply lenv_split_lookup_l.
  - by eapply lenv_split_lookup_r.
Qed.

Lemma wk_plain Δ' Δ : lenv_wk Δ' Δ → plain Δ → Δ' = Δ.
Proof.
  induction 1 as [|o Δ' Δ Hw IH|U Δ' Δ Hu Hw IH]; intros H; [done| |].
  - by rewrite IH by (by eapply plain_cons_inv).
  - exfalso. destruct (H 0 U eq_refl) as [Hn _]. by apply Hn.
Qed.


(** ** E-Conv as a relation *)

Lemma opt_rel_sym Ψ o o' : opt_rel (heqs Ψ) o o' → opt_rel (heqs Ψ) o' o.
Proof. destruct o, o'; simpl; try done; by intros ->. Qed.

Lemma opt_rel_trans Ψ o o' o'' :
  opt_rel (heqs Ψ) o o' → opt_rel (heqs Ψ) o' o'' → opt_rel (heqs Ψ) o o''.
Proof. destruct o, o', o''; simpl; try done; by intros -> ->. Qed.

Lemma teq_trans' T U V : teq T U → teq U V → teq T V.
Proof. apply eqT_trans, seq_trans. Qed.

Lemma hsteq_refl Ψ T : hsteq Ψ T T.
Proof. apply teq_hsteq, teq_refl. Qed.

Lemma hsteq_sym Ψ T : ∀ U, hsteq Ψ T U → hsteq Ψ U T.
Proof.
  induction T; intros [] H; simpl in *; try done.
  - destruct H as (Hu & Hl & H1 & H2). split_and!; auto using opt_rel_sym.
  - destruct H. split; auto.
  - destruct H. split; auto.
  - by apply teq_sym.
  - destruct H as [H1 H2]. split; [by apply he_sym|by apply seq_sym].
  - destruct H as (-> & -> & -> & H). split_and!; [done|done|done|by apply teq_sym].
Qed.

Lemma hsteq_trans Ψ T : ∀ U V, hsteq Ψ T U → hsteq Ψ U V → hsteq Ψ T V.
Proof.
  induction T; intros [] [] H H'; simpl in *; try done.
  - destruct H as (Hu & Hl & H1 & H2), H' as (Hu' & Hl' & H1' & H2').
    split_and!; eauto using opt_rel_trans.
  - destruct H, H'. split; eauto.
  - destruct H, H'. split; eauto.
  - by eapply teq_trans'.
  - destruct H as [H1 H2], H' as [H1' H2']. split; [by eapply he_trans|by eapply seq_trans].
  - destruct H as (-> & -> & -> & H), H' as (-> & -> & -> & H').
    split_and!; [done|done|done|by eapply teq_trans'].
Qed.

Lemma hsteq_ex Ψ T U : hsteq Ψ T U → is_ex T → is_ex U.
Proof. destruct T, U; simpl; done. Qed.

(** ** The last syntax-directed rule

    [styped_sd] is [styped] with only the rules whose conclusion fixes
    the term. Its premises are full [styped] derivations. *)

Inductive styped_sd : fhyps → hyps → lenv → sfuture → expr → ty → Prop :=
  | sd_unit Φ Ψ Δ F :
      lenv_empty Δ →
      styped_sd Φ Ψ Δ F EUnit TUnit
  | sd_konst Φ Ψ Δ F k T :
      lenv_empty Δ → konst_ty (heqs Ψ) (hlt Ψ) (hyp_known Ψ) k T → kscoped k T →
      styped_sd Φ Ψ Δ F (Konst k) T
  | sd_var Φ Ψ Δ F x T :
      lenv_only Δ x T →
      styped_sd Φ Ψ Δ F (Var x) T
  | sd_lam Φ Ψ Δ F e T U ub lb φ :
      φ ∉ dom Φ →
      hlb_below_hb Ψ lb (lenv_heads Δ) (lenv_bot Δ) →
      styped (<[φ := ub]> Φ) Ψ (Some T :: Δ) (∅, Some (FVar φ)) e U →
      styped_sd Φ Ψ Δ F (Lam e) (TLolli ub lb T U)
  | sd_app Φ Ψ Δ Δ1 Δ2 F e1 e2 ub lb T U :
      lenv_split Δ Δ1 Δ2 → hub_below_s Ψ Φ ub F →
      styped Φ Ψ Δ1 (sf_unionb F (lenv_heads Δ2) (lenv_bot Δ2)) e1 (TLolli ub lb T U) →
      styped Φ Ψ Δ2 (sf_union F (opt_heads lb)) e2 T →
      styped_sd Φ Ψ Δ F (App e1 e2) U
  | sd_pair Φ Ψ Δ Δ1 Δ2 F e1 e2 T U :
      lenv_split Δ Δ1 Δ2 →
      styped Φ Ψ Δ1 (sf_unionb F (lenv_heads Δ2) (lenv_bot Δ2)) e1 T →
      styped Φ Ψ Δ2 (sf_unionb F (heads T) (hbot T)) e2 U →
      styped_sd Φ Ψ Δ F (Pair e1 e2) (TProd T U)
  | sd_letu Φ Ψ Δ Δ1 Δ2 F e1 e2 T :
      lenv_split Δ Δ1 Δ2 →
      styped Φ Ψ Δ1 (sf_unionb F (lenv_heads Δ2) (lenv_bot Δ2)) e1 TUnit →
      styped Φ Ψ Δ2 F e2 T →
      styped_sd Φ Ψ Δ F (LetU e1 e2) T
  | sd_letp Φ Ψ Δ Δ1 Δ2 F e1 e2 T1 T2 T :
      lenv_split Δ Δ1 Δ2 →
      styped Φ Ψ Δ1 (sf_unionb F (lenv_heads Δ2) (lenv_bot Δ2)) e1 (TProd T1 T2) →
      styped Φ Ψ (Some T2 :: Some T1 :: Δ2) F e2 T →
      styped_sd Φ Ψ Δ F (LetP e1 e2) T
  | sd_inj1 Φ Ψ Δ F e T U :
      styped Φ Ψ Δ F e T → styped_sd Φ Ψ Δ F (Inj1 e) (TSum T U)
  | sd_inj2 Φ Ψ Δ F e T U :
      styped Φ Ψ Δ F e U → styped_sd Φ Ψ Δ F (Inj2 e) (TSum T U)
  | sd_case Φ Ψ Δ Δ1 Δ2 F e e1 e2 T1 T2 T :
      lenv_split Δ Δ1 Δ2 →
      styped Φ Ψ Δ1 (sf_unionb F (lenv_heads Δ2) (lenv_bot Δ2)) e (TSum T1 T2) →
      styped Φ Ψ (Some T1 :: Δ2) F e1 T →
      styped Φ Ψ (Some T2 :: Δ2) F e2 T →
      styped_sd Φ Ψ Δ F (Case e e1 e2) T
  | sd_box Φ Ψ Δ F e m k C ub T φ :
      lenv_unl Δ → φ ∉ dom Φ →
      (∀ ss, length ss = k → Forall hcontractive ss →
         styped (<[φ := ub]> (fhyps_pinst (pshift m) Φ))
           (hyps_inst (pshift m) Ψ ++ [(bcs_inst (pshift m) C, ids m)])
           (lenv_pinst (pshift m) (Some (TBox m k C (TLolli ub None TUnit T)) :: Δ))
           (∅, Some (FVar φ)) e (sinst_ty (slist ss) T)) →
      styped_sd Φ Ψ Δ F (EBox e) (TBox m k C (TLolli ub None TUnit T)).

(** In a plain context every derivation ends in a syntax-directed rule
    followed by conversions and packs. A pack makes the type an
    existential, and a conversion keeps it one. *)
Lemma sd_of Φ Ψ Δ F e T :
  styped Φ Ψ Δ F e T → plain Δ →
  ∃ T0, styped_sd Φ Ψ Δ F e T0 ∧ (hsteq Ψ T0 T ∨ is_ex T).
Proof.
  intros Hd. apply styped_sderiv in Hd. induction Hd; intros Hp;
    try (eexists; split;
         [econstructor;
          first [eassumption|apply sderiv_styped; eassumption
                |intros; apply sderiv_styped; auto]|left; apply hsteq_refl]).
  - (* E-Weak *) rewrite (wk_plain _ _ H Hp) in IHHd. by apply IHHd.
  - (* E-Contract *) exfalso. destruct (Hp 0 U eq_refl) as [Hn _]. by apply Hn.
  - (* E-Conv *) destruct (IHHd Hp) as (T0 & Hsd & HT0). exists T0. split; [done|].
    destruct HT0 as [Hq|Hx]; [left; by eapply hsteq_trans|right; by eapply hsteq_ex].
  - (* E-Pack *) destruct (IHHd Hp) as (T0 & Hsd & _). exists T0. split; [done|right; exact I].
  - (* E-Open *) exfalso. destruct (Hp i _ H) as [_ Hn]. by apply Hn.
Qed.

Lemma sd_app_inv Φ Ψ Δ F e1 e2 U :
  styped_sd Φ Ψ Δ F (App e1 e2) U →
  ∃ Δ1 Δ2 ub lb A, lenv_split Δ Δ1 Δ2 ∧ hub_below_s Ψ Φ ub F ∧
    styped Φ Ψ Δ1 (sf_unionb F (lenv_heads Δ2) (lenv_bot Δ2)) e1 (TLolli ub lb A U) ∧
    styped Φ Ψ Δ2 (sf_union F (opt_heads lb)) e2 A.
Proof. inversion 1; subst. eexists _, _, _, _, _. split_and!; eassumption. Qed.

Lemma sd_konst_inv Φ Ψ Δ F k K :
  styped_sd Φ Ψ Δ F (Konst k) K → lenv_empty Δ ∧ konst_ty (heqs Ψ) (hlt Ψ) (hyp_known Ψ) k K.
Proof. inversion 1; subst. by split. Qed.

Lemma sd_var_inv Φ Ψ Δ F x V : styped_sd Φ Ψ Δ F (Var x) V → lenv_only Δ x V.
Proof. by inversion 1. Qed.

(** ** Inversion of the forms of T2 *)

Lemma inv_letu Φ Ψ Δ F e1 e2 T :
  styped Φ Ψ Δ F (LetU e1 e2) T → plain Δ →
  ∃ Δ1 Δ2 T0, lenv_split Δ Δ1 Δ2 ∧
    styped Φ Ψ Δ1 (sf_unionb F (lenv_heads Δ2) (lenv_bot Δ2)) e1 TUnit ∧
    styped Φ Ψ Δ2 F e2 T0.
Proof.
  intros H Hp. destruct (sd_of _ _ _ _ _ _ H Hp) as (T0 & Hsd & _).
  inversion Hsd; subst. eexists _, _, _. split_and!; eassumption.
Qed.

Lemma inv_letp Φ Ψ Δ F e1 e2 T :
  styped Φ Ψ Δ F (LetP e1 e2) T → plain Δ →
  ∃ Δ1 Δ2 T1 T2 T0, lenv_split Δ Δ1 Δ2 ∧
    styped Φ Ψ Δ1 (sf_unionb F (lenv_heads Δ2) (lenv_bot Δ2)) e1 (TProd T1 T2) ∧
    styped Φ Ψ (Some T2 :: Some T1 :: Δ2) F e2 T0.
Proof.
  intros H Hp. destruct (sd_of _ _ _ _ _ _ H Hp) as (T0 & Hsd & _).
  inversion Hsd; subst. eexists _, _, _, _, _. split_and!; eassumption.
Qed.

Lemma inv_case Φ Ψ Δ F e e1 e2 T :
  styped Φ Ψ Δ F (Case e e1 e2) T → plain Δ →
  ∃ Δ1 Δ2 T1 T2 T0, lenv_split Δ Δ1 Δ2 ∧
    styped Φ Ψ Δ1 (sf_unionb F (lenv_heads Δ2) (lenv_bot Δ2)) e (TSum T1 T2) ∧
    styped Φ Ψ (Some T1 :: Δ2) F e1 T0 ∧
    styped Φ Ψ (Some T2 :: Δ2) F e2 T0.
Proof.
  intros H Hp. destruct (sd_of _ _ _ _ _ _ H Hp) as (T0 & Hsd & _).
  inversion Hsd; subst. eexists _, _, _, _, _. split_and!; eassumption.
Qed.

Lemma inv_var Φ Ψ Δ F x T :
  styped Φ Ψ Δ F (Var x) T → plain Δ →
  ∃ V, lenv_only Δ x V ∧ (hsteq Ψ V T ∨ is_ex T).
Proof.
  intros H Hp. destruct (sd_of _ _ _ _ _ _ H Hp) as (T0 & Hsd & HT).
  exists T0. split; [by apply sd_var_inv in Hsd|done].
Qed.

(** An application of a constant to a variable. The context holds the
    variable and nothing else, and the upper point of the constant lies
    below the future. *)
Lemma inv_kv Φ Ψ Δ F k x T :
  styped Φ Ψ Δ F (App (Konst k) (Var x)) T → plain Δ →
  ∃ ub lb A U K V,
    hub_below_s Ψ Φ ub F ∧
    konst_ty (heqs Ψ) (hlt Ψ) (hyp_known Ψ) k K ∧ hsteq Ψ K (TLolli ub lb A U) ∧
    Δ !! x = Some (Some V) ∧ (hsteq Ψ V A ∨ is_ex A) ∧
    (∀ y W, Δ !! y = Some (Some W) → y = x) ∧
    (hsteq Ψ U T ∨ is_ex T).
Proof.
  intros H Hp. destruct (sd_of _ _ _ _ _ _ H Hp) as (U & Hsd & HU).
  destruct (sd_app_inv _ _ _ _ _ _ _ Hsd) as (Δ1 & Δ2 & ub & lb & A & Hs & Hub & H1 & H2).
  destruct (plain_split _ _ _ Hs Hp) as [Hp1 Hp2].
  destruct (sd_of _ _ _ _ _ _ H1 Hp1) as (K & Hsd1 & HK).
  destruct (sd_konst_inv _ _ _ _ _ _ Hsd1) as [He1 Hk].
  destruct HK as [HK|[]].
  destruct (inv_var _ _ _ _ _ _ H2 Hp2) as (V & [HV Honly] & HVA).
  exists ub, lb, A, U, K, V. split_and!; [done|done|done| |done| |done].
  - by eapply lenv_split_lookup_r.
  - intros y W Hy. destruct (lenv_split_lookup_inv _ _ _ _ _ Hs Hy) as [Hy1|Hy2].
    + exfalso. apply list_elem_of_lookup_2, He1 in Hy1. discriminate.
    + by destruct (Honly _ _ Hy2).
Qed.

(** ** Facts *)

Lemma hfl_np Ψ Φ a b : hfl Ψ Φ a b → ∀ x y, a = NP x → b = NP y → hlt Ψ x y.
Proof.
  unfold hlt.
  induction 1 as [x0 y0 H|φ u H|x0 x' b H Hb IH|a y0 y' Ha IH H|a y0 b H1 IH1 H2 IH2|x0|x0];
    intros x y Ea Eb.
  - injection Ea as <-. injection Eb as <-. by apply hl_h.
  - discriminate.
  - injection Ea as <-. subst b. eapply hl_eql; [exact H|]. by apply IH.
  - injection Eb as <-. subst a. eapply hl_eqr; [|exact H]. by apply IH.
  - subst a b. eapply hl_trans; [by apply IH1|by apply IH2].
  - injection Ea as <-. injection Eb as <-. apply hl_po.
  - injection Ea as <-. injection Eb as <-. apply hl_dpo.
Qed.

Lemma hub_fact Ψ Φ x F y : hub_below_s Ψ Φ (Some x) F → y ∈ F.1 → hlt Ψ x y.
Proof. intros [H _] Hy. eapply hfl_np; [apply H; exact Hy|done|done]. Qed.

Lemma sf_unionb_fst F X b : X ⊆ (sf_unionb F X b).1.
Proof. destruct b; simpl; set_solver. Qed.

Lemma lenv_heads_lookup Δ i T y : Δ !! i = Some (Some T) → y ∈ heads T → y ∈ lenv_heads Δ.
Proof.
  revert i. induction Δ as [|o Δ IH]; intros i Hi Hy; [done|].
  destruct i as [|i]; simpl in Hi.
  - injection Hi as ->. simpl. set_solver.
  - destruct o; simpl; [apply elem_of_union_r|]; by eapply IH.
Qed.

Lemma hlt_eqs Ψ x x' y y' : heqs Ψ x' x → heqs Ψ y y' → hlt Ψ x y → hlt Ψ x' y'.
Proof. intros Hx Hy H. unfold hlt. eapply hl_eql; [exact Hx|]. by eapply hl_eqr. Qed.

(** A binding the variable of an application does not take stays on the
    other side of the split. *)
Lemma split_other Δ Δ1 Δ2 y W x :
  lenv_split Δ Δ1 Δ2 → Δ !! y = Some (Some W) →
  (∀ z W', Δ1 !! z = Some (Some W') → z = x) → y ≠ x →
  Δ2 !! y = Some (Some W).
Proof.
  intros Hs Hy Hon Hne. destruct (lenv_split_lookup_inv _ _ _ _ _ Hs Hy) as [H1|H2]; [|done].
  by apply Hon in H1.
Qed.

(** ** The shapes of recv and close *)

Lemma recv_shape Ψ K :
  konst_ty (heqs Ψ) (hlt Ψ) (hyp_known Ψ) KRecv K →
  ∃ m P S x, K = TLolli (Some x) None (TSess (SSeq (SRcv m P) S) x)
                  (TProd (payload_at m P x) (TSess S (pt_shift 1 x))).
Proof.
  intros H.
  assert (∀ k K, konst_ty (heqs Ψ) (hlt Ψ) (hyp_known Ψ) k K → k = KRecv →
    ∃ m P S x, K = TLolli (Some x) None (TSess (SSeq (SRcv m P) S) x)
                  (TProd (payload_at m P x) (TSess S (pt_shift 1 x)))) as G.
  { apply (konst_ty_case _ _ _ (λ k K, k = KRecv → ∃ m P S x,
      K = TLolli (Some x) None (TSess (SSeq (SRcv m P) S) x)
            (TProd (payload_at m P x) (TSess S (pt_shift 1 x)))));
      intros; first [discriminate|by eexists _, _, _, _]. }
  by apply (G KRecv K).
Qed.

Lemma clos_shape Ψ K :
  konst_ty (heqs Ψ) (hlt Ψ) (hyp_known Ψ) KClos K →
  ∃ x, K = TLolli (Some x) None (TSess SEnd x) TUnit.
Proof.
  intros H.
  assert (∀ k K, konst_ty (heqs Ψ) (hlt Ψ) (hyp_known Ψ) k K → k = KClos →
    ∃ x, K = TLolli (Some x) None (TSess SEnd x) TUnit) as G.
  { apply (konst_ty_case _ _ _ (λ k K, k = KClos → ∃ x, K = TLolli (Some x) None (TSess SEnd x) TUnit));
      intros; first [discriminate|by eexists]. }
  by apply (G KClos K).
Qed.

(** ** T2 with both arms at one payload point *)

Definition P0 : ty := TSum (TSess (dual Sd) (pvar 0)) (TSess (dual Sd) (pvar 0)).
Definition Sbr0 : sty := SSeq (SRcv 1 P0) SEnd.

Lemma dual_Sch0 : dual Sch0 = Sbr0.
Proof. done. Qed.

Lemma hd_rcv m P S : hd (SSeq (SRcv m P) S) = HRcv m P S.
Proof. unfold hd. by rewrite unfoldS_rcv. Qed.

(** T2 with c′ at the variable i. [choice_main] has i = 2, and the
    context of [t_new_at] twice has i = 4. *)
Definition t2i (i : nat) : expr := branch (Var i) t2_arm1 t2_arm2.
Definition t2 : expr := t2i 2.

(** The receive on c′ at a point x: the sum it binds has both arms at
    points equal to x[0]. *)
Lemma t2_recv Φ Ψ Δ F a i T1 T2 :
  plain Δ → (∀ U, Δ !! i = Some (Some U) → U = TSess Sbr0 a) →
  styped Φ Ψ Δ F (App ERecv (Var i)) (TProd T1 T2) →
  ∃ x r1 y1 r2 y2 r y, T1 = TSum (TSess r1 y1) (TSess r2 y2) ∧ T2 = TSess r y ∧
    heqs Ψ (pt_payload x 0) y1 ∧ heqs Ψ (pt_payload x 0) y2.
Proof.
  intros Hp Hc H.
  destruct (inv_kv _ _ _ _ _ _ _ H Hp) as (ub & lb & A & U & K & V & _ & HK & HKA & HV & HVA & _ & HU).
  destruct (recv_shape _ _ HK) as (m & P & S & x & ->).
  apply Hc in HV as ->.
  cbn [hsteq] in HKA. destruct HKA as (_ & _ & HA & HUr).
  destruct A as [| | | | |s z|]; cbn [hsteq] in HA; try contradiction.
  destruct HVA as [HVA|[]]. cbn [hsteq] in HVA.
  destruct HA as [Hxz Hs], HVA as [Haz Hs'].
  pose proof (seq_trans _ _ _ Hs (seq_sym _ _ Hs')) as Hss.
  apply seq_step in Hss. unfold eq_step in Hss. unfold Sbr0 in Hss. rewrite !hd_rcv in Hss.
  destruct Hss as (-> & HP & _).
  destruct HU as [HU|[]].
  pose proof (hsteq_trans Ψ (TProd (payload_at 1 P x) (TSess S (pt_shift 1 x))) U _ HUr HU) as HT.
  unfold P0 in HP.
  destruct P as [| | |P1 P2| | |]; cbn [eqT] in HP; try contradiction. destruct HP as [HP1 HP2].
  destruct P1 as [| | | | |s1 z1|]; cbn [eqT] in HP1; try contradiction.
  destruct P2 as [| | | | |s2 z2|]; cbn [eqT] in HP2; try contradiction.
  destruct HP1 as [-> _], HP2 as [-> _].
  assert (payload_at 1 (TSum (TSess s1 (pvar 0)) (TSess s2 (pvar 0))) x
          = TSum (TSess s1 (pt_payload x 0)) (TSess s2 (pt_payload x 0))) as E by reflexivity.
  rewrite E in HT.
  destruct T1 as [| | |T11 T12| | |]; cbn [hsteq] in HT; try (exfalso; destruct HT as [HT _]; exact HT).
  destruct HT as [[H1 H2] HT2].
  destruct T11 as [| | | | |r1 y1|]; cbn [hsteq] in H1; try contradiction.
  destruct T12 as [| | | | |r2 y2|]; cbn [hsteq] in H2; try contradiction.
  destruct T2 as [| | | | |r y|]; cbn [hsteq] in HT2; try contradiction.
  destruct H1 as [Hy1 _], H2 as [Hy2 _].
  exists x, r1, y1, r2, y2, r, y. by split_and!.
Qed.

(* END POINTS: open, see report.
Theorem t2i_underivable Φ Ψ Δ F T a i :
  (∀ p, ¬ hlt Ψ p p) → plain Δ → (∀ U, Δ !! i = Some (Some U) → U = TSess Sbr0 a) →
  ¬ styped Φ Ψ Δ F (t2i i) T.
Proof.
  intros Hacy Hp Hc H. unfold t2i, branch in H.
  (* let (p, c) = recv c′ *)
  destruct (inv_letp _ _ _ _ _ _ _ H Hp) as (Δ1 & Δ2 & T1 & T2 & T0 & Hs & H1 & H2).
  destruct (plain_split _ _ _ Hs Hp) as [Hp1 Hp2].
  assert (∀ U, Δ1 !! i = Some (Some U) → U = TSess Sbr0 a) as Hc1
    by (intros U HU; apply Hc; by eapply lenv_split_lookup_l).
  destruct (t2_recv _ _ _ _ _ _ _ _ Hp1 Hc1 H1) as (x & r1 & y1 & r2 & y2 & r & y & -> & -> & Hy1 & Hy2).
  assert (plain (Some (TSess r y) :: Some (TSum (TSess r1 y1) (TSess r2 y2)) :: Δ2)) as Hpb
    by (apply plain_some; [intros []|intros []|apply plain_some; [intros []|intros []|exact Hp2]]).
  (* let () = close c *)
  destruct (inv_letu _ _ _ _ _ _ _ H2 Hpb) as (Δb1 & Δb2 & Tb & Hsb & Hb1 & Hb2).
  destruct (plain_split _ _ _ Hsb Hpb) as [Hpb1 Hpb2].
  destruct (inv_kv _ _ _ _ _ _ _ Hb1 Hpb1) as (? & ? & ? & ? & ? & ? & _ & _ & _ & _ & _ & Honb & _).
  assert (Δb2 !! 1 = Some (Some (TSum (TSess r1 y1) (TSess r2 y2)))) as Hsum
    by (eapply split_other; [exact Hsb|done|exact Honb|done]).
  (* case p *)
  destruct (inv_case _ _ _ _ _ _ _ _ Hb2 Hpb2) as (Δc1 & Δc2 & C1 & C2 & Tc & Hsc & Hsc1 & Ha1 & Ha2).
  destruct (plain_split _ _ _ Hsc Hpb2) as [Hpc1 Hpc2].
  destruct (inv_var _ _ _ _ _ _ Hsc1 Hpc1) as (V & [HV _] & HVs).
  rewrite (lenv_split_lookup_l _ _ _ _ _ Hsc HV) in Hsum. injection Hsum as ->.
  destruct HVs as [HVs|[]].
  destruct C1 as [| | | | |q1 z1|]; cbn [hsteq] in HVs; try (exfalso; destruct HVs as [HVs _]; exact HVs).
  destruct C2 as [| | | | |q2 z2|]; cbn [hsteq] in HVs; try (exfalso; destruct HVs as [_ HVs]; exact HVs).
  destruct HVs as [[Hz1 _] [Hz2 _]].
  (* first arm: close d while holding k *)
  unfold t2_arm1 in Ha1.
  assert (plain (Some (TSess q1 z1) :: Δc2)) as Hpa by (apply plain_some; [intros []|intros []|exact Hpc2]).
  destruct (inv_letu _ _ _ _ _ _ _ Ha1 Hpa) as (Δa1 & Δa2 & ? & Hsa & Hc1' & _).
  destruct (plain_split _ _ _ Hsa Hpa) as [Hpa1 _].
  destruct (inv_kv _ _ _ _ _ _ _ Hc1' Hpa1)
    as (ub & lb & A & U & K & V4 & Hub & HK & HKA & HV4 & HVA & Hona & _).
  destruct (clos_shape _ _ HK) as (xc & ->).
  destruct ub as [xc'|]; cbn [hsteq opt_rel] in HKA; [|by destruct HKA].
  destruct HKA as (Hxc & _ & HA & _).
  destruct A as [| | | | |s w|]; cbn [hsteq] in HA; try contradiction. destruct HA as [Hxw _].
  destruct HVA as [HVA|[]].
  destruct V4 as [| | | | |s4 δ|]; cbn [hsteq] in HVA; try contradiction. destruct HVA as [Hδw _].
  assert (Δa2 !! 0 = Some (Some (TSess q1 z1))) as Hk
    by (eapply split_other; [exact Hsa|done|exact Hona|done]).
  assert (hlt Ψ xc' z1) as F1.
  { eapply hub_fact; [exact Hub|]. apply sf_unionb_fst.
    eapply lenv_heads_lookup; [exact Hk|]. simpl. set_solver. }
  assert (Δc2 !! 3 = Some (Some (TSess s4 δ))) as Hd.
  { pose proof (lenv_split_lookup_l _ _ _ _ _ Hsa HV4) as E. exact E. }
  (* second arm: receive on k while holding d *)
  unfold t2_arm2 in Ha2.
  assert (plain (Some (TSess q2 z2) :: Δc2)) as Hpa' by (apply plain_some; [intros []|intros []|exact Hpc2]).
  destruct (inv_letp _ _ _ _ _ _ _ Ha2 Hpa') as (Δe1 & Δe2 & ? & ? & ? & Hse & He1 & _).
  destruct (plain_split _ _ _ Hse Hpa') as [Hpe1 _].
  destruct (inv_kv _ _ _ _ _ _ _ He1 Hpe1)
    as (ub' & lb' & A' & U' & K' & V0 & Hub' & HK' & HKA' & HV0 & HVA' & Hone & _).
  destruct (recv_shape _ _ HK') as (m' & P' & S' & xr & ->).
  destruct ub' as [xr'|]; cbn [hsteq opt_rel] in HKA'; [|by destruct HKA'].
  destruct HKA' as (Hxr & _ & HA' & _).
  destruct A' as [| | | | |s' w'|]; cbn [hsteq] in HA'; try contradiction. destruct HA' as [Hxw' _].
  assert (V0 = TSess q2 z2) as ->.
  { pose proof (lenv_split_lookup_l _ _ _ _ _ Hse HV0) as E. simpl in E. congruence. }
  destruct HVA' as [HVA'|[]]. cbn [hsteq] in HVA'. destruct HVA' as [Hzw' _].
  assert (Δe2 !! 4 = Some (Some (TSess s4 δ))) as Hd'
    by (eapply split_other; [exact Hse|exact Hd|exact Hone|done]).
  assert (hlt Ψ xr' δ) as F2.
  { eapply hub_fact; [exact Hub'|]. apply sf_unionb_fst.
    eapply lenv_heads_lookup; [exact Hd'|]. simpl. set_solver. }
  (* δ ≺ x[0] ≺ δ *)
  assert (hlt Ψ δ (pt_payload x 0)) as G1.
  { eapply hlt_eqs; [|apply he_sym; exact (he_trans _ _ _ _ Hy1 Hz1)|exact F1].
    eapply he_trans; [exact Hδw|]. eapply he_trans; [apply he_sym; exact Hxw|exact Hxc]. }
  assert (hlt Ψ (pt_payload x 0) δ) as G2.
  { eapply hlt_eqs; [|apply he_refl|exact F2].
    eapply he_trans; [exact (he_trans _ _ _ _ Hy2 Hz2)|].
    eapply he_trans; [exact Hzw'|]. eapply he_trans; [apply he_sym; exact Hxw'|exact Hxr]. }
  apply (Hacy δ). by eapply hlt_trans.
Qed.

*)

(** ** The body of the program after the two news

      body₀ = let () = spawn T1 in let () = spawn T3 in T2

    The two spawns take a part of the context, and T2 runs in the rest.
    c′ is in the rest or nowhere, so T2 is underivable in either case. *)

(* END POINTS: open, see report.
Theorem t2_underivable Φ Ψ Δ F T a :
  (∀ p, ¬ hlt Ψ p p) → plain Δ → (∀ U, Δ !! 2 = Some (Some U) → U = TSess Sbr0 a) →
  ¬ styped Φ Ψ Δ F t2 T.
Proof. apply t2i_underivable. Qed.

*)

(** The body with any two spawned thunks: they are never inverted. *)
Definition bodyg (i : nat) (e1 e3 : expr) : expr :=
  LetU (App ESpawn e1) (LetU (App ESpawn e3) (t2i i)).

Definition body0 : expr := bodyg 2 t1_thunk t3_thunk.

(* END POINTS: open, see report.
Theorem bodyg_underivable Φ Ψ Δ F T a i e1 e3 :
  (∀ p, ¬ hlt Ψ p p) → plain Δ → (∀ U, Δ !! i = Some (Some U) → U = TSess Sbr0 a) →
  ¬ styped Φ Ψ Δ F (bodyg i e1 e3) T.
Proof.
  intros Hacy Hp Hc H. unfold bodyg in H.
  destruct (inv_letu _ _ _ _ _ _ _ H Hp) as (Δ1 & Δ2 & T1 & Hs & _ & H2).
  destruct (plain_split _ _ _ Hs Hp) as [_ Hp2].
  assert (∀ U, Δ2 !! i = Some (Some U) → U = TSess Sbr0 a) as Hc2
    by (intros U HU; apply Hc; by eapply lenv_split_lookup_r).
  destruct (inv_letu _ _ _ _ _ _ _ H2 Hp2) as (Δ3 & Δ4 & T2' & Hs' & _ & H4).
  destruct (plain_split _ _ _ Hs' Hp2) as [_ Hp4].
  refine (t2i_underivable _ _ _ _ _ a i Hacy Hp4 _ H4).
  intros U HU. apply Hc2. by eapply lenv_split_lookup_r.
Qed.

Theorem body0_underivable Φ Ψ Δ F T a :
  (∀ p, ¬ hlt Ψ p p) → plain Δ → (∀ U, Δ !! 2 = Some (Some U) → U = TSess Sbr0 a) →
  ¬ styped Φ Ψ Δ F body0 T.
Proof. apply bodyg_underivable. Qed.

*)

(** ** Top-level constraints

    A fact of the hypothesis (C₀, ιs) of a program is a fact of the
    closure of C₀, so an acyclic C₀ has an irreflexive order. *)

Lemma length_ids n : length (ids n) = n.
Proof. unfold ids. by rewrite length_fmap, length_seq. Qed.

Lemma hyp_fact_c0 n C g :
  bc_env C = [] → hyp_fact [(C, ids n)] g → bcs_open n C g.
Proof.
  intros Henv (C' & xs & Hin & g0 & Hg0 & ->).
  apply list_elem_of_singleton in Hin. injection Hin as -> ->.
  rewrite length_ids in Hg0. destruct (c0_open_vb n C g0 Henv Hg0) as [Hsc _].
  destruct g0 as [x y]; destruct Hsc as [Hx Hy]; cbn [fact_map];
    rewrite !pt_inst_ids by done; exact Hg0.
Qed.

Lemma heqs_c0 n C x y : bc_env C = [] → heqs [(C, ids n)] x y → geq (c0_eq n C) x y.
Proof.
  intros Henv ->. apply geq_refl.
Qed.

Lemma hfl_c0 n C Φ a b :
  bc_env C = [] → hfl [(C, ids n)] Φ a b →
  ∀ x y, a = NP x → b = NP y → glt (c0_eq n C) (c0_lt n C) x y.
Proof.
  intros Henv.
  induction 1 as [x0 y0 H|φ u H|x0 x' b H Hb IH|a y0 y' Ha IH H|a y0 b H1 IH1 H2 IH2|x0|x0];
    intros x y Ea Eb.
  - injection Ea as <-. injection Eb as <-. apply glt_base. by apply hyp_fact_c0.
  - discriminate.
  - injection Ea as <-. subst b. eapply glt_eq; [by apply heqs_c0|by apply IH|apply geq_refl].
  - injection Eb as <-. subst a. eapply glt_eq; [apply geq_refl|by apply IH|by apply heqs_c0].
  - subst a b. eapply glt_trans; [by apply IH1|by apply IH2].
  - injection Ea as <-. injection Eb as <-. apply glt_po.
  - injection Ea as <-. injection Eb as <-. apply glt_dpo.
Qed.

Lemma c0_irrefl n C : c0_acyclic n C → ∀ p, ¬ hlt [(C, ids n)] p p.
Proof.
  intros [Henv Hacy] p Hp. apply (Hacy p). by eapply (hfl_c0 n C ∅); [exact Henv|exact Hp|..].
Qed.

(* END POINTS: open, see report.
Corollary body0_underivable_top n C Φ Δ F T a :
  c0_acyclic n C → plain Δ → (∀ U, Δ !! 2 = Some (Some U) → U = TSess Sbr0 a) →
  ¬ styped Φ [(C, ids n)] Δ F body0 T.
Proof. intros HC. apply body0_underivable. by apply c0_irrefl. Qed.

*)

(** ** The route of [choice_typed]

    [choice_typed] creates c at a and d at δ with [t_new_at], which types
    the body under the same hypotheses with the two ends of each channel
    at its point. With Sch₀ in place of Sch the premise of the two
    [t_new_at] steps is the judgment below, and it has no derivation for
    any acyclic top-level constraint. The two thunks are whatever the
    renaming of [let_new_pair] makes of T1 and T3. *)

Lemma choice_main_new : ∃ e1 e3, choice_main = let_new (let_new (bodyg 4 e1 e3)).
Proof. eexists _, _. unfold choice_main, let_new_pair, bodyg, t2i. cbn. reflexivity. Qed.

Definition Δnew : lenv :=
  [Some (TSess (dual SEnd) (pd 0)); Some (TSess SEnd (pd 0)); None; None;
   Some (TSess (dual Sch0) (pa 0)); Some (TSess Sch0 (pa 0)); None; None].

(* END POINTS: open, see report.
Theorem negative_new_at C Φ F T e1 e3 :
  c0_acyclic 2 C → ¬ styped Φ [(C, ids 2)] Δnew F (bodyg 4 e1 e3) T.
Proof.
  intros HC. apply (bodyg_underivable _ _ _ _ _ (pa 0) 4).
  - by apply c0_irrefl.
  - intros i U HU. unfold Δnew in HU.
    destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; simpl in HU; try discriminate;
      injection HU as <-; split; intros [].
  - intros U HU. unfold Δnew in HU. simpl in HU. injection HU as <-. reflexivity.
Qed.
*)
