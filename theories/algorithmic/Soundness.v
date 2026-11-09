(** * Soundness of the algorithmic judgment for the source judgment

    [synth_sound]: a run of [synth] that returns (T, c), together with
    any hypothesis context Ψ in which c holds, gives a derivation of
    [styped Φ Ψ Δ F (erase a) T]. With [soundness_source] this makes
    every closed program the checker accepts deadlock free, as soon as
    its constraint holds under the program's creation constraint C₀
    ([synth_deadlock_free]). *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export algorithmic.Algorithmic.

Set Default Proof Using "All".

(** ** Linear environments *)

Lemma lenv_emptyb_sound Δ : lenv_emptyb Δ = true → lenv_empty Δ.
Proof.
  induction Δ as [|[T|] Δ IH]; simpl; intros H o Ho; [by apply elem_of_nil in Ho|done|].
  apply elem_of_cons in Ho as [->|Ho]; [done|by apply IH].
Qed.

Lemma lenv_onlyb_sound x Δ T : lenv_onlyb x Δ = Some T → lenv_only Δ x T.
Proof.
  revert x. induction Δ as [|[T'|] Δ IH]; intros [|x] H; simpl in *; try discriminate.
  - destruct (lenv_emptyb Δ) eqn:He; [|discriminate]. injection H as <-. split; [done|].
    intros [|y] T'' Hy; simpl in Hy; [by simplify_eq|]. exfalso.
    apply lenv_emptyb_sound in He. apply list_elem_of_lookup_2 in Hy. by apply He in Hy.
  - destruct (IH x H) as [H1 H2]. split; [done|]. intros [|y] T'' Hy; simpl in Hy; [done|].
    destruct (H2 y T'' Hy). split; [lia|done].
Qed.

Lemma sf_union_none F : sf_union F (opt_heads None) = F.
Proof. destruct F as [P o]. unfold sf_union. simpl. by rewrite union_empty_r_L. Qed.

(** ** The gate {u} ≺ F *)

Lemma ub_constr_sound Ψ Φ ub F : csat Ψ (ub_constr Φ ub F) → hub_below_s Ψ Φ ub F.
Proof.
  destruct ub as [u|]; [|done]. destruct F as [P o]. destruct o as [[φ|o']|].
  - simpl. destruct (Φ !! φ) as [[u'|]|] eqn:HΦ; simpl; intros [HP Ho]; try done. split_and!.
    + intros y Hy. apply hlt_hfl. by apply HP.
    + intros φ' Hφ'. injection Hφ' as <-. destruct Ho as [He|Hl].
      * eapply hl_eql; [exact He|]. by apply hl_v.
      * eapply hl_trans; [by apply hlt_hfl|]. by apply hl_v.
    + done.
  - simpl. intros [_ []].
  - simpl. intros [HP _]. split_and!; [intros y Hy; apply hlt_hfl; by apply HP|intros φ Hφ; discriminate|done].
Qed.

(** ** Matching *)

Lemma omatch_sound Ψ o o' c : omatch o o' = Some c → csat Ψ c → opt_rel (heqs Ψ) o o'.
Proof.
  destruct o as [x|], o' as [y|]; simpl; intros H Hc; try discriminate; injection H as <-; done.
Qed.

Lemma tmatch_sound Ψ T : ∀ U c, tmatch T U = Some c → csat Ψ c → hsteq Ψ T U.
Proof.
  induction T as [| ub lb T1 IH1 T2 IH2 | T1 IH1 T2 IH2 | T1 IH1 T2 IH2 | | s x | | x];
    intros [] c H Hc; simpl in H; try discriminate.
  - by injection H as <-.
  - destruct (omatch ub ub0) as [c0|] eqn:H0; [|discriminate].
    destruct (omatch lb lb0) as [c1|] eqn:H1; [|discriminate].
    destruct (tmatch T1 T) as [c2|] eqn:H2; [|discriminate].
    destruct (tmatch T2 U) as [c3|] eqn:H3; [|discriminate].
    injection H as <-. simpl in Hc.
    destruct Hc as (Hc0 & Hc1 & Hc2 & Hc3 & _). simpl.
    split_and!; [by eapply omatch_sound|by eapply omatch_sound|by eapply IH1|by eapply IH2].
  - destruct (tmatch T1 T) as [c1|] eqn:H1; [|discriminate].
    destruct (tmatch T2 U) as [c2|] eqn:H2; [|discriminate].
    injection H as <-. destruct Hc as [Hc1 Hc2]. simpl. split; [by eapply IH1|by eapply IH2].
  - destruct (tmatch T1 T) as [c1|] eqn:H1; [|discriminate].
    destruct (tmatch T2 U) as [c2|] eqn:H2; [|discriminate].
    injection H as <-. destruct Hc as [Hc1 Hc2]. simpl. split; [by eapply IH1|by eapply IH2].
  - destruct (sty_eqb s S) eqn:Hs; [|discriminate]. injection H as <-.
    apply sty_eqb_sound in Hs as ->. simpl. split; [exact Hc|apply seq_refl].
Qed.

(** ** Scoping *)

Lemma pt_scopedb_sound k x : pt_scopedb k x = true → pt_scoped k x.
Proof.
  unfold pt_scopedb, pt_scoped. intros H a Ha. rewrite Ha in H. by apply Nat.ltb_lt.
Qed.

Lemma opt_scopedb_sound k o : opt_scopedb k o = true → opt_scoped k o.
Proof. destruct o; simpl; [apply pt_scopedb_sound|done]. Qed.

Lemma lb_scopedb_sound k lb : lb_scopedb k lb = true → lb_scoped k lb.
Proof. destruct lb; simpl; [done|done|apply pt_scopedb_sound]. Qed.

Lemma bcs_scopedb_sound k C : bcs_scopedb k C = true → bcs_scoped k C.
Proof.
  unfold bcs_scopedb, bcs_scoped. induction (bc_env C) as [|x xs IH]; simpl; intros H; [constructor|].
  apply andb_true_iff in H as [H1 H2]. constructor; [by apply pt_scopedb_sound|by apply IH].
Qed.

Lemma pscopedb_sound T : ∀ k, pscopedb k T = true → pscoped k T.
Proof.
  induction T as [| ub lb T1 IH1 U IH2 | T1 IH1 U IH2 | T1 IH1 U IH2 | n kk C T1 IH | s x | lb n C T1 IH | x];
    intros k H; simpl in *.
  - done.
  - apply andb_true_iff in H as [[[H1 H2]%andb_true_iff H3]%andb_true_iff H4].
    split_and!; auto using opt_scopedb_sound.
  - apply andb_true_iff in H as [H1 H2]. auto.
  - apply andb_true_iff in H as [H1 H2]. auto.
  - apply andb_true_iff in H as [H1 H2]. split; [by apply bcs_scopedb_sound|auto].
  - by apply pt_scopedb_sound.
  - apply andb_true_iff in H as [[H1 H2]%andb_true_iff H3].
    split_and!; [by apply lb_scopedb_sound|by apply bcs_scopedb_sound|auto].
  - by apply pt_scopedb_sound.
Qed.

(** ** The head of a session type is bisimilar to it *)

Lemma seq_unfoldS s : seq s (unfoldS s).
Proof.
  apply seq_unf. destruct (unfoldS_cases s) as [[_ H]|[_ H]].
  - by rewrite (unfoldS_hd (unfoldS s) H).
  - rewrite H. symmetry. exact H.
Qed.

Lemma hd_seq s h : hd s = h → seq s (unview h).
Proof. intros <-. rewrite <-unfoldS_unview. apply seq_unfoldS. Qed.

(** ** Constants applied to an argument *)

Lemma st_app_konst Φ Ψ Δ F k e2 ub T U A :
  konst_ty (heqs Ψ) (hlt Ψ) (hyp_known Ψ) k (TLolli ub None T U) → kscoped k (TLolli ub None T U) →
  hub_below_s Ψ Φ ub F → hsteq Ψ A T → styped Φ Ψ Δ F e2 A →
  styped Φ Ψ Δ F (App (Konst k) e2) U.
Proof.
  intros Hk Hs Hub Heq He.
  eapply (st_app Φ Ψ Δ (lenv_nones Δ) Δ F _ _ ub None T U); [apply lenv_split_nones_l|exact Hub| |].
  - apply st_konst; [apply lenv_empty_nones|exact Hk|exact Hs].
  - rewrite sf_union_none. eapply st_conv; [exact Heq|exact He].
Qed.

Lemma konst_app_sound Φ Ψ Δ F k A U c e2 :
  konst_app Φ F k A = Some (U, c) → csat Ψ c → styped Φ Ψ Δ F e2 A →
  styped Φ Ψ Δ F (App (Konst k) e2) U.
Proof.
  intros Hk Hc He. destruct k; simpl in Hk; try discriminate.
  - (* spawn *)
    destruct A as [| ub lb [] []| | | | | |]; try discriminate. injection Hk as <- <-.
    eapply st_app_konst; [apply KTSpawn|done|done| |exact He]. apply teq_hsteq. cbn. split_and!; done.
  - (* recv *)
    destruct A as [| | | | | s x| |]; try discriminate.
    destruct (hd s) as [|m T s'| | | | | | |] eqn:Hhd; try discriminate.
    destruct (pscopedb m T) eqn:Hps; [|discriminate]. simpl in Hk. injection Hk as <- <-.
    eapply (st_app_konst _ _ _ _ _ _ (Some x) (TSess (SSeq (SRcv m T) s') x));
      [apply KTRecv|by apply pscopedb_sound|by apply ub_constr_sound| |exact He].
    simpl. split; [apply he_refl|exact (hd_seq _ _ Hhd)].
  - (* send *)
    destruct A as [| | P [| | | | | s x| |]| | | | |]; try discriminate.
    destruct (hd s) as [| |m T s'| | | | | |] eqn:Hhd; try discriminate.
    destruct (hbot T) eqn:Hb; [discriminate|]. destruct (pscopedb m T) eqn:Hps; [|discriminate].
    simpl in Hk. destruct (tmatch P (payload_at m T x)) as [c0|] eqn:Hm; [|discriminate].
    injection Hk as <- <-. simpl in Hc.
    destruct Hc as (Hc0 & Hc1 & Hc2 & _).
    eapply (st_app_konst _ _ _ _ _ _ (Some x)
              (TProd (payload_at m T x) (TSess (SSeq (SSnd m T) s') x)));
      [apply KTSend; rewrite Hb; exact Hc1|by apply pscopedb_sound|by apply ub_constr_sound| |exact He].
    simpl. split; [by eapply tmatch_sound|]. split; [apply he_refl|exact (hd_seq _ _ Hhd)].
  - (* close *)
    destruct A as [| | | | | s x| |]; try discriminate.
    destruct (hd s) as [| | | | | | | |] eqn:Hhd; try discriminate. injection Hk as <- <-.
    eapply (st_app_konst _ _ _ _ _ _ (Some x) (TSess SEnd x));
      [apply KTClos|done|by apply ub_constr_sound| |exact He].
    simpl. split; [apply he_refl|exact (hd_seq _ _ Hhd)].
  - (* link *)
    destruct A as [| | [| | | | | s x| |] [| | | | | r y| |]| | | | |]; try discriminate.
    destruct (sty_eqb r (dual s)) eqn:Hd; [|discriminate].
    destruct (bool_decide (y = pt_dual x)) eqn:Hy; [|discriminate]. injection Hk as <- <-.
    apply sty_eqb_sound in Hd as ->. apply bool_decide_eq_true in Hy as ->.
    eapply (st_app_konst _ _ _ _ _ _ None (TProd (TSess s x) (TSess (dual s) (pt_dual x))));
      [by apply KTLink|done|done| |exact He].
    apply teq_hsteq. cbn. split_and!; [done|apply seq_refl|done|apply seq_refl].
  - (* select₁ *)
    destruct A as [| | | | | s x| |]; try discriminate.
    destruct (hd s) as [| | | | |s1 s2| | |] eqn:Hhd; try discriminate. injection Hk as <- <-.
    destruct Hc as [Hc1 Hc2].
    eapply (st_app_konst _ _ _ _ _ _ (Some x) (TSess (SPlus s1 s2) x));
      [by apply KTSel1|done|by apply ub_constr_sound| |exact He].
    simpl. split; [apply he_refl|exact (hd_seq _ _ Hhd)].
  - (* select₂ *)
    destruct A as [| | | | | s x| |]; try discriminate.
    destruct (hd s) as [| | | | |s1 s2| | |] eqn:Hhd; try discriminate. injection Hk as <- <-.
    destruct Hc as [Hc1 Hc2].
    eapply (st_app_konst _ _ _ _ _ _ (Some x) (TSess (SPlus s1 s2) x));
      [by apply KTSel2|done|by apply ub_constr_sound| |exact He].
    simpl. split; [apply he_refl|exact (hd_seq _ _ Hhd)].
  - (* branch *)
    destruct A as [| | | | | s x| |]; try discriminate.
    destruct (hd s) as [| | | | | |s1 s2| |] eqn:Hhd; try discriminate. injection Hk as <- <-.
    simpl in Hc. destruct Hc as (Hc0 & Hc1 & Hc2 & _).
    eapply (st_app_konst _ _ _ _ _ _ (Some x) (TSess (SWith s1 s2) x));
      [by apply KTBra|done|by apply ub_constr_sound| |exact He].
    simpl. split; [apply he_refl|exact (hd_seq _ _ Hhd)].
Qed.

(** ** new@x, encoded as let_new_at, in the source judgment (static/Fundamental.v, t_new_at) *)

Lemma st_new_at Φ Ψ Δ F e T S x :
  pt_ground x → hyp_known Ψ x →
  styped Φ Ψ (Some (TSess (dual S) (pt_dual x)) :: Some (TSess S x) :: None :: None :: Δ) F e T →
  styped Φ Ψ Δ F (let_new_at (EPt x) e) T.
Proof.
  intros Hg HK Hb. unfold let_new_at.
  set (X := TProd (TSess S x) (TSess (dual S) (pt_dual x))).
  apply (st_letp Φ Ψ Δ (lenv_nones Δ) Δ F _ _ X TUnit).
  { apply lenv_split_nones_l. }
  { apply (st_pair Φ Ψ (lenv_nones Δ) (lenv_nones Δ) (lenv_nones Δ)).
    - apply lenv_split_nones_nones.
    - eapply (st_app Φ Ψ _ _ _ _ _ _ None None (TPt x)).
      + apply lenv_split_nones_l.
      + done.
      + apply st_konst; [apply lenv_empty_nones| |done]. by apply KTNewAt.
      + apply st_pt; [apply lenv_empty_nones|done|done].
    - apply st_unit. apply lenv_empty_nones. }
  apply (st_letu Φ Ψ _ (Some TUnit :: None :: lenv_nones Δ) (None :: Some X :: Δ)).
  { apply lsplit_l, lsplit_r, lenv_split_nones_l. }
  { apply st_var. split; [done|]. intros [|[|y]] T' Hy; simpl in Hy; [by simplify_eq|done|].
    exfalso. unfold lenv_nones in Hy. rewrite list_lookup_fmap in Hy.
    apply fmap_Some in Hy as (? & _ & ?). congruence. }
  apply (st_letp _ _ _ (None :: Some X :: lenv_nones Δ) (None :: None :: Δ)
           _ _ _ (TSess S x) (TSess (dual S) (pt_dual x))); [| |exact Hb].
  - apply lsplit_none, lsplit_l, lenv_split_nones_l.
  - apply st_var. split; [done|]. intros [|[|y]] T' Hy; simpl in Hy; [done|by simplify_eq|].
    exfalso. unfold lenv_nones in Hy. rewrite list_lookup_fmap in Hy.
    apply fmap_Some in Hy as (? & _ & ?). congruence.
Qed.

(** ** Soundness *)

Definition fv_below (n : nat) (Φ : fhyps) : Prop := ∀ φ, φ ∈ dom Φ → φ < n.

Lemma fv_below_insert n Φ ub : fv_below n Φ → fv_below (S n) (<[n := ub]> Φ).
Proof.
  intros H φ Hφ. rewrite dom_insert_L in Hφ. apply elem_of_union in Hφ as [Hφ|Hφ].
  - apply elem_of_singleton in Hφ as ->. lia.
  - specialize (H φ Hφ). lia.
Qed.

Lemma fv_below_pinst n σ Φ : fv_below n Φ → fv_below n (fhyps_pinst σ Φ).
Proof. intros H φ. rewrite fhyps_pinst_dom. apply H. Qed.

Ltac app_gen_case IH1 IH2 Hn H Hc :=
  let Hsok := fresh "Hsok" in
  let H1 := fresh "H1" in let H2 := fresh "H2" in let H3 := fresh "H3" in
  destruct (sok _ 0 _ 0 _) eqn:Hsok in H; [|discriminate];
  destruct (synth _ _ (lp _ 0 _) _ _) as [[[| ubf lbf Tf Uf| | | | | |] c1]|] eqn:H1 in H; try discriminate;
  destruct (synth _ _ (lp _ 0 _) _ _) as [[T' c2]|] eqn:H2 in H; [|discriminate];
  destruct (tmatch T' Tf) as [c3|] eqn:H3 in H; [|discriminate];
  injection H as <- <-;
  simpl in Hc;
  let Hc1 := fresh in let Hc2 := fresh in let Hc3 := fresh in let Hc4 := fresh in
  destruct Hc as (Hc1 & Hc2 & Hc3 & Hc4 & _);
  eapply st_app; [apply lp_split, Hsok|by apply ub_constr_sound|by eapply IH1|];
  eapply st_conv; [by eapply tmatch_sound|by eapply IH2].

Theorem synth_sound a : ∀ n Φ Δ F T c Ψ,
  fv_below n Φ → synth n Φ Δ F a = Some (T, c) → csat Ψ c → styped Φ Ψ Δ F (erase a) T.
Proof.
  induction a as [x| |k|ub lb T0 a IH|a1 IH1 a2 IH2|a1 IH1 a2 IH2|a1 IH1 a2 IH2|a1 IH1 a2 IH2
                 |U0 a IH|T0 a IH|a IH a1 IH1 a2 IH2|s0 C a IH];
    intros n Φ Δ F T c Ψ Hn H Hc; simpl in H.
  - (* var *)
    destruct (lenv_onlyb x Δ) as [T'|] eqn:Hx; [|discriminate]. injection H as <- <-.
    apply st_var. by apply lenv_onlyb_sound.
  - (* unit *)
    destruct (lenv_emptyb Δ) eqn:HΔ; [|discriminate]. injection H as <- <-.
    apply st_unit. by apply lenv_emptyb_sound.
  - (* bare constant *) discriminate.
  - (* λ *)
    destruct (synth (S n) (<[n := ub]> Φ) (Some T0 :: Δ) (∅, Some (FVar n)) a) as [[U c']|] eqn:H1;
      [|discriminate].
    injection H as <- <-. destruct Hc as [Hlb Hc'].
    eapply (st_lam _ _ _ _ _ _ _ _ _ n).
    + intros Hin. specialize (Hn n Hin). lia.
    + exact Hlb.
    + eapply IH; [by apply fv_below_insert|exact H1|exact Hc'].
  - (* application *)
    destruct a1 as [x| |k|ub0 lb0 Ta e| | | | | | | |].
    3: { destruct (synth n Φ Δ F a2) as [[A c2]|] eqn:H2; [|discriminate].
         destruct (konst_app Φ F k A) as [[U c']|] eqn:Hk; [|discriminate].
         injection H as <- <-. destruct Hc as [Hc2 Hc'].
         eapply konst_app_sound; [exact Hk|exact Hc'|by eapply IH2]. }
    all: app_gen_case IH1 IH2 Hn H Hc.
  - (* pair *)
    destruct (sok _ 0 _ 0 _) eqn:Hsok in H; [|discriminate].
    destruct (synth _ _ (lp _ 0 _) _ a1) as [[T1 c1]|] eqn:H1 in H; [|discriminate].
    destruct (synth _ _ (lp _ 0 _) _ a2) as [[T2 c2]|] eqn:H2 in H; [|discriminate].
    injection H as <- <-. destruct Hc as [Hc1 Hc2].
    eapply st_pair; [apply lp_split, Hsok|by eapply IH1|by eapply IH2].
  - (* let () *)
    destruct (sok _ 0 _ 0 _) eqn:Hsok in H; [|discriminate].
    destruct (synth _ _ (lp _ 0 _) _ a1) as [[[| | | | | | |] c1]|] eqn:H1 in H; try discriminate.
    destruct (synth _ _ (lp _ 0 _) _ a2) as [[T2 c2]|] eqn:H2 in H; [|discriminate].
    injection H as <- <-. destruct Hc as [Hc1 Hc2].
    eapply st_letu; [apply lp_split, Hsok|by eapply IH1|by eapply IH2].
  - (* let pair *)
    destruct (sok _ 0 _ 2 _) eqn:Hsok in H; [|discriminate].
    destruct (synth _ _ (lp _ 0 _) _ a1) as [[[| |T1 T2| | | | |] c1]|] eqn:H1 in H; try discriminate.
    destruct (synth _ _ (Some T2 :: Some T1 :: lp _ 2 _) _ a2) as [[T' c2]|] eqn:H2 in H; [|discriminate].
    injection H as <- <-. destruct Hc as [Hc1 Hc2].
    eapply st_letp; [apply lp_split, Hsok|by eapply IH1|by eapply IH2].
  - (* inj₁ *)
    destruct (synth n Φ Δ F a) as [[T1 c1]|] eqn:H1; [|discriminate]. injection H as <- <-.
    apply st_inj1. by eapply IH.
  - (* inj₂ *)
    destruct (synth n Φ Δ F a) as [[T2 c2]|] eqn:H1; [|discriminate]. injection H as <- <-.
    apply st_inj2. by eapply IH.
  - (* case *)
    destruct (sok _ 0 _ 0 _) eqn:Hsok in H; [|discriminate].
    destruct (synth _ _ (lp _ 0 _) _ a) as [[[| | |T1 T2| | | |] c0]|] eqn:H0 in H; try discriminate.
    destruct (synth _ _ (Some T1 :: lp _ 0 _) _ a1) as [[T' c1]|] eqn:H1 in H; [|discriminate].
    destruct (synth _ _ (Some T2 :: lp _ 0 _) _ a2) as [[T'' c2]|] eqn:H2 in H; [|discriminate].
    destruct (tmatch T'' T') as [c3|] eqn:H3 in H; [|discriminate].
    injection H as <- <-. simpl in Hc.
    destruct Hc as (Hc0 & Hc1 & Hc2 & Hc3 & _).
    eapply st_case; [apply lp_split, Hsok|by eapply IH|by eapply IH1|].
    eapply st_conv; [by eapply tmatch_sound|by eapply IH2].
  - (* new@x *)
    destruct (pt_groundb C) eqn:Hg; [|discriminate].
    destruct (synth n Φ _ F a) as [[T' c']|] eqn:H1; [|discriminate].
    injection H as <- <-. simpl in Hc. destruct Hc as (HK & Hb & _).
    apply (st_new_at _ _ _ _ _ _ s0 C); [by apply pt_groundb_sound|exact HK|].
    eapply IH; [exact Hn|exact H1|exact Hb].
Qed.

(** A closed program the checker accepts, whose constraint holds under
    the program's creation constraint C₀, is deadlock free. *)
Theorem synth_deadlock_free m C0 a T c :
  creation_ok m nofact nofact (λ _, False) C0 → prim T →
  synth 0 ∅ [] (∅, None) a = Some (T, c) → csat [(C0, ids m)] c →
  deadlock_free (∅, {[+ erase a +]}).
Proof.
  intros HC HT Hs Hc. apply (soundness_source m C0 _ T HC HT).
  eapply synth_sound; [|exact Hs|exact Hc]. intros φ Hφ. by rewrite dom_empty_L in Hφ.
Qed.

(** Under syntactic points a program that creates a channel names a
    ground point, so its hypotheses are those of [created] over
    constants (sharp edges 173). *)
Theorem synth_deadlock_free_created Ψ a T c :
  created (Wpo []) Ψ → prim T →
  synth 0 ∅ [] (∅, None) a = Some (T, c) → csat Ψ c →
  deadlock_free (∅, {[+ erase a +]}).
Proof.
  intros HΨ HT Hs Hc. apply (soundness_created_s Ψ _ T HΨ HT).
  eapply synth_sound; [|exact Hs|exact Hc]. intros φ Hφ. by rewrite dom_empty_L in Hφ.
Qed.
