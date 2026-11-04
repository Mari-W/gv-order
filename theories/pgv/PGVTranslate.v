(** * From PGV derivations to the static system, and deadlock freedom

    A derivation Γ ⊢^p M : T of the fragment ([pgv_frag]) becomes a
    derivation of [typed] at the protocol-point world [Wpgv], at every
    future F above u_p ([pgv_translate]). [soundness] then makes every
    closed program of type 1 deadlock free ([pgv_deadlock_free]).

    The term changes in two places ([pgv_eta]). The upper point of our
    send, recv and close is the channel's point, and PGV's is u_o. An
    unapplied send, recv, close or wait therefore becomes λz. k z, and
    an applied one stays. Our new has the existential signature alone
    (sharp edges 104), so PGV's new becomes λz. let ∗ = z in let ⟨a, b⟩
    = new ∗ in ⟨a, b⟩ on the encoded let of new ([new_tr]), typed at
    the protocol point of its session by the alias ι ≡ x ([t_new_at]).
    pgv/PGVSimulation.v carries deadlock freedom back to the program
    itself.

    PGV's bound p corresponds to futures. A side condition p < pr(Δ)
    puts u_p below every head of Δ, q < p′ puts u_q below ℓ_p′, and the
    lower bound pr(Γ) of T-Lam is at or below every head of Γ. *)

From stdpp Require Import base gmap.
From LRGV Require Export pgv.PGVWorld.

Set Default Proof Using "All".

(** ** The translation of terms *)

Definition comm (k : konst) : bool :=
  match k with KSend | KRecv | KClos => true | _ => false end.

(** PGV's new, λz. let ∗ = z in let ⟨a, b⟩ = new ∗ in ⟨a, b⟩. *)
Definition new_tr : expr := Lam (LetU (Var 0) (let_new_pair (Pair (Var 1) (Var 0)))).

(** The translation of an unapplied constant. *)
Definition kon_eta (k : konst) : expr :=
  match k with
  | KSend | KRecv | KClos => Lam (App (Konst k) (Var 0))
  | KNew => new_tr
  | _ => Konst k
  end.

Lemma kon_eta_comm k : comm k = true → kon_eta k = Lam (App (Konst k) (Var 0)).
Proof. by destruct k. Qed.

Fixpoint pgv_eta (e : expr) : expr :=
  match e with
  | Konst k => kon_eta k
  | App (Konst k) e2 => App (if comm k then Konst k else kon_eta k) (pgv_eta e2)
  | App e1 e2 => App (pgv_eta e1) (pgv_eta e2)
  | Lam e => Lam (pgv_eta e)
  | Pair e1 e2 => Pair (pgv_eta e1) (pgv_eta e2)
  | LetU e1 e2 => LetU (pgv_eta e1) (pgv_eta e2)
  | LetP e1 e2 => LetP (pgv_eta e1) (pgv_eta e2)
  | Inj1 e => Inj1 (pgv_eta e)
  | Inj2 e => Inj2 (pgv_eta e)
  | Case e e1 e2 => Case (pgv_eta e) (pgv_eta e1) (pgv_eta e2)
  | EBox e => EBox (pgv_eta e)
  | Var _ | EUnit | Chan _ => e
  end.

(** ** Environments *)

Lemma tr_env_split Γ Γ1 Γ2 : psplit Γ Γ1 Γ2 → lenv_split (tr_env Γ) (tr_env Γ1) (tr_env Γ2).
Proof. induction 1; simpl; by constructor. Qed.

Lemma tr_env_empty Γ : penv_empty Γ → lenv_empty (tr_env Γ).
Proof.
  intros H o Ho. apply list_elem_of_fmap in Ho as (o' & -> & Ho). by rewrite (H o' Ho).
Qed.

Lemma tr_env_lookup Γ x : tr_env Γ !! x = fmap tr_ty <$> Γ !! x.
Proof. revert x. induction Γ as [|o Γ IH]; intros [|x]; simpl; [done..|apply IH]. Qed.

Lemma tr_env_only Γ x T : penv_only Γ x T → lenv_only (tr_env Γ) x (tr_ty T).
Proof.
  intros [H1 H2]. split.
  - by rewrite tr_env_lookup, H1.
  - intros y T' Hy. rewrite tr_env_lookup in Hy.
    destruct (Γ !! y) as [[T0|]|] eqn:E; simplify_eq/=.
    destruct (H2 y T0 E) as [-> ->]. done.
Qed.

Lemma lenv_split_empty Δ : lenv_empty Δ → lenv_split Δ Δ Δ.
Proof.
  induction Δ as [|o Δ IH]; intros H; [constructor|].
  rewrite (H o) by set_solver. constructor. apply IH. intros o' Ho'. apply H. set_solver.
Qed.

(** ** Futures *)

Lemma sf_union_empty F : sf_union F ∅ = F.
Proof. destruct F as [P o]. unfold sf_union. simpl. by rewrite union_empty_r_L. Qed.

(** A lower upper point stays below the future. *)
Lemma ubs_lower Φ a b F :
  (∀ x, a = Some x → ∃ y, b = Some y ∧ (x = y ∨ w_lt Wpgv x y)) →
  ub_below_s Wpgv [] Φ b F → ub_below_s Wpgv [] Φ a F.
Proof.
  intros Hab Hb. destruct a as [x|]; [|done].
  destruct (Hab x eq_refl) as (y & -> & [<-|Hxy]); [done|].
  destruct Hb as (H1 & H2 & H3). split_and!; [| |done].
  - intros z Hz. eapply (fl_trans (FCtx Wpgv [] Φ)); [by apply fl_w|by apply H1].
  - intros φ Hφ. eapply (fl_trans (FCtx Wpgv [] Φ)); [by apply fl_w|by apply H2].
Qed.

Lemma ubs_prio Φ a b F : prio_le a b → ub_below_s Wpgv [] Φ (ubp b) F → ub_below_s Wpgv [] Φ (ubp a) F.
Proof. intros Hab. apply ubs_lower. intros x Hx. by eapply ubp_mono. Qed.

(** Adding points above the upper point keeps it below the future. *)
Lemma ubs_union Φ u F X :
  ub_below_s Wpgv [] Φ u F → (∀ x, u = Some x → ∀ h, h ∈ X → w_lt Wpgv x h) →
  ub_below_s Wpgv [] Φ u (sf_union F X).
Proof.
  destruct u as [x|]; [|done]. intros (H1 & H2 & H3) HX. split_and!; [|done|done]. simpl.
  intros y [Hy|Hy]%elem_of_union; [by apply H1|]. apply fl_w. by apply (HX x).
Qed.

Lemma prio_le_max_l a b : prio_le a (prio_max a b).
Proof. destruct a, b; simpl; lia. Qed.
Lemma prio_le_max_r a b : prio_le b (prio_max a b).
Proof. destruct a, b; simpl; lia. Qed.
Lemma prio_le_trans a b c : prio_le a b → prio_le b c → prio_le a c.
Proof. destruct a, b, c; simpl; lia. Qed.

(** u_p lies below the heads of an environment above p. *)
Lemma ubp_below_env p Γ x h :
  prio_lt p (pr_env Γ) → ubp p = Some x → h ∈ lenv_heads (tr_env Γ) → w_lt Wpgv x h.
Proof.
  intros Hp Hx Hh. apply heads_tr_env in Hh. destruct p as [|n|]; simpl in Hx; try done.
  injection Hx as <-. by eapply upt_below_hd.
Qed.

Lemma ubp_below_ty p T x h :
  prio_lt p (pr T) → ubp p = Some x → h ∈ heads (tr_ty T) → w_lt Wpgv x h.
Proof.
  intros Hp Hx Hh. apply heads_tr in Hh. destruct p as [|n|]; simpl in Hx; try done.
  injection Hx as <-. by eapply upt_below_hd.
Qed.

(** ** Applied constants of PGV *)

Lemma pgv_konst_comm ok k p q T U :
  pgv_konst ok k (PLolli p q T U) → comm k = true →
  p = PTop ∧ ∃ o, q = PNat o.
Proof. inversion 1; simpl; intros; try done; eauto. Qed.

(** send, recv, close and wait applied to an argument. The upper point
    of our constant is the channel's point, which lies below u_o. *)
Lemma konst_app ok k o T U Φ Δ Δ1 Δ2 F e2 :
  (∀ s, ok s → top_mono s) →
  pgv_konst ok k (PLolli PTop (PNat o) T U) →
  lenv_split Δ Δ1 Δ2 → lenv_empty Δ1 →
  ub_below_s Wpgv [] Φ (Some (upt o)) F →
  typed Wpgv Φ [] ∅ Δ2 F e2 (tr_ty T) →
  typed Wpgv Φ [] ∅ Δ F (App (Konst k) e2) (tr_ty U).
Proof.
  intros Hok Hk Hs He Hub H2.
  assert (∀ s, spr s = o → ub_below_s Wpgv [] Φ (Some (ppt s)) F) as Hx.
  { intros s <-. eapply ubs_lower; [|exact Hub]. intros x [=<-].
    eexists. split; [done|]. right. apply ppt_below_upt. }
  inversion Hk as [| |o' T0 S Hpr Hs0|o' T0 S Hpr Hs0|o'|o'|]; subst.
  - (* send *)
    set (x := ppt (PSnd o T0 S)).
    eapply t_conv.
    2:{ eapply (t_app Wpgv Φ [] ∅ ∅ ∅ Δ Δ1 Δ2 F _ _ (Some x) None
                  (TProd (tr_ty T0) (TSess (SSeq (SSnd 0 (tr_ty T0)) (tr_sty S)) x))
                  (TSess (tr_sty S) (pt_shift 1 x))).
        - apply comp0, Wpgv_wf.
        - done.
        - by apply Hx.
        - apply t_const; [done| |by apply tr_pscoped].
          rewrite <-(payload_tr T0 x) at 1. apply KTSend. rewrite hbot_tr.
          rewrite payload_tr. intros h Hh. apply sl_w. apply (ppt_below_hd _ (pr T0)); [|by apply heads_tr].
          done.
        - rewrite sf_union_empty. exact H2. }
    simpl. split; [|apply seq_refl]. apply se_w, pgv_eq; [done|done|].
    apply den_ppt_next. apply (Hok _ Hs0).
  - (* recv *)
    set (x := ppt (PRcv o T0 S)).
    eapply t_conv.
    2:{ eapply (t_app Wpgv Φ [] ∅ ∅ ∅ Δ Δ1 Δ2 F _ _ (Some x) None
                  (TSess (SSeq (SRcv 0 (tr_ty T0)) (tr_sty S)) x)
                  (TProd (payload_at 0 (tr_ty T0) x) (TSess (tr_sty S) (pt_shift 1 x)))).
        - apply comp0, Wpgv_wf.
        - done.
        - by apply Hx.
        - apply t_const; [done|apply KTRecv|by apply tr_pscoped].
        - rewrite sf_union_empty. exact H2. }
    rewrite payload_tr. simpl. split; [apply teq_steq, teq_refl|].
    split; [|apply seq_refl]. apply se_w, pgv_eq; [done|done|].
    apply den_ppt_next_rcv. apply (Hok _ Hs0).
  - (* close *)
    eapply (t_app Wpgv Φ [] ∅ ∅ ∅ Δ Δ1 Δ2 F _ _ (Some (ppt (PEndS o))) None).
    + apply comp0, Wpgv_wf.
    + done.
    + by apply Hx.
    + apply t_const; [done|apply KTClos|done].
    + rewrite sf_union_empty. exact H2.
  - (* wait *)
    eapply (t_app Wpgv Φ [] ∅ ∅ ∅ Δ Δ1 Δ2 F _ _ (Some (ppt (PEndR o))) None).
    + apply comp0, Wpgv_wf.
    + done.
    + by apply Hx.
    + apply t_const; [done|apply KTClos|done].
    + rewrite sf_union_empty. exact H2.
Qed.

(** PGV's new at the session S. *)
Lemma new_tr_typed Φ Γ F S :
  penv_empty Γ →
  typed Wpgv Φ [] ∅ (tr_env Γ) F new_tr
    (TLolli None None TUnit (TProd (TSess (tr_sty S) (ppt S)) (TSess (dual (tr_sty S)) (ppt S)))).
Proof.
  intros HΓ. pose proof (tr_env_empty Γ HΓ) as HΔ.
  set (S' := tr_sty S). set (x := ppt S). set (φ := fresh (dom Φ)).
  unfold new_tr. eapply (t_abs _ _ _ _ _ _ _ _ _ _ _ φ).
  - apply is_fresh.
  - unfold tenv_heads, lb_below_hb. rewrite map_fold_empty, union_empty_l_L, lenv_bot_tr.
    by apply lenv_heads_tr_empty.
  - eapply (t_letstar Wpgv _ [] ∅ ∅ ∅ _ (Some TUnit :: tr_env Γ) (None :: tr_env Γ)).
    + apply comp0, Wpgv_wf.
    + by apply lsplit_l, lenv_split_empty.
    + apply t_var. split; [done|]. intros [|y] T' Hy; simpl in Hy; [by simplify_eq|].
      apply list_elem_of_lookup_2 in Hy. by apply HΔ in Hy.
    + change (let_new_pair (Pair (Var 1) (Var 0))) with (let_new (Pair (Var 1) (Var 0))).
      apply (t_new_at Wpgv _ _ _ _ _ _ _ S' x Wpgv_strict); [left; by apply pgv_known|].
      assert (∀ y T', (None :: None :: None :: tr_env Γ) !! y = Some (Some T') → False) as Hn.
      { intros [|[|[|y]]] T' Hy; simpl in Hy; try done.
        apply list_elem_of_lookup_2 in Hy. by apply HΔ in Hy. }
      eapply (t_pair Wpgv _ [] ∅ ∅ ∅ _ (None :: Some (TSess S' x) :: None :: None :: None :: tr_env Γ)
                (Some (TSess (dual S') x) :: None :: None :: None :: None :: tr_env Γ)).
      * apply comp0, Wpgv_wf.
      * apply lsplit_r, lsplit_l, lsplit_none, lsplit_none, lsplit_none, lenv_split_empty, HΔ.
      * apply t_var. split; [done|]. intros [|[|y]] T' Hy; simpl in Hy; [done|by simplify_eq|].
        exfalso. by apply (Hn y T').
      * apply t_var. split; [done|]. intros [|[|y]] T' Hy; simpl in Hy; [by simplify_eq|done|].
        exfalso. by apply (Hn y T').
Qed.

(** A constant of PGV is a constant here, λz. k z or [new_tr]. *)
Lemma konst_tr ok k T Φ Γ F :
  (∀ s, ok s → top_mono s) → penv_empty Γ → pgv_konst ok k T →
  typed Wpgv Φ [] ∅ (tr_env Γ) F (pgv_eta (Konst k)) (tr_ty T).
Proof.
  intros Hok HΓ Hk. pose proof (tr_env_empty Γ HΓ) as HΔ.
  destruct (comm k) eqn:Ek.
  - destruct T as [| | |p q T U|]; try by inversion Hk.
    destruct (pgv_konst_comm _ _ _ _ _ _ Hk Ek) as [-> [o ->]].
    simpl. rewrite (kon_eta_comm k Ek). set (φ := fresh (dom Φ)).
    eapply t_abs.
    + apply is_fresh.
    + simpl. unfold tenv_heads, lb_below_hb. rewrite map_fold_empty, union_empty_l_L, lenv_bot_tr.
      by apply lenv_heads_tr_empty.
    + eapply (konst_app ok k o T U _ (Some (tr_ty T) :: tr_env Γ) (None :: tr_env Γ)
                (Some (tr_ty T) :: tr_env Γ)); [done|done| | | |].
      * constructor. by apply lenv_split_empty.
      * intros o' Ho'. apply elem_of_cons in Ho' as [->|Ho']; [done|by apply HΔ].
      * split_and!; simpl; [set_solver| |done]. intros φ' [=<-]. apply (fl_v (FCtx _ _ _)). simpl.
        by rewrite lookup_insert_eq.
      * apply t_var. split; [done|]. intros [|y] T' Hy; simpl in Hy; [by simplify_eq|].
        apply list_elem_of_lookup_2 in Hy. by apply HΔ in Hy.
  - destruct Hk as [S|p q| | | | |S]; simpl in Ek |- *; try done.
    + rewrite tr_sty_dual, ppt_dual. by apply new_tr_typed.
    + apply t_const; [done|apply KTSpawn|done].
    + apply t_const; [done| |done]. rewrite tr_sty_dual, ppt_dual.
      apply KTLink. apply se_refl.
Qed.

Lemma pgv_konst_inv ok Γ p k T :
  pgv_typed ok Γ p (Konst k) T → p = PBot ∧ penv_empty Γ ∧ pgv_konst ok k T.
Proof. inversion 1; subst; auto. Qed.

(** ** The translation lemma *)

Theorem pgv_translate ok Γ p M T :
  (∀ s, ok s → top_mono s) →
  pgv_typed ok Γ p M T →
  ∀ Φ F, ub_below_s Wpgv [] Φ (ubp p) F →
  typed Wpgv Φ [] ∅ (tr_env Γ) F (pgv_eta M) (tr_ty T).
Proof.
  intros Hok. pose proof Wpgv_wf as HW.
  induction 1 as [Γ x T Hx|Γ k T HΓ Hk|Γ HΓ|Γ M T U q HM IH
                 |Γ Γ1 Γ2 M N T U p q p' q' Hs HM IHM HN IHN Hp Hq
                 |Γ Γ1 Γ2 M N T p q Hs HM IHM HN IHN Hp
                 |Γ Γ1 Γ2 M N T U p q Hs HM IHM HN IHN Hp Hq
                 |Γ Γ1 Γ2 M N T T' U p q Hs HM IHM HN IHN Hp
                 |Γ M T U p HM IH Hpr|Γ M T U p HM IH Hpr
                 |Γ Γ1 Γ2 L M N T T' U p q Hs HL IHL HM IHM HN IHN Hp];
    intros Φ F HF; simpl.
  - (* T-Var *)
    apply t_var. by apply tr_env_only.
  - (* T-Const *)
    by apply (konst_tr ok).
  - (* T-Unit *)
    apply t_unit. by apply tr_env_empty.
  - (* T-Lam *)
    set (φ := fresh (dom Φ)).
    eapply t_abs.
    + apply is_fresh.
    + unfold tenv_heads, lb_below_hb. rewrite map_fold_empty, union_empty_l_L, lenv_bot_tr.
      destruct (pr_env Γ) as [|n|] eqn:EP; simpl.
      * intros y Hy. apply heads_tr_env in Hy. rewrite EP in Hy.
        destruct (lbp_below_hd PBot lbot y eq_refl Hy) as [<-|H]; [left; apply se_refl|].
        right. by apply sl_w.
      * intros y Hy. apply heads_tr_env in Hy. rewrite EP in Hy.
        destruct (lbp_below_hd (PNat n) (lpt n) y eq_refl Hy) as [<-|H]; [left; apply se_refl|].
        right. by apply sl_w.
      * apply set_eq. intros y. split; [|set_solver]. intros Hy.
        apply heads_tr_env in Hy. rewrite EP in Hy. by apply hd_ok_top in Hy.
    + apply IH. destruct (ubp q) as [u|] eqn:Eu; [|done]. split_and!; simpl; [set_solver| |done].
      intros φ' [=<-]. apply (fl_v (FCtx _ _ _)). simpl. by rewrite lookup_insert_eq.
  - (* T-App *)
    assert (ub_below_s Wpgv [] Φ (ubp q) (sf_union F (opt_heads (lbp p')))) as HFN.
    { apply ubs_union.
      - eapply ubs_prio; [|exact HF].
        eapply prio_le_trans; [apply prio_le_max_r|apply prio_le_max_l].
      - intros u Hu h Hh. destruct (lbp p') as [l|] eqn:El; simpl in Hh; [|set_solver].
        apply elem_of_singleton in Hh as ->. by eapply ubp_below_lbp. }
    assert (ub_below_s Wpgv [] Φ (ubp p) (sf_union F (lenv_heads (tr_env Γ2)))) as HFM.
    { apply ubs_union.
      - eapply ubs_prio; [|exact HF].
        eapply prio_le_trans; [apply prio_le_max_l|apply prio_le_max_l].
      - intros u Hu h Hh. by eapply ubp_below_env. }
    assert ((∃ k, M = Konst k ∧ comm k = true) ∨ ¬ ∃ k, M = Konst k ∧ comm k = true)
      as [(k & -> & Ek)|HMk].
    { destruct M; try (right; intros (? & [=] & ?); fail).
      destruct (comm k) eqn:E; [left; eauto|right; intros (? & [=<-] & ?); congruence]. }
    + (* an applied send, recv, close or wait *)
      destruct (pgv_konst_inv _ _ _ _ _ HM) as (-> & HΓ1 & Hk).
      destruct (pgv_konst_comm _ _ _ _ _ _ Hk Ek) as [-> [o ->]]. rewrite Ek.
      eapply (konst_app ok k o T U Φ _ (tr_env Γ1) (tr_env Γ2)); [done|done| |by apply tr_env_empty| |].
      * by apply tr_env_split.
      * apply (ubs_prio _ (PNat o) (prio_max (prio_max PBot q) (PNat o)) F); [apply prio_le_max_r|exact HF].
      * apply IHN. rewrite <-(sf_union_empty F). simpl in HFN. exact HFN.
    + assert (match M with Konst k => App (if comm k then Konst k else kon_eta k) (pgv_eta N)
              | _ => App (pgv_eta M) (pgv_eta N) end = App (pgv_eta M) (pgv_eta N)) as ->.
      { destruct M; try done. simpl. destruct (comm k) eqn:Ek; [|done].
        exfalso. apply HMk. by exists k. }
      eapply (t_app Wpgv Φ [] ∅ ∅ ∅ _ (tr_env Γ1) (tr_env Γ2) F _ _ (ubp q') (lbp p')).
      * by apply comp0.
      * by apply tr_env_split.
      * eapply ubs_prio; [|exact HF]. apply prio_le_max_r.
      * unfold sf_unionb; rewrite ?lenv_bot_tr, ?hbot_tr, (tenv_heads0 Wpgv HW), union_empty_l_L. by apply IHM.
      * by apply IHN.
  - (* T-LetUnit *)
    eapply (t_letstar Wpgv Φ [] ∅ ∅ ∅ _ (tr_env Γ1) (tr_env Γ2)).
    + by apply comp0.
    + by apply tr_env_split.
    + unfold sf_unionb; rewrite ?lenv_bot_tr, ?hbot_tr, (tenv_heads0 Wpgv HW), union_empty_l_L. apply IHM. apply ubs_union.
      * eapply ubs_prio; [|exact HF]. apply prio_le_max_l.
      * intros u Hu h Hh. by eapply ubp_below_env.
    + apply IHN. eapply ubs_prio; [|exact HF]. apply prio_le_max_r.
  - (* T-Pair *)
    eapply (t_pair Wpgv Φ [] ∅ ∅ ∅ _ (tr_env Γ1) (tr_env Γ2)).
    + by apply comp0.
    + by apply tr_env_split.
    + unfold sf_unionb; rewrite ?lenv_bot_tr, ?hbot_tr, (tenv_heads0 Wpgv HW), union_empty_l_L. apply IHM. apply ubs_union.
      * eapply ubs_prio; [|exact HF]. apply prio_le_max_l.
      * intros u Hu h Hh. by eapply ubp_below_env.
    + unfold sf_unionb. rewrite hbot_tr. apply IHN. apply ubs_union.
      * eapply ubs_prio; [|exact HF]. apply prio_le_max_r.
      * intros u Hu h Hh. by eapply ubp_below_ty.
  - (* T-LetPair *)
    eapply (t_letpair Wpgv Φ [] ∅ ∅ ∅ _ (tr_env Γ1) (tr_env Γ2)).
    + by apply comp0.
    + by apply tr_env_split.
    + unfold sf_unionb; rewrite ?lenv_bot_tr, ?hbot_tr, (tenv_heads0 Wpgv HW), union_empty_l_L. apply IHM. apply ubs_union.
      * eapply ubs_prio; [|exact HF]. apply prio_le_max_l.
      * intros u Hu h Hh. eapply (ubp_below_env p (Some T' :: Some T :: Γ2)); [done|done|].
        simpl. rewrite !elem_of_union. by right; right.
    + apply (IHN Φ F). eapply ubs_prio; [|exact HF]. apply prio_le_max_r.
  - (* T-Inl *)
    apply t_inj1. by apply IH.
  - (* T-Inr *)
    apply t_inj2. by apply IH.
  - (* T-CaseSum *)
    eapply (t_case Wpgv Φ [] ∅ ∅ ∅ _ (tr_env Γ1) (tr_env Γ2)).
    + by apply comp0.
    + by apply tr_env_split.
    + unfold sf_unionb; rewrite ?lenv_bot_tr, ?hbot_tr, (tenv_heads0 Wpgv HW), union_empty_l_L. apply IHL. apply ubs_union.
      * eapply ubs_prio; [|exact HF]. apply prio_le_max_l.
      * intros u Hu h Hh. by eapply ubp_below_env.
    + apply (IHM Φ F). eapply ubs_prio; [|exact HF]. apply prio_le_max_r.
    + apply (IHN Φ F). eapply ubs_prio; [|exact HF]. apply prio_le_max_r.
Qed.

(** ** Deadlock freedom *)

Theorem pgv_deadlock_free M p :
  pgv_frag [] p M PUnit → deadlock_free (∅, {[+ pgv_eta M +]}).
Proof.
  intros HM. apply (soundness Wpgv _ TUnit Wpgv_strict).
  apply ptyped_closed; [constructor|].
  apply (pgv_translate pgv_mono [] p M PUnit pgv_mono_top HM).
  destruct (ubp p); [|done]. split; simpl; [set_solver|done].
Qed.

(** A program that applies every send, recv, close and wait is its own
    translation. *)
Theorem pgv_deadlock_free_applied M p :
  pgv_frag [] p M PUnit → pgv_eta M = M → deadlock_free (∅, {[+ M +]}).
Proof. intros HM E. rewrite <-E. by apply (pgv_deadlock_free M p). Qed.
