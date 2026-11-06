(** * Tools for the examples of context-free session types (stage D)

    Hereditary contractiveness by induction on the depth, closure of it
    under ;, congruences of ≈ for the prefixes the examples rewrite
    under, a derived rule for case with Θ = ∅, the facts of a
    hypothesis whose constraint has outer points, closed boxes under
    more hypotheses, and creation constraints with outer points
    ([cc_ok_out]) with the orders along walks and offsets that prove
    them. The whole programs start under the ceiling of [top_C0], and
    Stream.v and CfstDeadlock.v create the lockstep pair [lsa_C],
    [lsb_C]. All lemmas are general. None of them changes a core
    definition. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.ExampleTools.

Set Default Proof Using "All".

(** ** Hereditary contractiveness *)

Lemma hc_step_mono (τ τ' : sty → Prop) s : (∀ t, τ t → τ' t) → hc_step τ s → hc_step τ' s.
Proof. intros H. unfold hc_step. destruct (hd s); intuition. Qed.

Lemma ahc_S n s : ahc (S n) s = hc_step (ahc n) s.
Proof. done. Qed.

Lemma ahc_mono n : ∀ m s, m ≤ n → ahc n s → ahc m s.
Proof.
  induction n as [|n IH]; intros [|m] s Hm Hs; try done; [lia|].
  rewrite ahc_S in Hs |- *.
  eapply hc_step_mono; [|exact Hs]. intros t Ht. apply IH; [lia|done].
Qed.

Lemma ahc_contractive n s : ahc (S n) s → contractive s.
Proof.
  intros H. rewrite ahc_S in H. unfold hc_step in H.
  unfold contractive. rewrite unfoldS_unview. destruct (hd s) eqn:E; done.
Qed.

(** One depth of the head of S₁;S₂ needs that depth of S₁ and S₂. *)
Lemma ahc_seq n : ∀ s t, ahc n s → ahc n t → ahc n (SSeq s t).
Proof.
  induction n as [|n IH]; intros s t Hs Ht; [done|].
  pose proof (ahc_contractive _ _ Hs) as Cs. pose proof (ahc_contractive _ _ Ht) as Ct.
  pose proof (ahc_mono (S n) n t ltac:(lia) Ht) as Ht'.
  rewrite ahc_S in Hs, Ht |- *. unfold hc_step in Hs, Ht |- *.
  rewrite (hd_seq s t Cs Ct).
  destruct (hd s) as [|m T s'|m T s'|a s'|a s'|a b|a b| |u]; cbn [unview]; try done.
  1-4: rewrite hseq_atom by exact I; cbn [view];
    destruct (sk_cases s' t) as [[-> ->]| ->]; [done|by apply IH].
  all: cbn [hseq view]; destruct Hs; split; by apply IH.
Qed.

Lemma hcontractive_seq s t : hcontractive s → hcontractive t → hcontractive (SSeq s t).
Proof. intros Hs Ht n. apply ahc_seq; [apply Hs|apply Ht]. Qed.

(** Induction on the depth: P is hereditarily contractive when one more
    depth of each member follows from that depth of all members. *)
Lemma hc_ind (P : sty → Prop) :
  (∀ n s, P s → (∀ t, P t → ahc n t) → ahc (S n) s) → ∀ s, P s → hcontractive s.
Proof.
  intros H s Hs n. revert s Hs. induction n as [|n IH]; intros s Hs; [done|].
  apply H; [done|]. intros t Ht. by apply IH.
Qed.

Lemma hcontractive_end : hcontractive SEnd.
Proof. intros [|n]; done. Qed.

Lemma hcontractive_snd m T : hcontractive (SSnd m T).
Proof.
  intros [|n]; [done|]. rewrite ahc_S. unfold hc_step.
  rewrite (hd_of (SSnd m T) (SSeq (SSnd m T) SSkip)) by reflexivity.
  apply hcontractive_skip.
Qed.

Lemma hcontractive_rcv m T : hcontractive (SRcv m T).
Proof.
  intros [|n]; [done|]. rewrite ahc_S. unfold hc_step.
  rewrite (hd_of (SRcv m T) (SSeq (SRcv m T) SSkip)) by reflexivity.
  apply hcontractive_skip.
Qed.

(** ** Congruences of ≈ *)

Lemma seq_snd_cong m T s r : seq s r → seq (SSeq (SSnd m T) s) (SSeq (SSnd m T) r).
Proof.
  intros H [|n]; [done|]. simpl. unfold eq_step.
  rewrite (hd_of _ _ (unfoldS_snd m T s)), (hd_of _ _ (unfoldS_snd m T r)). cbn.
  split_and!; [done|apply eqT_refl, aeq_refl|apply H].
Qed.

Lemma seq_rcv_cong m T s r : seq s r → seq (SSeq (SRcv m T) s) (SSeq (SRcv m T) r).
Proof.
  intros H [|n]; [done|]. simpl. unfold eq_step.
  rewrite (hd_of _ _ (unfoldS_rcv m T s)), (hd_of _ _ (unfoldS_rcv m T r)). cbn.
  split_and!; [done|apply eqT_refl, aeq_refl|apply H].
Qed.

Lemma seq_plus_cong a b a' b' : seq a a' → seq b b' → seq (SPlus a b) (SPlus a' b').
Proof.
  intros Ha Hb [|n]; [done|]. simpl. unfold eq_step.
  rewrite (hd_of _ _ (unfoldS_plus a b)), (hd_of _ _ (unfoldS_plus a' b')). cbn.
  split; [apply Ha|apply Hb].
Qed.

Lemma seq_with_cong a b a' b' : seq a a' → seq b b' → seq (SWith a b) (SWith a' b').
Proof.
  intros Ha Hb [|n]; [done|]. simpl. unfold eq_step.
  rewrite (hd_of _ _ (unfoldS_with a b)), (hd_of _ _ (unfoldS_with a' b')). cbn.
  split; [apply Ha|apply Hb].
Qed.

(** ** Case with Θ = ∅

    Both branches get the linear bindings that occur in either branch. *)
Section rules.
  Context (W : world) (HW : world_wf W).

  Lemma tv_case Φ Ψ Δ F e e1 e2 T1 T2 T :
    sok e 0 (Lam (Pair e1 e2)) 0 Δ && negb (lenv_bot (lp (Lam (Pair e1 e2)) 0 Δ)) = true →
    typed W Φ Ψ ∅ (lp e 0 Δ) (sf_union F (lenv_heads (lp (Lam (Pair e1 e2)) 0 Δ))) e (TSum T1 T2) →
    typed W Φ Ψ ∅ (Some T1 :: lp (Lam (Pair e1 e2)) 0 Δ) F e1 T →
    typed W Φ Ψ ∅ (Some T2 :: lp (Lam (Pair e1 e2)) 0 Δ) F e2 T →
    typed W Φ Ψ ∅ Δ F (Case e e1 e2) T.
  Proof.
    intros Hs H H1 H2. apply andb_true_iff in Hs as [Hs Hb]. apply negb_true_iff in Hb.
    eapply (t_case W Φ Ψ ∅ ∅ ∅ Δ (lp e 0 Δ) (lp (Lam (Pair e1 e2)) 0 Δ));
      [apply (comp0 W HW)|by apply lp_split| |exact H1|exact H2].
    by rewrite Hb, (tenv_heads0 W), union_empty_l_L.
  Qed.
End rules.

Lemma sf_pinst_empty σ o : sf_pinst σ (∅, o) = (∅, o).
Proof. unfold sf_pinst. simpl. by rewrite set_map_empty. Qed.

(** E-Open with Θ = ∅ and the shifted context given in normal form. *)
Lemma tv_open W Φ Ψ Δ F e i lb m C T U Φ' Ψ' Δ' F' U' :
  Δ !! i = Some (Some (TEx lb m C T)) → ¬ unlimited T →
  fhyps_pinst (pshift m) Φ = Φ' →
  hyps_inst (pshift m) Ψ ++ [(bcs_inst (pshift m) C, ids m)] = Ψ' →
  <[i := Some T]> (lenv_pinst (pshift m) Δ) = Δ' →
  sf_pinst (pshift m) F = F' → pinst_ty (pshift m) U = U' →
  typed W Φ' Ψ' ∅ Δ' F' e U' → typed W Φ Ψ ∅ Δ F e U.
Proof.
  intros Hi Hu <- <- <- <- <- H. eapply t_open; [exact Hi|exact Hu|].
  unfold tenv_pinst. by rewrite fmap_empty.
Qed.

(** ** Facts of a constraint with outer points

    C = BCs env P under a binder of |xs| points: instantiating the
    binder by xs and the outer points by env is one instantiation by
    xs ++ env. *)
Lemma pt_inst_env xs env x :
  pt_inst (plist xs) (pt_inst (pup (length xs) (plist env)) x) = pt_inst (plist (xs ++ env)) x.
Proof.
  rewrite pt_inst_comp. apply pt_inst_ext. intros a. unfold compose, pup.
  destruct (decide (a < length xs)) as [Ha|Ha].
  - rewrite pt_inst_pvar_at. unfold plist. rewrite lookup_app_l; [|lia].
    destruct (xs !! a) eqn:E; [done|apply lookup_ge_None_1 in E; lia].
  - unfold plist at 2. destruct (env !! (a - length xs)) as [y|] eqn:Ey.
    + rewrite pt_inst_comp. transitivity (pt_inst pvar y); [apply pt_inst_ext|].
      { intros b. unfold compose. rewrite pt_inst_pvar_at. by apply plist_shift. }
      rewrite pt_inst_pvar. unfold plist. rewrite lookup_app_r by lia. by rewrite Ey.
    + rewrite !pt_inst_pvar_at, (plist_shift xs (length xs)) by done.
      unfold plist. rewrite lookup_app_r by lia. rewrite Ey, length_app.
      apply lookup_ge_None_1 in Ey. unfold pvar. f_equal. f_equal. lia.
Qed.

Lemma bcs_hold_env (eq lt : point → point → Prop) env P xs :
  (∀ f, P f → fact_scoped (length xs + length env) f →
     fact_holds eq lt (fact_map (pt_inst (plist (xs ++ env))) f)) →
  bcs_hold eq lt (BCs env P) xs.
Proof.
  intros H g (f & Hf & Hs & ->). simpl in Hs.
  specialize (H f Hf Hs). destruct f; simpl in *; by rewrite !pt_inst_env.
Qed.

(** A ≺ fact of a hypothesis whose constraint has outer points. *)
Lemma sl_hyp W Ψ env P xs f x y :
  (BCs env P, xs) ∈ Ψ → P f → fact_scoped (length xs + length env) f →
  fact_map (pt_inst (plist (xs ++ env))) f = FLt x y → slt W Ψ x y.
Proof.
  intros Hg Hf Hs E. apply sl_h. exists (BCs env P), xs. split; [done|].
  exists (fact_map (pt_inst (pup (length xs) (plist env))) f). split.
  - exists f. split_and!; [done|done|done].
  - rewrite <-E. destruct f; simpl; by rewrite !pt_inst_env.
Qed.

(** Future variable lookups after E-Open. *)
Ltac fv_look := rewrite ?lookup_fmap; simplify_map_eq; reflexivity.

(** Scoping of a concrete fact, and membership in a concrete list. *)
Ltac fsc := cbn; repeat split; lia.

Ltac inlist := solve [repeat first [apply list_elem_of_here | apply list_elem_of_further]].

(** One typing step, with case. *)
Ltac cstep :=
  match goal with
  | |- typed _ _ _ _ _ _ (Case _ _ _) _ => eapply tv_case; [assumption|reflexivity| | |]
  | _ => tstep
  end.

(** ** Closed boxes under more hypotheses

    A term typed without hypotheses and without free variables types
    under any hypotheses. The whole programs type their boxes once and
    use them under the hypothesis of the ceiling. *)
Lemma sf_pinst_pvar F : sf_pinst pvar F = F.
Proof.
  destruct F as [P o]. unfold sf_pinst. simpl. f_equal.
  apply set_eq. intros x. rewrite elem_of_map. split.
  - intros (y & -> & Hy). by rewrite pt_inst_pvar.
  - intros Hx. exists x. by rewrite pt_inst_pvar.
Qed.

Lemma typed_hyps_wk W Ψ F e T : strict W → typed W ∅ [] ∅ [] F e T → typed W ∅ Ψ ∅ [] F e T.
Proof.
  intros HW H. pose proof (typed_pinst W _ _ _ _ _ _ _ HW H pvar Ψ) as H'.
  rewrite fhyps_pinst_empty, tenv_pinst_empty, sf_pinst_pvar, pinst_ty_pvar in H'.
  apply H'. intros C xs Hm. by apply elem_of_nil in Hm.
Qed.

(** ** Creation constraints with outer points

    A creation constraint whose facts enter the fresh channel from an
    outer point (u ≺ p), leave it to an outer point (q ≺ v), or order
    two points of the channel along an order R. It is acyclic and
    conservative when R contains program order and every entering fact
    u ≺ p and leaving fact q ≺ v with p at or below q in R give u ≺ v in
    the context. *)
Lemma cc_ok_out peq plt C (R : point → point → Prop) :
  (∀ x y z, R x y → R y z → R x z) → (∀ x, ¬ R x x) →
  (∀ x, pt_root x = NVar 0 → R x (pt_shift 1 x)) →
  (∀ x, pt_root x = NVar 0 → R x (pt_shift 1 (pt_dual x))) →
  (∀ a b, bcs_open 1 C (FLt a b) →
     (pt_root a = NVar 0 ∧ pt_root b = NVar 0 ∧ R a b) ∨
     (pt_root a ≠ NVar 0 ∧ pt_root b = NVar 0) ∨ (pt_root a = NVar 0 ∧ pt_root b ≠ NVar 0)) →
  (∀ u p q v, bcs_open 1 C (FLt u p) → bcs_open 1 C (FLt q v) →
     pt_root u ≠ NVar 0 → pt_root p = NVar 0 → pt_root q = NVar 0 → pt_root v ≠ NVar 0 →
     (p = q ∨ R p q) → glt (cc_up peq) (cc_up plt) u v) →
  cc_ok peq plt C.
Proof.
  intros Ht Hi Hp Hd Hc HB.
  apply (cc_model peq plt C id R
           (λ u p, bcs_open 1 C (FLt u p) ∧ pt_root u ≠ NVar 0 ∧ pt_root p = NVar 0)
           (λ q v, bcs_open 1 C (FLt q v) ∧ pt_root q = NVar 0 ∧ pt_root v ≠ NVar 0)).
  - done.
  - done.
  - done.
  - intros x y i E. unfold id in *. by subst.
  - done.
  - exact Ht.
  - exact Hp.
  - exact Hd.
  - exact Hi.
  - intros u p q v (H1 & Hu & Hp') (H2 & Hq & Hv) Hpq. by apply (HB u p q v).
  - intros a b H. unfold id. destruct (Hc a b H) as [(Ha & Hb & Hr)|[(Ha & Hb)|(Ha & Hb)]].
    + right; right; right. split_and!; [done|done|by left].
    + right; left. split_and!; [done|done|]. exists a, b. split; [done|split; [left; apply geq_refl|by left]].
    + right; right; left. split_and!; [done|done|]. exists a, b. split; [done|split; [by left|left; apply geq_refl]].
Qed.

(** A fact of the context, seen under the binder of the fresh point. *)
Lemma glt_up peq plt x y :
  plt x y → glt (cc_up peq) (cc_up plt) (pt_inst (λ a, pvar (a + 1)) x) (pt_inst (λ a, pvar (a + 1)) y).
Proof. intros H. apply glt_base. by exists x, y. Qed.

(** Program order along offsets. *)
Lemma glt_ofs E L p j k : j < k → glt E L (Pt p j) (Pt p k).
Proof.
  intros Hjk. induction Hjk as [|k _ IH].
  - pose proof (glt_po E L (Pt p j)) as H. unfold pt_shift in H. simpl in H.
    by rewrite Nat.add_1_r in H.
  - eapply glt_trans; [exact IH|]. pose proof (glt_po E L (Pt p k)) as H.
    unfold pt_shift in H. simpl in H. by rewrite Nat.add_1_r in H.
Qed.

(** Program order along offsets at either polarity. *)
Lemma glt_ofs_pol E L p b j k : j < k → glt E L (MkPt p b j) (MkPt p b k).
Proof.
  intros Hjk. induction Hjk as [|k _ IH].
  - pose proof (glt_po E L (MkPt p b j)) as H. unfold pt_shift in H. simpl in H.
    by rewrite Nat.add_1_r in H.
  - eapply glt_trans; [exact IH|]. pose proof (glt_po E L (MkPt p b k)) as H.
    unfold pt_shift in H. simpl in H. by rewrite Nat.add_1_r in H.
Qed.

(** x+j ≺ x̄+k for j < k, through x+j ≺ x̄+j+1. *)
Lemma glt_ofs_dual E L p b j k : j < k → glt E L (MkPt p b j) (MkPt p (negb b) k).
Proof.
  intros Hjk. pose proof (glt_dpo E L (MkPt p b j)) as H. unfold pt_shift, pt_dual in H. simpl in H.
  rewrite Nat.add_1_r in H. destruct (decide (S j = k)) as [<-|Hne]; [exact H|].
  eapply glt_trans; [exact H|]. apply glt_ofs_pol. lia.
Qed.

(** A walk that is not empty climbs in the size of the point. *)
Lemma pwalk_size x w : pt_size (pwalk x w) = pt_size x + length w.
Proof.
  revert x. induction w as [|[i|] w IH]; intros x; simpl; [lia| |];
    rewrite IH; unfold pt_size, pt_payload, pt_shift; simpl; lia.
Qed.

(** A walk from the dual point ends at the walk from the point or at
    its dual: a choice step forgets the polarity. *)
Lemma pwalk_dual x v : ∃ b, pwalk (pt_dual x) v = pt_polar b (pwalk x v).
Proof.
  revert x. induction v as [|[i|] v IH]; intros x; simpl.
  - by exists false.
  - exists true. by rewrite pt_payload_dual.
  - rewrite <-pt_dual_shift. apply IH.
Qed.

Lemma pt_polar_polar b c y : ∃ d, pt_polar c (pt_polar b y) = pt_polar d y.
Proof. destruct b, c; simpl; [by exists true|by exists false|by exists false|]. exists true. apply pt_dual_dual. Qed.

Lemma pwalk_polar b x v : ∃ c, pwalk (pt_polar b x) v = pt_polar c (pwalk x v).
Proof. destruct b; [by exists true|apply pwalk_dual]. Qed.

Lemma pt_size_polar b y : pt_size (pt_polar b y) = pt_size y.
Proof. by destruct b. Qed.

(** The order of a channel along its walks. y is above x when a walk
    that is not empty leads from x to y or to ȳ. *)
Definition wlt (x y : point) : Prop := pt_root x = NVar 0 ∧ ∃ v b, v ≠ [] ∧ y = pt_polar b (pwalk x v).

Lemma wlt_trans x y z : wlt x y → wlt y z → wlt x z.
Proof.
  intros [Hx (u & b & Hu & ->)] [_ (v & c & Hv & ->)]. split; [done|].
  destruct (pwalk_polar b (pwalk x u) v) as [d ->].
  destruct (pt_polar_polar d c (pwalk (pwalk x u) v)) as [e ->].
  exists (u ++ v), e. split; [by destruct u|by rewrite pwalk_app].
Qed.

Lemma wlt_irrefl x : ¬ wlt x x.
Proof.
  intros [_ (v & b & Hv & E)]. apply (f_equal pt_size) in E. rewrite pt_size_polar, pwalk_size in E.
  destruct v; [done|simpl in E; lia].
Qed.

Lemma wlt_po x : pt_root x = NVar 0 → wlt x (pt_shift 1 x).
Proof. intros Hx. split; [done|]. by exists [None], true. Qed.

Lemma wlt_dpo x : pt_root x = NVar 0 → wlt x (pt_shift 1 (pt_dual x)).
Proof. intros Hx. split; [done|]. exists [None], false. simpl. by rewrite pt_dual_shift. Qed.

Lemma pt_payload_root x i : pt_root (pt_payload x i) = pt_root x.
Proof. done. Qed.

Lemma pwalk_snoc x w s : pwalk x (w ++ [s]) = wstep (pwalk x w) s.
Proof. by rewrite pwalk_app. Qed.

Lemma wlt_walk x w v : pt_root x = NVar 0 → v ≠ [] → wlt (pwalk x w) (pwalk x (w ++ v)).
Proof. intros Hx Hv. split; [by rewrite pwalk_root|]. exists v, true. split; [done|by rewrite pwalk_app]. Qed.

(** A chain of steps that each hold climbs along a walk. *)
Lemma walk_chain (L : point → point → Prop) x :
  (∀ y z w, L y z → L z w → L y w) →
  (∀ u s, L (pwalk x u) (wstep (pwalk x u) s)) →
  ∀ v u, v ≠ [] → L (pwalk x u) (pwalk x (u ++ v)).
Proof.
  intros Ht Hs v. induction v as [|s v IH]; intros u Hv; [done|].
  destruct v as [|s' v].
  - rewrite pwalk_snoc. apply Hs.
  - replace (u ++ s :: s' :: v) with ((u ++ [s]) ++ s' :: v) by (by rewrite <-app_assoc).
    eapply Ht; [|apply IH; done]. rewrite pwalk_snoc. apply Hs.
Qed.

(** The order of a channel along its offsets. *)
Definition olt (x y : point) : Prop := pt_name x = pt_name y ∧ pt_off x < pt_off y.

Lemma olt_trans x y z : olt x y → olt y z → olt x z.
Proof. intros [??] [??]. split; [congruence|lia]. Qed.

Lemma olt_irrefl x : ¬ olt x x.
Proof. intros [_ ?]. lia. Qed.

Lemma olt_po x : olt x (pt_shift 1 x).
Proof. split; [done|simpl; lia]. Qed.

Lemma olt_dpo x : olt x (pt_shift 1 (pt_dual x)).
Proof. split; [done|simpl; lia]. Qed.

(** ** A ceiling and the lockstep pair

    The whole programs start under one top-level point variable z = 0
    with no fact. No channel occupies z, and the recursions use it as
    their ceiling. *)
Definition top_C0 : bcs := BCs [] (λ _, False).

Lemma top_acyclic : c0_acyclic 1 top_C0.
Proof. apply (c0_acyclic_rank 1 _ (vrank 1)); [apply vrank_shift|by intros ? ? []|apply vrank_dual]. Qed.

(** The first channel a of a lockstep pair, created under z = 1 with
    a+k ≺ z and ā+k ≺ z for every k. *)
Definition lsa_P (g : fact) : Prop := ∃ k c, g = FLt (pt_polar c (pv 0 k)) (pv 1 0).
Definition lsa_C : bcs := BCs [pvar 0] lsa_P.

Lemma lsa_ok peq plt : cc_ok peq plt lsa_C.
Proof.
  apply (cc_ok_out _ _ lsa_C olt); [exact olt_trans|exact olt_irrefl|intros x _; apply olt_po|intros x _; apply olt_dpo| |].
  - intros a b (f & (k & [|] & ->) & _ & E); injection E as -> ->; cbn; auto.
  - intros u p q v (f & (k & [|] & ->) & _ & E); injection E as -> ->; cbn; done.
Qed.

(** The second channel b, created under a = 1 and z = 2 with
    a+k ≺ b+k ≺ a+k+1 and b+k ≺ z for every k, between both ends:
    the facts hold for every choice of polarities. *)
Definition lsb_P (g : fact) : Prop :=
  ∃ k c c', g = FLt (pt_polar c (pv 1 k)) (pt_polar c' (pv 0 k)) ∨
            g = FLt (pt_polar c (pv 0 k)) (pt_polar c' (pv 1 (S k))) ∨ g = FLt (pt_polar c (pv 0 k)) (pv 2 0).
Definition lsb_C : bcs := BCs [pvar 0; pvar 1] lsb_P.

Lemma lsb_ok W Ψ : (BCs [pvar 1] lsa_P, [pvar 0]) ∈ Ψ → cc_ok (seqs W Ψ) (slt W Ψ) lsb_C.
Proof.
  intros Hg.
  apply (cc_ok_out _ _ lsb_C olt); [exact olt_trans|exact olt_irrefl|intros x _; apply olt_po|intros x _; apply olt_dpo| |].
  - intros a b (f & (k & [|] & [|] & [-> | [-> | ->]]) & _ & E); injection E as -> ->; cbn; auto.
  - intros u p q v (f & (k & c & c' & [-> | [-> | ->]]) & _ & E) (f' & (j & d & d' & [-> | [-> | ->]]) & _ & E')
      Hu Hp Hq Hv Hpq; injection E as -> ->; injection E' as -> ->;
      destruct c, c', d, d'; cbn in Hu, Hp, Hq, Hv |- *; try done;
      destruct Hpq as [Hpq|[_ Hpq]]; vm_compute in Hpq;
      try (match type of Hpq with _ = _ => inversion Hpq; subst end); cbn in *;
      first [apply glt_ofs_pol|apply (glt_ofs_dual _ _ _ true)|apply (glt_ofs_dual _ _ _ false)
            |apply (glt_up _ _ (pv 0 j) (pv 1 0));
             eapply (sl_hyp W Ψ [pvar 1] lsa_P [pvar 0] (FLt (pv 0 j) (pv 1 0))); [done|by exists j, true|fsc|reflexivity]
            |apply (glt_up _ _ (pt_dual (pv 0 j)) (pv 1 0));
             eapply (sl_hyp W Ψ [pvar 1] lsa_P [pvar 0] (FLt (pt_dual (pv 0 j)) (pv 1 0))); [done|by exists j, false|fsc|reflexivity]
            |apply (glt_up _ _ (pv 0 k) (pv 1 0));
             eapply (sl_hyp W Ψ [pvar 1] lsa_P [pvar 0] (FLt (pv 0 k) (pv 1 0))); [done|by exists k, true|fsc|reflexivity]
            |apply (glt_up _ _ (pt_dual (pv 0 k)) (pv 1 0));
             eapply (sl_hyp W Ψ [pvar 1] lsa_P [pvar 0] (FLt (pt_dual (pv 0 k)) (pv 1 0))); [done|by exists k, false|fsc|reflexivity]];
      unfold pt_shift in *; cbn in *; lia.
Qed.
