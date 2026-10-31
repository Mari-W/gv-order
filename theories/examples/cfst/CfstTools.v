(** * Tools for the examples of context-free session types (stage D)

    Hereditary contractiveness by induction on the depth, closure of it
    under ;, congruences of ≈ for the prefixes the examples rewrite
    under, a derived rule for case with Θ = ∅, and the facts of a
    hypothesis whose constraint has outer points. All lemmas are
    general. None of them changes a core definition. *)

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
    sok e 0 (Lam (Pair e1 e2)) 0 Δ = true →
    typed W Φ Ψ ∅ (lp e 0 Δ) (sf_union F (lenv_heads (lp (Lam (Pair e1 e2)) 0 Δ))) e (TSum T1 T2) →
    typed W Φ Ψ ∅ (Some T1 :: lp (Lam (Pair e1 e2)) 0 Δ) F e1 T →
    typed W Φ Ψ ∅ (Some T2 :: lp (Lam (Pair e1 e2)) 0 Δ) F e2 T →
    typed W Φ Ψ ∅ Δ F (Case e e1 e2) T.
  Proof.
    intros Hs H H1 H2. eapply (t_case W Φ Ψ ∅ ∅ ∅); [apply (comp0 W HW)|by apply lp_split| |exact H1|exact H2].
    by rewrite (tenv_heads0 W), union_empty_l_L.
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

(** ** The lockstep world

    Two channels a = 0 and b = 1 that alternate, (a,k) ≺ (b,k) ≺
    (a,k+1), and a ceiling z = 2 above both: (a,k), (b,k) ≺ (z,0).
    TreeCopy.v and Stream.v run in it. *)

Definition tree_L (x y : point) : Prop :=
  ∃ k, (x = pc 0 k ∧ y = pc 1 k) ∨ (x = pc 1 k ∧ y = pc 0 (S k)) ∨
       (x = pc 0 k ∧ y = pc 2 0) ∨ (x = pc 1 k ∧ y = pc 2 0).

Definition Wtree : world := wgen (list_to_set (NConst <$> [0; 1; 2])) (λ _ _, False) tree_L.

(** The ranks (0, 2k) for (a,k), (0, 2k+1) for (b,k) and (1, k) for (z,k). *)
Definition tree_rank (x : point) : nat * nat :=
  match pt_root x with
  | NConst 2 => (1, pt_off x)
  | NConst 1 => (0, 2 * pt_off x + 1)
  | _ => (0, 2 * pt_off x)
  end.

Lemma Wtree_strict : strict Wtree.
Proof.
  apply (wgen_strict_lex _ _ _ id tree_rank); try done.
  - intros p Hp. apply elem_of_list_to_set, list_elem_of_fmap in Hp as (a & -> & _). by exists a.
  - intros x y (k & [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]); right; rewrite !elem_of_list_to_set; cbn; set_solver.
  - intros x. unfold lexlt, tree_rank, pt_shift, pt_root. cbn.
    destruct (pn_root (pt_name x)) as [[|[|[|a]]]| |]; cbn; right; split; try done; lia.
  - intros x y (k & [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]); unfold lexlt, tree_rank, id; cbn; lia.
Qed.

(** Frame variable lookups after E-Open. *)
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
