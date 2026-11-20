(** * Two threads that branch on one flag are outside the relation in every world

      fp_case a b z = case z of inl _ ⇒ close a; close b
                              | inr _ ⇒ close b; close a

    Thread A runs [fp_case a b] on its ends a at x and b at y, thread B
    runs [fp_case ā b̄] on the partner ends ā at x̄ and b̄ at ȳ. Both
    branch on a flag that a third party sends them, the same flag to
    both, so in every run they close in the same order and the process
    is deadlock free. Only internal channels are involved, so the process
    relation P asks nothing more than deadlock freedom of it.

    The route through E rejects it. A flag received from the environment
    is any value of V at ∗ ⊕ ∗, so each thread must be in E for both
    flags. A with the flag inl closes a while it holds b and asks
    x ≺ ȳ. B with the flag inr closes b̄ while it holds ā and asks
    ȳ ≺ x. No strict world holds both, and P-Connect composes the two
    threads only over worlds whose join is strict.

    - [fp_gate]           : a thread in E at close a; close b with b held
                            asks the point of a below the partner point of b.
    - [fp_unrealizable]   : A in E at W1 for both flags and B in E at W2
                            for both flags contradict strict (W1 ⊔ W2).

    The theorem plays the part [db_component_unrealizable] played for the
    dispatcher of theories/examples/DataBranch.v, at the end points of
    the redesign. One thread alone is not outside the relation, its two
    arms ask x ≺ ȳ and y ≺ x̄, which one strict world can hold. *)

From GV Require Export examples.SemBranch.

(** ** The program *)

Definition fp_case (a b : cend) (z : expr) : expr := Case z (cl2 a b) (cl2 b a).

Definition fp_env (a b : cend) (x y : point) : senv := {[a := (SEnd, x)]} ∪ {[b := (SEnd, y)]}.

(** ** Steps *)

Lemma fp_close_step o α e' : tstep (EClose (Chan o)) α e' → α = LSess (SClose o) ∧ e' = EUnit.
Proof. intros Hs. apply op_head_only in Hs; [|done]. by inversion Hs. Qed.

Lemma fp_cl2_step a b α e' :
  tstep (cl2 a b) α e' → α = LSess (SClose a) ∧ e' = LetU EUnit (EClose (Chan b)).
Proof.
  intros Hs. unfold cl2 in Hs.
  change (LetU (EClose (Chan a)) (EClose (Chan b))) with
    (fill_frame (FLetU (EClose (Chan b))) (EClose (Chan a))) in Hs.
  destruct (tstep_fill_inv (FLetU (EClose (Chan b))) (EClose (Chan a)) _ _ I ltac:(intros []) Hs) as (e0 & Hs0 & ->).
  destruct (fp_close_step _ _ _ Hs0) as [-> ->]. done.
Qed.

Lemma fp_cl2_close a b : tstep (cl2 a b) (LSess (SClose a)) (LetU EUnit (EClose (Chan b))).
Proof.
  unfold cl2.
  change (LetU (EClose (Chan a)) (EClose (Chan b))) with
    (fill_frame (FLetU (EClose (Chan b))) (EClose (Chan a))).
  apply (tstep_fill (FLetU _)); [done|apply tstep_head, t_act_close].
Qed.

(** ** The gate of close a; close b *)

Lemma fp_gate κ n W a b x y :
  a ≠ b → Erel κ (S n) W (fp_env a b x y) TUnit ∅ (cl2 a b) → W ⊢ x ≺ y‾.
Proof.
  intros Hab HE.
  assert (¬ irred (cl2 a b)) as Hnr by (intros Hi; exact (Hi _ _ (fp_cl2_close a b))).
  pose proof (Erel_S_ready κ n W _ TUnit ∅ _ HE Hnr) as Hr.
  assert (stable_t (cl2 a b)) as Hst.
  { intros α e' Hs. destruct (fp_cl2_step _ _ _ _ Hs) as [-> _]. by eexists. }
  destruct (Hr Hst) as [_ [Hl|Hb]].
  { destruct Hl as (os & t' & Hs). destruct (fp_cl2_step _ _ _ _ Hs) as [Heq _]. discriminate. }
  assert (offered_t (fp_env a b x y) (cl2 a b) a) as Ha.
  { split; [unfold fp_env; rewrite dom_union_L, !dom_singleton_L; set_solver|].
    exists (SClose a), (LetU EUnit (EClose (Chan b))). split; [apply fp_cl2_close|simpl; set_solver]. }
  assert (¬ offered_t (fp_env a b x y) (cl2 a b) b) as Hnb.
  { intros (_ & σ & t' & Hs & Hin). destruct (fp_cl2_step _ _ _ _ Hs) as [Heq _].
    injection Heq as ->. simpl in Hin. set_solver. }
  assert (fp_env a b x y !! a = Some (SEnd, x)) as La.
  { unfold fp_env. apply lookup_union_Some_l, lookup_singleton_eq. }
  assert (fp_env a b x y !! b = Some (SEnd, y)) as Lb.
  { unfold fp_env. rewrite lookup_union_r by (by rewrite lookup_singleton_ne).
    apply lookup_singleton_eq. }
  destruct (Hb a SEnd x Ha La) as [H _]. exact (H b SEnd y Lb Hnb).
Qed.

(** ** One case step *)

Lemma fp_case_E κ n W a b x y (i : bool) :
  Erel κ (S (c_beta κ + n)) W (fp_env a b x y) TUnit ∅ (fp_case a b (Inj i EUnit)) →
  Erel κ (S n) W (fp_env a b x y) TUnit ∅ (if i then cl2 b a else cl2 a b).
Proof.
  intros HE. unfold fp_case in HE.
  assert (tstep (Case (Inj i EUnit) (cl2 a b) (cl2 b a)) LBeta (if i then cl2 b a else cl2 a b)) as Hs.
  { destruct i; apply tstep_head; constructor; done. }
  pose proof (Erel_S_step κ _ W W _ TUnit ∅ _ _ _ HE (wext_refl W) Hs) as H. cbn [Eobl] in H.
  unfold o_beta, at_cost_E in H.
  destruct (decide (c_beta κ = 0)) as [H0|H0].
  - rewrite H0 in H. exact (proj1 H eq_refl).
  - replace (S (c_beta κ + n) - c_beta κ) with (S n) in H by lia. exact (proj2 H H0).
Qed.

(** ** No strict world takes both threads *)

Definition fp_a : cend := EPos "a".
Definition fp_b : cend := EPos "b".

Theorem fp_unrealizable κ n W1 W2 x y :
  strict (W1 ⊔ W2) →
  (∀ i, Erel κ (S (c_beta κ + n)) W1 (fp_env fp_a fp_b x y) TUnit ∅ (fp_case fp_a fp_b (Inj i EUnit))) →
  (∀ i, Erel κ (S (c_beta κ + n)) W2 (fp_env (edual fp_a) (edual fp_b) (x‾) (y‾)) TUnit ∅
           (fp_case (edual fp_a) (edual fp_b) (Inj i EUnit))) →
  False.
Proof.
  intros [_ HS] HA HB.
  pose proof (fp_case_E _ _ _ _ _ _ _ false (HA false)) as HA'. cbn iota in HA'.
  pose proof (fp_case_E _ _ _ _ _ _ _ true (HB true)) as HB'. cbn iota in HB'.
  assert (fp_env (edual fp_a) (edual fp_b) (x‾) (y‾) = fp_env (edual fp_b) (edual fp_a) (y‾) (x‾)) as E.
  { unfold fp_env. apply map_union_comm. apply map_disjoint_singleton_l, lookup_singleton_ne. done. }
  rewrite E in HB'.
  pose proof (fp_gate _ _ _ fp_a fp_b _ _ ltac:(done) HA') as G1.
  pose proof (fp_gate _ _ _ (edual fp_b) (edual fp_a) _ _ ltac:(done) HB') as G2.
  rewrite pt_dual_dual in G2.
  apply (HS x). eapply w_lt_trans.
  - eapply w_lt_mono; [apply wext_join_l|exact G1].
  - eapply w_lt_mono; [apply wext_join_r|exact G2].
Qed.
