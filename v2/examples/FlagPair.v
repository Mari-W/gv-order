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
    ȳ ≺ x. No ranked world holds both, and P-Connect composes the two
    threads at one ranked world.

    - [fp_gate]           : a thread in E at close a; close b with b held
                            asks the point of a below the partner point of b.
    - [fp_unrealizable]   : A and B in E at one ranked world W for both
                            flags contradict the irreflexivity of W.
    - [fp_static_rejected]: the closed process of A, B and a thread that
                            sends them the flag has no typing at any
                            bound, annotation or world.
    - [ptyped_threads]    : every thread of a process derivation is typed
                            at a world below the world of the derivation,
                            with the two ends of a channel at dual points.

    The theorem plays the part [db_component_unrealizable] played for the
    dispatcher of theories/examples/DataBranch.v, at the end points of
    the redesign. One thread alone is not outside the relation, its two
    arms ask x ≺ ȳ and y ≺ x̄, which one ranked world can hold. *)

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
  a ≠ b → Erel κ n W (fp_env a b x y) TUnit ∅ (cl2 a b) → W ⊢ x ≺ y‾.
Proof.
  intros Hab HE.
  assert (¬ irred (cl2 a b)) as Hnr by (intros Hi; exact (Hi _ _ (fp_cl2_close a b))).
  pose proof (Erel_ready κ n W _ TUnit ∅ _ HE Hnr) as Hr.
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
  Erel κ (oadd n (c_beta κ)) W (fp_env a b x y) TUnit ∅ (fp_case a b (Inj i EUnit)) →
  Erel κ n W (fp_env a b x y) TUnit ∅ (if i then cl2 b a else cl2 a b).
Proof.
  intros HE. unfold fp_case in HE.
  assert (tstep (Case (Inj i EUnit) (cl2 a b) (cl2 b a)) LBeta (if i then cl2 b a else cl2 a b)) as Hs.
  { destruct i; apply tstep_head; constructor; done. }
  pose proof (Erel_step κ _ W W _ TUnit ∅ _ _ _ HE (wext_refl W) Hs) as H. cbn [Eobl] in H.
  unfold o_beta, at_cost_E in H.
  destruct (decide (c_beta κ = 0)) as [H0|H0].
  - rewrite H0 in H. exact (proj1 H eq_refl).
  - exact (proj2 H H0 n (ole_refl _)).
Qed.

(** ** No ranked world takes both threads *)

Definition fp_a : cend := EPos "a".
Definition fp_b : cend := EPos "b".

Theorem fp_unrealizable κ n W x y :
  (∀ i, Erel κ (oadd n (c_beta κ)) W (fp_env fp_a fp_b x y) TUnit ∅ (fp_case fp_a fp_b (Inj i EUnit))) →
  (∀ i, Erel κ (oadd n (c_beta κ)) W (fp_env (edual fp_a) (edual fp_b) (x‾) (y‾)) TUnit ∅
           (fp_case (edual fp_a) (edual fp_b) (Inj i EUnit))) →
  False.
Proof.
  intros HA HB.
  pose proof (fp_case_E _ _ _ _ _ _ _ false (HA false)) as HA'. cbn iota in HA'.
  pose proof (fp_case_E _ _ _ _ _ _ _ true (HB true)) as HB'. cbn iota in HB'.
  assert (fp_env (edual fp_a) (edual fp_b) (x‾) (y‾) = fp_env (edual fp_b) (edual fp_a) (y‾) (x‾)) as E.
  { unfold fp_env. apply map_union_comm. apply map_disjoint_singleton_l, lookup_singleton_ne. done. }
  rewrite E in HB'.
  pose proof (fp_gate _ _ _ fp_a fp_b _ _ ltac:(done) HA') as G1.
  pose proof (fp_gate _ _ _ (edual fp_b) (edual fp_a) _ _ ltac:(done) HB') as G2.
  rewrite pt_dual_dual in G2.
  apply (w_lt_irrefl W x). eapply w_lt_trans; [exact G1|exact G2].
Qed.

(** ** The static rejection

    The typed form of the program binds the flag. Thread A receives z on
    its end f, closes the continuation, and branches on z. Each arm reads
    its binder before it closes, as in [sbv_thread], because a payload of
    type ∗ is linear in Δ. Thread B does the same on g with the dual
    ends, and a third thread sends inj₁ ∗ on both f̄ and ḡ.

      fpv_case a b z = case z of inl w ⇒ let ∗ = w in close a; close b
                               | inr w ⇒ let ∗ = w in close b; close a
      fpv_thread f a b = let ⟨z, f′⟩ = recv f in let ∗ = close f′ in fpv_case a b z

    E-Case types both arms under one context and one world, so A asks
    x ≺ ȳ and y ≺ x̄ ([fpv_case_needs]) and B asks x̄ ≺ y and ȳ ≺ x. The
    world of every thread lies below the world of the whole derivation,
    and the points of the two ends of a channel are dual there
    ([ptyped_threads]). So the world of any derivation of the process
    holds x ≺ ȳ ≺ x, against the well-foundedness that P-Term and
    P-Connect ask ([fp_static_rejected]). *)

From GV Require Import static.Inversion cost.Exact.

Definition fpv_case (a b : cend) (z : expr) : expr :=
  Case z (LetU (Var 0) (cl2 a b)) (LetU (Var 0) (cl2 b a)).

Definition fpv_thread (f a b : cend) : expr :=
  LetP (ERecv (Chan f)) (LetU (EClose (Var 0)) (fpv_case a b (Var 1))).

Definition fp_sender : expr :=
  LetU (EClose (ESend (Pair (Inj false EUnit) (Chan (ENeg "f")))))
       (EClose (ESend (Pair (Inj false EUnit) (Chan (ENeg "g"))))).

Definition fp_A : expr := fpv_thread (EPos "f") (EPos "a") (EPos "b").
Definition fp_B : expr := fpv_thread (EPos "g") (ENeg "a") (ENeg "b").

Definition fp_config : proc :=
  (({["a"]} ∪ {["b"]} ∪ {["f"]} ∪ {["g"]}), {[+ fp_A +]} ⊎ {[+ fp_B +]} ⊎ {[+ fp_sender +]}).

(** Both arms of the case: a ≺ b̄ and b ≺ ā, for a scrutinee that holds
    no end. *)
Lemma fpv_case_needs W N Θ Γ Δ F a b z T c ea eb :
  a ≠ b → fends z = ∅ → typed W N Θ Γ Δ F (fpv_case a b z) T c →
  Θ !! a = Some ea → Θ !! b = Some eb → facts_const W →
  slt W Γ (te_pt ea) (te_pt eb)‾ ∧ slt W Γ (te_pt eb) (te_pt ea)‾.
Proof.
  intros Hab Hz H Ha Hb Hfc. unfold fpv_case in H.
  apply inv_case in H as (Θ' & Γ' & Δ' & F' & Θ1 & Θ2 & Θ2' & Δ1 & Δ2 & Δ2' & T1 & T2 & T' & c0 & c1 & c2
    & Ho & Hs & _ & H0 & Hage & _ & H1 & H2).
  destruct (opened_cons _ _ _ _ _ _ _ _ _ Hfc Ho) as (σ & Hσl & _ & Hσs).
  pose proof (typed_tfacts _ _ _ _ _ _ _ _ _ H0) as [Hd0 _]. rewrite Hz in Hd0.
  assert (∀ o, o ∉ dom Θ1) as Hn1 by (intros o; rewrite <-Hd0; set_solver).
  destruct (thage_pt _ _ _ _ _ Hage (tsplit_lookup_r _ _ _ _ _ Hs (Hn1 a) (Hσl _ _ Ha)))
    as (ea' & Ha' & Hpa).
  destruct (thage_pt _ _ _ _ _ Hage (tsplit_lookup_r _ _ _ _ _ Hs (Hn1 b) (Hσl _ _ Hb)))
    as (eb' & Hb' & Hpb).
  pose proof (letu_cl2_needs _ _ _ _ _ _ _ _ _ _ _ _ Hab H1 Ha' Hb' Hfc) as G1.
  pose proof (letu_cl2_needs _ _ _ _ _ _ _ _ _ _ _ _ (not_eq_sym Hab) H2 Hb' Ha' Hfc) as G2.
  rewrite Hpa, Hpb, !te_pt_pinst, <-pt_inst_dual in G1, G2. split; by apply Hσs.
Qed.

(** The same through the receive and the close of the continuation. *)
Lemma fpv_thread_needs W N Θ Γ Δ F f a b T c ea eb :
  a ≠ b → f ≠ a → f ≠ b → typed W N Θ Γ Δ F (fpv_thread f a b) T c →
  Θ !! a = Some ea → Θ !! b = Some eb → facts_const W →
  slt W Γ (te_pt ea) (te_pt eb)‾ ∧ slt W Γ (te_pt eb) (te_pt ea)‾.
Proof.
  intros Hab Hfa Hfb H Ha Hb Hfc. unfold fpv_thread in H.
  apply inv_letp in H as (Θ' & Γ' & Δ' & F' & Θ1 & Θ2 & Θ2' & Δ1 & Δ2 & Δ2' & T1 & T2 & T' & c1 & c2
    & Ho & Hs & _ & H1 & Hage & _ & H2).
  destruct (opened_cons _ _ _ _ _ _ _ _ _ Hfc Ho) as (σ & Hσl & _ & Hσs).
  pose proof (typed_tfacts _ _ _ _ _ _ _ _ _ H1) as [Hd1 _]. simpl in Hd1.
  assert ((a ∉ dom Θ1) ∧ (b ∉ dom Θ1)) as [Hn1 Hn2] by (rewrite <-Hd1; set_solver).
  destruct (thage_pt _ _ _ _ _ Hage (tsplit_lookup_r _ _ _ _ _ Hs Hn1 (Hσl _ _ Ha)))
    as (ea' & Ha' & Hpa).
  destruct (thage_pt _ _ _ _ _ Hage (tsplit_lookup_r _ _ _ _ _ Hs Hn2 (Hσl _ _ Hb)))
    as (eb' & Hb' & Hpb).
  clear Ho Hs H1 Hage Hd1 Hn1 Hn2.
  apply inv_letu in H2 as (Θ'' & Γ'' & Δ'' & F'' & Θ3 & Θ4 & Θ4' & Δ3 & Δ4 & Δ4' & T'' & c3 & c4
    & Ho & Hs & _ & H3 & Hage & _ & H4).
  destruct (opened_cons _ _ _ _ _ _ _ _ _ Hfc Ho) as (τ & Hτl & _ & Hτs).
  pose proof (typed_tfacts _ _ _ _ _ _ _ _ _ H3) as [Hd3 _]. simpl in Hd3.
  assert (∀ o, o ∉ dom Θ3) as Hn3 by (intros o; rewrite <-Hd3; set_solver).
  destruct (thage_pt _ _ _ _ _ Hage (tsplit_lookup_r _ _ _ _ _ Hs (Hn3 a) (Hτl _ _ Ha')))
    as (ea'' & Ha'' & Hpa').
  destruct (thage_pt _ _ _ _ _ Hage (tsplit_lookup_r _ _ _ _ _ Hs (Hn3 b) (Hτl _ _ Hb')))
    as (eb'' & Hb'' & Hpb').
  destruct (fpv_case_needs _ _ _ _ _ _ _ _ (Var 1) _ _ _ _ Hab eq_refl H4 Ha'' Hb'' Hfc) as [G1 G2].
  rewrite Hpa', Hpb', !te_pt_pinst, <-pt_inst_dual in G1, G2.
  apply Hτs in G1, G2. rewrite Hpa, Hpb, !te_pt_pinst, <-pt_inst_dual in G1, G2.
  split; by apply Hσs.
Qed.

(** *** The threads of a derivation

    A point of every end, given by a point [f c] of the positive end of
    each channel c, the negative end at its dual. Every thread of a
    derivation is typed at a world below the world of the derivation,
    with its ends at these points, and the interface agrees with them. *)

Definition pof (f : chan → point) (o : cend) : point :=
  match o with EPos c => f c | ENeg c => (f c)‾ end.

Lemma pof_dual f o : pof f (edual o) = (pof f o)‾.
Proof. destruct o; simpl; [done|by rewrite pt_dual_dual]. Qed.

Lemma pof_ext f g o : f (ech o) = g (ech o) → pof f o = pof g o.
Proof. destruct o; simpl; by intros ->. Qed.

Lemma pof_agree f g o : pof f o = pof g o → f (ech o) = g (ech o).
Proof.
  destruct o; simpl; [done|]. intros E. by rewrite <-(pt_dual_dual (f c)), E, pt_dual_dual.
Qed.

Definition pt0 : point := MkPt (NConst 0) true 0.

Lemma ptyped_threads N η W Σ p T :
  ptyped N η W Σ p T →
  ∃ f, (∀ o S x, Σ !! o = Some (S, x) → pof f o = x) ∧
    ∀ t, t ∈ p.2 → ∃ W' Θ T' c, W' ⊑ₛ W ∧ sworld_wf W' ∧
      typed W' N Θ hc_empty [] (∅, None) t T' c ∧
      ∀ o e, Θ !! o = Some e → ech o ∈ p.1 ∪ chans_of Σ ∧ te_pt e = pof f o.
Proof.
  induction 1 as [W Σ ΘB C0 t T c _ HB HC Hpf _ HBs _ Ht [Hw _]|
    W1 W2 Σ1 Σ2 ΣC C1 C2 E1 E2 T H1 (f1 & HΣ1 & Ht1) H2 (f2 & HΣ2 & Ht2) D12 D1C D2C DC12 DC1 DC2 _ _].
  - set (f := λ c, match Σ !! EPos c with
                  | Some (_, x) => x
                  | None => match Σ !! ENeg c with
                            | Some (_, x) => x‾
                            | None => match ΘB !! EPos c with Some e => te_pt e | None => pt0 end
                            end
                  end).
    assert (HΣ : ∀ o S x, Σ !! o = Some (S, x) → pof f o = x).
    { intros [c'|c'] S x Ho; simpl; unfold f.
      - by rewrite Ho.
      - assert (Σ !! EPos c' = None) as ->.
        { apply not_elem_of_dom. intros Hc. apply (Hpf (EPos c')); [done|]. simpl. by apply elem_of_dom. }
        by rewrite Ho, pt_dual_dual. }
    exists f. split; [exact HΣ|]. intros t' Ht'. simpl in Ht'. apply gmultiset_elem_of_singleton in Ht' as ->.
    exists W, (tenv_ofk η Σ ∪ ΘB), T, c. split_and!; [apply swext_refl|done|done|].
    intros o e He. apply lookup_union_Some_raw in He as [He|[Hn He]].
    + rewrite lookup_tenv_ofk in He. destruct (Σ !! o) as [[S x]|] eqn:Ho; [|done].
      injection He as <-. simpl. split; [apply elem_of_union_r, elem_of_chans_of'; by apply elem_of_dom|].
      symmetry. by apply (HΣ o S).
    + assert (ech o ∈ C0) as Hc by (apply HB; by apply elem_of_dom).
      split; [simpl; set_solver|].
      rewrite lookup_tenv_ofk in Hn. destruct (Σ !! o) eqn:Ho; [done|].
      assert (∀ o', ech o' = ech o → Σ !! o' = None) as Hno.
      { intros o' E. apply not_elem_of_dom. intros Hd. apply (HC (ech o)); [|done].
        rewrite <-E. by apply elem_of_chans_of'. }
      destruct (HBs _ Hc) as (S & x & m & m' & _ & _ & Hp & Hm).
      destruct o as [c'|c']; simpl in *; unfold f;
        rewrite (Hno (EPos c') eq_refl), (Hno (ENeg c') eq_refl), Hp.
      * rewrite Hp in He. by injection He as <-.
      * rewrite Hm in He. by injection He as <-.
  - set (L := C1 ∪ chans_of (Σ1 ∪ ΣC)).
    set (f := λ c, if decide (c ∈ L) then f1 c else f2 c).
    assert (Hf1 : ∀ o, ech o ∈ L → pof f o = pof f1 o).
    { intros o Ho. apply pof_ext. unfold f. by rewrite decide_True. }
    assert (Hf2 : ∀ o, ech o ∉ L → pof f o = pof f2 o).
    { intros o Ho. apply pof_ext. unfold f. by rewrite decide_False. }
    assert (Hcut : ∀ o, o ∈ dom ΣC → pof f1 o = pof f2 o).
    { intros o Ho. apply elem_of_dom in Ho as [[S x] Ho].
      rewrite (HΣ1 o S x) by (apply lookup_union_Some_r; [by apply chans_disj_map|done]).
      assert ((Σ2 ∪ senv_dual ΣC) !! edual o = Some (dual S, x‾)) as Hd.
      { apply lookup_union_Some_r; [by apply chans_disj_map_dual|by apply sdual_lookup]. }
      apply HΣ2 in Hd. rewrite pof_dual in Hd. by rewrite <-(pt_dual_dual (pof f2 o)), Hd, pt_dual_dual. }
    exists f. split.
    + intros o S x Ho. apply lookup_union_Some in Ho as [Ho|Ho]; [| |by apply chans_disj_map].
      * rewrite Hf1; [apply (HΣ1 o S); by apply lookup_union_Some_l|].
        unfold L. rewrite chans_of_union. apply elem_of_union_r, elem_of_union_l, elem_of_chans_of'.
        by apply elem_of_dom.
      * assert (ech o ∈ chans_of Σ2) as Hc by (apply elem_of_chans_of'; by apply elem_of_dom).
        rewrite Hf2; [apply (HΣ2 o S); by apply lookup_union_Some_l|].
        unfold L. rewrite chans_of_union. set_solver.
    + intros t Ht. simpl in Ht. apply gmultiset_elem_of_disj_union in Ht as [Ht|Ht].
      * destruct (Ht1 t Ht) as (W' & Θ & T' & c & Hle & Hw & Hty & Hpt).
        exists W', Θ, T', c. split_and!; [eapply swext_trans; [exact Hle|apply swext_join_l]|done|done|].
        intros o e He. destruct (Hpt o e He) as [Hc Hp]. simpl in Hc.
        rewrite chans_of_union in Hc.
        rewrite Hf1 by (unfold L; rewrite chans_of_union; set_solver). split; [|done].
        rewrite !chans_of_union. simpl. set_solver.
      * destruct (Ht2 t Ht) as (W' & Θ & T' & c & Hle & Hw & Hty & Hpt).
        exists W', Θ, T', c. split_and!; [eapply swext_trans; [exact Hle|apply swext_join_r]|done|done|].
        intros o e He. destruct (Hpt o e He) as [Hc Hp]. simpl in Hc.
        rewrite chans_of_union, chans_of_senv_dual in Hc.
        split; [rewrite !chans_of_union; simpl; set_solver|].
        destruct (decide (ech o ∈ chans_of ΣC)) as [HcC|HcC].
        -- rewrite Hf1 by (unfold L; rewrite chans_of_union; set_solver).
           unfold chans_of in HcC. apply elem_of_map in HcC as (o' & Eo & Ho').
           pose proof (pof_agree _ _ _ (Hcut o' Ho')) as E. rewrite <-Eo in E.
           rewrite Hp. symmetry. by apply pof_ext.
        -- rewrite Hf2; [done|]. unfold L. rewrite chans_of_union. set_solver.
Qed.

(** No bound, annotation or world types the process. *)
Theorem fp_static_rejected N η W : ¬ ptyped N η W ∅ fp_config TUnit.
Proof.
  intros H. pose proof (wok_acyc N _ (proj2 (ptyped_wf _ _ _ _ _ _ H))) as Hirr.
  destruct (ptyped_threads _ _ _ _ _ _ H) as (f & _ & Hth).
  destruct (Hth fp_A) as (WA & ΘA & TA & cA & HleA & HwA & HA & HptA); [unfold fp_config; cbn [snd]; multiset_solver|].
  destruct (Hth fp_B) as (WB & ΘB & TB & cB & HleB & HwB & HB & HptB); [unfold fp_config; cbn [snd]; multiset_solver|].
  pose proof (typed_tfacts _ _ _ _ _ _ _ _ _ HA) as [HdA _].
  pose proof (typed_tfacts _ _ _ _ _ _ _ _ _ HB) as [HdB _].
  assert (∀ o, o ∈ fends fp_A → ∃ e, ΘA !! o = Some e) as LA
    by (intros o Ho; apply elem_of_dom; by rewrite <-HdA).
  assert (∀ o, o ∈ fends fp_B → ∃ e, ΘB !! o = Some e) as LB
    by (intros o Ho; apply elem_of_dom; by rewrite <-HdB).
  destruct (LA (EPos "a")) as [ea Ha]; [unfold fp_A, fpv_thread, fpv_case, cl2; simpl; set_solver|].
  destruct (LA (EPos "b")) as [eb Hb]; [unfold fp_A, fpv_thread, fpv_case, cl2; simpl; set_solver|].
  destruct (LB (ENeg "a")) as [ea' Ha']; [unfold fp_B, fpv_thread, fpv_case, cl2; simpl; set_solver|].
  destruct (LB (ENeg "b")) as [eb' Hb']; [unfold fp_B, fpv_thread, fpv_case, cl2; simpl; set_solver|].
  destruct (fpv_thread_needs _ _ _ _ _ _ (EPos "f") (EPos "a") (EPos "b") _ _ _ _
    ltac:(done) ltac:(done) ltac:(done) HA Ha Hb (facts_const_wf _ HwA)) as [GA _].
  destruct (fpv_thread_needs _ _ _ _ _ _ (EPos "g") (ENeg "a") (ENeg "b") _ _ _ _
    ltac:(done) ltac:(done) ltac:(done) HB Ha' Hb' (facts_const_wf _ HwB)) as [_ GB].
  apply slt_empty_w in GA, GB.
  rewrite (proj2 (HptA _ _ Ha)), (proj2 (HptA _ _ Hb)) in GA.
  rewrite (proj2 (HptB _ _ Ha')), (proj2 (HptB _ _ Hb')) in GB.
  change (ENeg "a") with (edual (EPos "a")) in GB. change (ENeg "b") with (edual (EPos "b")) in GB.
  rewrite !pof_dual, pt_dual_dual in GB.
  apply (Hirr (pof f (EPos "a"))). eapply sw_lt_trans.
  - eapply sw_lt_mono; [exact HleA|exact GA].
  - eapply sw_lt_mono; [exact HleB|exact GB].
Qed.

Print Assumptions fp_static_rejected.
