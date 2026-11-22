(** * Milner's ring and the n-ary P-Connect

    Three components, each one thread that closes two ends in order,

      A = cl c⁻; cl a⁺     B = cl a⁻; cl b⁺     C = cl b⁻; cl c⁺,

    with a at the constant 0, b at 1 and c at 2. A thread that closes x
    before y asks x ≺ ȳ, so the thread worlds hold c̄ ≺ ā, ā ≺ b̄ and
    b̄ ≺ c̄. Each pair of hidden thread worlds is well-founded together
    ([ring_pairs]), the three together hold the cycle c̄ ≺ ā ≺ b̄ ≺ c̄
    ([ring_cyclic]). The components and cuts of the ring meet every
    condition of the n-ary rule but its world check ([ring_comps]). The
    ring deadlocks, so no world types it ([ring_rejected]).

    The acyclic variant C' = cl c⁺; cl b⁻ asks c ≺ b instead of b̄ ≺ c̄.
    The join of the three hidden worlds is well-founded, the n-ary rule
    types the ring ([ring_typed]), and it is deadlock free ([ring_df]). *)

From GV Require Import soup.LFConnectN examples.SharedRoots.

(** ** Points, threads and worlds *)

Definition pa : point := MkPt (NConst 0) true 0.
Definition pb : point := MkPt (NConst 1) true 0.
Definition pc : point := MkPt (NConst 2) true 0.

Definition tA : expr := cl2 (ENeg "c") (EPos "a").
Definition tB : expr := cl2 (ENeg "a") (EPos "b").
Definition tC : expr := cl2 (ENeg "b") (EPos "c").
Definition tC' : expr := cl2 (EPos "c") (ENeg "b").

Definition ΣA : senv := senv2 (ENeg "c") (EPos "a") pc‾ pa.
Definition ΣB : senv := senv2 (ENeg "a") (EPos "b") pa‾ pb.
Definition ΣCc : senv := senv2 (ENeg "b") (EPos "c") pb‾ pc.
Definition ΣC' : senv := senv2 (EPos "c") (ENeg "b") pc pb‾.

Definition WA : sworld := SWorld ({[0]} ∪ {[2]}) (λ g, g = FLt pc‾ pa‾).
Definition WB : sworld := SWorld ({[0]} ∪ {[1]}) (λ g, g = FLt pa‾ pb‾).
Definition WC : sworld := SWorld ({[1]} ∪ {[2]}) (λ g, g = FLt pb‾ pc‾).
Definition WC' : sworld := SWorld ({[1]} ∪ {[2]}) (λ g, g = FLt pc pb).

Definition HA : sworld := swrestrict WA (iface ΣA TUnit).
Definition HB : sworld := swrestrict WB (iface ΣB TUnit).
Definition HC : sworld := swrestrict WC (iface ΣCc TUnit).
Definition HC' : sworld := swrestrict WC' (iface ΣC' TUnit).

(** The closed ring with third thread t. *)
Definition ring_cfg (t : expr) : proc := ({["a"]} ∪ {["c"]} ∪ {["b"]}, {[+ tA +]} ⊎ {[+ tB +]} ⊎ {[+ t +]}).

(** ** Well-foundedness by a rank on points *)

Fixpoint rk (l : list (point * nat)) (x : point) : nat :=
  match l with [] => 0 | (y, n) :: l => if decide (x = y) then n else rk l x end.

Lemma rk_lt l x : Forall (λ pr, pr.2 < 3) l → rk l x < 3.
Proof.
  induction 1 as [|[y n] l Hn _ IH]; simpl; [lia|]. by case_decide.
Qed.

Lemma swf_rk W l : Forall (λ pr, pr.2 < 3) l →
  (∀ x y, sw_facts W (FLt x y) → pt_off x = pt_off y ∧ rk l x < rk l y) → swf W.
Proof.
  intros Hl Hf. set (m x := 3 * pt_off x + rk l x). apply swf_iff.
  assert (∀ x y, swstep W x y → m x < m y) as Hs.
  { intros x y [x' y' H|x'|x'].
    - destruct (Hf _ _ H) as [E Hr]. unfold m. lia.
    - assert (pt_off x' < pt_off x'⁺) by (apply po_root, tc_once; by left).
      pose proof (rk_lt l x' Hl). unfold m. lia.
    - assert (pt_off x' < pt_off x'‾⁺) by (apply po_root, tc_once; by right).
      pose proof (rk_lt l x' Hl). unfold m. lia. }
  assert (∀ x y, W ⊢ₛ x ≺ y → m x < m y) as Hm.
  { intros x y H. induction H as [x y H|x y z H _ IH]; [by apply Hs|]. specialize (Hs _ _ H). lia. }
  apply (wf_sub (ltof point m)); [exact Hm|]. apply well_founded_ltof.
Qed.

Ltac rk_tac := split; [reflexivity|vm_compute; lia].
Ltac rk_ok := repeat constructor; simpl; lia.

Lemma sw_lt_steps W W' x y : (∀ x y, sw_facts W (FLt x y) → W' ⊢ₛ x ≺ y) → W ⊢ₛ x ≺ y → W' ⊢ₛ x ≺ y.
Proof.
  intros Hf. assert (∀ x y, swstep W x y → W' ⊢ₛ x ≺ y) as Hs.
  { intros a b [a' b' H|a'|a']; [by apply Hf|apply sw_lt_po|apply sw_lt_dpo]. }
  induction 1 as [x y H|x y z H _ IH]; [by apply Hs|]. eapply sw_lt_trans; [by apply Hs|done].
Qed.

Ltac W_ok := split; intros u v E; injection E as -> ->; split; eexists; (split; [reflexivity|set_solver]).

Lemma WA_ok : sworld_wf WA ∧ swf WA.
Proof.
  split; [W_ok|].
  apply (swf_rk _ [(pa‾, 1)]); [rk_ok|]. intros x y E. injection E as -> ->. rk_tac.
Qed.

Lemma WB_ok : sworld_wf WB ∧ swf WB.
Proof.
  split; [W_ok|].
  apply (swf_rk _ [(pb‾, 1)]); [rk_ok|]. intros x y E. injection E as -> ->. rk_tac.
Qed.

Lemma WC_ok : sworld_wf WC ∧ swf WC.
Proof.
  split; [W_ok|].
  apply (swf_rk _ [(pc‾, 1)]); [rk_ok|]. intros x y E. injection E as -> ->. rk_tac.
Qed.

Lemma WC'_ok : sworld_wf WC' ∧ swf WC'.
Proof.
  split; [W_ok|].
  apply (swf_rk _ [(pb, 1)]); [rk_ok|]. intros x y E. injection E as -> ->. rk_tac.
Qed.

(** ** The components *)

Lemma tA_typed : ptyped None HA ΣA (∅, {[+ tA +]}) TUnit.
Proof. apply cl2_hterm; [apply WA_ok|done|done|reflexivity]. Qed.

Lemma tB_typed : ptyped None HB ΣB (∅, {[+ tB +]}) TUnit.
Proof. apply cl2_hterm; [apply WB_ok|done|done|reflexivity]. Qed.

Lemma tC_typed : ptyped None HC ΣCc (∅, {[+ tC +]}) TUnit.
Proof. apply cl2_hterm; [apply WC_ok|done|done|reflexivity]. Qed.

Lemma tC'_typed : ptyped None HC' ΣC' (∅, {[+ tC' +]}) TUnit.
Proof. apply cl2_hterm; [apply WC'_ok|done|done|reflexivity]. Qed.

(** ** The cuts *)

Lemma chans_of_singleton o v : chans_of {[o := v]} = {[ech o]}.
Proof. unfold chans_of. by rewrite dom_singleton_L, set_map_singleton_L. Qed.

Lemma chans_of_senv2 o1 o2 x y : chans_of (senv2 o1 o2 x y) = {[ech o1]} ∪ {[ech o2]}.
Proof. unfold senv2. by rewrite chans_of_union, !chans_of_singleton. Qed.

Lemma senv_dual_singleton o s x : senv_dual {[o := (s, x)]} = {[(o‾)%cend := (dual s, x‾)]}.
Proof. unfold senv_dual. rewrite map_fmap_singleton, kmap_singleton. done. Qed.

Lemma senv2_comm o1 o2 x y : o1 ≠ o2 → senv2 o1 o2 x y = senv2 o2 o1 y x.
Proof. intros H. unfold senv2. apply map_union_comm. by apply map_disjoint_singleton_l, lookup_singleton_ne. Qed.

Ltac chan_disj :=
  apply elem_of_disjoint; intros ?;
  rewrite ?elem_of_union, ?elem_of_singleton, ?elem_of_empty; intros;
  repeat match goal with H : _ ∨ _ |- _ => destruct H end; subst; simpl in *;
  first [discriminate|contradiction].

Lemma pcomps_conv N Ws Σ Σ' C C' E T : pcomps N Ws Σ (C, E) T → Σ = Σ' → C = C' → pcomps N Ws Σ' (C', E) T.
Proof. by intros H -> ->. Qed.

(** A and B over the cut a: the composite holds c⁻ and b⁺. *)
Lemma ring_two :
  pcomps None (HA :: [HB]) (senv2 (ENeg "c") (EPos "b") pc‾ pb) ({["a"]}, {[+ tA +]} ⊎ {[+ tB +]}) TUnit.
Proof.
  set (ΣC := {[EPos "a" := (SEnd, pa)]} : senv).
  assert (senv_dual ΣC = {[ENeg "a" := (SEnd, pa‾)]}) as Ed by (unfold ΣC; by rewrite senv_dual_singleton).
  eapply pcomps_conv.
  - apply (pc_snoc None [HA] HB {[ENeg "c" := (SEnd, pc‾)]} {[EPos "b" := (SEnd, pb)]} ΣC ∅ ∅
             {[+ tA +]} {[+ tB +]} TUnit).
    + apply pc_one, tA_typed.
    + rewrite Ed. assert ({[EPos "b" := (SEnd, pb)]} ∪ {[ENeg "a" := (SEnd, pa‾)]} = ΣB) as -> by
        (unfold ΣB; rewrite (senv2_comm (ENeg "a")) by done; done).
      apply tB_typed.
    + rewrite !chans_of_singleton. chan_disj.
    + unfold ΣC. rewrite !chans_of_singleton. chan_disj.
    + unfold ΣC. rewrite !chans_of_singleton. chan_disj.
    + set_solver.
    + set_solver.
    + set_solver.
  - done.
  - unfold ΣC. rewrite chans_of_singleton. simpl. set_solver.
Qed.

(** The third component over the cut {c, b}. *)
Lemma ring_three H t :
  ptyped None H ΣC' (∅, {[+ t +]}) TUnit → pcomps None (HA :: HB :: [H]) ∅ (ring_cfg t) TUnit.
Proof.
  intros Ht. set (ΣC := senv2 (ENeg "c") (EPos "b") pc‾ pb).
  eapply pcomps_conv.
  - apply (pc_snoc None (HA :: [HB]) H ∅ ∅ ΣC {["a"]} ∅ ({[+ tA +]} ⊎ {[+ tB +]}) {[+ t +]} TUnit).
    + rewrite (left_id_L ∅ (∪)). apply ring_two.
    + rewrite (left_id_L ∅ (∪)). unfold ΣC. rewrite senv_dual_senv2. exact Ht.
    + set_solver.
    + rewrite chans_of_empty. set_solver.
    + rewrite chans_of_empty. set_solver.
    + set_solver.
    + unfold ΣC. rewrite chans_of_empty, chans_of_senv2. chan_disj.
    + set_solver.
  - by rewrite (left_id_L ∅ (∪)).
  - unfold ΣC. rewrite chans_of_senv2. simpl. set_solver.
Qed.

(** ** The ring: pairwise consistent, cyclic as a whole *)

Lemma ring_comps : pcomps None (HA :: HB :: [HC]) ∅ (ring_cfg tC) TUnit.
Proof.
  apply ring_three. unfold ΣC'. rewrite (senv2_comm (EPos "c")) by done. apply tC_typed.
Qed.

Theorem ring_pairs : swf (HA ⊔ HB) ∧ swf (HB ⊔ HC) ∧ swf (HA ⊔ HC).
Proof.
  split_and!.
  - apply (swf_sub _ (WA ⊔ WB)); [intros x y; apply join_sub; intros u v; apply swrestrict_lt|].
    apply (swf_rk _ ((pa‾, 1) :: [(pb‾, 2)])); [rk_ok|]. intros x y [E|E]; injection E as -> ->; rk_tac.
  - apply (swf_sub _ (WB ⊔ WC)); [intros x y; apply join_sub; intros u v; apply swrestrict_lt|].
    apply (swf_rk _ ((pb‾, 1) :: [(pc‾, 2)])); [rk_ok|]. intros x y [E|E]; injection E as -> ->; rk_tac.
  - apply (swf_sub _ (WA ⊔ WC)); [intros x y; apply join_sub; intros u v; apply swrestrict_lt|].
    apply (swf_rk _ ((pc‾, 1) :: [(pa‾, 2)])); [rk_ok|]. intros x y [E|E]; injection E as -> ->; rk_tac.
Qed.

(** A fact of the whole world between interface points is a fact of the
    hidden world. *)
Lemma hidden_fact W Σ x y (a b : nat) :
  sw_facts W (FLt x y) → pt_root x = NConst a → pt_root y = NConst b →
  a ∈ sw_consts W ∩ iface Σ TUnit → b ∈ sw_consts W ∩ iface Σ TUnit →
  sw_facts (swrestrict W (iface Σ TUnit)) (FLt x y).
Proof. intros Hf Hx Hy Ha Hb. split_and!; [by apply sw_lt_fact|by exists a|by exists b]. Qed.

Lemma senv2_iface o1 o2 x y a b :
  o1 ≠ o2 → pt_root x = NConst a → pt_root y = NConst b →
  a ∈ iface (senv2 o1 o2 x y) TUnit ∧ b ∈ iface (senv2 o1 o2 x y) TUnit.
Proof.
  intros Ho Hx Hy. unfold iface. split; apply elem_of_union_l, elem_of_senv_consts.
  - exists o1, SEnd, x. split; [|right; rewrite (pt_consts_root _ _ Hx); set_solver].
    unfold senv2. by rewrite lookup_union, lookup_singleton_eq, lookup_singleton_ne.
  - exists o2, SEnd, y. split; [|right; rewrite (pt_consts_root _ _ Hy); set_solver].
    unfold senv2. by rewrite lookup_union, lookup_singleton_eq, lookup_singleton_ne.
Qed.

Theorem ring_cyclic : ¬ sacyc (sw_joins (HA :: HB :: [HC])).
Proof.
  intros HS. apply (HS pc‾).
  destruct (senv2_iface (ENeg "c") (EPos "a") pc‾ pa 2 0) as [IA1 IA2]; [done|done|done|].
  destruct (senv2_iface (ENeg "a") (EPos "b") pa‾ pb 0 1) as [IB1 IB2]; [done|done|done|].
  destruct (senv2_iface (ENeg "b") (EPos "c") pb‾ pc 1 2) as [IC1 IC2]; [done|done|done|].
  eapply sw_lt_trans; [|eapply sw_lt_trans]; apply sw_lt_fact.
  - exists HA. split; [set_solver|]. apply (hidden_fact _ _ _ _ 2 0); try done; set_solver.
  - exists HB. split; [set_solver|]. apply (hidden_fact _ _ _ _ 0 1); try done; set_solver.
  - exists HC. split; [set_solver|]. apply (hidden_fact _ _ _ _ 1 2); try done; set_solver.
Qed.

(** ** The ring deadlocks *)

Lemma cl2_tstep o1 o2 α e' : tstep (cl2 o1 o2) α e' → α = LSess (SClose o1).
Proof.
  intros H. apply act_step in H as (a & Ha & Hoff). simpl in Ha. injection Ha as <-.
  destruct α as [| | |[]]; simpl in Hoff; try done. by subst.
Qed.

Lemma ring_first e α e' :
  e ∈ ({[+ tA +]} ⊎ {[+ tB +]} ⊎ {[+ tC +]} : gmultiset expr) → tstep e α e' →
  α = LSess (SClose (ENeg "c")) ∨ α = LSess (SClose (ENeg "a")) ∨ α = LSess (SClose (ENeg "b")).
Proof.
  rewrite !gmultiset_elem_of_disj_union, !gmultiset_elem_of_singleton.
  intros [[->| ->]| ->] H; apply cl2_tstep in H; auto.
Qed.

Lemma ring_stuck p' : ¬ preduction (ring_cfg tC) p'.
Proof.
  intros H. apply pstep_iff in H. remember (ring_cfg tC) as p eqn:Ep. remember PTau as π eqn:Eπ.
  destruct H as [C E e σ e' Hs _|C E e e' Hs|C E e c e' Hs _ _ _|C E e v e' Hs
                |C E o v e e' f f' Hs Hf|C E o e e' f f' Hs Hf _|C E o b e e' f f' Hs Hf
                |C E e o1 o2 e' Hs _];
    try discriminate Eπ; injection Ep as _ HE;
    (assert (e ∈ ({[+ tA +]} ⊎ {[+ tB +]} ⊎ {[+ tC +]} : gmultiset expr)) as He
       by (rewrite <-HE; multiset_solver));
    destruct (ring_first _ _ _ He Hs) as [Ea|[Ea|Ea]]; try discriminate Ea.
  all: injection Ea as ->;
    (assert (f ∈ ({[+ tA +]} ⊎ {[+ tB +]} ⊎ {[+ tC +]} : gmultiset expr)) as Hf'
       by (rewrite <-HE; multiset_solver));
    destruct (ring_first _ _ _ Hf' Hf) as [Eb|[Eb|Eb]]; discriminate Eb.
Qed.

Theorem ring_not_df : ¬ deadlock_free (ring_cfg tC).
Proof.
  intros H. destruct (H (ring_cfg tC) (rtc_refl _ _)) as [(v & E & Ep & _)|(p' & Hp)].
  - injection Ep as Ec _. set_solver.
  - exact (ring_stuck p' Hp).
Qed.

(** No world types the ring, with or without hiding. *)
Theorem ring_rejected W T : ¬ ptyped None W ∅ (ring_cfg tC) T.
Proof. intros H. exact (ring_not_df (soundness_h W _ T H)). Qed.

Corollary ring_rejected_full W T : ¬ fptyped None W ∅ (ring_cfg tC) T.
Proof. intros H. destruct (fptyped_ptyped _ _ _ _ _ H) as (Wi & Hi & _). exact (ring_rejected Wi T Hi). Qed.

(** ** The two-channel cycle

    close c⁺; close d⁺ ∥ close d⁻; close c⁻ deadlocks. Typed as two
    components, the first asks the point of c below the head of d and
    the second the point of d‾ below the head of c‾, so the join holds a
    cycle. No world types it at N = ∞ ([cyc2_rejected]), through
    soundness, which reads only acyclicity of worlds. *)

Definition cyc2_cfg : proc :=
  ({["c"]} ∪ {["d"]}, {[+ cl2 (EPos "c") (EPos "d") +]} ⊎ {[+ cl2 (ENeg "d") (ENeg "c") +]}).

Lemma cyc2_first e α e' :
  e ∈ ({[+ cl2 (EPos "c") (EPos "d") +]} ⊎ {[+ cl2 (ENeg "d") (ENeg "c") +]} : gmultiset expr) →
  tstep e α e' → α = LSess (SClose (EPos "c")) ∨ α = LSess (SClose (ENeg "d")).
Proof.
  rewrite !gmultiset_elem_of_disj_union, !gmultiset_elem_of_singleton.
  intros [->| ->] H; apply cl2_tstep in H; auto.
Qed.

Lemma cyc2_stuck p' : ¬ preduction cyc2_cfg p'.
Proof.
  intros H. apply pstep_iff in H. remember cyc2_cfg as p eqn:Ep. remember PTau as π eqn:Eπ.
  destruct H as [C E e σ e' Hs _|C E e e' Hs|C E e c e' Hs _ _ _|C E e v e' Hs
                |C E o v e e' f f' Hs Hf|C E o e e' f f' Hs Hf _|C E o b e e' f f' Hs Hf
                |C E e o1 o2 e' Hs _];
    try discriminate Eπ; injection Ep as _ HE;
    (assert (e ∈ ({[+ cl2 (EPos "c") (EPos "d") +]} ⊎ {[+ cl2 (ENeg "d") (ENeg "c") +]} : gmultiset expr)) as He
       by (rewrite <-HE; multiset_solver));
    destruct (cyc2_first _ _ _ He Hs) as [Ea|Ea]; try discriminate Ea.
  all: injection Ea as ->;
    (assert (f ∈ ({[+ cl2 (EPos "c") (EPos "d") +]} ⊎ {[+ cl2 (ENeg "d") (ENeg "c") +]} : gmultiset expr)) as Hf'
       by (rewrite <-HE; multiset_solver));
    destruct (cyc2_first _ _ _ Hf' Hf) as [Eb|Eb]; discriminate Eb.
Qed.

Theorem cyc2_not_df : ¬ deadlock_free cyc2_cfg.
Proof.
  intros H. destruct (H cyc2_cfg (rtc_refl _ _)) as [(v & E & Ep & _)|(p' & Hp)].
  - injection Ep as Ec _. set_solver.
  - exact (cyc2_stuck p' Hp).
Qed.

Theorem cyc2_rejected W T : ¬ fptyped None W ∅ cyc2_cfg T.
Proof. intros H. exact (cyc2_not_df (soundness W _ T H)). Qed.

Corollary cyc2_rejected_h W T : ¬ ptyped None W ∅ cyc2_cfg T.
Proof. intros H. exact (cyc2_not_df (soundness_h W _ T H)). Qed.

(** ** The acyclic ring *)

Lemma ring'_comps : pcomps None (HA :: HB :: [HC']) ∅ (ring_cfg tC') TUnit.
Proof. apply ring_three, tC'_typed. Qed.

Definition Wall : sworld :=
  SWorld ({[0]} ∪ {[1]} ∪ {[2]}) (λ g, g = FLt pc‾ pa‾ ∨ g = FLt pa‾ pb‾ ∨ g = FLt pc pb).

Lemma ring'_wf : swf (sw_joins (HA :: HB :: [HC'])).
Proof.
  apply (swf_sub _ Wall).
  - intros x y. apply sw_lt_steps. intros u v (W & HW & Hf).
    assert (∀ W0, W0 ⊑ₛ Wall → sw_facts (swrestrict W0 (iface ΣA TUnit)) (FLt u v) ∨
              sw_facts (swrestrict W0 (iface ΣB TUnit)) (FLt u v) ∨
              sw_facts (swrestrict W0 (iface ΣC' TUnit)) (FLt u v) → Wall ⊢ₛ u ≺ v) as K.
    { intros W0 H0 [(Hl & _)|[(Hl & _)|(Hl & _)]]; by eapply sw_lt_mono. }
    rewrite !elem_of_cons, elem_of_nil in HW. destruct HW as [->|[->|[->|[]]]].
    + apply (K WA); [split; [simpl; set_solver|intros g E; by left]|by left].
    + apply (K WB); [split; [simpl; set_solver|intros g E; by right; left]|by right; left].
    + apply (K WC'); [split; [simpl; set_solver|intros g E; by right; right]|by right; right].
  - apply (swf_rk _ ((pa‾, 1) :: (pb‾, 2) :: [(pb, 1)])); [rk_ok|].
    intros x y [E|[E|E]]; injection E as -> ->; rk_tac.
Qed.

Theorem ring_typed : ∃ W, ptyped None W ∅ (ring_cfg tC') TUnit.
Proof. destruct (p_connect_n _ _ _ _ _ ring'_comps (swf_wok None _ ring'_wf)) as (W & H & _). by exists W. Qed.

Theorem ring_df : deadlock_free (ring_cfg tC').
Proof. exact (connect_n_soundness _ _ _ ring'_comps (swf_sacyc _ ring'_wf)). Qed.
