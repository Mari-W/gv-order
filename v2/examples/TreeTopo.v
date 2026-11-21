(** * A tree of three threads, proved in the relation

      tt_mid  = sb_thread                      (holds c at x and d at y)
      tt_a    = close c̄                        (a leaf, holds c̄ at x̄)
      tt_b    = close d̄                        (a leaf, holds d̄ at ȳ)

    The threads form the path A - M - B. The middle thread is the thread of
    [examples/SemBranch.v]. It computes a flag, closes c then d in the live
    arm and d then c in the dead arm. The process is
    [({c, d}, {M, A, B})]. Every thread holds at most the ends of its own
    channels, and the channel graph is a tree.

    The middle thread is shown in E by hand, as in SemBranch (three
    deterministic β steps, then the fundamental theorem for the live arm).
    The leaves are closed single-close terms and use the fundamental
    theorem. [sem_p_term] makes each thread a process, [sem_p_connect] joins
    A to M over c and then B to the result over d, and [adequacy] applies
    because the join of the worlds is strict.

    - [tt_deadlock_free]  : the closed process is deadlock free.
    - [tt_dead_world_strict] : one world holds both arm facts x ≺ ȳ and
      y ≺ x̄ and is strict, so a static derivation exists for this tree
      (see docs/redesign/tree-example.md). *)

From GV Require Export examples.SemBranch.

(** ** The program *)

Definition tt_mid : expr := sb_thread.
Definition tt_a : expr := EClose (Chan (edual oc)).
Definition tt_b : expr := EClose (Chan (edual od)).

Definition tt_config : proc :=
  (({["c"]} ∪ {["d"]}), ({[+ tt_mid +]} ⊎ {[+ tt_a +]}) ⊎ {[+ tt_b +]}).

(** ** Worlds

    All three threads live in [Wa]. The leaves close a channel that is
    their only one and need no fact. *)

Definition Wtt : world := (Wa ⊔ Wa) ⊔ Wa.

Lemma Wtt_strict : strict Wtt.
Proof.
  apply strict_rank.
  - apply wjoin_wf; [apply wjoin_wf|]; apply Wa_wf.
  - simpl. set_solver.
  - simpl. intros x y [[H|H]|H]; injection H as Hx Hy; subst; unfold rk, px, py, pt_dual; simpl; lia.
Qed.

Lemma Wt_strict : strict (Wa ⊔ Wa).
Proof.
  apply (strict_mono _ Wtt); [apply wjoin_wf; apply Wa_wf|apply wext_join_l|apply Wtt_strict].
Qed.

(** ** Static world of the dead arm

    The static system types both arms of the middle thread under one
    world, so it needs x ≺ ȳ and y ≺ x̄ together. That world is strict.
    The potential 10·offset + (0 for a positive point, 1 for a negative
    one) grows along both facts and along both kinds of step. *)

Definition Wd : world :=
  World ({[0]} ∪ {[1]}) (λ f, f = FLt px (py‾) ∨ f = FLt py (px‾)) ∅ (λ _ _, False).

Lemma Wd_wf : world_wf Wd.
Proof.
  split; simpl; [|done]. intros x y [H|H]; injection H as Hx Hy; subst;
    split; eexists; (split; [reflexivity|set_solver]).
Qed.

Definition pot (x : point) : nat := 10 * pt_off x + (if pt_pol x then 0 else 1).

Lemma tt_dead_world_strict : strict Wd.
Proof.
  split; [apply Wd_wf|]. intros x Hx.
  assert (∀ a b, wstep Wd a b → pot a < pot b) as Hs.
  { intros a b Hs. destruct Hs as [a b H|ℓ g a b Hℓ _|a|a].
    - simpl in H. destruct H as [H|H]; injection H as Hx' Hy'; subst; unfold pot, px, py, pt_dual; simpl; lia.
    - simpl in Hℓ. set_solver.
    - unfold pot. simpl. destruct (pt_pol a); simpl; lia.
    - unfold pot. simpl. destruct (pt_pol a); simpl; lia. }
  assert (∀ a b, Wd ⊢ a ≺ b → pot a < pot b) as H.
  { intros a b Hab. induction Hab as [a b H|a b c H _ IH]; [by apply Hs|].
    apply Hs in H. lia. }
  specialize (H x x Hx). lia.
Qed.

(** ** The leaves in E *)

Definition Θl (o : cend) (x : point) : tenv := {[o := TE SEnd x None None]}.

Lemma leaf_typed W o x :
  dftyped W (Θl o x) hc_empty [] (∅, None) (EClose (Chan o)) TUnit.
Proof.
  eapply d_close with (S0 := SEnd) (x := x) (a := None); [done|apply ub_below_empty|].
  apply d_chan; intros o' Ho; inversion Ho.
Unshelve. all: try exact None.
Qed.

Lemma leaf_E o x n :
  Erel κ_DF n Wa (tenv_erase (Θl o x)) TUnit ∅ (EClose (Chan o)).
Proof.
  apply typed_E_df; [apply Wa_strict| |apply leaf_typed].
  unfold tenv_df, Θl. by rewrite map_fmap_singleton.
Qed.

(** ** Interfaces *)

Definition Sc : senv := {[oc := (SEnd, px)]}.
Definition Sd : senv := {[od := (SEnd, py)]}.

Lemma Sc_Sd_disj : Sd ##ₘ Sc.
Proof. unfold Sc, Sd. apply map_disjoint_singleton_l_2. rewrite lookup_singleton_ne; [done|]. exact (oc_od). Qed.

Lemma ΣC_split : ΣC = Sd ∪ Sc.
Proof.
  unfold ΣC, Sc, Sd. apply map_union_comm. apply map_disjoint_singleton_l_2.
  rewrite lookup_singleton_ne; [done|]. exact (not_eq_sym oc_od).
Qed.

Lemma erase_Θl o x : tenv_erase (Θl o x) = {[o := (SEnd, x)]}.
Proof. unfold tenv_erase, Θl. by rewrite map_fmap_singleton. Qed.

Lemma dom_Sc : dom Sc = {[oc]}. Proof. unfold Sc. by rewrite dom_singleton_L. Qed.
Lemma dom_Sd : dom Sd = {[od]}. Proof. unfold Sd. by rewrite dom_singleton_L. Qed.
Lemma chans_Sc : chans_of Sc = {["c"]}.
Proof. unfold chans_of. rewrite dom_Sc, set_map_singleton_L. reflexivity. Qed.
Lemma chans_Sd : chans_of Sd = {["d"]}.
Proof. unfold chans_of. rewrite dom_Sd, set_map_singleton_L. reflexivity. Qed.

Lemma pfree_Sc : pfree Sc.
Proof. intros o Ho Hn. rewrite dom_Sc in Ho, Hn. set_unfold in Ho; set_unfold in Hn. subst. discriminate. Qed.
Lemma pfree_Sd : pfree Sd.
Proof. intros o Ho Hn. rewrite dom_Sd in Ho, Hn. set_unfold in Ho; set_unfold in Hn. subst. discriminate. Qed.

Lemma erase_Θl_c : tenv_erase (Θl (edual oc) (px‾)) = senv_dual Sc.
Proof.
  unfold tenv_erase, Θl, senv_dual, Sc. rewrite !map_fmap_singleton, kmap_singleton by apply _. reflexivity.
Qed.
Lemma erase_Θl_d : tenv_erase (Θl (edual od) (py‾)) = senv_dual Sd.
Proof.
  unfold tenv_erase, Θl, senv_dual, Sd. rewrite !map_fmap_singleton, kmap_singleton by apply _. reflexivity.
Qed.

Lemma pfree_dual' Σ : pfree Σ → pfree (senv_dual Σ).
Proof. apply pfree_dual. Qed.

(** ** The threads as processes *)

Lemma mid_P n : Prel κ_DF n Wa (Sd ∪ Sc) TUnit (∅, {[+ tt_mid +]}).
Proof.
  rewrite <-ΣC_split.
  refine (sem_p_term κ_DF n Wa _ ΣC ∅ ∅ _ TUnit _ sth_a (sb_thread_E n)). constructor.
Qed.

Lemma sth_leaf o x Σ : tenv_erase (Θl o x) = Σ → pfree Σ → sth Σ Σ ∅ ∅.
Proof.
  intros _ Hf. constructor.
  - by rewrite (right_id_L ∅ (∪)).
  - intros o'. rewrite dom_empty_L. set_solver.
  - set_solver.
  - exact Hf.
  - intros c Hc. set_solver.
Qed.

Lemma leaf_P o x Σ n : tenv_erase (Θl o x) = Σ → pfree Σ →
  Prel κ_DF n Wa Σ TUnit (∅, {[+ EClose (Chan o) +]}).
Proof.
  intros He Hf.
  assert (Erel κ_DF n Wa Σ TUnit ∅ (EClose (Chan o))) as HE by (rewrite <-He; apply leaf_E).
  refine (sem_p_term κ_DF n Wa Σ Σ ∅ ∅ _ TUnit _ (sth_leaf o x Σ He Hf) HE). constructor.
Qed.

Lemma a_P n : Prel κ_DF n Wa (senv_dual Sc) TUnit (∅, {[+ tt_a +]}).
Proof. apply (leaf_P _ (px‾)); [apply erase_Θl_c|apply pfree_dual', pfree_Sc]. Qed.

Lemma b_P n : Prel κ_DF n Wa (senv_dual Sd) TUnit (∅, {[+ tt_b +]}).
Proof. apply (leaf_P _ (py‾)); [apply erase_Θl_d|apply pfree_dual', pfree_Sd]. Qed.

(** ** The two connections *)

Lemma conn_c : conn Sd Sc (∅ : gset chan) ∅ (senv_dual Sc) (∅ : gset chan).
Proof.
  constructor.
  all: first [apply map_disjoint_empty_l|apply pfree_empty|apply senv_dual_cut|apply Sc_Sd_disj
             |apply pfree_Sc|apply pfree_Sd
             |(rewrite ?chans_of_empty', ?chans_Sc, ?chans_Sd; set_solver)].
Qed.

Lemma conn_d : conn ∅ Sd ({["c"]} : gset chan) ∅ (senv_dual Sd) (∅ : gset chan).
Proof.
  constructor.
  all: first [apply map_disjoint_empty_l|apply pfree_empty|apply senv_dual_cut|apply pfree_Sd
             |(rewrite ?chans_of_empty', ?chans_Sc, ?chans_Sd; set_solver)].
Qed.

(** ** Main theorem *)

Theorem tt_deadlock_free : deadlock_free tt_config.
Proof.
  apply (adequacy Wtt TUnit tt_config Wtt_strict). intros n.
  pose proof (sem_p_connect κ_DF n Wa Wa Sd Sc ∅ (senv_dual Sc) _ _ TUnit ltac:(constructor)
    (mid_P n) (eq_rect_r (λ S, Prel κ_DF n Wa S TUnit (∅, {[+ tt_a +]})) (a_P n) (left_id_L ∅ (∪) _)) conn_c) as H1.
  unfold pconn in H1. simpl in H1. rewrite chans_Sc, (right_id_L ∅ (∪)) in H1.
  assert (Prel κ_DF n (Wa ⊔ Wa) (∅ ∪ Sd) TUnit (∅ ∪ ∅ ∪ {["c"]}, {[+ tt_mid +]} ⊎ {[+ tt_a +]})) as H1' by (rewrite (left_id_L ∅ (∪)); exact H1).
  clear H1. rename H1' into H1.
  pose proof (sem_p_connect κ_DF n (Wa ⊔ Wa) Wa ∅ Sd ∅ (senv_dual Sd) _ _ TUnit ltac:(constructor)
    H1 (eq_rect_r (λ S, Prel κ_DF n Wa S TUnit (∅, {[+ tt_b +]})) (b_P n) (left_id_L ∅ (∪) _)) conn_d) as H2.
  unfold pconn in H2. simpl in H2. rewrite chans_Sd, !(left_id_L ∅ (∪)), !(right_id_L ∅ (∪)) in H2.
  exact H2.
Qed.

Print Assumptions tt_dead_world_strict.
Print Assumptions tt_deadlock_free.
