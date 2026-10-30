(** * Compositionality of the term rules (spec §11)

    One lemma per typing rule of §9, on top of the bind lemma
    (Bind.v). The elimination rules run their head subterm under the
    frame F ∪ H, where H holds the heads of the rest of the term. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export Bind.

Set Default Proof Using "All".

(** ** Aliasing a fresh point to a known one

    new at type S@x ⊗ S′@x creates its channel at a fresh point (a, 0)
    and must alias it to x (sharp edges 49). The world W0' below knows
    only the root r of x and a, and identifies the a-rooted points with
    their images under a ↦ x. Joined with W, it is a fresh extension of
    W placing a. *)

Section alias.
  Context (a : nat) (x : point).

  Fixpoint acn (p : pname) : point :=
    match p with
    | NConst c => if decide (c = a) then x else Pt (NConst c) 0
    | NVar v => Pt (NVar v) 0
    | NSlot q b i => pt_slot (pt_shift b (acn q)) i
    end.

  Definition acanon (y : point) : point := pt_shift (pt_off y) (acn (pt_name y)).

  Lemma acn_id p : pn_root p ≠ NConst a → acn p = Pt p 0.
  Proof.
    induction p as [c|v|q IH b i]; simpl; intros Hr.
    - rewrite decide_False; [done|]. intros ->. by apply Hr.
    - done.
    - rewrite IH by done. unfold pt_slot, pt_shift. simpl. done.
  Qed.

  Lemma acanon_id y : pt_root y ≠ NConst a → acanon y = y.
  Proof.
    intros Hr. unfold acanon. rewrite acn_id by done. destruct y. unfold pt_shift. simpl. done.
  Qed.

  Lemma acn_root p :
    pt_root (acn p) = if decide (pn_root p = NConst a) then pt_root x else pn_root p.
  Proof.
    induction p as [c|v|q IH b i]; simpl.
    - destruct (decide (c = a)) as [->|Hc].
      + by rewrite decide_True.
      + rewrite decide_False; [done|congruence].
    - done.
    - rewrite pt_root_slot, pt_root_shift. exact IH.
  Qed.

  Lemma acanon_root y :
    pt_root (acanon y) = if decide (pt_root y = NConst a) then pt_root x else pt_root y.
  Proof. unfold acanon. rewrite pt_root_shift. apply acn_root. Qed.

  Lemma acanon_shift y : acanon (pt_shift 1 y) = pt_shift 1 (acanon y).
  Proof. unfold acanon, pt_shift. simpl. f_equal. lia. Qed.

  Lemma acanon_slot y i : acanon (pt_slot y i) = pt_slot (acanon y) i.
  Proof.
    unfold acanon, pt_slot, pt_shift. simpl. repeat f_equal; try lia.
  Qed.

  Lemma acanon_name_off y z :
    pt_name y = pt_name z → pt_off y < pt_off z →
    pt_name (acanon y) = pt_name (acanon z) ∧ pt_off (acanon y) < pt_off (acanon z).
  Proof. intros Hn Ho. unfold acanon, pt_shift. simpl. rewrite Hn. split; [done|lia]. Qed.

  Definition W0 : world :=
    World {[pt_root x]} (λ y z, y = z)
      (λ y z, pt_name y = pt_name z ∧ pt_off y < pt_off z).

  Definition W0' : world :=
    World ({[pt_root x]} ∪ {[NConst a]}) (λ y z, acanon y = acanon z)
      (λ y z, pt_name (acanon y) = pt_name (acanon z) ∧
              pt_off (acanon y) < pt_off (acanon z)).

  Context (W : world) (HW : strict W) (Hx : pt_known W x) (Ha : NConst a ∉ w_names W).

  Lemma root_x_ne : pt_root x ≠ NConst a.
  Proof. intros He. apply Ha. unfold pt_known in Hx. by rewrite <-He. Qed.

  Lemma W0_wf : world_wf W0.
  Proof.
    split; simpl.
    - done.
    - done.
    - intros; congruence.
    - intros; congruence.
    - intros; congruence.
    - intros y z w [H1 H2] [H3 H4]. split; [congruence|lia].
    - intros y y' z z' -> [H1 H2] <-. done.
    - intros y. unfold pt_shift. simpl. split; [done|lia].
    - intros y z ->. by left.
    - intros y z H. by left.
    - intros p ->%elem_of_singleton. exact (wf_names_const _ (proj1 HW) _ Hx).
  Qed.

  Lemma W0_ext : wext W0 W.
  Proof.
    split_and!; simpl.
    - by apply singleton_subseteq_l.
    - intros y z ->. apply (wf_eq_refl _ (proj1 HW)).
    - intros y z [Hn Ho]. by apply wf_lt_same; [apply HW| |].
    - done.
  Qed.

  Lemma acanon_supp y z :
    pt_name (acanon y) = pt_name (acanon z) → y ≠ z ∨ True →
    (pt_root y = NConst a ∨ pt_root z = NConst a) →
    pt_root y ∈ ({[pt_root x]} ∪ {[NConst a]} : gset pname) ∧
    pt_root z ∈ ({[pt_root x]} ∪ {[NConst a]} : gset pname).
  Proof.
    intros Hn _ Hyz.
    assert (pt_root (acanon y) = pt_root (acanon z)) as Hr by (unfold pt_root; by rewrite Hn).
    rewrite !acanon_root in Hr.
    destruct (decide (pt_root y = NConst a)) as [Hy|Hy],
             (decide (pt_root z = NConst a)) as [Hz|Hz]; set_solver.
  Qed.

  Lemma W0'_wf : world_wf W0'.
  Proof.
    split; cbn [w_eq w_lt w_names W0'].
    - done.
    - done.
    - intros; congruence.
    - intros y z H. by rewrite !acanon_shift, H.
    - intros y z i H. by rewrite !acanon_slot, H.
    - intros y z w [H1 H2] [H3 H4]. split; [congruence|lia].
    - intros y y' z z' H1 [H2 H3] H4.
      change (acanon y = acanon y') in H1. change (acanon z' = acanon z) in H4.
      change (pt_name (acanon y) = pt_name (acanon z) ∧ pt_off (acanon y) < pt_off (acanon z)).
      rewrite H1, <-H4. split; [exact H2|exact H3].
    - intros y. rewrite acanon_shift. unfold pt_shift. simpl. split; [done|lia].
    - intros y z H. unfold eq_or_supp.
      destruct (decide (pt_root y = NConst a ∨ pt_root z = NConst a)) as [Hyz|Hyz].
      + right. apply acanon_supp; [by rewrite H|by right|done].
      + left. rewrite !acanon_id in H by naive_solver. done.
    - intros y z [Hn Ho]. unfold po_or_supp.
      destruct (decide (pt_root y = NConst a ∨ pt_root z = NConst a)) as [Hyz|Hyz].
      + right. apply acanon_supp; [done|by right|done].
      + left. rewrite !acanon_id in Hn, Ho by naive_solver. done.
    - intros p [Hp|Hp]%elem_of_union; apply elem_of_singleton in Hp as ->; [|by eexists].
      exact (wf_names_const _ (proj1 HW) _ Hx).
  Qed.

  Lemma W0'_strict : strict W0'.
  Proof. split; [apply W0'_wf|]. intros y [_ Ho]. lia. Qed.

  Lemma W0_fresh : wext_fresh W0 {[NConst a]} W0'.
  Proof.
    pose proof root_x_ne as Hne.
    split_and!.
    - split_and!; cbn [w_eq w_lt w_names W0 W0'].
      + set_solver.
      + intros y z ->. done.
      + intros y z [Hn Ho]. by apply acanon_name_off.
      + apply W0'_strict.
    - simpl. set_solver.
    - done.
    - intros y z Hy Hz.
      assert (pt_root y ≠ NConst a) by (clear -Hy; set_solver).
      assert (pt_root z ≠ NConst a) by (clear -Hz; set_solver).
      cbn [w_eq w_lt W0 W0']. rewrite !acanon_id by done. done.
  Qed.

  Lemma W0'_alias : w_eq W0' (pconst a) x.
  Proof.
    simpl. rewrite (acanon_id x) by apply root_x_ne.
    unfold acanon, pconst. simpl. rewrite decide_True by done.
    destruct x. unfold pt_shift. simpl. f_equal. lia.
  Qed.
End alias.

Lemma wext_fresh_alias W a x :
  strict W → pt_known W x → NConst a ∉ w_names W →
  ∃ W', wext_fresh W {[NConst a]} W' ∧ w_eq W' (pconst a) x.
Proof.
  intros HW Hx Ha. exists (wjoin (W0' a x) W). split.
  - apply (wext_fresh_join (W0 x)); [exact (W0_wf a x W HW Hx Ha)|exact (W0_fresh a x W HW Hx Ha)|
      exact (W0_ext a x W HW Hx Ha)|set_solver].
  - apply wjoin_l. exact (W0'_alias a x W HW Hx Ha).
Qed.

(** ** Heads of values

    The semantic condition behind the frames of E-App and E-Pair: the
    environment of a value of type T lies at or above heads(T). For
    a closure it is the lower point ({ℓ} ≼ heads(Θ), V-Abs), for a
    channel its point, and nothing for ∗, □ and constants. *)

Lemma comp_entry R Θ Θ1 Θ2 k e :
  tenv_comp R Θ Θ1 Θ2 → tenv_entry Θ k = Some e →
  (∃ k', tenv_entry Θ1 k' = Some e) ∨ (∃ k', tenv_entry Θ2 k' = Some e).
Proof.
  intros [Hj _] He. destruct k as [c b]. unfold tenv_entry in *. simpl in *.
  pose proof (Hj c) as J.
  destruct (Θ1 !! c) as [o1|] eqn:E1, (Θ2 !! c) as [o2|] eqn:E2, (Θ !! c) as [o|] eqn:E;
    inversion J; subst; try done.
  all: first [ left; exists (c, b); unfold tenv_entry; simpl; rewrite E1; exact He
             | right; exists (c, b); unfold tenv_entry; simpl; rewrite E2; exact He
             | destruct b; simplify_eq;
               first [ left; exists (c, false); unfold tenv_entry; simpl; by rewrite E1
                     | right; exists (c, false); unfold tenv_entry; simpl; by rewrite E2 ] ].
Qed.

Lemma heads_above_sub W H H' Θ : H ⊆ H' → heads_above W H Θ → heads_above W H' Θ.
Proof. intros Hs Hh k e He. destruct (Hh k e He) as (h & ? & ?). exists h. split; [set_solver|done]. Qed.

Lemma heads_above_comp R W H1 H2 Θ Θ1 Θ2 :
  tenv_comp R Θ Θ1 Θ2 → heads_above W H1 Θ1 → heads_above W H2 Θ2 →
  heads_above W (H1 ∪ H2) Θ.
Proof.
  intros Hc Hh1 Hh2 k e He.
  destruct (comp_entry _ _ _ _ _ _ Hc He) as [[k' Hk]|[k' Hk]].
  - destruct (Hh1 _ _ Hk) as (h & ? & ?). exists h. split; [set_solver|done].
  - destruct (Hh2 _ _ Hk) as (h & ? & ?). exists h. split; [set_solver|done].
Qed.

Lemma heads_above_empty W H : heads_above W H ∅.
Proof. intros [c b] e He. unfold tenv_entry in He. by rewrite lookup_empty in He. Qed.

Lemma heads_above_self W Θ : world_wf W → heads_above W (tenv_heads Θ) Θ.
Proof.
  intros HW k e He. exists e.2. split; [|left; apply (wf_eq_refl _ HW)].
  apply elem_of_tenv_heads_entry. eauto.
Qed.

Lemma Vrel_heads_above n W Θ T v :
  world_wf W → Vrel n W Θ T v → heads_above W (heads T) Θ.
Proof.
  intros HW. revert Θ v.
  induction T as [|ub lb T1 IH1 T2 IH2|T1 IH1 T2 IH2|T1 IH1 T2 IH2|m T1 IH1|s x];
    intros Θ v HV; simpl.
  - apply Vrel_unit_iff in HV as [-> _]. apply heads_above_empty.
  - apply Vrel_lolli_iff in HV as [(eb & _ & _ & Hlb & _)|(k & T0 & _ & -> & _)];
      [|apply heads_above_empty].
    intros k e He. destruct lb as [l|]; simpl in Hlb.
    + exists l. split; [set_solver|]. apply Hlb. apply elem_of_tenv_heads_entry. eauto.
    + exfalso. assert (e.2 ∈ tenv_heads Θ) as Hin by (apply elem_of_tenv_heads_entry; eauto).
      rewrite Hlb in Hin. set_solver.
  - apply Vrel_prod_iff in HV as (v1 & v2 & Θ1 & Θ2 & _ & Hc & H1 & H2).
    eapply heads_above_comp; [exact Hc|eauto|eauto].
  - apply Vrel_sum_iff in HV as [(v' & _ & H)|(v' & _ & H)].
    + eapply heads_above_sub; [|by eapply IH1]. set_solver.
    + eapply heads_above_sub; [|by eapply IH2]. set_solver.
  - apply Vrel_box_empty in HV as ->. apply heads_above_empty.
  - apply Vrel_sess_iff in HV as (c & s0 & k & _ & -> & _ & Hk).
    intros [c' b] e He. unfold tenv_entry in He. simpl in He.
    destruct (decide (c' = c)) as [->|Hne].
    + rewrite lookup_singleton_eq in He. destruct b; simplify_eq.
      exists x. split; [set_solver|]. left. by apply (wf_eq_sym _ HW).
    + rewrite lookup_singleton_ne in He by done. done.
Qed.

(** ** Grounding substitutions *)

Fixpoint lenv_heads (Δ : lenv) : gset point :=
  match Δ with
  | [] => ∅
  | None :: Δ' => lenv_heads Δ'
  | Some T :: Δ' => heads T ∪ lenv_heads Δ'
  end.

Lemma grounding_heads n W Θ Δ γ :
  world_wf W → grounding n W Θ Δ γ → heads_above W (lenv_heads Δ) Θ.
Proof.
  intros HW. revert Θ γ. induction Δ as [|[T|] Δ IH]; intros Θ γ Hg; simpl in *.
  - subst. apply heads_above_empty.
  - destruct Hg as (Θ1 & Θ2 & Hc & HV & Hg).
    eapply heads_above_comp; [exact Hc|by eapply Vrel_heads_above|by eapply IH].
  - by eapply IH.
Qed.

Lemma grounding_mono n W W' Θ Δ γ :
  world_wf W → wext W W' → grounding n W Θ Δ γ → grounding n W' Θ Δ γ.
Proof.
  intros HW0 HW. revert Θ γ. induction Δ as [|[T|] Δ IH]; intros Θ γ Hg; simpl in *; [done| |exact (IH _ _ Hg)].
  destruct Hg as (Θ1 & Θ2 & Hc & HV & Hg). exists Θ1, Θ2. split_and!.
  - eapply tenv_comp_mono; [|exact Hc]. intros. by apply (proj1 (proj2 HW)).
  - by eapply Vrel_mono.
  - exact (IH _ _ Hg).
Qed.

Lemma grounding_down n m W Θ Δ γ :
  m ≤ n → grounding n W Θ Δ γ → grounding m W Θ Δ γ.
Proof.
  intros Hle. revert Θ γ. induction Δ as [|[T|] Δ IH]; intros Θ γ Hg; simpl in *; [done| |exact (IH _ _ Hg)].
  destruct Hg as (Θ1 & Θ2 & Hc & HV & Hg). exists Θ1, Θ2. split_and!; [done|by eapply Vrel_down|exact (IH _ _ Hg)].
Qed.

(** ** Composition: units and rearrangements *)

Lemma tenv_comp_empty_l R Θ : (∀ x y, R x y → R y x) → tenv_comp R Θ ∅ Θ.
Proof. intros Hs. apply comp_comm; [done|]. apply tenv_comp_empty_r. Qed.

Lemma tenv_comp_empty_l_inv R Θ Θ2 : (∀ x y, R x y → R y x) → tenv_comp R Θ ∅ Θ2 → Θ = Θ2.
Proof. intros Hs Hc. by eapply tenv_comp_empty_r_inv, comp_comm. Qed.

Lemma tenv_comp_empty_inv R Θ : tenv_comp R Θ ∅ ∅ → Θ = ∅.
Proof. apply tenv_comp_empty_r_inv. Qed.

(** (Θ1, Θ2), (Θ1', Θ2') = (Θ1, Θ1'), (Θ2, Θ2'). *)
Lemma comp_swap4 R Θ'' Θ Θ' Θ1 Θ2 Θ1' Θ2' :
  (∀ x y, R x y → R y x) →
  tenv_comp R Θ'' Θ Θ' → tenv_comp R Θ Θ1 Θ2 → tenv_comp R Θ' Θ1' Θ2' →
  ∃ A B, tenv_comp R Θ'' A B ∧ tenv_comp R A Θ1 Θ1' ∧ tenv_comp R B Θ2 Θ2'.
Proof.
  intros Hs Hc Hc1 Hc2.
  (* Θ'' = (Θ1, Θ'), Θ2 *)
  destruct (comp_assoc _ _ _ _ _ _ Hs Hc Hc1) as [HX1 Hc3].
  set (X1 := tjoin_as Θ'' Θ1 Θ') in *.
  (* X1 = (Θ1', Θ1), Θ2' *)
  destruct (comp_assoc _ _ _ _ _ _ Hs (comp_comm _ _ _ _ Hs HX1) Hc2) as [HX2 Hc4].
  set (X2 := tjoin_as X1 Θ1' Θ1) in *.
  (* Θ'' = (Θ2', Θ2), X2 *)
  destruct (comp_assoc _ _ _ _ _ _ Hs Hc3 (comp_comm _ _ _ _ Hs Hc4)) as [HY Hc5].
  exists X2, (tjoin_as Θ'' Θ2' Θ2). split_and!.
  - by apply comp_comm.
  - by apply comp_comm.
  - by apply comp_comm.
Qed.

Lemma grounding_split n W Θ Δ Δ1 Δ2 γ :
  world_wf W → lenv_split Δ Δ1 Δ2 → grounding n W Θ Δ γ →
  ∃ Θ1 Θ2, tenv_comp (w_eq W) Θ Θ1 Θ2 ∧ grounding n W Θ1 Δ1 γ ∧ grounding n W Θ2 Δ2 γ.
Proof.
  intros HW Hsp. assert (∀ x y, w_eq W x y → w_eq W y x) as Hs by apply (wf_eq_sym _ HW).
  revert Θ γ. induction Hsp as [|Δ Δ1 Δ2 Hsp IH|T Δ Δ1 Δ2 Hsp IH|T Δ Δ1 Δ2 Hsp IH|U Δ Δ1 Δ2 HU Hsp IH];
    intros Θ γ Hg; simpl in *.
  - subst. exists ∅, ∅. split_and!; [apply tenv_comp_empty_r|done|done].
  - by apply IH.
  - destruct Hg as (Θa & Θr & Hc & HV & Hg).
    destruct (IH _ _ Hg) as (Θ1 & Θ2 & Hc' & Hg1 & Hg2).
    destruct (comp_assoc _ _ _ _ _ _ Hs (comp_comm _ _ _ _ Hs Hc) Hc') as [HX HY].
    eexists _, Θ2. split_and!; [exact HY| |done].
    exists Θa, Θ1. split_and!; [by apply comp_comm|done|done].
  - destruct Hg as (Θa & Θr & Hc & HV & Hg).
    destruct (IH _ _ Hg) as (Θ1 & Θ2 & Hc' & Hg1 & Hg2).
    destruct (comp_assoc _ _ _ _ _ _ Hs (comp_comm _ _ _ _ Hs Hc) (comp_comm _ _ _ _ Hs Hc'))
      as [HX HY].
    eexists Θ1, _. split_and!; [by apply comp_comm|done|].
    exists Θa, Θ2. split_and!; [by apply comp_comm|done|done].
  - destruct Hg as (Θa & Θr & Hc & HV & Hg).
    pose proof (Vrel_unl_empty _ _ _ _ _ HU HV) as ->.
    apply (tenv_comp_empty_l_inv _ _ _ Hs) in Hc as ->.
    destruct (IH _ _ Hg) as (Θ1 & Θ2 & Hc' & Hg1 & Hg2).
    exists Θ1, Θ2. split_and!; [done| |].
    + exists ∅, Θ1. split_and!; [by apply tenv_comp_empty_l|done|done].
    + exists ∅, Θ2. split_and!; [by apply tenv_comp_empty_l|done|done].
Qed.

Lemma grounding_lenv_empty n W Θ Δ γ : lenv_empty Δ → grounding n W Θ Δ γ → Θ = ∅.
Proof.
  revert Θ γ. induction Δ as [|o Δ IH]; intros Θ γ He Hg; simpl in *; [done|].
  destruct o as [T|].
  - exfalso. assert (Some T = None) by (apply He; set_solver). done.
  - apply (IH _ (γ ∘ S)); [|done]. intros o Ho. apply He. set_solver.
Qed.

Lemma grounding_only n W Θ Δ γ x T :
  world_wf W → lenv_only Δ x T → grounding n W Θ Δ γ → Vrel n W Θ T (γ x).
Proof.
  intros HW. assert (∀ x y, w_eq W x y → w_eq W y x) as Hs by apply (wf_eq_sym _ HW).
  revert Θ γ x. induction Δ as [|o Δ IH]; intros Θ γ x [Hx Honly] Hg; simpl in *.
  - done.
  - destruct x as [|x]; simpl in Hx.
    + injection Hx as ->. destruct Hg as (Θa & Θr & Hc & HV & Hg).
      assert (lenv_empty Δ) as He.
      { intros o Ho. destruct o as [U|]; [|done]. exfalso.
        apply list_elem_of_lookup in Ho as [i Hi].
        destruct (Honly (S i) U Hi) as [? _]. done. }
      rewrite (grounding_lenv_empty _ _ _ _ _ He Hg) in Hc.
      by apply tenv_comp_empty_r_inv in Hc as ->.
    + destruct o as [U|].
      * exfalso. by destruct (Honly 0 U eq_refl).
      * apply (IH Θ (γ ∘ S) x); [|done]. split; [done|].
        intros y T' Hy. destruct (Honly (S y) T' Hy) as [Hy' ->]. split; [congruence|done].
Qed.

(** ** Reductions that cost one β step *)

Lemma Erel_det_beta n W Θ T F e e' :
  tstep e LBeta e' → (∀ α e'', tstep e α e'' → α = LBeta ∧ e'' = e') →
  Erel n W Θ T F e' → Erel n W Θ T F e.
Proof.
  destruct n as [|n']; [intros; apply Erel_0|]. intros Hst Hdet HE.
  apply Erel_S_iff. split_and!.
  - intros Hirr. exfalso. exact (Hirr _ _ Hst).
  - intros _. split; intros Hs; exfalso; exact (Hs _ _ Hst).
  - intros α e'' Hst'. destruct (Hdet _ _ Hst') as [-> ->]. simpl.
    eapply Erel_down; [|exact HE]. lia.
Qed.

(** ** The rules without elimination of a function *)

Lemma sem_typed_unit W Δ F : lenv_empty Δ → sem_typed W ∅ Δ F EUnit TUnit.
Proof.
  intros He n W' Θ' Θ'' γ HW Hc Hg. rewrite (grounding_lenv_empty _ _ _ _ _ He Hg) in Hc.
  apply tenv_comp_empty_inv in Hc as ->. apply Vrel_Erel. by apply Vrel_unit_iff.
Qed.

Lemma teqW_refl W T : teqW W T T.
Proof. apply teq_teqW, teq_refl. Qed.

Lemma sem_typed_konst W Δ F k T :
  lenv_empty Δ → konst_ty (w_eq W) (w_lt W) (pt_known W) k T →
  sem_typed W ∅ Δ F (Konst k) T.
Proof.
  intros He Hk n W' Θ' Θ'' γ HW Hc Hg. rewrite (grounding_lenv_empty _ _ _ _ _ He Hg) in Hc.
  apply tenv_comp_empty_inv in Hc as ->. apply Vrel_Erel. simpl.
  destruct HW as (Hn & Heq & Hlt & _).
  assert (konst_ty (w_eq W') (w_lt W') (pt_known W') k T) as Hk'.
  { eapply konst_ty_mono; [| | |exact Hk]; [done|done|]. unfold pt_known. intros x Hx. by apply Hn. }
  destruct Hk'; apply Vrel_lolli_iff; right; eexists _, _; (split_and!; [done|done| |apply teqW_refl]);
    by econstructor.
Qed.

Lemma sem_typed_var W Δ F x T : lenv_only Δ x T → sem_typed W ∅ Δ F (Var x) T.
Proof.
  intros Ho n W' Θ' Θ'' γ HW Hc Hg. simpl.
  pose proof (wf_eq_sym _ (proj1 (proj2 (proj2 (proj2 HW))))) as Hs.
  apply (tenv_comp_empty_l_inv _ _ _ Hs) in Hc as ->.
  apply Vrel_Erel. eapply grounding_only; [apply HW|done|done].
Qed.

Lemma sem_typed_chan W Δ F c s k s' y :
  lenv_empty Δ → seq s s' → w_eq W k y →
  sem_typed W {[c := One (s, k)]} Δ F (Chan c) (TSess s' y).
Proof.
  intros He Hs Hk n W' Θ' Θ'' γ HW Hc Hg. rewrite (grounding_lenv_empty _ _ _ _ _ He Hg) in Hc.
  apply tenv_comp_empty_r_inv in Hc as ->. apply Vrel_Erel. simpl.
  apply Vrel_sess_iff. exists c, s, k. split_and!; [done|done|done|]. by apply (proj1 (proj2 HW)).
Qed.

Lemma grounding_ext n W Θ Δ γ γ' :
  (∀ i, γ i = γ' i) → grounding n W Θ Δ γ → grounding n W Θ Δ γ'.
Proof.
  revert Θ γ γ'. induction Δ as [|[T|] Δ IH]; intros Θ γ γ' Hγ Hg; simpl in *; [done| |].
  - destruct Hg as (Θ1 & Θ2 & Hc & HV & Hg). exists Θ1, Θ2. split_and!; [done|by rewrite <-Hγ|].
    eapply IH; [|exact Hg]. intros i. apply Hγ.
  - eapply IH; [|exact Hg]. intros i. apply Hγ.
Qed.

Lemma wext_sym W W' : wext W W' → ∀ x y, w_eq W' x y → w_eq W' y x.
Proof. intros HW. apply (wf_eq_sym _ (wext_wf _ _ HW)). Qed.

(** ** The elimination skeleton

    Θ1; Δ1 ⊨^{F ∪ heads(Θ2, Δ2)} e1 : Th, and a continuation that
    takes the value of e1 together with a grounding of Δ2, give the
    composite. One instance per elimination rule. *)

Lemma sem_elim W Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 Th T (f : (nat → expr) → frame) :
  tenv_comp (w_eq W) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 → (∀ γ, frame_val (f γ)) →
  sem_typed W Θ1 Δ1 (F ∪ (tenv_heads Θ2 ∪ lenv_heads Δ2)) e1 Th →
  (∀ n W' Θ' Θ'' γ, wext W W' → tenv_comp (w_eq W') Θ'' Θ2 Θ' → grounding n W' Θ' Δ2 γ →
     ∀ W'' j Θ1' Θ3 v, wext W' W'' → j ≤ n → tenv_comp (w_eq W'') Θ3 Θ1' Θ'' →
       Vrel j W'' Θ1' Th v → Erel j W'' Θ3 T F (fill_frame (f γ) v)) →
  ∀ n W' Θ' Θ'' γ, wext W W' → tenv_comp (w_eq W') Θ'' Θ Θ' → grounding n W' Θ' Δ γ →
    Erel n W' Θ'' T F (fill_frame (f γ) (subst γ e1)).
Proof.
  intros Hc Hsp Hf He1 HK n W' Θ' Θ'' γ HW Hc'' Hg.
  pose proof (wext_wf _ _ HW) as HW'. pose proof (wext_sym _ _ HW) as Hs.
  destruct (grounding_split _ _ _ _ _ _ _ HW' Hsp Hg) as (Θ'1 & Θ'2 & Hc' & Hg1 & Hg2).
  pose proof (tenv_comp_mono _ _ _ _ _ (proj1 (proj2 HW)) Hc) as HcW.
  destruct (comp_swap4 _ _ _ _ _ _ _ _ Hs Hc'' HcW Hc') as (A & B & HAB & HA & HB).
  eapply (Erel_bind n (f γ) W' Θ'' A B Th T F (tenv_heads Θ2 ∪ lenv_heads Δ2)).
  - apply Hf.
  - apply HW.
  - done.
  - eapply heads_above_comp; [exact HB|by apply heads_above_self|by eapply grounding_heads].
  - by apply (He1 n W' Θ'1 A γ).
  - intros W'' j Θ1' Θ3 v HW'' Hj Hc3 HV. by eapply (HK n W' Θ'2 B γ).
Qed.

(** ** E-Inj *)

Lemma sem_typed_inj1 W Θ Δ F e T U :
  sem_typed W Θ Δ F e T → sem_typed W Θ Δ F (Inj1 e) (TSum T U).
Proof.
  intros He n W' Θ' Θ'' γ HW Hc Hg. simpl.
  change (Inj1 (subst γ e)) with (fill_frame FInj1 (subst γ e)).
  eapply (Erel_bind n FInj1 W' Θ'' Θ'' ∅ T _ F ∅); [done|apply HW|apply tenv_comp_empty_r|
    apply heads_above_empty|rewrite (right_id_L ∅ (∪)); by eapply He|].
  intros W'' j Θ1' Θ3 v HW'' Hj Hc3 HV.
  apply tenv_comp_empty_r_inv in Hc3 as ->. apply Vrel_Erel. simpl.
  apply Vrel_sum_iff. left. eauto.
Qed.

Lemma sem_typed_inj2 W Θ Δ F e T U :
  sem_typed W Θ Δ F e U → sem_typed W Θ Δ F (Inj2 e) (TSum T U).
Proof.
  intros He n W' Θ' Θ'' γ HW Hc Hg. simpl.
  change (Inj2 (subst γ e)) with (fill_frame FInj2 (subst γ e)).
  eapply (Erel_bind n FInj2 W' Θ'' Θ'' ∅ U _ F ∅); [done|apply HW|apply tenv_comp_empty_r|
    apply heads_above_empty|rewrite (right_id_L ∅ (∪)); by eapply He|].
  intros W'' j Θ1' Θ3 v HW'' Hj Hc3 HV.
  apply tenv_comp_empty_r_inv in Hc3 as ->. apply Vrel_Erel. simpl.
  apply Vrel_sum_iff. right. eauto.
Qed.

(** Moving the second premise of an elimination rule to a later world
    and a lower index. *)
Lemma sem_typed_later W Θ2 Δ2 F e T n W' Θ' Θ'' γ W'' j :
  sem_typed W Θ2 Δ2 F e T → wext W W' → tenv_comp (w_eq W') Θ'' Θ2 Θ' →
  grounding n W' Θ' Δ2 γ → wext W' W'' → j ≤ n →
  Erel j W'' Θ'' T F (subst γ e).
Proof.
  intros He HW Hc Hg HW'' Hj. apply (He j W'' Θ' Θ'' γ).
  - by eapply wext_trans.
  - eapply tenv_comp_mono; [|exact Hc]. apply HW''.
  - eapply grounding_down; [exact Hj|]. eapply grounding_mono; [|exact HW''|exact Hg].
    exact (wext_wf _ _ HW).
Qed.

(** ** E-Let* *)

Lemma sem_typed_letu W Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T :
  tenv_comp (w_eq W) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
  sem_typed W Θ1 Δ1 (F ∪ (tenv_heads Θ2 ∪ lenv_heads Δ2)) e1 TUnit →
  sem_typed W Θ2 Δ2 F e2 T →
  sem_typed W Θ Δ F (LetU e1 e2) T.
Proof.
  intros Hc Hsp He1 He2 n W' Θ' Θ'' γ HW Hc'' Hg. simpl.
  change (LetU (subst γ e1) (subst γ e2)) with (fill_frame (FLetU (subst γ e2)) (subst γ e1)).
  eapply (sem_elim W Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 TUnit T (λ γ, FLetU (subst γ e2)));
    [done|done|done|done| |done|done|done].
  clear dependent Θ' Θ'' n γ W'.
  intros n W' Θ' Θ'' γ HW Hc' Hg W'' j Θ1' Θ3 v HW'' Hj Hc3 HV. simpl.
  apply Vrel_unit_iff in HV as [-> ->].
  apply (tenv_comp_empty_l_inv _ _ _ (wext_sym _ _ (wext_trans _ _ _ HW HW''))) in Hc3 as ->.
  apply (Erel_det_beta _ _ _ _ _ _ (subst γ e2)).
  - apply TStepHead, HeadLetU.
  - intros α e'' Hst. apply tstep_letu_inv in Hst as [(e1' & Hst & _)|(_ & -> & ->)]; [|done].
    exfalso. by eapply val_no_tstep.
  - by eapply sem_typed_later.
Qed.

(** Rearranging the environment of a let-bound value: Θ3 = Θ1', B with
    Θ1' = Θa, Θb and B = Θ2, Θ'2 gives Θ3 = Θ2, X with X = Θb, A and
    A = Θa, Θ'2. *)
Lemma comp_bind2 R Θ3 Θ1' B Θa Θb Θ2 Θ'2 :
  (∀ x y, R x y → R y x) →
  tenv_comp R Θ3 Θ1' B → tenv_comp R Θ1' Θa Θb → tenv_comp R B Θ2 Θ'2 →
  ∃ X A, tenv_comp R Θ3 Θ2 X ∧ tenv_comp R X Θb A ∧ tenv_comp R A Θa Θ'2.
Proof.
  intros Hs Hc HcA HcB.
  destruct (comp_swap4 _ _ _ _ _ _ _ _ Hs Hc HcA (comp_comm _ _ _ _ Hs HcB))
    as (A & B' & H1 & H2 & H3).
  destruct (comp_assoc _ _ _ _ _ _ Hs (comp_comm _ _ _ _ Hs H1) H3) as [HX HY].
  eexists _, A. split_and!; [by apply comp_comm|exact HX|done].
Qed.

(** ** E-LetPair *)

Lemma sem_typed_letp W Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T1 T2 T :
  tenv_comp (w_eq W) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
  sem_typed W Θ1 Δ1 (F ∪ (tenv_heads Θ2 ∪ lenv_heads Δ2)) e1 (TProd T1 T2) →
  sem_typed W Θ2 (Some T2 :: Some T1 :: Δ2) F e2 T →
  sem_typed W Θ Δ F (LetP e1 e2) T.
Proof.
  intros Hc Hsp He1 He2 n W' Θ' Θ'' γ HW Hc'' Hg. simpl.
  change (LetP (subst γ e1) (subst (up (up γ)) e2))
    with (fill_frame (FLetP (subst (up (up γ)) e2)) (subst γ e1)).
  eapply (sem_elim W Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 (TProd T1 T2) T (λ γ, FLetP (subst (up (up γ)) e2)));
    [done|done|done|done| |done|done|done].
  clear dependent Θ' Θ'' n γ W'.
  intros n W' Θ' Θ'' γ HW Hc' Hg W'' j Θ1' Θ3 v HW'' Hj Hc3 HV. simpl.
  pose proof (wext_trans _ _ _ HW HW'') as HW2.
  apply Vrel_prod_iff in HV as (v1 & v2 & Θa & Θb & -> & Hcab & HV1 & HV2).
  pose proof (Vrel_val _ _ _ _ _ HV1) as Hv1. pose proof (Vrel_val _ _ _ _ _ HV2) as Hv2.
  pose proof (tenv_comp_mono _ _ _ _ _ (proj1 (proj2 HW'')) Hc') as Hc'W.
  destruct (comp_bind2 _ _ _ _ _ _ _ _ (wext_sym _ _ HW2) Hc3 Hcab Hc'W) as (X & A & HX & HXA & HA).
  apply (Erel_det_beta _ _ _ _ _ _ (subst2 v1 v2 (subst (up (up γ)) e2))).
  - by apply TStepHead, HeadLetP.
  - intros α e'' Hst. apply tstep_letp_inv in Hst as [(e1' & Hst & _)|(u & w & Heq & _ & _ & -> & ->)].
    + exfalso. eapply val_no_tstep; [exact Hst|]. simpl. by apply andb_True.
    + by injection Heq as -> ->.
  - rewrite subst2_subst. apply (He2 j W'' X Θ3); [done|done|].
    exists Θb, A. split_and!; [done|done|].
    exists Θa, Θ'. split_and!; [done|done|].
    eapply grounding_ext; [|eapply grounding_down; [exact Hj|]].
    { intros i. done. }
    eapply grounding_mono; [exact (wext_wf _ _ HW)|exact HW''|exact Hg].
Qed.

(** ** E-Case *)

Lemma sem_typed_case W Θ Θ1 Θ2 Δ Δ1 Δ2 F e e1 e2 T1 T2 T :
  tenv_comp (w_eq W) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
  sem_typed W Θ1 Δ1 (F ∪ (tenv_heads Θ2 ∪ lenv_heads Δ2)) e (TSum T1 T2) →
  sem_typed W Θ2 (Some T1 :: Δ2) F e1 T →
  sem_typed W Θ2 (Some T2 :: Δ2) F e2 T →
  sem_typed W Θ Δ F (Case e e1 e2) T.
Proof.
  intros Hc Hsp He He1 He2 n W' Θ' Θ'' γ HW Hc'' Hg. simpl.
  change (Case (subst γ e) (subst (up γ) e1) (subst (up γ) e2))
    with (fill_frame (FCase (subst (up γ) e1) (subst (up γ) e2)) (subst γ e)).
  eapply (sem_elim W Θ Θ1 Θ2 Δ Δ1 Δ2 F e (TSum T1 T2) T
            (λ γ, FCase (subst (up γ) e1) (subst (up γ) e2)));
    [done|done|done|done| |done|done|done].
  clear dependent Θ' Θ'' n γ W'.
  intros n W' Θ' Θ'' γ HW Hc' Hg W'' j Θ1' Θ3 v HW'' Hj Hc3 HV. simpl.
  pose proof (wext_trans _ _ _ HW HW'') as HW2. pose proof (wext_sym _ _ HW2) as Hs.
  pose proof (tenv_comp_mono _ _ _ _ _ (proj1 (proj2 HW'')) Hc') as Hc'W.
  (* Θ3 = Θ2, X with X = Θ1', Θ' *)
  destruct (comp_assoc _ _ _ _ _ _ Hs (comp_comm _ _ _ _ Hs Hc3) (comp_comm _ _ _ _ Hs Hc'W))
    as [HX HY].
  assert (grounding j W'' Θ' Δ2 γ) as Hg'.
  { eapply grounding_down; [exact Hj|].
    eapply grounding_mono; [exact (wext_wf _ _ HW)|exact HW''|exact Hg]. }
  apply Vrel_sum_iff in HV as [(w & -> & HVw)|(w & -> & HVw)];
    pose proof (Vrel_val _ _ _ _ _ HVw) as Hw.
  - apply (Erel_det_beta _ _ _ _ _ _ (subst1 w (subst (up γ) e1))).
    + by apply TStepHead, HeadCase1.
    + intros α e'' Hst. apply tstep_case_inv in Hst
        as [(e' & Hst & _)|[(u & Heq & _ & -> & ->)|(u & Heq & _)]]; [|by injection Heq as ->|done].
      exfalso. by eapply val_no_tstep.
    + rewrite subst1_subst. apply (He1 j W'' (tjoin_as Θ3 Θ' Θ1') Θ3); [done|by apply comp_comm|].
      exists Θ1', Θ'. split_and!; [by apply comp_comm|done|].
      eapply grounding_ext; [|exact Hg']. done.
  - apply (Erel_det_beta _ _ _ _ _ _ (subst1 w (subst (up γ) e2))).
    + by apply TStepHead, HeadCase2.
    + intros α e'' Hst. apply tstep_case_inv in Hst
        as [(e' & Hst & _)|[(u & Heq & _)|(u & Heq & _ & -> & ->)]]; [|done|by injection Heq as ->].
      exfalso. by eapply val_no_tstep.
    + rewrite subst1_subst. apply (He2 j W'' (tjoin_as Θ3 Θ' Θ1') Θ3); [done|by apply comp_comm|].
      exists Θ1', Θ'. split_and!; [by apply comp_comm|done|].
      eapply grounding_ext; [|exact Hg']. done.
Qed.

(** ** E-Pair *)

Lemma sem_typed_pair W Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 T U :
  tenv_comp (w_eq W) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 →
  sem_typed W Θ1 Δ1 (F ∪ (tenv_heads Θ2 ∪ lenv_heads Δ2)) e1 T →
  sem_typed W Θ2 Δ2 (F ∪ heads T) e2 U →
  sem_typed W Θ Δ F (Pair e1 e2) (TProd T U).
Proof.
  intros Hc Hsp He1 He2 n W' Θ' Θ'' γ HW Hc'' Hg. simpl.
  change (Pair (subst γ e1) (subst γ e2)) with (fill_frame (FPairL (subst γ e2)) (subst γ e1)).
  eapply (sem_elim W Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 T (TProd T U) (λ γ, FPairL (subst γ e2)));
    [done|done|done|done| |done|done|done].
  clear dependent Θ' Θ'' n γ W'.
  intros n W' Θ' Θ'' γ HW Hc' Hg W'' j Θ1' Θ3 v1 HW'' Hj Hc3 HV1. simpl.
  pose proof (wext_trans _ _ _ HW HW'') as HW2. pose proof (wext_sym _ _ HW2) as Hs.
  pose proof (Vrel_val _ _ _ _ _ HV1) as Hv1.
  change (Pair v1 (subst γ e2)) with (fill_frame (FPairR v1) (subst γ e2)).
  eapply (Erel_bind j (FPairR v1) W'' Θ3 Θ'' Θ1' U (TProd T U) F (heads T)).
  - done.
  - apply HW''.
  - by apply comp_comm.
  - eapply Vrel_heads_above; [exact (wext_wf _ _ HW2)|exact HV1].
  - exact (sem_typed_later _ _ _ _ _ _ n W' Θ' Θ'' γ W'' j He2 HW Hc' Hg HW'' Hj).
  - intros W3 j' Θ2' Θ4 v2 HW3 Hj' Hc4 HV2. apply Vrel_Erel. simpl.
    apply Vrel_prod_iff. exists v1, v2, Θ1', Θ2'. split_and!; [done| | |done].
    { apply comp_comm; [exact (wext_sym _ _ (wext_trans _ _ _ HW2 HW3))|exact Hc4]. }
    eapply Vrel_down; [exact Hj'|]. eapply Vrel_mono; [exact (wext_wf _ _ HW2)|exact HW3|exact HV1].
Qed.

(** ** Channels of a grounding *)

Lemma grounding_fchans n W Θ Δ γ x T :
  grounding n W Θ Δ γ → Δ !! x = Some (Some T) → fchans (γ x) ⊆ dom Θ.
Proof.
  revert Θ γ x. induction Δ as [|[T0|] Δ IH]; intros Θ γ x Hg Hx; simpl in *; [done| |].
  - destruct Hg as (Θ1 & Θ2 & [Hj _] & HV & Hg). rewrite (tenv_join_dom _ _ _ Hj).
    destruct x as [|x]; simpl in Hx.
    + rewrite (Vrel_fchans _ _ _ _ _ HV). set_solver.
    + pose proof (IH _ _ _ Hg Hx). set_solver.
  - destruct x as [|x]; simpl in Hx; [done|]. exact (IH _ _ _ Hg Hx).
Qed.

Lemma grounding_dom n W Θ Δ γ ch :
  grounding n W Θ Δ γ → ch ∈ dom Θ →
  ∃ x T, Δ !! x = Some (Some T) ∧ ¬ unlimited T ∧ ch ∈ fchans (γ x).
Proof.
  revert Θ γ. induction Δ as [|[T0|] Δ IH]; intros Θ γ Hg Hch; simpl in *.
  - subst. rewrite dom_empty_L in Hch. set_solver.
  - destruct Hg as (Θ1 & Θ2 & [Hj _] & HV & Hg). rewrite (tenv_join_dom _ _ _ Hj) in Hch.
    apply elem_of_union in Hch as [Hch|Hch].
    + exists 0, T0. split_and!; [done| |].
      * intros Hu. rewrite (Vrel_unl_empty _ _ _ _ _ Hu HV), dom_empty_L in Hch. set_solver.
      * by rewrite (Vrel_fchans _ _ _ _ _ HV).
    + destruct (IH _ _ Hg Hch) as (x & T & ? & ? & ?). by exists (S x), T.
  - destruct (IH _ _ Hg Hch) as (x & T & ? & ? & ?). by exists (S x), T.
Qed.

Lemma le_le_W W x y z : world_wf W → w_le W x y → w_le W y z → w_le W x z.
Proof.
  intros HW Hxy [Hyz|Hyz]; [by eapply eq_le_W|]. right.
  destruct Hxy as [Hxy|Hxy].
  - eapply (wf_lt_eq _ HW); [exact Hxy|exact Hyz|apply HW].
  - eapply (wf_lt_trans _ HW); eauto.
Qed.

(** ** E-Abs *)

Lemma sem_typed_lam W Θ Δ F e T U ub lb :
  term_wf Θ (Some T :: Δ) e →
  lb_below W lb (tenv_heads Θ ∪ lenv_heads Δ) →
  (∀ W1 F', wext W W1 → ub_below W1 ub F' → sem_typed W1 Θ (Some T :: Δ) F' e U) →
  sem_typed W Θ Δ F (Lam e) (TLolli ub lb T U).
Proof.
  intros (Hfc & Hfv & Hrel) Hlb He n W' Θ' Θ'' γ HW Hc Hg. simpl.
  pose proof (wext_wf _ _ HW) as HW'. pose proof (wext_sym _ _ HW) as Hs.
  apply Vrel_Erel, Vrel_lolli_iff. left. exists (subst (up γ) e). split_and!; [done| | |].
  - rewrite (tenv_join_dom _ _ _ (proj1 Hc)). apply set_eq. intros ch. split.
    + intros Hch.
      assert (fchans (subst (up γ) e) ⊆ fchans e ∪ dom Θ') as Hsub.
      { apply fchans_subst. eapply allfv_mono; [|exact Hfv]. intros [|x]; simpl.
        - intros _. set_solver.
        - intros (T' & Hx). unfold compose. rewrite fchans_rename. by eapply grounding_fchans. }
      rewrite <-Hfc. set_solver.
    + intros [Hch|Hch]%elem_of_union.
      * apply fchans_subst_super. by rewrite Hfc.
      * destruct (grounding_dom _ _ _ _ _ _ Hg Hch) as (x & T' & Hx & Hu & Hin).
        assert (freevar (S x) e) as Hfree by (apply Hrel; by exists T').
        pose proof (fchans_subst_free e (S x) (up γ) Hfree) as Hsub. simpl in Hsub.
        unfold compose in Hsub. rewrite fchans_rename in Hsub. set_solver.
  - assert (∀ h, h ∈ tenv_heads Θ'' → (h ∈ tenv_heads Θ ∨ ∃ h', h' ∈ lenv_heads Δ ∧ w_le W' h' h))
      as Hh.
    { intros h (k & e0 & He0 & ->)%elem_of_tenv_heads_entry.
      destruct (comp_entry _ _ _ _ _ _ Hc He0) as [[k' Hk]|[k' Hk]].
      - left. apply elem_of_tenv_heads_entry. eauto.
      - right. exact (grounding_heads _ _ _ _ _ HW' Hg _ _ Hk). }
    pose proof (lb_below_mono _ _ _ _ HW Hlb) as Hlb'.
    destruct lb as [l|]; simpl in *.
    + intros h Hin. destruct (Hh h Hin) as [Hin'|(h' & Hh' & Hle)].
      * apply Hlb'. set_solver.
      * eapply le_le_W; [exact HW'| |exact Hle]. apply Hlb'. set_solver.
    + apply set_eq. intros h. split; [|set_solver]. intros Hin.
      destruct (Hh h Hin) as [Hin'|(h' & Hh' & _)]; set_solver.
  - intros W2 j Θa Θb w F' HW2 Hj Hcb HVw Hub. rewrite subst1_subst.
    pose proof (wext_trans _ _ _ HW HW2) as HWW2. pose proof (wext_sym _ _ HWW2) as Hs2.
    pose proof (tenv_comp_mono _ _ _ _ _ (proj1 (proj2 HW2)) Hc) as HcW2.
    destruct (comp_assoc _ _ _ _ _ _ Hs2 Hcb (comp_comm _ _ _ _ Hs2 HcW2)) as [HX HY].
    apply (He W2 F' HWW2 Hub j W2 (tjoin_as Θb Θ' Θa) Θb).
    + by apply wext_refl, HWW2.
    + by apply comp_comm.
    + exists Θa, Θ'. split_and!; [by apply comp_comm|done|].
      eapply grounding_ext; [|eapply grounding_down; [|eapply grounding_mono; [exact HW'|exact HW2|exact Hg]]].
      * done.
      * lia.
Qed.
