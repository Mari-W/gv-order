(** * Compositionality of the term rules (spec §11)

    One lemma per typing rule of §9, on top of the bind lemma
    (Bind.v). The elimination rules run their head subterm under the
    future F ∪ H, where H holds the heads of the rest of the term. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export rules.Bind relation.Creation.

(** Branch no-eq: [w_eq W] abbreviates equality and leaves W untyped. *)
Implicit Types W : world.


Set Default Proof Using "All".

(** ** Heads of values

    The semantic condition behind the futures of E-App and E-Pair: the
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
  intros HW k e He. exists (pt_dual e.2). split; [|left; apply (wf_eq_refl _ HW)].
  apply elem_of_tenv_heads_entry. eauto.
Qed.

Lemma Vrel_heads_above n W Θ T v :
  world_wf W → hbot T = false → Vrel n W Θ T v → heads_above W (heads T) Θ.
Proof.
  intros HW. revert Θ v.
  induction T as [|ub lb T1 IH1 T2 IH2|T1 IH1 T2 IH2|T1 IH1 T2 IH2|m kk C T1 IH1|s x|lb m C T1 IH1|x];
    intros Θ v Hb HV; simpl; simpl in Hb; try apply orb_false_iff in Hb as [Hb1 Hb2].
  - apply Vrel_unit_iff in HV as [-> _]. apply heads_above_empty.
  - apply Vrel_lolli_iff in HV as [(eb & _ & _ & Hlb & _)|(k & T0 & _ & -> & _)];
      [|apply heads_above_empty].
    intros k e He. destruct lb as [l|]; simpl in Hlb.
    + exists l. split; [set_solver|]. apply Hlb. apply elem_of_tenv_heads_entry. eauto.
    + exfalso. assert (pt_dual e.2 ∈ tenv_heads Θ) as Hin by (apply elem_of_tenv_heads_entry; eauto).
      rewrite Hlb in Hin. set_solver.
  - apply Vrel_prod_iff in HV as (v1 & v2 & Θ1 & Θ2 & _ & Hc & H1 & H2).
    eapply heads_above_comp; [exact Hc|eauto|eauto].
  - apply Vrel_sum_iff in HV as [(v' & _ & H)|(v' & _ & H)].
    + eapply heads_above_sub; [|by eapply IH1]. set_solver.
    + eapply heads_above_sub; [|by eapply IH2]. set_solver.
  - apply Vrel_box_empty in HV as ->. apply heads_above_empty.
  - apply Vrel_sess_iff in HV as (c & bb & s0 & k & _ & -> & _ & Hk & _).
    intros [c' b] e He. unfold tenv_entry in He. simpl in He.
    destruct (decide (c' = c)) as [->|Hne].
    + rewrite lookup_singleton_eq in He. destruct b; simplify_eq.
      exists (pt_dual x). split; [set_solver|]. left. apply (wf_eq_dual _ HW). by apply (wf_eq_sym _ HW).
    + rewrite lookup_singleton_ne in He by done. done.
  - apply Vrel_ex_iff in HV as [Hlb _].
    intros k e He. destruct lb as [| |l]; simpl in Hlb, Hb; [|done|].
    + exfalso. assert (pt_dual e.2 ∈ tenv_heads Θ) as Hin by (apply elem_of_tenv_heads_entry; eauto).
      rewrite (proj1 Hlb) in Hin. set_solver.
    + exists l. split; [set_solver|]. apply Hlb. apply elem_of_tenv_heads_entry. eauto.
  - apply Vrel_pt_iff in HV as [-> _]. apply heads_above_empty.
Qed.

(** ** Grounding substitutions *)

Fixpoint lenv_heads (Δ : lenv) : gset point :=
  match Δ with
  | [] => ∅
  | None :: Δ' => lenv_heads Δ'
  | Some T :: Δ' => heads T ∪ lenv_heads Δ'
  end.

(** The ⊥ flag of an environment (sharp edges 103). *)
Fixpoint lenv_bot (Δ : lenv) : bool :=
  match Δ with
  | [] => false
  | None :: Δ' => lenv_bot Δ'
  | Some T :: Δ' => hbot T || lenv_bot Δ'
  end.

Lemma grounding_heads n W Θ Δ γ :
  world_wf W → lenv_bot Δ = false → grounding n W Θ Δ γ → heads_above W (lenv_heads Δ) Θ.
Proof.
  intros HW. revert Θ γ. induction Δ as [|[T|] Δ IH]; intros Θ γ Hb Hg; simpl in *.
  - subst. apply heads_above_empty.
  - apply orb_false_iff in Hb as [Hb1 Hb2]. destruct Hg as (Θ1 & Θ2 & Hc & HV & Hg).
    eapply heads_above_comp; [exact Hc|by eapply Vrel_heads_above|by eapply IH].
  - by eapply IH.
Qed.

(** With the flag, the future holds [pbot]. *)
Lemma heads_above_x_bot W H b Θ :
  (b = false → heads_above W H Θ) → heads_above_x W (H ∪ bot_pts b) Θ.
Proof.
  intros Hh. destruct b; simpl.
  - right. set_solver.
  - left. eapply heads_above_sub; [|by apply Hh]. set_solver.
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

Lemma tenv_comp_empty_l R Θ : rdsym R → tenv_comp R Θ ∅ Θ.
Proof. intros Hs. apply comp_comm; [done|]. apply tenv_comp_empty_r. Qed.

Lemma tenv_comp_empty_l_inv R Θ Θ2 : rdsym R → tenv_comp R Θ ∅ Θ2 → Θ = Θ2.
Proof. intros Hs Hc. by eapply tenv_comp_empty_r_inv, comp_comm. Qed.

Lemma tenv_comp_empty_inv R Θ : tenv_comp R Θ ∅ ∅ → Θ = ∅.
Proof. apply tenv_comp_empty_r_inv. Qed.

(** (Θ1, Θ2), (Θ1', Θ2') = (Θ1, Θ1'), (Θ2, Θ2'). *)
Lemma comp_swap4 R Θ'' Θ Θ' Θ1 Θ2 Θ1' Θ2' :
  rdsym R →
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
  intros HW Hsp. assert (rdsym (w_eq W)) as Hs by apply eq_rdsym.
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
  intros HW. assert (rdsym (w_eq W)) as Hs by apply eq_rdsym.
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
  - intros _ Hs. exfalso. exact (Hs _ _ Hst).
  - intros α e'' Hst'. destruct (Hdet _ _ Hst') as [-> ->]. simpl.
    eapply Erel_down; [|exact HE]. lia.
Qed.

Lemma Erel_det_beta_S n W Θ T F e e' :
  tstep e LBeta e' → (∀ α e'', tstep e α e'' → α = LBeta ∧ e'' = e') →
  Erel n W Θ T F e' → Erel (S n) W Θ T F e.
Proof.
  intros Hst Hdet HE. apply Erel_S_iff. split_and!.
  - intros Hirr. exfalso. exact (Hirr _ _ Hst).
  - intros _ Hs. exfalso. exact (Hs _ _ Hst).
  - intros α e'' Hst'. destruct (Hdet _ _ Hst') as [-> ->]. exact HE.
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
  assert (∃ ub lb A B, T = TLolli ub lb A B) as (ub & lb & A & B & ->)
    by (destruct Hk' as [? ? ? ? Hs ? ?| | |]; [destruct Hs| | |]; eauto).
  apply Vrel_lolli_iff; right; eexists _, _; split_and!; [done|done|exact Hk'|apply teqW_refl].
Qed.

Lemma sem_typed_var W Δ F x T : lenv_only Δ x T → sem_typed W ∅ Δ F (Var x) T.
Proof.
  intros Ho n W' Θ' Θ'' γ HW Hc Hg. simpl.
  pose proof (wf_rdsym _ (proj1 (proj2 (proj2 (proj2 HW))))) as Hs.
  apply (tenv_comp_empty_l_inv _ _ _ Hs) in Hc as ->.
  apply Vrel_Erel. eapply grounding_only; [apply HW|done|done].
Qed.

Lemma sem_typed_chan W Δ F c b s k s' y :
  lenv_empty Δ → seq s s' → w_eq W k y → pt_pol k = b →
  sem_typed W {[c := One (s, k)]} Δ F (Chan c b) (TSess s' y).
Proof.
  intros He Hs Hk Hb n W' Θ' Θ'' γ HW Hc Hg. rewrite (grounding_lenv_empty _ _ _ _ _ He Hg) in Hc.
  apply tenv_comp_empty_r_inv in Hc as ->. apply Vrel_Erel. simpl.
  apply Vrel_sess_iff. exists c, b, s, k. split_and!; [done|done|done| |done].
  by apply (proj1 (proj2 HW)).
Qed.

(** The point value x at its singleton type [TPt x] (§16.4). *)
Lemma sem_typed_pt W Δ F x :
  lenv_empty Δ → pt_known W x → sem_typed W ∅ Δ F (EPt x) (TPt x).
Proof.
  intros He Hx n W' Θ' Θ'' γ HW Hc Hg. rewrite (grounding_lenv_empty _ _ _ _ _ He Hg) in Hc.
  apply tenv_comp_empty_inv in Hc as ->. apply Vrel_Erel. simpl.
  apply Vrel_pt_iff. split_and!; [done|done|]. unfold pt_known in *. by apply (proj1 HW).
Qed.

Lemma grounding_ext n W Θ Δ γ γ' :
  (∀ i, γ i = γ' i) → grounding n W Θ Δ γ → grounding n W Θ Δ γ'.
Proof.
  revert Θ γ γ'. induction Δ as [|[T|] Δ IH]; intros Θ γ γ' Hγ Hg; simpl in *; [done| |].
  - destruct Hg as (Θ1 & Θ2 & Hc & HV & Hg). exists Θ1, Θ2. split_and!; [done|by rewrite <-Hγ|].
    eapply IH; [|exact Hg]. intros i. apply Hγ.
  - eapply IH; [|exact Hg]. intros i. apply Hγ.
Qed.

Lemma wext_sym W W' : wext W W' → rdsym (w_eq W').
Proof. intros HW. apply eq_rdsym. Qed.

(** ** The elimination skeleton

    Θ1; Δ1 ⊨^{F ∪ heads(Θ2, Δ2)} e1 : Th, and a continuation that
    takes the value of e1 together with a grounding of Δ2, give the
    composite. One instance per elimination rule. *)

Lemma sem_elim W Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 Th T (f : (nat → expr) → frame) :
  tenv_comp (w_eq W) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 → (∀ γ, frame_val (f γ)) →
  sem_typed W Θ1 Δ1 (F ∪ (tenv_heads Θ2 ∪ lenv_heads Δ2 ∪ bot_pts (lenv_bot Δ2))) e1 Th →
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
  eapply (Erel_bind n (f γ) W' Θ'' A B Th T F (tenv_heads Θ2 ∪ lenv_heads Δ2 ∪ bot_pts (lenv_bot Δ2))).
  - apply Hf.
  - apply HW.
  - done.
  - apply heads_above_x_bot. intros Hb.
    eapply heads_above_comp; [exact HB|by apply heads_above_self|by eapply grounding_heads].
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
    left; apply heads_above_empty|rewrite (right_id_L ∅ (∪)); by eapply He|].
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
    left; apply heads_above_empty|rewrite (right_id_L ∅ (∪)); by eapply He|].
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
  sem_typed W Θ1 Δ1 (F ∪ (tenv_heads Θ2 ∪ lenv_heads Δ2 ∪ bot_pts (lenv_bot Δ2))) e1 TUnit →
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
  rdsym R →
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
  sem_typed W Θ1 Δ1 (F ∪ (tenv_heads Θ2 ∪ lenv_heads Δ2 ∪ bot_pts (lenv_bot Δ2))) e1 (TProd T1 T2) →
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
  sem_typed W Θ1 Δ1 (F ∪ (tenv_heads Θ2 ∪ lenv_heads Δ2 ∪ bot_pts (lenv_bot Δ2))) e (TSum T1 T2) →
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
  sem_typed W Θ1 Δ1 (F ∪ (tenv_heads Θ2 ∪ lenv_heads Δ2 ∪ bot_pts (lenv_bot Δ2))) e1 T →
  sem_typed W Θ2 Δ2 (F ∪ (heads T ∪ bot_pts (hbot T))) e2 U →
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
  eapply (Erel_bind j (FPairR v1) W'' Θ3 Θ'' Θ1' U (TProd T U) F (heads T ∪ bot_pts (hbot T))).
  - done.
  - apply HW''.
  - by apply comp_comm.
  - apply heads_above_x_bot. intros Hb. eapply Vrel_heads_above; [exact (wext_wf _ _ HW2)|exact Hb|exact HV1].
  - exact (sem_typed_later _ _ _ _ _ _ n W' Θ' Θ'' γ W'' j He2 HW Hc' Hg HW'' Hj).
  - intros W3 j' Θ2' Θ4 v2 HW3 Hj' Hc4 HV2. apply Vrel_Erel. simpl.
    apply Vrel_prod_iff. exists v1, v2, Θ1', Θ2'. split_and!; [done| | |done].
    { apply comp_comm; [exact (wext_sym _ _ (wext_trans _ _ _ HW2 HW3))|exact Hc4]. }
    eapply Vrel_down; [exact Hj'|]. eapply Vrel_mono; [exact (wext_wf _ _ HW2)|exact HW3|exact HV1].
Qed.

(** ** Channels of a grounding *)

Lemma grounding_fends n W Θ Δ γ x T :
  grounding n W Θ Δ γ → Δ !! x = Some (Some T) → fends (γ x) ⊆ tenv_ends Θ.
Proof.
  revert Θ γ x. induction Δ as [|[T0|] Δ IH]; intros Θ γ x Hg Hx; simpl in *; [done| |].
  - destruct Hg as (Θ1 & Θ2 & [Hj _] & HV & Hg). rewrite (tenv_join_ends _ _ _ Hj).
    destruct x as [|x]; simpl in Hx.
    + rewrite (Vrel_fends _ _ _ _ _ HV). set_solver.
    + pose proof (IH _ _ _ Hg Hx). set_solver.
  - destruct x as [|x]; simpl in Hx; [done|]. exact (IH _ _ _ Hg Hx).
Qed.

Lemma grounding_ends n W Θ Δ γ o :
  grounding n W Θ Δ γ → o ∈ tenv_ends Θ →
  ∃ x T, Δ !! x = Some (Some T) ∧ ¬ unlimited T ∧ o ∈ fends (γ x).
Proof.
  revert Θ γ. induction Δ as [|[T0|] Δ IH]; intros Θ γ Hg Ho; simpl in *.
  - subst. rewrite tenv_ends_empty in Ho. set_solver.
  - destruct Hg as (Θ1 & Θ2 & [Hj _] & HV & Hg). rewrite (tenv_join_ends _ _ _ Hj) in Ho.
    apply elem_of_union in Ho as [Ho|Ho].
    + exists 0, T0. split_and!; [done| |].
      * intros Hu. rewrite (Vrel_unl_empty _ _ _ _ _ Hu HV), tenv_ends_empty in Ho. set_solver.
      * by rewrite (Vrel_fends _ _ _ _ _ HV).
    + destruct (IH _ _ Hg Ho) as (x & T & ? & ? & ?). by exists (S x), T.
  - destruct (IH _ _ Hg Ho) as (x & T & ? & ? & ?). by exists (S x), T.
Qed.

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
  - eapply (wf_lt_eq _ HW); [exact Hxy|exact Hyz|reflexivity].
  - eapply (wf_lt_trans _ HW); eauto.
Qed.

(** ** E-Abs *)

Lemma sem_typed_lam W Θ Δ F e T U ub lb :
  term_wf Θ (Some T :: Δ) e →
  lenv_bot Δ = false →
  lb_below W lb (tenv_heads Θ ∪ lenv_heads Δ) →
  (∀ W1 F', wext W W1 → ub_below W1 ub F' → sem_typed W1 Θ (Some T :: Δ) F' e U) →
  sem_typed W Θ Δ F (Lam e) (TLolli ub lb T U).
Proof.
  intros (Hfc & Hfv & Hrel) Hbot Hlb He n W' Θ' Θ'' γ HW Hc Hg. simpl.
  pose proof (wext_wf _ _ HW) as HW'. pose proof (wext_sym _ _ HW) as Hs.
  apply Vrel_Erel, Vrel_lolli_iff. left. exists (subst (up γ) e). split_and!; [done| | |].
  - rewrite (tenv_join_ends _ _ _ (proj1 Hc)). apply set_eq. intros ch. split.
    + intros Hch.
      assert (fends (subst (up γ) e) ⊆ fends e ∪ tenv_ends Θ') as Hsub.
      { apply fends_subst. eapply allfv_mono; [|exact Hfv]. intros [|x]; simpl.
        - intros _. set_solver.
        - intros (T' & Hx). unfold compose. rewrite fends_rename. by eapply grounding_fends. }
      rewrite <-Hfc. set_solver.
    + intros [Hch|Hch]%elem_of_union.
      * apply fends_subst_super. by rewrite Hfc.
      * destruct (grounding_ends _ _ _ _ _ _ Hg Hch) as (x & T' & Hx & Hu & Hin).
        assert (freevar (S x) e) as Hfree by (apply Hrel; by exists T').
        pose proof (fends_subst_free e (S x) (up γ) Hfree) as Hsub. simpl in Hsub.
        unfold compose in Hsub. rewrite fends_rename in Hsub. set_solver.
  - assert (∀ h, h ∈ tenv_heads Θ'' → (h ∈ tenv_heads Θ ∨ ∃ h', h' ∈ lenv_heads Δ ∧ w_le W' h' h))
      as Hh.
    { intros h (k & e0 & He0 & ->)%elem_of_tenv_heads_entry.
      destruct (comp_entry _ _ _ _ _ _ Hc He0) as [[k' Hk]|[k' Hk]].
      - left. apply elem_of_tenv_heads_entry. eauto.
      - right. exact (grounding_heads _ _ _ _ _ HW' Hbot Hg _ _ Hk). }
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

(** ** Applying a value to a value

    One lemma per kind of function: a closure, and each constant but
    force (sharp edges 51). *)

Lemma app_val_step v1 v2 α e' :
  is_val v1 → is_val v2 → tstep (App v1 v2) α e' → head_step (App v1 v2) α e'.
Proof.
  intros H1 H2 Hst. apply tstep_app_inv in Hst as [(? & Hst & _)|[(_ & ? & Hst & _)|(_ & _ & H)]];
    [exfalso; by eapply val_no_tstep..|done].
Qed.

Lemma Erel_app_lam n W Θ Θ1 Θ2 ub lb T U F eb v2 :
  strict W → tenv_comp (w_eq W) Θ Θ1 Θ2 →
  Vrel n W Θ1 (TLolli ub lb T U) (Lam eb) → Vrel n W Θ2 T v2 → ub_below W ub F →
  Erel n W Θ U F (App (Lam eb) v2).
Proof.
  intros HW Hc HV1 HV2 Hub. pose proof (Vrel_val _ _ _ _ _ HV2) as Hv2.
  destruct n as [|n']; [apply Erel_0|].
  apply Vrel_lolli_iff in HV1 as [(eb' & Heq & _ & _ & HL)|(k & _ & Heq & _)]; [|done].
  injection Heq as <-.
  apply (Erel_det_beta_S _ _ _ _ _ _ (subst1 v2 eb)).
  - by apply TStepHead, HeadApp.
  - intros α e'' Hst. apply app_val_step in Hst; [|done|done]. by inversion Hst.
  - apply (HL W n' Θ2 Θ v2 F); [by apply wext_refl|lia|done| |done].
    eapply Vrel_down; [|exact HV2]. lia.
Qed.

Lemma konst_app_inv n W Θ1 Θ2 ub lb T U k v2 :
  world_wf W → Vrel n W Θ1 (TLolli ub lb T U) (Konst k) → Vrel n W Θ2 T v2 →
  Θ1 = ∅ ∧ ∃ ub0 lb0 A B, konst_ty (w_eq W) (w_lt W) (pt_known W) k (TLolli ub0 lb0 A B) ∧
    opt_rel (pteqW W) ub0 ub ∧ teqW W B U ∧ Vrel n W Θ2 A v2.
Proof.
  intros HW HV1 HV2.
  destruct (Vrel_konst_inv _ _ _ _ _ _ _ _ HV1) as (ub0 & lb0 & A & B & Hk & Hub & _ & HA & HB & ->).
  split; [done|]. exists ub0, lb0, A, B. split_and!; [done|done|done|].
  eapply Vrel_tconv; [done| |exact HV2]. by apply teqW_sym.
Qed.

Lemma Erel_app_new n W Θ ub lb T U F v2 :
  strict W → Vrel n W ∅ (TLolli ub lb T U) ENew → Vrel n W Θ T v2 →
  Erel n W Θ U F (App ENew v2).
Proof.
  intros HW HV1 HV2.
  destruct (konst_app_inv _ _ _ _ _ _ _ _ _ _ (proj1 HW) HV1 HV2)
    as (_ & ub0 & lb0 & A & B & Hk & Hub & HB & HV).
  inversion Hk as [kq Tq Gq xq Hsig| S x Hx| |]; subst; [inversion Hsig|].
  (* new@x (§16.1): the argument is the point value x, the label carries x *)
  apply Vrel_pt_iff in HV as (-> & -> & Hkx). destruct n as [|n']; [apply Erel_0|].
  assert (tstep (App ENew (EPt x)) (LNew "c" x)
            (Pair (Chan "c" (pt_pol x)) (Chan "c" (negb (pt_pol x))))) as Hst0
    by apply TStepHead, HeadNew.
  apply Erel_S_iff. split_and!.
  - intros Hirr. exfalso. exact (Hirr _ _ Hst0).
  - intros _ Hs. exfalso. exact (Hs _ _ Hst0).
  - intros α e' Hst. apply app_val_step in Hst; [|done|done].
    inversion Hst as [| | |c x0| | | | | | | | | | | | |]; subst. simpl. intros _.
    split; [done|]. exists S, (dual S). split_and!.
    + apply sdual_dual.
    + apply Vrel_Erel. eapply Vrel_tconv; [first [exact HW|exact (proj1 HW)]|exact HB|].
      apply Vrel_prod_iff. exists (Chan c (pt_pol x)), (Chan c (negb (pt_pol x))), {[c := One (S, x)]},
        {[c := One (dual S, pt_dual x)]}. split_and!.
      * done.
      * split.
        -- intros c'. rewrite insert_empty. destruct (decide (c' = c)) as [->|Hne].
           ++ rewrite !lookup_singleton_eq. constructor.
           ++ rewrite !lookup_singleton_ne by done. constructor.
        -- intros c' e1 e2 H1 H2. destruct (decide (c' = c)) as [->|Hne];
             [|by rewrite lookup_singleton_ne in H1].
           rewrite lookup_singleton_eq in H1, H2. simplify_eq. simpl.
           rewrite pt_dual_dual. split; [apply (wf_eq_refl _ (proj1 HW))|apply sdual_dual].
      * apply Vrel_sess_iff. exists c, (pt_pol x), S, x.
        split_and!; [done|done|apply seq_refl|apply (wf_eq_refl _ (proj1 HW))|done].
      * apply Vrel_sess_iff. exists c, (negb (pt_pol x)), (dual S), (pt_dual x).
        split_and!; [done|done|apply seq_refl|apply (wf_eq_refl _ (proj1 HW))|done].
Qed.

(** x[i] and x+1 on point values (§16.1): one β step each. *)
Lemma Erel_app_pay n W Θ ub lb T U F i v2 :
  strict W → Vrel n W ∅ (TLolli ub lb T U) (Konst (KPay i)) → Vrel n W Θ T v2 →
  Erel n W Θ U F (App (Konst (KPay i)) v2).
Proof.
  intros HW HV1 HV2.
  destruct (konst_app_inv _ _ _ _ _ _ _ _ _ _ (proj1 HW) HV1 HV2)
    as (_ & ub0 & lb0 & A & B & Hk & Hub & HB & HV).
  inversion Hk as [kq Tq Gq xq Hsig| |i0 x Hx|]; subst; [inversion Hsig|].
  apply Vrel_pt_iff in HV as (-> & -> & Hkx). destruct n as [|n']; [apply Erel_0|].
  eapply Erel_det_beta_S; [by apply TStepHead, HeadPay| |].
  - intros α e'' Hst. apply app_val_step in Hst; [|done|done]. by inversion Hst.
  - apply Vrel_Erel. eapply Vrel_tconv; [exact (proj1 HW)|exact HB|].
    by apply Vrel_pt_iff.
Qed.

Lemma Erel_app_succ n W Θ ub lb T U F v2 :
  strict W → Vrel n W ∅ (TLolli ub lb T U) (Konst KSucc) → Vrel n W Θ T v2 →
  Erel n W Θ U F (App (Konst KSucc) v2).
Proof.
  intros HW HV1 HV2.
  destruct (konst_app_inv _ _ _ _ _ _ _ _ _ _ (proj1 HW) HV1 HV2)
    as (_ & ub0 & lb0 & A & B & Hk & Hub & HB & HV).
  inversion Hk as [kq Tq Gq xq Hsig| | |x Hx]; subst; [inversion Hsig|].
  apply Vrel_pt_iff in HV as (-> & -> & Hkx). destruct n as [|n']; [apply Erel_0|].
  eapply Erel_det_beta_S; [by apply TStepHead, HeadSucc| |].
  - intros α e'' Hst. apply app_val_step in Hst; [|done|done]. by inversion Hst.
  - apply Vrel_Erel. eapply Vrel_tconv; [exact (proj1 HW)|exact HB|].
    by apply Vrel_pt_iff.
Qed.

Lemma Erel_app_spawn n W Θ ub lb T U F v2 :
  strict W → Vrel n W ∅ (TLolli ub lb T U) ESpawn → Vrel n W Θ T v2 →
  Erel n W Θ U F (App ESpawn v2).
Proof.
  intros HW HV1 HV2.
  destruct (konst_app_inv _ _ _ _ _ _ _ _ _ _ (proj1 HW) HV1 HV2)
    as (_ & ub0 & lb0 & A & B & Hk & Hub & HB & HV).
  inversion Hk as [kq Tq Gq xq Hsig _ _| | |]; subst. inversion Hsig as [ub1 lb1| | | | | | | |]; subst.
  pose proof (Vrel_val _ _ _ _ _ HV) as Hv.
  destruct n as [|n']; [apply Erel_0|].
  assert (tstep (App ESpawn v2) (LSpawn v2) EUnit) as Hst0 by by apply TStepHead, HeadSpawn.
  apply Erel_S_iff. split_and!.
  - intros Hirr. exfalso. exact (Hirr _ _ Hst0).
  - intros _ Hs. exfalso. exact (Hs _ _ Hst0).
  - intros α e' Hst. apply app_val_step in Hst; [|done|done].
    inversion Hst; subst. simpl.
    exists Θ, ∅, ub1, lb1. split_and!; [apply tenv_comp_empty_r|done|].
    apply Vrel_Erel. eapply Vrel_tconv; [apply HW|exact HB|]. by apply Vrel_unit_iff.
Qed.

(** Readiness and future of a term holding one end, which it offers. *)
Lemma entry_single c o k' e' :
  tenv_entry {[c := One o]} k' = Some e' → k' = (c, false) ∧ e' = o.
Proof.
  destruct k' as [c' b]. unfold tenv_entry. simpl.
  destruct (decide (c' = c)) as [->|Hne].
  - rewrite lookup_singleton_eq. destruct b; intros; simplify_eq. done.
  - by rewrite lookup_singleton_ne.
Qed.

Lemma ready_single W c o e F :
  offered_t {[c := One o]} e (c, false) → (∀ y, y ∈ F → w_lt W o.2 y) →
  ready_t W {[c := One o]} F e.
Proof.
  intros Hoff HF Hs. split.
  - intros H. exfalso. exact (H _ Hoff).
  - right. intros k e' _ He. destruct (entry_single _ _ _ _ He) as [-> ->]. split.
    + intros k' e'' He' Hn. exfalso. apply Hn. by destruct (entry_single _ _ _ _ He') as [-> ->].
    + intros y Hy. by apply HF.
Qed.

Lemma ub_some_below W x x' F :
  world_wf W → opt_rel (pteqW W) (Some x) x' → ub_below W x' F → ∀ y, y ∈ F → w_lt W x y.
Proof.
  intros HW Hr Hub. apply (ub_below_conv W x' (Some x)) in Hub; [done|done|].
  by apply opt_rel_sym.
Qed.

Lemma tenv_ext_empty c o Θ : tenv_ext ∅ c o Θ → Θ = {[c := One o]}.
Proof.
  intros [[_ ->]|(e' & H & _)]; [by rewrite insert_empty|by rewrite lookup_empty in H].
Qed.

Lemma Erel_app_recv n W Θ ub lb T U F v2 :
  strict W → Vrel n W ∅ (TLolli ub lb T U) ERecv → Vrel n W Θ T v2 → ub_below W ub F →
  Erel n W Θ U F (App ERecv v2).
Proof.
  intros HW HV1 HV2 Hub0. pose proof (proj1 HW) as HWf.
  destruct (konst_app_inv _ _ _ _ _ _ _ _ _ _ HWf HV1 HV2)
    as (_ & ub0 & lb0 & A & B & Hk & Hub & HB & HV).
  inversion Hk as [kq Tq Gq xq Hsig _ _| | |]; subst. inversion Hsig as [|m T0 S x| | | | | | |]; subst.
  pose proof (ub_some_below _ _ _ _ HWf Hub Hub0) as Hxl.
  apply Vrel_sess_iff in HV as (c & β & s0 & k & -> & -> & Hs0 & <- & <-).
  destruct (seq_rcv_inv _ _ _ _ _ Hs0 (unfoldS_rcv _ _ _))
    as (U0 & s' & Hu0 & HU0 & Hs').
  destruct n as [|n']; [apply Erel_0|].
  assert (∀ w, is_val w → tstep (App ERecv (Chan c (pt_pol k)))
            (LSess (SRecv (c, pt_pol k) w)) (Pair w (Chan c (pt_pol k))))
    as Hst0 by (intros; by apply TStepHead, HeadRecv).
  apply Erel_S_iff. split_and!.
  - intros Hirr. exfalso. exact (Hirr _ _ (Hst0 EUnit I)).
  - intros _. apply ready_single.
    + exists (SRecv (c, pt_pol k) EUnit), (Pair EUnit (Chan c (pt_pol k))). split; [by apply Hst0|].
      split; [done|]. exists (s0, k), m, U0, s'. split_and!; [|done|done].
      unfold tenv_entry. simpl. by rewrite lookup_singleton_eq.
    + intros y Hy. simpl.
      eapply (wf_lt_eq _ HWf); [reflexivity|by apply Hxl|reflexivity].
  - intros α e' Hst. apply app_val_step in Hst; [|done|done].
    inversion Hst as [| | | | | | |c' β' w Hw| | | | | | | | |]; subst. simpl.
    exists ∅, m, U0, s', k. split.
    { split; [|done]. exists s0. split; [|done]. left. split; [done|by rewrite insert_empty]. }
    intros W' j Θ2 Θ1c Θ' HW' Hj Hext Hcomp HVw.
    apply tenv_ext_empty in Hext as ->.
    pose proof (wext_wf _ _ HW') as HWf'.
    apply Vrel_Erel. eapply Vrel_tconv; [done|eapply teqW_mono; [apply HW'|exact HB]|].
    apply Vrel_prod_iff. exists w, (Chan c (pt_pol k)), Θ2, {[c := One (s', pt_shift 1 k)]}. split_and!.
    + done.
    + apply comp_comm; [exact (wf_rdsym _ HWf')|exact Hcomp].
    + eapply Vrel_teq; [apply teq_ty_inst, HU0|].
      eapply Vrel_payload; [done| |exact HVw]. by apply (proj1 (proj2 HW')).
    + apply Vrel_sess_iff. exists c, (pt_pol k), s', (pt_shift 1 k). split_and!; [done|done|done| |done].
      apply (wf_eq_shift _ HWf'). by apply (proj1 (proj2 HW')).
Qed.

Lemma Erel_app_close n W Θ ub lb T U F v2 :
  strict W → Vrel n W ∅ (TLolli ub lb T U) EClos → Vrel n W Θ T v2 → ub_below W ub F →
  Erel n W Θ U F (App EClos v2).
Proof.
  intros HW HV1 HV2 Hub0. pose proof (proj1 HW) as HWf.
  destruct (konst_app_inv _ _ _ _ _ _ _ _ _ _ HWf HV1 HV2)
    as (_ & ub0 & lb0 & A & B & Hk & Hub & HB & HV).
  inversion Hk as [kq Tq Gq xq Hsig _ _| | |]; subst. inversion Hsig as [| | |x| | | | |]; subst.
  pose proof (ub_some_below _ _ _ _ HWf Hub Hub0) as Hxl.
  apply Vrel_sess_iff in HV as (c & β & s0 & k & -> & -> & Hs0 & <- & <-).
  pose proof (seq_end_inv _ _ Hs0 eq_refl) as Hu0.
  destruct n as [|n']; [apply Erel_0|].
  assert (tstep (App EClos (Chan c (pt_pol k))) (LSess (SClos (c, pt_pol k))) EUnit) as Hst0
    by apply TStepHead, HeadClos.
  apply Erel_S_iff. split_and!.
  - intros Hirr. exfalso. exact (Hirr _ _ Hst0).
  - intros _. apply ready_single.
    + exists (SClos (c, pt_pol k)), EUnit. split; [done|].
      split; [done|]. exists (s0, k). split_and!; [|done|done|done].
      unfold tenv_entry. simpl. by rewrite lookup_singleton_eq.
    + intros y Hy. simpl.
      eapply (wf_lt_eq _ HWf); [reflexivity|by apply Hxl|reflexivity].
  - intros α e' Hst. apply app_val_step in Hst; [|done|done].
    inversion Hst; subst. simpl.
    exists ∅, k. split.
    + split; [|done]. exists s0. split; [|done]. left. split; [done|by rewrite insert_empty].
    + apply Vrel_Erel. eapply Vrel_tconv; [done|exact HB|]. by apply Vrel_unit_iff.
Qed.

(** select₁ and select₂ (K4): a giving step like send, at cost 0. *)
Lemma Erel_app_sel n W Θ ub lb T U F v2 (b : bool) :
  strict W → Vrel n W ∅ (TLolli ub lb T U) (Konst (ksel b)) → Vrel n W Θ T v2 →
  ub_below W ub F → Erel n W Θ U F (App (Konst (ksel b)) v2).
Proof.
  intros HW HV1 HV2 Hub0. pose proof (proj1 HW) as HWf.
  destruct (konst_app_inv _ _ _ _ _ _ _ _ _ _ HWf HV1 HV2)
    as (_ & ub0 & lb0 & A & B & Hk & Hub & HB & HV).
  assert (∃ S1 S2 x, ub0 = Some x ∧ A = TSess (SPlus S1 S2) x ∧
            B = TSess (sbranch b S1 S2) (sel_pt x b)) as (S1 & S2 & x & -> & -> & ->).
  { destruct b; simpl in Hk; inversion Hk as [kq Tq Gq xq Hsig| | |]; subst; inversion Hsig; subst; eauto 10. }
  pose proof (ub_some_below _ _ _ _ HWf Hub Hub0) as Hxl.
  apply Vrel_sess_iff in HV as (c & β & s0 & k & -> & -> & Hs0 & <- & <-).
  destruct (seq_plus_inv _ _ _ _ Hs0 (unfoldS_plus _ _)) as (s1 & s2 & Hu0 & Hs1 & Hs2).
  destruct n as [|n']; [apply Erel_0|].
  assert (tstep (App (Konst (ksel b)) (Chan c (pt_pol k))) (LSess (SSel (c, pt_pol k) b))
            (Chan c false)) as Hst0
    by (destruct b; apply TStepHead; constructor).
  apply Erel_S_iff. split_and!.
  - intros Hirr. exfalso. exact (Hirr _ _ Hst0).
  - intros _. apply ready_single.
    + exists (SSel (c, pt_pol k) b), (Chan c false). split; [done|]. split; [done|].
      exists (s0, k), s1, s2. split_and!; [|done|done].
      unfold tenv_entry. simpl. by rewrite lookup_singleton_eq.
    + intros y Hy. simpl.
      eapply (wf_lt_eq _ HWf); [reflexivity|by apply Hxl|reflexivity].
  - intros α e' Hst. apply app_val_step in Hst; [|by destruct b|done].
    assert (α = LSess (SSel (c, pt_pol k) b) ∧ e' = Chan c false) as [-> ->]
      by (destruct b; inversion Hst; subst; done).
    simpl. exists ∅, s1, s2, k, {[c := One (sbranch b s1 s2, sel_pt k b)]}. split_and!.
    + split; [|done]. exists s0. split; [|done]. left. split; [done|by rewrite insert_empty].
    + left. split; [done|by rewrite insert_empty].
    + apply Vrel_Erel. eapply Vrel_tconv; [done|exact HB|].
      apply Vrel_sess_iff. exists c, false, (sbranch b s1 s2), (sel_pt k b).
      split_and!; [done|done|by destruct b|by apply (wf_eq_dual _ HWf), (wf_eq_payload _ HWf)|done].
Qed.

(** branch (K4): it waits like receive, at cost 1, and returns the
    channel in the injection of the branch taken. *)
Lemma Erel_app_bra n W Θ ub lb T U F v2 :
  strict W → Vrel n W ∅ (TLolli ub lb T U) EBra → Vrel n W Θ T v2 → ub_below W ub F →
  Erel n W Θ U F (App EBra v2).
Proof.
  intros HW HV1 HV2 Hub0. pose proof (proj1 HW) as HWf.
  destruct (konst_app_inv _ _ _ _ _ _ _ _ _ _ HWf HV1 HV2)
    as (_ & ub0 & lb0 & A & B & Hk & Hub & HB & HV).
  assert (∃ S1 S2 x, ub0 = Some x ∧ A = TSess (SWith S1 S2) x ∧
            B = TSum (TSess S1 (pt_payload x (bidx false))) (TSess S2 (pt_payload x (bidx true))))
    as (S1 & S2 & x & -> & -> & ->)
    by (inversion Hk as [kq Tq Gq xq Hsig| | |]; subst; inversion Hsig; subst; eauto 10).
  pose proof (ub_some_below _ _ _ _ HWf Hub Hub0) as Hxl.
  apply Vrel_sess_iff in HV as (c & β & s0 & k & -> & -> & Hs0 & <- & <-).
  destruct (seq_with_inv _ _ _ _ Hs0 (unfoldS_with _ _)) as (s1 & s2 & Hu0 & Hs1 & Hs2).
  destruct n as [|n']; [apply Erel_0|].
  assert (∀ b, tstep (App EBra (Chan c (pt_pol k))) (LSess (SBra (c, pt_pol k) b))
                 (inj_of b (Chan c true))) as Hst0
    by (intros; apply TStepHead, HeadBra).
  apply Erel_S_iff. split_and!.
  - intros Hirr. exfalso. exact (Hirr _ _ (Hst0 false)).
  - intros _. apply ready_single.
    + exists (SBra (c, pt_pol k) false), (inj_of false (Chan c true)). split; [done|]. split; [done|].
      exists (s0, k), s1, s2. split_and!; [|done|done].
      unfold tenv_entry. simpl. by rewrite lookup_singleton_eq.
    + intros y Hy. simpl.
      eapply (wf_lt_eq _ HWf); [reflexivity|by apply Hxl|reflexivity].
  - intros α e' Hst. apply app_val_step in Hst; [|done|done].
    inversion Hst as [| | | | | | | | | | | |c' β' b'| | | |]; subst. simpl.
    exists ∅, s1, s2, k, {[c := One (sbranch b' s1 s2, pt_payload k (bidx b'))]}. split_and!.
    + split; [|done]. exists s0. split; [|done]. left. split; [done|by rewrite insert_empty].
    + left. split; [done|by rewrite insert_empty].
    + apply Vrel_Erel. eapply Vrel_tconv; [done|eapply teqW_mono; [|exact HB]; done|].
      apply Vrel_sum_iff. destruct b'; [right|left]; eexists; (split; [done|]);
        apply Vrel_sess_iff; eexists _, true, _, (pt_payload k (bidx _));
        (split_and!; [done|done|done|by apply (wf_eq_payload _ HWf)|done]).
Qed.

(** Θ = Θ1, c : e as a composition with a singleton. *)
Lemma comp_single_ext R Θ Θ1 c e : tenv_comp R Θ Θ1 {[c := One e]} → tenv_ext Θ1 c e Θ.
Proof.
  intros [Hj _]. pose proof (Hj c) as Jc. rewrite lookup_singleton_eq in Jc.
  assert (∀ c', c' ≠ c → Θ !! c' = Θ1 !! c') as Hoff.
  { intros c' Hne. specialize (Hj c'). rewrite lookup_singleton_ne in Hj by done.
    by inversion Hj. }
  inversion Jc as [|o H1 H2 H3|o H1 H2 H3|e1 e2 H1 H2 H3|e1 e2 H1 H2 H3]; subst.
  - left. split; [done|]. apply map_eq. intros c'. destruct (decide (c' = c)) as [->|Hne].
    + by rewrite lookup_insert_eq.
    + rewrite lookup_insert_ne by done. by apply Hoff.
  - right. exists e1. split; [done|]. right. apply map_eq. intros c'.
    destruct (decide (c' = c)) as [->|Hne]; [by rewrite lookup_insert_eq|].
    rewrite lookup_insert_ne by done. by apply Hoff.
  - right. exists e1. split; [done|]. left. apply map_eq. intros c'.
    destruct (decide (c' = c)) as [->|Hne]; [by rewrite lookup_insert_eq|].
    rewrite lookup_insert_ne by done. by apply Hoff.
Qed.

Lemma Erel_app_send n W Θ ub lb T U F v2 :
  strict W → Vrel n W ∅ (TLolli ub lb T U) ESend → Vrel n W Θ T v2 → ub_below W ub F →
  Erel n W Θ U F (App ESend v2).
Proof.
  intros HW HV1 HV2 Hub0. pose proof (proj1 HW) as HWf.
  destruct (konst_app_inv _ _ _ _ _ _ _ _ _ _ HWf HV1 HV2)
    as (_ & ub0 & lb0 & A & B & Hk & Hub & HB & HV).
  inversion Hk as [kq Tq Gq xq Hsig HG _| | |]; subst.
  inversion Hsig as [|m T0 S x Hpb| | | | | | |]; subst.
  assert (∀ h, h ∈ heads (payload_at m T0 x) → w_lt W x h) as Hpay
    by (intros h Hh; apply (HG (FLt x h)); by exists h).
  pose proof (ub_some_below _ _ _ _ HWf Hub Hub0) as Hxl.
  apply Vrel_prod_iff in HV as (w & vc & Θw & Θc & -> & Hc & HVw & HVc).
  apply Vrel_sess_iff in HVc as (c & β & s0 & k & -> & -> & Hs0 & <- & <-).
  pose proof (Vrel_val _ _ _ _ _ HVw) as Hw.
  destruct (seq_snd_inv _ _ _ _ _ Hs0 (unfoldS_snd _ _ _))
    as (U0 & s' & Hu0 & HU0 & Hs').
  pose proof (comp_single_ext _ _ _ _ _ Hc) as Hext.
  (* the payload's entries lie above x *)
  assert (∀ k' e', tenv_entry Θw k' = Some e' → w_lt W k (pt_dual e'.2)) as Habove.
  { intros k' e' He'.
    assert (hbot (payload_at m T0 k) = false) as Hpb' by (unfold payload_at, ty_inst; by rewrite hbot_pinst).
    destruct (Vrel_heads_above _ _ _ _ _ HWf Hpb' HVw _ _ He') as (h & Hh & Hle).
    eapply (wf_lt_eq _ HWf); [reflexivity|eapply lt_le_W; [done|by apply Hpay|exact Hle]|reflexivity]. }
  (* the key of the sending end *)
  assert (∃ kc, tenv_entry Θ kc = Some (s0, k) ∧ kc.1 = c ∧
            ∀ k' e', k' ≠ kc → tenv_entry Θ k' = Some e' → ∃ k'', tenv_entry Θw k'' = Some e')
    as (kc & Hkc & Hkc1 & Hrest).
  { assert (∀ c' b e', c' ≠ c → tenv_entry Θ (c', b) = Some e' → tenv_entry Θw (c', b) = Some e')
      as Hne.
    { intros c' b e' Hne He'. unfold tenv_entry in *. simpl in *.
      destruct Hext as [[_ ->]|(f & _ & [->| ->])]; by rewrite lookup_insert_ne in He'. }
    destruct Hext as [[H1 ->]|(f & H1 & [->| ->])].
    - exists (c, false). unfold tenv_entry at 1. simpl. rewrite lookup_insert_eq.
      split_and!; [done|done|]. intros [c' b] e' Hk' He'. destruct (decide (c' = c)) as [->|Hc'].
      + unfold tenv_entry in He'. simpl in He'. rewrite lookup_insert_eq in He'.
        destruct b; [done|congruence].
      + exists (c', b). apply Hne; [done|]. done.
    - exists (c, false). unfold tenv_entry at 1. simpl. rewrite lookup_insert_eq.
      split_and!; [done|done|]. intros [c' b] e' Hk' He'. destruct (decide (c' = c)) as [->|Hc'].
      + unfold tenv_entry in He'. simpl in He'. rewrite lookup_insert_eq in He'.
        destruct b; [|congruence]. injection He' as <-. exists (c, false).
        unfold tenv_entry. simpl. by rewrite H1.
      + exists (c', b). by apply Hne.
    - exists (c, true). unfold tenv_entry at 1. simpl. rewrite lookup_insert_eq.
      split_and!; [done|done|]. intros [c' b] e' Hk' He'. destruct (decide (c' = c)) as [->|Hc'].
      + unfold tenv_entry in He'. simpl in He'. rewrite lookup_insert_eq in He'.
        destruct b; [congruence|]. injection He' as <-. exists (c, false).
        unfold tenv_entry. simpl. by rewrite H1.
      + exists (c', b). by apply Hne. }
  destruct n as [|n']; [apply Erel_0|].
  assert (tstep (App ESend (Pair w (Chan c (pt_pol k)))) (LSess (SSend (c, pt_pol k) w))
            (Chan c (pt_pol k))) as Hst0
    by by apply TStepHead, HeadSend.
  assert (offered_t Θ (App ESend (Pair w (Chan c (pt_pol k)))) kc) as Hoff.
  { exists (SSend (c, pt_pol k) w), (Chan c (pt_pol k)). split; [done|]. split; [done|].
    exists (s0, k), m, U0, s'. done. }
  (* only the sending end is offered: the other end of c, if Θw holds it, is dual *)
  assert (∀ k' e', offered_t Θ (App ESend (Pair w (Chan c (pt_pol k)))) k' → tenv_entry Θ k' = Some e' →
            e' = (s0, k)) as Honly.
  { intros k' e' (σ & t' & Hst & Hsel) He'.
    apply app_val_step in Hst; [|done|simpl; by apply andb_True].
    assert (σ = SSend (c, pt_pol k) w) as -> by (inversion Hst; done).
    destruct Hsel as (Hk1 & e'' & m' & T' & s'' & He'' & _ & Hu''). rewrite He' in He''.
    injection He'' as <-. destruct k' as [c' b]. simpl in Hk1. subst c'.
    assert (∀ f, Θw !! c = Some (One f) → unfoldS f.1 = SSeq (SSnd m' T') s'' → False) as Hno.
    { intros f Hf Hfu. destruct Hc as [_ Hd].
      destruct (Hd c f (s0, k) Hf (lookup_singleton_eq _ _)) as [_ Hdu].
      destruct (sdual_snd _ _ _ _ _ Hdu Hfu) as (U1 & r1 & Hr1). simpl in Hr1.
      by rewrite Hu0 in Hr1. }
    unfold tenv_entry in He'. simpl in He'.
    destruct Hext as [[H1 ->]|(f & H1 & [->| ->])]; rewrite lookup_insert_eq in He';
      destruct b; simplify_eq; try done; exfalso; by apply (Hno e'). }
  apply Erel_S_iff. split_and!.
  - intros Hirr. exfalso. exact (Hirr _ _ Hst0).
  - intros _ Hs. split; [intros H; exfalso; exact (H _ Hoff)|].
    right. intros k0 e0 Hoff0 He0. rewrite (Honly k0 e0 Hoff0 He0). split.
    + intros k' e' He' Hn.
      destruct (decide (k' = kc)) as [->|Hne]; [by exfalso|].
      destruct (Hrest k' e' Hne He') as (k'' & Hk'').
      unfold entry_head. simpl. by apply (Habove k'').
    + intros y Hy. unfold entry_head. simpl.
      eapply (wf_lt_eq _ HWf); [reflexivity|by apply Hxl|reflexivity].
  - intros α e' Hst. apply app_val_step in Hst; [|done|simpl; by apply andb_True].
    assert (α = LSess (SSend (c, pt_pol k) w) ∧ e' = Chan c (pt_pol k)) as [-> ->]
      by (inversion Hst; done). simpl.
    exists Θw, ∅, Θw, m, U0, s', k, {[c := One (s', pt_shift 1 k)]}. split_and!.
    + split; [by exists s0|done].
    + apply tenv_comp_empty_l. exact (wf_rdsym _ HWf).
    + eapply Vrel_payload; [done|reflexivity|].
      eapply Vrel_teq; [apply teq_ty_inst, teq_sym, HU0|exact HVw].
    + left. split; [done|by rewrite insert_empty].
    + apply Vrel_Erel. eapply Vrel_tconv; [done|exact HB|].
      apply Vrel_sess_iff. exists c, (pt_pol k), s', (pt_shift 1 k). split_and!; [done|done|done| |done].
      by apply (wf_eq_shift _ HWf).
Qed.

Lemma Erel_app_link n W Θ ub lb T U F v2 :
  strict W → Vrel n W ∅ (TLolli ub lb T U) ELink → Vrel n W Θ T v2 → ub_below W ub F →
  Erel n W Θ U F (App ELink v2).
Proof.
  intros HW HV1 HV2 Hub0. pose proof (proj1 HW) as HWf.
  destruct (konst_app_inv _ _ _ _ _ _ _ _ _ _ HWf HV1 HV2)
    as (_ & ub0 & lb0 & A & B & Hk & Hub & HB & HV).
  inversion Hk as [kq Tq Gq xq Hsig HG _| | |]; subst.
  inversion Hsig as [| | | | | | |S x|]; subst.
  assert (w_eq W x (pt_dual (pt_dual x))) as Hxx' by (rewrite pt_dual_dual; apply (wf_eq_refl _ HWf)).

  apply Vrel_prod_iff in HV as (vc & vd & Θc & Θd & -> & Hc & HVc & HVd).
  apply Vrel_sess_iff in HVc as (c & bc & sc & kc & -> & -> & Hsc & Hkc & <-).
  apply Vrel_sess_iff in HVd as (d & bd & sd & kd & -> & -> & Hsd & Hkd & <-).
  set (cd := ({[(c, pt_pol kc); (d, pt_pol kd)]} : gset cend)).
  destruct n as [|n']; [apply Erel_0|].
  assert (tstep (App ELink (Pair (Chan c (pt_pol kc)) (Chan d (pt_pol kd)))) (LSess (SLink cd)) EUnit)
    as Hst0 by apply TStepHead, HeadLink.
  assert (∀ k', is_Some (tenv_entry Θ k') →
            offered_t Θ (App ELink (Pair (Chan c (pt_pol kc)) (Chan d (pt_pol kd)))) k')
    as Hoff.
  { intros k' [e' He']. exists (SLink cd), EUnit. split; [done|].
    exists e'. split; [done|].
    assert ((k'.1, pt_pol e'.2) ∈ tenv_ends Θ) as Hin
      by (apply elem_of_tenv_ends_entry; eauto).
    rewrite (tenv_join_ends _ _ _ (proj1 Hc)), !tenv_ends_singleton_one in Hin. exact Hin. }
  apply Erel_S_iff. split_and!.
  - intros Hirr. exfalso. exact (Hirr _ _ Hst0).
  - intros _ Hs. split.
    + intros H. exfalso. apply (H (c, false)), Hoff.
      destruct Hc as [Hj _]. specialize (Hj c). rewrite lookup_singleton_eq in Hj.
      unfold tenv_entry. simpl. inversion Hj; by eexists.
    + (* a link compares nothing (sharp edges 68) *)
      left. by exists cd, EUnit.
  - intros α e' Hst. apply app_val_step in Hst; [|done|done].
    assert (α = LSess (SLink cd) ∧ e' = EUnit) as [-> ->] by (inversion Hst; done). simpl.
    exists c, d, ∅, {[d := One (sd, kd)]}, sc, sd, kc, kd. split_and!.
    + done.
    + left. split; [done|by rewrite insert_empty].
    + apply (comp_single_ext (w_eq W)). apply comp_comm; [exact (wf_rdsym _ HWf)|exact Hc].
    + apply sdual_seq_dual. eapply seq_trans; [exact Hsd|]. apply seq_dual, seq_sym, Hsc.
    + eapply (wf_eq_trans _ HWf); [exact Hkc|].
      eapply (wf_eq_trans _ HWf); [exact Hxx'|exact (wf_eq_dual _ HWf _ _ (wf_eq_sym _ HWf _ _ Hkd))].
    + apply Vrel_Erel. eapply Vrel_tconv; [done|exact HB|]. by apply Vrel_unit_iff.
Qed.

(** Every function value but force (sharp edges 51). *)
Lemma Erel_app_noforce n W Θ Θ1 Θ2 ub lb T U F v1 v2 :
  strict W → tenv_comp (w_eq W) Θ Θ1 Θ2 → v1 ≠ EForce →
  Vrel n W Θ1 (TLolli ub lb T U) v1 → Vrel n W Θ2 T v2 → ub_below W ub F →
  Erel n W Θ U F (App v1 v2).
Proof.
  intros HW Hc Hnf HV1 HV2 Hub.
  pose proof (wf_rdsym _ (proj1 HW)) as Hs.
  destruct (proj1 (Vrel_lolli_iff _ _ _ _ _ _ _ _) HV1) as [(eb & -> & _)|(k & T0 & -> & -> & _)].
  - by eapply Erel_app_lam.
  - apply (tenv_comp_empty_l_inv _ _ _ Hs) in Hc as ->.
    destruct k; [eapply Erel_app_new|eapply Erel_app_spawn|eapply Erel_app_recv|eapply Erel_app_send
                |eapply Erel_app_close|eapply Erel_app_link|done
                |eapply (Erel_app_sel _ _ _ _ _ _ _ _ _ false)
                |eapply (Erel_app_sel _ _ _ _ _ _ _ _ _ true)|eapply Erel_app_bra
                |eapply Erel_app_pay|eapply Erel_app_succ]; eauto.
Qed.

(** ** E-App, given the application of values

    The skeleton of E-App: two binds, then the application of two
    values. [app_good] holds for every function value except force
    ([Erel_app_noforce]); force waits for sharp edges 51. *)

Definition app_good (ub lb : option point) (T U : ty) : Prop :=
  ∀ n W Θ Θ1 Θ2 F v1 v2, strict W → tenv_comp (w_eq W) Θ Θ1 Θ2 →
    Vrel n W Θ1 (TLolli ub lb T U) v1 → Vrel n W Θ2 T v2 → ub_below W ub F →
    Erel n W Θ U F (App v1 v2).

Lemma sem_typed_app_gen W Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 e2 ub lb T U :
  app_good ub lb T U →
  tenv_comp (w_eq W) Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 → ub_below W ub F →
  sem_typed W Θ1 Δ1 (F ∪ (tenv_heads Θ2 ∪ lenv_heads Δ2 ∪ bot_pts (lenv_bot Δ2))) e1 (TLolli ub lb T U) →
  sem_typed W Θ2 Δ2 (F ∪ opt_heads lb) e2 T →
  sem_typed W Θ Δ F (App e1 e2) U.
Proof.
  intros Hgood Hc Hsp Hub He1 He2 n W' Θ' Θ'' γ HW Hc'' Hg. simpl.
  change (App (subst γ e1) (subst γ e2)) with (fill_frame (FAppL (subst γ e2)) (subst γ e1)).
  eapply (sem_elim W Θ Θ1 Θ2 Δ Δ1 Δ2 F e1 (TLolli ub lb T U) U (λ γ, FAppL (subst γ e2)));
    [done|done|done|done| |done|done|done].
  clear dependent Θ' Θ'' n γ W'.
  intros n W' Θ' Θ'' γ HW Hc' Hg W'' j Θ1' Θ3 v1 HW'' Hj Hc3 HV1. simpl.
  pose proof (wext_trans _ _ _ HW HW'') as HW2. pose proof (wext_sym _ _ HW2) as Hs.
  pose proof (Vrel_val _ _ _ _ _ HV1) as Hv1.
  change (App v1 (subst γ e2)) with (fill_frame (FAppR v1) (subst γ e2)).
  eapply (Erel_bind j (FAppR v1) W'' Θ3 Θ'' Θ1' T U F (opt_heads lb)).
  - done.
  - apply HW''.
  - by apply comp_comm.
  - left. eapply (Vrel_heads_above _ _ _ (TLolli ub lb T U)); [exact (wext_wf _ _ HW2)|done|exact HV1].
  - exact (sem_typed_later _ _ _ _ _ _ n W' Θ' Θ'' γ W'' j He2 HW Hc' Hg HW'' Hj).
  - intros W3 j' Θ2' Θ4 v2 HW3 Hj' Hc4 HV2.
    pose proof (wext_trans _ _ _ HW2 HW3) as HW4.
    apply (Hgood j' W3 Θ4 Θ1' Θ2'); [apply HW4| | |done|].
    + apply comp_comm; [exact (wext_sym _ _ HW4)|exact Hc4].
    + eapply Vrel_down; [exact Hj'|]. eapply Vrel_mono; [exact (wext_wf _ _ HW2)|exact HW3|exact HV1].
    + eapply ub_below_mono; [exact HW4|exact Hub].
Qed.

(** ** E-Weak (E-Conv is [sem_typed_teq], EquivInvariance.v) *)

Lemma grounding_wk n W Θ Δ' Δ γ :
  world_wf W → lenv_wk Δ' Δ → grounding n W Θ Δ γ → grounding n W Θ Δ' γ.
Proof.
  intros HW Hwk. revert Θ γ.
  induction Hwk as [|[T|] Δ' Δ Hwk IH|U Δ' Δ HU Hwk IH]; intros Θ γ Hg; simpl in *.
  - done.
  - destruct Hg as (Θ1 & Θ2 & Hc & HV & Hg). exists Θ1, Θ2. split_and!; [done|done|by apply IH].
  - by apply IH.
  - destruct Hg as (Θ1 & Θ2 & Hc & HV & Hg).
    rewrite (Vrel_unl_empty _ _ _ _ _ HU HV) in Hc.
    apply (tenv_comp_empty_l_inv _ _ _ (wf_rdsym _ HW)) in Hc as ->. by apply IH.
Qed.

Lemma sem_typed_wk W Θ Δ' Δ F e T :
  lenv_wk Δ' Δ → sem_typed W Θ Δ' F e T → sem_typed W Θ Δ F e T.
Proof.
  intros Hwk He n W' Θ' Θ'' γ HW Hc Hg. apply (He n W' Θ' Θ'' γ HW Hc).
  eapply grounding_wk; [exact (wext_wf _ _ HW)|exact Hwk|exact Hg].
Qed.
