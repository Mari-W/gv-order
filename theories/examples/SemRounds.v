(** * A component whose order pattern is not eventually periodic

    The box K sends one unit on c and one on d per round, forever. Its
    state is a pair of unary numerals (i, j). A round with i = 0 sends
    on d first and moves to (j+1, 0). A round with i = i'+1 sends on c
    first and moves to (i', j+1).

      K = !(f = λp. let (s, q) = p in let (c, d) = q in let (i, j) = s in
              case i of
                inl u  ⇒ let () = u in
                         let (d, c) = ⟨send ⟨∗, d⟩, send ⟨∗, c⟩⟩ in
                         (force f) ⟨⟨inr j, inl ∗⟩, ⟨c, d⟩⟩
              | inr i' ⇒ let (c, d) = ⟨send ⟨∗, c⟩, send ⟨∗, d⟩⟩ in
                         (force f) ⟨⟨i', inr j⟩, ⟨c, d⟩⟩)

    From (0, 0) the rounds that send on d first are 0, 2, 5, 9, 14, …,
    the gaps grow by one each time, and the pattern is not eventually
    periodic ([rdfirst_not_periodic]).

    - [rthread_Erel] : the running thread is in the logical relation at
      every index, every round and every world above [rW], the world
      that orders the points of round k by the pattern. The proof is an
      induction on the index through the recursion.

    - [rounds_deadlock_free] : the thread, with two receivers typed by
      the static system on the other ends of c and d, is deadlock free,
      by a mixed derivation ([mixed_soundness]).

    The static system has no derivation for K at any type that serves
    this thread. That is the conjecture of
    docs/extensions/data-dependent-worlds.md §3 for patterns that are not
    eventually periodic, and this file does not prove it. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.SemFlag examples.DataAlternate.

Set Default Proof Using "All".

(** ** Numerals and the program *)

Fixpoint num (n : nat) : expr :=
  match n with 0 => Inj1 EUnit | S n => Inj2 (num n) end.

Lemma num_val n : is_val (num n).
Proof. induction n; simpl; done. Qed.

Lemma rename_num r n : rename r (num n) = num n.
Proof. induction n; simpl; by f_equal. Qed.

Lemma subst_num σ n : subst σ (num n) = num n.
Proof. induction n; simpl; by f_equal. Qed.

Definition rsend (e : expr) : expr := App ESend (Pair EUnit e).

(** i = 0. The context is u, j, i, d, c, q, s, p, f. *)
Definition rd_zero : expr :=
  LetU (Var 0) (LetP (Pair (rsend (Var 3)) (rsend (Var 4)))
    (App (App EForce (Var 10)) (Pair (Pair (Inj2 (Var 3)) (Inj1 EUnit)) (Pair (Var 0) (Var 1))))).

(** i = i'+1. The context is i', j, i, d, c, q, s, p, f. *)
Definition rd_succ : expr :=
  LetP (Pair (rsend (Var 4)) (rsend (Var 3)))
    (App (App EForce (Var 10)) (Pair (Pair (Var 2) (Inj2 (Var 3))) (Pair (Var 1) (Var 0)))).

Definition rbody : expr :=
  Lam (LetP (Var 0) (LetP (Var 0) (LetP (Var 3) (Case (Var 1) rd_zero rd_succ)))).

Definition rK : expr := EBox rbody.

Definition rthread (a b : nat) (c d : chan) : expr :=
  App (App EForce rK) (Pair (Pair (num a) (num b)) (Pair (Chan c) (Chan d))).

(** ** The pattern *)

Definition rstep (st : nat * nat) : nat * nat :=
  match st.1 with 0 => (S st.2, 0) | S i => (i, S st.2) end.

Fixpoint rst (k : nat) : nat * nat :=
  match k with 0 => (0, 0) | S k => rstep (rst k) end.

(** Round k sends on d first. *)
Definition rdfirst (k : nat) : bool := Nat.eqb (rst k).1 0.

Lemma rst_count k i j : rst k = (i, j) → rst (k + i) = (0, j + i).
Proof.
  revert k j. induction i as [|i IH]; intros k j H.
  - by rewrite Nat.add_0_r, H, Nat.add_0_r.
  - assert (rst (S k) = (i, S j)) as H1 by (simpl; by rewrite H).
    replace (k + S i) with (S k + i) by lia. rewrite (IH _ _ H1). f_equal. lia.
Qed.

Lemma rst_down k i j m : rst k = (i, j) → m ≤ i → rst (k + m) = (i - m, j + m).
Proof.
  revert k i j. induction m as [|m IH]; intros k i j H Hm.
  - rewrite !Nat.add_0_r, Nat.sub_0_r. done.
  - destruct i as [|i]; [lia|].
    assert (rst (S k) = (i, S j)) as H1 by (simpl; by rewrite H).
    replace (k + S m) with (S k + m) by lia. rewrite (IH _ _ _ H1); [|lia]. f_equal; lia.
Qed.

(** The rounds with state (0, j) come at every j, later and later. *)
Lemma rst_zero_every j : ∃ k, j ≤ k ∧ rst k = (0, j).
Proof.
  induction j as [|j (k & Hk & H)]; [by exists 0|].
  exists (S k + S j). split; [lia|].
  assert (rst (S k) = (S j, 0)) as H1 by (simpl; by rewrite H).
  rewrite (rst_count _ _ _ H1). done.
Qed.

(** The pattern is not eventually periodic. *)
Theorem rdfirst_not_periodic p N : 0 < p → ∃ k, N ≤ k ∧ rdfirst k ≠ rdfirst (k + p).
Proof.
  intros Hp. destruct (rst_zero_every (N + p)) as (k & Hk & H).
  exists k. split; [lia|]. unfold rdfirst. rewrite H.
  assert (rst (S k) = (S (N + p), 0)) as H1 by (simpl; by rewrite H).
  replace (k + p) with (S k + (p - 1)) by lia.
  rewrite (rst_down _ _ _ _ H1) by lia. cbn [fst].
  replace (S (N + p) - (p - 1)) with (S (S N)) by lia. simpl. discriminate.
Qed.

(** ** The world

    c lives at the points (0, k), d at (1, k). A round that sends on c
    first has (0, k) ≺ (1, k) ≺ (0, k+1), a round that sends on d first
    has (1, k) ≺ (0, k) ≺ (1, k+1). *)

Definition px (k : nat) : point := Pt (NConst 0) k.
Definition py (k : nat) : point := Pt (NConst 1) k.

Definition rfacts (u v : point) : Prop := ∃ k,
  if rdfirst k then (u = py k ∧ v = px k) ∨ (u = px k ∧ v = py (S k))
  else (u = px k ∧ v = py k) ∨ (u = py k ∧ v = px (S k)).

Definition rW : world := wgen {[NConst 0; NConst 1]} (λ _ _, False) rfacts.

Definition rrank (x : point) : nat :=
  match pt_name x with
  | NConst 0 => 2 * pt_off x + (if rdfirst (pt_off x) then 1 else 0)
  | NConst 1 => 2 * pt_off x + (if rdfirst (pt_off x) then 0 else 1)
  | _ => pt_off x
  end.

Lemma rW_strict : strict rW.
Proof.
  apply (wgen_strict _ _ _ id rrank).
  - intros q Hq. apply elem_of_union in Hq as [Hq|Hq]; apply elem_of_singleton in Hq as ->; eauto.
  - done.
  - intros u v (k & Hk). right. destruct (rdfirst k);
      destruct Hk as [[-> ->]|[-> ->]]; cbn; set_solver.
  - done.
  - done.
  - done.
  - intros [[a| |q b i] o]; unfold rrank, pt_shift; cbn; [|lia|lia].
    destruct a as [|[|a]]; [| |lia]; destruct (rdfirst o), (rdfirst (o + 1)); lia.
  - intros u v (k & Hk). unfold id. destruct (rdfirst k) eqn:E;
      destruct Hk as [[-> ->]|[-> ->]]; unfold rrank; cbn; rewrite ?E;
      destruct (rdfirst (S k)); lia.
Qed.

Lemma rW_lt u v : rfacts u v → w_lt rW u v.
Proof. intros H. by apply glt_base. Qed.

(** ** The β-steps of a round *)

Lemma det_beta_appl e1 e1' e2 : det_beta e1 e1' → det_beta (App e1 e2) (App e1' e2).
Proof.
  intros [Hs Hd]. split; [by apply TStepAppL|].
  intros α e'' H. apply tstep_app_inv in H as [(f & Hf & ->)|[(Hv & _)|(Hv & _)]].
  - by destruct (Hd _ _ Hf) as [-> ->].
  - exfalso. by eapply val_no_tstep.
  - exfalso. by eapply val_no_tstep.
Qed.

Lemma det_beta_force e : det_beta (App EForce (EBox e)) (subst1 (EBox e) e).
Proof.
  split; [by apply TStepHead, HeadForce|].
  intros α e'' H. apply app_val_step in H; [|done|done]. by inversion H; subst.
Qed.

Lemma det_beta_letp u v e : is_val u → is_val v → det_beta (LetP (Pair u v) e) (subst2 u v e).
Proof.
  intros Hu Hv. split; [by apply TStepHead, HeadLetP|].
  intros α e'' H. apply tstep_letp_inv in H as [(f & Hf & _)|(u' & v' & Huv & _ & _ & -> & ->)].
  - exfalso. eapply val_no_tstep; [exact Hf|]. simpl. by apply andb_True.
  - by injection Huv as -> ->.
Qed.

Lemma det_beta_letu e : det_beta (LetU EUnit e) e.
Proof.
  split; [by apply TStepHead, HeadLetU|].
  intros α e'' H. apply tstep_letu_inv in H as [(f & Hf & _)|(_ & -> & ->)]; [|done].
  exfalso. by eapply val_no_tstep.
Qed.

Lemma Erel_dstep n W Θ T F e e' : det_beta e e' → Erel n W Θ T F e' → Erel n W Θ T F e.
Proof. intros [Hs Hd]. by apply Erel_det_beta. Qed.

Lemma Erel_dstep_S n W Θ T F e e' : det_beta e e' → Erel n W Θ T F e' → Erel (S n) W Θ T F e.
Proof. intros [Hs Hd]. by apply Erel_det_beta_S. Qed.

Definition round_z (b : nat) (c d : chan) : expr :=
  LetP (Pair (rsend (Chan d)) (rsend (Chan c)))
    (App (App EForce rK) (Pair (Pair (Inj2 (num b)) (Inj1 EUnit)) (Pair (Var 0) (Var 1)))).

Definition round_s (a b : nat) (c d : chan) : expr :=
  LetP (Pair (rsend (Chan c)) (rsend (Chan d)))
    (App (App EForce rK) (Pair (Pair (num a) (Inj2 (num b))) (Pair (Var 1) (Var 0)))).


Lemma det_beta_letp' u v e e' : is_val u → is_val v → e' = subst2 u v e → det_beta (LetP (Pair u v) e) e'.
Proof. intros ? ? ->. by apply det_beta_letp. Qed.

Lemma det_beta_force' e e' : e' = subst1 (EBox e) e → det_beta (App EForce (EBox e)) e'.
Proof. intros ->. apply det_beta_force. Qed.

Definition zK : expr := LetU (Var 0) (LetP (Pair (rsend (Var 3)) (rsend (Var 4)))
  (App (App EForce rK) (Pair (Pair (Inj2 (Var 3)) (Inj1 EUnit)) (Pair (Var 0) (Var 1))))).
Definition sK : expr := LetP (Pair (rsend (Var 4)) (rsend (Var 3)))
  (App (App EForce rK) (Pair (Pair (Var 2) (Inj2 (Var 3))) (Pair (Var 1) (Var 0)))).
Definition BK : expr := LetP (Var 0) (LetP (Var 0) (LetP (Var 3) (Case (Var 1) zK sK))).

Definition zKc (c d : chan) : expr := LetU (Var 0) (LetP (Pair (rsend (Chan d)) (rsend (Chan c)))
  (App (App EForce rK) (Pair (Pair (Inj2 (Var 3)) (Inj1 EUnit)) (Pair (Var 0) (Var 1))))).
Definition sKc (c d : chan) : expr := LetP (Pair (rsend (Chan c)) (rsend (Chan d)))
  (App (App EForce rK) (Pair (Pair (Var 2) (Inj2 (Var 3))) (Pair (Var 1) (Var 0)))).

Definition zKj (b : nat) (c d : chan) : expr := LetU (Var 0) (round_z b c d).
Definition sKj (b : nat) (c d : chan) : expr := LetP (Pair (rsend (Chan c)) (rsend (Chan d)))
  (App (App EForce rK) (Pair (Pair (Var 2) (Inj2 (num b))) (Pair (Var 1) (Var 0)))).

Definition rval (a b : nat) (c d : chan) : expr := Pair (Pair (num a) (num b)) (Pair (Chan c) (Chan d)).

Lemma rval_val a b c d : is_val (rval a b c d).
Proof. simpl. rewrite !andb_True. split_and!; try apply num_val; done. Qed.

Lemma rthread_head n W Θ T F a b c d :
  Erel n W Θ T F (Case (num a) (zKj b c d) (sKj b c d)) → Erel (S n) W Θ T F (rthread a b c d).
Proof.
  intros HE. unfold rthread.
  eapply Erel_dstep_S; [apply det_beta_appl, (det_beta_force' _ (Lam BK)); reflexivity|].
  eapply Erel_dstep; [apply (det_beta_app_lam _ _ (LetP (rval a b c d) (LetP (Var 0) (LetP (Var 3) (Case (Var 1) zK sK)))));
    [apply rval_val|reflexivity]|].
  eapply Erel_dstep; [apply (det_beta_letp' _ _ _ (LetP (Pair (Chan c) (Chan d)) (LetP (Pair (num a) (num b)) (Case (Var 1) zK sK))));
    [simpl; rewrite andb_True; split; apply num_val|done|]|].
  { unfold subst2. cbn. rewrite !rename_num. reflexivity. }
  eapply Erel_dstep; [apply (det_beta_letp' _ _ _ (LetP (Pair (num a) (num b)) (Case (Var 1) (zKc c d) (sKc c d))));
    [done|done|]|].
  { unfold subst2. cbn. rewrite !subst_num. reflexivity. }
  eapply Erel_dstep; [apply (det_beta_letp' _ _ _ (Case (num a) (zKj b c d) (sKj b c d)));
    [apply num_val|apply num_val|]|].
  { unfold subst2. cbn. rewrite !rename_num. reflexivity. }
  exact HE.
Qed.

Lemma Sb_unf : seq Sb (SSeq (SSnd 0 TUnit) Sb).
Proof. apply seq_unf. done. Qed.

Lemma heads_above_one W c s p : world_wf W → heads_above W {[p]} {[c := One (s, p)]}.
Proof.
  intros HW. pose proof (heads_above_self W {[c := One (s, p)]} HW) as H.
  by rewrite tenv_heads_one in H.
Qed.

(** send ⟨∗, c⟩ on c : Sb at p, with a future above p. *)
Lemma Erel_rsend n W c s p F :
  strict W → seq s Sb → (∀ z, z ∈ F → w_lt W p z) →
  Erel n W {[c := One (s, p)]} (TSess Sb (pt_shift 1 p)) F (rsend (Chan c)).
Proof.
  intros HW Hs HF. pose proof (proj1 HW) as HWf.
  apply (Erel_app_send n W _ (Some p) None (TProd TUnit (TSess (SSeq (SSnd 0 TUnit) Sb) p))); [done| | |].
  - apply Vrel_lolli_iff. right. eexists KSend, _. split_and!; [done|done| |apply teqW_refl].
    apply (KTSend _ _ _ 0 TUnit Sb p). simpl. intros h Hh. set_solver.
  - apply Vrel_prod_iff. exists EUnit, (Chan c), ∅, {[c := One (s, p)]}. split_and!; [done| | |].
    + apply tenv_comp_empty_l, (wf_eq_sym _ HWf).
    + by apply Vrel_unit_iff.
    + apply Vrel_sess_iff. eexists _, _, _. split_and!; [done|done| |apply (wf_eq_refl _ HWf)].
      eapply seq_trans; [exact Hs|apply Sb_unf].
  - exact HF.
Qed.

(** One round: send on f, then on g, and continue with Q. The first send
    needs f ≺ g, the second g ≺ f+1. *)
Lemma Erel_round n W Θ f g s1 s2 pf pg Q :
  strict W → tenv_comp (w_eq W) Θ {[f := One (s1, pf)]} {[g := One (s2, pg)]} →
  seq s1 Sb → seq s2 Sb → w_lt W pf pg → w_lt W pg (pt_shift 1 pf) →
  (∀ W' j f' g' s1' s2' pf' pg' Θ', wext W W' → j ≤ n →
     tenv_comp (w_eq W') Θ' {[f' := One (s1', pf')]} {[g' := One (s2', pg')]} →
     seq s1' Sb → seq s2' Sb → w_eq W' pf' (pt_shift 1 pf) → w_eq W' pg' (pt_shift 1 pg) →
     Erel j W' Θ' TUnit ∅ (subst2 (Chan f') (Chan g') Q)) →
  Erel n W Θ TUnit ∅ (LetP (Pair (rsend (Chan f)) (rsend (Chan g))) Q).
Proof.
  intros HW Hc Hs1 Hs2 Hfg Hgf HK. pose proof (proj1 HW) as HWf.
  set (Th := TProd (TSess Sb (pt_shift 1 pf)) (TSess Sb (pt_shift 1 pg))).
  change (LetP ?e Q) with (fill_frame (FLetP Q) e).
  apply (Erel_bind n (FLetP Q) W Θ Θ ∅ Th TUnit ∅ ∅);
    [done|done|apply tenv_comp_empty_r|left; apply heads_above_empty| |].
  - change (Pair ?a ?b) with (fill_frame (FPairL b) a).
    apply (Erel_bind n (FPairL (rsend (Chan g))) W Θ {[f := One (s1, pf)]} {[g := One (s2, pg)]}
             (TSess Sb (pt_shift 1 pf)) Th (∅ ∪ ∅) {[pg]});
      [done|done|done|left; by apply heads_above_one| |].
    + apply Erel_rsend; [done|done|]. intros z Hz. assert (z = pg) as -> by set_solver. done.
    + intros W' j Θ1' Θ' v HW' Hj Hc' HV.
      apply Vrel_sess_iff in HV as (f' & s1' & pf' & -> & -> & Hs1' & Hpf').
      pose proof (wext_wf _ _ HW') as HWf'. pose proof (proj2 (proj2 (proj2 HW'))) as HWs'.
      change (fill_frame (FPairL (rsend (Chan g))) (Chan f'))
        with (fill_frame (FPairR (Chan f')) (rsend (Chan g))).
      apply (Erel_bind j (FPairR (Chan f')) W' Θ' {[g := One (s2, pg)]} {[f' := One (s1', pf')]}
               (TSess Sb (pt_shift 1 pg)) Th (∅ ∪ ∅) {[pf']});
        [done|done|apply comp_comm; [apply (wf_eq_sym _ HWf')|exact Hc']
        |left; by apply heads_above_one| |].
      * apply Erel_rsend; [done|done|]. intros z Hz. assert (z = pf') as -> by set_solver.
        eapply (wf_lt_eq _ HWf'); [apply (wf_eq_refl _ HWf')| |apply (wf_eq_sym _ HWf'), Hpf'].
        apply (proj1 (proj2 (proj2 HW'))). exact Hgf.
      * intros W'' j' Θ1'' Θ'' v HW'' Hj' Hc'' HV.
        apply Vrel_sess_iff in HV as (g' & s2' & pg' & -> & -> & Hs2' & Hpg').
        apply Vrel_Erel. apply Vrel_prod_iff.
        exists (Chan f'), (Chan g'), {[f' := One (s1', pf')]}, {[g' := One (s2', pg')]}.
        split_and!; [done| | |].
        -- apply comp_comm; [apply (wf_eq_sym _ (wext_wf _ _ HW''))|exact Hc''].
        -- apply Vrel_sess_iff. eexists _, _, _. split_and!; [done|done|done|]. exact (wext_eq _ _ _ _ HW'' Hpf').
        -- apply Vrel_sess_iff. eexists _, _, _. split_and!; [done|done|done|exact Hpg'].
  - intros W' j Θ1' Θ' v HW' Hj Hc' HV.
    apply tenv_comp_empty_r_inv in Hc' as ->.
    apply Vrel_prod_iff in HV as (v1 & v2 & Θa & Θb & -> & Hab & Ha & Hb).
    apply Vrel_sess_iff in Ha as (f' & s1' & pf' & -> & -> & Hs1' & Hpf').
    apply Vrel_sess_iff in Hb as (g' & s2' & pg' & -> & -> & Hs2' & Hpg').
    eapply Erel_dstep; [by apply det_beta_letp|].
    by apply (HK W' j f' g' s1' s2' pf' pg').
Qed.
