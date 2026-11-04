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

(** ** The thread through the recursion *)

Lemma px_shift k : pt_shift 1 (px k) = px (S k).
Proof. unfold pt_shift, px. simpl. f_equal. lia. Qed.

Lemma py_shift k : pt_shift 1 (py k) = py (S k).
Proof. unfold pt_shift, py. simpl. f_equal. lia. Qed.

(** A fact of rW between points aliased in a later world. *)
Lemma rW_lt_at W u v x y : wext rW W → rfacts u v → w_eq W x u → w_eq W y v → w_lt W x y.
Proof.
  intros Hw Huv Hx Hy. pose proof (wext_wf _ _ Hw) as HWf.
  eapply (wf_lt_eq _ HWf); [exact Hx| |apply (wf_eq_sym _ HWf), Hy].
  apply (proj1 (proj2 (proj2 Hw))). by apply rW_lt.
Qed.

Lemma eq_shift_at W x p q :
  wext rW W → w_eq W x p → pt_shift 1 p = q → w_eq W (pt_shift 1 x) q.
Proof. intros Hw Hx <-. apply (wf_eq_shift _ (wext_wf _ _ Hw)), Hx. Qed.

(** The thread in round k with state (a, b) = rst k, c at a point
    aliased to (0, k) and d at one aliased to (1, k), lies in the
    relation at every index, in every world above rW. *)
Theorem rthread_Erel n : ∀ W k a b c d s1 s2 xk yk Θ,
  wext rW W → rst k = (a, b) → seq s1 Sb → seq s2 Sb →
  w_eq W xk (px k) → w_eq W yk (py k) →
  tenv_comp (w_eq W) Θ {[c := One (s1, xk)]} {[d := One (s2, yk)]} →
  Erel n W Θ TUnit ∅ (rthread a b c d).
Proof.
  induction n as [n IH] using lt_wf_ind.
  intros W k a b c d s1 s2 xk yk Θ Hw Hk Hs1 Hs2 Hx Hy Hc.
  destruct n as [|n']; [apply Erel_0|].
  pose proof (proj2 (proj2 (proj2 Hw))) as HW. pose proof (proj1 HW) as HWf.
  apply rthread_head.
  destruct a as [|a].
  - (* d first *)
    assert (rdfirst k = true) as Hd by (unfold rdfirst; by rewrite Hk).
    eapply Erel_dstep; [apply det_beta_case1; [done|]|].
    { unfold zKj, round_z. cbn. rewrite !subst_num. reflexivity. }
    eapply Erel_dstep; [apply det_beta_letu|].
    unfold round_z. apply (Erel_round n' W Θ d c s2 s1 yk xk); [done| |done|done| | |].
    + apply comp_comm; [apply (wf_eq_sym _ HWf)|exact Hc].
    + apply (rW_lt_at W (py k) (px k)); [done| |done|done]. exists k. rewrite Hd. by left.
    + apply (rW_lt_at W (px k) (py (S k))); [done| |done|by apply (eq_shift_at W _ (py k)); [| |apply py_shift]].
      exists k. rewrite Hd. by right.
    + intros W' j d' c' s2' s1' pd' pc' Θ' HW' Hj Hc' Hs2' Hs1' Hpd' Hpc'.
      match goal with |- Erel _ _ _ _ _ ?e => assert (e = rthread (S b) 0 c' d') as -> end.
      { unfold subst2, rthread. cbn. rewrite !subst_num. reflexivity. }
      pose proof (wext_trans _ _ _ Hw HW') as Hw'. pose proof (wext_wf _ _ Hw') as HWf'.
      apply (IH j ltac:(lia) W' (S k) (S b) 0 c' d' s1' s2' pc' pd' Θ'); [done|by simpl; rewrite Hk|done|done| | |].
      * eapply (wf_eq_trans _ HWf'); [exact Hpc'|]. apply (eq_shift_at W' _ (px k)); [done| |apply px_shift].
        exact (wext_eq _ _ _ _ HW' Hx).
      * eapply (wf_eq_trans _ HWf'); [exact Hpd'|]. apply (eq_shift_at W' _ (py k)); [done| |apply py_shift].
        exact (wext_eq _ _ _ _ HW' Hy).
      * apply comp_comm; [apply (wf_eq_sym _ HWf')|exact Hc'].
  - (* c first *)
    assert (rdfirst k = false) as Hd by (unfold rdfirst; by rewrite Hk).
    eapply Erel_dstep; [apply det_beta_case2; [apply num_val|]|].
    { unfold sKj, round_s. cbn. rewrite !rename_num. reflexivity. }
    unfold round_s. apply (Erel_round n' W Θ c d s1 s2 xk yk); [done|done|done|done| | |].
    + apply (rW_lt_at W (px k) (py k)); [done| |done|done]. exists k. rewrite Hd. by left.
    + apply (rW_lt_at W (py k) (px (S k))); [done| |done|by apply (eq_shift_at W _ (px k)); [| |apply px_shift]].
      exists k. rewrite Hd. by right.
    + intros W' j c' d' s1' s2' pc' pd' Θ' HW' Hj Hc' Hs1' Hs2' Hpc' Hpd'.
      match goal with |- Erel _ _ _ _ _ ?e => assert (e = rthread a (S b) c' d') as -> end.
      { unfold subst2, rthread. cbn. rewrite !subst_num. reflexivity. }
      pose proof (wext_trans _ _ _ Hw HW') as Hw'. pose proof (wext_wf _ _ Hw') as HWf'.
      apply (IH j ltac:(lia) W' (S k) a (S b) c' d' s1' s2' pc' pd' Θ'); [done|by simpl; rewrite Hk|done|done| | |done].
      * eapply (wf_eq_trans _ HWf'); [exact Hpc'|]. apply (eq_shift_at W' _ (px k)); [done| |apply px_shift].
        exact (wext_eq _ _ _ _ HW' Hx).
      * eapply (wf_eq_trans _ HWf'); [exact Hpd'|]. apply (eq_shift_at W' _ (py k)); [done| |apply py_shift].
        exact (wext_eq _ _ _ _ HW' Hy).
Qed.

(** ** The closed configuration

    The thread starts in round 0 with c at (0, 0) and d at (1, 0). Two
    receivers (alt_R of DataAlternate.v) hold the other ends. *)

Definition rthr : expr := rthread 0 0 chc chd.
Definition rrecv (c : chan) : expr := App (App EForce alt_R) (Chan c).

Definition rΘ : tenv := <[chd := One (Sb, py 0)]> {[chc := One (Sb, px 0)]}.

Lemma rΘ_comp R : tenv_comp R rΘ {[chd := One (Sb, py 0)]} {[chc := One (Sb, px 0)]}.
Proof.
  split.
  - intros c. unfold rΘ. destruct (decide (c = chd)) as [->|Hd].
    + rewrite lookup_insert_eq, lookup_singleton_eq, lookup_singleton_ne by done. constructor.
    + rewrite lookup_insert_ne, lookup_singleton_ne by done.
      destruct (decide (c = chc)) as [->|Hc].
      * rewrite lookup_singleton_eq. constructor.
      * rewrite lookup_singleton_ne by done. constructor.
  - intros c e1 e2 H1 H2. apply lookup_singleton_Some in H1 as [<- _].
    by rewrite lookup_singleton_ne in H2.
Qed.

Theorem rthr_sem : sem_typed rW rΘ [] ∅ rthr TUnit.
Proof.
  intros n W' Θ' Θ'' γ HW Hc Hg. cbn [grounding] in Hg. subst Θ'.
  apply tenv_comp_empty_r_inv in Hc as ->. pose proof (wext_wf _ _ HW) as HWf.
  change (subst γ rthr) with rthr.
  apply (rthread_Erel n W' 0 0 0 chc chd Sb Sb (px 0) (py 0)); try done;
    [apply seq_refl|apply seq_refl|apply (wf_eq_refl _ HWf)|apply (wf_eq_refl _ HWf)|].
  apply comp_comm; [apply (wf_eq_sym _ HWf)|apply rΘ_comp].
Qed.

(** A receiver on c at the point (a, 0), typed by the static system. *)
Lemma rrecv_typed W c a :
  world_wf W → pt_known W (Pt (NConst a) 0) →
  typed W ∅ [] {[c := One (Sa, Pt (NConst a) 0)]} [] (∅, None) (rrecv c) TUnit.
Proof.
  intros HW Hk. unfold rrecv.
  eapply (t_app W ∅ [] _ ∅ {[c := One (Sa, Pt (NConst a) 0)]} [] [] [] _ _ _
            (Some (Pt (NConst a) 0)) None (TSess Sa (Pt (NConst a) 0))).
  - apply tenv_comp_empty_l. intros ? ?. apply se_sym.
  - constructor.
  - apply ubs_intro; [|done]. intros z Hz. cbn in Hz. set_solver.
  - apply (typed_force0 W _ _ _ _ _ _ 1 alt_RC None alt_R_body [Pt (NConst a) 0]);
      [done|done| | |apply ubs_none|apply alt_R_typed, HW].
    + apply bcs_hold_intro. intros g [].
    + constructor; [by left|constructor].
  - apply t_ch; [intros o Ho; by apply elem_of_nil in Ho|apply seq_refl|apply se_refl].
Qed.

Lemma Sb_Sa : sdual Sb Sa.
Proof. pose proof (sdual_dual Sb) as H. assert (dual Sb = Sa) as E by reflexivity. by rewrite E in H. Qed.

Lemma rknown a : a = 0 ∨ a = 1 → pt_known rW (Pt (NConst a) 0).
Proof. intros [->| ->]; unfold pt_known; cbn; set_solver. Qed.

Definition rconfig : proc := ({[chc; chd]}, {[+ rthr; rrecv chc; rrecv chd +]}).

(** The mixed derivation: the thread is a semantic leaf, the two
    receivers are syntactic leaves, and two cuts join them. *)
Theorem rounds_mixed : mptyped rW ∅ rconfig TUnit.
Proof.
  pose proof rW_strict as HW. pose proof (proj1 HW) as HWf.
  assert (chc ≠ chd) as Hcd by done.
  assert (mptyped rW ({[chd := (Sb, py 0)]} ∪ ∅) (∅ ∪ ∅ ∪ {[chc]}, {[+ rthr +]} ⊎ {[+ rrecv chc +]}) TUnit)
    as P1.
  { apply (mp_connect rW {[chd := (Sb, py 0)]} ∅ {[chc := (Sb, px 0)]} {[chc := (Sa, px 0)]} {[chc]}
             ∅ ∅ {[+ rthr +]} {[+ rrecv chc +]} TUnit).
    - apply (mp_sem_thread rW _ ∅ ∅); [constructor|done|done|set_solver| | |].
      + intros c o Ho. by rewrite lookup_empty in Ho.
      + intros c e1 e2 He. by rewrite lookup_empty in He.
      + assert (tenv_of ({[chd := (Sb, py 0)]} ∪ {[chc := (Sb, px 0)]}) ∪ ∅ = rΘ) as ->.
        { rewrite (right_id_L ∅ (∪)). unfold tenv_of, rΘ.
          by rewrite <-insert_union_singleton_l, fmap_insert, map_fmap_singleton. }
        apply rthr_sem.
    - rewrite (left_id_L ∅ (∪)). apply mp_syn.
      apply (pt_term rW {[chc := (Sa, px 0)]} ∅ ∅); [constructor|done|set_solver| | |].
      + intros c o Ho. by rewrite lookup_empty in Ho.
      + intros c e1 e2 He. by rewrite lookup_empty in He.
      + unfold tenv_of. rewrite map_fmap_singleton, (right_id_L ∅ (∪)).
        apply rrecv_typed; [done|apply rknown; by left].
    - apply dom_singleton_L.
    - apply dom_singleton_L.
    - intros c e e' He He'. apply lookup_singleton_Some in He as [<- <-].
      apply lookup_singleton_Some in He' as [_ <-]. split; [apply (wf_eq_refl _ HWf)|apply Sb_Sa].
    - set_solver.
    - set_solver.
    - apply map_disjoint_singleton_l. by rewrite lookup_singleton_ne.
    - apply map_disjoint_empty_l.
    - apply map_disjoint_empty_r.
    - set_solver.
    - set_solver.
    - set_solver.
    - set_solver.
    - set_solver. }
  rewrite (right_id_L ∅ (∪)) in P1.
  assert (rconfig = ((∅ ∪ ∅ ∪ {[chc]}) ∪ ∅ ∪ {[chd]},
                     ({[+ rthr +]} ⊎ {[+ rrecv chc +]}) ⊎ {[+ rrecv chd +]})) as ->.
  { unfold rconfig. f_equal; try set_solver; try multiset_solver. }
  assert ((∅ : senv) = ∅ ∪ ∅) as E by by rewrite (left_id_L ∅ (∪)).
  rewrite E at 1.
  apply (mp_connect rW ∅ ∅ {[chd := (Sb, py 0)]} {[chd := (Sa, py 0)]} {[chd]}
           (∅ ∪ ∅ ∪ {[chc]}) ∅ ({[+ rthr +]} ⊎ {[+ rrecv chc +]}) {[+ rrecv chd +]} TUnit).
  - by rewrite (left_id_L ∅ (∪)).
  - rewrite (left_id_L ∅ (∪)). apply mp_syn.
    apply (pt_term rW {[chd := (Sa, py 0)]} ∅ ∅); [constructor|done|set_solver| | |].
    + intros c o Ho. by rewrite lookup_empty in Ho.
    + intros c e1 e2 He. by rewrite lookup_empty in He.
    + unfold tenv_of. rewrite map_fmap_singleton, (right_id_L ∅ (∪)).
      apply rrecv_typed; [done|apply rknown; by right].
  - apply dom_singleton_L.
  - apply dom_singleton_L.
  - intros c e e' He He'. apply lookup_singleton_Some in He as [<- <-].
    apply lookup_singleton_Some in He' as [_ <-]. split; [apply (wf_eq_refl _ HWf)|apply Sb_Sa].
  - set_solver.
  - set_solver.
  - apply map_disjoint_empty_l.
  - apply map_disjoint_empty_l.
  - apply map_disjoint_empty_l.
  - set_solver.
  - set_solver.
  - set_solver.
  - set_solver.
  - set_solver.
Qed.

(** The configuration is deadlock free, by the mixed derivation. *)
Theorem rounds_deadlock_free : deadlock_free rconfig.
Proof. exact (mixed_soundness rW rconfig TUnit rW_strict rounds_mixed). Qed.
