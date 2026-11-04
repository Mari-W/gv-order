(** * Rounds of a recursion in Mordido and Pérez

    docs/extensions/adequacy/mordido-perez.md, section 15. A round is
    one run of the body of a recursive function, from one call to the
    next. Their rules type the body once, under the sequences of the
    first call (the derivation for client, pdf pp. 28 and 29). Version 2
    asks the body to type at every round, because its priority
    abstraction holds at every valuation that a recursive call reaches.

    - Program 8 shows that checking only the first round is unsound.
      The spawned thread runs client of Listing 1.1 (p. 4), which acts
      once on each channel per round. The main thread runs [dsend],
      which receives once on a and sends twice on b per round. With the
      sequences 1 + 4k for a and 2 + 2k for b both first rounds type
      (1 < 2 < 5 for client, 1 < 2 < 4 < 5 for dsend), and the program
      deadlocks in their semantics after one round
      ([p8_not_deadlock_free]). Version 2 rejects it
      ([p8_not_mtyped]), because client's second round would need
      5 < 4.
    - Unequal increments are fine when every round advances all
      channels by one amount of priority. [rr_main] replaces client by
      [hrecv], which sends once on a and receives twice on b. Each
      round advances a by 4 and b by 2 · 2, so every round types, and
      the program goes through the general translation of version 2
      ([rr_mp2_deadlock_free], [rr_deadlock_free_src]). *)

From Stdlib Require Import String.
From stdpp Require Import base gmap gmultiset relations.
From LRGV Require Export mp.MP2Simulation.

Set Default Proof Using "All".

(** ** The two loops

      dsend b a = let (_, a) = receive a in let b = send () b in
                  let b = send () b in dsend b a
      hrecv a b = let a = send () a in let (_, b) = receive b in
                  let (_, b) = receive b in hrecv a b *)

Definition dsend : expr :=
  EBox (Lam (Lam (LetP (App ERecv (Var 0))
    (App (Lam (App (Lam (App (App (Var 6) (Var 0)) (Var 2))) (App ESend (Pair EUnit (Var 0)))))
         (App ESend (Pair EUnit (Var 3))))))).

Definition hrecv : expr :=
  EBox (Lam (Lam (App (Lam (LetP (App ERecv (Var 1)) (LetP (App ERecv (Var 0))
                                (App (App (Var 7) (Var 4)) (Var 0)))))
                      (App ESend (Pair EUnit (Var 1)))))).

(** Program 8: client (MP2Examples.v) against dsend. *)
Definition p8_main : expr := App (App (Lam (Lam st_body)) client) dsend.

(** The program with matching rates. *)
Definition rr_main : expr := App (App (Lam (Lam st_body)) hrecv) dsend.

(** ** Program 8 deadlocks in their semantics *)

Lemma ps_one (e : expr) : ({[+ e +]} : gmultiset expr) = ∅ ⊎ {[+ e +]}.
Proof. multiset_solver. Qed.

Lemma ps_beta1 C e e' q :
  src_step e SBeta e' → rtc src_pstep (C, {[+ e' +]}) q → rtc src_pstep (C, {[+ e +]}) q.
Proof.
  intros H Hq. eapply rtc_l; [|exact Hq]. rewrite (ps_one e), (ps_one e'). by apply SPBeta.
Qed.

Lemma ps_new1 C e a e' q :
  src_step e (SNew a) e' → a ∉ C → a ∉ fchans e →
  rtc src_pstep (C ∪ {[a]}, {[+ e' +]}) q → rtc src_pstep (C, {[+ e +]}) q.
Proof.
  intros H HC Ha Hq. eapply rtc_l; [|exact Hq]. rewrite (ps_one e), (ps_one e').
  apply SPNew; [done|done| |done]. unfold echans. rewrite gmultiset_elements_empty. set_solver.
Qed.

Lemma ps_spawn1 C e v e' q :
  src_step e (SSpawn v) e' → rtc src_pstep (C, {[+ App v EUnit +]} ⊎ {[+ e' +]}) q →
  rtc src_pstep (C, {[+ e +]}) q.
Proof.
  intros H Hq. eapply rtc_l; [|exact Hq]. rewrite (ps_one e).
  replace ({[+ App v EUnit +]} ⊎ {[+ e' +]} : gmultiset expr)
    with (∅ ⊎ {[+ e' +]} ⊎ {[+ App v EUnit +]} : gmultiset expr) by multiset_solver.
  by apply SPSpawn.
Qed.

Lemma ps_betaL C s s' m q :
  src_step s SBeta s' → rtc src_pstep (C, {[+ s' +]} ⊎ {[+ m +]}) q →
  rtc src_pstep (C, {[+ s +]} ⊎ {[+ m +]}) q.
Proof.
  intros H Hq. eapply rtc_l; [|exact Hq].
  rewrite !(comm (⊎) {[+ _ +]} {[+ m +]}). by apply SPBeta.
Qed.

Lemma ps_betaR C s m m' q :
  src_step m SBeta m' → rtc src_pstep (C, {[+ s +]} ⊎ {[+ m' +]}) q →
  rtc src_pstep (C, {[+ s +]} ⊎ {[+ m +]}) q.
Proof. intros H Hq. eapply rtc_l; [|exact Hq]. by apply SPBeta. Qed.

(** The left thread sends, the right thread receives. *)
Lemma ps_comLR C a v s s' m m' q :
  src_step s (SOut a v) s' → src_step m (SIn a v) m' →
  rtc src_pstep (C, {[+ s' +]} ⊎ {[+ m' +]}) q → rtc src_pstep (C, {[+ s +]} ⊎ {[+ m +]}) q.
Proof.
  intros Hs Hm Hq. eapply rtc_l; [|exact Hq].
  replace ({[+ s +]} ⊎ {[+ m +]} : gmultiset expr) with (∅ ⊎ {[+ s +]} ⊎ {[+ m +]} : gmultiset expr) by multiset_solver.
  replace ({[+ s' +]} ⊎ {[+ m' +]} : gmultiset expr) with (∅ ⊎ {[+ s' +]} ⊎ {[+ m' +]} : gmultiset expr) by multiset_solver.
  by eapply SPCom.
Qed.

(** The right thread sends, the left thread receives. *)
Lemma ps_comRL C a v s s' m m' q :
  src_step m (SOut a v) m' → src_step s (SIn a v) s' →
  rtc src_pstep (C, {[+ s' +]} ⊎ {[+ m' +]}) q → rtc src_pstep (C, {[+ s +]} ⊎ {[+ m +]}) q.
Proof.
  intros Hm Hs Hq. eapply rtc_l; [|exact Hq].
  replace ({[+ s +]} ⊎ {[+ m +]} : gmultiset expr) with (∅ ⊎ {[+ m +]} ⊎ {[+ s +]} : gmultiset expr) by multiset_solver.
  replace ({[+ s' +]} ⊎ {[+ m' +]} : gmultiset expr) with (∅ ⊎ {[+ m' +]} ⊎ {[+ s' +]} : gmultiset expr) by multiset_solver.
  by eapply SPCom.
Qed.

Ltac sst := first
  [ apply SSHead; first [ apply SHApp; reflexivity | apply SHFix; reflexivity | apply SHLetU
                        | apply SHLetP; reflexivity | apply SHNew | apply SHSpawn; reflexivity
                        | apply SHSend; reflexivity | apply SHRecv; reflexivity ]
  | apply SSAppR; [reflexivity|sst]
  | apply SSAppL; sst
  | apply SSPairR; [reflexivity|sst]
  | apply SSPairL; sst
  | apply SSLetU; sst
  | apply SSLetP; sst ].

(** A thread that waits to send on c steps only by that send. *)
Lemma swait_step K c α e' :
  src_step (App (Lam K) (App ESend (Pair EUnit (Chan c)))) α e' → α = SOut c EUnit.
Proof.
  intros H. inversion H as [? ? ? Hh|? ? ? ? H1|? ? ? ? Hv H1| | | | |]; subst.
  - inversion Hh; subst; simpl in *; done.
  - exfalso. revert H1. apply src_val_no_step. done.
  - inversion H1 as [? ? ? Hh|? ? ? ? H2|? ? ? ? Hv2 H2| | | | |]; subst.
    + by inversion Hh.
    + exfalso. revert H2. apply src_val_no_step. done.
    + exfalso. revert H2. apply src_val_no_step. done.
Qed.

Lemma ms2_elem (e t1 t2 : expr) (E : gmultiset expr) :
  E ⊎ {[+ e +]} = {[+ t1 +]} ⊎ {[+ t2 +]} → e = t1 ∨ e = t2.
Proof.
  intros H. assert (e ∈ {[+ t1 +]} ⊎ {[+ t2 +]}) as He by (rewrite <-H; multiset_solver).
  apply gmultiset_elem_of_disj_union in He as [He|He]; apply gmultiset_elem_of_singleton in He; auto.
Qed.

Lemma ms2_elem2 (e f t1 t2 : expr) (E : gmultiset expr) :
  E ⊎ {[+ e +]} ⊎ {[+ f +]} = {[+ t1 +]} ⊎ {[+ t2 +]} → (e = t1 ∨ e = t2) ∧ (f = t1 ∨ f = t2).
Proof.
  intros H. split; [apply (ms2_elem e t1 t2 (E ⊎ {[+ f +]}))|apply (ms2_elem f t1 t2 (E ⊎ {[+ e +]}))];
    rewrite <-H; multiset_solver.
Qed.

(** Two threads that both wait to send make no step. *)
Lemma swait2_stuck C K1 c1 K2 c2 q :
  ¬ src_pstep (C, {[+ App (Lam K1) (App ESend (Pair EUnit (Chan c1))) +]} ⊎
                  {[+ App (Lam K2) (App ESend (Pair EUnit (Chan c2))) +]}) q.
Proof.
  intros H. inversion H; subst.
  all: first
    [ match goal with
      | Hm : _ ⊎ {[+ ?e +]} ⊎ {[+ ?f +]} = _, Hs : src_step ?e _ _, Hf : src_step ?f (SIn _ _) _ |- _ =>
          apply ms2_elem2 in Hm as [_ [-> | ->]]; apply swait_step in Hf; discriminate
      | Hm : _ ⊎ {[+ ?e +]} ⊎ {[+ ?f +]} = _, Hs : src_step ?e _ _, Hf : src_step ?f _ _ |- _ =>
          apply ms2_elem2 in Hm as [[-> | ->] _]; apply swait_step in Hs; discriminate
      end
    | match goal with
      | Hm : _ ⊎ {[+ ?e +]} = _, Hs : src_step ?e _ _ |- _ =>
          apply ms2_elem in Hm as [-> | ->]; apply swait_step in Hs; discriminate
      end ].
Qed.

Lemma p8_reach : ∃ q, rtc src_pstep (∅, {[+ p8_main +]}) q ∧ src_irred q ∧ q.1 ≠ ∅.
Proof.
  eexists. split_and!.
  - unfold p8_main, st_body, client, dsend.
    eapply ps_beta1; [sst|]. cbn.
    eapply ps_beta1; [sst|]. cbn.
    eapply (ps_new1 _ _ "a"%string); [sst|set_solver|cbn; set_solver|]. cbn.
    eapply ps_beta1; [sst|]. cbn.
    eapply (ps_new1 _ _ "b"%string); [sst|set_solver|cbn; set_solver|]. cbn.
    eapply ps_beta1; [sst|]. cbn.
    eapply ps_spawn1; [sst|]. cbn.
    (* the spawned thread enters client a b *)
    eapply ps_betaL; [sst|]. cbn.
    eapply ps_betaL; [sst|]. cbn.
    eapply ps_betaL; [sst|]. cbn.
    (* the main thread enters dsend b a *)
    eapply ps_betaR; [sst|]. cbn.
    eapply ps_betaR; [sst|]. cbn.
    eapply ps_betaR; [sst|]. cbn.
    (* round 0: a from client to dsend *)
    eapply ps_comLR; [sst|sst|]. cbn.
    eapply ps_betaL; [sst|]. cbn.
    eapply ps_betaR; [sst|]. cbn.
    (* round 0: the first b from dsend to client *)
    eapply ps_comRL; [sst|sst|]. cbn.
    eapply ps_betaL; [sst|]. cbn.
    eapply ps_betaR; [sst|]. cbn.
    (* client starts round 1 *)
    eapply ps_betaL; [sst|]. cbn.
    eapply ps_betaL; [sst|]. cbn.
    apply rtc_refl.
  - intros q. apply swait2_stuck.
  - cbn. set_solver.
Qed.

Theorem p8_not_deadlock_free : ¬ mp_deadlock_free_src p8_main.
Proof.
  intros Hdf. destruct p8_reach as (q & Hq & Hi & Hc).
  destruct (Hdf q Hq Hi) as [H0 _]. by apply Hc.
Qed.

(** Version 2 rejects program 8: a derivation would make it deadlock
    free in their semantics. *)
Theorem p8_not_mtyped : ¬ ∃ ef e', mtyped pc0 [] p8_main MUnit ef e'.
Proof.
  intros (ef & e' & H). apply p8_not_deadlock_free. by eapply mp2_deadlock_free_source.
Qed.

(** ** Matching rates go through version 2

    a has the sequence 1 + 4k, b has 2 + 2k. Both functions name the
    heads p of a and q of b and ask p < q < p + 2. A round of hrecv
    acts at p, q and q + 2 while it holds the other channel at q, p + 4
    and p + 4, and the recursive call moves both heads by 4. dsend acts
    at p, q and q + 2 in the same pattern. *)

Lemma oeq_std v ts j n d :
  oeq (DCh (mclose v ts stream) (pclose v (PV j n)) d)
      (DCh (mclose v ts (MSeq (MSnd (PV j n) MPUnit) stream)) (pclose v (PV j (n + d))) d).
Proof. apply oeq_hdt. cbn. by rewrite Z.add_0_r, Z.add_assoc. Qed.

Lemma m_inst_std Θ Γ e e' pol j n d ef :
  pc_nt Θ = 0 →
  mtyped Θ Γ e (MCh pol stream (PR (PV j n) d)) ef e' →
  mtyped Θ Γ e (MCh pol (MSeq (MSnd (PV j n) MPUnit) stream) (PR (PV j (n + d)) d)) ef e'.
Proof.
  intros Hnt H. eapply m_eq; [exact H|]. split.
  - intros ss Hl _. rewrite Hnt in Hl. destruct ss; [|discriminate]. rewrite !sinst_nil.
    exact seq_st.
  - split; [done|]. intros v ts _. apply oeq_std.
Qed.

Definition rr_ty (lt : Z → Z → Prop) (d1 d2 : Z) : mty :=
  MPoly (cl_ctx lt) (MCh false stream (PR (PV 0 0) d1)) []
    (MArr (MCh true stream (PR (PV 1 0) d2)) [LC stream (PV 0 0) d1] [PTop] MUnit).

(** hrecv names (p, q), dsend names (q, p). *)
Definition hr_lt (p q : Z) : Prop := (p < q < p + 2)%Z.
Definition ds_lt (q p : Z) : Prop := (p < q < p + 2)%Z.

Ltac plt_rr :=
  right; intros ?v ?ts [-> (?p & ?q & -> & ?Hpq)] ?l ?Hl; simpl in Hl;
  repeat (apply elem_of_cons in Hl as [->|Hl]; [cbn; unfold hr_lt, ds_lt in *; lia|]); by apply elem_of_nil in Hl.

Lemma pok_rr lt : (∀ p q, lt p q → lt (p + 4) (q + 4))%Z →
  pinst_ok (cl_ctx lt) (cl_ctx lt) [PV 0 4; PV 1 4] [].
Proof.
  intros Hlt. split_and!; [done|done|repeat constructor|constructor|intros ss _ _; constructor|].
  intros v ts [-> (p & q & -> & Hpq)]. split; [done|]. exists (p + 4)%Z, (q + 4)%Z. split; [done|]. by apply Hlt.
Qed.

Lemma tpure_rr k d1 d2 : tpure k (MCh false stream (PR (PV 0 0) d1)) ∧
  tpure k (MArr (MCh true stream (PR (PV 1 0) d2)) [LC stream (PV 0 0) d1] [PTop] MUnit).
Proof. split; cbn; repeat split; repeat constructor. Qed.

Lemma hrecv_typed Θ : ∃ e', mtyped Θ [] hrecv (rr_ty hr_lt 4 2) [] e'.
Proof.
  eexists. unfold hrecv, rr_ty.
  eapply m_fix; [allun|apply (tpure_rr 0 4 2)|apply (tpure_rr 0 4 2)|exists [0%Z; 1%Z], []; split; [done|]; exists 0%Z, 1%Z; split; [done|]; unfold hr_lt; lia| |left; done].
  eapply m_lam.
  eapply (m_sub _ _ _ _ _ _ [PTop]); [|right; left; set_solver].
  eapply (m_let _ _ [None; Some _; None] [Some _; None; Some _]); [msp| | |].
  - eapply (m_send _ _ [None; None; None] [None; Some _; None] _ _ _ _ false (PV 0 0) MPUnit stream (PR (PV 0 4) 4));
      [msp|apply m_unit; allun| |split; [done|split; [apply plt_none|plt_rr]]|apply plt_nil|apply plt_none].
    apply (m_inst_std _ _ _ _ _ 0 0 4); [done|]. apply m_var; onlyun.
  - eapply (m_recv _ _ [None; Some _; None; None] [Some _; None; None; Some _] _ _ _ _ true (PV 1 0) MPUnit stream (PR (PV 1 2) 2));
      [msp| |split; [done|split; [apply plt_none|plt_rr]]| |].
    + apply (m_inst_std _ _ _ _ _ 1 0 2); [done|]. apply m_var; onlyun.
    + eapply (m_recv _ _ [Some _; None; None; None; None; None] [None; Some _; Some _; None; None; Some _]
                _ _ _ _ true (PV 1 2) MPUnit stream (PR (PV 1 4) 2));
        [msp| |split; [done|split; [apply plt_none|plt_rr]]| |].
      * apply (m_inst_std _ _ _ _ _ 1 2 2); [done|]. apply m_var; onlyun.
      * eapply (m_app _ _ [None; Some _; None; Some _; Some _; None; None; Some _] [Some _; None; None; None; None; None; None; None]);
          [msp| | |apply plt_nil|apply plt_nil].
        -- eapply (m_app_poly' _ _ [None; Some _; None; Some _; None; None; None; Some _] [None; None; None; None; Some _; None; None; None]
                    _ _ _ _ _ _ _ _ _ _ [PV 0 4; PV 1 4] []);
             [msp|apply m_var; onlyun|apply pok_rr; unfold hr_lt; lia|apply (tpure_rr 0 4 2)|apply (tpure_rr 0 4 2)|apply m_var; onlyun
             |apply plt_nil|apply pntop_nil|reflexivity|reflexivity].
        -- apply m_var; onlyun.
      * plt_rr.
    + plt_rr.
  - plt_rr.
Qed.

Lemma dsend_typed Θ : ∃ e', mtyped Θ [] dsend (rr_ty ds_lt 2 4) [] e'.
Proof.
  eexists. unfold dsend, rr_ty.
  eapply m_fix; [allun|apply (tpure_rr 0 2 4)|apply (tpure_rr 0 2 4)|exists [1%Z; 0%Z], []; split; [done|]; exists 1%Z, 0%Z; split; [done|]; unfold ds_lt; lia| |left; done].
  eapply m_lam.
  eapply (m_sub _ _ _ _ _ _ [PTop]); [|right; left; set_solver].
  eapply (m_recv _ _ [Some _; None; None] [None; Some _; Some _] _ _ _ _ true (PV 1 0) MPUnit stream (PR (PV 1 4) 4));
    [msp| |split; [done|split; [apply plt_none|plt_rr]]| |].
  - apply (m_inst_std _ _ _ _ _ 1 0 4); [done|]. apply m_var; onlyun.
  - eapply (m_let _ _ [None; None; None; Some _; None] [Some _; Some _; None; None; Some _]); [msp| | |].
    + eapply (m_send _ _ [None; None; None; None; None] [None; None; None; Some _; None] _ _ _ _ false (PV 0 0) MPUnit stream (PR (PV 0 2) 2));
        [msp|apply m_unit; allun| |split; [done|split; [apply plt_none|plt_rr]]|apply plt_nil|apply plt_none].
      apply (m_inst_std _ _ _ _ _ 0 0 2); [done|]. apply m_var; onlyun.
    + eapply (m_let _ _ [Some _; None; None; None; None; None] [None; Some _; Some _; None; None; Some _]); [msp| | |].
      * eapply (m_send _ _ [None; None; None; None; None; None] [Some _; None; None; None; None; None] _ _ _ _ false (PV 0 2) MPUnit stream (PR (PV 0 4) 2));
          [msp|apply m_unit; allun| |split; [done|split; [apply plt_none|plt_rr]]|apply plt_nil|apply plt_none].
        apply (m_inst_std _ _ _ _ _ 0 2 2); [done|]. apply m_var; onlyun.
      * eapply (m_app _ _ [Some _; None; None; Some _; None; None; Some _] [None; None; Some _; None; None; None; None]);
          [msp| | |apply plt_nil|apply plt_nil].
        -- eapply (m_app_poly' _ _ [None; None; None; Some _; None; None; Some _] [Some _; None; None; None; None; None; None]
                    _ _ _ _ _ _ _ _ _ _ [PV 0 4; PV 1 4] []);
             [msp|apply m_var; onlyun|apply pok_rr; unfold ds_lt; lia|apply (tpure_rr 0 2 4)|apply (tpure_rr 0 2 4)|apply m_var; onlyun
             |apply plt_nil|apply pntop_nil|reflexivity|reflexivity].
        -- apply m_var; onlyun.
      * plt_rr.
    + plt_rr.
  - plt_rr.
Qed.

Lemma rr_main_typed : ∃ ef e', mtyped pc0 [] rr_main MUnit ef e'.
Proof.
  destruct (hrecv_typed pc0) as [eh Hh]. destruct (dsend_typed pc0) as [ed Hd].
  do 2 eexists. unfold rr_main.
  eapply (m_app _ _ [] []); [msp| |exact Hd|apply plt_none|apply plt_nil].
  eapply (m_app _ _ [] []); [msp| |exact Hh|apply plt_none|apply plt_nil].
  eapply m_lam. eapply m_lam. unfold st_body.
  eapply (m_new _ _ _ _ stream (PZ 1) 4). eapply (m_new _ _ _ _ stream (PZ 2) 2).
  eapply (m_letu _ _ [Some _; None; None; Some _; None; Some _] [None; Some _; Some _; None; Some _; Some _]);
    [msp| | |apply plt_nil].
  - eapply m_fork. eapply m_lam.
    eapply (m_app _ _ [None; None; None; None; Some _; None; Some _] [Some _; Some _; None; None; None; None; None]);
      [msp| | |apply plt_nil|apply plt_nil].
    + eapply (m_app_poly' _ _ [None; None; None; None; None; None; Some _] [None; None; None; None; Some _; None; None]
                _ _ _ _ _ _ _ _ _ _ [PZ 1; PZ 2] []);
        [msp|apply m_var; onlyun|apply pok_main; unfold hr_lt; lia|apply (tpure_rr 0 4 2)|apply (tpure_rr 0 4 2)|apply m_var; onlyun
        |apply plt_nil|apply pntop_nil|reflexivity|reflexivity].
    + apply m_var; onlyun.
  - eapply (m_app _ _ [None; Some _; None; None; Some _; Some _] [None; None; Some _; None; None; None]);
      [msp| | |apply plt_nil|apply plt_nil].
    + eapply (m_app_poly' _ _ [None; None; None; None; Some _; Some _] [None; Some _; None; None; None; None]
                _ _ _ _ _ _ _ _ _ _ [PZ 2; PZ 1] []);
        [msp|apply m_var; onlyun|apply pok_main; unfold ds_lt; lia|apply (tpure_rr 0 2 4)|apply (tpure_rr 0 2 4)|apply m_var; onlyun
        |apply plt_nil|apply pntop_nil|reflexivity|reflexivity].
    + apply m_var; onlyun.
Qed.

Theorem rr_mp2_deadlock_free : ∃ ef e', mtyped pc0 [] rr_main MUnit ef e' ∧ deadlock_free (∅, {[+ e' +]}).
Proof.
  destruct rr_main_typed as (ef & e' & H). exists ef, e'. split; [done|]. by eapply mp2_deadlock_free.
Qed.

Theorem rr_deadlock_free_src : mp_deadlock_free_src rr_main.
Proof. destruct rr_main_typed as (ef & e' & H). by eapply mp2_deadlock_free_source. Qed.
