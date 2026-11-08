(** * Junk renaming for the live relation (invariance/JunkRenaming.v)

    [LPrel_junk]: a process that holds neither end of x and does not
    restrict x stays related when x is renamed to b. The proof follows
    [Prel_junk]. The τ steps of β, new, spawn and link and the external
    links stay at the index and are read inductively, the other steps are read one or two levels
    down, where the outer induction applies. The stepping lemmas are
    reused from JunkRenaming.v. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export liveness.LiveRenaming liveness.LiveTermRules invariance.JunkRenaming.

Local Set Warnings "-register-all".
Set Default Proof Using "All".

(** ** Inversion of the classified τ steps *)

Lemma padmin_inv C E p' :
  padmin (C, E) p' →
  (∃ F e e', E = F ⊎ {[+ e +]} ∧ tstep e LBeta e' ∧ p' = (C, F ⊎ {[+ e' +]}))
  ∨ (∃ F e c e', E = F ⊎ {[+ e +]} ∧ tstep e (LNew c) e' ∧
       c ∉ C ∧ c ∉ echans F ∧ c ∉ fchans e ∧ p' = (C ∪ {[c]}, F ⊎ {[+ e' +]}))
  ∨ (∃ F e v e', E = F ⊎ {[+ e +]} ∧ tstep e (LSpawn v) e' ∧
       p' = (C, F ⊎ {[+ e' +]} ⊎ {[+ App v EUnit +]}))
  ∨ ptau_link (C, E) p'.
Proof.
  intros H. inversion H; simplify_eq.
  - left. eauto 10.
  - right; left. eauto 12.
  - right; right; left. eauto 12.
  - right; right; right. eexists _, _, _, _, _, _. split_and!; [done|eassumption|done|done].
Qed.

Lemma pcomm_inv C E p' :
  pcomm (C, E) p' →
  (∃ F c v e e' f f', E = F ⊎ {[+ e +]} ⊎ {[+ f +]} ∧
     tstep e (LSess (SSend c v)) e' ∧ tstep f (LSess (SRecv c v)) f' ∧
     p' = (C, F ⊎ {[+ e' +]} ⊎ {[+ f' +]}))
  ∨ (∃ F c e e' f f', E = F ⊎ {[+ e +]} ⊎ {[+ f +]} ∧
       tstep e (LSess (SClos c)) e' ∧ tstep f (LSess (SClos c)) f' ∧
       c ∈ C ∧ p' = (C ∖ {[c]}, F ⊎ {[+ e' +]} ⊎ {[+ f' +]}))
  ∨ (∃ F c i e e' f f', E = F ⊎ {[+ e +]} ⊎ {[+ f +]} ∧
       tstep e (LSess (SSel c i)) e' ∧ tstep f (LSess (SBra c i)) f' ∧
       p' = (C, F ⊎ {[+ e' +]} ⊎ {[+ f' +]})).
Proof.
  intros H. inversion H; simplify_eq.
  - left. eauto 14.
  - right; left. eauto 14.
  - right; right. eauto 14.
Qed.

(** ** Reading the clauses at the base world *)

Lemma LPstep_mono (X Y : world → senv → ty → proc → Prop) n W Σ T p :
  (∀ W Σ T p, X W Σ T p → Y W Σ T p) → LPstep X n W Σ T p → LPstep Y n W Σ T p.
Proof.
  intros HXY H W1 HW1. destruct (H W1 HW1) as (Hs & Hr & Ha & Hc & Hl & Hσ).
  split_and!; [done|done| |done| |done].
  - intros p' Hst Hd L. destruct (Ha p' Hst Hd L) as (N & W' & ? & ? & ?). exists N, W'. auto.
  - intros cd p' Hst. eapply Plink_case_mono; [|exact (Hl cd p' Hst)]. auto.
Qed.

Lemma LPrel_S_plink n W Σ T p cd p' :
  LPrel (S n) W Σ T p → proc_step p (PSess (SLink cd)) p' →
  Plink_case (LPrel (S n)) W Σ T cd p'.
Proof.
  intros HP Hst. apply LPrel_S_iff in HP. destruct (HP W (wext_r_refl W)) as (_ & _ & _ & _ & H & _).
  by apply H.
Qed.

Lemma LPrel_S_sess n W Σ T p σ p' :
  LPrel (S n) W Σ T p → proc_step p (PSess σ) p' →
  LPobl LVrel LPrel (S n) W Σ T p σ p'.
Proof.
  intros HP Hst. apply LPrel_S_iff in HP. destruct (HP W (wext_r_refl W)) as (_ & _ & _ & _ & _ & H).
  by apply H.
Qed.

Lemma LPrel_S_irred n W Σ T p :
  LPrel (S n) W Σ T p → pirred p →
  ∃ v E, p = (∅, {[+ v +]} ⊎ E) ∧ is_val v ∧ LVrel (S n) W (tenv_of Σ) T v ∧
         (∀ e, e ∈ E → e = EUnit).
Proof.
  intros HP Hirr. apply LPrel_S_iff in HP. destruct (HP W (wext_r_refl W)) as (H & _).
  by apply H.
Qed.

Lemma LPrel_S_ready n W Σ T p : LPrel (S n) W Σ T p → ¬ pirred p → ready_p W Σ p.
Proof.
  intros HP Hirr. apply LPrel_S_iff in HP. destruct (HP W (wext_r_refl W)) as (_ & H & _).
  by apply H.
Qed.

(** Every external offer of a related process is on interface channels. *)
Lemma LPrel_offer_dom n W Σ T C E0 e σ e' :
  LPrel (S n) W Σ T (C, E0 ⊎ {[+ e +]}) → tstep e (LSess σ) e' → subjs σ ## C →
  subjs σ ⊆ dom Σ.
Proof.
  intros HP Hst Hd.
  pose proof (LPrel_S_sess _ _ _ _ _ _ _ HP (PStepSession C E0 e σ e' Hst Hd)) as Hc.
  destruct σ as [c w|c w|c|cd|c i|c i]; simpl in Hc |- *;
    [| | |pose proof (LPrel_S_plink _ _ _ _ _ _ _ HP (PStepSession C E0 e (SLink cd) e' Hst Hd)) as Hc'; clear Hc; rename Hc' into Hc| |].
  5,6: destruct Hc as (Σ1 & s1 & s2 & k & Hhd & _); apply senv_hd_dom in Hhd; set_solver.
  - destruct Hc as (Σ1 & m & U & s & k & Hhd & _). apply senv_hd_dom in Hhd. set_solver.
  - destruct Hc as (?&?&?&?&?&?&?&?&Hhd&_). apply senv_hd_dom in Hhd. set_solver.
  - destruct Hc as (Σ1 & k & Hhd & _). apply senv_hd_dom in Hhd. set_solver.
  - destruct Hc as (c & d & Σ1 & sc & sd & kc & kd & -> & _ & -> & _).
    rewrite !dom_insert_L. set_solver.
Qed.

Lemma LVrel_chsubst_id n W Θ U w x b :
  x ∉ dom Θ → LVrel n W Θ U w → chsubst x b w = w.
Proof.
  intros Hx HV. apply chsubst_id.
  rewrite (LVrel_fchans _ _ _ _ _ HV). exact Hx.
Qed.

(** [set_solver] after dropping the large hypotheses of the transport. *)
Local Ltac sset :=
  repeat match goal with
    | H : ?P |- _ =>
        lazymatch P with
        | context [LPrel] => clear H
        | context [LPobl] => clear H
        | context [LPstep] => clear H
        | context [proc_step] => clear H
        | context [offered_p] => clear H
        | context [LVrel] => clear H
        | context [tstep] => clear H
        end
    end; set_solver.

(** ** The transport *)

Lemma LPrel_junk n : ∀ W Σ T C E x b,
  x ∉ dom Σ → x ∉ C → (b ∈ C → b ∉ dom Σ) → b ≠ x →
  LPrel n W Σ T (C, E) → LPrel n W Σ T (C, echsubst x b E).
Proof.
  induction n as [n IHn] using lt_wf_ind.
  intros W Σ T C E x b HxΣ HxC HbC Hbx HP.
  destruct n as [|n']; [apply LPrel_0|].
  assert (IH1 : ∀ W0 Σ0 C0 E0 b0, x ∉ dom Σ0 → x ∉ C0 → (b0 ∈ C0 → b0 ∉ dom Σ0) →
             b0 ≠ x → LPrel n' W0 Σ0 T (C0, E0) → LPrel n' W0 Σ0 T (C0, echsubst x b0 E0)).
  { intros. apply IHn; [lia|done..]. }
  assert (IH2 : ∀ W0 Σ0 C0 E0 b0, x ∉ dom Σ0 → x ∉ C0 → (b0 ∈ C0 → b0 ∉ dom Σ0) →
             b0 ≠ x → LPrel (pred n') W0 Σ0 T (C0, E0) →
             LPrel (pred n') W0 Σ0 T (C0, echsubst x b0 E0)).
  { intros. apply IHn; [lia|done..]. }
  revert W Σ C E HP b HxΣ HxC HbC Hbx.
  cut (∀ W Σ T' p, LPrel (S n') W Σ T' p → T' = T → ∀ C E b, p = (C, E) →
         x ∉ dom Σ → x ∉ C → (b ∈ C → b ∉ dom Σ) → b ≠ x →
         LPrel (S n') W Σ T (C, echsubst x b E)).
  { intros H W Σ C E HP b ????. by eapply H. }
  refine (LPrel_S_ind n' _ _).
  intros W Σ T' p H -> C E b -> HxΣ HxC HbC Hbx.
  assert (HP : LPrel (S n') W Σ T (C, E)).
  { apply LPrel_S_iff. eapply LPstep_mono; [|exact H]. by intros ? ? ? ? [? _]. }
  assert (Hoff : ∀ E0 e σ e', E = E0 ⊎ {[+ e +]} → tstep e (LSess σ) e' →
                   subjs σ ## C → x ∉ subjs σ).
  { intros E0 e σ e' -> Hst Hd Hx. apply HxΣ.
    by apply (LPrel_offer_dom _ _ _ _ _ _ _ _ _ HP Hst Hd). }
  (* a step whose preimage subjects avoid C but contain x is impossible *)
  assert (Hpre : ∀ E0 e σ e', E = E0 ⊎ {[+ e +]} → tstep e (LSess σ) e' →
                   gsub x b (subjs σ) ## C → x ∉ subjs σ).
  { intros E0 e σ e' HE Hst Hd Hx. apply (Hoff E0 e σ e' HE Hst); [|done].
    apply elem_of_disjoint. intros y Hy HyC.
    destruct (decide (y = x)) as [->|Hyx]; [done|].
    apply (elem_of_disjoint _ _) in Hd. apply (Hd y); [|done].
    unfold gsub. apply elem_of_map. exists y. by rewrite csub_ne. }
  (* forward: a τ step of the original gives one of the image *)
  assert (Hfwd_tau : ∀ q, proc_step (C, E) PTau q →
            ∃ q', proc_step (C, echsubst x b E) PTau q').
  { intros q Hq.
    apply ptau_inv in Hq as
      [ (F & e & e' & -> & Hts & _)
      | [ (F & e & c & e' & -> & Hts & _)
      | [ (F & e & v & e' & -> & Hts & _)
      | [ (F & c & v & e & e' & f & f' & -> & Hts & Htr & _)
      | [ (F & c & e & e' & f & f' & -> & Hts & Htr & HcC & _)
      | [ (F & e & c & d & e' & -> & Hts & HcC & _)
      | (F & c & i & e & e' & f & f' & -> & Hts & Htr & _) ]]]]]].
    - apply (tstep_chsubst x b) in Hts. eexists.
      rewrite echsubst_disj_union1. by apply PStepBeta.
    - apply (tstep_chsubst x b) in Hts. simpl in Hts.
      destruct (exist_fresh (C ∪ echans (echsubst x b F) ∪ fchans (chsubst x b e))) as [z Hz].
      destruct (new_retarget _ _ _ z Hts) as [e'' He''].
      eexists. rewrite echsubst_disj_union1. apply PStepNew; [done|set_solver..].
    - apply (tstep_chsubst x b) in Hts. eexists.
      rewrite echsubst_disj_union1. by apply PStepSpawn.
    - apply (tstep_chsubst x b) in Hts, Htr. eexists.
      rewrite echsubst_disj_union2. by eapply PStepMsg.
    - assert (c ≠ x) by set_solver.
      apply (tstep_chsubst x b) in Hts, Htr. simpl in Hts, Htr.
      rewrite csub_ne in Hts, Htr by done. eexists.
      rewrite echsubst_disj_union2. by eapply PStepClose.
    - assert (c ≠ x) by set_solver.
      apply (tstep_chsubst x b) in Hts. simpl in Hts. rewrite gsub_upair, csub_ne in Hts by done.
      eexists. rewrite echsubst_disj_union1. by eapply PStepLink.
    - apply (tstep_chsubst x b) in Hts, Htr. simpl in Hts, Htr. eexists.
      rewrite echsubst_disj_union2. by eapply PStepChoice. }
  assert (Hfwd_sess : ∀ σ q, proc_step (C, E) (PSess σ) q →
            ∃ q', proc_step (C, echsubst x b E) (PSess (ssub x b σ)) q').
  { intros σ q Hq. apply proc_step_sess_inv in Hq as (F & e & e' & HE & Hst & Hd & _).
    pose proof (Hoff _ _ _ _ HE Hst Hd) as Hx.
    apply (tstep_chsubst x b) in Hst. simpl in Hst. eexists.
    rewrite HE, echsubst_disj_union1. apply PStepSession; [done|].
    by rewrite subjs_ssub, gsub_id. }
  assert (Hoffers : ∀ k, offered_p Σ (C, E) k ↔ offered_p Σ (C, echsubst x b E) k).
  { intros k. split.
    - intros (σ & q & Hq & Hsel). pose proof Hq as Hq'.
      apply proc_step_sess_inv in Hq' as (F & e & e' & HE & Hst & Hd & _).
      pose proof (Hoff _ _ _ _ HE Hst Hd) as Hx.
      destruct (Hfwd_sess σ q Hq) as [q' Hq''].
      exists (ssub x b σ), q'. split; [done|].
      assert (ssub_rel x b σ (ssub x b σ)) as Hr by (destruct σ; simpl; done).
      apply (ssub_rel_select x b Σ σ (ssub x b σ) k Hr); [|done].
      by rewrite subjs_ssub, gsub_id.
    - intros (σ' & q & Hq & Hsel).
      apply proc_step_sess_inv in Hq as (F' & e1 & e1' & HE & Hst & Hd & _).
      apply echsubst_decomp in HE as (F & e & -> & -> & ->).
      destruct (tstep_chsubst_back x b e σ' e1' Hst) as (σ & f & Hf & Hr).
      pose proof (ssub_rel_subjs _ _ _ _ Hr) as Hs.
      assert (x ∉ subjs σ) as Hx.
      { apply (Hpre F e σ f eq_refl Hf). by rewrite <-Hs. }
      rewrite gsub_id in Hs by done.
      exists σ, (C ∖ sentc σ, F ⊎ {[+ f +]}). split.
      + apply PStepSession; [done|]. by rewrite <-Hs.
      + by apply (ssub_rel_select x b Σ σ σ' k Hr). }
  apply LPrel_S_iff. intros W1 HW1.
  destruct (H W1 HW1) as (Hirr & Hrdy & Had & Hc & Hl & Hσ).
  assert (Had' : ∀ p', padmin (C, E) p' → p'.1 ## dom Σ → ∀ L : gset pname,
            ∃ N W', N ## L ∪ senv_roots Σ ∪ ty_roots T ∧ wext_fresh W1 N W' ∧
              LPrel (S n') W' Σ T p' ∧ ∀ C E b, p' = (C, E) →
                x ∉ dom Σ → x ∉ C → (b ∈ C → b ∉ dom Σ) → b ≠ x →
                LPrel (S n') W' Σ T (C, echsubst x b E)).
  { intros p' Hp Hd L. destruct (Had p' Hp Hd L) as (N & W' & ? & ? & HP' & HΦ).
    exists N, W'. split_and!; [done|done|done|]. intros. by eapply HΦ. }
  clear Had H. rename Had' into Had.
  split_and!.
  - (* P-Stop *)
    intros Hpirr.
    assert (pirred (C, E)) as Hp0.
    { intros π q Hq. destruct π as [|σ].
      - destruct (Hfwd_tau q Hq) as [q' Hq']. by apply (Hpirr PTau q').
      - destruct (Hfwd_sess σ q Hq) as [q' Hq']. by apply (Hpirr (PSess (ssub x b σ)) q'). }
    destruct (Hirr Hp0) as (v & E1 & Heq & Hv & HVv & HE1).
    injection Heq as -> ->.
    exists v, (echsubst x b E1). split_and!.
    + rewrite echsubst_disj_union, echsubst_singleton.
      assert (x ∉ dom (tenv_of Σ)) as HxΣ' by (unfold tenv_of; by rewrite dom_fmap_L).
      by rewrite (LVrel_chsubst_id _ _ _ _ _ x b HxΣ' HVv).
    + done.
    + done.
    + intros e0 He0. unfold echsubst in He0.
      apply elem_of_gmultiset_map in He0 as (f0 & -> & Hf0). by rewrite (HE1 _ Hf0).
  - (* readiness *)
    intros Hnirr Hs.
    assert (stable_p (C, E)) as Hs0.
    { intros q Hq. destruct (Hfwd_tau q Hq) as [q' Hq']. exact (Hs q' Hq'). }
    assert (∀ E1 v, (C, E) = (∅, {[+ v +]} ⊎ E1) → is_val v → (∀ e, e ∈ E1 → e = EUnit) →
              terminated (C, echsubst x b E)) as Hterm.
    { intros E1 v Heq Hv HE1. injection Heq as -> ->.
      exists (chsubst x b v), (echsubst x b E1). split_and!.
      - by rewrite echsubst_disj_union, echsubst_singleton.
      - by rewrite is_val_chsubst.
      - intros e0 He0. unfold echsubst in He0.
        apply elem_of_gmultiset_map in He0 as (f0 & -> & Hf0). by rewrite (HE1 _ Hf0). }
    assert (¬ pirred (C, E)) as Hni.
    { intros Hp0. apply Hnirr. destruct (Hirr Hp0) as (v & E1 & Heq & Hv & _ & HE1).
      apply terminated_pirred. by apply (Hterm E1 v). }
    destruct (Hrdy Hni Hs0) as [(cd & q & Hq)|[Hv Ha]].
    { left. destruct (Hfwd_sess _ _ Hq) as [q' Hq']. by exists (gsub x b cd), q'. }
    right. split.
    + intros Hno. destruct (Hv (λ k Ho, Hno k (proj1 (Hoffers k) Ho)))
        as (v & E1 & Heq & Hvv & HE1).
      by apply (Hterm E1 v).
    + intros k e He Hk. destruct (Ha k e He) as (k' & e' & Ho & He' & Hlt).
      { intros Ho. apply Hk. by apply Hoffers. }
      exists k', e'. split_and!; [by apply Hoffers|done|done].
  - (* Q-Admin *)
    intros q Hst Hd L.
    apply padmin_inv in Hst as
      [ (F' & e' & e'' & HeqE & Hts & ->)
      | [ (F' & e' & c & e'' & HeqE & Hts & HcC & HcF & Hce & ->)
      | [ (F' & e' & v' & e'' & HeqE & Hts & ->)
      | (C0 & F' & e' & c & d & e'' & HeqP & Hts & HcC & Hq) ]]].
    + (* β *)
      apply echsubst_decomp in HeqE as (F & f & -> & -> & ->).
      apply tstep_chsubst_det_inv in Hts as (α & f0 & Hf0 & Hα & ->); [|done].
      apply eq_sym, lsub_beta in Hα as ->.
      destruct (Had _ (PABeta _ _ _ _ Hf0) Hd L) as (N & W2 & HN & Hfr & _ & HΦ).
      exists N, W2. split_and!; [done|done|].
      rewrite <-echsubst_disj_union1. by apply HΦ.
    + (* new *)
      apply echsubst_decomp in HeqE as (F & f & -> & -> & ->).
      destruct (decide (c = b)) as [->|Hcb].
      { (* new at b: the substitution was trivial *)
        assert (x ∉ fchans f) as Hxf by (intros Hx; by apply Hce, fchans_chsubst_hit).
        assert (x ∉ echans F) as HxF by (intros Hx; by apply HcF, echans_echsubst_hit).
        rewrite (chsubst_id x b f) in Hts, Hce by done.
        rewrite (echsubst_id x b F) in HcF |- * by done.
        destruct (Had _ (PANew C F f b e'' Hts HcC HcF Hce) Hd L) as (N & W2 & HN & Hfr & HP' & _).
by exists N, W2. }
      destruct (decide (c = x)) as [->|Hcx].
      { (* new at x: freshen through z, then transpose back *)
        destruct (exist_fresh (C ∪ dom Σ ∪ echans F ∪ fchans f ∪ {[x; b]})) as [z Hz].
        destruct (tstep_chsubst_new_inv x b f x e'' Hts z) as (f0 & Hf0 & ->);
          [set_solver..|].
        assert (padmin (C, F ⊎ {[+ f +]}) (C ∪ {[z]}, F ⊎ {[+ f0 +]})) as Horig.
        { apply PANew; [done|set_solver..]. }
        destruct (Had _ Horig ltac:(simpl; set_solver) L) as (N & W2 & HN & Hfr & _ & HΦ).
        exists N, W2. split_and!; [done|done|].
        refine (imp4 _ _ _ _ _ _ (HΦ _ _ b eq_refl) (λ HP', _) _ _ _ _); [|done|set_solver| |done].
        2: { intros Hb. apply HbC. set_solver. }
        apply (LPrel_swap_restricted x z) in HP'; [|done|set_solver].
        unfold pswap in HP'. simpl in HP'.
        rewrite echsubst_disj_union1, msswap_disj_union, msswap_singleton in HP'.
        rewrite (msswap_fresh x z (echsubst x b F)) in HP';
          [|apply echans_echsubst_notin; congruence|].
        2: { pose proof (echans_echsubst_sub x b F) as Hsub. set_solver. }
        assert (gswap x z (C ∪ {[z]}) = C ∪ {[x]}) as Hg.
        { apply set_eq. intros y. rewrite elem_of_gswap'. unfold cswap.
          repeat case_decide; subst; set_solver. }
        rewrite Hg in HP'.
        assert (eswap x z (chsubst x b f0) = chsubst z x (chsubst x b f0)) as He.
        { rewrite eswap_comm. rewrite <-(chsubst_id x z (chsubst x b f0)) at 1;
            [apply eswap_chsubst_flip|]. apply fchans_chsubst_notin. congruence. }
        by rewrite <-He. }
      assert (c ∉ fchans f) as Hcf.
      { pose proof (fchans_chsubst_sup x b f). set_solver. }
      destruct (tstep_chsubst_new_inv x b f c e'' Hts c Hcf Hcx Hcb) as (f0 & Hf0 & ->).
      rewrite chsubst_refl.
      assert (c ∉ echans F) as HcF0.
      { pose proof (echans_echsubst_sup x b F). set_solver. }
      destruct (Had _ (PANew C F f c f0 Hf0 HcC HcF0 Hcf) Hd L)
        as (N & W2 & HN & Hfr & _ & HΦ).
      exists N, W2. split_and!; [done|done|].
      rewrite <-echsubst_disj_union1. apply (HΦ _ _ b eq_refl); [done|set_solver| |done].
      intros Hb. apply HbC. set_solver.
    + (* spawn *)
      apply echsubst_decomp in HeqE as (F & f & -> & -> & ->).
      apply tstep_chsubst_det_inv in Hts as (α & f0 & Hf0 & Hα & ->); [|done].
      destruct α as [| | |v]; simpl in Hα; try discriminate. injection Hα as ->.
      destruct (Had _ (PASpawn _ _ _ _ _ Hf0) Hd L) as (N & W2 & HN & Hfr & _ & HΦ).
      exists N, W2. split_and!; [done|done|].
      refine (imp4 _ _ _ _ _ _ (HΦ _ _ b eq_refl) (λ HP', _) _ _ _ _); [|done..].
      by rewrite !echsubst_disj_union, !echsubst_singleton in HP'.
    + (* link, a τ at the index *)
    injection HeqP as <- HeqE. subst q.
    apply echsubst_decomp in HeqE as (F & f & -> & -> & ->).
    apply tstep_chsubst_det_inv in Hts as (α & f0 & Hf0 & Hα & ->); [|done].
    destruct α as [|[c0 w0|c0 w0|c0|cd0|c0 i0|c0 i0]| |]; simpl in Hα; try discriminate.
    injection Hα as Hcd.
    destruct (tstep_link_shape _ _ _ Hf0) as (c0 & d0 & ->).
    assert (c ≠ x) as Hcx by set_solver.
    rewrite <-echsubst_disj_union1.
    assert (∀ C', C' ⊆ C ∖ {[c]} ∪ {[b]} → b ∈ C → C' ## dom Σ) as Hguard.
    { intros C' HC' HbC'. apply elem_of_disjoint. intros y Hy1 Hy2.
      apply HC' in Hy1. apply elem_of_union in Hy1 as [Hy1| ->%elem_of_singleton].
      - by apply (elem_of_disjoint _ _) in Hd; apply (Hd y).
      - by apply (HbC HbC'). }
    destruct (decide (x = c0 ∨ x = d0)) as [Hx|Hx].
    { (* the original links the junk x with a restricted d1 *)
      assert (∃ d1, {[c0; d0]} = ({[x; d1]} : gset chan)) as [d1 Hxd1].
      { destruct Hx as [<-|<-]; [by exists d0|exists c0; by rewrite upair_comm]. }
      rewrite Hxd1 in Hf0, Hcd. rewrite gsub_upair, csub_hit in Hcd.
      assert (d1 ≠ x) as Hd1x.
      { intros ->. apply (Hoff F f (SLink {[x; x]}) f0); [done|done| |simpl; set_solver].
        simpl. set_solver. }
      rewrite csub_ne in Hcd by done.
      assert (d1 ∈ C) as Hd1C.
      { destruct (decide (d1 ∈ C)) as [|Hn]; [done|]. exfalso.
        apply (Hoff F f (SLink {[x; d1]}) f0); [done|done| |simpl; set_solver].
        simpl. set_solver. }
      rewrite upair_comm in Hf0.
      symmetry in Hcd.
      assert (c ∈ ({[b; d1]} : gset chan)) as Hc'.
      { rewrite Hcd. apply elem_of_union; left. by apply elem_of_singleton. }
      assert (b ≠ d1 → (c = b ∧ d = d1) ∨ (c = d1 ∧ d = b)) as Hcases.
      { intros Hbd. apply upair_eq_inv in Hcd; [|done]. naive_solver. }
      assert ((C ∖ {[d1]}) ## dom Σ) as Hd'.
      { destruct (decide (b = d1)) as [->|Hbd].
        - assert (c = d1) as ->.
          { apply elem_of_union in Hc' as [?%elem_of_singleton|?%elem_of_singleton]; done. }
          done.
        - destruct (Hcases Hbd) as [[-> ->]|[-> ->]]; [|done].
          apply Hguard; [|done]. intros y Hy. apply elem_of_difference in Hy as [Hy _].
          destruct (decide (y = b)) as [->|Hyb].
          + apply elem_of_union; right. by apply elem_of_singleton.
          + apply elem_of_union; left. apply elem_of_difference.
            split; [done|]. by intros ->%elem_of_singleton. }
      destruct (Had _ (padmin_link _ _ ltac:(exists C, F, f, d1, x, f0; split_and!; done)) Hd' L)
        as (N & W2 & HN & Hfr & _ & HΦ).
      exists N, W2. split_and!; [done|done|].
      refine (imp4 _ _ _ _ _ _ (HΦ _ _ b eq_refl) (λ HP', _) _ _ _ _); [|done|set_solver| |done].
      2: { intros Hb. apply HbC. set_solver. }
      destruct (decide (b = d1)) as [->|Hbd].
      - assert (c = d1 ∧ d = d1) as [-> ->].
        { assert (d ∈ ({[d1; d1]} : gset chan)) as Hd1.
          { rewrite Hcd. apply elem_of_union; right. by apply elem_of_singleton. }
          apply elem_of_union in Hc' as [?%elem_of_singleton|?%elem_of_singleton];
          apply elem_of_union in Hd1 as [?%elem_of_singleton|?%elem_of_singleton]; done. }
        rewrite echsubst_refl. by rewrite echsubst_collapse in HP'.
      - rewrite echsubst_chain in HP' by done.
        destruct (Hcases Hbd) as [[-> ->]|[-> ->]]; [|done].
        apply (LPrel_swap_restricted b d1) in HP'; [|by apply HbC|].
        2: { intros Hin. apply (elem_of_disjoint _ _) in Hd. apply (Hd d1); [set_solver|done]. }
        unfold pswap in HP'. simpl in HP'.
        assert (gswap b d1 (C ∖ {[d1]}) = C ∖ {[b]}) as Hg.
        { apply set_eq. intros y. rewrite elem_of_gswap'. unfold cswap.
          repeat case_decide; subst; set_solver. }
        rewrite Hg, msswap_echsubst_flip in HP'. done. }
    assert (x ∉ ({[c0; d0]} : gset chan)) as Hx'.
    { intros Hin. apply elem_of_union in Hin as [?%elem_of_singleton|?%elem_of_singleton];
        apply Hx; auto. }
    rewrite gsub_id in Hcd by done. rewrite <-Hcd in Hf0.
    assert (d ≠ x) as Hdx.
    { intros ->. apply Hx'. rewrite <-Hcd. apply elem_of_union; right.
      by apply elem_of_singleton. }
    destruct (Had _ (padmin_link _ _ ltac:(exists C, F, f, c, d, f0; split_and!; done)) Hd L)
      as (N & W2 & HN & Hfr & _ & HΦ).
    exists N, W2. split_and!; [done|done|].
    assert (x ∉ C ∖ {[c]}) as HxC'.
    { intros Hin. apply elem_of_difference in Hin as [? _]. done. }
    destruct (decide (b = c)) as [->|Hbc].
    { refine (imp4 _ _ _ _ _ _ (HΦ _ _ d eq_refl) (λ HP', _) _ _ _ _); [|done|done| |done].
      2: { intros Hdin HdΣ. apply (elem_of_disjoint _ _) in Hd. by apply (Hd d). }
      by rewrite echsubst_retarget. }
    refine (imp4 _ _ _ _ _ _ (HΦ _ _ b eq_refl) (λ HP', _) _ _ _ _); [|done|done| |done].
    2: { intros Hb. apply HbC. by apply elem_of_difference in Hb as [? _]. }
    by rewrite echsubst_comm in HP'.
  - (* Q-Comm *)
    intros q Hst Hd L.
    apply pcomm_inv in Hst as
      [ (F' & c & v' & e' & e'' & g' & g'' & HeqE & Hts & Htr & ->)
      | [ (F' & c & e' & e'' & g' & g'' & HeqE & Hts & Htr & HcC & ->)
      | (F' & c & i & e' & e'' & g' & g'' & HeqE & Hts & Htr & ->) ]].
    + (* internal message *)
      apply echsubst_decomp in HeqE as (F1 & g & -> & HeqE1 & ->).
      symmetry in HeqE1. apply echsubst_decomp in HeqE1 as (F2 & h & -> & -> & ->).
      apply tstep_chsubst_det_inv in Hts as (α & h0 & Hh0 & Hα & ->); [|done].
      destruct α as [|[c0 w0|c0 w0|c0|cd0|c0 i0|c0 i0]| |]; simpl in Hα; try discriminate.
      injection Hα as Hc0 Hw0. subst v'.
      apply tstep_chsubst_recv_inv_subst in Htr as (c1 & g0 & Hc1 & Hg0 & ->).
      assert (c0 ≠ x) as Hc0x.
      { intros ->. apply (Hoff (F2 ⊎ {[+ g +]}) h (SSend x w0) h0); [multiset_solver|done| |];
          simpl; set_solver. }
      assert (c1 ≠ x) as Hc1x.
      { intros ->. apply (Hoff (F2 ⊎ {[+ h +]}) g (SRecv x w0) g0); [multiset_solver|done| |];
          simpl; set_solver. }
      rewrite csub_ne in Hc0, Hc1 by done. subst c0 c1.
      destruct (Hc _ (PCMsg C F2 c w0 h h0 g g0 Hh0 Hg0) Hd L)
        as (N & W2 & HN & Hfr & HP').
      exists N, W2. split_and!; [done|done|].
      apply (IH2 _ _ _ _ b) in HP'; [|done..]. by rewrite echsubst_disj_union2 in HP'.
    + (* internal close *)
      apply echsubst_decomp in HeqE as (F1 & g & -> & HeqE1 & ->).
      symmetry in HeqE1. apply echsubst_decomp in HeqE1 as (F2 & h & -> & -> & ->).
      apply tstep_chsubst_det_inv in Hts as (α & h0 & Hh0 & Hα & ->); [|done].
      destruct α as [|[c0 w0|c0 w0|c0|cd0|c0 i0|c0 i0]| |]; simpl in Hα; try discriminate.
      injection Hα as Hc0.
      apply tstep_chsubst_det_inv in Htr as (α & g0 & Hg0 & Hα2 & ->); [|done].
      destruct α as [|[c1 w1|c1 w1|c1|cd1|c1 i1|c1 i1]| |]; simpl in Hα2; try discriminate.
      injection Hα2 as Hc1.
      assert (c0 ≠ x) as Hc0x.
      { intros ->. apply (Hoff (F2 ⊎ {[+ g +]}) h (SClos x) h0); [multiset_solver|done| |];
          simpl; set_solver. }
      assert (c1 ≠ x) as Hc1x.
      { intros ->. apply (Hoff (F2 ⊎ {[+ h +]}) g (SClos x) g0); [multiset_solver|done| |];
          simpl; set_solver. }
      rewrite csub_ne in Hc0, Hc1 by done. subst c0 c1.
      destruct (Hc _ (PCClose C F2 c h h0 g g0 Hh0 Hg0 HcC) Hd L)
        as (N & W2 & HN & Hfr & HP').
      exists N, W2. split_and!; [done|done|].
      apply (IH2 _ _ _ _ b) in HP'; [|set_solver|set_solver| |done].
      2: { intros Hb. apply HbC. set_solver. }
      by rewrite echsubst_disj_union2 in HP'.
    + (* internal choice *)
      apply echsubst_decomp in HeqE as (F1 & g & -> & HeqE1 & ->).
      symmetry in HeqE1. apply echsubst_decomp in HeqE1 as (F2 & h & -> & -> & ->).
      apply tstep_chsubst_det_inv in Hts as (α & h0 & Hh0 & Hα & ->); [|done].
      destruct α as [|[c0 w0|c0 w0|c0|cd0|c0 i0|c0 i0]| |]; simpl in Hα; try discriminate.
      injection Hα as Hc0 Hi0. subst i0.
      apply tstep_chsubst_det_inv in Htr as (α & g0 & Hg0 & Hα2 & ->); [|done].
      destruct α as [|[c1 w1|c1 w1|c1|cd1|c1 i1|c1 i1]| |]; simpl in Hα2; try discriminate.
      injection Hα2 as Hc1 Hi1. subst i1.
      assert (c0 ≠ x) as Hc0x.
      { intros ->. apply (Hoff (F2 ⊎ {[+ g +]}) h (SSel x i) h0); [multiset_solver|done| |];
          simpl; set_solver. }
      assert (c1 ≠ x) as Hc1x.
      { intros ->. apply (Hoff (F2 ⊎ {[+ h +]}) g (SBra x i) g0); [multiset_solver|done| |];
          simpl; set_solver. }
      rewrite csub_ne in Hc0, Hc1 by done. subst c0 c1.
      destruct (Hc _ (PCChoice C F2 c i h h0 g g0 Hh0 Hg0) Hd L)
        as (N & W2 & HN & Hfr & HP').
      exists N, W2. split_and!; [done|done|].
      apply (IH2 _ _ _ _ b) in HP'; [|done..]. by rewrite echsubst_disj_union2 in HP'.
  - (* Q-Link: an external link, at the index *)
    intros cd q Hst.
    apply proc_step_sess_inv in Hst as (F' & e1 & e1' & HE & Hts & Hd & ->).
    apply echsubst_decomp in HE as (F & e & -> & -> & ->).
    apply tstep_chsubst_det_inv in Hts as (α & f & Hf & Hα & ->); [|done].
    destruct α as [|[c0 w0|c0 w0|c0|cd0|c0 i0|c0 i0]| |]; simpl in Hα; try discriminate.
    injection Hα as Hcd.
    assert (x ∉ cd0) as Hx.
    { apply (Hpre F e (SLink cd0) f eq_refl Hf). simpl. by rewrite <-Hcd. }
    rewrite gsub_id in Hcd by done. subst cd.
    destruct (Hl _ _ (PStepSession C F e (SLink cd0) f Hf Hd))
      as (c1 & d1 & Σ1 & sc & sd & kc & kd & -> & Hne & HΣ & Hc1 & Hd1 & Hdu & Hal & _ & HΦ).
    exists c1, d1, Σ1, sc, sd, kc, kd. split_and!; try done.
    refine (imp4 _ _ _ _ _ _ (HΦ eq_refl _ _ b eq_refl) (λ HP', _) _ _ _ _).
    { by rewrite echsubst_disj_union1 in HP'. }
    { rewrite HΣ in HxΣ. rewrite !dom_insert_L in HxΣ. sset. }
    { sset. }
    { intros Hb. rewrite HΣ in HbC. rewrite !dom_insert_L in HbC.
      pose proof (HbC ltac:(sset)). sset. }
    { done. }
  - (* external steps *)
  intros σ' q Hst.
  apply proc_step_sess_inv in Hst as (F' & e1 & e1' & HE & Hts & Hd & ->).
    apply echsubst_decomp in HE as (F & e & -> & -> & ->).
    destruct σ' as [c w'|c w'|c|cd|c i|c i]; simpl.
    * (* receive: the value may mention x; freshen through z *)
      destruct (exist_fresh (fchans w' ∪ fchans e ∪ echans F ∪ C ∪ dom Σ ∪ {[x; b]}))
        as [z Hz].
      destruct (tstep_chsubst_recv_inv_swap x b z e c w' e1')
        as (c0 & f & Hc0 & Hf & ->); [done|sset|sset|sset|done|sset|].
      assert (c0 ≠ x) as Hc0x.
      { intros ->. apply (Hoff F e (SRecv x (eswap x z w')) f); [done|done| |];
          simpl; sset. }
      rewrite csub_ne in Hc0 by done. subst c0.
      destruct (Hσ _ _ (PStepSession C F e (SRecv c (eswap x z w')) f Hf Hd))
        as (Σ1 & m & U & s & k & Hhd & Hc1 & H).
      exists Σ1, m, U, s, k. split_and!; [done|done|].
      intros W' j Θ2' HW' Hj Hfr Hok HVw.
      assert (x ∉ dom (<[c := (s, pt_shift 1 k)]> Σ1)) as HxΣr.
      { apply senv_hd_dom in Hhd. rewrite dom_insert_L. sset. }
      assert (z ∉ dom (<[c := (s, pt_shift 1 k)]> Σ1)) as HzΣr.
      { apply senv_hd_dom in Hhd. rewrite dom_insert_L. sset. }
      assert (z ∉ dom Θ2') as HzΘ by (rewrite <-(LVrel_fchans _ _ _ _ _ HVw); sset).
      set (Σr := <[c := (s, pt_shift 1 k)]> Σ1) in *.
      set (Θ2 := tenvswap x z Θ2').
      assert (dom Θ2 ## C) as Hfr2.
      { unfold Θ2. rewrite dom_tenvswap. apply elem_of_disjoint. intros y Hy HyC.
        apply elem_of_gswap' in Hy. unfold cswap in Hy.
        repeat case_decide; subst; [sset|sset|].
        by apply (elem_of_disjoint _ _) in Hfr; apply (Hfr y). }
      assert (recv_ok W' Σr Θ2) as Hok2.
      { apply (recv_ok_swap x z) in Hok. rewrite senvswap_fix in Hok by done. done. }
      assert (LVrel j W' Θ2 (payload_at m U k) (eswap x z w')) as HVw2 by (by apply LVrel_swap).
      pose proof (H W' j Θ2 HW' Hj Hfr2 Hok2 HVw2) as HP1.
      cbn [sentc fst snd] in HP1. rewrite ?difference_empty_L in HP1.
      assert (x ∉ dom Θ2) as HxΘ2.
      { unfold Θ2. rewrite dom_tenvswap, elem_of_gswap', cswap_l. done. }
      apply (IHn j ltac:(simpl in Hj; lia) _ _ _ _ _ x b) in HP1.
      2: { unfold recv_env. rewrite dom_union_L, !dom_difference_L. intros Hx.
           apply elem_of_union in Hx as [Hx|Hx]; apply elem_of_difference in Hx as [Hx _];
             [done|]. revert Hx. apply not_elem_of_dom. unfold tenv_ones.
           rewrite lookup_omap. by apply not_elem_of_dom in HxΘ2 as ->. }
      2: { intros Hx. apply elem_of_union in Hx as [Hx|Hx]; [done|].
           unfold recv_back in Hx. sset. }
      2: { intros Hb. apply elem_of_union in Hb as [Hb|Hb].
           - unfold recv_env. rewrite dom_union_L, !dom_difference_L. intros Hb'.
             apply elem_of_union in Hb' as [Hb'|Hb']; apply elem_of_difference in Hb' as [Hb' _].
             + apply (HbC Hb). apply senv_hd_dom in Hhd. unfold Σr in Hb'.
               rewrite dom_insert_L in Hb'. apply elem_of_union in Hb' as [Hb'|Hb'];
                 sset.
             + apply (elem_of_disjoint _ _) in Hfr2. apply (Hfr2 b); [|done].
               revert Hb'. unfold tenv_ones. rewrite !elem_of_dom, lookup_omap.
               intros [o Ho]. destruct (Θ2 !! b) eqn:E; [by eexists|done].
           - by apply (recv_back_not_env W' _ _ _ Hok2). }
      2: done.
      apply (LPrel_swap x z) in HP1. unfold pswap in HP1. simpl in HP1. unfold Θ2 in HP1.
      rewrite <-recv_env_swap, senvswap_fix, tenvswap_involutive in HP1 by done.
      rewrite gswap_union, <-recv_back_swap, senvswap_fix, tenvswap_involutive in HP1
        by done.
      rewrite gswap_fresh in HP1 by sset.
      rewrite echsubst_disj_union1, msswap_disj_union, msswap_singleton in HP1.
      rewrite (msswap_fresh x z (echsubst x b F)) in HP1;
        [|apply echans_echsubst_notin; congruence|].
      2: { pose proof (echans_echsubst_sub x b F) as Hsub. sset. }
      cbn [sentc fst snd]. rewrite ?difference_empty_L. exact HP1.
    * (* send: the value carries no x *)
      apply tstep_chsubst_det_inv in Hts as (α & f & Hf & Hα & ->); [|done].
      destruct α as [|[c0 w0|c0 w0|c0|cd0|c0 i0|c0 i0]| |]; simpl in Hα; try discriminate.
      injection Hα as Hc0 Hw0. subst w'.
      assert (c0 ≠ x) as Hc0x.
      { intros ->. apply (Hoff F e (SSend x w0) f); [done|done| |]; simpl; sset. }
      rewrite csub_ne in Hc0 by done. subst c0.
      destruct (Hσ _ _ (PStepSession C F e (SSend c w0) f Hf Hd))
        as (Σ0 & Σv & m & U & s & k & Σe & Θe & Hhd & Hd0v & Hc0' & Hcv & Hdom & Hsplit &
            HdΣ & HVw & HP').
      assert (x ∉ fchans w0) as Hxw.
      { rewrite (LVrel_fchans _ _ _ _ _ HVw), dom_union_L.
        unfold tenv_of. rewrite dom_fmap_L. apply senv_hd_dom in Hhd.
        rewrite dom_union_L in Hhd. sset. }
      rewrite (chsubst_id x b w0) by done.
      exists Σ0, Σv, m, U, s, k, Σe, Θe. split_and!; try done.
      refine (imp4 _ _ _ _ _ _ (λ a1 a2 a3 a4, IH1 _ _ _ _ b a1 a2 a3 a4 HP') (λ HP', _) _ _ _ _).
      { by rewrite echsubst_disj_union1 in HP'. }
      { rewrite dom_insert_L, dom_union_L. apply senv_hd_dom in Hhd.
        rewrite dom_union_L in Hhd. destruct Hsplit as [Hsub _].
        intros Hx. apply elem_of_union in Hx as [Hx|Hx]; [sset|].
        apply elem_of_union in Hx as [Hx|Hx]; [sset|].
        apply Hsub in Hx. rewrite Hdom in Hx. sset. }
      { sset. }
      { intros Hb. rewrite dom_insert_L, dom_union_L. destruct Hsplit as [Hsub _].
        apply elem_of_difference in Hb as [HbC' Hbs]. simpl in Hbs.
        apply senv_hd_dom in Hhd. rewrite dom_union_L in Hhd.
        pose proof (HbC HbC') as HbΣ.
        intros Hb'. apply elem_of_union in Hb' as [Hb'|Hb']; [sset|].
        apply elem_of_union in Hb' as [Hb'|Hb']; [sset|].
        apply Hsub in Hb'. rewrite Hdom in Hb'. sset. }
      { done. }
    * (* close *)
      apply tstep_chsubst_det_inv in Hts as (α & f & Hf & Hα & ->); [|done].
      destruct α as [|[c0 w0|c0 w0|c0|cd0|c0 i0|c0 i0]| |]; simpl in Hα; try discriminate.
      injection Hα as Hc0.
      assert (c0 ≠ x) as Hc0x.
      { intros ->. apply (Hoff F e (SClos x) f); [done|done| |]; simpl; sset. }
      rewrite csub_ne in Hc0 by done. subst c0.
      destruct (Hσ _ _ (PStepSession C F e (SClos c) f Hf Hd))
        as (Σ1 & k & Hhd & Hc1 & HP').
      exists Σ1, k. split_and!; [done|done|].
      refine (imp4 _ _ _ _ _ _ (λ a1 a2 a3 a4, IH1 _ _ _ _ b a1 a2 a3 a4 HP') (λ HP', _) _ _ _ _).
      { by rewrite echsubst_disj_union1 in HP'. }
      { apply senv_hd_dom in Hhd. sset. }
      { sset. }
      { intros Hb. apply senv_hd_dom in Hhd. pose proof (HbC ltac:(sset)). sset. }
      { done. }
    * (* link: Q-Link above *)
      done.
    * (* select *)
      apply tstep_chsubst_det_inv in Hts as (α & f & Hf & Hα & ->); [|done].
      destruct α as [|[c0 w0|c0 w0|c0|cd0|c0 i0|c0 i0]| |]; simpl in Hα; try discriminate.
      injection Hα as Hc0 Hi0. subst i0.
      assert (c0 ≠ x) as Hc0x.
      { intros ->. apply (Hoff F e (SSel x i) f); [done|done| |]; simpl; sset. }
      rewrite csub_ne in Hc0 by done. subst c0.
      destruct (Hσ _ _ (PStepSession C F e (SSel c i) f Hf Hd))
        as (Σ1 & s1 & s2 & k & Hhd & Hc1 & HP').
      exists Σ1, s1, s2, k. split_and!; [done|done|].
      refine (imp4 _ _ _ _ _ _ (λ a1 a2 a3 a4, IH1 _ _ _ _ b a1 a2 a3 a4 HP') (λ HP', _) _ _ _ _).
      { by rewrite echsubst_disj_union1 in HP'. }
      { apply senv_hd_dom in Hhd. rewrite dom_insert_L. sset. }
      { sset. }
      { intros Hb. apply senv_hd_dom in Hhd. rewrite dom_insert_L.
        pose proof (HbC ltac:(sset)). sset. }
      { done. }
    * (* branch *)
      apply tstep_chsubst_det_inv in Hts as (α & f & Hf & Hα & ->); [|done].
      destruct α as [|[c0 w0|c0 w0|c0|cd0|c0 i0|c0 i0]| |]; simpl in Hα; try discriminate.
      injection Hα as Hc0 Hi0. subst i0.
      assert (c0 ≠ x) as Hc0x.
      { intros ->. apply (Hoff F e (SBra x i) f); [done|done| |]; simpl; sset. }
      rewrite csub_ne in Hc0 by done. subst c0.
      destruct (Hσ _ _ (PStepSession C F e (SBra c i) f Hf Hd))
        as (Σ1 & s1 & s2 & k & Hhd & Hc1 & HP').
      exists Σ1, s1, s2, k. split_and!; [done|done|].
      apply (IH1 _ _ _ _ b) in HP'.
      { by rewrite echsubst_disj_union1 in HP'. }
      { apply senv_hd_dom in Hhd. rewrite dom_insert_L. sset. }
      { sset. }
      { intros Hb. apply senv_hd_dom in Hhd. rewrite dom_insert_L.
        pose proof (HbC ltac:(sset)). sset. }
      { done. }
Qed.
