(** * Downward closure and monotonicity of R^κ (stage S3)

    For every cost table κ:

    - members of V are values ([Vrel_val]), and values in V are in E
      under any future ([Vrel_Erel]);
    - V, E and P are monotone in the world ([Vrel_mono], [Erel_mono],
      [Prel_mono]), E and P by the Kripke quantifier of every unfolding;
    - V, E and P are downward closed in the step index ([Vrel_down],
      [Erel_down], [Prel_down]), and E is antitone in the future
      ([Erel_future]). *)

From GV Require Export relation.Relation.

(** Induction on the size of a type. *)
Lemma tsize_ind (P : ty → Prop) :
  (∀ T, (∀ T', tsize T' < tsize T → P T') → P T) → ∀ T, P T.
Proof.
  intros Hind T. remember (tsize T) as k eqn:Hk. revert T Hk.
  induction k as [k IH] using lt_wf_ind. intros T ->. apply Hind.
  intros T' HT'. by apply (IH (tsize T')).
Qed.

Section closure.
  Context (κ : ctable).

  (** ** Values *)

  Lemma Vrel_val n W Θ T v : Vrel κ n W Θ T v → is_val v.
  Proof.
    revert W Θ v. induction T as [T IH] using tsize_ind. intros W Θ v.
    destruct T as [|ub lb c t h T1 a1 U a2|T1 a1 U a2|T1 a1 U a2|m kk C ub c t U a|s x|lb m C T1 a].
    - by intros [_ ->]%Vrel_unit_iff.
    - by intros (e & -> & _)%Vrel_lolli_iff.
    - intros (v1 & v2 & Θ1 & Θ2 & -> & _ & _ & H1 & H2)%Vrel_prod_iff. simpl.
      apply andb_True. split; [eapply (IH T1)|eapply (IH U)]; eauto; simpl; lia.
    - intros [(v' & -> & H)|(v' & -> & H)]%Vrel_sum_iff; simpl;
        [eapply (IH T1)|eapply (IH U)]; eauto; simpl; lia.
    - by intros (_ & e & -> & _)%Vrel_box_iff.
    - by intros (o & s' & -> & _)%Vrel_sess_iff.
    - intros (_ & xs & _ & _ & H)%Vrel_ex_iff. eapply (IH (ty_inst xs T1)); [|exact H].
      unfold ty_inst. rewrite tsize_pinst. simpl. lia.
  Qed.

  (** ** Monotone in the world *)

  Lemma Vrel_mono n W W' Θ T v : W ⊑ W' → Vrel κ n W Θ T v → Vrel κ n W' Θ T v.
  Proof.
    intros HW. revert W W' HW Θ v. induction T as [T IH] using tsize_ind. intros W W' HW Θ v.
    destruct T as [|ub lb c t h T1 a1 U a2|T1 a1 U a2|T1 a1 U a2|m kk C ub c t U a|s x|lb m C T1 a].
    - by rewrite !Vrel_unit_iff.
    - rewrite !Vrel_lolli_iff. intros (e & -> & Hfe & Hlb & H). exists e.
      split_and!; [done|done|by eapply lb_le_mono|]. intros W'' j Θ' w F HW'' Hj Hd Hub Hw.
      apply H; [by eapply wext_trans|done..].
    - rewrite !Vrel_prod_iff. intros (v1 & v2 & Θ1 & Θ2 & -> & Hd & -> & H1 & H2).
      exists v1, v2, Θ1, Θ2. split_and!; [done|done|done| |];
        [eapply (IH T1)|eapply (IH U)]; eauto; simpl; lia.
    - rewrite !Vrel_sum_iff. intros [(v' & -> & H)|(v' & -> & H)]; [left|right]; exists v';
        (split; [done|]); [eapply (IH T1)|eapply (IH U)]; eauto; simpl; lia.
    - rewrite !Vrel_box_iff. intros (-> & e & -> & Hfe & H). split; [done|]. exists e. split; [done|].
      split; [done|]. intros W'' xs ss HW'' Hxs Hss Hsc HC. apply H; [by eapply wext_trans|done..].
    - by rewrite !Vrel_sess_iff.
    - rewrite !Vrel_ex_iff. intros (Hlb & xs & Hxs & HC & H). split; [by eapply lbx_le_mono|].
      exists xs. split_and!; [done|by eapply wholds_mono|]. eapply (IH (ty_inst xs T1)); [|done|done].
      unfold ty_inst. rewrite tsize_pinst. simpl. lia.
  Qed.

  Lemma Vrel_Erel n W Θ T F v : Vrel κ n W Θ T v → Erel κ n W Θ T F v.
  Proof.
    intros HV. pose proof (Vrel_val _ _ _ _ _ HV) as Hv.
    destruct n as [|n]; [apply Erel_0|]. apply Erel_S_iff. intros W1 HW1.
    split_and!.
    - intros _. by eapply Vrel_mono.
    - intros Hirr. exfalso. by apply Hirr, val_irred.
    - split_and!; intros; exfalso; eauto using val_no_tstep.
  Qed.

  Lemma Erel_mono n W W' Θ T F e : W ⊑ W' → Erel κ n W Θ T F e → Erel κ n W' Θ T F e.
  Proof.
    intros HW. destruct n as [|n]; [intros; apply Erel_0|]. rewrite !Erel_S_iff.
    intros H W1 HW1. apply H. by eapply wext_trans.
  Qed.

  Lemma Prel_mono n W W' Σ T p : W ⊑ W' → Prel κ n W Σ T p → Prel κ n W' Σ T p.
  Proof.
    intros HW. destruct n as [|n]; [intros; apply Prel_0|]. rewrite !Prel_S_iff.
    intros H W1 HW1. apply H. by eapply wext_trans.
  Qed.

  (** ** Downward closed in the step index *)

  Lemma Vrel_down n m W Θ T v : m ≤ n → Vrel κ n W Θ T v → Vrel κ m W Θ T v.
  Proof.
    intros Hmn. revert W Θ v. induction T as [T IH] using tsize_ind. intros W Θ v.
    destruct T as [|ub lb c t h T1 a1 U a2|T1 a1 U a2|T1 a1 U a2|m' kk C ub c t U a|s x|lb m' C T1 a].
    - by rewrite !Vrel_unit_iff.
    - rewrite !Vrel_lolli_iff. intros (e & -> & Hfe & Hlb & H). exists e.
      split_and!; [done|done|done|]. intros W' j Θ' w F HW Hj Hd Hub Hw. apply H; [done|lia|done..].
    - rewrite !Vrel_prod_iff. intros (v1 & v2 & Θ1 & Θ2 & -> & Hd & -> & H1 & H2).
      exists v1, v2, Θ1, Θ2. split_and!; [done|done|done| |];
        [eapply (IH T1)|eapply (IH U)]; eauto; simpl; lia.
    - rewrite !Vrel_sum_iff. intros [(v' & -> & H)|(v' & -> & H)]; [left|right]; exists v';
        (split; [done|]); [eapply (IH T1)|eapply (IH U)]; eauto; simpl; lia.
    - rewrite !Vrel_box_iff. intros (-> & e & -> & Hfe & H). split; [done|]. exists e. split; [done|].
      split; [done|]. intros W' xs ss HW Hxs Hss Hsc HC. eapply IH; [|by apply H].
      rewrite tsize_tthunk. unfold ty_inst. rewrite tsize_sinst, tsize_pinst. simpl. lia.
    - by rewrite !Vrel_sess_iff.
    - rewrite !Vrel_ex_iff. intros (Hlb & xs & Hxs & HC & H). split; [done|].
      exists xs. split_and!; [done|done|]. eapply (IH (ty_inst xs T1)); [|done].
      unfold ty_inst. rewrite tsize_pinst. simpl. lia.
  Qed.

  Lemma at_cost_V_down n m c W Θ T v :
    m ≤ n → at_cost_V n c (Vrel κ) (Vrel κ n) W Θ T v → at_cost_V m c (Vrel κ) (Vrel κ m) W Θ T v.
  Proof.
    intros Hmn [H1 H2]. split; intros Hc; eapply Vrel_down; [|by apply H1| |by apply H2]; lia.
  Qed.

  (** E at level n and future F is E at every level m ≤ n and every
      future F' ⊆ F. *)
  Lemma Erel_weaken m : ∀ n W Θ T F F' e,
    m ≤ n → F' ⊆ F → Erel κ n W Θ T F e → Erel κ m W Θ T F' e.
  Proof.
    induction m as [m IHm] using lt_wf_ind. intros n W Θ T F F' e Hmn HF HE.
    destruct m as [|m]; [apply Erel_0|]. destruct n as [|n]; [lia|].
    revert W Θ T F e HE F' HF.
    refine (Erel_S_ind κ n (λ W Θ T F e, ∀ F', F' ⊆ F → Erel κ (S m) W Θ T F' e) _).
    intros W Θ T F e H F' HF. apply Erel_S_iff. intros W1 HW1.
    destruct (H W1 HW1) as (Hs & Hr & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
    (* the continuation after a step of cost c *)
    assert (∀ c W Θ T0 F0 F0' e', F0' ⊆ F0 →
      at_cost_E (S n) c (Erel κ) (λ W Θ T F e, Erel κ (S n) W Θ T F e ∧
                                     ∀ F', F' ⊆ F → Erel κ (S m) W Θ T F' e) W Θ T0 F0 e' →
      at_cost_E (S m) c (Erel κ) (Erel κ (S m)) W Θ T0 F0' e') as Hac.
    { intros c W0 Θ0 T0 F0 F0' e' HF0 [A1 A2]. split.
      - intros Hc. by apply A1.
      - intros Hc. apply (IHm (S m - c) ltac:(lia) (S n - c) W0 Θ0 T0 F0 F0' e'); [lia|done|by apply A2]. }
    split; [|split; [|unfold Esteps; split_and!]].
    - intros Hirr. eapply Vrel_down; [|by apply Hs]. lia.
    - intros Hirr. eapply ready_t_future; [done|by apply Hr].
    - intros e' Hst. eapply Hac; [done|by apply H1].
    - intros ℓ c e' Hst Hc g Hg. destruct (H2 ℓ c e' Hst Hc g Hg) as [S HS].
      exists S. eapply Hac; [done|exact HS].
    - intros κf o c e' Hst Hc. destruct (H3 κf o c e' Hst Hc) as (S0 & x & Ho & S & HS).
      exists S0, x. split; [done|]. exists S. eapply Hac; [done|exact HS].
    - intros M v e' Hst. destruct (H4 M v e' Hst) as (ΘM & Θr & A1 & A2 & A3 & A4 & A5).
      exists ΘM, Θr. split_and!; [done|done|done| |eapply Hac; [done|exact A5]].
      destruct A4 as (eb & -> & Hfe & A4). exists eb. split_and!; [done|done|].
      intros W' j Θ' w HW Hj Hd. destruct (A4 W' j Θ' w HW ltac:(lia) Hd) as [B1 B2].
      split; [intros Hjm; apply B1; lia|].
      intros -> [-> ->]. destruct (decide (m = n)) as [->|Hne].
      + by apply B2.
      + apply B1; [lia|]. by apply Vrel_unit_iff.
    - intros o M w e' Hst.
      destruct (H5 o M w e' Hst) as (S0 & x & m' & U & b & S & ΘM & Θr & A1 & A2 & A3 & A4 & A5 & A6 & A7).
      exists S0, x, m', U, b, S, ΘM, Θr. split_and!; [done..| |eapply Hac; [done|exact A7]].
      eapply at_cost_V_down; [|exact A6]. lia.
    - intros o w e' Hst. destruct (H6 o w e' Hst) as (S0 & x & m' & U & b & S & A1 & A2 & A3).
      exists S0, x, m', U, b, S. split_and!; [done|done|].
      intros j Θin Hj Hd Hw. pose proof (c_take_pos κ).
      apply (IHm j ltac:(lia) j W1 _ T F F'); [lia|done|]. apply A3; [lia|done|done].
    - intros o e' Hst. destruct (H7 o e' Hst) as (S0 & x & A1 & A2 & A3).
      exists S0, x. split_and!; [done|done|eapply Hac; [done|exact A3]].
    - intros o i e' Hst. destruct (H8 o i e' Hst) as (S0 & x & S1 & S2 & A1 & A2 & A3).
      exists S0, x, S1, S2. split_and!; [done|done|eapply Hac; [done|exact A3]].
    - intros o i e' Hst. destruct (H9 o i e' Hst) as (S0 & x & S1 & S2 & A1 & A2 & A3).
      exists S0, x, S1, S2. split_and!; [done|done|eapply Hac; [done|exact A3]].
    - intros os e' Hst. destruct (H10 os e' Hst) as (o1 & o2 & S1 & S2 & x & A1 & A2 & A3 & A4 & A5 & A6).
      exists o1, o2, S1, S2, x. split_and!; [done..|eapply Hac; [done|exact A6]].
  Qed.

  Lemma Erel_down n m W Θ T F e : m ≤ n → Erel κ n W Θ T F e → Erel κ m W Θ T F e.
  Proof. intros Hmn. by apply Erel_weaken. Qed.

  Lemma Erel_future n W Θ T F F' e : F' ⊆ F → Erel κ n W Θ T F e → Erel κ n W Θ T F' e.
  Proof. intros HF. by apply Erel_weaken. Qed.

  Lemma Prel_down m : ∀ n W Σ T p, m ≤ n → Prel κ n W Σ T p → Prel κ m W Σ T p.
  Proof.
    induction m as [m IHm] using lt_wf_ind. intros n W Σ T p Hmn HP.
    destruct m as [|m]; [apply Prel_0|]. destruct n as [|n]; [lia|].
    revert W Σ T p HP.
    refine (Prel_S_ind κ n (λ W Σ T p, Prel κ (S m) W Σ T p) _).
    intros W Σ T p H. apply Prel_S_iff. intros W1 HW1 HS1 h D Hh.
    destruct (H W1 HW1 HS1 h D Hh) as (Hs & Hr & H1 & H2 & H3 & H4 & H5 & H6 & H7).
    assert (∀ c W Σ T0 p', at_cost_P (S n) c (Prel κ)
        (λ W Σ T p, Prel κ (S n) W Σ T p ∧ Prel κ (S m) W Σ T p) W Σ T0 p' →
      at_cost_P (S m) c (Prel κ) (Prel κ (S m)) W Σ T0 p') as Hac.
    { intros c W0 Σ0 T0 p' [A1 A2]. split.
      - intros Hc. by apply A1.
      - intros Hc. apply (IHm (S m - c) ltac:(lia) (S n - c)); [lia|by apply A2]. }
    split; [|split; [|unfold Psteps; split_and!]].
    - intros Hirr. destruct (Hs Hirr) as (v & E & -> & Hv & HE). exists v, E.
      split_and!; [done| |done]. eapply Vrel_down; [|exact Hv]. lia.
    - done.
    - intros q ev q' Hq Hst Hτ Hd. apply Hac. exact (H1 q ev q' Hq Hst Hτ Hd).
    - intros q i o M w q' Hq Hst.
      destruct (H2 q i o M w q' Hq Hst)
        as (S0 & x & m' & U & b & S & Σv & Σr & Θe & Σe & A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
      exists S0, x, m', U, b, S, Σv, Σr, Θe, Σe. split_and!; [done..| |by apply Hac].
      eapply at_cost_V_down; [|exact A8]. lia.
    - intros q i o w q' Hq Hst. destruct (H3 q i o w q' Hq Hst) as (S0 & x & m' & U & b & S & A1 & A2 & A3).
      exists S0, x, m', U, b, S. split_and!; [done|done|].
      intros j Θ2 Hj Hd Hok Hw. apply A3; [lia|done..].
    - intros q i o q' Hq Hst. destruct (H4 q i o q' Hq Hst) as (S0 & x & A1 & A2 & A3).
      exists S0, x. split_and!; [done|done|by apply Hac].
    - intros q i o b q' Hq Hst. destruct (H5 q i o b q' Hq Hst) as (S0 & x & S1 & S2 & A1 & A2 & A3).
      exists S0, x, S1, S2. split_and!; [done|done|by apply Hac].
    - intros q i o b q' Hq Hst. destruct (H6 q i o b q' Hq Hst) as (S0 & x & S1 & S2 & A1 & A2 & A3).
      exists S0, x, S1, S2. split_and!; [done|done|by apply Hac].
    - intros q i os q' Hq Hst.
      destruct (H7 q i os q' Hq Hst) as (o1 & o2 & S1 & S2 & x & A1 & A2 & A3 & A4 & A5 & A6).
      exists o1, o2, S1, S2, x. split_and!; [done..|by apply Hac].
  Qed.

  (** ** The step clauses, read off the label *)

  Lemma Erel_S_step n W W1 Θ T F e α e' :
    Erel κ (S n) W Θ T F e → W ⊑ W1 → tstep e α e' →
    Eobl κ (S n) (Vrel κ) (Erel κ) (Vrel κ (S n)) (Erel κ (S n)) W1 Θ T F α e'.
  Proof.
    intros HE HW Hst. apply Erel_S_iff in HE. destruct (HE W1 HW) as (_ & _ & H).
    exact (proj1 (Esteps_iff _ _ _ _ _ _ _ _ _ _ _) H α e' Hst).
  Qed.

  Lemma Prel_S_step n W W1 Σ T q ev q' :
    Prel κ (S n) W Σ T (erase q) → W ⊑ W1 → strict W1 → istep q ev q' →
    Pobl κ (S n) (Vrel κ) (Prel κ) (Vrel κ (S n)) (Prel κ (S n)) W1 Σ T (erase q) ev (erase q').
  Proof.
    intros HP HW HS Hst. destruct (Prel_S_clauses κ n _ _ _ _ HP W1 HW HS) as (_ & _ & H).
    exact (proj1 (Psteps_iff _ _ _ _ _ _ _ _ _ _) H q ev q' eq_refl Hst).
  Qed.

  (** The thunk of O-Spawn is read at the level of the parent, inside
      the fixpoint when β is free. A value at 1 ⊸^ub_lb 1 is a thunk: its
      body is read at the empty future, above every upper point, and
      the lower point is dropped. *)
  Lemma Vrel_thunk n W Θ ub lb v :
    Vrel κ n W Θ (TLolli ub lb None tinf None TUnit None TUnit None) v →
    Vthunk κ n (Vrel κ) (Erel κ) (λ _ Θ' w, Θ' = ∅ ∧ w = EUnit)
      (λ W' Θ' F e, Erel κ n W' Θ' TUnit F e) W Θ v.
  Proof.
    rewrite Vrel_lolli_iff, <-Varr_rel_iff. intros HV. apply Varr_thunk in HV. revert HV.
    apply Vthunk_mono; [intros; done|intros; done| |intros; done].
    intros _ W0 Θ0 w. by rewrite Vrel_unit_iff.
  Qed.

End closure.
