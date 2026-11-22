(** * Four programs that deadlock freedom admits and lock freedom rejects

    Each program steps forever without a deadlock while one thread waits
    forever (docs/explorer, examples rx-relink, rx-postpone, rx-delegate
    and rx-chain). The rejections go through the credit skeleton of
    static/Skeleton.v: a derivation of the lock-free judgment at a finite
    bound N erases to a skeleton derivation ([typed_skel]), which keeps
    credits, tickets and session types, and every argument below reads
    only these.

    - rx-relink ([rl_refresh_untyped], [rx_relink_rejected]). The box
      that links the end it was handed to a new channel has no type at
      any finite N. E-Link asks a + m₂ > N of the linked end at credit a
      and the partner end with tickets m₂, and E-New asks m₂ + m₂' ≤ N
      of the new channel, so a > m₂'. The recursive call passes the new
      end, of credit at most m₂', where the parameter asks the credit of
      the linked end, at least a. *)

From GV Require Export static.Skeleton examples.Tools.

Lemma skle_prod_inv A B C D : skle (TProd A B) (TProd C D) → skle A C ∧ skle B D.
Proof. by inversion 1. Qed.

(** ** rx-relink

      refresh = !(f = λ⟨w, k⟩. let ⟨c, c′⟩ = new in let ∗ = link ⟨w, c⟩ in
                               let k = send ⟨∗, k⟩ in (force f) ⟨c′, k⟩)
      sink    = !(f = λk. let ⟨u, k⟩ = recv k in let ∗ = u in (force f) k)
      main    = let ⟨w, w′⟩ = new in let ⟨k, k′⟩ = new in
                let ∗ = spawn (λ_. close w′) in
                let ∗ = spawn (λ_. (force sink) k′) in (force refresh) ⟨w, k⟩ *)

Definition rl_refresh : expr :=
  EBox (Lam (LetP (Var 0) (let_new (LetU (ELink (Pair (Var 4) (Var 1)))
    (ELet (ESend (Pair EUnit (Var 3))) (App (EForce (Var 7)) (Pair (Var 1) (Var 0)))))))).

Definition rl_sink : expr :=
  EBox (Lam (LetP (ERecv (Var 0)) (LetU (Var 1) (App (EForce (Var 3)) (Var 0))))).

Definition rl_main : expr :=
  let_new (let_new (LetU (ESpawn (Lam (EClose (Var 4))))
    (LetU (ESpawn (Lam (App (EForce rl_sink) (Var 1))))
      (App (EForce rl_refresh) (Pair (Var 4) (Var 1)))))).

Theorem rl_refresh_untyped n Δ T c : ¬ sktyped (Some n) Δ rl_refresh T c.
Proof.
  intros H. unfold rl_refresh in H.
  apply sk_box_inv in H as (k & cb & U & _ & Hb & _).
  specialize (Hb (repeat SEnd k) (repeat_length _ _) (sinsts_repeat_end _ _)).
  apply sk_abs_inv in Hb as (Δh & P & Ui & ci & a & Hah & Hb & HlU).
  apply skle_arr_l in HlU as (c1' & P' & U1' & a' & HU & _ & _ & HPP & _).
  apply sinst_inv_lolli in HU as (A0 & B0 & -> & -> & ->).
  (* λ⟨w, k⟩ *)
  apply sk_letp_inv in Hb as (Δ1 & Δ2 & Δ2' & T1 & T2 & T3 & c1 & c2 & Hs1 & Hv & Ha1 & Hb & _).
  apply sk_var_anc in Hv. climb Hv. apply anc_top in Hv.
  (* let ⟨c, c′⟩ = new *)
  unfold let_new, ELet in Hb. simpl in Hb.
  apply sk_letp_inv in Hb as (Δ3 & Δ4 & Δ4' & A1 & A2 & T4 & c3 & c4 & Hs3 & Hn & Ha3 & Hb & _).
  apply sk_pair_inv in Hn as (Δ5 & Δ6 & Δ6' & B1 & B1' & B2 & c5 & c6 & _ & Hn & _ & _ & Hag & HlA).
  apply sk_new_inv in Hn as (S1 & m1 & m2 & _ & Htk & HlB).
  apply sk_letu_inv in Hb as (Δ7 & Δ8 & Δ8' & T5 & c7 & c8 & Hs7 & _ & Ha7 & Hb & _).
  apply sk_letp_inv in Hb as (Δ9 & Δ10 & Δ10' & C1 & C2 & T6 & c9 & c10 & Hs9 & Hq & Ha9 & Hb & _).
  apply sk_var_anc in Hq. climb Hq. apply anc_top in Hq.
  (* link ⟨w, c⟩ *)
  apply sk_letu_inv in Hb as (Δ11 & Δ12 & Δ12' & T7 & c11 & c12 & Hs11 & Hl & Ha11 & Hb & _).
  apply sk_link_inv in Hl as (S & a1 & m1' & a2 & m2' & c13 & Hp & Hg1 & _).
  apply sk_pair_inv in Hp as (Δ13 & Δ14 & Δ14' & D1 & D1' & D2 & c14 & c15 & Hs13 & Hw & Ha13 & Hc & HagD & HlD).
  apply sk_var_anc in Hw. climb Hw. apply anc_top in Hw.
  apply sk_var_anc in Hc. climb Hc. apply anc_top in Hc.
  (* let k = send ⟨∗, k⟩ in (force f) ⟨c′, k⟩ *)
  apply sk_letp_inv in Hb as (Δ15 & Δ16 & Δ16' & F1 & F2 & T8 & c16 & c17 & Hs15 & _ & Ha15 & Hb & _).
  apply sk_letu_inv in Hb as (Δ17 & Δ18 & Δ18' & T9 & c18 & c19 & Hs17 & _ & Ha17 & Hb & _).
  apply sk_app_inv in Hb as (Δ19 & Δ20 & Δ20' & c0 & Targ & Ur & a1r & c20 & c21 & Hs19 & Hf & Ha19 & Hp & _ & _).
  apply sk_force_inv in Hf as (k' & cb' & U'' & ss' & c22 & _ & _ & Hfv & HlR).
  apply sk_var_anc in Hfv. climb Hfv. apply anc_top in Hfv.
  apply skle_box_l in Hfv as (cb2 & U2 & [= -> -> ->] & _ & Hbx).
  apply sk_pair_inv in Hp as (Δ21 & Δ22 & Δ22' & E1 & E1' & E2 & c23 & c24 & Hs21 & Hc' & Ha21 & _ & HagE & HlE).
  apply sk_var_anc in Hc'. climb Hc'. apply anc_top in Hc'.
  (* The new channel: c at tickets m1, c′ at credit and tickets m2. *)
  apply skle_prod_inv in HlA as [HlA _].
  pose proof (skle_trans _ _ _ (skle_trans _ _ _ (skle_trans _ _ _ HlB (tage_skle _ _ _ Hag)) HlA) Hq) as Hnew.
  apply skle_prod_inv in Hnew as [HC1 HC2].
  (* The tickets of c at the link are m1. *)
  apply skle_prod_inv in HlD as [HlD1 HlD2].
  pose proof (skle_trans _ _ _ (skle_trans _ _ _ HC1 Hc) HlD2) as Hct.
  apply skle_sess_l in Hct as (? & ? & [= _ _ ->] & _ & _).
  (* The credit a1 of w at the link is at most the credit p of the parameter. *)
  pose proof (skle_trans _ _ _ (skle_trans _ _ _ Hw (tage_skle _ _ _ HagD)) HlD1) as HT1.
  apply skle_prod_r in Hv as (P1 & P2 & -> & HP1 & _).
  apply skle_prod_r in HPP as (P1' & P2' & HP' & HP1' & _).
  pose proof (skle_trans _ _ _ (skle_trans _ _ _ HP1' HP1) HT1) as Hwp.
  apply skle_sess_r in Hwp as (sP & p & -> & _ & Hap).
  apply sinst_inv_prod in HP' as (A01 & A02 & -> & HA01 & _).
  symmetry in HA01. apply sinst_inv_sess in HA01 as (s0 & -> & _).
  (* The recursive call asks the credit p of c′, which has at most m2. *)
  apply boxeq_teq, teq_lolli_l in Hbx as (A'' & B'' & -> & HA'' & _).
  apply teq_prod_l in HA'' as (A1'' & A2'' & -> & HA1'' & _).
  apply teq_sess_l in HA1'' as (s0' & -> & _).
  simpl in HlR. apply skle_arr_l in HlR as (? & ? & ? & ? & [= _ <- _ _] & _ & _ & HTarg & _).
  apply skle_prod_r in HTarg as (Tg1 & Tg2 & -> & HTg1 & _).
  apply skle_prod_inv in HlE as [HlE _].
  pose proof (skle_trans _ _ _ (skle_trans _ _ _ (skle_trans _ _ _ (skle_trans _ _ _ HC2 Hc')
    (tage_skle _ _ _ HagE)) HlE) HTg1) as Hcp.
  apply skle_sess_l in Hcp as (? & ? & [= _ <- _] & _ & Hpm).
  (* a1 + m1 > N ≥ m1 + m2 and a1 ≤ p ≤ m2. *)
  unfold lgt, tsum_ok in *. destruct a1, p, m1, m2; simpl in *; lia.
Qed.

Theorem rx_relink_rejected n W Θ Γ Δ F T c : ¬ typed W (Some n) Θ Γ Δ F rl_main T c.
Proof.
  intros H. apply typed_skel in H. unfold rl_main, let_new, ELet in H. simpl in H.
  apply sk_letp_inv in H as (? & ? & ? & ? & ? & ? & ? & ? & _ & _ & _ & H & _).
  apply sk_letu_inv in H as (? & ? & ? & ? & ? & ? & _ & _ & _ & H & _).
  apply sk_letp_inv in H as (? & ? & ? & ? & ? & ? & ? & ? & _ & _ & _ & H & _).
  apply sk_letp_inv in H as (? & ? & ? & ? & ? & ? & ? & ? & _ & _ & _ & H & _).
  apply sk_letu_inv in H as (? & ? & ? & ? & ? & ? & _ & _ & _ & H & _).
  apply sk_letp_inv in H as (? & ? & ? & ? & ? & ? & ? & ? & _ & _ & _ & H & _).
  apply sk_letu_inv in H as (? & ? & ? & ? & ? & ? & _ & _ & _ & H & _).
  apply sk_letu_inv in H as (? & ? & ? & ? & ? & ? & _ & _ & _ & H & _).
  apply sk_app_inv in H as (? & ? & ? & ? & ? & ? & ? & ? & ? & _ & H & _).
  apply sk_force_inv in H as (? & ? & ? & ? & ? & _ & _ & H & _).
  exact (rl_refresh_untyped _ _ _ _ H).
Qed.

Corollary rx_relink_box_rejected n W Θ Γ Δ F T c : ¬ typed W (Some n) Θ Γ Δ F rl_refresh T c.
Proof. intros H. apply typed_skel in H. exact (rl_refresh_untyped _ _ _ _ H). Qed.

(** A process of the one thread main is untypable too. *)
Corollary rx_relink_proc_rejected n W T : ¬ fptyped (Some n) W ∅ (∅, {[+ rl_main +]}) T.
Proof.
  intros H. apply fptyped_one in H as (ΘB & c & _ & _ & _ & _ & _ & _ & H & _).
  exact (rx_relink_rejected _ _ _ _ _ _ _ _ H).
Qed.

(** ** rx-postpone

      chat = !(f = λa. let a = send ⟨∗, a⟩ in (force f) a)
      loop = !(f = λ⟨a, b⟩. let ⟨u, a⟩ = recv a in let ∗ = u in (force f) ⟨a, b⟩)
      main = let ⟨a, a′⟩ = new in let ⟨b, b′⟩ = new in
             let ∗ = spawn (λ_. (force chat) a′) in
             let ∗ = spawn (λ_. close b′) in (force loop) ⟨a, b⟩

    The thread of close b′ makes the session of b not idle. Each round of
    loop receives on a while it holds b, so aging asks the cost of the
    receive, at least 1, below the credit of b and lowers it by that cost.
    The recursive call passes b where the parameter asks its old credit.
    The parameter credit is finite, because main passes b from a new
    channel with finite tickets. *)

Definition pp_chat : expr :=
  EBox (Lam (ELet (ESend (Pair EUnit (Var 0))) (App (EForce (Var 2)) (Var 0)))).

Definition pp_loop : expr :=
  EBox (Lam (LetP (Var 0) (LetP (ERecv (Var 1)) (LetU (Var 1)
    (App (EForce (Var 5)) (Pair (Var 0) (Var 2))))))).

Definition pp_main : expr :=
  let_new (let_new (LetU (ESpawn (Lam (App (EForce pp_chat) (Var 4))))
    (LetU (ESpawn (Lam (EClose (Var 1))))
      (App (EForce pp_loop) (Pair (Var 4) (Var 1)))))).

Lemma skle_sess_inv s x a m s' x' a' m' :
  skle (TSess s x a m) (TSess s' x' a' m') → sequiv s s' ∧ fle a' a ∧ m' = m.
Proof. inversion 1; subst. done. Qed.

Lemma teq_lolli_inv ub lb c A B a ub' lb' c' A' B' a' :
  teq (TLolli ub lb c A B a) (TLolli ub' lb' c' A' B' a') → teq A A'.
Proof. unfold teq. simpl. tauto. Qed.

Lemma teq_sess_inv s x a m s' x' a' m' :
  teq (TSess s x a m) (TSess s' x' a' m') → sequiv s s' ∧ a' = a ∧ m' = m.
Proof. unfold teq. simpl. intros (_ & -> & -> & H). done. Qed.

(** Aging an end that is not idle asks the cost below its credit. *)
Lemma tage_sess_nonidle c s x a m T' :
  tage c (TSess s x a m) T' → ¬ idle s → fle c a ∧ T' = TSess s x (fsub a c) m.
Proof. inversion 1; subst; try done. by match goal with H : tfree _ |- _ => inversion H end. Qed.

Theorem rx_postpone_skel n Δ T c : ¬ sktyped (Some n) Δ pp_main T c.
Proof.
  intros H. unfold pp_main, let_new, ELet in H. simpl in H.
  (* let ⟨a, a′⟩ = new *)
  apply sk_letp_inv in H as (? & ? & ? & ? & ? & ? & ? & ? & _ & _ & _ & H & _).
  apply sk_letu_inv in H as (? & ? & ? & ? & ? & ? & _ & _ & _ & H & _).
  apply sk_letp_inv in H as (? & ? & ? & ? & ? & ? & ? & ? & _ & _ & _ & H & _).
  (* let ⟨b, b′⟩ = new *)
  apply sk_letp_inv in H as (Δ3 & Δ4 & Δ4' & A1 & A2 & T4 & c3 & c4 & Hs3 & Hn & Ha3 & H & _).
  apply sk_pair_inv in Hn as (Δ5 & Δ6 & Δ6' & B1 & B1' & B2 & c5 & c6 & _ & Hn & _ & _ & Hag & HlA).
  apply sk_new_inv in Hn as (S1 & m1 & m2 & _ & Htk & HlB).
  apply sk_letu_inv in H as (Δ7 & Δ8 & Δ8' & T5 & c7 & c8 & Hs7 & _ & Ha7 & H & _).
  apply sk_letp_inv in H as (Δ9 & Δ10 & Δ10' & C1 & C2 & T6 & c9 & c10 & Hs9 & Hq & Ha9 & H & _).
  apply sk_var_anc in Hq. climb Hq. apply anc_top in Hq.
  apply skle_prod_inv in HlA as [HlA _].
  pose proof (skle_trans _ _ _ (skle_trans _ _ _ (skle_trans _ _ _ HlB (tage_skle _ _ _ Hag)) HlA) Hq) as Hnew.
  apply skle_prod_inv in Hnew as [HC1 HC2].
  (* the two spawns *)
  apply sk_letu_inv in H as (Δa1 & Δa2 & Δa2' & Ta & ca1 & ca2 & Hsa & _ & Haa & H & _).
  apply sk_letu_inv in H as (Δb1 & Δb2 & Δb2' & Tb & cb1 & cb2 & Hsb & Hsp & Hab & H & _).
  apply sk_spawn_inv in Hsp as (? & ? & ? & Hsp).
  apply sk_abs_inv in Hsp as (Δh0 & Tu & Uu & cu & au & Hah0 & Hsp & _).
  apply sk_close_inv in Hsp as (S0 & a0 & mS0 & c0' & HS0 & Hv0 & _).
  apply sk_var_anc in Hv0. climb Hv0. apply anc_top in Hv0.
  (* b is not idle *)
  destruct (skle_sess_inv _ _ _ _ _ _ _ _ (skle_trans _ _ _ HC2 Hv0)) as [HdS1 _].
  assert (¬ idle S1) as HS1.
  { intros HI. apply (end_not_idle S0 HS0). apply (idle_sequiv _ _ HdS1). by apply idle_dual_iff. }
  (* (force loop) ⟨a, b⟩ *)
  apply sk_app_inv in H as (Δc1 & Δc2 & Δc2' & cf & Targ & Ur & ar & cc1 & cc2 & Hsc & Hf & Hac & Hp & _ & _).
  apply sk_force_inv in Hf as (k & cb' & U' & ss & cfo & Hlen & Hss & Hbox & HlR).
  apply sk_box_inv in Hbox as (k0 & cb & U & _ & Hbody & Hbl).
  apply skle_box_l in Hbl as (cb2' & U2 & [= -> -> ->] & _ & Hbx).
  apply sk_pair_inv in Hp as (Δd1 & Δd2 & Δd2' & X1 & X1' & X2 & cd1 & cd2 & Hsd & _ & Had & Hvb & _ & HlP).
  apply sk_var_anc in Hvb. climb Hvb. apply anc_top in Hvb.
  apply skle_arr_r in HlR as (cR & R & UR & aR & HR & _ & _ & HTR & _).
  apply skle_prod_l in HlP as (Tg1 & Tg2 & -> & _ & HX2).
  apply skle_prod_l in HTR as (R1 & R2 & -> & _ & HR2).
  pose proof (skle_trans _ _ _ (skle_trans _ _ _ (skle_trans _ _ _ HC1 Hvb) HX2) HR2) as HmR.
  apply skle_sess_l in HmR as (sR & β & -> & HsR & Hβm).
  (* the body of loop at the instance ss of main *)
  specialize (Hbody ss Hlen Hss).
  pose proof (boxeq_sinst _ _ _ _ _ Hbx Hlen Hss) as Hteq. rewrite HR in Hteq.
  apply sk_abs_inv in Hbody as (Δh & P & Ui & ci & a & Hah & Hb & HlU).
  apply skle_arr_l in HlU as (c' & P' & U1' & a' & HU & _ & _ & HPP & _).
  rewrite HU in Hteq. apply teq_lolli_inv, teq_sym, teq_prod_l in Hteq as (P1' & P2' & -> & _ & HP2').
  apply teq_sess_l in HP2' as (sR' & -> & HsR').
  apply skle_prod_l in HPP as (P1 & P2 & -> & _ & HP2).
  apply skle_sess_l in HP2 as (sP & p & -> & HsP & Hpβ).
  apply sinst_inv_lolli in HU as (A0 & B0 & -> & HA0 & _).
  symmetry in HA0. apply sinst_inv_prod in HA0 as (A01 & A02 & -> & _ & HA02).
  symmetry in HA02. apply sinst_inv_sess in HA02 as (s0 & -> & _).
  (* λ⟨a, b⟩ *)
  apply sk_letp_inv in Hb as (Δ1 & Δ2 & Δ2' & T1 & T2 & T3 & c1 & c2 & Hs1 & Hv & Ha1 & Hb & _).
  apply sk_var_anc in Hv. climb Hv. apply anc_top in Hv.
  apply skle_prod_inv in Hv as [_ Hv].
  apply skle_sess_l in Hv as (sT & t & -> & HsT & Htp).
  assert (¬ idle sT) as HsTi.
  { intros HI. apply HS1. apply (idle_sequiv _ _ HsR), (idle_sequiv _ _ HsR'), (idle_sequiv _ _ HsP).
    by apply (idle_sequiv _ _ HsT). }
  (* let ⟨u, a⟩ = recv a: b is aged by the cost of the receive *)
  apply sk_letp_inv in Hb as (Δr1 & Δr2 & Δr2' & V1 & V2 & T4' & cr1 & cr2 & Hsr & Hr & Har & Hb & _).
  destruct (pass_r _ _ _ _ _ _ _ _ _ 0 (TSess sT pd t m1) Hsr Hr eq_refl Har eq_refl (λ HF : False, HF))
    as (X' & HX' & HagX).
  apply tage_sess_nonidle in HagX as [Hct ->]; [|done].
  apply sk_recv_inv in Hr as (? & ? & ? & ? & ? & ? & cr0 & _ & _ & _ & Hcr).
  (* let ∗ = u in (force f) ⟨a, b⟩ *)
  apply sk_letu_inv in Hb as (Δu1 & Δu2 & Δu2' & T5' & cu1 & cu2 & Hsu & _ & Hau & Hb & _).
  apply sk_app_inv in Hb as (Δe1 & Δe2 & Δe2' & cs & Targ2 & Ur2 & a2 & ce1 & ce2 & Hse & Hf2 & Hae & Hp2 & _ & _).
  apply sk_force_inv in Hf2 as (k2 & cb3 & U3 & ss2 & cf2 & _ & _ & Hfv & HlR2).
  apply sk_var_anc in Hfv. climb Hfv. apply anc_top in Hfv.
  apply skle_box_l in Hfv as (cb4 & U4 & [= -> -> ->] & _ & Hbx2).
  apply sk_pair_inv in Hp2 as (Δf1 & Δf2 & Δf2' & Y1 & Y1' & Y2 & cf3 & cf4 & Hsf & _ & Haf & Hvb2 & _ & HlY).
  apply sk_var_anc in Hvb2. climb_to Hvb2 Δr2'.
  destruct Hvb2 as (X0 & HX0 & HlX). rewrite HX' in HX0. injection HX0 as <-.
  apply boxeq_teq, teq_lolli_l in Hbx2 as (A'' & B'' & -> & HA'' & _).
  apply teq_prod_l in HA'' as (A1'' & A2'' & -> & _ & HA2'').
  apply teq_sess_l in HA2'' as (s0' & -> & _).
  simpl in HlR2. apply skle_arr_l in HlR2 as (? & ? & ? & ? & [= _ <- _ _] & _ & _ & HTarg & _).
  apply skle_prod_r in HTarg as (Tg1' & Tg2' & -> & _ & HTg2).
  apply skle_prod_inv in HlY as [_ HlY].
  pose proof (skle_trans _ _ _ (skle_trans _ _ _ HlX HlY) HTg2) as Hself.
  apply skle_sess_inv in Hself as (_ & Hβt & _).
  (* t ≤ p ≤ β ≤ t − c with 1 ≤ c ≤ t, and β ≤ m1 is finite *)
  clear - Htk Hβm Hpβ Htp Hct Hcr Hβt. unfold tsum_ok in Htk.
  destruct t, p, β, cr1, cr0, m1, m2; simpl in *; lia.
Qed.

Theorem rx_postpone_rejected n W Θ Γ Δ F T c : ¬ typed W (Some n) Θ Γ Δ F pp_main T c.
Proof. intros H. apply typed_skel in H. exact (rx_postpone_skel _ _ _ _ H). Qed.

Corollary rx_postpone_proc_rejected n W T : ¬ fptyped (Some n) W ∅ (∅, {[+ pp_main +]}) T.
Proof.
  intros H. apply fptyped_one in H as (ΘB & c & _ & _ & _ & _ & _ & _ & H & _).
  exact (rx_postpone_rejected _ _ _ _ _ _ _ _ H).
Qed.
