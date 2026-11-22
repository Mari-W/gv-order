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

(** ** rx-delegate

      pass = !(f = λ⟨e, x, y⟩. let x = send ⟨e, x⟩ in let ⟨e, y⟩ = recv y in
                              (force f) ⟨e, x, y⟩)
      back = !(f = λ⟨x, y⟩. let ⟨e, x⟩ = recv x in let y = send ⟨e, y⟩ in
                           (force f) ⟨x, y⟩)
      main = let ⟨e, e′⟩ = new in let ⟨x, x′⟩ = new in let ⟨y, y′⟩ = new in
             let ∗ = spawn (λ_. close e′) in
             let ∗ = spawn (λ_. (force back) ⟨x′, y′⟩) in
             (force pass) ⟨e, ⟨x, y⟩⟩

    The thread of close e′ makes the session of e not idle. E-Send ages
    the payload by 1, so pass sends e on x at a payload credit p_x below
    the credit of its parameter e, and back sends the e it received on x′
    at a payload credit p_y below p_x. The two ends of a channel have dual
    sessions with the same payloads, so pass receives e on y at credit p_y
    and passes it to the recursive call, which asks the parameter credit β:
    β ≤ p_y < p_x < β. β is finite, because main passes e from a new
    channel with finite tickets. *)

Definition dl_pass : expr :=
  EBox (Lam (LetP (Var 0) (LetP (Var 0) (ELet (ESend (Pair (Var 3) (Var 1)))
    (LetP (ERecv (Var 1)) (App (EForce (Var 8)) (Pair (Var 1) (Pair (Var 2) (Var 0))))))))).

Definition dl_back : expr :=
  EBox (Lam (LetP (Var 0) (LetP (ERecv (Var 1)) (ELet (ESend (Pair (Var 1) (Var 2)))
    (App (EForce (Var 6)) (Pair (Var 1) (Var 0))))))).

Definition dl_main : expr :=
  let_new (let_new (let_new (LetU (ESpawn (Lam (EClose (Var 7))))
    (LetU (ESpawn (Lam (App (EForce dl_back) (Pair (Var 4) (Var 1)))))
      (App (EForce dl_pass) (Pair (Var 7) (Pair (Var 4) (Var 1)))))))).

(** One let ⟨c, c′⟩ = new of main: the two ends at their types C1, C2. *)
Local Ltac new_block H S m1 m2 C1 C2 Hnew Htk :=
  apply sk_letp_inv in H as (?nDx & ?nDx & ?nDx & ?nAx & ?nAx & ?nTx & ?ncx & ?ncx & ?nHsx & Hn & ?nHax & H & _);
  apply sk_pair_inv in Hn as (?nDx & ?nDx & ?nDx & ?nBx & ?nBx & ?nBx & ?ncx & ?ncx & _ & Hn & _ & _ & Hag & HlA);
  apply sk_new_inv in Hn as (S & m1 & m2 & _ & Htk & HlB);
  apply sk_letu_inv in H as (?nDx & ?nDx & ?nDx & ?nTx & ?ncx & ?ncx & ?nHsx & _ & ?nHax & H & _);
  apply sk_letp_inv in H as (?nDx & ?nDx & ?nDx & C1 & C2 & ?nTx & ?ncx & ?ncx & ?nHsx & Hq & ?nHax & H & _);
  apply sk_var_anc in Hq; climb Hq; apply anc_top in Hq;
  apply skle_prod_inv in HlA as [HlA _];
  pose proof (skle_trans _ _ _ (skle_trans _ _ _ (skle_trans _ _ _ HlB (tage_skle _ _ _ Hag)) HlA) Hq) as Hnew;
  clear Hag HlA HlB Hq.

Lemma teq_skel_skle A B : teq A B → skle (skel A) (skel B) ∧ skle (skel B) (skel A).
Proof. intros H. apply teq_skle_both. by apply eqT_skel. Qed.

Lemma dual_seq_snd S m T R : unfoldS S = SSeq (SSnd m T) R → unfoldS (dual S) = SSeq (SRcv m T) (dual R).
Proof. intros H. by rewrite <-dual_unfoldS, H. Qed.

Lemma dual_seq_rcv S m T R : unfoldS S = SSeq (SRcv m T) R → unfoldS (dual S) = SSeq (SSnd m T) (dual R).
Proof. intros H. by rewrite <-dual_unfoldS, H. Qed.

Theorem rx_delegate_skel n Δ T c : ¬ sktyped (Some n) Δ dl_main T c.
Proof.
  intros H. unfold dl_main, let_new, ELet in H. simpl in H.
  new_block H Se me me' E1 E2 HnE HtkE.
  new_block H Sx mx mx' X1 X2 HnX HtkX.
  new_block H Sy my my' Y1 Y2 HnY HtkY.
  apply skle_prod_inv in HnE as [HE1 HE2].
  apply skle_prod_inv in HnX as [HX1 HX2].
  apply skle_prod_inv in HnY as [HY1 HY2].
  (* spawn (λ_. close e′): e is not idle *)
  apply sk_letu_inv in H as (Dqa1 & Dqa2 & Dqa2' & ? & ? & ? & Hsa & Hcl & Haa & H & _).
  apply sk_spawn_inv in Hcl as (? & ? & ? & Hcl).
  apply sk_abs_inv in Hcl as (Dqh0 & ? & ? & ? & ? & Hah0 & Hcl & _).
  apply sk_close_inv in Hcl as (S0 & ? & ? & ? & HS0 & Hv0 & _).
  apply sk_var_anc in Hv0. climb Hv0. apply anc_top in Hv0.
  destruct (skle_sess_inv _ _ _ _ _ _ _ _ (skle_trans _ _ _ HE2 Hv0)) as [HdSe _].
  assert (¬ idle Se) as HSe.
  { intros HI. apply (end_not_idle S0 HS0). apply (idle_sequiv _ _ HdSe). by apply idle_dual_iff. }
  (* spawn (λ_. (force back) ⟨x′, y′⟩) *)
  apply sk_letu_inv in H as (Dqb1 & Dqb2 & Dqb2' & ? & ? & ? & Hsb & Hbk & Hab & H & _).
  apply sk_spawn_inv in Hbk as (? & ? & ? & Hbk).
  apply sk_abs_inv in Hbk as (Δhb & ? & ? & ? & ? & Hahb & Hbk & _).
  apply sk_app_inv in Hbk as (Dqg1 & Dqg2 & Dqg2' & cgb & TargB & UrB & arB & cg1 & cg2 & Hsg & HfB & HagB & HpB & _ & _).
  apply sk_force_inv in HfB as (kB & cbB' & UB' & ssB & cfB & HlenB & HssB & HboxB & HlRB).
  assert (sktyped (Some n) Dqg1 dl_back (TBox 0 kB bcs0 None cbB' UB') cfB) as HboxB' by exact HboxB.
  clear HboxB. unfold dl_back, ELet in HboxB'. simpl in HboxB'.
  apply sk_box_inv in HboxB' as (kB0 & cbB & UB & _ & HbodyB & HblB).
  apply skle_box_l in HblB as (? & ? & [= -> -> ->] & _ & HbxB).
  apply sk_pair_inv in HpB as (Dqh1 & Dqh2 & Dqh2' & Q1 & Q1' & Q2 & ch1 & ch2 & Hsh & Hvx & Hah & Hvy & HagQ & HlQ).
  apply sk_var_anc in Hvx. climb Hvx. apply anc_top in Hvx.
  apply sk_var_anc in Hvy. climb Hvy. apply anc_top in Hvy.
  specialize (HbodyB ssB HlenB HssB).
  pose proof (boxeq_sinst _ _ _ _ _ HbxB HlenB HssB) as HteqB.
  apply skle_arr_r in HlRB as (? & RB & ? & ? & HRB & _ & _ & HTRB & _).
  rewrite HRB in HteqB.
  apply sk_abs_inv in HbodyB as (ΔhB & PB & ? & ? & ? & HahB & Hbb & HlUB).
  apply skle_arr_l in HlUB as (? & PB' & ? & ? & HUB & _ & _ & HPB & _).
  rewrite HUB in HteqB. apply teq_lolli_inv, teq_sym, teq_skle in HteqB.
  pose proof (skle_trans _ _ _ (skle_trans _ _ _ (skle_trans _ _ _ HlQ HTRB) HteqB) HPB) as HQP.
  apply skle_prod_l in HQP as (PB1 & PB2 & -> & HPB1 & HPB2).
  pose proof (skle_trans _ _ _ (skle_trans _ _ _ (skle_trans _ _ _ HX2 Hvx) (tage_skle _ _ _ HagQ)) HPB1) as Hx'.
  pose proof (skle_trans _ _ _ (skle_trans _ _ _ HY2 Hvy) HPB2) as Hy'.
  clear HPB1 HPB2.
  apply skle_sess_l in Hx' as (sB1 & ? & -> & HsB1 & _).
  apply skle_sess_l in Hy' as (sB2 & ? & -> & HsB2 & _).
  (* the body of back: λ⟨x, y⟩. let ⟨e, x⟩ = recv x in send ⟨e, y⟩ … *)
  apply sk_letp_inv in Hbb as (Dqk1 & Dqk2 & Dqk2' & K1 & K2 & ? & ? & ? & Hsk & Hvk & Hak & Hbb & _).
  apply sk_var_anc in Hvk. climb Hvk. apply anc_top in Hvk.
  apply skle_prod_inv in Hvk as [HK1 HK2].
  apply skle_sess_l in HK1 as (sK1 & ? & -> & HsK1 & _).
  apply skle_sess_l in HK2 as (sK2 & ? & -> & HsK2 & _).
  apply sk_letp_inv in Hbb as (Dqr1 & Dqr2 & Dqr2' & V1 & V2 & ? & ? & ? & Hsr & Hr & Har & Hbb & _).
  apply sk_recv_inv in Hr as (S0b & mb & Tpay & ? & ? & ? & ? & HSb & Hrv & HlRv & _).
  apply sk_var_anc in Hrv. climb Hrv. apply anc_top in Hrv.
  apply skle_sess_inv in Hrv as [HsKb _].
  apply skle_prod_inv in HlRv as [HTpay _].
  apply sk_letp_inv in Hbb as (Dqs1 & Dqs2 & Dqs2' & ? & ? & ? & ? & ? & Hss1 & Hsd & Has1 & _ & _).
  apply sk_pair_inv in Hsd as (Dqs3 & Dqs4 & Dqs4' & ? & ? & ? & ? & ? & Hss3 & Hsd & _ & _ & _ & _).
  apply sk_send_inv in Hsd as (S0q & mq & Qpay & ? & ? & ? & Tpb & Tpb' & ? & HSq & Hsp & HagTb & HlTb & _ & _).
  apply sk_pair_inv in Hsp as (Dqt1 & Dqt2 & Dqt2' & Z1 & Z1' & Z2 & ? & ? & Hst & Hve & Hat & Hvq & HagZ & HlZ).
  apply sk_var_anc in Hve. climb Hve. apply anc_top in Hve.
  apply sk_var_anc in Hvq. climb Hvq. apply anc_top in Hvq.
  apply skle_prod_inv in HlZ as [HZ1 HZ2].
  pose proof (skle_trans _ _ _ (skle_trans _ _ _ (skle_trans _ _ _ HTpay Hve) (tage_skle _ _ _ HagZ)) HZ1) as HTb.
  pose proof (skle_sess_inv _ _ _ _ _ _ _ _ (skle_trans _ _ _ Hvq HZ2)) as Hq'.
  (* (force pass) ⟨e, ⟨x, y⟩⟩ *)
  apply sk_app_inv in H as (Dqc1 & Dqc2 & Dqc2' & cf & Targ & Ur & ar & cc1 & cc2 & Hsc & Hf & Hac & Hp & _ & _).
  apply sk_force_inv in Hf as (k & cb' & U' & ss & cfo & Hlen & Hss & Hbox & HlR).
  assert (sktyped (Some n) Dqc1 dl_pass (TBox 0 k bcs0 None cb' U') cfo) as Hbox' by exact Hbox.
  clear Hbox. unfold dl_pass, ELet in Hbox'. simpl in Hbox'.
  apply sk_box_inv in Hbox' as (k0 & cb & U & _ & Hbody & Hbl).
  apply skle_box_l in Hbl as (? & ? & [= -> -> ->] & _ & Hbx).
  apply sk_pair_inv in Hp as (Dqd1 & Dqd2 & Dqd2' & Ge & Ge' & G2 & ? & ? & Hsd & Hve' & Had & Hp & HagG & HlG).
  apply sk_var_anc in Hve'. climb Hve'. apply anc_top in Hve'.
  apply sk_pair_inv in Hp as (Dqe1 & Dqe2 & Dqe2' & Gx & Gx' & Gy & ? & ? & Hse & Hvx2 & Hae & Hvy2 & HagGx & HlG2).
  apply sk_var_anc in Hvx2. climb Hvx2. apply anc_top in Hvx2.
  apply sk_var_anc in Hvy2. climb Hvy2. apply anc_top in Hvy2.
  specialize (Hbody ss Hlen Hss).
  pose proof (boxeq_sinst _ _ _ _ _ Hbx Hlen Hss) as Hteq.
  apply skle_arr_r in HlR as (? & R & ? & ? & HR & _ & _ & HTR & _).
  rewrite HR in Hteq.
  apply sk_abs_inv in Hbody as (Δh & P & ? & ? & ? & Hah' & Hb & HlU).
  apply skle_arr_l in HlU as (c' & P' & U1' & a' & HU & _ & _ & HPP & _).
  rewrite HU in Hteq. apply teq_lolli_inv, teq_sym, teq_skle in Hteq.
  pose proof (skle_trans _ _ _ (skle_trans _ _ _ HlG HTR) Hteq) as HGP'.
  apply skle_prod_l in HGP' as (P1' & P23' & -> & HP1' & HP23').
  apply skle_prod_l in HPP as (P1 & P23 & -> & HPP1 & HPP23).
  pose proof (skle_trans _ _ _ (skle_trans _ _ _ (skle_trans _ _ _ HE1 Hve') (tage_skle _ _ _ HagG)) HP1') as He1.
  apply skle_sess_l in He1 as (sP1' & β & -> & HsP1' & Hβme).
  apply skle_sess_l in HPP1 as (sP1 & pe & -> & HsP1 & Hpeβ).
  pose proof (skle_trans _ _ _ HlG2 (skle_trans _ _ _ HP23' HPP23)) as HG23.
  apply skle_prod_l in HG23 as (P2 & P3 & -> & HP2 & HP3).
  pose proof (skle_trans _ _ _ (skle_trans _ _ _ (skle_trans _ _ _ HX1 Hvx2) (tage_skle _ _ _ HagGx)) HP2) as Hx2.
  pose proof (skle_trans _ _ _ (skle_trans _ _ _ HY1 Hvy2) HP3) as Hy2.
  clear HP2 HP3.
  apply skle_sess_l in Hx2 as (sP2 & ? & -> & HsP2 & _).
  apply skle_sess_l in Hy2 as (sP3 & ? & -> & HsP3 & _).
  apply sinst_inv_lolli in HU as (Ap0 & Bp0 & -> & HA0 & _).
  symmetry in HA0. apply sinst_inv_prod in HA0 as (Ap01 & Ap02 & -> & HA01 & _).
  symmetry in HA01. apply sinst_inv_sess in HA01 as (s0 & -> & _).
  (* the body of pass: λ⟨e, ⟨x, y⟩⟩ *)
  apply sk_letp_inv in Hb as (Dq1 & Dq2 & Dq2' & T1 & T23 & ? & ? & ? & Hs1 & Hv & Ha1 & Hb & _).
  apply sk_var_anc in Hv. climb Hv. apply anc_top in Hv.
  apply skle_prod_inv in Hv as [HT1 HT23].
  apply skle_sess_l in HT1 as (sT1 & t1 & -> & HsT1 & Ht1).
  apply sk_letp_inv in Hb as (Dq3 & Dq4 & Dq4' & W1 & W2 & ? & ? & ? & Hs3 & Hv & Ha3 & Hb & _).
  apply sk_var_anc in Hv. climb Hv. apply anc_top in Hv.
  destruct (skle_prod_inv _ _ _ _ (skle_trans _ _ _ HT23 Hv)) as [HW1 HW2].
  apply skle_sess_l in HW1 as (sW1 & ? & -> & HsW1 & _).
  apply skle_sess_l in HW2 as (sW2 & ? & -> & HsW2 & _).
  (* let x = send ⟨e, x⟩ *)
  apply sk_letp_inv in Hb as (Dq5 & Dq6 & Dq6' & ? & ? & ? & ? & ? & Hs5 & Hsd' & Ha5 & Hb & _).
  apply sk_pair_inv in Hsd' as (Dq7 & Dq8 & Dq8' & ? & ? & ? & ? & ? & Hs7 & Hsd' & _ & _ & _ & _).
  apply sk_send_inv in Hsd' as (S0x & mx0 & Tpx & ? & ? & ? & Tp & Tp' & ? & HSx & Hsp & HagTp & HlTp & _ & _).
  apply sk_pair_inv in Hsp as (Dq9 & Dq10 & Dq10' & Ze & Ze' & Zx & ? & ? & Hs9 & Hve2 & Ha9 & Hvx3 & HagZe & HlZe).
  apply sk_var_anc in Hve2. climb Hve2. apply anc_top in Hve2.
  apply sk_var_anc in Hvx3. climb Hvx3. apply anc_top in Hvx3.
  apply skle_prod_inv in HlZe as [HZe HZx].
  pose proof (skle_trans _ _ _ (skle_trans _ _ _ Hve2 (tage_skle _ _ _ HagZe)) HZe) as HTp.
  apply skle_sess_l in HTp as (sTp & tp & -> & HsTp & Htp).
  destruct (skle_sess_inv _ _ _ _ _ _ _ _ (skle_trans _ _ _ Hvx3 HZx)) as [HsX0 _].
  (* let ⟨e, y⟩ = recv y *)
  apply sk_letu_inv in Hb as (Dq11 & Dq12 & Dq12' & ? & ? & ? & Hs11 & _ & Ha11 & Hb & _).
  apply sk_letp_inv in Hb as (Dq13 & Dq14 & Dq14' & J1 & J2 & ? & ? & ? & Hs13 & Hry & Ha13 & Hb & _).
  apply sk_recv_inv in Hry as (S0y & my0 & Qy & ? & ? & ? & ? & HSy & Hry & HlRy & _).
  apply sk_var_anc in Hry. climb Hry. apply anc_top in Hry.
  apply skle_sess_inv in Hry as [HsY0 _].
  apply skle_prod_inv in HlRy as [HQy _].
  (* (force f) ⟨e, x, y⟩ *)
  apply sk_app_inv in Hb as (Dq15 & Dq16 & Dq16' & ? & Targ3 & ? & ? & ? & ? & Hs15 & Hf3 & Ha15 & Hp3 & _ & _).
  apply sk_force_inv in Hf3 as (k3 & cb3 & U3 & ss3 & ? & _ & _ & Hfv & HlR3).
  apply sk_var_anc in Hfv. climb Hfv. apply anc_top in Hfv.
  apply skle_box_l in Hfv as (? & ? & [= -> -> ->] & _ & Hbx3).
  apply sk_pair_inv in Hp3 as (Dq17 & Dq18 & Dq18' & G1 & G1' & ? & ? & ? & Hs17 & Hvg & Ha17 & _ & HagG1 & HlG1).
  apply sk_var_anc in Hvg. climb Hvg. apply anc_top in Hvg.
  apply boxeq_teq, teq_lolli_l in Hbx3 as (A'' & B'' & -> & HA'' & _).
  apply teq_prod_l in HA'' as (A1'' & A2'' & -> & HA1'' & _).
  apply teq_sess_l in HA1'' as (s0' & -> & _).
  simpl in HlR3. apply skle_arr_l in HlR3 as (? & ? & ? & ? & [= _ <- _ _] & _ & _ & HTarg3 & _).
  apply skle_prod_r in HTarg3 as (Tg1 & Tg2 & -> & HTg1 & _).
  apply skle_prod_inv in HlG1 as [HlG1 _].
  pose proof (skle_trans _ _ _ (skle_trans _ _ _ (skle_trans _ _ _ (skle_trans _ _ _ HQy Hvg)
    (tage_skle _ _ _ HagG1)) HlG1) HTg1) as HQβ.
  apply skle_sess_r in HQβ as (sq & qy & HQy' & _ & Hβq).
  (* e is not idle in pass and in back *)
  assert (¬ idle sTp) as HnTp.
  { intros HI. apply HSe. apply (idle_sequiv _ _ HsP1'), (idle_sequiv _ _ HsP1), (idle_sequiv _ _ HsT1).
    by apply (idle_sequiv _ _ HsTp). }
  apply tage_sess_nonidle in HagTp as [H1tp ->]; [|done].
  apply skle_sess_l in HlTp as (spx & px & HTpx & HsTpx & Hpx).
  (* the payload on x: p_x in pass and in back *)
  assert (sequiv Sx S0x) as HSxX.
  { eapply sequiv_trans; [exact HsP2|]. eapply sequiv_trans; [exact HsW1|exact HsX0]. }
  destruct (sequiv_unfold_snd' _ _ _ _ _ HSxX HSx) as (Tx' & Rx' & HSxu & HTx').
  assert (sequiv (dual Sx) S0b) as HSxB.
  { eapply sequiv_trans; [exact HsB1|]. eapply sequiv_trans; [exact HsK1|exact HsKb]. }
  destruct (sequiv_unfold_rcv' _ _ _ _ _ HSxB HSb) as (Tx'' & Rx'' & HSxu' & HTx'').
  rewrite (dual_seq_snd _ _ _ _ HSxu) in HSxu'. injection HSxu' as <- <-.
  destruct (teq_skel_skle _ _ (teq_trans _ _ _ (teq_sym _ _ HTx') HTx'')) as [Hpxb _].
  rewrite HTpx in Hpxb.
  pose proof (skle_trans _ _ _ Hpxb HTb) as HTb'.
  apply skle_sess_l in HTb' as (sTb & tb & -> & HsTb & Htb).
  assert (¬ idle sTb) as HnTb.
  { intros HI. apply HnTp. apply (idle_sequiv _ _ HsTpx). by apply (idle_sequiv _ _ HsTb). }
  apply tage_sess_nonidle in HagTb as [H1tb ->]; [|done].
  (* the payload on y: p_y in back and in pass *)
  assert (sequiv Sy S0y) as HSyY.
  { eapply sequiv_trans; [exact HsP3|]. eapply sequiv_trans; [exact HsW2|exact HsY0]. }
  destruct (sequiv_unfold_rcv' _ _ _ _ _ HSyY HSy) as (Qy' & Ry' & HSyu & HQy1).
  assert (sequiv (dual Sy) S0q) as HSyB.
  { eapply sequiv_trans; [exact HsB2|]. eapply sequiv_trans; [exact HsK2|exact (proj1 Hq')]. }
  destruct (sequiv_unfold_snd' _ _ _ _ _ HSyB HSq) as (Qy'' & Ry'' & HSyu' & HQy2).
  rewrite (dual_seq_rcv _ _ _ _ HSyu) in HSyu'. injection HSyu' as <- <-.
  destruct (teq_skel_skle _ _ (teq_trans _ _ _ (teq_sym _ _ HQy1) HQy2)) as [_ Hqb].
  rewrite HQy' in Hqb.
  pose proof (skle_trans _ _ _ HlTb Hqb) as Hq.
  apply skle_sess_inv in Hq as (_ & Hqyb & _).
  (* β ≤ p_y ≤ t_b − 1 ≤ p_x − 1 ≤ t_p − 2 ≤ t_1 − 2 ≤ p_e − 2 ≤ β − 2, β ≤ me finite *)
  clear - HtkE Hβme Hpeβ Ht1 Htp H1tp Hpx Htb H1tb Hqyb Hβq.
  unfold tsum_ok in HtkE.
  destruct me, me', β, pe, t1, tp, px, tb, qy; simpl in *; lia.
Qed.

Theorem rx_delegate_rejected n W Θ Γ Δ F T c : ¬ typed W (Some n) Θ Γ Δ F dl_main T c.
Proof. intros H. apply typed_skel in H. exact (rx_delegate_skel _ _ _ _ H). Qed.

Corollary rx_delegate_proc_rejected n W T : ¬ fptyped (Some n) W ∅ (∅, {[+ dl_main +]}) T.
Proof.
  intros H. apply fptyped_one in H as (ΘB & c & _ & _ & _ & _ & _ & _ & H & _).
  exact (rx_delegate_rejected _ _ _ _ _ _ _ _ H).
Qed.
