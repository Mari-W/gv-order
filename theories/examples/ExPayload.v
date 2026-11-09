(** * Existential payloads as a derived form

    A message whose payload introduces facts at the send: the sender
    proves the facts, the receiver assumes them. The payload type of a
    send already is any type, so the payload may be an existential
    ∃^ℓ ι. C. T. The sender packs (E-Pack, C proved at the instance),
    sends, and the receiver opens (E-Open, C as a hypothesis). No rule
    and no definition of the core changes.

    The example. A server creates a signal channel k₁ at the payload
    point a[0] and a data channel k₂ at a point v with the creation
    constraint {a[0] ≺ v}. Under the constant world (sharp edges 172) v
    is a top-level point of the program, and the server creates k₂ with
    new@v ([ex_Ψ]). It sends both ends in one message on
    c, the end of k₂ packed with the fact a[0] ≺ ι:

      Pay = ∃ι₀. Close@ι₀ ⊗ ∃^{ι₀} ι. {ι₀ ≺ ι}. (!∗.Close)@ι
      Sx  = !Pay.Close

      server = let (k₁, k₁′) = new ∗ at a[0] in
               let (k₂, k₂′) = new ∗ with {a[0] ≺ ι} in
               let () = spawn (λu. let () = u in recvclose k₂) in
               let () = close (send ⟨⟨k₁′, pack k₂′⟩, c⟩) in close k₁
      client = let (p, c′) = recv c′ in let () = close c′ in
               let (k₁′, q) = p in [open q as k₂′ at v′]
               let () = close k₁′ in close (send ⟨∗, k₂′⟩)
      ex_main = let (c, c′) = new ∗ at a in
                let () = spawn (λu. let () = u in server) in client

    The client closes k₁′ at a[0] while it holds k₂′ at v′ and asks
    a[0] ≺ v′. That fact is the hypothesis E-Open gives it. The point v′
    is not a payload point of c, so no constraint written before the
    receive mentions it. The top-level constraint is {a+1 ≺ a[0]}.

    With end points the two ends of a channel sit at dual points. k₁ is
    created at (a[0])‾ so that the sent end k₁′ sits at the payload
    point a[0]. k₂ is created at v with {a[0] ≺ v, a[0] ≺ v̄}, k₂′ sits
    at v̄, and the payload constraint becomes {ι₀ ≺ ι, ι₀ ≺ ῑ}, because
    the client blocks at a[0] while it holds k₂′ at v′, whose partner
    point is v̄′. The top-level constraint states a+1 ≺ a[0] at all four
    polarities. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.ExampleTools.
From LRGV Require Import examples.cfst.CfstTools.
From LRGV Require Import static.SourceRules.

Set Default Proof Using "All".

Abbreviation pa k := (pv 0 k).
Abbreviation pa0 k := (Pt (NPayload (NVar 0) 0 0) k).
Abbreviation pb k := (pv 1 k).
Abbreviation pb0 k := (Pt (NPayload (NVar 1) 0 0) k).
(** a at the constant 1 and its field point (syntactic points, sharp
    edges 173). *)
Abbreviation pbc k := (pc 1 k).
Abbreviation pb0c k := (Pt (NPayload (NConst 1) 0 0) k).

(** ** The payload *)

(** {ι₀ ≺ ι}: the variable 0 is ι, the variable 1 is the outer point ι₀. *)
Definition Cx : bcs := BCs [pvar 0] (λ g, g = FLt (pvar 1) (pvar 0) ∨ g = FLt (pvar 1) (pt_dual (pvar 0))).
Definition Pay : ty := TProd (TSess SEnd (pvar 0)) (TEx (LPt (pvar 0)) 1 Cx (TSess Sd (pvar 0))).
Definition Sx : sty := SSeq (SSnd 1 Pay) SEnd.

Definition Cx_at (x : point) : bcs := BCs [x] (λ g, g = FLt (pvar 1) (pvar 0) ∨ g = FLt (pvar 1) (pt_dual (pvar 0))).

Lemma pay_at x :
  payload_at 1 Pay x =
  TProd (TSess SEnd (pt_payload x 0)) (TEx (LPt (pt_payload x 0)) 1 (Cx_at (pt_payload x 0)) (TSess Sd (pvar 0))).
Proof. reflexivity. Qed.

(** ** The program *)

Definition server : expr :=
  let_new_pair_at (EPt (pt_dual (pb0c 0))) (let_new_pair_at (EPt (pconst 0))
    (LetU (App ESpawn (Lam (LetU (Var 0) (recvclose (Var 2)))))
      (LetU (App EClos (App ESend (Pair (Pair (Var 2) (Var 0)) (Var 6))))
        (App EClos (Var 3))))).

Definition client : expr :=
  LetP (App ERecv (Var 0))
    (LetU (App EClos (Var 0))
      (LetP (Var 1)
        (LetU (App EClos (Var 1)) (sendclose (Var 0))))).

Definition ex_main : expr :=
  let_new_pair_at (EPt (pconst 1)) (LetU (App ESpawn (Lam (LetU (Var 0) server))) client).

Definition ex_fact (g : fact) : Prop :=
  g = FLt (pa 1) (pa0 0) ∨ g = FLt (pa 1) (pt_dual (pa0 0)) ∨
  g = FLt (pt_dual (pa 1)) (pa0 0) ∨ g = FLt (pt_dual (pa 1)) (pt_dual (pa0 0)).
Definition C0x : bcs := BCs [] ex_fact.

(** The creation constraint of k₂ at v = 0 with a[0] = 1 outside. *)
Definition Ck2 : bcs := BCs [pb0c 0] (λ g, g = FLt (pvar 1) (pvar 0) ∨ g = FLt (pvar 1) (pt_dual (pvar 0))).

Lemma ck2_ok peq plt : cc_ok peq plt Ck2.
Proof.
  apply (cc_ok_out _ _ Ck2 olt); [exact olt_trans|exact olt_irrefl|intros x _; apply olt_po|intros x _; apply olt_dpo| |].
  - intros a b (f & [-> | ->] & _ & E); injection E as -> ->; cbn; auto.
  - intros u p q v (f & [-> | ->] & _ & E) (f' & [-> | ->] & _ & E') Hu Hp Hq Hv _;
      injection E as -> ->; injection E' as -> ->; exfalso; apply Hu, Hq.
Qed.

Lemma ex_rank_ok : c0_acyclic 1 C0x.
Proof.
  set (r := λ x : point, match pt_name x with
    | NPayload (NVar 0) 0 0 => 15 + 10 * pt_off x
    | _ => 10 * pt_off x
    end).
  apply (c0_acyclic_rank 1 _ r).
  - intros [p pb o]. unfold r, pt_shift. simpl. repeat case_match; lia.
  - intros x y [[= -> ->]|[[= -> ->]|[[= -> ->]|[= -> ->]]]]; unfold r; cbn; lia.
  - intros [p pb o]. done.
Qed.

(** The top-level points (sharp edges 172): a with the constraint C₀,
    then v under the creation constraint of k₂. The server creates k₂
    with new@v, so v is a top-level point and its facts are facts of
    the initial world. *)
Definition ex_Ψ : hyps :=
  ([] ++ [(C0x, [pconst 1])]) ++ [(Ck2, [pconst 0])].

Lemma ex_created : created (Wpo []) ex_Ψ.
Proof.
  apply created_snoc; [apply created_snoc; [constructor| |constructor|fresh_const]|apply ck2_ok| |fresh_const].
  - set (r := λ x : point, match pt_name x with
      | NPayload (NVar 0) 0 0 => 15 + 10 * pt_off x
      | _ => 10 * pt_off x
      end).
    apply (cc_ok_inner _ _ ex_fact (λ x y, r x < r y)).
    + intros x y z; lia.
    + intros x; lia.
    + intros [q pb o] _. unfold r, pt_shift. simpl. repeat case_match; lia.
    + intros g Hg _. destruct Hg as [-> |[-> |[-> | ->]]]; eexists _, _; (split; [done|]); unfold r; cbn; lia.
    + intros [q pb o] _. unfold r, pt_shift, pt_dual. simpl. repeat case_match; lia.
  - cbn. constructor; [|constructor]. right. exists C0x, [pconst 1], (pconst 1).
    split_and!; [by left|by left|done].
Qed.

(** ** The derived rules

    Send-∃ is E-Pack of the value followed by the send signature. The
    send asks x ≺ ℓ for the lower bound ℓ of the packed payload, and
    E-Pack asks ℓ at or below every head of the value. Recv-∃ is the
    receive signature, E-LetPair and E-Open of the bound payload, which
    adds C at fresh points as a hypothesis. *)

Lemma sf_union_none F : sf_union F (opt_heads None) = F.
Proof. destruct F as [P o]. unfold sf_union. cbn. by rewrite union_empty_r_L. Qed.

Lemma send_ex Φ Ψ Δ Δ1 Δ2 F v c m P S x l n C T ys :
  payload_at m P x = TEx (LPt l) n C T → hbot P = false → pscoped m P →
  lenv_split Δ Δ1 Δ2 →
  length ys = n → Forall (hyp_known Ψ) ys → bcs_hold (heqs Ψ) (hlt Ψ) C ys →
  (∀ y, y ∈ heads (ty_inst ys T) → hle Ψ l y) → hbot (ty_inst ys T) = false →
  hlt Ψ x l → hub_below_s Ψ Φ (Some x) F →
  styped Φ Ψ Δ1 (sf_unionb F (lenv_heads Δ2) (lenv_bot Δ2)) v (ty_inst ys T) →
  styped Φ Ψ Δ2 (sf_union F {[l]}) c (TSess (SSeq (SSnd m P) S) x) →
  styped Φ Ψ Δ F (App ESend (Pair v c)) (TSess S (pt_shift 1 x)).
Proof.
  intros Hpay Hb Hsc Hs Hn HK HC Hl Hbt Hxl Hub Hv Hc.
  eapply (st_app Φ Ψ Δ (lenv_nones Δ) Δ F _ _ (Some x) None
            (TProd (payload_at m P x) (TSess (SSeq (SSnd m P) S) x))).
  - apply lenv_split_nones_l.
  - exact Hub.
  - apply st_konst; [apply lenv_empty_nones| |exact Hsc].
    apply KTSend. rewrite Hb. intros h Hh. rewrite Hpay in Hh. cbn in Hh.
    apply elem_of_singleton in Hh as ->. exact Hxl.
  - rewrite sf_union_none. eapply (st_pair _ _ _ Δ1 Δ2); [exact Hs| |].
    + rewrite Hpay. eapply st_pack; [exact Hn|exact HK|exact HC|split; [exact Hl|exact Hbt]|exact Hv].
    + rewrite Hpay. exact Hc.
Qed.

Lemma recv_ex Φ Ψ Δ Δ1 Δ2 F c e m P S x lb n C T U :
  payload_at m P x = TEx lb n C T → ¬ unlimited T → pscoped m P →
  lenv_split Δ Δ1 Δ2 →
  hub_below_s Ψ Φ (Some x) (sf_unionb F (lenv_heads Δ2) (lenv_bot Δ2)) →
  styped Φ Ψ Δ1 (sf_unionb F (lenv_heads Δ2) (lenv_bot Δ2)) c (TSess (SSeq (SRcv m P) S) x) →
  styped (fhyps_pinst (pshift n) Φ) (hyps_inst (pshift n) Ψ ++ [(bcs_inst (pshift n) C, ids n)])
    (<[1 := Some T]> (lenv_pinst (pshift n)
       (Some (TSess S (pt_shift 1 x)) :: Some (TEx lb n C T) :: Δ2)))
    (sf_pinst (pshift n) F) e (pinst_ty (pshift n) U) →
  styped Φ Ψ Δ F (LetP (App ERecv c) e) U.
Proof.
  intros Hpay Hu Hsc Hs Hub Hc He.
  eapply (st_letp Φ Ψ Δ Δ1 Δ2 F _ _ (payload_at m P x) (TSess S (pt_shift 1 x))); [exact Hs| |].
  - eapply (st_app _ _ Δ1 (lenv_nones Δ1) Δ1 _ _ _ (Some x) None (TSess (SSeq (SRcv m P) S) x)).
    + apply lenv_split_nones_l.
    + exact Hub.
    + apply st_konst; [apply lenv_empty_nones|apply KTRecv|exact Hsc].
    + rewrite sf_union_none. exact Hc.
  - rewrite Hpay. eapply (st_open _ _ _ _ _ 1); [done|exact Hu|exact He].
Qed.

(** ** Typing *)

Lemma pay_scoped : pscoped 1 Pay.
Proof.
  cbn. split; [|split; [|split]].
  - intros ? Hv. injection Hv. lia.
  - intros ? Hv. injection Hv. lia.
  - unfold bcs_scoped. cbn. constructor; [|constructor]. intros ? Hv. injection Hv. lia.
  - intros ? Hv. injection Hv. lia.
Qed.

Lemma ex_typed : styped ∅ ex_Ψ [] (∅, None) ex_main TUnit.
Proof.
  apply styped_wnil. set (W := wnil). unfold ex_Ψ. cbn.
  match goal with |- typed _ _ ?Q _ _ _ _ _ => set (Ψ := Q) end.
  pose proof wnil_strict as HWs. pose proof (proj1 HWs) as HW. unfold ex_main, let_new_pair_at.
  assert (slt W Ψ (pt_dual (pbc 1)) (pb0c 0)) as F1.
  { apply (sl_hyp0 W Ψ ex_fact [pconst 1] (pt_dual (pa 1)) (pa0 0)); [by left|by right; right; left|split; cbn; lia|reflexivity|reflexivity]. }
  assert (slt W Ψ (pt_dual (pbc 1)) (pt_dual (pb0c 0))) as F1b.
  { apply (sl_hyp0 W Ψ ex_fact [pconst 1] (pt_dual (pa 1)) (pt_dual (pa0 0))); [by left|by right; right; right|split; cbn; lia|reflexivity|reflexivity]. }
  assert (skn W Ψ (pt_dual (pb0c 0))) as Ka0d by (right; exists C0x, [pconst 1], (pconst 1); split_and!; [by left|by left|done]).
  assert (skn W Ψ (pbc 0)) as Ka by (right; exists C0x, [pconst 1], (pconst 1); split_and!; [by left|by left|done]).
  assert (skn W Ψ (pb0c 0)) as Ka0 by (right; exists C0x, [pconst 1], (pconst 1); split_and!; [by left|by left|done]).
  apply (t_new_at W _ _ _ _ _ _ _ Sx (pbc 0) HWs ltac:(ground) Ka). cbn.
  tstep.
  { (* the server thread *)
    tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pt_dual (pb0c 0))) (Some (pt_dual (pbc 0))) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
    cbn. tstep; [tstep|]. cbn. unfold server, let_new_pair_at.
    apply (t_new_at W _ _ _ _ _ _ _ SEnd (pt_dual (pb0c 0)) HWs ltac:(ground) Ka0d). cbn.
    assert (skn W Ψ (pconst 0)) as Kv0 by (right; eexists _, [pconst 0], (pconst 0); split_and!; [by right; left|by left|done]).
    apply (t_new_at W _ _ _ _ _ _ _ (dual Sd) (pconst 0) HWs ltac:(ground) Kv0).
    cbn.
    match goal with |- typed _ _ ?Q _ _ _ _ _ => set (Ψ' := Q) end.
    assert (slt W Ψ' (pc 1 1) (Pt (NPayload (NConst 1) 0 0) 0)) as F1'.
    { apply (sl_hyp0 W Ψ' ex_fact [pconst 1] (pa 1) (pa0 0)); [by left|by left|split; cbn; lia|done|done]. }
    assert (slt W Ψ' (pc 1 1) (pt_dual (Pt (NPayload (NConst 1) 0 0) 0))) as F1d.
    { apply (sl_hyp0 W Ψ' ex_fact [pconst 1] (pa 1) (pt_dual (pa0 0))); [by left|by right; left|split; cbn; lia|done|done]. }
    assert (slt W Ψ' (Pt (NPayload (NConst 1) 0 0) 0) (pconst 0)) as G.
    { eapply (sl_hyp W Ψ' _ _ [pconst 0] (FLt (pvar 1) (pvar 0))); [by right; left|by left|fsc|reflexivity]. }
    assert (slt W Ψ' (Pt (NPayload (NConst 1) 0 0) 0) (pt_dual (pconst 0))) as G'.
    { eapply (sl_hyp W Ψ' _ _ [pconst 0] (FLt (pvar 1) (pt_dual (pvar 0)))); [by right; left|by right|fsc|reflexivity]. }
    assert (slt W Ψ' (pc 1 0) (Pt (NPayload (NConst 1) 0 0) 0)) as F0'.
    { eapply sl_trans; [apply (slt_po W _ (pc 1 0) HW)|exact F1']. }
    assert (slt W Ψ' (pc 1 0) (pt_dual (Pt (NPayload (NConst 1) 0 0) 0))) as F0d.
    { eapply sl_trans; [apply (slt_po W _ (pc 1 0) HW)|exact F1d]. }
    assert (skn W Ψ' (pt_dual (pconst 0))) as Kv.
    { right. eexists _, [pconst 0], (pconst 0). split_and!; [by right; left|by left|done]. }
    tstep.
    { (* the receiver of k₂ *)
      tstep; [|apply KTSpawn|done|apply ubs_none].
      eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pc 0 1)) (Some (pt_dual (pconst 0))) 1); [set_solver| |].
      { intros y Hy. mem_cases Hy. apply sle_refl, HW. }
      cbn. tstep; [tstep|]. cbn. unfold recvclose. tstep.
      - tstep; [tstep|apply KTRecv|kscope|].
        apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pc 0 1). split; [done|]. right. apply (slt_po W _ (pconst 0) HW).
      - cbn. tstep; [tstep|]. cbn. tstep; [tstep|apply KTClos|done|].
        apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pc 0 1). split; [done|]. apply sle_refl, HW. }
    cbn. tstep.
    { (* send ⟨⟨k₁′, pack k₂′⟩, c⟩, then close c *)
      tstep; [|apply (KTClos _ _ _ (pc 1 1))|done|].
      - tstep; [|apply (KTSend _ _ _ 1 Pay SEnd (pc 1 0))|exact pay_scoped|].
        + rewrite pay_at. tstep; [tstep|]. tstep; [|tstep].
          eapply (t_pack W _ _ _ _ _ _ (LPt (Pt (NPayload (NConst 1) 0 0) 0)) 1
                    (Cx_at (Pt (NPayload (NConst 1) 0 0) 0)) (TSess Sd (pvar 0)) [pt_dual (pconst 0)]).
          * done.
          * constructor; [exact Kv|constructor].
          * apply bcs_hold_env. intros f [-> | ->] _; cbn; [exact G'|exact G].
          * split; [|done]. intros y Hy. mem_cases Hy. right. exact G.
          * cbn. tstep.
        + rewrite pay_at. cbn. intros h Hh. mem_cases Hh; first [exact F0'|exact F0d].
        + apply ubs_intro; [intros y Hy; mem_cases Hy; first [exact F0'|exact F0d]|].
          exists (pt_dual (Pt (NPayload (NConst 1) 0 0) 0)). split; [done|]. right. exact F0d.
      - apply ubs_intro; [intros y Hy; mem_cases Hy; first [exact F1'|exact F1d]|].
        exists (pt_dual (Pt (NPayload (NConst 1) 0 0) 0)). split; [done|]. right. exact F1d. }
    (* close k₁ *)
    tstep; [tstep|apply KTClos|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (pt_dual (Pt (NPayload (NConst 1) 0 0) 0)). split; [done|]. apply sle_refl, HW. }
  (* the client *)
  cbn. unfold client. tstep.
  { tstep; [tstep|apply KTRecv|exact pay_scoped|]. apply ubs_intro; [intros y Hy; mem_cases Hy|done]. }
  rewrite pay_at. cbn. tstep.
  { tstep; [tstep|apply KTClos|done|]. apply ubs_intro; [intros y Hy; mem_cases Hy; first [exact F1|exact F1b]|done]. }
  cbn. tstep; [tstep|]. cbn.
  eapply (tv_open W _ _ _ _ _ 0); [reflexivity|intros []|reflexivity|reflexivity|reflexivity|reflexivity|reflexivity|].
  cbn. rewrite ?sf_pinst_empty.
  match goal with |- typed _ _ ?Q _ _ _ _ _ => set (Ψ'' := Q) end.
  assert (slt W Ψ'' (Pt (NPayload (NConst 1) 0 0) 0) (pvar 0)) as H0.
  { assert ((bcs_inst (pshift 1) (Cx_at (pt_payload (pbc 0) 0)), [pvar 0]) ∈ Ψ'') as Hin by (by right; right; left).
    assert (bcs_open 1 (bcs_inst (pshift 1) (Cx_at (pt_payload (pbc 0) 0)))
              (fact_map (pt_inst (pup 1 (plist [pt_inst (pshift 1) (pt_payload (pbc 0) 0)])))
                 (FLt (pvar 1) (pvar 0)))) as Ho.
    { exists (FLt (pvar 1) (pvar 0)). split_and!; [by left|split; cbn; lia|done]. }
    apply (hyp_in_fact W Ψ'' _ _ Hin) in Ho. exact Ho. }
  assert (slt W Ψ'' (Pt (NPayload (NConst 1) 0 0) 0) (pt_dual (pvar 0))) as H0d.
  { assert ((bcs_inst (pshift 1) (Cx_at (pt_payload (pbc 0) 0)), [pvar 0]) ∈ Ψ'') as Hin by (by right; right; left).
    assert (bcs_open 1 (bcs_inst (pshift 1) (Cx_at (pt_payload (pbc 0) 0)))
              (fact_map (pt_inst (pup 1 (plist [pt_inst (pshift 1) (pt_payload (pbc 0) 0)])))
                 (FLt (pvar 1) (pt_dual (pvar 0))))) as Ho.
    { exists (FLt (pvar 1) (pt_dual (pvar 0))). split_and!; [by right|split; cbn; lia|done]. }
    apply (hyp_in_fact W Ψ'' _ _ Hin) in Ho. exact Ho. }
  tstep.
  { tstep; [tstep|apply KTClos|done|]. apply ubs_intro; [intros y Hy; mem_cases Hy; first [exact H0d|exact H0]|done]. }
  cbn. unfold sendclose. tstep; [|apply KTClos|done|apply ubs_intro; [intros y Hy; mem_cases Hy|done]].
  tstep; [|apply (KTSend _ _ _ 0 TUnit SEnd (pvar 0)); cbn; set_solver|done|].
  - tstep; tstep.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|done].
Qed.

Theorem ex_deadlock_free : deadlock_free (∅, {[+ ex_main +]}).
Proof. apply (soundness_created_s ex_Ψ _ TUnit ex_created); [constructor|apply ex_typed]. Qed.
