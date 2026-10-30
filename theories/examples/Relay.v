(** * relay: typable, recursive (SHARP-EDGES 65)

      S = μX. ?(∃ι. D@ι).X      D = ?∗.Close
      C₀(x, y) = {x ≺ y, x ≺ x[0], x[0] ≺ x+1, x[0] ≺ y, y ≺ x+1, y ≺ x[0]+1}
      C = C₀(ι, ι′) ∪ {C₀(ι+k+1, ι+k[0]+1) ∣ k ∈ ℕ}       (slots from 0)
      relay : □(∀ι ι′. C. ∗ ⊸^⊥_⊤ (S@ι ⊗ Close@ι′ ⊸^{ι′}_⊤ ∗))
      relay = !(f = λp. let (c, d) = p in let (e, c) = recv c in
                       let (v, e) = recv e in let () = v in let () = close d in
                       spawn (λw. let () = w in (force f) ⟨c, e⟩))
      prod  : the same box over S̄ ⊗ Close
      prod  = !(g = λp. let (c, d) = p in let (e, e′) = new ∗ in
                       let (c, u) = ⟨send ⟨e, c⟩, ∗⟩ in let () = u in
                       let (e′, u) = ⟨send ⟨∗, e′⟩, ∗⟩ in let () = u in let () = close d in
                       spawn (λw. let () = w in (force g) ⟨c, e′⟩))
      rel_main = let (r, g) = ⟨relay, prod⟩ in let (c, c′) = new ∗ in let (d, d′) = new ∗ in
                 let () = spawn (λw. let () = w in (force r) ⟨c, d⟩) in (force g) ⟨c′, d′⟩

    The relay is §8.2's with a spawn in place of the tail call, which
    removes the ceiling. prod creates e at ι[0], the slot its payload
    must live at, so it needs new under □∀ (59) and ι ≺ ι[0] for its
    send. The call at (ι+1, ι[0]+1) asks C there, which is round 0 of
    the family and round k+1 for round k, so C[ι+1, ι[0]+1] ⊆ C
    ([rel_sub]). At ((a,0), (b,0)) round k is C₀((a,k), [rel_ip] k),
    with rel_ip 0 = (b,0) and rel_ip (k+1) = (a,k)[0]+1. [Wrel] orders
    them by the ranks 3k+3, 3k+4+4o for (a,k)[0]+o, and 5 for (b,0). *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.ExampleTools.

Set Default Proof Using "All".

Definition Dr : sty := SRcv 0 TUnit SEnd.
Definition Srl : sty := SMu (SRcv 1 (TSess Dr (Pt (NVar 0) 0)) (SVar 0)).

Abbreviation sv o := (Pt (NSlot (NVar 0) 0 0) o).

Definition c0 (x y : point) (g : fact) : Prop :=
  g = FLt x y ∨ g = FLt x (pt_slot x 0) ∨ g = FLt (pt_slot x 0) (pt_shift 1 x) ∨
  g = FLt (pt_slot x 0) y ∨ g = FLt y (pt_shift 1 x) ∨ g = FLt y (pt_shift 1 (pt_slot x 0)).

Definition rel_P (g : fact) : Prop :=
  c0 (pv 0 0) (pv 1 0) g ∨ ∃ k, c0 (pv 0 (S k)) (Pt (NSlot (NVar 0) k 0) 1) g.

Definition rel_C : bcs := BCs [] rel_P.

Lemma c0_inst σ x y g : c0 x y g → c0 (pt_inst σ x) (pt_inst σ y) (fact_map (pt_inst σ) g).
Proof.
  unfold c0. intros [-> | [-> | [-> | [-> | [-> | ->]]]]]; cbn [fact_map];
    rewrite ?pt_inst_slot, ?pt_inst_shift, ?pt_inst_slot;
    repeat (first [left; reflexivity|right]); reflexivity.
Qed.

(** C[ι+1, ι[0]+1] ⊆ C: round 0 goes to round 0 of the family, round
    k+1 to round k+2. *)
Lemma rel_sub g : rel_P g → fact_scoped 2 g → rel_P (fact_map (pt_inst (plist [pv 0 1; sv 1])) g).
Proof.
  intros [Hg|(k & Hg)] _; right.
  - exists 0. exact (c0_inst _ _ _ _ Hg).
  - exists (S k). exact (c0_inst _ _ _ _ Hg).
Qed.

Lemma rel_call W Ψ :
  (rel_C, ids 2) ∈ Ψ → bcs_hold (seqs W Ψ) (slt W Ψ) rel_C [pv 0 1; sv 1].
Proof. intros Hg. apply bcs_hold_self; [done|vb_list|exact rel_sub]. Qed.

Definition relay_body : ty :=
  TLolli (Some (pv 1 0)) None (TProd (TSess Srl (pv 0 0)) (TSess SEnd (pv 1 0))) TUnit.
Definition prod_body : ty :=
  TLolli (Some (pv 1 0)) None (TProd (TSess (dual Srl) (pv 0 0)) (TSess SEnd (pv 1 0))) TUnit.

Definition relay : expr :=
  EBox (Lam (LetP (Var 0) (LetP (App ERecv (Var 1)) (LetP (App ERecv (Var 1)) (LetU (Var 1)
    (LetU (App EClos (Var 4))
      (App ESpawn (Lam (LetU (Var 0) (App (App EForce (Var 8)) (Pair (Var 3) (Var 1)))))))))))).

Definition prod : expr :=
  EBox (Lam (LetP (Var 0) (LetP (App ENew EUnit)
    (LetP (Pair (App ESend (Pair (Var 1) (Var 3))) EUnit) (LetU (Var 0)
      (LetP (Pair (App ESend (Pair EUnit (Var 2))) EUnit) (LetU (Var 0)
        (LetU (App EClos (Var 6))
          (App ESpawn (Lam (LetU (Var 0) (App (App EForce (Var 10)) (Pair (Var 4) (Var 2)))))))))))))).

Definition rel_main : expr :=
  LetP (Pair relay prod) (LetP (App ENew EUnit) (LetP (App ENew EUnit)
    (LetU (App ESpawn (Lam (LetU (Var 0) (App (App EForce (Var 6)) (Pair (Var 4) (Var 2))))))
      (App (App EForce (Var 4)) (Pair (Var 2) (Var 0)))))).

Lemma relay_typed W F : world_wf W → typed W ∅ [] ∅ [] F relay (TBox 2 rel_C (TLolli None None TUnit relay_body)).
Proof.
  intros HW. unfold relay.
  apply (t_box W _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|].
  box_open rel_C relay_body. cbn. unfold relay_body.
  eapply (tv_lam W HW _ _ _ _ _ _ _ _ None 1); [set_solver|cbn; set_solver|].
  cbn. tstep; [tstep|]. cbn. tstep.
  { eapply (tv_appk W HW _ _ _ _ KRecv _ (Some (pv 0 0))
              (TSess (SRcv 1 (TSess Dr (Pt (NVar 0) 0)) Srl) (pv 0 0))).
    - eapply t_conv; [|tstep]. conv_sess.
    - apply KTRecv.
    - kscope.
    - apply ubs_intro; [intros y Hy; mem_cases Hy; hyp0 (pv 0 0) (pv 1 0)|].
      exists (pv 1 0). split; [done|]. right. hyp0 (pv 0 0) (pv 1 0). }
  cbn. tstep.
  { tstep; [tstep|apply KTRecv|kscope|].
    apply ubs_intro; [intros y Hy; mem_cases Hy; first [hyp0 (sv 0) (pv 0 1)|hyp0 (sv 0) (pv 1 0)]|].
    exists (pv 1 0). split; [done|]. right. hyp0 (sv 0) (pv 1 0). }
  cbn. tstep; [tstep|]. cbn. tstep.
  { tstep; [tstep|apply KTClos|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy; first [hyp0 (pv 1 0) (pv 0 1)|hyp0 (pv 1 0) (sv 1)]|].
    exists (pv 1 0). split; [done|]. apply sle_refl, HW. }
  tstep; [|apply KTSpawn|done|apply ubs_none].
  eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (sv 1)) (Some (sv 0)) 2); [set_solver| |].
  { intros y Hy. mem_cases Hy;
      first [right; hyp0 (sv 0) (pv 0 1)|right; apply (slt_po W _ (sv 0) HW)]. }
  cbn. tstep; [tstep|]. cbn.
  eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force W _ _ _ _ _ _ 2 rel_C None relay_body [pv 0 1; sv 1]);
      [done|done| | |apply ubs_none|tstep].
    + apply rel_call. by left.
    + apply Forall_cons. split; [|apply Forall_singleton];
        apply (skn_in W _ rel_C [pvar 0; pvar 1] (pvar 0)); [by left|by left|done|by left|by left|done].
  - tstep; tstep.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (sv 1). split; [done|]. apply sle_refl, HW.
Qed.

Lemma prod_typed W F : world_wf W → typed W ∅ [] ∅ [] F prod (TBox 2 rel_C (TLolli None None TUnit prod_body)).
Proof.
  intros HW. unfold prod.
  apply (t_box W _ _ _ _ _ _ _ _ _ 0); [by intros o Ho; apply elem_of_nil in Ho|set_solver|].
  box_open rel_C prod_body. cbn. unfold prod_body.
  eapply (tv_lam W HW _ _ _ _ _ _ _ _ None 1); [set_solver|cbn; set_solver|].
  cbn. tstep; [tstep|]. cbn. tstep.
  { tstep; [tstep| |done|apply ubs_none]. apply (KTNew _ _ _ Dr (sv 0)). skn_slot. }
  cbn. tstep.
  { tstep; [tstep|].
    eapply (tv_appk W HW _ _ _ _ KSend _ (Some (pv 0 0))
              (TProd (TSess Dr (sv 0)) (TSess (SSnd 1 (TSess Dr (Pt (NVar 0) 0)) (dual Srl)) (pv 0 0)))).
    - tstep; [|tstep]. eapply t_conv; [|tstep]. conv_sess.
    - apply (KTSend _ _ _ 1 (TSess Dr (Pt (NVar 0) 0)) (dual Srl) (pv 0 0)).
      intros h Hh. cbn in Hh. apply elem_of_singleton in Hh as ->. hyp0 (pv 0 0) (sv 0).
    - kscope.
    - apply ubs_intro; [intros y Hy; mem_cases Hy; first [hyp0 (pv 0 0) (sv 0)|hyp0 (pv 0 0) (pv 1 0)]|].
      exists (pv 1 0). split; [done|]. right. hyp0 (pv 0 0) (pv 1 0). }
  cbn. tstep; [tstep|]. cbn. tstep.
  { tstep; [tstep|].
    eapply (tv_appk W HW _ _ _ _ KSend _ (Some (sv 0)) (TProd TUnit (TSess (SSnd 0 TUnit SEnd) (sv 0)))).
    - tstep; tstep.
    - apply (KTSend _ _ _ 0 TUnit SEnd (sv 0)). cbn. set_solver.
    - kscope.
    - apply ubs_intro; [intros y Hy; mem_cases Hy; first [hyp0 (sv 0) (pv 0 1)|hyp0 (sv 0) (pv 1 0)]|].
      exists (pv 1 0). split; [done|]. right. hyp0 (sv 0) (pv 1 0). }
  cbn. tstep; [tstep|]. cbn. tstep.
  { tstep; [tstep|apply KTClos|done|].
    apply ubs_intro; [intros y Hy; mem_cases Hy; first [hyp0 (pv 1 0) (pv 0 1)|hyp0 (pv 1 0) (sv 1)]|].
    exists (pv 1 0). split; [done|]. apply sle_refl, HW. }
  tstep; [|apply KTSpawn|done|apply ubs_none].
  eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (sv 1)) (Some (sv 0)) 2); [set_solver| |].
  { intros y Hy. mem_cases Hy;
      first [right; hyp0 (sv 0) (pv 0 1)|right; apply (slt_po W _ (sv 0) HW)]. }
  cbn. tstep; [tstep|]. cbn.
  eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force W _ _ _ _ _ _ 2 rel_C None prod_body [pv 0 1; sv 1]);
      [done|done| | |apply ubs_none|tstep].
    + apply rel_call. by left.
    + apply Forall_cons. split; [|apply Forall_singleton];
        apply (skn_in W _ rel_C [pvar 0; pvar 1] (pvar 0)); [by left|by left|done|by left|by left|done].
  - tstep; tstep.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|].
    exists (sv 1). split; [done|]. apply sle_refl, HW.
Qed.

(** Round k of C at ((a,0), (b,0)). *)
Definition rel_sl (k : nat) : point := Pt (NSlot (NConst 0) k 0) 0.
Definition rel_ip (k : nat) : point :=
  match k with 0 => pc 1 0 | S j => Pt (NSlot (NConst 0) j 0) 1 end.

Lemma rel_hold_W W :
  (∀ k, w_lt W (pc 0 k) (rel_ip k) ∧ w_lt W (pc 0 k) (rel_sl k) ∧
        w_lt W (rel_sl k) (pt_shift 1 (pc 0 k)) ∧ w_lt W (rel_sl k) (rel_ip k) ∧
        w_lt W (rel_ip k) (pt_shift 1 (pc 0 k)) ∧ w_lt W (rel_ip k) (pt_shift 1 (rel_sl k))) →
  bcs_hold (w_eq W) (w_lt W) rel_C [pc 0 0; pc 1 0].
Proof.
  intros H.
  assert (∀ k g, c0 (pc 0 k) (rel_ip k) g → fact_holds (w_eq W) (w_lt W) g) as Hc.
  { intros k g Hg. destruct (H k) as (A1 & A2 & A3 & A4 & A5 & A6).
    unfold c0 in Hg. repeat destruct Hg as [->|Hg]; subst; cbn;
      first [exact A1|exact A2|exact A3|exact A4|exact A5|exact A6]. }
  apply bcs_hold_intro. intros g [Hg|(k & Hg)] _.
  - apply (Hc 0). exact (c0_inst _ _ _ _ Hg).
  - apply (Hc (S k)). exact (c0_inst _ _ _ _ Hg).
Qed.

Definition rel_L_facts (x y : point) : Prop :=
  ∃ k, (x = pc 0 k ∧ y = rel_ip k) ∨ (x = pc 0 k ∧ y = rel_sl k) ∨
       (x = rel_sl k ∧ y = pt_shift 1 (pc 0 k)) ∨ (x = rel_sl k ∧ y = rel_ip k) ∨
       (x = rel_ip k ∧ y = pt_shift 1 (pc 0 k)) ∨ (x = rel_ip k ∧ y = pt_shift 1 (rel_sl k)).

Definition Wrel : world := wgen (list_to_set (NConst <$> [0; 1])) (λ _ _, False) rel_L_facts.

Definition rel_base (p : pname) : nat :=
  match p with NConst 0 => 3 | NConst 1 => 5 | NSlot (NConst 0) k 0 => 3 * k + 4 | _ => 0 end.
Definition rel_step (p : pname) : nat :=
  match p with NConst 0 => 3 | NConst 1 => 10 | NSlot (NConst 0) _ 0 => 4 | _ => 1 end.
Definition rel_rank (x : point) : nat := rel_base (pt_name x) + rel_step (pt_name x) * pt_off x.

Lemma Wrel_strict : strict Wrel.
Proof.
  apply (wgen_strict _ _ _ id rel_rank); try done.
  - intros p Hp. apply elem_of_list_to_set, list_elem_of_fmap in Hp as (a & -> & _). by exists a.
  - intros x y (k & H); right; rewrite !elem_of_list_to_set;
      repeat destruct H as [[-> ->]|H]; try destruct H as [-> ->];
      destruct k; cbn; set_solver.
  - intros x. unfold rel_rank, pt_shift. cbn.
    assert (0 < rel_step (pt_name x)) by (unfold rel_step; repeat case_match; lia). nia.
  - intros x y (k & H); unfold id;
      repeat destruct H as [[-> ->]|H]; try destruct H as [-> ->];
      destruct k; unfold rel_rank; cbn; lia.
Qed.

Lemma rel_typed W : world_wf W → pt_known W (pc 0 0) → pt_known W (pc 1 0) →
  (∀ k, w_lt W (pc 0 k) (rel_ip k) ∧ w_lt W (pc 0 k) (rel_sl k) ∧
        w_lt W (rel_sl k) (pt_shift 1 (pc 0 k)) ∧ w_lt W (rel_sl k) (rel_ip k) ∧
        w_lt W (rel_ip k) (pt_shift 1 (pc 0 k)) ∧ w_lt W (rel_ip k) (pt_shift 1 (rel_sl k))) →
  typed W ∅ [] ∅ [] (∅, None) rel_main TUnit.
Proof.
  intros HW Ha Hb H. unfold rel_main.
  assert (bcs_hold (seqs W []) (slt W []) rel_C [pc 0 0; pc 1 0]) as HC.
  { eapply bcs_hold_mono; [intros ? ? ?; by apply se_w|intros ? ? ?; by apply sl_w|by apply rel_hold_W]. }
  assert (Forall (skn W []) [pc 0 0; pc 1 0]) as HK.
  { constructor; [by left|constructor; [by left|constructor]]. }
  assert (w_lt W (pc 0 0) (pc 1 0)) as H0 by apply (H 0).
  tstep.
  { tstep; [apply prod_typed, HW|apply relay_typed, HW]. }
  cbn. tstep.
  { tstep; [tstep|apply (KTNew _ _ _ Srl (pc 0 0) (or_introl Ha))|done|apply ubs_none]. }
  cbn. tstep.
  { tstep; [tstep|apply (KTNew _ _ _ SEnd (pc 1 0) (or_introl Hb))|done|apply ubs_none]. }
  cbn. tstep.
  { tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pc 1 0)) (Some (pc 0 0)) 0); [set_solver| |].
    { intros y Hy. mem_cases Hy; first [apply sle_refl, HW|right; by apply sl_w]. }
    cbn. tstep; [tstep|]. cbn.
    eapply tv_app; [exact HW|reflexivity| | |].
    - apply (typed_force W _ _ _ _ _ _ 2 rel_C None relay_body [pc 0 0; pc 1 0]);
        [done|done|exact HC|exact HK|apply ubs_none|tstep].
    - tstep; tstep.
    - apply ubs_intro; [intros y Hy; mem_cases Hy|].
      exists (pc 1 0). split; [done|]. apply sle_refl, HW. }
  cbn. eapply tv_app; [exact HW|reflexivity| | |].
  - apply (typed_force W _ _ _ _ _ _ 2 rel_C None prod_body [pc 0 0; pc 1 0]);
      [done|done|exact HC|exact HK|apply ubs_none|tstep].
  - tstep; tstep.
  - apply ubs_intro; [intros y Hy; mem_cases Hy|done].
Qed.

Lemma rel_deadlock_free : deadlock_free (∅, {[+ rel_main +]}).
Proof.
  apply (soundness Wrel _ TUnit Wrel_strict).
  apply ptyped_closed; [constructor|]. apply rel_typed; [apply Wrel_strict| | |].
  - unfold pt_known, Wrel. simpl. set_solver.
  - unfold pt_known, Wrel. simpl. set_solver.
  - intros k. split_and!; apply glt_base; exists k; naive_solver.
Qed.
