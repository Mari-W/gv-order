(** * End points: the bit program (docs/extensions/end-points.md)

      bit = let (e, e′) = new ε in let (c, c′) = new γ in let (d, d′) = new δ in
            spawn (λ_. close (send ⟨inj₁ ∗, e′⟩));
            spawn (λ_. close c′); spawn (λ_. close d′);
            let (v, e) = recv e in let () = close e in
            case v { inj₁ u ⇒ u; close c; close d
                   | inj₂ u ⇒ u; close d; close c }

    The main thread holds c at γ and d at δ, their partners sit at γ̄ and
    δ̄. Branch inj₁ closes c while it holds d and owes γ ≺ δ̄. Branch inj₂
    closes d while it holds c and owes δ ≺ γ̄. The receive and the close
    of e owe ε ≺ γ̄, ε ≺ δ̄ and ε+1 ≺ γ̄, ε+1 ≺ δ̄. The top-level
    constraint

      C₀ = {ε+1 ≺ γ̄, ε+1 ≺ δ̄, γ ≺ δ̄, δ ≺ γ̄}

    is acyclic ([bit_C0_acyclic]), so [bit_typed] and [soundness_source]
    give [bit_deadlock_free]. With one point per channel the two branch
    facts read γ ≺ δ and δ ≺ γ, a cycle: the collapsed system rejects
    the program ([bit_collapsed_cyclic]). *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.LitTools.

Set Default Proof Using "All".

(** ** The program *)

(** The session of the receiving end of e: ?(∗ + ∗).Close. *)
Definition Sbit : sty := SSeq (SRcv 0 (TSum TUnit TUnit)) SEnd.

(** After the three news: d′ 0, d 1, c′ 2, c 3, e′ 4, e 5. *)
Definition bit_sender : expr := Lam (LetU (Var 0) (App EClos (App ESend (Pair (Inj1 EUnit) (Var 5))))).
Definition bit_closer (k : nat) : expr := Lam (LetU (Var 0) (App EClos (Var k))).

(** After recv: e 0, v 1, d 3, c 5. In a branch: u 0, d 4, c 6. *)
Definition bit_arm1 : expr := LetU (Var 0) (LetU (App EClos (Var 6)) (App EClos (Var 4))).
Definition bit_arm2 : expr := LetU (Var 0) (LetU (App EClos (Var 4)) (App EClos (Var 6))).

Definition bit_main : expr :=
  let_new_pair (let_new_pair (let_new_pair
    (LetU (App ESpawn bit_sender)
      (LetU (App ESpawn (bit_closer 3))
        (LetU (App ESpawn (bit_closer 1))
          (LetP (App ERecv (Var 5))
            (LetU (App EClos (Var 0)) (Case (Var 1) bit_arm1 bit_arm2)))))))).

(** ** The top-level constraint, over ε = 0, γ = 1, δ = 2 *)

Definition bit_P (g : fact) : Prop :=
  g = FLt (pv 0 1) (pt_dual (pv 1 0)) ∨ g = FLt (pv 0 1) (pt_dual (pv 2 0)) ∨
  g = FLt (pv 1 0) (pt_dual (pv 2 0)) ∨ g = FLt (pv 2 0) (pt_dual (pv 1 0)).
Definition bit_C0 : bcs := BCs [] bit_P.

(** Acyclicity by a rank that reads the polarity: three per step, five
    for γ and δ, one more for a negative end. It rises along x ≺ x+1,
    along x ≺ x̄+1 and along the four facts. *)
Definition bit_rank (x : point) : nat :=
  3 * pt_off x + (match pt_name x with NVar 1 | NVar 2 => 5 | _ => 0 end) +
  (if pt_pol x then 0 else 1).

Lemma c0_acyclic_prank n P (r : point → nat) :
  (∀ x, r x < r (pt_shift 1 x)) → (∀ x, r x < r (pt_shift 1 (pt_dual x))) →
  (∀ x y, ¬ P (FEq x y)) → (∀ x y, P (FLt x y) → r x < r y) →
  c0_acyclic n (BCs [] P).
Proof.
  intros Hs Hd HE HL. split; [done|].
  assert (∀ x y, geq (c0_eq n (BCs [] P)) x y → x = y) as Heq.
  { induction 1 as [x y H| | | | | |]; try congruence.
    apply bcs_open_nil in H as [H _]. by destruct (HE x y). }
  assert (∀ x y, glt (c0_eq n (BCs [] P)) (c0_lt n (BCs [] P)) x y → r x < r y) as Hlt.
  { induction 1 as [x y H|x|x x' y y' Hx _ IH Hy|x y z _ IH1 _ IH2|x].
    - apply bcs_open_nil in H as [H _]. by apply HL.
    - apply Hs.
    - apply Heq in Hx, Hy. by subst.
    - lia.
    - apply Hd. }
  intros p H. specialize (Hlt _ _ H). lia.
Qed.

Lemma bit_C0_acyclic : c0_acyclic 3 bit_C0.
Proof.
  apply (c0_acyclic_prank 3 bit_P bit_rank).
  - intros [p [] o]; unfold bit_rank, pt_shift; simpl; lia.
  - intros [p [] o]; unfold bit_rank, pt_shift, pt_dual; simpl; lia.
  - intros x y [?|[?|[?|?]]]; discriminate.
  - intros x y [E|[E|[E|E]]]; injection E as -> ->; vm_compute; lia.
Qed.

(** ** The derivation *)

Section facts.
  Context (W : world) (HW : world_wf W).
  Local Notation Ψ := [(bit_C0, ids 3)].

  Lemma bit_hyp x y : bit_P (FLt x y) → fact_scoped 3 (FLt x y) → slt W Ψ x y.
  Proof.
    intros H Hs. eapply (sl_hyp0 _ _ bit_P (ids 3) x y); [by apply list_elem_of_singleton|done|done| |].
    all: by apply pt_inst_ids; destruct Hs.
  Qed.

  Lemma bit_known a : a < 3 → skn W Ψ (pv a 0).
  Proof.
    intros Ha. apply (skn_inst _ _ bit_C0 (ids 3) (pv a 0)); [by apply list_elem_of_singleton| |done].
    unfold ids. apply list_elem_of_fmap. exists a. split; [done|]. apply elem_of_seq. lia.
  Qed.
End facts.

Lemma bit_typed : styped ∅ [(bit_C0, ids 3)] [] (∅, None) bit_main TUnit.
Proof.
  apply styped_wnil. pose proof wnil_strict as HWs.
  pose proof (proj1 HWs) as HW. set (W := wnil) in *. unfold bit_main.
  assert (slt W [(bit_C0, ids 3)] (pv 0 1) (pt_dual (pv 1 0))) as H1
    by (apply (bit_hyp W HW); [by left|cbn; lia]).
  assert (slt W [(bit_C0, ids 3)] (pv 0 1) (pt_dual (pv 2 0))) as H2
    by (apply (bit_hyp W HW); [by right; left|cbn; lia]).
  assert (slt W [(bit_C0, ids 3)] (pv 1 0) (pt_dual (pv 2 0))) as H3
    by (apply (bit_hyp W HW); [by right; right; left|cbn; lia]).
  assert (slt W [(bit_C0, ids 3)] (pv 2 0) (pt_dual (pv 1 0))) as H4
    by (apply (bit_hyp W HW); [by right; right; right|cbn; lia]).
  assert (slt W [(bit_C0, ids 3)] (pv 0 0) (pt_dual (pv 1 0))) as H5
    by (eapply sl_trans; [apply (slt_po W _ (pv 0 0) HW)|exact H1]).
  assert (slt W [(bit_C0, ids 3)] (pv 0 0) (pt_dual (pv 2 0))) as H6
    by (eapply sl_trans; [apply (slt_po W _ (pv 0 0) HW)|exact H2]).
  apply (t_new_at W _ _ _ _ _ _ _ Sbit (pv 0 0) HWs); [apply (bit_known W HW); lia|].
  apply (t_new_at W _ _ _ _ _ _ _ SEnd (pv 1 0) HWs); [apply (bit_known W HW); lia|].
  apply (t_new_at W _ _ _ _ _ _ _ SEnd (pv 2 0) HWs); [apply (bit_known W HW); lia|].
  cbn.
  (* spawn the sender of the bit, which holds e′ at ε̄ *)
  tstep.
  { tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pt_dual (pv 0 1))) (Some (pv 0 0)) 0);
      [set_solver|intros y Hy; mem_cases Hy; apply sle_refl, HW|].
    cbn. tstep; [tstep|]. cbn.
    tstep; [|apply KTClos|done|apply ubs_intro; [intros y Hy; mem_cases Hy|]].
    - tstep; [|apply (KTSend _ _ _ 0 (TSum TUnit TUnit) SEnd (pt_dual (pv 0 0))); cbn; set_solver|kscope|].
      + tstep; [tstep|apply t_inj1; tstep].
      + apply ubs_intro; [intros y Hy; mem_cases Hy|].
        exists (pt_dual (pv 0 1)). split; [done|]. right. apply (slt_po W _ (pt_dual (pv 0 0)) HW).
    - exists (pt_dual (pv 0 1)). split; [done|]. apply sle_refl, HW. }
  cbn. tstep.
  { tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pt_dual (pv 1 0))) (Some (pv 1 0)) 0);
      [set_solver|intros y Hy; mem_cases Hy; apply sle_refl, HW|].
    cbn. tstep; [tstep|]. cbn.
    tstep; [tstep|apply KTClos|done|apply ubs_intro; [intros y Hy; mem_cases Hy|]].
    exists (pt_dual (pv 1 0)). split; [done|]. apply sle_refl, HW. }
  cbn. tstep.
  { tstep; [|apply KTSpawn|done|apply ubs_none].
    eapply (tv_lam W HW _ _ _ _ _ TUnit TUnit (Some (pt_dual (pv 2 0))) (Some (pv 2 0)) 0);
      [set_solver|intros y Hy; mem_cases Hy; apply sle_refl, HW|].
    cbn. tstep; [tstep|]. cbn.
    tstep; [tstep|apply KTClos|done|apply ubs_intro; [intros y Hy; mem_cases Hy|]].
    exists (pt_dual (pv 2 0)). split; [done|]. apply sle_refl, HW. }
  (* the main thread: receive the bit, close e, close c and d in the order it picks *)
  cbn. tstep.
  { tstep; [tstep|apply KTRecv|kscope|].
    apply ubs_intro; [|done]. intros y Hy. mem_cases Hy; done. }
  cbn. tstep.
  { tstep; [tstep|apply KTClos|done|].
    apply ubs_intro; [|done]. intros y Hy. mem_cases Hy; done. }
  cbn. eapply tv_case; [exact HW|reflexivity|tstep| |].
  - cbn. tstep; [tstep|]. cbn. tstep.
    + tstep; [tstep|apply KTClos|done|].
      apply ubs_intro; [|done]. intros y Hy. mem_cases Hy; done.
    + tstep; [tstep|apply KTClos|done|]. apply ubs_intro; [intros y Hy; mem_cases Hy|done].
  - cbn. tstep; [tstep|]. cbn. tstep.
    + tstep; [tstep|apply KTClos|done|].
      apply ubs_intro; [|done]. intros y Hy. mem_cases Hy; done.
    + tstep; [tstep|apply KTClos|done|]. apply ubs_intro; [intros y Hy; mem_cases Hy|done].
Qed.

Theorem bit_deadlock_free : deadlock_free (∅, {[+ bit_main +]}).
Proof.
  apply (soundness_source 3 bit_C0 _ TUnit (c0_acyclic_creation _ _ bit_C0_acyclic));
    [constructor|apply bit_typed].
Qed.

(** ** The collapsed reading

    With one point per channel (x̄ read as x) the facts of the two branches
    are γ ≺ δ and δ ≺ γ, so no strict order contains them. *)
Definition collapse (x : point) : point := MkPt (pt_name x) true (pt_off x).

Lemma bit_collapsed_cyclic (lt : point → point → Prop) :
  (∀ x y z, lt x y → lt y z → lt x z) → (∀ x, ¬ lt x x) →
  ¬ (lt (collapse (pv 1 0)) (collapse (pt_dual (pv 2 0))) ∧
     lt (collapse (pv 2 0)) (collapse (pt_dual (pv 1 0)))).
Proof. intros Ht Hi [Ha Hb]. apply (Hi (pv 1 0)). exact (Ht _ _ _ Ha Hb). Qed.
