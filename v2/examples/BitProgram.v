(** * The bit program (fx-final, 2026-11-24)

      bit = let ⟨e, e′⟩ = new in                       e at ε, e′ at ε̄
            let ⟨c, c′⟩ = new in                       at the field ε·0
            let ⟨d, d′⟩ = new in                       at the field ε·1
            let ∗ = spawn (λ_. close (send ⟨inj₁ ∗, e′⟩)) in
            let ∗ = spawn (λ_. close c′) in let ∗ = spawn (λ_. close d′) in
            let ⟨v, e⟩ = recv e in let ∗ = close e in
            case v of inj₁ u ⇒ let ∗ = u in let ∗ = close c in close d
                    | inj₂ u ⇒ let ∗ = u in let ∗ = close d in close c

    The port of the program of theories/examples/EndPoints.v on old-main.
    The main thread holds c at ε·0 and d at ε·1, the dual ends sit at
    (ε·0)‾ and (ε·1)‾. E-Case types both arms in one world. Arm inj₁
    closes c while it holds d and asks ε·0 ≺ (ε·1)‾, arm inj₂ closes d
    while it holds c and asks ε·1 ≺ (ε·0)‾. The receive and the close of
    e ask ε ≺ (ε·0)‾, ε ≺ (ε·1)‾ and the same at ε⁺. The creation of e
    states these six facts as its constraint, which satisfies (wf-new)
    by a rank that reads the offset, the depth and the polarity
    ([bit_wf_new]). With one point per channel the two arms would ask
    ε·0 ≺ ε·1 and ε·1 ≺ ε·0, a cycle. The dual points keep them apart.

    - [bit_dftyped]      : the program types at N = ∞ over the empty world.
    - [bit_deadlock_free]: the closed program is deadlock free. *)

From GV Require Export examples.GenNew.

(** ** The program *)

(** The session of the receiving end of e, ?(∗ ⊕ ∗).Close. *)
Definition Sbit : sty := SSeq (SRcv 0 (TSum TUnit TUnit)) SEnd.

(** After the three creations: d′ 0, d 1, c′ 2, c 3, e′ 4, e 5. *)
Definition bit_sender : expr := Lam (LetU (Var 0) (EClose (ESend (Pair (Inj false EUnit) (Var 5))))).
Definition bit_closer (k : nat) : expr := Lam (LetU (Var 0) (EClose (Var k))).

(** In an arm: u 0, d 4, c 6. *)
Definition bit_arm1 : expr := LetU (Var 0) (LetU (EClose (Var 6)) (EClose (Var 4))).
Definition bit_arm2 : expr := LetU (Var 0) (LetU (EClose (Var 4)) (EClose (Var 6))).

Definition bit_main : expr :=
  let_new (LetP ENew (LetP ENew
    (LetU (ESpawn bit_sender)
      (LetU (ESpawn (bit_closer 3))
        (LetU (ESpawn (bit_closer 1))
          (LetP (ERecv (Var 5))
            (LetU (EClose (Var 0)) (Case (Var 1) bit_arm1 bit_arm2)))))))).

(** ** The constraint of e, over ε = ι₀ *)

Definition bit_L (g : fact) : Prop :=
  g = FLt ρ0 (ρ0·0)‾ ∨ g = FLt ρ0 (ρ0·1)‾ ∨ g = FLt ρ0⁺ (ρ0·0)‾ ∨ g = FLt ρ0⁺ (ρ0·1)‾ ∨
  g = FLt (ρ0·0) (ρ0·1)‾ ∨ g = FLt (ρ0·1) (ρ0·0)‾.

(** The rank: three per offset, five per field, one more for a negative
    point. It rises along x ≺ x⁺, along x ≺ x̄⁺ and along the six facts. *)
Definition bit_rank (x : point) : nat * nat * nat :=
  (3 * pt_off x + 5 * pt_depth x + (if pt_pol x then 0 else 1), 0, 0).

Lemma bit_wf_new : wf_new (bcs_of bit_L).
Proof.
  apply (wf_new_lex3 _ bit_rank).
  - intros x y [E|[E|[E|[E|[E|E]]]]]; injection E as -> ->; split; reflexivity.
  - intros [p [] o]; unfold bit_rank, pt_shift, pt_dual, pt_depth, lex3; simpl; lia.
  - intros x y [E|[E|[E|[E|[E|E]]]]]; injection E as -> ->; vm_compute; lia.
Qed.
#[global] Hint Resolve bit_wf_new : wfnew.

Ltac bit_fact := apply law_slt'; [unfold bit_L; disj_tac|cbn; lia].

(** ** The derivation *)

Theorem bit_dftyped : dftyped sw_empty ∅ hc_empty [] (∅, None) bit_main TUnit.
Proof.
  unfold bit_main, let_new.
  eapply d_let; [apply tsplit_empty|apply lsplit_nil| |].
  { eapply (d_new' _ _ _ _ bit_L Sbit None None); [spare_tac|apply bit_wf_new|contr_tac]. }
  eapply d_open with (i := 0); [reflexivity|cbn; tauto|cons_tac|].
  rewrite tenv_pinst_empty, sf_pinst_empty. cbn [lenv_pinst fmap list_fmap insert list_insert].
  fold (Γnew bit_L).
  eapply d_letp; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
  { eapply d_var'; [reflexivity|]. spare_tac. }
  eapply d_letp; [apply tsplit_empty|lsplit_tac ENew EUnit| |].
  { apply (d_new_fld _ _ _ _ ρ0 0 SEnd None None None None); [apply spare_unl; spare_tac|contr_tac]. }
  eapply d_letp; [apply tsplit_empty|lsplit_tac ENew EUnit| |].
  { apply (d_new_fld _ _ _ _ ρ0 1 SEnd None None None None); [apply spare_unl; spare_tac|contr_tac]. }
  (* the sender *)
  eapply d_letu; [apply tsplit_empty|lsplit_tac (ESpawn bit_sender) EUnit| |].
  { apply d_spawn_lam.
    eapply d_letu; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
    { eapply d_var'; [reflexivity|]. spare_tac. }
    eapply d_close with (S0 := SEnd) (x := ρ0‾⁺); [done|apply ub_below_empty|].
    eapply d_send with (x := ρ0‾) (m := 0) (T := TSum TUnit TUnit) (S0 := dual Sbit);
      [done|cbn; tauto|done|cbn; set_solver|apply ub_below_empty|].
    eapply d_pair; [apply tsplit_empty|lsplit_tac (Inj false EUnit) (Var 5)| |].
    - apply d_inj; [contr_tac|]. apply d_unit'. spare_tac.
    - eapply d_var'; [reflexivity|]. spare_tac. }
  (* the two closers *)
  eapply d_letu; [apply tsplit_empty|lsplit_tac (ESpawn (bit_closer 3)) EUnit| |].
  { apply d_spawn_lam.
    eapply d_letu; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
    { eapply d_var'; [reflexivity|]. spare_tac. }
    eapply d_close with (S0 := SEnd) (x := (ρ0·0)‾); [done|apply ub_below_empty|].
    eapply d_var'; [reflexivity|]. spare_tac. }
  eapply d_letu; [apply tsplit_empty|lsplit_tac (ESpawn (bit_closer 1)) EUnit| |].
  { apply d_spawn_lam.
    eapply d_letu; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
    { eapply d_var'; [reflexivity|]. spare_tac. }
    eapply d_close with (S0 := SEnd) (x := (ρ0·1)‾); [done|apply ub_below_empty|].
    eapply d_var'; [reflexivity|]. spare_tac. }
  (* the receive *)
  eapply d_letp; [apply tsplit_empty|lsplit_tac (ERecv (Var 5)) EUnit| |].
  { eapply d_recv with (x := ρ0) (m := 0) (T := TSum TUnit TUnit) (S0 := Sbit);
      [done|cbn; tauto| |eapply d_var'; [reflexivity|spare_tac]].
    apply ub_below_nil; [bot_false|]. intros y Hy. heads_cases Hy; bit_fact. }
  eapply d_letu; [apply tsplit_empty|lsplit_tac (EClose (Var 0)) EUnit| |].
  { eapply d_close with (S0 := SEnd) (x := ρ0⁺); [done| |eapply d_var'; [reflexivity|spare_tac]].
    apply ub_below_nil; [bot_false|]. intros y Hy. heads_cases Hy; bit_fact. }
  (* the case on the received bit *)
  eapply d_case; [apply tsplit_empty|lsplit_tac (Var 1) EUnit| | |].
  { eapply d_var'; [reflexivity|]. spare_tac. }
  - unfold bit_arm1.
    eapply d_letu; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
    { eapply d_var'; [reflexivity|]. spare_tac. }
    eapply d_letu; [apply tsplit_empty|lsplit_tac (EClose (Var 6)) EUnit| |].
    { eapply d_close with (S0 := SEnd) (x := ρ0·0); [done| |eapply d_var'; [reflexivity|spare_tac]].
      apply ub_below_nil; [bot_false|]. intros y Hy. heads_cases Hy; bit_fact. }
    eapply d_close with (S0 := SEnd) (x := ρ0·1); [done|apply ub_below_empty|].
    eapply d_var'; [reflexivity|]. spare_tac.
  - unfold bit_arm2.
    eapply d_letu; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
    { eapply d_var'; [reflexivity|]. spare_tac. }
    eapply d_letu; [apply tsplit_empty|lsplit_tac (EClose (Var 4)) EUnit| |].
    { eapply d_close with (S0 := SEnd) (x := ρ0·1); [done| |eapply d_var'; [reflexivity|spare_tac]].
      apply ub_below_nil; [bot_false|]. intros y Hy. heads_cases Hy; bit_fact. }
    eapply d_close with (S0 := SEnd) (x := ρ0·0); [done|apply ub_below_empty|].
    eapply d_var'; [reflexivity|]. spare_tac.
  Unshelve. all: exact None.
Qed.

Theorem bit_deadlock_free : deadlock_free (∅, {[+ bit_main +]}).
Proof.
  apply (soundness_source sw_empty bit_main TUnit); [apply sw_empty_acyc|apply sw_empty_acyc|constructor|].
  exact bit_dftyped.
Qed.

Print Assumptions bit_dftyped.
Print Assumptions bit_deadlock_free.
