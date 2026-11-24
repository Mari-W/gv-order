(** * Milner's cyclic scheduler (fx-final, 2026-11-24)

    The port of theories/examples/MilnerSched.v on old-main, Example 1
    of Dardha and Gay with k = 3 agents. Agent A_i sits on a ring and
    reports to its collector P_i.

      A_0 = let ∗ = sendclose c_0 in let ∗ = recvclose d_0 in sendclose a_0   (main)
      A_i = let ∗ = recvclose d_i in let ∗ = sendclose a_i in sendclose c_i   (spawned)
      P_i = recvclose b_i                                                     (spawned)
      sendclose r = close (send ⟨∗, r⟩)
      recvclose r = let ⟨x, r⟩ = recv r in let ∗ = x in close r

    The ring closes because c_i and d_{(i+1) mod 3} are the two ends of
    one channel. The six channels sit at the root ρ of the first
    creation and at its fields, the sending end at the point, the
    receiving end at its dual.

      c_0, d_1 : ρ      a_1, b_1 : ρ·1    c_1, d_2 : ρ·2
      a_2, b_2 : ρ·3    c_2, d_0 : ρ·4    a_0, b_0 : ρ·5

    Each agent acts on an end while it holds the ends it uses later. A_1
    asks ρ̄ ≺ (ρ·1)‾, ρ̄ ≺ (ρ·2)‾ and ρ·1 ≺ (ρ·2)‾, A_2 asks
    (ρ·2)‾ ≺ (ρ·3)‾, (ρ·2)‾ ≺ (ρ·4)‾ and ρ·3 ≺ (ρ·4)‾, and A_0 asks
    ρ ≺ ρ·4, ρ ≺ (ρ·5)‾ and (ρ·4)‾ ≺ (ρ·5)‾, each also at the shift of
    its lower point for the close. The first creation states these 18
    facts. They rise with the field label, so a rank that reads the
    label first satisfies (wf-new) ([ms_wf_new]). This is the order of
    the priorities of Dardha and Gay for the scheduler.

    - [ms_dftyped]      : the program types at N = ∞ over the empty world.
    - [ms_deadlock_free]: the closed program is deadlock free. *)

From GV Require Export examples.GenNew.

(** ** The program *)

Definition sendclose (r : expr) : expr := EClose (ESend (Pair EUnit r)).
Definition recvclose (r : expr) : expr := LetP (ERecv r) (LetU (Var 1) (EClose (Var 0))).

(** After the six creations: b₀ 0, a₀ 1, d₀ 2, c₂ 3, b₂ 4, a₂ 5, d₂ 6,
    c₁ 7, b₁ 8, a₁ 9, d₁ 10, c₀ 11. A thunk shifts them by one. *)
Definition ms_ag1 : expr :=
  Lam (LetU (Var 0) (LetU (recvclose (Var 11)) (LetU (sendclose (Var 10)) (sendclose (Var 8))))).
Definition ms_ag2 : expr :=
  Lam (LetU (Var 0) (LetU (recvclose (Var 7)) (LetU (sendclose (Var 6)) (sendclose (Var 4))))).
Definition ms_col0 : expr := Lam (LetU (Var 0) (recvclose (Var 1))).
Definition ms_col1 : expr := Lam (LetU (Var 0) (recvclose (Var 9))).
Definition ms_col2 : expr := Lam (LetU (Var 0) (recvclose (Var 5))).
Definition ms_ag0 : expr :=
  LetU (sendclose (Var 11)) (LetU (recvclose (Var 2)) (sendclose (Var 1))).

Definition ms_main : expr :=
  let_new (LetP ENew (LetP ENew (LetP ENew (LetP ENew (LetP ENew
    (LetU (ESpawn ms_ag1)
      (LetU (ESpawn ms_ag2)
        (LetU (ESpawn ms_col0)
          (LetU (ESpawn ms_col1)
            (LetU (ESpawn ms_col2) ms_ag0)))))))))).

(** ** The constraint of the first creation *)

Definition Sm : sty := SSeq (SSnd 0 TUnit) SEnd.

Definition msk (i : nat) : point := match i with 0 => pvar 0 | _ => (pvar 0)·i end.

(** The lower points of the agents, at offset 0 or 1, below the upper points. *)
Definition ms_base (g : fact) : Prop :=
  g = FLt (pvar 0)‾ (msk 1)‾ ∨ g = FLt (pvar 0)‾ (msk 2)‾ ∨ g = FLt (msk 1) (msk 2)‾ ∨
  g = FLt (msk 2)‾ (msk 3)‾ ∨ g = FLt (msk 2)‾ (msk 4)‾ ∨ g = FLt (msk 3) (msk 4)‾ ∨
  g = FLt (pvar 0) (msk 4) ∨ g = FLt (pvar 0) (msk 5)‾ ∨ g = FLt (msk 4)‾ (msk 5)‾.

Definition ms_L (g : fact) : Prop :=
  ∃ x y, ms_base (FLt x y) ∧ (g = FLt x y ∨ g = FLt x⁺ y).

(** Ten per field label, three per offset, one more for a negative point. *)
Definition ms_rank (x : point) : nat * nat * nat :=
  (10 * pt_fsum x + 3 * pt_off x + (if pt_pol x then 0 else 1), 0, 0).

Lemma ms_wf_new : wf_new (bcs_of ms_L).
Proof.
  apply (wf_new_lex3 _ ms_rank).
  - intros u v (x & y & [E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]] & [E'|E']); injection E as -> ->;
      injection E' as -> ->; split; reflexivity.
  - intros [p [] o]; unfold ms_rank, pt_shift, pt_dual, pt_fsum, lex3; simpl; lia.
  - intros u v (x & y & [E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]] & [E'|E']); injection E as -> ->;
      injection E' as -> ->; vm_compute; lia.
Qed.
#[global] Hint Resolve ms_wf_new : wfnew.

Ltac ms_disj := hnf; repeat first [left; reflexivity | right]; reflexivity.
Ltac ms_fact x y :=
  apply law_slt'; [first [exists x, y; split; [ms_disj|left; reflexivity]
                         |exists x, y; split; [ms_disj|right; reflexivity]]|cbn; lia].
Ltac ms_any :=
  first [ ms_fact ((pvar 0)‾) ((msk 1)‾) | ms_fact ((pvar 0)‾) ((msk 2)‾) | ms_fact (msk 1) ((msk 2)‾)
        | ms_fact ((msk 2)‾) ((msk 3)‾) | ms_fact ((msk 2)‾) ((msk 4)‾) | ms_fact (msk 3) ((msk 4)‾)
        | ms_fact ((pvar 0)) (msk 4) | ms_fact ((pvar 0)) ((msk 5)‾) | ms_fact ((msk 4)‾) ((msk 5)‾) ].

(** ** The derivation *)

(** recvclose on the end y at x, with the lower point x and its shift
    below the future. *)
Ltac ms_ub :=
  apply ub_below_novar;
    [intros ? Hy; cbn [sf_unionb fst snd lenv_bot hbot orb] in Hy; heads_cases Hy; ms_any|reflexivity].

Ltac ms_recvclose y pp :=
  unfold recvclose;
  eapply d_letp; [apply tsplit_empty|lsplit_tac (ERecv (Var y)) EUnit| |];
  [ eapply d_recv with (x := pp) (m := 0) (T := TUnit) (S0 := dual Sm);
      [done|exact I| |eapply d_var'; [reflexivity|spare_tac]];
    ms_ub
  | eapply d_letu; [apply tsplit_empty|lsplit_tac (Var 1) EUnit| |];
    [ eapply d_var'; [reflexivity|]; spare_tac
    | eapply d_close with (S0 := SEnd) (x := pp⁺); [done| |eapply d_var'; [reflexivity|spare_tac]];
      first [apply ub_below_empty|ms_ub] ] ].

Ltac ms_sendclose y pp :=
  unfold sendclose;
  eapply d_close with (S0 := SEnd) (x := pp⁺); [done| |];
  [ first [apply ub_below_empty|ms_ub]
  | eapply d_send with (x := pp) (m := 0) (T := TUnit) (S0 := Sm);
      [done|exact I|done|cbn; set_solver| |];
    [ first [apply ub_below_empty|ms_ub]
    | eapply d_pair; [apply tsplit_empty|lsplit_tac EUnit (Var y)
                     |apply d_unit'; spare_tac|eapply d_var'; [reflexivity|spare_tac]] ] ].

Ltac ms_fld κ :=
  eapply d_letp; [apply tsplit_empty|lsplit_tac ENew EUnit| |];
  [apply (d_new_fld _ _ _ _ (pvar 0) κ Sm None None None None); [apply spare_unl; spare_tac|contr_tac]|].

Theorem ms_dftyped : dftyped sw_empty ∅ hc_empty [] (∅, None) ms_main TUnit.
Proof.
  unfold ms_main, let_new.
  eapply d_let; [apply tsplit_empty|apply lsplit_nil| |].
  { eapply (d_new' _ _ _ _ ms_L Sm None None); [spare_tac|apply ms_wf_new|contr_tac]. }
  eapply d_open with (i := 0); [reflexivity|cbn; tauto|cons_tac|].
  rewrite tenv_pinst_empty, sf_pinst_empty. cbn [lenv_pinst fmap list_fmap insert list_insert].
  fold (Γnew ms_L).
  eapply d_letp; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
  { eapply d_var'; [reflexivity|]. spare_tac. }
  ms_fld 1. ms_fld 2. ms_fld 3. ms_fld 4. ms_fld 5.
  eapply d_letu; [apply tsplit_empty|lsplit_tac (ESpawn ms_ag1) EUnit| |].
  { apply d_spawn_lam.
    eapply d_letu; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
    { eapply d_var'; [reflexivity|]. spare_tac. }
    eapply d_letu; [apply tsplit_empty|lsplit_tac (recvclose (Var 11)) EUnit| |].
    { ms_recvclose 11 ((pvar 0)‾). }
    eapply d_letu; [apply tsplit_empty|lsplit_tac (sendclose (Var 10)) EUnit| |].
    { ms_sendclose 10 (msk 1). }
    ms_sendclose 8 (msk 2). }
  eapply d_letu; [apply tsplit_empty|lsplit_tac (ESpawn ms_ag2) EUnit| |].
  { apply d_spawn_lam.
    eapply d_letu; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
    { eapply d_var'; [reflexivity|]. spare_tac. }
    eapply d_letu; [apply tsplit_empty|lsplit_tac (recvclose (Var 7)) EUnit| |].
    { ms_recvclose 7 ((msk 2)‾). }
    eapply d_letu; [apply tsplit_empty|lsplit_tac (sendclose (Var 6)) EUnit| |].
    { ms_sendclose 6 (msk 3). }
    ms_sendclose 4 (msk 4). }
  eapply d_letu; [apply tsplit_empty|lsplit_tac (ESpawn ms_col0) EUnit| |].
  { apply d_spawn_lam.
    eapply d_letu; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
    { eapply d_var'; [reflexivity|]. spare_tac. }
    ms_recvclose 1 ((msk 5)‾). }
  eapply d_letu; [apply tsplit_empty|lsplit_tac (ESpawn ms_col1) EUnit| |].
  { apply d_spawn_lam.
    eapply d_letu; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
    { eapply d_var'; [reflexivity|]. spare_tac. }
    ms_recvclose 9 ((msk 1)‾). }
  eapply d_letu; [apply tsplit_empty|lsplit_tac (ESpawn ms_col2) EUnit| |].
  { apply d_spawn_lam.
    eapply d_letu; [apply tsplit_empty|lsplit_tac (Var 0) EUnit| |].
    { eapply d_var'; [reflexivity|]. spare_tac. }
    ms_recvclose 5 ((msk 3)‾). }
  unfold ms_ag0.
  eapply d_letu; [apply tsplit_empty|lsplit_tac (sendclose (Var 11)) EUnit| |].
  { ms_sendclose 11 ((pvar 0)). }
  eapply d_letu; [apply tsplit_empty|lsplit_tac (recvclose (Var 2)) EUnit| |].
  { ms_recvclose 2 ((msk 4)‾). }
  ms_sendclose 1 (msk 5).
  Unshelve. all: exact None.
Qed.

Theorem ms_deadlock_free : deadlock_free (∅, {[+ ms_main +]}).
Proof.
  apply (soundness_source sw_empty ms_main TUnit); [apply sw_empty_acyc|apply sw_empty_acyc|constructor|].
  exact ms_dftyped.
Qed.

Print Assumptions ms_dftyped.
Print Assumptions ms_deadlock_free.
