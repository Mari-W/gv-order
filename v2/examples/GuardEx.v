(** * The programs of Appendix B without the guard (F3)

    The guard is gone (F3 of docs/redesign/fable-findings.md). A force
    costs one unit in κ_L, F-Force ticks every held end that is not
    idle, and E-Force charges one unit of effect, which the enclosing
    rules age the held context by. The verdicts of the programs below
    change as follows.

    - Accepted now. A box that forces itself before it acts
      ([div_box], #14), PN's ⟨fix λx.x⟩ as a box whose λ applies the
      forced self ([pn_fix], #13), and the box of GuardCex, which forces
      itself in the hole of a let ([cx_box], #15). None of them holds an
      end, so their loops are harmless for lock freedom, and the box
      relation reads the body one force below the level
      ([Vrel_box_iff], [gen_e_box]).
    - Rejected still. A recursion that spawns the forced self with an
      end ([spawn_loop], #12, #40). The child calls the box at cost ∞,
      and the end it holds must have credit at least that cost, which no
      finite bound gives. A loop that holds a non-idle end across its
      forces is rejected the same way, by aging.
    - Accepted as before. A server loop that receives before it recurses
      ([loop]) and the stage of the C2 pipeline of B.1 #4 ([stage]). *)

From GV Require Export examples.LFTools.

(** !(f = force f) *)
Definition div_box : expr := EBox (EForce (Var 0)).


(** !(f = λx. (force f) x) *)
Definition pn_fix : expr := EBox (Lam (App (EForce (Var 1)) (Var 0))).


(** !(f = let ∗ = (force f) ∗ in λy. y) *)
Definition cx_box : expr := EBox (LetU (App (EForce (Var 0)) EUnit) (Lam (Var 0))).


(** !(f = λc. spawn (λ_. (force f) c)) *)
Definition spawn_loop : expr := EBox (Lam (ESpawn (Lam (App (EForce (Var 2)) (Var 1))))).


(** !(f = λx. let ⟨v, x'⟩ = recv x in (force f) x') *)
Definition loop : expr := EBox (Lam (LetP (ERecv (Var 0)) (App (EForce (Var 3)) (Var 0)))).


(** The stage of B.1 #4:
    !(f = λin. let ⟨v, in⟩ = recv in in let ∗ = close in in
              let ⟨a, b⟩ = new in let ∗ = spawn (λ_. (force f) b) in close (send ⟨v, a⟩)) *)
Definition stage : expr :=
  EBox (Lam (LetP (ERecv (Var 0))
    (LetU (EClose (Var 0))
      (LetP ENew
        (LetU (ESpawn (Lam (App (EForce (Var 6)) (Var 1))))
          (EClose (ESend (Pair (Var 3) (Var 1))))))))).


(** ** The new verdicts as theorems *)

Definition Cnil : bcs := bcs_of (λ _, False).

Lemma Cnil_hold W Γ : hold_at W Γ Cnil [].
Proof. intros x y (g0 & (f & Hf & _) & _). done. Qed.

(** [pn_fix] types in the lock-free judgment, at each bound: a box of
    ∗ ⊸ ∗ whose call has cost ∞. It holds no end, so no credit pays for
    the forces. *)
Theorem pn_fix_typed W N Γ F : typed W (Some N) ∅ Γ [] F pn_fix (lbox 0 Cnil None TUnit TUnit) (Some 0).
Proof.
  unfold pn_fix. change [] with (nones 0).
  eapply lbox_typed; [done|done|reflexivity|].
  eapply e_app_; [lsplit_tac (EForce (Var 1)) (Var 0)|shelve| | | |shelve].
  { eapply (lbox_force_eq _ _ _ _ _ _ 0 Cnil None TUnit TUnit [] _ UNone TUnit TUnit);
      [done|apply Cnil_hold|done|done|done|].
    eapply e_var'; [reflexivity|]. spare_tac. }
  lage_tac.
  eapply e_var'; [reflexivity|]. spare_tac.
  Unshelve. all: first [exact I | exact None | simpl; lia | simpl; done].
Qed.

(** [div_box] types in the lock-free judgment, at each bound: a box of
    cost ∞ whose body forces it. *)
Theorem div_box_typed W N Γ F : typed W (Some N) ∅ Γ [] F div_box (TBox 0 0 Cnil None None TUnit) (Some 0).
Proof.
  unfold div_box. eapply e_box; [intros o Ho; inversion Ho|done|].
  intros ss Hk _. destruct ss; [|done]. cbn.
  eapply (e_force _ _ _ _ _ _ _ 0 0 Cnil None None TUnit [] [] (Some 0));
    [done|apply Cnil_hold|done|done|done|].
  eapply e_var'; [reflexivity|]. spare_tac.
Qed.

(** [cx_box] types in the lock-free judgment, at each bound: a box of
    cost ∞ whose body applies the forced self in the hole of a let. *)
Definition Tid : ty := TLolli UNone LBot (Some 0) TUnit TUnit (Some 0).

Theorem cx_box_typed W N Γ F : typed W (Some N) ∅ Γ [] F cx_box (TBox 0 0 Cnil None None Tid) (Some 0).
Proof.
  unfold cx_box. eapply e_box; [intros o Ho; inversion Ho|done|].
  intros ss Hk _. destruct ss; [|done]. cbn.
  eapply (e_letu_ _ _ _ _ _ _ _ _ _ _ _ None (Some 0)); [lsplit_tac (App (EForce (Var 0)) EUnit) (Lam (Var 0))| | | ].
  { eapply (e_app_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ None (Some 0)); [lsplit_tac (EForce (Var 0)) EUnit|shelve| | | |shelve].
    { eapply (e_force _ _ _ _ _ _ _ 0 0 Cnil None None Tid [] [] (Some 0));
        [done|apply Cnil_hold|done|done|done|].
      eapply e_var'; [reflexivity|]. spare_tac. }
    lage_tac.
    apply e_unit'. spare_tac. }
  lage_tac.
  eapply e_abs with (Θh := ∅) (a := Some 0) (ub := UNone) (lb := LBot);
    [done|apply thage_empty|lage_tac|done|].
  eapply e_var'; [reflexivity|]. spare_tac.
  Unshelve. all: first [exact I | exact None | simpl; lia | simpl; done].
Qed.

(** [spawn_loop] is rejected by aging. Its child runs (force f) c with c
    held while the force runs, so E-App ages the type of c by the cost
    of the force, at least one, and the self call then asks c back at the
    credit of the parameter. Credits only fall under subtyping, so the
    parameter credit a must satisfy a ≤ a − 1, which no finite credit
    does unless the protocol of c is idle. Typing keeps a ≤ m on every
    end ([typed_cr_tk]) and P-Term and E-New give every end finite
    tickets, so no end a program can pass meets it. *)
Theorem spawn_loop_rejected S x a m a' :
  ¬ idle S → a ≠ None → tage (Some 1) (TSess S x a m) (TSess S x a' m) → ¬ fle a a'.
Proof.
  intros Hi Ha Hage Hle. inversion Hage as [T HT| S0 x0 a0 m0 H1| S0 x0 a0 m0 HI| | | |]; subst.
  - inversion HT.
  - destruct a as [n|]; [|done]. simpl in H1, Hle. lia.
  - done.
Qed.
