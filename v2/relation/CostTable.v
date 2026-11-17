(** * Cost tables and levels (stage S3, proposal §2.8)

    A cost table κ assigns each kind of step a cost. The records live in
    a file of their own, because the record syntax clashes with the
    notation of the typing judgment of static/Typing.v. *)

From GV Require Export lang.Process static.Contexts.

(** ** Cost tables

    The cost of each kind of step. Receive and branch cost at least one,
    because their continuation quantifies over the received value, which
    the relation at the current level cannot read negatively. When β is
    free, so that V at level n reads E at level n, a send costs at least
    one, so that its payload is read below n. *)
Record ctable := CTable {
  c_beta : nat;    (* β, let, case, force *)
  c_new : nat;     (* new_ℓ and new_κ *)
  c_spawn : nat;
  c_link : nat;
  c_give : nat;    (* send, select, close *)
  c_take : nat;    (* receive, branch *)
  c_take_pos : (1 ≤ c_take);
  c_give_pos : (c_beta = 0 → 1 ≤ c_give)
}.

(** κ_DF and κ_L (§2.8). A synchronization costs κ(send) + κ(recv),
    1 in κ_DF and 2 in κ_L. *)
Definition κ_DF : ctable := CTable 1 1 1 0 0 1 ltac:(lia) ltac:(lia).
Definition κ_L : ctable := CTable 0 0 0 0 1 1 ltac:(lia) ltac:(lia).
Abbreviation live := κ_L.

Definition scost (κ : ctable) (σ : slabel) : nat :=
  match σ with
  | SSend _ _ _ | SClose _ | SSel _ _ => c_give κ
  | SRecv _ _ | SBra _ _ => c_take κ
  | SLink _ => c_link κ
  end.

Definition tcost (κ : ctable) (α : tlabel) : nat :=
  match α with
  | LBeta => c_beta κ
  | LNew _ _ | LNewAt _ _ _ => c_new κ
  | LSpawn _ _ => c_spawn κ
  | LSess σ => scost κ σ
  end.

Definition ev_cost (κ : ctable) (ev : event) : nat :=
  match ev with
  | EvBeta _ => c_beta κ
  | EvNew _ _ _ | EvNewAt _ _ _ _ => c_new κ
  | EvSpawn _ _ _ => c_spawn κ
  | EvLink _ _ _ => c_link κ
  | EvMsg _ _ _ _ | EvClose _ _ _ | EvChoice _ _ _ _ => c_give κ + c_take κ
  | EvSess _ σ => scost κ σ
  end.

(** The largest cost of a τ step of a process. *)
Definition cmax (κ : ctable) : nat :=
  Nat.max (Nat.max (Nat.max (Nat.max (c_beta κ) (c_new κ)) (c_spawn κ)) (c_link κ))
    (c_give κ + c_take κ).

Lemma ev_cost_le κ ev : ev_tau ev → ev_cost κ ev ≤ cmax κ.
Proof. unfold ev_tau, cmax. destruct ev; simpl; try discriminate; lia. Qed.

(** ** Readers and levels

    The value, term and process relations at one level, as readers. *)

Abbreviation vrel := (world → senv → ty → expr → Prop).
Abbreviation erel := (world → senv → ty → gset point → expr → Prop).
Abbreviation prel := (world → senv → ty → proc → Prop).

Record level := Level { lV : vrel; lE : erel; lP : prel }.
