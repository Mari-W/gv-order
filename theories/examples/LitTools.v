(** * Shared tools for the examples taken from the literature

    The literature examples place every channel at a point of one root.
    The first [new] of a program creates a fresh point variable ι with
    the empty creation constraint, and every later channel is created by
    [t_new_at] at ι+k, which the hypothesis of the first [new] makes
    known. The facts these programs need are then ι+j ≺ ι+k for j < k,
    which program order gives ([slt_po_lt]).

    A file that needs facts between points of two roots states them in
    the creation constraint of the second channel, as the examples on
    this branch do. *)

From stdpp Require Import base strings gmap gmultiset relations.
From LRGV Require Export examples.ExampleTools.

Set Default Proof Using "All".

(** Program order over a gap: j < k gives (a, j) ≺ (a, k). *)
Lemma slt_po_lt W Ψ a j k : world_wf W → j < k → slt W Ψ (Pt a j) (Pt a k).
Proof.
  intros HW Hjk.
  replace (Pt a k) with (pt_shift (S (k - j - 1)) (Pt a j))
    by (unfold pt_shift; cbn; f_equal; lia).
  apply sl_w, wf_lt_po_n, HW.
Qed.

(** The two shapes of x ≼ u on one root. *)
Lemma sle_po_le W Ψ a j k : world_wf W → j ≤ k → sle W Ψ (Pt a j) (Pt a k).
Proof.
  intros HW Hjk. destruct (decide (j = k)) as [->|Hne]; [left; apply se_refl|].
  right. apply slt_po_lt; [done|lia].
Qed.

(** A point of the first root is known from the hypothesis of the first
    [new]. *)
Lemma skn_root0 W Ψ C j :
  (C, [pvar 0]) ∈ Ψ → skn W Ψ (Pt (NVar 0) j).
Proof.
  intros Hg. eapply (skn_inst W Ψ C [pvar 0] (pvar 0)); [exact Hg|by left|done].
Qed.

(** One goal per point of a concrete frame, each by program order. *)
Ltac po_frame HW := intros ? Hy; mem_cases Hy; (apply slt_po_lt; [exact HW|cbn; lia]).

(** The frame variable of the enclosing λ, at its upper point u. *)
Ltac po_fvar HW u := exists u; split; [done|apply sle_po_le; [exact HW|cbn; lia]].

(** The lower point of a λ against the heads it captures. *)
Ltac lb_po HW := intros ? Hy; mem_cases Hy; (apply sle_po_le; [exact HW|cbn; lia]).

(** A blocking call whose frame is concrete points and the frame
    variable of the enclosing λ at u. *)
Ltac po_gate HW u := apply ubs_intro; [po_frame HW|po_fvar HW u].

(** The same at the top level, where the frame has no variable. *)
Ltac po_gate0 HW := apply ubs_intro; [po_frame HW|done].

(** ** Chains of carried roots

    A recursive server that creates one channel per call places it at a
    carried root of the channel it answers on, so the points of every
    round sit on one root and no creation constraint names an outer
    point. ι.0ⁿ is the n-fold first carried root of the point variable 0
    (slots counted from 0 in Rocq). *)

Fixpoint slotv (n : nat) : pname :=
  match n with 0 => NVar 0 | S m => NSlot (slotv m) 0 0 end.

Abbreviation pcr := (Pt (NSlot (NVar 0) 0 0) 0).

(** Instantiating ι by ι.0 moves every point of the chain one level
    deeper, which is what the recursive [force] does. *)
Lemma slotv_inst n : pn_inst (plist [pcr]) (slotv n) = Pt (slotv (S n)) 0.
Proof. induction n as [|n IH]; [done|]. cbn [slotv pn_inst]. by rewrite IH. Qed.

(** The depth of a name in carried roots. *)
Fixpoint sdepth (p : pname) : nat :=
  match p with NSlot q _ _ => S (sdepth q) | _ => 0 end.

Lemma sdepth_slotv n : sdepth (slotv n) = n.
Proof. induction n as [|n IH]; [done|]. cbn. by rewrite IH. Qed.

(** A strict order on points, read lexicographically on depth and
    offset. [ult] puts a deeper carried root above a shallower one, the
    order of a producer that sends its fresh channel on. A server whose
    fresh channel answers before the channel it was called on orders
    the other way and uses the rank −2·depth + offset in ℤ instead
    (examples/FactServer.v, examples/KobForwarder.v). *)
Definition ult (x y : point) : Prop :=
  sdepth (pt_name x) < sdepth (pt_name y) ∨
  (sdepth (pt_name x) = sdepth (pt_name y) ∧ pt_off x < pt_off y).

Lemma ult_trans x y z : ult x y → ult y z → ult x z.
Proof. unfold ult. lia. Qed.
Lemma ult_irrefl x : ¬ ult x x.
Proof. unfold ult. lia. Qed.
Lemma ult_po x : ult x (pt_shift 1 x).
Proof. unfold ult, pt_shift. cbn. lia. Qed.

(** A creation constraint whose facts are ≺ facts inside ι that rise
    along the depth. *)
Lemma cc_ok_ult peq plt P :
  (∀ g, P g → fact_scoped 1 g → ∃ x y, g = FLt x y ∧ ult x y) →
  cc_ok peq plt (BCs [] P).
Proof.
  intros HP. apply (cc_ok_inner peq plt P ult);
    [exact ult_trans|exact ult_irrefl|intros x _; apply ult_po|exact HP].
Qed.

(** ** E-Case for Θ = ∅

    The scrutinee takes the bindings it occurs in and both branches take
    the rest, so [sok] is checked against the first branch and the
    second branch runs under the same environment. A branch that leaves
    a □ binding unused weakens it away at its leaves. *)
Lemma tv_case W Φ Ψ Δ F e e1 e2 T1 T2 T :
  world_wf W →
  sok e 0 e1 1 Δ && negb (lenv_bot (lp e1 1 Δ)) = true →
  typed W Φ Ψ ∅ (lp e 0 Δ) (sf_union F (lenv_heads (lp e1 1 Δ))) e (TSum T1 T2) →
  typed W Φ Ψ ∅ (Some T1 :: lp e1 1 Δ) F e1 T →
  typed W Φ Ψ ∅ (Some T2 :: lp e1 1 Δ) F e2 T →
  typed W Φ Ψ ∅ Δ F (Case e e1 e2) T.
Proof.
  intros HW Hs He H1 H2. apply andb_true_iff in Hs as [Hs Hb]. apply negb_true_iff in Hb.
  eapply t_case; [apply (comp0 W HW)|by apply lp_split| |exact H1|exact H2].
  by rewrite Hb, (tenv_heads0 W HW), union_empty_l_L.
Qed.
