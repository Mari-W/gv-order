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
