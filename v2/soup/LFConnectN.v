(** * The n-ary P-Connect in the lock-free judgment

    [p_connect_n] (static/ConnectN.v) folds the binary P-Connect, so a
    closed n-ary composition at Some N is lock
    free by [lf_soundness_h]. *)

From GV Require Import soup.LFAdequacy.
From GV Require Export static.ConnectN soup.LFTyped.

Theorem connect_n_lf_soundness N Ws p T :
  excluded_middle → functional_choice →
  pcomps (Some N) Ws ∅ p T → swf (sw_joins Ws) → lock_free p.
Proof.
  intros EM FC Hp HS. destruct (p_connect_n (Some N) Ws ∅ p T Hp HS) as (W & Hty & _).
  exact (lf_soundness_h N W p T EM FC Hty).
Qed.
