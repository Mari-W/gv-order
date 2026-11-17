(** * Every main result of v2 is closed under the global context

    Stage S1. [make check] compiles this file and fails if any line below
    reports an axiom. *)

From GV Require Import lang.Harmony lang.ThreadSim lang.ChannelSwap
  lockfree.Reach lockfree.TauThread.

(** Language: the redex once, progress, preservation. *)
Print Assumptions act_offer_sig.
Print Assumptions act_offer.
Print Assumptions act_step.
Print Assumptions tstep_progress.
Print Assumptions istep_progress.
Print Assumptions proc_progress.
Print Assumptions itstep_closed.
Print Assumptions tstep_transfer.
(** One instrumented semantics and its erasure. *)
Print Assumptions istep_pspec.
Print Assumptions pspec_lift.
Print Assumptions pstep_iff.
Print Assumptions pstep_lift.
Print Assumptions pred_star_lift.
(** Harmony and renamings. *)
Print Assumptions harmony.
Print Assumptions tstep_cmap.
Print Assumptions pstep_pswap.
Print Assumptions safe_pswap_iff.
(** Thread simulation tools. *)
Print Assumptions normalize.
Print Assumptions mrel_extract.
(** Runs, fairness, lock freedom. *)
Print Assumptions lock_free_reach_of.
Print Assumptions thread_acc.
Print Assumptions run_reach.
