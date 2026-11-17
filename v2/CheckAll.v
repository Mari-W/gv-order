(** * Every main result of v2 is closed under the global context

    Stages S1, S2 and S3. [make check] compiles this file and fails if any line below
    reports an axiom. *)

From GV Require Import lang.Harmony lang.ThreadSim lang.ChannelSwap
  lockfree.Reach lockfree.TauThread.
From GV Require Import static.Conservativity static.Weakening static.Renaming static.PointSubst
  examples.ClientServer.
From GV Require Import relation.Adequacy.

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
(** S2. Worlds: R7, renaming families apart, renaming generated roots. *)
Print Assumptions strict_join_iff.
Print Assumptions strict_wfrename.
Print Assumptions lfworld_wfrename.
Print Assumptions w_lt_grename.
Print Assumptions p_join_iff_connect.
(** S2. The merged judgment: conservativity over DF typing. *)
Print Assumptions typed_dftyped.
Print Assumptions dftyped_typed.
Print Assumptions conservative.
(** S2. Structural lemmas. *)
Print Assumptions typed_wext.
Print Assumptions typed_rename.
Print Assumptions typed_insert_none.
Print Assumptions typed_emap.
Print Assumptions typed_gmap.
Print Assumptions typed_grename.
Print Assumptions typed_pinst.
(** S2. Examples. *)
Print Assumptions cs_typed.
(** S3. The step-indexed fixpoint. *)
Print Assumptions sfix_unfold.
Print Assumptions sfix_below_lt.
(** S3. Readiness. *)
Print Assumptions ready_t_future.
Print Assumptions ready_t_mono.
Print Assumptions ready_p_mono.
(** S3. The characteristic equations of R^κ. *)
Print Assumptions Vrel_unit_iff.
Print Assumptions Vrel_sess_iff.
Print Assumptions Vrel_prod_iff.
Print Assumptions Vrel_sum_iff.
Print Assumptions Vrel_lolli_iff.
Print Assumptions Vrel_box_iff.
Print Assumptions Vrel_ex_iff.
Print Assumptions Erel_S_iff.
Print Assumptions Erel_S_ind.
Print Assumptions Prel_S_iff.
Print Assumptions Prel_S_ind.
Print Assumptions Erel_S_step.
Print Assumptions Prel_S_step.
Print Assumptions Varr_spawn_iff.
(** S3. Downward closure and monotonicity. *)
Print Assumptions Vrel_val.
Print Assumptions Vrel_Erel.
Print Assumptions Vrel_mono.
Print Assumptions Erel_mono.
Print Assumptions Prel_mono.
Print Assumptions Vrel_down.
Print Assumptions Erel_down.
Print Assumptions Erel_future.
Print Assumptions Prel_down.
(** S3. Adequacy. *)
Print Assumptions adequacy_gen.
Print Assumptions adequacy.
Print Assumptions live_adequacy.
Print Assumptions Prel_done.
Print Assumptions Erel_beta_unit.
