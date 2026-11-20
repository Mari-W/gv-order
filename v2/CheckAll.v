(** * The main results of v2 are closed under the global context

    The theorems the explorer page (docs/explorer) presents. [make check]
    compiles this file and fails if any line below reports an axiom. *)

From GV Require Import types.Points types.Worlds static.Typing static.Conservativity static.Constants.
From GV Require Import examples.ClientServer examples.Cycle examples.FreshBetween examples.FreshMany.
From GV Require Import examples.FactoryEx examples.GrowRing relation.Relation relation.Adequacy.
From GV Require Import cost.Forwarder cost.CostFund compat.Bind compat.LiveDF.
From GV Require Import compat.ConnectP compat.PTerm static.Fundamental static.FundamentalProc.
From GV Require Import examples.GuardEx examples.LFClose examples.LFCycle examples.LFFreshBetween.
From GV Require Import examples.LFFreshMany examples.LFClientServer examples.LFFactoryEx examples.LFGrowRing.
From GV Require Import examples.LFController soup.SoupRun soup.SoupTau soup.LFAdequacy.
From GV Require Import soup.LFCompose soup.LFTyped.

(** types/Points.v *)
Print Assumptions pt_dual_dual.
Print Assumptions pt_field_dual.
(** types/Worlds.v *)
Print Assumptions strict_join_iff.
(** static/Typing.v *)
Print Assumptions ptyped_strict.
Print Assumptions p_connect_join.
(** static/Conservativity.v *)
Print Assumptions d_conv.
Print Assumptions dftyped_typed.
Print Assumptions typed_dftyped.
Print Assumptions conservative.
(** static/Constants.v *)
Print Assumptions k_send_df.
Print Assumptions k_recv_df.
Print Assumptions k_close_df.
Print Assumptions k_select_df.
Print Assumptions k_branch_df.
Print Assumptions k_link_df.
Print Assumptions k_spawn_df.
Print Assumptions k_force_df.
(** examples/ClientServer.v *)
Print Assumptions cs_dftyped.
Print Assumptions cs_typed.
(** examples/Cycle.v *)
Print Assumptions cy_dftyped.
Print Assumptions cy_typed.
(** examples/FreshBetween.v *)
Print Assumptions fb_dftyped.
Print Assumptions fb_typed.
(** examples/FreshMany.v *)
Print Assumptions fm_dftyped.
Print Assumptions fm_typed.
(** examples/FactoryEx.v *)
Print Assumptions fx_dftyped.
Print Assumptions fx_typed.
(** examples/GrowRing.v *)
Print Assumptions rg_dftyped.
Print Assumptions rg_typed.
(** relation/Relation.v *)
Print Assumptions Erel_0.
Print Assumptions Vrel_box_iff.
Print Assumptions Vrel_ex_iff.
(** relation/Adequacy.v *)
Print Assumptions adequacy_gen.
Print Assumptions adequacy.
Print Assumptions live_adequacy.
(** cost/Forwarder.v *)
Print Assumptions dead_thunk_rejected.
Print Assumptions fw_ptyped.
(** cost/CostFund.v *)
Print Assumptions cost_fundamental.
Print Assumptions fsem_of_cost.
Print Assumptions fw_fsem.
(** compat/Bind.v *)
Print Assumptions Erel_bind.
(** compat/LiveDF.v *)
Print Assumptions live_sub_df.
(** compat/ConnectP.v *)
Print Assumptions sem_p_connect.
(** compat/PTerm.v *)
Print Assumptions sem_p_term.
(** static/Fundamental.v *)
Print Assumptions typed_sem.
Print Assumptions fundamental.
Print Assumptions fundamental_typed.
Print Assumptions live_fundamental.
Print Assumptions live_fundamental_typed.
(** static/FundamentalProc.v *)
Print Assumptions fundamental_proc.
Print Assumptions live_fundamental_proc.
Print Assumptions soundness.
Print Assumptions live_soundness.
Print Assumptions soundness_source.
(** examples/GuardEx.v *)
Print Assumptions div_not_guarded.
Print Assumptions pn_fix_not_guarded.
Print Assumptions cx_not_guarded.
Print Assumptions spawn_loop_not_guarded.
Print Assumptions loop_guarded.
Print Assumptions stage_guarded.
(** examples/LFClose.v *)
Print Assumptions cl_lftyped.
Print Assumptions cl_lock_free.
(** examples/LFCycle.v *)
Print Assumptions cy_guarded.
Print Assumptions cy_lftyped.
Print Assumptions cy_lock_free.
(** examples/LFFreshBetween.v *)
Print Assumptions fb_guarded.
Print Assumptions fb_lftyped.
Print Assumptions fb_lock_free.
(** examples/LFFreshMany.v *)
Print Assumptions fm_guarded.
Print Assumptions fm_lftyped.
Print Assumptions fm_lock_free.
(** examples/LFClientServer.v *)
Print Assumptions cs_guarded.
Print Assumptions cs_lftyped.
Print Assumptions cs_lock_free.
(** examples/LFFactoryEx.v *)
Print Assumptions fx_guarded.
Print Assumptions fx_lftyped.
Print Assumptions fx_lock_free.
(** examples/LFGrowRing.v *)
Print Assumptions rg_guarded.
Print Assumptions rg_lftyped.
Print Assumptions rg_lock_free.
(** examples/LFController.v *)
Print Assumptions ctl_typedN.
Print Assumptions ctl_guarded.
Print Assumptions ctl_lftyped.
Print Assumptions ctl_lock_free.
(** soup/SoupRun.v *)
Print Assumptions lfsoup_step.
(** soup/SoupTau.v *)
Print Assumptions soup_no_tau_divergence.
(** soup/LFAdequacy.v *)
Print Assumptions lf_adequacy.
Print Assumptions lf_thread_progress.
(** soup/LFCompose.v *)
Print Assumptions lf_p_connect.
Print Assumptions lf_p_term.
Print Assumptions lf_soundness_source.
(** soup/LFTyped.v *)
Print Assumptions lf_fundamental.
Print Assumptions lf_soundness.
