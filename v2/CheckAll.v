(** * The main results of v2 are closed under the global context

    The theorems the explorer page (docs/explorer) presents. [make check]
    compiles this file and fails if any line below reports an axiom. *)

From GV Require Import types.Points types.Worlds static.Typing static.Conservativity static.Constants.
From GV Require Import examples.ClientServer examples.Cycle examples.FreshBetween examples.FreshMany.
From GV Require Import examples.FactoryEx examples.GrowRing relation.Relation relation.Adequacy.
From GV Require Import cost.Forwarder cost.CostFund compat.Bind compat.LiveDF.
From GV Require Import compat.ConnectP compat.PTerm static.Fundamental static.FundamentalProc.
From GV Require Import examples.GuardEx examples.LFClose examples.LFCycle examples.LFFreshBetween.
From GV Require Import examples.LFFreshMany examples.LFClientServer examples.LFClientServerSplit examples.LFFactoryEx examples.LFGrowRing.
From GV Require Import examples.LFController soup.SoupRun soup.SoupTau soup.LFAdequacy.
From GV Require Import soup.LFCompose soup.LFTyped lockfree.FairRun.
From GV Require Import examples.SemBranch static.Inversion relation.Ord relation.ExProp relation.Ranks examples.LFLink compat.Redex static.PointSubst.
From GV Require Import examples.SinstStuck static.Sinst examples.SharedRoots static.Hiding examples.GenNew.
From GV Require Import soup.LFConnectN examples.Ring.

(** types/Points.v *)
Print Assumptions pt_dual_dual.
Print Assumptions pt_field_dual.
(** types/Worlds.v *)
Print Assumptions wf_join_iff.
Print Assumptions wmodels_exists.
Print Assumptions wchain_lt_wf.
(** static/Typing.v *)
Print Assumptions fptyped_wf.
Print Assumptions fp_connect_join.
Print Assumptions ptyped_wf.
(** static/Hiding.v *)
Print Assumptions swrestrict_iff.
Print Assumptions typed_ren.
Print Assumptions fptyped_ren.
Print Assumptions join_vis.
Print Assumptions connect_hidden.
Print Assumptions ptyped_full.
Print Assumptions fptyped_ptyped.
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
Print Assumptions Erel_iff.
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
Print Assumptions sem_p_connect_sw.
Print Assumptions fundamental_proc.
Print Assumptions live_fundamental_proc.
Print Assumptions soundness.
Print Assumptions live_soundness.
Print Assumptions soundness_source.
Print Assumptions sem_p_connect_h.
Print Assumptions fundamental_proc_h.
Print Assumptions live_fundamental_proc_h.
Print Assumptions soundness_h.
Print Assumptions live_soundness_h.
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
(** examples/LFClientServerSplit.v *)
Print Assumptions cs_split_lock_free.
Print Assumptions cs_split_typed.
Print Assumptions cs_split_lock_free_h.
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
(** examples/LFLink.v *)
Print Assumptions lk_new.
Print Assumptions lk_typed.
(** soup/SoupRun.v *)
Print Assumptions lfsoup_step.
(** soup/SoupTau.v *)
Print Assumptions soup_no_tau_divergence.
(** soup/LFAdequacy.v *)
Print Assumptions lf_adequacy.
Print Assumptions lf_thread_progress.
(** soup/LFCompose.v *)
Print Assumptions lf_soup_connect.
Print Assumptions lf_p_connect.
Print Assumptions join_models.
Print Assumptions lf_sems_adequacy.
Print Assumptions lf_connect_adequacy.
Print Assumptions lf_p_term.
Print Assumptions lf_soundness_source.
(** soup/LFTyped.v *)
Print Assumptions lf_fundamental.
Print Assumptions lf_soundness.
Print Assumptions lf_soundness_run.
Print Assumptions lf_soundness_padovani.
Print Assumptions lf_p_connect_h.
Print Assumptions lf_fundamental_h.
Print Assumptions lf_soundness_h.
(** lockfree/FairRun.v *)
Print Assumptions fair_run_exists.
Print Assumptions fair_run_exists_proc.
Print Assumptions lock_free_padovani.

(** static/PointSubst.v, static/Inversion.v: conservativity at E-Open *)
Print Assumptions cons_new.
Print Assumptions cons_gen.
Print Assumptions wf_new_gen.
Print Assumptions wf_new_plus_gen.
Print Assumptions gen_new1_gen.
Print Assumptions gen_new_sem_of.
Print Assumptions Erel_new.
Print Assumptions Erel_new_fld.
Print Assumptions opened_cons.
(** examples/SemBranch.v: the flag variant *)
Print Assumptions Tbad_not_cons.
Print Assumptions sbv_deadlock_free.
Print Assumptions sbv_rejected.
Print Assumptions sbv_rejected_h.
(** relation/Ord.v: ordinals and the transfinite fixpoint *)
Print Assumptions olt_wf.
Print Assumptions oadd_lt.
Print Assumptions osfix_unfold.
Print Assumptions exist_prop.
Print Assumptions wf_iff_wellfounded.
(** types/Contractive.v and static/Sinst.v: contractive session types,
    instantiation preserves typing over contractive contexts *)
Print Assumptions unrN_sfuel.
Print Assumptions sequiv_sinst.
Print Assumptions typed_scontr.
Print Assumptions typed_sinst.
(** examples/SinstStuck.v: without contractive contexts instantiation
    does not preserve typing *)
Print Assumptions inv_chan_sty.
Print Assumptions typed_sinst_false.
Print Assumptions ss_var_guard.
(** examples/SharedRoots.v: the shared constants of P-Connect are not the roots of the cut, and hiding *)
Print Assumptions shared_not_cut.
Print Assumptions fact_needs_zero.
Print Assumptions shared_hidden.
Print Assumptions opposite_clash.
Print Assumptions opposite_compose.
Print Assumptions opposite_df.
(** static/ConnectN.v, soup/LFConnectN.v: the n-ary P-Connect, admissible from the binary one *)
Print Assumptions p_connect_n.
Print Assumptions connect_n_soundness.
Print Assumptions connect_n_live_soundness.
Print Assumptions connect_n_lf_soundness.
(** examples/Ring.v: Milner's ring, pairwise consistent and cyclic, rejected; the acyclic ring typed *)
Print Assumptions ring_comps.
Print Assumptions ring_pairs.
Print Assumptions ring_cyclic.
Print Assumptions ring_rejected.
Print Assumptions ring_rejected_full.
Print Assumptions ring_typed.
Print Assumptions ring_df.
(** static/Fundamental.v and static/Conservativity.v: Sub-Ex lowers the
    lower bound below the heads of the body *)
Print Assumptions Vrel_heads.
Print Assumptions Vrel_tsub.
Print Assumptions tsub_open_pack.
(** relation/Ranks.v: the largest of finitely many ranks, under excluded
    middle *)
Print Assumptions ole_total.
Print Assumptions list_max_rank.
Print Assumptions two_below_gd.
(** examples/GenNew.v: creations with exits, two upper bounds and two
    entries *)
Print Assumptions tu_gen1.
Print Assumptions tu_not_wf_new.
Print Assumptions tu_dftyped.
Print Assumptions tu_deadlock_free.
Print Assumptions tu_rejected_wf_new.
Print Assumptions te_gen.
Print Assumptions te_not_wf_new.
Print Assumptions te_dftyped.
Print Assumptions te_deadlock_free.
Print Assumptions te_rejected_wf_new.
