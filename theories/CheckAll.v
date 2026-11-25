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
From GV Require Import examples.SemBranch examples.BranchExt examples.PointReuse static.Inversion relation.Ord relation.ExProp relation.Ranks examples.LFLink compat.Redex static.PointSubst.
From GV Require Import examples.SinstStuck static.Sinst examples.SharedRoots static.Hiding examples.GenNew.
From GV Require Import soup.LFConnectN examples.Ring.
From GV Require Import examples.Copycat examples.ForkJoin.
From GV Require Import static.ChanRen examples.CopycatTwo static.LetVar examples.LetVarCounter examples.CopycatTwoN.
From GV Require Import static.Skeleton examples.Rejects.
From GV Require Import examples.Descent.
From GV Require Import examples.FlagPair examples.RxChain examples.BitProgram examples.MilnerSched.

(** types/Points.v *)
Print Assumptions pt_dual_dual.
Print Assumptions pt_field_dual.
(** types/Worlds.v *)
Print Assumptions wf_join_iff.
Print Assumptions wmodels_exists.
Print Assumptions wchain_lt_wf.
(** static/Typing.v *)
Print Assumptions ptyped_wf.
Print Assumptions ptyped_iann_local.
Print Assumptions p_connect_iann.
(** static/Hiding.v *)
Print Assumptions swrestrict_iff.
Print Assumptions typed_ren.
Print Assumptions ptyped_ren.
Print Assumptions ptyped_apart.
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
Print Assumptions cs_deadlock_free.
(** examples/Cycle.v *)
Print Assumptions cy_dftyped.
Print Assumptions cy_typed.
Print Assumptions cy_deadlock_free.
(** examples/FreshBetween.v *)
Print Assumptions examples.FreshBetween.fb_dftyped.
Print Assumptions fb_typed.
Print Assumptions fb_deadlock_free.
(** examples/FreshMany.v *)
Print Assumptions fm_dftyped.
Print Assumptions fm_typed.
Print Assumptions fm_deadlock_free.
(** examples/FactoryEx.v *)
Print Assumptions fx_dftyped.
Print Assumptions fx_typed.
Print Assumptions fx_deadlock_free.
(** examples/GrowRing.v *)
Print Assumptions rg_dftyped.
Print Assumptions rg_typed.
Print Assumptions rg_deadlock_free.
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
Print Assumptions typed_cr_tk.
Print Assumptions fw_fsem.
(** compat/Bind.v *)
Print Assumptions Erel_bind.
(** compat/LiveDF.v *)
Print Assumptions live_sub_df.
(** compat/Fusion.v *)
Print Assumptions Prel_gfuse.
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
Print Assumptions proc_gen.
Print Assumptions soundness_source.
Print Assumptions fundamental_proc.
Print Assumptions live_fundamental_proc.
Print Assumptions adequacy_sw.
Print Assumptions soundness.
Print Assumptions live_soundness.
(** examples/GuardEx.v *)
Print Assumptions div_box_typed.
Print Assumptions pn_fix_typed.
Print Assumptions cx_box_typed.
Print Assumptions spawn_loop_rejected.
(** examples/LFClose.v *)
Print Assumptions cl_lftyped.
Print Assumptions cl_dftyped.
Print Assumptions cl_deadlock_free.
Print Assumptions cl_lock_free.
(** examples/LFCycle.v *)
Print Assumptions cy_lftyped.
Print Assumptions cy_lock_free.
(** examples/LFFreshBetween.v *)
Print Assumptions fb_lftyped.
Print Assumptions fb_lock_free.
(** examples/LFFreshMany.v *)
Print Assumptions fm_lftyped.
Print Assumptions fm_lock_free.
(** examples/LFClientServer.v *)
Print Assumptions cs_lftyped.
Print Assumptions cs_lock_free.
(** examples/LFClientServerSplit.v *)
Print Assumptions cs_split_lock_free.
Print Assumptions cs_split_typed.
(** examples/LFFactoryEx.v *)
Print Assumptions fx_lftyped.
Print Assumptions fx_lock_free.
(** examples/LFGrowRing.v *)
Print Assumptions rg_lftyped.
Print Assumptions rg_lock_free.
(** examples/LFController.v *)
Print Assumptions ctl_typedN.
Print Assumptions ctl_lftyped.
Print Assumptions ctl_lock_free.
(** examples/LFLink.v *)
Print Assumptions lk_new.
Print Assumptions lk_typed.
Print Assumptions lk_closed_typed.
Print Assumptions lk_closed_lock_free.
(** soup/SoupRun.v *)
Print Assumptions lfsoup_step.
(** soup/SoupTau.v *)
Print Assumptions soup_no_free_divergence.
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
Print Assumptions lf_soundness_run.
Print Assumptions lf_soundness_padovani.
Print Assumptions lf_fundamental.
Print Assumptions lf_soundness.
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
Print Assumptions cons_open_iff.
Print Assumptions gen_new_sem_of.
Print Assumptions Erel_new.
Print Assumptions Erel_new_fld.
Print Assumptions opened_cons.
(** examples/SemBranch.v: the flag variant *)
Print Assumptions Tbad_not_cons.
Print Assumptions sbv_deadlock_free.
Print Assumptions sbv_rejected.
(** examples/BranchExt.v: one world per arm of E-Case fails in the relation *)
Print Assumptions bx_not_E.
Print Assumptions bx_rejected.
Print Assumptions bx_left_typed.
Print Assumptions bx_right_typed.
Print Assumptions bx_scrut_typed.
(** examples/PointReuse.v: two exchanges at one point in a typed program *)
Print Assumptions pr_round_typed.
Print Assumptions pr_term.
Print Assumptions pr_deadlock_free.
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
(** types/SessSub.v and fuel/FuelSub.v: session subtyping, payload
    credits with variance *)
Print Assumptions ssub_trans.
Print Assumptions ssub_dual.
Print Assumptions ssub_df.
Print Assumptions ssub_sinst.
Print Assumptions Vfuel_crT.
Print Assumptions typed_scontr.
Print Assumptions typed_sinst.
(** examples/SinstStuck.v: without contractive contexts instantiation
    does not preserve typing *)
Print Assumptions inv_chan_sty.
Print Assumptions typed_sinst_false.
Print Assumptions ss_var_guard.
(** examples/SharedRoots.v: two components that use one private constant, composed as they are or renamed apart *)
Print Assumptions fact_needs_zero.
Print Assumptions shared_compose.
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
Print Assumptions examples.Ring.ring_rejected.
Print Assumptions cyc2_rejected.
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
(** examples/Copycat.v *)
Print Assumptions fwd_dftyped.
Print Assumptions fwd_expand.
Print Assumptions fwd_config_deadlock_free.
Print Assumptions examples.Copycat.ring_rejected.
Print Assumptions fwdh_term.
Print Assumptions fwdh_config_deadlock_free.
Print Assumptions examples.Copycat.fb_dftyped.
Print Assumptions fwdp_expand.
Print Assumptions fwdp_sem.
(** static/ChanRen.v *)
Print Assumptions typed_cren.
Print Assumptions ptyped_cren.
(** examples/CopycatTwo.v *)
Print Assumptions fwdq_term.
Print Assumptions J_acyc.
Print Assumptions fwdp_expand2.
Print Assumptions fwdp_expand2_df.
Print Assumptions fwdp_expand2_example.
Print Assumptions collapse_swf.
Print Assumptions J_wok.
Print Assumptions fwdp_expand2_N.
(** examples/CopycatTwoN.v *)
Print Assumptions fb_typed.
Print Assumptions fwdq_term_fin.
Print Assumptions fwdp_expand2_fin.
Print Assumptions fwdp_expand2_lf.
(** static/Inversion.v, variables and the unit *)
Print Assumptions inv_var_ctx.
Print Assumptions inv_unit_ctx.
Print Assumptions inv_var_transfer.
(** static/PointSubstTyped.v *)
Print Assumptions cons_open_hinst.
Print Assumptions new_ok_hinst.
Print Assumptions tsub_hinst.
Print Assumptions typed_pinst.
Print Assumptions typed_open_inst.
(** static/LetVar.v *)
Print Assumptions let_intro.
Print Assumptions inv_cont.
Print Assumptions inv_pair_prod.
Print Assumptions unit_ex_wit.
Print Assumptions inv_cont_ex.
Print Assumptions let_elim.
(** examples/LetVarCounter.v *)
Print Assumptions let_force_typed.
Print Assumptions force_types_ex.
Print Assumptions let_var_counter.
(** examples/ForkJoin.v *)
Print Assumptions fj_dftyped.
Print Assumptions fj_term.
Print Assumptions fj_deadlock_free.
Print Assumptions fj_wait_needs.
Print Assumptions fjr_acyc.
Print Assumptions fjr_dftyped.
Print Assumptions fjr_term.
Print Assumptions fjr_deadlock_free.
Print Assumptions fa_acyc.
Print Assumptions fct_dftyped.
Print Assumptions fct_deadlock_free.
Print Assumptions fb_acyc.
Print Assumptions fib_dftyped.
Print Assumptions fib_deadlock_free.
(** static/Inversion.v, the rules of boxes, closures, spawn, link and new *)
Print Assumptions inv_abs.
Print Assumptions inv_app.
Print Assumptions inv_spawn.
Print Assumptions inv_link.
Print Assumptions inv_force.
Print Assumptions inv_box.
Print Assumptions inv_new.
(** static/Skeleton.v *)
Print Assumptions typed_skel.
Print Assumptions sk_occ.
(** examples/Rejects.v *)
Print Assumptions rl_refresh_untyped.
Print Assumptions rx_relink_rejected.
Print Assumptions rx_relink_box_rejected.
Print Assumptions rx_relink_proc_rejected.
Print Assumptions rx_postpone_rejected.
Print Assumptions rx_postpone_proc_rejected.
Print Assumptions rx_delegate_rejected.
Print Assumptions rx_delegate_proc_rejected.
Print Assumptions gp_main_skel.
Print Assumptions guard_pos_rejected.
Print Assumptions guard_pos_proc_rejected.
(** examples/Descent.v *)
Print Assumptions descent.
Print Assumptions prop7.
Print Assumptions prop7_new.
Print Assumptions prop7_fld.
Print Assumptions gen_new_ext.
Print Assumptions rc_grow_no_model.
Print Assumptions rx_chain_rejected.
Print Assumptions rx_chain_proc_rejected.
Print Assumptions wkr_no_model.
Print Assumptions fjr_lf_rejected.
Print Assumptions fjr_lf_proc_rejected.
(** examples/FlagPair.v: two threads on one received flag *)
Print Assumptions fp_unrealizable.
Print Assumptions ptyped_threads.
Print Assumptions fp_static_rejected.
(** examples/RxChain.v: rx-chain at N = ∞ *)
Print Assumptions rc_acyc.
Print Assumptions rc_C_acyc.
Print Assumptions rc_dftyped.
Print Assumptions rc_term.
Print Assumptions rc_deadlock_free.
(** examples/BitProgram.v, examples/MilnerSched.v: ports from the old development *)
Print Assumptions bit_wf_new.
Print Assumptions bit_dftyped.
Print Assumptions bit_deadlock_free.
Print Assumptions ms_wf_new.
Print Assumptions ms_dftyped.
Print Assumptions ms_deadlock_free.
