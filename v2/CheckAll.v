(** * Every main result of v2 is closed under the global context

    Stages S1, S2, S3 and S6, and the part of S4 done so far
    (docs/redesign/progress.md). [make check] compiles this file and fails if any line below
    reports an axiom. *)

From GV Require Import lang.Harmony lang.ThreadSim lang.ChannelSwap
  lockfree.Reach lockfree.TauThread.
From GV Require Import static.Conservativity static.Weakening static.Renaming static.PointSubst
  examples.ClientServer examples.Cycle examples.FreshBetween examples.FreshMany
  examples.FactoryEx examples.GrowRing.
From GV Require Import relation.Adequacy.
From GV Require Import fuel.FuelSub.
From GV Require Import compat.Rules compat.LiveDF compat.Swap compat.Rename compat.PSwap.

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
Print Assumptions cy_typed.
Print Assumptions fb_typed.
Print Assumptions fm_typed.
Print Assumptions fx_typed.
Print Assumptions rg_typed.
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
(** S6. Fuel: unfolding and the clauses. *)
Print Assumptions FuelE_0.
Print Assumptions FuelE_S.
Print Assumptions Vfuel_eq.
Print Assumptions fuel_val.
Print Assumptions fuel_obl.
Print Assumptions fuel_wait.
Print Assumptions fuel_tick.
Print Assumptions fuel_zero_act.
Print Assumptions fuel_zero_nospawn.
Print Assumptions fuel_zero_nosend.
(** S6. Downward closure, F4 monotonicity, renaming. *)
Print Assumptions FuelE_down.
Print Assumptions Vfuel_down.
Print Assumptions FuelE_mono.
Print Assumptions Vfuel_mono.
Print Assumptions FuelE_rename.
Print Assumptions Vfuel_rename.
(** S6. F2, F3, F5, F6. *)
Print Assumptions FuelE_val.
Print Assumptions FuelE_beta.
Print Assumptions Vfuel_recount.
Print Assumptions Vfuel_age.
Print Assumptions Vfuel_pinst.
Print Assumptions Vfuel_teq.
Print Assumptions Vfuel_sub.
Print Assumptions FuelE_sub.
Print Assumptions FuelE_res_mono.
Print Assumptions FuelE_thread.
Print Assumptions Vfuel_pair.
(** S6. F1 bind, link loops. *)
Print Assumptions FuelE_bind.
Print Assumptions link_tickets_fall.
(** S4. The bind lemma, blindness, groundings. *)
Print Assumptions Erel_sends.
Print Assumptions Erel_bind.
Print Assumptions Vrel_teq.
Print Assumptions Erel_teq_ty.
Print Assumptions Prel_teq.
Print Assumptions Vrel_blind.
Print Assumptions Erel_blind.
Print Assumptions Grel_split.
Print Assumptions sf_den_unionb.
Print Assumptions sem_typed_points.
(** S4. Decision Q14, operator redexes and rules, live ⊆ DF, renaming. *)
Print Assumptions Vrel_exact.
Print Assumptions Vrel_heads.
Print Assumptions Erel_beta.
Print Assumptions Erel_app.
Print Assumptions Erel_send.
Print Assumptions Erel_recv.
Print Assumptions Erel_close.
Print Assumptions Erel_select.
Print Assumptions Erel_branch.
Print Assumptions Erel_link.
Print Assumptions Erel_spawn.
Print Assumptions Erel_new_at.
Print Assumptions Erel_new.
Print Assumptions Erel_force.
Print Assumptions sem_e_send.
Print Assumptions sem_e_recv.
Print Assumptions sem_e_close.
Print Assumptions sem_e_select.
Print Assumptions sem_e_branch.
Print Assumptions sem_e_link.
Print Assumptions sem_e_spawn.
Print Assumptions sem_e_new_at.
Print Assumptions sem_e_force.
Print Assumptions sem_e_new.
Print Assumptions live_e_send.
Print Assumptions live_e_recv.
Print Assumptions live_e_close.
Print Assumptions live_e_select.
Print Assumptions live_e_branch.
Print Assumptions live_e_link.
Print Assumptions live_e_spawn.
Print Assumptions live_e_new_at.
Print Assumptions live_e_force.
Print Assumptions live_e_new.
Print Assumptions dual_unfoldS.
Print Assumptions sequiv_dual.
Print Assumptions live_sub_df.
Print Assumptions Vrel_swap.
Print Assumptions Erel_swap.
(** S4. Decision Q16: maps injective on the held ends. *)
Print Assumptions tstep_det.
Print Assumptions tstep_emap.
Print Assumptions fresh_pull.
Print Assumptions ready_rename.
Print Assumptions Vrel_rename.
Print Assumptions Erel_rename.
(** S4. Renaming of P. *)
Print Assumptions istep_qswap.
Print Assumptions erase_qswap.
Print Assumptions send_split_swap.
Print Assumptions recv_ok_swap.
Print Assumptions recv_env_swap.
Print Assumptions recv_back_swap.
Print Assumptions ready_p_swap.
Print Assumptions Prel_swap.
Print Assumptions csub_fuses.
