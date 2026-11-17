#!/usr/bin/env python3
"""Generate CheckAll.v (outside _CoqProject): Print Assumptions for the main
theorems, every Theorem/Corollary of theories/examples, pgv, pn, mp and
counterexamples, and every Lemma there whose name says deadlock_free, typed,
untypable, underivable or not."""
import re, pathlib
root = pathlib.Path('theories')
main = [('static/Fundamental.v', 'soundness'), ('static/Fundamental.v', 'soundness_source'),
        ('static/Fundamental.v', 'soundness_created'),
        ('static/Fundamental.v', 'fundamental'), ('static/Fundamental.v', 'fundamental_proc'),
        ('relation/LogicalRelation.v', 'adequacy'), ('rules/SemanticRules.v', 'sem_rules_fundamental'),
        ('liveness/LiveAdequacy.v', 'live_adequacy'), ('liveness/LiveAdequacy.v', 'live_runs'),
        ('liveness/LiveAdequacy.v', 'live_finite_runs'), ('liveness/LiveRules.v', 'LErel_app_lam'),
        ('liveness/LiveRules.v', 'LErel_force'), ('liveness/LiveRules.v', 'LVrel_box_lob'),
        ('liveness/LiveRules.v', 'LErel_spawn'), ('liveness/LiveKob.v', 'kob_tau_diverges'),
        ('liveness/LiveKob.v', 'live_fundamental_false'),
        ('liveness/LiveBind.v', 'LErel_bind'), ('liveness/LiveBind.v', 'LErel_bind_R'),
        ('liveness/LiveConsts.v', 'LErel_app_noforce'), ('liveness/LiveTermRules.v', 'LErel_app'),
        ('liveness/LiveTermRules.v', 'lsem_rules_fundamental'),
        ('liveness/LiveGuard.v', 'gd_noret'), ('liveness/LiveGuard.v', 'LErel_bind_guarded'),
        ('liveness/LiveGuard.v', 'lsem_typed_box_live'), ('liveness/LiveGuard.v', 'lsem_later_letu_guard'),
        ('liveness/GuardEx.v', 'fw_gstyped'), ('liveness/GuardEx.v', 'tc_gstyped'),
        ('liveness/GuardEx.v', 'kob_not_guarded'),
        ('liveness/GuardCex.v', 'cx_gptyped0'), ('liveness/GuardCex.v', 'cx_tau_diverges'),
        ('liveness/GuardCex.v', 'live_guarded_unrepaired_false'), ('liveness/GuardCex.v', 'cx_not_guarded'),
        ('liveness/GuardCex.v', 'guarded_examples'),
        ('liveness/LiveGuard.v', 'lsem_later_box_live'), ('liveness/GuardMarks.v', 'okv_okR'),
        ('liveness/GuardMarks.v', 'okR_rename'), ('liveness/GuardRules.v', 'okM_iff'),
        ('liveness/GuardRules.v', 'gbody_iff'), ('liveness/GuardRules.v', 'guarded_iff'),
        ('liveness/GuardRules.v', 'gtyped_iff'), ('liveness/GuardRules.v', 'gptyped_iff'),
        ('liveness/LiveGuardRules.v', 'lsem_later_lam'),
        ('liveness/LiveGuardRules.v', 'lsem_later_app_lam'), ('liveness/LiveGuardRules.v', 'lsem_later_app_force'),
        ('liveness/LiveGuardFund.v', 'typed_live'), ('liveness/LiveGuardFund.v', 'live_fundamental_guarded'),
        ('liveness/LiveGuardFund.v', 'live_fundamental_guarded_closed'),
        ('liveness/LiveGuardFund.v', 'fw_live'), ('liveness/LiveGuardFund.v', 'tc_live'),
        ('liveness/LiveRenaming.v', 'LPrel_swap'), ('liveness/LiveRenaming.v', 'LPrel_swap_restricted'),
        ('liveness/LiveJunk.v', 'LPrel_junk'), ('liveness/LiveFuse.v', 'LVrel_fuse'),
        ('liveness/LiveFuse.v', 'LErel_fuse'), ('liveness/LiveEconv.v', 'LErel_econv'),
        ('liveness/LiveEconv.v', 'LPrel_sconv'), ('liveness/LiveInternalize.v', 'LPrel_internalize'),
        ('liveness/LivePConnect.v', 'LPrel_connect'), ('liveness/LivePConnect.v', 'LPrel_join'),
        ('liveness/LivePTerm.v', 'LPrel_term'), ('liveness/LivePTerm.v', 'LPrel_indep'),
        ('liveness/LiveGuardProc.v', 'live_fundamental_proc'), ('liveness/LiveGuardProc.v', 'live_soundness'),
        ('liveness/LiveGuardProc.v', 'live_soundness_term'), ('liveness/LiveGuardProc.v', 'live_soundness_source'),
        ('liveness/LiveGuardProc.v', 'fw_live_sound'), ('liveness/LiveGuardProc.v', 'tc_live_sound'),
        ('liveness/LiveGuardProc.v', 'fa_live_sound'), ('liveness/LiveGuardProc.v', 'fac_live_sound'),
        ('lockfree/Instr.v', 'istep_erase'), ('lockfree/Instr.v', 'preduction_lift'),
        ('lockfree/Instr.v', 'pred_star_lift'), ('lockfree/TauThread.v', 'thread_acc'),
        ('lockfree/Criterion.v', 'lf_criterion'), ('lockfree/LocalProgress.v', 'local_progress_ready'),
        ('lockfree/ThreadProgress.v', 'thread_progress'), ('lockfree/ThreadProgress.v', 'thread_progress_val'),
        ('lockfree/ThreadProgress.v', 'stopped_forever'), ('lockfree/Reach.v', 'lock_free_reach_of'),
        ('lockfree/Rank.v', 'cworld_hold'), ('lockfree/Rank.v', 'kob_cworld_not_wf'),
        ('lockfree/Rank.v', 'kob_rank_fails'), ('lockfree/Rank.v', 'c1_rank_fails'),
        ('lockfree/Rank.v', 'fw_wf'), ('lockfree/Rank.v', 'tc_wf'), ('lockfree/Rank.v', 'cs_wf'),
        ('lockfree/Rank.v', 'rc_wf'), ('lockfree/Rank.v', 'rg_wf'), ('lockfree/Rank.v', 'abp_wf'),
        ('lockfree/Rank.v', 'sched_wf'), ('lockfree/Rank.v', 'sync_wf'),
        ('lockfree/LFTyped.v', 'lf_fundamental'), ('lockfree/LFTyped.v', 'lf_soundness'),
        ('lockfree/LFTyped.v', 'lfptyped_gptyped'), ('lockfree/LFTyped.v', 'lfptyped_join'),
        ('lockfree/LFTyped.v', 'fuel_unknown_zero'),
        ('lockfree/LFSoup.v', 'LFsoup_down'), ('lockfree/LFSoup.v', 'lfsoup_step'),
        ('lockfree/LFSoup.v', 'lfsoup_run'), ('lockfree/LFSoup.v', 'lfc_local_progress'),
        ('lockfree/LFAdequacy.v', 'lf_adequacy'), ('lockfree/LFAdequacy.v', 'lf_adequacy_ex'),
        ('lockfree/LFAdequacy.v', 'lf_thread_progress'), ('lockfree/LFCompose.v', 'LFP_term'),
        ('lockfree/LFCompose.v', 'LFP_connect'), ('lockfree/LFCompose.v', 'LFP_join'),
        ('lockfree/LFFuel.v', 'FuelE_wbext'),
        ('lockfree/LFFuel.v', 'FuelE_down'), ('lockfree/LFFuel.v', 'Vfuel_down'),
        ('lockfree/LFFuel.v', 'fuel_cap'), ('lockfree/LFFuel.v', 'fuel_wait'),
        ('lockfree/LFFuel.v', 'lffuel_step'), ('lockfree/LFFuel.v', 'lffuel_recv'),
        ('lockfree/LFFuel.v', 'lffuel_spawn'), ('lockfree/LFFuel.v', 'fuel_zero_act'),
        ('lockfree/LFFuel.v', 'fuel_zero_nospawn'), ('lockfree/LFFuel.v', 'fuel_val'),
        ('lockfree/LFFuel.v', 'fupd_cap'), ('lockfree/LFFuel.v', 'FuelE_tk_mono'),
        ('lockfree/LFFuel.v', 'FuelE_rename'), ('lockfree/LFFuel.v', 'link_tickets_fall'),
        ('lockfree/LFAdequacy.v', 'ksum_step'),
        ('lockfree/LFFuel.v', 'fchild_fin_ok'), ('lockfree/LFFuel.v', 'fcap_finite'),
        ('lockfree/LFFuel.v', 'fuel_send_val'), ('lockfree/LFFuel.v', 'fuel_frame'),
        ('relation/CostTypes.v', 'spawn_split'), ('relation/CostTypes.v', 'link_split'),
        ('relation/CostTypes.v', 'seq_sound'), ('relation/CostTypes.v', 'link_loop_no_tix'),
        ('relation/CostTypes.v', 'cst_any'),
        ('static/CostTyping.v', 'tle_check'), ('static/CostTyping.v', 'cst_refl'),
        ('static/CostTyping.v', 'ctyped_mono'), ('static/CostTyping.v', 'cagex_zero'),
        ('static/CostTyping.v', 'cage_env_zero'),
        ('examples/CostEx.v', 'sync_ctyped'), ('examples/CostEx.v', 'tc_ctyped'),
        ('examples/CostEx.v', 'fw_ctyped'), ('examples/CostEx.v', 'rc_ctyped'),
        ('examples/CostEx.v', 'abp_ctyped'), ('examples/CostEx.v', 'cs_ctyped'),
        ('examples/CostEx.v', 'sched_ctyped'), ('examples/CostEx.v', 'cb_ctyped'),
        ('examples/CostEx.v', 'ring_ctyped'), ('examples/CostEx.v', 'rg_ctyped'),
        ('lockfree/LFFuel.v', 'fuel_send_travel'),
        ('lockfree/LFFuel.v', 'fuel_send_held'), ('lockfree/LFFuel.v', 'fuel_spawn_held'),
        ('lockfree/LFFuel.v', 'fuel_link_held'),
        ('relation/CostTypes.v', 'cst_refl'), ('relation/CostTypes.v', 'cst_trans'), ('relation/CostTypes.v', 'cst_cadd'), ('relation/CostTypes.v', 'pfits_at_mono'), ('relation/CostTypes.v', 'pfits_at_cst'), ('relation/CostTypes.v', 'pfitpt_at_cst'),
        ('lockfree/LFFuelBind.v', 'FuelE_bind'), ('lockfree/LFFuelBind.v', 'Fobl_bind'), ('lockfree/LFFuelBind.v', 'fkont_tick'), ('lockfree/LFFuelBind.v', 'fkont_rename'), ('lockfree/LFFuelBind.v', 'fupd_union'), ('lockfree/LFFuelBind.v', 'FuelE_val'), ('lockfree/LFFuelBind.v', 'FuelE_beta'), ('lockfree/LFFuelBind.v', 'head_beta_det'), ('lockfree/LFFuelBind.v', 'FuelE_mono'), ('lockfree/LFFuelBind.v', 'FuelE_frame_mono'), ('lockfree/LFFuelBind.v', 'FuelE_reserve_mono'), ('lockfree/LFFuelBind.v', 'FuelE_ty_mono'), ('lockfree/LFFuelBind.v', 'FuelE_thread'), ('lockfree/LFFuelBind.v', 'Vfuel_sub'), ('lockfree/LFFuelBind.v', 'Vfuel_wbext'), ('lockfree/LFFuelBind.v', 'Vfuel_rename'), ('lockfree/LFFuelBind.v', 'Vfuel_recount'), ('lockfree/LFFuelBind.v', 'Vfuel_minus'), ('lockfree/LFFuelBind.v', 'pfits_wbext'), ('lockfree/LFFuelBind.v', 'pfitpt_wbext'), ('lockfree/LFFuelBind.v', 'pfits_node'), ('lockfree/LFFuelBind.v', 'pfits_snd'), ('lockfree/LFFuelBind.v', 'pfits_rcv'), ('lockfree/LFFuelBind.v', 'pfits_sel'), ('lockfree/LFFuelBind.v', 'pfits_bra'), ('lockfree/LFFuelBind.v', 'pfits_sub'), ('lockfree/LFFuelBind.v', 'Vfuel_refill'), ('lockfree/LFFuelBind.v', 'Vfuel_pair'), ('lockfree/LFFuelBind.v', 'renk_union_split'), ('lockfree/LFFuelBind.v', 'FuelE_fcap_ext'),
        ('lockfree/CostFund.v', 'ctyped_csem'), ('lockfree/CostFund.v', 'ctyped_fsem'), ('lockfree/CostFund.v', 'ctyped_cfacts'), ('lockfree/CostFund.v', 'sem_bind0'), ('lockfree/CostFund.v', 'sem_bind1'), ('lockfree/CostFund.v', 'sem_bind2'), ('lockfree/CostFund.v', 'c_unit_sem'), ('lockfree/CostFund.v', 'c_pt_sem'), ('lockfree/CostFund.v', 'c_var_sem'), ('lockfree/CostFund.v', 'c_ch_sem'), ('lockfree/CostFund.v', 'c_abs_sem'), ('lockfree/CostFund.v', 'c_app_sem'), ('lockfree/CostFund.v', 'c_pair_sem'), ('lockfree/CostFund.v', 'c_letu_sem'), ('lockfree/CostFund.v', 'c_letp_sem'), ('lockfree/CostFund.v', 'c_inj1_sem'), ('lockfree/CostFund.v', 'c_inj2_sem'), ('lockfree/CostFund.v', 'c_case_sem'), ('lockfree/CostFund.v', 'c_box_sem'), ('lockfree/CostFund.v', 'c_force_sem'), ('lockfree/CostFund.v', 'c_new_sem'), ('lockfree/CostFund.v', 'c_pay_sem'), ('lockfree/CostFund.v', 'c_succ_sem'), ('lockfree/CostFund.v', 'c_send_sem'), ('lockfree/CostFund.v', 'c_recv_sem'), ('lockfree/CostFund.v', 'c_close_sem'), ('lockfree/CostFund.v', 'c_sel_sem'), ('lockfree/CostFund.v', 'c_bra_sem'), ('lockfree/CostFund.v', 'c_link_sem'), ('lockfree/CostFund.v', 'c_spawn_sem'), ('lockfree/CostFund.v', 'c_spawnlam_sem'), ('lockfree/CostFund.v', 'c_sub_sem'), ('lockfree/CostFund.v', 'c_weak_sem'), ('lockfree/CostFund.v', 'c_contract_sem'), ('examples/CostFsem.v', 'sync_fsem'), ('examples/CostFsem.v', 'cb_fsem')]
items = []
def mod(p): return 'LRGV.' + str(p.with_suffix('')).replace('/', '.')
def strip_comments(t):
    # drop (* ... *) comments, nested, so that commented-out theorems are skipped
    out, depth, i = [], 0, 0
    while i < len(t):
        if t.startswith('(*', i): depth += 1; i += 2; continue
        if depth and t.startswith('*)', i): depth -= 1; i += 2; continue
        if not depth: out.append(t[i])
        elif t[i] == '\n': out.append('\n')
        i += 1
    return ''.join(out)
for f, n in main:
    items.append((mod(pathlib.Path(f)), n))
for d in ['examples', 'pgv', 'pn', 'mp', 'counterexamples']:
    for f in sorted((root / d).rglob('*.v')):
        rel = f.relative_to(root)
        for m in re.finditer(r"^(Theorem|Corollary|Lemma)\s+([A-Za-z0-9_']+)", strip_comments(f.read_text()), re.M):
            kind, n = m.group(1), m.group(2)
            if kind != 'Lemma' or re.search(r'deadlock_free|untypable|underivable|_typed|_not_', n):
                items.append((mod(rel), n))
# Files of theories/ that _CoqProject leaves out (branch no-eq: the
# translations that still need ≡). Their entries stay, commented out.
lines = pathlib.Path('_CoqProject').read_text().splitlines()
built = {mod(pathlib.Path(l.strip()).relative_to('theories'))
         for l in lines if l.strip().endswith('.v') and not l.strip().startswith('#')}
# Files left out under the constant world (sharp edges 172), with their own marker.
const_world = {'LRGV.examples.cfst.SegmentInterleave'}
# Translations taken out of the build for syntactic points (sharp edges 173).
SP = '# SYNTACTIC-POINTS: translation port pending '
synpts = {mod(pathlib.Path(l[len(SP):].strip()).relative_to('theories'))
          for l in lines if l.startswith(SP)}
# Examples taken out of the build for syntactic points (stage L3b).
SPE = '# SYNTACTIC-POINTS: example port pending '
synexs = {mod(pathlib.Path(l[len(SPE):].strip()).relative_to('theories'))
          for l in lines if l.startswith(SPE)}
# Lock-freedom files taken out of the build for syntactic points: the
# adequacy (stage L5, fuel) by a marker.
SPL = '# SYNTACTIC-POINTS: lockfree port pending '
synlf = {mod(pathlib.Path(l[len(SPL):].strip()).relative_to('theories'))
         for l in lines if l.startswith(SPL)}
def why(m):
    if m in synlf: return 'SYNTACTIC-POINTS: lockfree port pending'
    if m in const_world: return 'CONST-WORLD: retyping pending'
    if m in synpts:
        return 'SYNTACTIC-POINTS: translation port pending'
    if m in synexs:
        return 'SYNTACTIC-POINTS: example port pending'
    return 'NO-EQ: translation pending'
mods = sorted({m for m, _ in items})
out = ['(* generated by scripts/gen-checkall.py; not part of _CoqProject *)']
for m in mods:
    out.append(f'Require {m}.' if m in built else f'(* {why(m)}  Require {m}. *)')
for m, n in items:
    out.append(f'Print Assumptions {m}.{n}.' if m in built
               else f'(* {why(m)}  Print Assumptions {m}.{n}. *)')
pathlib.Path('CheckAll.v').write_text('\n'.join(out) + '\n')
print(len(items), 'theorems')
