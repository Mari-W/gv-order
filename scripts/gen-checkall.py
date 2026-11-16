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
        ('liveness/GuardMarks.v', 'okR_rename'), ('liveness/LiveGuardRules.v', 'lsem_later_lam'),
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
        ('lockfree/Fragment.v', 'lfptyped_gptyped'), ('lockfree/Fragment.v', 'fw_lfptyped'),
        ('lockfree/Fragment.v', 'tc_lfptyped'), ('lockfree/Fragment.v', 'sch_lfsource'),
        ('lockfree/Fragment.v', 'kob_checks'), ('lockfree/Fragment.v', 'kob_not_lfptyped'),
        ('lockfree/Fragment.v', 'kob_rank_fails'), ('lockfree/Fragment.v', 'c1_checks'),
        ('lockfree/Fragment.v', 'c1_rank_fails'), ('lockfree/Fragment.v', 'c3_checks'),
        ('lockfree/Fragment.v', 'c3_not_lfptyped'), ('lockfree/Fragment.v', 'tsum_r1_fails'),
        ('lockfree/Fragment.v', 'starve_checks'), ('lockfree/Fragment.v', 'starve_feds'),
        ('lockfree/Fragment.v', 'starve_not_lfptyped'), ('lockfree/Fragment.v', 'r2r_earlier'),
        ('lockfree/Fragment.v', 'rc_r2_fails'), ('lockfree/Fragment.v', 'rc_lfptyped'),
        ('lockfree/Fragment.v', 'rg_r2_fails'), ('lockfree/Fragment.v', 'rg_wf'),
        ('lockfree/Fragment.v', 'rg_lfsource'), ('lockfree/Fragment.v', 'abp_r2'),
        ('lockfree/Fragment.v', 'abp_wf'), ('lockfree/Fragment.v', 'abp_lfsource'),
        ('lockfree/Fragment.v', 'cworld_hold'), ('lockfree/Fragment.v', 'lfsource_lfptyped'),
        ('lockfree/Fragment.v', 'fw_lfsource'), ('lockfree/Fragment.v', 'tc_lfsource'),
        ('lockfree/Fragment.v', 'rc_lfsource'), ('lockfree/Fragment.v', 'kob_cworld_not_wf'),
        ('lockfree/Fragment.v', 'lfsource_lfptyped_at'), ('lockfree/Fragment.v', 'lfsource_budgets'),
        ('lockfree/Fragment.v', 'c3_r2h'), ('lockfree/Fragment.v', 'fw_budgets'),
        ('lockfree/Fragment.v', 'tc_budgets'), ('lockfree/Fragment.v', 'sch_budgets'),
        ('lockfree/Fragment.v', 'rc_budgets'), ('lockfree/Fragment.v', 'rg_budgets'),
        ('lockfree/Fragment.v', 'abp_budgets'), ('lockfree/Fragment.v', 'lc_r2_fails'),
        ('lockfree/Fragment.v', 'relay_roots'),
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
        ('lockfree/LFFuel.v', 'fuel_zero_nosend'), ('lockfree/LFFuel.v', 'fuel_zero_nospawn'),
        ('lockfree/LFFuel.v', 'fuel_zero_nolink'), ('lockfree/LFFuel.v', 'fupd_cap'),
        ('lockfree/LFFuel.v', 'fhand_fin_ok'), ('lockfree/LFFuel.v', 'fcap_finite'),
        ('lockfree/LFFuel.v', 'fuel_send_travel'),
        ('lockfree/LFFuelTyped.v', 'sched_lfsource'),
        ('lockfree/LFFuelTyped.v', 'sync_lfsource'), ('lockfree/LFFuelTyped.v', 'sync_budgets'),
        ('lockfree/LFFuelTyped.v', 'sched_budgets'), ('lockfree/LFFuelTyped.v', 'fw_fuel_floor'),
        ('lockfree/LFFuelTyped.v', 'fw_not_fsem_roots'), ('lockfree/LFFuelTyped.v', 'fw_not_fsem'),
        ('lockfree/LFFuelTyped.v', 'lf_fuel_fundamental_fails')]
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
