# Lock freedom: progress

Branch `lock-freedom`, off `liveness` at 3d9aef9. Plan: lock-freedom-plan.md.
Updated after every stage and every agent result.

| Stage | Status | Rocq files / theorems | make | Admitted | Open problems |
|---|---|---|---|---|---|
| 0  Paper proof (criterion, fuel and rank from the fragment) | done (0a, 0b) | none | n/a | n/a | decisions 1 to 4 of the plan await the author |
| 1  Fair semantics, lock_free, local_progress, lf_criterion | done (f99a2bd) | theories/lockfree/Instr.v (istep_erase, preduction_lift, pred_star_lift), Fair.v (wfair, lock_free, lock_free_reach), TauThread.v (thread_acc), LocalProgress.v (local_progress_ready), Criterion.v (lf_criterion) | passes | 0, no axioms | see log: LPrel alone does not give local progress; linearity facts must come from typing; links still channel steps |
| 2a Link τ costs 0 (relation, guard, liveness proofs, TauThread) | done on the liveness side (31c95da), lockfree widening folded into 2b-core | LiveRelation.v (PALink, LElink, Q-Link), Guard.v (KLink out), LiveGuard.v, LiveBind.v, Internalize, LiveConnect.v (lsteps_link), P-Term | passes | 0, no axioms | thread_acc needs the premise "every link redex has a restricted end" |
| 2b-core Constant world in the core (base and live relation, typing without KTNewEx, examples retyped) | done (de6e13c..6540027) | Typing.v (created), Fundamental.v (created_world, soundness_created), base and live relation (O-New at a known point, Q-Admin and process τ keep W), TauThread.v (links_restricted) | passes, 255 closed | 0, no axioms | SegmentInterleave not retyped (needs a stronger TreeSum box type, author); paper cites t_new_open and si_deadlock_free |
| 2b Rank and fuel in the relation (well-founded W, fuel constant N, per-thread invariant) | done with the placement oracle ω (plan §15) | theories/lockfree/LFRelation.v (oracle, aupd, LFErel, LFconf, LFPrel, LFPrel_down, LFPrel_fuel), LFAdequacy.v (lf_adequacy, lf_adequacy_ex, lf_thread_progress); lf_criterion over npend threads | passes, CheckAll closed | 0, no axioms | the layer is closed-world, stage 3 proves it by typed preservation; or_pick from Prop typings needs computable picks (plan §15.7); controller not done |
| 3a Fragment checks R1, R2′, R4′, wf_world, lfptyped (branch lf-rules) | done (4d74f15, merge into lock-freedom after 2a) | theories/lockfree/Fragment.v: lfptyped, lfsource, fw_lfptyped, tc_lfptyped, sch_lfsource, kob/c1/c3 rejections, tsum_r1_fails | passes, 267 closed | 0, no axioms | Rank on W catches chains only under the constant world; R4′ needs a typing annotation |
| 3  Fundamental theorem, lf_soundness, thread_progress, examples | thread_progress and lock_free_reach_of done (lf-fuel, type-free), the rest waits on plan §14 | ThreadProgress.v (thread_progress, thread_progress_val, stopped_forever), Reach.v (lock_free_reach_of) | passes | 0, no axioms | converse of lock_free_reach_of fails untyped; typed case open |
| 3c Coverage of the literature (plan §12) | done (cc300ce on lf-rules) | Fragment.v (lf_r2r, starve_not_lfptyped, rc_lfptyped, abp_lfsource, rg_lfsource, wgen_rank_wf), examples/ABP.v, examples/GrowRing.v | passes | 0, no axioms | none. The ring gap is closed | | | | author's acceptance criterion |
| L1, L2 Syntactic points (plan §16.6 P1, P2, world fields of §17.8) | done (e767283..b5849ec) | lang (`Chan c b`, `EPt`, `KPay`, `KSucc`, labels on ends, `HeadNew c x`, `fends`, `let_new_at`), types (`TPt`, `konst_ty`, `tenv_ends`, `tenv_fit`), relation (`w_bud`, `w_pay`, V at `TSess` and `TPt`, `fends` in the arrow, O-New at the label's point, `tenv_hd_end`, `selects`), rules (`sem_typed_pt`, `Erel_app_pay`, `Erel_app_succ`), static (`t_pt`, `t_ch`, `created` over constants, `tenv_pol`) | lang to static pass, liveness, lockfree, examples, algorithmic broken until L3 and L4 | 0, no axioms | `wext` does not keep budgets yet (`wext_bud` apart), translations out of the build |
| L3a Syntactic points in the live relation (plan §16.6 P3a) | done (ecd1872..0db07a9) | liveness: labels on ends, E-Fit (`tenv_fit Θ e` in `Ebody` and `LEstep`), O-New at the label's point, `tenv_fit Θ eb` in the arrow and in `Vspawn`, `tenv_hd_end`, V at `TSess` with the bit and at `TPt`, `LErel_app_pay`, `LErel_app_succ`, `lsem_typed_pt`. The twelve listed statements keep their text | liveness passes except GuardEx, GuardCex, LiveKob, LiveGuardFund, LiveGuardProc, which wait on examples (ExampleTools, Forwarder, KobForwarder); LiveGuardFund and LiveGuardProc checked against a stub of `Wpo` | 0, no axioms (stub aside) | lockfree waits on L4 |
| L4a Lock-free soup on syntactic points (plan §16.5, §17.3) | done (ac909ce..1512312), the soup reads environments only | Criterion.v (`lf_run_criterion` over a dependency relation, `lf_criterion` as its instance), LocalProgress.v (`local_progress_gen`), LFSoup.v (`LFconf`, `lf_fuelc`, `LFsoup`, `LFP`, `pupd`, `fstep`, `lfsoup_step`, `lfsoup_run`, `lfsoup_isteps`, `LFP_soup`, `hwaits`, `lfc_local_progress`), LFAdequacy.v (`lf_adequacy`, `lf_adequacy_ex`, `lf_thread_progress`) | passes, CheckAll closed | 0, no axioms | `LFP_term`, `LFP_connect`, `LFP_join` (next stage) |
| L5 Composition of LFP (plan §17.4) | done. `LFP_term` (fdd919e), then FuelE closed under `wbext`, the Σ conjuncts of `LFconf`, `LFP_connect` and `LFP_join` | LFCompose.v (`LFP_term`, `LFP_connect`, `LFP_join`, `wbud_agree`, `mcat`, `tsel`, `held`), LFFuel.v (`wbext`, `FuelE_wbext`, `fsem_wbext`), LFSoup.v (`lf_sig`, `lf_own`) | passes, CheckAll closed | 0, no axioms | none. LFCompose.v takes about 4 minutes, most of it in `set_solver` |
| L6b Links accounted like sends (option 2) | done | LFFuel.v (`flink1` at `w_pay`, `frep`, replacement clause in `Fdef`, `fuel_rep`), LFSoup.v (`flr`, `fuel_link`, `ppts`, `LFsoupAt`, `LFsoupAt_ppts`, `LFP` without π), LFAdequacy.v (`fe_link` through the handed counter), LFCompose.v (`LFP_term` at `tenv_points`) | passes, CheckAll closed | 0, no axioms | C3 argued, no lemma |
| 4  Paper section | not started | | | | |

## Log

- 2026-11-08. Branch created. Plan moved here from the liveness worktree.
  Stages 0 and 1 started in parallel. Stage 1 changes no existing definition.
- 2026-11-08. The first stage 0 agent was cut off by a content filter partway
  through and delivered nothing. Stage 0 is restarted in three smaller parts:
  0a (fuel, rank and the criterion proof), 0b (rules R1 to R4 and the oracle),
  0c (example verdicts). 0a is running.

- 2026-11-08. Stage 0a done: paper proof of lf_criterion, measure (rank,
  fuel, admin depth). Four corrections to the plan (plan §6.1), among them a
  link loop that refreshes fuel, closed by the decision that links cost 0.
  Open: the proof argues classically (plan §6.3). Third uniformity option
  recorded, the constant world (plan §6.4).

- 2026-11-08. Revision approved by the author (relayed): fuel ticks only
  while the partner end is offered (plan §7). The static fragment keeps R2.
  The controller program must type by a direct semantic proof.

- 2026-11-08. Stage 1 done. lf_criterion is closed under the global context,
  constructive (fairness with deadlines, no axiom). Findings:
  (1) `∀ n, LPrel n W ∅ T p` alone does not give local progress. The closed
  process ({a, c}, {recv a, ping c, pong c}) satisfies the relation at every n
  because it never becomes stable, yet recv a waits forever. The false
  statement sits in theories/lockfree/open/LocalProgressLR.v, outside the
  build. Stage 2 must therefore keep a per-thread invariant (each thread's
  gate at its own Θ, one holder per entry, partner entries at dual points),
  as the fundamental theorem's derivation has it, and not rely on the closed
  P relation alone.
  (2) fuel_bound carries two linearity clauses (unique holder, enabled
  pending threads stay enabled) that typing has to supply.
  (3) Links are still channel steps in padmin, admin_at and tR. With link
  cost 0 these widen in TauThread.v and the admin predicate.
  (4) lock_free_reach (Padovani's Def. II.1) is defined, not yet related.

- 2026-11-08. Stage 0b done (plan §10). R3 and its alternative fail (C1, C1′).
  R4 rejects the Forwarder. A link loop with a chatter step defeats R2 (C3).
  Revised: R1, R2′ (with a link clause), R4′ (acyclic forwarding graph), and
  Rank as well-foundedness of W. Rank needs no number, and fuel is one
  constant N per program. Constant world adopted for the lock-free relation
  only. Core adoption goes to the author (three box types get stronger).

- 2026-11-08. Stage 3a done on lf-rules. R1 is strict tail position
  (syntactic). R2′ checks that ends passed to recursion or link are fresh in
  the round. R4′ is backed by a typing annotation, because terms carry no
  types. Finding: in the current calculus the descending chains of C1 and
  KobForwarder sit in box constraints and creation hypotheses, not in W, so
  `wf_world W` alone accepts C1. Rank catches them only under the constant
  world, where those facts become facts of W. This makes the constant world
  essential for stage 2b, not optional.

- 2026-11-08. Stage 3c analysis done (plan §13). All lock-free examples of
  Padovani 2013/2014, PVV14 and Kobayashi 2002 are covered or outside the
  calculus, except the growing ring III.7. Decision: relax R2′ to R2-recv
  with fed slots (fragment check only). Ring, ReceivedChain and the ABP to
  be checked in Rocq. Example (10) of padovani2014deadlock was mislabelled
  in an older store fact, now separated.

- 2026-11-08. Stage 2a done on the liveness side. No approved statement
  changed. Widening the lockfree admin step to links makes thread_acc false
  in the untyped semantics (a thread links a channel it already closed,
  forever). Decision under delegation: lf_criterion gains the premise that
  every link redex of a reachable configuration has a restricted end.
  Typing supplies it, as it supplies the linearity clauses of fuel_bound.
  lf_criterion is a theorem of this branch, not an approved statement.

- 2026-11-08. Stage 3c done in Rocq. The core types Padovani's growing ring
  (GrowRing.v) and the alternating bit protocol (ABP.v). Both pass the
  revised checks with R2-recv, and Rank holds by a pair rank. ReceivedChain is
  now in the fragment. The starving server fails exactly by the fed-slot
  clause. The fuel bound N = (d+1)·2L stays valid on paper. TreeSum fails
  R2-recv as well as R1, so R1′ alone would not admit it. CheckAll lists 396
  Print Assumptions, of which 109 are the commented-out translation entries.
  All 287 active ones are closed.

- 2026-11-09. Stage 2b-core done. The constant world is in the base and
  live relation. KTNewEx is gone, and top-level channels come from creation
  hypotheses (`created`, `soundness_created`). All composition statements
  and the soundness family keep their form. Lemmas that concluded
  `∃ W'` with `wext_fresh` now conclude at the same W. Boxes of FreshBetween,
  FreshMany, FactoryEx and GuardCex got stronger types. SegmentInterleave is
  out of the build: its channel needs facts against the point opened from
  TreeSum's result, which only a stronger TreeSum box type gives (author).
  lf-rules merged (1d0e977). The merge is clean in git but Fragment.v breaks,
  because its closed typings predate the creation hypotheses. A port runs on
  lock-freedom, stage 2b on branch lf-fuel.

- 2026-11-09. Fragment port to the constant world done. Rank is asked of
  `cworld Ψ`, the world where the run of a program over creation hypotheses
  Ψ starts. It places variable k at the constant k and has exactly the facts
  of Ψ, so creation facts are facts of W. `lfsource Ψ t T` takes
  `created (Wpo []) Ψ` and `wf_world (cworld Ψ)`, and `lfsource_lfptyped`
  turns it into `lfptyped (cworld Ψ)` with `cworld Ψ` strict. Forwarder,
  TailCall and ReceivedChain are stated as `∃ W, strict W ∧ lfptyped W …`.
  ABP is retyped over a ladder of rank constraints (θ, then ζ, υ, χ), the
  construction of the CFST scheduler made generic. GrowRing's C₀ is already
  a creation constraint. Every rejection keeps its statement, and
  `kob_cworld_not_wf` shows that Rank rejects the world of Kobayashi's
  forwarder itself. CheckAll lists 404 Print Assumptions, 293 active, all
  closed.

- 2026-11-09. Stage 2b stopped before any Rocq definition (branch lf-fuel,
  plan §14). The constant world fixes W at every index but not the point
  of an entry, which O-New picks inside each level. C1 in a well-founded
  world with a ceiling (TailCall's shape) is then in the relation at every
  index, with fuel 2 and the per-thread invariant, and main starves. Rank
  needs a placement that is the same at every index. Four ways out are in
  plan §14.3. We recommend a placement oracle. Fuel, local progress and
  links_restricted are unaffected.

- 2026-11-09. Type-free results on lf-fuel, independent of the §14 choice.
  `thread_progress` (ThreadProgress.v, plan §9): from lock_free,
  no_tau_divergence and links_restricted, every thread of a weakly fair
  maximal run stops or takes part in a channel step after every position.
  `thread_progress_val` adds threads_safe and gives a value that stays.
  `lock_free_reach_of` (Reach.v): lock_free p implies lock_free_reach p for
  every p, with no premise. The proof lifts process steps backwards and
  builds a fair run with a computable round-robin scheduler. The converse
  fails untyped (a race of two senders on a free channel). For typed
  processes it is open. Both constructive, no axiom.

- 2026-11-09. Stage 2b done with the oracle (plan §15). `LFPrel N ω n` is
  the live relation plus a layer over annotated runs. ω gives the starting
  environments, the point and types at new, and the entries a spawn or a
  send hands over. The splits are a real choice, because Close/Close ends
  differ only in their point. `aupd` computes every successor annotation,
  so the annotation is the same at every index, and every reachable
  annotated configuration satisfies `LFconf n` (live term relation per
  thread, linearity, pairing, at most two entries per channel, a counter at
  0 forces an action on its channel). `lf_adequacy` gives lock freedom in a
  well-founded world, `lf_thread_progress` individual progress. Both are
  closed under the global context. `lf_criterion` now asks its clauses of
  `npend` threads only and local progress at run positions, and
  `local_progress_ready` lets meeting offers enable either side. C1 with a
  ceiling is rejected on paper (§15.6). Stage 3 must prove the layer by
  preservation from typing, and `or_pick` needs picks computable from the
  term, or the relational form of §14.3 option 2 (§15.7).

- 2026-11-09. Stages L1 and L2 of the syntactic points (plan §16.6 P1, P2)
  build through theories/static with no Admitted and no axiom.
  `soundness`, `soundness_source`, `soundness_created`, `fundamental`,
  `adequacy`, `Prel_connect`, `fundamental_join` and `Prel_term` keep their
  statements. Four things differ from §16. `wext` does not keep the budgets.
  The clause `wext_bud` exists on its own, because as a conjunct of `wext`
  it puts an agreement premise on the cut into `Prel_connect` and
  `fundamental_join`, and L3 has to choose where that premise lives.
  `typed_sem_rules` and `typed_pinst` gain the premise `tenv_pol σ Θ`,
  because `pt_inst σ` flips the polarity of a point whose root σ sends to a
  negative point, and the bit of `Chan c b` does not move. Every call with
  Θ ≠ ∅ uses `pvar` or a shift. `created_snoc` adds `(C, [pconst a])` under
  `¬ skn W Ψ (pconst a)`, which equals the plan's
  `bcs_inst (plist [pconst a]) C` because every outer point of C is known
  and so ground. `term_wf` asks `fends e = tenv_ends Θ`. A source program
  over the point variables of `soundness_source` names no point and so
  creates no channel. Programs that create channels go through `created`
  and `soundness_created`. Sharp edge 173.
- 2026-11-09. Stage L3a (plan §16.6 P3a). theories/liveness builds with
  E-Fit, except five files that import broken examples (GuardEx, GuardCex,
  LiveKob directly, LiveGuardFund and LiveGuardProc through GuardEx and
  `Wpo` of ExampleTools). A copy of LiveGuardFund and LiveGuardProc with an
  axiomatic `Wpo` compiles, and `Print Assumptions` closes on the ten
  listed theorems that do not mention `Wpo`. The twelve listed statements
  keep their text. Three things differ from §16.3. The arrow and `Vspawn`
  ask `tenv_fit Θ eb`, not only `fends eb = tenv_ends Θ`, because
  `LVrel_LErel` must give E-Fit and the polarity half of `tenv_fit` is no
  consequence of the ends of the body. The bind lemmas take the fit of their
  frame (`tenv_fit Θ2 (fill_frame f EUnit)`), the fallback of §16.5, and the
  elimination rules of `lsem_rules` and the later judgment take
  `term_wf` of the continuation and `tenv_bipol` of its environment, which
  `typed_live` supplies from the typing (`typed_wf_inst`). `typed_live`
  takes `tenv_pol σ Θ`, as `typed_sem_rules` does after L2.
- 2026-11-09. Stage L4b (plan §17.3, §17.8). theories/lockfree/LFFuel.v
  builds on lang and Worlds alone, with no Admitted and no axiom.
  `FuelE n W π φ e` and `Vfuel` are defined by the course-of-values
  scheme of the base relation (`flevels`). `fupd` computes the successor
  counters from the label. `FuelE_down`, `Vfuel_down`, `lffuel_step`,
  `lffuel_recv`, `lffuel_spawn`, `fuel_cap`, `fuel_wait`, `fupd_cap`,
  `fhand_fin_ok`, `fcap_finite` and four lemmas at counter 0 (no action
  on another end, no send, spawn or link of the end) are proved, and the
  14 CheckAll entries close in a scratch file. The receive floor reads
  `w_pay` at the sender's point, the dual of the receiver's. Receive is
  universal over the points of the incoming ends, as §17.3 has it, and
  this is too strong. A receiver that acts on a received end must meet
  F-Wait at every point the clause offers, so it fails in any world
  where some point has a partner budget ∞ and a budget above the floor.
  The clause stays as written until the author picks a restriction of
  the incoming points. Under delegation only ends with a finite partner
  budget travel. `fin_ok` asks it of the incoming ends, the send clause
  asks it of the payload (`ftravel`, `fuel_send_travel`), and spawn and
  link stay unchanged because no proof needs it there.

- 2026-11-09. Stage L3b of the syntactic points (plan §16.6 P3b, branch
  sp-examples). theories/algorithmic and 53 example files build with no
  Admitted and no axiom. Every top-level `new` names a constant of the
  hypotheses, and `created` adds one constant per channel. A box that
  creates a channel takes its point as a λ-parameter of type `TPt ι`
  and computes the points of its news and of its recursive calls with
  `KPay i` and `KSucc`. Relay, KobForwarder, FactServer, Stream,
  Forwarder, FreshBetween, FreshMany, GrowRing and the box of Factory.v
  take ι, and ReceivedChain, Stream and GrowRing also take a partner
  point ῑ, because x̄[i] = x[i] and no constant computes x̄. FactoryEx
  packs the point value of the hidden point with the handle. The
  ladders of CfstScheduler.v and ABP.v share one ladder over constants
  in CfstTools.v. `ALetNew S x e` erases to `let_new_at (EPt x)` and the
  checker asks x ground. The theorems over a C₀ of point variables
  (`soundness_source`) stay true but say nothing about a program that
  creates a channel, so the examples use `soundness_created`, and the
  rejections of LitRejected.v and CfstDeadlock.v gain a version under
  created hypotheses. Ten files are out of the build with the marker
  `# SYNTACTIC-POINTS: example port pending`. ChoiceTranslate.v and
  ChoiceTranslateEx.v translate `select` into a send that creates a
  channel at the point of the carrier, which the source term does not
  name. SegmentDeleg.v creates a channel at an opened existential, so
  the result of the box tsum needs a `TPt` in its package. ChoiceEnc.v,
  ChoiceNegative.v, DataBranch.v, DataAlternate.v, GrowDeadlock.v,
  SemFlag.v and SemRounds.v were not reached.

- 2026-11-09. Stage L4a (plan §16.5, §17.3). Instr.v, Fair.v,
  TauThread.v, LocalProgress.v and Reach.v build on labels on ends.
  `waits` reads ends (`cdual`, `aends`). `lf_criterion`, `thread_progress`,
  `thread_progress_val`, `lock_free_reach_of` and `lock_free` keep their
  text. `local_progress_ready` keeps its conclusion, and its section
  hypothesis `Hmention` now names the end of the entry, `(k.1, pt_pol
  ek.2) ∈ fends e`, because `waits` does. `links_restricted` asks
  `c.1 ∈ q.1`. LFRelation.v is gone. LFSoup.v holds the soup over a
  configuration with environments per thread id (`LFconf n W Σ T π q A
  U`), read through ends (`tenv_end`). `pupd` reads the step off the
  redexes (`pev_of`). A link removes both ends of the restricted channel
  from π, because the renamed peer lands on the linker's end of the other
  channel, which sits at the peer's point already. `lfconf_step` proves
  the preservation of the live soup from index n + 2 to n for every step,
  a link included, where `LErel_fuse` renames the peer and fuses it with
  the holder of the other peer when one thread holds both. `lfconf_run`
  gives the soup at every index at every position of a run, at π_k, and
  `lfc_local_progress` gives local progress of one soup. The soup asks
  `prim T`, because a main thread that ends as a value holding an end
  starves its partner while the process keeps running. The fuel conjunct
  of `LFsoup` is not preserved at a message. The receive clause of
  `FuelE` continues only for payloads in `Vfuel`, and the send clause
  promises no `Vfuel` of the payload, so a closure sent in a message
  breaks the receiver's conjunct. The fix that suggests itself is a send
  conjunct `Vfuel n' W (mres (fends w) π) (ftick <$> mres (fends w) φ) w`,
  the counterpart of `Vlow` in O-Send. It waits on the author. The fuel
  conjunct also needs `FuelE` invariant under the renaming of a link, a
  lemma of the size of LiveFuse.v. So `lf_adequacy`, `lf_adequacy_ex` and
  `lf_thread_progress` are not proved, LFAdequacy.v is out of the build
  (`# SYNTACTIC-POINTS: lockfree port pending`) and keeps the oracle-era
  instantiation for the port, and `LFP_term`, `LFP_connect` and
  `LFP_join` move to L5.

- 2026-11-09. The remaining examples on syntactic points (branch
  sp-examples2). SemFlag, SemRounds, ChoiceEnc, ChoiceNegative,
  DataBranch, DataAlternate, GrowDeadlock and liveness/LiveKob.v build
  with no Admitted and no axiom. sel_i takes the carrier point x as a
  value before the carrier and creates k by new (x[i]). It sends the end
  at x[i] and keeps the end at x[i]‾, so no constant has to compute x̄
  (`sel_at`, `sel_lit_typed`). The programs of ChoiceEnc, DataBranch and
  DataAlternate create their channels at constants under `created`
  hypotheses (`ch_Ψ`, `lp_Ψ`, `dbf_Ψ`, `dbt_Ψ`, `alt_Ψ`), and the round
  points of the recursive choice are literals over the constant 0
  (`cvc`). A channel value names its end by the polarity of its point,
  so `cc2` takes two ends, and SemFlag states the thread and the partner
  for the points x and y (`sf_thread_at`, `sf_config_at`), with
  `sf_thread` and `sf_config` their instances at the constants 0 and 1.
  SemRounds gives the thread the positive ends and the receivers the
  negative ones. In LiveKob every call passes the server a point value,
  the main thread the literal of 0 and each spawned call `KPay 0` applied
  to the point of its caller, and `kob_tau_diverges` and
  `live_fundamental_false` keep their statements. The rejection theorems
  of ChoiceNegative, SemFlag and DataBranch stay commented out as the
  end-points port left them. ChoiceTranslate, ChoiceTranslateEx and
  SegmentDeleg keep their marker. In liveness/GuardCex.v the box body
  forces its self with no λ in front, so it cannot take a point
  parameter, and `cx_g` creates its channel at the literal of the
  constant 0 with the box's upper point at 0+1 (`cx_bad_typed` asks
  that the world knows 0).

- 2026-11-16. No expression syntax in the relations. E-Fit is gone from
  `Ebody` and `LEstep`, and with it `LErel_S_fit`, the frame fit of
  `LErel_bind`, `LErel_bind_R` and `LErel_bind_guarded`, the fit premise
  of `LErel_det_beta` and `LErel_intro`, `lfr`, and the `term_wf` and
  `tenv_bipol` premises on the continuations of the elimination rules
  (`lsem_elim`, `lsem_later_elim`, `lsem_later_elim_guarded`, the
  `lsem_typed_*`, `lsem_later_*` and `lsr_*` rules of let, let-pair,
  case, pair and application, `typed_wf_inst`). Values keep their
  conditions. The arrow and `Vspawn` ask `tenv_fit Θ eb`, V at `TSess`
  names the end, and E-Abs keeps `term_wf` of its body for the arrow.
  theories/liveness builds with no Admitted and no axiom, and the twelve
  listed statements keep their text. LFSoup.v leaves the build with
  LFAdequacy.v (`# SYNTACTIC-POINTS: lockfree port pending`), unchanged.
  Without `lf_fit` the theorem `lfc_local_progress` is false. `waits`
  reads the ends a term names, so `local_progress_ready` asks that a
  thread names every end its environment holds (`Hmention`), and the
  live relation no longer gives that. At index 1 a thread may hold an end
  it never names and close another channel, and the partner of the
  unnamed end then waits on no thread. `lfconf_step` also loses
  `lf_disj`, which reads terms and fails at a spawn whose context names
  an end of the closure. Both wait on the author.

- 2026-11-09. The fragment on syntactic points and §17.6 (branch
  lf-fragment, stage L6 without `lf_fundamental`). Fragment.v builds
  with no Admitted and no axiom, and its 39 CheckAll entries close.
  `cworld Ψ` is generated over the constants of Ψ (`hroots`) with
  exactly the facts of Ψ (`hyps_lt`), and no instantiation sits in
  between. `lfsource_lfptyped` concludes at T instead of
  `pinst_ty (cst 0) T`, and `rg_wf` and `rg_lfsource` read
  `GrowRing.rg_Ψ`. The checks read the leading λs of a box as point
  parameters, a call as force applied to point values and then to its
  argument (`fhead`), and a point value as fresh. R4′ and the link
  clause of R2′ are one hand-off graph (`hops` with `HFwd`, `HLink` and
  `HBind`, then `box_edges`). A link ⟨u, v⟩ adds edges from the type of
  u to the type of the partner of v and from the type of v to the type
  of the partner of u. An end of a new takes its type from the slot of
  the next round that receives it or its partner. The fragment asks
  `lf_r2h`, R2-recv without the link clause, and `c3_not_lfptyped`
  follows from a self-loop at every annotation of the box
  (`c3_items`). Budgets come from depth (`with_budgets W E L ty_of`
  with `depth`, `gdepth` and `round_len`), and `fw_budgets` to
  `abp_budgets` show that the example worlds carry them. The forwarder
  has d = 1 and L = 2, so the consumer's end gets 4 and every other end
  8, and a payload arrives at fwd with floor 7 and at the consumer with
  floor 3. The ladder of CfstScheduler and ABP is `CfstTools.cl_Ψ`
  (`ladder_wf`). Every rejection keeps its statement. C1 and C3 now
  take their chatter step before the call, because the guard asks the
  first argument of a forced self to perform a primitive and a point
  value performs none. The session type at each point (`ty_of`) is an
  input of the budgets and is not checked against the derivation.
  A leading λ of a box counts as a fresh point parameter only when the
  box type of a typed annotation says TPt (`box_npt`, `r2h_ok`), no
  example needs that annotation, and `lc_r2_fails` shows that a box
  passing a leading channel parameter on unacted is rejected otherwise.

- 2026-11-16. The lock-free soup on environments, and lock-free adequacy
  (L4a). LFSoup.v and LFAdequacy.v are back in the build with no
  Admitted and no axiom, and `lf_adequacy` is closed under the global
  context. The soup reads environments only. `LFconf` asks `tenv_bipol
  (A t)`, disjoint `tenv_ends` of distinct threads, `dom (A t) ⊆ q.1 ∪
  dom Σ`, the points of held ends and a partner for every internal end.
  The fuel conjunct `lf_fuelc` holds FuelE at points `P t` and counters
  `F t` of each thread, whose domains are `tenv_ends (A t)`. `LFP`
  changes form. It fixes the configuration, π, P and F outside the index
  (`∃ q π P F, erase q = p ∧ ∀ n, LFsoup n W Σ T π P F q`), and the
  environments and session types stay per index. The criterion needs one
  holder per end at each position of a run, and its counter `fu` is a
  function. With ownership chosen per index, two indices may put an end
  in different threads, and no proof without choice reads a function off
  them. P outside the index fixes the ends of each thread at every
  index, because `fstep` moves them as the relation moves environments
  (the payload by V, the closure by `Vspawn`, both conditions on values).
  `lfsoup_step` is stated over the configuration, `LFsoup (S (S n)) W ∅
  T π P F q → istep q L q' → LFsoup n W ∅ T (pupd π q L q') (fstep W P F
  q L q').1 (fstep W P F q L q').2 q'`. A link renames every thread by
  `LErel_fuse` and `FuelE_rename`, also a thread that names the removed
  channel in code it never runs.
  `lf_criterion` keeps its statement but no longer fits the judgment. Its
  uniqueness clause reads `waits`, which reads the ends a term names. A
  thread that names the partner end in a discarded argument, as in
  `(λ_. ()) (λ_. close c)`, waits beside the real holder, and the clause
  fails. `lf_run_criterion` now takes the dependency as a relation, and
  `lf_criterion` is its instance at `waits`. Adequacy takes `hwaits`, the
  thread whose points hold the partner end. `local_progress_gen` does
  the same for `local_progress_ready`, whose statement is unchanged.
  `lfc_local_progress` changes form and concludes a chain of `hwaits`.
  The lemma that a held and waited end is named is not needed, because
  no clause of the instantiation reads names. The earlier counterexample
  fails along the run. There s holds o′ at index 1 only, closes n
  channels and goes quiet. Under `LFP` s holds o′ at every index, because
  P lies outside the index, and the criterion follows s. Every channel
  step of s on another end burns the counter of o′, which F-Wait at the
  waiting thread and F-Cap bound by a finite budget. After finitely many
  steps FuelE at a large index allows s no channel step but one on o′.
  If s then blocks on another end, its gate at index 1 puts that end
  below the waited point, and the well-founded order applies. If s ends
  as a value, V at unit asks an empty environment. Internal divergence
  is excluded by `no_tau_divergence`.
  `lf_adequacy W T p : world_wf W → well_founded (w_lt W) → LFP W ∅ T p →
  lock_free p` needs no `strict W`, which follows from its hypotheses.
  `lf_adequacy_ex` quantifies the world, `(∃ W, world_wf W ∧ well_founded
  (w_lt W) ∧ LFP W ∅ T p) → lock_free p`, because §17.8 moved the budgets
  into W. `lf_thread_progress` takes the hypotheses of `lf_adequacy`.
  `LFP_term`, `LFP_connect` and `LFP_join` come next.

- 2026-11-16. Stage L5, composition (LFCompose.v). `LFP_term` is closed
  under the global context. It has the hypotheses of `LPrel_term` and
  three more, all on the environment `Θ = tenv_of Σ ∪ ΘB` of the typing.
  A map π holds the points of exactly the ends of Θ (`dom π = tenv_ends
  Θ` and `tenv_end Θ o = Some x → π !! o = Some x.2`), and `fsem W π t`.
  The soup is thread 0 with environment Θ, points π and counters
  `w_bud W <$> π`. A channel of ΘB is its own partner, read off
  `tenv_dual`. `LFP_connect` and `LFP_join` stopped on two gaps, and
  neither is proved. First, the fuel conjunct does not move to the joined
  world. FuelE reads W at every point it meets, through `w_bud` and
  `w_pay`. These are the points of `new@x`, the points of incoming ends in
  the universal receive clause (`fin_ok`) and the floors at carriers, and
  none of them is restricted to the names of W. `wjoin W1 W2` takes the
  budgets of W1 on the names of W1 and those of W2 elsewhere. A thread of
  the left soup therefore needs `w_bud W1 = w_bud W2` off the names of W1,
  and a thread of the right soup needs it on the names of W1. Agreement at
  the cut gives neither. The thread `new@x; close c` with the root of x
  outside W1 shows it. Under W1 with `w_bud W1 x = None` the new counters
  are ∞ and FuelE holds at every index. Under the join with `w_bud W2 x =
  Some 0` the close fails F-Tick. The live relation reads no budgets, so
  `lf_rel` cannot rule this out, and FuelE has to hold on its own. Two
  repairs would work. Global budgets (`w_bud W1 = w_bud W2` and `w_pay W1
  = w_pay W2`) change the form of the statement. A FuelE closed under
  `wext_bud` by definition, the way `Fdef` is closed under renaming, keeps
  the form, because `wext_bud W1 (wjoin W1 W2)` is `wext_bud_join_l` and
  `wext_bud W2 (wjoin W1 W2)` is agreement on the names W1 and W2 share.
  That second repair changes LFFuel.v and what `fsem` asks. Second,
  `LFconf` does not tie the environments to Σ. A thread of the left soup
  may hold either end of a cut channel c, and nothing makes the right soup
  hold the other one. So the joined soup fails `lf_disj` (both soups may
  hold one end) and `lf_pair` (the partner of a cut end may be missing). Two
  conjuncts on environments would close it, `tenv_end (A t) o = Some x →
  o.1 ∈ dom Σ → Σ !! o.1 = Some x` and `Σ !! c = Some x → ∃ t e, q.2 !! t
  = Some e ∧ tenv_end (A t) (c, pt_pol x.2) = Some x`. Both are trivial at
  Σ = ∅, where `lfsoup_step` and adequacy work, and `LFP_term` meets them.
  The fixed configuration outside the index is no obstacle. The two
  configurations join after shifting the thread ids of the right one, P
  and F join by thread, and π joins on the held ends. Both gaps wait on
  the author.

- 2026-11-16. Stage L5 closed after the two decisions below.
  `LFP_connect` and `LFP_join` are closed under the global context. Their
  one extra hypothesis over `LPrel_connect` and `LPrel_join` is
  `wbud_agree W1 W2`, the agreement of `w_bud` and `w_pay` at every point
  whose root both worlds know. FuelE is now closed under `wbext` by
  definition. `wbext W W'` asks `w_names W ⊆ w_names W'` and `wext_bud W
  W'`. Without the inclusion of names the relation is not transitive, and
  then `FuelE_wbext` fails. `wbext W1 (wjoin W1 W2)` holds always
  (`wbext_join_l`), and `wbext W2 (wjoin W1 W2)` holds under
  `wbud_agree` (`wbext_join_r`). Only the clause lemmas of LFFuel.v unfold
  `Fdef`, and they take W′ = W, so LFSoup.v and LFAdequacy.v need no
  change for it. `fsem` keeps its text and asks more through FuelE.
  `LFconf` gains `lf_sig` and `lf_own`. Both are trivial at Σ = ∅, and
  `lfsoup_step`, `lfsoup_run` and adequacy keep their statements and
  proofs except for the two new fields in `LFconf_down` and
  `LFsoup_relabel`. `LFP_term` keeps its statement. In the proof of
  `LFP_connect` the left threads sit at even ids and the right ones at odd
  ids (`mcat`), and A, U, P and F join by parity (`tsel`). The point map
  is `mrem (held M2 P2) π1 ∪ π2`, so an end held on the right reads π2.
  It lies outside the index because P2 does. A cut end held on the left
  sits at its entry of ΣC by `lf_sig`, and the right soup holds the dual
  entry of ΣC′ by `lf_own`. So the two sides hold different ends of a cut
  channel, and each finds its partner on the other side.

- 2026-11-16. Links accounted like sends (option 2), stage L6b. The link
  clause of `Fobl` is `flink1 W π φ o1 := ∀ k m, π !! o1 = Some k → φ !!
  o1 = Some (Some m) → w_pay W k + 1 ≤ m`, for both ends of the label. So
  the minimum at a point k is `w_pay W k`, and no world field is added.
  `Fdef` gains the replacement clause `∀ φ1, frep W' π' φ' φ1 → E n' W'
  π' φ1 (emap g e)`. `frep W π φ φ1` lets every counter of φ1 either keep
  its value or lie between `w_pay W k` and `w_bud W k` at the point k of
  its end. The clause is universal over counters and reads no term. It
  costs one level, which the soup affords, because a step goes from index
  n + 2 to n. `fuel_rep` is the clause lemma. `FuelE_S_down`,
  `FuelE_wbext`, `FuelE_rename` and `lffuel_step` keep their statements.
  `fsingle` now replaces, before the renaming, the counter of the partner
  of o2 by the linker's counter of o1 minus one, and the partner of o1
  symmetrically (`flr`). In the soup the partner of o2 sits at the point
  of o1 by `lf_pair` and the point equation of `LElink`, so the link
  clause and F-Cap at the linker give exactly the range of `frep`.
  `fuel_link` (LFSoup.v) moves every thread one level down by `fuel_rep`
  and renames at index n. In adequacy, a waiter whose partner the linker
  held now waits on the holder of the other peer, whose counter is m − 1
  (`fe_link`). The bound comes from the link clause, not from the budget.
  `LFP` drops π, `LFP W Σ T p := (∀ n, LPrel n W Σ T p) ∧ ∃ q P F, erase q
  = p ∧ ∀ n, LFsoup n W Σ T P F q`. `LFsoup` takes for π the union of the
  per-thread maps (`ppts`), and `LFsoupAt` is the old soup at a given π.
  `LFsoupAt_ppts` turns a soup at any π into one at `ppts`, because the
  soup reads π only at held ends, where it agrees with P. `prun` is gone,
  and adequacy reads the waited point in `ppts`. `LFP_term` drops the two
  π hypotheses and asks `fsem W (tenv_points (tenv_of Σ ∪ ΘB)) t`. C3 is
  argued in the header of LFFuel.v. The new partner's counter falls by one
  per link and one more per chatter step, nothing refills it, and
  replacement makes FuelE hold at the minimum itself. No lemma for it.

## Decisions

- 2026-11-08, author. Links: the link τ costs 0, so link loops count as
  τ-divergence (plan decision 3). Part of stage 2.
- 2026-11-08, author. SemRounds (G4) after lock freedom.
- 2026-11-08, author. Uniformity (oracle or annotations in types): open,
  the author asked whether the oracle keeps compositionality.

- Open for the author: an axiom of classical logic, or constructive fairness
  with deadlines (plan §6.3).
- Open for the author: the constant world (plan §6.4) as the preferred
  uniformity option.

- 2026-11-08, author. The constant world goes into the core, not only the
  lock-free fragment. FactoryEx, FreshBetween and FreshMany get stronger box
  types.
- 2026-11-08, author. skip-drop and skip-drop-release deleted on GitHub.
  Local tags archive/skip-drop and archive/skip-drop-release keep them.
- 2026-11-09, author. Plan §14: placement oracle ω (option 1). ω fixes
  the starting point of a channel at O-New, independent of the step index.
  Every later point of its ends follows (shifts, payload fields). Points in
  the syntax (`new@x` read off the term) stay a possible later extension,
  which would make ω disappear.
- 2026-11-09, author. Syntactic points replace the oracle ω (after the
  stage 2b findings: the ω layer is not compositional, and ω cannot be read
  off a Prop derivation constructively). Design first as plan §16, then
  implementation.
- 2026-11-09, under delegation. `wext` does not carry budgets (L2
  deviation 1). Budgets matter only for the lock-free layer, so the
  agreement of W1 and W2 on budgets at the cut is a hypothesis of
  `LFP_connect` and `LFP_join` only. Prel_connect, fundamental_join and
  pt_join keep their statements. `LFP_connect` gains this one hypothesis
  over the form of `LPrel_connect`.
- 2026-11-09, under delegation. The arrow and `Vspawn` of the live relation
  ask `tenv_fit Θ eb` (ends and the polarity condition `tenv_bipol`), not
  only `fends eb = tenv_ends Θ` as §16.3 had it. `LVrel_LErel` needs it for
  E-Fit, and typing supplies `tenv_bipol`.
- 2026-11-09, under delegation. Fuel receive clause (L4b obstacle): only
  ends whose partner budget is finite travel in a message (`ftravel`, and a
  conjunct of `fin_ok`). Acting on an end whose partner budget is ∞ can
  starve the actor, which F-Wait forbids anyway, and idle ends are never
  delegated. The receive clause stays universal.
- 2026-11-09, under delegation. The send clause of `Fobl` (LFFuel) gains
  `Vfuel` of the payload at the handed-on counters, the counterpart of
  `Vlow` in O-Send. Without it the receiver's fuel conjunct breaks when a
  closure travels (L4a obstacle). The section hypothesis of
  `local_progress_ready` reading ends follows from the approved change to
  `waits` and is accepted.
- 2026-11-16, author. No syntactic conditions in the relations except on
  values (what the semantics moves). E-Fit removed from expressions.
- 2026-11-16, author. The property definitions over the untyped semantics
  (`waits`, `pending`, `lock_free`) may read which ends a term names, as
  `sentc` does. The relation may not. The soup's term-reading conjuncts get
  environment-level replacements (`dom (A t) ⊆ q.1 ∪ dom Σ`, disjoint
  environments, `tenv_bipol (A t)`, fuel over the ends of `A t`), and
  "held and waited on implies named" is derived in adequacy from fuel and
  liveness across all indices.
- 2026-11-16, author. Accepted: `LFP` fixes the configuration and the
  per-thread point and counter maps (P, F) outside the index
  (`∃ q π P F, erase q = p ∧ ∀ n, LFsoup …`), and adequacy goes through
  `lf_run_criterion` with the ownership dependency `hwaits`; `lf_criterion`
  stays as its instance at `waits`. Next: L5 (composition) and L6
  (`lf_fundamental`).
- 2026-11-16, under delegation. FuelE is closed under extension of the
  budgets (`wbext`: names included, budgets and floors kept on the known
  names), the way `Fdef` is closed under renaming. `LFP_connect` and
  `LFP_join` take `wbud_agree W1 W2` (agreement on `w_bud` and `w_pay` at
  every point whose root both worlds know) in place of agreement at the
  cut. Global budgets are not used.
- 2026-11-16, under delegation. `LFconf` gains two conjuncts on
  environments. An end held of a channel of Σ sits at the entry of Σ
  (`lf_sig`), and every entry of Σ is held by some thread (`lf_own`).
- 2026-11-16, author. Links: option 2. A link is accounted like sending u
  along v. Fuel counters belong to obligations: every hand-over of an
  obligation (send, spawn, link) costs one, only acting refills. The link
  rule becomes "counter(u) − 1 ≥ the minimum at k", the peer's counter for
  v̄ is replaced by counter(u) − 1, and FuelE gains a replacement clause: a
  held end at point k tolerates its counter being lowered by another
  thread's link, down to the minimum at k. Replaces the impossible rule
  "peer budget < counter" (L6a: sched_not_fsem, lf_fuel_fundamental_false).

## Related work hooks

- padovani2014deadlock p2 and p7. Tickets bound delegation and natural
  priorities give the well-founded order. Lock freedom requires both (p7).
  Fuel and rank are their counterparts.
- padovani2014deadlock p15, Def. B.8. The measure is priority, tickets and
  depth. lf_criterion uses rank, fuel and admin depth.
- padovani2014deadlock p8. The lock-freedom proof inducts on a measure of
  priority and tickets. lf_criterion inducts on (rank, fuel).
- balzer2023logical p13. An observation index stays constant under internal
  steps. The live relation does the same with cost-0 internal steps.
- namakonov2026lawyer p2. Step-indexing "is inherently at odds with liveness
  reasoning". The uniformity problem (plan §2, G1) is this conflict, met for
  lock freedom. The choice oracle is our way around it.
- lee2025lilo p1. Stratified propositions replace step-indexing for liveness.
  An alternative to the oracle, not pursued.
