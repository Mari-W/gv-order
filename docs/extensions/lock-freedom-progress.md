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
