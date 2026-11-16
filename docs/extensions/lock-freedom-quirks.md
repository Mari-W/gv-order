# Lock freedom: quirks, weak justifications, and what could be lifted

State of branch `lock-freedom` on 2026-11-16, after L5 and the link redesign,
with L6 (`lf_fundamental`) running. Each entry says what is odd, why it is
there, and what would lift it. Entries marked *artefact* exist for the proof
and not for the idea. Entries and additions marked *(audit)* come from the
read-only sweep of theories/lockfree and theories/liveness at d91fa5c.
Sections F to J are new, and the cleanup items they imply are Part 4 of
lock-freedom-cleanup.md.

## A. The relations

**A1. Value-level syntactic conditions.** A closure's environment holds
exactly the ends it mentions, a channel value is `Chan c b` with exactly
that entry, a box mentions no channel, and the payload of a send owns
exactly `fchans w ∩ p.1`. They mirror the semantics, which extrudes scope by
syntax (`sentc` removes `fchans v` from C at an external send). Justified,
but it is the one place where the relation reads terms. Lift: no scoping in
the semantics (drop C), scope only in the relation through Σ and Θ, and
ownership validated by use. That changes every process rule and the paper's
calculus.

**A2. The polarity bit `Chan c b`.** *Artefact.* Both ends of a channel share
the name c, so the bit says which end a value is, and it has to agree with
the polarity of the end's point (`pt_pol k = b`). Lift: distinct names for
the two ends (c and c̄). The bit and the agreement disappear, and so does
`tenv_bipol`. Addition (audit). The bit costs more than the agreement.
`tenv_end` picks an entry by two nested `bool_decide (pt_pol _ = o.2)`
tests, `typed_sem_rules` and `typed_pinst` carry the premise `tenv_pol σ
Θ` (sharp edges 173), `LFconf` carries `lf_bipol`, `fact` and `pev_upd`
rewrite the end to `(o.1, false)` and `(o.1, true)` after a choice, and 18
of the 71 lines of `LFP_term` read `pt_pol`, `bool_decide`, `tenv_end` or
`tenv_bipol`.

**A3. Two kinds of waiting.** `waits` (Fair.v) reads which ends a term
names. Adequacy cannot use it, because a thread like `(λ_. ()) (λ_. close c)`
names c without owning it. So adequacy runs `lf_run_criterion` with
`hwaits`, waiting by ownership, and `lf_criterion` survives only as the
instance at `waits`. The definitions are allowed to read syntax (author,
2026-11-16), yet the proof needs the semantic one. Lift: define `waits` by
ownership in the first place, if the property can be stated over an
ownership annotation of runs.

**A4. Base and live relation are two copies.** *Artefact of Rocq.* The live
relation copies the base clauses and changes one rule (internal steps
inductive at the same index). Every change to the base relation is redone
in the live one, as L2 and L3a showed. Lift: one relation with a switch.
Size (audit). The live side is about 6,500 lines against about 9,600 for
the base files it mirrors. LiveInternalize has 1,301 against Internalize
1,895, LiveJunk 664 against JunkRenaming 3,034, LivePTerm 559 against
PTerm 1,032, LiveConnect and LivePConnect 1,895 against ConnectSteps,
ConnectCut and PConnect 1,909, LiveBind 614 against Bind 566, LiveTermRules
905 against TermRules 1,199. The three step-indexed fixpoints (`levels`,
`llevels`, `flevels`) are a third copy of the same construction (H6).

**A5. Links cost 0.** A link is an internal step (author, 2026-11-08), so a
link loop is τ-divergence. Fine, but it makes link a primitive with its own
cost rule in liveness, in fuel (A10) and in the fragment (B5).

**A6. `LFP` is two conjuncts.** `(∀ n, LPrel n …) ∧ ∃ q P F, ∀ n, LFsoup …`.
Every thread of the soup is already in the live relation, so the first
conjunct may be redundant. Composition uses it (`LPrel_connect`), so it
stays until someone checks. Correction (audit). Adequacy uses it as well.
`lf_adequacy` and `lf_thread_progress` take `no_tau_divergence` from
`live_no_tau_divergence W T p (proj1 HP)`, so dropping the conjunct needs
a lemma from the soup to `LPrel` (G1) or a per-thread proof of no
τ-divergence from `lf_rel`.

**A7. The soup fixes q, P and F before the index.** *Artefact.* q is an
instrumented configuration with thread identifiers, P the point map per
thread, F the counters per thread. P and F are determined by the run
(syntactic points, value conditions), so a determinism lemma would make them
derived. They are existential because extracting one function from "for
every n there is an environment" needs that lemma or a choice principle.
Thread identifiers are an artefact of the instrumented semantics. Lift: the
determinism lemma, then P and F are read off the environments.

**A8. `prim T` and `lf_sig`, `lf_own` in the soup.** `prim T` excludes a main
thread that ends as a value while holding an end. `lf_sig` and `lf_own` tie
the environments to Σ and are trivial for closed programs. Both are honest
side conditions, yet they make the definition longer than its idea.

**A9. Index loss.** A soup step goes from index n + 2 to n, and the
replacement clause costs one more level. Harmless for `∀ n`, ugly to state.

**A10. Fuel sits on ends, not on obligations.** The idea is that a counter
belongs to an obligation ("someone waits for this end"), and every hand-over
(send, spawn, link) costs one. The mechanization keeps counters per held
end, so a link *overwrites* the peer's counter, and every end at point k has
to tolerate such an overwrite down to `w_pay W k` (`frep`). Lift: make
obligations explicit in the soup (waiter, serving end, counter), with the
per-thread predicate reading them.

**A11. Two budget maps, one keyed oddly.** The world has `w_bud` (cap and
refill) and `w_pay` (floor of a delegated end). The floor is read at the
*sender's* point, because sender and receiver sit at dual points. The link
minimum reuses it at u's point. Lift: key the floor on the carrier channel's
identity rather than on a point, if the world can speak about it, or fold
both maps into one budget per root.

**A12. Budget ∞ and `ftravel`.** Ends nobody waits on get ∞, which replaces
"fuel ticks only while the partner offers" (§7). Only ends with a finite
partner budget may travel in a message (`ftravel`). The restriction is
sound (acting on an ∞ end can starve) but excludes delegating idle ends.
Lift: let ∞ ends travel and forbid only *acting* on them, if F-Wait alone
carries the argument. Addition (audit). The static fragment never uses ∞
(`bud_at` is `Some ((gdepth E + 2) * L)` at every point), so for every
program of the fragment F-Wait, `ftravel` and the fifth conjunct of
`fin_ok` are vacuous. That conjunct is `ftravel` restated over the
incoming map. The only world with ∞ is the one of `lfsource_lfptyped`
(`λ _, None` everywhere), where F-Wait forbids every action. So ∞ serves
no proved result today.

**A13. Kripke closure needs name inclusion.** `FuelE` is closed under
`wbext W W'`, which asks W′ to know W's names and agree on their budgets.
Bare budget agreement is not transitive. Composition then asks `wbud_agree
W1 W2` on *every shared name*, not only at the cut. Lift: if FuelE only ever
reads budgets at points the world knows, agreement at the cut suffices.

**A13b. Replacement minimum against the send floor (open, 2026-11-16).**
The replacement clause lets another thread's link lower a counter to the
floor at the end's *own* point, while a send asks counter − 1 ≥ the floor
at the *carrier's* point. A delegated end sits at a payload point of its
carrier, so with floors keyed on roots both floors are equal and the send
fails. The Forwarder is in the fragment and fails the fuel predicate at
every world `with_budgets` builds (`fw_not_fsem`, `lf_fuel_fundamental_fails`
in LFFuelTyped.v). Two candidate repairs. Exempt from replacement every end
whose partner the same thread holds, because no other thread can link it
(environment-level). Let floors grow along payload fields, so a payload's
own floor exceeds its carrier's (fragment budgets). Not decided.

**A14. `well_founded (w_lt W)` beside `world_wf W`.** Two premises about the
world, one structural and one for rank. Could be one record field of a
"lock-free world". Addition (audit). There are three names for nearly the
same thing. `world_wf` is the structural record (Worlds.v), `strict W` is
`world_wf W` plus irreflexivity, and `wf_world W` (Fragment.v) is
`well_founded (w_lt W)`. `world_wf` and `wf_world` differ only in word
order. Adequacy turns the last two into the second (`strict_of`), and the
step lemmas take `strict`. Rename `wf_world` to `rank_wf` at least.

## B. The static fragment

**B1. A pile of syntactic checks.** The guard, R1 (recursion in tail
position), R2-recv (ends passed to a call were acted on in the round or
are fed slots), the hand-off graph (forwards and links), the root graph,
`wf_world (cworld Ψ)`, and the annotation `ann` backed by typing
derivations. Each closes a counterexample. Together they are a sufficient
condition, not a characterisation. Lift: semantic premises wherever the
proof allows. The controller already types only by a direct semantic proof.

**B2. The root graph and its restrictions.** Floors are keyed on the *root*
of a point because the term records roots (syntactic points) and nothing
else about types. A box that forwards must keep its slots stable from round
to round (`stab`) and must not be called from inside a box (`foreign`). A
received end passed into a call leaves the program without a root graph
(`troots`, `bleak`). No example is affected, but the rules exist only to
make the root graph computable.

**B3. The stretch bound.** L = 2 · `seg_len`, with `scost` charging one unit
for a channel step, a spawn and a link, inlining forced non-recursive boxes,
and ending a segment at any other force. The factor 2 ("a stretch spans at
most two segments") was only argued when written and is being proved in L6.
Budgets are uniform, (d + 2)·L for every end, and floors fall by L per level
of the root graph. Correction (audit). L6 stopped on the forwarder
counterexample (`lf_fuel_fundamental_fails`), so the factor 2 is still
only argued. No lemma relates `scost` to the steps of a thread.

**B7. Two graphs over the same hand-offs (audit).** `lfptyped` asks the
hand-off graph (`lf_r4`, `r4_ok`), whose nodes are erased session types
read from the annotation `ann`. `lfsource` asks the same graph and also
the root graph (`root_ok`), whose nodes are root names read off the term.
Both trace carriers through binders, each with its own carrier type and
helpers. The first has `car`, `ecar`, `pcar`, `ccar` and `mentions`, the
second `tcar`, `tecar`, `tpcar`, `tccar` and `tmentions`. The budgets come
only from the root graph, so `lfptyped` alone gives no budgets, and the
world of `lfsource_lfptyped` carries ∞ everywhere. Lift: one carrier
analysis with roots as nodes, and the self-loop rule of B5 dropped.

**B8. Three variants of R2 stay in the file (audit).** `lf_r2` (R2′, the
stricter rule), `lf_r2r` (R2-recv with the link clause) and `lf_r2h`
(R2-recv without it) are all instances of `r2x`. Only `lf_r2h` enters
`lfptyped` and `lfsource`. The other two serve the coverage theorems of
stage 3c (`rc_r2_fails`, `rg_r2_fails`, `abp_r2`, `r2r_earlier`), which
compare rules nobody uses any more.

**B9. Examples inside the theory file (audit).** Fragment.v imports nine
example files and proves the fragment facts of the forwarder, the tail
call, the scheduler, KobForwarder, C1, C3, the received chain, the growing
ring and ABP, about 560 of its 2,102 lines. LFFuelTyped.v holds the facts
of the scheduler and of sync next to the typed fuel interpretation. The
examples' own files (theories/examples) carry no lock-freedom fact. Lift:
an examples/LockFree.v that imports Fragment.v.

**B4. Leading point parameters.** A box's leading λs count as fresh point
parameters only when its annotated type says `TPt`. The checks read the
annotation, and the annotation needs a typing derivation (`r2h_ok`). A
syntactic check leaning on a semantic certificate.

**B5. Links inside boxes are rejected.** The type hand-off graph gives every
link inside a box a self-loop. That was the old way to close C3. With links
accounted like sends (option 2), fuel closes C3 itself, so the self-loop
rule may now reject more than needed. Lift: drop it and let the link
accounting do the work.

**B6. Recursion with a point argument needs a primitive first.** The guard
asks the first argument of a forced self to perform a primitive, and a point
value performs none. C1 and C3 had to be rewritten so the chatter comes
before the call. GuardCex could not take a point parameter at all.

## C. Syntactic points and the constant world (calculus level)

**C1. Points in terms.** `new` takes a point value, boxes take points as
λ-arguments of type `TPt ι`, and `KPay`, `KSucc` build points at runtime.
Needed so that O-New does not choose a point inside each index (§14). The
runtime never uses the points. They exist for the proof. Correction
(audit). The runtime reads one bit of them. `head_step` for `new` names
the two ends `Chan c (pt_pol x)` and `Chan c (negb (pt_pol x))`, so the
polarity bit of A2 is computed from the point at runtime, and `KPay` and
`KSucc` are β steps. With distinct end names (R2) the runtime would ignore
points entirely.

**C2. Source soundness says nothing about channel creation.** A program over
the point variables of C₀ cannot name a ground point, so it cannot create a
channel. `soundness_source` and `synth_deadlock_free` stay true but say
little, and the old rejection theorems became weak. Every creating program
goes through creation hypotheses (`soundness_created`).

**C3. Choice is no longer derivable syntactically.** ChoiceTranslate creates
a channel at the carrier's point, which the source term does not name.

**C4. TreeSum's result has no point.** SegmentInterleave and SegmentDeleg
need TreeSum's box result to carry a `TPt`. Author's decision, open.

**C5. The constant world must hold every point a run uses,** infinitely many
under recursion (ι + k, ι[k]). Four box types got stronger (FreshBetween,
FreshMany, FactoryEx, GuardCex) because a channel can no longer be squeezed
between two points at runtime.

## D. Scope

**D1.** No select and no mixed choice, so weak fairness suffices.
**D2.** No termination. Fair termination (Padovani and Zavattaro 2025) is out.
**D3.** Data-dependent postponement and non-tail recursion (TreeSum, fact,
fibo, mergesort) are outside the fragment. R1′ would admit TreeSum.
**D4.** The translations PGV, PN and MP are out of the build.
**D5.** SemFlag's underivability has been open since the end-points port, so
"semantic typing types more" is proved only on the semantic side.

## F. Definitions (audit, 2026-11-16)

**F1. Two point maps for one thing (audit).** `LFconf` takes a global
point map π (`lf_pt`), and `lf_fuelc` asks `P t !! o = π !! o` on the ends
of every thread. Since L6b `LFsoup` instantiates π with `ppts P q`, the
union of the per-thread maps, so π is derived. `pupd` with `pev`,
`pev_upd`, `pev1`, `pev2` and `pev_of` recomputes along a step what the P
component of `fstep` already computes. π also costs `LFsoupAt`, `ppts`,
`ppts_lookup`, `lf_ppts`, `LFsoupAt_ppts`, `pcat_l` and `pcat_r` in
LFCompose.v, and one argument of every step lemma and of `fuel_step`
(`pupd` occurs 58 times). Lift: state `lf_pt` as `P t !! o = Some x.2` and
delete π, `pupd` and the `pev` family.

**F2. The step is read back off the redexes (audit).** An instrumented
label is the set of thread identifiers. `fstep`, `fsingle`, `fpair` and
`pev_of` recover the kind of step from `act e` of the participants, the
new channel from `head (elements (q'.1 ∖ q.1))` with default `""`, the
spawned identifier from `dom q'.2 ∖ dom q.2` with default 0, and the
order of a pair from `elements {[i; j]}`, which is why `fstep_pair`
returns a disjunction and `f2_swap` exists. Lift: labels that carry the
event (`IBeta i`, `INew i c x`, `ISpawn i j w`, `IMsg i j c b v`,
`IClose i j c`, `IChoice i j c b`, `ILink i c d`). Then `fstep` is a
match on the event, and the defaults, `fstep_pair`, `pev_of_pair` and
`f2_swap` go. `enabled` and `wfair` read the participants off the label
as they do now.

**F3. Measures totalised by defaults (audit).** `pt_of` returns `pvar 0`
for an end without a point, `fval` and `fu_at` return 0, `holder` searches
`map_to_list q.2` with `list_find`, and the rank measure in `lf_adequacy`
falls back to `pvar 0`. No default is reached on a thread in `npend`, and
each needs a spec lemma (`holder_spec`, `rend_some`). Lift: let
`lf_run_criterion` take the fuel and rank measures as relations on
pending threads, or read the holder from the soup's partner clause.

**F4. Renaming in two styles, with two `csub` (audit).** `renk g m m'`
(LFFuel.v) is relational, `kren g m` (LFSoup.v) is functional through
`list_to_map` with the side condition `kinj`, and `renk_kren`,
`kren_lookup_safe` and `kren_keep` bridge them. stdpp's `kmap` does the
same for injective maps. `Instr.csub c d x` and `JunkRenaming.csub x b c`
are one function with different argument order, and `fe_link` uses both
within one proof. `emap` (the general renaming) sits in lockfree/Instr.v,
while `chsubst` in lang/Syntax.v is `emap (csub c d)` (`chsubst_emap`).
Lift: `emap` and one `csub` in lang, `chsubst` defined from them, `kren`
from `kmap`.

**F5. `Fobl` is a nine-way split that could be a product (audit).** Every
clause of `Fobl` except receive ends with `E n' W (fupd W π φ α) e'`. What
differs per label is a side condition (tick for session labels, the floor,
`ftravel` and the payload for send, the child for spawn, `flink` for
link). As written, `Fobl_ext`, `FuelE_S_down` and `lffuel_step` each
destruct α into nine cases. Lift: `Fobl α = Fside α ∧ (α not a receive →
E n' (fupd α) e') ∧ Frecv α`, with the label analysis in `Fside` only.

**F6. Three hand-over clauses for one rule (audit).** A send asks `fhand
(w_pay W k) (fends w)` at the carrier's point k, a spawn `fhand 0`, and a
link `flink1` at the linked end's own point. The soup has three matching
updates, `fmsg` (the receiver gets `ftick <$> mres (fends w) (F s)`),
`fchild`, and `flr` (the partner of the other end gets the linker's
counter minus one). LFFuel.v proves the consequence four times
(`fuel_zero_nosend`, `fuel_zero_nospawn`, `fuel_zero_nolink`,
`fuel_zero_act`), and no proof uses any of the four. Lift: a hand-out set
`hout α` and a floor `hfloor W π α o` per label, one `Fobl` clause, and
one soup update that moves an end with its counter minus one. This is R1
in small and can be done before it.

**F7. The replacement clause quantifies over a set of maps where one map
is the worst case (audit).** `frep` lets every replaceable counter take
any value between `w_pay W k` and the cap. If FuelE is monotone in the
counters (G3, not proved), the clause is equivalent to FuelE at the single
map that lowers every held counter to `min (φ o) (w_pay W k)`. `frep` also
applies to an end whose partner the same thread holds, which no other
thread can link. That is the root of A13b, and `fw_fuel_floor` uses
exactly such an end. Neither the definition nor any world axiom asks
`w_pay W k ≤ w_bud W k`, so `fw_fuel_floor` takes it as a premise.

**F8. Budgets live in the core world (audit).** `w_bud` and `w_pay` are
fields of `world`, which the base and live relations never read. They
force `wjoin_bud`, `wext_bud`, `wbext`, `wbud_agree`, the rebuilds `World
(w_names W) (w_lt W) B P` in `strict_budgets` and `with_budgets`, and a
premise of `LFP_connect` and `LFP_join`. Lift: a separate budget map β (a
point to a cap and a floor), a parameter of FuelE, `fsem` and `LFP`. A
program has one β, so `wbext` becomes equality of β and composition joins
β1 and β2 at the cut. With A11 and R4 the floor may go altogether.

**F9. Dead definitions and lemmas (audit).** 34 names in theories/lockfree
are referenced nowhere, CheckAll.v included. They are `snd_next`, `rcv_next`,
`sel_next`, `bra_next` (entries after an action, never used),
`pupd_stuck`, `fgoal_cap` (the old link rule, "the peer's budget lies
below the counter"), `fsem_wbext`, `fsem_cap`, `renk_id_inv`,
`frep_refl`, `fcap_union`, `tenv_entry_end_inj`, `tenv_end_empty`,
`tenv_end_delete_eq`, `fchans_of_fends`, `fends_of_fchans`, `cdual_snd`,
`cend_two`, `fchans_eq_fends`, `act_aends_fends`, `synced_sym_t`,
`offered_pend`, `isteps_erase`, `act_chsubst`, `admin_sess_link`,
`pcall`, `bbox_body`, `Wpo_wf`, `cworld_ptyped`, `lfsource_gstyped`,
`with_budgets_strict`, `with_budgets_wf`, `elem_of_single`, `fw_E_one`.
Ten more are reached only from CheckAll.v, namely the four `fuel_zero_*`,
`local_progress_ready`, `lf_criterion` with `fuel_bound` and
`rank_bound`, `tsum_r1_fails`, and `lock_free_reach_of`. The last ones are
results, the rest is scaffolding. theories/lockfree/open/LocalProgressLR.v
is outside the build and records a false statement.

## G. Statements (audit)

**G1. No lemma from the soup to the live process relation (audit).**
`LFsoup n W Σ T P F q → LPrel n W Σ T (erase q)` is missing. With it `LFP`
loses its first conjunct (A6), and `LFP_term` and `LFP_connect` stop
calling `LPrel_term` and `LPrel_connect` beside the soup. It needs P-Term
for each thread and P-Connect over the pairing clause, so it is not
cheap. The alternative is no τ-divergence per thread from `lf_rel`.

**G2. No inclusion of the live relation in the base one (audit).** Nothing
states `(∀ n, LPrel n W Σ T p) → ∀ n, Prel n W Σ T p` or the same for
terms. The paper's story "the live relation types fewer programs" rests
on it. Live adequacy proves deadlock freedom separately.

**G3. No monotonicity of FuelE in the counters (audit).** FuelE at φ and
`φ ≤ φ'` pointwise under the cap should give FuelE at φ'. Every clause
asks lower bounds of counters, and receive and replacement are universal.
With it `frep` collapses to one map (F7) and the fuel parts of `fe_*`
need fewer exact counter computations.

**G4. One index serves two clocks (audit).** The live index counts
observations, so a β leaves it unchanged. The fuel index counts every
step. `lfsoup_step` lowers the index by two for every step, a β included,
and `fuel_step` and `stab_step` ask the soup at S (S (S n)) and S (S n).
`lf_adequacy` reads the soup at indices 0, 1 and 3. Harmless under ∀ n,
and it explains A9. Lift: two indices in the soup, or a fuel index that
counts observations like the live one.

**G5. Leftovers of the no-eq branch in statements (audit).** `LFP_term`
asks `tenv_dual (w_eq W) ΘB`, `LFP_connect` and `LFP_join` ask `w_eq
(wjoin W1 W2) e.2 (pt_dual e'.2)`, and `st_spawn` states `tenv_comp (@eq
point)`. `w_eq` is syntactic equality since sharp edges 159. `wjoin` still
passes an alias relation to `wgen_b`, and Worlds.v keeps eight lemmas
(`wf_eq_refl` to `wf_eq_dual`) whose proofs are `intros ->`. The protected statements would read
better with `=`.

## H. Proofs (audit)

**H1. Proof length and compile time.** Measured on 2026-11-16 at d91fa5c,
one file at a time with `rocq c -time-file`, dependencies built. Lines of
the longest proofs, from `Lemma` to `Qed`.

| File | Lines | Longest proofs (lines) | Compile (s) |
|---|---|---|---|
| lockfree/LFCompose.v | 430 | LFP_connect 171, LFP_term 71 | 205 |
| lockfree/LFSoup.v | 2,894 | step_msg 214, step_link_ne 206, fuel_link 141, step_new 114, step_choice 114, step_spawn 105 | 106 |
| lockfree/LFAdequacy.v | 1,345 | fe_link 173, stab_step 88, fuel_step 77, fe_msg 77, lf_adequacy 60 | 85 |
| lockfree/Reach.v | 599 | act_offer_sig 120, try_thread 88, preduction_back 71 | 2.3 |
| lockfree/Instr.v | 431 | preduction_lift 49, admin_enabled 25 | 1.9 |
| lockfree/Fragment.v | 2,102 | cworld_hold 28, ladder_lt 24 (most lines are checkers) | 1.9 |
| lockfree/LFFuel.v | 755 | FuelE_S_down 20, Fobl_ext 19 | 1.5 |
| lockfree/LocalProgress.v | 470 | chain_from 42, chain_from_gen 39 | 1.4 |
| lockfree/TauThread.v | 233 | padmin_acc_thread 55, tstep_det_cerase 39 | 1.4 |
| lockfree/LFFuelTyped.v | 226 | fw_fuel_floor 35 | 0.8 |
| lockfree/Criterion.v | 290 | core 63, holder_moves 30 | 0.8 |
| lockfree/ThreadProgress.v | 168 | tp_acc 34 | 0.7 |
| lockfree/Fair.v | 130 | run_admin_step 8 | 0.6 |
| liveness/LiveJunk.v | 664 | LPrel_junk 530 | 69 |
| liveness/LiveGuardFund.v | 454 | typed_live 348 | 1.1 |
| liveness/LiveFuse.v | 556 | LErel_fuse_at 283 | 15.5 |
| liveness/LivePConnect.v | 386 | lconn_level 252 | 62 |
| liveness/LiveConnect.v | 1,509 | lc2_cross_msg 243, lc_ext_recv 144, lc_ext_send 139 | 119 |
| liveness/LiveInternalize.v | 1,301 | li_ext_send 192, li_sync_case 174, li_link_give 145 | 22 |
| liveness/LiveBind.v | 614 | LErel_bind_R 153, LErel_bind 149 | 6.8 |
| liveness/LiveEconv.v | 415 | LErel_econv_at 142, LPrel_sconv 137 | 2.1 |
| liveness/LiveRenaming.v | 388 | LPrel_swap_at 109 | 1.1 |
| liveness/LivePTerm.v | 559 | lterm_level 105, link_env_split 104 | 18 |

The lockfree directory takes about 410 s, 396 s of it in three files.
The liveness directory takes about 336 s, 272 s of it in LiveConnect.v,
LiveJunk.v, LivePConnect.v and LiveInternalize.v.

**H2. Hot spots are a handful of `set_solver` calls (audit).** In
LFCompose.v six `set_solver` calls take 193 of 205 s (lines 274, 277, 296,
371, 372 and 384 of `LFP_connect`). Each decides channel membership with
about fifteen disjointness hypotheses in context. One lemma "a channel of
a left and of a right environment lies in C0", proved once with only its
premises, removes all six. In LFSoup.v one `set_solver` in `two_frame`
(line 1478) takes 36 s. In LFAdequacy.v one `eapply fe_two …; try done;
try set_solver; try (by eexists)` (line 1246) takes 38 s, because
`set_solver` runs and fails on goals it cannot close, and two `destruct
bc; simpl; set_solver` in `fe_link` (lines 1126, 1153) take 14 s. Clearing
the context or naming the goal for each call should bring the directory
under two minutes.

**H3. Duplicated proof scripts (audit).**
- `chain_from` and `chain_from_gen`, `local_progress_ready` and
  `local_progress_gen` (LocalProgress.v) are copies. The first pair is
  the second at `wt := waits q`, with `Hwt` from `Hmention` by `waits_of`.
  About 60 lines go.
- `act_offer` (lang/Safety.v, 120 lines) and `act_offer_sig` (Reach.v,
  120 lines) are the same proof in Prop and in Type. `act_offer` is a
  one-line corollary of the second.
- The eight step lemmas of LFSoup.v re-prove the frame for the threads
  that do not take part, each with its own `Hlk` and the nine premises of
  `LFconf_frame`. The six `fe_*` lemmas of LFAdequacy.v re-derive the
  counter of the partner end the same way.
- `LFP_connect` proves every field of `LFconf` twice, once per side. A
  lemma "the disjoint union of two soups is a soup when the cut pairs up"
  would serve `LFP_connect`, `LFP_join` and any n-ary join.
- `LFsoupAt_relabel` (25 lines) maps every field by hand.

**H4. Brittle case analyses and computation (audit).** `lfsoup_conf_step`
inverts `istep` with a seven-constructor intro pattern, and `Fobl_ext`,
`FuelE_S_down` and `lffuel_step` destruct α with `[|[o w|o w|o|cd|o b|o
b]|c x|w]`. Any new rule or label breaks all of them. FuelE has no
`Arguments … : simpl never`, so `simpl` or `cbn` near it unfolds `flevels`
and the string-keyed maps until the stack runs out. LFFuelTyped.v steps
threads by `vm_compute` (`fnorm`) at a fixed index (`Hf 80`), and
Fragment.v runs 66 `vm_compute` calls. They are fast (under 2 s) but read
only as computation.

**H5. Three copies of the step-indexed fixpoint (audit).** `level`,
`levels`, `level_at`, `dummy_level` (LogicalRelation.v), `llevel` and
friends (LiveRelation.v) and `flevel` and friends (LFFuel.v) build the
same "level n from all levels below" construction, each with its own
extensionality lemmas (`Fobl_ext`, `Fdef_ext`, `Vfdef_ext`, `flevels_at`
for fuel). A generic `sfix (F : ∀ n, (nat → X) → X)` with one unfolding
lemma under extensionality serves all three.

## I. Generality (audit)

**I1. One per-thread predicate along steps.** `Erel`, `LErel` and FuelE
share a shape. For every step α of the term there is an obligation per
label and a continuation one level down, closed under future worlds. A
generic per-thread predicate (an obligation per label plus a closure)
would carry `down`, extensionality and closure once. The soup is then
generic over any per-thread predicate Q that is preserved by each
participant and stable under renaming for the others. `LFconf_frame` and
`ffr` are that lemma for one Q today.

**I2. One way to get Kripke and renaming closure.** FuelE builds closure
under `wbext` and under renaming into `Fdef` (`∀ W' g π' φ'`), so
`FuelE_rename` and `FuelE_wbext` are four lines each. The live relation
proves renaming invariance after the fact (LiveRenaming.v 388 lines,
LiveJunk.v 664 lines, `LPrel_junk` alone 530). Baking renaming into the
definition of the live relation, as FuelE does, may remove most of both
files. Not checked against the arrow clause, which reads the body's ends.

**I3. Hand-over costs one, at three levels.** F6 at the fuel clause, the
three soup updates, and the moving branches of `fe_msg`, `fe_spawn` and
`fe_link` in adequacy (the partner end moves from s to j with counter
m − 1). One adequacy lemma "if the partner end moves with its counter
minus one, `fgoal` holds" replaces those branches.

**I4. Soups as products of per-thread, pairwise and global parts.**
`LFconf` mixes per-thread fields (`lf_rel`, `lf_bipol`, `lf_ty`,
`lf_closed`), pairwise ones (`lf_disj`, `lf_pair`) and global ones
(`lf_prim`, `lf_sig`, `lf_own`). Stated as three groups, relabelling,
framing and the disjoint union are generic in the per-thread part.

## J. Readability (audit)

**J1. Stale headers.**
- LiveRelation.v lines 3 to 6 say every channel step costs one "send,
  select, close and link included" and list the free τ steps as "β, new,
  spawn". A link costs nothing since sharp edges 171.
- LFAdequacy.v says that "a link hands the obligation to a peer whose
  budget lies below it ([fuel_step])", the rule option 2 replaced.
- Criterion.v says "Stage 2 instantiates them from the budgeted
  relation". That relation (LFRelation.v) is gone, and adequacy
  instantiates `lf_run_criterion`, not the bounds.
- ThreadProgress.v takes `lock_free` "from [lf_criterion]". It comes from
  `lf_adequacy`.
- Fragment.v presents R2′ and R4′ as the rules and the hand-off graph as
  replacing "the link clause of R2′". The fragment asks `lf_r2h`, the
  hand-off graph and, for sources, the root graph.
- LFSoup.v says that "[pupd] moves π". π is derived (F1).

**J2. Terminology.** The code says "slot" 53 times (fed slots,
`new_slots`, `ref_slots`, `peer_slots`, `slot_root`) and "payload" 61
times in theories/lockfree, against the decision of 2026-11-07 (fields
σ.κ, never "slot"). B1 and B2 of this file follow the code. `pt_payload`
and `KPay` stand for the field notation `!^{ƛξ}(A).S`, and `pt_shift 1`
(21 times) and `KSucc` for x⁺. Rename together with R2.

**J3. Name clashes.**
- π is the per-thread point map in LFFuel.v, the global point map in
  LFSoup.v, a path `list bool` in Fragment.v (`CPar π`, `RPar π`,
  `ty_at π`), and was the placement in the old `LFP`. The same maps are
  π and φ for one thread and P and F for the soup.
- `fact` is the fuel update of an action (LFFuel.v) and the type of world
  facts (`c1_P (g : fact)` in Fragment.v), so LFSoup.v writes
  `LFFuel.fact`. Rename the first to `fuel_act`.
- `csub` twice (F4), `is_rcv` twice (on session types in
  LocalProgress.v, on carriers in Fragment.v), `world_wf` and `wf_world`
  (A14).
- `f2`, `fmsg`, `fpair`, `fsingle`, `flr`, `flr1` name soup updates with
  the prefix f, which elsewhere marks fuel clauses (`fcap`, `fwait`,
  `fhand`).

## E. Is it nice?

The idea is small. The order on points rules out circular waiting and, being
well founded, endless chains of waiting. Fuel per obligation rules out
endless postponement and endless hand-over. Ownership and points fixed for
the run make both survive step-indexing. The mechanization carries many
artefacts around that idea (A2, A7, A9, A10, A11, B1 to B9, C1, F1 to F8). For the
paper, present the idea with three definitions (the gate, fuel per
obligation, ownership per run) and keep the artefacts in the appendix or the
artifact description.
