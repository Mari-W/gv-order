# Lock freedom: cleanup and simplification plan

For a later agent. Goal: a clean, workable lock-freedom result whose static
side is a typing discipline with compositional rules, not a pile of
syntactic checks. Read docs/extensions/lock-freedom-quirks.md first (every
quirk with its reason), then the progress file's decisions, then plan §16
to §18.

## Standing rules (from the author)

- No syntactic condition inside any relation (base, live, fuel, soup). The
  only exceptions are value-level conditions (a value's environment holds
  exactly the channels it contains, mirroring `sentc`) and conditions on
  step labels. Never add one under delegation. Ask first.
- Property definitions over the untyped semantics (`waits`, `lock_free`)
  may read syntax.
- Semantic premises over syntactic ones. Fewest rules. Encode or derive
  before adding a rule.
- Protected statements keep their form unless the author agrees: the
  soundness family, `fundamental`, `adequacy`, the composition lemmas, the
  live theorems, `lf_criterion`, `lock_free`, `thread_progress`,
  `lf_adequacy`, `LFP_term`, `LFP_connect`, `LFP_join`.
- At most two agents at once. Builds in the background
  (`ulimit -s 1000000`, retry on Error 139). `simpl`/`cbn` on FuelE blows
  the stack, use `vm_compute` on terms. Targeted edits. No AI attribution
  in commits.

## Part 1. Simplify the relations

Ordered by value for effort. Each item names what it removes.

**R1. Obligations explicit in the soup.** The soup carries an obligation
map (waiting end, serving end, counter). The per-thread fuel predicate reads
the obligations its thread serves. Send, spawn and link *move* an
obligation and charge one, acting on the end discharges it and refills.
Removes the replacement clause `frep`, the overwrite `flr`, one index level
per soup step, and quirk A13b at its root. This is the principled form of
option 2 (author, 2026-11-16). Do it before any further patching of floors.

**R2. Distinct names for the two ends.** Replace `Chan c b` by two end
names c and c̄. Removes the polarity bit, `pt_pol k = b` everywhere,
`tenv_bipol`, the bit check in `tenv_hd_end`, and the sender-keyed oddity of
the delegation floor (the floor can be read at the carrier end itself).
Mechanical but wide: lang, types, every relation, every example. Do it in
its own stage with a full build after.

**R3. A determinism lemma.** Show that soups at two indices agree on
points and ownership at every position of a run (syntactic points plus
value conditions make every split forced). Then P and F become derived from
the environments, and `LFP` loses `∃ q P F`. Also check whether the first
conjunct `∀ n, LPrel n …` of `LFP` follows from the soup and drop it if so.

**R4. One "lock-free world".** Bundle `world_wf`, `well_founded (w_lt W)`
and the budgets into one record. If R1 makes floors a property of
obligations, fold `w_pay` into `w_bud` or drop it.

**R5. Smaller side conditions.** Drop `ftravel` if F-Wait alone carries the
argument. Weaken `wbud_agree` to the cut if FuelE only reads budgets at
points the world knows. Remove lemma premises that only served E-Fit.

**R6. Optional, large.** One relation with a switch instead of the base and
the live copy (quirk A4). Only if the paper presents them as one relation or
the duplication blocks further work.

**R7. State connect by the interface order (author, 2026-11-17).**
`Prel_connect`, `LFP_connect` and their N-ary forms ask `strict (wjoin W1
W2)`, a condition on the whole join. Each Wᵢ is strict, so a cycle in the
join crosses between the worlds only at shared names, possibly passing
private names on the way (W₁ ⊢ a ≺ p ≺ b, W₂ ⊢ b ≺ a). Prove that the join
is strict iff the two orders, each closed transitively and restricted to the
shared names (`wrestrict`), are acyclic together, and restate the connect
hypotheses in that form. The check then reads only the interface. No lemma
states this yet.

## Part 2. Replace the static fragment by typing rules

Today `lfptyped` and `lfsource` are the typing judgment plus a list of
global analyses: the guard, R1 (recursion in tail position), R2-recv with
fed slots, the type hand-off graph, the root graph with `stab`, `foreign`,
`bleak`, `troots`, the stretch bound `stretch_len = 2·seg_len` via `scost`,
the annotation `ann` backed by derivations, the count of leading `TPt`
parameters, and `wf_world (cworld Ψ)`. Each closes one counterexample. The
fundamental theorem then has to rebuild per-thread facts from them.

The clean version makes each concern a local rule of a typing judgment, so
`lf_fundamental` is again one compatibility lemma per rule, like
`fundamental` and `live_fundamental_guarded`.

**T1. Liveness by guarded recursion.** Replace the syntactic guard by a
typing rule for box bodies: the self is available only after one channel
action of the round (a later modality on the self, or a cost index in the
judgment). Compositional and standard (guarded recursion). It also lifts
quirk B6, because a point argument is just an argument.

**T2. Fuel by bounds in the typing context.** The judgment tracks, per held
end, a static bound: acting on the end resets it to the end's budget, every
other channel action decrements it, a hand-over (send, spawn, link)
requires it to be at least one plus the floor. Box types state what their
point parameters need as budget atoms in the box's constraint set, next to
the order atoms (for example β(ι) ≥ k beside ι ≺ κ). This replaces the
stretch bound, R1, R2-recv, the fed-slot clause, the hand-off graph, the
root graph and the annotation in one go. Non-tail recursion becomes
admissible where the bounds work out, which may admit TreeSum (quirk D3).
**Needs the author's decision.** Budget atoms in constraints are not
tickets in session types (session types stay as they are), but they are
numbers in box types. Present the difference before building.

**T3. Rank.** Keep `well_founded (w_lt W)` as a semantic premise. The only
global static check left is that the creation hypotheses give a
well-founded starting world (`wf_world (cworld Ψ)`), which is a property of
the world, not of code.

**T4. What remains of the old checks.** Nothing, if T1 and T2 work. If T2
is rejected, keep the current fragment but drop the rules that option 2
made redundant: the self-loop rule for links inside boxes (quirk B5), and
whatever R1 (Part 1) makes unnecessary in the root graph.

A minimal alternative, if the author prefers it to T2: drop the static
fragment from the headline. Lock freedom is semantic (`LFP`, adequacy,
composition), examples get direct semantic proofs, and the static
discipline becomes future work.

## Part 3. Calculus-level items (author decisions)

- TreeSum's box result carrying a `TPt` would bring back SegmentInterleave
  and SegmentDeleg.
- ChoiceTranslate is impossible under syntactic points. Accept the loss or
  add point expressions that read the current point of a held end.
- Source-level soundness no longer covers channel creation. State it in the
  paper or retire `soundness_source` in favour of `soundness_created`.
- The translations PGV, PN and MP need the port to syntactic points.
- SemFlag's underivability is open since the end-points port.

## Part 4. Proof engineering (audit, 2026-11-16)

From the read-only audit at d91fa5c (quirks F to J). No item changes a
protected statement unless it says so. Each names what it removes, its
risk, and when to do it.

**P1. Dead code and stale headers.** Delete the 34 unreferenced names of
quirk F9 and rewrite the six stale headers of J1. Removes about 150
lines and every comment that still describes the old link rule, the
oracle relation or link cost one. Risk none. First, in one commit.

**P2. Compile time.** Replace the six `set_solver` calls of `LFP_connect`
by one lemma "a channel held on both sides lies in C0" with only its
premises, split the slow call in `two_frame` (LFSoup.v line 1478), and
replace `try set_solver` after `eapply fe_two` (LFAdequacy.v line 1246) by
calls on the goals that need it. Removes about 280 of the 410 s that
theories/lockfree takes (193 s in LFCompose.v alone). Risk low. First,
with P1. Then add `Arguments FuelE : simpl never` and the same for
`Vfuel` (H4).

**P3. Drop the global point map π.** `lf_pt` reads `P t`, and π, `pupd`,
`pev`, `pev_upd`, `pev1`, `pev2`, `pev_of`, `LFsoupAt`, `ppts`,
`ppts_lookup`, `lf_ppts`, `LFsoupAt_ppts`, `pcat_l`, `pcat_r` go (F1).
`LFP` keeps its text, because it already quantifies over P and F. Risk
medium. It touches every step lemma of LFSoup.v, `stab_step`,
`fuel_step` and `LFP_connect`, all mechanically. Before R1, because R1
rewrites the same lemmas and is smaller without π.

**P4. One hand-over clause and `Fobl` as a product.** Restate `Fobl` as a
side condition per label, the continuation for every label but receive,
and the receive clause (F5). Replace `fhand` at send, `fhand 0` at spawn
and `flink` by one clause over a hand-out set and a floor per label, and
`fmsg`, `fchild` and `flr` by one update that moves an end with its
counter minus one (F6, I3). Removes the nine-way case splits of
`Fobl_ext`, `FuelE_S_down` and `lffuel_step`, folds the four `fuel_zero_*`
into one lemma, and shares the moving branches of `fe_msg`, `fe_spawn`
and `fe_link`. Risk medium. FuelE is not protected. Do it inside R1,
because R1 replaces the link update anyway and obligations make the
hand-out set the natural unit.

**P5. Prove FuelE monotone in the counters (G3).** If it holds, the
replacement clause becomes FuelE at one map (F7). Cheap, and it sharpens
the choice between the quick patch of §18 and R1. Risk low (a failed
attempt costs an afternoon). Before R1.

**P6. Event labels for the instrumented semantics.** Let `istep` carry the
event (F2) and keep `istep q L q'` as the projection `∃ ev, iev q ev q' ∧
parts ev = L`, so `lock_free`, `wfair` and `enabled` keep their text.
Removes the defaults `""` and 0, the re-reading of `act e` in `fstep`,
`fsingle`, `fpair` and `pev_of`, `fstep_pair`, `pev_of_pair` and
`f2_swap`. Risk medium. Instr.v, Fair.v, Reach.v and ThreadProgress.v
read labels. After P3, before or with R1.

**P7. Merge duplicated proofs.** Make `local_progress_ready` an instance of
`local_progress_gen` and `act_offer` a corollary of `act_offer_sig`
(H3). Removes about 180 lines. Risk low. Both statements stay. Any time,
best with P1.

**P8. One renaming.** Move `emap` and one `csub` to lang/Syntax.v, define
`chsubst` from them, delete `JunkRenaming.csub`, and define `kren` by
`kmap` (F4). Removes the second `csub`, `kinj`, `kren_lookup_safe` and
`renk_kren`. Risk low, but it touches invariance/JunkRenaming.v and
needs a full build. Any time after P1.

**P9. Generic soup lemmas.** Group `LFconf` into per-thread, pairwise and
global fields (I4) and prove framing, relabelling and the disjoint union
once. `LFP_connect` shrinks from 171 lines to the cut argument,
`LFsoupAt_relabel` to a line. Risk medium. After P3.

**P10. Budgets out of the world.** Make the budgets a parameter β of
FuelE, `fsem` and `LFP` instead of fields of `world` (F8). Removes
`wjoin_bud`, `wext_bud`, `wbext`, `wbud_agree`, `strict_budgets` and the
world rebuilds of `with_budgets`. **Changes the protected `LFP_term`,
`LFP_connect`, `LFP_join` and `lf_adequacy`.** Needs the author. With R4.

**P11. Missing lemmas.** The soup gives the live process relation (G1),
then drop the first conjunct of `LFP` (A6). The live relation is
included in the base one (G2), for the paper. Risk high for G1 (it needs
P-Term and P-Connect over the pairing clause), low for G2. After R1 and
R3, because R3 may make G1 easier.

**P12. Names.** `wf_world` to `rank_wf`, `LFFuel.fact` to `fuel_act`, the
soup updates without the f prefix, one `is_rcv`, and "field" for "slot"
and "payload" with `pt_field`, `KField` and x⁺ for `pt_shift 1` (J2, J3,
A14). Risk low but wide. With R2, which renames ends anyway.

**P13. The fragment file.** Move the examples' fragment facts out of
Fragment.v and LFFuelTyped.v into examples/LockFree.v (B9). Merge the two
carrier analyses into one over roots and drop `lf_r2`, `lf_r2r` and the
self-loop rule for links (B7, B8, B5). Risk low for the move, medium for
the merge. Only if T2 is rejected. With T2 the analyses go altogether.

**P14. Leftovers of no-eq.** Replace `w_eq` by `=` in `LFP_term`,
`LFP_connect`, `LFP_join` and `st_spawn`, drop the alias argument of
`wjoin` and the eight trivial `wf_eq_*` lemmas (G5). **Touches protected
statements (cosmetically).** Ask the author. Any time.

**P15. One step-indexed fixpoint.** A generic `sfix` with one unfolding
lemma for the base, live and fuel relations (H5). Removes three copies of
`levels` and their extensionality lemmas. Risk high, because it touches
the base relation. Optional, with R6.

## Suggested order

0. P1, P2 and P7 (dead code, stale headers, compile time, duplicated
   proofs). Then P5, which informs step 1.
1. Finish §18 (replacement against the send floor) only as far as needed to
   decide between a quick patch and R1. Prefer R1.
2. P3, then R1 with P4 and P6 folded in, then L6 (`lf_fundamental`) on the
   current fragment, so a complete result exists. P9 after R1.
3. R2 with P12, and R3 as separate stages, each with a full build and
   CheckAll. P8 any time in between.
4. T1 and T2 after the author decides on budget atoms. Then retire the old
   analyses in Fragment.v (or P13 if T2 is rejected).
5. R4 with P10, R5, P11, then R6 with P15 if wanted. P14 whenever the
   author agrees.

Acceptance for every stage: full build, no Admitted, no axioms, CheckAll
regenerated with every active entry closed, protected statements diffed
against the stage's base commit, one log bullet in the progress file, and
quirks file updated (remove what was lifted).

## Addendum 2026-11-16: link tickets

The author chose link tickets (plan §18) over option 2's counter hand-over.
R1 (explicit obligations) no longer carries the link rule: links are paid by
per-thread tickets, so R1 is only a readability item now. Under T2 the
tickets become part of the typing context (a link costs one, a spawn
splits), which removes the static count 2^s·ℓ of initial tickets.
