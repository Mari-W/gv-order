# Findings of the content pass, 2026-11-22

Branch redesign-fable. Proposals change what a rule, definition or theorem
states and are not on the map. Each one quotes the Rocq with file and line,
states the proposed form, says what it buys, what could break, and gives a
confidence. Quirks are oddities the pass could not resolve. The map stays
faithful to the Rocq on redesign at 1ed17be.

## Big picture

The system has four devices, each added for one family of counterexamples.

1. Points and a static order of facts. One point per end, actions move it,
   a thread waits only below the dual points of what it holds. This alone
   gives deadlock freedom over acyclic worlds (F7 to F10 touch its edges).
2. Credits, tickets, costs and aging. Two numbers per end bound a run-time
   counter from both sides, so that a thread postpones an end only finitely
   often and a link lowers the counter a waiting thread faces (F1, F2, F5).
3. Ranked worlds and the switch on $N$. Lock freedom follows one wait through
   a run, so the union of the worlds of a run must be well-founded, which
   ranks fixed at creation give (F6).
4. The guard. Internal steps cost nothing at $\kappa_L$, so a syntactic check
   keeps a box from recursing before an action (F3).

Ranked by how much they would simplify the system:

1. **F3, drop the guard** by charging `force` one counter unit. Removes a
   second judgment on terms (13 rules), the `pguard` premise of four
   theorems and the `no_tau_divergence` result, which lock freedom does
   not need. Medium confidence.
2. **F9, contractive types by construction.** Removes seven `tcontr`,
   `scontr` and `sinsts` premises and the premise of E-Sub. High confidence,
   medium cost.
3. **F4, one bridge condition for creation and opening.** `cons_open` and
   the second clause of `acyc_new` state the same thing. Lemma C and the
   fifteen `cons_*` discharges collapse. High confidence.
4. **F8, drop the $\bot$ flag of the future.** It denotes the same set as
   the rest "everything". High confidence, small cost.
5. **F2, spawn costs nothing.** The premise $a \geq 1$ of E-Spawn and the
   decrement in F-Spawn are a leftover of treating spawn as a send. High
   confidence.
6. **F10, two redundant premises of P-Connect.** Derivable from the left
   premise. High confidence, trivial cost.
7. **F11, one process judgment.** The full judgment duplicates the hidden
   one. Medium confidence.
8. **F12, `dftyped` as the instance $N = \infty$** instead of a second
   inductive with 25 rules. Medium confidence.
9. **F6, `gen_new` as `acyc_new` plus rankability.** Presentation of the
   same conditions in layers; Lemma C becomes trivial. High confidence.
10. **F5, tickets per interface end chosen at P-Term**, not $N/2$. Medium.
11. **F1, where credit and tickets differ and where they do not.** Not a
    merge, the pass confirms that two numbers are needed while link is a
    primitive. The real simplification is design C of pending.md (replace
    link by the derived forwarder), which the author has declined.
12. **F13, the world as a hypothesis of $\Gamma$.** Removes one parameter
    from every rule. Low priority.

A clean redesign from scratch would keep device 1 as it is, with the
existential of E-New and the bridge condition as the single well-formedness
of a constraint against a context (F4, F6). It would make contractivity and
$a \leq m$ properties of the type syntax (F9, Q2). It would have one typing
judgment with a mode $N \in \mathbb{N} \cup \{\infty\}$ and no second
inductive for either the deadlock-free terms or the full processes (F11,
F12). Lock freedom would then add exactly three things to the judgment: the
numbers on types with aging, the finite bound on the world kind, and one
cost unit per `force` (F3). The guard, the $\bot$ flag, the spawn credit and
the duplicate P-Connect premises would not exist. What stays as it is and
looks essential: the future, hiding at P-Term, fusion in $P$, ordinal indices
for lock freedom, and the two rules of `new`.

## Proposals

### F1. Credit and tickets, aging (block `t-lf-counters`)

**Current.** `TSess (S : sty) (x : point) (a : fuel) (m : fuel)`
(types/Types.v:38). `e_link … : lgt N a1 m2 → lgt N a2 m1 → …`
(static/Typing.v:153) with `lgt N a m := a + m > N` (types/Costs.v:72).
`tsum_ok N m1 m2 := m1 + m2 ≤ N` (types/Costs.v:76).

**Assessment.** The two numbers do two jobs that one number cannot do
(the map now says so in `t-lf-counters.why`). The credit is a lower bound
that aging lowers; the tickets are the reset value and, through
$\mathsf{tk}(o) + \mathsf{tk}(\overline{o}) \leq N$, an upper bound on the
partner. Tickets exist only for E-Link. Without link every lock-free example
types with $m = N$ on both ends (check-links-without-tickets.md, "The lock-free
examples"), and E-Link is the only rule that reads $m$ of another end.

**Proposal.** None on the numbers. Two cleanups. (a) Make $a \leq m$ an
invariant of the syntax, see Q2. (b) If the author ever accepts design C of
the link discussion in pending.md (forwarder in place of fusion), tickets, the
bound $N$ on channels, `tsum_ok`, `sp_tsum` and the premise of E-Link all go,
and an end type is $S_x^{a}$ again. The author declined C on 2026-11-22; this
entry records what C would buy.

**Confidence.** High that nothing simpler holds with link as a primitive
(check-links-without-tickets.md, "Why the candidate fails").

### F2. Spawn costs the child nothing (blocks `r-threads`, `fu-obls`)

**Status (2026-11-22, branch fx-cost): done.** `e_spawn` has no credit
premise, `f_spawn` hands the child `mres (fends v) φ`, and `e_spawn_lam` is
E-Abs at credit 0. The soundness argument holds in Rocq: `spawn_redex`
(cost/CostRedex.v) calls the closure at the unchanged counters, which the
call clause of FV-Arrow accepts at each credit. The ownership update of a
spawn is `kspawn` (soup/Soup.v), with no tick. The lock-free measure no
longer falls at a spawn that passes the awaited end on. The criterion now
inducts on `tRs` (lockfree/TauThread.v), the administrative order of a
thread with its spawned children, and `lf_stay` (soup/LFAdequacy.v) lets the
holder become a child of the old holder. `sp_cap` holds because no counter
rises. No example bound changed.

**Current.** `e_spawn … : typed … e (TLolli ub lb c' TUnit TUnit a) c0 → fle (Some 1) a → …`
(static/Typing.v:157). F-Spawn (fuel/Fuel.v, `f_spawn`) asks
$\mathsf{positive}(\Phi|_M)$ and starts the child at $\Phi|_M{\downarrow}$,
the counters minus one. The map shows both.

**Proposed.** Drop `fle (Some 1) a` from `e_spawn`. In `f_spawn` drop the
positivity premise and start the child at $\Phi|_M$ unchanged:
`v ∗ ∈ F^N_β⟦Φ|_M ⊢ thread ! ∞⟧`. `e_spawn_lam` becomes E-Abs at $a = 0$
followed by E-Spawn.

**Why.** A counter counts actions of the holder on other ends. A spawn is an
internal step and no action, so no counter should fall. The decrement copies
the send case, where the sender does act. The soundness of F-Spawn with the
unchanged counters follows from FV-Arrow at credit $a = 0$, whose call clause
accepts $\Phi' = \Phi$ (check-per-end-capture.md, "Why it is sound").

**What could break.** `rx-delegate`, `rx-postpone`, `rx-relink` and `rx-chain`
do not rely on the spawn decrement (check-links-without-tickets.md, "The
four checks", item 4). The forwarder example `fw_fsem` spawns received
closures; it needs only that the closure owns its ends. The counter invariant
`sp_cap` ($f \leq m$) is kept because nothing rises.

**Confidence.** High.

### F3. Drop the guard, charge `force` one unit (blocks `g-guard`, `ct-costs`, `fu-obls`)

**Current.** `lguard : (nat → bool) → expr → Prop` with 13 constructors
(static/Guard.v:63), `acts`, `kmarks L L' e := L' = L ∨ (L' = ∅ ∧ acts e)`
(static/Guard.v:59), `pguard`. The premises `⊢▷ p` of `lf_fundamental_h`
(soup/LFTyped.v:109), `lf_soundness_h` (soup/LFTyped.v:120),
`live_fundamental_ranked` (static/Fundamental.v:839) and `live_soundness_h`.
The cost table $\kappa_L = (0,0,0,0,1,1)$ makes $\beta$, hence `force`,
free, so `!(f = force f)` is in no $E$ at $\kappa_L$ and the guard is what
keeps typed terms out of it.

**Proposed.** (a) Split the label $\beta$ into $\beta$ and $\mathsf{force}$
in `tlabel` (lang/Semantics.v) and add a cost $\kappa_{\mathsf{force}}$ to the
table, $0$ in $\kappa_{DF}$ and $1$ in $\kappa_L$. (b) A fuel obligation
F-Force like F-Count without a protocol step: a force requires positive
counters on the held ends that are not idle and decrements them,
`e' ∈ F^N_β⟦Φ↓ ⊢ σ ! d⟧`. (c) E-Force gets effect
$\varepsilon_0 \cdot \varepsilon \cdot 1$ and ages $\Delta$ by one as an action
does. (d) Delete `lguard`, `acts`, `kmarks`, `pguard` and the `⊢▷` premises.
(e) `live_soundness_h` and `no_tau_divergence` go, or stay as results about
a guarded fragment.

**Why.** The guard is the only place where lock-free typing reads the shape
of a term. Its job is to keep a thread from looping on internal steps while a
partner waits on an end it holds. With `force` charged like an action, such a
thread exhausts the counters of its held ends (F-Force), and aging rejects it
statically: a loop has cost $\infty$ already today, and holding a non-idle end
across a call of cost $\infty$ fails $c \leq a$ at a finite bound. A loop that
holds no end is harmless for lock freedom and would be accepted, as it should.
`spawn_loop` of the guard examples is rejected by the hand-over of its end at
each spawn already (F-Spawn, or with F2 by aging across the call of cost
$\infty$).

**What could break.** Lock-free adequacy measures a wait by (rank, counter of
the dual end); a force of the holder then lowers the counter like a step on
another end, so the measure still falls. $\beta$ steps without a force cannot
loop (no fixpoint without a box). The result `no_tau_divergence` is lost as a
theorem of typing; lock freedom as defined in lockfree/Fair.v does not use it.
The guard rejections `div_box`, `pn_fix`, `cx_box` become accepted programs
(they hold no end), so the example block changes meaning.

**Confidence.** Medium. The step that needs checking in Rocq is the
$\kappa_L$ compatibility lemma of E-Force with the new cost, and that
`lf_adequacy` reads only counters and ranks (its proof in soup/LFAdequacy.v
does today).

### F4. One bridge condition for creation and opening (blocks `r-new`, `r-ex`)

**Status (fx-static).** Done. `cons_open W Γ m C` is the bridge condition for $m$ roots (`in_tree`, `cfact_at`, `tree_step`, `outer_pt`, `bridge_at`, static/Contexts.v), including $m = 0$. `acyc_new = tree_acyclic ∧ cons_open W Γ 1 C`, with `cons_open_1` relating the instance to `cbridge`. The old form is `cons_open_conservative` (static/PointSubst.v), which needs the facts of $W$ at constant roots (`facts_const`). So `opened_cons` and the inversions built on it (`cl2_needs`, `letu_cl2_needs`, `sbv_thread_needs`, `fwd_needs`, `fj_wait_needs`) take `facts_const W`, which every process derivation supplies. `cons_tree`, `cons_new` and `cons_gen` lose the `facts_const` premise and become two-line lemmas. The section `cons_gen` of PointSubst.v (the partner-set walk) is replaced by the bridge walk `binv`. `sbv_rejected`, `sbv_rejected_h`, `Tbad_not_cons` and the ring rejections still hold.

**Current.** `cons_open W Γ m C := ∀ x y, slt W (hc_open m C Γ) (shift x) (shift y) → slt W Γ x y`
(static/Contexts.v:200), a premise of `e_open` (static/Typing.v:179).
`acyc_new W Γ C := (∀ x, in_tree0 x → ¬ tc (new_step C) x x) ∧ (∀ z y, cbridge C z y → slt W Γ (ctx_pt C z) (ctx_pt C y))`
(static/Contexts.v:319). Fifteen example sites discharge `cons_open` by
`cons_law`, `cons_gen` or `cons_tree` (pending.md, stage 4).

**Proposed.** Define `cons_open W Γ m C := ∀ z y, cbridge C z y → slt W Γ (ctx_pt C z) (ctx_pt C y)`,
the second clause of `acyc_new`, and prove the old form as a lemma. Then
`acyc_new W Γ C = tree_acyclic C ∧ cons_open W Γ 1 C`, and
`new_ok`, `gen_new` and `e_open` share one definition.

**Why.** A fact between two old points that the opened constraint derives
is a chain old–tree–old–…–old. Each stretch through the tree is a bridge, so
the chain is derivable from $\Gamma$ iff each bridge is. That is the content
of `cbridge`. One notion instead of two, one proof instead of the three
discharge lemmas, and the map can say "a creation and an opening add no fact
between old points" once.

**What could break.** `sbv_rejected` must stay rejected: the dead arm's binder
constraint $\{y \prec \overline{x}\}$ has no bound variable, so its one fact is a
bridge of length zero and must be derivable from $\Gamma$, which it is not.
Same verdict as today. Existentials with several bound variables ($m > 1$)
need `cbridge` stated for a tree of $m$ roots; today `cbridge` is for one
root.

**Confidence.** High on the equivalence, medium on the $m > 1$ generalization.

### F5. Interface tickets chosen at P-Term (block `p-typing`)

**Status (fx-static).** Not done. The tickets of an interface end would have to live in `senv`, whose entries `(S, x)` 53 files destructure, and in the soup invariant `sp_sigcap` (soup/State.v), which bounds the cap of an interface end by `fhalf N` and which `soup_connect` and `lf_p_term` read. The change is a refactor of the lock-free process semantics and of `senv`, larger than this pass and close to the files of fx-cost. No commit touches it.

**Current.** `p_term … : … typed W N (tenv_of (fhalf N) Σ ∪ ΘB) … → …`
(static/Typing.v:354), each interface end at credit and tickets $N/2$.
`p_connect` cuts $\Sigma_C$ against `senv_dual ΣC` exactly.

**Proposed.** `tenv_of` takes the tickets from $\Sigma$, whose entries then
carry $m$, and P-Connect asks $m + m' \leq N$ for each cut pair $o \mapsto
S_x^{m}$, $\overline{o} \mapsto \overline{S}_{\overline{x}}^{m'}$.

**Why.** The split $N/2$ is a convention that rejects programs whose link
needs all $N$ tickets on one interface end (the link example works only
because both channels are created inside one thread). The general form is
the one E-New already uses, a split chosen per channel.

**What could break.** `sp_tsum` after a cut, and `lf_p_connect`, which
builds the soup state of the composite from the two components; both read
the tickets off $K$, which the new $\Sigma$ would supply.

**Confidence.** Medium.

### F6. `gen_new` as `acyc_new` plus rankability (block `r-new`)

**Status (fx-static).** Done. `new_ok N := acyc_new ∧ (N ≠ None → well_founded (new_step C) ∧ ∃ Sr, gen_new_rel)`. `gen_new_iff` proves `gen_new` equal to `acyc_new` plus the part for ranks, `new_ok_acyc` is a projection and `new_ok_gen`, `gen_new_ok` translate. Lemma C stays, as one direction of `gen_new_iff`.

**Current.** `gen_new W Γ C := well_founded (new_step C) ∧ (∀ x y, cfact C x y → ¬ in_tree0 x → ¬ in_tree0 y → slt W Γ …) ∧ ∃ Sr, gen_new_rel W Γ C Sr`
(static/Contexts.v:245), `new_ok N := match N with None => acyc_new | Some _ => gen_new end`
(static/Contexts.v:363), and Lemma C `gen_new_acyc`.

**Proposed.** `new_ok N W Γ C := acyc_new W Γ C ∧ (N ≠ None → well_founded (new_step C) ∧ ∃ Sr, gen_new_rel W Γ C Sr)`.

**Why.** The lock-free premise is the deadlock-free premise plus what ranks
need. Stated that way, the map shows one rule with one coloured conjunct,
Lemma C is a projection, and the second clause of `gen_new` (facts between
context points) is the bridge clause of `acyc_new` for bridges of length
zero, so it is not repeated.

**What could break.** Nothing semantic. `gen_new_rel` already implies the
bridge clause for longer bridges (check-general-new.md, section 4), so the
conjunction is equivalent to today's `gen_new`.

**Confidence.** High.

### F7. The two kinds of world and the switch on $N$ (blocks `w-world`, `w-wf`)

**Current.** `Record world := { w_roots; w_ord; …; w_rk : option (point → rank_ord); w_rk_ord … }`
(types/Worlds.v:520). `wok N W := match N with None => sacyc W | Some _ => swf W end`
(static/Contexts.v:366). The relation is read over strict worlds for deadlock
freedom and over ranked worlds for the lock-free threads.

**Assessment.** The pass looked for a single kind. The deadlock-free
examples need acyclic worlds that are not well-founded (fork-join with
replies, check-df-acyclic.md, verdict 3), and lock freedom needs ranks fixed
at creation (check-layers-open.md, verdict 1). So two kinds are forced by the
examples. The field `w_rk` with extension keeping it is the cheapest way to
say "a world and its extensions have one kind".

**Proposal.** None on the kinds. One cleanup: the kind is determined by $N$
everywhere ($N = \infty$ strict, finite ranked), so the mode could be a
parameter of the relation and the judgment instead of a field of each world,
with `wok`, `new_ok` and the kind reading one flag. This removes `wk_ext`,
`w_rk_ord` and the kind case split from the extension lemmas and makes the
map's $\mathsf{ok}_N$ and $\mathsf{new\_ok}_N$ one switch.

**Confidence.** Medium that the flag form is simpler in Rocq; the report of
2026-11-22 chose the field form to avoid a `Context` line in 40 files.

### F8. Drop the $\bot$ flag of the future (blocks `t-contexts`, `t-side`)

**Status (fx-static).** Done. `futrest`, `FBot`, `fs_var`, `fs_bot` are gone, a future is `gset point * option frest`, and `sf_unionb F X true := (F.1 ∪ X, Some RAll)`. The denotation `sf_den R F` and `sem_typed` lose the set $B$. The cases of `typed_sem` that held a set $B'$ for the flag read the rest at `ρ ∪ (if b then B' else ∅)` (`rest_ok_unionb_b`, `den_unionb`). `hbot` and E-Abs.lb are unchanged.

**Current.** `Inductive futrest := FRest (r : frest) | FBot (o : option frest)`
(static/Contexts.v:102). `sf_unionb F X true := (F.1 ∪ X, Some (FBot (fs_var F.2)))`
(static/Contexts.v:113). `ub_below_s` asks `fs_bot F.2 = false` and
`rest_below x RAll = False` (static/Contexts.v:150). The denotation
`sf_den R B F := F.1 ∪ (if fs_var F.2 then R else ∅) ∪ (if fs_bot F.2 then B else ∅)`
(compat/SemTyped.v:51) with `rest_ok` constraining $R$ only for `RAbove u`.

**Proposed.** Delete `FBot`; `futrest := frest`. Let
`sf_unionb F X true := (F.1 ∪ X, Some RAll)`. The future is $(X, \cdot)$,
$(X, {\uparrow}u)$ or $(X, {\uparrow})$.

**Why.** Statically, the flag $\bot$ and the rest ${\uparrow}$ both forbid
every action and both are kept by every rule. Semantically, both denote an
arbitrary finite set ($B$ unconstrained, $R$ unconstrained at `RAll`). Two
spellings of one thing. The map's `F = (X, {\uparrow}u \mid {\uparrow} \mid \bot)`
becomes two cases, and `ctx.bot`, `fs_bot`, the second conjunct of `hsat` for
$B$, and `den_fresh` for the flag go.

**What could break.** `E-Abs.lb` and `hbot` stay: $\bot$ as a lower bound of
a type is a different thing (it marks hidden ends). Only the flag on futures
goes. Weakening in the future (`ready_t_future`) is unchanged.

**Confidence.** High.

### F9. Contractive types by construction (blocks `ty-session`, `r-fun`, `r-data`, `r-boxes`, `r-new`, `t-subs`, `p-typing`)

**Current.** `tcontr T` at `e_abs` (static/Typing.v:68), `tcontr (TSum T U)`
at `e_inj` (101), `tcontr U` at `e_box` (113), `scontr S` at `e_new` (161) and
`e_new_fld` (166), `(tcontr T → tcontr T')` at `e_sub` (170), `scontr` of
$\Sigma$ and $\Theta_B$ at `p_term` (354), `Forall contractive ss` in `sinsts`
(static/Contexts.v:503), and the clause of `sub_box` (static/Contexts.v:487).
`scontr (SMu b) := negb (ugv 0 b) && scontr b` (types/Contractive.v:197).

**Proposed.** Make `SMu` take a guarded body: either a subset type
`{b | ugv 0 b = false}` or a separate inductive of session types in which
`SMu` is only applicable under an action (the usual contractive grammar of
session types). Then every `tcontr`, `scontr` and `contractive` premise is
a tautology and goes, `sinsts N ss` keeps only `sscoped` and the $N = \infty$
clause, and E-Sub loses its third premise. `sub_box` keeps only
`teq U U'`.

**Why.** The premises sit at every introduction site of a type and state
one invariant, "every type in a derivation is contractive". Standard practice
makes that a property of the syntax. The example `ex-sinst` shows why the
invariant matters; it does not show why it should be a premise.

**What could break.** Substitution of a session variable by `Skip` must stay
impossible, which the grammar gives when a variable counts as unguarded
(`ugv` today). The equivalence `sequiv` and `unfoldS` are then total without
a fuel argument. Cost: `sinst` and `unroll` must produce guarded bodies,
which is a lemma today and a typing obligation in the subset form.

**Confidence.** High on the simplification, medium on the Rocq cost.

### F10. Two redundant premises of P-Connect (block `p-typing`)

**Status (fx-static).** Done. `p_connect`, `fp_connect`, `pc_snoc` and `lf_p_connect` lose `Σ1 ##ₘ ΣC` and `Σ2 ##ₘ senv_dual ΣC`. `p_connect`, `fp_connect` and `pc_snoc` also lose the partner-freedom of $\Sigma_C$, which `lf_p_connect` keeps because the soup does not give it. The lemmas `chans_disj_map`, `chans_disj_map_dual` and `pfree_union_r` (static/Typing.v) derive them.

**Current.** `p_connect … : … → Σ1 ##ₘ ΣC → Σ2 ##ₘ senv_dual ΣC → (∀ o, o ∈ dom ΣC → (o‾)%cend ∉ dom ΣC) → chans_of Σ1 ## chans_of Σ2 → chans_of Σ1 ## chans_of ΣC → chans_of Σ2 ## chans_of ΣC → …`
(static/Typing.v:363). `ptyped_pfree : ptyped N W Σ p T → pfree Σ`
(static/Typing.v:401).

**Proposed.** Drop `(∀ o, o ∈ dom ΣC → o‾ ∉ dom ΣC)`, which follows from
`ptyped_pfree` of the left premise ($\Sigma_C \subseteq \Sigma_1 \cup \Sigma_C$),
and drop `Σ1 ##ₘ ΣC` and `Σ2 ##ₘ senv_dual ΣC`, which follow from the
channel disjointness premises. The rule then has the two typings, three
channel disjointness premises, two restriction disjointness premises and
`wok N (W1 ⊔ W2)`.

**Why.** Derivable premises make a rule look stronger than it is and cost a
discharge at every use.

**What could break.** Nothing. The same holds for `fp_connect` (static/Typing.v:258)
and for `pcomps` of the n-ary rule.

**Confidence.** High.

### F11. One process judgment (blocks `p-typing`, `th-fund-proc`)

**Current.** `ptyped` (static/Typing.v:353) and `fptyped` (static/Typing.v:248)
have the same two rules, the hidden one restricting the world of the
conclusion and the full one keeping it. `ptyped_full` and `fptyped_ptyped`
(static/Hiding.v) translate between them, and `fundamental_proc_h` goes
through the full judgment.

**Proposed.** Keep `ptyped` only. Prove the fundamental theorem by induction
on `ptyped` with the strengthened statement "there is an acyclic whole world
$W'$ that hides to the conclusion world and the semantic judgment holds at
$W'$", which is `sem_ptyped_h` already. The P-Connect case renames the private
constants of one side apart (`typed_ren`, `connect_hidden`) exactly as the
proof of `ptyped_full` does today.

**Why.** Two inductives with four identical rules are a maintenance cost and
make the map show two judgments where the paper has one. The full world is a
proof device, not a judgment anyone writes.

**What could break.** The n-ary rule (`p_connect_n`) is stated over `ptyped`
already. The renaming lemma must be available on `ptyped` derivations, which
`ptyped_full` shows it is.

**Confidence.** Medium.

### F12. `dftyped` as the instance $N = \infty$ (blocks `r-*`, `th-conserv`)

**Current.** `dftyped` (static/Conservativity.v, rules `d_unit` … `d_open`,
25 constructors) duplicates `typed` without annotations, and `conservative`
proves the two equivalent on `ty_df` types.

**Proposed.** `Definition dftyped W Θ Γ Δ F e T := ∃ c, typed W None Θ Γ Δ F e T c`
on types with `ty_df T = T`, and keep `conservative` as the statement that
`typed W (Some N)` erases into `typed W None`.

**Why.** Twenty-five rules less, and the map's deadlock-free view is
literally the lock-free rules with the coloured parts removed, which is what
it already shows.

**What could break.** The inversion lemmas of static/Inversion.v for
`dftyped` and the example files that build `dftyped` derivations by hand.

**Confidence.** Medium (mechanical, but many sites).

### F13. The world as a hypothesis of $\Gamma$ (blocks `t-contexts`, `t-judgment`)

**Current.** `fl W Γ` has the two generators `fl_w` (facts of $W$) and `fl_h`
(instances in $\Gamma$) (static/Contexts.v:122), and every typing rule carries
$W$ as a parameter.

**Proposed.** Let $\Gamma$ start with the instance $(\prec_A, \varepsilon)$ of
the world's facts at no variables, so that `fl Γ` has one generator plus
transitivity and `typed` loses the parameter $W$ (the world then appears only
at P-Term, which builds the initial $\Gamma$, and in `wmodels`).

**Why.** One order judgment, one fewer parameter on 30 rules.

**What could break.** `cons_open` and `acyc_new` read $W$ and $\Gamma$
separately only through `slt`, so they are unchanged. Renaming of constants
(`typed_ren`) must rename the first hypothesis.

**Confidence.** Medium. Low priority.

## Quirks

- **Q1 (resolved on the map).** Contexts showed end types as $S_x^{a}$ while
  `tentry` (static/Contexts.v:24) has credit and tickets. Now $S_x^{a,m}$.
- **Q2.** $a \leq m$ is not an invariant of the syntax. `cr_tk Θ`
  (static/Contexts.v:32) is a hypothesis of `fsem_of_cost` (cost/CostFund.v:62)
  and the rules keep it only for the types they produce. A context entry
  $S_x^{5,2}$ is accepted by E-Chan. Make it part of well-formedness or of
  `TSess`.
  **Status (2026-11-22, branch fx-cost): done, variant "check at the
  rules".** E-Chan asks `fle a m`, and `thage` asks `fle (te_cr e) (te_tk e)`
  of each end it ages. `typed_cr_tk` (static/Typing.v) proves that every
  context that types a term satisfies `cr_tk`, and `fsem_of_cost`,
  `lf_p_term` and `fw_fsem` lose the hypothesis. A check at E-Chan alone
  does not suffice, because aging hides the original credit: under E-Abs at
  credit 3 the entry $S_x^{5,2}$ reaches E-Chan as $S_x^{2,2}$. The variant
  in the syntax of `TSess` would have to constrain every type, also payload
  and result types where nothing reads $a \leq m$, and would change every
  constructor use. The chosen variant adds one rule premise (E-Chan) and
  one conjunct to one definition (`thage`).
- **Q3.** `sinsts N ss` has the clause `N = None → Forall (λ s, sty_df s = s) ss`
  (static/Contexts.v:503), a lock-free detail inside a deadlock-free premise,
  needed only so that `typed W None` is conservative. With F12 the clause is
  the only trace of annotations in the deadlock-free judgment.
- **Q4.** E-Open asks `¬ unlimited T` (static/Typing.v:179) for a reason of
  the renaming lemma. An existential over a box is harmless and cannot be
  opened.
  **Status (fx-static).** Kept. Dropping the premise builds through the renaming lemma (`lren_insert` needs only the existential linear) and fails in cost/Exact.v. `lsame_pinst_insert` and `typed_vfacts` need the opened entry linear, so that each linear variable of a typed term occurs in it. An existential opened at an unlimited body could otherwise be dropped unused. The reason the map gives is corrected.
- **Q5.** `ex_wf` at E-Pack (static/Typing.v:173) is justified by the
  algorithmic system (eager opening), not by soundness. A reviewer will ask
  why a declarative rule carries it.
- **Q6.** The theorems `lf_soundness_h`, `lf_fundamental_h`, `lf_p_term`
  state `N ∈ ℕ` beside `ptyped (Some N)`; one of the two is enough.
  **Status (fx-static).** No change. The Rocq states only `ptyped (Some N)` with `N : nat`. The map writes $\vdash^{N}$ for both instances, so $N \in \mathbb{N}$ on the theorem rows is the display of `Some N` and stays.
- **Q7.** `fundamental` and `typed_sem` (static/Fundamental.v:787, 535) take
  `sworld_wf W`. The pass did not find where the proof uses it; `wmodels`
  does not need it. To check.
  **Status (fx-static).** Kept. `typed_sem` uses `sworld_wf W` through `slt_sem`, which instantiates facts of $W$ by `sw_lt_pinst` and needs them at constant roots. `fundamental` passes it on.
- **Q8.** P-Act-Msg and P-Act-Choice (lang/Process.v:166, 175) have no
  premise `ech o ∈ C`, P-Act-Close has. Harmless for typed processes (the
  map says why), odd for an untyped semantics, where two threads may
  synchronize on an interface channel.
  **Status (fx-static).** Not done. Adding `ech o ∈ C` to P-Act-Msg and P-Act-Choice needs it also on the multiset steps of lang/Process.v, in `partner_need` and the progress proof of lang/Safety.v, in `compat_enabled` (soup/LFLocal.v) and its callers in soup/LFAdequacy.v, and in compat/Connect.v. Removing it from P-Act-Close instead breaks the proofs that read the premise of a close step (`HC` in soup/LFRunFacts.v, soup/LFEvents.v and soup/SoupRun.v). Neither is a soundness problem, both change the process semantics that `deadlock_free` and `lock_free` quantify over, and both reach beyond this pass.
- **Q9.** The link label is a set $\{o_1, o_2\}$ and the event carries the
  ordered pick $(o_1, o_2)$; readiness treats a stuck link as ready
  (`link_t`). A link is thus both an internal step and a session label.
- **Q10.** `world` asks program order and transitivity only on rooted points
  (`w_ord_po`, `w_ord_trans`, types/Worlds.v:520) and `w_lt` adds program
  order for unrooted points separately. One order on all points with program
  order built in would be one definition less.
- **Q11.** The relation's value clause at an end compares session types by
  $\approx$ (annotations erased) while subtyping compares by $\simeq$
  (annotations equal). Correct, but two equivalences on one syntax.
- **Q12.** `p_connect_n` concludes `∃ W, ptyped N W Σ p T ∧ facts W ⊆ facts (⊔ W_i)|_I`
  (static/ConnectN.v:102) rather than equality, so the n-ary rule is weaker
  than the fold of binary ones by an unnamed world.
- **Q13.** `e_box` quantifies over all instances `∀ ss, sinsts N ss → typed …`
  (static/Typing.v:113), a derivation per instance, while `typed_sinst`
  (static/Sinst.v) shows the identity instance suffices. The rule could ask
  the identity instance only.
  **Status (fx-static).** Not done. `typed_sinst` asks the contexts contractive (`lenv_contr Δ`) and an instance changes the box type in $\Delta$ unless its session variables are bound, so E-Box with the identity instance needs two premises the rule does not have. The fundamental theorem also reads the body at each instance by induction, and an instance obtained by `typed_sinst` is no subderivation.
- **Q14.** `e_send` has both `hbot T = false` and the heads condition
  (static/Typing.v:125); the map merges them into $x \prec T$. Fine on the map,
  two premises in the Rocq.
  **Status (fx-static).** Done. `below_ty W Γ x T := hbot T = false ∧ ∀ y ∈ heads T, slt W Γ x y` (static/Contexts.v) is the one premise of `e_send`, at the payload $T[x\cdot i]$ (`hbot_payload_at`). `d_send` keeps its two premises and builds `below_ty`.

## Check fix reported

`docs/explorer/ext/gv-check.js`, one line: the DF-LEAK regex `lock[- ]free`
matched "deadlock free", which had led earlier edits to hide 22 deadlock-free
sentences from the deadlock-free view. Now `(?<!dead)lock[- ]free`.
