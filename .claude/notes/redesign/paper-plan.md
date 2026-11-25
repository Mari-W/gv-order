# Paper plan of 2026-11-22, bringing paper/*.tex up to the current design

Branch redesign-paper, from redesign at 6bef129. This is a plan only. No
.tex file was edited. The author drafts the paper and reviews this plan
before any drafting run.

Sources checked. The Rocq development v2/ at 6bef129 (built from a clean
tree on this branch, `make` exit 0, CheckAll.v 210 of 210 closed under the
global context, 14 further theorems checked by hand, see Part 3), the map
docs/explorer/gen/*.js, docs/redesign/pending.md (the reports of
2026-11-22 and the Decisions section) and docs/redesign/map-audit.md.

## 0. What the tex is written against

Every `\rocq{...}` name in paper/*.tex points into theories/, the old
development of the end-points branch. v2 imports nothing from theories/
(v2/README.md). The tex therefore describes a different system. It has
one channel name for both ends, constants as values with type schemes,
aliasing facts `≡`, future variables, creation constraints `cc_ok`, a
program constraint `C_0`, natural step indices, one world per process
judgment, and choice and context-free session types as extensions.

None of these survive in v2. Sections 2 and 3 of the paper need a
rewrite against v2, and sections 4, 4b and the appendix examples cite
programs that v2 does not have. The plan below goes file by file and
names the v2 replacement for each stale part.

Two consequences hold for the whole paper.

- The links. paper/rocqrefs.py generates the `\rocq` links from
  theories/. Every link has to be regenerated against v2 once the text
  names v2 declarations.
- The end type. The author fixed the notation `S_x^{a,m}` today. The
  point goes in the subscript, then credit and tickets in the
  superscript, and the deadlock-free sections write `S_x`. The tex writes
  `S@x` through one macro, listed in full in section 0.1.

### 0.1 Every use of the `@` notation in the tex

The tex writes the end type only through the macro `\sAt{S}{x}`, defined
at paper/preamble.tex:324-325 (`\NewDocumentCommand\sAt{mm}{{#1}{\color{cTy}@}{#2}}`).
No `S@x` appears as raw text. Redefining the macro to `{#1}_{#2}` changes
every use at once. The lock-free form needs a second macro with four
arguments, for example `\sAtA{S}{x}{a}{m}` for `S_x^{a,m}`. Uses, 69 in
total:

- paper/2-calculus.tex, 21 uses, lines 315, 388, 425, 426, 444, 470, 475,
  499, 608, 689, 690, 692, 693, 695, 698, 709, 917, 922, 925, 926, 930.
- paper/3-logical-rel.tex, 20 uses, lines 170, 171, 172, 182, 199, 223,
  319, 335, 337, 342, 344, 350, 358, 430, 434, 436, 446, 448, 454, 463.
- paper/4-extensions.tex, 15 uses, lines 20, 31, 39, 87, 89, 113, 114,
  118, 119, 152, 154, 160, 162, 170, 296.
- paper/7-appendix.tex, 13 uses, lines 95, 133, 248, 279, 303, 305, 322,
  337, 338, 377, 405, 492, 715.
- paper/preamble.tex:324 has the comment `% S@x, ...`.

Two uses need more than the macro change. 2-calculus.tex:470 and 475
write `\sAt{\sty}{\pntB}` and `\sAt{\tvar}{\pslot{\pself}{0}}` inside the
remark on payloads, which goes away with the payload notation (section
2.2 below). 4-extensions.tex:20, 87 and 89 put a recursion variable at
`\pslot{\pself}{0}`, which also changes with the payload notation.

### 0.2 Words the tex uses that the author has ruled out

- "gate" for our order check. 2-calculus.tex:954, 955, 1024,
  3-logical-rel.tex:98 ("gated by readiness"), 4b-subsumption.tex:13, 16,
  6-related-work.tex:47 ("The gate fact"), 7-appendix.tex:566.
- "slot". 4-extensions.tex:17 ("$n$ slots deep"). The macro `\pslot`
  (preamble, 92 uses) names the payload point and is not visible in the
  PDF. It goes with the payload notation.
- "priority" appears only for other systems. That use stays.

## 1. Section by section

### Abstract (paper/main.tex)

- Stale. There is no abstract. Commit 5bbf52a removed it from main.tex.
  The removed text held the universal claim "All soundness proofs of such
  session type systems in the literature hinge on topological
  constraints", which van den Heuvel, Derakhshan and Balzer ECOOP'24
  contradict (claim issue 5 in Part 3c).
- Replaces. A new abstract built on the standing decisions. The
  relation is the headline, it is compositional (`sem_p_term`,
  `sem_p_connect`, `sem_p_connect_h`) and it holds of programs the type
  system rejects (`sbv_thread_E`, `sbv_deadlock_free`, `sbv_rejected`).
  The universal claim becomes a claim about deadlock freedom. ECOOP'24
  drops the tree restriction for a deadlock-sensitive noninterference
  relation and removes APCP's priorities, so its relation establishes no
  deadlock freedom (`heuvel2024information` p1, p2, p7).
- New. The single-program and composed soundness theorems, the
  mechanization with no axioms, and EM and FC as hypotheses of the
  lock-free results if lock freedom is in scope (Question 1).
- Effort. Small.

### Section 1, Introduction (paper/1-intro.tex, 15 lines)

- Stale. 1-intro.tex:8 "Every result in this paper is mechanized in
  Rocq." This holds of v2 only once the subsumption theorems, the
  harmony theorem and the appendix examples are ported or cut (Part 5).
  The intro has no other text yet. The author writes it by hand.
- Replaces. A running example from the first page, the self-computed
  flag of v2/examples/SemBranch.v (map block `ex-flag`). The thread
  computes `not (inj₂ ∗)`, branches on the result and closes `c` and `d`
  in the order the flag picks. The partner closes `c̄` then `d̄`. The
  standing decision named theories/examples/SemFlag.v and
  `mixed_soundness`. Both exist only in theories/. On v2 the example is
  the variant `sbv` whose arms read their binder (Decisions,
  2026-11-21, "E-Open asks conservativity"). It holds on this branch, see
  Part 3.
  - `sbv_rejected` and `sbv_rejected_h`. No world and no bound type the
    closed process, in the full and the hidden judgment.
  - `Tbad_not_cons`. E-Open cannot supply the dead arm's fact, because
    opening must be conservative.
  - `sbv_thread_E`. The thread is in `E` at every index. Three β steps
    reach the live arm (`Erel_det`), and the fundamental theorem places
    the live arm in a world with `x ≺ ȳ` alone.
  - `sbv_deadlock_free`. `sem_p_term` on each side, `sem_p_connect` at a
    strict model of the joined world (`dmodels_exists`), then `adequacy`.
    No excluded middle.
- New. The contributions list with Rocq names (Part 3). The two
  citation points the intro must get right. Lindley and Morris proved
  deadlock freedom for GV and translate GV and CP in both directions
  (`lindley2015semantics` p2). The ECOOP'24 sentence above.
- Cut. Nothing.
- Effort. Medium (author's prose, the plan only fixes the content).

### Section 2.1, Syntax and semantics (paper/2-calculus.tex:1-308)

- Stale.
  - 2-calculus.tex:9-19, "Variables are ranged over by $\vr, \vrB$ and
    channels by $\ch, \chB$", and `new ()` as a constant applied to unit.
  - 2-calculus.tex:21-55 (Fig. syntax). Constants `new, spawn, recv,
    send, close, link, force` are values. No select or branch.
  - 2-calculus.tex:148-149, "Both ends of a channel carry one name:
    T-Act-New returns the pair ⟨c, c⟩".
  - 2-calculus.tex:57-146 (Fig. term semantics). Labels without choice,
    `\lNew{\ch}` returns `⟨c, c⟩`.
  - 2-calculus.tex:150-158, the subject and sent-channel functions `fc`
    and `sent`.
  - 2-calculus.tex:190-196, "Theorem [Harmony \rocq{harmony}]". v2 has
    no reduction semantics and no harmony theorem.
  - 2-calculus.tex:204-268 (Fig. process LTS), one name per channel,
    link as substitution of names.
  - 2-calculus.tex:283-300, terminated, safe, deadlock free, cite
    theories/ names.
- Replaces.
  - Ends `c⁺` and `c⁻` of a channel `c`, `ō` the other end, `ech o` its
    channel (map `syn-ends`, Syntax.v `cend`, `ech`, `edual`).
  - Thirteen term formers with `new` a term and every operation a
    saturated constant `k e` (`syn-terms`, `syn-prims`, `syn-values`,
    Syntax.v `expr`, `prim`). A constant applied to a value is a redex,
    never a value. Select and branch are core constants.
  - Labels with `o◁i` and `o▷i`, links on an unordered pair of ends
    (`sem-labels`, `sem-head`, `sem-ctx`, Semantics.v `slabel`,
    `tlabel`).
  - `fends` and `fchans` (`syn-fends`). Remark rm:sentc (178-188) stays
    in substance. The relation still reads ownership off terms.
  - Process `(C, E)` and the instrumented configurations with thread
    names and events, erased to the plain step (`syn-procs`, `sem-proc`,
    `sem-events`, Process.v `istep`, `pstep`). Link renames `ō₁` to `o₂`
    in the other threads (`syn-csub`, `csub`).
  - `terminated`, `safe`, `deadlock_free` of lang/Safety.v (`sem-props`).
    `no_tau_divergence` and `lock_free` only if lock freedom is in scope.
- New. Choice labels and the choice step in the process LTS.
- Cut. The harmony theorem and the appendix it points to (7-appendix.tex
  835-931), unless v2 gains a reduction semantics (Question 6).
- Effort. Medium.

### Section 2.2, The static system (paper/2-calculus.tex:310-1036)

Everything in this subsection is stale. The order below follows the tex.

- Points, 2-calculus.tex:314-381 (Fig. points).
  - Stale. 327, "$\pnm ::= \pviA \sepr \pcst \sepr \pslot{\pntA}{j}$" and
    333, facts `x ≺ y` and `x ≡ y`. 370-375, hatted facts.
  - Replaces. A point has a root, a constant `a` or a variable `ι`, a
    polarity and an offset. `x̄`, `x⁺` and the field `x·κ` (`syn-points`,
    `syn-moves`, `syn-labels`, Points.v `point`, `pt_dual`, `pt_shift`,
    `pt_field`). Facts are `x ≺ y` only (`fact`, `FLt`). A constraint is
    a set of facts under binders, finite or infinite (`bcs`). An action
    moves an end from `x` to `x⁺`, a choice to a field, and the `j`-th
    payload end arrives at `x·j`.
  - Cut. Aliasing. Hatted facts, unless the subsumption section stays.
- Types, 2-calculus.tex:383-490 (Fig. types, Def. payload, Remark
  payload).
  - Stale. 394, "$\payty ::= \ty$ subject to points(T) ⊆ {self·j}", 434
    `\payloadAt`, 456-464 Def. payload with `\pself`, 466-483 Remark
    payload (`kscoped`, `payload_pinst`, `sren_ty`, `sflip_ty` are not in
    v2). 391, session types without `Skip`, sequencing and choice.
  - Replaces. Types `1, T ⊗ U, T ⊕ U, T ⊸^u_l U, S_x, □∀ῑ∀ᾱ. C ⇒ ...,
    ∃^l ῑ. C. T` (`ty-grammar`, Types.v `ty`). Session types with
    `Skip`, `S.S`, `⊕`, `&`, `µ`, `α`, `ᾱ` (`ty-session`, `sty`), read
    through `unfoldS`. Duality (`ty-dual`, `dual`), equivalence `≃` and
    `≈` (`ty-equiv`, `sequiv`), contractivity (types/Contractive.v
    `scontr`, `tcontr`). The payload in the paper's notation
    `!^{ƛσ}(T).S` with fields `σ.κ`, decided for the paper. The Rocq
    writes `SSnd m T` with numeric binders, and `payload_at` places them
    at `x·0, …, x·(m−1)` (`ty-payload`). The paper states this
    correspondence once, in the mechanization section.
  - Point substitution, 413-431. `pt_inst` and `pinst_ty` still exist
    and keep their roles.
- Contexts and the judgment, 2-calculus.tex:492-522.
  - Stale. 496-502, "The fact context $\fctx$ holds facts ... and facts
    $\fLt{\ubd}{\pfv}$ for future variables". 518-522, "A source program
    has $\tenv = \emptyset$ and no constant in $\fctx$ (\rocq{styped})".
  - Replaces. `Θ ; Γ ; Δ ⊢^F e : T` over a static world `W` (`t-judgment`,
    `t-contexts`, Typing.v `typed`, `dftyped`). The future is a set of
    points with a rest, everything above `u` or everything, or the flag
    `⊥`. No future variables (Decisions, entry 14b). `Γ` holds the facts
    of opened binders. The world `W` holds constants and facts
    (`sworld`). The order judgment `Γ ⊢ x ≺ y` is the least transitive
    relation with `≺_W` and the instances in `Γ` (`slt`).
- Fact theory, 2-calculus.tex:524-651 (Fig. facts).
  - Stale. 526-568, the seven aliasing rules A-Hyp to A-Dual. 585-597,
    O-EqL and O-EqR. 606-633, `heads` with absent and `⊥` bounds.
  - Replaces. Program order `x ≺ x⁺` and `x ≺ x̄⁺` with transitive
    closure (`w-order`). `ap(T)`, the dual points of the ends in a value,
    with `⊥` for hidden ends (`ty-heads`). The side conditions
    `u ≺ F`, `x ≺ T`, `l ≼ Δ` (`t-side`).
  - Cut. Aliasing and its two order rules. The figure shrinks to a
    third.
- Constants, 2-calculus.tex:653-718 (Fig. signatures).
  - Stale. 654-659, "A constant has a constrained type-indexed scheme
    ... (\rocq{konst_sig})". 666-670, "$\tLink$ asks
    $\fEq{\pntA}{\pdual{\pntB}}$". 672-678 and 706-711, `new` as the one
    constant outside the schemes, with a creation constraint.
  - Replaces. One rule per constant, E-Send, E-Recv, E-Close, E-Select,
    E-Branch, E-Link, E-Spawn, E-Force (`r-act`, `r-threads`, `r-force`,
    `t-consts`, Typing.v `e_send` to `e_force`). E-Link takes a pair at
    `x` and `x̄` and asks no order fact (`e_link`). `new` has the two
    rules of section "E-New" below.
- Term rules, 2-calculus.tex:720-859 (Figs. typeSys and typeSysPoints).
  - Stale. 743-749, E-Const. 755-761, E-Abs with "$\pfv$ fresh" and
    `\fctx, \fLt{\ubd}{\pfv}`. 818-823, E-Conv "up to $\fctx \types
    {\equiv}$". 825-834, E-Exp with a future variable and points only.
    836-843, E-Pack without well-formedness. 845-852, E-Open without
    conservativity.
  - Replaces. E-Abs types the body under everything above `u`
    (`r-fun`, `e_abs`, `abs_fut`). E-Box over points and session types,
    each instance contractive, typed once per allowed list `s̄`
    (`r-boxes`, `e_box`, `sinsts`). E-Sub with Sub-Ex by entailment and
    lowering of `l` (`t-subs`, `e_sub`, `tsub`, `sub_ex`, `lb_lower`,
    proved by `Vrel_tsub`). E-Pack asks `ex_wf` (`r-ex`, `e_pack`).
    E-Open asks `cons_open W Γ m C` and `¬ unlimited T` (`r-ex`,
    `e_open`). Weakening and contraction are admissible (`r-admis`,
    static/Weakening.v).
- E-New, 2-calculus.tex:861-908.
  - Stale. 861-878, "Definition [Creation constraint \rocq{cc_ok}]",
    acyclic relative to `Γ` and conservative. 880-895, annotations
    `\tNewC`, `\tBoxA`, `\tAbsA`, `\tForceA` and `t_new_open`. 897-908,
    "The creation constraint of a program" `C_0` and `c0_creation_ok`.
  - Replaces. Plain `new` with two rules (`r-new`, `e_new`,
    `e_new_fld`). E-New at a fresh root `ρ` returns
    `∃^⊥ ρ. C. (S_ρ ⊗ S̄_ρ̄)` and asks `new_ok N W Γ C`. At `N = ∞` this is
    `acyc_new`. The order that `C` and program order induce on the tree
    of `ρ` has no cycle, and `Γ` derives `z ≺ y` for each bridge from `z`
    through the tree to `y` (`cbridge`). E-New-Field returns the pair at
    `x·κ` and `x·κ̄`, with no constraint and no existential. The source
    soundness theorem takes an acyclic static world in place of `C_0`
    (`soundness_source`, `sacyc W`). Annotations follow the algorithmic
    decision of 2026-11-21. An erased `unpack x as ῑ` names opened
    points, and `(new : ...)` fixes a position where the expected type
    does not.
  - New. Lemma C, `gen_new_acyc`. The finite-bound premise implies the
    acyclic one, constructively. Needed only if lock freedom is in
    scope.
- Example Delegation, 2-calculus.tex:910-975.
  - Stale. 922-927, the second `new` places `b` by "$\fEq{\pviB}{\pslot{\pviA}{0}}$".
    954-955, "gates". `deleg_main`, `deleg_typed`, `deleg_deadlock_free`
    are theories/ names.
  - Replaces. The second creation becomes E-New-Field at `ρ·0`. v2 has
    no delegation example. Port it or replace it by `ex-between`
    (FreshBetween.v `fb_typed`), which also places a channel between two
    others (Question 5).
- "Why each end has its own point", 2-calculus.tex:977-984. Still true.
  Keep.
- Example bit, 2-calculus.tex:986-1035.
  - Stale. `bit_main`, `bit_typed`, `bit_deadlock_free` are theories/
    names. 1024 "gate".
  - Replaces. Either a port, or the running example's partner, which
    makes the same point about one point per end. The received bit types
    statically here. It is no semantic example.
- Effort. Large.

### Section 3, The logical relation (paper/3-logical-rel.tex)

- Goals, 3-logical-rel.tex:4-24.
  - Stale. 21-24, "No example in this paper establishes membership for a
    process that the static system refuses, and every example of
    \cref{sec:examples} goes through \cref{th:fundamental}."
  - Replaces. The running example does exactly that (`sbv_thread_E`,
    `sbv_rejected`). This paragraph becomes the pointer to it.
- Worlds, 3-logical-rel.tex:27-96.
  - Stale. 33-48, "A world $\wrld = (N,{\equiv}_{\wrld},{\prec}_{\wrld})$
    ... well formed ... strict". 50-58, `wext` and `wext_fresh`. 60-65,
    `wext_cc`. 74-86, "Theorem [Amalgamation \rocq{amalgamation}]".
    88-96, "Theorem [Fresh extension \rocq{fresh_extension}]".
  - Replaces. Two kinds of world (`w-world`, Worlds.v). A static world
    `W` holds constants and facts (`sworld`). A world `R` of the relation
    holds roots and a strict partial order on rooted points that
    contains program order, with a kind field (`world`, `w_ord`, `w_rk`).
    The deadlock-free relation reads strict worlds (`wstrict`).
    `R ⊨ W` (`wmodels`). Extension keeps roots, order and kind (`w-ext`).
    A creation at a fresh root grows a strict world by the facts of `C`
    and transitive closure (Proposition A, `Erel_new_acyc`). An acyclic
    well-formed static world has a strict model, its own order
    (`dmodels_exists`). The join of two static worlds is acyclic exactly
    when their restrictions to the shared constants join acyclically
    (`acyc_join_iff`).
  - Cut. Fresh extension. Composition no longer grows a joined world.
    Hiding and renaming of private constants take its place (`typed_ren`,
    `fptyped_ren`, `swrestrict_iff`).
- Readiness, 3-logical-rel.tex:98-185.
  - Stale. 98, "gated". 102-104, "Entries are compared, not names" and
    the thread that holds both ends of one channel. 106-150, `ready_t`
    and `ready_p` with entries.
  - Replaces. Readiness on ends (`rd`, Readiness.v `ready`). A stuck
    process is at a link, or has finished, and each interface end it
    keeps has an offered end below its dual point. Internal channels
    have no points. The two examples 161-185 survive with `S_x`.
- The relation, 3-logical-rel.tex:187-502 (three figures).
  - Stale. 195-196, "The index $n \in \Nat$ is a step index". 197-209,
    `senv` versus `tenv` with both ends under one name, `tenv_comp`.
    219-231, V-Chan up to `≡` and V-Const. 260-270, V-Box over points
    only. 291-293, E-Zero. 314-322, O-New with `wext_fresh`. 353-360,
    O-Link with `≡`. 369-382, `tcost`, `pcost`, `Efuel`. 398-415, P-Zero
    and P-Intro without fusion. 418-425 and 473-478, Q-Tau grows the
    world freshly. 457-464, Q-Link with `≡`.
  - Replaces. Ordinal indices with `osfix` (`sr-ord`, relation/Ord.v),
    cost tables `κ_DF` (`ct-costs`, CostTable.v). `Θ` maps ends to types
    (`sr-reading`). V by recursion on the type, a box safe when its
    thunk is safe at each point and session instance (`v-rel`, `v-box`,
    Relation.v `Vrel_box_iff`, `Vrel_ex_iff`). E with its three clauses
    at every index, `0` included (`e-rel`, `Erel_iff`). Obligations with
    O-New at a fresh root or at a field, O-Select and O-Branch, O-Link
    with no point premise (`e-obl`). P with the fusion clause `(h, D)·p`
    (`p-rel`, `p-fuse`, `pfuse`, `fuse_ok`, kept by Decisions entry 15),
    its obligations (`p-obls`).
  - Remark rm:vabs, 384-394, stays. Update the names.
- Fundamental property, 3-logical-rel.tex:504-812.
  - Stale. 526-541, `sem_typed` and `sem_ptyped` with `n ∈ ℕ` and
    `W' ⊒ W`. 543-552, `term_wf`, `typed_term_wf_s`. 554-582, `Prel_steps`,
    `Prel_safe`. 596-624, the compositionality table with 18 theories/
    names. 632-660, `sem_typed_lam`, `sem_typed_box`. 662-702, the
    P-Connect lemma and a list of 60 theories/ names. 704-709,
    "strictness of the composed world is needed:
    \cref{thm:amalgamation,thm:fresh-extension} supply it". 749-761, the
    two-stage proof that "instantiates the future variables".
    782-812, source soundness through `C_0` (`wnil`, `wc0`,
    `c0_creation_ok`).
  - Replaces. Semantic judgments over ordinal indices, larger worlds and
    groundings, at a static world through every strict model (`sj-all`,
    SemTyped.v `sem_typed`, `Grel`, FundamentalProc.v `sem_ptyped_sw`,
    `sem_ptyped_h`). Adequacy (`th-adequacy`, `adequacy`, `adequacy_h`).
    The table becomes one row per rule with the v2 lemma, `later_unit` to
    `later_force` of compat/LiveRules.v and `Erel_send` to `Erel_force`
    of compat/Redex.v, `Erel_bind`, `Vrel_tsub`, `sem_p_term`,
    `sem_p_connect` (`th-fund-term`, `th-bind`, `th-compose`). The
    P-Connect lemma at one world with fusion (`sem_p_connect`,
    ConnectP.v), and the static form with hiding (`sem_p_connect_h`). The
    chain argument 711-723 stays in substance (`pc_ready`,
    `finite_lt_acc`). Fundamental theorems `fundamental` (term, strict
    `R ⊨ W`) and `fundamental_proc_h` (`th-fund-proc`). Soundness
    `soundness_h` and `soundness` (`th-sound`). Source soundness
    `soundness_source` with `sacyc W` (`th-sound-src`).
  - New. The running example inside the relation, `sbv_thread_E` and
    `sbv_deadlock_free` (section "Semantic examples" of the outline).
    Hiding in the process judgment, `ptyped` with P-Term at
    `swrestrict W (iface Σ T)`, `fptyped` as the auxiliary full judgment
    (`ptyped_full`, `fptyped_ptyped`). The n-ary connect,
    `p_connect_n` and `connect_n_soundness`.
- Effort. Large.

### Section 4, Examples (paper/4-extensions.tex:1-95)

- Stale. 13-93, "Example [The received chain \rocq{ch_main}]". `ch_main`,
  `ch_typed`, `ch_deadlock_free`, `ch_C`, `chs_C`, `chc_C`, `ch_sub` are
  theories/ names and v2 has no received chain. 17 "slots deep". 20 and
  87 put a recursion variable at `\pslot{\pself}{0}`.
- Replaces. The v2 examples, each with a closed result.
  - Client and server cycle, `ex-cs`, ClientServer.v `cs_typed`.
  - Cycle, `ex-cycle`, Cycle.v `cy_typed`.
  - Copycat, `ex-copycat`, Copycat.v `fwd_term`, `fwd_expand`,
    `fwd_config_deadlock_free`, and the two-forwarder ring rejected,
    `ring_rejected`.
  - Recursive fork-join with replies, `ex-forkjoin`, ForkJoin.v
    `fjr_dftyped`, `fjr_deadlock_free`, with Padovani's fact and fibo
    (`fct_deadlock_free`, `fib_deadlock_free`). The order on the tree is
    an infinite descending chain, acyclic and not well-founded, which
    is why the DF premise is `acyc_new`.
  - The three-thread ring, `ex-milner`, Ring.v `ring_pairs`,
    `ring_cyclic`, `ring_rejected`, the acyclic variant `ring_typed`,
    `ring_df`, and the two-channel cycle `cyc2_rejected`.
  - Private constants and hiding, `ex-shared`, SharedRoots.v
    `opposite_clash`, `opposite_compose`, `opposite_df`.
  - Creations with exits, `ex-gennew`, GenNew.v `te_dftyped`,
    `te_deadlock_free`, `tu_deadlock_free`.
  - Contractivity, `ex-sinst`, SinstStuck.v `typed_sinst_false`,
    `ss_var_guard`.
  - In the appendix, `ex-between`, `ex-many`, `ex-factory`, `ex-ring`.
- New. Each example states which rule it exercises. The rejections sit
  next to the accepted variant.
- Cut. The received chain, unless ported (Question 5).
- Effort. Large in prose, small in Rocq.

### Section 4, Extensions (paper/4-extensions.tex:97-361)

Choice and context-free session types are core in v2. The section
dissolves into sections 2 and 3.

- Choice, 4-extensions.tex:100-190.
  - Stale. 103-110, "The mechanized core has binary choice as primitive
    session types ... (\rocq{konst_sig})", `sel_pt`/`bra_pt` placement
    described with `\pslot`. 139-185, a separate figure of obligations.
    187-190, the choice encoding (`sel1_typed`, `sel2_typed`,
    `branch_typed`, `choice_deadlock_free`), not in v2.
  - Replaces. E-Select and E-Branch in the term rules (`r-select`,
    `r-branch`, `e_select`, `e_branch`). The branching end moves to
    `x·i` and the selecting end to its dual (Points.v `bra_pt`,
    `sel_pt`). The obligations join the figure of section 3.
  - Cut. The encoding paragraph.
- Context-free session types, 4-extensions.tex:192-361.
  - Stale. 200-311, two figures of "changed definitions" (`hc`,
    `hcontractive`, `E-Exp-CF`, `KSForce`, `eqT`). 318-332, walks and
    ceilings. 333-348, `sendTree_ty`, `tree_deadlock_free`,
    `sch_deadlock_free`, `ts_deadlock_free`, `as_deadlock_free`,
    `dlfix_deadlock_free`, `dl_untypable`, `si_deadlock_free`,
    `sd_deadlock_free`. 351-354, `sd_not_deadlock_free`. None is in v2.
  - Replaces. `Skip`, sequencing, choice and session-polymorphic boxes
    in the core figures. Contractivity and `typed_sinst` with its
    counterexample in the type section or the appendix.
  - Cut. Walks, ceilings and the tree programs, unless ported
    (Question 5).
- Effort. Medium.

### Section 4b, Subsumption (paper/4b-subsumption.tex)

- Stale. The whole section. The translations of PGV, Padovani and
  Novara, and Mordido and Pérez live in theories/pgv, theories/pn and
  theories/mp. v2 has none of them. 13-17 identify each point of the
  image with its partner by `x ≡ x̄`, and v2 has no `≡`. 13 and 16 say
  "gate".
- Replaces. Nothing in v2 yet. Hatted facts expand to four `≺` facts, so
  a priority translation may work without `≡`. That is a Rocq task, not a
  paper edit.
- Cut. Theorems thm:pgv and thm:pn until ported (Question 2). The
  comparison with Padovani and Novara's levels (121-139) can move to
  related work as prose.
- Effort. Large if ported, small if cut.

### Section 5, Mechanization (paper/5-formalization.tex)

- Stale. 5-12, "Everything this paper states is mechanized ... the two
  embeddings ... The translation of the system of \citet{MordidoP} is
  mechanized as well (\rocq{mp3_deadlock_free_source})". 22-35, counts
  for theories/ (54,662 lines, 137 files). 41-62, the table by old
  directories. 64-68, "it has to keep the composed world strict, which
  is what \cref{thm:amalgamation,thm:fresh-extension} are for".
- Replaces. v2 has 129 files outside test/ and 38,584 non-blank lines
  before comment stripping. A drafting run recounts with the comment
  rule of the existing footnote (5-formalization.tex:25-30). Rows by v2
  directory: lang, types, static, relation, compat, cost and fuel, soup
  and lockfree, examples. No axiom (CheckAll.v, 210 of 210). EM and FC
  are explicit hypotheses of the lock-free results only, DC of the fair
  run lemma. The hard proof is semantic P-Connect with fusion
  (compat/Connect*.v).
- New. One sentence on the payload binders, numeric in the Rocq and
  fields `σ.κ` in the paper. One sentence on ordinal indices.
- Effort. Small.

### Section 6, Related work (paper/6-related-work.tex)

- Stale.
  - 9-12, CLASS "based on an extension of second-order linear logic".
    Correct as far as it goes. CLASS is second-order linear logic with
    DiLL co-exponentials (`rocha2023safe` p2). Claim issue 2.
  - 20-21, "\citet{DBLP:conf/ecoop/0001DB24} extend that work to cyclic
    processes." One passing clause for the closest semantic competitor.
    Claim issue 5.
  - 36-53, Kobayashi with "inner tags are the payload points
    $\pslot{\pntA}{j}$" and "creation constraint" (42-43), "The gate fact"
    (47).
  - 61-69, P&N with "It mentions only the points $\pslot{\pself}{j}$".
  - 74-77, PolyVGR, "Both ends compute the same payload point
    $\pslot{\pntA}{j}$". True for fields. Update the notation.
  - 102-163, Table tab:related, column "Here" with "creation
    constraint", "payload points", "send's premise", "E-App".
  - 169-170, "\citet{DardhaG18} note that this rejects Milner's cyclic
    scheduler, which \cref{ex:scheduler} types." v2 has no Milner
    scheduler (Part 3b).
  - 178-181, "liveness properties such as lock freedom ... among them"
    listed as open. False if lock freedom is in scope.
  - 190-192, "Multiparty session types~\cite{HondaYC16} need
    priority-based annotations for programs that interleave several
    sessions". Claim issue 3.
- Replaces. Fields `σ.κ` and E-New in the comparisons. A paragraph on
  ECOOP'24. A sentence on MPGV with a new bib entry.
- New. Lock freedom related work if in scope (Padovani 2014, Kobayashi
  2002 already in main.bib). Measured boxes as future work, one sentence
  at most.
- Effort. Medium.

### Appendix (paper/7-appendix.tex)

- Typing running threads and processes, 7-appendix.tex:63-189.
  - Stale. 66-79, `fctx` triple, `styped`, `wnil`,
    `typed_world_transfer`. 91-96, E-Ch "up to aliasing". 98-109, E-Weak
    and E-Contract as rules. 118-120 and 141-163, `prim`. 129-137,
    `balanced` with `≡`. 165-182, P-Term and P-Connect at one world `W`.
  - Replaces. E-Chan exact (`r-chan`, `e_chan`). Weakening and
    contraction admissible. `tfree` (`ty-kinds`). The restricted
    channels of P-Term at dual types at `x` and `x̄` with `tsum_ok`.
    P-Term at `swrestrict W (iface Σ T)`, P-Connect asks
    `wok N (W1 ⊔ W2)`, which is `sacyc` at `N = ∞` and `swf` at a finite
    `N`, and hides the cut (`p-typing`, Typing.v `p_term`, `p_connect`).
    The full judgment `fptyped` and `ptyped_full`. The n-ary connect as
    an admissible rule (`p_connect_n`).
  - Effort. Medium.
- Further examples, 7-appendix.tex:192-546.
  - Stale. `sync_main`, `cycle_main`, `blocked_main`, `some_main`,
    `none_main`, `rr_main`, `fw_main` (whose constraint uses `≡` at
    317), `fwsrv`, `fcsrv`, `ms_main`, and the rejections
    `rr_call_underivable`, `ord_no_constraint`, `sched_rev_underivable`,
    `ms_rev_underivable`, `badlink_underivable`. All theories/.
  - Replaces. `ex-between`, `ex-many`, `ex-factory`, `ex-ring`,
    `fwdh_term` and `fwdp_expand` of Copycat.v, `tu_deadlock_free`. The
    rejections of v2, `ring_rejected` (both files), `cyc2_rejected_h`,
    `sbv_rejected_h`, `tu_rejected_wf_new`, `te_rejected_wf_new`,
    `typed_sinst_false`, `fp_unrealizable`, `fj_wait_needs`.
  - Effort. Large.
- End points against priorities, 7-appendix.tex:548-587. The argument
  stands. 566 "gate". 577 `cycle_typed` becomes Cycle.v `cy_typed`.
  Small.
- Order obligations of the delegation example, 7-appendix.tex:589-650.
  Goes with the delegation example. Cut or redo after the port.
- Duality and equivalence, 7-appendix.tex:652-833. Recursive duality
  with `ᾱ` stays (Types.v `dual`, Duality.v `dual_unfoldS`). Equivalence
  becomes `sequiv` through `unfoldS`, with `Skip` and sequencing. 797-805
  "Facts" with `≡` goes. Medium.
- Reduction semantics and harmony, 7-appendix.tex:835-931. No v2
  counterpart. Cut (Question 6).

## 2. Proposed outline

The structure changes. Choice and context-free session types join the
core, the running example gets its own section after the relation, and
the extensions section disappears.

0. Abstract.
1. Introduction. The running example `sbv` on page one. The static
   system rejects it, the relation accepts the thread, and the thread
   composes with a typed partner to a deadlock-free process.
   Contributions with theorem names.
2. GV♯. Syntax with ends, saturated constants and `new` as a term.
   Labelled thread steps, process steps, link as renaming. Deadlock
   freedom.
3. Typing.
   1. Points, fields and program order.
   2. Types and session types with `Skip`, sequencing, choice, recursion
      and the payload `!^{ƛσ}(T).S`. End type `S_x`. Duality, equivalence,
      contractivity.
   3. Static worlds and the order judgment `Γ ⊢ x ≺ y`. `ap(T)` and
      futures.
   4. Term rules. One rule per former and constant, E-Box over points
      and session types, E-New and E-New-Field with `acyc_new`, E-Pack,
      E-Open with conservativity, E-Sub with Sub-Ex.
   5. Process typing with hiding. P-Term at the interface world,
      P-Connect on the acyclic join, the n-ary connect as an admissible
      rule.
   6. Static examples. Cycle, client and server, fork-join, copycat. The
      three-thread ring and the two-channel cycle as rejections that show
      why P-Connect checks the joined order.
4. The logical relation.
   1. Worlds of the relation, strict orders and `R ⊨ W`. Creation grows
      a strict world (Proposition A). Ordinal indices in two sentences.
   2. Readiness.
   3. V, E and P, with fusion in P.
   4. Semantic judgments at static worlds, hidden form.
   5. Adequacy.
   6. Compositionality. `sem_p_term`, `sem_p_connect`, `sem_p_connect_h`.
      Fundamental theorems and soundness, single program and n-ary.
5. What the relation adds.
   1. The running example in the relation (`sbv_thread_E`,
      `sbv_deadlock_free`) against `sbv_rejected` and `Tbad_not_cons`.
   2. Private constants (`opposite_df` against `opposite_clash`). The
      relation composes components whose private orders disagree.
   3. The limit of compositionality. Two threads on one received flag
      (`ex-flagpair`). Thread by thread the relation fails
      (`fp_unrealizable`). The whole process is deadlock free by an
      argument over its reductions that is not mechanized.
6. Lock freedom (if Question 1 says so). `S_x^{a,m}`, credit and
   tickets, E-Link with `lgt`, `tsum_ok`, ranked worlds and `gen_new`,
   the guard, fuel, the theorem under EM and FC. The four `rx-*`
   programs as rejections. Rules in the appendix.
7. Mechanization.
8. Related work and future directions.

Appendix. A. Full typing and process rules, the full judgment
`fptyped`. B. Full obligations of E and P. C. Duality, equivalence and
contractivity with `ex-sinst`. D. Further examples (`ex-between`,
`ex-many`, `ex-factory`, `ex-ring`, `ex-gennew`, copycat schema, fact and
fibo). E. End points against priorities. F. Subsumption, only if ported.

Placement of the four new structural items. Hiding goes into 3.5 (the
rules) and 4.6 (`sem_p_connect_h`), with `ex-shared` in 5.2. The two
kinds of world split as follows. Static worlds go into 3.3, worlds of the
relation into 4.1, and the strict and ranked kinds appear only in
section 6, because deadlock freedom reads strict worlds alone. The n-ary
connect goes into 3.5 as an admissible rule and is used once, in the
three-thread ring of 3.6.

## 3. Claims the paper will make

### 3a. Checked on this branch

Built from a clean tree on redesign-paper at 6bef129. `make` exit 0,
CheckAll.v prints "Closed under the global context" for each of its 210
lines. A scratch file checked the 14 theorems marked (s), each closed
under the global context. "Hyp." lists the classical hypotheses in the
statement. "none" means no classical hypothesis.

| Claim | Rocq | Hyp. |
|---|---|---|
| A closed process typed with hiding is deadlock free | `soundness_h` (static/FundamentalProc.v) | none |
| The same for the full judgment | `soundness` | none |
| A closed typed program over an acyclic static world is deadlock free | `soundness_source` (premises `sworld_wf W`, `sacyc W`, `tfree T`) | none |
| Semantic judgment implies deadlock freedom | `adequacy` (relation/Adequacy.v), `adequacy_h` | none |
| Typing implies the semantic term judgment at each strict model | `fundamental` (static/Fundamental.v), `typed_sem` (s) | none |
| Typing implies the hidden semantic process judgment | `fundamental_proc_h`, `fundamental_proc` (s) | none |
| P-Term holds in the relation | `sem_p_term` (compat/PTerm.v), every cost table | none |
| P-Connect holds in the relation at one world | `sem_p_connect` (compat/ConnectP.v) | none |
| P-Connect at static worlds with hiding | `sem_p_connect_h` (s) | none |
| The n-ary connect is admissible and sound | `p_connect_n`, `connect_n_soundness` (static/ConnectN.v) | none |
| Running example, thread in the relation | `sbv_thread_E` (s), `sb_thread_E` (s) for the arm that ignores its binder | none |
| Running example, deadlock free | `sbv_deadlock_free`, `sb_deadlock_free` (s) | none |
| Running example, rejected by every world and bound | `sbv_rejected`, `sbv_rejected_h` (s) | none |
| E-Open cannot supply the dead arm's fact | `Tbad_not_cons` | none |
| Creation preserves a strict world (Proposition A) | `Erel_new_acyc` (compat/Redex.v), premise `wstrict` | none |
| Lemma C, the finite-bound premise implies the acyclic one | `gen_new_acyc` (s) | none |
| Acyclic join through shared constants | `acyc_join_iff` (s), `wf_join_iff` for well-founded | none |
| An acyclic static world has a strict model | `dmodels_exists` | none |
| Sub-Ex is sound | `Vrel_tsub` | none |
| Box bodies instantiate at contractive session types | `typed_sinst` (static/Sinst.v) | none |
| Without contractivity instantiation fails | `typed_sinst_false`, `ss_var_guard` | none |
| Lock-free typing at `N = ∞` is deadlock-free typing | `conservative` (static/Conservativity.v) | none |
| Fork-join with replies, fact, fibo deadlock free | `fjr_deadlock_free` (s), `fct_deadlock_free`, `fib_deadlock_free` | none |
| Copycat deadlock free, identity expansion | `fwd_config_deadlock_free`, `fwd_expand` | none |
| Two forwarders in a ring rejected | `examples.Copycat.ring_rejected` | none |
| Three-thread ring, pairwise acyclic, jointly cyclic, rejected | `ring_pairs`, `ring_cyclic`, `examples.Ring.ring_rejected` | none |
| Acyclic ring variant typed and deadlock free | `ring_typed`, `ring_df` | none |
| Two-channel cycle rejected | `cyc2_rejected`, `cyc2_rejected_h` (s) | none |
| Opposite private orders compose under hiding | `opposite_clash`, `opposite_compose`, `opposite_df` (s) | none |
| Creations with exits type and are deadlock free | `te_deadlock_free`, `tu_deadlock_free`, rejected by the simple condition `te_rejected_wf_new`, `tu_rejected_wf_new` | none |
| Received-flag pair fails thread by thread | `fp_unrealizable` (s) | none |
| Guarded typed process has no internal divergence | `live_soundness_h` | none |
| Lock-free soundness, hidden judgment | `lf_soundness_h` (soup/LFTyped.v) | EM, FC |
| Lock-free soundness, full judgment | `lf_soundness` | EM, FC |
| Lock-free fundamental theorem | `lf_fundamental_h` | EM |
| Lock-free P-Term | `lf_p_term` | EM |
| Lock-free P-Connect | `lf_p_connect` (s) | none |
| Lock-free adequacy at a static world | `lf_sems_adequacy` | EM, FC |
| Lock-free n-ary connect | `connect_n_lf_soundness` | EM, FC |
| Existential property of ordinal indices | `exist_prop` (relation/ExProp.v, section context) | EM, FC |
| A weakly fair maximal run exists | `fair_run_exists` | EM, DC |
| Lock freedom implies Padovani's formulation | `lock_free_padovani` | EM, DC |
| Creation at either kind of world | `Erel_new_any` | EM at ranked worlds only |
| Live judgment implies the DF judgment | `live_sub_df` | EM, FC |

### 3b. Claims that do not hold or are not mechanized on v2

- "Every result in this paper is mechanized" (1-intro.tex:8). False for
  every item of this list.
- Milner's cyclic scheduler types (7-appendix.tex:412-449,
  6-related-work.tex:169-170). v2 has no scheduler. v2's "Milner's ring"
  (Ring.v, map `ex-milner`) is a different program, three threads that
  each close two ends and deadlock. The name invites a wrong reading.
  I recommend renaming the map example to "three-thread ring" (Question
  7).
- The PGV and P&N fragments are deadlock free (4b-subsumption.tex,
  thm:pgv, thm:pn). theories/ only.
- Harmony of LTS and reduction semantics (2-calculus.tex:190-196).
  theories/ only.
- Every example of the current tex. `ch_main`, `deleg_main`, `bit_main`,
  the appendix examples and the context-free programs are theories/
  only.
- The two threads on one received flag are deadlock free as a whole
  process. Argued, no Rocq proof (map `ex-flagpair`).
- `rx-postpone`, `rx-delegate`, `rx-relink` are rejected by lock-free
  typing. "to be mechanized" (rejects.js). `rx-chain` is argued.
- Recursive fork-join has no lock-free typing. Argued on paper
  (Proposition 7 of check-general-new.md), the author chose to state it
  as argued.
- A generic mixed-composition theorem. theories/static/Mixed.v has
  `mixed_soundness`. v2 composes the running example by hand in
  `sbv_deadlock_free_R`. The claim "a component proved safe without
  typing composes with typed components" holds through
  `sem_p_connect_h` and `fundamental_proc_h`, but v2 has no named
  corollary.
- Two statements in this run's brief that differ from the Rocq.
  P-Connect asks `wok N (W1 ⊔ W2)`, which is `sacyc` at `N = ∞`. It asks
  `swf` only at a finite bound. The running example lives in
  examples/SemBranch.v, and SemFlag.v and `mixed_soundness` are
  theories/ names.

### 3c. The five citation issues, with locations on this branch

1. Lindley and Morris proved deadlock freedom for GV, not CP
   (`lindley2015semantics` p2). Not in the current tex. Commit 37f5584
   removed the intro sentence. The current citations at
   2-calculus.tex:8 and 274 cite them for the language and for unjoined
   forked threads, which is correct. The hand-written intro must say GV.
2. CLASS is second-order linear logic with DiLL co-exponentials
   (`rocha2023safe` p2). 6-related-work.tex:9-12 says "based on an
   extension of second-order linear logic~\cite{DBLP:journals/tcs/Girard87}".
   The ILL error is gone. Adding "with co-exponentials from differential
   linear logic" makes it exact.
3. Interleaved multiparty sessions need priorities.
   6-related-work.tex:190-192, still present. MPGV is a counterexample,
   with deadlock freedom "solely by linear typing and n-ary fork, and
   without any extrinsic mechanisms like orders/priorities"
   (`jacobs2022multiparty` p5). main.bib has no MPGV entry.
4. The Lily quotation is a paraphrase (`bierman2001operational` p4).
   Not in the current tex. Commit 37f5584 removed it from
   4-extensions.tex. If Lily comes back, quote "A syntactic novelty of
   Lily is the absorption of fixpoint recursion into the terms of
   exponential type".
5. The abstract's universal claim. No abstract on this branch (commit
   5bbf52a removed it). 6-related-work.tex:20-21 gives ECOOP'24 one
   clause. Their relation drops the tree restriction, is
   deadlock-sensitive, and their calculus removes APCP's priorities, so
   the relation does not establish deadlock freedom
   (`heuvel2024information` p1, p2, p7). The new abstract and related
   work need one explicit sentence each.

## 4. Questions for the author

1. Lock freedom in this paper? I recommend a short section 6 that states
   the theorem with its EM and FC hypotheses and explains credit and
   tickets on `S_x^{a,m}`, with the rules in the appendix. The main text
   stays deadlock free and `S_x`. The alternative leaves lock freedom to
   a second paper and drops the "open" claim in related work.
2. Subsumption? I recommend cutting thm:pgv and thm:pn from this paper
   and keeping the end-points argument of appendix E plus prose on
   levels. A port to v2 first needs a translation without `≡`.
3. Payload notation. I recommend `!^{ƛσ}(T).S` in the paper, as decided,
   with one sentence in section 7 on the numeric binders of the Rocq.
4. Term variables. The map uses de Bruijn indices `i`. The paper's
   examples need names. I recommend named binders from letters that
   never name points or channels, for example `f`, `g`, `u`, `v`, `w`,
   and points `x`, `y`, `z`, `ι`, `ρ`.
5. Which theories/ examples to port? I recommend Milner's cyclic
   scheduler, because the related work and the cyclic-topology story
   need it, and the delegation example. The received chain, the bit
   example, the context-free tree programs and the appendix servers can
   go.
6. Harmony appendix? I recommend cutting it. The paper needs no
   reduction semantics.
7. The map's `ex-milner`. I recommend renaming it to "three-thread
   ring", so that "Milner" means the scheduler only.
8. Ordinal indices in the DF sections? I recommend the ordinal index
   from the start, as in the Rocq, with two sentences saying that the
   deadlock-free proofs read it as a natural number and that limits
   serve lock freedom.
9. Title. I recommend keeping it. It says deadlock freedom, cyclic and
   recursive, all three still true. Change it only if Question 1 puts
   lock freedom in the headline.
10. FlagPair. I recommend presenting it as the boundary of
    compositionality with `fp_unrealizable`, and stating the
    whole-process argument as argued. A Rocq proof is optional.

## 5. What the paper needs that the Rocq does not have yet

- A named mixed-composition corollary at static worlds. A component in
  `sem_ptyped_sw` and a typed component compose to a deadlock-free
  process. It is a few lines from `sem_p_connect_h`,
  `fundamental_proc_h` and `adequacy_h`, and replaces the hand
  composition in `sbv_deadlock_free_R`.
- The theories/ examples the author keeps (Question 5), on v2.
- The subsumption translations, if kept (Question 2).
- The rejections of `rx-postpone`, `rx-delegate` and `rx-relink`, if
  lock freedom is in scope. They are marked "to be mechanized".
- The whole-process proof for `ex-flagpair`, if the author wants it
  mechanized.
- The process-level erasure `fptyped (Some N) → fptyped None` and
  `cons_acyc`, both open (report of 2026-11-22). The paper needs them
  only if it states that lock-free process typing erases to deadlock-free
  process typing.
- Link generation. paper/rocqrefs.py must point at v2, and every
  `\rocq` name must exist there.
- Line counts and the table of section 7, recounted on v2.
- Stale Rocq comments that a reader of the artifact will meet.
  relation/Ord.v mentions the removed relation/Sfix.v. Comments in
  relation/Readiness.v, relation/Relation.v, compat/*.v and the header of
  examples/SemBranch.v and examples/FlagPair.v say "ranked world" where
  the world is strict. static/Contexts.v:205 calls `acyc_new`'s
  predecessor "(wf-new)".
- Measured boxes (branch redesign-mbox) stay out, at most one sentence
  of future work.


## Author's answers, 2026-11-22

No paper writing for now, only the map. Subsumption stays in the paper as argued, marked as not mechanized. Porting the theories/ examples comes later. The six defaults are accepted: payload notation `!^{ƛσ}(T).S`, term variables from letters that never name points, harmony appendix cut, ordinal indices from the start, title kept, the map example renamed to three-thread ring (done on redesign).
