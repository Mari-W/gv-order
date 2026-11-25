# Faithfulness of the map

Generated from docs/explorer/map.json at 7eb53c34 by map-faithfulness.py. Do not edit by hand.

check.sh confirms that every cited Rocq name exists. No tool compares a formula with the statement it cites. The formulas are checked by hand. The differences below are the recorded ones.

| kind | count |
|---|---|
| other | 1 |
| simplified | 6 |
| merged | 12 |
| renamed | 48 |
| notation | 42 |

## Statements with no Rocq counterpart (other, 1)

- **block fu-vs** (`Erel`, `FuelE`, `o_recv`, `f_recv`, `o_new`, `f_new`). The Rocq proves no lemma that merges `Erel` and `FuelE` into one fixed point. Such a fixed point would read at a receive only the values in both $V$ and $FV$, and it would choose one session type at a creation where O-New and F-New choose one each. Its equivalence with the conjunction is unproved.

## The map says less than the Rocq (simplified, 6)

- **block t-lf-wf** (`wok`, `swf`, `wfit`, `wstrict`, `wranked`). The Rocq asks `wok N W` of process typing, which is `swf W` at a finite bound. The induction behind the fundamental theorems reads worlds under `wfit N W`, which is `wstrict W`, or `wranked W` with $N$ finite and excluded middle. The lock-free view shows the ranked case only.
- **block p-typing** (`wok`, `sacyc`, `swf`). The Rocq premise is `wok N W`, which is `sacyc W` at $N = \infty$ and `swf W` at a finite $N$. The lock-free view shows the finite case as $\mathsf{ranked}\,W$, and the deadlock-free view the case $N = \infty$ as $\mathsf{cons}\,W$.
- **block fu** (`Fdef`, `kinj`, `renk`). `Fdef` states both clauses for each renaming `g` of ends injective on the held ends (`kinj`, `renk`), at the term `emap g e`. The map shows the identity renaming. The closure under renamings is a proof device for a link, which renames the dual end of a removed end in another thread.
- **block soup** (`soup_consistent`, `soup_gen`). $\mathsf{wa}$ names the other eleven conjuncts of `soup_consistent`, the fields `sp_owner` to `sp_sigcap` of `soup_gen`. Its note lists each conjunct.
- **note fu.Phi** (`sp_fin`, `sp_cap`). Counters and tickets range over $\mathbb{N} \cup \{\infty\}$, the type `fuel`. The map writes $\mathbb{N}$, and the lock-free process relation keeps both finite by `sp_fin` and `sp_cap`.
- **note sp.own** (`soup_inv`, `khalf`, `sp_sigcap`). The interface annotation $\eta$ of `soup_gen` gives the bound on the tickets of an interface end. `soup_inv` fixes it to $\lfloor N/2 \rfloor$ at each end by `khalf`, and the map writes that bound.

## One notion in the map, two in the Rocq (merged, 12)

- **block w-world** (`sworld`, `world`, `wmodels`, `wstrict_of`). The Rocq has two types of world, `sworld` with constants and facts for typing and `world` with bases and a strict order `w_ord` for the relation, linked by `wmodels`. The map shows one notion. A world of the relation is the world whose facts are its order, because a strict order that contains program order is the order it generates, so no generality is lost. A consistent world of typing gives a world of the relation with its own order, `wstrict_of`, as [[w-ext]] states.
- **block w-order** (`sw_lt`, `w_lt`). The Rocq orders a world of typing by `sw_lt`, the closure `tc (swstep W)`, and a world of the relation by `w_lt`, which is program order or `w_ord` between points of its bases. Both are $\prec_W$ of the one notion, because `w_ord` is transitive and contains program order on the points of its bases.
- **block w-ext** (`swext`, `wext`, `wmodels`, `aw_W`, `dmodels_exists`, `wstrict_of`). The Rocq extends a world of typing by `swext`, which asks the facts themselves, and a world of the relation by `wext`, which asks the order. Inclusion of facts implies inclusion of orders, and the map uses the order for both. The Rocq relates a world of typing to a larger world of the relation by `wmodels`, the constants among the bases and each fact in the order of the larger world. That is the inclusion of orders, because that order is transitive and contains program order, and the map writes it $W \sqsubseteq W'$ with $W'$ consistent. The growth `aw_W` of a world of the relation closes its order transitively, and the map adds the facts, whose order is the same closure. The consistent extension of a consistent world is `dmodels_exists`, through `wstrict_of`.
- **block r-new** (`e_new`, `e_new_fld`). The Rocq has two constructors, e_new for a fresh base with a constraint and e_new_fld for a field without one. The map shows one rule whose triple $(p, \bar\rho, C)$ picks the case. With no bound point and the constraint $\top$ the existential is the plain product, so the field case is e_new_fld as stated.
- **block soup** (`sp_pts`, `sp_dom`, `ctrs`, `kres`). The Rocq chooses an environment `A` of the relation and a protocol map `Π` of fuel per index, and reads counters and tickets off `K` by `ctrs`. The map writes them as one map $\Delta$. `sp_pts` and `sp_dom` make this exact, because they give `A` the points of `K` and give `A`, `Π` and `K` one domain.
- **note w.world** (`sworld`, `world`). The Rocq has `sworld` for typing and `world` for the relation, shown as one notion in [[w-world]].
- **note w.rlt** (`w_lt`, `sw_lt`). `w_lt` orders a world of the relation and `sw_lt` a world of typing. Both are $\prec_W$ of [[w-order]].
- **note w.ext** (`swext`, `wext`). `swext` extends worlds of typing by their facts and `wext` worlds of the relation by their order. The map uses the order for both, as [[w-ext]] states.
- **note w.ext** (`wmodels`, `wmodels_lt`). `wmodels` relates a world of typing to a world of the relation, which is consistent by its type. It asks the constants among the bases and each fact in the order of the larger world, which is ${\prec_W} \subseteq {\prec_{W'}}$ by `wmodels_lt`. The map writes this relation as $W \sqsubseteq W'$ with $\mathsf{cons}\,W'$.
- **note fu.Phi** (`cenv`). The Rocq keeps the protocols in a map `penv` and the counters and tickets in a map `cenv`, and the formula shows both in one map $\Phi$ from $\mathsf{End}$ to $\mathsf{STy} \times \mathbb{N} \times \mathbb{N}$.
- **note E-New.pos** (`e_new`, `e_new_fld`). The two constructors e_new and e_new_fld are the two cases of the triple.
- **note sp.delta** (`sp_pts`, `sp_dom`). The Rocq keeps an environment `A` of the relation and a protocol map `Π` of fuel, chosen per index, and the counters and tickets in `K`. `sp_pts` and `sp_dom` give the three maps one domain and the points of `K`, so one map $\Delta$ states the three maps.

## Renamed (renamed, 48)

- **block w-wf** (`sacyc`). $\mathsf{cons}$ is `sacyc`. A world is consistent exactly when its order has no cycle.
- **block w-wf** (`swf`). $\mathsf{ranked}$ for a world of typing is `swf`, which is `wf` of relation/Ranks.v at the order of the world, the existence of a rank function.
- **note syn.values** (`is_val`). The Rocq writes the injections as `Inj`, shown as $\mathsf{inj}_i$, and `is_val` decides which terms are values.
- **note proc.config** (`config`). The Rocq type `gmap nat expr` of the thread map is shown as $\mathbb{N} \rightharpoonup \mathsf{Expr}$, with $\mathsf{Expr}$ for the type `expr` of terms.
- **note sx.kappai** (`bfield`). `bfield false` is $0$ and `bfield true` is $1$, shown as the fields $\kappa_{\mathsf{false}}$ and $\kappa_{\mathsf{true}}$.
- **note ev.event** (`event`). The constructors `EvSolo`, `EvSync` and `EvOffer` of `event` are shown as $\mathsf{solo}$, $\mathsf{sync}$ and $\mathsf{offer}$.
- **note ev.tau** (`ev_tau`, `itstep`). `ev_tau` holds of the events whose process label is `PTau`, shown as a set of events. $\mathsf{Event}$ is the type `event`.
- **note sty.seqv** (`seqv`). The relation `seqv` is shown as $\approx$. It is `sequiv` after `sty_df`, which is the identity on the types of the deadlock-free view.
- **note ann.tsum** (`tsum_ok`). $\mathsf{tk}(o)$ reads the tickets of the end $o$, and `tsum_ok` states the bound on their sum.
- **note w.tree** (`in_tree0`, `in_tree`, `pt_unroot`). $\mathsf{tree}(a)$ is the set of points with base $a$, which `in_tree0` states for the base of the variable $0$ and `in_tree m` for the variables below $m$.
- **note w.lt** (`sw_lt`, `swstep`). `sw_lt` is defined as `tc (swstep W)`, shown as $\mathsf{tc}$ of the facts and program order.
- **note w.lfworld** (`swf`, `wf`). $\mathsf{ranked}$ is `swf`, which is `wf` of relation/Ranks.v at the order of the world.
- **note w.restrict** (`croot_in`). $\mathsf{base}(x) \in A \cap S$ is the Rocq predicate `croot_in`, which asks the base of $x$ to be a constant in the set.
- **note w.R7** (`acyc_join_iff`, `wf_join_iff`, `wok_join_iff`). $\mathsf{cons}$ is `sacyc` and $\mathsf{ranked}$ is `swf`. `acyc_join_iff` and `wf_join_iff` state the two equivalences, and `wok_join_iff` combines them by the bound.
- **note w.acyc** (`sacyc`, `w_ord_irrefl`). $\mathsf{cons}$ is `sacyc` for worlds of typing. A world of the relation is consistent by `w_ord_irrefl`.
- **note w.models** (`dmodels_exists`, `wstrict_of`, `wmodels_exists`). $\mathsf{world\_wf}$ and $\mathsf{cons}$ stand for `sworld_wf` and `sacyc`\inmode{lf}{, and $\mathsf{ranked}$ for `swf`}. `dmodels_exists` gives a strict world of the relation that extends $W$, `wstrict_of`, which is $W$ with its own order.
- **note new.rank** (`new_ok`, `gen_new_rel`, `in_tree0`, `ctx_pt`). $\mathsf{rankable}_{\Gamma}(\rho, C)$ names `∃ Sr, gen_new_rel W Γ C Sr`, the last conjunct of `new_ok` at a finite bound. $\mathsf{tree}(\rho)$ stands for the points that `in_tree0` describes, and $\mathsf{Point}_{\Gamma}$ for the points of the context that `ctx_pt` gives.
- **note tj.hage** (`thage`, `lage`). $\mathsf{def}(H - c)$ stands for the Rocq relations `thage` and `lage`, which age the ends and the closures of $H$ by $c$.
- **note lfi.measure** (`we`, `lf_rank`, `lf_adequacy`). $x$ is the point of $o$ that `we` reads from the ownership map.
- **note ct.give** (`c_give`). The cost field `c_give` applies to $\mathsf{send}$, $\mathsf{select}$ and $\mathsf{close}$, which the formula names by their keywords.
- **note ct.takek** (`c_take`). The cost field `c_take` applies to $\mathsf{recv}$ and $\mathsf{branch}$, which the formula names by their keywords.
- **note ct.sync** (`ev_cost`). $\kappa_\ell$ is `tcost κ ℓ` and $\kappa_\sigma$ is `scost κ σ`.
- **note rel.lfp** (`Eind`, `Pind`). $(\mathsf{lfp})$ marks the least fixpoints, the inductive types `Eind` and `Pind`.
- **note rel.vsize** (`tsize`, `Vtop`, `RelA`, `osfix`). The Rocq builds the levels with `osfix` in `RelA` and measures types with `tsize`, written $\mathsf{size}$. `Vtop` unfolds `Vbody` with the fuel $\mathsf{size}\,T + 1$, which is the recursion on the size within a level.
- **note E.stop** (`Ebody`). $(\mathsf{stop})$ labels the first clause of `Ebody`.
- **note E.ready** (`Ebody`). $(\mathsf{ready})$ labels the second clause of `Ebody`, and $\mathsf{irred}$ is the Rocq predicate `irred`.
- **note E.step** (`Esteps`, `Eobl`). $(\mathsf{step})$ labels the clause that `Esteps` and `Eobl` state.
- **note rd.offered** (`offered_t`, `offered_p`). `offered_t`$\,\Theta\,t\,o$ also asks $o \in \mathrm{dom}\,\Theta$. The map writes it as $o \in \mathsf{offered}\,t$ and takes the restriction to $\Theta$ in $\Theta|_{\mathsf{offered}\,t}$ and $\Theta \setminus \mathsf{offered}\,t$.
- **note rd.value** (`ready_t`). $\mathsf{Val}$ is the set of terms that `is_val` accepts, and $\Theta|_{\mathsf{offered}\,t} = \varnothing$ stands for $\forall o.\ \neg$`offered_t`$\,\Theta\,t\,o$.
- **note rd.below-rest** (`below_rest`). $\Theta|_{\mathsf{offered}\,t} \prec_W \overline{\Theta \setminus \mathsf{offered}\,t} \cup F$ writes `below_rest` with sets of points in place of its two quantified clauses.
- **note rd.p-term** (`ready_p`). $\Sigma|_{\mathsf{offered}\,p} = \varnothing$ stands for $\forall o.\ \neg$`offered_p`$\,\Sigma\,p\,o$.
- **note rd.above-offered** (`above_offered`). The map quantifies over the dual points $\overline{\Sigma \setminus \mathsf{offered}\,p}$ and the points $\Sigma|_{\mathsf{offered}\,p}$, where `above_offered` quantifies over the ends.
- **note P-Stop** (`Pclauses`). $(\mathsf{stop})$ labels the first clause of `Pclauses`.
- **note P-Ready** (`Pclauses`). $(\mathsf{ready})$ labels the second clause of `Pclauses`, and $\mathsf{pirred}$ is the Rocq predicate `pirred`.
- **note P-Step** (`Psteps`). $(\mathsf{step})$ labels the clause that `Psteps` states.
- **note fuse.inj** (`fuse_ok`). $\mathsf{held}$ is the set of ends that `pheld` accepts in `fuse_ok`.
- **note fuse.partners** (`fuse_ok`). $\mathsf{held}$ is the set of ends that `pheld` accepts in `fuse_ok`.
- **note Q-Link** (`q_close`, `q_select`, `q_branch`, `q_link`). Q-Close, Q-Select, Q-Branch and Q-Link are the clauses `q_close`, `q_select`, `q_branch` and `q_link`, shown as the term obligations they repeat.
- **note fu.rty** (`rty`). $\mathsf{thread}$ is the constructor `RThread` of `rty`.
- **note fu.val** (`Fdef`). $(\mathsf{stop})$ labels the value clause of `Fdef`, and $\mathsf{Val}$ is the set of terms that `is_val` accepts.
- **note fu.step** (`Fdef`, `Fobl`). $(\mathsf{step})$ labels the step clause of `Fdef`, stated through `Fobl`.
- **note F-Beta** (`f_beta`). $\mathsf{Fobl}_\beta$ is the clause `f_beta` of the fuel obligation.
- **note fu.fspare** (`fspare`). $\mathsf{positive}$ is the Rocq predicate `fspare`, and $\mathsf{idle}$ is `idle_at`.
- **note sp.hold** (`hold`). $K$ maps an end to a record `hold` of thread, point, counter and tickets, shown as a tuple in $\mathbb{N} \times \mathsf{Point} \times \mathbb{N} \times \mathbb{N}$.
- **note sp.own** (`soup_consistent`). $\mathsf{wa}$ names the conjuncts of `soup_consistent` other than `sp_pts` and `sp_dom`, which $\Delta : K$ states.
- **note sr.FE** (`FuelE`, `Fdef`, `FLevA`). $\mathsf{thread}$ is the constructor `RThread` of `rty`, the result of a thread.
- **note sr.pfuse** (`pfuse`). $(h, D) \cdot p$ is `pfuse h D p`, which renames the channels with `gch h`.
- **note new.wf** (`new_ok`). $\mathsf{wf}$ is `well_founded` of the Rocq standard library, which `new_ok` applies to `new_step C`.

## Notation (notation, 42)

- **block syn-let** (`ELet`). Derived form. Syntax.v defines `ELet e1 e2` as `LetP (Pair e1 EUnit) (LetU (Var 0) (rename S e2))`, the pair elimination and unit elimination shown.
- **block ty-equiv** (`seqv`, `sequiv`, `sty_df`). The deadlock-free view shows one equivalence, $\approx$ for `seqv`. `seqv` compares two session types after `sty_df`, which is the identity on the types of that view, so `seqv` and `sequiv` coincide there. The lock-free view shows both.
- **block ty-heads** (`heads`, `hbot`, `lbound`, `ubound`, `lb_heads`). The Rocq has `heads T`, a finite set of points, and `hbot T`, a flag set when $T$ holds a closure or an existential at the lower bound `LBot`. The bounds are `lbound` with `LNone`, `LBot`, `LPt x` and `ubound` with `UNone`, `UPt x`, `UTop`. The map writes $l = \top$ for `LNone`, $l = \bot$ for `LBot`, $u = \bot$ for `UNone` and $u = \top$ for `UTop`. It writes $\mathsf{ap}(T)$ for `heads T` with $\bot$ added when `hbot T` holds and $\top$ added for each closure or existential at `LNone`. $\bot$ lies below each bound and $\top$ above each bound. Each check that reads a bound is then one comparison with a set, as [[t-side]] states, and it agrees with the Rocq case by case.
- **block w-wf** (`sworld_wf`, `sacyc`, `swf`). The map folds `sworld_wf` into $\mathsf{cons}$ and $\mathsf{ranked}$. The Rocq states `sworld_wf W` as a separate conjunct next to `sacyc W` and `swf W`, and the term-level theorems ask `sworld_wf W` alone, which the map writes $\mathsf{world\_wf}\,W$.
- **block t-judgment** (`sf_unionb`). The Rocq writes $F \triangleleft H$ as `sf_unionb F (heads H) (hbot H)`, which adds the heads and sets the rest to `RAll` when `hbot H` holds. The map adds $\bot$ to the set instead. Both make each $x \prec F$ fail, as [[t-side]] states.
- **block t-contexts** (`sfuture`, `frest`). The Rocq future `sfuture` is a pair of a finite set of points and an optional rest, with `frest` = `RAbove u | RAll`. The map writes $X \cup {\vartriangle}v$, with $v = u$ for `Some (RAbove u)`, $v = \bot$ for `Some RAll` and $v = \top$ for `None`. The map lets $X$ hold the bounds $\bot$ and $\top$ as well, where the Rocq sets the rest to `RAll` for a held value with `hbot` and adds nothing for a closure at `LNone`. The rules read a future only through $u \prec F$ of [[t-side]], the union of [[t-judgment]] and the instantiation of points, and each comparison agrees. The semantic judgment of [[sj-all]] denotes a future by a set of points, which drops the bounds of $X$ and reads $\bot \in X$ as the rest `RAll`.
- **block t-contexts** (`hctx`, `hyps`, `fl`, `slt`). $\Gamma$ is `hctx`, a list of pairs `(C, xs)` that the map writes $C[\bar x]$. The three rules are the constructors `fl_w`, `fl_h` and `fl_trans` of `fl`, and `slt` is `fl`. Program order enters through `fl_w`, because the order of each world contains program order.
- **block t-side** (`ub_below_u`, `ub_below_s`, `rest_below`, `below_ty`, `lbx_below_h`). The Rocq states these checks by cases on the bounds, and the map reads each case as one comparison, with $\bot$ below and $\top$ above each bound. `ub_below_u` gives `UNone` no condition, which is $\bot \prec F$, and `UTop` the empty future `(∅, None)`, which is $\top \prec F$. For `UPt x` it asks `ub_below_s`, $x$ below each point of the set and `rest_below x r`. That is $x \preccurlyeq u$ for `RAbove u`, false for `RAll` and nothing for no rest, the three values of $x \preccurlyeq v$ at $v = u$, $v = \bot$ and $v = \top$. `below_ty` asks `hbot T = false` and $x$ below each head, which is $x \prec \mathsf{ap}(T)$ with $\bot \in \mathsf{ap}(T)$ for `hbot`. `lbx_below_h` gives `LBot` no condition, `LNone` no head and no `hbot`, and `LPt x` the bound $x \preccurlyeq y$ for each head and no `hbot`. Each case is $l \preccurlyeq \mathsf{ap}(H)$, because $\bot \preccurlyeq y$ holds for each $y$, $\top \preccurlyeq y$ only for $y = \top$, and $x \preccurlyeq \bot$ for no point $x$.
- **block r-fun** (`e_abs`, `e_app`, `abs_fut`, `lbx_below_h`, `ub_below_u`). E-Abs types the body under `abs_fut ub`, which is `(∅, Some RAll)` for `UNone`, `(∅, Some (RAbove u))` for `UPt u` and `(∅, None)` for `UTop`. Each is the future ${\vartriangle}u$ of [[ty-heads]]. Its premise on $l$ is `lbx_below_h`, which is $l \preccurlyeq \Delta$ of [[t-side]] in each case, and E-App asks `ub_below_u`, which is $u \prec F$.
- **block r-boxes** (`e_box`, `e_force`, `rest_of`, `ubound_of`, `ub_below_s`). The upper point of a box is an optional point in the Rocq, and the map writes $\bot$ for none. The body runs under `(∅, Some (rest_of ub))`, which is ${\vartriangle}u$. The thunk of a forced box has the arrow upper point `ubound_of ub`, which is $u$ itself, and E-Force asks `ub_below_s`, which is $u[\bar x] \prec F$.
- **block r-ex** (`cons_open`, `bridge_at`, `cons_open_conservative`, `conserv`, `cons_open_iff`). $\mathsf{conserv}_{\Gamma}(\bar\iota, C)$ is `conserv W Γ m C`, stated over the points of $\Gamma$ shifted past the $m$ binders, which are the points outside the tree. The typing rules check the finite form `cons_open W Γ m C`. It asks $\Gamma$ to derive $z \prec y$ for each path `bridge_at` from an old point $z$ to an old point $y$. Such a path uses one fact of $C$, or it enters the tree by a fact of $C$, follows facts of $C$ and program order inside the tree and leaves by a fact of $C$. `cons_open_iff` proves `cons_open` and `conserv` equivalent for a world whose facts lie at constant bases.
- **block r-new** (`acyc_new`, `cons_open`, `cbridge`). The second clause of `acyc_new` is `cons_open W Γ 1 C`, the finite form of $\mathsf{conserv}_{\Gamma}(\rho, C)$ at one base, as [[r-ex]] states.
- **block fu** (`Fobl`). $e'\ \mathsf{at}\ \Phi'\ !\ d'$ abbreviates the premise that each obligation of `Fobl` states for its successor, `FuelE` at each lower level.
- **block fu-obls** (`refill`, `fhand`, `mres`, `mrem`). $\Phi{\downarrow}[o \mapsto S^{m,m}]$ is `refill o φ` with the protocol of $o$ updated in the map `Π`, and $\Phi_M{\downarrow}$ is `fhand`. $\Phi = \Phi_M \uplus \Phi_r$ with $\mathrm{dom}\,\Phi_M = \mathsf{fends}(v)$ states the inclusion of `fends v` in the held ends and the maps `mres` and `mrem`.
- **note ty.ubound** (`ubound`). `UNone` is $\bot$, `UPt x` is $x$ and `UTop` is $\top$.
- **note ty.heads** (`heads`, `hbot`, `lb_heads`). The map writes $\mathsf{ap}$ for the Rocq function `heads`, with $\bot$ added when `hbot` holds and $\top$ added for a closure or existential at `LNone`, whose `lb_heads` is empty.
- **note ty.lbound** (`lbound`). `LBot` is $\bot$, `LNone` is $\top$ and `LPt x` is $x$.
- **note w.facts** (`sw_facts`, `fact`). $\mathsf{Point}$ is the Rocq type `point` of [[syn-points]]. The facts `sw_facts` of a world are a predicate on `fact`, the pairs of points, and the map writes that predicate as a subset of $\mathsf{Point}^{2}$.
- **note w.lfworld** (`sworld_wf`). Well-formedness `sworld_wf` is a separate conjunct in the Rocq, folded in here.
- **note w.grow** (`wgrow`, `wgrow_ext`, `aw_W`, `aw_W_ext`, `Erel_new_acyc`, `Erel_new`). The Rocq growth `aw_W` builds the order as the transitive closure of the old order, the facts $C[a]$ and program order. The map adds the facts, whose order is that closure.
- **note w.acyc** (`sworld_wf`). Well-formedness `sworld_wf` is a separate conjunct in the Rocq, folded in here.
- **note tj.F** (`sfuture`, `frest`). `sfuture` is the pair of $X$ and an optional `frest`, written $X \cup {\vartriangle}v$ as [[t-contexts]] states.
- **note ctx.hyps** (`hyps`, `hc_open`). The Rocq stores the pair `(C, xs)`.
- **note side.ub** (`ub_below_s`, `ub_below_u`, `rest_below`). The Rocq gives the cases by `ub_below_u`, `ub_below_s` and `rest_below`, as [[t-side]] states.
- **note side.lb** (`lbx_below_h`). `lbx_below_h` gives `LBot` no condition, `LNone` no head and no `hbot`, and `LPt x` the bound for each head and no `hbot`, as [[t-side]] states.
- **note side.top** (`lbound`, `ubound`). The Rocq has no order on bounds. It states each check by cases on `lbound` and `ubound`, and the map reads the cases as this one order, as [[t-side]] states.
- **note E-Abs.body** (`abs_fut`). The future `abs_fut ub` is ${\vartriangle}u$, as [[r-fun]] states.
- **note E-Send.heads** (`below_ty`, `hbot_payload_at`, `heads`, `hbot`). `below_ty` asks `hbot T = false` and $x$ below each point of `heads T`, which is $x \prec \mathsf{ap}(T)$ with $\bot \in \mathsf{ap}(T)$ for `hbot`.
- **note E-Open.cons** (`cons_open`, `bridge_at`, `cons_open_conservative`, `conserv`, `cons_open_iff`). $\mathsf{conserv}_{\Gamma}(\bar\iota, C)$ is `conserv W Γ m C`, stated over the points of $\Gamma$ shifted past the $m$ binders, which are the points outside the tree. The typing rules check the finite form `cons_open W Γ m C`. It asks $\Gamma$ to derive $z \prec y$ for each path `bridge_at` from an old point $z$ to an old point $y$. Such a path uses one fact of $C$, or it enters the tree by a fact of $C$, follows facts of $C$ and program order inside the tree and leaves by a fact of $C$. `cons_open_iff` proves `cons_open` and `conserv` equivalent for a world whose facts lie at constant bases.
- **note P-Connect.wf** (`p_connect`, `ptyped_wf`). The rule asks `wok N (W1 ⊔ W2)` only. The join of the two component worlds is well formed by `ptyped_wf`, so the folded $\mathsf{cons}$\inmode{lf}{ and $\mathsf{ranked}$} of the join ask nothing more.
- **note P-Term.wf** (`p_term`). `p_term` asks `sworld_wf W ∧ wok N W`. The map folds `sworld_wf` into $\mathsf{cons}$\inmode{lf}{ and $\mathsf{ranked}$}, and it shows `wok N W` as $\mathsf{cons}$ at $N = \infty$\inmode{lf}{ and as $\mathsf{ranked}$ at a finite bound}.
- **note P-Connect.n** (`p_connect_n`). `p_connect_n` concludes a derivation at some world $W$ with $W \sqsubseteq W_1 \sqcup \cdots \sqcup W_n$ and $W_1 \sqcup \cdots \sqcup W_n \sqsubseteq W$, the join `sw_joins` of the list, because the binary joins of the fold nest to the left. Both have the same bases and the same facts, and the map writes the join.
- **note sj.sw** (`sem_ptyped_sw`). The Rocq quantifies over the Rocq worlds of type `world` that `wmodels` relates to $W$, and the map writes them as consistent extensions. At each of them it reads `sem_ptyped`, whose Rocq notation is $\Sigma \vDash_W p : T$. The map writes that judgment out as $\forall \alpha.\ p \in P^{W'}_{\alpha}\llbracket \Sigma \vdash T \rrbracket$, so that $\vDash_W$ names this judgment alone.
- **note sj.sw** (`sem_ptyped_sw`, `sem_ptyped`). At $\kappa_L$ the Rocq writes `⊫`. The map writes $\vDash[\kappa_L]$, the instance of the family $\vDash[\kappa]$, as for terms.
- **note sj.den** (`sf_den`, `rest_ok`). `sf_den Y F` adds $Y$ when $F$ has a rest, and `rest_ok` asks each point of $Y$ above $u$ for the rest `RAbove u`. With no rest the Rocq still quantifies over $Y$ and adds nothing, which the map writes as $Y = \varnothing$. The Rocq future has no bounds in its set. A future with $\bot \in X$ is the Rocq future with the rest `RAll`, for which `rest_ok` asks nothing of $Y$, as [[t-contexts]] states.
- **note sj.term** (`sem_typed`). The Rocq writes the judgment at $\kappa_L$ with a turnstile of its own, `⊫`, for `sem_typed κ_L` and `sem_ptyped κ_L`. The map writes $\vDash[\kappa_L]$, the instance of the family $\vDash[\kappa]$ at $\kappa_L$, so that one symbol serves each cost table.
- **note sj.proc** (`sem_ptyped`). The Rocq calls it `sem_ptyped`, with the notation $\Sigma \vDash_W p : T$. The map writes the quantifier out and keeps $\Sigma \vDash_W p : T$ for the judgment at each consistent extension of [[sj-all]].
- **note sp.allR** (`lf_sems`). `lf_sems` quantifies over the ranked Rocq worlds of type `world` that `wmodels` relates to $W$, which the map writes as ranked extensions.
- **note sp.lfsem** (`lf_sem`, `lf_sems`). The Rocq reads `lf_sem` at each ranked world, with the notation $\Sigma \Vvdash^{N}_W p : T$. The map writes it out and keeps $\Sigma \Vvdash^{N}_W p : T$ for `lf_sems`, the judgment at each ranked extension. `lf_sems` reads `lf_semk`, the judgment at the annotations $\eta$ of the interface. The map leaves $\eta$ implicit here and in the theorem rows, because it is fixed with the interface.
- **note E-New.vanish** (`e_new_fld`). The Rocq types the field case at the product directly, and the map writes it as an existential with no bound point and no facts.
- **note ty.up** (`frest`, `rest_of`, `abs_fut`, `rest_below`). The Rocq writes the rest of a future as `RAbove v` for ${\vartriangle}v$, `RAll` for ${\vartriangle}\bot$ and no rest for ${\vartriangle}\top$, and compares by `rest_below`, which is $x \preccurlyeq v$, false and true in the three cases.
- **note fu.at** (`Fobl`). The Rocq repeats the premise in each obligation of `Fobl`, as `FuelE` at each lower level.
