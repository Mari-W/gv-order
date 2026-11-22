const { R, h, n, section, block, rule, Q, DEF } = require('./core');

const s = section('types', 'Types and worlds',
  'This section introduces types $T$, credits $a$, session types $S$ with $\\mathsf{unfold}$, $\\mathsf{dual}$, $\\simeq$ and $\\approx$, the sets $\\mathsf{ap}$, payloads, costs $c$ and tickets $m$, the kinds $\\mathsf{unlimited}$ and $\\mathsf{tfree}$, and worlds, static worlds $W$ with the order $\\prec_W$ and ranked worlds $R$ with ranks $\\varrho$, the predicates $\\mathsf{world\\_wf}$, $\\mathsf{wf}$ and $\\mathsf{wf\\_new}$, extension $\\sqsubseteq$ and join $\\sqcup$. Signatures name the sorts $\\mathsf{Ty}$ of types, $\\mathsf{STy}$ of session types, $\\mathsf{LBound}$ of lower bounds and $\\mathsf{World}$ of worlds, and $X_{\\bot}$ adds an absent element to $X$.');

block(s, {
  id: 'ty-grammar', title: 'Types', rocq: 'types/Types.v: ty',
  tex: R`\begin{array}{rl}
T, U ::= & ${h('ty.unit', R`\ast`)} \mid ${h('ty.arrow', R`(T \multimap^{${h('ty.arrow.ub', 'u')}}_{${h('ty.arrow.lb', 'l')}}[${h('ty.arrow.cost', 'c')}]\, U)^{${h('ty.credit', 'a')}}`)} \mid ${h('ty.prod', R`T \otimes U`)} \mid ${h('ty.sum', R`T \oplus U`)} \mid ${h('ty.sess', R`(S@x)^{${h('ty.credit', 'a')}}_{${h('ty.tickets', 'm')}}`)} \\
\mid & ${h('ty.box', R`\Box(\forall ${h('pt.var', R`\bar\iota`)}\, ${h('ty.box.svars', R`\bar\alpha`)}.\ ${h('ty.box.constraint', 'C')}.\ \ast \multimap^{u}[c]\, U)`)} \mid ${h('ty.ex', R`\exists^{${h('ty.ex.lb', 'l')}} \bar\iota.\ C.\ T`)}
\end{array}`,
  variants: { df: R`\begin{array}{rl} T, U ::= & ${h('ty.unit', R`\ast`)} \mid ${h('ty.arrow', R`T \multimap^{${h('ty.arrow.ub', 'u')}}_{${h('ty.arrow.lb', 'l')}} U`)} \mid ${h('ty.prod', R`T \otimes U`)} \mid ${h('ty.sum', R`T \oplus U`)} \mid ${h('ty.sess', R`S@x`)} \\ \mid & ${h('ty.box', R`\Box(\forall ${h('pt.var', R`\bar\iota`)}\, ${h('ty.box.svars', R`\bar\alpha`)}.\ ${h('ty.box.constraint', 'C')}.\ \ast \multimap^{u} U)`)} \mid ${h('ty.ex', R`\exists^{${h('ty.ex.lb', 'l')}} \bar\iota.\ C.\ T`)} \end{array}`,
    live: R`\begin{array}{rl} T, U ::= & ${h('ty.unit', R`\ast`)} \mid ${h('ty.arrow', R`T \multimap^{${h('ty.arrow.ub', 'u')}}_{${h('ty.arrow.lb', 'l')}} U`)} \mid ${h('ty.prod', R`T \otimes U`)} \mid ${h('ty.sum', R`T \oplus U`)} \mid ${h('ty.sess', R`S@x`)} \\ \mid & ${h('ty.box', R`\Box(\forall ${h('pt.var', R`\bar\iota`)}\, ${h('ty.box.svars', R`\bar\alpha`)}.\ ${h('ty.box.constraint', 'C')}.\ \ast \multimap^{u} U)`)} \mid ${h('ty.ex', R`\exists^{${h('ty.ex.lb', 'l')}} \bar\iota.\ C.\ T`)} \end{array}` },
  caption: '$S@x$ is an end at the point $x$. Credits $a$ sit on ends and on closures, the two places where a value holds ends of its own.'
});
block(s, {
  id: 'ty-credit', title: 'Credits', rocq: 'types/Costs.v: fuel',
  modes: ['lf'],
  tex: R`${h('ty.credit', R`(S@x)^{a},\ (T \multimap U)^{a},\ a \in \mathbb{N} \cup \{\infty\}`)}`,
  caption: 'The credit of an end bounds its counter from below, and the credit of a closure bounds the counters of the ends it captured from below and bounds what they lose before a call. Pairs, sums, existentials and payloads carry no credit, their ends carry their own.'
});
block(s, {
  id: 'ty-session', title: 'Session types', rocq: 'types/Types.v: sty, unfoldS',
  tex: R`\begin{array}{rl}
S ::= & ${h('sty.skip', R`\mathsf{Skip}`)} \mid ${h('sty.seq', R`S.S`)} \mid ${h('sty.recv', R`?(\bar\iota.\ T)`)} \mid ${h('sty.send', R`!(\bar\iota.\ T)`)} \mid ${h('sty.plus', R`\oplus(S_1, S_2)`)} \\
\mid & ${h('sty.with', R`\&(S_1, S_2)`)} \mid ${h('sty.close', R`\mathsf{Close}`)} \mid ${h('sty.mu', R`\mu\alpha.S`)} \mid ${h('sty.var', R`\alpha`)} \mid ${h('sty.vard', R`\overline{\alpha}`)}  \\
 & ${h('sty.unfold', R`\mathsf{unfold} : \mathsf{STy} \to \mathsf{STy}`)} \qquad ${h('sty.contr', R`\mathsf{contr} \subseteq \mathsf{STy}`)}
\end{array}`,
  caption: 'Session types with sequencing $S.S$, read through $\\mathsf{unfold}(S)$, whose payloads bind point variables $\\bar\\iota$ at the fields of the carrier.'
});
block(s, {
  id: 'ty-dual', title: 'Duality', rocq: 'types/Types.v: dual, sflip',
  tex: h('sty.dual', R`\begin{array}{l}
\mathsf{dual}(!P) = ?P \qquad \mathsf{dual}(?P) = !P \qquad \mathsf{dual}(\alpha) = \overline{\alpha} \\
\mathsf{dual}(\oplus(S_1,S_2)) = \&(\mathsf{dual}\,S_1,\mathsf{dual}\,S_2) \\
\mathsf{dual}(S_1.S_2) = \mathsf{dual}\,S_1.\mathsf{dual}\,S_2 \\
\mathsf{dual}(\mu\alpha.S) = \mu\alpha.\,${h('sty.flip', R`\mathsf{flip}_\alpha`)}(\mathsf{dual}\,S)
\end{array}`),
  caption: '$\\mathsf{dual}$ keeps payloads $P$, $\\mathsf{Skip}$ and $\\mathsf{Close}$, and $\\overline{S} := \\mathsf{dual}\\,S$.'
});
block(s, {
  id: 'ty-equiv', title: 'Session equivalence', rocq: 'types/Types.v: sequiv, relation/Relation.v: seqv, sdual',
  tex: R`\begin{array}{l}
${h('sty.sequiv', R`S \simeq S'`)} \qquad ${h('sty.seqv', R`S \approx S' \iff ${h('ty2.stydf', R`\mathsf{sty\_df}`)}(S) \simeq \mathsf{sty\_df}(S')`)} \\
${h('sty.sdual', R`\mathsf{sdual}\,S\,S' \iff S' \approx \mathsf{dual}\,S`)}
\end{array}`,
  caption: 'Equivalence $\\simeq$ by behaviour, $\\approx$ the same after erasing annotations, and $\\mathsf{sdual}$ duality up to annotations.'
});
block(s, {
  id: 'ty-heads', title: 'Active points and lower bounds', rocq: 'types/Types.v: heads, hbot, types/Points.v: lbound',
  tex: R`\begin{array}{l}
${h('ty.heads', R`\mathsf{ap}(S@x) = \{\overline{x}\}`)} \qquad ${h('ty.heads', R`\mathsf{ap}(T \multimap^{u}_{l} U) = \mathsf{ap}(\exists^{l}\bar\iota.\ C.\ T) = \{l\} \setminus \{\cdot\}`)} \\
${h('ty.heads', R`\mathsf{ap}(T \otimes U) = \mathsf{ap}(T \oplus U) = \mathsf{ap}(T) \cup \mathsf{ap}(U)`)} \qquad ${h('ty.heads', R`\mathsf{ap}(\ast) = \mathsf{ap}(\Box(\forall\bar\iota\,\bar\alpha.\ C.\ \ast \multimap^{u} U)) = \varnothing`)} \\
${h('ty.lbound', R`l ::= \cdot \mid \bot \mid x`)} \qquad ${h('ty.ubound', R`u ::= \cdot \mid x \mid \top`)} \qquad ${h('ty.botord', R`\Gamma \nvdash x \prec \bot \quad \Gamma \nvdash \bot \preccurlyeq y`)}
\end{array}`,
  caption: '$\\mathsf{ap}(T)$ are the dual points a holding thread of a value of $T$ stays below while it waits. Hidden ends contribute $\\bot$, which no order fact relates to a point, so every check against a held value with hidden ends fails.'
});
block(s, {
  id: 'ty-payload', title: 'Payloads', rocq: 'types/Types.v: payload_at, pscoped',
  tex: R`\begin{array}{l}
${h('ty.payload-at', R`\mathsf{payload\_at}\,m\,T\,x = T[x\cdot 0, \ldots, x\cdot(m{-}1) / \iota_0, \ldots, \iota_{m-1}]`)} \\
${h('ty.pscoped', R`\mathsf{pscoped}\,\bar\iota\,T`)}
\end{array}`,
  caption: 'A payload $!(\\bar\\iota.\\,T)$ mentions only its own point variables $\\bar\\iota = \\iota_0, \\ldots, \\iota_{m-1}$, placed at the fields $x\\cdot 0, \\ldots, x\\cdot(m{-}1)$ of the carrier point $x$.'
});
block(s, {
  id: 'ty-annot', title: 'Annotation values', rocq: 'types/Costs.v: fuel',
  modes: ['lf'],
  tex: h('ann.fuel', R`a, c, m, N \in \mathbb{N} \cup \{\infty\} \qquad \infty - c = \infty`),
  caption: 'Credits $a$, costs $c$, tickets $m$ and the bound $N$ are numbers, and $\\infty$ means unbounded.'
});
block(s, {
  id: 'ty-tix', title: 'Tickets', rocq: 'types/Types.v: TSess m; types/Costs.v: tsum_ok, lgt',
  modes: ['lf'],
  tex: R`\begin{array}{l}
${h('ty.tickets', R`(S@x)^{a}_{m} \qquad a \leq m \qquad m \in \mathbb{N} \cup \{\infty\}`)} \\
${h('ann.tsum', R`\mathsf{tk}(o) + \mathsf{tk}(\overline{o}) \leq N`)}
\end{array}`,
  caption: 'An end has $m$ tickets, an upper bound on its counter, and its credit is at most $m$. The tickets of the two ends of a channel sum to at most $N$.'
});
block(s, {
  id: 'ty-df', title: 'Deadlock-free typing as an instance', rocq: 'types/Types.v: ty_df', modes: ['lf'],
  tex: h('ann.tydf', R`\mathsf{ty\_df}:\quad a = c = m = N = \infty`),
  caption: 'Deadlock-free typing is the annotated typing with every annotation at its unbounded value. $\\mathsf{ty\\_df}$ sets a type to these values, and then every premise about annotations holds.'
});
block(s, {
  id: 'ty-kinds', title: 'Kinds of types', rocq: 'types/Types.v: unlimited, tfree',
  tex: R`\begin{array}{l}
${h('ty.tfree', R`\mathsf{tfree}\,T \iff T \in \mathcal{T}_{0}, \qquad \mathcal{T}_{0} ::= \ast \mid \Box(\forall\bar\iota\,\bar\alpha.\ C.\ \ast \multimap^{u} U) \mid \mathcal{T}_{0} \otimes \mathcal{T}_{0} \mid \mathcal{T}_{0} \oplus \mathcal{T}_{0}`)} \\
${h('ty.unlimited', R`\mathsf{unlimited}\,T \iff \exists \bar\iota, \bar\alpha, C, u, U.\ T = \Box(\forall\bar\iota\,\bar\alpha.\ C.\ \ast \multimap^{u} U)`)}
\end{array}`,
  caption: '$\\mathsf{tfree}$ is the shape of a process result, the types whose values hold no end, and $\\mathsf{unlimited}$ the types that admit weakening and contraction.'
});
block(s, {
  id: 'w-world', title: 'Worlds', rocq: 'types/Worlds.v: sworld, world',
  tex: R`\begin{array}{l}
${h('w.world', R`W = (${h('w.consts', 'A')}, ${h('w.facts', R`\prec_A`)})`)} \\
${h('w.rworld', R`R = (A, \varrho)`)},\ ${h('w.rank', R`\varrho_a : ${h('w.tree', R`\mathsf{tree}(a)`)} \to \mathsf{Ord}`)}\ \text{for}\ a \in A \\
${h('w.rank', R`\varrho_a(x) < \varrho_a(x^{+}),\ \varrho_a(x) < \varrho_a(\overline{x}^{+})`)}
\end{array}`,
  caption: 'A world $W$ has roots $A$ and facts $\\prec_A$ between points with roots in $A$.'
});
block(s, {
  id: 'w-order', title: 'The order of a world', rocq: 'types/Worlds.v: swstep, sw_lt, w_lt, wmodels',
  tex: R`\begin{array}{l}
${h('w.lt', R`\begin{array}{l} \prec_W\ =\ \mathsf{tc}\big(${h('w.ws-fact', R`\prec_A`)} \\ \qquad\qquad \cup\; ${h('w.ws-po', R`\{x \prec x^{+}\}`)} \;\cup\; ${h('w.ws-dpo', R`\{x \prec \overline{x}^{+}\}`)}\big) \end{array}`)} \\
${h('ty2.le', R`x \preceq y \iff x = y \lor x \prec_W y`)} \\
${h('w.rlt', R`R \vDash x \prec y \iff \varrho(x) < \varrho(y)`)} \\
${h('w.sat', R`R \vDash W \iff \forall x \prec_A y.\ R \vDash x \prec y`)}
\end{array}`,
  caption: '$\\prec_W$ is the transitive closure $\\mathsf{tc}$ of the facts, $x \\prec x^{+}$ and $x \\prec \\overline{x}^{+}$. A ranked world orders points by their ranks.'
});
block(s, {
  id: 'w-wf', title: 'Well-formed and well-founded worlds', rocq: 'types/Worlds.v: sworld_wf, swf, wmodels_exists; static/Contexts.v: wf_new, gen_new',
  tex: R`\begin{array}{l}
${h('w.wf', R`\mathsf{world\_wf}\,W`)} \\
${h('w.lfworld', R`\mathsf{wf}\,W \iff \prec_W \text{ is well-founded}`)} \\
${h('w.wfnew', R`\begin{array}{l} \mathsf{wf\_new}\,\rho\,C \iff (\forall (x \prec y) \in C.\ y \in ${h('w.tree', R`\mathsf{tree}(\rho)`)}) \\ \qquad \land\ (C \cup ${h('w.po', R`\mathsf{po}`)}) \cap \mathsf{tree}(\rho)^{2} \text{ is well-founded} \end{array}`)} \\
${h('w.gennew', R`\begin{array}{l} \mathsf{gen\_new}\,\Gamma\,\rho\,C \iff (C \cup \mathsf{po}) \cap \mathsf{tree}(\rho)^{2} \text{ is well-founded} \\ \qquad \land\ \forall (z \prec y) \in C.\ z, y \notin \mathsf{tree}(\rho) \Rightarrow \Gamma \vdash z \prec y \\ \qquad \land\ \exists S \subseteq \mathsf{tree}(\rho) \times \mathsf{Point}_{\Gamma}.\ \forall (u \prec y) \in C.\ u \in \mathsf{tree}(\rho),\ y \notin \mathsf{tree}(\rho) \Rightarrow \exists (u, t) \in S.\ \Gamma \vdash t \prec y \\ \qquad\qquad \land\ \forall (s, t) \in S.\ \forall s' \prec s \in C \cup \mathsf{po}.\ \exists (s', t') \in S.\ \Gamma \vdash t' \prec t \\ \qquad\qquad \land\ \forall (s, t) \in S.\ \forall (z \prec s) \in C.\ z \notin \mathsf{tree}(\rho) \Rightarrow \Gamma \vdash z \prec t \end{array}`)}
\end{array}`,
  caption: 'P-Term and P-Connect ask $\\mathsf{wf}$ of the static world, and E-New asks $\\mathsf{gen\\_new}$ of a creation at a fresh root, which $\\mathsf{wf\\_new}$ implies.'
});
block(s, {
  id: 'w-ext', title: 'Extension, growth, join, restriction', rocq: 'types/Worlds.v: wext, wgrow, swjoin, swrestrict, wf_join_iff',
  tex: R`\begin{array}{l}
${h('w.ext', R`W \sqsubseteq W'`)} \qquad ${h('w.ext', R`R \sqsubseteq R'`)} \qquad ${h('w.grow', R`R \oplus (a, \varrho_a) = (A \cup \{a\},\ \varrho \cup \varrho_a)`)} \qquad ${h('w.join', R`W_1 \sqcup W_2`)} \\
${h('w.R7', R`\begin{array}{l} ${h('w.lfworld', R`\mathsf{wf}`)}(W_1 \sqcup W_2) \iff {} \\ \qquad \mathsf{wf}\,W_1 \land \mathsf{wf}\,W_2 \land \mathsf{wf}(${h('w.restrict', R`W_1|_S`)} \sqcup W_2|_S),\ S = A_1 \cap A_2 \end{array}`)}
\end{array}`,
  caption: 'Extension $\\sqsubseteq$ of static and of ranked worlds, growth $R \\oplus (a, \\varrho_a)$ by the ranks of a fresh root, the join $\\sqcup$, and well-foundedness of a join decided on the shared roots $S = A_1 \\cap A_2$.'
});

// ---- notes ----
n('ty.unit', 'Unit type $\\ast$', 'The type of $\\ast$, with $V\\llbracket\\Theta \\vdash \\ast\\rrbracket = \\{\\ast\\}$ at $\\Theta = \\varnothing$ and empty otherwise.', 'A plain type. $\\mathsf{close}$, $\\mathsf{link}$ and $\\mathsf{spawn}$ return $\\ast$, and every spawned thread returns $\\ast$.', DEF, '$\\mathsf{close}\\,o : \\ast$.', 'types/Types.v: TUnit');
n('ty.arrow', 'Arrow', '$(T \\multimap^{u}_{l}[c]\\,U)^{a}$ is a closure type with upper point $u$, lower point $l$, cost $c$ and credit $a$. The body sees each captured end at its own credit minus $a$.', 'A call runs code that may block and holds the ends of the closure. The type bounds where the call blocks by $u$ and where the held ends are by $l$.', DEF, '$\\ast \\multimap \\ast$ is the type of a spawned thunk.', 'types/Types.v: TLolli');
n('ty.ubound', 'Upper point $u$', '$u = x$ bounds the points where a call may block, $u = \\cdot$ (no end held, nothing to bound) asks nothing of the caller, and $u = \\top$ admits only the empty future, $\\top \\prec F \\iff F = (\\varnothing, \\cdot)$.', 'With $u = \\top$ the body runs as the last code of its thread. A spawned abstraction is such a closure, so E-Abs at $u = \\top$ and $l = \\bot$ followed by E-Spawn types it, and V-Arrow at $(\\top, \\bot)$ is the predicate of a spawned thunk.', DEF, '$\\mathsf{spawn}\\,(\\lambda e)$ uses $\\lambda e : \\ast \\multimap^{\\top}_{\\bot} \\ast$.', 'types/Points.v: ubound; static/Contexts.v: ub_below_u; relation/Readiness.v: ub_ltu');
n('ty.arrow.ub', 'Upper point $u$', 'The body is in $E$ under every $F$ with $\\forall y \\in F.\\ u \\prec y$, which every caller must establish.', 'The type of a closure does not show its body. The condition $u \\prec F$ places the later actions of the caller above the points where the body may block.', 'Without $u$, a closure that blocks at $x$ with $y \\prec x$ for some later action $y$ of the caller could be called first, and the thread waits on its own later action.', 'A function that blocks on an end at $\\kappa$ has $u = \\kappa$.', 'types/Types.v: TLolli ub');
n('ty.arrow.lb', 'Lower point $l$', '$\\forall y \\in \\mathsf{ap}(\\Theta).\\ l \\preceq y$ for the captured ends, with $l$ absent iff $\\Theta = \\varnothing$.', 'A closure is a held value. A thread blocked at $x$ while holding it needs $x \\prec y$ for every dual point $y$ of the captured ends, and $x \\prec l$ implies these facts.', 'Without $l$, a thread blocks at $x$ while it holds a closure with a captured end at $v$ and $x \\not\\prec \\overline{v}$, so the partner of that end may wait on the thread.', 'A closure capturing $a^{+}$ at $\\rho$ has $l = \\overline{\\rho}$.', 'types/Types.v: TLolli lb');
n('ty.arrow.cost', 'Arrow cost $c$', 'A call performs at most $c \\in \\mathbb{N} \\cup \\{\\infty\\}$ channel actions before it returns.', 'A thread that holds an end $o$ while a call runs delays $o$ by at most $c$ actions. Aging subtracts $c$ from the credit of $o$.', 'A thread that holds an end across a call that never returns waits forever the partner. With $c = \\infty$ the held end has credit $a - \\infty$, which fails $c \\leq a$ at finite counter bound.', 'A loop body that never returns has $c = \\infty$.', 'types/Types.v: TLolli c');
n('ty.credit', 'Credit $a$', '$a \\in \\mathbb{N} \\cup \\{\\infty\\}$ on an end type $(S@x)^{a}_{m}$ is a lower bound on the counter of that end. On a closure type $(T \\multimap [c]\\, U)^{a}$ every captured end that is not idle has counter at least $a$.', 'A counter bounds how many actions of other ends an end may still wait through. Only ends and closures hold ends of their own. A pair, a sum or an existential holds the ends of its parts, and their types have the credits.', 'A send of an end whose counter may be $0$ lets the end be sent on forever while its partner waits.', 'A fresh end with $m$ tickets has type $(S@\\rho)^{m}_{m}$.', 'types/Types.v: TSess, TLolli');
n('ty.prod', 'Product', '$T \\otimes U$. Its value relation splits $\\Theta = \\Theta_1 \\uplus \\Theta_2$ between the components.', 'A plain type. $\\mathsf{send}$ takes a pair and $\\mathsf{recv}$ returns one.', DEF, '$S_1@\\iota \\otimes S_2@\\kappa$ for two ends of a client.', 'types/Types.v: TProd');
n('ty.sum', 'Sum', '$T \\oplus U$, the type of $\\mathsf{inj}_1\\,v$ with $v : T$ and of $\\mathsf{inj}_2\\,v$ with $v : U$.', 'A plain type. $\\mathsf{branch}$ returns a sum whose injection records the choice.', DEF, '$\\mathsf{branch}$ at $x$ returns $S_1@x\\cdot\\kappa_{\\mathsf{false}} \\oplus S_2@x\\cdot\\kappa_{\\mathsf{true}}$.', 'types/Types.v: TSum');
n('ty.sess', 'End type $S@x$', 'An end that runs the protocol $S$ and acts next at the point $x$.', 'The points order the next actions of all ends, and readiness compares them to exclude circular waiting.', DEF, '$(!\\ast.\\mathsf{Close})@\\rho$.', 'types/Types.v: TSess');
n('ty.box', 'Box type', '$\\Box(\\forall\\bar\\iota\\,\\bar\\alpha.\\ C.\\ \\ast \\multimap^{u} U)$ is a replicable thunk, usable at every point instance $\\bar x$ with $C[\\bar x]$ and every session instance $\\bar s$.', 'A loop needs fresh points in each round. Quantifying over $\\bar\\iota$ under $\\Box$ gives every call its own instance.', DEF, 'A client loop has type $\\Box\\forall\\iota\\,\\kappa\\,\\zeta.\\ C.\\ \\ast \\multimap (S_1@\\iota \\otimes S_2@\\kappa \\multimap^{\\zeta} \\ast)$.', 'types/Types.v: TBox');
n('ty.box.svars', 'Session variables $\\bar\\alpha$', '$k$ session variables, instantiated at every $\\mathsf{force}$ by session types whose recursion passes an action.', 'One box serves every protocol the caller substitutes for $\\bar\\alpha$.', DEF, 'A forwarder box for every protocol $\\alpha$.', 'types/Types.v: TBox k');
n('ty.box.constraint', 'Box constraint $C$', 'A set of facts $x \\prec y$ over $\\bar\\iota$ and outer points, possibly infinite.', 'A loop orders the points of all its rounds at once, and an infinite $C$ states the facts of every round.', 'Without $C$ a box cannot type a loop that waits on one end while it holds another across rounds.', '$C$ states $\\iota \\prec \\overline{\\kappa}$ for the points of every round of a client loop.', 'types/Points.v: bcs');
n('ty.ex', 'Existential', '$\\exists^{l}\\bar\\iota.\\ C.\\ T^{a}$ is $T[\\bar x]$ for some $\\bar x$ with $C[\\bar x]$, and $l$ bounds the dual points of its ends from below.', 'A fresh point is unknown outside the term that created the point. $\\mathsf{new}$ returns an existential over it, and payloads bind their points the same way.', DEF, '$\\mathsf{new} : \\exists^{\\bot}\\iota.\\ \\{\\overline{\\iota} \\prec \\iota\\cdot 0\\}.\\ (S@\\iota \\otimes \\overline{S}@\\overline{\\iota})$.', 'types/Types.v: TEx');
n('ty.ex.lb', 'Lower bound $l$', '$l = \\cdot$ when the value holds no end, $l = \\bot$ when its ends are at points unknown outside, and $l = x$ when $x \\preceq y$ for every dual point $y$ of its ends.', '$\\bot$ stands for a fresh point that no fact of the context mentions, and $\\mathsf{hbot}$ propagates $\\bot$.', 'Without $\\bot$, a closure captures an unopened fresh pair and claims a lower point $l$ that no fact of $W$ supports.', '$\\mathsf{new} : \\exists^{\\bot}\\ldots$', 'types/Points.v: lbound');
n('sty.skip', '$\\mathsf{Skip}$', 'The empty protocol, and an end at $S$ with $\\mathsf{unfold}(S) = \\mathsf{Skip}$ is idle.', 'No partner waits on an idle end. The fuel layer drops for idle ends the checks that counters are at least $1$, so they may be held indefinitely.', DEF, 'A control end that is passed around and never used is at $\\mathsf{Skip}$.', 'types/Types.v: SSkip, idle');
n('sty.seq', 'Sequencing', '$S.S\'$ runs $S$ and then $S\'$, and $\\mathsf{unfold}$ normalizes it to its first action.', 'Sequencing composes protocols, so a recursion variable need not occur in tail position.', DEF, '$(!\\ast).\\mathsf{Close}$.', 'types/Types.v: SSeq');
n('sty.recv', 'Receive', '$?(\\bar\\iota.\\ T)$ receives a value of $T[x\\cdot 0, \\ldots, x\\cdot(m{-}1)]$ for $\\bar\\iota = \\iota_0, \\ldots, \\iota_{m-1}$ when the end is at $x$.', 'A plain protocol action. The binder $\\bar\\iota$ is no existential, because the points of the payload are determined, the fields of $x$. It lets a message have ends whose points the receiver learns as fields of $x$.', DEF, '$\\mu\\alpha.\\,?(\\kappa.\\ \\alpha @\\kappa).\\mathsf{Close}$ receives an end of the same protocol at a field.', 'types/Types.v: SRcv');
n('sty.send', 'Send', '$!(\\bar\\iota.\\ T)$ sends a value of $T[x\\cdot 0, \\ldots, x\\cdot(m{-}1)]$ for $\\bar\\iota = \\iota_0, \\ldots, \\iota_{m-1}$. The ends of $T$ have their credits, and the sender ages the payload by one transfer.', 'A plain protocol action, $\\mathsf{dual}$ of receive.', DEF, '$!\\ast.\\mathsf{Close}$.', 'types/Types.v: SSnd');
n('sty.plus', 'Internal choice', '$\\oplus(S_1, S_2)$, where the selecting side chooses $i$ and continues with $S_1$ or $S_2$.', 'A plain protocol action. The holding thread decides the continuation.', DEF, '$\\oplus(\\mathsf{Close}, !\\ast.\\mathsf{Close})$.', 'types/Types.v: SPlus');
n('sty.with', 'External choice', '$\\&(S_1, S_2)$, where the branching side receives $i$ and continues with $S_1$ or $S_2$.', 'A plain protocol action, $\\mathsf{dual}$ of internal choice.', DEF, '$\\&(\\mathsf{Close}, ?\\ast.\\mathsf{Close})$.', 'types/Types.v: SWith');
n('sty.close', '$\\mathsf{Close}$', 'The next action of the end is $\\mathsf{close}$.', 'A plain protocol action. Every finite protocol ends with $\\mathsf{Close}$.', DEF, '$\\mathsf{Close}@x^{+}$ after one send at $x$.', 'types/Types.v: SEnd');
n('sty.mu', 'Recursion $\\mu\\alpha.S$', 'A recursive protocol, equal to its unrolling $S[\\mu\\alpha.S/\\alpha]$ up to $\\simeq$.', 'A plain former. Loops run repeating protocols.', DEF, '$\\mu\\alpha.\\,!\\ast.\\alpha$ sends $\\ast$ forever.', 'types/Types.v: SMu');
n('sty.var', 'Session variable $\\alpha$', 'A recursion variable bound by $\\mu$, or a session variable bound by a box.', 'A plain former. It refers to an enclosing $\\mu\\alpha$ or to a protocol substituted at $\\mathsf{force}$.', DEF, '$\\alpha$ in $\\mu\\alpha.\\,!\\ast.\\alpha$.', 'types/Types.v: SVar');
n('sty.vard', 'Dual variable $\\overline{\\alpha}$', '$\\mathsf{dual}(\\alpha) = \\overline{\\alpha}$, and substituting $s$ for $\\alpha$ substitutes $\\mathsf{dual}\\,s$ for $\\overline{\\alpha}$.', 'The dual of a protocol substituted for $\\alpha$ is known only after substitution, so $\\overline{\\alpha}$ defers the dual.', DEF, '$\\mathsf{dual}\\,\\alpha = \\overline{\\alpha}$.', 'types/Types.v: SVarD');
n('sty.unfold', 'Head normal form', '$\\mathsf{unfold}(S)$ unrolls $\\mu$ and reassociates sequencing until the first action is on top.', 'Every rule reads the first action of a session type, so rules match on $\\mathsf{unfold}(S)$ and need no separate rule for $\\mu$.', DEF, '$\\mathsf{unfold}(\\mu\\alpha.\\,!\\ast.\\alpha) = !\\ast.(\\mu\\alpha.\\,!\\ast.\\alpha)$.', 'types/Types.v: unfoldS');
n('sty.contr', 'Contractive session types', '$\\mathsf{contr}\\,S$ holds when the variable of each recursion $\\mu\\alpha.S\'$ inside $S$, also inside payloads, is reached only through an action, a choice or $\\mathsf{Close}$. A session variable does not guard, because an instance may set it to $\\mathsf{Skip}$.', 'On a contractive type $\\mathsf{unfold}$ finds the first action within the fuel the size of the type gives, and $\\simeq$ is kept by substituting contractive types for session variables. The rules ask it where a session type enters a derivation, so a box body typed at one instance is typed at each instance.', 'Without it $\\alpha.\\mu\\beta.\\beta \\simeq (\\alpha.\\mathsf{Skip}).\\mu\\beta.\\beta$, and their instances at $\\alpha = ?\\ast.(\\mathsf{Skip}.\\mathsf{Skip})$ are not equivalent, so a derivation at one instance gives none at the other.', '$\\mu\\alpha.\\,!\\ast.\\alpha$ and $\\mu\\alpha.\\,?(\\kappa.\\ \\alpha @\\kappa).\\mathsf{Close}$ are contractive, $\\mu\\beta.\\beta$ and $\\mu\\beta.\\,\\alpha.\\beta$ are not.', 'types/Contractive.v: scontr, tcontr, unrN_sfuel, sequiv_sinst; static/Sinst.v: typed_sinst; examples/SinstStuck.v: typed_sinst_false, ss_var_guard');
n('sty.dual', 'Duality', '$\\mathsf{dual}$ swaps $!$ with $?$ and $\\oplus$ with $\\&$, keeps payloads, $\\mathsf{Skip}$ and $\\mathsf{Close}$, and $\\overline{S} := \\mathsf{dual}\\,S$.', 'The two ends of a channel run $S$ and $\\mathsf{dual}\\,S$, so every send meets a receive.', DEF, '$\\mathsf{dual}(!\\ast.\\mathsf{Close}) = ?\\ast.\\mathsf{Close}$.', 'types/Types.v: dual');
n('sty.flip', '$\\mathsf{flip}_\\alpha$', '$\\mathsf{flip}_\\alpha$ swaps $\\alpha$ and $\\overline{\\alpha}$ for the variable bound by the enclosing $\\mu$.', 'In $\\mu\\alpha.S$ the variable $\\alpha$ names the whole protocol. After dualizing $S$, the occurrences $\\overline{\\alpha}$ must name $\\mathsf{dual}(\\mu\\alpha.S)$, which is $\\alpha$ again.', DEF, '$\\mathsf{dual}(\\mu\\alpha.\\,!\\ast.\\alpha) = \\mu\\alpha.\\,?\\ast.\\alpha$.', 'types/Types.v: sflip');
n('sty.sequiv', 'Session equivalence $\\simeq$', 'The greatest relation with $S \\simeq S\'$ only if $\\mathsf{unfold}(S)$ and $\\mathsf{unfold}(S\')$ have the same first action, with equal annotations, and equivalent continuations.', 'One protocol has many spellings, unrolled or not. Rules compare protocols up to $\\simeq$.', DEF, '$\\mu\\alpha.\\,!\\ast.\\alpha \\simeq !\\ast.\\mu\\alpha.\\,!\\ast.\\alpha$.', 'types/Types.v: sequiv');
n('ty2.stydf', '$\\mathsf{sty\\_df}$', '$\\mathsf{sty\\_df}(S)$ sets every annotation of $S$ to its value at $N = \\infty$.', 'Deadlock freedom and liveness read no credit, so two protocols that differ only in annotations are equal for them.', DEF, '$\\mathsf{sty\\_df}(!(\\ast^{2}).\\mathsf{Close}) = !(\\ast^{\\infty}).\\mathsf{Close}$.', 'types/Types.v: sty_df');
n('sty.seqv', 'Up to annotations $\\approx$', '$S \\approx S\' \\iff \\mathsf{sty\\_df}(S) \\simeq \\mathsf{sty\\_df}(S\')$.', 'The relations of deadlock freedom and liveness ignore credits, so one relation serves every counter bound $N$.', DEF, '$!(\\ast^{2}).\\mathsf{Close} \\approx !(\\ast^{\\infty}).\\mathsf{Close}$.', 'relation/Relation.v: seqv');
n('sty.sdual', 'Dual up to annotations', '$\\mathsf{sdual}\\,S\\,S\'$ iff $S\' \\approx \\mathsf{dual}\\,S$.', 'The relation pairs the two ends of a channel by $\\mathsf{sdual}$, consistent with comparing by $\\approx$.', DEF, 'A link of ends at $S$ and $S\'$ asks $\\mathsf{sdual}\\,S\\,S\'$.', 'relation/Relation.v: sdual');
n('ty.heads', '$\\mathsf{ap}$', '$\\mathsf{ap}(T)$ is the set of dual points of the ends a value of $T$ holds. It is $\\{\\overline{x}\\}$ for $S@x$, $\\{l\\}$ for an arrow or existential with bound $l$, and $\\varnothing$ for bound $\\cdot$. For $\\otimes$ and $\\oplus$ it is the union. An existential at $\\bot$ contributes $\\bot$.', 'A thread blocked at $u$ while holding a value of $T$ needs $u \\prec y$ for every $y \\in \\mathsf{ap}(T)$, or the partner of a held end may wait on the thread. With $\\bot$ in the set this fails, which is what hidden ends require.', DEF, '$\\mathsf{ap}(\\mathsf{Close}@\\rho \\otimes \\mathsf{Close}@\\rho\\cdot 0) = \\{\\overline{\\rho}, \\overline{\\rho\\cdot 0}\\}$ and $\\mathsf{ap}(\\exists^{\\bot}\\iota.\\,C.\\,T) = \\{\\bot\\}$.', 'types/Types.v: heads, hbot');
n('ty.botord', '$\\bot$ in the order', 'No fact relates $\\bot$ to a point, $\\Gamma \\nvdash x \\prec \\bot$ and $\\Gamma \\nvdash \\bot \\preccurlyeq y$.', 'Hidden ends are at points that no fact outside the existential mentions. A holding thread of such ends can be ordered against nothing, so it may not block.', DEF, '$x \\prec \\{\\overline{\\rho}, \\bot\\}$ fails for every $x$.', 'types/Types.v: hbot; static/Contexts.v: sf_unionb, lbx_below_h');
n('ty.lbound', 'Lower bounds $l$', '$l ::= \\cdot \\mid \\bot \\mid x$, absent, unknown, or a point.', 'It records which facts about the points of the hidden ends are available to a holding thread.', DEF, '$l = \\bot$ for $\\mathsf{new}_\\ell$.', 'types/Points.v: lbound');
n('ty.payload-at', '$\\mathsf{payload\\_at}$', '$\\mathsf{payload\\_at}\\,m\\,T\\,x = T[x\\cdot 0, \\ldots, x\\cdot(m{-}1) / \\iota_0, \\ldots, \\iota_{m-1}]$.', '$\\overline{x}\\cdot j = x\\cdot j$, so sender at $x$ and receiver at $\\overline{x}$ compute the same payload type.', DEF, 'A payload $\\alpha @\\iota_0$ sent at $Y$ has type $\\alpha @Y\\cdot 0$.', 'types/Types.v: payload_at');
n('ty.pscoped', '$\\mathsf{pscoped}$', '$\\mathsf{pscoped}\\,\\bar\\iota\\,T$ iff every point variable of $T$ is among $\\bar\\iota$.', 'A payload mentions only its own point variables, so unrolling a $\\mu$ never captures an outer point.', 'A free outer point inside a $\\mu$-body is captured on unrolling, and point substitution changes its meaning.', '$\\mathsf{pscoped}\\,\\iota_0\\,(S@\\iota_0)$.', 'types/Types.v: pscoped');
n('ann.fuel', 'Numbers with $\\infty$', 'Credits, costs, counters, tickets and the bound $N$ range over $\\mathbb{N} \\cup \\{\\infty\\}$, where $\\infty$ means unbounded and $\\infty - c = \\infty$.', 'Deadlock-free typing sets every annotation to $\\infty$. Then a held end remains arbitrarily many actions, and the checks on credits hold.', DEF, 'A credit $\\infty$ aged by $3$ stays $\\infty$.', 'types/Costs.v: fuel');
n('ty.tickets', 'Tickets $m$', '$m \\in \\mathbb{N} \\cup \\{\\infty\\}$ on an end type $(S@x)^{a}_{m}$ bounds the counter of the end from above, and the credit satisfies $a \\leq m$. An action on the end sets its counter back to $m$, and the tickets stay with the end, also in a payload.', 'The thread holding the partner of an end acts on other ends at most as often as the counter of the partner allows, and the tickets of the partner bound that counter. A link compares the credit of one end with this bound, so the new partner of a waiting thread has a lower counter than the old one.', 'Without tickets a link can give a waiting thread a partner with a full counter in every round, and the wait never ends.', 'A new channel at $N = 4$ may give its ends $3$ and $1$ tickets.', 'types/Types.v: TSess');
n('ann.tsum', '$\\mathsf{tk}(o) + \\mathsf{tk}(\\overline{o}) \\leq N$', 'The tickets of the two ends of a channel sum to at most $N$, the bound of the judgment. An end with $m$ tickets has a partner with at most $N - m$ tickets, a bound read off its own type.', 'E-Link compares the credit of each linked end with the partner bound of the other. Then the new partner of each waiting thread has a counter below the counter of the old one, and the measure of lock-free adequacy falls at every link.', 'Without the bound no premise of a link relates the counters of ends that other threads hold, and relinking a waiting end forever is accepted.', 'At $N = 4$ the two ends of a channel have $3$ and $1$ or $2$ and $2$ tickets.', 'types/Costs.v: tsum_ok');
n('ann.tydf', '$\\mathsf{ty\\_df}$', '$\\mathsf{ty\\_df}(T)$ is $T$ with every annotation at its unbounded value. Credits, costs and tickets become $\\infty$.', 'Deadlock-free typing is the annotated typing at counter bound $N = \\infty$ with these annotations. One set of rules then serves both systems, and every premise about annotations holds at $\\infty$.', DEF, '$\\mathsf{ty\\_df}((S@x)^{3}) = (S@x)^{\\infty}$.', 'types/Types.v: ty_df');
n('ty.unlimited', '$\\mathsf{unlimited}$', '$\\mathsf{unlimited}\\,T$ iff $T$ is a box type, so its variables admit weakening and contraction.', '$V$ at a box type asks $\\Theta = \\varnothing$, so copying or dropping the value duplicates or loses no end.', DEF, 'The self of a box is unlimited.', 'types/Types.v: unlimited');
n('ty.tfree', '$\\mathsf{tfree}$', '$\\mathsf{tfree}\\,T$ iff $T$ is built from $\\ast$, boxes, $\\otimes$ and $\\oplus$. A value of such a type holds no end, because $V$ at a box asks $\\Theta = \\varnothing$.', 'Aging and capture leave an entry at a $\\mathsf{tfree}$ type unchanged. P-Term asks it of the result, so no partner waits on the result of a process.', 'A main thread that returns an end holds it forever, and its partner waits forever.', '$\\mathsf{tfree}(\\ast \\otimes \\Box\\ldots)$.', 'types/Types.v: tfree');
n('w.world', 'Static world', '$W = (A, \\prec_A)$, roots and facts.', 'Typing reads the order $\\prec_W$ that $W$ generates. The relation reads ranked worlds $R$ with $R \\vDash W$, and a creation adds the ranks of its fresh root.', DEF, '$W$ with $A = \\{1, 2\\}$ and the fact $1 \\prec \\overline{2}$.', 'types/Worlds.v: world');
n('w.rworld', 'Ranked world', '$R = (A, \\varrho)$, a finite set $A$ of roots and for each root $a$ a rank function $\\varrho_a$ on $\\mathsf{tree}(a)$.', 'The relation reads the order of points through ranks. Ranks are ordinals, so the order of a ranked world is well-founded and acyclic, and no premise on the world remains.', 'With a symbolic order the union of the worlds of a run may hold an infinite descending chain, and lock-free adequacy then needs a premise that no typing rule checks.', '$R$ with $A = \\{\\rho\\}$ and $\\varrho(\\rho + k) = \\omega \\cdot k$.', 'types/Worlds.v: world');
n('w.rank', 'Rank function $\\varrho_a$', 'A map from $\\mathsf{tree}(a)$ to the ordinals with $\\varrho_a(x) < \\varrho_a(x^{+})$ and $\\varrho_a(x) < \\varrho_a(\\overline{x}^{+})$ for each $x$.', 'A creation at a fresh root ranks the whole tree of the root, fields included, so a later creation at a field finds its ranks fixed and picks nothing. Ordinals leave no room between $\\alpha$ and $\\alpha + 1$, so the room for later fields is fixed at the root.', 'If a root ranked only its own shifts, a field creation could need a rank strictly between $k + 1$ and $k + 2$, and no ordinal exists there.', 'Client and server rank $\\rho + k$ at $\\omega \\cdot k$ and $\\rho\\cdot 0 + k$ at $\\omega \\cdot k + 1$.', 'types/Worlds.v: w_rank, w_po');
n('w.tree', 'Tree $\\mathsf{tree}(a)$', 'The points whose root is $a$, that is $a$, its shifts, its dual and its fields at each depth with their shifts and duals.', 'A rank function is chosen for the whole tree of a root at once.', DEF, '$\\rho\\cdot 0^{+} \\in \\mathsf{tree}(\\rho)$.', 'static/Contexts.v: in_tree0; types/Points.v: pt_unroot');
n('w.rlt', 'Order of a ranked world', '$R \\vDash x \\prec y$ iff $\\varrho(x) < \\varrho(y)$.', 'Readiness and the obligations compare points in the ranked world. The order is transitive and well-founded because $<$ on ordinals is.', DEF, '$\\varrho(\\rho) = 0 < \\omega = \\varrho(\\rho\\cdot 1)$ gives $R \\vDash \\rho \\prec \\rho\\cdot 1$.', 'types/Worlds.v: w_lt, w_lt_wf');
n('w.sat', 'Satisfaction $R \\vDash W$', 'Each fact of $W$ holds under the ranks of $R$.', 'The semantic judgments at a static world $W$ read the relation at each ranked world $R$ with $R \\vDash W$. Static entailment is sound in such $R$, so each fact a derivation uses holds in $R$.', DEF, 'A world with no facts is satisfied by each ranked world with its roots.', 'types/Worlds.v: wmodels');
n('w.po', 'Program order $\\mathsf{po}$', 'The facts $x \\prec x^{+}$ and $x \\prec \\overline{x}^{+}$ for each point $x$.', 'A rank function satisfies program order by definition, so a creation must rank program order together with its facts.', DEF, '$\\rho \\prec \\rho^{+} \\in \\mathsf{po}$.', 'types/Worlds.v: po, w_po');
n('w.wfnew', '$\\mathsf{wf\\_new}\\,\\rho\\,C$', 'Each fact of $C$ ends in $\\mathsf{tree}(\\rho)$, and $C$ with program order is well-founded on $\\mathsf{tree}(\\rho)$.', 'A creation at a fresh root must find ranks for the new tree in each ranked world that satisfies its context. Facts from context points up into the new tree are met by ranks above the context points below the tree, and ranks inside the tree exist exactly when the order there is well-founded.', 'A fact from a new point down to a context point fails at a context point of rank $0$. A chain of creations each below the previous one would need an infinite descending chain of ordinals.', '$\\{\\rho \\prec \\overline{\\rho\\cdot 0},\\ \\overline{\\rho} \\prec \\rho\\cdot 0\\}$ satisfies $\\mathsf{wf\\_new}\\,\\rho$.', 'static/Contexts.v: wf_new, new_step');
n('w.gennew', '$\\mathsf{gen\\_new}\\,\\Gamma\\,\\rho\\,C$', 'The order of $C$ with program order is well-founded on $\\mathsf{tree}(\\rho)$, and facts of $C$ between context points follow from $\\Gamma$. A relation $S$ pairs points of $\\mathsf{tree}(\\rho)$ with points of $\\Gamma$. Each exit $u \\prec y$ from the tree to a context point has a partner of $u$ below $y$. Partners descend along $C$ with program order, and each entry $z \\prec s$ into a paired point lies below its partner.', 'A creation at a fresh root takes the least ranks of the new tree above the context points below the tree. A paired point stays at or below the rank of its partner, so each exit holds in each ranked world that satisfies $\\Gamma$. The same pairs show that opening the existential derives no new fact between points of $\\Gamma$.', 'Without partners an exit is rejected. Without descent along $C$ a chain of new points below an exit could rise above the context point it must stay below.', '$\\Gamma \\vdash z \\prec y$ and $C = \\{\\rho \\prec y\\}$ with $S = \\{(\\rho, z)\\}$. With $\\Gamma \\vdash z \\prec y$, $\\Gamma \\vdash z\' \\prec y\'$ and $C = \\{\\rho \\prec y, \\rho \\prec y\'\\}$, $S = \\{(\\rho, z), (\\rho, z\')\\}$.', 'static/Contexts.v: gen_new, gen_new_rel, wf_new_gen, wf_new_plus_gen; static/PointSubst.v: cons_gen; compat/Redex.v: Erel_new')
n('w.consts', 'Roots $A$', '$A$ is the finite set of roots of $W$.', 'Facts mention only points with roots in $A$, and composition compares two worlds through $A_1 \\cap A_2$.', DEF, '$A = \\{1, 2\\}$.', 'types/Worlds.v: w_consts');
n('w.facts', 'Facts $\\prec_A$', 'A set of facts $x \\prec y$, possibly infinite, between points whose roots lie in $A$.', 'They order the channels a component shares with its environment and the channels created so far.', DEF, '$1 \\prec \\overline{2}$.', 'types/Worlds.v: w_facts');
n('w.lt', '$\\prec_W$', '$\\prec_W$ is the transitive closure of the three generators, and $W \\vdash x \\prec y$ means $x \\prec_W y$.', 'A waiting chain combines several facts, so the order is transitive.', DEF, '$W \\vdash x \\prec x^{++}$.', 'types/Worlds.v: w_lt');
n('w.ws-fact', 'Facts generator', '$x \\prec_A y$ implies $x \\prec_W y$.', 'A plain generator. The facts of $W$ hold in $\\prec_W$.', DEF, '$1 \\prec_W \\overline{2}$.', 'types/Worlds.v: ws_fact');
n('w.ws-po', '$x \\prec x^{+}$', 'For every $x$, $x \\prec_W x^{+}$.', 'An end acts at $x$ before it acts at $x^{+}$, so $\\prec_W$ contains the program order of each end.', DEF, '$\\rho \\prec \\rho^{+}$.', 'types/Worlds.v: ws_po');
n('ty2.le', 'Order or equal $\\preceq$', '$x \\preceq y$ iff $x = y$ or $x \\prec_W y$.', 'Lower bounds compare by $\\preceq$, so a closure whose only captured end has dual point $l$ may have lower point $l$.', DEF, 'A closure capturing $a^{+}$ at $\\rho$ has $l = \\overline{\\rho}$ and $\\overline{\\rho} \\preceq \\overline{\\rho}$.', 'types/Worlds.v: w_le');
n('w.ws-dpo', '$x \\prec \\overline{x}^{+}$', 'For every $x$, $x \\prec_W \\overline{x}^{+}$.', 'The fact holds in every run. The action at $x$ synchronizes with the partner at $\\overline{x}$, and the partner acts at $\\overline{x}^{+}$ only afterwards, so $W$ may contain it for free.', DEF, '$\\rho \\prec \\overline{\\rho}^{+}$.', 'types/Worlds.v: ws_dpo');
n('w.wf', '$\\mathsf{world\\_wf}$', '$\\mathsf{world\\_wf}\\,W$ iff every fact of $\\prec_A$ relates points with roots in $A$.', 'A fact outside $A$ mentions a point no component owns.', DEF, 'A fact $1 \\prec 3$ with $3 \\notin A$ violates the property.', 'types/Worlds.v: world_wf');
n('w.lfworld', '$\\mathsf{wf}$', '$\\mathsf{wf}\\,W$ iff $\\prec_W$ is well-founded, so no infinite chain $\\cdots \\prec x_2 \\prec x_1 \\prec x_0$ exists.', 'A static world has a ranked world that satisfies it exactly when its order is well-founded, and the rank function of $\\prec_W$ is that ranked world. P-Term and P-Connect ask it, so the world of each process derivation is well-founded.', 'A cycle or an infinite descending chain in $\\prec_W$ admits no ranks, and the semantic judgment at $W$ would hold vacuously.', '$W$ with no facts satisfies $\\mathsf{wf}\\,W$.', 'types/Worlds.v: swf, wmodels_exists');
n('w.ext', 'Extension $\\sqsubseteq$', '$W \\sqsubseteq W\'$ iff $A \\subseteq A\'$ and each fact of $W$ is a fact of $W\'$. For ranked worlds $R \\sqsubseteq R\'$ iff $A \\subseteq A\'$ and $\\varrho\'$ agrees with $\\varrho$ on the trees of $A$.', 'No rank changes once chosen, so each fact true in $R$ stays true in each $R\' \\sqsupseteq R$, and the relation is monotone in the world.', DEF, '$R \\sqsubseteq R \\oplus (a, \\varrho_a)$ and $W \\sqsubseteq W \\sqcup W\'$.', 'types/Worlds.v: swext, wext');
n('w.grow', 'Growth $R \\oplus (a, \\varrho_a)$', '$R \\oplus (a, \\varrho_a)$ adds the fresh root $a$ to $A$ and its rank function $\\varrho_a$ to $\\varrho$.', 'A creation at a fresh root ranks the new tree, so the ranked world of a run grows with each root creation and never changes a rank. The union of the worlds of a run is one rank assignment, which lock-free adequacy uses as its measure.', 'If ranks could change along a run, the measure of a waiting thread could rise.', '$R \\oplus (\\rho, \\varrho_\\rho)$ with $\\varrho_\\rho(x) = \\sigma + \\rho_C(x)$ for $\\sigma$ above each context point below the tree.', 'types/Worlds.v: wgrow; compat/Redex.v: Erel_new');
n('w.join', 'Join $\\sqcup$', '$W_1 \\sqcup W_2$ takes the unions of roots and facts.', 'Two components typed in $W_1$ and $W_2$ compose in $W_1 \\sqcup W_2$.', DEF, '$W \\sqsubseteq W \\sqcup W\'$ and $W\' \\sqsubseteq W \\sqcup W\'$.', 'types/Worlds.v: wjoin');
n('w.restrict', 'Restriction $W|_S$', '$W|_S$ has the facts $x \\prec_W y$ with roots of $x, y$ in $S$.', 'It is the derived order of $W$ on the points of the shared roots $S$, chains through private points included, and the only order a component exposes to another.', DEF, '$W|_{A_1 \\cap A_2}$.', 'types/Worlds.v: wrestrict');
n('w.R7', 'Well-founded join', '$\\mathsf{wf}(W_1 \\sqcup W_2)$ iff $\\mathsf{wf}\\,W_1$, $\\mathsf{wf}\\,W_2$ and $\\mathsf{wf}(W_1|_S \\sqcup W_2|_S)$ for $S = A_1 \\cap A_2$.', 'A descending chain of the join that meets shared points infinitely often gives a descending chain of the amalgam, and one that meets them finitely often ends in one private zone. So well-foundedness of the join is decided on the shared roots alone.', DEF, 'Two well-founded worlds with $A_1 \\cap A_2 = \\varnothing$ have a well-founded join.', 'types/Worlds.v: wf_join_iff');

// ---- signatures and arguments ----
const { sa } = require('./core');
const A = (name, meaning) => ({ name, meaning });
const Tt = A('T', R`A type.`);
const Ss = A('S', R`A session type.`);
const Ww = A('W', R`A world.`);
const XY = A(R`x, y`, R`Points.`);
sa('ty.unit', R`\ast \in \mathsf{Ty}`, []);
sa('ty.arrow', R`(T \multimap^{u}_{l}[c]\,U)^{a} \in \mathsf{Ty}`, [A('T', R`The argument type.`), A('U', R`The result type.`), A('a', R`The credit of the closure, a lower bound on its captured counters and what they lose before a call.`), A('u', R`The upper point, optional.`), A('l', R`The lower point, absent iff the closure holds no end.`), A('c', R`The cost of a call, $c \in \mathbb{N} \cup \{\infty\}$.`)]);
sa('ty.arrow.ub', R`u \in \mathsf{Point}_{\bot}`, [A('u', R`A point or absent. The body is in $E$ under every future $F$ with $u \prec y$ for all $y \in F$.`)]);
sa('ty.arrow.lb', R`l \in \mathsf{Point} \cup \{\cdot\}`, [A('l', R`A point with $l \preceq y$ for every dual point $y$ of the captured ends, or $\cdot$ iff the closure captures no end. Not $\bot$, which marks hidden points at $\exists^{\bot}$.`)]);
sa('ty.arrow.cost', R`c \in \mathbb{N} \cup \{\infty\}`, [A('c', R`An upper bound on the channel actions of one call before it returns.`)]);
sa('ty.credit', R`a \in \mathbb{N} \cup \{\infty\}`, [A('a', R`A lower bound on the counter of an end, or of the ends a closure captured.`)]);
sa('ty.prod', R`T \otimes U \in \mathsf{Ty}`, [A(R`T, U`, R`The component types.`)]);
sa('ty.sum', R`T \oplus U \in \mathsf{Ty}`, [A(R`T, U`, R`The types of the two injections.`)]);
sa('ty.sess', R`(S@x)^{a}_{m} \in \mathsf{Ty}`, [A('S', R`The protocol the end runs.`), A('x', R`The point of its next action.`), A('a', R`Its credit, a lower bound on its counter.`), A('m', R`Its tickets, an upper bound on its counter, with $a \leq m$.`)]);
sa('ty.tickets', R`m \in \mathbb{N} \cup \{\infty\}`, [A('m', R`The tickets of an end, the value an action resets its counter to.`), A('a', R`The credit of the end, $a \leq m$.`)]);
sa('ann.tsum', R`\mathsf{tk}(o) + \mathsf{tk}(\overline{o}) \leq N : \mathsf{Prop}`, [A('o', R`An end of a channel and $\overline{o}$ its partner.`), A(R`\mathsf{tk}(o)`, R`The tickets $m$ of $o$, read off its type $(S@x)^{a}_{m}$.`), A('N', R`The bound of the judgment.`)]);
sa('ty.box', R`\Box(\forall\bar\iota\,\bar\alpha.\ C.\ \ast \multimap^{u}[c]\,U) \in \mathsf{Ty}`, [A(R`\bar\iota`, R`$m$ point variables, instantiated at each $\mathsf{force}$ by points $\bar x$ with $C[\bar x]$.`), A(R`\bar\alpha`, R`$k$ session variables, instantiated at each $\mathsf{force}$.`), A('C', R`The constraint over $\bar\iota$ and outer points.`), A('u', R`The upper point of the thunk.`), A('c', R`The cost of one force.`), A('U', R`The result type.`)]);
sa('ty.box.svars', R`\bar\alpha = \alpha_1, \ldots, \alpha_k`, [A('k', R`The number of session variables.`)]);
sa('ty.box.constraint', R`C \subseteq \{x \prec y \mid x, y \in \mathsf{Point}\}`, [A('C', R`A set of facts over $\bar\iota$ and outer points, possibly infinite.`)]);
sa('ty.ex', R`\exists^{l}\bar\iota.\ C.\ T \in \mathsf{Ty}`, [A('l', R`The lower bound, $\cdot$, $\bot$ or a point.`), A(R`\bar\iota`, R`$m$ point variables, the witness $\bar x$ is hidden.`), A('C', R`The facts the witness satisfies.`), A('T', R`The body type.`)]);
sa('ty.ex.lb', R`l \in \{\cdot, \bot\} \cup \mathsf{Point}`, [A('l', R`$\cdot$ for no end, $\bot$ for ends at unknown points, $x$ when $x \preceq y$ for every dual point $y$ of the ends.`)]);
sa('sty.skip', R`\mathsf{Skip} \in \mathsf{STy}`, []);
sa('sty.seq', R`S.S' \in \mathsf{STy}`, [A(R`S, S'`, R`The first and the second protocol.`)]);
sa('sty.recv', R`?(\bar\iota.\ T) \in \mathsf{STy}`, [A(R`\bar\iota`, R`The point variables of the payload, $\iota_0, \ldots, \iota_{m-1}$, placed at $x\cdot 0, \ldots, x\cdot(m{-}1)$ for the carrier point $x$.`), A('T', R`The payload type.`)]);
sa('sty.send', R`!(\bar\iota.\ T) \in \mathsf{STy}`, [A(R`\bar\iota`, R`The point variables of the payload, placed at the fields of the carrier point.`), A('T', R`The payload type.`)]);
sa('sty.plus', R`\oplus(S_1, S_2) \in \mathsf{STy}`, [A(R`S_1, S_2`, R`The continuations for $i = \mathsf{false}$ and $i = \mathsf{true}$.`)]);
sa('sty.with', R`\&(S_1, S_2) \in \mathsf{STy}`, [A(R`S_1, S_2`, R`The continuations for the received $i = \mathsf{false}$ and $i = \mathsf{true}$.`)]);
sa('sty.close', R`\mathsf{Close} \in \mathsf{STy}`, []);
sa('sty.mu', R`\mu\alpha.S \in \mathsf{STy}`, [A(R`\alpha`, R`The recursion variable, bound in $S$.`), A('S', R`The body.`)]);
sa('sty.var', R`\alpha \in \mathsf{STy}`, [A(R`\alpha`, R`A variable bound by an enclosing $\mu$ or by a box.`)]);
sa('sty.vard', R`\overline{\alpha} \in \mathsf{STy}`, [A(R`\alpha`, R`A session variable, $\overline{\alpha}$ stands for $\mathsf{dual}$ of its instance.`)]);
sa('sty.contr', R`\mathsf{contr} \subseteq \mathsf{STy}`, [A('S', R`A session type, possibly with session variables of a box.`)]);
sa('sty.unfold', R`\mathsf{unfold} : \mathsf{STy} \to \mathsf{STy}`, [A('S', R`A contractive session type, $\mathsf{unfold}(S)$ has its first action on top.`)]);
sa('sty.dual', R`\mathsf{dual} : \mathsf{STy} \to \mathsf{STy}`, [Ss, A('P', R`A payload, kept unchanged.`), A(R`S_1, S_2`, R`Continuations.`)]);
sa('sty.flip', R`\mathsf{flip}_\alpha : \mathsf{STy} \to \mathsf{STy}`, [A(R`\alpha`, R`The variable of the enclosing $\mu$, whose occurrences $\alpha$ and $\overline{\alpha}$ are swapped.`)]);
sa('sty.sequiv', R`\cdot \simeq \cdot \subseteq \mathsf{STy} \times \mathsf{STy}`, [A(R`S, S'`, R`Session types, related iff their unfoldings agree on first action and annotations and have related continuations.`)]);
sa('ty2.stydf', R`\mathsf{sty\_df} : \mathsf{STy} \to \mathsf{STy}`, [Ss]);
sa('sty.seqv', R`\cdot \approx \cdot \subseteq \mathsf{STy} \times \mathsf{STy}`, [A(R`S, S'`, R`Session types compared after $\mathsf{sty\_df}$.`)]);
sa('sty.sdual', R`\mathsf{sdual} : \mathsf{STy} \to \mathsf{STy} \to \mathsf{Prop}`, [A('S', R`The protocol of one end.`), A(R`S'`, R`The protocol of its partner, $S' \approx \mathsf{dual}\,S$.`)]);
sa('ty.heads', R`\mathsf{ap} : \mathsf{Ty} \to \mathcal{P}_{\mathrm{fin}}(\mathsf{Point} \cup \{\bot\})`, [Tt]);
sa('ty.botord', R`\Gamma \nvdash x \prec \bot,\ \Gamma \nvdash \bot \preccurlyeq y`, [A('x, y', R`points`)]);
sa('ty.lbound', R`l \in \mathsf{LBound} = \{\cdot, \bot\} \cup \mathsf{Point}`, []);
sa('ty.ubound', R`u \in \mathsf{UBound} = \{\cdot, \top\} \cup \mathsf{Point}`, []);
sa('ty.payload-at', R`\mathsf{payload\_at} : \mathbb{N} \to \mathsf{Ty} \to \mathsf{Point} \to \mathsf{Ty}`, [A('m', R`The number of point variables of the payload.`), A('T', R`The payload type over $\iota_0, \ldots, \iota_{m-1}$.`), A('x', R`The point of the carrier end.`)]);
sa('ty.pscoped', R`\mathsf{pscoped} : \mathsf{PVar}^{*} \to \mathsf{Ty} \to \mathsf{Prop}`, [A(R`\bar\iota`, R`The point variables the payload binds.`), A('T', R`The payload type.`)]);
sa('ann.fuel', R`\mathbb{N} \cup \{\infty\}`, []);
sa('ann.tydf', R`\mathsf{ty\_df} : \mathsf{Ty} \to \mathsf{Ty}`, [Tt]);
sa('ty.unlimited', R`\mathsf{unlimited} : \mathsf{Ty} \to \mathsf{Prop}`, [Tt]);
sa('ty.tfree', R`\mathsf{tfree} : \mathsf{Ty} \to \mathsf{Prop}`, [Tt]);
sa('w.world', R`W = (A, \prec_A) \in \mathsf{World}`, [A('A', R`The roots.`), A(R`\prec_A`, R`The facts.`)]);
sa('w.rworld', R`R = (A, \varrho) \in \mathsf{RWorld}`, [A('A', R`The roots.`), A(R`\varrho`, R`A rank function for the tree of each root.`)]);
sa('w.rank', R`\varrho_a : \mathsf{tree}(a) \to \mathsf{Ord}`, [A('a', R`A root of $A$.`), A('x', R`A point of $\mathsf{tree}(a)$.`)]);
sa('w.tree', R`\mathsf{tree} : \mathsf{Root} \to \mathcal{P}(\mathsf{Point})`, [A('a', R`A root.`)]);
sa('w.rlt', R`R \vDash \cdot \prec \cdot \subseteq \mathsf{Point} \times \mathsf{Point}`, [A('R', R`A ranked world.`), XY]);
sa('w.sat', R`\cdot \vDash \cdot \subseteq \mathsf{RWorld} \times \mathsf{World}`, [A('R', R`A ranked world.`), Ww]);
sa('w.po', R`\mathsf{po} \subseteq \mathsf{Point} \times \mathsf{Point}`, [A('x', R`A point.`)]);
sa('w.gennew', R`\mathsf{gen\_new} : \mathsf{Ctx} \to \mathsf{PVar} \to \mathcal{P}(\mathsf{Point} \times \mathsf{Point}) \to \mathsf{Prop}`, [A(R`\Gamma`, R`The facts of the context of the creation.`), A(R`\rho`, R`The fresh root.`), A('C', R`The facts of the creation.`)]);
sa('w.wfnew', R`\mathsf{wf\_new} : \mathsf{PVar} \to \mathcal{P}(\mathsf{Point} \times \mathsf{Point}) \to \mathsf{Prop}`, [A(R`\rho`, R`The fresh root, a point variable bound by the existential of $\mathsf{new}$.`), A('C', R`The facts of the creation.`)]);
sa('w.consts', R`A \in \mathcal{P}_{\mathrm{fin}}(\mathsf{Root})`, []);
sa('w.facts', R`\prec_A \subseteq \mathsf{Point} \times \mathsf{Point}`, []);
sa('w.lt', R`W \vdash \cdot \prec \cdot \subseteq \mathsf{Point} \times \mathsf{Point}`, [Ww, XY]);
sa('w.ws-fact', R`x \prec_A y \Rightarrow x \prec_W y`, [XY]);
sa('w.ws-po', R`\forall x.\ x \prec_W x^{+}`, [A('x', R`Any point.`)]);
sa('ty2.le', R`\cdot \preceq \cdot \subseteq \mathsf{Point} \times \mathsf{Point}`, [XY]);
sa('w.ws-dpo', R`\forall x.\ x \prec_W \overline{x}^{+}`, [A('x', R`Any point.`)]);
sa('w.wf', R`\mathsf{world\_wf} : \mathsf{World} \to \mathsf{Prop}`, [Ww]);
sa('w.lfworld', R`\mathsf{wf} : \mathsf{World} \to \mathsf{Prop}`, [Ww]);
sa('w.grow', R`\cdot \oplus \cdot : \mathsf{RWorld} \to \mathsf{Root} \times (\mathsf{Point} \to \mathsf{Ord}) \to \mathsf{RWorld}`, [A('R', R`A ranked world.`), A('a', R`The fresh root, $a \notin A$.`), A(R`\varrho_a`, R`Its rank function on $\mathsf{tree}(a)$.`)]);
sa('w.ext', R`\cdot \sqsubseteq \cdot \subseteq \mathsf{World}^{2} \cup \mathsf{RWorld}^{2}`, [A(R`W, W'`, R`The smaller and the larger static world.`), A(R`R, R'`, R`The smaller and the larger ranked world.`)]);
sa('w.join', R`\cdot \sqcup \cdot : \mathsf{World} \to \mathsf{World} \to \mathsf{World}`, [A(R`W_1, W_2`, R`The worlds of two components.`)]);
sa('w.restrict', R`\cdot|_{\cdot} : \mathsf{World} \to \mathcal{P}(\mathsf{Root}) \to \mathsf{World}`, [Ww, A('S', R`A set of constants, instantiated with $A_1 \cap A_2$.`)]);
sa('w.R7', R`\mathsf{wf}(W_1 \sqcup W_2) \iff \ldots`, [A(R`W_1, W_2`, R`Two well-formed worlds.`), A('S', R`The shared roots $A_1 \cap A_2$.`)]);
