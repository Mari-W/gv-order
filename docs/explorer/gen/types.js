const { R, h, n, section, block, rule, Q, DEF } = require('./core');

const s = section('types', 'Types and worlds',
  'This section introduces types $T$, credits $a$, session types $S$ with $\\mathsf{unfold}$, $\\mathsf{dual}$, $\\simeq$ and $\\approx$, the sets $\\mathsf{heads}$ and the flag $\\mathsf{hbot}$, payloads, costs $c$ and ticket transformers $\\vartheta$, the kinds $\\mathsf{prim}$, $\\mathsf{unlimited}$, $\\mathsf{tfree}$, and worlds $W$ with the order $\\prec_W$, the predicates $\\mathsf{world\\_wf}$, $\\mathsf{strict}$, $\\mathsf{wfworld}$, extension $\\sqsubseteq$ and join $\\sqcup$. Signatures name the sorts $\\mathsf{Ty}$ of types, $\\mathsf{STy}$ of session types, $\\mathsf{Tix}$ of transformers, $\\mathsf{LBound}$ of lower bounds and $\\mathsf{World}$ of worlds, and $X_{\\bot}$ adds an absent element to $X$.');

block(s, {
  id: 'ty-grammar', title: 'Types', rocq: 'types/Types.v: ty',
  tex: R`\begin{array}{rl}
T, U ::= & ${h('ty.unit', R`\ast`)} \mid ${h('ty.arrow', R`T^{a} \multimap^{${h('ty.arrow.ub', 'u')}}_{${h('ty.arrow.lb', 'l')}}[${h('ty.arrow.cost', 'c')} ; ${h('ty.arrow.tix', R`\vartheta`)} ; ${h('ty.arrow.floor', 'h')}]\, U^{b}`)} \mid ${h('ty.prod', R`T^{a} \otimes U^{b}`)} \mid ${h('ty.sum', R`T^{a} \oplus U^{b}`)} \mid ${h('ty.sess', R`S@x`)} \\
\mid & ${h('ty.box', R`\Box(\forall ${h('pt.var', R`\bar\iota`)}\, ${h('ty.box.svars', R`\bar\alpha`)}.\ ${h('ty.box.constraint', 'C')}.\ \ast \multimap^{u}[c ; \vartheta]\, U^{b})`)} \mid ${h('ty.ex', R`\exists^{${h('ty.ex.lb', 'l')}} \bar\iota.\ C.\ T^{a}`)}
\end{array}`,
  variants: { df: R`\begin{array}{rl} T, U ::= & ${h('ty.unit', R`\ast`)} \mid ${h('ty.arrow', R`T \multimap^{${h('ty.arrow.ub', 'u')}}_{${h('ty.arrow.lb', 'l')}} U`)} \mid ${h('ty.prod', R`T \otimes U`)} \mid ${h('ty.sum', R`T \oplus U`)} \mid ${h('ty.sess', R`S@x`)} \\ \mid & ${h('ty.box', R`\Box(\forall ${h('pt.var', R`\bar\iota`)}\, ${h('ty.box.svars', R`\bar\alpha`)}.\ ${h('ty.box.constraint', 'C')}.\ \ast \multimap^{u} U)`)} \mid ${h('ty.ex', R`\exists^{${h('ty.ex.lb', 'l')}} \bar\iota.\ C.\ T`)} \end{array}`,
    live: R`\begin{array}{rl} T, U ::= & ${h('ty.unit', R`\ast`)} \mid ${h('ty.arrow', R`T \multimap^{${h('ty.arrow.ub', 'u')}}_{${h('ty.arrow.lb', 'l')}} U`)} \mid ${h('ty.prod', R`T \otimes U`)} \mid ${h('ty.sum', R`T \oplus U`)} \mid ${h('ty.sess', R`S@x`)} \\ \mid & ${h('ty.box', R`\Box(\forall ${h('pt.var', R`\bar\iota`)}\, ${h('ty.box.svars', R`\bar\alpha`)}.\ ${h('ty.box.constraint', 'C')}.\ \ast \multimap^{u} U)`)} \mid ${h('ty.ex', R`\exists^{${h('ty.ex.lb', 'l')}} \bar\iota.\ C.\ T`)} \end{array}` },
  caption: '$S@x$ is an end at the point $x$, and the superscripts $a, b$ are credits.'
});
block(s, {
  id: 'ty-credit', title: 'Credits', rocq: 'types/Costs.v: fuel',
  modes: ['lf'],
  tex: R`${h('ty.credit', R`T^{a},\ a \in \mathbb{N} \cup \{\infty\}`)} \qquad ${h('ty.credit-agg', R`(T^{a_1} \otimes U^{a_2})^{a} \text{ gives } a + a_1,\ a + a_2`)}`,
  caption: 'A credit $a$ bounds the counters of the ends a value holds from below, and adds to the credits of the parts of an aggregate.'
});
block(s, {
  id: 'ty-session', title: 'Session types', rocq: 'types/Types.v: sty, unfoldS',
  tex: R`\begin{array}{rl}
S ::= & ${h('sty.skip', R`\mathsf{Skip}`)} \mid ${h('sty.seq', R`S.S`)} \mid ${h('sty.recv', R`?(\bar\iota.\ T^{${h('sty.payload-credit', 'b')}})`)} \mid ${h('sty.send', R`!(\bar\iota.\ T^{b})`)} \mid ${h('sty.plus', R`\oplus(S_1, S_2)`)} \\
\mid & ${h('sty.with', R`\&(S_1, S_2)`)} \mid ${h('sty.close', R`\mathsf{Close}`)} \mid ${h('sty.mu', R`\mu\alpha.S`)} \mid ${h('sty.var', R`\alpha`)} \mid ${h('sty.vard', R`\overline{\alpha}`)} \qquad ${h('sty.unfold', R`\mathsf{unfold}(S)`)}
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
  id: 'ty-heads', title: 'Heads, bottom flag, lower bounds', rocq: 'types/Types.v: heads, hbot, types/Points.v: lbound',
  tex: R`\begin{array}{l}
${h('ty.heads', R`\mathsf{heads}(S@x) = \{\overline{x}\} \quad \mathsf{heads}(T \multimap_{l} U) = \{l\} \quad \mathsf{heads}(\exists^{l}) = \{l\} \quad \mathsf{heads}(\Box\ldots) = \varnothing`)} \\
${h('ty.hbot', R`\mathsf{hbot}(T)`)} \qquad ${h('ty.lbound', R`l ::= \cdot \mid \bot \mid x`)}
\end{array}`,
  caption: '$\\mathsf{heads}(T)$ are the partner points a holder of a value of $T$ stays below while it waits, and $\\mathsf{hbot}(T)$ marks hidden ends.'
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
  id: 'ty-annot', title: 'Costs and ticket transformers', rocq: 'types/Costs.v: tix, meets, tspawn, tlink, tseq, tok',
  modes: ['lf'],
  tex: R`\begin{array}{l}
${h('ann.fuel', R`a, c, h \in \mathbb{N}\cup\{\infty\}`)} \qquad ${h('ann.tix', R`\vartheta = (s, b) : r \mapsto 2^{s} r + b`)} \qquad ${h('ann.tid', R`\hat 1 = (0, 0)`)} \\
${h('ann.meets', R`\mathsf{meets}\,\vartheta\,r\,tk \iff \vartheta(r) \leq tk`)} \qquad ${h('ann.tlink', R`\mathsf{tlink}\,\vartheta = (s, b{+}1)`)} \\
${h('ann.tspawn', R`\mathsf{tspawn}\,b_c\,\vartheta = (s{+}1, \max(2b, 2b_c{-}1))`)} \qquad ${h('ann.tseq', R`\vartheta_1 \circ \vartheta_2`)} \\
${h('ann.tok', R`\mathsf{tok}\,\vartheta_1\,\vartheta_2 \iff b_2 = 0 \lor s_1 \neq \infty \lor b_1 = \infty`)}
\end{array}`,
  caption: 'Credits, costs and floors range over $\\mathbb{N} \\cup \\{\\infty\\}$, and $\\vartheta$ maps a reserve $r$ to the tickets $tk$ a term needs.'
});
block(s, {
  id: 'ty-df', title: 'Annotations of deadlock-freedom typing', rocq: 'types/Types.v: ty_df, cr_df',
  tex: h('ann.tydf', R`\begin{array}{l}
\mathsf{ty\_df}(T):\ \text{credits } \infty\ (0 \text{ on } \otimes, \oplus, \exists),\ \text{costs } \infty, \\
\qquad \vartheta = (\infty,\infty),\ \text{floors } \infty
\end{array}`),
  caption: 'The deadlock-freedom instance $N = \\infty$ of every annotation.'
});
block(s, {
  id: 'ty-kinds', title: 'Kinds of types', rocq: 'types/Types.v: prim, unlimited, tfree',
  tex: R`\begin{array}{l}
${h('ty.prim', R`\mathsf{prim}\,T ::= \ast \mid \mathsf{prim} \otimes \mathsf{prim} \mid \mathsf{prim} \oplus \mathsf{prim} \mid \Box(\ldots \mathsf{prim})`)} \\
${h('ty.unlimited', R`\mathsf{unlimited}\,T \iff T = \Box\ldots`)} \qquad ${h('ty.tfree', R`\mathsf{tfree}\,T`)}
\end{array}`,
  caption: '$\\mathsf{prim}$ is the shape of a process result, $\\mathsf{unlimited}$ the types that admit weakening and contraction, $\\mathsf{tfree}$ the types whose values hold no end.'
});
block(s, {
  id: 'w-world', title: 'Worlds', rocq: 'types/Worlds.v: world',
  tex: h('w.world', R`W = (${h('w.consts', 'A')}, ${h('w.facts', R`\prec_A`)})`),
  caption: 'A world $W$ has roots $A$ and facts $\\prec_A$ between points with roots in $A$.'
});
block(s, {
  id: 'w-order', title: 'The order of a world', rocq: 'types/Worlds.v: wstep, w_lt',
  tex: R`\begin{array}{l}
${h('w.lt', R`\begin{array}{l} \prec_W\ =\ \mathsf{tc}\big(${h('w.ws-fact', R`\prec_A`)} \\ \qquad\qquad \cup\; ${h('w.ws-po', R`\{x \prec x^{+}\}`)} \;\cup\; ${h('w.ws-dpo', R`\{x \prec \overline{x}^{+}\}`)}\big) \end{array}`)} \\
${h('ty2.le', R`x \preceq y \iff x = y \lor x \prec_W y`)}
\end{array}`,
  caption: '$\\prec_W$ is the transitive closure $\\mathsf{tc}$ of the facts, $x \\prec x^{+}$ and $x \\prec \\overline{x}^{+}$.'
});
block(s, {
  id: 'w-wf', title: 'Well-formed, strict and well-founded worlds', rocq: 'types/Worlds.v: world_wf, strict, wfworld',
  tex: R`\begin{array}{l}
${h('w.wf', R`\mathsf{world\_wf}\,W`)} \\
${h('w.strict', R`\mathsf{strict}\,W \iff \mathsf{world\_wf}\,W \land \forall x.\ W \nvdash x \prec x`)} \\
${h('w.lfworld', R`\mathsf{wfworld}\,W \iff \prec_W \text{ is well-founded}`)}
\end{array}`,
  caption: '$\\mathsf{strict}\\,W$ is asked by every result, $\\mathsf{wfworld}\\,W$ in addition by lock freedom.'
});
block(s, {
  id: 'w-ext', title: 'Extension, growth, join, restriction', rocq: 'types/Worlds.v: wext, wjoin, wrestrict, strict_join_iff',
  tex: R`\begin{array}{l}
${h('w.ext', R`W \sqsubseteq W'`)} \qquad ${h('w.grow', R`W \oplus C = (A \cup \mathsf{roots}(C),\ \prec_A \cup\, C)`)} \qquad ${h('w.join', R`W_1 \sqcup W_2`)} \\
${h('w.R7', R`\begin{array}{l} \mathsf{strict}(W_1 \sqcup W_2) \iff {} \\ \qquad \mathsf{strict}\,W_1 \land \mathsf{strict}\,W_2 \land \mathsf{strict}(${h('w.restrict', R`W_1|_S`)} \sqcup W_2|_S),\ S = A_1 \cap A_2 \end{array}`)}
\end{array}`,
  caption: 'Extension $\\sqsubseteq$, growth $W \\oplus C$ by the facts of a creation, the join $\\sqcup$, and strictness of a join decided on the shared constants $S = A_1 \\cap A_2$.'
});

// ---- notes ----
n('ty.unit', 'Unit type $\\ast$', 'The type of $\\ast$, with $V\\llbracket\\Theta \\vdash \\ast\\rrbracket = \\{\\ast\\}$ at $\\Theta = \\varnothing$ and empty otherwise.', 'A plain type. $\\mathsf{close}$, $\\mathsf{link}$ and $\\mathsf{spawn}$ return $\\ast$, and every spawned thread returns $\\ast$.', DEF, '$\\mathsf{close}\\,o : \\ast$.', 'types/Types.v: TUnit');
n('ty.arrow', 'Arrow', '$T^{a} \\multimap^{u}_{l}[c ; \\vartheta ; h]\\,U^{b}$ is a closure type with upper point $u$, lower point $l$, cost $c$, transformer $\\vartheta$, floor $h$ and credits $a, b$.', 'A call runs code that may block and holds the ends of the closure. The type bounds where the call blocks by $u$ and where the held ends sit by $l$.', DEF, '$\\ast \\multimap \\ast$ is the type of a spawned thunk.', 'types/Types.v: TLolli');
n('ty.arrow.ub', 'Upper point $u$', 'The body is in $E$ under every $F$ with $\\forall y \\in F.\\ u \\prec y$, which every caller must establish.', 'The caller does not see the body. The condition $u \\prec F$ makes every later action of the caller lie above every point where the body may block.', 'Without $u$, a closure that blocks at $x$ with $y \\prec x$ for some later action $y$ of the caller could be called first, and the thread waits on its own later action.', 'A function that blocks on an end at $\\kappa$ has $u = \\kappa$.', 'types/Types.v: TLolli ub');
n('ty.arrow.lb', 'Lower point $l$', '$\\forall y \\in \\mathsf{heads}(\\Theta).\\ l \\preceq y$ for the captured ends, with $l$ absent iff $\\Theta = \\varnothing$.', 'A closure is a held value. A thread blocked at $x$ while holding it needs $x \\prec y$ for every partner point $y$ of the captured ends, and $x \\prec l$ implies all of them.', 'Without $l$, a thread blocks at $x$ while it holds a closure with a captured end at $v$ and $x \\not\\prec \\overline{v}$, so the partner of that end may wait on the thread.', 'A closure capturing $a^{+}$ at $\\rho$ has $l = \\overline{\\rho}$.', 'types/Types.v: TLolli lb');
n('ty.arrow.cost', 'Arrow cost $c$', 'A call performs at most $c \\in \\mathbb{N} \\cup \\{\\infty\\}$ channel actions before it returns.', 'A thread that holds an end $o$ while a call runs delays $o$ by at most $c$ actions. Aging subtracts $c$ from the credit of $o$.', 'A thread that holds an end across a call that never returns starves the partner. With $c = \\infty$ the held end has credit $a - \\infty$, which fails $c \\leq a$ at finite refill.', 'A loop body that never returns has $c = \\infty$.', 'types/Types.v: TLolli c');
n('ty.arrow.tix', 'Arrow transformer $\\vartheta$', '$\\vartheta(r)$ bounds the link tickets a call needs when it must still hold $r$ tickets on return.', 'A link acts on no protocol. A finite ticket count bounds the number of links a thread performs.', 'A box that links once per round forever needs an unbounded number of tickets, and no finite $tk$ meets its transformer.', 'One link needs $r + 1$ tickets, $\\vartheta = (0, 1)$.', 'types/Types.v: TLolli t');
n('ty.arrow.floor', 'Floor $h$', 'Every captured end must have counter at least $h + a$ when the closure is built, and the body sees each captured end at credit $h$.', 'The body does not know the counters of the ends it captured. $h$ is the lower bound it may assume.', DEF, 'Deadlock-freedom typing has $h = \\infty$.', 'types/Types.v: TLolli h');
n('ty.credit', 'Credit $a$', '$a \\in \\mathbb{N} \\cup \\{\\infty\\}$ is a lower bound on the counter of every end a value of type $T^{a}$ holds.', 'A counter bounds how many actions of other ends an end may still wait through. A credit lets a type state that bound.', 'A send of an end whose counter may be $0$ lets the end travel forever while its partner waits.', 'A fresh end has credit $N$.', 'types/Types.v: ty (fuel fields)');
n('ty.credit-agg', 'Credit of an aggregate', '$(T^{a_1} \\otimes U^{a_2})^{a}$ gives credit $a + a_1$ to $T$ and $a + a_2$ to $U$, and likewise for $\\oplus$ and $\\exists$.', 'Aging, capture and subtyping push the outer credit inward, so a credit on an aggregate bounds the counters of all its ends.', DEF, '$(T^{1} \\otimes U^{2})^{1}$ gives $T$ credit $2$ and $U$ credit $3$.', 'static/Contexts.v: tage, tcap, tsub');
n('ty.prod', 'Product', '$T^{a} \\otimes U^{b}$. Its value relation splits $\\Theta = \\Theta_1 \\uplus \\Theta_2$ between the components.', 'A plain type. $\\mathsf{send}$ takes a pair and $\\mathsf{recv}$ returns one.', DEF, '$S_1@\\iota \\otimes S_2@\\kappa$ for two ends of a client.', 'types/Types.v: TProd');
n('ty.sum', 'Sum', '$T^{a} \\oplus U^{b}$, the type of $\\mathsf{inj}_1\\,v$ with $v : T$ and of $\\mathsf{inj}_2\\,v$ with $v : U$.', 'A plain type. $\\mathsf{branch}$ returns a sum whose injection records the choice.', DEF, '$\\mathsf{branch}$ at $x$ returns $S_1@x\\cdot\\kappa_{\\mathsf{false}} \\oplus S_2@x\\cdot\\kappa_{\\mathsf{true}}$.', 'types/Types.v: TSum');
n('ty.sess', 'End type $S@x$', 'An end that runs the protocol $S$ and acts next at the point $x$.', 'The points order the next actions of all ends, and readiness compares them to exclude circular waiting.', DEF, '$(!\\ast.\\mathsf{Close})@\\rho$.', 'types/Types.v: TSess');
n('ty.box', 'Box type', '$\\Box(\\forall\\bar\\iota\\,\\bar\\alpha.\\ C.\\ \\ast \\multimap^{u} U)$ is a replicable thunk, usable at every point instance $\\bar x$ with $C[\\bar x]$ and every session instance $\\bar s$.', 'A loop needs fresh points in each round. Quantifying over $\\bar\\iota$ under $\\Box$ gives every call its own instance.', DEF, 'A client loop has type $\\Box\\forall\\iota\\,\\kappa\\,\\zeta.\\ C.\\ \\ast \\multimap (S_1@\\iota \\otimes S_2@\\kappa \\multimap^{\\zeta} \\ast)$.', 'types/Types.v: TBox');
n('ty.box.svars', 'Session variables $\\bar\\alpha$', '$k$ session variables, instantiated at every $\\mathsf{force}$ by session types whose recursion passes an action.', 'One box serves every protocol the caller substitutes for $\\bar\\alpha$.', DEF, 'A forwarder box for every protocol $\\alpha$.', 'types/Types.v: TBox k');
n('ty.box.constraint', 'Box constraint $C$', 'A set of facts $x \\prec y$ over $\\bar\\iota$ and outer points, possibly infinite.', 'A loop orders the points of all its rounds at once, and an infinite $C$ states the facts of every round.', 'Without $C$ a box cannot type a loop that waits on one end while it holds another across rounds.', '$C$ states $\\iota \\prec \\overline{\\kappa}$ for the points of every round of a client loop.', 'types/Points.v: bcs');
n('ty.ex', 'Existential', '$\\exists^{l}\\bar\\iota.\\ C.\\ T^{a}$ is $T[\\bar x]$ for some $\\bar x$ with $C[\\bar x]$, and $l$ bounds the partner points of its ends from below.', 'A fresh point is unknown outside the term that created it. $\\mathsf{new}$ returns an existential over it, and payloads bind their points the same way.', DEF, '$\\mathsf{new} : \\exists^{\\bot}\\iota.\\ \\{\\overline{\\iota} \\prec \\iota\\cdot 0\\}.\\ (S@\\iota \\otimes \\overline{S}@\\overline{\\iota})$.', 'types/Types.v: TEx');
n('ty.ex.lb', 'Lower bound $l$', '$l = \\cdot$ when the value holds no end, $l = \\bot$ when its ends sit at points unknown outside, and $l = x$ when $x \\preceq y$ for every partner point $y$ of its ends.', '$\\bot$ stands for a fresh point that the context does not know, and $\\mathsf{hbot}$ propagates it.', 'Without $\\bot$, a closure captures an unopened fresh pair and claims a lower point $l$ that no fact of $W$ supports.', '$\\mathsf{new} : \\exists^{\\bot}\\ldots$', 'types/Points.v: lbound');
n('sty.skip', '$\\mathsf{Skip}$', 'The empty protocol, and an end at $S$ with $\\mathsf{unfold}(S) = \\mathsf{Skip}$ is idle.', 'No partner waits on an idle end. The fuel layer drops for idle ends the checks that counters are at least $1$, so they may be held indefinitely.', DEF, 'A control end that is passed around and never used sits at $\\mathsf{Skip}$.', 'types/Types.v: SSkip, fuel/Fuel.v: idle');
n('sty.seq', 'Sequencing', '$S.S\'$ runs $S$ and then $S\'$, and $\\mathsf{unfold}$ normalizes it to its first action.', 'Sequencing composes protocols, so a recursion variable need not occur in tail position.', DEF, '$(!\\ast).\\mathsf{Close}$.', 'types/Types.v: SSeq');
n('sty.recv', 'Receive', '$?(\\bar\\iota.\\ T^{b})$ receives a value of $T[x\\cdot 0, \\ldots, x\\cdot(m{-}1)]$ for $\\bar\\iota = \\iota_0, \\ldots, \\iota_{m-1}$ when the end sits at $x$.', 'A plain protocol action. The binder $\\bar\\iota$ is no existential, because the receiver knows the points of the payload, the fields of $x$. It lets a message carry ends whose points the receiver learns as fields of $x$.', DEF, '$\\mu\\alpha.\\,?(\\kappa.\\ \\alpha @\\kappa).\\mathsf{Close}$ receives an end of the same protocol at a field.', 'types/Types.v: SRcv');
n('sty.send', 'Send', '$!(\\bar\\iota.\\ T^{b})$ sends a value of $T[x\\cdot 0, \\ldots, x\\cdot(m{-}1)]$ for $\\bar\\iota = \\iota_0, \\ldots, \\iota_{m-1}$, at payload credit $b$.', 'A plain protocol action, $\\mathsf{dual}$ of receive.', DEF, '$!\\ast.\\mathsf{Close}$.', 'types/Types.v: SSnd');
n('sty.payload-credit', 'Payload credit $b$', 'Every end of the payload has counter at least $b$ at the receiver, and the sender supplies credit $b$ after aging by $1$.', 'Each hop of an end costs $1$. Requiring $b + 1$ of the sender when the receiver gets $b$ bounds the number of hops by the counter.', 'Without payload credits two threads pass an end back and forth forever, and its partner waits forever.', 'A payload at credit $2$.', 'types/Types.v: SRcv b, SSnd b');
n('sty.plus', 'Internal choice', '$\\oplus(S_1, S_2)$, where the selecting side chooses $i$ and continues with $S_1$ or $S_2$.', 'A plain protocol action. The holder decides the continuation.', DEF, '$\\oplus(\\mathsf{Close}, !\\ast.\\mathsf{Close})$.', 'types/Types.v: SPlus');
n('sty.with', 'External choice', '$\\&(S_1, S_2)$, where the branching side receives $i$ and continues with $S_1$ or $S_2$.', 'A plain protocol action, $\\mathsf{dual}$ of internal choice.', DEF, '$\\&(\\mathsf{Close}, ?\\ast.\\mathsf{Close})$.', 'types/Types.v: SWith');
n('sty.close', '$\\mathsf{Close}$', 'The next action of the end is $\\mathsf{close}$.', 'A plain protocol action. Every finite protocol ends with it.', DEF, '$\\mathsf{Close}@x^{+}$ after one send at $x$.', 'types/Types.v: SEnd');
n('sty.mu', 'Recursion $\\mu\\alpha.S$', 'A recursive protocol, equal to its unrolling $S[\\mu\\alpha.S/\\alpha]$ up to $\\simeq$.', 'A plain former. Loops run repeating protocols.', DEF, '$\\mu\\alpha.\\,!\\ast.\\alpha$ sends $\\ast$ forever.', 'types/Types.v: SMu');
n('sty.var', 'Session variable $\\alpha$', 'A recursion variable bound by $\\mu$, or a session variable bound by a box.', 'A plain former. It refers to an enclosing $\\mu\\alpha$ or to a protocol substituted at $\\mathsf{force}$.', DEF, '$\\alpha$ in $\\mu\\alpha.\\,!\\ast.\\alpha$.', 'types/Types.v: SVar');
n('sty.vard', 'Dual variable $\\overline{\\alpha}$', '$\\mathsf{dual}(\\alpha) = \\overline{\\alpha}$, and substituting $s$ for $\\alpha$ substitutes $\\mathsf{dual}\\,s$ for $\\overline{\\alpha}$.', 'The dual of a protocol substituted for $\\alpha$ is known only after substitution, so $\\overline{\\alpha}$ defers it.', DEF, '$\\mathsf{dual}\\,\\alpha = \\overline{\\alpha}$.', 'types/Types.v: SVarD');
n('sty.unfold', 'Head normal form', '$\\mathsf{unfold}(S)$ unrolls $\\mu$ and reassociates sequencing until the first action is on top.', 'Every rule reads the first action of a session type, so rules match on $\\mathsf{unfold}(S)$ and need no separate rule for $\\mu$.', DEF, '$\\mathsf{unfold}(\\mu\\alpha.\\,!\\ast.\\alpha) = !\\ast.(\\mu\\alpha.\\,!\\ast.\\alpha)$.', 'types/Types.v: unfoldS');
n('sty.dual', 'Duality', '$\\mathsf{dual}$ swaps $!$ with $?$ and $\\oplus$ with $\\&$, keeps payloads, $\\mathsf{Skip}$ and $\\mathsf{Close}$, and $\\overline{S} := \\mathsf{dual}\\,S$.', 'The two ends of a channel run $S$ and $\\mathsf{dual}\\,S$, so every send meets a receive.', DEF, '$\\mathsf{dual}(!\\ast.\\mathsf{Close}) = ?\\ast.\\mathsf{Close}$.', 'types/Types.v: dual');
n('sty.flip', '$\\mathsf{flip}_\\alpha$', '$\\mathsf{flip}_\\alpha$ swaps $\\alpha$ and $\\overline{\\alpha}$ for the variable bound by the enclosing $\\mu$.', 'In $\\mu\\alpha.S$ the variable $\\alpha$ names the whole protocol. After dualizing $S$, the occurrences $\\overline{\\alpha}$ must name $\\mathsf{dual}(\\mu\\alpha.S)$, which is $\\alpha$ again.', DEF, '$\\mathsf{dual}(\\mu\\alpha.\\,!\\ast.\\alpha) = \\mu\\alpha.\\,?\\ast.\\alpha$.', 'types/Types.v: sflip');
n('sty.sequiv', 'Session equivalence $\\simeq$', 'The greatest relation with $S \\simeq S\'$ only if $\\mathsf{unfold}(S)$ and $\\mathsf{unfold}(S\')$ have the same first action, with equal annotations, and equivalent continuations.', 'One protocol has many spellings, unrolled or not. Rules compare protocols up to $\\simeq$.', DEF, '$\\mu\\alpha.\\,!\\ast.\\alpha \\simeq !\\ast.\\mu\\alpha.\\,!\\ast.\\alpha$.', 'types/Types.v: sequiv');
n('ty2.stydf', '$\\mathsf{sty\\_df}$', '$\\mathsf{sty\\_df}(S)$ sets every annotation of $S$ to its value at $N = \\infty$.', 'Deadlock freedom and liveness read no credit, so two protocols that differ only in annotations are equal for them.', DEF, '$\\mathsf{sty\\_df}(!(\\ast^{2}).\\mathsf{Close}) = !(\\ast^{\\infty}).\\mathsf{Close}$.', 'types/Types.v: sty_df');
n('sty.seqv', 'Up to annotations $\\approx$', '$S \\approx S\' \\iff \\mathsf{sty\\_df}(S) \\simeq \\mathsf{sty\\_df}(S\')$.', 'The relations of deadlock freedom and liveness ignore credits, so one relation serves every refill $N$.', DEF, '$!(\\ast^{2}).\\mathsf{Close} \\approx !(\\ast^{\\infty}).\\mathsf{Close}$.', 'relation/Relation.v: seqv');
n('sty.sdual', 'Dual up to annotations', '$\\mathsf{sdual}\\,S\\,S\'$ iff $S\' \\approx \\mathsf{dual}\\,S$.', 'The relation pairs the two ends of a channel by $\\mathsf{sdual}$, consistent with comparing by $\\approx$.', DEF, 'A link of ends at $S$ and $S\'$ asks $\\mathsf{sdual}\\,S\\,S\'$.', 'relation/Relation.v: sdual');
n('ty.heads', '$\\mathsf{heads}$', '$\\mathsf{heads}(T)$ is the set of partner points of the ends a value of $T$ holds, $\\{\\overline{x}\\}$ for $S@x$, $\\{l\\}$ for an arrow or existential with bound $l$, and the union for $\\otimes$ and $\\oplus$.', 'A thread blocked at $u$ while holding a value of $T$ needs $u \\prec y$ for every $y \\in \\mathsf{heads}(T)$, or the partner of a held end may wait on the thread.', DEF, '$\\mathsf{heads}(\\mathsf{Close}@\\rho \\otimes \\mathsf{Close}@\\rho\\cdot 0) = \\{\\overline{\\rho}, \\overline{\\rho\\cdot 0}\\}$.', 'types/Types.v: heads');
n('ty.hbot', '$\\mathsf{hbot}$', '$\\mathsf{hbot}(T) = \\mathsf{true}$ iff $T$ contains an existential with bound $\\bot$ reachable through $\\otimes$ and $\\oplus$ alone.', 'Ends at unknown points satisfy no fact $u \\prec y$. A term whose context holds such ends performs no session action.', DEF, '$\\mathsf{hbot}(\\exists^{\\bot}\\iota.\\ T) = \\mathsf{true}$.', 'types/Types.v: hbot');
n('ty.lbound', 'Lower bounds $l$', '$l ::= \\cdot \\mid \\bot \\mid x$, absent, unknown, or a point.', 'It records how much a holder knows about the points of the hidden ends.', DEF, '$l = \\bot$ for $\\mathsf{new}_\\ell$.', 'types/Points.v: lbound');
n('ty.payload-at', '$\\mathsf{payload\\_at}$', '$\\mathsf{payload\\_at}\\,m\\,T\\,x = T[x\\cdot 0, \\ldots, x\\cdot(m{-}1) / \\iota_0, \\ldots, \\iota_{m-1}]$.', '$\\overline{x}\\cdot j = x\\cdot j$, so sender at $x$ and receiver at $\\overline{x}$ compute the same payload type.', DEF, 'A payload $\\alpha @\\iota_0$ sent at $Y$ has type $\\alpha @Y\\cdot 0$.', 'types/Types.v: payload_at');
n('ty.pscoped', '$\\mathsf{pscoped}$', '$\\mathsf{pscoped}\\,\\bar\\iota\\,T$ iff every point variable of $T$ is among $\\bar\\iota$.', 'A payload mentions only its own point variables, so unrolling a $\\mu$ never captures an outer point.', 'A free outer point inside a $\\mu$-body is captured on unrolling, and point substitution changes its meaning.', '$\\mathsf{pscoped}\\,\\iota_0\\,(S@\\iota_0)$.', 'types/Types.v: pscoped');
n('ann.fuel', '$\\mathbb{N} \\cup \\{\\infty\\}$', 'Credits, costs, floors and counters range over $\\mathbb{N} \\cup \\{\\infty\\}$ with $\\infty - c = \\infty$ for every $c \\in \\mathbb{N}$.', 'Deadlock-freedom typing is the instance where every fresh and refilled counter is $\\infty$, so every aging premise holds there.', DEF, '$\\infty - 3 = \\infty$.', 'types/Costs.v: fuel');
n('ann.tix', 'Ticket transformer', '$\\vartheta = (s, b)$ denotes $r \\mapsto 2^{s} r + b$ with $s, b \\in \\mathbb{N} \\cup \\{\\infty\\}$.', 'A spawn halves the tickets, so needs grow by doubling. $b = \\infty$ marks a term that no finite ticket count serves, the case of deadlock-freedom typing.', 'Without $b = \\infty$, the transformer of deadlock-freedom typing does not compose with $\\mathsf{tlink}$.', '$(0, 1)$ needs $r + 1$ tickets.', 'types/Costs.v: tix, tapp');
n('ann.tid', '$\\hat 1$', '$\\hat 1 = (0, 0)$, the identity $r \\mapsto r$.', 'A value performs no link, so it needs exactly its reserve $r$.', DEF, 'Every value types at $\\hat 1$.', 'types/Costs.v: tid');
n('ann.meets', '$\\mathsf{meets}$', '$\\mathsf{meets}\\,\\vartheta\\,r\\,tk$ iff $\\vartheta(r) \\leq tk$.', 'A thread starts with a finite ticket count $tk$, and $\\mathsf{meets}\\,\\vartheta\\,0\\,tk$ states that $tk$ covers its transformer at reserve $0$.', DEF, '$\\mathsf{meets}\\,(0, 1)\\,0\\,1$.', 'types/Costs.v: meets');
n('ann.tspawn', '$\\mathsf{tspawn}$', '$\\mathsf{tspawn}\\,b_c\\,\\vartheta = (s{+}1, \\max(2b, 2b_c{-}1))$. The child gets $\\lceil tk/2\\rceil$ tickets and needs $b_c$, the parent keeps $\\lfloor tk/2\\rfloor$.', 'The split $\\lceil tk/2\\rceil, \\lfloor tk/2\\rfloor$ is fixed, so it is the same in every run and at every index.', DEF, 'A spawn of a child that links once has $b_c = 1$.', 'types/Costs.v: tspawn');
n('ann.tlink', '$\\mathsf{tlink}$', '$\\mathsf{tlink}\\,(s, b) = (s, b{+}1)$, one ticket and then $\\vartheta$.', 'A link spends one ticket and no step creates tickets, so the total number of links of a run is at most the initial ticket count.', DEF, 'A link has transformer $\\mathsf{tlink}\\,\\hat 1 = (0, 1)$.', 'types/Costs.v: tlink');
n('ann.tseq', 'Sequencing $\\vartheta_1 \\circ \\vartheta_2$', '$(\\vartheta_1 \\circ \\vartheta_2)(r) = \\vartheta_1(\\vartheta_2(r))$, first $\\vartheta_1$, then $\\vartheta_2$.', 'The first part of a term must leave enough tickets for the rest.', DEF, 'An application composes the transformers of function, argument and call.', 'types/Costs.v: tseq');
n('ann.tok', '$\\mathsf{tok}$', '$\\mathsf{tok}\\,\\vartheta_1\\,\\vartheta_2$ iff $b_2 = 0$ or $s_1 \\neq \\infty$ or $b_1 = \\infty$.', 'Under this condition the pair $\\vartheta_1 \\circ \\vartheta_2$ bounds the tickets of the two parts in sequence. With $b_1 = \\infty$ no $tk$ meets $\\vartheta_1 \\circ \\vartheta_2$, so the composite is met nowhere.', DEF, 'An application asks $\\mathsf{tok}$ of its parts.', 'types/Costs.v: tok');
n('ann.tydf', '$\\mathsf{ty\\_df}$', '$\\mathsf{ty\\_df}(T)$ sets every annotation of $T$ to its value at $N = \\infty$, credits $\\infty$ ($0$ on $\\otimes$, $\\oplus$, $\\exists$), costs $\\infty$, $\\vartheta = (\\infty, \\infty)$, floors $\\infty$.', 'Deadlock-freedom typing is the merged judgment at $N = \\infty$, and its types carry exactly these annotations.', DEF, '$\\mathsf{ty\\_df}(S@x)$ has every payload credit of $S$ equal to $\\infty$.', 'types/Types.v: ty_df');
n('ty.prim', '$\\mathsf{prim}$', '$\\mathsf{prim}\\,T$ iff $T$ is built from $\\ast$, $\\otimes$, $\\oplus$ and boxes with $\\mathsf{prim}$ results.', 'A value of a $\\mathsf{prim}$ type holds no end, so no partner waits on the result of a process.', 'A main thread that returns an end holds it forever, and its partner waits forever.', '$\\mathsf{prim}(\\ast \\otimes \\ast)$.', 'types/Types.v: prim');
n('ty.unlimited', '$\\mathsf{unlimited}$', '$\\mathsf{unlimited}\\,T$ iff $T$ is a box type, so its variables admit weakening and contraction.', '$V$ at a box type asks $\\Theta = \\varnothing$, so copying or dropping the value duplicates or loses no end.', DEF, 'The self of a box is unlimited.', 'types/Types.v: unlimited');
n('ty.tfree', '$\\mathsf{tfree}$', '$\\mathsf{tfree}\\,T$ holds for types built from $\\ast$, boxes, $\\otimes$ and $\\oplus$ whose values hold no end.', 'Aging and capture change the credits of entries that hold ends. For $\\mathsf{tfree}\\,T$ the entry holds none, so they leave it unchanged.', DEF, '$\\mathsf{tfree}(\\ast \\otimes \\Box\\ldots)$.', 'types/Types.v: tfree');
n('w.world', 'World', '$W = (A, \\prec_A)$, roots and facts.', 'Points carry the order, and $W$ is the data that generates the order $\\prec_W$. A creation grows $W$ by its facts.', DEF, '$W$ with $A = \\{1, 2\\}$ and the fact $1 \\prec \\overline{2}$.', 'types/Worlds.v: world');
n('w.consts', 'Roots $A$', '$A$ is the finite set of roots of $W$.', 'Facts mention only points with roots in $A$, and composition compares two worlds through $A_1 \\cap A_2$.', DEF, '$A = \\{1, 2\\}$.', 'types/Worlds.v: w_consts');
n('w.facts', 'Facts $\\prec_A$', 'A set of facts $x \\prec y$, possibly infinite, between points whose roots lie in $A$.', 'They order the channels a component shares with its environment and the channels created so far.', DEF, '$1 \\prec \\overline{2}$.', 'types/Worlds.v: w_facts');
n('w.lt', '$\\prec_W$', '$\\prec_W$ is the transitive closure of the three generators, and $W \\vdash x \\prec y$ means $x \\prec_W y$.', 'A waiting chain combines several facts, so the order is transitive.', DEF, '$W \\vdash x \\prec x^{++}$.', 'types/Worlds.v: w_lt');
n('w.ws-fact', 'Facts generator', '$x \\prec_A y$ implies $x \\prec_W y$.', 'A plain generator. The facts of $W$ hold in $\\prec_W$.', DEF, '$1 \\prec_W \\overline{2}$.', 'types/Worlds.v: ws_fact');
n('w.ws-po', '$x \\prec x^{+}$', 'For every $x$, $x \\prec_W x^{+}$.', 'An end acts at $x$ before it acts at $x^{+}$, so $\\prec_W$ contains the program order of each end.', DEF, '$\\rho \\prec \\rho^{+}$.', 'types/Worlds.v: ws_po');
n('ty2.le', 'Order or equal $\\preceq$', '$x \\preceq y$ iff $x = y$ or $x \\prec_W y$.', 'Lower bounds compare by $\\preceq$, so a closure whose only captured end has partner point $l$ may have lower point $l$.', DEF, 'A closure capturing $a^{+}$ at $\\rho$ has $l = \\overline{\\rho}$ and $\\overline{\\rho} \\preceq \\overline{\\rho}$.', 'types/Worlds.v: w_le');
n('w.ws-dpo', '$x \\prec \\overline{x}^{+}$', 'For every $x$, $x \\prec_W \\overline{x}^{+}$.', 'The fact holds in every run. The action at $x$ synchronizes with the partner at $\\overline{x}$, and the partner acts at $\\overline{x}^{+}$ only afterwards, so $W$ may contain it for free.', DEF, '$\\rho \\prec \\overline{\\rho}^{+}$.', 'types/Worlds.v: ws_dpo');
n('w.wf', '$\\mathsf{world\\_wf}$', '$\\mathsf{world\\_wf}\\,W$ iff every fact of $\\prec_A$ relates points with roots in $A$.', 'A fact outside $A$ mentions a point no component owns.', DEF, 'A fact $1 \\prec 3$ with $3 \\notin A$ violates it.', 'types/Worlds.v: world_wf');
n('w.strict', '$\\mathsf{strict}$', '$\\mathsf{strict}\\,W$ iff $\\mathsf{world\\_wf}\\,W$ and $W \\nvdash x \\prec x$ for every $x$, so $\\prec_W$ is acyclic.', 'Readiness of two threads that wait on each other needs $x \\prec y$ and $y \\prec x$, hence $x \\prec x$. Strictness excludes it.', 'In a cyclic $W$ two threads that wait on each other both count as ready, and a deadlocked process is in the relation.', '$W$ whose only fact is $1 \\prec \\overline{2}$.', 'types/Worlds.v: strict');
n('w.lfworld', '$\\mathsf{wfworld}$', '$\\mathsf{wfworld}\\,W$ iff $\\prec_W$ is well-founded, so no infinite chain $\\cdots \\prec x_2 \\prec x_1 \\prec x_0$ exists.', 'Lock freedom ranks a pending thread by the point of the end it waits on, and every waiting chain descends in $\\prec_W$. Well-foundedness makes every such chain finite.', 'Without it, waiting descends forever. Each thread waits on one below it, new threads keep appearing below, and the top thread never proceeds.', '$W$ with no facts satisfies $\\mathsf{wfworld}\\,W$.', 'types/Worlds.v: wfworld');
n('w.ext', 'Extension $\\sqsubseteq$', '$W \\sqsubseteq W\'$ iff $A \\subseteq A\'$ and every fact of $W$ is a fact of $W\'$.', '$W \\sqsubseteq W\'$ implies $\\prec_W \\subseteq \\prec_{W\'}$, so every relation stated monotone in $W$ survives growth and composition with another component.', DEF, '$W \\sqsubseteq W \\oplus C$ and $W \\sqsubseteq W \\sqcup W\'$.', 'types/Worlds.v: wext');
n('w.grow', 'Growth $W \\oplus C$', '$W \\oplus C$ adds the roots of the facts $C$ to $A$ and the facts $C$ to $\\prec_A$.', 'A creation adds a fresh root and the facts its typing chose, so the world of a run grows with every $\\mathsf{new}$ and never loses a fact.', 'With all facts fixed before the run, every fresh point obeys facts chosen in advance, and a channel between two given channels needs those facts for every possible pair.', '$W \\oplus \\{1 \\prec a,\\ a \\prec \\overline{2}\\}$ with $a$ fresh places $a$ between $1$ and $\\overline{2}$.', 'types/Worlds.v: wgrow');
n('w.join', 'Join $\\sqcup$', '$W_1 \\sqcup W_2$ takes the unions of roots and facts.', 'Two components typed in $W_1$ and $W_2$ compose in $W_1 \\sqcup W_2$.', DEF, '$W \\sqsubseteq W \\sqcup W\'$ and $W\' \\sqsubseteq W \\sqcup W\'$.', 'types/Worlds.v: wjoin');
n('w.restrict', 'Restriction $W|_S$', '$W|_S$ has the facts $x \\prec_W y$ with roots of $x, y$ in $S$.', 'It is the part of $\\prec_W$ another component sees through the shared constants $S$.', DEF, '$W|_{A_1 \\cap A_2}$.', 'types/Worlds.v: wrestrict');
n('w.R7', 'Strict join', '$\\mathsf{strict}(W_1 \\sqcup W_2)$ iff $\\mathsf{strict}\\,W_1$, $\\mathsf{strict}\\,W_2$ and $\\mathsf{strict}(W_1|_S \\sqcup W_2|_S)$ for $S = A_1 \\cap A_2$.', 'Strictness of the join is decided on the shared constants $S$ alone.', DEF, 'Two strict worlds with $A_1 \\cap A_2 = \\varnothing$ have a strict join.', 'types/Worlds.v: strict_join_iff');

// ---- signatures and arguments ----
const { sa } = require('./core');
const A = (name, meaning) => ({ name, meaning });
const Tt = A('T', R`A type.`);
const Ss = A('S', R`A session type.`);
const Ww = A('W', R`A world.`);
const XY = A(R`x, y`, R`Points.`);
const TH = A(R`\vartheta`, R`A ticket transformer $(s, b)$, denoting $r \mapsto 2^{s} r + b$.`);
sa('ty.unit', R`\ast \in \mathsf{Ty}`, []);
sa('ty.arrow', R`T^{a} \multimap^{u}_{l}[c ; \vartheta ; h]\,U^{b} \in \mathsf{Ty}`, [A('T, a', R`The argument type and its credit.`), A('U, b', R`The result type and its credit.`), A('u', R`The upper point, optional.`), A('l', R`The lower point, absent iff the closure holds no end.`), A('c', R`The cost of a call, $c \in \mathbb{N} \cup \{\infty\}$.`), TH, A('h', R`The floor of the captured ends.`)]);
sa('ty.arrow.ub', R`u \in \mathsf{Point}_{\bot}`, [A('u', R`A point or absent. The body is in $E$ under every future $F$ with $u \prec y$ for all $y \in F$.`)]);
sa('ty.arrow.lb', R`l \in \mathsf{Point}_{\bot}`, [A('l', R`A point with $l \preceq y$ for every $y \in \mathsf{heads}(\Theta)$ of the captured environment $\Theta$, or absent iff $\Theta = \varnothing$.`)]);
sa('ty.arrow.cost', R`c \in \mathbb{N} \cup \{\infty\}`, [A('c', R`An upper bound on the channel actions of one call before it returns.`)]);
sa('ty.arrow.tix', R`\vartheta \in \mathsf{Tix}`, [TH]);
sa('ty.arrow.floor', R`h \in \mathbb{N} \cup \{\infty\}`, [A('h', R`The credit at which the body sees each captured end.`)]);
sa('ty.credit', R`a \in \mathbb{N} \cup \{\infty\}`, [A('a', R`A lower bound on the counter of every end a value of $T^{a}$ holds.`)]);
sa('ty.credit-agg', R`(T^{a_1} \otimes U^{a_2})^{a}`, [A('a', R`The outer credit of the aggregate.`), A(R`a_1, a_2`, R`The inner credits, the parts get $a + a_1$ and $a + a_2$.`)]);
sa('ty.prod', R`T^{a} \otimes U^{b} \in \mathsf{Ty}`, [A(R`T, U`, R`The component types.`), A(R`a, b`, R`The component credits.`)]);
sa('ty.sum', R`T^{a} \oplus U^{b} \in \mathsf{Ty}`, [A(R`T, U`, R`The types of the two injections.`), A(R`a, b`, R`Their credits.`)]);
sa('ty.sess', R`S@x \in \mathsf{Ty}`, [A('S', R`The protocol the end runs.`), A('x', R`The point of its next action.`)]);
sa('ty.box', R`\Box(\forall\bar\iota\,\bar\alpha.\ C.\ \ast \multimap^{u}[c ; \vartheta]\,U^{b}) \in \mathsf{Ty}`, [A(R`\bar\iota`, R`$m$ point variables, instantiated at each $\mathsf{force}$ by points $\bar x$ with $C[\bar x]$.`), A(R`\bar\alpha`, R`$k$ session variables, instantiated at each $\mathsf{force}$.`), A('C', R`The constraint over $\bar\iota$ and outer points.`), A('u', R`The upper point of the thunk.`), A(R`c, \vartheta`, R`Cost and transformer of one force.`), A('U, b', R`The result type and credit.`)]);
sa('ty.box.svars', R`\bar\alpha = \alpha_1, \ldots, \alpha_k`, [A('k', R`The number of session variables.`)]);
sa('ty.box.constraint', R`C \subseteq \{x \prec y \mid x, y \in \mathsf{Point}\}`, [A('C', R`A set of facts over $\bar\iota$ and outer points, possibly infinite.`)]);
sa('ty.ex', R`\exists^{l}\bar\iota.\ C.\ T^{a} \in \mathsf{Ty}`, [A('l', R`The lower bound, $\cdot$, $\bot$ or a point.`), A(R`\bar\iota`, R`$m$ point variables, the witness $\bar x$ is hidden.`), A('C', R`The facts the witness satisfies.`), A('T, a', R`The body type and its credit.`)]);
sa('ty.ex.lb', R`l \in \{\cdot, \bot\} \cup \mathsf{Point}`, [A('l', R`$\cdot$ for no end, $\bot$ for ends at unknown points, $x$ when $x \preceq y$ for every partner point $y$ of the ends.`)]);
sa('sty.skip', R`\mathsf{Skip} \in \mathsf{STy}`, []);
sa('sty.seq', R`S.S' \in \mathsf{STy}`, [A(R`S, S'`, R`The first and the second protocol.`)]);
sa('sty.recv', R`?(\bar\iota.\ T^{b}) \in \mathsf{STy}`, [A(R`\bar\iota`, R`The point variables of the payload, $\iota_0, \ldots, \iota_{m-1}$, placed at $x\cdot 0, \ldots, x\cdot(m{-}1)$ for the carrier point $x$.`), A('T', R`The payload type.`), A('b', R`The payload credit.`)]);
sa('sty.send', R`!(\bar\iota.\ T^{b}) \in \mathsf{STy}`, [A(R`\bar\iota`, R`The point variables of the payload, placed at the fields of the carrier point.`), A('T', R`The payload type.`), A('b', R`The payload credit.`)]);
sa('sty.payload-credit', R`b \in \mathbb{N} \cup \{\infty\}`, [A('b', R`The counter the receiver may assume for each end of the payload.`)]);
sa('sty.plus', R`\oplus(S_1, S_2) \in \mathsf{STy}`, [A(R`S_1, S_2`, R`The continuations for $i = \mathsf{false}$ and $i = \mathsf{true}$.`)]);
sa('sty.with', R`\&(S_1, S_2) \in \mathsf{STy}`, [A(R`S_1, S_2`, R`The continuations for the received $i = \mathsf{false}$ and $i = \mathsf{true}$.`)]);
sa('sty.close', R`\mathsf{Close} \in \mathsf{STy}`, []);
sa('sty.mu', R`\mu\alpha.S \in \mathsf{STy}`, [A(R`\alpha`, R`The recursion variable, bound in $S$.`), A('S', R`The body.`)]);
sa('sty.var', R`\alpha \in \mathsf{STy}`, [A(R`\alpha`, R`A variable bound by an enclosing $\mu$ or by a box.`)]);
sa('sty.vard', R`\overline{\alpha} \in \mathsf{STy}`, [A(R`\alpha`, R`A session variable, $\overline{\alpha}$ stands for $\mathsf{dual}$ of its instance.`)]);
sa('sty.unfold', R`\mathsf{unfold} : \mathsf{STy} \to \mathsf{STy}`, [A('S', R`A contractive session type, $\mathsf{unfold}(S)$ has its first action on top.`)]);
sa('sty.dual', R`\mathsf{dual} : \mathsf{STy} \to \mathsf{STy}`, [Ss, A('P', R`A payload, kept unchanged.`), A(R`S_1, S_2`, R`Continuations.`)]);
sa('sty.flip', R`\mathsf{flip}_\alpha : \mathsf{STy} \to \mathsf{STy}`, [A(R`\alpha`, R`The variable of the enclosing $\mu$, whose occurrences $\alpha$ and $\overline{\alpha}$ are swapped.`)]);
sa('sty.sequiv', R`\cdot \simeq \cdot \subseteq \mathsf{STy} \times \mathsf{STy}`, [A(R`S, S'`, R`Session types, related iff their unfoldings agree on first action and annotations and have related continuations.`)]);
sa('ty2.stydf', R`\mathsf{sty\_df} : \mathsf{STy} \to \mathsf{STy}`, [Ss]);
sa('sty.seqv', R`\cdot \approx \cdot \subseteq \mathsf{STy} \times \mathsf{STy}`, [A(R`S, S'`, R`Session types compared after $\mathsf{sty\_df}$.`)]);
sa('sty.sdual', R`\mathsf{sdual} : \mathsf{STy} \to \mathsf{STy} \to \mathsf{Prop}`, [A('S', R`The protocol of one end.`), A(R`S'`, R`The protocol of its partner, $S' \approx \mathsf{dual}\,S$.`)]);
sa('ty.heads', R`\mathsf{heads} : \mathsf{Ty} \to \mathcal{P}_{\mathrm{fin}}(\mathsf{Point})`, [Tt]);
sa('ty.hbot', R`\mathsf{hbot} : \mathsf{Ty} \to \mathbb{B}`, [Tt]);
sa('ty.lbound', R`l \in \mathsf{LBound} = \{\cdot, \bot\} \cup \mathsf{Point}`, []);
sa('ty.payload-at', R`\mathsf{payload\_at} : \mathbb{N} \to \mathsf{Ty} \to \mathsf{Point} \to \mathsf{Ty}`, [A('m', R`The number of point variables of the payload.`), A('T', R`The payload type over $\iota_0, \ldots, \iota_{m-1}$.`), A('x', R`The point of the carrier end.`)]);
sa('ty.pscoped', R`\mathsf{pscoped} : \mathsf{PVar}^{*} \to \mathsf{Ty} \to \mathsf{Prop}`, [A(R`\bar\iota`, R`The point variables the payload binds.`), A('T', R`The payload type.`)]);
sa('ann.fuel', R`\mathbb{N} \cup \{\infty\}`, []);
sa('ann.tix', R`\vartheta = (s, b) \in \mathsf{Tix} = (\mathbb{N} \cup \{\infty\})^{2}`, [A('s', R`The doubling exponent.`), A('b', R`The offset.`), A('r', R`The reserve of tickets on return.`)]);
sa('ann.tid', R`\hat 1 \in \mathsf{Tix}`, []);
sa('ann.meets', R`\mathsf{meets} : \mathsf{Tix} \to \mathbb{N} \to \mathbb{N} \to \mathsf{Prop}`, [TH, A('r', R`The reserve on return.`), A('tk', R`The available tickets.`)]);
sa('ann.tspawn', R`\mathsf{tspawn} : (\mathbb{N} \cup \{\infty\}) \to \mathsf{Tix} \to \mathsf{Tix}`, [A(R`b_c`, R`The offset the child needs.`), A(R`\vartheta`, R`The transformer $(s, b)$ of the parent continuation.`)]);
sa('ann.tlink', R`\mathsf{tlink} : \mathsf{Tix} \to \mathsf{Tix}`, [A(R`\vartheta`, R`The transformer $(s, b)$ after the link.`)]);
sa('ann.tseq', R`\cdot \circ \cdot : \mathsf{Tix} \to \mathsf{Tix} \to \mathsf{Tix}`, [A(R`\vartheta_1, \vartheta_2`, R`The transformers of the first and the second part.`)]);
sa('ann.tok', R`\mathsf{tok} : \mathsf{Tix} \to \mathsf{Tix} \to \mathsf{Prop}`, [A(R`\vartheta_1 = (s_1, b_1)`, R`The first transformer.`), A(R`\vartheta_2 = (s_2, b_2)`, R`The second transformer.`)]);
sa('ann.tydf', R`\mathsf{ty\_df} : \mathsf{Ty} \to \mathsf{Ty}`, [Tt]);
sa('ty.prim', R`\mathsf{prim} : \mathsf{Ty} \to \mathsf{Prop}`, [Tt]);
sa('ty.unlimited', R`\mathsf{unlimited} : \mathsf{Ty} \to \mathsf{Prop}`, [Tt]);
sa('ty.tfree', R`\mathsf{tfree} : \mathsf{Ty} \to \mathsf{Prop}`, [Tt]);
sa('w.world', R`W = (A, \prec_A) \in \mathsf{World}`, [A('A', R`The roots.`), A(R`\prec_A`, R`The facts.`)]);
sa('w.consts', R`A \in \mathcal{P}_{\mathrm{fin}}(\mathsf{Root})`, []);
sa('w.facts', R`\prec_A \subseteq \mathsf{Point} \times \mathsf{Point}`, []);
sa('w.lt', R`W \vdash \cdot \prec \cdot \subseteq \mathsf{Point} \times \mathsf{Point}`, [Ww, XY]);
sa('w.ws-fact', R`x \prec_A y \Rightarrow x \prec_W y`, [XY]);
sa('w.ws-po', R`\forall x.\ x \prec_W x^{+}`, [A('x', R`Any point.`)]);
sa('ty2.le', R`\cdot \preceq \cdot \subseteq \mathsf{Point} \times \mathsf{Point}`, [XY]);
sa('w.ws-dpo', R`\forall x.\ x \prec_W \overline{x}^{+}`, [A('x', R`Any point.`)]);
sa('w.wf', R`\mathsf{world\_wf} : \mathsf{World} \to \mathsf{Prop}`, [Ww]);
sa('w.strict', R`\mathsf{strict} : \mathsf{World} \to \mathsf{Prop}`, [Ww, A('x', R`Ranges over all points.`)]);
sa('w.lfworld', R`\mathsf{wfworld} : \mathsf{World} \to \mathsf{Prop}`, [Ww]);
sa('w.grow', R`\cdot \oplus \cdot : \mathsf{World} \to \mathcal{P}(\mathsf{Point} \times \mathsf{Point}) \to \mathsf{World}`, [Ww, A('C', R`The facts of a creation, over the fresh root and points of $W$.`)]);
sa('w.ext', R`\cdot \sqsubseteq \cdot \subseteq \mathsf{World} \times \mathsf{World}`, [A(R`W, W'`, R`The smaller and the larger world.`)]);
sa('w.join', R`\cdot \sqcup \cdot : \mathsf{World} \to \mathsf{World} \to \mathsf{World}`, [A(R`W_1, W_2`, R`The worlds of two components.`)]);
sa('w.restrict', R`\cdot|_{\cdot} : \mathsf{World} \to \mathcal{P}(\mathsf{Root}) \to \mathsf{World}`, [Ww, A('S', R`A set of constants, instantiated with $A_1 \cap A_2$.`)]);
sa('w.R7', R`\mathsf{strict}(W_1 \sqcup W_2) \iff \ldots`, [A(R`W_1, W_2`, R`Two well-formed worlds.`), A('S', R`The shared constants $A_1 \cap A_2$.`)]);
