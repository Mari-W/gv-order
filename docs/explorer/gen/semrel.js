const { R, h, n, sa, section, block, rule, DEF } = require('./core');

const s = section('semantic', 'Semantic typing',
  'One step-indexed relation $(V, E, P)$ parametric in a cost table $\\kappa$, the fuel predicate $F^N$ on counters and tickets, and the soup $S^{N,W}_n$ that fixes ownership before the level. The sorts are $\\mathsf{Env} = \\mathsf{End} \\rightharpoonup \\mathsf{STy} \\times \\mathsf{Point}$, $\\mathsf{TEnv}$ the same with credits, $\\mathsf{PEnv} = \\mathsf{End} \\rightharpoonup \\mathsf{STy}$, $\\mathsf{CEnv} = \\mathsf{End} \\rightharpoonup \\mathbb{N} \\cup \\{\\infty\\}$, $\\mathsf{Own}$ the ownership maps, $\\mathsf{LFState}$ the soup states, $\\mathsf{CTable} \\subseteq \\mathbb{N}^6$, $\\mathsf{Fam}$ and $\\mathsf{Field}$ the labels, $\\mathsf{SFuture}$ the static futures.');

// symbols used across the blocks
const BIN = (k, t) => R`\mathbin{${h(k, t)}}`;
const REL = (k, t) => R`\mathrel{${h(k, t)}}`;
const FENDS = h('syn.fends', R`\mathsf{fends}`);
const HEADS = h('ty.heads', R`\mathsf{heads}`);
const UNF = h('sty.unfold', R`\mathsf{unfold}`);
const CLOSE = h('sty.close', R`\mathsf{Close}`);
const ECH = h('end.ech', R`\mathsf{ech}`);
const EXT = REL('w.ext', R`\sqsupseteq`);
const UPL = BIN('ctx.tsplit', R`\uplus`);
const SEQV = REL('sty.seqv', R`\approx`);
const SEQU = REL('sty.sequiv', R`\simeq`);
const ARR = REL('ty.arrow', R`\multimap`);
const LEQ = REL('ty2.le', R`\preccurlyeq`);
const SDUAL = h('sty.sdual', R`\mathsf{sdual}`);
const WLT = (W, x, y) => h('w.lt', R`${W} \vdash ${x} \prec ${y}`);
const PAY = (U, x) => h('ty.payload-at', R`${U}[${x}\cdot\bar\imath]`);
const SND = (U) => h('sty.send', R`!(\bar\iota.\ ${U})`);
const RCV = (U) => h('sty.recv', R`?(\bar\iota.\ ${U})`);
// the deadlock-free reading of a level condition, and its lock-free reading under a general table
const DL = (df, lf) => R`\dfo{${df}}\annot{${lf}}`;
const KA = DL(R`${h('ct.DF', R`\kappa_{DF}`)}(\alpha)`, R`${h('ct.table', R`\kappa`)}(\alpha)`);
const LT = (j, k) => DL(R`${j} < n`, R`${j} + \kappa_{${k}} \leq n`);
// an end whose protocol unfolds to a given head
const HD = (env, o, form, x) => h('sr.head', R`${env}(${o}) \doteq ${form}@${x}`);
const V = (W, nn, Th, T) => h('th.Vrel', R`V^{${W}}_{${nn}}\llbracket ${Th} \vdash ${T} \rrbracket`);
const E = (W, nn, Th, T, F) => h('th.Erel', R`E^{${W}}_{${nn}}\llbracket ${Th} \vdash ${T} \rrbracket^{${F}}`);
const P = (W, nn, Sg, T) => h('th.Prel', R`P^{${W}}_{${nn}}\llbracket ${Sg} \vdash ${T} \rrbracket`);
const AT = (t) => h('rel.atcost', R`${t}\ \text{at}`);
const FV = (N, nn, T, args) => h('sr.FV', R`FV^{${N}}_{${nn}}\llbracket ${T} \rrbracket(${args})`);
const FE = (N, nn, body, args) => h('sr.FE', R`F^{${N}}_{${nn}}\llbracket ${body} \rrbracket(${args})`);
const THR = h('fu.rty', R`\mathsf{thread}`);
const ACT = h('sr.act', R`\mathsf{act}`);
const FSPARE = h('fu.fspare', R`\mathsf{fspare}`);
const REFILL = h('fu.refillop', R`\mathsf{refill}`);
const FHAND = h('fu.fhand', R`\mathsf{fhand}`);
const MEETS = h('ann.meets', R`\mathsf{meets}`);
const RLE = REL('fu.refill-kripke', R`\sqsupseteq_{\mathsf{rle}}`);
const DM = R`\mathbin{\dot-}`;
// a clause of a relation as a rule, premises side by side, rows stacked
// the conclusion of an obligation rule hovers to the note of the rule
const RULE = (name, rows, concl) => rule(name, R`\begin{array}{c}${rows.map(r => r.join(R`\quad `)).join(R` \\ `)}\end{array}`, /^[OQ]-/.test(name) ? h(name, concl) : concl);
const PB = (a) => h('sr.pobl', R`\mathsf{Pobl}_{${a}}(p')`);
const OB = (a) => h('sr.obl', R`\mathsf{Obl}_{${a}}(e')`);

// cost tables
block(s, {
  id: 'sr-reading', title: 'Reading the relations', rocq: 'relation/Relation.v: Vrel, Erel, Prel, at_cost_E',
  tex: R`\begin{array}{ll}
${h('th.Vrel', R`v \in V^{W}_{n}\llbracket \Theta \vdash T \rrbracket`)} & \text{the value } v \text{ owns exactly the ends } \Theta \text{ and is safe at } T \\
${h('th.Erel', R`e \in E^{W}_{n}\llbracket \Theta \vdash T \rrbracket^{F}`)} & \text{the term } e \text{, holding } \Theta \text{, is safe until it returns a value of } T \text{, its context acting at } F \text{ afterwards} \\
${h('th.Prel', R`p \in P^{W}_{n}\llbracket \Sigma \vdash T \rrbracket`)} & \text{the process } p \text{ is safe with interface } \Sigma \\
${h('sr.obl', R`\mathsf{Obl}_\alpha(e')`)} & \text{what a step } e \xrightarrow{\alpha} e' \text{ must preserve} \\
${h('rel.atcost', R`e'\ \text{at}\ \Theta'`)} & e' \text{ is safe holding } \Theta' \text{, at the same level after a free step and one level lower otherwise}
\annraw{\\}\annot{${h('sr.FE', R`e \in F^{N}_{n}\llbracket \sigma \triangleright d ; r \rrbracket(\Pi, \varphi, tk)`)}}\annraw{&}\annot{\text{the thread } e \text{ has counters } \varphi \text{ and tickets } tk \text{ for } n \text{ more steps, reading no point}}
\annraw{\\}\annot{${h('th.soup', R`a \in S^{N,W}_{n}\llbracket \Sigma \vdash T \rrbracket`)}}\annraw{&}\annot{\text{every thread of } a \text{ is in } E[\kappa_L] \text{ and fueled, over one ownership map}}
\end{array}`,
  caption: 'Every relation is indexed by a world $W$, whose order of points the relation reads, and a level $n$, the number of further steps it promises safety for. Safe means never stuck in a deadlock, every end owned by exactly one thread, and every message fitting its protocol.'
});
block(s, {
  id: 'ct-table', title: 'Cost tables', rocq: 'relation/CostTable.v: ctable', modes: ['lf'],
  tex: R`\begin{array}{l}
${h('ct.table', R`\kappa = (\kappa_\beta, \kappa_{new}, \kappa_{spawn}, \kappa_{link}, \kappa_{give}, \kappa_{take}) \in \mathbb{N}^{6}`)} \\
${h('ct.take-pos', R`1 \leq \kappa_{take}`)} \qquad ${h('ct.give-pos', R`\kappa_\beta = 0 \Rightarrow 1 \leq \kappa_{give}`)} \qquad ${h('ct.give-take', R`\kappa_{give} \leq \kappa_{take}`)}
\end{array}`,
  caption: 'A cost table $\\kappa$ assigns a cost to each kind of step, subject to three conditions.'
});
block(s, {
  id: 'ct-two', title: 'Step costs', rocq: 'relation/CostTable.v: κ_DF, κ_L, ev_cost',
  tex: R`\begin{array}{lcc}
 & ${h('ct.DF', R`\kappa_{DF}`)} & ${h('ct.L', R`\kappa_L`)} \\ \hline
${h('ct.beta', R`\beta`)} & 1 & 0 \\
${h('ct.new', R`\mathsf{new}`)} & 1 & 0 \\
${h('ct.spawn', R`\mathsf{spawn}`)} & 1 & 0 \\
${h('ct.link', R`\mathsf{link}`)} & 0 & 0 \\
${h('ct.give', R`\mathsf{send},\ \mathsf{select},\ \mathsf{close}`)} & 0 & 1 \\
${h('ct.takek', R`\mathsf{recv},\ \mathsf{branch}`)} & 1 & 1 \\
${h('ct.sync', R`\kappa_{give} + \kappa_{take}`)} & 1 & 2
\end{array}`,
  variants: {
    df: R`\begin{array}{lc}
 & ${h('ct.DF', R`\kappa_{DF}`)} \\ \hline
${h('ct.beta', R`\beta`)} & 1 \\
${h('ct.new', R`\mathsf{new}`)} & 1 \\
${h('ct.spawn', R`\mathsf{spawn}`)} & 1 \\
${h('ct.link', R`\mathsf{link}`)} & 0 \\
${h('ct.give', R`\mathsf{send},\ \mathsf{select},\ \mathsf{close}`)} & 0 \\
${h('ct.takek', R`\mathsf{recv},\ \mathsf{branch}`)} & 1 \\
${h('ct.sync', R`\text{a message, send with recv}`)} & 1
\end{array}`
  },
  caption: 'The levels each kind of step costs in the deadlock-free relation. \\annp{The lock-free relation uses $\\kappa_L$, and a synchronization costs $\\kappa_{give} + \\kappa_{take}$.}'
});
block(s, {
  id: 'rel-atcost', title: 'After a step', rocq: 'relation/Relation.v: at_cost_E, at_cost_V, at_cost_P',
  tex: R`${AT(R`e'`)}\ \Theta' \iff \begin{cases} ${h('rel.lfp', R`X(W, \Theta', T, F, e')`)} & ${KA} = 0 \\ e' \in ${E('W', R`n-${KA}`, R`\Theta'`, 'T', 'F')} & ${KA} > 0 \end{cases}`,
  caption: 'The reading of a successor $e\'$ after a step $\\alpha$ taken at level $n$, where $X$ is the least fixpoint under construction.'
});

// V
block(s, {
  id: 'v-base', title: 'Values of unit, end, product and sum type', rocq: 'relation/Relation.v: Vbody',
  tex: R`\begin{array}{c}
${RULE('V-Unit', [[R`\phantom{x}`]], h('V-Unit', R`\ast \in ${V('W', 'n', R`\varnothing`, R`\ast`)}`))} \qquad ${RULE('V-Sess', [[R`S' ${SEQV} S`]], h('V-Sess', R`o \in ${V('W', 'n', h('V-Sess.exact', R`\{o \mapsto S'@x\}`), R`S@x`)}`))} \\[2ex]
${RULE('V-Prod', [[R`v_1 \in ${V('W', 'n', R`\Theta_1`, R`T_1`)}`, R`v_2 \in ${V('W', 'n', R`\Theta_2`, R`T_2`)}`]], h('V-Prod', R`\langle v_1, v_2\rangle \in ${V('W', 'n', h('V-Prod.split', R`\Theta_1 ${UPL} \Theta_2`), R`T_1 \otimes T_2`)}`))} \qquad ${RULE('V-Sum', [[R`v \in ${V('W', 'n', R`\Theta`, R`T_i`)}`]], h('V-Sum', R`${h('syn.inj', R`\mathsf{inj}_i`)}\,v \in ${V('W', 'n', R`\Theta`, R`T_1 \oplus T_2`)}`))}
\end{array}`,
  caption: 'Each rule is one clause of $V$, read as an equivalence. The environment $\\Theta$ maps exactly the ends the value owns, so a unit owns none, an end owns itself, and a pair splits its ends between its components.'
});
block(s, {
  id: 'v-arrow', title: 'Values of arrow type', rocq: 'relation/Relation.v: Varr',
  tex: RULE('V-Arrow', [
    [h('V-Arrow.exact', R`\mathrm{dom}\,\Theta = ${FENDS}(e)`), h('V-Arrow.lb', R`l ${LEQ} ${HEADS}\,\Theta`)],
    [R`${h('V-Arrow.kripke', R`\forall W' ${EXT} W`)},\ ${h('V-Arrow.level', LT('j', R`\beta`))},\ \Theta' \mathbin{\#} \Theta,\ ${h('V-Arrow.ub', R`F \text{ with } ${WLT("W'", 'u', 'F')}`)}.`],
    [R`w \in ${V("W'", 'j', R`\Theta'`, 'T')} \ \Longrightarrow\ ${h('V-Arrow.body', R`e[w] \in ${E("W'", 'j', R`\Theta \cup \Theta'`, 'U', 'F')}`)}`]],
    R`\lambda e \in ${V('W', 'n', R`\Theta`, R`T ${ARR}^{u}_{l} U`)}`),
  caption: 'A closure owns exactly the ends it mentions, and $l$ lies at or below their partner points. Calling it is safe in every later world, at every lower level, with every argument owning other ends, and for every caller future above $u$.'
});
block(s, {
  id: 'v-thunk', title: 'Thunks, the closures a spawn runs', rocq: 'relation/Relation.v: Vthunk',
  tex: RULE('V-Thunk', [
    [h('V-Arrow.exact', R`\mathrm{dom}\,\Theta = ${FENDS}(e)`)],
    [R`\forall W' ${EXT} W,\ ${LT('j', R`\beta`)},\ \Theta' \mathbin{\#} \Theta.\quad w \in ${V("W'", 'j', R`\Theta'`, R`\ast`)} \ \Longrightarrow\ e[w] \in ${E("W'", 'j', R`\Theta \cup \Theta'`, R`\ast`, h('V-Thunk.empty', R`\varnothing`))}`]],
    R`\lambda e \in ${h('sr.vthunk', R`\mathsf{Vthunk}^{W}_{n}(\Theta)`)}`),
  caption: 'A thunk is a closure $\\lambda\\_.\\,e$ that only takes $\\ast$, a computation put off until it is called. $\\mathsf{spawn}$ takes a thunk and runs its body as a new thread. The child has nothing after it, so its body is read at the empty future, and the thunk needs no lower or upper point.'
});
block(s, {
  id: 'v-box', title: 'Values of box type', rocq: 'relation/Relation.v: Vbody (TBox), Vrel_box_iff',
  tex: RULE('V-Box', [
    [h('V-Box.empty', R`\Theta = \varnothing`), h('V-Box.noends', R`${FENDS}(e) = \varnothing`)],
    [R`${h('V-Box.kripke', R`\forall W' ${EXT} W`)},\ ${h('V-Box.inst', R`\bar x \text{ with } W' \vdash C[\bar x]`)},\ ${h('V-Box.hc', R`\bar s \text{ contractive}`)}.\quad ${h('V-Box.thunk', R`${h('sr.thunk', R`\mathsf{thunk}(e)`)} \in ${V("W'", 'n', R`\varnothing`, R`\ast ${ARR}^{u[\bar x]} U[\bar s][\bar x]`)}`)}`]],
    R`!e \in ${V('W', 'n', R`\varnothing`, R`\Box(\forall\bar\iota\,\bar\alpha.\,C.\ \ast ${ARR}^{u} U)`)}`),
  caption: 'A box owns no end, and every force of it is safe. A force runs $\\mathsf{thunk}(e) = \\lambda\\_.\\,e[!e]$, the body with the box put in for its self, so the box is in $V$ when that thunk is, in every later world and at every instance meeting $C$.'
});
block(s, {
  id: 'v-ex', title: 'Values of existential type', rocq: 'relation/Relation.v: Vbody (TEx), Vrel_ex_iff',
  tex: RULE('V-Ex', [[h('V-Ex.lb', R`l ${LEQ} ${HEADS}\,\Theta`), h('V-Ex.witness', R`W \vdash C[\bar x]`), R`v \in ${V('W', 'n', R`\Theta`, R`T[\bar x]`)}`]],
    R`v \in ${V('W', 'n', R`\Theta`, R`\exists^{l}\bar\iota.\,C.\,T`)}`),
  caption: 'An existential value is a value of the body at some witness points $\\bar x$ whose facts hold in $W$. Its lower bound lies at or below the partner points of its ends.'
});
block(s, {
  id: 'v-size', title: 'Recursion of V', rocq: 'relation/Relation.v: tsize, Vtop; relation/Sfix.v: sfix',
  tex: R`\begin{array}{l}
${h('rel.vsize', R`V_n \text{ by recursion on } (n, ${h('sr.size', R`\mathsf{size}`)}\,T) \text{ ordered lexicographically}`)} \\
${h('sr.size', R`\mathsf{size}(\Box(\forall\bar\iota\,\bar\alpha.\,C.\ \ast ${ARR}^{u} U)) = 3 + \mathsf{size}\,U`)} \qquad ${h('sr.size', R`\mathsf{size}(\ast ${ARR}^{u} U) = 2 + \mathsf{size}\,U`)}
\end{array}`,
  caption: '$V$ at level $n$ recurses on the size of the type inside the level, and the box clause stays inside the recursion.'
});

// E
block(s, {
  id: 'e-body', title: 'The term relation', rocq: 'relation/Relation.v: Ebody, Eind, Etop',
  tex: R`\begin{array}{l}
${h('E.zero', R`\forall e.\ e \in ${E('W', '0', R`\Theta`, 'T', 'F')}`)} \\
e \in ${E('W', R`n{+}1`, R`\Theta`, 'T', 'F')} \iff ${h('E.kripke', R`\forall W_1 ${EXT} W`)}. \\
\quad ${h('E.stop', R`(\mathsf{stop})\ ${h('sr.irred', R`\mathsf{irred}`)}\,e \Rightarrow e \in ${V('W_1', R`n{+}1`, R`\Theta`, 'T')}`)} \\
\quad ${h('E.ready', R`(\mathsf{ready})\ \neg\mathsf{irred}\,e \Rightarrow ${h('sr.ready', R`\mathsf{ready}_{W_1}(\Theta \mid F, e)`)}`)} \\
\quad ${h('E.step', R`(\mathsf{step})\ \forall \alpha, e'.\ e \xrightarrow{\alpha} e' \Rightarrow ${h('sr.obl', R`\mathsf{Obl}_\alpha(e')`)}`)} \qquad ${h('rel.lfp', R`\text{least fixpoint}`)}
\end{array}`,
  caption: 'A term in $E$ is a value in $V$ when irreducible, ready when reducible, and every step meets its obligation.'
});
block(s, {
  id: 'e-obl-admin', title: 'Obligations of internal steps', rocq: 'relation/Relation.v: o_beta, o_new, o_spawn, new_env',
  tex: R`\begin{array}{c}
${RULE('O-Beta', [[R`${AT(R`e'`)}\ \Theta`]], OB(R`\beta`))} \qquad ${RULE('O-Spawn', [[h('O-Spawn.split', R`\Theta = \Theta_M ${UPL} \Theta_r`), h('O-Spawn.thunk', R`v \in ${h('sr.vthunk', R`\mathsf{Vthunk}_n(\Theta_M)`)}`), R`${AT(R`e'`)}\ \Theta_r`]], OB(R`\mathsf{spawn}\,v`))} \\[2ex]
${RULE('O-New', [[h('O-New.cfresh', R`c^{\pm} \notin \mathrm{dom}\,\Theta`)], [R`${h('O-New.forall', R`\forall ${h('O-New.gfresh', R`a \notin A_W`)}`)}.\ ${h('O-New.grow', R`\exists S, \pi, C.\ \pi \in \{a, x\cdot\kappa\},\ \mathsf{strict}(W \oplus C)`)},\ ${AT(R`e'`)}_{W \oplus C}\ ${h('O-New.dual', R`\Theta[c^{+} \mapsto S@\pi,\ c^{-} \mapsto \overline{S}@\overline{\pi}]`)}`]], OB(R`\mathsf{new}\,c`))}
\end{array}`,
  caption: 'Each step $e \\xrightarrow{\\alpha} e\'$ of a term holding $\\Theta$ must meet the obligation $\\mathsf{Obl}_\\alpha(e\')$. A $\\beta$ step keeps the ends, a spawn gives the child exactly the ends its thunk mentions, and a creation adds the two new ends at a fresh root or a field and grows the world by their facts.'
});
block(s, {
  id: 'e-obl-msg', title: 'Obligations of send and receive', rocq: 'relation/Relation.v: o_send, o_recv',
  tex: R`\begin{array}{c}
${RULE('O-Send', [[HD(R`\Theta`, 'o', R`${SND('U')}.S`, 'x'), h('O-Send.split', R`\Theta \setminus o = \Theta_M ${UPL} \Theta_r`)], [h('O-Send.payload', R`w \in ${V('W', DL('n', R`n-\kappa_{give}`), R`\Theta_M`, PAY('U', 'x'))}`), R`${AT(R`e'`)}\ ${h('O-Send.shift', R`\Theta_r[o \mapsto S@x^{+}]`)}`]], OB(R`\mathsf{send}\,o\,w`))} \\[2ex]
${RULE('O-Recv', [[HD(R`\Theta`, 'o', R`${RCV('U')}.S`, 'x')], [R`${h('O-Recv.forall', R`\forall j, \Theta_{in}.\ ${LT('j', 'take')},\ \Theta_{in} \mathbin{\#} \Theta,\ w \in ${V('W', 'j', R`\Theta_{in}`, PAY('U', 'x'))}`)} \ \Longrightarrow\ ${h('O-Recv.level', R`e' \in ${E('W', 'j', R`\Theta[o \mapsto S@x^{+}] \cup \Theta_{in}`, 'T', 'F')}`)}`]], OB(R`\mathsf{recv}\,o\,w`))}
\end{array}`,
  caption: 'A send gives away exactly the ends of its payload, which must be a safe value, and keeps the rest. A receive does not know what arrives, so it must be safe for every incoming value at every lower level, with the new ends added.'
});
block(s, {
  id: 'e-obl-other', title: 'Obligations of close, choice and link', rocq: 'relation/Relation.v: o_close, o_select, o_branch, o_link',
  tex: R`\begin{array}{c}
${RULE('O-Close', [[HD(R`\Theta`, 'o', CLOSE, 'x'), R`${AT(R`e'`)}\ \Theta \setminus o`]], OB(R`\mathsf{close}\,o`))} \qquad ${RULE('O-Link', [[h('O-Link.distinct', R`o_1 \neq o_2`), h('O-Link.dual', R`\Theta(o_1) = S_1@x,\ \Theta(o_2) = S_2@\overline{x},\ ${SDUAL}\,S_1\,S_2`), R`${AT(R`e'`)}\ \Theta \setminus \{o_1, o_2\}`]], OB(R`\mathsf{link}\,o_1\,o_2`))} \\[2ex]
${RULE('O-Select', [[HD(R`\Theta`, 'o', h('sty.plus', R`\oplus(S_1,S_2)`), 'x'), R`${AT(R`e'`)}\ \Theta[o \mapsto S_i@${h('pt.sel', R`\overline{x\cdot\kappa_i}`)}]`]], OB(R`\mathsf{select}_i\,o`))} \qquad ${RULE('O-Branch', [[HD(R`\Theta`, 'o', h('sty.with', R`\&(S_1,S_2)`), 'x'), R`${AT(R`e'`)}\ \Theta[o \mapsto S_i@${h('pt.bra', R`x\cdot\kappa_i`)}]`]], OB(R`\mathsf{branch}_i\,o`))}
\end{array}`,
  caption: 'Close drops the end, a choice moves it to the field of the chosen branch, and a link drops two dual ends whose partners now talk to each other.'
});

// readiness
block(s, {
  id: 'rd-term', title: 'Readiness of a term', rocq: 'relation/Readiness.v: ready_t, below_rest, offered_t, stable_t, link_t',
  tex: R`\begin{array}{rcl}
${h('sr.ready', R`\mathsf{ready}_W(\Theta \mid F, t)`)} & \iff & ${h('rd.stable', R`\mathsf{stable}\,t`)} \Longrightarrow ${h('rd.value', R`\mathsf{done}`)} \land ${h('rd.below-rest', R`\mathsf{ordered}`)} \\[1ex]
${h('rd.value', R`\mathsf{done}`)} & \iff & ${h('rd.value', R`O = \varnothing \Rightarrow t \in \mathsf{Val}`)} \\
${h('rd.below-rest', R`\mathsf{ordered}`)} & \iff & ${h('rd.link', R`\mathsf{link}\,t`)} \lor {} ${h('rd.below-rest', R`\forall o \in O.\ ${h('rd.below-held', R`(\forall o' \in \mathrm{dom}\,\Theta \setminus O.\ W \vdash x_o \prec \overline{x_{o'}})`)} \land ${h('rd.below-future', R`(\forall y \in F.\ W \vdash x_o \prec y)`)}`)} \\[1ex]
 & & O = ${h('rd.offered', R`\mathsf{offered}_\Theta(t)`)},\ \text{the ends } t \text{ offers} \qquad x_o \text{ the point of } \Theta(o)
\end{array}`,
  caption: 'Readiness only matters when the term is stuck, $\\mathsf{stable}\\,t$, all it can do is offer actions to partners. Then it has finished if it offers nothing, and every end it offers lies below the partner point of every end it keeps and below every point of its future. In a strict order some stuck thread is then at the bottom and its partner can serve it.'
});
block(s, {
  id: 'rd-proc', title: 'Readiness of a process', rocq: 'relation/Readiness.v: ready_p, above_offered, stable_p, link_p, offered_p',
  tex: R`\begin{array}{rcl}
${h('sr.readyp', R`\mathsf{ready}_W(\Sigma, p)`)} & \iff & ${h('rd.p-stable', R`\mathsf{stable}\,p`)} \Longrightarrow ${h('rd.link', R`\mathsf{link}\,p`)} \lor (${h('rd.p-term', R`\mathsf{done}`)} \land ${h('rd.above-offered', R`\mathsf{covered}`)}) \\[1ex]
${h('rd.p-term', R`\mathsf{done}`)} & \iff & ${h('rd.p-term', R`O = \varnothing \Rightarrow ${h('prop.terminated', R`\mathsf{terminated}`)}\,p`)} \\
${h('rd.above-offered', R`\mathsf{covered}`)} & \iff & ${h('rd.above-offered', R`\forall o \in \mathrm{dom}\,\Sigma \setminus O.\ \exists o' \in O.\ W \vdash x_{o'} \prec \overline{x_o}`)} \\[1ex]
 & & O = ${h('rd.offered', R`\mathsf{offered}_\Sigma(p)`)},\ \text{the interface ends } p \text{ offers}
\end{array}`,
  caption: 'Only the interface ends have points, internal channels carry none. A stuck process sits at a link, or has finished if it offers nothing, and every interface end it keeps has an offered end below its partner point. For a closed process this is deadlock freedom itself.'
});

// P
block(s, {
  id: 'p-body', title: 'The process relation', rocq: 'relation/Relation.v: Pbody, Pclauses, Pind, Ptop',
  tex: R`\begin{array}{l}
p \in ${P('W', R`n{+}1`, R`\Sigma`, 'T')} \iff ${h('P.strict', R`\forall W_1 ${EXT} W.\ ${h('w.strict', R`\mathsf{strict}`)}\,W_1`)} \Rightarrow ${h('P.fuse', R`\forall h, D.\ ${h('sr.fuseok', R`\mathsf{fuse\_ok}`)}\,h\,D\,\Sigma\,p`)} \Rightarrow \text{at } p' = ${h('sr.pfuse', R`\mathsf{pfuse}`)}\,h\,D\,p,\ \Sigma' = ${h('sr.sdrop', R`\mathsf{sdrop}`)}\,D\,(h\,\Sigma) \\
\quad ${h('P-Stop', R`(\mathsf{stop})\ ${h('sr.pirred', R`\mathsf{pirred}`)}\,p' \Rightarrow p' = (\varnothing, \{v\} ${BIN('tp.msunion', R`\uplus`)} E) \land v \in ${V('W_1', R`n{+}1`, R`\Sigma'`, 'T')} \land E \subseteq \{\ast\}`)} \\
\quad ${h('P-Ready', R`(\mathsf{ready})\ \neg\mathsf{pirred}\,p' \Rightarrow ${h('sr.readyp', R`\mathsf{ready}_{W_1}(\Sigma', p')`)}`)} \\
\quad ${h('P-Step', R`(\mathsf{step})\ ${h('proc.erase', R`\mathsf{erase}`)}\,q = p' \land q \xrightarrow{ev} q' \Rightarrow ${h('sr.pobl', R`\mathsf{Pobl}_{ev}(\mathsf{erase}\,q')`)}`)} \qquad ${h('rel.lfp', R`\text{least fixpoint}`)}
\end{array}`,
  caption: 'A process meets the three clauses of a term, stop, ready and step, in every strict later world and after every admissible fusion of its held ends. Composition fuses ends, so the relation is closed under it from the start.'
});
block(s, {
  id: 'p-fuse', title: 'Fusions of held ends', rocq: 'relation/Relation.v: fuse_ok, pheld, pfuse, sdrop, dpairs, gch',
  tex: R`\begin{array}{rcll}
${h('sr.fuseok', R`\mathsf{fuse\_ok}\,h\,D\,\Sigma\,(C, E)`)} & \iff & ${h('fuse.dcomm', R`\forall o.\ h(\overline{o}) = \overline{h(o)}`)} & \text{respects duality} \\
 & \land & ${h('fuse.inj', R`h(o_1) = h(o_2) \Rightarrow o_1 = o_2`)} & \text{injective, } o_1, o_2 \in \mathsf{held} \\
 & \land & ${h('fuse.partners', R`h(o_2) = \overline{h(o_1)} \Rightarrow o_2 = \overline{o_1} \lor ${ECH}(h\,o_1) \in D`)} & \text{new pairs restricted, } o_1, o_2 \in \mathsf{held} \\
 & \land & ${h('fuse.D', R`D \cap ${h('sr.gch', R`\mathsf{gch}_h`)}[C] = \varnothing`)} \land ${h('fuse.dpairs', R`\mathsf{dpairs}\,D\,(h\,\Sigma)`)} & D \text{ fresh and dual} \\[1ex]
${h('sr.held', R`\mathsf{held}`)} & = & ${h('sr.held', R`\{o \mid o \in \mathrm{dom}\,\Sigma \lor ${ECH}\,o \in C\}`)} \\
${h('sr.gch', R`\mathsf{gch}_h(c)`)} & = & ${h('sr.gch', R`${ECH}(h(c^{+}))`)} \\
${h('sr.sdrop', R`\mathsf{sdrop}\,D\,\Sigma`)} & = & ${h('sr.sdrop', R`\{o \mapsto y \in \Sigma \mid ${ECH}\,o \notin D\}`)} \\
${h('sr.pfuse', R`\mathsf{pfuse}\,h\,D\,(C, E)`)} & = & ${h('sr.pfuse', R`(\mathsf{gch}_h[C] \cup D,\ h[E])`)} \\
${h('fuse.dpairs', R`\mathsf{dpairs}\,D\,\Sigma`)} & \iff & ${h('fuse.dpairs', R`${ECH}\,o \in D \Rightarrow \Sigma(o) = S@x \land \Sigma(\overline{o}) = S'@\overline{x} \land ${SDUAL}\,S\,S'`)}
\end{array}`,
  caption: 'An admissible fusion $(h, D)$ renames held ends injectively up to the new pairs it restricts as $D$.'
});
block(s, {
  id: 'p-obl', title: 'Obligations of process steps', rocq: 'relation/Relation.v: q_tau, q_send, q_recv, q_close, q_select, q_branch, q_link',
  tex: R`\begin{array}{c}
${RULE('Q-Tau', [[R`C' \cap ${h('tp.chans', R`\mathsf{chans}`)}\,\Sigma = \varnothing`, R`${AT(R`p'`)}\ \Sigma \text{ after cost } ${h('ct.sync', DL(R`${h('ct.DF', R`\kappa_{DF}`)}(ev)`, R`${h('ct.table', R`\kappa`)}(ev)`))}`]], PB('ev'))} \\[2ex]
${RULE('Q-Send', [[HD(R`\Sigma`, 'o', R`${SND('U')}.S`, 'x'), R`\Sigma \setminus o = \Sigma_v ${UPL} \Sigma_r`], [h('Q-Send.theta-e', R`\mathrm{dom}\,\Theta_e = \{o' \in ${FENDS}(w) \mid ${ECH}(o') \in C\}`), h('Q-Send.split', R`\mathsf{send\_split}\,\Sigma\,\Sigma_e\,\Theta_e`)], [R`w \in ${V('W', DL('n', R`n-\kappa_{give}`), R`\Sigma_v \cup \Theta_e`, PAY('U', 'x'))}`, R`${AT(R`p'`)}\ (\Sigma_r \cup ${h('Q-Send.sigma-e', R`\Sigma_e`)})[o \mapsto S@x^{+}]`]], PB(R`\mathsf{send}\,o\,w`))} \\[2ex]
${RULE('Q-Recv', [[HD(R`\Sigma`, 'o', R`${RCV('U')}.S`, 'x')], [R`\forall j, \Theta_2.\ ${LT('j', 'take')},\ ${ECH}[\mathrm{dom}\,\Theta_2] \cap C = \varnothing,\ ${h('Q-Recv.ok', R`\mathsf{recv\_ok}\,\Sigma'\,\Theta_2`)},\ w \in ${V('W', 'j', R`\Theta_2`, PAY('U', 'x'))}`], [R`\Longrightarrow\ (C' \cup ${h('Q-Recv.back', R`\mathsf{recv\_back}\,\Sigma'\,\Theta_2`)}, E') \in ${P('W', 'j', h('Q-Recv.env', R`\mathsf{recv\_env}\,\Sigma'\,\Theta_2`), 'T')}`]], PB(R`\mathsf{recv}\,o\,w`))} \\[2ex]
${h('Q-Link', R`\textsf{Q-Close, Q-Select, Q-Branch, Q-Link}\ \text{are the term obligations with } \Sigma \text{ for } \Theta \text{ and } P \text{ for } E`)} \\
p = (C, E),\ p' = (C', E'),\ \Sigma' = \Sigma[o \mapsto S@x^{+}]
\end{array}`,
  caption: 'Internal steps, including messages between two threads inside $p$, keep the interface. A message with the outside moves ends across it. A send gives away the payload ends, those of internal channels $\\Theta_e$ included, and a receive must be safe for every incoming value at every lower level.'
});
block(s, {
  id: 'p-msg', title: 'Interfaces after a message', rocq: 'relation/Relation.v: send_split, recv_ok, recv_back, recv_env',
  tex: R`\begin{array}{l}
${h('Q-Send.split', R`\mathsf{send\_split}\,\Sigma\,\Sigma_e\,\Theta_e`)} \iff (\forall o \in \mathrm{dom}\,\Theta_e.\ o, \overline{o} \notin \mathrm{dom}\,\Sigma) \land {} \\
\quad (\forall o.\ o \in \mathrm{dom}\,\Sigma_e \iff \overline{o} \in \mathrm{dom}\,\Theta_e \land o \notin \mathrm{dom}\,\Theta_e) \land {} \\
\quad (\forall o.\ \Theta_e(o) = S@y \Rightarrow \exists S'.\ (\Sigma_e \cup \Theta_e)(\overline{o}) = S'@\overline{y} \land ${SDUAL}\,S\,S') \\
${h('Q-Recv.ok', R`\mathsf{recv\_ok}\,\Sigma\,\Theta_2`)} \iff (\forall o \in \mathrm{dom}\,\Theta_2.\ o \notin \mathrm{dom}\,\Sigma) \land {} \\
\quad (\forall o.\ \Theta_2(o) = S@y \land (\Sigma \cup \Theta_2)(\overline{o}) = S'@y' \Rightarrow y' = \overline{y} \land ${SDUAL}\,S\,S') \\
${h('Q-Recv.back', R`\mathsf{recv\_back}\,\Sigma\,\Theta_2 = ${ECH}[\{o \in \mathrm{dom}\,\Theta_2 \mid \overline{o} \in \mathrm{dom}\,\Sigma \cup \mathrm{dom}\,\Theta_2\}]`)} \\
${h('Q-Recv.env', R`\mathsf{recv\_env}\,\Sigma\,\Theta_2 = \{o \mapsto y \in \Sigma \mid \overline{o} \notin \mathrm{dom}\,\Theta_2\} \cup {}`)} \\
\quad ${h('Q-Recv.env', R`\{o \mapsto y \in \Theta_2 \mid \overline{o} \notin \mathrm{dom}\,\Sigma \cup \mathrm{dom}\,\Theta_2\}`)}
\end{array}`,
  caption: 'The side conditions that move ends across the interface at an external send and receive.'
});

// semantic judgments
const SJ = (rel, k) => R`\begin{array}{l}
${h('sj.at', R`\Delta ${REL('sj.term', rel)}^{X}_W e : T \iff \forall n, W' ${EXT} W, \Theta', \gamma.\ ${h('sr.tenv-erase', R`|\Delta|`)} \mathbin{\#} \Theta' \land {}`)} \\
\quad ${h('sj.at', R`${h('sj.grel', R`\gamma \in G${k}^{W'}_n\llbracket\Theta' \vdash \Delta\rrbracket`)} \Rightarrow \gamma(e) \in ${h('th.Erel', R`E${k}^{W'}_n\llbracket |\Delta| \cup \Theta' \vdash T\rrbracket^{X}`)}`)} \\
${h('sj.term', R`\Delta ${rel}^{F}_W e : T \iff \forall \rho, B.\ \Delta ${rel}^{${h('sj.den', R`\mathsf{den}_{\rho,B}(F)`)}}_W e : T`)} \\
${h('sj.proc', R`\Sigma ${rel}_W p : T \iff \forall n.\ p \in ${h('th.Prel', R`P${k}^{W}_n\llbracket\Sigma \vdash T\rrbracket`)}`)}
\end{array}`;
block(s, {
  id: 'sj', title: 'Semantic judgments', rocq: 'compat/SemTyped.v: Grel, sem_typed_at, sf_den, sem_typed; relation/Adequacy.v: sem_ptyped',
  tex: SJ(R`\vDash[\kappa]`, R`[\kappa]`),
  variants: { df: SJ(R`\vDash`, '') },
  caption: 'The semantic judgments quantify over every level, later world and grounding, and read the static future at every denotation.'
});

// fuel
// the successor has fuel at level j with the listed components changed, the others as before
const FN = (j, upd) => h('fu.upd', upd ? R`e' \in F_{${j}}[${upd}]` : R`e' \in F_{${j}}`);
const UNFO = (o) => R`${UNF}(\Pi\,${o})`;
block(s, {
  id: 'fu-def', title: 'Fuel', rocq: 'fuel/Fuel.v: Fdef, FuelE, FLev',
  modes: ['lf'],
  tex: R`\begin{array}{c}
${RULE('F-Run', [[h('fu.refill-kripke', R`\forall N' ${RLE} N`), h('fu.rename', R`\forall g \text{ injective on } \mathrm{dom}\,\Pi`)], [h('fu.val', R`g(e) \in \mathsf{Val} \Rightarrow r \leq tk \land g(e) \in ${FV("N'", R`n{+}1`, R`\sigma`, R`g\Pi, g\varphi`)}`)], [h('fu.step', R`g(e) \xrightarrow{\alpha} e' \Rightarrow ${h('sr.fobl', R`\mathsf{Fobl}^{N'}_{\alpha}(e')`)}`)]], R`e \in ${FE('N', R`n{+}1`, R`${h('fu.rty', R`\sigma`)} \triangleright ${h('fu.frame', 'd')} ; ${h('fu.reserve', 'r')}`, R`${h('fu.Pi', R`\Pi`)}, ${h('fu.phi', R`\varphi`)}, ${h('fu.tk', 'tk')}`)}`)}
\qquad ${h('fu.zero', R`e \in ${FE('N', '0', R`\sigma \triangleright d ; r`, R`\Pi, \varphi, tk`)}`)} \\[6pt]
${h('fu.upd', R`F_n[x := v]`)} = F^{N'}_{n}\llbracket \sigma \triangleright d ; r \rrbracket(\Pi, \varphi, tk) \text{ with the component } x \text{ replaced by } v \qquad ${h('fu.oneclock', R`\text{every step costs one level}`)}
\end{array}`,
  caption: 'A thread $e$ holds ends with protocols $\\Pi$ and counters $\\varphi$, and $tk$ link tickets. It returns at $\\sigma$ after at most $d$ actions with $r$ tickets left. At level $n+1$ it returns a fueled value or every step meets its fuel obligation at level $n$. Fuel reads no point, no world and no relation.'
});
block(s, {
  id: 'fu-act', title: 'An action', rocq: 'fuel/Fuel.v: f_act, fspare, idle_at, refill, ftick',
  modes: ['lf'],
  tex: R`\begin{array}{rcll}
${ACT}\,o & \iff & ${h('F-Wait', R`o \in \mathrm{dom}\,\varphi \land \neg ${h('fu.idle', R`\mathsf{idle}`)}(\Pi\,o)`)} & \text{F-Wait} \\
 & \land & ${h('F-Tick', R`${FSPARE}\,\Pi\,\varphi\,(\mathrm{dom}\,\varphi \setminus \{o\})`)} \land ${h('F-Tick.frame', R`1 \leq d`)} & \text{F-Tick} \\[4pt]
${FSPARE}\,\Pi\,\varphi\,X & \iff & ${h('fu.fspare', R`\forall o' \in X.\ \neg\mathsf{idle}(\Pi\,o') \Rightarrow 1 \leq \varphi(o')`)} \\
${REFILL}\,N\,o\,\varphi & = & ${h('fu.refillop', R`(\varphi \setminus o) ${DM} 1\ [o \mapsto N]`)} \\
${FHAND}\,M\,\varphi & = & ${h('fu.fhand', R`(\varphi|_M) ${DM} 1`)} \\
\mathsf{idle}\,S & \iff & ${UNF}\,S = ${h('sty.skip', R`\mathsf{Skip}`)}
\end{array}`,
  caption: 'An action on $o$ asks $o$ held and not idle, and a unit to spare on every other live end and on the frame. Afterwards $o$ refills to $N$ and every other counter drops by one. Ends handed to another thread arrive one lower.'
});
block(s, {
  id: 'fu-obl-int', title: 'Fuel obligations of internal steps', rocq: 'fuel/Fuel.v: f_beta, f_new, f_spawn, f_link, plink',
  modes: ['lf'],
  tex: R`\begin{array}{c}
${RULE('F-Beta', [[FN('n')]], R`${h('F-Beta', R`\mathsf{Fobl}_{\beta}(e')`)}`)} \qquad
${RULE('F-New', [[R`${h('F-New.fresh', R`c^{\pm} \notin \mathrm{dom}\,\varphi`)} \Rightarrow \exists S.\ ${FN('n', R`\Pi := \Pi[c^{+} \mapsto S, c^{-} \mapsto \overline{S}],\ ${h('F-New.cnew', R`\varphi := \varphi[c^{\pm} \mapsto N]`)}`)}`]], R`${h('F-New', R`\mathsf{Fobl}_{\mathsf{new}\,c}(e')`)}`)} \\[10pt]
${RULE('F-Spawn', [[R`M = ${FENDS}(v)`, h('F-Spawn.held', R`M \subseteq \mathrm{dom}\,\varphi`), R`${FSPARE}\,\Pi\,\varphi\,M`], [h('F-Spawn.child', R`v\,\ast \in ${FE('N', 'n', R`${THR} \triangleright \infty ; 0`, R`\Pi|_M,\ ${FHAND}\,M\,\varphi,\ \lceil tk/2 \rceil`)}`)], [FN('n', R`\Pi := \Pi \setminus M,\ \varphi := \varphi \setminus M,\ ${h('F-Spawn.tickets', R`tk := \lfloor tk/2 \rfloor`)}`)]], R`${h('F-Spawn', R`\mathsf{Fobl}_{\mathsf{spawn}\,v}(e')`)}`)} \\[10pt]
${RULE('F-Link', [[h('F-Link.plink', R`o_1 \neq o_2 \land \Pi(o_2) ${SEQU} \overline{\Pi(o_1)}`), R`o_1, o_2 \in \mathrm{dom}\,\varphi`, h('F-Link.ticket', R`1 \leq tk`)], [FN('n', R`\Pi := \Pi \setminus \{o_1,o_2\},\ \varphi := \varphi \setminus \{o_1,o_2\},\ tk := tk - 1`)]], R`${h('F-Link', R`\mathsf{Fobl}_{\mathsf{link}\,o_1\,o_2}(e')`)}`)}
\end{array}`,
  caption: 'Internal steps tick no counter. A new channel starts both ends at $N$. A spawn hands the ends of the thunk to the child one lower, with half the tickets. A link drops two dual ends and spends one ticket.'
});
block(s, {
  id: 'fu-obl', title: 'Fuel obligations of actions', rocq: 'fuel/Fuel.v: f_send, f_recv, f_close, f_select, f_branch',
  modes: ['lf'],
  tex: R`\begin{array}{c}
${RULE('F-Send', [[R`${ACT}\,o`, R`${UNFO('o')} = ${SND('T')}.S`, R`M = ${FENDS}(w)`, h('F-Send.notsubj', R`M \subseteq \mathrm{dom}\,\varphi \setminus \{o\}`), R`${FSPARE}\,\Pi\,\varphi\,M`], [h('F-Send.payload', R`w \in ${FV('N', 'n', 'T', R`\Pi|_M,\ ${FHAND}\,M\,\varphi`)}`)], [FN('n', R`d := d ${DM} 1,\ \Pi := (\Pi \setminus M)[o \mapsto S],\ \varphi := ${REFILL}\,N\,o\,(\varphi \setminus M)`)]], R`${h('F-Send', R`\mathsf{Fobl}_{\mathsf{send}\,o\,w}(e')`)}`)} \\[10pt]
${RULE('F-Recv', [[R`${ACT}\,o`, R`${UNFO('o')} = ${RCV('T')}.S`], [h('F-Recv.forall', R`\forall j \leq n,\ \Pi_i, \varphi_i \text{ disjoint}.\ w \in ${FV('N', 'j', 'T', R`\Pi_i, \varphi_i`)}`) + R` \Rightarrow ${FN('j', R`d := d ${DM} 1,\ \Pi := \Pi[o \mapsto S] \cup \Pi_i,\ \varphi := ${REFILL}\,N\,o\,\varphi \cup \varphi_i`)}`]], R`${h('F-Recv', R`\mathsf{Fobl}_{\mathsf{recv}\,o\,w}(e')`)}`)} \\[10pt]
${RULE('F-Close', [[R`${ACT}\,o`, R`${UNFO('o')} = ${CLOSE}`], [FN('n', R`d := d ${DM} 1,\ \Pi := \Pi \setminus o,\ \varphi := (\varphi \setminus o) ${DM} 1`)]], R`${h('F-Close', R`\mathsf{Fobl}_{\mathsf{close}\,o}(e')`)}`)} \qquad
${RULE('F-Choice', [[R`${ACT}\,o`, R`${UNFO('o')} \in \{\oplus(S_1,S_2), \&(S_1,S_2)\}`], [FN('n', R`d := d ${DM} 1,\ \Pi := \Pi[o \mapsto S_i],\ \varphi := ${REFILL}\,N\,o\,\varphi`)]], R`${h('F-Close', R`\mathsf{Fobl}_{\mathsf{sel}_i\,o}(e'),\ \mathsf{Fobl}_{\mathsf{bra}_i\,o}(e')`)}`)}
\end{array}`,
  caption: 'Every action spends one unit of the frame, advances the protocol of $o$, refills $o$ and ticks the other ends. A send also hands its payload ends on one lower, and a receive continues for every fueled value that may arrive.'
});
block(s, {
  id: 'fv', title: 'Fueled values', rocq: 'fuel/Fuel.v: Vty, Vres',
  modes: ['lf'],
  tex: R`\begin{array}{c}
${RULE('FV-Sess', [[R`\Pi = \{o \mapsto S'\}`, R`\varphi = \{o \mapsto f\}`, R`S' ${SEQU} S`, h('FV-Sess.counter', R`a \leq f`)]], h('FV-Sess', R`o \in FV\llbracket (S@x)^{a}\rrbracket(\Pi, \varphi)`))} \qquad
${RULE('FV-Thread', [[R`\Pi = \varphi = \varnothing`]], h('FV-Thread', R`v \in FV\llbracket ${THR} \rrbracket(\Pi,\varphi)`))} \\[10pt]
${RULE('FV-Arrow', [[h('FV-Arrow.exact', R`${FENDS}\,e = \mathrm{dom}\,\Pi = \mathrm{dom}\,\varphi`), h('FV-Arrow.floor', R`\forall o.\ h + a \leq \varphi(o)`)], [R`\forall N' ${RLE} N,\ j < n,\ \varphi' \geq h \text{ on } \mathrm{dom}\,\varphi,\ u \in ${FV("N'", 'j', 'T', R`\Pi_u, \varphi_u`)},\ ${MEETS}\,\vartheta\,r\,tk`], [h('FV-Arrow.body', R`e[u] \in ${FE("N'", 'j', R`U \triangleright c ; r`, R`\Pi \cup \Pi_u, \varphi' \cup \varphi_u, tk`)}`)]], h('FV-Arrow', R`\lambda e \in FV^N_n\llbracket (T ${ARR}[(c,\vartheta);h]\, U)^{a}\rrbracket(\Pi,\varphi)`))} \\[10pt]
${RULE('FV-Box', [[h('FV-Box.noends', R`${FENDS}\,e = \varnothing`)], [R`\forall N' ${RLE} N,\ j < n,\ \bar s \in ${h('tp.sinsts', R`\mathsf{sinsts}`)}\,N',\ ${MEETS}\,\vartheta\,r\,tk`], [h('FV-Box.body', R`e[!e] \in ${FE("N'", 'j', R`U[\bar s] \triangleright c ; r`, R`\varnothing,\varnothing,tk`)}`)]], h('FV-Box', R`!e \in FV^N_n\llbracket \Box(\ldots (c,\vartheta) \ldots U)\rrbracket(\varnothing,\varnothing)`))} \\[6pt]
${h('sr.fvagg', R`\otimes, \oplus, \exists \text{ split } \Pi, \varphi \text{ among their parts}`)}
\end{array}`,
  caption: 'Fueled values by recursion on the type. An end has at least its credit. A closure keeps its captured counters at the floor $h$ plus its credit, and its body has fuel at every call. A box holds nothing and its body has fuel at every force. Points are never read.'
});
block(s, {
  id: 'fu-fsem', title: 'Fuel of a thread', rocq: 'fuel/Fuel.v: fsem; cost/CostSem.v: csem',
  modes: ['lf'],
  tex: R`\begin{array}{l}
${h('fu.fsem', R`\mathsf{fsem}\,N\,\Pi\,e \iff \exists tk.\ \forall n.\ e \in ${FE('N', 'n', R`${THR} \triangleright \infty ; 0`, R`\Pi, (\lambda\_.N)|_{\mathrm{dom}\,\Pi}, tk`)}`)} \\
${h('cs.csem', R`\Delta \vDash^{N} e : T\ !\ \varepsilon`)}
\end{array}`,
  caption: 'A thread has fuel at every level with every held end at $N$ and one ticket count for all levels.'
});

// soup
block(s, {
  id: 'sp-state', title: 'Soup states', rocq: 'soup/State.v: hold, lfstate',
  modes: ['lf'],
  tex: R`\begin{array}{c}
${h('sp.state', R`a = (q, K, tk)`)} \qquad ${h('sp.hold', R`K : \mathsf{End} \rightharpoonup \mathbb{N} \times \mathsf{Point} \times (\mathbb{N} \cup \{\infty\})`)} \qquad ${h('sp.tk', R`tk : \mathbb{N} \to \mathbb{N}`)} \\
${h('sp.next', R`\mathsf{lf\_next}\,N\,(q, K, tk)\,ev\,q' = (q',\ \mathsf{own\_next}\,N\,ev\,K,\ \mathsf{tk\_next}\,ev\,tk)`)}
\end{array}`,
  caption: 'A soup state is a configuration with an ownership map from held ends to holder, point and counter, and a ticket count per thread.'
});
block(s, {
  id: 'sp-inv', title: 'The soup', rocq: 'soup/State.v: soup_gen, soup/Soup.v: soup_inv, Soup',
  modes: ['lf'],
  tex: R`\begin{array}{ll}
a \in ${h('th.soup', R`S^{N,W}_n\llbracket\Sigma \vdash T\rrbracket`)} \iff ${h('sp.exists', R`\exists A, \Pi, U`)}.\ ${h('sp.prim', R`${h('ty.prim', R`\mathsf{prim}`)}\,T`)} \land \text{for every thread } q(t) = e & \\[1ex]
\quad ${h('sp.rel', R`e \in ${h('th.Erel', R`E[\kappa_L]^W_n\llbracket K_t(A) \vdash U_t\rrbracket^{\varnothing}`)}`)} \land ${h('sp.ty', R`U_t \in \{T, \ast\}`)} & \text{live} \\
\quad ${h('sp.fuel', R`e \in ${FE('N', 'n', R`${THR} \triangleright \infty ; 0`, R`K_t(\Pi), ${h('sr.ctrs', R`\mathsf{ctrs}`)}\,K\,t, tk_t`)}`)} & \text{fueled} \\[1ex]
\text{and for every end } o & \\[1ex]
\quad ${h('sp.pts', R`\mathsf{pt}(A\,o) = \mathsf{pt}(K\,o)`)} \land ${h('sp.dom', R`\mathrm{dom}\,\Pi = \mathrm{dom}\,K`)} \land ${h('sp.owner', R`K(o) = (t, \_, \_) \Rightarrow t \in \mathrm{dom}\,q`)} & \text{one owner} \\
\quad ${h('sp.closed', R`o \in \mathrm{dom}\,K \Rightarrow ${ECH}\,o \in C \lor o \in \mathrm{dom}\,\Sigma`)} \land ${h('sp.pair', R`o \in \mathrm{dom}\,K \land ${ECH}\,o \in C \Rightarrow \overline{o} \in \mathrm{dom}\,K`)} & \text{closed} \\
\quad ${h('sp.sdual', R`${ECH}\,o \in C \land A(o) = S@x \land A(\overline{o}) = S'@x' \Rightarrow x' = \overline{x} \land ${SDUAL}\,S\,S'`)} & \text{dual} \\
\quad ${h('sp.pdual', R`${ECH}\,o \in C \land \Pi(o) = P \land \Pi(\overline{o}) = P' \Rightarrow P' ${SEQU} \overline{P}`)} & \\
\quad ${h('sp.sig', R`\Sigma(o) = y \Rightarrow A(o) = y`)} \land ${h('sp.psig', R`\Sigma(o) = S@x \Rightarrow \Pi(o) = S`)} \land ${h('sp.fin', R`K(o) = (\_, \_, f) \Rightarrow f \in \mathbb{N}`)} & \text{interface}
\end{array}`,
  caption: 'At each level $n$ the soup asks every thread live and fueled at its part of $A$ and $\\Pi$, with ends, points and counters read from $K$.'
});
block(s, {
  id: 'sp-lf', title: 'Lock-free semantic judgment', rocq: 'soup/Soup.v: lf_sem, lf_next, own_next, tk_next',
  modes: ['lf'],
  tex: R`\begin{array}{l}
${h('sp.lfsem', R`\Sigma \Vvdash_W p : T \iff ${h('sp.exists-before-forall', R`\exists N \in \mathbb{N}, a.\ ${h('proc.erase', R`\mathsf{erase}`)}(${h('th.qa', 'q_a')}) = p \land \forall n`)}.\ a \in ${h('th.soup', R`S^{N,W}_n\llbracket\Sigma \vdash T\rrbracket`)}`)}
\end{array}`,
  caption: 'The lock-free semantic judgment fixes the refill and the soup state once, before the level.'
});

// ---- notes ----
// cost tables
n('ct.table', R`Cost table $\kappa$`, R`A sextuple $\kappa \in \mathbb{N}^6$ of costs, one per kind of step.`, R`One relation parametric in $\kappa$ yields both the deadlock-freedom and the liveness relation, so every compatibility proof is done once for all $\kappa$.`, DEF, R`$\kappa_{DF} = (1,1,1,0,0,1)$.`, 'relation/CostTable.v: ctable');
n('ct.take-pos', R`$1 \leq \kappa_{take}$`, R`Receive and branch cost at least one level.`, R`A receive reads $V$ of its payload negatively at the level of its continuation, so that level is $j < n$ and $V_n$ is well defined.`, R`With $\kappa_{take} = 0$, $V_n$ would quantify negatively over $V_n$ and the fixpoint would not exist.`, R`Both tables have $\kappa_{take} = 1$.`, 'relation/CostTable.v: c_take_pos');
n('ct.give-pos', R`$\kappa_\beta = 0 \Rightarrow 1 \leq \kappa_{give}$`, R`If $\beta$ is free, a give costs at least one level.`, R`For $\kappa_\beta = 0$, $V_n$ and $E_n$ are defined together by recursion on the size of the type, and a free send would read $V_n$ at a payload type of any size.`, DEF, R`$\kappa_L$ has $\kappa_\beta = 0$ and $\kappa_{give} = 1$.`, 'relation/CostTable.v: c_give_pos');
n('ct.give-take', R`$\kappa_{give} \leq \kappa_{take}$`, R`A give costs at most a take.`, R`A synchronization costs $\kappa_{give} + \kappa_{take}$, and composing two components pays a synchronization of two gives, which needs $2\kappa_{give} \leq \kappa_{give} + \kappa_{take}$.`, DEF, R`$\kappa_{DF}$ has $0 \leq 1$ and $\kappa_L$ has $1 \leq 1$.`, 'relation/CostTable.v: c_give_take');
n('ct.DF', R`$\kappa_{DF}$, the step index`, R`The table $(1,1,1,0,0,1)$. It is the ordinary step index of a logical relation. Almost every step costs one level, and only a send, select, close or link costs none.`, R`A step index lets $V$ and $E$ refer to themselves at lower levels, which recursion and received closures need. The four free steps each shrink the term, so the successor can be checked at the same level by recursion on the term, and a send can hand its payload over at the level of the continuation.`, DEF, R`$\beta$ and $\mathsf{recv}$ cost one level, $\mathsf{send}$ costs none.`, 'relation/CostTable.v: κ_DF');
n('ct.L', R`$\kappa_L$, the live table`, R`The table $(0,0,0,0,1,1)$. Internal steps, $\beta$, $\mathsf{new}$, $\mathsf{spawn}$ and $\mathsf{link}$, cost nothing, and only session actions cost a level.`, R`A free step is checked inside the least fixpoint of the current level, and a least fixpoint admits only finitely many steps in a row. So a term in the relation at $\kappa_L$ cannot take infinitely many internal steps without an action, which is absence of internal divergence. Lock freedom needs it, because a thread that loops internally never serves its partner. It is not about paying for messages.`, R`$!(f = \\mathsf{force}\\,f)$ steps by $\\beta$ forever and is in no level at $\\kappa_L$, while it is in every level at $\\kappa_{DF}$.`, R`Under $\kappa_L$ a synchronization costs $2$, one level for each side.`, 'relation/CostTable.v: κ_L');
n('ct.beta', R`Cost $\kappa_\beta$`, R`The cost of application, pair and unit elimination, case and force.`, R`An arrow reads its body at every $j < n$ under $\kappa_{DF}$. \annp{Under a general table it reads every $j$ with $j + \kappa_\beta \leq n$, so one arrow clause also serves $j \leq n$ for $\kappa_L$.}`, DEF, R`$(\lambda e)\,v \xrightarrow{\beta} e[v]$ costs $\kappa_\beta$.`, 'relation/CostTable.v: c_beta');
n('ct.new', R`Cost $\kappa_{new}$`, R`The cost of $\mathsf{new}$.`, R`Creation synchronizes with nobody, so $\kappa_L$ counts it as an internal step.`, DEF, R`$\kappa_L(\mathsf{new}) = 0$.`, 'relation/CostTable.v: c_new');
n('ct.spawn', R`Cost $\kappa_{spawn}$`, R`The cost of $\mathsf{spawn}$.`, R`For $\kappa_{spawn} = 0$ the child thunk is read inside the least fixpoint of the parent, so an infinite chain of spawns is in no $E_n$.`, DEF, R`$\kappa_L(\mathsf{spawn}) = 0$.`, 'relation/CostTable.v: c_spawn');
n('ct.link', R`Cost $\kappa_{link}$`, R`The cost of $\mathsf{link}$, $0$ in both tables.`, R`A link acts alone and synchronizes with nobody, so it is an internal step.`, R`Under $\kappa_L$ a loop that creates and links forever is an infinite sequence of internal steps and lies in no $E_n$.`, R`$!(f = \mathsf{let}\ \langle a, b\rangle = \mathsf{new}\ \mathsf{in}\ \mathsf{let}\ \ast = \mathsf{link}\,\langle a, b\rangle\ \mathsf{in}\ \mathsf{force}\,f)$ diverges internally.`, 'relation/CostTable.v: c_link');
n('ct.give', R`Cost $\kappa_{give}$`, R`The cost of $\mathsf{send}$, $\mathsf{select}$ and $\mathsf{close}$.`, R`The obligation of a give reads the continuation at level $n - \kappa_{give}$.`, DEF, R`$\kappa_{DF}(\mathsf{send}) = 0$.`, 'relation/CostTable.v: c_give');
n('ct.takek', R`Cost $\kappa_{take}$`, R`The cost of $\mathsf{recv}$ and $\mathsf{branch}$, $1$ in both tables.`, R`The obligation of a take reads every incoming value at $j \leq n - \kappa_{take} < n$.`, DEF, R`$\kappa(\mathsf{recv}) = 1$.`, 'relation/CostTable.v: c_take');
n('ct.sync', R`Cost of an event $\kappa(ev)$`, R`$\kappa(ev)$ is the cost of the step kind of $ev$, and $\kappa_{give} + \kappa_{take}$ for a synchronization.`, R`Both partners of a synchronization step at once, so the process pays both costs.`, DEF, R`A message costs $1$ under $\kappa_{DF}$\annp{ and $2$ under $\kappa_L$}.`, 'relation/CostTable.v: ev_cost');
n('rel.atcost', R`$e'$ at $\Theta'$`, R`The successor of a step of cost $c$ at level $n$ is read in the fixpoint $X$ if $c = 0$ and in $E_{n-c}$ if $c > 0$.`, R`Stated as two implications, $X$ occurs strictly positively and the inductive definition is admissible.`, DEF, R`Under $\kappa_L$ a $\beta$ step stays at level $n$.`, 'relation/Relation.v: at_cost_E, at_cost_V, at_cost_P');
n('rel.lfp', R`Least fixpoint $X$`, R`$E_n$ and $P_n$ are the least fixpoints of their clauses over steps of cost $0$.`, R`A least fixpoint admits only finite sequences of cost-$0$ steps, so under $\kappa_L$ no term in $E_n$ diverges internally.`, R`A greatest fixpoint would admit $!(f = \mathsf{force}\,f)$, which takes only $\beta$ steps.`, R`Induction on $E_n$ is induction on cost-$0$ steps.`, 'relation/Relation.v: Eind, Pind');
// V
n('V-Unit', R`$V$ at $\ast$`, R`$v \in V\llbracket\Theta \vdash \ast\rrbracket \iff \Theta = \varnothing \land v = \ast$.`, R`A finished thread has result type $T$ or $\ast$, and $\Theta = \varnothing$ shows that a thread holding a value of type $\ast$ holds no end.`, R`Without $\Theta = \varnothing$, a thread could end as $\ast$ while owning an end that its partner waits on forever.`, R`$\ast \in V\llbracket\varnothing \vdash \ast\rrbracket$.`, 'relation/Relation.v: Vbody TUnit');
n('V-Sess', R`$V$ at $S@x$`, R`$v \in V\llbracket\Theta \vdash S@x\rrbracket \iff \exists o, S'.\ v = o \land \Theta = \{o \mapsto S'@x\} \land S' \approx S$.`, R`$\Theta$ keeps its annotations for the fuel layer, and $V$ compares session types erased.`, DEF, R`$c^{+} \in V\llbracket\{c^{+} \mapsto S'@\rho\} \vdash S@\rho\rrbracket$ for $S' \approx S$.`, 'relation/Relation.v: Vbody TSess');
n('V-Sess.exact', R`$\Theta = \{o \mapsto S'@x\}$`, R`The environment of an end value is the singleton of its own entry at the point $x$ of the type.`, R`Exact environments make $\mathrm{dom}\,\Theta = \mathsf{fends}(v)$ for every $v \in V$, which fixes ownership at sends and spawns.`, DEF, R`$\Theta = \{c^{+} \mapsto S@\rho\}$.`, 'relation/Relation.v: Vbody TSess');
n('V-Prod', R`$V$ at $\otimes$`, R`$\langle v_1, v_2\rangle \in V\llbracket\Theta \vdash T_1 \otimes T_2\rrbracket \iff \exists \Theta_1, \Theta_2.\ \Theta = \Theta_1 \uplus \Theta_2 \land \forall i.\ v_i \in V\llbracket\Theta_i \vdash T_i\rrbracket$.`, R`The clause mirrors E-Pair, and the disjoint split keeps environments exact through pairs.`, DEF, R`$\langle c^{+}, d^{-}\rangle$ splits $\{c^{+}, d^{-}\}$ into $\{c^{+}\} \uplus \{d^{-}\}$.`, 'relation/Relation.v: Vbody TProd');
n('V-Prod.split', R`$\Theta = \Theta_1 \uplus \Theta_2$`, R`The components own disjoint parts of $\Theta$.`, R`An end is owned by exactly one component, so no renaming can move a held end into a box inside a pair.`, DEF, R`$\{c^{+}\} \uplus \{d^{-}\}$.`, 'relation/Relation.v: Vbody TProd');
n('V-Sum', R`$V$ at $\oplus$`, R`$\mathsf{inj}_i\,v \in V\llbracket\Theta \vdash T_1 \oplus T_2\rrbracket \iff v \in V\llbracket\Theta \vdash T_i\rrbracket$.`, R`The clause mirrors E-Inj and E-Case, and branch returns its end in an injection.`, DEF, R`$\mathsf{inj}_1\,c^{+} \in V\llbracket\{c^{+} \mapsto S_1@x\cdot\kappa_1\} \vdash S_1@x\cdot\kappa_1 \oplus T\rrbracket$.`, 'relation/Relation.v: Vbody TSum');
n('V-Arrow.exact', R`$\mathrm{dom}\,\Theta = \mathsf{fends}(e)$`, R`A closure owns exactly the ends its body mentions.`, R`With it, every $v \in V$ satisfies $\mathrm{dom}\,\Theta = \mathsf{fends}(v)$, so the ends a send or spawn hands over are $\mathsf{fends}$ of the value.`, R`$\lambda\_.\,\mathsf{let}\ \ast = \Omega\ \mathsf{in}\ \mathsf{close}\,q^{+}$ owns nothing and is in $V$ at every level, and then a send of it next to $q^{+}$ fails E-Send.`, R`$\lambda\_.\,\mathsf{close}\,a$ owns $\{a\}$.`, 'relation/Relation.v: Varr');
n('V-Arrow.lb', R`$l \preccurlyeq \mathsf{heads}\,\Theta$`, R`For $l = y$, $\forall z \in \mathsf{heads}\,\Theta.\ y \preccurlyeq z$, and for $l$ absent, $\mathsf{heads}\,\Theta = \varnothing$.`, R`The holder of a closure reads its heads through $l$, which bounds the heads of the values it holds.`, DEF, R`A closure over $a$ at $\rho$ has $\mathsf{heads}\,\Theta = \{\overline{\rho}\}$ and $l = \overline{\rho}$.`, 'relation/Relation.v: Varr, lb_le');
n('V-Arrow.kripke', R`$\forall W' \sqsupseteq W$`, R`The body is in $E$ in every extension $W'$ of $W$.`, R`A closure may be called after composition has extended the world, so $V$ is monotone in $W$.`, DEF, R`A received closure is called in $W \sqcup W'$.`, 'relation/Relation.v: Varr');
n('V-Arrow.level', R`Level of the body`, R`The body is read at every level $j < n$, \annp{and under a general table at every $j \leq n - \kappa_\beta$.}`, R`A $\beta$-step costs one level in the deadlock-free relation. \annp{Under $\kappa_L$, where $\beta$ is free, the body is read at level $n$.}`, DEF, R`The body of a closure in $V_3$ is read at levels $0$ to $2$.`, 'relation/Relation.v: Varr');
n('V-Arrow.ub', R`$W' \vdash u \prec F$`, R`The body is in $E$ under every future $F$ with $\forall y \in F.\ W' \vdash u \prec y$.`, R`A closure may block up to $u$, so its caller must still act only above $u$.`, DEF, R`The body of $\mathsf{between}$ runs under every $F$ above $\kappa$.`, 'relation/Readiness.v: ub_lt');
n('V-Arrow.body', R`Body in $E$`, R`$e[w] \in E^{W'}_j\llbracket\Theta \cup \Theta' \vdash U\rrbracket^{F}$ for every argument $w \in V^{W'}_j\llbracket\Theta' \vdash T\rrbracket$ with $\Theta' \mathbin{\#} \Theta$.`, R`The call owns the closure's ends and the argument's ends, which are disjoint, and the compatibility of E-App feeds exactly this union to the body.`, DEF, R`$\mathsf{cli}$ applied to $\langle a, b\rangle$ runs at $\{a, b\}$.`, 'relation/Relation.v: Varr');
n('V-Thunk.empty', R`Empty future $\varnothing$`, R`The spawned body is read at $F = \varnothing$ with no lower and no upper point.`, R`The thunk leaves the parent and starts a thread with no context, so no readiness of the parent reads its heads and nothing waits after it.`, R`With a lower point, a thread holding ends at unrelated points $1$ and $2$ could not spawn a thunk that closes both.`, R`$\mathsf{spawn}\,(\lambda u.\,\mathsf{close}\,d')$.`, 'relation/Relation.v: Vthunk');
n('V-Box.empty', R`$\Theta = \varnothing$`, R`A box value owns no end.`, R`Every value in $V$ satisfies $\mathrm{dom}\,\Theta = \mathsf{fends}(v)$, and at a box this is $\Theta = \varnothing$.`, R`Without it, a box could be copied together with an end it owns.`, R`$!(\ldots) \in V\llbracket\varnothing \vdash \Box(\ldots)\rrbracket$.`, 'relation/Relation.v: Vbody TBox');
n('V-Box.noends', R`$\mathsf{fends}(e) = \varnothing$`, R`The body of a box mentions no end.`, R`A box is unlimited, so it must be copyable, and an end mentioned inside would be copied with it.`, R`A box hiding an end under an empty environment could be forced twice and act on the end twice.`, R`$\mathsf{ring}$ mentions no end.`, 'relation/Relation.v: Vbody TBox');
n('V-Box.kripke', R`$\forall W' \sqsupseteq W$`, R`The thunk is in $V$ in every extension $W'$ of $W$.`, R`$V$ is monotone in $W$, and at a box the extension cannot be pushed into the thunk clause, because the instances $\bar x$ range over points ordered only in $W'$.`, R`Without it, a box received after composition could not be forced at an instance whose constraint holds only in the joined world.`, R`Forcing a received box in $W \sqcup W'$.`, 'relation/Relation.v: Vbody TBox');
n('V-Box.inst', R`$W' \vdash C[\bar x]$`, R`The thunk is in $V$ at every instance $\bar x \in \mathsf{Point}^m$ with $\forall (y \prec z) \in C.\ W' \vdash y[\bar x] \prec z[\bar x]$.`, R`E-Force asks $\Gamma \vdash C[\bar x]$ at its instance, so the box must work at every instance meeting $C$ and at no other.`, DEF, R`The self call of $\mathsf{cli}$ at $(\iota^{+}, \kappa^{+}, \zeta)$.`, 'relation/Readiness.v: wholds');
n('V-Box.hc', R`Hereditarily contractive instances`, R`The thunk is in $V$ at every list $\bar s$ of $k$ hereditarily contractive session types.`, R`Session instances must unfold to a head, which hereditary contractiveness guarantees.`, DEF, R`$k = 0$ in every example.`, 'types/Types.v: hcontractive');
n('V-Box.thunk', R`The thunk at level $n$`, R`$\mathsf{thunk}(e) \in V^{W'}_n\llbracket\varnothing \vdash \ast \multimap^{u[\bar x]} U[\bar s][\bar x]\rrbracket$.`, R`$\mathsf{size}(\Box\ldots) > \mathsf{size}(\ast \multimap U)$, so $V$ at the box reads $V$ at the thunk type inside level $n$.`, DEF, R`$\mathsf{thunk}(e) = \lambda.\,e[!e]$.`, 'relation/Relation.v: thunk, tthunk');
n('V-Ex.lb', R`$l \preccurlyeq \mathsf{heads}\,\Theta$`, R`For $l = y$, $\forall z \in \mathsf{heads}\,\Theta.\ y \preccurlyeq z$, for $l$ absent $\mathsf{heads}\,\Theta = \varnothing$, and for $l = \bot$ nothing.`, R`It lets a holder bound the actual heads of a packed value by its static heads, which the readiness of a send carrying a packed payload and the compatibility of E-Pack use.`, R`Without it, a sender holding a packed payload could not show its offered end below the partner points of the payload ends.`, R`$\bot$ for $\mathsf{new}_\ell$.`, 'relation/Readiness.v: lbx_le');
n('V-Ex.witness', R`A witness in $W$`, R`$\exists \bar x \in \mathsf{Point}^m.\ W \vdash C[\bar x] \land v \in V\llbracket\Theta \vdash T[\bar x]\rrbracket$.`, R`Opening an existential substitutes fresh point variables and adds $C$ to $\Gamma$, and the compatibility of E-Open instantiates them with this witness.`, DEF, R`The fresh root $a$ with the facts $C$ of its creation.`, 'relation/Relation.v: Vbody TEx');
n('rel.vsize', R`Recursion on $(n, \mathsf{size}\,T)$`, R`$V_n$ is defined by recursion on $n$ and, inside a level, on the size of the type, with all levels built by one course-of-values fixpoint.`, R`Under $\kappa_L$, $V_n$ reads $E_n$ and $V_n$ at smaller types, and instantiation preserves size.`, DEF, R`$\mathsf{size}(\Box(\ldots U)) = 3 + \mathsf{size}\,U$.`, 'relation/Relation.v: tsize, Vtop; relation/Sfix.v: sfix');
// E
n('E.zero', R`Level $0$`, R`$E_0$ holds every term.`, R`Step indexing starts from the trivial relation.`, DEF, R`$\forall e.\ e \in E_0\llbracket\Theta \vdash T\rrbracket^{F}$.`, 'relation/Relation.v: Etop, Erel_0');
n('E.kripke', R`$\forall W_1 \sqsupseteq W$`, R`Each unfolding of $E$ holds in every extension $W_1$ of $W$.`, R`$E$ is monotone in $W$ by definition, so no clause needs its own world quantifier.`, DEF, R`$e \in E^{W}_n \Rightarrow e \in E^{W \sqcup W'}_n$.`, 'relation/Relation.v: Ebody');
n('E.stop', R`(stop)`, R`$\mathsf{irred}\,e \Rightarrow e \in V^{W_1}_{n+1}\llbracket\Theta \vdash T\rrbracket$.`, R`A term that takes no step must be a value in $V$, so a stuck term is in no $E_n$ for $n \geq 1$ and adequacy reads termination off $V$.`, R`A stuck non-value would count as well typed, and adequacy would fail.`, R`$\ast \in E_1\llbracket\varnothing \vdash \ast\rrbracket^{\varnothing}$.`, 'relation/Relation.v: Ebody');
n('E.ready', R`(ready)`, R`$\neg\mathsf{irred}\,e \Rightarrow \mathsf{ready}_{W_1}(\Theta \mid F, e)$.`, R`Readiness excludes circular waiting between threads.`, R`Two threads each waiting on the partner of the other's second end deadlock.`, R`$\mathsf{ready}_W(\Theta \mid F, e)$.`, 'relation/Relation.v: Ebody');
n('E.step', R`(step)`, R`$\forall \alpha, e'.\ e \xrightarrow{\alpha} e' \Rightarrow \mathsf{Obl}_\alpha(e')$.`, R`One conjunct per kind of label keeps $X$ strictly positive.`, DEF, R`A send step meets O-Send.`, 'relation/Relation.v: Esteps, Eobl');
n('O-Beta', R`O-Beta`, R`$e'$ at $\Theta$.`, R`A $\beta$ step changes no end, and the compatibility of every elimination rule discharges it by reading the redex at the same environment.`, DEF, R`Under $\kappa_L$ a $\beta$ step stays at level $n$.`, 'relation/Relation.v: o_beta');
n('O-New', R`O-New`, R`For a fresh name $c$ and every root $a \notin A_W$, some $S$, position $\pi$ and facts $C$ with $\mathsf{strict}(W \oplus C)$ place $c^{+}$ at $S@\pi$ and $c^{-}$ at $\overline{S}@\overline{\pi}$, and the successor runs in $W \oplus C$.`, R`It is the semantic counterpart of E-New. The typing chooses $\pi$ and $C$, and the relation continues in the grown world.`, DEF, R`$\mathsf{new}$ in the cycle.`, 'relation/Relation.v: o_new');
n('O-New.cfresh', R`$c^{\pm} \notin \mathrm{dom}\,\Theta$`, R`The new name is no end of $\Theta$.`, R`The process rule picks $c$ globally fresh, so the term obligation may assume it.`, DEF, R`$c^{+}, c^{-} \notin \mathrm{dom}\,\Theta$.`, 'relation/Relation.v: cfresh');
n('O-New.forall', R`For every fresh root`, R`The obligation holds at every root $a$ outside $A_W$.`, R`The root is then a function of the run, the same at every level.`, R`A root chosen per level breaks lock freedom, because no ownership is then the same at every level.`, R`$\forall a.\ a \notin A_W \Rightarrow \ldots$`, 'relation/Relation.v: o_new');
n('O-New.gfresh', R`$a \notin A_W$`, R`The root $a$ is no root of the current world.`, R`Roots come from a supply separate from channel names, so a link that renames a channel never revives a used root.`, DEF, R`$a \notin \{1, 2\}$.`, 'relation/Relation.v: gfresh');
n('O-New.grow', R`Position and growth`, R`$\pi$ is the fresh root $a$ or a field $x\cdot\kappa$, and $C$ is a set of facts over $\pi$ and points of $W$ with $\mathsf{strict}(W \oplus C)$.`, R`The witness of the existential that E-New returns is $\pi$, and the facts it states hold in $W \oplus C$.`, DEF, R`$C = \{\rho \prec \overline{\rho\cdot 0},\ \overline{\rho} \prec \rho\cdot 0\}$ at $\pi = \rho\cdot 0$.`, 'relation/Relation.v: o_new');
n('O-New.dual', R`Dual placement`, R`$\Theta[c^{+} \mapsto S@\pi,\ c^{-} \mapsto \overline{S}@\overline{\pi}]$.`, R`It is the static result of E-New at the witness $\pi$, and duality of the pair is what the soup asks of restricted channels.`, DEF, R`$\mathsf{new}$ gives $c^{+} : S@a$ and $c^{-} : \overline{S}@\overline{a}$.`, 'relation/Relation.v: new_env');
n('O-Spawn', R`O-Spawn`, R`$\Theta$ splits into a part $\Theta_M$ for the thunk, which is in $\mathsf{Vthunk}_n(\Theta_M)$, and a rest $\Theta_r$ for the continuation.`, R`Exactness of $\mathsf{Vthunk}$ fixes $\mathrm{dom}\,\Theta_M = \mathsf{fends}(v)$, so the split is the same at every level.`, DEF, R`$\mathsf{spawn}\,(\lambda\_.\,\mathsf{close}\,d')$ gives the child $\{d'\}$.`, 'relation/Relation.v: o_spawn');
n('O-Spawn.split', R`$\Theta = \Theta_M \uplus \Theta_r$`, R`The child and the parent own disjoint parts of $\Theta$.`, R`The fundamental theorem builds the split from E-Spawn's split of the context, and the soup moves exactly $\Theta_M$ to the new thread.`, DEF, R`$\Theta_M = \{d'\}$.`, 'relation/Relation.v: o_spawn');
n('O-Spawn.transfer', R`$\mathrm{dom}\,\Theta_M = \mathsf{fends}(v)$`, R`The part that leaves is exactly the set of ends of the value that leaves.`, R`It follows from exactness of $V$ and $\mathsf{Vthunk}$, which makes ownership at a hand-over independent of the level.`, R`Without exactness, an end mentioned by neither side could go to either side at different levels.`, R`$\mathsf{fends}(\lambda\_.\,\mathsf{close}\,d') = \{d'\}$.`, 'relation/Relation.v: o_spawn, o_send');
n('O-Spawn.thunk', R`$v \in \mathsf{Vthunk}_n(\Theta_M)$`, R`The thunk is in $\mathsf{Vthunk}$ at the parent's level $n$.`, R`For $\kappa_{spawn} = 0$ the child is read inside the parent's least fixpoint, so an infinite chain of spawns is in no $E_n$.`, DEF, R`$\mathsf{Vthunk}_n(\{d'\})$.`, 'relation/Relation.v: o_spawn');
n('O-Send', R`O-Send`, R`The subject is at a send head, $\Theta \setminus o$ splits into the payload part $\Theta_M$ and the rest, the payload is in $V$, and the continuation runs at the rest with $o$ at $S@x^{+}$.`, R`Exactness of $V$ fixes $\mathrm{dom}\,\Theta_M = \mathsf{fends}(w)$.`, DEF, R`$\mathsf{send}\,\langle a, y\rangle$ in the growing ring.`, 'relation/Relation.v: o_send');
n('O-Send.split', R`$\Theta \setminus o = \Theta_M \uplus \Theta_r$`, R`The payload owns no copy of the subject $o$.`, R`A send hands on held ends other than its subject.`, R`A term that sends its own subject would leave the continuation acting on an end it gave away.`, R`$\Theta \setminus o = \Theta_M \cup \Theta_r$.`, 'relation/Relation.v: o_send');
n('sr.head', R`Head of an end $\Theta(o) \doteq S@x$`, R`$\Theta(o) \doteq S@x$ states $\Theta(o) = S_0@x$ for some $S_0$ with $\mathsf{unfold}\,S_0 = S$.`, R`Every obligation reads the first action of the subject end after unfolding, so the notation states it once.`, DEF, R`$\Theta(o) \doteq {!}(\bar\iota.\,\ast).\mathsf{Close}@x$ for $\Theta(o) = (\mu\alpha.\,{!}\ast.\mathsf{Close})@x$.`, 'relation/Relation.v: o_send, o_recv, o_close, o_select, o_branch');
n('O-Send.payload', R`Payload level`, R`$w \in V_{n}\llbracket\Theta_M \vdash U[x\cdot\bar\imath]\rrbracket$, \annp{and $V_{n-\kappa_{give}}$ under a general table.}`, R`The payload is read at the level of the continuation, because a send costs no level in the deadlock-free relation. \annp{Under $\kappa_L$ it costs one.}`, DEF, R`The payload $a$ of $\mathsf{send}\,\langle a, y\rangle$ at $Y\cdot 0$.`, 'relation/Relation.v: o_send');
n('O-Send.shift', R`$o : S@x^{+}$`, R`The subject continues at $S$ and the next point $x^{+}$.`, R`$x \prec x^{+}$ holds in every world, so successive actions on one end are ordered.`, DEF, R`$\Theta_r[o \mapsto S@x^{+}]$.`, 'relation/Relation.v: o_send');
n('O-Recv', R`O-Recv`, R`For every $j < n$ and every incoming $w \in V_j$ with ends disjoint from $\Theta$, the continuation is in $E_j$ with those ends added.`, R`The receiver cannot know what arrives, so it continues for every value its type admits, and the compatibility of E-Recv pairs this with the sender's O-Send.`, DEF, R`$\mathsf{let}\ \langle u, b\rangle = \mathsf{recv}\,b\ \mathsf{in}\ \ldots$`, 'relation/Relation.v: o_recv');
n('O-Recv.forall', R`Every incoming value`, R`$\forall j, \Theta_{in}.\ j < n \land \Theta_{in} \mathbin{\#} \Theta \land w \in V_j\llbracket\Theta_{in} \vdash U[x\cdot\bar\imath]\rrbracket$.`, R`This negative occurrence of $V$ is at a lower level, so $V$ is well defined. \annp{Under a general table the bound is $j + \kappa_{take} \leq n$, and $1 \leq \kappa_{take}$ keeps $j < n$.}`, DEF, R`$\forall j\,\Theta_{in}$.`, 'relation/Relation.v: o_recv');
n('O-Recv.level', R`Continuation at level $j$`, R`$e' \in E_j\llbracket\Theta[o \mapsto S@x^{+}] \cup \Theta_{in} \vdash T\rrbracket^{F}$.`, R`The continuation owns the old ends with $o$ advanced and the received ends, and is read at the level of the value it received.`, DEF, R`$E_j\llbracket\Theta[o \mapsto S@x^{+}] \cup \Theta_{in} \vdash T\rrbracket^{F}$.`, 'relation/Relation.v: o_recv');
n('O-Close', R`O-Close`, R`At a $\mathsf{Close}$ head, $e'$ at $\Theta \setminus o$.`, R`After the close nobody holds $o$, which matches the restriction removed by the process rule.`, DEF, R`$\mathsf{close}\,c^{+}$.`, 'relation/Relation.v: o_close');
n('O-Select', R`O-Select`, R`At a head $\oplus(S_1, S_2)$, $e'$ at $\Theta[o \mapsto S_i@\overline{x\cdot\kappa_i}]$.`, R`The selecting end keeps its name and moves to the dual side of the field of choice $i$, where E-Select places it.`, DEF, R`$\mathsf{select}_{\mathsf{true}}\,o$.`, 'relation/Relation.v: o_select');
n('O-Branch', R`O-Branch`, R`For the choice $i$ the step took, $e'$ at $\Theta[o \mapsto S_i@x\cdot\kappa_i]$, one level later.`, R`The branching end moves to the field of choice $i$, the partner point of the selecting side.`, DEF, R`$\mathsf{branch}\,o$.`, 'relation/Relation.v: o_branch');
n('O-Link', R`O-Link`, R`Two distinct ends at $x$ and $\overline{x}$ with dual types leave $\Theta$.`, R`After the link the partners of $o_1$ and $o_2$ form one channel, which is well typed only if $o_1$ and $o_2$ were dual.`, DEF, R`$\mathsf{link}\,\langle c^{+}, d^{-}\rangle$.`, 'relation/Relation.v: o_link');
n('O-Link.distinct', R`$o_1 \neq o_2$`, R`A self link is rejected.`, R`The link label is a set and may be degenerate.`, DEF, R`$\mathsf{link}\,\langle c^{+}, c^{+}\rangle$ is in no $E_n$.`, 'relation/Relation.v: o_link');
n('O-Link.dual', R`Dual at dual points`, R`$\Theta(o_1) = S_1@x \land \Theta(o_2) = S_2@\overline{x} \land \mathsf{sdual}\,S_1\,S_2$.`, R`E-Link types the two ends exactly dual at dual points, and the soup keeps restricted pairs dual, which the renaming of the link preserves only under this condition.`, DEF, R`$c^{+} : S@x$ and $d^{-} : \overline{S}@\overline{x}$.`, 'relation/Relation.v: o_link');
// readiness
n('rd.stable', R`$\mathsf{stable}\,t$`, R`$\forall \alpha, t'.\ t \xrightarrow{\alpha} t' \Rightarrow \alpha \text{ is a session label}$.`, R`Readiness constrains only terms that wait for a partner.`, DEF, R`$\mathsf{recv}\,b$ is stable, $(\lambda x.x)\,\ast$ is not.`, 'relation/Readiness.v: stable_t');
n('rd.offered', R`$\mathsf{offered}_\Theta(t, o)$`, R`$o \in \mathrm{dom}\,\Theta \land \exists \sigma, t'.\ t \xrightarrow{\sigma} t' \land o \in \mathsf{subj}\,\sigma$.`, R`Each end has its own entry, so the offered ends are read off the labels.`, DEF, R`$\mathsf{recv}\,b$ offers $b$.`, 'relation/Readiness.v: offered_t');
n('rd.value', R`No offer means a value`, R`$(\forall o.\ \neg\mathsf{offered}_\Theta(t, o)) \Rightarrow t \in \mathsf{Val}$.`, R`A stable term offering only ends it does not hold would be stuck.`, DEF, R`$\mathsf{close}\,q$ with $q \notin \mathrm{dom}\,\Theta$ is not ready.`, 'relation/Readiness.v: ready_t');
n('rd.link', R`$\mathsf{link}\,t$`, R`$\exists os, t'.\ t \xrightarrow{\leftrightarrow os} t'$, and a term at a link is ready.`, R`A link step at process level needs no partner thread, so a link never waits and readiness need not order it.`, R`Asking the order of a link would reject every link next to an end held at an unrelated point, and E-Link has no order premise.`, R`$\mathsf{link}\,\langle c^{+}, d^{-}\rangle$.`, 'relation/Readiness.v: link_t');
n('rd.below-rest', R`$\mathsf{below\_rest}$`, R`Every offered end at $x$ lies below the partner point of every held end it does not offer and below every point of $F$.`, R`It excludes circular waiting, because a waiting thread's offer is minimal among what it holds and what its context still does.`, R`Client and server each blocked on their second channel while holding the first, under a cyclic order.`, R`Closing $c$ at $\rho$ while $d$ is held at $\rho\cdot 0$ needs $\rho \prec \overline{\rho\cdot 0}$.`, 'relation/Readiness.v: below_rest');
n('rd.below-held', R`Below held partners`, R`$\forall o' \notin O.\ \Theta(o') = S'@x' \Rightarrow W \vdash x \prec \overline{x'}$.`, R`The partner of a held end acts at $\overline{x'}$, so the offered end is served before anyone waits on the held ends.`, DEF, R`$\rho \prec \overline{\rho\cdot 0}$.`, 'relation/Readiness.v: below_rest');
n('rd.below-future', R`Below the future`, R`$\forall y \in F.\ W \vdash x \prec y$.`, R`The context acts at the points of $F$ after the term returns.`, DEF, R`$\kappa \prec \varphi$ in $\mathsf{between}$.`, 'relation/Readiness.v: below_rest');
n('rd.p-stable', R`$\mathsf{stable}\,p$`, R`$p$ takes no internal step.`, R`A process with an internal step is not waiting, and readiness speaks only of waiting processes.`, DEF, R`A thread at an external $\mathsf{recv}$.`, 'relation/Readiness.v: stable_p');
n('rd.p-term', R`No offer means terminated`, R`$(\forall o.\ \neg\mathsf{offered}_\Sigma(p, o)) \Rightarrow \mathsf{terminated}\,p$.`, R`A stable process that offers nothing to its environment must be finished, which is the deadlock-freedom statement at the process level.`, R`Without it, a stable process blocked on internal ends would satisfy P-Ready.`, R`$(\varnothing, \{\ast\})$.`, 'relation/Readiness.v: ready_p');
n('rd.above-offered', R`$\mathsf{above\_offered}$`, R`Every interface end at $x$ that is not offered has an offered end at $x'$ with $W \vdash x' \prec \overline{x}$.`, R`The environment can always serve some offered end first, so composing two ready processes over a strict world keeps one of them able to move.`, DEF, R`$\mathsf{above\_offered}\,W\,\Sigma\,O$.`, 'relation/Readiness.v: above_offered');
// P
n('P.strict', R`Strict later worlds only`, R`Each unfolding of $P$ holds in every $W_1 \sqsupseteq W$ with $\mathsf{strict}\,W_1$.`, R`In a cyclic $W_1$ a receive could bring ends that only a cyclic order accepts, and both components of a composition would be ready around the cycle.`, R`Two components each holding the partner of the other's second channel are both ready in a cyclic world and deadlock.`, R`$\forall W_1 \sqsupseteq W.\ \mathsf{strict}\,W_1 \Rightarrow \ldots$`, 'relation/Relation.v: Pbody');
n('P.fuse', R`Closed under fusions`, R`Each unfolding holds at $\mathsf{sdrop}\,D\,(h\,\Sigma)$ and $\mathsf{pfuse}\,h\,D\,p$ for every $(h, D)$ with $\mathsf{fuse\_ok}\,h\,D\,\Sigma\,p$.`, R`Renaming, internalizing a pair of interface ends and the renaming done by a link are all fusions, and closure by definition makes each of them a projection.`, R`With renamings alone, a link could join two unrelated interface ends into one channel and composition would fail.`, R`$h = \mathsf{id}$ internalizes pairs, $D = \varnothing$ renames.`, 'relation/Relation.v: Pbody');
n('P-Stop', R`P-Stop`, R`$\mathsf{pirred}\,p' \Rightarrow \exists v, E.\ p' = (\varnothing, \{v\} \uplus E) \land v \in V\llbracket\Sigma' \vdash T\rrbracket \land \forall e \in E.\ e = \ast$.`, R`An irreducible process in $P$ has no restricted channel left, its main thread returned a value in $V$ and every other thread returned $\ast$, which is the definition of terminated.`, R`Without it, a process stuck with restricted channels would be in $P$, and adequacy would fail.`, R`$(\varnothing, \{\ast, \ast\})$ at $T = \ast$.`, 'relation/Relation.v: Pclauses');
n('P-Ready', R`P-Ready`, R`$\neg\mathsf{pirred}\,p' \Rightarrow \mathsf{ready}_{W_1}(\Sigma', p')$.`, R`Readiness of processes excludes circular waiting across the interface.`, DEF, R`$\mathsf{ready}_{W_1}(\Sigma', p')$.`, 'relation/Relation.v: Pclauses');
n('P-Step', R`P-Step`, R`Every instrumented step $q \xrightarrow{ev} q'$ with $\mathsf{erase}\,q = p'$ meets $\mathsf{Pobl}_{ev}$.`, R`$P$ quantifies over every thread numbering of $p'$, so it speaks of the one instrumented semantics.`, DEF, R`A message between two threads meets Q-Tau.`, 'relation/Relation.v: Psteps');
n('fuse.dcomm', R`$h$ commutes with duality`, R`$\forall o.\ h(\overline{o}) = \overline{h(o)}$.`, R`Restricted channels and the partners added by Q-Send and Q-Recv enter $P$ as pairs, which $h$ must map to pairs.`, DEF, R`$\mathsf{csub}\,o_1\,o_2$ commutes with duality.`, 'relation/Relation.v: dcomm');
n('fuse.inj', R`Injective on held ends`, R`$\forall o_1, o_2 \in \mathsf{held}.\ h(o_1) = h(o_2) \Rightarrow o_1 = o_2$.`, R`$\mathsf{csub}$ of a link identifies $\overline{o_1}$ and $o_2$, so $h$ is no bijection, but it is injective on the held ends of the other component.`, DEF, R`$\mathsf{csub}$ is injective on the other side's held ends.`, 'relation/Relation.v: fuse_ok');
n('fuse.partners', R`New partners only on $D$`, R`$h(o_2) = \overline{h(o_1)} \Rightarrow o_2 = \overline{o_1} \lor \mathsf{ech}(h\,o_1) \in D$.`, R`Two held ends become partners only if they were or their channel is restricted by the fusion.`, R`Without it, $h$ joins unrelated interface ends into one channel, and composition fails.`, R`$D = \varnothing$ creates no new pair.`, 'relation/Relation.v: fuse_ok');
n('fuse.D', R`$D \cap \mathsf{gch}_h[C] = \varnothing$`, R`The channels restricted by the fusion are not images of channels already restricted.`, R`Composition splits a fused process into its two sides, and this condition keeps the two restricted sets $\mathsf{gch}_h[C_i] \cup D_i$ disjoint from each other and from the interface.`, R`Without it, a restricted channel could be restricted again as a new pair, and the split of the fused composite fails.`, R`$D \mathbin{\#} \mathsf{gch}_h[C]$.`, 'relation/Relation.v: fuse_ok');
n('fuse.dpairs', R`$\mathsf{dpairs}\,D\,\Sigma$`, R`Both ends of every channel of $D$ are in $\Sigma$, at dual points and dual types.`, R`They become restricted, and restricted channels are dual pairs.`, DEF, R`Internalizing $c$ with $\Sigma(c^{+}) = S@x$ and $\Sigma(c^{-}) = \overline{S}@\overline{x}$.`, 'relation/Relation.v: dpairs');
n('Q-Tau', R`Q-Tau`, R`An internal step that restricts no interface channel keeps $\Sigma$ and costs the levels of its kind of step.`, R`Administrative steps and internal synchronizations are one clause.`, DEF, R`A message between two threads costs one level\annp{, and $\kappa_{give} + \kappa_{take}$ under a general table}.`, 'relation/Relation.v: q_tau');
n('Q-Send', R`Q-Send`, R`An external send. The interface part $\Sigma_v$ and the restricted part $\Theta_e$ of the payload leave, and the partners $\Sigma_e$ left behind join the interface.`, R`It is O-Send at the process level, and the compatibility of P-Term discharges it from O-Send of the thread.`, DEF, R`Sending a restricted end $d^{+}$ puts $d^{-}$ into the interface.`, 'relation/Relation.v: q_send');
n('Q-Send.theta-e', R`Extruded ends $\Theta_e$`, R`$\mathrm{dom}\,\Theta_e = \{o' \in \mathsf{fends}(w) \mid \mathsf{ech}(o') \in C\}$.`, R`$\Theta_e$ is exactly the restricted part of the ends of $w$. Exactness of $V$ at the payload gives $\mathsf{fends}(w) = \mathrm{dom}\,\Sigma_v \cup \mathrm{dom}\,\Theta_e$, so the payload carries $\mathsf{fends}(w)$ and nothing else.`, DEF, R`$\Theta_e = \{d^{+}\}$.`, 'relation/Relation.v: q_send, compat/Redex.v: Vrel_exact');
n('Q-Send.split', R`$\mathsf{send\_split}$`, R`The extruded ends are no interface ends, and $\Sigma_e$ holds the partners of extruded ends that stay, at dual types and points.`, R`The partner of an extruded end becomes an interface end, and the interface must record its type and point.`, R`Without it, the process would keep an end its interface does not mention, and P-Stop could not hold.`, R`$\Sigma_e = \{d^{-}\}$.`, 'relation/Relation.v: send_split');
n('Q-Send.sigma-e', R`$\Sigma_e$ joins the interface`, R`Partners of extruded ends become interface ends.`, R`Scope extrusion frees their channel.`, DEF, R`$d^{-}$ joins $\Sigma$.`, 'relation/Relation.v: q_send');
n('Q-Recv', R`Q-Recv`, R`For every incoming environment and value, the process continues with the received ends added and the channels both of whose ends it now holds restricted.`, R`It is O-Recv at the process level, and composition feeds one component's Q-Send into the other's Q-Recv.`, DEF, R`Receiving $d^{-}$ while holding $d^{+}$ restricts $d$.`, 'relation/Relation.v: q_recv');
n('Q-Recv.ok', R`$\mathsf{recv\_ok}$`, R`Incoming ends are new to $\Sigma$, and every incoming end whose partner is held or received sits at the dual point with the dual type.`, R`Composition delivers one component's payload only under this condition, and it is what makes a newly restricted pair dual.`, R`Without the duality conjunct, receiving the partner of a held end at a mismatched type would restrict an ill-typed channel.`, R`$\mathsf{recv\_ok}\,\Sigma\,\Theta_2$.`, 'relation/Relation.v: recv_ok');
n('Q-Recv.back', R`$\mathsf{recv\_back}$`, R`The channels of incoming ends whose partner is held or received along.`, R`Both ends of such a channel are now in the process, so it is restricted, as the interface stays partner-free.`, DEF, R`$\mathsf{recv\_back}\,\Sigma\,\{d^{-}\} = \{d\}$ for $d^{+} \in \mathrm{dom}\,\Sigma$.`, 'relation/Relation.v: recv_back');
n('Q-Recv.env', R`$\mathsf{recv\_env}$`, R`The interface after the receive, without the ends that became internal.`, R`Internal ends leave the interface, and the rest of $\Theta_2$ joins it.`, DEF, R`$\mathsf{recv\_env}\,\Sigma\,\Theta_2$.`, 'relation/Relation.v: recv_env');
n('Q-Link', R`Q-Close, Q-Select, Q-Branch, Q-Link`, R`The term obligations O-Close, O-Select, O-Branch and O-Link with $\Sigma$ for $\Theta$ and $P$ for $E$.`, R`An external close, choice or link acts on interface ends exactly as a thread acts on its own ends.`, DEF, R`Q-Link removes both linked ends from $\Sigma$.`, 'relation/Relation.v: q_close, q_select, q_branch, q_link');
// semantic judgments
n('sj.at', R`Judgment at a set of points $X$`, R`For every level, later world, environment $\Theta'$ disjoint from the ends $|\Delta|$ and grounding $\gamma$ of the variables of $\Delta$ in $\Theta'$, $\gamma(e) \in E_n\llbracket|\Delta| \cup \Theta' \vdash T\rrbracket^{X}$.`, R`It quantifies over everything a context may supply, so it composes by the compatibility lemmas.`, DEF, R`$\Delta \vDash^{X}_W e : T$.`, 'compat/SemTyped.v: sem_typed_at');
n('sj.grel', R`Grounding $\gamma \in G\llbracket\Theta \vdash \Delta\rrbracket$`, R`$\gamma$ substitutes for each entry $T^a$ of $\Delta$ a value in $V\llbracket\Theta_i \vdash T\rrbracket$, with $\Theta = \biguplus_i \Theta_i$.`, R`Variables of $\Delta$ stand for values, and the ends of those values split $\Theta$ disjointly.`, DEF, R`For $\Delta = [T]$, $\gamma(0) \in V\llbracket\Theta \vdash T\rrbracket$.`, 'compat/SemTyped.v: Grel');
n('sj.den', R`$\mathsf{den}_{\rho,B}(F)$`, R`$\mathsf{den}_{\rho,B}(F_1, f) = F_1 \cup \rho(\varphi) \cup B$, with $\rho(\varphi)$ only if $f$ has the variable $\varphi$ and $B$ only if $f$ has the flag $\bot$.`, R`A future variable and the flag $\bot$ stand for unknown sets of points, so the judgment holds at every choice of them.`, DEF, R`$\mathsf{den}_{\rho,B}(\varnothing, \varphi) = \rho(\varphi)$.`, 'compat/SemTyped.v: sf_den');
n('sj.term', R`$\Delta \vDash^{F}_W e : T$`, R`$\forall \rho, B.\ \Delta \vDash^{\mathsf{den}_{\rho,B}(F)}_W e : T$, with the same context $\Delta$ as the typing judgment.`, R`It is the conclusion of the fundamental theorem for terms. \annp{The lock-free reading $\vDash[\kappa_L]$ uses the table $\kappa_L$.}`, DEF, R`$\varnothing \vDash^{\varnothing}_W e : T$.`, 'compat/SemTyped.v: sem_typed');
n('sj.proc', R`$\Sigma \vDash_W p : T$`, R`$\forall n.\ p \in P^W_n\llbracket\Sigma \vdash T\rrbracket$.`, R`Adequacy turns it into deadlock freedom. \annp{With $\kappa_L$ it also gives absence of internal divergence.}`, DEF, R`$\varnothing \vDash_W p : \ast$.`, 'relation/Adequacy.v: sem_ptyped');
// fuel
n('fu.zero', R`Level $0$`, R`$F_0$ holds every term.`, R`Step indexing starts from the trivial predicate.`, DEF, R`$\forall e.\ e \in F^N_0\llbracket\sigma \triangleright d ; r\rrbracket(\Pi,\varphi,tk)$.`, 'fuel/Fuel.v: mk_flevel');
n('fu.rty', R`Result $\sigma$`, R`$\sigma$ is a credited type $T^a$ of the returned value, or $\mathsf{thread}$, whose value holds no end.`, R`A spawned thread returns $\ast$ and keeps no end, which $\mathsf{thread}$ states without a type.`, DEF, R`$\mathsf{thread}$ for a soup thread.`, 'fuel/Fuel.v: rty');
n('fu.frame', R`Frame $d$`, R`$d \in \mathbb{N} \cup \{\infty\}$ bounds the channel actions the term performs before it returns.`, R`Every action asks $1 \leq d$ and lowers $d$ by one, so a context that ticks its own ends during the term is paid by the frame.`, DEF, R`A thread has frame $\infty$.`, 'fuel/Fuel.v: Fdef');
n('fu.reserve', R`Reserve $r$`, R`$r \in \mathbb{N}$ is the number of tickets the term must still hold when it returns.`, R`The context of the term spends these tickets on its own links afterwards, which the ticket need of the term promises through $\mathsf{meets}\,\vartheta\,r\,tk$.`, R`Without a reserve, a term could spend tickets its context needs, and a context link would find $tk = 0$.`, R`A thread has reserve $0$.`, 'fuel/Fuel.v: Fdef');
n('fu.Pi', R`Protocols $\Pi$`, R`$\Pi$ maps each held end to its session type with annotations.`, R`Counters are compared with credits that the annotations carry, so fuel keeps them.`, DEF, R`$\Pi = \{a \mapsto S_a\}$.`, 'fuel/Fuel.v: penv');
n('fu.phi', R`Counters $\varphi$`, R`$\varphi$ maps each held end to a counter in $\mathbb{N} \cup \{\infty\}$.`, R`A counter bounds how many actions of its holder may pass before the end acts again, and only the holder updates it.`, DEF, R`$\varphi = \{a \mapsto 3\}$.`, 'fuel/Fuel.v: cenv');
n('fu.tk', R`Tickets $tk$`, R`$tk \in \mathbb{N}$ is the thread's count of link tickets.`, R`Each link spends one ticket and tickets are conserved, so a thread performs finitely many links between actions.`, DEF, R`$tk = 0$ in every example.`, 'fuel/Fuel.v: Fdef');
n('fu.refill-kripke', R`Every refill above $N$`, R`$F^N$ holds at every $N'$ with $N \sqsubseteq_{\mathsf{rle}} N'$, where finite refills are ordered by $\leq$ and $\infty$ lies above $\infty$ only.`, R`A received value may be used at a larger refill, and $\infty$ must stay separate because a box received at $\infty$ promises nothing at finite instances.`, R`With $\leq$ on $\mathbb{N} \cup \{\infty\}$, a thread at $N = 2$ could receive a box typed at $\infty$ and fail at its finite instance.`, R`$2 \sqsubseteq_{\mathsf{rle}} 3$, and $2 \not\sqsubseteq_{\mathsf{rle}} \infty$.`, 'fuel/Fuel.v: rle');
n('fu.rename', R`Injective renamings`, R`$F^N$ holds for every renaming $g$ injective on $\mathrm{dom}\,\Pi$ and on $\mathrm{dom}\,\varphi$.`, R`A link renames the partner of a removed end in another thread, so fuel must survive renaming.`, R`A renaming that merges two held ends would merge their counters.`, R`$\mathsf{kinj}\,g\,\Pi$.`, 'fuel/Fuel.v: kinj, renk');
n('fu.val', R`(val)`, R`$g(e) \in \mathsf{Val} \Rightarrow r \leq tk \land g(e) \in FV^{N'}_{n+1}\llbracket\sigma\rrbracket(g\Pi, g\varphi)$.`, R`A returning term hands its context the reserve it promised and a value whose counters meet its credits, which the bind lemma of fuel consumes.`, R`Without $r \leq tk$, a context link after the term could find no ticket.`, R`$\ast$ returns with $r = 0 \leq tk$.`, 'fuel/Fuel.v: Fdef');
n('fu.step', R`(step)`, R`$\forall \alpha, e'.\ g(e) \xrightarrow{\alpha} e' \Rightarrow \mathsf{Fobl}^{N'}_\alpha(e')$ at level $n$.`, R`Each step updates the state by one index-free rule, which the soup follows along a run.`, DEF, R`A send step meets F-Send.`, 'fuel/Fuel.v: Fdef, Fobl');
n('fu.oneclock', R`One level per step`, R`Every step costs one level, $\beta$, creation, spawn and link included.`, R`A clock that let $\beta$ be free would admit a box that only takes $\beta$ steps at every level, so the cost fundamental theorem would need the guard as a premise.`, DEF, R`F-Beta reads $e'$ at level $n$.`, 'fuel/Fuel.v: Fdef');
n('F-Wait', R`F-Wait`, R`$\neg\mathsf{idle}(\Pi\,o)$, an idle end does not act.`, R`An idle end is exempt from the checks $\geq 1$, so it must not act either.`, DEF, R`An end at $\mathsf{Skip}$ cannot act.`, 'fuel/Fuel.v: f_act');
n('F-Tick', R`F-Tick`, R`$\mathsf{fspare}\,\Pi\,\varphi\,(\mathrm{dom}\,\varphi \setminus \{o\})$, every other end that is not idle has counter at least $1$.`, R`Each action ticks the other ends, so an end can wait only as many actions of its holder as its counter allows.`, R`A holder that loops on other ends forever while its partner waits on a held end.`, R`At $\varphi = \{a \mapsto 2, b \mapsto 0\}$ no action on $a$ is allowed unless $b$ is idle.`, 'fuel/Fuel.v: f_act, fspare');
n('F-Tick.frame', R`$1 \leq d$`, R`The frame has a unit for the action.`, R`The frame pays the ticks the context's ends take during the term.`, DEF, R`$1 \leq d$.`, 'fuel/Fuel.v: f_act');
n('fu.refillop', R`$\mathsf{refill}$`, R`$\mathsf{refill}\,N\,o\,\varphi$ sets $o$ to $N$ and lowers every other counter by one, truncated at $0$.`, R`Counters evolve by one index-free update.`, DEF, R`$\mathsf{refill}\,3\,a\,\{a \mapsto 1, b \mapsto 2\} = \{a \mapsto 3, b \mapsto 1\}$.`, 'fuel/Fuel.v: refill');
n('fu.idle', R`$\mathsf{idle}$`, R`$\mathsf{idle}\,S \iff \mathsf{unfold}\,S = \mathsf{Skip}$.`, R`Idleness removes the checks $\geq 1$ and never changes how a counter evolves, so counters stay index-free. The typing ages idle ends by truncation at $0$, matching counters that tick down to $0$.`, R`An idle end whose credit stayed fixed while its counter ticks would exceed its counter.`, R`$\mathsf{idle}\,\mathsf{Skip}$.`, 'fuel/Fuel.v: idle');
n('F-Beta', R`F-Beta`, R`$e'$ in $F_n$ at the same state.`, R`A $\beta$ step changes no counter and costs one level.`, DEF, R`$(\lambda x.\,x)\,\ast$.`, 'fuel/Fuel.v: f_beta');
n('F-New', R`F-New`, R`For a fresh $c$, some $S$ adds $c^{+} : S$ and $c^{-} : \overline{S}$ to $\Pi$ with counters $N$.`, R`A new channel starts with both ends at the refill $N$, the credit E-New gives them.`, DEF, R`$\mathsf{new}$ adds $c^{\pm}$ at $N$.`, 'fuel/Fuel.v: f_new');
n('F-New.fresh', R`Fresh against the thread`, R`$c^{\pm} \notin \mathrm{dom}\,\Pi \cup \mathrm{dom}\,\varphi$.`, R`Without it, a new channel could reuse a held name and overwrite its counter.`, DEF, R`$\mathsf{ffresh}\,c\,\Pi\,\varphi$.`, 'fuel/Fuel.v: ffresh');
n('F-New.cnew', R`New counters $N$`, R`$\varphi[c^{+} \mapsto N, c^{-} \mapsto N]$.`, R`One refill $N$ serves fresh ends and ends after an action.`, DEF, R`$\mathsf{cnew}\,N\,c\,\varphi$.`, 'fuel/Fuel.v: cnew');
n('F-Spawn', R`F-Spawn`, R`The child takes $M = \mathsf{fends}(v)$ with counters minus one and $\lceil tk/2 \rceil$ tickets and runs as a thread, the parent keeps the rest and $\lfloor tk/2 \rfloor$.`, R`Every component of the split is a function of $v$ and $tk$, so it is the same at every level.`, DEF, R`The thunk takes $d'$ at $1$ in the cycle.`, 'fuel/Fuel.v: f_spawn');
n('F-Spawn.held', R`$M \subseteq \mathrm{dom}\,\varphi$`, R`Only held ends are handed on.`, R`A child mentioning an end the parent does not hold would act on an end without a counter.`, R`A box mentioning channel constants would hand over ends nobody holds.`, R`$M = \{d'\}$.`, 'fuel/Fuel.v: f_spawn');
n('fu.fspare', R`$\mathsf{fspare}$`, R`$\mathsf{fspare}\,\Pi\,\varphi\,X \iff \forall o \in X.\ \varphi(o) = f \land \neg\mathsf{idle}(\Pi\,o) \Rightarrow 1 \leq f$.`, R`A hand-over passes the counter minus one, so a non-idle end must have a unit to spare. A spawn is no action, so this is its only check.`, R`A hop at counter $0$ under truncation passes $0$ again and an end travels forever.`, R`$\mathsf{fspare}\,\Pi\,\{d' \mapsto 1\}\,\{d'\}$.`, 'fuel/Fuel.v: fspare');
n('F-Spawn.child', R`The child`, R`$v\,\ast \in F^N_n\llbracket\mathsf{thread} \triangleright \infty ; 0\rrbracket(\Pi|_M, \mathsf{fhand}\,M\,\varphi, \lceil tk/2 \rceil)$.`, R`The child is a new soup thread, so it must have thread fuel at exactly the protocols, counters and tickets the soup moves to it.`, DEF, R`$(\lambda u.\,\mathsf{close}\,d')\,\ast$.`, 'fuel/Fuel.v: f_spawn');
n('fu.fhand', R`$\mathsf{fhand}$`, R`$\mathsf{fhand}\,M\,\varphi = (\varphi|_M) \mathbin{\dot-} 1$.`, R`Every counter passed on is the holder's minus one, which the termination measure of adequacy reads.`, DEF, R`$\mathsf{fhand}\,\{a\}\,\{a \mapsto 3\} = \{a \mapsto 2\}$.`, 'fuel/Fuel.v: fhand');
n('F-Spawn.tickets', R`Ticket split`, R`Child $\lceil tk/2 \rceil$, parent $\lfloor tk/2 \rfloor$.`, R`A fixed split is the only split independent of the level.`, DEF, R`$tk = 3$ gives $2$ and $1$.`, 'fuel/Fuel.v: f_spawn');
n('F-Send', R`F-Send`, R`An action on $o$ that hands on $M = \mathsf{fends}(w)$ with counters minus one, the payload in $FV$, and the continuation with $o$ refilled.`, R`A send is an action, so F-Tick applies, and a hand-over, so $\mathsf{fspare}$ applies.`, DEF, R`$\mathsf{send}\,\langle a, y\rangle$ in the growing ring.`, 'fuel/Fuel.v: f_send');
n('F-Send.notsubj', R`$M \subseteq \mathrm{dom}\,\varphi \setminus \{o\}$`, R`A send hands on held ends other than its subject.`, R`The continuation keeps acting on $o$, so $o$ cannot leave.`, R`A term that sends its own subject or an end its context holds.`, R`$M = \{a\}$.`, 'fuel/Fuel.v: f_send');
n('F-Send.payload', R`Payload in $FV$`, R`$w \in FV^N_n\llbracket T\rrbracket(\Pi|_M, \mathsf{fhand}\,M\,\varphi)$, with every handed counter lowered by one hop.`, R`$FV$ reads no point, so the raw payload type and its placed form agree.`, DEF, R`$FV^N_n\llbracket (S@x)^{2}\rrbracket$ for a payload end promised at credit $2$.`, 'fuel/Fuel.v: f_send');
n('F-Recv', R`F-Recv`, R`An action on $o$ that continues for every incoming value in $FV$ at every level $j \leq n$ with disjoint maps.`, R`The receiver continues for every value its type admits, and the soup supplies the sender's handed maps.`, DEF, R`$\mathsf{recv}\,b$ in the client loop.`, 'fuel/Fuel.v: f_recv');
n('F-Recv.forall', R`Every incoming value`, R`$\forall j \leq n, \Pi_i, \varphi_i.\ w \in FV^N_j\llbracket T^b\rrbracket(\Pi_i, \varphi_i)$.`, R`Every value of $FV$ is exact, so incoming closures hold exactly what they mention.`, R`Without exactness, a received closure owning nothing but mentioning an end could not be spawned.`, R`$\forall j\,\Pi_i\,\varphi_i$.`, 'fuel/Fuel.v: f_recv');
n('F-Close', R`F-Close, F-Select, F-Branch`, R`Actions that drop $o$ and tick the rest at a close, or advance $\Pi(o)$ to $S_i$ and refill $o$ at a choice.`, R`They are the fuel forms of O-Close, O-Select and O-Branch, and each is an action, so F-Tick applies.`, DEF, R`$\mathsf{close}\,c^{+}$.`, 'fuel/Fuel.v: f_close, f_select, f_branch');
n('F-Link', R`F-Link`, R`Two distinct held ends at dual protocols leave, and one ticket is spent.`, R`Tickets bound the links between actions.`, DEF, R`$\mathsf{link}\,\langle c^{+}, d^{-}\rangle$ with $tk = 1$.`, 'fuel/Fuel.v: f_link');
n('F-Link.plink', R`$\mathsf{plink}$`, R`$o_1 \neq o_2 \land \Pi(o_2) \simeq \overline{\Pi(o_1)}$, with annotations.`, R`After the link the partners form one channel, whose protocols are dual only if $\Pi(o_1)$ and $\Pi(o_2)$ were, and annotations must match for later payload credits.`, R`A credit mismatch at a link breaks the payload credit of a later message.`, R`$\mathsf{plink}\,\Pi\,\{o_1, o_2\}$.`, 'fuel/Fuel.v: plink');
n('F-Link.ticket', R`$1 \leq tk$`, R`A link spends one ticket.`, R`Tickets are conserved and spent, so links cannot repeat forever.`, R`A box that links once per round forever.`, R`$tk - 1$.`, 'fuel/Fuel.v: f_link');
n('FV-Sess', R`$FV$ at $S@x$`, R`An end with protocol $S' \simeq S$ and counter $f \geq a$.`, R`Credits are lower bounds on counters.`, DEF, R`$o$ at $(S@x)^2$ with counter $3$.`, 'fuel/Fuel.v: Vty TSess');
n('FV-Sess.counter', R`$a \leq f$`, R`The counter meets the credit.`, R`Typing reasons with credits and the soup with counters, and this inequality transfers every credit bound of typing to the counters.`, R`Without it, a context could age an end below its actual counter and F-Tick would fail on an end typing considers spare.`, R`$2 \leq 3$.`, 'fuel/Fuel.v: Vty TSess');
n('FV-Arrow', R`$FV$ at an arrow`, R`A closure whose body has fuel for every larger refill, lower level, counters at or above the floor and argument in $FV$.`, R`The clause reads costs, ticket needs, floors and credits, the data typing attaches to arrows.`, DEF, R`A loop body at cost $\infty$.`, 'fuel/Fuel.v: Vty TLolli');
n('FV-Arrow.exact', R`$\mathsf{fends}\,e = \mathrm{dom}\,\Pi$`, R`The closure holds exactly the ends it mentions.`, R`It mirrors exactness of $V$, and the cost fundamental theorem needs it to read fuel off typing.`, R`A closure mentioning an end it does not hold would be in $FV$, and a forwarder receiving it could not spawn it.`, R`$\lambda\_.\,\mathsf{close}\,a$ holds $\{a\}$.`, 'fuel/Fuel.v: Vty TLolli');
n('FV-Arrow.floor', R`Counters $\geq h + a$`, R`$\forall o.\ h + a \leq \varphi(o)$.`, R`The body may assume the floor $h$ on its captured counters, and the closure's own credit $a$ is spent while it is held.`, DEF, R`$h = 1$, $a = 1$ needs counters $\geq 2$.`, 'fuel/Fuel.v: Vty TLolli');
n('FV-Arrow.body', R`Body fuel`, R`$e[u] \in F^{N'}_j\llbracket U^{a_2} \triangleright c ; r\rrbracket(\Pi \cup \Pi_u, \varphi' \cup \varphi_u, tk)$ for every $tk$ with $\mathsf{meets}\,\vartheta\,r\,tk$.`, R`The caller supplies an argument, counters lowered to the floor by its own actions, and a ticket count meeting the arrow's ticket need, and the body promises fuel with frame $c$.`, DEF, R`$\mathsf{meets}\,\vartheta\,r\,tk$.`, 'fuel/Fuel.v: Vty TLolli');
n('FV-Box', R`$FV$ at a box`, R`A box with no ends whose body has fuel per force at every larger refill, lower level and session instance in $\mathsf{sinsts}\,N'$.`, R`A box is unlimited, so it holds no counters and works at every use.`, DEF, R`$\mathsf{ring}$ at $N = 4$.`, 'fuel/Fuel.v: Vty TBox');
n('FV-Box.noends', R`$\mathsf{fends}\,e = \varnothing$`, R`A box mentions no end and holds no protocol or counter.`, R`A copied box would otherwise copy ends.`, DEF, R`$\mathsf{ring}$.`, 'fuel/Fuel.v: Vty TBox');
n('FV-Box.body', R`Body per force`, R`$e[!e] \in F^{N'}_j\llbracket U[\bar s] \triangleright c ; r\rrbracket(\varnothing, \varnothing, tk)$ for every $N' \sqsupseteq_{\mathsf{rle}} N$, $j < n$, $\bar s \in \mathsf{sinsts}\,N'$ and $tk$ meeting $\vartheta$.`, R`Each force unrolls the box once, at a refill and instance the forcing context chooses.`, DEF, R`$\mathsf{sinsts}\,N'\,\bar s$.`, 'fuel/Fuel.v: Vty TBox');
n('FV-Thread', R`Thread result`, R`$v \in FV\llbracket\mathsf{thread}\rrbracket(\Pi,\varphi) \iff \Pi = \varphi = \varnothing$.`, R`A finished thread holds no end.`, DEF, R`$\Pi = \varphi = \varnothing$.`, 'fuel/Fuel.v: Vres');
n('fu.fsem', R`$\mathsf{fsem}$`, R`$\exists tk.\ \forall n.\ e$ has thread fuel at level $n$ with every held end at $N$.`, R`It is the per-thread fuel the soup needs, obtained from typing by the cost fundamental theorem.`, DEF, R`$\mathsf{fsem}\,N\,\Pi\,e$.`, 'fuel/Fuel.v: fsem');
n('fu.upd', R`$F_n[x := v]$`, R`The fuel of the successor at level $n$, with the refill $N'$, result, frame, reserve, protocols, counters and tickets of the current term, except the listed components, which take the listed values.`, R`Each obligation changes only a few components, so it lists only those.`, DEF, R`$e' \in F_n[tk := tk - 1]$ after a link.`, 'fuel/Fuel.v: f_beta, f_send, f_link');
n('fu.measure', R`The waiting measure $\mu(t)$`, R`For a thread $t$ waiting on $o$, the pair of the tickets of all threads and the counter of the partner end $\overline{o}$, ordered lexicographically.`, R`A link spends a ticket. A step of the holder of $\overline{o}$ on another end ticks $\varphi(\overline{o})$, which F-Tick keeps at $1$ or more because $\overline{o}$ is not idle. Every other step keeps $\mu(t)$. So the holder acts on $\overline{o}$ after finitely many steps.`, R`Without counters the holder could act on other ends forever, as the server that sends an end back and forth starves its waiter.`, R`A thread waits on $c^{+}$ while the holder of $c^{-}$ first acts on another end. Each such action lowers $\varphi(c^{-})$ by one.`, 'soup/LFAdequacy.v: fu, wt');
n('cs.csem', R`$\Delta \vDash^{N} e : T\ !\ \varepsilon$`, R`For every larger refill, level, injective renaming of the ends of $\Delta$, grounding in $FV$ and ticket count meeting $\vartheta$, the instance has fuel at $T$ with frame $c$, for $\varepsilon = (c, \vartheta)$.`, R`It reads no $\Gamma$, world or future, because $F$ reads none of them.`, DEF, R`The cost fundamental theorem concludes it.`, 'cost/CostSem.v: csem');
// soup
n('sp.state', R`Soup state $a = (q, K, tk)$`, R`A configuration $q$, an ownership map $K$ and a ticket count per thread.`, R`Ranks and counters of the termination measure are read off $K$, so ownership is fixed outside the index.`, R`Placement chosen per level lets a waiting main thread starve in every fair run.`, R`$(q, K, tk)$.`, 'soup/State.v: lfstate');
n('sp.hold', R`$K(o) = (t, x, f)$`, R`The holder thread $t$, point $x$ and counter $f$ of a held end $o$.`, R`One map records all data the measure reads.`, DEF, R`$K(a) = (0, \rho, 2)$.`, 'soup/State.v: hold');
n('sp.tk', R`$tk : \mathbb{N} \to \mathbb{N}$`, R`$tk_t$ is the ticket count of thread $t$.`, R`The termination measure of lock-free adequacy sums the tickets of all threads with their reserves, and links lower that sum.`, DEF, R`$tk_0 = 0$.`, 'soup/State.v: s_tk');
n('sp.exists', R`Chosen per level`, R`$\exists A, \Pi, U$, the environment, protocols and result types chosen at each level.`, R`O-New and F-New pick the session type of a new channel by separate existentials, so $\Pi$ cannot be read off $A$.`, DEF, R`$\exists A\,\Pi\,U$.`, 'soup/Soup.v: Soup');
n('sp.prim', R`$\mathsf{prim}\,T$`, R`The result type holds no end.`, R`A main thread returning an end would leave that end's partner waiting.`, R`$\mathsf{main}$ returning an end.`, R`$\mathsf{prim}\,\ast$.`, 'soup/State.v: sp_prim');
n('sp.rel', R`Every thread live`, R`$\forall t.\ q(t) \in E[\kappa_L]^W_n\llbracket K_t(A) \vdash U_t\rrbracket^{\varnothing}$, where $K_t(A)$ restricts $A$ to the ends held by $t$.`, R`The per-thread live relation excludes internal divergence and infinite chains of spawns.`, DEF, R`$q(0) \in E[\kappa_L]\llbracket K_0(A) \vdash T\rrbracket^{\varnothing}$.`, 'soup/State.v: sp_rel');
n('sp.ty', R`$U_t \in \{T, \ast\}$`, R`Each thread returns at $T$ or at $\ast$.`, R`A thread that returns has a value in $V$ at $U_t$, and for $U_t \in \{T, \ast\}$ with $\mathsf{prim}\,T$ that value holds no end, which the termination argument uses.`, R`Without it, a finished thread could still hold an end.`, R`$\mathsf{main}$ at $T$, spawned threads at $\ast$.`, 'soup/State.v: sp_ty');
n('sp.fuel', R`Every thread fueled`, R`$\forall t.\ q(t) \in F^N_n\llbracket\mathsf{thread}\rrbracket(K_t(\Pi), \mathsf{ctrs}\,K\,t, tk_t)$.`, R`Counters of the fuel layer are read from $K$, so they are the same at every level.`, DEF, R`$q(0) \in F^N_n\llbracket\mathsf{thread}\rrbracket(\ldots)$.`, 'soup/State.v: sp_fuel');
n('sp.pts', R`Points of $A$ from $K$`, R`$\forall o.\ \mathsf{pt}(A\,o) = \mathsf{pt}(K\,o)$.`, R`Points are fixed outside the index.`, DEF, R`$A(a) = S@\rho$ and $K(a) = (0, \rho, 2)$.`, 'soup/State.v: sp_pts');
n('sp.dom', R`$\mathrm{dom}\,\Pi = \mathrm{dom}\,K$`, R`Protocols exist exactly for the held ends.`, R`The lock-free argument finds the protocol of an end of $K$, and of its partner, to decide idleness, and a synchronization updates $\Pi$ and $K$ together.`, R`Without it, a held end could lack a protocol and idleness of a waiting end would be undefined.`, R`$\mathrm{dom}\,\Pi = \mathrm{dom}\,K$.`, 'soup/State.v: sp_dom');
n('sp.owner', R`Holders exist`, R`$\forall o.\ K(o) = (t, \_, \_) \Rightarrow t \in \mathrm{dom}\,q$.`, R`A thread waiting on an end needs its partner's holder to be a thread of $q$, so the dependency of waiting threads is a relation on threads.`, R`Without it, an end could be held by a thread that no longer exists, and its partner would wait forever.`, R`$K(a) = (0, \rho, 2)$ with $q(0)$ defined.`, 'soup/State.v: sp_owner');
n('sp.closed', R`Held ends restricted or interface`, R`$\forall o \in \mathrm{dom}\,K.\ \mathsf{ech}\,o \in C \lor o \in \mathrm{dom}\,\Sigma$.`, R`For $\Sigma = \varnothing$ every held end is restricted, which gives both ends of every acted channel to the soup, and composition splits held ends by it.`, R`Without it, a closed process could hold an end whose partner nobody holds, and its holder would wait forever.`, R`For $\Sigma = \varnothing$, $\mathsf{ech}\,o \in C$.`, 'soup/State.v: sp_closed');
n('sp.pair', R`Restricted partners held`, R`$\forall o \in \mathrm{dom}\,K.\ \mathsf{ech}\,o \in C \Rightarrow \overline{o} \in \mathrm{dom}\,K$.`, R`The partner of an internal end is held by some thread.`, DEF, R`Both ends of $c$ in the pair of closes.`, 'soup/State.v: sp_pair');
n('sp.sdual', R`Restricted pairs dual`, R`$A(o) = S@x \land A(\overline{o}) = S'@x' \land \mathsf{ech}\,o \in C \Rightarrow x' = \overline{x} \land \mathsf{sdual}\,S\,S'$.`, R`Internal partners sit at dual points with dual session types.`, DEF, R`$x' = \overline{x}$.`, 'soup/State.v: sp_sdual');
n('sp.pdual', R`Restricted protocols dual`, R`$\Pi(o) = P \land \Pi(\overline{o}) = P' \land \mathsf{ech}\,o \in C \Rightarrow P' \simeq \overline{P}$.`, R`Lock-free adequacy reads idleness off $\Pi$, and duality transfers idleness across a pair.`, DEF, R`$\Pi(c^{-}) \simeq \overline{\Pi(c^{+})}$.`, 'soup/State.v: sp_pdual');
n('sp.sig', R`Interface entries in $A$`, R`$\Sigma(o) = y \Rightarrow A(o) = y$.`, R`Restricting a cut makes its channels internal, and their dual entries in $A$ come from $\Sigma$ through this condition.`, R`Without it, a channel restricted at composition could have non-dual entries in $A$.`, R`$A(c^{+}) = \Sigma(c^{+})$.`, 'soup/State.v: sp_sig');
n('sp.psig', R`Interface protocols in $\Pi$`, R`$\Sigma(o) = S@x \Rightarrow \Pi(o) = S$.`, R`At composition the cut's protocols come from $\Sigma$, which typing makes exactly dual.`, DEF, R`$\Pi(o) = S$.`, 'soup/State.v: sp_psig');
n('sp.fin', R`Finite counters`, R`$\forall o.\ K(o) = (\_, \_, f) \Rightarrow f \in \mathbb{N}$.`, R`The termination measure reads every counter as a natural number.`, DEF, R`$K(a) = (0, \rho, 2)$.`, 'soup/State.v: sp_fin');
n('sp.lfsem', R`$\Sigma \Vvdash_W p : T$`, R`$\exists N \in \mathbb{N}, a.\ \mathsf{erase}(q_a) = p \land \forall n.\ a \in S^{N,W}_n\llbracket\Sigma \vdash T\rrbracket$.`, R`The soup alone suffices, and absence of internal divergence of the soup gives what a process conjunct would.`, DEF, R`The lock-free fundamental theorem concludes it.`, 'soup/Soup.v: lf_sem');
n('sp.exists-before-forall', R`$\exists$ before $\forall n$`, R`$N$ and the state $a$ are fixed before the level quantifier.`, R`Ownership, points and counters are then the same at every level.`, R`A placement chosen per level lets the main thread starve in every fair run.`, R`$\exists N\,a.\ \ldots \forall n$.`, 'soup/Soup.v: lf_sem');
n('sp.next', R`$\mathsf{lf\_next}$`, R`$\mathsf{lf\_next}\,N\,(q, K, tk)\,ev\,q' = (q', \mathsf{own\_next}\,N\,ev\,K, \mathsf{tk\_next}\,ev\,tk)$.`, R`Creation places new ends with counter $N$, actions move and refill, hand-overs move with counter minus one, links spend a ticket and rename, spawns split tickets, all independent of the level.`, DEF, R`One step of the soup along an event.`, 'soup/Soup.v: lf_next');
// new symbols
n('sr.FE', R`Fuel $F^N_n\llbracket\sigma \triangleright d ; r\rrbracket(\Pi, \varphi, tk)$`, R`The fuel predicate at refill $N$ and level $n$.`, R`It bounds postponement and link chatter per thread, independent of points.`, DEF, R`$F^{3}_n\llbracket\mathsf{thread} \triangleright \infty ; 0\rrbracket(\Pi, \varphi, 0)$.`, 'fuel/Fuel.v: FuelE');
n('sr.FV', R`Fueled values $FV^N_n\llbracket\sigma\rrbracket(\Pi, \varphi)$`, R`The value predicate of fuel at refill $N$ and level $n$.`, R`Values carry the protocols and counters of their ends.`, DEF, R`$FV\llbracket(S@x)^2\rrbracket(\{o \mapsto S\}, \{o \mapsto 3\})$.`, 'fuel/Fuel.v: Vfuel, Vty');
n('sr.act', R`$\mathsf{act}\,o$`, R`The common premise of every action on $o$, F-Wait and F-Tick.`, R`Send, receive, close, select and branch share it.`, DEF, R`$\mathsf{act}\,a$ at $\varphi = \{a \mapsto 0, b \mapsto 1\}$ holds.`, 'fuel/Fuel.v: f_act');
n('sr.vthunk', R`$\mathsf{Vthunk}^W_n(\Theta)$`, R`The predicate of a spawned thunk owning $\Theta$.`, R`A spawned thunk needs neither lower nor upper point.`, DEF, R`$\lambda u.\,\mathsf{close}\,d' \in \mathsf{Vthunk}_n(\{d'\})$.`, 'relation/Relation.v: Vthunk');
n('sr.thunk', R`$\mathsf{thunk}(e)$`, R`$\mathsf{thunk}(e) = \lambda\_.\,e[!e]$.`, R`Forcing $!e$ steps to $e[!e]$, which the thunk delays by one $\lambda$.`, DEF, R`$\mathsf{thunk}(\mathsf{force}\,f) = \lambda\_.\,\mathsf{force}\,(!\mathsf{force}\,f)$.`, 'relation/Relation.v: thunk');
n('sr.size', R`$\mathsf{size}\,T$`, R`The size of a type, with a box counting $3 + \mathsf{size}\,U$.`, R`It makes $V$ at a box read $V$ at the smaller thunk type.`, DEF, R`$\mathsf{size}\,\ast = 1$.`, 'relation/Relation.v: tsize');
n('sr.irred', R`$\mathsf{irred}\,e$`, R`$e$ takes no step, $\neg\exists \alpha, e'.\ e \xrightarrow{\alpha} e'$.`, R`Values and stuck terms are irreducible.`, DEF, R`$\mathsf{irred}\,\ast$.`, 'lang/Semantics.v: irred');
n('sr.ready', R`$\mathsf{ready}_W(\Theta \mid F, t)$`, R`Readiness of a term with environment $\Theta$ and future $F$ in world $W$.`, R`It excludes circular waiting.`, DEF, R`$\mathsf{ready}_W(\{c^{+} \mapsto \mathsf{Close}@\rho\} \mid \varnothing, \mathsf{close}\,c^{+})$.`, 'relation/Readiness.v: ready_t');
n('sr.readyp', R`$\mathsf{ready}_W(\Sigma, p)$`, R`Readiness of a process with interface $\Sigma$ in world $W$.`, R`It excludes circular waiting across the interface.`, DEF, R`$\mathsf{ready}_W(\varnothing, (\varnothing, \{\ast\}))$.`, 'relation/Readiness.v: ready_p');
n('sr.obl', R`$\mathsf{Obl}_\alpha(e')$`, R`The obligation of the step label $\alpha$, one of O-Beta to O-Link.`, R`Each label has its own obligation, read off the label.`, DEF, R`$\mathsf{Obl}_{\beta}(e') = $ O-Beta.`, 'relation/Relation.v: Eobl');
n('sr.pobl', R`$\mathsf{Pobl}_{ev}(p')$`, R`The obligation of the event $ev$, one of Q-Tau to Q-Link.`, R`Each event has its own obligation, read off the event.`, DEF, R`$\mathsf{Pobl}_{ev}$ is Q-Tau for an internal event.`, 'relation/Relation.v: Pobl');
n('sr.fobl', R`$\mathsf{Fobl}^N_\alpha(e')$`, R`The fuel obligation of the step label $\alpha$, one of F-Beta to F-Link.`, R`Each label has its own fuel update.`, DEF, R`$\mathsf{Fobl}$ of a send is F-Send.`, 'fuel/Fuel.v: Fobl');
n('sr.fuseok', R`$\mathsf{fuse\_ok}\,h\,D\,\Sigma\,p$`, R`$(h, D)$ is an admissible fusion of the held ends of $p$ with interface $\Sigma$.`, R`One notion covers renaming, internalizing pairs and the renaming of a link.`, DEF, R`$\mathsf{fuse\_ok}\,\mathsf{id}\,\varnothing\,\Sigma\,p$.`, 'relation/Relation.v: fuse_ok');
n('sr.sdrop', R`$\mathsf{sdrop}\,D\,\Sigma$`, R`$\Sigma$ without the ends of the channels $D$.`, R`The channels of $D$ become restricted and leave the interface.`, DEF, R`$\mathsf{sdrop}\,\{c\}\,\{c^{+}, c^{-}, d^{+}\} = \{d^{+}\}$.`, 'relation/Relation.v: sdrop');
n('sr.pfuse', R`$\mathsf{pfuse}\,h\,D\,p$`, R`$p$ renamed by $h$ with the channels $D$ added to the restricted set.`, R`It is the process after the fusion.`, DEF, R`$\mathsf{pfuse}\,\mathsf{id}\,\{c\}\,(C, E) = (C \cup \{c\}, E)$.`, 'relation/Relation.v: pfuse');
n('sr.pirred', R`$\mathsf{pirred}\,p$`, R`$p$ takes no process step.`, R`P-Stop applies exactly to irreducible processes.`, DEF, R`$\mathsf{pirred}\,(\varnothing, \{\ast\})$.`, 'lang/Process.v: pirred');
n('sr.held', R`Held ends`, R`$\mathsf{held} = \{o \mid o \in \mathrm{dom}\,\Sigma \lor \mathsf{ech}\,o \in C\}$.`, R`A process holds its interface ends and both ends of every restricted channel.`, DEF, R`For $\Sigma = \{d^{+}\}$ and $C = \{c\}$, $\mathsf{held} = \{d^{+}, c^{+}, c^{-}\}$.`, 'relation/Relation.v: pheld');
n('sr.gch', R`$\mathsf{gch}_h$`, R`$\mathsf{gch}_h(c) = \mathsf{ech}(h(c^{+}))$, the channel map induced by $h$.`, R`Restricted sets are sets of channels, so $h$ acts on them through its action on $c^{+}$.`, DEF, R`$\mathsf{gch}_{\mathsf{id}}(c) = c$.`, 'relation/Relation.v: gch');
n('sr.tenv-erase', R`$|\Delta|$`, R`The ends of $\Delta$ with their session types and points, each entry $(S@x)^{a}$ becoming $S@x$.`, R`$E$ reads ends only, and no credit.`, DEF, R`$|c^{+} : (S@\rho)^{3},\ 0 : T| = \{c^{+} \mapsto S@\rho\}$.`, 'relation/Relation.v: tenv_erase');
n('sr.fvagg', R`Products, sums and existentials in $FV$`, R`$\otimes$ splits $\Pi$ and $\varphi$ disjointly between its parts, $\oplus$ checks the injected part, and $\exists$ checks its body.`, R`Only ends and closures carry credits, so these types only pass $\Pi$ and $\varphi$ on.`, DEF, R`$(S@x)^{2} \otimes \ast$ gives $o$ to the first part.`, 'fuel/Fuel.v: Vty');
n('sr.ctrs', R`$\mathsf{ctrs}\,K\,t$`, R`The counters of the ends held by thread $t$, read from $K$.`, R`Fuel of a soup thread uses exactly these counters.`, DEF, R`$\mathsf{ctrs}\,K\,0 = \{a \mapsto 2\}$.`, 'soup/State.v: ctrs');

// ---- signatures and arguments ----
const A = (name, meaning) => ({ name, meaning });
const aW = A(R`W`, R`the world, $W \in \mathsf{World}$`);
const an = A(R`n`, R`the level, $n \in \mathbb{N}$`);
const aTh = A(R`\Theta`, R`the environment, a finite map $\mathsf{End} \rightharpoonup \mathsf{STy} \times \mathsf{Point}$`);
const aT = A(R`T`, R`the type, $T \in \mathsf{Ty}$`);
const aF = A(R`F`, R`the future, a finite set of points`);
const ae = A(R`e, e'`, R`a term and its successor, $e, e' \in \mathsf{Expr}$`);
const ao = A(R`o`, R`the subject end, $o \in \mathsf{End}$`);
const aSg = A(R`\Sigma`, R`the interface, a finite map $\mathsf{End} \rightharpoonup \mathsf{STy} \times \mathsf{Point}$`);
const ap = A(R`p`, R`the process, $p = (C, E) \in \mathsf{Proc}$`);
const ak = A(R`\kappa`, R`the cost table`);
const aPi = A(R`\Pi`, R`the protocols, a finite map $\mathsf{End} \rightharpoonup \mathsf{STy}$`);
const aphi = A(R`\varphi`, R`the counters, a finite map $\mathsf{End} \rightharpoonup \mathbb{N} \cup \{\infty\}$`);
const atk = A(R`tk`, R`the tickets of the thread, $tk \in \mathbb{N}$`);
const aN = A(R`N`, R`the refill, $N \in \mathbb{N} \cup \{\infty\}$`);
const aK = A(R`K`, R`the ownership map of the soup state`);
const ax = A(R`x`, R`the point of the subject, $x \in \mathsf{Point}$`);
const aS0 = A(R`S_0, S`, R`the session type of the subject and its continuation after the head`);
const ENV = R`\mathsf{Env}`;
const OBL = (nm) => R`\mathsf{${nm}} : \mathsf{Expr} \to \mathsf{Prop}`;
const SIGV = R`v \in V[\kappa]^{W}_{n}\llbracket \Theta \vdash T \rrbracket`;
const SIGE = R`e \in E[\kappa]^{W}_{n}\llbracket \Theta \vdash T \rrbracket^{F}`;
const SIGP = R`p \in P[\kappa]^{W}_{n}\llbracket \Sigma \vdash T \rrbracket`;
const SIGF = R`e \in F^{N}_{n}\llbracket \sigma \triangleright d ; r \rrbracket(\Pi, \varphi, tk)`;
const SIGS = R`a \in S^{N,W}_{n}\llbracket \Sigma \vdash T \rrbracket`;
const fuelArgs = [aN, an, A(R`\sigma`, R`the result, a credited type or $\mathsf{thread}$`), A(R`d`, R`the frame, $d \in \mathbb{N} \cup \{\infty\}$`), A(R`r`, R`the reserve, $r \in \mathbb{N}$`), aPi, aphi, atk, A(R`e`, R`the term`)];
const soupArgs = [aN, aW, an, aSg, aT, A(R`a = (q, K, tk)`, R`the soup state, with $q = (C, M)$ a configuration`)];
const vArgs = [ak, aW, an, aTh, aT, A(R`v`, R`the value`)];
const eArgs = [ak, aW, an, aTh, aT, aF, A(R`e`, R`the term`)];
const pArgs = [ak, aW, an, aSg, aT, ap];
const oblArgs = [aW, an, aTh, aT, aF, ae];
const qArgs = [aW, an, aSg, aT, A(R`p, p'`, R`the process before and after the step, $p = (C, E)$ and $p' = (C', E')$`)];

sa('ct.table', R`\kappa \in \mathsf{CTable} \subseteq \mathbb{N}^{6}`, [A(R`\kappa_\beta, \ldots, \kappa_{take}`, R`the costs of $\beta$, creation, spawn, link, give and take`)]);
sa('ct.take-pos', R`1 \leq \kappa_{take} : \mathsf{Prop}`, [ak]);
sa('ct.give-pos', R`\kappa_\beta = 0 \Rightarrow 1 \leq \kappa_{give} : \mathsf{Prop}`, [ak]);
sa('ct.give-take', R`\kappa_{give} \leq \kappa_{take} : \mathsf{Prop}`, [ak]);
sa('ct.DF', R`\kappa_{DF} = (1,1,1,0,0,1) \in \mathsf{CTable}`, []);
sa('ct.L', R`\kappa_L = (0,0,0,0,1,1) \in \mathsf{CTable}`, []);
sa('ct.beta', R`\kappa_\beta \in \mathbb{N}`, [ak]);
sa('ct.new', R`\kappa_{new} \in \mathbb{N}`, [ak]);
sa('ct.spawn', R`\kappa_{spawn} \in \mathbb{N}`, [ak]);
sa('ct.link', R`\kappa_{link} \in \mathbb{N}`, [ak]);
sa('ct.give', R`\kappa_{give} \in \mathbb{N}`, [ak]);
sa('ct.takek', R`\kappa_{take} \in \mathbb{N}`, [ak]);
sa('ct.sync', R`\kappa(\cdot) : \mathsf{Event} \to \mathbb{N}`, [ak, A(R`ev`, R`an event of the instrumented semantics`)]);
sa('rel.atcost', R`e' \text{ at } \Theta' : \mathsf{Prop}`, [A(R`e'`, R`the successor`), A(R`\Theta'`, R`its environment`), A(R`\kappa(\alpha)`, R`the cost of the step label $\alpha$`), A(R`X`, R`the least fixpoint under construction at level $n$`)]);
sa('rel.lfp', R`X : \mathsf{World} \to ${ENV} \to \mathsf{Ty} \to \mathcal{P}(\mathsf{Point}) \to \mathsf{Expr} \to \mathsf{Prop}`, [A(R`X`, R`the least relation closed under the clauses of level $n$`)]);
sa('V-Unit', SIGV, vArgs);
sa('V-Sess', SIGV, [...vArgs, A(R`o`, R`the end the value is`), A(R`S'`, R`the session type of $o$ in $\Theta$, with annotations`)]);
sa('V-Sess.exact', R`\Theta = \{o \mapsto S'@x\} : \mathsf{Prop}`, [aTh, ao, A(R`S'@x`, R`the entry of $o$, at the point $x$ of the type`)]);
sa('V-Prod', SIGV, [...vArgs, A(R`\Theta_1, \Theta_2`, R`the disjoint parts owned by $v_1$ and $v_2$`)]);
sa('V-Prod.split', R`\Theta = \Theta_1 \uplus \Theta_2 : \mathsf{Prop}`, [aTh, A(R`\Theta_i`, R`the part of component $i \in \{1,2\}$`)]);
sa('V-Sum', SIGV, [...vArgs, A(R`i`, R`the side of the injection, $i \in \{1, 2\}$`)]);
sa('V-Arrow.exact', R`\mathrm{dom}\,\Theta = \mathsf{fends}(e) : \mathsf{Prop}`, [aTh, A(R`e`, R`the body of the closure`)]);
sa('V-Arrow.lb', R`l \preccurlyeq \mathsf{heads}\,\Theta : \mathsf{Prop}`, [A(R`l`, R`the lower point of the arrow, a point or absent`), aTh]);
sa('V-Arrow.kripke', R`\forall W' \sqsupseteq W`, [aW, A(R`W'`, R`any extension of $W$`)]);
sa('V-Arrow.level', R`j + \kappa_\beta \leq n : \mathsf{Prop}`, [A(R`j`, R`the level at which the body is read`), an]);
sa('V-Arrow.ub', R`W' \vdash u \prec F : \mathsf{Prop}`, [A(R`u`, R`the upper point of the arrow, a point or absent`), A(R`F`, R`the future of the call, any set of points above $u$`)]);
sa('V-Arrow.body', R`e[w] \in E^{W'}_{j}\llbracket \Theta \cup \Theta' \vdash U \rrbracket^{F}`, [A(R`w`, R`the argument, in $V^{W'}_j\llbracket\Theta' \vdash T\rrbracket$`), A(R`\Theta'`, R`the ends of the argument, disjoint from $\Theta$`), A(R`U`, R`the result type`)]);
sa('V-Thunk.empty', R`F = \varnothing`, [A(R`F`, R`the future of the spawned body`)]);
sa('V-Box.empty', R`\Theta = \varnothing : \mathsf{Prop}`, [aTh]);
sa('V-Box.noends', R`\mathsf{fends}(e) = \varnothing : \mathsf{Prop}`, [A(R`e`, R`the body of the box`)]);
sa('V-Box.kripke', R`\forall W' \sqsupseteq W`, [aW, A(R`W'`, R`any extension of $W$`)]);
sa('V-Box.inst', R`W' \vdash C[\bar x] : \mathsf{Prop}`, [A(R`C`, R`the box constraint over $m$ point variables`), A(R`\bar x`, R`the point instance, $\bar x \in \mathsf{Point}^m$`)]);
sa('V-Box.hc', R`\forall s \in \bar s.\ \mathsf{hcontractive}\,s`, [A(R`\bar s`, R`the session instance, $\bar s \in \mathsf{STy}^k$`)]);
sa('V-Box.thunk', R`\mathsf{thunk}(e) \in V^{W'}_{n}\llbracket \varnothing \vdash \ast \multimap^{u[\bar x]} U[\bar s][\bar x] \rrbracket`, [A(R`u[\bar x]`, R`the upper point instantiated at $\bar x$`), A(R`U[\bar s][\bar x]`, R`the result instantiated at $\bar s$ and $\bar x$`)]);
sa('V-Ex.lb', R`l \preccurlyeq \mathsf{heads}\,\Theta : \mathsf{Prop}`, [A(R`l`, R`the lower bound, a point, absent or $\bot$`), aTh]);
sa('V-Ex.witness', R`\exists \bar x \in \mathsf{Point}^{m}.\ W \vdash C[\bar x] \land v \in V^{W}_{n}\llbracket \Theta \vdash T[\bar x] \rrbracket`, [A(R`\bar x`, R`the witness points`), A(R`C`, R`the constraint of the existential`), A(R`T[\bar x]`, R`the body type at the witness`)]);
sa('rel.vsize', R`V : \mathbb{N} \to \mathsf{World} \to ${ENV} \to \mathsf{Ty} \to \mathsf{Expr} \to \mathsf{Prop}`, [an, A(R`\mathsf{size}\,T`, R`the inner recursion measure`)]);
sa('E.zero', R`e \in E^{W}_{0}\llbracket \Theta \vdash T \rrbracket^{F}`, eArgs);
sa('E.kripke', R`\forall W_1 \sqsupseteq W`, [aW, A(R`W_1`, R`any extension of $W$, the world at which the clauses are read`)]);
sa('E.stop', R`\mathsf{irred}\,e \Rightarrow e \in V^{W_1}_{n+1}\llbracket \Theta \vdash T \rrbracket`, [A(R`e`, R`the term`), A(R`W_1`, R`the extension of $W$`)]);
sa('E.ready', R`\neg\mathsf{irred}\,e \Rightarrow \mathsf{ready}_{W_1}(\Theta \mid F, e)`, [A(R`e`, R`the term`), A(R`W_1`, R`the extension of $W$`)]);
sa('E.step', R`\forall \alpha, e'.\ e \xrightarrow{\alpha} e' \Rightarrow \mathsf{Obl}_\alpha(e')`, [A(R`\alpha`, R`a step label`), A(R`e'`, R`the successor`)]);
sa('O-Beta', OBL('o\\_beta'), oblArgs);
sa('O-New', R`\mathsf{o\_new} : \mathsf{Chan} \to \mathsf{Expr} \to \mathsf{Prop}`, [...oblArgs, A(R`c`, R`the new channel name`), A(R`a`, R`a root outside $A_W$`), A(R`S`, R`the session type of $c^{+}$`), A(R`\pi`, R`the position of $c^{+}$`), A('C', R`the facts of the creation`)]);
sa('O-New.cfresh', R`c^{\pm} \notin \mathrm{dom}\,\Theta : \mathsf{Prop}`, [A(R`c`, R`the new channel name`), aTh]);
sa('O-New.forall', R`\forall a \in \mathsf{Root}.\ a \notin A_W \Rightarrow \ldots`, [A(R`a`, R`a candidate root`)]);
sa('O-New.gfresh', R`a \notin A_W : \mathsf{Prop}`, [A(R`a`, R`the root`), aW]);
sa('O-New.grow', R`\exists S, \pi, C.\ \pi \in \{a\} \cup \{x\cdot\kappa\} \land \mathsf{strict}(W \oplus C)`, [A(R`\pi`, R`the position, the root $a$ or a field of a point $x$ of $W$`), A('C', R`the facts added to $W$`)]);
sa('O-New.dual', R`\Theta[c^{+} \mapsto S@\pi,\ c^{-} \mapsto \overline{S}@\overline{\pi}] \in ${ENV}`, [A(R`c`, R`the new channel`), A(R`S`, R`the chosen session type`), A(R`\pi`, R`the position`)]);
sa('O-Spawn', R`\mathsf{o\_spawn} : \mathsf{Val} \to \mathsf{Expr} \to \mathsf{Prop}`, [...oblArgs, A(R`v`, R`the spawned thunk`), A(R`\Theta_M, \Theta_r`, R`the parts of the child and of the parent`)]);
sa('O-Spawn.split', R`\exists \Theta_M, \Theta_r.\ \Theta = \Theta_M \uplus \Theta_r`, [A(R`\Theta_M`, R`the child's ends`), A(R`\Theta_r`, R`the parent's ends`)]);
sa('O-Spawn.transfer', R`\mathrm{dom}\,\Theta_M = \mathsf{fends}(v)`, [A(R`\Theta_M`, R`the part that leaves`), A(R`v`, R`the value that leaves, the thunk or the payload`)]);
sa('O-Spawn.thunk', R`v \in \mathsf{Vthunk}^{W}_{n}(\Theta_M)`, [A(R`v`, R`the thunk`), A(R`\Theta_M`, R`its ends`)]);
sa('O-Send', R`\mathsf{o\_send} : \mathsf{End} \to \mathsf{Val} \to \mathsf{Expr} \to \mathsf{Prop}`, [...oblArgs, ao, A(R`w`, R`the payload`), ax, aS0, A(R`m, U, b`, R`the number of point variables, the type and the credit of the payload`)]);
sa('O-Send.split', R`\Theta \setminus o = \Theta_M \uplus \Theta_r`, [A(R`\Theta_M`, R`the payload's ends`), A(R`\Theta_r`, R`the remaining ends`)]);
sa('O-Send.payload', R`w \in V^{W}_{n-\kappa_{give}}\llbracket \Theta_M \vdash U[x\cdot\bar\imath] \rrbracket`, [A(R`U[x\cdot\bar\imath]`, R`the payload type with its point variables at the fields $x\cdot i$`)]);
sa('O-Send.shift', R`\Theta_r[o \mapsto S@x^{+}] \in ${ENV}`, [ao, A(R`x^{+}`, R`the next point of $o$`)]);
sa('O-Recv', R`\mathsf{o\_recv} : \mathsf{End} \to \mathsf{Val} \to \mathsf{Expr} \to \mathsf{Prop}`, [...oblArgs, ao, A(R`w`, R`the received value`), ax, aS0]);
sa('O-Recv.forall', R`\forall j \in \mathbb{N}, \Theta_{in}.\ j + \kappa_{take} \leq n \land \Theta_{in} \mathbin{\#} \Theta \land w \in V_j\llbracket\Theta_{in} \vdash U[x\cdot\bar\imath]\rrbracket`, [A(R`j`, R`the level of the incoming value`), A(R`\Theta_{in}`, R`the ends it brings`)]);
sa('O-Recv.level', R`e' \in E^{W}_{j}\llbracket \Theta[o \mapsto S@x^{+}] \cup \Theta_{in} \vdash T \rrbracket^{F}`, [A(R`j`, R`the level of the incoming value`), A(R`\Theta_{in}`, R`the received ends`)]);
sa('O-Close', R`\mathsf{o\_close} : \mathsf{End} \to \mathsf{Expr} \to \mathsf{Prop}`, [...oblArgs, ao]);
sa('O-Select', R`\mathsf{o\_select} : \mathsf{End} \to \mathbb{B} \to \mathsf{Expr} \to \mathsf{Prop}`, [...oblArgs, ao, A(R`i`, R`the selected choice`)]);
sa('O-Branch', R`\mathsf{o\_branch} : \mathsf{End} \to \mathbb{B} \to \mathsf{Expr} \to \mathsf{Prop}`, [...oblArgs, ao, A(R`i`, R`the received choice`)]);
sa('O-Link', R`\mathsf{o\_link} : \mathcal{P}_{\mathrm{fin}}(\mathsf{End}) \to \mathsf{Expr} \to \mathsf{Prop}`, [...oblArgs, A(R`\{o_1, o_2\}`, R`the linked ends`)]);
sa('O-Link.distinct', R`o_1 \neq o_2 : \mathsf{Prop}`, [A(R`o_1, o_2`, R`the linked ends`)]);
sa('O-Link.dual', R`\Theta(o_1) = S_1@x \land \Theta(o_2) = S_2@\overline{x} \land \mathsf{sdual}\,S_1\,S_2`, [A(R`S_1, S_2`, R`the session types of the linked ends`), A(R`x`, R`the point of $o_1$`)]);
sa('rd.stable', R`\mathsf{stable} : \mathsf{Expr} \to \mathsf{Prop}`, [A(R`t`, R`the term`)]);
sa('rd.offered', R`\mathsf{offered} : ${ENV} \to \mathsf{Expr} \to \mathsf{End} \to \mathsf{Prop}`, [aTh, A(R`t`, R`the term`), A(R`o`, R`the end`)]);
sa('rd.value', R`(\forall o.\ \neg\mathsf{offered}_\Theta(t, o)) \Rightarrow t \in \mathsf{Val}`, [A(R`t`, R`the term`)]);
sa('rd.link', R`\mathsf{link} : \mathsf{Expr} \to \mathsf{Prop}`, [A(R`t`, R`the term`), A(R`os`, R`the linked ends of the step`)]);
sa('rd.below-rest', R`\mathsf{below\_rest} : \mathsf{World} \to ${ENV} \to (\mathsf{End} \to \mathsf{Prop}) \to \mathcal{P}(\mathsf{Point}) \to \mathsf{Prop}`, [aW, aTh, A(R`O`, R`the offered ends`), aF]);
sa('rd.below-held', R`\forall o' \notin O.\ \Theta(o') = S'@x' \Rightarrow W \vdash x \prec \overline{x'}`, [A(R`x`, R`the point of an offered end`), A(R`o', x'`, R`a held end that is not offered and its point`)]);
sa('rd.below-future', R`\forall y \in F.\ W \vdash x \prec y`, [A(R`x`, R`the point of an offered end`), A(R`y`, R`a point of the future`)]);
sa('rd.p-stable', R`\mathsf{stable} : \mathsf{Proc} \to \mathsf{Prop}`, [ap]);
sa('rd.p-term', R`(\forall o.\ \neg\mathsf{offered}_\Sigma(p, o)) \Rightarrow \mathsf{terminated}\,p`, [aSg, ap]);
sa('rd.above-offered', R`\mathsf{above\_offered} : \mathsf{World} \to ${ENV} \to (\mathsf{End} \to \mathsf{Prop}) \to \mathsf{Prop}`, [aW, aSg, A(R`o, x`, R`an interface end that is not offered and its point`), A(R`o', x'`, R`an offered end and its point`)]);
sa('P.strict', R`\forall W_1 \sqsupseteq W.\ \mathsf{strict}\,W_1 \Rightarrow \ldots`, [aW, A(R`W_1`, R`any strict extension of $W$`)]);
sa('P.fuse', R`\forall h, D.\ \mathsf{fuse\_ok}\,h\,D\,\Sigma\,p \Rightarrow \ldots`, [A(R`h`, R`a map of ends`), A(R`D`, R`the channels the fusion restricts`)]);
sa('P-Stop', R`\mathsf{pirred}\,p' \Rightarrow \exists v, E.\ p' = (\varnothing, \{v\} \uplus E) \land \ldots`, [A(R`p'`, R`the fused process`), A(R`v`, R`the main thread's value`), A(R`E`, R`the other threads, all $\ast$`)]);
sa('P-Ready', R`\neg\mathsf{pirred}\,p' \Rightarrow \mathsf{ready}_{W_1}(\Sigma', p')`, [A(R`\Sigma', p'`, R`the fused interface and process`), A(R`W_1`, R`the strict extension`)]);
sa('P-Step', R`\forall q, ev, q'.\ \mathsf{erase}\,q = p' \land q \xrightarrow{ev} q' \Rightarrow \mathsf{Pobl}_{ev}(\mathsf{erase}\,q')`, [A(R`q, q'`, R`configurations, $q$ a numbering of the threads of $p'$`), A(R`ev`, R`the event`)]);
sa('fuse.dcomm', R`\forall o.\ h(\overline{o}) = \overline{h(o)}`, [A(R`h`, R`the map of ends`)]);
sa('fuse.inj', R`\forall o_1, o_2 \in \mathsf{held}.\ h(o_1) = h(o_2) \Rightarrow o_1 = o_2`, [A(R`o_1, o_2`, R`held ends of $p$`)]);
sa('fuse.partners', R`h(o_2) = \overline{h(o_1)} \Rightarrow o_2 = \overline{o_1} \lor \mathsf{ech}(h\,o_1) \in D`, [A(R`o_1, o_2`, R`held ends of $p$`), A(R`D`, R`the channels the fusion restricts`)]);
sa('fuse.D', R`D \cap \mathsf{gch}_h[C] = \varnothing`, [A(R`D`, R`the channels the fusion restricts`), A(R`C`, R`the restricted channels of $p$`)]);
sa('fuse.dpairs', R`\mathsf{dpairs} : \mathcal{P}_{\mathrm{fin}}(\mathsf{Chan}) \to ${ENV} \to \mathsf{Prop}`, [A(R`D`, R`the channels`), aSg]);
sa('Q-Tau', R`\mathsf{q\_tau} : \mathsf{Event} \to \mathsf{Proc} \to \mathsf{Prop}`, [...qArgs, A(R`ev`, R`the internal event`)]);
sa('Q-Send', R`\mathsf{q\_send} : \mathsf{End} \to \mathsf{Val} \to \mathsf{Proc} \to \mathsf{Prop}`, [...qArgs, ao, A(R`w`, R`the payload`), A(R`\Sigma_v, \Sigma_r`, R`the interface ends of the payload and the rest`), A(R`\Theta_e, \Sigma_e`, R`the restricted ends that leave and their partners that stay`)]);
sa('Q-Send.theta-e', R`\mathrm{dom}\,\Theta_e = \{o' \in \mathsf{fends}(w) \mid \mathsf{ech}(o') \in C\}`, [A(R`\Theta_e`, R`the restricted ends of the payload`), A(R`w`, R`the payload`), A(R`C`, R`the restricted channels`), A(R`\Sigma_v`, R`the interface ends of the payload`)]);
sa('Q-Send.split', R`\mathsf{send\_split} : ${ENV} \to ${ENV} \to ${ENV} \to \mathsf{Prop}`, [aSg, A(R`\Sigma_e`, R`the partners that join the interface`), A(R`\Theta_e`, R`the extruded ends`)]);
sa('Q-Send.sigma-e', R`\Sigma_e \in ${ENV}`, [A(R`\Sigma_e`, R`the partners of extruded ends`)]);
sa('Q-Recv', R`\mathsf{q\_recv} : \mathsf{End} \to \mathsf{Val} \to \mathsf{Proc} \to \mathsf{Prop}`, [...qArgs, ao, A(R`w`, R`the received value`), A(R`j`, R`the level of the value`), A(R`\Theta_2`, R`the ends it brings`), A(R`\Sigma'`, R`$\Sigma[o \mapsto S@x^{+}]$`)]);
sa('Q-Recv.ok', R`\mathsf{recv\_ok} : ${ENV} \to ${ENV} \to \mathsf{Prop}`, [aSg, A(R`\Theta_2`, R`the incoming ends`)]);
sa('Q-Recv.back', R`\mathsf{recv\_back} : ${ENV} \to ${ENV} \to \mathcal{P}_{\mathrm{fin}}(\mathsf{Chan})`, [aSg, A(R`\Theta_2`, R`the incoming ends`)]);
sa('Q-Recv.env', R`\mathsf{recv\_env} : ${ENV} \to ${ENV} \to ${ENV}`, [aSg, A(R`\Theta_2`, R`the incoming ends`)]);
sa('Q-Link', R`\mathsf{q\_close}, \mathsf{q\_select}, \mathsf{q\_branch}, \mathsf{q\_link}`, qArgs);
sa('sj.at', R`\Delta \vDash^{X}_{W} e : T`, [A(R`\Delta`, R`the linear context of the typing judgment, its ends erased to $|\Delta|$`), A(R`X`, R`a set of points read as the future`), A(R`n, W', \Theta', \gamma`, R`every level, extension, environment of the grounding and grounding`)]);
sa('sj.grel', R`\gamma \in G^{W}_{n}\llbracket \Theta \vdash \Delta \rrbracket`, [A(R`\gamma`, R`a substitution $\mathbb{N} \to \mathsf{Expr}$ for the variables of $\Delta$`), aTh, A(R`\Delta`, R`the linear context`)]);
sa('sj.den', R`\mathsf{den} : (\mathbb{N} \to \mathcal{P}(\mathsf{Point})) \to \mathcal{P}(\mathsf{Point}) \to \mathsf{SFuture} \to \mathcal{P}(\mathsf{Point})`, [A(R`\rho`, R`the denotation of future variables`), A(R`B`, R`the denotation of the flag $\bot$`), A(R`F`, R`the static future`)]);
sa('sj.term', R`\Delta \vDash^{F}_{W} e : T`, [A(R`\Delta`, R`the linear context`), A(R`F`, R`the static future`), aW, A(R`e, T`, R`the term and its type`)]);
sa('sj.proc', R`\Sigma \vDash_{W} p : T`, [aSg, aW, ap, aT]);
sa('fu.zero', SIGF, fuelArgs);
sa('fu.rty', R`\sigma \in \{T^{a}\} \cup \{\mathsf{thread}\}`, [A(R`T^{a}`, R`a credited type`)]);
sa('fu.frame', R`d \in \mathbb{N} \cup \{\infty\}`, []);
sa('fu.reserve', R`r \in \mathbb{N}`, []);
sa('fu.Pi', R`\Pi : \mathsf{End} \rightharpoonup \mathsf{STy}`, []);
sa('fu.phi', R`\varphi : \mathsf{End} \rightharpoonup \mathbb{N} \cup \{\infty\}`, []);
sa('fu.tk', R`tk \in \mathbb{N}`, []);
sa('fu.refill-kripke', R`N \sqsubseteq_{\mathsf{rle}} N' : \mathsf{Prop}`, [A(R`N, N'`, R`refills in $\mathbb{N} \cup \{\infty\}$`)]);
sa('fu.rename', R`g : \mathsf{End} \to \mathsf{End} \text{ injective on } \mathrm{dom}\,\Pi, \mathrm{dom}\,\varphi`, [A(R`g`, R`the renaming`)]);
sa('fu.val', R`g(e) \in \mathsf{Val} \Rightarrow r \leq tk \land g(e) \in FV^{N'}_{n+1}\llbracket \sigma \rrbracket(g\Pi, g\varphi)`, [A(R`g, N'`, R`the renaming and the refill`)]);
sa('fu.step', R`\forall \alpha, e'.\ g(e) \xrightarrow{\alpha} e' \Rightarrow \mathsf{Fobl}^{N'}_{\alpha}(e')`, [A(R`\alpha, e'`, R`the step label and the successor`)]);
sa('fu.oneclock', R`\text{cost}(\alpha) = 1`, [A(R`\alpha`, R`every step label`)]);
sa('F-Wait', R`\neg\mathsf{idle}(\Pi\,o)`, [aPi, ao]);
sa('F-Tick', R`\mathsf{fspare}\,\Pi\,\varphi\,(\mathrm{dom}\,\varphi \setminus \{o\})`, [aPi, aphi, ao]);
sa('F-Tick.frame', R`1 \leq d`, [A(R`d`, R`the frame`)]);
sa('fu.refillop', R`\mathsf{refill} : (\mathbb{N} \cup \{\infty\}) \to \mathsf{End} \to \mathsf{CEnv} \to \mathsf{CEnv}`, [aN, ao, aphi]);
sa('fu.idle', R`\mathsf{idle} : \mathsf{STy} \to \mathsf{Prop}`, [A(R`S`, R`a session type`)]);
sa('F-Beta', R`\mathsf{f\_beta} : \mathsf{Expr} \to \mathsf{Prop}`, [...fuelArgs.slice(0, 8), A(R`e'`, R`the successor`)]);
sa('F-New', R`\mathsf{f\_new} : \mathsf{Chan} \to \mathsf{Expr} \to \mathsf{Prop}`, [A(R`c`, R`the new channel`), A(R`S`, R`the protocol of $c^{+}$`), A(R`e'`, R`the successor`)]);
sa('F-New.fresh', R`\mathsf{ffresh} : \mathsf{Chan} \to \mathsf{PEnv} \to \mathsf{CEnv} \to \mathsf{Prop}`, [A(R`c`, R`the new channel`), aPi, aphi]);
sa('F-New.cnew', R`\mathsf{cnew}\,N\,c\,\varphi = \varphi[c^{+} \mapsto N, c^{-} \mapsto N]`, [aN, A(R`c`, R`the new channel`), aphi]);
sa('F-Spawn', R`\mathsf{f\_spawn} : \mathsf{Val} \to \mathsf{Expr} \to \mathsf{Prop}`, [A(R`v`, R`the thunk`), A(R`M`, R`$\mathsf{fends}(v)$, the handed ends`), A(R`e'`, R`the parent's successor`)]);
sa('F-Spawn.held', R`M \subseteq \mathrm{dom}\,\varphi`, [A(R`M`, R`the handed ends`)]);
sa('fu.fspare', R`\mathsf{fspare} : \mathsf{PEnv} \to \mathsf{CEnv} \to \mathcal{P}_{\mathrm{fin}}(\mathsf{End}) \to \mathsf{Prop}`, [aPi, aphi, A(R`X`, R`the ends that must spare a unit`)]);
sa('F-Spawn.child', R`v\,\ast \in F^{N}_{n}\llbracket \mathsf{thread} \triangleright \infty ; 0 \rrbracket(\Pi|_M, \mathsf{fhand}\,M\,\varphi, \lceil tk/2 \rceil)`, [A(R`v\,\ast`, R`the child thread`), A(R`M`, R`the handed ends`)]);
sa('fu.fhand', R`\mathsf{fhand} : \mathcal{P}_{\mathrm{fin}}(\mathsf{End}) \to \mathsf{CEnv} \to \mathsf{CEnv}`, [A(R`M`, R`the handed ends`), aphi]);
sa('F-Spawn.tickets', R`(\lceil tk/2 \rceil, \lfloor tk/2 \rfloor)`, [atk]);
sa('F-Send', R`\mathsf{f\_send} : \mathsf{End} \to \mathsf{Val} \to \mathsf{Expr} \to \mathsf{Prop}`, [ao, A(R`w`, R`the payload`), A(R`M`, R`$\mathsf{fends}(w)$`), A(R`T, b`, R`the payload type and credit`), A(R`S`, R`the continuation protocol`)]);
sa('F-Send.notsubj', R`M \subseteq \mathrm{dom}\,\varphi \setminus \{o\}`, [A(R`M`, R`the handed ends`), ao]);
sa('F-Send.payload', R`w \in FV^{N}_{n}\llbracket T^{b} \rrbracket(\Pi|_M, \mathsf{fhand}\,M\,\varphi)`, [A(R`w`, R`the payload`), A(R`T^{b}`, R`the raw payload type at the credit of the protocol`)]);
sa('F-Recv', R`\mathsf{f\_recv} : \mathsf{End} \to \mathsf{Val} \to \mathsf{Expr} \to \mathsf{Prop}`, [ao, A(R`w`, R`the received value`), A(R`j, \Pi_i, \varphi_i`, R`its level, protocols and counters`)]);
sa('F-Recv.forall', R`\forall j \leq n, \Pi_i, \varphi_i.\ w \in FV^{N}_{j}\llbracket T^{b} \rrbracket(\Pi_i, \varphi_i) \Rightarrow \ldots`, [A(R`\Pi_i, \varphi_i`, R`disjoint from $\Pi[o \mapsto S]$ and $\mathsf{refill}\,N\,o\,\varphi$`)]);
sa('F-Close', R`\mathsf{f\_close}, \mathsf{f\_select}, \mathsf{f\_branch} : \mathsf{End} \to \ldots \to \mathsf{Prop}`, [ao, A(R`i`, R`the choice, for select and branch`)]);
sa('F-Link', R`\mathsf{f\_link} : \mathcal{P}_{\mathrm{fin}}(\mathsf{End}) \to \mathsf{Expr} \to \mathsf{Prop}`, [A(R`\{o_1, o_2\}`, R`the linked ends`)]);
sa('F-Link.plink', R`\mathsf{plink} : \mathsf{PEnv} \to \mathcal{P}_{\mathrm{fin}}(\mathsf{End}) \to \mathsf{Prop}`, [aPi, A(R`\{o_1, o_2\}`, R`the linked ends`)]);
sa('F-Link.ticket', R`1 \leq tk`, [atk]);
sa('FV-Sess', R`o \in FV\llbracket (S@x)^{a} \rrbracket(\Pi, \varphi)`, [ao, A(R`S@x, a`, R`the end type and its credit`), A(R`S', f`, R`the protocol and counter of $o$`)]);
sa('FV-Sess.counter', R`a \leq f`, [A(R`a`, R`the credit`), A(R`f`, R`the counter`)]);
sa('FV-Arrow', R`\lambda e \in FV^{N}_{n}\llbracket (T^{a_1} \multimap_{c;\vartheta;h} U^{a_2})^{a} \rrbracket(\Pi, \varphi)`, [A(R`c, \vartheta, h`, R`the cost, ticket need and floor of the arrow`), A(R`a`, R`the credit of the closure`)]);
sa('FV-Arrow.exact', R`\mathsf{fends}\,e = \mathrm{dom}\,\Pi = \mathrm{dom}\,\varphi`, [A(R`e`, R`the body`)]);
sa('FV-Arrow.floor', R`\forall o.\ h + a \leq \varphi(o)`, [A(R`h`, R`the floor`), A(R`a`, R`the closure's credit`)]);
sa('FV-Arrow.body', R`e[u] \in F^{N'}_{j}\llbracket U^{a_2} \triangleright c ; r \rrbracket(\Pi \cup \Pi_u, \varphi' \cup \varphi_u, tk)`, [A(R`N', j`, R`a larger refill and a lower level`), A(R`\varphi'`, R`the captured counters at the call, at least $h$`), A(R`u, \Pi_u, \varphi_u`, R`the argument with its maps`), A(R`r, tk`, R`a reserve and ticket count with $\mathsf{meets}\,\vartheta\,r\,tk$`)]);
sa('FV-Box', R`!e \in FV^{N}_{n}\llbracket \Box(\ldots) \rrbracket(\Pi, \varphi)`, [A(R`e`, R`the body`)]);
sa('FV-Box.noends', R`\mathsf{fends}\,e = \varnothing \land \Pi = \varphi = \varnothing`, [A(R`e`, R`the body`)]);
sa('FV-Box.body', R`e[!e] \in F^{N'}_{j}\llbracket U[\bar s] \triangleright c ; r \rrbracket(\varnothing, \varnothing, tk)`, [A(R`N', j`, R`a larger refill and a lower level`), A(R`\bar s`, R`a session instance in $\mathsf{sinsts}\,N'$`), A(R`r, tk`, R`with $\mathsf{meets}\,\vartheta\,r\,tk$`)]);
sa('FV-Thread', R`v \in FV\llbracket \mathsf{thread} \rrbracket(\Pi, \varphi)`, [A(R`v`, R`the returned value`)]);
sa('fu.fsem', R`\mathsf{fsem} : (\mathbb{N} \cup \{\infty\}) \to \mathsf{PEnv} \to \mathsf{Expr} \to \mathsf{Prop}`, [aN, aPi, A(R`e`, R`the thread`), A(R`tk`, R`the ticket count, fixed for all levels`)]);
sa('fu.upd', R`F_n[x := v] : \mathsf{Expr} \to \mathsf{Prop}`, [A(R`x`, R`a component among $d, \Pi, \varphi, tk$`), A(R`v`, R`its new value`), an]);
sa('fu.measure', R`\mu(t) \in \mathbb{N} \times (\mathbb{N} \cup \{\infty\})`, [A(R`t`, R`a thread pending on the end $o$`), A(R`tk_s`, R`the tickets of thread $s$`), A(R`\varphi(\overline{o})`, R`the counter of the partner end in the ownership map`)]);
sa('cs.csem', R`\Delta \vDash^{N} e : T\ !\ \varepsilon`, [A(R`\Delta`, R`the linear context`), aN, A('T', R`the type`), A(R`\varepsilon`, R`the effect, cost and ticket need`)]);
sa('sp.state', R`a = (q, K, tk) \in \mathsf{Config} \times \mathsf{Own} \times (\mathbb{N} \to \mathbb{N})`, [A(R`q`, R`the configuration`), aK, A(R`tk`, R`the tickets per thread`)]);
sa('sp.hold', R`K : \mathsf{End} \rightharpoonup \mathbb{N} \times \mathsf{Point} \times (\mathbb{N} \cup \{\infty\})`, [A(R`t, x, f`, R`holder thread, point and counter`)]);
sa('sp.tk', R`tk : \mathbb{N} \to \mathbb{N}`, [A(R`t`, R`a thread identifier`)]);
sa('sp.exists', R`\exists A \in ${ENV}, \Pi \in \mathsf{PEnv}, U : \mathbb{N} \to \mathsf{Ty}`, [A(R`A`, R`the environment of all held ends`), aPi, A(R`U`, R`the result type of each thread`)]);
sa('sp.prim', R`\mathsf{prim}\,T`, [aT]);
sa('sp.rel', R`\forall t, e.\ q(t) = e \Rightarrow e \in E[\kappa_L]^{W}_{n}\llbracket K_t(A) \vdash U_t \rrbracket^{\varnothing}`, [A(R`t`, R`a thread`), A(R`K_t(A)`, R`$A$ restricted to the ends held by $t$`)]);
sa('sp.ty', R`U_t \in \{T, \ast\}`, [A(R`t`, R`a thread`)]);
sa('sp.fuel', R`e \in F^{N}_{n}\llbracket \mathsf{thread} \triangleright \infty ; 0 \rrbracket(K_t(\Pi), \mathsf{ctrs}\,K\,t, tk_t)`, [A(R`t`, R`a thread`)]);
sa('sp.pts', R`\forall o.\ \mathsf{pt}(A\,o) = \mathsf{pt}(K\,o)`, [A(R`o`, R`an end`)]);
sa('sp.dom', R`\mathrm{dom}\,\Pi = \mathrm{dom}\,K`, [aPi, aK]);
sa('sp.owner', R`\forall o.\ K(o) = (t, \_, \_) \Rightarrow t \in \mathrm{dom}\,q`, [A(R`o, t`, R`a held end and its holder`)]);
sa('sp.closed', R`\forall o \in \mathrm{dom}\,K.\ \mathsf{ech}\,o \in C \lor o \in \mathrm{dom}\,\Sigma`, [A(R`C`, R`the restricted channels of $q$`), aSg]);
sa('sp.pair', R`\forall o \in \mathrm{dom}\,K.\ \mathsf{ech}\,o \in C \Rightarrow \overline{o} \in \mathrm{dom}\,K`, [A(R`o`, R`a held end`)]);
sa('sp.sdual', R`A(o) = S@x \land A(\overline{o}) = S'@x' \land \mathsf{ech}\,o \in C \Rightarrow x' = \overline{x} \land \mathsf{sdual}\,S\,S'`, [A(R`o`, R`an end of a restricted channel`)]);
sa('sp.pdual', R`\Pi(o) = P \land \Pi(\overline{o}) = P' \land \mathsf{ech}\,o \in C \Rightarrow P' \simeq \overline{P}`, [A(R`P, P'`, R`the protocols of the two ends`)]);
sa('sp.sig', R`\Sigma(o) = y \Rightarrow A(o) = y`, [A(R`y`, R`an entry $S@x$`)]);
sa('sp.psig', R`\Sigma(o) = S@x \Rightarrow \Pi(o) = S`, [ao]);
sa('sp.fin', R`\forall o.\ K(o) = (\_, \_, f) \Rightarrow f \in \mathbb{N}`, [A(R`f`, R`the counter of $o$`)]);
sa('sp.lfsem', R`\Sigma \Vvdash_{W} p : T`, [aSg, aW, ap, aT, A(R`N, a`, R`the refill and the soup state, fixed before $n$`)]);
sa('sp.exists-before-forall', R`\exists N \in \mathbb{N}, a.\ \mathsf{erase}(q_a) = p \land \forall n.\ \ldots`, [aN, A(R`a`, R`the soup state`)]);
sa('sp.next', R`\mathsf{lf\_next} : \mathbb{N} \to \mathsf{LFState} \to \mathsf{Event} \to \mathsf{Config} \to \mathsf{LFState}`, [aN, A(R`(q, K, tk)`, R`the state`), A(R`ev`, R`the event`), A(R`q'`, R`the configuration after the event`)]);
sa('sr.FE', SIGF, fuelArgs);
sa('sr.FV', R`v \in FV^{N}_{n}\llbracket \sigma \rrbracket(\Pi, \varphi)`, [aN, an, A(R`\sigma`, R`the result`), aPi, aphi, A(R`v`, R`the value`)]);
sa('sr.act', R`\mathsf{act} : \mathsf{End} \to \mathsf{Prop}`, [ao, aPi, aphi, A(R`d`, R`the frame`)]);
sa('sr.vthunk', R`\mathsf{Vthunk}^{W}_{n} : ${ENV} \to \mathsf{Expr} \to \mathsf{Prop}`, [aW, an, aTh]);
sa('sr.thunk', R`\mathsf{thunk} : \mathsf{Expr} \to \mathsf{Val}`, [A(R`e`, R`the body of a box`)]);
sa('sr.size', R`\mathsf{size} : \mathsf{Ty} \to \mathbb{N}`, [aT]);
sa('sr.irred', R`\mathsf{irred} : \mathsf{Expr} \to \mathsf{Prop}`, [A(R`e`, R`the term`)]);
sa('sr.ready', R`\mathsf{ready} : \mathsf{World} \to ${ENV} \to \mathcal{P}(\mathsf{Point}) \to \mathsf{Expr} \to \mathsf{Prop}`, [aW, aTh, aF, A(R`t`, R`the term`)]);
sa('sr.readyp', R`\mathsf{ready} : \mathsf{World} \to ${ENV} \to \mathsf{Proc} \to \mathsf{Prop}`, [aW, aSg, ap]);
sa('sr.obl', R`\mathsf{Obl} : \mathsf{TLabel} \to \mathsf{Expr} \to \mathsf{Prop}`, [A(R`\alpha`, R`the step label`), A(R`e'`, R`the successor`)]);
sa('sr.pobl', R`\mathsf{Pobl} : \mathsf{Event} \to \mathsf{Proc} \to \mathsf{Prop}`, [A(R`ev`, R`the event`), A(R`p'`, R`the process after the step`)]);
sa('sr.fobl', R`\mathsf{Fobl}^{N} : \mathsf{TLabel} \to \mathsf{Expr} \to \mathsf{Prop}`, [aN, A(R`\alpha`, R`the step label`), A(R`e'`, R`the successor`)]);
sa('sr.fuseok', R`\mathsf{fuse\_ok} : (\mathsf{End} \to \mathsf{End}) \to \mathcal{P}_{\mathrm{fin}}(\mathsf{Chan}) \to ${ENV} \to \mathsf{Proc} \to \mathsf{Prop}`, [A(R`h`, R`the map of ends`), A(R`D`, R`the channels restricted by the fusion`), aSg, ap]);
sa('sr.sdrop', R`\mathsf{sdrop} : \mathcal{P}_{\mathrm{fin}}(\mathsf{Chan}) \to ${ENV} \to ${ENV}`, [A(R`D`, R`the channels`), aSg]);
sa('sr.pfuse', R`\mathsf{pfuse} : (\mathsf{End} \to \mathsf{End}) \to \mathcal{P}_{\mathrm{fin}}(\mathsf{Chan}) \to \mathsf{Proc} \to \mathsf{Proc}`, [A(R`h`, R`the map of ends`), A(R`D`, R`the new restricted channels`), ap]);
sa('sr.pirred', R`\mathsf{pirred} : \mathsf{Proc} \to \mathsf{Prop}`, [ap]);
sa('sr.held', R`\mathsf{held} \subseteq \mathsf{End}`, [aSg, A(R`C`, R`the restricted channels`)]);
sa('sr.gch', R`\mathsf{gch}_h : \mathsf{Chan} \to \mathsf{Chan}`, [A(R`h`, R`the map of ends`), A(R`c`, R`a channel`)]);
sa('sr.tenv-erase', R`|\cdot| : \mathsf{Ctx} \to ${ENV}`, [A(R`\Delta`, R`a linear context`)]);
sa('sr.head', R`\Theta(o) \doteq S@x \iff \exists S_0.\ \Theta(o) = S_0@x \land \mathsf{unfold}\,S_0 = S`, [aTh, A('o', R`the subject end`), A('S', R`the head form of its protocol`)]);
sa('sr.fvagg', R`FV \text{ at } \otimes, \oplus, \exists`, [A(R`\Pi, \varphi`, R`the protocols and counters, split among the parts`)]);
sa('sr.ctrs', R`\mathsf{ctrs} : \mathsf{Own} \to \mathbb{N} \to \mathsf{CEnv}`, [aK, A(R`t`, R`a thread`)]);
