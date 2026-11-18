const { R, h, n, section, block, rule, Q, DEF } = require('./core');

const s = section('semantic', 'Semantic typing',
  'One step-indexed relation R^κ with a cost table κ gives deadlock freedom (κ_DF) and liveness (κ_L). Fuel adds per-thread counters and tickets, and the soup fixes ownership outside the index for lock freedom.');

const V = (W, nn, Th, T) => R`V[\kappa]^{${W}}_{${nn}}\llbracket ${Th} \vdash ${T} \rrbracket`;
const E = (W, nn, Th, T, F) => R`E[\kappa]^{${W}}_{${nn}}\llbracket ${Th} \vdash ${T} \rrbracket^{${F}}`;
const P = (W, nn, Sg, T) => R`P[\kappa]^{${W}}_{${nn}}\llbracket ${Sg} \vdash ${T} \rrbracket`;

// cost tables
block(s, {
  id: 'ct-table', title: 'Cost tables', rocq: 'relation/CostTable.v: ctable',
  tex: R`${h('ct.table', R`\kappa = (\kappa_\beta, \kappa_{new}, \kappa_{spawn}, \kappa_{link}, \kappa_{give}, \kappa_{take})`)} \qquad ${h('ct.take-pos', R`1 \leq \kappa_{take}`)} \qquad ${h('ct.give-pos', R`\kappa_\beta = 0 \Rightarrow 1 \leq \kappa_{give}`)} \qquad ${h('ct.give-take', R`\kappa_{give} \leq \kappa_{take}`)}`,
  caption: 'A step of cost c taken at level n carries its obligation at level n − c. Three side conditions make the generic relation well defined and composable.'
});
block(s, {
  id: 'ct-two', title: 'κ_DF and κ_L', rocq: 'relation/CostTable.v: κ_DF, κ_L',
  tex: R`\begin{array}{lcc}
 & ${h('ct.DF', R`\kappa_{DF}`)} & ${h('ct.L', R`\kappa_L`)} \\ \hline
${h('ct.beta', R`\beta,\ \mathsf{let},\ \mathsf{case},\ \mathsf{force}`)} & 1 & 0 \\
${h('ct.new', R`\mathsf{new}_\ell,\ \mathsf{new}_\kappa`)} & 1 & 0 \\
${h('ct.spawn', R`\mathsf{spawn}`)} & 1 & 0 \\
${h('ct.link', R`\mathsf{link}`)} & 0 & 0 \\
${h('ct.give', R`\mathsf{send},\ \mathsf{select},\ \mathsf{close}`)} & 0 & 1 \\
${h('ct.takek', R`\mathsf{recv},\ \mathsf{branch}`)} & 1 & 1 \\
${h('ct.sync', R`\text{synchronization}`)} & 1 & 2
\end{array}`,
  variants: {
    df: R`\begin{array}{lc}
 & ${h('ct.DF', R`\kappa_{DF}`)} \\ \hline
${h('ct.beta', R`\beta,\ \mathsf{let},\ \mathsf{case},\ \mathsf{force}`)} & 1 \\
${h('ct.new', R`\mathsf{new}_\ell,\ \mathsf{new}_\kappa`)} & 1 \\
${h('ct.spawn', R`\mathsf{spawn}`)} & 1 \\
${h('ct.link', R`\mathsf{link}`)} & 0 \\
${h('ct.give', R`\mathsf{send},\ \mathsf{select},\ \mathsf{close}`)} & 0 \\
${h('ct.takek', R`\mathsf{recv},\ \mathsf{branch}`)} & 1 \\
${h('ct.sync', R`\text{synchronization}`)} & 1
\end{array}`,
    live: R`\begin{array}{lc}
 & ${h('ct.L', R`\kappa_L`)} \\ \hline
${h('ct.beta', R`\beta,\ \mathsf{let},\ \mathsf{case},\ \mathsf{force}`)} & 0 \\
${h('ct.new', R`\mathsf{new}_\ell,\ \mathsf{new}_\kappa`)} & 0 \\
${h('ct.spawn', R`\mathsf{spawn}`)} & 0 \\
${h('ct.link', R`\mathsf{link}`)} & 0 \\
${h('ct.give', R`\mathsf{send},\ \mathsf{select},\ \mathsf{close}`)} & 1 \\
${h('ct.takek', R`\mathsf{recv},\ \mathsf{branch}`)} & 1 \\
${h('ct.sync', R`\text{synchronization}`)} & 2
\end{array}`
  },
  caption: 'Steps of cost 0 are read inductively inside a level. In κ_DF they shrink the term, in κ_L they are the τ steps.'
});
block(s, {
  id: 'rel-atcost', title: 'After a step', rocq: 'relation/Relation.v: at_cost_E, at_cost_V, at_cost_P',
  tex: h('rel.atcost', R`e' \text{ at } \Theta' \iff \begin{cases} ${h('rel.lfp', R`X(\Theta', e')`)} & \kappa(\alpha) = 0 \\ e' \in ${E("W", R`n-\kappa(\alpha)`, R`\Theta'`, 'T', 'F')} & \kappa(\alpha) > 0 \end{cases}`),
  caption: 'X is the least fixpoint being defined. Cost-0 steps stay inside the level.'
});

// V
block(s, {
  id: 'v-base', title: 'V at ∗, S@x, ⊗, ⊕', rocq: 'relation/Relation.v: Vbody',
  tex: R`\begin{array}{l}
${h('V-Unit', R`\ast \in ${V('W', 'n', R`\varnothing`, R`\ast`)}`)} \\
${h('V-Sess', R`o \in ${V('W', 'n', h('V-Sess.exact', R`\{o \mapsto S'@x\}`), R`S@x`)} \iff ${h('sty.seqv', R`S' \approx S`)}`)} \\
${h('V-Prod', R`\langle v_1, v_2\rangle \in ${V('W', 'n', h('V-Prod.split', R`\Theta_1 \uplus \Theta_2`), R`T_1 \otimes T_2`)} \iff v_i \in ${V('W', 'n', R`\Theta_i`, R`T_i`)}`)} \\
${h('V-Sum', R`\mathsf{inj}_i\,v \in ${V('W', 'n', R`\Theta`, R`T_1 \oplus T_2`)} \iff v \in ${V('W', 'n', R`\Theta`, R`T_i`)}`)}
\end{array}`,
  caption: 'Values hold exactly the ends of their environment. An end value holds its own entry at the same point.'
});
block(s, {
  id: 'v-arrow', title: 'V at an arrow', rocq: 'relation/Relation.v: Varr, Varr_rel',
  tex: R`\lambda e \in ${V('W', 'n', R`\Theta`, R`T \multimap^{u}_{l} U`)} \iff ${h('V-Arrow.exact', R`\mathsf{dom}\,\Theta = \mathsf{fends}(e)`)} \land ${h('V-Arrow.lb', R`l \preccurlyeq \mathsf{heads}\,\Theta`)} \land ${h('V-Arrow.kripke', R`\forall W' \sqsupseteq W`)},\ ${h('V-Arrow.level', R`j + \kappa_\beta \leq n`)},\ \Theta' \mathbin{\#} \Theta,\ ${h('V-Arrow.ub', R`u \prec F`)},\ w \in ${V("W'", 'j', R`\Theta'`, 'T')}.\ ${h('V-Arrow.body', R`e[w] \in ${E("W'", 'j', R`\Theta \cup \Theta'`, 'U', 'F')}`)}`,
  caption: 'One arrow for both tables. κ_DF reads the body at j < n, κ_L at j ≤ n. Costs, transformers, floors and credits are not read.'
});
block(s, {
  id: 'v-thunk', title: 'The thunk of O-Spawn', rocq: 'relation/Relation.v: Vthunk',
  tex: R`\lambda e \in \mathsf{Vthunk}^{W}_{n}(\Theta) \iff ${h('V-Arrow.exact', R`\mathsf{dom}\,\Theta = \mathsf{fends}(e)`)} \land \forall W' \sqsupseteq W,\ j + \kappa_\beta \leq n,\ \Theta' \mathbin{\#} \Theta,\ w \in ${V("W'", 'j', R`\Theta'`, R`\ast`)}.\ e[w] \in ${E("W'", 'j', R`\Theta \cup \Theta'`, R`\ast`, h('V-Thunk.empty', R`\varnothing`))}`,
  caption: 'An arrow ∗ ⊸ ∗ without lower point and without upper point, its body read at the empty future.'
});
block(s, {
  id: 'v-box', title: 'V at a box', rocq: 'relation/Relation.v: Vbody (TBox), Vrel_box_iff',
  tex: R`!e \in ${V('W', 'n', h('V-Box.empty', R`\varnothing`), R`\Box(\forall\bar\iota\,\bar\alpha.\,C.\,\ast \multimap^{u} U)`)} \iff ${h('V-Box.noends', R`\mathsf{fends}(e) = \varnothing`)} \land ${h('V-Box.kripke', R`\forall W' \sqsupseteq W`)},\ ${h('V-Box.inst', R`\bar x,\ W' \vdash C[\bar x]`)},\ ${h('V-Box.hc', R`\bar s\ \text{hcontractive}`)}.\ ${h('V-Box.thunk', R`\mathsf{thunk}(e) \in ${V("W'", 'n', R`\varnothing`, R`\ast \multimap^{u[\bar x]} U[\bar s][\bar x]`)}`)}`,
  caption: 'A box is in V when its thunk λ_. e[!e] is, at every later world and every instance meeting C, at the same level.'
});
block(s, {
  id: 'v-ex', title: 'V at an existential', rocq: 'relation/Relation.v: Vbody (TEx), Vrel_ex_iff',
  tex: R`v \in ${V('W', 'n', R`\Theta`, R`\exists^{l}\bar\iota.\,C.\,T`)} \iff ${h('V-Ex.lb', R`l \preccurlyeq \mathsf{heads}\,\Theta`)} \land ${h('V-Ex.witness', R`\exists \bar x.\ W \vdash C[\bar x] \land v \in ${V('W', 'n', R`\Theta`, R`T[\bar x]`)}`)}`,
  caption: 'Some instance in W meets C. ⊥ bounds nothing.'
});
block(s, {
  id: 'v-size', title: 'Recursion of V', rocq: 'relation/Relation.v: tsize, Vtop, sfix',
  tex: h('rel.vsize', R`V_n \text{ by recursion on } (n, \mathsf{size}\,T),\quad \mathsf{size}(\Box\ldots) = 3 + \mathsf{size}\,U,\quad \text{levels by one } \mathsf{sfix}`),
  caption: 'For κ_L, V at level n reads E at level n, so V recurses on the size of the type inside a level.'
});

// E
block(s, {
  id: 'e-body', title: 'The term relation E', rocq: 'relation/Relation.v: Ebody, Eind, Etop',
  tex: R`\begin{array}{l}
${h('E.zero', R`e \in ${E('W', '0', R`\Theta`, 'T', 'F')}`)} \\
e \in ${E('W', R`n{+}1`, R`\Theta`, 'T', 'F')} \iff ${h('E.kripke', R`\forall W_1 \sqsupseteq W`)}. \\
\quad ${h('E.stop', R`(\mathsf{stop})\ \mathsf{irred}\,e \Rightarrow e \in ${V('W_1', R`n{+}1`, R`\Theta`, 'T')}`)} \\
\quad ${h('E.ready', R`(\mathsf{ready})\ \neg\mathsf{irred}\,e \Rightarrow \mathsf{ready}_{W_1}(\Theta \mid F, e)`)} \\
\quad ${h('E.step', R`(\mathsf{step})\ e \xrightarrow{\alpha} e' \Rightarrow \mathsf{Obl}_\alpha(e')`)} \qquad ${h('rel.lfp', R`\text{least fixpoint}`)}
\end{array}`,
  caption: 'A term either stops at a value in V, or is ready and every step meets its obligation.'
});
block(s, {
  id: 'e-obl-admin', title: 'Obligations of τ steps', rocq: 'relation/Relation.v: o_beta, o_new, o_new_at, o_spawn',
  tex: R`\begin{array}{ll}
${h('O-Beta', R`\textsf{O-Beta}`)} & e' \text{ at } \Theta \\
${h('O-New', R`\textsf{O-New}`)} & ${h('O-New.cfresh', R`c\ \text{fresh for}\ \Theta`)} \Rightarrow ${h('O-New.forall', R`\forall g.\ ${h('O-New.gfresh', R`g\ \text{fresh for}\ \Theta`)}`)} \Rightarrow \exists S.\ e' \text{ at } \Theta, ${h('O-New.dual', R`c^{+} : S@g_\ell,\ c^{-} : \overline{S}@\overline{g_\ell}`)} \\
${h('O-NewAt', R`\textsf{O-NewAt}`)} & ${h('O-NewAt.held', R`\Theta(o) = S_0@x`)},\ \exists S.\ e' \text{ at } \Theta, c^{+} : S@x\cdot\kappa,\ c^{-} : \overline{S}@\overline{x\cdot\kappa} \\
${h('O-Spawn', R`\textsf{O-Spawn}`)} & ${h('O-Spawn.split', R`\Theta = \Theta_M \uplus \Theta_r`)},\ ${h('O-Spawn.transfer', R`\mathsf{dom}\,\Theta_M = M`)},\ ${h('O-Spawn.thunk', R`v \in \mathsf{Vthunk}_n(\Theta_M)`)},\ e' \text{ at } \Theta_r
\end{array}`,
  caption: 'Creation places the new channel deterministically. A spawn splits the environment by the transfer set.'
});
block(s, {
  id: 'e-obl-msg', title: 'Obligations of send and receive', rocq: 'relation/Relation.v: o_send, o_recv',
  tex: R`\begin{array}{ll}
${h('O-Send', R`\textsf{O-Send}`)} & \Theta(o) = S_0@x,\ \mathsf{unfold}\,S_0 = {!}(\exists^m.U^b);S,\ ${h('O-Send.split', R`\Theta \setminus o = \Theta_M \uplus \Theta_r`)},\ ${h('O-Spawn.transfer', R`\mathsf{dom}\,\Theta_M = M`)}, \\
 & ${h('O-Send.payload', R`w \in V_{n-\kappa_{give}}\llbracket \Theta_M \vdash U[x\cdot i]\rrbracket`)},\ e' \text{ at } \Theta_r, ${h('O-Send.shift', R`o : S@x^{+}`)} \\
${h('O-Recv', R`\textsf{O-Recv}`)} & \Theta(o) = S_0@x,\ \mathsf{unfold}\,S_0 = {?}(\exists^m.U^b);S,\ ${h('O-Recv.forall', R`\forall j + \kappa_{take} \leq n,\ \Theta_{in} \mathbin{\#} \Theta,\ w \in V_j\llbracket\Theta_{in} \vdash U[x\cdot i]\rrbracket`)}. \\
 & ${h('O-Recv.level', R`e' \in E_j\llbracket \Theta[o \mapsto S@x^{+}] \cup \Theta_{in} \vdash T\rrbracket^{F}`)}
\end{array}`,
  caption: 'The sender gives up exactly the ends of its transfer set. The receiver continues for every incoming value at every lower level.'
});
block(s, {
  id: 'e-obl-other', title: 'Obligations of close, choice and link', rocq: 'relation/Relation.v: o_close, o_select, o_branch, o_link',
  tex: R`\begin{array}{ll}
${h('O-Close', R`\textsf{O-Close}`)} & \Theta(o) = S_0@x,\ \mathsf{unfold}\,S_0 = \mathsf{Close},\ e' \text{ at } \Theta \setminus o \\
${h('O-Select', R`\textsf{O-Select}`)} & \mathsf{unfold}\,S_0 = \oplus(S_1,S_2),\ e' \text{ at } \Theta[o \mapsto S_i@${h('pt.sel', R`\overline{x\cdot\kappa_i}`)}] \\
${h('O-Branch', R`\textsf{O-Branch}`)} & \mathsf{unfold}\,S_0 = \&(S_1,S_2),\ e' \text{ at } \Theta[o \mapsto S_i@${h('pt.bra', R`x\cdot\kappa_i`)}] \\
${h('O-Link', R`\textsf{O-Link}`)} & ${h('O-Link.distinct', R`o_1 \neq o_2`)},\ ${h('O-Link.dual', R`\Theta(o_1) = S_1@x,\ \Theta(o_2) = S_2@\overline{x},\ \mathsf{sdual}\,S_1\,S_2`)},\ e' \text{ at } \Theta \setminus \{o_1, o_2\}
\end{array}`,
  caption: 'Every obligation reads the subject\'s own entry, so a frame\'s ends are never touched.'
});

// readiness
block(s, {
  id: 'rd-term', title: 'Readiness of a term', rocq: 'relation/Readiness.v: ready_t, below_rest, offered_t',
  tex: R`\begin{array}{l}
\mathsf{ready}_W(\Theta \mid F, t) \iff ${h('rd.stable', R`\mathsf{stable}\,t`)} \Rightarrow (${h('rd.value', R`(\forall o.\ \neg${h('rd.offered', R`\mathsf{offered}\,o`)}) \Rightarrow t\ \text{value}`)}) \land (${h('rd.link', R`\mathsf{link}\,t`)} \lor ${h('rd.below-rest', R`\mathsf{below\_rest}`)}) \\
${h('rd.below-rest', R`\mathsf{below\_rest}`)} \iff \forall o\ \text{offered at } x.\ ${h('rd.below-held', R`\forall o'\ \text{held, not offered, at } x'.\ W \vdash x \prec \overline{x'}`)} \land ${h('rd.below-future', R`\forall y \in F.\ W \vdash x \prec y`)}
\end{array}`,
  caption: 'A stable reducible term offers some held ends, each below the partner point of every other held end and below the future.'
});
block(s, {
  id: 'rd-proc', title: 'Readiness of a process', rocq: 'relation/Readiness.v: ready_p, above_offered',
  tex: R`\mathsf{ready}_W(\Sigma, p) \iff ${h('rd.p-stable', R`\mathsf{stable}\,p`)} \Rightarrow \mathsf{link}\,p \lor \big(${h('rd.p-term', R`(\text{no offer} \Rightarrow \mathsf{terminated}\,p)`)} \land ${h('rd.above-offered', R`\forall o \in \Sigma\ \text{not offered at } x.\ \exists o'\ \text{offered at } x'.\ W \vdash x' \prec \overline{x}`)}\big)`,
  caption: 'A stable process offers some interface end, and every interface end it does not offer has an offered end below its partner point.'
});

// P
block(s, {
  id: 'p-body', title: 'The process relation P', rocq: 'relation/Relation.v: Pbody, Pclauses, Pind',
  tex: R`\begin{array}{l}
p \in ${P('W', R`n{+}1`, R`\Sigma`, 'T')} \iff ${h('P.strict', R`\forall W_1 \sqsupseteq W,\ \mathsf{strict}\,W_1`)},\ ${h('P.fuse', R`\forall h\,D.\ \mathsf{fuse\_ok}\,h\,D\,\Sigma\,p`)} \Rightarrow \text{clauses at } W_1,\ \mathsf{sdrop}\,D\,(h\,\Sigma),\ \mathsf{pfuse}\,h\,D\,p \\
\quad ${h('P-Stop', R`(\textsf{P-Stop})\ \mathsf{pirred}\,p \Rightarrow p = (\varnothing, \{v\} \uplus E),\ v \in V\llbracket\Sigma \vdash T\rrbracket,\ E \subseteq \{\ast\}`)} \\
\quad ${h('P-Ready', R`(\textsf{P-Ready})\ \neg\mathsf{pirred}\,p \Rightarrow \mathsf{ready}_{W_1}(\Sigma, p)`)} \\
\quad ${h('P-Step', R`(\textsf{P-Step})\ \text{every instrumented step of every lifting meets } \mathsf{Pobl}`)} \qquad ${h('rel.lfp', R`\text{least fixpoint}`)}
\end{array}`,
  caption: 'P is Kripke over strict later worlds only and closed under fusions of held ends by definition.'
});
block(s, {
  id: 'p-fuse', title: 'Fusions of held ends', rocq: 'relation/Relation.v: fuse_ok, pfuse, sdrop, dpairs',
  tex: R`\mathsf{fuse\_ok}\,h\,D\,\Sigma\,p \iff ${h('fuse.dcomm', R`h(\overline{o}) = \overline{h(o)}`)} \land ${h('fuse.inj', R`h\ \text{injective on held ends}`)} \land ${h('fuse.partners', R`h(o_2) = \overline{h(o_1)} \Rightarrow o_2 = \overline{o_1} \lor \mathsf{ech}(h\,o_1) \in D`)} \land ${h('fuse.D', R`D \mathbin{\#} h[C]`)} \land ${h('fuse.dpairs', R`\mathsf{dpairs}\,D\,(h\,\Sigma)`)}`,
  caption: 'D = ∅ is a renaming, h = id internalizes pairs of Σ. One concept covers renaming, Internalize and the link case of P-Connect.'
});
block(s, {
  id: 'p-obl', title: 'Obligations of process steps', rocq: 'relation/Relation.v: q_tau, q_send, q_recv, send_split, recv_ok, recv_back, recv_env',
  tex: R`\begin{array}{ll}
${h('Q-Tau', R`\textsf{Q-Tau}`)} & p'.1 \mathbin{\#} \mathsf{chans}\,\Sigma \Rightarrow p' \text{ at } \Sigma \text{ after cost } \kappa(ev) \\
${h('Q-Send', R`\textsf{Q-Send}`)} & \Sigma \setminus o = \Sigma_v \uplus \Sigma_r,\ ${h('Q-Send.theta-e', R`\mathsf{dom}\,\Theta_e = M \cap \mathsf{ends}(C)`)},\ M = \mathsf{dom}\,\Sigma_v \cup \mathsf{dom}\,\Theta_e,\ ${h('Q-Send.split', R`\mathsf{send\_split}\,\Sigma\,\Sigma_e\,\Theta_e`)}, \\
 & w \in V\llbracket\Sigma_v \cup \Theta_e \vdash U[x\cdot i]\rrbracket,\ p' \text{ at } (\Sigma_r \cup ${h('Q-Send.sigma-e', R`\Sigma_e`)})[o \mapsto S@x^{+}] \\
${h('Q-Recv', R`\textsf{Q-Recv}`)} & \forall j + \kappa_{take} \leq n,\ \Theta_2,\ ${h('Q-Recv.ok', R`\mathsf{recv\_ok}\,\Sigma'\,\Theta_2`)},\ w \in V_j\llbracket\Theta_2 \vdash U[x\cdot i]\rrbracket \Rightarrow \\
 & (p'.1 \cup ${h('Q-Recv.back', R`\mathsf{recv\_back}\,\Sigma'\,\Theta_2`)}, p'.2) \in P_j\llbracket ${h('Q-Recv.env', R`\mathsf{recv\_env}\,\Sigma'\,\Theta_2`)} \vdash T\rrbracket \\
${h('Q-Link', R`\textsf{Q-Close, Q-Select, Q-Branch, Q-Link}`)} & \text{as for terms, on } \Sigma
\end{array}`,
  caption: 'External messages move restricted ends in and out of the interface. A τ step keeps the interface.'
});

// semantic judgments
block(s, {
  id: 'sj', title: 'Semantic judgments ⊨, ⊫', rocq: 'compat/SemTyped.v: Grel, sem_typed_at, sf_den, sem_typed; relation/Adequacy.v: sem_ptyped',
  tex: R`\begin{array}{l}
${h('sj.at', R`\Theta;\Delta \vDash^{X}_W t : T \iff \forall n\,W' \sqsupseteq W\,\Theta'\,\gamma.\ ${h('sj.grel', R`\gamma \in G_n^{W'}\llbracket\Theta' \vdash \Delta\rrbracket`)} \Rightarrow \gamma(t) \in E_n^{W'}\llbracket \Theta \cup \Theta' \vdash T\rrbracket^{X}`)} \\
${h('sj.term', R`\Theta;\Delta \vDash^{F}_W t : T \iff \forall \rho\,B.\ \Theta;\Delta \vDash^{${h('sj.den', R`\mathsf{den}_{\rho,B}(F)`)}}_W t : T \qquad (\mathrel{|\!\!\vDash} \text{ at } \kappa_L)`)} \\
${h('sj.proc', R`\Sigma \vDash_W p : T \iff \forall n.\ p \in P_n^W\llbracket\Sigma \vdash T\rrbracket \qquad (\mathrel{|\!\!\vDash}_W \text{ at } \kappa_L)`)}
\end{array}`,
  variants: {
    df: R`\begin{array}{l}
${h('sj.at', R`\Theta;\Delta \vDash^{X}_W t : T \iff \forall n\,W' \sqsupseteq W\,\Theta'\,\gamma.\ ${h('sj.grel', R`\gamma \in G_n^{W'}\llbracket\Theta' \vdash \Delta\rrbracket`)} \Rightarrow \gamma(t) \in E_n^{W'}\llbracket \Theta \cup \Theta' \vdash T\rrbracket^{X}`)} \\
${h('sj.term', R`\Theta;\Delta \vDash^{F}_W t : T \iff \forall \rho\,B.\ \Theta;\Delta \vDash^{${h('sj.den', R`\mathsf{den}_{\rho,B}(F)`)}}_W t : T`)} \\
${h('sj.proc', R`\Sigma \vDash_W p : T \iff \forall n.\ p \in P_n^W\llbracket\Sigma \vdash T\rrbracket`)}
\end{array}`,
    live: R`\begin{array}{l}
${h('sj.at', R`\Theta;\Delta \mathrel{|\!\!\vDash}^{X}_W t : T \iff \forall n\,W' \sqsupseteq W\,\Theta'\,\gamma.\ ${h('sj.grel', R`\gamma \in G[\kappa_L]_n^{W'}\llbracket\Theta' \vdash \Delta\rrbracket`)} \Rightarrow \gamma(t) \in E[\kappa_L]_n^{W'}\llbracket \Theta \cup \Theta' \vdash T\rrbracket^{X}`)} \\
${h('sj.term', R`\Theta;\Delta \mathrel{|\!\!\vDash}^{F}_W t : T \iff \forall \rho\,B.\ \Theta;\Delta \mathrel{|\!\!\vDash}^{${h('sj.den', R`\mathsf{den}_{\rho,B}(F)`)}}_W t : T`)} \\
${h('sj.proc', R`\Sigma \mathrel{|\!\!\vDash}_W p : T \iff \forall n.\ p \in P[\kappa_L]_n^W\llbracket\Sigma \vdash T\rrbracket`)}
\end{array}`
  },
  caption: 'The semantic judgments quantify over every level, later world and grounding. The static future is read with its variable and ⊥ flag as arbitrary sets.'
});

// fuel
block(s, {
  id: 'fu-def', title: 'Fuel F^N', rocq: 'fuel/Fuel.v: Fdef, FuelE, FLev',
  modes: ['lf'],
  tex: R`\begin{array}{l}
${h('fu.zero', R`e \in F^N_0\llbracket\ldots\rrbracket`)} \\
e \in F^N_{n+1}\llbracket ${h('fu.rty', R`\sigma`)} \triangleright ${h('fu.frame', 'd')} ; ${h('fu.reserve', 'r')} \rrbracket(${h('fu.Pi', R`\Pi`)}, ${h('fu.phi', R`\varphi`)}, ${h('fu.tk', 'tk')}) \iff ${h('fu.refill-kripke', R`\forall N' \geq_{\mathsf{rle}} N`)},\ ${h('fu.rename', R`g\ \text{injective on}\ \mathsf{dom}\,\Pi, \mathsf{dom}\,\varphi`)}. \\
\quad ${h('fu.val', R`(\mathsf{val})\ g(e)\ \text{value} \Rightarrow r \leq tk \land g(e) \in FV^{N'}_{n+1}\llbracket\sigma\rrbracket(g\Pi, g\varphi)`)} \\
\quad ${h('fu.step', R`(\mathsf{step})\ g(e) \xrightarrow{\alpha} e' \Rightarrow \mathsf{Fobl}_\alpha \text{ at level } n`)} \qquad ${h('fu.oneclock', R`\text{every step costs one level}`)}
\end{array}`,
  caption: 'A per-thread predicate on counters, protocols and tickets. It reads no point, no world and no relation.'
});
block(s, {
  id: 'fu-act', title: 'An action on o (F-Wait, F-Tick)', rocq: 'fuel/Fuel.v: f_act, fspare, idle, refill',
  modes: ['lf'],
  tex: R`\mathsf{act}\,o \iff ${h('F-Wait', R`\neg\mathsf{idle}(\Pi\,o)`)} \land o \in \mathsf{dom}\,\varphi \land ${h('F-Tick', R`\mathsf{fspare}\,\Pi\,\varphi\,(\mathsf{dom}\,\varphi \setminus o)`)} \land ${h('F-Tick.frame', R`1 \leq d`)} \qquad ${h('fu.refillop', R`\mathsf{refill}\,N\,o\,\varphi = \varphi[o \mapsto N]\ \text{and every other counter} - 1`)} \qquad ${h('fu.idle', R`\mathsf{idle}\,S \iff \mathsf{unfold}\,S = \mathsf{Skip}`)}`,
  caption: 'An action refills its end and ticks every other end of the thread. Each other end that is not idle must have a unit to spare.'
});
block(s, {
  id: 'fu-obl', title: 'Fuel obligations', rocq: 'fuel/Fuel.v: f_beta, f_new, f_spawn, f_send, f_recv, f_close, f_select, f_branch, f_link',
  modes: ['lf'],
  tex: R`\begin{array}{ll}
${h('F-Beta', R`\textsf{F-Beta}`)} & e' \text{ at the same state} \\
${h('F-New', R`\textsf{F-New}`)} & ${h('F-New.fresh', R`c\ \text{fresh for}\ \Pi, \varphi`)} \Rightarrow \exists S.\ e' \text{ at } \Pi + \{c^{+} : S, c^{-} : \overline{S}\},\ ${h('F-New.cnew', R`\varphi + \{c^{\pm} \mapsto N\}`)} \\
${h('F-Spawn', R`\textsf{F-Spawn}`)} & ${h('F-Spawn.held', R`M \subseteq \mathsf{dom}\,\varphi`)},\ ${h('fu.fspare', R`\mathsf{fspare}\,M`)},\ ${h('F-Spawn.child', R`v\,\ast \in F^N\llbracket\mathsf{thread}\rrbracket(\Pi|_M, ${h('fu.fhand', R`(\varphi - 1)|_M`)}, \lceil tk/2\rceil)`)},\ e' \text{ at } \Pi \setminus M, \varphi \setminus M, ${h('F-Spawn.tickets', R`\lfloor tk/2 \rfloor`)} \\
${h('F-Send', R`\textsf{F-Send}`)} & \mathsf{act}\,o,\ ${h('F-Send.notsubj', R`M \subseteq \mathsf{dom}\,\varphi \setminus o`)},\ ${h('fu.fspare', R`\mathsf{fspare}\,M`)},\ ${h('F-Send.payload', R`w \in FV^N\llbracket T^{b}\rrbracket(\Pi|_M, (\varphi-1)|_M)`)},\ e' \text{ at } d-1,\ \Pi[o \mapsto S] \setminus M,\ ${h('fu.refillop', R`\mathsf{refill}\,N\,o`)}(\varphi \setminus M) \\
${h('F-Recv', R`\textsf{F-Recv}`)} & \mathsf{act}\,o,\ ${h('F-Recv.forall', R`\forall j \leq n,\ \Pi_i,\ \varphi_i,\ w \in FV^N_j\llbracket T^{b}\rrbracket(\Pi_i, \varphi_i)`)}.\ e' \text{ at level } j,\ \Pi[o\mapsto S] \cup \Pi_i,\ \mathsf{refill}\,N\,o\,\varphi \cup \varphi_i \\
${h('F-Close', R`\textsf{F-Close, F-Select, F-Branch}`)} & \mathsf{act}\,o,\ \text{advance } \Pi\,o,\ \text{tick or refill, frame } d - 1 \\
${h('F-Link', R`\textsf{F-Link}`)} & ${h('F-Link.plink', R`\Pi(o_1), \Pi(o_2)\ \text{dual}`)},\ \{o_1,o_2\} \subseteq \mathsf{dom}\,\varphi,\ ${h('F-Link.ticket', R`1 \leq tk`)},\ e' \text{ at } \Pi \setminus \{o_1,o_2\}, tk - 1
\end{array}`,
  caption: 'Counters evolve by one update at every index. Hand-overs pass the counter minus one, links spend a ticket.'
});
block(s, {
  id: 'fv', title: 'Values at a credited type FV^N', rocq: 'fuel/Fuel.v: Vty, Vres',
  modes: ['lf'],
  tex: R`\begin{array}{l}
${h('FV-Sess', R`o \in FV\llbracket (S@x)^{a}\rrbracket(\{o : S'\}, \{o : f\}) \iff S' \simeq S \land ${h('FV-Sess.counter', R`a \leq f`)}`)} \\
${h('FV-Arrow', R`\lambda e \in FV_n\llbracket (T^{a_1} \multimap[c;\vartheta;h] U^{a_2})^{a}\rrbracket(\Pi,\varphi) \iff ${h('FV-Arrow.exact', R`\mathsf{fends}\,e = \mathsf{dom}\,\Pi`)} \land ${h('FV-Arrow.floor', R`\varphi \geq h + a`)} \land {}`)} \\
\quad ${h('FV-Arrow.body', R`\forall N' \geq_{\mathsf{rle}} N,\ j < n,\ \varphi' \geq h,\ u \in FV_j\llbracket T^{a_1}\rrbracket,\ \mathsf{meets}\,\vartheta\,r\,tk.\ e[u] \in F^{N'}_j\llbracket U^{a_2} \triangleright c ; r\rrbracket(\Pi \cup \Pi_u, \varphi' \cup \varphi_u, tk)`)} \\
${h('FV-Box', R`!e \in FV_n\llbracket \Box(\ldots)\rrbracket(\varnothing,\varnothing) \iff ${h('FV-Box.noends', R`\mathsf{fends}\,e = \varnothing`)} \land ${h('FV-Box.body', R`\forall N', j < n, \bar s \in \mathsf{sinsts}\,N', \mathsf{meets}\,\vartheta\,r\,tk.\ e[!e] \in F^{N'}_j\llbracket U[\bar s] \triangleright c ; r\rrbracket(\varnothing,\varnothing,tk)`)}`)} \\
${h('FV-Thread', R`v \in FV\llbracket\mathsf{thread}\rrbracket(\Pi,\varphi) \iff \Pi = \varphi = \varnothing`)} \qquad \otimes, \oplus, \exists:\ \text{credit added to the parts, maps split}
\end{array}`,
  caption: 'By recursion on the type. Points, bounds and constraints are not read.'
});
block(s, {
  id: 'fu-fsem', title: 'fsem and the semantic cost judgment', rocq: 'fuel/Fuel.v: fsem; cost/CostSem.v: csem, thfuel, gfuel',
  modes: ['lf'],
  tex: R`${h('fu.fsem', R`\mathsf{fsem}\,N\,\Pi\,e \iff \exists tk\,\forall n.\ e \in F^N_n\llbracket\mathsf{thread} \triangleright \infty ; 0\rrbracket(\Pi, N \text{ on } \mathsf{dom}\,\Pi, tk)`)} \qquad ${h('cs.csem', R`\Theta;\Delta \vDash^{N} e : T^{a} \triangleright c ; \vartheta`)}`,
  caption: 'Every held end starts at N, at one ticket count for every index. csem is the cost half of the merged judgment read semantically.'
});

// soup
block(s, {
  id: 'sp-state', title: 'Soup states', rocq: 'soup/State.v: hold, lfstate',
  modes: ['lf'],
  tex: R`${h('sp.state', R`a = (q, K, tk)`)} \qquad ${h('sp.hold', R`K : o \mapsto (t, x, f)`)} \qquad ${h('sp.tk', R`tk : t \mapsto \mathbb{N}`)}`,
  caption: 'The configuration, the ownership (holder, point, counter of each held end) and the tickets per thread, fixed outside the index.'
});
block(s, {
  id: 'sp-inv', title: 'The soup S^{N,W}_n', rocq: 'soup/State.v: soup_gen, soup/Soup.v: soup_inv, Soup',
  modes: ['lf'],
  tex: R`\begin{array}{l}
a \in S^{N,W}_n\llbracket\Sigma \vdash T\rrbracket \iff ${h('sp.exists', R`\exists A\,\Pi\,U`)}. \\
\quad ${h('sp.prim', R`\mathsf{prim}\,T`)} \quad ${h('sp.rel', R`\forall t.\ q(t) \in E[\kappa_L]^W_n\llbracket A|_t \vdash U_t\rrbracket^{\varnothing}`)} \quad ${h('sp.ty', R`U_t \in \{T, \ast\}`)} \\
\quad ${h('sp.fuel', R`\forall t.\ q(t) \in F^N_n\llbracket\mathsf{thread}\rrbracket(\Pi|_t, \mathsf{ctrs}\,K\,t, tk_t)`)} \quad ${h('sp.pts', R`\text{points of } A = \text{points of } K`)} \quad ${h('sp.dom', R`\mathsf{dom}\,\Pi = \mathsf{dom}\,K`)} \\
\quad ${h('sp.owner', R`\text{holders exist}`)} \quad ${h('sp.closed', R`o \in K \Rightarrow \mathsf{ech}\,o \in C \lor o \in \Sigma`)} \quad ${h('sp.pair', R`o \in K,\ \mathsf{ech}\,o \in C \Rightarrow \overline{o} \in K`)} \\
\quad ${h('sp.sdual', R`\text{internal partners at } x, \overline{x},\ \text{types dual up to annotations}`)} \quad ${h('sp.pdual', R`\Pi(\overline{o}) \simeq \overline{\Pi(o)}`)} \\
\quad ${h('sp.sig', R`\Sigma(o) = A(o)`)} \quad ${h('sp.psig', R`\Sigma(o) = (S, x) \Rightarrow \Pi(o) = S`)} \quad ${h('sp.fin', R`\text{every counter finite}`)}
\end{array}`,
  caption: 'Per index, every thread is live and fueled at its part of A and Π. Ends, points and counters come from K and are the same at every index.'
});
block(s, {
  id: 'sp-lf', title: 'The lock-free semantic judgment ⊪', rocq: 'soup/Soup.v: lf_sem, lf_next',
  modes: ['lf'],
  tex: R`${h('sp.lfsem', R`\Sigma \Vvdash_W p : T \iff ${h('sp.exists-before-forall', R`\exists N\,a.\ \mathsf{erase}(q_a) = p \land \forall n`)}.\ a \in S^{N,W}_n\llbracket\Sigma \vdash T\rrbracket`)} \qquad ${h('sp.next', R`\mathsf{lf\_next}\,N\,a\,ev\,q'`)}`,
  caption: 'The soup alone. The state is chosen once, before the index, and follows events by one index-free update.'
});

// ---- notes ----
n('ct.table', 'Cost table κ', 'The cost of each kind of step. A step of cost 0 is read inside the least fixpoint of the level, a step of cost c > 0 at level n − c.', 'L6 and quirk A4. The live relation was a copy of the base relation. One relation with a cost table gives both (proposal §2.8).', DEF, 'κ_DF = (1, 1, 1, 0, 0, 1).', 'relation/CostTable.v: ctable');
n('ct.take-pos', 'κ(take) ≥ 1', 'Receive and branch cost at least one level.', 'Progress.md, S3 cost tables. A receive reads V of its payload at the level of its continuation in a negative position, so that level must lie below n.', 'With a free receive, V at level n would quantify negatively over itself.', 'Both tables charge 1.', 'relation/CostTable.v: c_take_pos');
n('ct.give-pos', 'κ(β) = 0 ⇒ κ(give) ≥ 1', 'When β is free, a send costs at least one.', 'Progress.md, S3. When β is free, V at level n is defined together with E at level n by fuel on the size of the type, and a free send would read V at level n at a payload of unbounded size.', DEF, 'κ_L charges send 1.', 'relation/CostTable.v: c_give_pos');
n('ct.give-take', 'κ(give) ≤ κ(take)', 'A give costs at most a take.', 'Decision after S4.18 (fusion). A synchronization of two closes costs κ(send) + κ(recv), and composition pays it with two gives (comment in CostTable.v).', DEF, 'κ_DF 0 ≤ 1, κ_L 1 ≤ 1.', 'relation/CostTable.v: c_give_take');
n('ct.DF', 'κ_DF', 'The deadlock-freedom table. Giving steps and links cost 0 and shrink the term, so the fixpoint is a size recursion.', 'B3 (proposal §2.8).', DEF, 'adequacy at κ_DF.', 'relation/CostTable.v: κ_DF');
n('ct.L', 'κ_L', 'The live table. τ steps cost 0, channel actions 1, a synchronization 2.', 'L1 and L2. The least fixpoint over τ steps is the content of liveness (proposal §2.8).', DEF, 'live_adequacy at κ_L.', 'relation/CostTable.v: κ_L');
n('ct.beta', 'Cost of β', '1 in κ_DF, 0 in κ_L. An arrow reads its body at j + κ(β) ≤ n.', 'One arrow for both tables (proposal §2.8). For κ_L the body sits at the current level.', DEF, 'κ_L reads λ bodies at level n.', 'relation/CostTable.v: c_beta');
n('ct.new', 'Cost of creation', '1 in κ_DF, 0 in κ_L.', 'Proposal §2.8 table.', DEF, 'new_0 is free in κ_L.', 'relation/CostTable.v: c_new');
n('ct.spawn', 'Cost of spawn', '1 in κ_DF, 0 in κ_L. In κ_L the child is read inside the parent\'s least fixpoint.', 'Proposal §2.12. This is how κ_L rejects the infinite spawn chain (#40, kob_not_live).', DEF, 'O-Spawn reads the thunk at level n.', 'relation/CostTable.v: c_spawn');
n('ct.link', 'Cost of link', '0 in both tables.', 'L2, decision 2026-11-08, quirk A5.', 'Link loops are τ-divergence in κ_L (#11).', 'rec f. new; link; f () τ-diverges.', 'relation/CostTable.v: c_link');
n('ct.give', 'Cost of a give', 'send, select and close. 0 in κ_DF, 1 in κ_L.', 'Proposal §2.8.', DEF, 'O-Send at n − κ(give).', 'relation/CostTable.v: c_give');
n('ct.takek', 'Cost of a take', 'recv and branch. 1 in both.', 'Proposal §2.8 and c_take_pos.', DEF, 'O-Recv at j ≤ n − 1.', 'relation/CostTable.v: c_take');
n('ct.sync', 'Cost of a synchronization', 'κ(give) + κ(take). 1 in κ_DF, 2 in κ_L.', 'Sharp edge 44 (#16). κ_L charges 2, so the index does not halve at a synchronization.', DEF, 'P-Act-Msg costs ev_cost.', 'relation/CostTable.v: ev_cost');
n('rel.atcost', 'e′ at Θ′', 'After a step of cost 0, the term must be in the fixpoint X at the same level. After a positive cost, in E at the lower level.', 'Stated as two implications, so X occurs strictly positively (comment in Relation.v).', DEF, 'A β step in κ_L stays at level n.', 'relation/Relation.v: at_cost_E');
n('rel.lfp', 'Least fixpoint', 'E and P at a level are least fixpoints over cost-0 steps.', 'In κ_DF the cost-0 steps shrink the term, in κ_L the least fixpoint excludes infinite τ sequences (proposal §2.8).', 'A greatest fixpoint would admit !(f = force f) in κ_L, which only takes β steps.', 'Erel_S_ind is its induction principle.', 'relation/Relation.v: Eind, Pind');
n('V-Unit', 'V at ∗', 'Only ∗, with an empty environment.', 'Not documented.', DEF, '∗ ∈ V⟦∅ ⊢ ∗⟧.', 'relation/Relation.v: Vbody TUnit');
n('V-Sess', 'V at S@x', 'The value is an end o, the environment holds exactly o at the same point x, at a session type equal to S up to annotations.', 'Progress.md, S3 annotations. The environment keeps its annotations for the fuel layer, V compares erased.', DEF, 'c⁺ ∈ V⟦{c⁺ ↦ (S′, ρ)} ⊢ S@ρ⟧ when S′ ≈ S.', 'relation/Relation.v: Vbody TSess');
n('V-Sess.exact', 'Exactly one entry', 'Θ is the singleton {o ↦ S′@x}.', 'Values own exactly their ends. The point is the same, no alias (W2, no-eq).', DEF, 'Θ = {c⁺ ↦ (S, ρ)}.', 'relation/Relation.v: Vbody TSess');
n('V-Prod', 'V at ⊗', 'Components split the environment disjointly.', 'Not documented.', DEF, '⟨c⁺, d⁻⟩ splits {c⁺, d⁻}.', 'relation/Relation.v: Vbody TProd');
n('V-Prod.split', 'Disjoint split', 'Θ = Θ₁ ⊎ Θ₂.', 'F19, a pair splits its ends into disjoint parts. A renaming that pushes a held end into a box inside a pair is ruled out by the split (#36).', DEF, '{c⁺} ⊎ {d⁻}.', 'relation/Relation.v: Vbody TProd');
n('V-Sum', 'V at ⊕', 'An injection into one side.', 'Not documented.', DEF, 'inj₁ c⁺.', 'relation/Relation.v: Vbody TSum');
n('V-Arrow.exact', 'dom Θ = fends(e)', 'A closure holds exactly the ends its body mentions.', 'Decision Q14, agreed explicitly. It is the clause V already has at an end value.', 'send_gap (v2/compat/SendGap.v, S4.3). λ_. let ∗ = Ω in close q⁺ mentions q⁺, owns nothing, and is in V at every level, so send ⟨w′, d⁺⟩ is not in E at level 1 and E-Send fails.', 'λ_. close a holds {a}.', 'relation/Relation.v: Varr');
n('V-Arrow.lb', 'l ≼ heads Θ', 'The lower point bounds the heads of the closure\'s ends.', 'The holder reads the closure\'s heads through l.', DEF, 'A closure over a at ρ has l ≼ ρ̄.', 'relation/Relation.v: Varr, lb_le');
n('V-Arrow.kripke', 'Every later world', 'The body works in every W′ ⊒ W.', 'Monotonicity in the world. A closure may be called after the world grew.', DEF, 'Calling a received closure in W ⊔ W′.', 'relation/Relation.v: Varr');
n('V-Arrow.level', 'j + κ(β) ≤ n', 'The body is read at every level up to n − κ(β).', 'One arrow for both tables. κ_DF gives j < n, κ_L gives j ≤ n (proposal §2.8).', DEF, 'κ_L reads the body at level n.', 'relation/Relation.v: Varr');
n('V-Arrow.ub', 'u ≺ F', 'The body runs under every future above u.', 'Futures and the upper point are one concept in presentation (proposal §2.16).', DEF, 'ub_lt W\' u F.', 'relation/Readiness.v: ub_lt');
n('V-Arrow.body', 'Body in E', 'e[w] is in E with the union of the closure\'s and the argument\'s ends.', 'Not documented.', DEF, 'The body of cli at ⟨a, b⟩.', 'relation/Relation.v: Varr');
n('V-Thunk.empty', 'Empty future of the thunk', 'The spawned thunk is read without lower and upper point, at the empty future.', 'Decisions after S5.5 and S5.6. The thunk leaves the parent, so no readiness of the parent reads its heads, and a thread with no context waits for nothing in a future.', 'spawn_gap (v2/compat/SpawnGap.v). With the lower point, a thread holding ends at unrelated points 1 and 2 cannot spawn a thunk that closes both, and fundamental fails.', 'Vthunk_of_Vrel gives Erel_spawn.', 'relation/Relation.v: Vthunk');
n('V-Box.empty', 'Θ = ∅', 'A box owns no end.', 'Not documented beyond Q14.', DEF, '!(…) with Θ = ∅.', 'relation/Relation.v: Vbody TBox');
n('V-Box.noends', 'fends(e) = ∅', 'A box mentions no end.', 'Decision Q14. Implied by the clause at its thunk, kept because Q14 states it (progress.md, S4 Q14).', 'A box hiding an end under an empty map could be copied with the end inside (#32).', 'ring mentions no end.', 'relation/Relation.v: Vbody TBox');
n('V-Box.kripke', 'Every later world', 'The box works in every W′ ⊒ W.', 'Not documented.', DEF, 'Forcing a received box later.', 'relation/Relation.v: Vbody TBox');
n('V-Box.inst', 'Instances meeting C', 'Every point instance x̄ whose constraint holds in W′.', 'Not documented.', DEF, 'The self call of cli at (ι⁺, κ⁺, ζ).', 'relation/Readiness.v: wholds');
n('V-Box.hc', 'Hereditarily contractive instances', 'Every session instance that is hcontractive.', 'Progress.md, S3. V-Box quantifies over every hcontractive instance, D-Box only over the N = ∞ ones, and blindness bridges the two.', DEF, 'k = 0 in the examples.', 'types/Types.v: hcontractive');
n('V-Box.thunk', 'The thunk at the same level', 'λ_. e[!e] is in V at the instantiated arrow at level n.', 'A box counts three in tsize so that V of a box reads V of its thunk type inside the level (comment in Relation.v).', DEF, 'thunk e := λ. e[!e].', 'relation/Relation.v: thunk, tthunk');
n('V-Ex.lb', 'l ≼ heads Θ', 'The lower bound holds of the actual ends, trivially for ⊥.', 'Not documented.', DEF, '⊥ for new.', 'relation/Readiness.v: lbx_le');
n('V-Ex.witness', 'A witness in W', 'Some instance meets C in W, and the value is in V at that instance.', 'Not documented.', DEF, 'The fresh root g with Λ_ℓ(g).', 'relation/Relation.v: Vbody TEx');
n('rel.vsize', 'Recursion on (n, size T)', 'V at level n recurses on the type size inside the level. Levels come from one generic course-of-values fixpoint sfix.', 'B1 and proposal §2.8. Instantiation keeps the size (tsize_sinst), so the box clause stays inside the recursion.', DEF, 'size(□…) = 3 + size U.', 'relation/Relation.v: tsize, Vtop; relation/Sfix.v: sfix');
n('E.zero', 'Level 0', 'Every term is in E at level 0.', 'Step indexing.', DEF, 'Erel_0.', 'relation/Relation.v: Etop, Erel_0');
n('E.kripke', 'Every later world', 'Each unfolding of E holds in every W₁ ⊒ W.', 'Decision Q9 (a). E is monotone in the world by definition. The receive clause needs no quantifier of its own.', DEF, 'Erel_mono.', 'relation/Relation.v: Ebody');
n('E.stop', '(stop)', 'An irreducible term is a value in V at the current level.', 'Not documented.', 'A stuck non-value term would count as typed.', 'close c⁺ alone is reducible by its offer, not stuck.', 'relation/Relation.v: Ebody');
n('E.ready', '(ready)', 'A reducible term is ready against its environment and future.', 'B2. Readiness excludes circular waiting.', 'Two threads each waiting on the other\'s second end.', 'ready_t W (Θ ∣ F, e).', 'relation/Relation.v: Ebody');
n('E.step', '(step)', 'Every labelled step meets its obligation.', 'One conjunct per label so that X occurs strictly positively (progress.md, S3 the step clause).', DEF, 'Esteps, Eobl.', 'relation/Relation.v: Esteps, Eobl');
n('O-Beta', 'O-Beta', 'The continuation at the same environment.', 'Not documented.', DEF, 'β in κ_L stays at level n.', 'relation/Relation.v: o_beta');
n('O-New', 'O-New', 'For every generated root fresh for Θ, some S places c⁺ at S@g and c⁻ at S̄@ḡ.', 'Proposal §2.5. The clause is universal over fresh roots, harmless because all roots of a family obey the same laws. The soup picks the least unused root.', DEF, 'new_0 in Cycle.', 'relation/Relation.v: o_new');
n('O-New.cfresh', 'c fresh for Θ', 'The new name is no end of Θ.', 'As the old O-New (progress.md, S3 creation).', DEF, 'c⁺, c⁻ ∉ dom Θ.', 'relation/Relation.v: cfresh');
n('O-New.forall', 'For every fresh root', 'The obligation holds at every fresh root of the family.', 'Placement is a function of the run, the same at every index (§4).', 'Choosing the point per index breaks lock freedom (C1, §4.2).', '∀ g, gfresh ℓ g Θ.', 'relation/Relation.v: o_new');
n('O-New.gfresh', 'g fresh for Θ', 'g is the root of no point of Θ.', 'A generated root reused after a link renamed its channel is ruled out by roots from a supply separate from channel names (#41).', DEF, 'gfresh ℓ g Θ.', 'relation/Relation.v: gfresh');
n('O-New.dual', 'Dual placement', 'c⁺ at S@g, c⁻ at dual S at ḡ.', 'Not documented.', DEF, 'new_env c S (pgen ℓ g) Θ.', 'relation/Relation.v: new_env');
n('O-NewAt', 'O-NewAt', 'The anchor is held at x, and the new channel goes to x·κ and (x·κ)‾.', 'Nothing to pick, placement is deterministic (proposal §2.5).', DEF, 'new_0 c at ρ gives d at ρ·0.', 'relation/Relation.v: o_new_at');
n('O-NewAt.held', 'Anchor held', 'Θ holds the anchor and gives its point.', 'Progress.md, S3 creation.', DEF, 'Θ(c) = S₀@ρ.', 'relation/Relation.v: o_new_at');
n('O-Spawn', 'O-Spawn', 'Θ splits into the child\'s part, whose ends are exactly M, and the parent\'s rest. The thunk is in Vthunk at the parent\'s level.', 'Q3 and the decisions after S5.5 and S5.6.', DEF, 'spawn (λ_. close d′) gives the child {d′}.', 'relation/Relation.v: o_spawn');
n('O-Spawn.split', 'Θ = Θ_M ⊎ Θ_r', 'A disjoint split between child and parent.', 'Not documented beyond §2.7.', DEF, 'Θ_M = {d′}.', 'relation/Relation.v: o_spawn');
n('O-Spawn.transfer', 'dom Θ_M = M', 'The part that leaves is exactly the transfer set of the label.', 'Decision Q3. The transfer set is the one index-free source of the split.', 'Without it, a thread can give an end neither side mentions to either side at different indices, so ownership is not the same at every index (§2.7).', 'O-Send and O-Spawn read M off the label.', 'relation/Relation.v: o_spawn, o_send');
n('O-Spawn.thunk', 'Thunk in Vthunk', 'The thunk is a λ in Vthunk at the parent\'s level.', 'Progress.md, S3 spawn. In κ_L the child is read inside the parent\'s fixpoint, which rejects the infinite spawn chain (#40).', DEF, 'Vthunk n … ΘM v.', 'relation/Relation.v: o_spawn');
n('O-Send', 'O-Send', 'The subject is at a send head. The rest of Θ splits into the payload\'s ends M and the remainder. The payload is in V at the payload type, the continuation at the rest with o at S@x⁺.', 'Q3. Ownership at a send follows the transfer set.', DEF, 'send ⟨a, y⟩ in GrowRing.', 'relation/Relation.v: o_send');
n('O-Send.split', 'Θ ∖ o = Θ_M ⊎ Θ_r', 'The subject is not part of the payload.', 'A send hands on held ends other than its subject (F17).', 'A hole that sends its own subject (#34).', 'delete o Θ = ΘM ∪ Θr.', 'relation/Relation.v: o_send');
n('O-Send.payload', 'Payload level', 'The payload is read at the level of the continuation, n − κ(give). n in κ_DF, n − 1 in κ_L.', 'Progress.md, S3 payload level.', DEF, 'at_cost_V n (c_give κ).', 'relation/Relation.v: o_send');
n('O-Send.shift', 'o moves to x⁺', 'The subject continues at S@x⁺.', 'Program order of one end.', DEF, '<[o := (S, x⁺)]> Θr.', 'relation/Relation.v: o_send');
n('O-Recv', 'O-Recv', 'For every lower level and every incoming value in V with fresh ends, the continuation is in E with those ends added.', 'Not documented beyond §2.8.', DEF, 'let ⟨u, b⟩ = recv b in … in cli.', 'relation/Relation.v: o_recv');
n('O-Recv.forall', 'Every incoming value', 'Any value in V at the payload type at level j ≤ n − κ(take) with ends disjoint from Θ.', 'c_take_pos keeps this read below n.', DEF, '∀ j Θin.', 'relation/Relation.v: o_recv');
n('O-Recv.level', 'Continuation at level j', 'The continuation is in E at level j, the subject at S@x⁺ and the incoming ends added.', 'Not documented.', DEF, 'El j W (<[o := (S, x⁺)]> Θ ∪ Θin).', 'relation/Relation.v: o_recv');
n('O-Close', 'O-Close', 'The end leaves the environment.', 'Not documented.', DEF, 'close c⁺.', 'relation/Relation.v: o_close');
n('O-Select', 'O-Select', 'The end moves to (x·κᵢ)‾ at Sᵢ.', 'Not documented.', DEF, 'select_true o.', 'relation/Relation.v: o_select');
n('O-Branch', 'O-Branch', 'For the choice the step took, the end moves to x·κᵢ at Sᵢ. It costs κ(take).', 'Not documented.', DEF, 'branch o.', 'relation/Relation.v: o_branch');
n('O-Link', 'O-Link', 'Both linked ends leave the environment.', 'Not documented.', DEF, 'link ⟨c⁺, d⁻⟩.', 'relation/Relation.v: o_link');
n('O-Link.distinct', 'o₁ ≠ o₂', 'A self link is rejected.', 'The label may be degenerate (comment in Semantics.v).', DEF, 'link ⟨c⁺, c⁺⟩ is in no E.', 'relation/Relation.v: o_link');
n('O-Link.dual', 'Dual at dual points', 'The ends sit at x and x̄ with dual types up to annotations.', 'Not documented beyond §2.8.', DEF, 'c⁺ at S@x, d⁻ at S̄@x̄.', 'relation/Relation.v: o_link');
n('rd.stable', 'stable', 'Every step of the term is a session offer.', 'Readiness speaks of terms that wait.', DEF, 'recv b is stable, (λx.x) ∗ is not.', 'relation/Readiness.v: stable_t');
n('rd.offered', 'offered', 'o is held and is a subject of some step of the term.', 'Progress.md, S3 readiness. Each end has one entry, so no shape test picks an entry.', DEF, 'recv b offers b.', 'relation/Readiness.v: offered_t');
n('rd.value', 'No offer means a value', 'A stable term that offers no held end is a value.', 'A stable term offering only on ends it does not hold would be stuck.', DEF, 'close q with q not held is not ready.', 'relation/Readiness.v: ready_t');
n('rd.link', 'A link redex compares nothing', 'A term at a link is ready.', 'Proposal §2.6 states that a link redex compares nothing. A further rationale is not documented.', DEF, 'link ⟨c⁺, d⁻⟩.', 'relation/Readiness.v: link_t');
n('rd.below-rest', 'below_rest', 'Every offered end lies below the partner point of every held end it does not offer, and below every point of the future.', 'Proposal §2.6. It excludes circular waiting.', 'Client and server each blocked on their second channel while holding the first, if the order were cyclic.', 'Cycle. close c at ρ while d is held at ρ·0 needs ρ ≺ (ρ·0)‾.', 'relation/Readiness.v: below_rest');
n('rd.below-held', 'Below held partners', 'x ≺ x̄′ for every held end o′ at x′ that is not offered.', 'End points (W1). Readiness asks u ≺ v̄.', DEF, 'ρ ≺ (ρ·0)‾.', 'relation/Readiness.v: below_rest');
n('rd.below-future', 'Below the future', 'x ≺ y for every y in F.', 'The context acts at F after the term.', DEF, 'κ ≺ φ in between.', 'relation/Readiness.v: below_rest');
n('rd.p-stable', 'stable process', 'The process takes no τ step.', 'Not documented.', DEF, 'A thread at an external recv.', 'relation/Readiness.v: stable_p');
n('rd.p-term', 'No offer means terminated', 'A stable process that offers no interface end is terminated.', 'Not documented.', DEF, '(∅, {∗}).', 'relation/Readiness.v: ready_p');
n('rd.above-offered', 'above_offered', 'Every interface end not offered has an offered end below its partner point.', 'Proposal §2.6.', DEF, 'above_offered W Σ off.', 'relation/Readiness.v: above_offered');
n('P.strict', 'Strict later worlds only', 'Each unfolding of P holds in every strict W₁ ⊒ W.', 'Decision after S4.15. With every W₁ ⊒ W, Q-Recv can deliver ends at points only a cyclic world orders, each component is ready round the cycle, and P-Connect and Internalize fail. adequacy and live_adequacy gain strict W.', 'S4.15. p₁ holding r⁺ and a⁺, p₂ holding a⁻ and d⁺, in W′ with x ≺ z the composite after receiving d⁻ on r⁺ is stuck.', 'Pbody asks strict W1.', 'relation/Relation.v: Pbody');
n('P.fuse', '(fuse)', 'Every unfolding of P holds after every fusion h, D with fuse_ok, at sdrop D (h Σ) and pfuse h D p.', 'Decision after S4.18. With (rename) alone, h may join two unrelated interface ends into one channel and P-Connect fails. Closure by definition makes the renaming of P a projection (Q16, after S4.12).', 'S4.18. close (send ⟨∗, d⁺⟩) ∥ let ⟨u, y⟩ = recv e⁺ in close y, with h mapping d and e onto one channel, has a τ message at unadvanced interface types.', 'Prel_fuse, Prel_internalize.', 'relation/Relation.v: Pbody');
n('P-Stop', 'P-Stop', 'An irreducible process has no restricted channel, a main value in V and only ∗ elsewhere.', 'Not documented.', DEF, '(∅, {∗, ∗}) at T = ∗.', 'relation/Relation.v: Pclauses');
n('P-Ready', 'P-Ready', 'A reducible process is ready against its interface.', 'B2.', DEF, 'ready_p W1 Σ p.', 'relation/Relation.v: Pclauses');
n('P-Step', 'P-Step', 'Every instrumented step of every lifting meets its obligation.', 'Progress.md, S3 process steps. P quantifies over istep of every lifting, not over pspec.', DEF, 'Psteps.', 'relation/Relation.v: Psteps');
n('fuse.dcomm', 'h commutes with duality', 'h(ō) is the partner of h(o).', 'Q16. Needed for P, where restricted channels and the partners of Q-Send and Q-Recv enter (progress.md, S4 Q16 for terms).', DEF, 'csub o₁ o₂ commutes with duality.', 'relation/Relation.v: dcomm');
n('fuse.inj', 'Injective on held ends', 'h never merges two held ends.', 'Q16 refinement after S4.10. csub fuses ō₁ and o₂, so no bijection covers it, but it is injective on the other component\'s held ends.', DEF, 'pren_ok_csub.', 'relation/Relation.v: fuse_ok');
n('fuse.partners', 'Partners only on D', 'Two held ends become partners only if they were, or their channel lies in D.', 'S4.18. Without it, h joins unrelated interface ends into one channel.', 'The S4.18 counterexample.', 'D = ∅ forbids new pairs.', 'relation/Relation.v: fuse_ok');
n('fuse.D', 'D apart from C', 'The newly restricted channels are new.', 'Not documented.', DEF, 'D ## set_map (gch h) p.1.', 'relation/Relation.v: fuse_ok');
n('fuse.dpairs', 'dpairs', 'Both ends of every channel of D are in the renamed interface, at dual points and dual types.', 'They become restricted, so they must be a well-typed pair.', DEF, 'Internalizing c with c⁺ : S@x, c⁻ : S̄@x̄.', 'relation/Relation.v: dpairs');
n('Q-Tau', 'Q-Tau (Q-Admin, Q-Comm)', 'A τ step keeps the interface and costs ev_cost.', 'Progress.md, S3. Q-Admin and Q-Comm are one clause.', DEF, 'msg between two threads costs κ(give) + κ(take).', 'relation/Relation.v: q_tau');
n('Q-Send', 'Q-Send', 'An external send. Interface ends of the payload leave Σ, restricted ends of the payload leave C, and the partners left behind join the interface.', 'Not documented beyond §2.8.', DEF, 'Sending a restricted end d⁺ puts d⁻ into the interface.', 'relation/Relation.v: q_send');
n('Q-Send.theta-e', 'dom Θ_e = M ∩ ends(C)', 'The restricted ends that leave are those of the transfer set.', 'B8. Read from the transfer set of the label.', DEF, 'Θe = {d⁺}.', 'relation/Relation.v: q_send');
n('Q-Send.split', 'send_split', 'Θ_e and its partners Σ_e at dual types and points, Σ_e for those partners that stay.', 'Not documented.', DEF, 'Σe = {d⁻}.', 'relation/Relation.v: send_split');
n('Q-Send.sigma-e', 'Σ_e joins the interface', 'Partners of extruded ends become interface ends.', 'Scope extrusion.', DEF, 'd⁻ joins Σ.', 'relation/Relation.v: q_send');
n('Q-Recv', 'Q-Recv', 'For every incoming environment and value, the process continues with the received ends added and the channels both of whose ends it now holds restricted.', 'Not documented beyond §2.8.', DEF, 'Receiving d⁻ while holding d⁺ restricts d.', 'relation/Relation.v: q_recv');
n('Q-Recv.ok', 'recv_ok', 'Incoming ends are new, and those whose partner is held are dual at dual points.', 'Not documented.', DEF, 'recv_ok Σ Θ2.', 'relation/Relation.v: recv_ok');
n('Q-Recv.back', 'recv_back', 'Channels whose partner end the process holds or receives along become restricted.', 'Not documented.', DEF, 'recv_back Σ Θ2.', 'relation/Relation.v: recv_back');
n('Q-Recv.env', 'recv_env', 'The interface after the receive, without the ends that became internal.', 'Not documented.', DEF, 'recv_env Σ Θ2.', 'relation/Relation.v: recv_env');
n('Q-Link', 'Q-Close, Q-Select, Q-Branch, Q-Link', 'The interface versions of the term obligations.', 'Not documented.', DEF, 'q_link removes both ends from Σ.', 'relation/Relation.v: q_close, q_select, q_branch, q_link');
n('sj.at', 'Judgment at a set of points', 'In every later world, at every level, for every grounding disjoint from Θ, the instance is in E at the union of environments.', 'Progress.md, S4. The form of the old semantic rules.', DEF, 'sem_typed_at.', 'compat/SemTyped.v: sem_typed_at');
n('sj.grel', 'Grounding G', 'A substitution of values in V for Δ that splits an environment among them.', 'Progress.md, S4 groundings. It has no notation in Appendix A.', DEF, 'Grel κ n W Θ Δ γ.', 'compat/SemTyped.v: Grel');
n('sj.den', 'Denotation of a static future', 'The future variable stands for an arbitrary set ρ φ, the ⊥ flag for an arbitrary set B.', 'Progress.md, S4 static futures. pbot (W8) is not used, because a point no world orders does not survive the Kripke quantifier of E.', DEF, 'sf_den ρ B F.', 'compat/SemTyped.v: sf_den');
n('sj.term', 'Θ ; Δ ⊨ t : T and ⊫', 'The semantic term judgment, ⊨ at κ_DF and ⊫ at κ_L.', 'A.2. Θ enters erased of credits.', DEF, 'fundamental concludes it.', 'compat/SemTyped.v: sem_typed');
n('sj.proc', 'Σ ⊨_W p : T and ⊫_W', 'p is in P at every level.', 'A.2.', DEF, 'fundamental_proc concludes it.', 'relation/Adequacy.v: sem_ptyped');
n('fu.zero', 'Fuel at level 0', 'Every term has fuel at level 0.', 'Step indexing.', DEF, 'FuelE_0.', 'fuel/Fuel.v: mk_flevel');
n('fu.rty', 'Result σ', 'The credited type of the returned value, or thread, which returns holding no end.', 'Progress.md, S6 threads. RThread replaces CAny (T4, #37).', DEF, 'RThread for a soup thread.', 'fuel/Fuel.v: rty');
n('fu.frame', 'Frame d', 'The channel actions the term may still perform before it returns.', 'Frame.v, bind_needs_bound (#28). Context ticks need a frame.', DEF, 'A thread has frame ∞.', 'fuel/Fuel.v: Fdef');
n('fu.reserve', 'Reserve r', 'The tickets the term must still hold when it returns.', 'Not documented beyond the comment in Fuel.v.', DEF, 'A thread has reserve 0.', 'fuel/Fuel.v: Fdef');
n('fu.Pi', 'Protocols Π', 'The session type of each held end, with annotations.', 'Q11 and S6 protocols. Π is chosen per index next to the live environment A in the soup (decision after S8).', DEF, 'Π = {a ↦ Sa}.', 'fuel/Fuel.v: penv');
n('fu.phi', 'Counters φ', 'A counter per held end, in ℕ ∪ {∞}.', 'F8 and A10. Counters belong to held ends, only the holder writes them.', DEF, 'φ = {a ↦ 3}.', 'fuel/Fuel.v: cenv');
n('fu.tk', 'Tickets tk', 'The thread\'s count of link tickets.', 'F13. Tickets bound link chatter (#5, #39).', DEF, 'tk = 0 in the examples.', 'fuel/Fuel.v: Fdef');
n('fu.refill-kripke', 'Every refill above N', 'FuelE holds at every refill N′ above N in the order rle, finite refills by ≤ and ∞ above ∞ only.', 'Decision "fuel is Kripke in the refill" and its refinement after S7.5. Plain monotonicity in N fails at receive, and ≥ on ℕ ∪ {∞} lets a finite refill jump to ∞, where a received box promises nothing at finite instances.', 'S7.5. A thread at N = 2 forcing a received box at a finite instance has no fsem when the refill may jump to ∞.', 'rle (Some 2) (Some 3).', 'fuel/Fuel.v: rle, Fdef');
n('fu.rename', 'Injective renamings', 'FuelE holds for every renaming g injective on the held ends.', 'F15 and S6 renamings. A link renames the partner of the removed end in another thread.', 'Merging two held ends by a renaming (#25).', 'kinj g Π.', 'fuel/Fuel.v: kinj, renk');
n('fu.val', '(val)', 'A value holds the reserve and is in FV at σ.', 'Not documented.', DEF, 'r ≤ tk.', 'fuel/Fuel.v: Fdef');
n('fu.step', '(step)', 'Every step meets its fuel obligation at level n.', 'Not documented.', DEF, 'Fobl.', 'fuel/Fuel.v: Fdef, Fobl');
n('fu.oneclock', 'Every step costs one level', 'β, new, spawn and link included.', 'Decision Q10 (b), after S6. One clock fails at E-Box. The box !(f = force f) types at cost 0 and only takes β steps, so cost_fundamental would need a guard premise.', DEF, 'F-Beta at level n.', 'fuel/Fuel.v: Fdef');
n('F-Wait', 'F-Wait', 'No action on an idle end.', 'Decision Q5 (b), corrected form.', DEF, 'An end at Skip cannot act.', 'fuel/Fuel.v: f_act');
n('F-Tick', 'F-Tick', 'An action on o asks every other non-idle end of the thread to have a counter of at least 1.', 'F8. Endless postponement (#7) and endless delegation (#8). A send is an action on o, so F-Tick enforces φ|M ≥ 1 at a send (proposal §2.10).', 'A holder that loops on other ends forever while its partner waits (#7).', 'fuel_tick, fuel_zero_act.', 'fuel/Fuel.v: f_act, fspare');
n('F-Tick.frame', 'Frame ≥ 1', 'The frame has a unit for the action.', 'Context ticks without a frame (#28).', DEF, 'fle (Some 1) d.', 'fuel/Fuel.v: f_act');
n('fu.refillop', 'refill', 'o goes to N, every other counter ticks by one, truncated at 0.', 'F8. Counters evolve by one index-free update (§4.4).', DEF, 'refill 3 a {a ↦ 1, b ↦ 2} = {a ↦ 3, b ↦ 1}.', 'fuel/Fuel.v: refill');
n('fu.idle', 'idle', 'A session type that unfolds to Skip.', 'Q5 (b). Idleness only removes the ≥ 1 checks, never changes how a counter evolves (#44).', 'An idle end whose credit stayed fixed while its counter ticks would exceed the counter (idle_age_cex). So the typing ages idle ends by truncation at 0 (age_idle), and the controller (#20) is being retyped with it.', 'idle Skip.', 'fuel/Fuel.v: idle');
n('F-Beta', 'F-Beta', 'The continuation at the same state, one level lower.', 'Q10 (b).', DEF, 'f_beta.', 'fuel/Fuel.v: f_beta');
n('F-New', 'F-New', 'Both new ends at N with dual protocols.', 'Not documented beyond §2.10.', DEF, 'new_0 adds c± at N.', 'fuel/Fuel.v: f_new');
n('F-New.fresh', 'Fresh against the thread', 'The new name is fresh against the thread\'s own maps.', 'F16. new reusing a held name (#26, Collide.v).', DEF, 'ffresh c Π φ.', 'fuel/Fuel.v: ffresh');
n('F-New.cnew', 'New counters N', 'c⁺ and c⁻ start at N.', 'One refill (Q4).', DEF, 'cnew N c φ.', 'fuel/Fuel.v: cnew');
n('F-Spawn', 'F-Spawn', 'The child takes M with counters minus one and ⌈tk/2⌉ tickets and runs as a thread, the parent keeps ⌊tk/2⌋.', 'F13 and Q3.', DEF, 'LFCycle. The thunk takes d′ at 1.', 'fuel/Fuel.v: f_spawn');
n('F-Spawn.held', 'M ⊆ dom φ', 'Only held ends are handed on.', 'F17.', 'A box hiding channel constants (#32).', 'M = {d′}.', 'fuel/Fuel.v: f_spawn');
n('fu.fspare', 'fspare M', 'Every handed counter of a non-idle end is at least 1.', 'Proposal §2.10, no hand-over at counter 0. A spawn is no action, so this is the only enforcement there.', 'A hop at counter 0 under truncation passes 0 again for free and an end travels forever (#9).', 'fuel_zero_nospawn, fuel_zero_nosend.', 'fuel/Fuel.v: fspare');
n('F-Spawn.child', 'The child', 'v ∗ has thread fuel at its part of Π, counters minus one, ⌈tk/2⌉ tickets.', 'Not documented beyond §2.10.', DEF, 'App v EUnit.', 'fuel/Fuel.v: f_spawn');
n('fu.fhand', 'fhand', 'Handed counters lose one.', 'Every counter passed on is the holder\'s minus one with no truncation, which fuel_step of adequacy uses.', DEF, 'fhand {a} {a ↦ 3} = {a ↦ 2}.', 'fuel/Fuel.v: fhand');
n('F-Spawn.tickets', 'Ticket split', 'Child ⌈tk/2⌉, parent ⌊tk/2⌋.', 'F13. The fixed split is the only index-free split (proposal §3.4).', DEF, 'tk = 3 gives 2 and 1.', 'fuel/Fuel.v: f_spawn');
n('F-Send', 'F-Send', 'An action on o that hands on M with counters minus one, the payload in FV at its type and floor, the continuation with o refilled.', 'Proposal §2.10.', DEF, 'send ⟨a, y⟩ in LFGrowRing.', 'fuel/Fuel.v: f_send');
n('F-Send.notsubj', 'M ⊆ dom φ ∖ {o}', 'A send hands on held ends other than its subject.', 'F17 and #34.', 'A hole that sends its own subject or an end its context holds (#34).', 'M = {a}.', 'fuel/Fuel.v: f_send');
n('F-Send.payload', 'Payload in FV', 'The payload is in FV at the raw payload type T^b with its handed maps.', 'Progress.md, S6 payloads. FV reads no point, so the raw type and payload_at agree.', DEF, 'Vl n′ N (RTy T b).', 'fuel/Fuel.v: f_send');
n('F-Recv', 'F-Recv', 'An action on o that continues for every incoming value in FV at every lower level.', 'Not documented beyond §2.10.', DEF, 'recv b in the client loop.', 'fuel/Fuel.v: f_recv');
n('F-Recv.forall', 'Every incoming value', 'Any value at level j ≤ n with fresh maps.', 'Q15 makes every value of FV exact, so incoming closures hold what they mention.', 'fw_counterexample (S7.1). dead_thunk o is in FV, and after receiving it fw cannot spawn it.', '∀ j Πi φi.', 'fuel/Fuel.v: f_recv');
n('F-Close', 'F-Close, F-Select, F-Branch', 'Actions that advance Π at o and refill o, or drop o and tick the rest at a close.', 'Not documented.', DEF, 'close c⁺.', 'fuel/Fuel.v: f_close, f_select, f_branch');
n('F-Link', 'F-Link', 'Linked ends must be held at dual protocols, and one ticket is spent.', 'F13 and the decision after S8.3.', DEF, 'link_tickets_fall.', 'fuel/Fuel.v: f_link');
n('F-Link.plink', 'plink', 'The two ends hold dual protocols up to ≃ with annotations.', 'Decision after S8.3. O-Link compares only up to annotations, and a credit mismatch at a link breaks the payload credit of a later message in the soup.', 'After linking o₁ and o₂ the partners form one channel, dual only if o₁ and o₂ were.', 'plink Π {o1; o2}.', 'fuel/Fuel.v: plink');
n('F-Link.ticket', 'tk ≥ 1', 'A link spends one ticket.', 'F13. Tickets are conserved and spent (#39).', 'A box that links once per round forever (c3_link_loop_not_tix, #5).', 'tk − 1.', 'fuel/Fuel.v: f_link');
n('FV-Sess', 'FV at S@x', 'An end with protocol S′ ≃ S and counter at least the credit.', 'Credits are lower bounds on counters (§2.11).', DEF, 'o at (S@x)^2 with counter 3.', 'fuel/Fuel.v: Vty TSess');
n('FV-Sess.counter', 'a ≤ f', 'The counter meets the credit.', 'Not documented beyond §2.11.', DEF, '2 ≤ 3.', 'fuel/Fuel.v: Vty TSess');
n('FV-Arrow', 'FV at an arrow', 'A closure whose body has fuel for every argument, refill above N, lower level and counters at or above the floor.', 'Proposal §2.11.', DEF, 'A loop body at cost ∞.', 'fuel/Fuel.v: Vty TLolli');
n('FV-Arrow.exact', 'fends e = dom Π', 'The closure holds exactly the ends it mentions.', 'Decision Q15, agreed explicitly. It mirrors Q14.', 'fw_counterexample (v2/cost/FuelGap.v on redesign-s7). Without it fsem_of_cost is false.', 'dead_thunk_rejected.', 'fuel/Fuel.v: Vty TLolli');
n('FV-Arrow.floor', 'Counters ≥ h + a', 'Captured counters meet floor plus credit.', 'T2.', DEF, 'h = 1, a = 1.', 'fuel/Fuel.v: Vty TLolli');
n('FV-Arrow.body', 'Body fuel', 'The body has fuel at U with frame c for every ticket count that meets ϑ.', 'Not documented beyond §2.11.', DEF, 'meets t r tk.', 'fuel/Fuel.v: Vty TLolli');
n('FV-Box', 'FV at a box', 'A box with no ends whose body has fuel per force at every session instance.', 'Progress.md, S6 boxes.', DEF, 'ring at N = 4.', 'fuel/Fuel.v: Vty TBox');
n('FV-Box.noends', 'fends e = ∅', 'A box mentions no end.', 'Decision Q15.', DEF, 'ring.', 'fuel/Fuel.v: Vty TBox');
n('FV-Box.body', 'Body per force', 'e[!e] has fuel for every refill above N, lower level and instance in sinsts N′.', 'Progress.md, S6 boxes and S7.5.', DEF, 'sinsts N′ ss.', 'fuel/Fuel.v: Vty TBox');
n('FV-Thread', 'Thread result', 'A finished thread holds no end.', 'Replaces CAny (T4).', DEF, 'Π = φ = ∅.', 'fuel/Fuel.v: Vres');
n('fu.fsem', 'fsem', 'A thread has fuel at every level with every held end at N and one ticket count.', 'The per-thread fuel premise LF needs, obtained from typing by fsem_of_cost, never asked by ⊩ (2026-11-18).', DEF, 'fw_fsem.', 'fuel/Fuel.v: fsem');
n('cs.csem', 'csem', 'For every refill above N, level, injective renaming of Θ, grounding in FV and ticket count meeting ϑ, the instance has fuel at T^a with frame c.', 'Progress.md, S7 the semantic judgment. It reads no Γ, world or future, because FuelE reads none of them.', DEF, 'cost_fundamental concludes it.', 'cost/CostSem.v: csem');
n('sp.state', 'Soup state', 'q a configuration with thread ids, K the ownership, tk the tickets per thread.', 'F20 and progress.md S8 ownership. Rank and counters of adequacy are read off owners, so ownership is fixed outside the index.', 'Placement per index starves main in C1 (§4.2).', 'LFState q K tk.', 'soup/State.v: lfstate');
n('sp.hold', 'hold', 'The holder thread, point and counter of a held end.', 'Progress.md, S8 ownership.', DEF, 'Hold 0 ρ (Some 2).', 'soup/State.v: hold');
n('sp.tk', 'Tickets per thread', 'tk t for each thread.', 'Not documented.', DEF, 's_tk a t.', 'soup/State.v: s_tk');
n('sp.exists', 'Chosen per index', 'The environment A, the protocols Π and the result types U are chosen at each index.', 'Decision after S8. O-New and F-New pick the session type of a new channel by separate existentials, so Π cannot be read off A.', DEF, '∃ A Π U.', 'soup/Soup.v: Soup');
n('sp.prim', 'sp_prim', 'The result type is prim.', 'F22.', 'main returning an end (#19).', 'prim ∗.', 'soup/State.v: sp_prim');
n('sp.rel', 'sp_rel', 'Every thread is in E[live] at its part of A, at the empty future.', 'Proposal §2.12. The per-thread live relation rejects the infinite spawn chain (#40).', DEF, 'Erl (kres K t A) (U t) e.', 'soup/State.v: sp_rel');
n('sp.ty', 'sp_ty', 'Each thread returns T or ∗.', 'Not documented.', DEF, 'main at T, spawned at ∗.', 'soup/State.v: sp_ty');
n('sp.fuel', 'sp_fuel', 'Every thread has thread fuel at its part of Π, its counters from K and its tickets.', 'Proposal §2.12.', DEF, 'Frl (kres K t Π) (ctrs K t) (tk t) e.', 'soup/State.v: sp_fuel');
n('sp.pts', 'sp_pts', 'The points of A are those of K.', 'Points are fixed outside the index (§4.2).', DEF, 'snd <$> A = h_pt <$> K.', 'soup/State.v: sp_pts');
n('sp.dom', 'sp_dom', 'Π and K have the same ends.', 'Not documented.', DEF, 'dom Π = dom K.', 'soup/State.v: sp_dom');
n('sp.owner', 'sp_owner', 'Every holder is a thread of q.', 'Not documented.', DEF, 'is_Some (q.2 !! h_th).', 'soup/State.v: sp_owner');
n('sp.closed', 'sp_closed', 'A held end is restricted or in the interface.', 'Not documented.', DEF, 'ech o ∈ C ∨ o ∈ Σ.', 'soup/State.v: sp_closed');
n('sp.pair', 'sp_pair', 'An internal end\'s partner is held.', 'Proposal §2.12, per channel.', DEF, 'Both ends of c in LFClose.', 'soup/State.v: sp_pair');
n('sp.sdual', 'sp_sdual', 'Internal partners sit at dual points with session types dual up to annotations.', 'Proposal §2.12.', DEF, 'x′ = x̄.', 'soup/State.v: sp_sdual');
n('sp.pdual', 'sp_pdual', 'Internal partners hold protocols dual up to ≃ with annotations.', 'Progress.md, S8 the protocol map. Adequacy reads idleness off Π, and idle_dual transfers it across a pair.', DEF, 'Π(c⁻) ≃ dual Π(c⁺).', 'soup/State.v: sp_pdual');
n('sp.sig', 'sp_sig', 'Interface ends are held at their entry of Σ.', 'Not documented.', DEF, 'A !! o = Σ !! o.', 'soup/State.v: sp_sig');
n('sp.psig', 'sp_psig', 'Interface ends hold their session type of Σ in Π.', 'Progress.md, S9 the exact cut.', DEF, 'Π !! o = Some S.', 'soup/State.v: sp_psig');
n('sp.fin', 'sp_fin', 'Every counter in K is finite.', 'Progress.md, S8 finite counters. The measure of adequacy reads a counter as a natural number.', DEF, 'is_Some h_ctr.', 'soup/State.v: sp_fin');
n('sp.lfsem', 'Σ ⊪_W p : T', 'Some refill and state erase to p, and the state is in the soup at every index.', 'Q12, decided 2026-11-18. LF drops the process conjunct, and soup_no_tau_divergence gives what it was kept for.', DEF, 'lf_fundamental concludes it.', 'soup/Soup.v: lf_sem');
n('sp.exists-before-forall', '∃ before ∀ n', 'N and the state a are fixed before the index quantifier.', 'F20. Ownership, points and counters must be the same at every index (§4.2).', 'C1 without a ceiling. A placement chosen per index lets main starve in every fair run (§4.2).', '∃ N a, … ∀ n.', 'soup/Soup.v: lf_sem');
n('sp.next', 'lf_next', 'The index-free update along an event. Creation places new ends with counter N, actions move and refill, transfers move with counter minus one, links spend a ticket and rename, spawns split tickets.', 'Proposal §2.12. lfsoup_step preserves the soup along it.', DEF, 'lfsoup_step.', 'soup/Soup.v: lf_next');
