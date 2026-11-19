// Draft notation for the typing rules, shown at the end of the typing section for review.
// Pure notation over the current rules: every abbreviation unfolds to their premises.
const core = require('./core');
const { R, h, n, sa, DEF } = core;
const { awb } = require('./typing');
const s = core.sections.find(x => x.id === 'typing');
const block = b => core.block(s, awb(b));
const A = (name, meaning) => ({ name, meaning });
const Q = R`\\ `;
const rule = (name, prem, concl) => core.rule(name, R`\begin{array}{c}${prem}\end{array}`, concl);

// the judgment Γ ; Δ ∥ H ⊢^F e : T ! ε, with W and N fixed for the whole derivation
const HOLD = H => H ? R` ${h('dr.held', R`\parallel ${H}`)}` : '';
const J = (G, D, H, F, e, T, eff) => R`${G} ; ${D}${HOLD(H)} \vdash^{${F}} ${e} : ${T}\annot{\ ${h('dr.eff', '!')}\ ${eff}}`;

block({
  id: 'dr-notation', title: 'Draft notation for readable rules', rocq: 'static/Typing.v: typed (unfolded)',
  tex: R`\begin{array}{l}
${h('dr.judg', R`\Gamma ; \Delta \parallel H \vdash^{F} e : T\annot{\ !\ \varepsilon}`)} \\
${h('dr.held', R`\Delta \parallel H \vdash^{F} e\ \ \equiv\ \ \Delta \vdash^{F \cup \mathsf{heads}(H)} e\annot{\ \land\ H - c\ \mathrm{defined}}`)} \\
\annot{${h('dr.eff', R`\varepsilon = (c, \vartheta)`)} \qquad ${h('dr.seq', R`\varepsilon_1 \cdot \varepsilon_2 = (c_1 + c_2,\ \vartheta_1 \circ \vartheta_2)\ \ (\mathsf{tok}\,\vartheta_1\,\vartheta_2)`)} \qquad ${h('dr.zero', R`0 = (0, \hat 1)`)}}
\end{array}`,
  caption: 'One linear context $\\Delta$ holds ends and variables, $\\Gamma$ holds facts, and $W$ and $N$ are fixed for a whole derivation. $\\parallel H$ marks what the thread holds while $e$ runs, and in the lock-free mode $! \\, \\varepsilon$ is the effect of $e$.'
});

block({
  id: 'dr-app', title: 'Draft E-App', rocq: 'static/Typing.v: e_app',
  tex: rule('E-App',
    R`${J(R`\Gamma`, R`\Delta_1`, R`\Delta_2`, 'F', R`e_1`, R`(T \multimap^{u}_{l}\annot{[\varepsilon ; h]}\, U)\annot{^{a}}`, R`\varepsilon_1`)} \\ ${J(R`\Gamma`, R`\Delta_2\annot{ - \varepsilon_1}`, R`(T \multimap^{u}_{l} U)\annot{^{a}}`, 'F', R`e_2`, 'T', R`\varepsilon_2`)}${Q}${h('E-App.ub', R`u \prec F`)}`,
    J(R`\Gamma`, R`\Delta_1, \Delta_2`, '', 'F', R`e_1\,e_2`, 'U', R`\varepsilon_1 \cdot \varepsilon_2 \cdot \varepsilon`)),
  caption: 'The thread holds $\\Delta_2$ while $e_1$ runs and the closure while $e_2$ runs. Holding gives the future and, in the lock-free mode, the aging and the credit check.'
});

block({
  id: 'dr-send', title: 'Draft E-Send', rocq: 'static/Typing.v: e_send',
  tex: rule('E-Send',
    R`${h('E-Send.unfold', R`${h('sty.unfold', R`\mathsf{unfold}`)}(S_0) = {!}(\bar\iota.\,T).S`)}${Q}${h('E-Send.heads', R`x \prec \mathsf{heads}(T[x\cdot i])`)}${Q}${h('E-Send.nobot', R`\neg${h('ty.hbot', R`\mathsf{hbot}`)}\,T`)}${Q}${h('side.act', R`x \prec F`)} \\ ${J(R`\Gamma`, R`\Delta`, '', 'F', 'e', R`T' \otimes (S_0@x)\annot{^{a}}`, R`\varepsilon`)}\annraw{${Q}}\annot{${h('dr.hop', R`T' - 1 \leq T[x\cdot i]`)}}`,
    J(R`\Gamma`, R`\Delta`, '', 'F', R`\mathsf{send}\,e`, R`(S@${h('pt.shift', R`x^{+}`)})\annot{^{N}}`, R`\varepsilon \cdot 1`)),
  caption: 'The sender waits at $x$ while it holds the payload. In the lock-free mode the payload survives one hop and the end returns refilled at $N$.'
});

block({
  id: 'dr-abs', title: 'Draft E-Abs', rocq: 'static/Typing.v: e_abs',
  tex: rule('E-Abs',
    R`${h('E-Abs.phi', R`\varphi\ \text{fresh}`)}${Q}${h('E-Abs.lb', R`l \preccurlyeq \mathsf{heads}(\Delta),\ \neg\bot_\Delta`)}\annraw{${Q}}\annot{${h('E-Abs.cap', R`\Delta \leadsto_{h,a} \Delta^{h}`)}} \\ ${J(R`\Gamma, ${h('E-Abs.phi', R`u \prec \varphi`)}`, R`\Delta\annot{^{h}}, T`, '', R`(\varnothing, \varphi)`, 'e', 'U', R`\varepsilon`)}`,
    J(R`\Gamma`, R`\Delta`, '', 'F', R`\lambda e`, R`(T \multimap^{u}_{l}\annot{[\varepsilon ; h]}\, U)\annot{^{a}}`, '0')),
  caption: 'The body runs at a later call under a fresh future. In the lock-free mode the closure records the effect of its body and restates its captured ends at the floor $h$.'
});

n('dr.judg', 'Draft judgment', '$\\Gamma ; \\Delta \\parallel H \\vdash^{F} e : T \\ ! \\ \\varepsilon$ types $e$ with the linear context $\\Delta$ of ends and variables, the facts $\\Gamma$, the held entries $H$, the future $F$ and, in the lock-free mode, the effect $\\varepsilon$.', 'The world $W$ and the refill $N$ never change inside a derivation, so they are left implicit. Ends and variables split the same way, so one context holds both.', DEF, '$\\Gamma ; a : (!\\ast.\\mathsf{Close})@\\rho \\vdash^{F} \\mathsf{send}\\,\\langle \\ast, a \\rangle : \\mathsf{Close}@\\rho^{+}$.', 'static/Typing.v: typed');
n('dr.held', 'Held entries $\\parallel H$', '$\\Delta \\parallel H \\vdash^{F} e$ types $e$ while the thread holds $H$. It unfolds to the future $F \\cup \\mathsf{heads}(H)$, and in the lock-free mode also to the aging $H - c$ by the cost $c$ of $e$.', 'Every rule that runs one part while it holds another states the same two facts about the held part. The notation states them once.', 'Without it, E-App lists the heads of the held context, the aging of that context and the credit of the closure as four separate premises.', '$\\Delta_1 \\parallel \\Delta_2 \\vdash^{F} e_1$ in E-App.', 'static/Typing.v: e_app');
n('dr.eff', 'Effect $\\varepsilon$', '$\\varepsilon = (c, \\vartheta)$ pairs the cost $c$ of a term, the number of channel actions before it returns, with its ticket need $\\vartheta$.', 'Cost and ticket need always travel together and combine in the same places, so one symbol carries both.', DEF, 'A send has effect $(1, \\hat 1)$, written $1$.', 'static/Typing.v: typed');
n('dr.seq', 'Sequencing $\\varepsilon_1 \\cdot \\varepsilon_2$', '$\\varepsilon_1 \\cdot \\varepsilon_2 = (c_1 + c_2, \\vartheta_1 \\circ \\vartheta_2)$, defined when $\\mathsf{tok}\\,\\vartheta_1\\,\\vartheta_2$.', 'A term that runs two parts in sequence adds their costs and composes their ticket needs. The side condition $\\mathsf{tok}$ becomes definedness.', DEF, '$1 \\cdot 1 = (2, \\hat 1)$.', 'types/Costs.v: tseq, tok');
n('dr.zero', 'No effect $0$', '$0 = (0, \\hat 1)$, the effect of a value.', 'A value performs no action and no link.', DEF, '$\\lambda e$ has effect $0$.', 'types/Costs.v: tid');
n('dr.hop', 'One hop', '$T\' - 1 \\leq T[x\\cdot i]$, the payload value aged by one step still has the credits the protocol promises.', 'Each send of an end lowers its counter by one, so an end cannot travel forever.', DEF, 'A payload end at credit $3$ meets a protocol that promises $2$.', 'static/Typing.v: e_send');
const aH = A('H', R`the entries the thread holds while $e$ runs`);
sa('dr.judg', R`\Gamma ; \Delta \parallel H \vdash^{F} e : T\ !\ \varepsilon`, [A(R`\Gamma`, R`the facts`), A(R`\Delta`, R`the linear context of ends and variables`), aH, A('F', R`the future`), A('e', R`the term`), A('T', R`its type`), A(R`\varepsilon`, R`its effect, lock-free mode only`)]);
sa('dr.held', R`\Delta \parallel H \vdash^{F} e \ \equiv\ \Delta \vdash^{F \cup \mathsf{heads}(H)} e\ \land\ H - c\ \mathrm{defined}`, [aH, A('c', R`the cost of $e$`)]);
sa('dr.eff', R`\varepsilon = (c, \vartheta) \in (\mathbb{N} \cup \{\infty\}) \times \mathsf{Tix}`, [A('c', R`the cost`), A(R`\vartheta`, R`the ticket need`)]);
sa('dr.seq', R`\cdot : \mathsf{Eff} \times \mathsf{Eff} \rightharpoonup \mathsf{Eff}`, [A(R`\varepsilon_1, \varepsilon_2`, R`the effects of the first and the second part`)]);
sa('dr.zero', R`0 \in \mathsf{Eff}`, []);
sa('dr.hop', R`T' - 1 \leq T[x\cdot i]`, [A(R`T'`, R`the type of the payload value`), A(R`T[x\cdot i]`, R`the payload type of the protocol at the fields of $x$`)]);
