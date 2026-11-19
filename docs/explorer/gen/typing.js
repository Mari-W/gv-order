const core = require('./core');
const { R, h, n, sa, section, DEF } = core;
// hover autowrap: wraps every symbol of a formula in \htmlData unless the
// innermost enclosing \htmlData already is its own note.
function spans(tex) {
  const out = []; const re = /\\htmlData\{k=([^}]*)\}\{/g; let m;
  while ((m = re.exec(tex))) {
    let i = re.lastIndex, d = 1;
    while (i < tex.length && d > 0) { if (tex[i] === '\\') { i += 2; continue; } if (tex[i] === '{') d++; else if (tex[i] === '}') d--; i++; }
    out.push({ s: m.index, b: re.lastIndex, e: i, k: m[1] });
  }
  return out;
}
function inner(sp, i) { let best = null; for (const x of sp) if (x.b <= i && i < x.e && (!best || x.b > best.b)) best = x; return best; }
const after = (tex, i) => tex.slice(i, i + 40);
const SF = {
  strict: 'w.strict', wfworld: 'th.wfworld', 'deadlock\\_free': 'prop.df', 'lock\\_free': 'prop.lf',
  'no\\_tau\\_divergence': 'prop.notau', prim: 'ty.prim', heads: 'ty.heads', unfold: 'sty.unfold',
  chans: 'tp.chans', Close: 'sty.close', pfree: 'pfree', meets: 'ann.meets', tok: 'ann.tok',
  erase: 'proc.erase', 'lf\\_next': 'sp.next', sinsts: 'tp.sinsts', pscoped: 'ty.pscoped',
  tfree: 'ty.tfree', unlimited: 'ty.unlimited', 'ty\\_df': 'ann.tydf', acts: 'guard.acts',
  'world\\_wf': 'w.wf', tlink: 'ann.tlink', tspawn: 'ann.tspawn', sth: 'th.sth', conn: 'th.conn',
  true: 'guard.marks', false: 'guard.marks', wk: 'E-Weak.drop', case: 'syn.case', force: 'prim.force',
  send: 'prim.send', recv: 'prim.recv', close: 'prim.close', select: 'prim.select', branch: 'prim.branch',
  link: 'prim.link', spawn: 'prim.spawn', ends: 'tp.ends', maximal: 'prop.maximal', wfair: 'prop.wfair',
  'thread\\_progress\\_run': 'th.tpr', pend: 'prop.pend', terminated: 'prop.terminated'
};
function aw(tex) {
  const sp = spans(tex);
  const re = /\\vdash\\!\\triangleright|\\mathrel\{\|\\!\\!\\vDash\}|\\Vvdash|\\Vdash|\\vDash|\\vdash(?![a-zA-Z])|\\!\\triangleright|\\triangleright|\\multimap|\\sqsupseteq|\\sqsubseteq|\\sqcup|\\uplus|\\mathsf\{new\}(?:_\\kappa|_\\ell)?|\\mathsf\{let\}|\\mathsf\{in\}|\\mathsf\{([^}]*)\}/g;
  let m, out = '', last = 0, letKey = 'syn.letp';
  while ((m = re.exec(tex))) {
    const t = m[0], i = m.index, a = after(tex, i + t.length);
    let key = null, wrapAs = 'ord';
    if (t === '\\!\\triangleright') continue;
    if (t === '\\vdash\\!\\triangleright') { key = /^\s*p(?![a-zA-Z_])/.test(a) ? 'guard.proc' : 'guard.judg'; wrapAs = 'rel'; }
    else if (t === '\\Vvdash') { key = 'sp.lfsem'; wrapAs = 'rel'; }
    else if (t === '\\Vdash') { key = 'tp.lfjudg'; wrapAs = 'rel'; }
    else if (t === '\\vDash' || t.startsWith('\\mathrel{|')) { key = /^\s*\^/.test(a) ? 'sj.term' : 'sj.proc'; wrapAs = 'rel'; }
    else if (t === '\\vdash') {
      const before = tex.slice(Math.max(0, i - 200), i);
      if (before.lastIndexOf('\\llbracket') > before.lastIndexOf('\\rrbracket')) key = null;
      else if (/^\s*\^\{(N|\\infty)\}/.test(a)) key = 'tp.pjudg';
      else if (/^\s*C\[/.test(a)) key = 'side.hold';
      else if (/^[^\\$]{0,4}\s*[a-z](_\d|')?\s*\\prec/.test(a) || /^\s*[a-z]\s*\\prec/.test(a)) key = 'ctx.slt';
      else key = 'tp.vdash';
      wrapAs = 'rel';
    }
    else if (t === '\\triangleright') { key = 'tp.tri'; wrapAs = 'bin'; }
    else if (t === '\\multimap') { key = 'ty.arrow'; wrapAs = 'rel'; }
    else if (t === '\\sqsupseteq' || t === '\\sqsubseteq') { key = 'w.ext'; wrapAs = 'rel'; }
    else if (t === '\\sqcup') { key = 'w.join'; wrapAs = 'bin'; }
    else if (t === '\\uplus') { key = /^\s*E_/.test(a) ? 'tp.msunion' : 'ctx.tsplit'; wrapAs = 'bin'; }
    else if (t.startsWith('\\mathsf{new}')) key = 'syn.new';
    else if (t === '\\mathsf{let}') { letKey = /^\\\s*\\ast/.test(a) || /^\\ \\ast/.test(a) ? 'syn.letu' : 'syn.letp'; key = letKey; }
    else if (t === '\\mathsf{in}') key = letKey;
    else if (m[1] !== undefined && SF[m[1]]) key = SF[m[1]];
    if (!key) continue;
    const inn = inner(sp, i);
    if (inn && (inn.k === key || (key === 'w.join' && inn.k === 'ctx.lsplit') || (key === 'guard.judg' && inn.k === 'guard.proc'))) continue;
    // skip if the token is the whole body of an enclosing htmlData with this key already handled above
    let w = `\\htmlData{k=${key}}{${t}}`;
    if (wrapAs === 'rel') w = `\\mathrel{${w}}`; else if (wrapAs === 'bin') w = `\\mathbin{${w}}`;
    out += tex.slice(last, i) + w; last = i + t.length;
  }
  return out + tex.slice(last);
}
function awb(b) {
  b.tex = aw(b.tex);
  if (b.variants) for (const k of Object.keys(b.variants)) b.variants[k] = aw(b.variants[k]);
  return b;
}
module.exports = { aw, awb };
const block = (sec, b) => core.block(sec, awb(b));
// premises stack one per line above the bar
const Q = R`\\ `;
const rule = (name, prem, concl) =>
  core.rule(name, prem.startsWith(R`\begin{array}`) ? prem : R`\begin{array}{c}${prem}\end{array}`, concl);
const rows = (...rs) => R`\begin{array}{c}${rs.join(R` \\[2ex] `)}\end{array}`;
const lrows = (...rs) => R`\begin{array}{l}${rs.join(R` \\ `)}\end{array}`;

const s = section('typing', 'Typing',
  'This section introduces the typing judgment $\\Gamma ; \\Delta \\parallel H \\vdash^{F} e : T \\ ! \\ \\varepsilon$, its contexts $\\Gamma$ and $\\Delta$, the held entries $H$ and the future $F$, the side conditions on points, aging $T - c$ and capture of credits, subtyping, one rule per term former, the process judgment $\\Sigma \\vdash^{N}_{W} p : T$ with the rules P-Term and P-Connect, the lock-free judgment $\\Sigma \\Vdash^{N}_{W} p : T$, and the guard $\\Lambda \\vdash\\!\\triangleright t$. Deadlock-free typing is the instance $N = \\infty$ with every annotation erased, and lock-free typing takes $N \\in \\mathbb{N}$ and adds the guard.');

// judgment builders
// the judgment Γ ; Δ ∥ H ⊢^F e : T ! ε, with W and N fixed for a whole derivation
const HOLD = H => H ? R` ${h('tj.held', R`\parallel ${H}`)}` : '';
const J = (G, D, H, F, e, T, eff) => R`${G} ; ${D}${HOLD(H)} \vdash^{${F}} ${e} : ${T}\annot{\ ${h('tj.eff', '!')}\ ${eff}}`;
const act = h('side.act', R`x \prec F`);
const CRD = a => R`\annot{^{${a}}}`;
const AGE = (D, eff) => R`${D}\annot{ ${h('age.ctx', R`- ${eff}`)}}`;
const ONE = h('tj.one', '1');
const ZERO = h('tj.zero', '0');
const SEQ = h('tj.seq', R`\cdot`);
const REF = h('act.refill', 'N');
const ARR = (T, U, eff, hh, a) => R`(${T} \multimap^{u}_{l}\annot{[${eff} ; ${hh}]}\, ${U})${CRD(a)}`;
const QH = R`\quad `;

block(s, {
  id: 't-lf-intro', title: 'What lock freedom adds to typing', rocq: 'static/Typing.v: typed; static/Guard.v: lguard; types/Worlds.v: wfworld', modes: ['lf'],
  tex: R`\begin{array}{lll}
\text{mechanism} & \text{written} & \text{rules out} \\ \hline
${h('lfi.credit', R`\text{credits}`)} & (S@x)^{a},\ (T \multimap U)^{a} & \text{a holder that acts elsewhere forever} \\
${h('lfi.cost', R`\text{cost, aging, refill}`)} & e : T\ !\ (c, \vartheta),\ \ \Delta - c,\ \ (S@x^{+})^{N} & \text{(the counting behind credits)} \\
${h('lfi.floor', R`\text{floors}`)} & T \multimap[\varepsilon ; h]\, U & \text{(credits carried into a later call)} \\
${h('lfi.hop', R`\text{hops}`)} & T' - 1 \leq T[x\cdot i],\ \ \Delta - 1 & \text{an end passed on forever} \\
${h('lfi.tickets', R`\text{tickets}`)} & \vartheta,\ \ \mathsf{tlink},\ \ \mathsf{tspawn} & \text{a waiter relinked to fresh ends forever} \\
${h('lfi.guard', R`\text{guard}`)} & \Lambda \vdash\!\triangleright t & \text{internal steps forever} \\
${h('lfi.wf', R`\text{well-founded world}`)} & \mathsf{wfworld}\,W & \text{an endless chain of waiting threads}
\end{array}`,
  caption: 'Deadlock freedom promises that some thread can always step. Lock freedom promises more, every waiting thread eventually meets its partner. A deadlock-free program can still keep one thread waiting forever while the others step, and each mechanism here rules out one way of doing that. Hover a row for the intuition and the example it rejects, which the Examples tab lists.'
});
block(s, {
  id: 't-judgment', title: 'The typing judgment', rocq: 'static/Typing.v: typed, dftyped',
  tex: R`\begin{array}{l}${h('tj.Gamma', R`\Gamma`)} ; ${h('tj.Delta', R`\Delta`)} ${h('tj.held', R`\parallel H`)} \vdash^{${h('tj.F', 'F')}} e : T\annot{\ ${h('tj.eff', '!')}\ \varepsilon} \\ ${h('tj.held', R`\Delta \parallel H \vdash^{F} e\ \ \equiv\ \ \Delta \vdash^{F \cup \mathsf{heads}(H)} e`)}\annot{\ \land\ ${h('tj.hage', R`H - c`)}\ \text{defined}} \\ ${h('tj.W', 'W')}\annot{,\ ${h('tj.N', 'N')}}\ \text{fixed for a whole derivation}\annraw{ \\ }\annot{${h('tj.eff', R`\varepsilon = (c, \vartheta)`)} \qquad ${h('tj.seq', R`\varepsilon_1 \cdot \varepsilon_2 = (c_1 + c_2,\ \vartheta_1 \circ \vartheta_2)\ \text{if}\ ${h('ann.tok', R`\mathsf{tok}`)}\,\vartheta_1\,\vartheta_2`)}}\annraw{ \\ }\annot{${h('tj.zero', R`0 = (0, \hat 1)`)} \qquad ${h('tj.one', R`1 = (1, \hat 1)`)} \qquad ${h('tp.max', R`\max(\varepsilon_1, \varepsilon_2)`)} \qquad ${h('E-Sub.cost', R`\varepsilon \leq \varepsilon'`)}}\end{array}`,
  caption: '$\\Gamma$ holds facts, $\\Delta$ the ends and variables, $F$ is the future, and $\\parallel H$ names what the thread holds while $e$ runs. The world $W$ and the refill $N$ stay fixed for a whole derivation. In the lock-free mode $\\varepsilon$ is the effect of $e$.'
});
block(s, {
  id: 't-contexts', title: 'Contexts and the fact theory', rocq: 'static/Contexts.v: tentry, tsplit, lenv_split, hctx, fl, sfuture',
  tex: lrows(R`${h('tj.Delta', R`\Delta : o \mapsto (S@x)\annot{^{a}},\ i \mapsto T`)} \qquad ${h('ctx.lsplit', R`\Delta = \Delta_1, \Delta_2`)}`, R`${h('tj.Gamma', R`\Gamma = (${h('ctx.hyps', R`(C, \bar x)^{*}`)}, ${h('ctx.fvar', R`\varphi \mapsto u`)})`)} \qquad ${h('ctx.slt', R`\Gamma \vdash x \prec y`)}`, R`${h('tj.F', R`F = (X, ${h('ctx.fvarF', R`\varphi`)} \mid ${h('ctx.bot', R`\bot`)})`)}`),
  caption: 'Every order fact a rule reads is a judgment $\\Gamma \\vdash x \\prec y$, the least transitive relation containing $\\prec_W$, the facts $C[\\bar x]$ of the instances in $\\Gamma$, and $u \\prec \\varphi$ for every $\\varphi \\mapsto u$ in $\\Gamma$.'
});
block(s, {
  id: 't-side', title: 'Side conditions on points', rocq: 'static/Contexts.v: ub_below_s, lbx_below_h, lbound_of, hold_at',
  tex: lrows(h('side.ub', R`u \prec F \iff \forall y \in X.\ \Gamma \vdash u \prec y,\ \Gamma \vdash u \prec \varphi,\ \neg\bot`), R`${h('E-Send.heads', R`x \prec T \iff \forall y \in ${h('ty.heads', R`\mathsf{heads}`)}(T).\ \Gamma \vdash x \prec y`)} \qquad ${h('side.lb', R`l \preccurlyeq \Delta \iff \forall y \in \mathsf{heads}(\Delta).\ \Gamma \vdash l \preccurlyeq y`)} \qquad ${h('side.hold', R`\Gamma \vdash C[\bar x]`)}`),
  caption: '$u \\prec F$ states that $u$ lies below every point of $F$, $x \\prec T$ that $x$ lies below every partner point of the ends in $T$, $l \\preccurlyeq \\Delta$ that $l$ lies at or below every partner point of $\\Delta$, and $\\Gamma \\vdash C[\\bar x]$ that every fact of $C$ at $\\bar x$ is derivable.'
});
block(s, {
  id: 't-age', title: 'Aging $T - c$', rocq: 'static/Contexts.v: tage, lage, thage, types/Types.v: idle', modes: ['lf'],
  tex: rows(R`${rule('Age-Free', h('age.free', R`${h('ty.tfree', R`\mathsf{tfree}`)}\,T`), R`T - c = T`)} \qquad ${rule('Age-Credit', h('age.credit', R`c \leq a`), R`(S@x)^{a} - c = (S@x)^{a - c}`)}`, R`${rule('Age-Idle', h('age.idle', R`${h('fu.idle', R`\mathsf{idle}`)}\,S`), R`(S@x)^{a} - c = (S@x)^{\max(a - c, 0)}`)} \qquad ${rule('Age-Arr', h('age.credit', R`c \leq a`), R`(T \multimap U)^{a} - c = (T \multimap U)^{a - c}`)}`, h('age.agg', R`(T_1 \otimes T_2) - c = (T_1 - c) \otimes (T_2 - c) \qquad (T_1 \oplus T_2) - c = (T_1 - c) \oplus (T_2 - c) \qquad (\exists^{l}\bar\iota.\,C.\,T) - c = \exists^{l}\bar\iota.\,C.\,(T - c)`)),
  caption: '$T - c$ lowers the credit of every end and closure in $T$ by $c$, asks $c \\leq a$ of every end that is not idle and of every closure, and keeps types with $\\mathsf{tfree}\\,T$. $\\Delta - c$ ages every entry.'
});
block(s, {
  id: 't-cap', title: 'Capture at E-Abs', rocq: 'static/Contexts.v: tcap, thcap', modes: ['lf'],
  tex: rows(R`${rule('Cap-Sess', h('cap.sess', R`h + a \leq a_0`), R`(S@x)^{a_0} \leadsto_{h,a} (S@x)^{h}`)} \qquad ${rule('Cap-Arr', h('cap.arr', R`h_0 \leq h \quad h + a \leq h_0 + a_0`), R`(T \multimap[\varepsilon;h_0] U)^{a_0} \leadsto_{h,a} (T \multimap[\varepsilon;h_0] U)^{h - h_0}`)}`, R`${rule('Cap-Free', h('ty.tfree', R`\mathsf{tfree}\,T`), R`T \leadsto_{h,a} T`)} \qquad ${rule('Cap-Prod, Cap-Sum, Cap-Ex', h('cap.agg', R`T_i \leadsto_{h,a} T_i'`), R`T_1 \otimes T_2 \leadsto_{h,a} T_1' \otimes T_2' \quad T_1 \oplus T_2 \leadsto_{h,a} T_1' \oplus T_2' \quad \exists^{l}\bar\iota.\,C.\,T_1 \leadsto_{h,a} \exists^{l}\bar\iota.\,C.\,T_1'`)}`),
  caption: 'A captured end needs credit at least $h + a$, and the body sees it at credit $h$.'
});
const SUBC = h('tp.sub-credit', R`a' \leq a`);
const SUBH = h('tp.sub-floor', R`h \leq h',\ h' + a' \leq h + a`);
const LE = (x, y) => h('sub.tsub', R`${x} \leq ${y}`);
const SUBLF = rows(
  rule('Sub-Sess', R`${h('tp.sub-sess', R`S ${h('sty.sequiv', R`\simeq`)} S'`)}${QH}${SUBC}`, LE(R`(S@x)^{a}`, R`(S'@x)^{a'}`)),
  rule('Sub-Arr', R`\begin{array}{c}${h('E-Sub.cost', R`\varepsilon \leq \varepsilon'`)}${QH}${SUBH} \\ ${h('tp.sub-var', R`${LE(R`T_1'`, R`T_1`)} \quad ${LE('U', R`U'`)}`)}\end{array}`,
    R`(T_1 \multimap^{u}_{l}[\varepsilon;h]\,U)^{a} \leq (T_1' \multimap^{u}_{l}[\varepsilon';h']\,U')^{a'}`),
  R`${rule('Sub-Box', R`${h('E-Sub.cost', R`\varepsilon \leq \varepsilon'`)}${QH}${h('tp.sub-teq', R`U \equiv U'`)}`, R`\Box(\forall \bar\iota\,\bar\alpha.\ C.\ \ast \multimap^{u}[\varepsilon]\,U) \leq \Box(\ldots[\varepsilon']\,U')`)} \qquad ${rule('Sub-Ex', R`${h('tp.sub-ex', R`\mathsf{facts}\,C' \subseteq \mathsf{facts}\,C`)}${QH}${h('tp.sub-teq', R`T \equiv T'`)}`, LE(R`\exists^{l}\bar\iota.\,C.\,T`, R`\exists^{l}\bar\iota.\,C'.\,T'`))}`,
  rule('Sub-Prod, Sub-Sum', h('tp.sub-agg', R`${LE(R`T_1`, R`T_1'`)} \quad ${LE(R`T_2`, R`T_2'`)}`), R`T_1 \otimes T_2 \leq T_1' \otimes T_2' \qquad T_1 \oplus T_2 \leq T_1' \oplus T_2'`));
const SUBDF = rows(
  R`${rule('Sub-Sess', h('tp.sub-sess', R`S ${h('sty.seqv', R`\approx`)} S'`), LE(R`S@x`, R`S'@x`))} \qquad ${rule('Sub-Ex', R`${h('tp.sub-ex', R`\mathsf{facts}\,C' \subseteq \mathsf{facts}\,C`)}${QH}${h('tp.sub-teq', R`T \equiv T'`)}`, LE(R`\exists^{l}\bar\iota.\,C.\,T`, R`\exists^{l}\bar\iota.\,C'.\,T'`))}`,
  R`${rule('Sub-Prod, Sub-Sum', h('tp.sub-agg', R`${LE(R`T_1`, R`T_1'`)} \quad ${LE(R`T_2`, R`T_2'`)}`), R`T_1 \otimes T_2 \leq T_1' \otimes T_2' \qquad T_1 \oplus T_2 \leq T_1' \oplus T_2'`)} \qquad ${rule('Sub-Arr', h('tp.sub-var', R`${LE(R`T_1'`, R`T_1`)} \quad ${LE('U', R`U'`)}`), R`T_1 \multimap^{u}_{l} U \leq T_1' \multimap^{u}_{l} U'`)}`,
  rule('Sub-Box', h('tp.sub-teq', R`U \equiv U'`), R`\Box(\forall \bar\iota\,\bar\alpha.\ C.\ \ast \multimap^{u} U) \leq \Box(\forall \bar\iota\,\bar\alpha.\ C.\ \ast \multimap^{u} U')`));
block(s, {
  id: 't-sub', title: 'Subtyping', rocq: 'static/Contexts.v: tsub, static/Typing.v: e_sub, d_conv',
  tex: SUBLF,
  variants: { df: SUBDF },
  caption: 'Without annotations subtyping is $\\approx$ on sessions plus dropping facts of $\\exists$. In the lock-free mode credits fall while costs, ticket needs and floors rise.'
});

// ---- term rules: one form, the lock-free parts marked ----
const T = (id, title, rocq, tex, caption) => block(s, { id, title, rocq, tex, caption });
const UNL = h('ctx.empty', R`\Delta\ \text{unlimited}`);

T('r-unit', 'E-Unit', 'static/Typing.v: e_unit, d_unit',
  rule('E-Unit', UNL, J(R`\Gamma`, R`\Delta`, '', 'F', R`\ast`, R`\ast`, ZERO)),
  '$\\ast$ uses no entry of $\\Delta$.');
T('r-var', 'E-Var', 'static/Typing.v: e_var, d_var',
  rule('E-Var', UNL, J(R`\Gamma`, h('ctx.only', R`\Delta, x : T`), '', 'F', 'x', 'T', ZERO)),
  '$x$ is the only entry of the context that is not unlimited.');
T('r-chan', 'E-Chan', 'static/Typing.v: e_chan, d_chan',
  rule('E-Chan', UNL, J(R`\Gamma`, h('ctx.only', R`\Delta, o : (S@x)\annot{^{a}}`), '', 'F', 'o', R`(S@x)\annot{^{a}}`, ZERO)),
  'The end $o$ is typed by its own entry.');
T('r-abs', 'E-Abs', 'static/Typing.v: e_abs, d_abs',
  rule('E-Abs',
    R`${h('E-Abs.phi', R`\varphi\ \text{fresh}`)}${QH}${h('E-Abs.lb', R`l \preccurlyeq \Delta`)}\annraw{${QH}}\annot{${h('E-Abs.cap', R`\Delta \leadsto_{h,a} \Delta^{h}`)}} \\ ${h('E-Abs.body', J(R`\Gamma, u \prec \varphi`, R`\Delta\annot{^{h}}, T`, '', R`(\varnothing, \varphi)`, 'e', 'U', R`\varepsilon`))}`,
    J(R`\Gamma`, R`\Delta`, '', 'F', R`\lambda e`, ARR('T', 'U', R`\varepsilon`, 'h', 'a'), ZERO)),
  'The body runs at a later call under a fresh future $\\varphi$ above $u$, and $l$ lies at or below the partner points of the captured entries. In the lock-free mode the closure records the effect of its body and restates its captured ends at the floor $h$.');
T('r-app', 'E-App', 'static/Typing.v: e_app, d_app',
  rule('E-App',
    R`${h('E-App.fut1', J(R`\Gamma`, R`\Delta_1`, R`\Delta_2`, 'F', R`e_1`, ARR('T', 'U', R`\varepsilon`, 'h', 'a'), R`\varepsilon_1`))} \\ ${h('E-App.fut2', J(R`\Gamma`, AGE(R`\Delta_2`, R`\varepsilon_1`), R`(T \multimap^{u}_{l} U)\annot{^{a}}`, 'F', R`e_2`, 'T', R`\varepsilon_2`))}${QH}${h('E-App.ub', R`u \prec F`)}`,
    J(R`\Gamma`, R`\Delta_1, \Delta_2`, '', 'F', R`e_1\,e_2`, 'U', R`\varepsilon_1 ${SEQ} \varepsilon_2 ${SEQ} \varepsilon`)),
  'The thread holds $\\Delta_2$ while $e_1$ runs and the closure while $e_2$ runs, and the body runs under $F$ with $u \\prec F$. In the lock-free mode holding the closure ages it by the cost of $e_2$, which needs that much credit.');
T('r-pair', 'E-Pair', 'static/Typing.v: e_pair, d_pair',
  rule('E-Pair',
    R`${h('E-App.fut1', J(R`\Gamma`, R`\Delta_1`, R`\Delta_2`, 'F', R`e_1`, R`T_1`, R`\varepsilon_1`))}${QH}${h('E-Pair.fut2', J(R`\Gamma`, AGE(R`\Delta_2`, R`\varepsilon_1`), R`T_1`, 'F', R`e_2`, R`T_2`, R`\varepsilon_2`))}`,
    J(R`\Gamma`, R`\Delta_1, \Delta_2`, '', 'F', R`\langle e_1, e_2\rangle`, R`\annot{(}T_1${AGE('', R`\varepsilon_2`)}\annot{)} \otimes T_2`, R`\varepsilon_1 ${SEQ} \varepsilon_2`)),
  'The value of $e_1$ is held while $e_2$ runs. In the lock-free mode it ages by the cost of $e_2$.');
T('r-let', 'E-LetP, E-LetU', 'static/Typing.v: e_letp, e_letu, d_letp, d_letu',
  rows(rule('E-LetP', R`${h('E-App.fut1', J(R`\Gamma`, R`\Delta_1`, R`\Delta_2`, 'F', R`e_1`, R`T_1 \otimes T_2`, R`\varepsilon_1`))}${QH}${h('tp.letp', J(R`\Gamma`, R`T_2, T_1, ${AGE(R`\Delta_2`, R`\varepsilon_1`)}`, '', 'F', R`e_2`, 'T', R`\varepsilon_2`))}`,
    J(R`\Gamma`, R`\Delta_1, \Delta_2`, '', 'F', R`\mathsf{let}\ \langle a, b\rangle = e_1\ \mathsf{in}\ e_2`, 'T', R`\varepsilon_1 ${SEQ} \varepsilon_2`)),
    rule('E-LetU', R`${h('E-App.fut1', J(R`\Gamma`, R`\Delta_1`, R`\Delta_2`, 'F', R`e_1`, R`\ast`, R`\varepsilon_1`))}${QH}${h('tp.letu', J(R`\Gamma`, AGE(R`\Delta_2`, R`\varepsilon_1`), '', 'F', R`e_2`, 'T', R`\varepsilon_2`))}`,
    J(R`\Gamma`, R`\Delta_1, \Delta_2`, '', 'F', R`\mathsf{let}\ \ast = e_1\ \mathsf{in}\ e_2`, 'T', R`\varepsilon_1 ${SEQ} \varepsilon_2`))),
  '$\\mathsf{let}\\ x = e_1\\ \\mathsf{in}\\ e_2$ abbreviates a pair elimination followed by a unit elimination and types by E-LetP, E-Pair and E-LetU.');
T('r-case', 'E-Inj, E-Case', 'static/Typing.v: e_inj, e_case, d_inj, d_case',
  rows(rule('E-Inj', J(R`\Gamma`, R`\Delta`, '', 'F', 'e', R`T_i`, R`\varepsilon`), J(R`\Gamma`, R`\Delta`, '', 'F', h('syn.inj', R`\mathsf{inj}_i\,e`), R`T_1 \oplus T_2`, R`\varepsilon`)),
    rule('E-Case', R`${h('E-App.fut1', J(R`\Gamma`, R`\Delta_1`, R`\Delta_2`, 'F', 'e', R`T_1 \oplus T_2`, R`\varepsilon_0`))}${QH}${h('E-Case.branches', J(R`\Gamma`, R`T_i, ${AGE(R`\Delta_2`, R`\varepsilon_0`)}`, '', 'F', R`e_i`, 'T', R`\varepsilon_i`))}`,
    J(R`\Gamma`, R`\Delta_1, \Delta_2`, '', 'F', R`\mathsf{case}\ e\,(e_1)\,(e_2)`, 'T', R`\varepsilon_0 ${SEQ} ${h('tp.max', R`\max`)}(\varepsilon_1,\varepsilon_2)`))),
  'An injection keeps the context of its argument. Both branches of a case type under one context at one result.');
T('r-box', 'E-Box', 'static/Typing.v: e_box, d_box',
  rule('E-Box', R`${h('E-Box.unl', R`\Delta\ \text{unlimited}`)}${QH}${h('E-Abs.phi', R`\varphi\ \text{fresh}`)}${QH}${h('E-Box.fresh', R`\bar\iota\ \text{fresh}`)}${QH}${h('E-Box.inst', R`\forall \bar s.\ ${h('tp.sinsts', R`\mathsf{sinsts}`)}\,\bar s`)} \\ ${h('E-Box.body', J(h('E-Box.open', R`\Gamma, C(\bar\iota), u \prec \varphi`), h('E-Box.self', R`\Delta, f : \Box(\ldots)`), '', R`(\varnothing,\varphi)`, 'e', h('tp.sinst', R`U[\bar s]`), R`\varepsilon`))}`,
    J(R`\Gamma`, R`\Delta`, '', 'F', R`!e`, R`\Box(\forall \bar\iota\,\bar\alpha.\ C.\ \ast \multimap^{u}\annot{[\varepsilon]}\,U)`, ZERO)),
  'A box $!e$ is a procedure that can be forced many times, and its body calls itself through $f$. A copy of a box must not copy an end, so $\\Delta$ is unlimited. Each force may pick other points for $\\bar\\iota$ and other session types for $\\bar\\alpha$, so the body is typed once with $\\bar\\iota$ fresh and only $C(\\bar\\iota)$ known, and once for every allowed choice $\\bar s$. Its future is a fresh $\\varphi$ above $u$, which stands for whatever a caller does after the force.');
T('r-force', 'E-Force', 'static/Typing.v: e_force, d_force',
  rule('E-Force', R`${h('E-Force.hold', R`\Gamma \vdash C[\bar x]`)}${QH}${h('E-Box.inst', R`\mathsf{sinsts}\,\bar s`)}${QH}${h('E-Force.ub', R`u[\bar x] \prec F`)} \\ ${J(R`\Gamma`, R`\Delta`, '', 'F', 'e', R`\Box(\forall\bar\iota\,\bar\alpha.\ C.\ \ast\multimap^{u}\annot{[\varepsilon]}\,U)`, R`\varepsilon_0`)}`,
    J(R`\Gamma`, R`\Delta`, '', 'F', R`\mathsf{force}\,e`, R`${h('tp.sinst', R`U[\bar s]`)}${h('tp.pinst', R`[\bar x]`)}`, R`\varepsilon_0 ${SEQ} \varepsilon`)),
  '$\\mathsf{force}\\,e$ runs the body of the box once. The caller picks points $\\bar x$ for $\\bar\\iota$ and session types $\\bar s$ for $\\bar\\alpha$. The body was typed assuming $C$, so $C[\\bar x]$ must hold here. The body waits at most at $u[\\bar x]$, and the caller acts at $F$ afterwards, so $u[\\bar x] \\prec F$, as in E-App. The result is $U$ with both choices put in.');
block(s, {
  id: 't-consts', title: 'Types of constants', rocq: 'static/Typing.v: e_send, e_recv, e_close, e_select, e_branch, e_link, e_spawn, e_force, e_new',
  tex: R`\begin{array}{lll}
\mathsf{send} & : T[x\cdot i] \otimes S_0@x \multimap^{x} S@${h('pt.shift', R`x^{+}`)} & ${h('E-Send.unfold', R`${h('sty.unfold', R`\mathsf{unfold}`)}(S_0) = {!}(\bar\iota.\,T).S`)},\ \mathsf{pscoped}\,\bar\iota\,T,\ ${h('E-Send.heads', R`x \prec T[x\cdot i]`)} \\
\mathsf{recv} & : S_0@x \multimap^{x} T[x\cdot i] \otimes S@x^{+} & ${h('E-Recv.unfold', R`${h('sty.unfold', R`\mathsf{unfold}`)}(S_0) = {?}(\bar\iota.\,T).S`)},\ \mathsf{pscoped}\,\bar\iota\,T \\
\mathsf{close} & : S_0@x \multimap^{x} \ast & ${h('E-Close.unfold', R`${h('sty.unfold', R`\mathsf{unfold}`)}(S_0) = \mathsf{Close}`)} \\
\mathsf{select}_i & : S_0@x \multimap^{x} S_i@${h('pt.sel', R`\overline{x\cdot\kappa_i}`)} & ${h('E-Select.unfold', R`${h('sty.unfold', R`\mathsf{unfold}`)}(S_0) = \oplus(S_1,S_2)`)} \\
\mathsf{branch} & : S_0@x \multimap^{x} S_1@${h('pt.bra', R`x\cdot\kappa_1`)} \oplus S_2@x\cdot\kappa_2 & ${h('E-Branch.unfold', R`${h('sty.unfold', R`\mathsf{unfold}`)}(S_0) = \&(S_1,S_2)`)} \\
\mathsf{link} & : ${h('E-Link.dual', R`S@x \otimes \overline{S}@\overline{x}`)} \multimap \ast & \\
\mathsf{spawn} & : (\ast \multimap^{u}_{l} \ast) \multimap \ast & \\
\mathsf{force} & : \Box(\forall\bar\iota\,\bar\alpha.\ C.\ \ast\multimap^{u} U) \multimap^{u[\bar x]} U[\bar s][\bar x] & ${h('E-Force.hold', R`\Gamma \vdash C[\bar x]`)} \\
\mathsf{new} & : \exists^{\bot}\bar\iota.\ ${h('E-New.facts', 'C')}.\ (S@\pi \otimes \overline{S}@\overline{\pi}) & ${h('E-New.pos', R`(\bar\iota, \pi) \in \{(\rho, \rho), (\varnothing, x\cdot\kappa)\}`)},\ ${h('E-New.strict', R`\mathsf{strict}(\Gamma \cup C)`)}
\end{array}`,
  caption: 'Each constant has the type of its eta-expansion $\\lambda y.\\,k\\,y$, for every instance of its variables that meets the conditions on the right, shown without credits, cost and ticket need. An action on $x$ has upper point $x$, so it runs only below the future of its caller. $\\mathsf{new}$ is a term and has the type of E-New.'
});
const UNF = (k, form) => h(k, R`${h('sty.unfold', R`\mathsf{unfold}`)}(S_0) = ${form}`);
const XP = h('pt.shift', R`x^{+}`);
T('r-send', 'E-Send', 'static/Typing.v: e_send, d_send',
  rule('E-Send', R`${UNF('E-Send.unfold', R`{!}(\bar\iota.\,T).S`)}${QH}${h('ty.pscoped', R`\mathsf{pscoped}\,\bar\iota\,T`)}${QH}${h('E-Send.heads', R`x \prec ${h('ty.payload-at', R`T[x\cdot i]`)}`)}${QH}${act} \\ ${J(R`\Gamma`, R`\Delta`, '', 'F', 'e', R`T' \otimes (S_0@x)\annot{^{a}}`, R`\varepsilon`)}\annraw{${QH}}\annot{${h('E-Send.floor', R`T' - 1 \leq T[x\cdot i]`)}}`,
    J(R`\Gamma`, R`\Delta`, '', 'F', R`\mathsf{send}\,e`, R`(S@${XP})\annot{^{${REF}}}`, R`\varepsilon ${SEQ} ${ONE}`)),
  'The sender holds the payload while it waits at $x$, so $x$ lies below the partner points of the payload. In the lock-free mode the payload survives one hop and the end returns refilled at $N$.');
T('r-recv', 'E-Recv', 'static/Typing.v: e_recv, d_recv',
  rule('E-Recv', R`${UNF('E-Recv.unfold', R`{?}(\bar\iota.\,T).S`)}${QH}${h('ty.pscoped', R`\mathsf{pscoped}\,\bar\iota\,T`)}${QH}${act}${QH}${J(R`\Gamma`, R`\Delta`, '', 'F', 'e', R`(S_0@x)\annot{^{a}}`, R`\varepsilon`)}`,
    J(R`\Gamma`, R`\Delta`, '', 'F', R`\mathsf{recv}\,e`, R`T[x\cdot i] \otimes (S@${XP})\annot{^{${REF}}}`, R`\varepsilon ${SEQ} ${ONE}`)),
  'The payload arrives with its ends at the fields of $x$, and the end continues at $x^{+}$.');
T('r-close', 'E-Close', 'static/Typing.v: e_close, d_close',
  rule('E-Close', R`${UNF('E-Close.unfold', R`\mathsf{Close}`)}${QH}${act}${QH}${J(R`\Gamma`, R`\Delta`, '', 'F', 'e', R`(S_0@x)\annot{^{a}}`, R`\varepsilon`)}`,
    J(R`\Gamma`, R`\Delta`, '', 'F', R`\mathsf{close}\,e`, R`\ast`, R`\varepsilon ${SEQ} ${ONE}`)),
  'A close is an action at $x$.');
T('r-select', 'E-Select', 'static/Typing.v: e_select, d_select',
  rule('E-Select', R`${UNF('E-Select.unfold', R`\oplus(S_1,S_2)`)}${QH}${act}${QH}${J(R`\Gamma`, R`\Delta`, '', 'F', 'e', R`(S_0@x)\annot{^{a}}`, R`\varepsilon`)}`,
    J(R`\Gamma`, R`\Delta`, '', 'F', R`\mathsf{select}_i\,e`, R`(S_i@${h('pt.sel', R`\overline{x\cdot\kappa_i}`)})\annot{^{${REF}}}`, R`\varepsilon ${SEQ} ${ONE}`)),
  'The selecting end continues at $\\overline{x\\cdot\\kappa_i}$.');
T('r-branch', 'E-Branch', 'static/Typing.v: e_branch, d_branch',
  rule('E-Branch', R`${UNF('E-Branch.unfold', R`\&(S_1,S_2)`)}${QH}${act}${QH}${J(R`\Gamma`, R`\Delta`, '', 'F', 'e', R`(S_0@x)\annot{^{a}}`, R`\varepsilon`)}`,
    J(R`\Gamma`, R`\Delta`, '', 'F', R`\mathsf{branch}\,e`, R`(S_1@${h('pt.bra', R`x\cdot\kappa_1`)})\annot{^{${REF}}} \oplus (S_2@x\cdot\kappa_2)\annot{^{${REF}}}`, R`\varepsilon ${SEQ} ${ONE}`)),
  'The branching end continues at $x\\cdot\\kappa_i$.');
T('r-link', 'E-Link', 'static/Typing.v: e_link, d_link',
  rule('E-Link', h('E-Link.dual', J(R`\Gamma`, R`\Delta`, '', 'F', 'e', R`(S@x)\annot{^{a_1}} \otimes (\overline{S}@\overline{x})\annot{^{a_2}}`, R`\varepsilon`)),
    J(R`\Gamma`, R`\Delta`, '', 'F', R`\mathsf{link}\,e`, R`\ast`, R`\varepsilon ${SEQ} (0, ${h('ann.tlink', R`\mathsf{tlink}\,\hat 1`)})`)),
  'A link asks no order fact. In the lock-free mode it spends one ticket.');
T('r-spawnlam', 'E-SpawnLam', 'static/Typing.v: e_spawn_lam, d_spawn_lam',
  rule('E-SpawnLam', h('E-SpawnLam.body', J(R`\Gamma`, R`${h('E-SpawnLam.age', AGE(R`\Delta`, '1'))}, \ast`, '', h('E-SpawnLam.future', R`(\varnothing, \cdot)`), 'e', R`\ast`, R`(c', \vartheta')`)),
    J(R`\Gamma`, R`\Delta`, '', 'F', R`\mathsf{spawn}\,(\lambda e)`, R`\ast`, R`(0, ${h('ann.tspawn', R`\mathsf{tspawn}(\vartheta'(0))\,\hat 1`)})`)),
  'The child body runs under the empty future. In the lock-free mode every handed entry ages by one hop.');
T('r-spawn', 'E-Spawn', 'static/Typing.v: e_spawn, d_spawn',
  rule('E-Spawn', R`${J(R`\Gamma`, R`\Delta`, '', 'F', 'e', ARR(R`\ast`, R`\ast`, R`(c', \vartheta')`, 'h', 'a'), R`\varepsilon`)}\annraw{${QH}}\annot{${h('E-Spawn.credit', R`a \geq 1`)}}`,
    J(R`\Gamma`, R`\Delta`, '', 'F', R`\mathsf{spawn}\,e`, R`\ast`, R`\varepsilon ${SEQ} (0, ${h('ann.tspawn', R`\mathsf{tspawn}(\vartheta'(0))\,\hat 1`)})`)),
  'Spawning a closure value hands over its captured ends to a new thread.');
T('r-new', 'E-New', 'static/Typing.v: e_new, d_new',
  rule('E-New', R`${UNL}${QH}${h('E-New.pos', R`(\bar\iota, \pi) \in \{(\rho, \rho), (\varnothing, x\cdot\kappa)\}`)}${QH}${h('E-New.strict', R`${h('w.strict', R`\mathsf{strict}`)}(\Gamma \cup C)`)}`,
    J(R`\Gamma`, R`\Delta`, '', 'F', R`\mathsf{new}`, R`\exists^{${h('E-New.bot', R`\bot`)}}\bar\iota.\ ${h('E-New.facts', 'C')}.\ ${h('E-New.dual', R`(S@\pi)\annot{^{${REF}}} \otimes (${h('sty.dual', R`\overline{S}`)}@\overline{\pi})\annot{^{${REF}}}`)}`, ZERO)),
  'The pair sits at a fresh root $\\rho$ or at a field $x\\cdot\\kappa$, with facts $C$ that keep the order strict and lower bound $\\bot$.');
T('r-struct', 'E-Sub', 'static/Typing.v: e_sub, d_conv',
  rule('E-Sub', R`e : T\annot{\ !\ \varepsilon}${QH}${h('sub.tsub', R`T \leq T'`)}\annraw{${QH}}\annot{${h('E-Sub.cost', R`\varepsilon \leq \varepsilon'`)}}`, R`e : T'\annot{\ !\ \varepsilon'}`),
  'A type may lose facts of an existential. In the lock-free mode credits may fall and costs and ticket needs may rise.');
T('r-admis', 'E-Weak, E-Contract (admissible)', 'static/Weakening.v: e_weak, e_contract, d_weak, d_contract, typed_rename',
  rows(rule('E-Weak', h('E-Weak.drop', R`\Delta' \preceq_{\mathsf{wk}} \Delta`), R`\Delta' \vdash e \Rightarrow \Delta \vdash e`), rule('E-Contract', h('ty.unlimited', R`\mathsf{unlimited}\,U`), R`U, U, \Delta \vdash e \Rightarrow U, \Delta \vdash e[x/x']`)),
  'Both are renamings of the variables, the identity and the map $x \\mapsto x - 1$. They hold because E-Unit, E-Var, E-Chan and E-New accept unused entries of unlimited type.');
T('r-ex', 'E-Pack, E-Open', 'static/Typing.v: e_pack, e_open, d_pack, d_open',
  rows(rule('E-Pack', R`${h('E-Force.hold', R`\Gamma \vdash C[\bar x]`)}${QH}${h('E-Pack.lb', R`l \preccurlyeq ${h('tp.pinst', R`T[\bar x]`)}`)}${QH}e : T[\bar x]`, R`e : \exists^{l}\bar\iota.\,C.\,T`),
    rule('E-Open', R`${h('E-Open.entry', R`\Delta(i) = \exists^{l}\bar\iota.\,C.\,T\annot{,\ \neg\mathsf{unlimited}\,T}`)}${QH}${h('E-Box.fresh', R`\bar\iota\ \text{fresh}`)}${QH}${h('E-Open.body', J(R`\Gamma, C(\bar\iota)`, R`\Delta[i \mapsto T]`, '', 'F', 'e', 'U', R`\varepsilon`))}`, J(R`\Gamma`, R`\Delta`, '', 'F', 'e', 'U', R`\varepsilon`))),
  'Packing chooses $\\bar x$ with $\\Gamma \\vdash C[\\bar x]$, and opening names the witness by fresh point variables $\\bar\\iota$ with hypothesis $C(\\bar\\iota)$.');

// ---- process rules ----
const MEETSP = R`${h('lf.meets', R`N \in \mathbb{N} \Rightarrow ${h('ann.fin0', R`\vartheta(0) \in \mathbb{N}`)}`)}`;
const PTERM = (m) => rule('P-Term', R`\begin{array}{c}${h('ty.prim', R`\mathsf{prim}\,T`)}${Q}${h('P-Term.C0', R`\mathrm{dom}\,\Theta_B = ${h('tp.ends', R`\mathsf{ends}`)}(C_0)`)}${Q}${h('P-Term.disj', R`${h('tp.chans', R`\mathsf{chans}`)}\,${h('tp.Sigma', R`\Sigma`)} \cap C_0 = \varnothing`)}${Q}${h('pfree', R`\mathsf{pfree}\,\Sigma`)}${Q}${h('P-Term.strict', R`${h('w.strict', R`\mathsf{strict}`)}\,W`)} \\ ${h('P-Term.pairs', R`\forall c \in C_0.\ \Theta_B(c^{+}) = S@x^{N},\ \Theta_B(c^{-}) = \overline{S}@\overline{x}^{N}`)} \\ ${h('P-Term.typed', R`\varnothing ; ${h('tp.lift', R`\Sigma\annot{^{N}}`)}, \Theta_B \vdash^{${h('P-Term.future', R`(\varnothing,\cdot)`)}} t : T\annot{\ !\ (c, \vartheta)}`)}\annraw{ \\ }\annot{${m(MEETSP)}}\end{array}`, R`\Sigma ${h('tp.pjudg', R`\vdash^{N}_W`)} (C_0, \{t\}) : T`);
const PCONN = R`\begin{array}{c}${h('P-Connect.left', R`\Sigma_1 \cup \Sigma_C \vdash^{N}_{W_1} (C_1, E_1) : T`)} \\ ${h('P-Connect.right', R`\Sigma_2 \cup ${h('P-Connect.cut', R`\overline{\Sigma_C}`)} \vdash^{N}_{W_2} (C_2, E_2) : \ast`)} \\ ${h('P-Connect.disj', R`\mathsf{chans}\,\Sigma_1,\ \mathsf{chans}\,\Sigma_2,\ \mathsf{chans}\,\Sigma_C,\ C_1,\ C_2\ \text{pairwise disjoint}`)} \\ ${h('P-Connect.cutfree', R`\mathsf{pfree}\,\Sigma_C`)} \\ ${h('P-Connect.strict', R`${h('w.strict', R`\mathsf{strict}`)}(${h('w.restrict', R`W_1|_S`)} \sqcup W_2|_S)\ \ \text{for}\ \ S = ${h('w.consts', R`A_{W_1}`)} \cap A_{W_2}`)}\end{array}`;
const PCONC = R`\begin{array}{c}\Sigma_1 \cup \Sigma_2 \vdash^{N}_{${h('P-Connect.join', R`W_1 ${h('w.join', R`\sqcup`)} W_2`)}} \\ (C_1 \cup C_2 \cup ${h('tp.chans', R`\mathsf{chans}`)}\,\Sigma_C, E_1 \uplus E_2) : T\end{array}`;
block(s, {
  id: 'p-term', title: 'P-Term', rocq: 'static/Typing.v: p_term',
  tex: PTERM((x) => x),
  variants: { lf: PTERM((x) => R`\boxed{${x}}`) },
  caption: 'One thread $t$ holding both ends of every $c \\in C_0$ at dual types and points over a partner-free $\\Sigma$.'
});
block(s, {
  id: 'p-connect', title: 'P-Connect', rocq: 'static/Typing.v: p_connect',
  tex: rule('P-Connect', PCONN, PCONC),
  caption: 'Two components at refill $N$ in worlds $W_1$, $W_2$, cut at $\\Sigma_C$ against $\\overline{\\Sigma_C}$, the left one carrying $T$.'
});
block(s, {
  id: 'p-lf', title: 'Lock-free process typing', rocq: 'static/Typing.v: ptyped, static/FundamentalProc.v: pguard', modes: ['lf'],
  tex: h('tp.lfjudg', R`\Sigma \Vdash^{N}_W p : T \iff ${h('lf.N', R`N \in \mathbb{N}`)} \land \Sigma \vdash^{N}_W p : T \land ${h('guard.proc', R`\vdash\!\triangleright p`)}`),
  caption: 'Lock-free typing is process typing at finite $N$ with every thread guarded.'
});
block(s, {
  id: 'g-acts', title: 'Terms that act', rocq: 'static/Guard.v: sprim, acts',
  modes: ['live', 'lf'],
  tex: h('guard.acts', R`\begin{array}{l}\mathsf{acts}\,(k\,e) \iff k \in K_{\mathrm{act}} \lor \mathsf{acts}\,e \\ K_{\mathrm{act}} = \{\mathsf{send}, \mathsf{recv}, \mathsf{close}, \mathsf{select}_i, \mathsf{branch}\} \\ \mathsf{acts}\,(e_1\,e_2),\ \mathsf{acts}\,\langle e_1, e_2\rangle \iff \mathsf{acts}\,e_1 \lor \mathsf{acts}\,e_2 \\ \mathsf{acts}\,(\mathsf{let}\ p = e_1\ \mathsf{in}\ e_2) \iff \mathsf{acts}\,e_1 \lor \mathsf{acts}\,e_2 \\ \mathsf{acts}\,(\mathsf{case}\ e\,(e_1)\,(e_2)) \iff \mathsf{acts}\,e \lor (\mathsf{acts}\,e_1 \land \mathsf{acts}\,e_2) \\ \mathsf{acts}\,(\mathsf{inj}_i\,e) \iff \mathsf{acts}\,e, \quad \text{false for values and } \mathsf{new}_\ell\end{array}`),
  caption: '$\\mathsf{acts}\\,e$ holds when every evaluation of $e$ to a value performs a session action.'
});
block(s, {
  id: 'g-rules', title: 'The guard $\\Lambda \\vdash\\!\\triangleright t$', rocq: 'static/Guard.v: lguard',
  modes: ['live', 'lf'],
  tex: R`\begin{array}{c}
${rule('gl_var', h('guard.var', R`\Lambda(y) = \mathsf{false}`), R`${h('guard.marks', R`\Lambda`)} \vdash\!\triangleright y`)} \quad ${rule('gl_lam', h('guard.lam', R`\mathsf{false}.\Lambda \vdash\!\triangleright b`), R`\Lambda \vdash\!\triangleright \lambda b`)} \quad ${rule('gl_box', h('guard.box', R`\mathsf{true}.\Lambda \vdash\!\triangleright b`), R`\Lambda \vdash\!\triangleright\ !b`)} \\[2ex]
${rule('gl_app', R`${h('guard.cong', R`\Lambda \vdash\!\triangleright e_1`)}${Q}${h('guard.tick', R`\mathsf{kmarks}\,\Lambda\,\Lambda'\,e_1`)}${Q}\Lambda' \vdash\!\triangleright e_2`, R`\Lambda \vdash\!\triangleright e_1\,e_2`)} \\[2ex]
${rule('gl_letp', R`\Lambda \vdash\!\triangleright e_1${Q}${h('guard.tick', R`\mathsf{kmarks}\,\Lambda\,\Lambda'\,e_1`)}${Q}${h('guard.bind', R`\mathsf{false}.\mathsf{false}.\Lambda' \vdash\!\triangleright e_2`)}`, R`\Lambda \vdash\!\triangleright \mathsf{let}\ \langle a, b\rangle = e_1\ \mathsf{in}\ e_2`)}
\end{array}`,
  caption: 'A box marks its self, a marked variable is unusable, and after an acting $e_1$ the rest may be checked under $\\varnothing$. The pair, $\\mathsf{let}\\ \\ast$ and the case follow $\\mathsf{gl\\_app}$ and $\\mathsf{gl\\_letp}$.'
});
block(s, {
  id: 'g-proc', title: 'Guard of a process', rocq: 'static/FundamentalProc.v: pguard',
  modes: ['live', 'lf'],
  tex: h('guard.proc', R`\vdash\!\triangleright p \iff \forall t \in p.\ \varnothing \vdash\!\triangleright t`),
  caption: '$\\vdash\\!\\triangleright p$ holds when every thread $t$ of $p$ satisfies $\\varnothing \\vdash\\!\\triangleright t$.'
});

// what each definitional block is for, shown when its title is hovered or clicked
const ABOUT = {
  't-lf-intro': { why: 'Each row names one mechanism the lock-free mode adds and the endless postponement it rules out. Hover a row for its intuition.', used: ['t-judgment', 't-age', 't-cap', 'r-send', 'r-link', 'p-lf'] },
  't-judgment': { why: 'Every typing rule concludes and assumes this judgment. The held entries $\\parallel H$ state once what every rule that runs one part while holding another needs, the future of the running part and, in the lock-free mode, the aging of the held part.', example: 'E-App runs $e_1$ while holding $\\Delta_2$, written $\\Gamma ; \\Delta_1 \\parallel \\Delta_2 \\vdash^{F} e_1 : \\ldots$', used: ['r-app', 'r-pair', 'r-let', 'r-case'] },
  't-contexts': { why: 'Rules split $\\Delta$ between subterms, extend $\\Gamma$ under boxes and existentials, and read order facts only through $\\Gamma \\vdash x \\prec y$. This block fixes what those three objects are.', used: ['t-side', 'r-app', 'r-box', 'r-ex'] },
  't-side': { why: 'These are the only order checks typing makes. $u \\prec F$ and $x \\prec F$ say a term never waits above a point its context still acts at, $x \\prec T$ says a thread may wait while holding $T$, and $l \\preccurlyeq \\Delta$ fixes the lower point of a closure.', breaks: 'Without them the type system is plain GV and the cycle of two threads closing two channels in opposite orders types.', used: ['r-app', 'r-send', 'r-recv', 'r-close', 'r-abs', 'r-force', 'r-ex'] },
  't-age': { why: 'Aging is how credits fall. Every rule that holds entries while a subterm runs ages them by the cost of that subterm, and $c \\leq a$ makes the credit cover the actions performed in between.', breaks: 'Without aging a thread may hold an end across unboundedly many actions on other ends, and the partner of that end waits without bound, as in Postponement in the Examples tab.', example: '$((S@x)^{2} \\otimes \\ast) - 1 = (S@x)^{1} \\otimes \\ast$.', used: ['t-judgment', 'r-app', 'r-pair', 'r-let', 'r-case', 'r-spawnlam'] },
  't-cap': { why: 'Capture fixes what a closure body may assume of the ends it captured. The ends are invisible in the closure type, so the body sees them at the floor $h$, and creation asks each to have $h + a$, the floor plus what the closure may lose while it is held.', breaks: 'Without it a closure could be held across many actions and then use a captured end whose counter has run out.', example: 'An end at credit $2$ captured with $h = 1$ and $a = 1$ is seen at credit $1$ by the body.', used: ['r-abs'] },
  't-sub': { why: 'Subtyping lets one value fit several expected types. The branches of a case and two creations of one channel type need a common type, and in the lock-free mode a fresh end at credit $N$ must fit a parameter that asks less.', breaks: 'Without it two branches that create a channel with different facts have no common result type.', example: '$\\exists^{\\bot}\\rho.\\,\\{\\rho \\prec \\overline{\\rho\\cdot 0}\\}.\\,T \\leq \\exists^{\\bot}\\rho.\\,\\varnothing.\\,T$.', used: ['r-struct'] },
  't-consts': { why: 'The constants are values, so they have types. Each type is the type of the constant applied to a variable, and an action on $x$ has upper point $x$, so a caller can only use it while every later action of the caller lies above $x$.', used: ['r-send', 'r-recv', 'r-close', 'r-select', 'r-branch', 'r-link', 'r-spawn', 'r-force', 'r-new'] },
  'p-term': { why: 'P-Term turns one well-typed thread into a process. It splits the ends the thread holds into the interface $\\Sigma$ and the channels $C_0$ whose both ends it holds, and asks the world to be strict.', used: ['p-connect', 'p-lf'] },
  'p-connect': { why: 'P-Connect composes two processes along the cut $\\Sigma_C$. Each side was checked in its own world, so only the order the two worlds induce on their shared roots must stay acyclic.', breaks: 'Without the strictness check two sides could order shared points in opposite directions, and each thread could wait on the other although each side alone is ready.', used: ['p-lf'] },
  'p-lf': { why: 'Lock-free process typing is process typing at a finite refill with every thread guarded. This is the premise of the lock-free soundness theorem.', used: ['g-proc'] },
  'g-acts': { why: 'The guard needs to know when a session action has certainly happened, because only after an action may a box call itself. $\\mathsf{acts}\\,e$ says that evaluating $e$ to a value performs an action.', used: ['g-rules'] },
  'g-rules': { why: 'Internal steps, $\\beta$, $\\mathsf{new}$ and $\\mathsf{spawn}$, cost no counter. A box that calls itself before any action could step forever without serving anyone, which deadlock freedom allows and lock freedom does not. The guard marks the self of a box unusable until an action has happened.', breaks: 'Without the guard $!(f = \\mathsf{force}\\,f)$ types in the lock-free mode and diverges by internal steps, see Guard rejections in the Examples tab.', example: '$!(f = \\lambda x.\\,\\mathsf{let}\\ \\langle v, x\\rangle = \\mathsf{recv}\\,x\\ \\mathsf{in}\\ (\\mathsf{force}\\,f)\\,x)$ is guarded, because the receive acts before the self call.', used: ['g-proc', 'p-lf'] },
  'g-proc': { why: 'A process is guarded when each of its threads is. Lock-free process typing asks it.', used: ['p-lf'] }
};
for (const b of s.blocks) if (ABOUT[b.id]) b.about = ABOUT[b.id];

// ---- notes ----
n("tj.Gamma", "$\\Gamma$, facts and future hypotheses", "$\\Gamma$ consists of a list of constraint instances $(C, \\bar x)$ and a finite map of future variables $\\varphi \\mapsto u$, read as $u \\prec \\varphi$.", "Every order fact a rule may use beyond $\\prec_W$ is recorded in $\\Gamma$. The derivable facts are exactly the judgments $\\Gamma \\vdash x \\prec y$.", DEF, "In the body of the client loop $\\Gamma$ holds $(C, [\\iota, \\kappa, \\zeta])$.", "static/Contexts.v: hctx");
n("tj.hage", "$H - c$, aging what is held", "$H - c$ ages every entry of $H$ by the cost $c$ of $e$. It is defined when every end and closure in $H$ that is not idle has credit at least $c$.", "The thread holds $H$ while $e$ runs, and each of the up to $c$ actions of $e$ lowers the counters of the held ends by $1$.", "Without it a thread holds an end across unboundedly many actions on other ends, and the partner of that end waits without bound.", "$(S@x)^{2} - 1 = (S@x)^{1}$ is defined, $(S@x)^{0} - 1$ is not.", "static/Contexts.v: thage, lage");
n("lfi.credit", "Credits, a bound on postponement", "Every end has a counter at run time, the number of actions its holder may still perform on other ends before it must act on this one. The credit $a$ in $(S@x)^{a}$ is a lower bound on that counter, known statically. A closure has a credit too, because the ends it captured are invisible in its type.", "A partner waiting on an end needs the holder to act on it eventually. If every action elsewhere lowers the counter and the counter must stay non-negative, the holder can only postpone the end finitely often.", "Postponement in the Examples tab holds $b$ across a loop that never returns, so $\\mathsf{close}\\,b'$ waits forever. The loop has cost $\\infty$, and no credit is large enough.", "$(S@x)^{3}$ may be held across three actions on other ends.", "types/Types.v: TSess, TLolli; fuel/Fuel.v: f_act");
n("lfi.cost", "Cost, aging and refill, the counting", "The cost $c$ of a term bounds its actions before it returns. Every rule that runs a subterm while holding $\\Delta$ ages $\\Delta$ by that cost, $\\Delta - c$, which asks each credit to be at least the cost. An action on an end refills it to $N$, so the end returns as $(S@x^{+})^{N}$. Idle ends, $\\mathsf{Skip}$, age without the check, because no thread waits on an idle end.", "Credits bound postponement only if the holder's actions lower the credits. The cost says how much, aging applies it to everything held, and the refill starts the count again after the holder kept its promise.", "Without the refill a long-running protocol would run out of credit after $N$ actions.", "$\\langle c, \\mathsf{send}\\,\\langle\\ast, d\\rangle\\rangle$ ages $c$ by $1$ while the send on $d$ runs.", "static/Typing.v: typed; static/Contexts.v: tage, lage");
n("lfi.floor", "Floors, credit inside a closure", "A closure $T \\multimap[\\varepsilon ; h]\\, U$ records the floor $h$, the credit its body may assume of every captured end when it is called. At creation each captured end needs $h + a$, the floor plus what the closure itself may lose while it is held.", "Between creating a closure and calling it, its holder may act elsewhere, which lowers the counters of the captured ends. The credit $a$ of the closure absorbs that loss, and $h$ is what remains for the body.", "Without the floor the body could not hold a captured end across any action.", "A callback with $h = 1$ and $a = 1$ needs its captured ends at credit $2$.", "static/Contexts.v: tcap, thcap");
n("lfi.hop", "Hops, a passed end loses one", "Every time an end is handed to another thread, by a send or a spawn, its counter drops by $1$. A send asks $T' - 1 \\leq T[x\\cdot i]$ of the payload, a spawned body sees $\\Delta - 1$, and spawning a closure asks its credit $a \\geq 1$.", "Handing an end on is not an action on it, so it does not refill. Without the loss an end could be sent between threads forever and its partner would never be served.", "Endless delegation in the Examples tab sends $e$ back and forth forever while $e'$ waits. After finitely many hops no credit is left to send it again.", "An end at credit $3$ can be passed on three times before a thread must act on the end.", "static/Typing.v: e_send, e_spawn_lam, e_spawn");
n("lfi.tickets", "Tickets, a bound on links", "Each thread holds a number of link tickets. A link uses one, and a spawn splits the tickets between parent and child. The ticket need $\\vartheta$ of a term says how many tickets it needs, $\\mathsf{tlink}$ adds one for a link and $\\mathsf{tspawn}$ accounts for the split. P-Term asks the thread to start with enough.", "A link acts on no end, so counters cannot bound the number of links. Worse, it gives the waiter a fresh partner end at full counter, so a thread could link forever while every counter stays full.", "Link refresh in the Examples tab relinks the partner of a waiting end to a fresh channel every round, so the waiter always faces a new end. Each round uses a ticket and none is ever created.", "A thread that links twice needs $\\vartheta(0) \\geq 2$.", "types/Costs.v: tlink, tspawn; static/Typing.v: e_link, p_term");
n("lfi.guard", "The guard, no recursion before an action", "$\\Lambda \\vdash\\!\\triangleright t$ asks that a box calls itself only after a session action. It is a syntactic check on terms.", "Internal steps, $\\beta$, $\\mathsf{new}$ and $\\mathsf{spawn}$, cost no counter. A loop made only of them would step forever without ever serving anyone, which deadlock freedom allows and lock freedom does not.", "Guard rejections in the Examples tab, e.g. $!(f = \\mathsf{force}\\,f)$ and a box that spawns itself forever.", "$!(f = \\lambda x.\\, \\mathsf{let}\\ \\langle v, x\\rangle = \\mathsf{recv}\\,x\\ \\mathsf{in}\\ (\\mathsf{force}\\,f)\\,x)$ is guarded.", "static/Guard.v: lguard");
n("lfi.wf", "A well-founded world", "$\\mathsf{wfworld}\\,W$ asks $\\prec_W$ to have no infinite descending chain. It is a premise of the lock-free theorems and no typing rule checks well-foundedness.", "A waiting thread waits on a holder whose own waiting point lies lower. With a well-founded order this chain ends, so someone at the bottom can act.", "A waiting chain that grows forever, in the Examples tab, spawns threads that each wait below their predecessor, and new ones keep appearing.", "Every world of the lock-free examples is well-founded.", "types/Worlds.v: wfworld; soup/LFAdequacy.v: lf_adequacy");
n("tj.held", "Held entries $\\parallel H$", "$\\Delta \\parallel H \\vdash^{F} e$ types $e$ while the thread holds $H$. It unfolds to $\\Delta \\vdash^{F \\cup \\mathsf{heads}(H)} e$, \\annp{and in the lock-free mode also asks that $H - c$ is defined for the cost $c$ of $e$.}", "Every rule that runs one part while it holds another states the same facts about the held part, and the notation states them once. $H$ is a context, as in E-App, or a type, as in E-Pair.", "Without the future part a thread waits above an end it holds, and the partner of that end waits on the thread.", "$\\Delta_1 \\parallel \\Delta_2 \\vdash^{F} e_1$ in E-App.", "static/Typing.v: e_app, e_pair, e_letp, e_letu, e_case");
n("tj.eff", "Effect $\\varepsilon$", "$\\varepsilon = (c, \\vartheta)$ pairs the cost $c$ of a term, an upper bound on its channel actions before it returns, with its ticket need $\\vartheta$.", "Cost and ticket need appear together and combine at the same places, so one symbol has both. Aging reads the cost, and the tickets of links read $\\vartheta$.", DEF, "A send has effect $\\varepsilon \\cdot 1$, one more action than its argument.", "static/Typing.v: typed");
n("tj.seq", "Sequencing $\\varepsilon_1 \\cdot \\varepsilon_2$", "$\\varepsilon_1 \\cdot \\varepsilon_2 = (c_1 + c_2, \\vartheta_1 \\circ \\vartheta_2)$, defined when $\\mathsf{tok}\\,\\vartheta_1\\,\\vartheta_2$.", "A term that runs two parts in sequence adds their costs and composes their ticket needs. The side condition $\\mathsf{tok}$ becomes definedness, so no rule lists $\\mathsf{tok}$.", DEF, "$1 \\cdot 1 = (2, \\hat 1)$.", "types/Costs.v: tseq, tok");
n("tj.zero", "No effect $0$", "$0 = (0, \\hat 1)$, the effect of a value.", "A value performs no action and no link.", DEF, "$\\lambda e$ has effect $0$.", "types/Costs.v: tid");
n("tj.one", "One action $1$", "$1 = (1, \\hat 1)$, the effect of one channel action.", "Every action adds one to the cost and needs no ticket.", DEF, "$\\mathsf{close}\\,e$ has effect $\\varepsilon \\cdot 1$.", "static/Typing.v: e_send, e_recv, e_close, e_select, e_branch");
n("tj.Delta", "$\\Delta$, the linear context", "$\\Delta$ maps ends $o$ to end types $(S@x)^{a}$ and de Bruijn indices $i$ to types $T$, with empty entries for indices another part owns.", "Ends and variables split the same way between two subterms, so one context holds both. A split puts an empty entry at index $i$ in the half that does not own variable $i$, so no index shifts.", DEF, "$\\Delta = a : (S_a@\\rho)^{N},\\ 0 : S_1@\\iota \\otimes S_2@\\kappa$.", "static/Contexts.v: tenv, lenv");
n("tj.F", "The future $F$", "$F = (X, \\varphi)$, $(X, \\bot)$ or $(X, \\cdot)$ with $X$ the points the context acts at after the term, $\\varphi$ an unknown rest above a known point and $\\bot$ a rest at hidden points.", "Every action at $x$ asks $x \\prec F$. Hence a term never waits at a point above a point at which its own context still acts.", "Without $F$ the thread $\\mathsf{let}\\ \\ast = \\mathsf{close}\\,c\\ \\mathsf{in}\\ \\mathsf{close}\\,d$ types for every placement of $c$ and $d$, and beside a partner that closes $d$ before $c$ both threads wait forever.", "$e_1$ of E-App runs under $F \\cup \\mathsf{heads}(\\Delta_2)$.", "static/Contexts.v: sfuture");
n("tj.W", "The world $W$", "The world whose order $\\prec_W$ the rules read.", "Every point fact a rule uses comes from $\\prec_W$ or from $\\Gamma$. Typing is monotone in $W$, so a program typed in $W$ is typed in every $W' \\sqsupseteq W$.", DEF, "E-New asks $\\mathsf{strict}(\\Gamma \\cup C)$ over $\\prec_W$.", "static/Typing.v: typed W");
n("tj.N", "The refill $N$", "$N \\in \\mathbb{N} \\cup \\{\\infty\\}$ is the credit of a fresh end and of an end after an action on that end.", "A credit is a lower bound on a counter, and each action of a holder on another end lowers the counter by $1$. A finite $N$ bounds the number of such actions between two actions on one end, which lock freedom needs, and $N = \\infty$ gives deadlock-free typing.", DEF, "The client and server loop types at $N = 3$.", "static/Typing.v: typed N");
n("ctx.tsplit", "$\\Theta = \\Theta_1 \\uplus \\Theta_2$", "$\\mathrm{dom}\\,\\Theta_1 \\cap \\mathrm{dom}\\,\\Theta_2 = \\varnothing$ and $\\Theta = \\Theta_1 \\cup \\Theta_2$.", "Each end has exactly one owner. Two subterms therefore never act on the same end.", DEF, "In E-App $\\Theta_1$ holds the ends of $e_1$ and $\\Theta_2$ those of $e_2$.", "static/Contexts.v: tsplit");
n("ctx.lsplit", "$\\Delta = \\Delta_1, \\Delta_2$", "Every end of $\\Delta$ goes to exactly one of $\\Delta_1$ and $\\Delta_2$. For every index $i$, a linear entry goes to one side and the other side has an empty entry, and an entry of unlimited type goes to both.", "An end and a linear entry are used exactly once. An entry of unlimited type holds no end, so using it twice duplicates no end.", DEF, "A box variable $f$ may be forced in both $e_1$ and $e_2$.", "static/Contexts.v: tsplit, lenv_split");
n("ctx.hyps", "Constraint instances $(C, \\bar x)$", "A constraint $C$ with the points $\\bar x$ it is instantiated at, added by E-Box and E-Open.", "A box body and the scope of an opened existential refer to their points only through these instances. The facts $C[\\bar x]$ are the only hypotheses about these points.", DEF, "$(C, [\\iota, \\kappa, \\zeta])$ in the body of the client loop.", "static/Contexts.v: hyps, hc_open");
n("ctx.fvar", "Future variables $\\varphi \\mapsto u$", "$\\varphi \\mapsto u \\in \\Gamma$ states $u \\prec \\varphi$ for an unknown future $\\varphi$ above $u$.", "A $\\lambda$ or box body is typed once for all its callers. By E-App every caller future $F$ satisfies $u \\prec F$, and $\\varphi$ stands for every such $F$.", DEF, "A $\\lambda$-body under $(\\varnothing, \\varphi)$ with $u \\prec \\varphi$.", "static/Contexts.v: hc_fvar");
n("ctx.fvarF", "The variable $\\varphi$ in $F$", "The unknown part of a future, read only through $\\Gamma \\vdash u \\prec \\varphi$.", "In the semantics $\\varphi$ denotes an arbitrary set of points above $u$. A body typed under $\\varphi$ is therefore correct for every caller future above $u$.", DEF, "$F = (\\varnothing, \\varphi)$.", "static/Contexts.v: futrest");
n("ctx.bot", "The flag $\\bot$ in $F$", "$\\bot$ states that the context holds ends at points unknown to the term, which then performs no session action.", "Every action asks $u \\prec F$, which requires $F$ to have no $\\bot$. No point is known to lie below a hidden point, so an action under $\\bot$ could wait above the hidden point.", DEF, "$e_1$ beside a context that holds an unopened $\\exists^{\\bot}$.", "static/Contexts.v: FBot, fs_bot");
n("ctx.slt", "$\\Gamma \\vdash x \\prec y$", "The least transitive relation containing $\\prec_W$, the facts $C[\\bar x]$ of the instances $(C, \\bar x)$ in $\\Gamma$, and $u \\prec \\varphi$ for every $\\varphi \\mapsto u$ in $\\Gamma$.", "Every order fact a typing rule reads is a judgment $\\Gamma \\vdash x \\prec y$.", DEF, "$\\Gamma \\vdash x \\prec x^{+}$ for every $\\Gamma$ and $x$.", "static/Contexts.v: fl, slt");
n("ctx.empty", "$\\Delta$ unlimited", "Every non-empty entry of $\\Delta$ has unlimited type.", "A value that mentions no variable uses no linear entry, and an unlimited entry may go unused.", DEF, "$\\ast$ types under every $\\Delta$ whose entries are empty or unlimited.", "static/Contexts.v: lenv_unl");
n("ctx.only", "The only used entry", "In $\\Delta, x : T$ the entry $x$ is used and every entry of $\\Delta$ has unlimited type.", "Every linear entry is used exactly once, and an unlimited entry may go unused.", DEF, "$x = 0$ types under $0 : T$.", "static/Contexts.v: lenv_only, tenv_only");
n("side.act", "$x \\prec F$ at an action", "For an action at $x$ under $F = (X, \\cdot)$, $\\Gamma \\vdash x \\prec y$ for every $y \\in X$, $\\Gamma \\vdash x \\prec \\varphi$ when $F$ has a variable $\\varphi$, and $F$ has no $\\bot$.", "While the term waits at $x$, every point at which its context acts later lies above $x$. This is readiness against the future.", "Without it a term may wait at $x$ while its context must first act at a point below $x$, and the thread waits on itself through the partner end.", "E-Close at $x$ asks $x \\prec F$.", "static/Contexts.v: ub_below_s");
n("act.refill", "Refill $N$ after an action", "An end returned by an action, or created fresh, has credit $N$.", "The fuel layer sets the counter of an end to $N$ at every action on it, and the static credit is a lower bound on that counter.", DEF, "$\\mathsf{send}$ returns $(S@x^{+})^{N}$.", "static/Typing.v: e_send, e_recv, e_select, e_branch, e_new");
n("side.ub", "$u \\prec F$", "$u \\prec F \\iff (\\forall y \\in X.\\ \\Gamma \\vdash u \\prec y) \\land \\Gamma \\vdash u \\prec \\varphi \\land \\bot \\notin F$, true for absent $u$.", "It is the condition $x \\prec F$ of an action, stated for the upper point $u$ up to which a callee may wait.", DEF, "E-App asks $u \\prec F$ of the upper point $u$ of the closure.", "static/Contexts.v: ub_below_s");
n("side.lb", "$l \\preccurlyeq H$", "$l \\preccurlyeq H \\iff \\forall y \\in H.\\ l = y \\lor \\Gamma \\vdash l \\prec y$ for a point $l$, and $H = \\varnothing$ for absent $l$.", "For a holder of a closure, the heads of its ends are bounded only through $l$. Hence $l$ must be a lower bound of those heads.", DEF, "$\\overline{\\rho} \\preccurlyeq \\{\\overline{\\rho}\\}$.", "static/Contexts.v: lbx_below_h, lbound_of");
n("side.hold", "$\\Gamma \\vdash C[\\bar x]$", "For every fact $y \\prec z$ of $C$ instantiated at $\\bar x$, $\\Gamma \\vdash y \\prec z$.", "E-Force and E-Pack choose an instance $\\bar x$, and the box body or the packed value relies on $C[\\bar x]$.", DEF, "The self call of the client loop instantiates $C$ at $(\\iota^{+}, \\kappa^{+}, \\zeta)$.", "static/Contexts.v: hold_at");
n("age.free", "Aging a type without ends", "$T - c = T$ when $\\mathsf{tfree}\\,T$.", "A type without ends has no counter that could fall, so aging changes nothing.", DEF, "A box variable never ages.", "static/Contexts.v: age_free");
n("age.credit", "Aging an end or a closure", "$(S@x)^{a} - c = (S@x)^{a - c}$ and $(T \\multimap U)^{a} - c = (T \\multimap U)^{a - c}$, defined when $c \\leq a$.", "While a term of cost $c$ runs, the holder performs up to $c$ actions on other ends, and each lowers the counter of every held end by $1$. The premise $c \\leq a$ keeps the credit a lower bound on the counter.", "Without $c \\leq a$ a server holds its client end while it runs a callback of cost $\\infty$ at finite $N$, and the client waits without bound.", "$(S@x)^{3} - 1 = (S@x)^{2}$.", "static/Contexts.v: age_credit");
n("age.idle", "Aging an idle end", "$(S@x)^{a} - c = (S@x)^{\\max(a - c, 0)}$ when $\\mathsf{unfold}(S) = \\mathsf{Skip}$.", "No thread acts on an idle end, so no action refills an idle end. Truncation keeps its credit at or below its counter, which ticks and truncates at $0$ in the same way.", "With $c \\leq a$ required an idle end held across a loop loses credit every round and no finite $N$ types the loop. Keeping the credit instead exceeds the counter after one tick.", "$(\\mathsf{Skip}@\\chi)^{0} - 1 = (\\mathsf{Skip}@\\chi)^{0}$.", "static/Contexts.v: age_idle");
n("age.agg", "Aging a product, sum or existential", "Aging goes into the parts. $(T_1 \\otimes T_2) - c = (T_1 - c) \\otimes (T_2 - c)$, likewise for $\\oplus$, and $\\exists^{l}\\bar\\iota.\\,C.\\,T$ ages its body.", "Only ends and closures have credits, so a compound type ages by aging the ends and closures it contains.", DEF, "$((S@x)^{2} \\otimes \\ast) - 1 = (S@x)^{1} \\otimes \\ast$.", "static/Contexts.v: age_prod, age_sum, age_ex");
n("age.ctx", "Aging what is held", "$\\Delta - \\varepsilon$ ages every entry of $\\Delta$ by the cost $c$ of $\\varepsilon = (c, \\vartheta)$.", "The entries are held while the subterm with effect $\\varepsilon$ runs, and each of its actions lowers their counters by $1$.", "Without aging a thread holds an end across unboundedly many actions on other ends, and the partner of that end waits without bound.", "In the cycle example main loses $1$ of the credit of $d$ while it closes $c$.", "static/Contexts.v: thage, lage");
n("cap.sess", "Capturing an end", "$(S@x)^{a_0} \\leadsto_{h,a} (S@x)^{h}$, defined when $h + a \\leq a_0$.", "The closure itself has credit $a$ and ages by up to $a$ before its body runs. The body may assume credit $h$ on the end, so the end needs $h + a$.", DEF, "$h = 1$ and $a = 1$ need $a_0 \\geq 2$.", "static/Contexts.v: cap_sess");
n("cap.arr", "Capturing a closure", "$(T \\multimap[\\varepsilon;h_0] U)^{a_0} \\leadsto_{h,a} (T \\multimap[\\varepsilon;h_0] U)^{h - h_0}$, defined when $h_0 \\leq h$ and $h + a \\leq h_0 + a_0$.", "A captured closure guarantees credit $h_0 + a_0$ on its own ends, and the premise asks this to cover $h + a$. The new credit $h - h_0$ places those ends at exactly the floor $h$ of the outer closure.", DEF, "A callback with $h_0 = 1$ and $a_0 = 2$, captured at $h = 2$ and $a = 1$, gets credit $1$.", "static/Contexts.v: cap_arr");
n("cap.agg", "Capture of other types", "Capture goes into the parts of $\\otimes$, $\\oplus$ and $\\exists$ and leaves types with $\\mathsf{tfree}$ unchanged.", "Only ends and closures have credits, so only they are restated.", DEF, "$((S@x)^{2} \\otimes \\ast) \\leadsto_{1,1} (S@x)^{1} \\otimes \\ast$.", "static/Contexts.v: tcap");
n("sub.tsub", "Subtyping $T \\leq T'$", "The least relation closed under Sub-Sess, Sub-Arr, Sub-Box, Sub-Ex and componentwise on $\\otimes$ and $\\oplus$, used by E-Sub.", "The branches of $\\mathsf{case}$ and of a received choice need one common type. Every clause weakens what a value guarantees.", "Without E-Sub two branches that create a channel with different facts have no common result type.", "$\\exists^{\\bot}\\rho.\\,\\{\\rho \\prec \\overline{\\rho\\cdot 0}\\}.\\,T \\leq \\exists^{\\bot}\\rho.\\,\\varnothing.\\,T$, and $(S@x)^{3} \\leq (S@x)^{1}$ in the lock-free mode.", "static/Contexts.v: tsub");
n("tp.sub-credit", "Credits may fall", "$a' \\leq a$ for the credits of an end.", "A credit is a lower bound on the counter of an end, so a smaller credit guarantees less. $\\mathsf{new}$ and every action return credit $N$, and a parameter or a payload asks a fixed credit $b \\leq N$.", "Without it a fresh end at credit $N$ fits only a parameter at credit exactly $N$, and no loop that ages an end before its self call types.", "$(S@x)^{3} \\leq (S@x)^{2}$.", "static/Contexts.v: tsub");
n("tp.sub-floor", "The wait bound of an arrow", "$h \\leq h'$ and $h' + a' \\leq h + a$ for the floors $h, h'$ and credits $a, a'$ of two arrows.", "The body of a closure may assume that every captured end has credit $h$, and the holder guarantees $h + a$ in total. Raising the floor to $h'$ is sound only when the guarantee $h' + a'$ does not exceed the old $h + a$.", "Without $h' + a' \\leq h + a$ a closure could claim a floor above the credit its captured ends have.", "$h = 1, a = 1$ converts to $h' = 2, a' = 0$.", "static/Contexts.v: tsub");
n("tp.sub-sess", "Session types up to equivalence", "$S \\simeq S'$, bisimilar head normal forms with equal annotations, which is $S \\approx S'$ at annotations $\\infty$.", "With $\\mathsf{Skip}$, sequencing and $\\mu$ one protocol has many spellings, e.g. $\\mathsf{Skip}.S \\simeq S$. Rules compare protocols by behaviour.", "Without it an unfolded recursive protocol and its folded form would be different types, and no loop that acts once and recurses would type.", "$\\mu\\alpha.\\,!\\ast.\\alpha \\leq\\ !\\ast.\\mu\\alpha.\\,!\\ast.\\alpha$ at the same point.", "static/Contexts.v: sub_sess, types/Types.v: sequiv");
n("tp.sub-ex", "An existential may drop facts", "$\\mathsf{facts}\\,C' \\subseteq \\mathsf{facts}\\,C$, the constraint $C'$ of the supertype states a subset of the facts of $C$ over the same variables.", "E-New states the facts $C$ of a creation in its existential. Two branches of a $\\mathsf{case}$ or two creations that serve one type then agree on the facts both state, by dropping the rest.", "Without it, two branches that create a channel with different facts have different result types, and the $\\mathsf{case}$ does not type.", "$\\exists^{\\bot}\\rho.\\,\\{\\rho \\prec \\overline{\\rho\\cdot 0}\\}.\\,T \\leq \\exists^{\\bot}\\rho.\\,\\varnothing.\\,T$.", "static/Contexts.v: sub_ex");
n("tp.sub-var", "Variance", "$\\leq$ is contravariant in the argument and covariant in the result of $\\multimap$, and covariant in the components of $\\otimes$ and $\\oplus$.", "A closure that accepts more and returns less can stand for one that accepts less and returns more.", DEF, "$((S@x)^{1} \\multimap (S@y)^{3}) \\leq ((S@x)^{2} \\multimap (S@y)^{1})$.", "static/Contexts.v: sub_arr, sub_prod, sub_sum");
n("tp.sub-agg", "Products and sums", "$T_1 \\otimes T_2 \\leq T_1' \\otimes T_2'$ when $T_i \\leq T_i'$ for $i = 1, 2$, and likewise for $\\oplus$.", "A product or a sum has no credit of its own, so it compares part by part.", DEF, "$(S@x)^{2} \\otimes \\ast \\leq (S@x)^{1} \\otimes \\ast$.", "static/Contexts.v: sub_prod, sub_sum");
n("tp.sub-teq", "Equal up to $\\simeq$", "$T \\equiv T'$, the two types have the same shape and their session types are pairwise $\\simeq$.", "The body of a box and of an existential is compared exactly up to protocol spellings. Credits inside it are not lowered, because a box is copied and an existential is opened at its own credit.", DEF, "$\\Box(\\ldots\\,(\\mathsf{Skip}.S)@x) \\leq \\Box(\\ldots\\,S@x)$.", "types/Types.v: teq");
n("E-Abs.phi", "Fresh future variable", "The body is typed under $(\\varnothing, \\varphi)$ for a $\\varphi \\notin \\mathrm{dom}\\,\\Gamma$ with $u \\prec \\varphi$.", "The body runs when a caller applies the closure, and by E-App every caller future $F$ satisfies $u \\prec F$. Typing under a fresh $\\varphi$ covers all such $F$.", "A body typed under the future of its definition is checked against facts that fail at another call site.", "The body of $\\mathsf{between}$ runs under $\\varphi$ with $\\kappa \\prec \\varphi$.", "static/Typing.v: e_abs, e_box");
n("E-Abs.lb", "Lower point of a closure", "$l \\preccurlyeq \\Delta$, the point $l$ lies at or below every element of $\\mathsf{heads}(\\Delta)$. Hidden ends put $\\bot$ there, which no point lies below.", "A holder of the closure reads the partner points of its ends only through $l$. A hidden end has no partner point to bound, so a closure cannot capture a hidden end.", "A thread holding ends at the unrelated points $1$ and $2$ has no common lower point, so E-Abs rejects a $\\lambda$ that captures both. E-SpawnLam types the spawn of such a $\\lambda$.", "Capturing $a^{+}$ at $\\rho$ gives $l = \\overline{\\rho}$.", "static/Contexts.v: lbx_below_h, lbound_of");
n("E-Abs.cap", "Capture", "$\\Delta \\leadsto_{h,a} \\Delta^{h}$ restates every captured end and closure at the floor $h$.", "The closure has credit $a$, and its body may assume credit $h$ on every captured end. Capture asks $h + a$ of each captured credit.", DEF, "$a^{+}$ at credit $2$ captured with $h = 1$ and $a = 1$ is seen at credit $1$.", "static/Contexts.v: thcap, lcap");
n("E-Abs.body", "Body of a $\\lambda$", "$e$ is typed under $\\Gamma$ extended by $u \\prec \\varphi$, the captured $\\Delta$ extended by the argument $T$, and the future $(\\varnothing, \\varphi)$. In the lock-free mode the captured entries are restated at the floor $h$.", "The body runs at a later call. It may rely only on its captured entries, its argument and $u \\prec \\varphi$, and E-App establishes $u \\prec F$ at every call.", DEF, "The body of the client loop with argument $S_1@\\iota \\otimes S_2@\\kappa$.", "static/Typing.v: e_abs");
n("E-App.ub", "$u \\prec F$ at a call", "The upper point $u$ of the closure satisfies $u \\prec F$.", "The callee waits only at points up to $u$. Every point at which the caller acts afterwards lies above $u$.", "A call of a closure that waits at $\\kappa$, while the caller must still act at a point below $\\kappa$, makes the caller wait on itself.", "main forces $\\mathsf{between}$ last, so $F = \\varnothing$.", "static/Typing.v: e_app");
n("E-App.fut1", "The first subterm runs while the rest is held", "$e_1$ is typed under $\\Delta_1 \\parallel \\Delta_2$, so its future is $F \\cup \\mathsf{heads}(\\Delta_2)$, with $\\bot$ added when $\\Delta_2$ has $\\bot$.", "The entries of the second subterm are held while $e_1$ runs. Hence $e_1$ must not wait above their partner points.", "$\\mathsf{let}\\ \\ast = \\mathsf{close}\\,c\\ \\mathsf{in}\\ \\mathsf{close}\\,d$ beside a partner that closes $d$ before $c$ deadlocks. E-LetU rejects the first thread unless $x_c \\prec \\overline{x_d}$.", "The cycle example needs $\\rho \\prec \\overline{\\rho\\cdot 0}$ for $\\mathsf{close}\\,c$ while $d$ is held.", "static/Typing.v: e_app, e_pair, e_letp, e_letu, e_case");
n("E-App.fut2", "The argument runs while the closure is held", "$e_2$ is typed while the thread holds the closure, so its future is $F \\cup \\{l\\}$ with $l$ the lower point of the closure. In the lock-free mode the closure ages by the cost of $e_2$, which needs that much credit.", "The closure is held while $e_2$ runs, and $l$ bounds the partner points of its ends from below.", DEF, "$f\\,(\\mathsf{close}\\,c)$ with $f$ capturing $d$.", "static/Typing.v: e_app");
n("E-Pair.fut2", "The second component runs while the first is held", "$e_2$ is typed while the thread holds the value of $e_1$, so its future is $F \\cup \\mathsf{heads}(T_1)$. In the lock-free mode $T_1$ ages by the cost of $e_2$.", "The value of $e_1$ is held while $e_2$ runs.", DEF, "$\\langle c, \\mathsf{close}\\,d\\rangle$ needs $x_d \\prec \\overline{x_c}$.", "static/Typing.v: e_pair");
n("tp.letp", "Body of a pair elimination", "$e_2$ is typed under $\\Delta_2$, aged by $e_1$ in the lock-free mode, extended by $T_2$ at index $0$ and $T_1$ at index $1$, under $F$.", "Both components become variables of $e_2$.", DEF, "$\\mathsf{let}\\ \\langle v, c\\rangle = \\mathsf{recv}\\,c\\ \\mathsf{in}\\ e$ binds the received value and the continuation end.", "static/Typing.v: e_letp");
n("tp.letu", "Body of a unit elimination", "$e_2$ is typed under $\\Delta_2$, aged by $e_1$ in the lock-free mode, under $F$, after $e_1$ returned $\\ast$.", "$\\ast$ holds no end, so nothing is bound. The rule sequences $e_1$ before $e_2$.", DEF, "$\\mathsf{let}\\ \\ast = \\mathsf{close}\\,c\\ \\mathsf{in}\\ \\mathsf{close}\\,d$.", "static/Typing.v: e_letu");
n("E-Case.branches", "Branches", "Each branch $e_i$ is typed under $T_i, \\Delta_2$ at the common result $T$.", "Exactly one branch runs, and the choice is known only at run time. Both branches must fit the same continuation.", DEF, "$\\mathsf{case}\\,(\\mathsf{branch}\\,o)\\,(a.\\,\\mathsf{close}\\,a)\\,(a.\\,\\mathsf{close}\\,a)$.", "static/Typing.v: e_case");
n("E-Box.unl", "$\\Delta$ unlimited", "Every entry of $\\Delta$ has unlimited type, so $\\Delta$ holds no end.", "A box value is copied freely. If it held an end, a copy would duplicate that end.", DEF, "$\\mathsf{ring}$ captures no variable.", "static/Contexts.v: lenv_unl");
n("E-Box.inst", "Typed for every instance", "The premise has one derivation of the body for every list $\\bar s$ with $\\mathsf{sinsts}\\,\\bar s$, one session type per session variable $\\bar\\alpha$ of the box.", "A force may pick any allowed $\\bar s$, and the derivation for that $\\bar s$ is the one that justifies the call. Checking every instance up front keeps E-Force a plain lookup.", DEF, "A box with no session variable has exactly one instance, the empty list, so the premise is one derivation.", "static/Typing.v: e_box");
n("E-Box.body", "Body of a box", "The body is typed with no end, the fresh point variables $\\bar\\iota$, the hypothesis $C(\\bar\\iota)$, the box as $f$, and the future $(\\varnothing, \\varphi)$.", "Each force instantiates $\\bar\\iota$ and the session variables anew. The body may assume only $C(\\bar\\iota)$ and $u \\prec \\varphi$.", DEF, "The body of the client loop.", "static/Typing.v: e_box");
n("E-Box.open", "Opened constraint", "$\\Gamma$ extended by the instance $C(\\bar\\iota)$ at the fresh variables.", "The body relies on $C$ at its own point variables, and every force checks $C$ at the chosen instance.", "Without $C$ the client loop cannot order the points of two consecutive rounds.", "$\\Gamma, C(\\iota, \\kappa, \\zeta)$.", "static/Contexts.v: hc_open");
n("E-Box.self", "The self", "The body binds the box as $f$ at index $0$, at its own type.", "This is recursion. A box holds no end, so it has no credit.", DEF, "$(\\mathsf{force}\\,f)\\,\\langle a, b\\rangle$ calls the self $f$.", "static/Typing.v: e_box");
n("E-Force.hold", "The instance meets $C$", "$\\Gamma \\vdash C[\\bar x]$, for points $\\bar x$, one per variable of $\\bar\\iota$.", "The body was typed under $C(\\bar\\iota)$. Running it at $\\bar x$ is correct only when $C[\\bar x]$ holds.", DEF, "main forces $\\mathsf{between}$ at $(\\rho, \\rho\\cdot 1)$, where $\\Lambda_0$ gives $C$.", "static/Typing.v: e_force, e_pack");
n("E-Force.ub", "$u[\\bar x] \\prec F$", "The highest point the body waits at, $u$ with the chosen points put in, lies below every point of the future $F$.", "After the force returns, the caller still acts at the points of $F$. If the body waited at a point above one of them, a partner could wait on the caller while the caller waits inside the body. This is the condition $u \\prec F$ of E-App for a box.", DEF, "The self call of a loop at $\\zeta$ under $F = \\varnothing$.", "static/Typing.v: e_force");
n("E-Send.unfold", "Send head", "$\\mathsf{unfold}(S_0) = {!}(\\bar\\iota.\\,T).S$.", "Rules read the first action of $S_0$ after unfolding, so a recursive protocol $\\mu\\alpha.S$ needs no rule of its own.", DEF, "$S_0 = \\mu\\alpha.\\,{!}\\ast.\\alpha$ unfolds to ${!}\\ast.(\\mu\\alpha.\\,{!}\\ast.\\alpha)$.", "static/Typing.v: e_send");
n("E-Send.heads", "$x \\prec T$, the action point below a held value", "$x \\prec T$ states $\\Gamma \\vdash x \\prec y$ for every $y \\in \\mathsf{heads}(T)$. If $T$ holds hidden ends, $\\bot \\in \\mathsf{heads}(T)$ and the check fails.", "A thread waiting at $x$ while it holds a value of $T$ does not offer the ends in $T$, so readiness asks $x$ below the partner point of each. Hidden ends have no known partner point, so a thread holding them may not wait.", "Without $\\bot$ in the heads, $\\mathsf{send}\\,\\langle p, o\\rangle$ with the unopened pair $p$ of a $\\mathsf{new}$ types, and the sender waits while holding ends at points nothing orders.", "The growing ring needs $Y \\prec \\overline{Y\\cdot 0}$ for the payload $a$ of the send on $y$ at $Y$.", "static/Typing.v: e_send; types/Types.v: heads, hbot");
n("E-Send.floor", "One hop", "$T' - 1 \\leq T[x\\cdot i]$, the payload value aged by one hop still has the credits the protocol guarantees.", "A handed end loses $1$ of its counter at the send. Asking the promised credits after the loss bounds how often one end may be handed on.", "Without the loss of $1$, an end is handed on forever, and its partner waits forever.", "The growing ring sends $a'$ at credit $4$ against a promised $2$.", "static/Typing.v: e_send");
n("E-Recv.unfold", "Receive head", "$\\mathsf{unfold}(S_0) = {?}(\\bar\\iota.\\,T).S$.", "Rules read the first action of $S_0$ after unfolding, so recursive protocols need no rule of their own.", DEF, "$\\mu\\alpha.\\,{?}\\ast.\\alpha$ unfolds to ${?}\\ast.(\\mu\\alpha.\\,{?}\\ast.\\alpha)$.", "static/Typing.v: e_recv");
n("E-Close.unfold", "Close head", "$\\mathsf{unfold}(S_0) = \\mathsf{Close}$.", "Rules read the first action of $S_0$ after unfolding.", DEF, "$\\mathsf{Close}@x$.", "static/Typing.v: e_close");
n("E-Select.unfold", "Select head", "$\\mathsf{unfold}(S_0) = \\oplus(S_1, S_2)$.", "Rules read the first action of $S_0$ after unfolding.", DEF, "$\\oplus(\\mathsf{Close}, \\mathsf{Close})$.", "static/Typing.v: e_select");
n("E-Branch.unfold", "Branch head", "$\\mathsf{unfold}(S_0) = \\&(S_1, S_2)$.", "Rules read the first action of $S_0$ after unfolding.", DEF, "$\\&(\\mathsf{Close}, \\mathsf{Close})$.", "static/Typing.v: e_branch");
n("E-Link.dual", "Linked ends dual", "$e$ returns $S@x \\otimes \\overline{S}@\\overline{x}$, two ends at dual types and dual points.", "After the link the partners of the two ends form one channel. They are a well-typed pair only when the linked ends are exactly dual at dual points.", DEF, "$\\mathsf{link}\\,\\langle c^{+}, d^{-}\\rangle$ with $c^{+} : S@x$ and $d^{-} : \\overline{S}@\\overline{x}$.", "static/Typing.v: e_link");
n("E-SpawnLam.age", "Handed ends lose $1$", "$\\Delta - 1$ ages every handed entry by one hop.", "A hand-over passes each counter minus $1$. A spawn is no action, so this loss is the only bound on how often an end is handed on by spawns.", "Under truncation a counter $0$ is handed on as $0$ again, and an end is passed from thread to thread forever.", "In the cycle example the thunk receives $d'$ with credit $1$ less.", "static/Typing.v: e_spawn_lam");
n("E-SpawnLam.body", "Body of a spawned $\\lambda$", "$e$ is typed under the handed $\\Delta$ extended by the unit argument, and the empty future.", "A spawned $\\lambda$ needs no lower point, because no thread holds it as a closure. Each spawned body therefore gets its own floor.", DEF, "$\\mathsf{spawn}\\,(\\lambda u.\\,\\mathsf{let}\\ \\ast = u\\ \\mathsf{in}\\ \\mathsf{close}\\,d')$.", "static/Typing.v: e_spawn_lam");
n("E-SpawnLam.future", "Empty future of the child", "The child body runs under $(\\varnothing, \\cdot)$, a future with no point, no variable and no $\\bot$.", "The child is a new thread with no context, so no point of any context lies in its future.", "Typing the child under every future above an upper point fails for a body that creates a channel at a fresh root and waits on that channel.", "P-Term types every thread under $(\\varnothing, \\cdot)$.", "static/Typing.v: e_spawn_lam");
n("E-Spawn.credit", "Closure credit $a \\geq 1$", "A spawned closure value has credit $a \\geq 1$.", "Spawning passes on the captured ends with their counters minus $1$, and $a \\geq 1$ makes up for that loss.", DEF, "$\\mathsf{spawn}\\,f$ with $f$ at credit $1$.", "static/Typing.v: e_spawn");
n("E-New.bot", "Lower bound $\\bot$", "The pair is at a root $\\rho$ that no point of the context is related to.", "$\\exists^{\\bot}$ records that the ends of the value are at points without a known lower bound, and $\\bot$ propagates into every future that holds the value.", DEF, "$\\mathsf{mk}_0$ returns $\\exists^{\\bot}\\iota.\\,C.\\,({?}\\ast.\\mathsf{Close})@\\overline{\\iota}$.", "static/Typing.v: e_new");
n("E-New.facts", "The constraint $C$", "A set of facts, possibly infinite, over $\\pi$, its shifts and fields, and points of $\\Gamma$.", "The derivation chooses the facts the new channel needs, and an interval $l \\prec \\pi \\prec u$ is the simplest case. Opening the existential adds $C$ to $\\Gamma$.", "With facts limited to finitely many bounds by held ends, a client and server loop that orders the two channels at every round, $\\iota^{+k} \\prec \\overline{\\kappa^{+k}}$ for all $k$, does not type.", "$C = \\{\\rho \\prec \\overline{\\rho\\cdot 0},\\ \\overline{\\rho} \\prec \\rho\\cdot 0\\}$ in the cycle example.", "static/Typing.v: e_new");
n("E-New.pos", "Position $\\pi$", "Either $\\pi = \\rho$, bound by the existential, or $\\pi = x\\cdot\\kappa$ for a point $x$ of the context.", "A channel created to be sent on an end at $x$ lands at the field $x\\cdot j$ where the receiver expects its $j$-th payload end.", DEF, "$d$ at $\\iota\\cdot 0$ in the example with a channel between two box arguments.", "static/Typing.v: e_new");
n("E-New.strict", "$\\mathsf{strict}(\\Gamma \\cup C)$", "The facts of $\\Gamma$, the order $\\prec_W$ and $C$ together derive no $x \\prec x$.", "Every creation grows the world by $C$, and the results ask a strict world. The check keeps every grown world strict.", "Facts $\\overline{\\rho} \\prec \\rho\\cdot 0$ and $\\rho\\cdot 0 \\prec \\overline{\\rho}$ in one $C$ give a cycle, and two threads waiting on each other would both count as ready.", "$\\{\\rho \\prec \\overline{\\rho\\cdot 0}\\}$ is strict.", "static/Typing.v: e_new");
n("E-New.dual", "Dual pair at $N$", "$c^{+}$ has type $S@\\pi$ and $c^{-}$ type $\\overline{S}@\\overline{\\pi}$, both at credit $N$.", "The fuel layer starts both counters of a new channel at $N$, and the credits are lower bounds on these counters.", DEF, "$(S_a@\\pi)^{N} \\otimes (S_b@\\overline{\\pi})^{N}$ with $S_b = \\overline{S_a}$.", "static/Typing.v: e_new");
n("E-Sub.cost", "Effects may rise", "$\\varepsilon \\leq \\varepsilon'$, so $c \\leq c'$ in $\\mathbb{N} \\cup \\{\\infty\\}$ and $\\vartheta \\leq \\vartheta'$ pointwise.", "The cost and the ticket need are upper bounds, so a larger bound is also correct. The branches of a case and closures passed to one parameter have different effects, and the larger bound covers both.", DEF, "Every cost may rise to $\\infty$.", "static/Typing.v: e_sub, types/Costs.v: tle");
n("E-Weak.drop", "Weakening", "$\\Delta'$ arises from $\\Delta$ by emptying entries of unlimited type only.", "A linear entry may hold ends that must be used, so only entries of unlimited type are dropped.", DEF, "Dropping an unused box variable.", "static/Contexts.v: lenv_wk");
n("E-Pack.lb", "Lower bound of a pack", "$l = \\bot$, the ends become hidden, or $l \\preccurlyeq T[\\bar x]$, every head of the packed value lies at or above $l$, where $l = \\cdot$ asks that $T[\\bar x]$ holds no end.", "After packing, a holder refers to the ends only through $l$, so $l$ must bound the heads of the packed value from below. The value relation at an existential states exactly this bound.", DEF, "Packing a fresh pair at $\\bot$.", "static/Contexts.v: lbx_below_h");
n("E-Open.entry", "Opened entry", "$\\Delta(i) = \\exists^{l}\\bar\\iota.\\,C.\\,T$ and $T$ is not unlimited.", "Opening replaces entry $i$ in place. Variable renaming, used for contraction, maps distinct linear entries to distinct indices, and this needs the opened entry to be linear.", DEF, "Opening the result of $\\mathsf{new}$.", "static/Typing.v: e_open");
n("E-Open.body", "Body after opening", "$e$ is typed with $C(\\bar\\iota)$ added to $\\Gamma$ and entry $i$ replaced by $T$, under the same future and result.", "The fresh variables stand for the unknown witness, and $C$ is the only hypothesis about the witness in the scope. Freshness keeps them out of $F$ and $U$.", DEF, "$\\mathsf{let}\\ p = (\\mathsf{force}\\,\\mathsf{mk}_0)\\,\\ast\\ \\mathsf{in}\\ \\ldots$ opens at $\\iota$.", "static/Typing.v: e_open");
n("pfree", "$\\mathsf{pfree}\\,\\Sigma$", "For every $o \\in \\mathrm{dom}\\,\\Sigma$, $\\overline{o} \\notin \\mathrm{dom}\\,\\Sigma$.", "P-Term puts every channel whose two ends the thread holds into $C_0$. Hence an interface never holds both ends of a channel, which the semantic P-Connect needs.", "No program is lost, because such a channel always moves into $C_0$.", "$\\Sigma = \\{c^{+}, c^{-}\\}$ is rejected, and $(\\{c\\}, \\ldots)$ with $\\Sigma = \\varnothing$ types instead.", "static/Typing.v: pfree");
n("P-Term.C0", "$\\mathrm{dom}\\,\\Theta_B = \\mathsf{ends}(C_0)$", "$o \\in \\mathrm{dom}\\,\\Theta_B$ iff the channel of $o$ is in $C_0$.", "Every end of the thread is an interface end or an end of a restricted channel, and the second kind is exactly $\\Theta_B$.", DEF, "$C_0 = \\varnothing$ and $\\Theta_B = \\varnothing$ for a source program.", "static/Typing.v: p_term");
n("P-Term.disj", "$\\mathsf{chans}\\,\\Sigma \\cap C_0 = \\varnothing$", "No channel of the interface is restricted.", "Then every end of $\\Sigma^{N} \\cup \\Theta_B$ lies in exactly one part, and the interface is the environment restricted to the channels outside $C_0$.", DEF, "$\\Sigma = \\{c^{+} \\mapsto \\mathsf{Close}@x\\}$ with $C_0 = \\varnothing$.", "static/Typing.v: p_term");
n("P-Term.pairs", "Restricted pairs dual", "For every $c \\in C_0$ there are $S$ and $x$ with $\\Theta_B(c^{+}) = S@x^{N}$ and $\\Theta_B(c^{-}) = \\overline{S}@\\overline{x}^{N}$.", "A restricted channel has both ends inside the process. They synchronize with each other only, so they need dual types at dual points.", DEF, "$c^{+} : S@x$ and $c^{-} : \\overline{S}@\\overline{x}$.", "static/Typing.v: p_term");
n("P-Term.typed", "Thread typing", "$t$ is typed under no facts, the interface ends and $\\Theta_B$, and the empty future.", "The process judgment has static premises only. Its semantic content comes from the fundamental theorems.", DEF, "The client and server main.", "static/Typing.v: p_term");
n("P-Term.future", "Empty future", "A thread at top level runs under $(\\varnothing, \\cdot)$.", "A thread has no context, so no point lies in its future.", DEF, "$(\\varnothing, \\cdot)$.", "static/Typing.v: p_term");
n("lf.meets", "$N \\in \\mathbb{N} \\Rightarrow \\vartheta(0) \\in \\mathbb{N}$", "At a finite refill the ticket need of the thread is finite, trivial at $N = \\infty$.", "Lock freedom needs a finite number of link tickets per thread, and typing at a finite $N$ does not give one, because a ticket need may have offset $\\infty$.", "A loop that links once per round has no finite ticket need and is rejected at finite $N$.", "$\\vartheta = \\hat 1$, need $0$, in the examples without links.", "static/Typing.v: p_term");
n("lf.N", "$N \\in \\mathbb{N}$", "The refill of lock-free typing is a natural number.", "Lock freedom ranks waiting threads by counters as natural numbers, and at $N = \\infty$ every counter is $\\infty$.", DEF, "$N = 4$ for the growing ring.", "static/Typing.v: ptyped");
n("P-Connect.left", "Left component", "$(C_1, E_1)$ is typed over $\\Sigma_1 \\cup \\Sigma_C$ in $W_1$ at result $T$.", "The main thread lies on the left, so the left side has the result $T$ and the right side returns $\\ast$.", DEF, "$\\mathsf{close}\\,c^{+}$ at $T = \\ast$.", "static/Typing.v: p_connect");
n("P-Connect.right", "Right component at $\\ast$", "$(C_2, E_2)$ is typed over $\\Sigma_2 \\cup \\overline{\\Sigma_C}$ in $W_2$ at result $\\ast$.", "Only the main thread returns a value, and every other thread returns $\\ast$.", DEF, "$\\mathsf{close}\\,c^{-}$.", "static/Typing.v: p_connect");
n("P-Connect.cut", "Exact dual cut $\\overline{\\Sigma_C}$", "$\\overline{\\Sigma_C}$ maps $\\overline{o}$ to $\\overline{S}@\\overline{x}$ for every $o \\mapsto S@x$ in $\\Sigma_C$.", "After composition the two ends of each cut channel are restricted, and lock freedom asks their protocols dual up to annotations. An exact dual gives this, a dual up to annotations does not.", "An annotation mismatch on a cut channel breaks the payload credit of a later message.", "$\\overline{\\{c^{+} \\mapsto \\mathsf{Close}@x\\}} = \\{c^{-} \\mapsto \\mathsf{Close}@\\overline{x}\\}$.", "static/Typing.v: senv_dual");
n("P-Connect.disj", "Disjoint channels", "$\\mathrm{dom}\\,\\Sigma_1 \\cap \\mathrm{dom}\\,\\Sigma_C = \\varnothing$, $\\mathrm{dom}\\,\\Sigma_2 \\cap \\mathrm{dom}\\,\\overline{\\Sigma_C} = \\varnothing$, the channel sets of $\\Sigma_1$, $\\Sigma_2$, $\\Sigma_C$ are pairwise disjoint, $C_1 \\cap C_2 = \\varnothing$, and each $C_i$ is disjoint from the channels of $\\Sigma_1$, $\\Sigma_2$, $\\Sigma_C$.", "Every channel then belongs to one side. The cut $\\Sigma_C$ is the only channel set both sides use, so composition merges no two channels.", DEF, "Two closes cut at $c$ with $\\Sigma_1 = \\Sigma_2 = \\varnothing$ and $C_1 = C_2 = \\varnothing$.", "static/Typing.v: p_connect");
n("P-Connect.cutfree", "$\\mathsf{pfree}\\,\\Sigma_C$", "The cut holds no partner pair.", "The composite interface stays partner-free, which P-Term establishes for single threads.", DEF, "$\\Sigma_C = \\{c^{+} \\mapsto \\mathsf{Close}@x\\}$.", "static/Typing.v: p_connect");
n("P-Connect.strict", "Only the shared part is compared", "$\\mathsf{strict}(W_1|_S \\sqcup W_2|_S)$ for $S = A_{W_1} \\cap A_{W_2}$, the roots of both worlds. $W|_S$ keeps the facts $x \\prec_W y$ derivable in $W$ whose roots lie in $S$.", "Each side is strict by its own derivation, so the only new cycles a join can create run through shared roots. Checking the orders the two sides induce on those roots is enough, and the join is then strict.", "If $W_1$ derives $\\rho \\prec \\rho\\cdot 0$ and $W_2$ derives $\\rho\\cdot 0 \\prec \\rho$, the join has a cycle and two threads each wait on the other although each side alone is ready.", "Two worlds without a common root need no check.", "static/Typing.v: p_connect, p_join_iff_connect");
n("P-Term.strict", "$\\mathsf{strict}\\,W$", "The world of a single thread is well formed and acyclic.", "Every process derivation then is over a strict world. P-Connect checks only the shared part, and the joined world is strict again.", "Without it P-Connect would have to check the whole join.", "The empty world.", "static/Typing.v: p_term");
n("P-Connect.join", "Result in $W_1 \\sqcup W_2$", "The composite is typed in the join of the two worlds.", "Each component keeps its own facts, and the join contains the facts of both.", DEF, "Two closes are typed in the join of their two worlds.", "static/Typing.v: p_connect");
n("guard.judg", "The guard $\\varnothing \\vdash\\!\\triangleright t$", "$\\Lambda \\vdash\\!\\triangleright t$ holds iff the self of every box in $t$ is used only after a session action of the body.", "$\\kappa_L$ makes $\\beta$ free, so without the guard $!(f = \\mathsf{force}\\,f)$ types and diverges on free steps. Deadlock-free typing does not use the guard.", "$!(f = \\mathsf{force}\\,f)$ types and is in no live relation.", "$!(f = \\lambda x.\\,\\mathsf{let}\\ \\langle v, x'\\rangle = \\mathsf{recv}\\,x\\ \\mathsf{in}\\ (\\mathsf{force}\\,f)\\,x')$ is guarded.", "static/Guard.v: lguard");
n("guard.marks", "Marks $\\Lambda$", "$\\Lambda$ maps each variable to $\\mathsf{true}$, marked and not usable, or $\\mathsf{false}$.", "A marked variable denotes a self that is available only one step later, as in guarded recursion.", DEF, "$\\mathsf{true}.\\varnothing$ marks the self of a box.", "static/Guard.v: lguard");
n("guard.var", "Marked variables unusable", "$\\Lambda \\vdash\\!\\triangleright y$ requires $\\Lambda(y) = \\mathsf{false}$.", "Using the self before an action would recurse with no step of positive cost in between.", "$!(f = \\lambda x.\\,(\\mathsf{force}\\,f)\\,x)$ uses $f$ under a $\\lambda$ before any action and is rejected.", "$y$ with $\\Lambda(y) = \\mathsf{false}$.", "static/Guard.v: gl_var");
n("guard.lam", "$\\lambda$ keeps the marks", "$\\Lambda \\vdash\\!\\triangleright \\lambda b$ iff $\\mathsf{false}.\\Lambda \\vdash\\!\\triangleright b$.", "The body of a $\\lambda$ runs at the level at which the $\\lambda$ is a value, so a self marked outside stays marked inside.", DEF, "$\\lambda x.\\,(\\mathsf{force}\\,f)\\,x$ is not guarded under $\\Lambda(f) = \\mathsf{true}$.", "static/Guard.v: gl_lam");
n("guard.box", "A box marks its self", "$\\Lambda \\vdash\\!\\triangleright\\ !b$ iff $\\mathsf{true}.\\Lambda \\vdash\\!\\triangleright b$.", "The self of a box is the recursive call, which must wait for an action.", DEF, "$!b$ checks $b$ under $\\mathsf{true}.\\Lambda$.", "static/Guard.v: gl_box");
n("guard.cong", "Frames", "A frame checks its first subterm $e_1$ under $\\Lambda$ and the rest under the marks $\\Lambda'$ that $e_1$ leaves.", "Without an action no step of positive cost happens, so every mark stays in force until $e_1$ acts.", DEF, "$\\Lambda \\vdash\\!\\triangleright e_1\\,e_2$ from $\\Lambda \\vdash\\!\\triangleright e_1$ and $\\Lambda \\vdash\\!\\triangleright e_2$ with $\\Lambda' = \\Lambda$.", "static/Guard.v: gl_app, gl_pair, gl_letu, gl_letp, gl_case");
n("guard.tick", "$\\mathsf{kmarks}\\,\\Lambda\\,\\Lambda'\\,e$", "$\\Lambda' = \\Lambda$, or $\\Lambda' = \\varnothing$ and $\\mathsf{acts}\\,e$.", "After a session action the rest runs one level lower, where every self is available.", "Without the second case no loop that recurses after an action is guarded.", "$\\mathsf{let}\\ \\langle v, x'\\rangle = \\mathsf{recv}\\,x\\ \\mathsf{in}\\ (\\mathsf{force}\\,f)\\,x'$ takes $\\Lambda' = \\varnothing$.", "static/Guard.v: kmarks");
n("guard.bind", "Bound variables unmarked", "Variables bound by a pair elimination or a case are marked $\\mathsf{false}$.", "The bound value is computed by $e_1$ under $\\Lambda$. A value checked under $\\Lambda$ contains no variable marked in $\\Lambda$, so binding it unmarked lets no self escape.", DEF, "$\\mathsf{let}\\ \\langle a, b\\rangle = e_1\\ \\mathsf{in}\\ e_2$ checks $e_2$ under $\\mathsf{false}.\\mathsf{false}.\\Lambda$.", "static/Guard.v: gl_letp, gl_case");
n("guard.acts", "$\\mathsf{acts}\\,e$", "$\\mathsf{acts}$ is the least predicate closed under the clauses shown, so every evaluation of $e$ to a value performs a step $k\\,v$ with $k \\in \\{\\mathsf{send}, \\mathsf{recv}, \\mathsf{close}, \\mathsf{select}_i, \\mathsf{branch}\\}$.", "Each such step costs at least one level in the live cost table, so the rest after an acting $e_1$ runs one level lower, where the selves are in $V$.", DEF, "$\\mathsf{acts}\\,(\\mathsf{recv}\\,x)$.", "static/Guard.v: acts, sprim");
n("guard.proc", "Guard of a process $\\vdash\\!\\triangleright p$", "Every thread $t$ of $p$ satisfies $\\varnothing \\vdash\\!\\triangleright t$.", "Live soundness and lock-free typing ask it beside process typing.", DEF, "The client and server main is guarded.", "static/FundamentalProc.v: pguard");
n("tp.Sigma", "The interface $\\Sigma$", "$\\Sigma$ is a finite map from the ends a process offers to its environment to pairs $S@x$ of a session type and a point.", "A process is typed against its interface, and composition cuts interface ends against each other.", DEF, "$\\Sigma = \\{c^{+} \\mapsto \\mathsf{Close}@x\\}$.", "static/Contexts.v: senv");
n("tp.pjudg", "$\\Sigma \\vdash^{N}_{W} p : T$", "The process $p$ is typed over $\\Sigma$ in $W$ at refill $N$ with result $T$, derived by P-Term and P-Connect.", "One judgment serves deadlock freedom at $N = \\infty$ and lock freedom at finite $N$.", DEF, "$\\varnothing \\vdash^{\\infty}_{W} (\\varnothing, \\{t\\}) : \\ast$.", "static/Typing.v: ptyped");
n("tp.lfjudg", "$\\Sigma \\Vdash^{N}_{W} p : T$", "$\\Sigma \\Vdash^{N}_{W} p : T$ iff $N \\in \\mathbb{N}$, $\\Sigma \\vdash^{N}_{W} p : T$ and $\\vdash\\!\\triangleright p$.", "Lock freedom needs finite counters and no infinite run of free steps, and the guard excludes the latter.", DEF, "Two threads closing $c^{+}$ and $c^{-}$, at every $N \\in \\mathbb{N}$.", "static/Typing.v: ptyped, static/FundamentalProc.v: pguard");
n("tp.chans", "$\\mathsf{chans}\\,\\Sigma$", "The set of channels of the ends in $\\mathrm{dom}\\,\\Sigma$.", "Restricted sets are sets of channels, so disjointness is stated on channels.", DEF, "$\\mathsf{chans}\\,\\{c^{+}, d^{-}\\} = \\{c, d\\}$.", "static/Typing.v: chans_of");
n("tp.ends", "$\\mathsf{ends}(C)$", "The set $\\{c^{+}, c^{-} \\mid c \\in C\\}$.", "A restricted channel contributes both its ends.", DEF, "$\\mathsf{ends}(\\{c\\}) = \\{c^{+}, c^{-}\\}$.", "static/Typing.v: p_term");
n("tp.lift", "$\\Sigma^{N}$", "$\\Sigma$ with every entry at credit $N$.", "Interface ends start a thread at credit $N$, as fresh ends do.", DEF, "$\\{c^{+} \\mapsto \\mathsf{Close}@x\\}^{N} = \\{c^{+} \\mapsto \\mathsf{Close}@x^{N}\\}$.", "static/Contexts.v: tenv_of");
n("E-Box.fresh", "$\\bar\\iota$ fresh", "The bound point variables $\\bar\\iota$ occur nowhere in $\\Gamma$, $\\Delta$, $F$ or the result type.", "They stand for points chosen later, at each force or for the unknown witness of an existential, so nothing in scope may mention these variables. The Rocq uses de Bruijn indices and shifts the context instead.", DEF, "Opening $\\exists^{\\bot}\\iota.\\,C.\\,T$ under a context that mentions $\\rho$ picks $\\iota \\neq \\rho$.", "types/Points.v: pshift; static/Typing.v: e_box, e_open");
n("tp.pinst", "Point instance $T[\\bar x]$", "Replaces the point variables $\\bar\\iota$ of $T$ by the points $\\bar x$.", "Forcing and packing choose concrete points for the bound variables.", DEF, "$(S@\\iota)[\\rho] = S@\\rho$.", "types/Types.v: ty_inst");
n("tp.sinst", "Session instance $U[\\bar s]$", "Replaces the session variables of $U$ by the session types $\\bar s$.", "A box is polymorphic in its session variables, and each force chooses an instance.", DEF, "$({\\alpha}@x)[\\mathsf{Close}] = \\mathsf{Close}@x$.", "types/Types.v: sinst_ty");
n("tp.sinsts", "Allowed session instances $\\mathsf{sinsts}\\,\\bar s$", "The session types a session variable of a box may stand for. Every recursion $\\mu\\alpha.S$ inside each $s \\in \\bar s$, also inside payloads, passes an action before $\\alpha$ recurs. At $N = \\infty$ each $s$ also has no finite credit.", "The rules read the first action of a protocol after unfolding. An instance such as $\\mu\\alpha.\\alpha$ has no first action, so substituting it would give an end no rule can type. At $N = \\infty$ every annotation in a derivation is $\\infty$, and an instance with a finite credit inside its payloads would bring one in.", "Without the first condition a box with a variable $\\alpha$ could be forced at $\\mu\\alpha.\\alpha$, and an end of type $\\mu\\alpha.\\alpha$ would be stuck with no action to perform.", "$\\mu\\alpha.\\,{!}\\ast.\\alpha$ and $\\mathsf{Close}$ are allowed, $\\mu\\alpha.\\alpha$ and $\\mu\\alpha.\\,\\mathsf{Skip}.\\alpha$ are not.", "static/Contexts.v: sinsts; types/Types.v: hcontractive");
n("tp.max", "$\\max(\\varepsilon_1, \\varepsilon_2)$", "The larger of two effects, $(\\max(c_1, c_2), \\max(\\vartheta_1, \\vartheta_2))$ with the ticket needs compared pointwise.", "Only one branch of a case runs, so its effect is bounded by the larger of the two.", DEF, "$\\max(1, (0, \\mathsf{tlink}\\,\\hat 1)) = (1, \\mathsf{tlink}\\,\\hat 1)$.", "types/Costs.v: fmax, tmax");
n("tp.vdash", "The term turnstile $\\vdash$", "The least relation closed under E-Unit to E-Open. The deadlock-free judgment $\\Gamma ; \\Delta \\vdash^{F} t : T$ is the instance $N = \\infty$ with every annotation $\\infty$.", "One relation has the session type, the points and, in the lock-free mode, the credits and the effect of $e$, so every mode reads its premises off one derivation.", DEF, "$\\varnothing ; \\varnothing \\vdash^{(\\varnothing, \\cdot)} \\ast : \\ast$.", "static/Typing.v: typed, dftyped");
n("tp.msunion", "Multiset union $E_1 \\uplus E_2$", "$E_1 \\uplus E_2$, the multiset sum, counts every thread as often as $E_1$ and $E_2$ together.", "A composite process runs the threads of both components side by side.", DEF, "$\\{t_1\\} \\uplus \\{t_2\\} = \\{t_1, t_2\\}$.", "lang/Syntax.v: proc");

// ---- signatures and arguments ----
const A = (name, meaning) => ({ name, meaning });
const aGa = A(R`\Gamma`, R`the hypotheses, constraint instances $(C, \bar x)$ and future variables $\varphi \mapsto u$`);
const aDe = A(R`\Delta`, R`the linear context, ends $o$ with end types and de Bruijn indices with types`);
const aF = A('F', R`the future, the points at which the context acts after the term`);
const aW = A('W', R`the world whose order $\prec_W$ the rule reads`);
const aN = A('N', R`the refill, $N \in \mathbb{N} \cup \{\infty\}$`);
const aE = A('e', R`the term`);
const aT = A('T', R`the result type`);
const aH = A('H', R`the entries the thread holds while $e$ runs, a context or a type`);
const aEps = A(R`\varepsilon`, R`the effect of $e$, its cost and ticket need, lock-free mode only`);
const aX = A('x', R`the point of the end the action is on`);
const aS0 = A(R`S_0`, R`the session type of the end before the action`);
const JG = R`\Gamma ; \Delta \parallel H \vdash^{F} e : T\ !\ \varepsilon`;
const JA = [aGa, aDe, aH, aF, aE, aT, aEps];
const PJ = R`\Sigma \vdash^{N}_{W} p : T`;
const aSi = A(R`\Sigma`, R`the interface, a finite map from the ends the process offers to its environment to $S@x$`);
const aP = A('p', R`the process $(C, E)$, restricted channels $C$ and a multiset $E$ of threads`);
const aPT = A('T', R`the result type of the main thread`);
const aLam = A(R`\Lambda`, R`the marks, a list mapping each variable to $\mathsf{true}$ (unusable) or $\mathsf{false}$`);
const unf = (k, form) => sa(k, R`\mathsf{unfold}(S_0) = ${form}`, [aS0, A(R`\mathsf{unfold}`, R`the head normal form, which unfolds $\mu$ and removes leading $\mathsf{Skip}$`)]);

sa('tj.Gamma', R`\Gamma : (\mathsf{Bcs} \times \mathsf{Pt}^{*})^{*} \times (\mathsf{FVar} \rightharpoonup_{\mathrm{fin}} \mathsf{Pt})`, [A(R`(C, \bar x)`, R`a constraint $C$ instantiated at the list of points $\bar x$`), A(R`\varphi \mapsto u`, R`a future variable $\varphi$ with the fact $u \prec \varphi$`)]);
sa('tj.held', R`\Delta \parallel H \vdash^{F} e \ \equiv\ \Delta \vdash^{F \cup \mathsf{heads}(H)} e\ \land\ H - c\ \text{defined}`, [A(R`F \cup \mathsf{heads}(H)`, R`$F$ with the partner points of the ends in $H$ added, and the flag $\bot$ added when $H$ holds an unopened existential at $\bot$`), aH, A('c', R`the cost of $e$, lock-free mode only`)]);
sa('tj.hage', R`H - c`, [aH, A('c', R`the cost of $e$`)]);
sa('lfi.credit', R`(S@x)^{a},\ (T \multimap U)^{a},\ a \in \mathbb{N} \cup \{\infty\}`, [A('a', R`a lower bound on the counter of the end, or of the ends a closure captured`)]);
sa('lfi.cost', R`e : T\ !\ (c, \vartheta),\ \Delta - c,\ (S@x^{+})^{N}`, [A('c', R`the cost, an upper bound on the actions of $e$`), A('N', R`the refill`)]);
sa('lfi.floor', R`T \multimap[\varepsilon ; h]\, U`, [A('h', R`the credit the body may assume of every captured end`)]);
sa('lfi.hop', R`T' - 1 \leq T[x\cdot i],\ \Delta - 1,\ a \geq 1`, [A(R`T'`, R`the type of a payload value`)]);
sa('lfi.tickets', R`\vartheta = (s, b),\ \vartheta(r) = 2^{s} r + b`, [A(R`\vartheta`, R`the ticket need, the tickets a term needs to leave $r$ behind`)]);
sa('lfi.guard', R`\Lambda \vdash\!\triangleright t`, [A(R`\Lambda`, R`the marks, which variables are boxes not yet allowed to recur`)]);
sa('lfi.wf', R`\mathsf{wfworld} : \mathsf{World} \to \mathsf{Prop}`, [A('W', R`a world`)]);
sa('tj.eff', R`\varepsilon = (c, \vartheta) \in \mathsf{Eff} = (\mathbb{N} \cup \{\infty\}) \times \mathsf{Tix}`, [A('c', R`the cost`), A(R`\vartheta`, R`the ticket need`)]);
sa('tj.seq', R`\cdot : \mathsf{Eff} \times \mathsf{Eff} \rightharpoonup \mathsf{Eff}`, [A(R`\varepsilon_1, \varepsilon_2`, R`the effects of the first and the second part`)]);
sa('tj.zero', R`0 = (0, \hat 1) \in \mathsf{Eff}`, []);
sa('tj.one', R`1 = (1, \hat 1) \in \mathsf{Eff}`, []);
sa('tj.Delta', R`\Delta : (\mathsf{End} \rightharpoonup_{\mathrm{fin}} \mathsf{Ty}) \times \mathsf{Ty}_{\bot}^{*}`, [A('o', R`an end held by the term, with its end type $(S@x)^{a}$`), A(R`\Delta(i)`, R`the entry of de Bruijn index $i$, empty or a type $T$`)]);
sa('tj.F', R`F : \mathcal{P}_{\mathrm{fin}}(\mathsf{Pt}) \times (\mathsf{FVar} + \{\bot, \cdot\})`, [A('X', R`the finite set of points the context acts at after the term`), A(R`\varphi`, R`a future variable standing for an unknown set of points above its bound`), A(R`\bot`, R`the flag that the context holds ends at points unknown to the term`)]);
sa('tj.W', R`W : \mathsf{World}`, [A('W', R`a world $(A, \prec_A)$ of roots and facts`)]);
sa('tj.N', R`N \in \mathbb{N} \cup \{\infty\}`, [A('N', R`the credit of a fresh end and of an end after an action on it, $\infty$ for deadlock-free typing`)]);
sa('ctx.tsplit', R`\Theta = \Theta_1 \uplus \Theta_2 \iff \mathrm{dom}\,\Theta_1 \cap \mathrm{dom}\,\Theta_2 = \varnothing \land \Theta = \Theta_1 \cup \Theta_2`, [A(R`\Theta_1, \Theta_2`, R`the ends given to the first and to the second subterm`)]);
sa('ctx.lsplit', R`\Delta = \Delta_1, \Delta_2`, [aDe, A(R`\Delta_1, \Delta_2`, R`the contexts of the two subterms, the ends disjoint and the index lists of the same length as in $\Delta$`), A('i', R`a de Bruijn index, linear entries go to one side, unlimited entries to both`)]);
sa('ctx.hyps', R`(C, \bar x) \in \Gamma`, [A('C', R`a box constraint, a set of facts over its bound point variables`), A(R`\bar x`, R`the points $C$ is instantiated at, fresh point variables $\bar\iota$ inside a box or an opened existential`)]);
sa('ctx.fvar', R`(\varphi \mapsto u) \in \Gamma`, [A(R`\varphi`, R`a future variable naming the unknown future of a caller`), A('u', R`the upper point of the closure or box, with $u \prec \varphi$`)]);
sa('ctx.fvarF', R`F = (X, \varphi)`, [A(R`\varphi`, R`the variable part of the future`), A('X', R`the known points of the future`)]);
sa('ctx.bot', R`F = (X, \bot)`, [A(R`\bot`, R`the flag that some held end of the context has a point unknown to the term`), A('X', R`the known points of the future`)]);
sa('ctx.slt', R`\Gamma \vdash x \prec y \subseteq \mathsf{Hctx} \times \mathsf{Pt} \times \mathsf{Pt}`, [aGa, A('x, y', R`points, the judgment states that $x$ lies strictly below $y$`)]);
sa('ctx.empty', R`\Delta\ \text{unlimited} \iff \Delta \text{ holds no end} \land \forall i.\ \Delta(i) = \bot \lor \mathsf{unlimited}\,\Delta(i)`, [aDe]);
sa('ctx.only', R`\Delta, x : T`, [A('x', R`the variable or end used`), A('T', R`its type`), A(R`\Delta`, R`the rest of the context, unlimited`)]);
sa('side.act', R`x \prec F \iff (\forall y \in X.\ \Gamma \vdash x \prec y) \land (F = (X, \varphi) \Rightarrow \Gamma \vdash x \prec \varphi) \land F \neq (X, \bot)`, [aX, aF, aGa]);
sa('act.refill', R`(S@x)^{N}`, [A('S@x', R`the end after the action, at its new point`), aN]);
sa('side.ub', R`u \prec F \iff (\forall y \in X.\ \Gamma \vdash u \prec y) \land (F = (X, \varphi) \Rightarrow \Gamma \vdash u \prec \varphi) \land F \neq (X, \bot)`, [A('u', R`the upper point of a closure or box, the highest point its body waits at`), aF, aGa]);
sa('side.lb', R`l \preccurlyeq H \iff (l = \cdot \Rightarrow H = \varnothing) \land \forall y \in H.\ l = y \lor \Gamma \vdash l \prec y`, [A('l', R`a lower point, or $\cdot$ when the value holds no end`), A('H', R`a set of heads, partner points of held ends`)]);
sa('side.hold', R`\Gamma \vdash C[\bar x] \iff \forall (y \prec z) \in C[\bar x].\ \Gamma \vdash y \prec z`, [A('C', R`a constraint over $m$ point variables`), A(R`\bar x`, R`a list of $m$ points, the instance`), aGa]);
sa('age.free', R`\mathsf{tfree}\,T \Rightarrow T - c = T`, [A('T', R`a type holding no end`), A('c', R`the cost of what runs meanwhile`)]);
sa('age.idle', R`\mathsf{idle}\,S \Rightarrow (S@x)^{a} - c = (S@x)^{\max(a - c, 0)}`, [A('S', R`a session type with $\mathsf{unfold}(S) = \mathsf{Skip}$`), A('x', R`the point of the end`), A('a', R`its credit`), A('c', R`the cost of what runs while the end is held`)]);
sa('age.credit', R`c \leq a \Rightarrow (S@x)^{a} - c = (S@x)^{a - c}`, [A('a', R`the credit of the end or closure`), A('c', R`the cost of what runs while it is held`)]);
sa('age.agg', R`(T_1 \otimes T_2) - c = (T_1 - c) \otimes (T_2 - c)`, [A(R`T_1, T_2`, R`the components`), A('c', R`the cost of what runs while the value is held`)]);
sa('age.ctx', R`\Delta - \varepsilon`, [A(R`\Delta`, R`the entries held while a subterm runs`), A(R`\varepsilon = (c, \vartheta)`, R`the effect of that subterm, whose cost $c$ ages every entry`)]);
sa('cap.sess', R`h + a \leq a_0 \Rightarrow (S@x)^{a_0} \leadsto_{h,a} (S@x)^{h}`, [A('h', R`the floor of the closure, the credit its body may assume of every captured end`), A('a', R`the credit of the closure`), A(R`a_0`, R`the credit of the captured end`)]);
sa('cap.arr', R`h_0 \leq h \land h + a \leq h_0 + a_0 \Rightarrow (T \multimap[\varepsilon;h_0] U)^{a_0} \leadsto_{h,a} (T \multimap[\varepsilon;h_0] U)^{h - h_0}`, [A(R`h_0`, R`the floor of the captured closure`), A(R`a_0`, R`its credit`), A('h, a', R`the floor and credit of the capturing closure`)]);
sa('cap.agg', R`(T_1 \otimes T_2) \leadsto_{h,a} (T_1' \otimes T_2') \iff T_i \leadsto_{h,a} T_i'`, [A('h, a', R`the floor and credit of the capturing closure`)]);
sa('sub.tsub', R`T \leq T' \subseteq \mathsf{Ty} \times \mathsf{Ty}`, [A('T', R`the type a value has`), A(R`T'`, R`the type it is used at`)]);
sa('tp.sub-credit', R`a' \leq a`, [A('a', R`the credit of the end in the subtype`), A(R`a'`, R`the credit in the supertype`)]);
sa('tp.sub-floor', R`h \leq h' \land h' + a' \leq h + a`, [A('h, a', R`floor and credit of the arrow subtype`), A(R`h', a'`, R`floor and credit of the arrow supertype`)]);
sa('tp.sub-sess', R`S \simeq S'`, [A(R`S, S'`, R`session types at the same point $x$`)]);
sa('tp.sub-ex', R`\mathsf{facts}\,C' \subseteq \mathsf{facts}\,C`, [A('C', R`the constraint of the subtype existential`), A(R`C'`, R`the constraint of the supertype existential, over the same variables`)]);
sa('tp.sub-var', R`T_1' \leq T_1 \land U \leq U'`, [A(R`T_1, T_1'`, R`the argument types, compared contravariantly`), A(R`U, U'`, R`the result types, compared covariantly`)]);
sa('tp.sub-agg', R`T_1 \leq T_1' \land T_2 \leq T_2'`, [A(R`T_i, T_i'`, R`the components of the two products or sums`)]);
sa('tp.sub-teq', R`T \equiv T'`, [A(R`T, T'`, R`types of the same shape whose session types are pairwise $\simeq$`)]);
sa('E-Abs.phi', R`\varphi \notin \mathrm{dom}\,\Gamma`, [A(R`\varphi`, R`the future variable of the body`), aGa]);
sa('E-Abs.lb', R`l \preccurlyeq \Delta \iff \forall y \in \mathsf{heads}(\Delta).\ \Gamma \vdash l \preccurlyeq y`, [A('l', R`the lower point of the arrow`), A(R`\mathsf{heads}(\Delta)`, R`the partner points of every captured end, with $\bot$ for hidden ends`)]);
sa('E-Abs.cap', R`\Delta \leadsto_{h,a} \Delta^{h}`, [A('h', R`the floor of the arrow`), A('a', R`the credit of the closure`), A(R`\Delta^{h}`, R`the captured context restated at floor $h$`)]);
sa('E-Abs.body', R`\Gamma, u \prec \varphi ; \Delta^{h}, T \vdash^{(\varnothing, \varphi)} e : U\ !\ \varepsilon`, [A('T', R`the argument at index $0$`), A('U', R`the result of the body`), A(R`\varepsilon`, R`the effect recorded on the arrow`)]);
sa('E-App.ub', R`u \prec F`, [A('u', R`the upper point of the arrow type of $e_1$`), aF]);
sa('E-App.fut1', R`\Gamma ; \Delta_1 \parallel \Delta_2 \vdash^{F} e_1 : \ldots`, [A(R`\Delta_1`, R`the part of the context given to $e_1$`), A(R`\Delta_2`, R`the part held for the rest of the term`)]);
sa('E-App.fut2', R`\Gamma ; \Delta_2 - \varepsilon_1 \parallel (T \multimap^{u}_{l} U)^{a} \vdash^{F} e_2 : T\ !\ \varepsilon_2`, [A('l', R`the lower point of the closure, held while $e_2$ runs`), A('a', R`the credit of the closure, which bounds the cost of $e_2$`)]);
sa('E-Pair.fut2', R`\Gamma ; \Delta_2 - \varepsilon_1 \parallel T_1 \vdash^{F} e_2 : T_2\ !\ \varepsilon_2`, [A(R`T_1`, R`the type of the first component, held while $e_2$ runs`)]);
sa('tp.letp', R`\Gamma ; T_2, T_1, \Delta_2 - \varepsilon_1 \vdash^{F} e_2 : T\ !\ \varepsilon_2`, [A(R`T_1 \otimes T_2`, R`the type of $e_1$`)]);
sa('tp.letu', R`\Gamma ; \Delta_2 - \varepsilon_1 \vdash^{F} e_2 : T\ !\ \varepsilon_2`, [A(R`\Delta_2 - \varepsilon_1`, R`the context of $e_2$ aged by the cost of $e_1$`)]);
sa('E-Case.branches', R`\Gamma ; T_i, \Delta_2 - \varepsilon_0 \vdash^{F} e_i : T\ !\ \varepsilon_i`, [A('i', R`$1$ or $2$, the branch`), A(R`T_i`, R`the payload of injection $i$ at index $0$`)]);
sa('E-Box.unl', R`\Delta \text{ holds no end} \land \forall i.\ \Delta(i) = T \Rightarrow \mathsf{unlimited}\,T`, [aDe]);
sa('E-Box.inst', R`\forall \bar s.\ \mathsf{sinsts}\,\bar s \Rightarrow \ldots`, [A(R`\bar s`, R`a list of session types, one per session variable of the box`)]);
sa('E-Box.body', R`\Gamma, C(\bar\iota), u \prec \varphi ; \Delta, f \vdash^{(\varnothing, \varphi)} e : U[\bar s]\ !\ \varepsilon`, [A(R`\bar\iota`, R`the fresh point variables of the box`), A('f', R`the box itself at index $0$`), A(R`\varphi`, R`the future variable of the body`)]);
sa('E-Box.open', R`\Gamma, C(\bar\iota)`, [A(R`C(\bar\iota)`, R`the constraint at the fresh variables`)]);
sa('E-Box.self', R`f : \Box(\forall \bar\iota\,\bar\alpha.\ C.\ \ast \multimap^{u}[\varepsilon]\,U)`, [A('f', R`the variable at index $0$ bound to the box itself`)]);
sa('E-Force.hold', R`\Gamma \vdash C[\bar x]`, [A(R`\bar x`, R`the points the force or pack instantiates $\bar\iota$ with, one per variable`)]);
sa('E-Force.ub', R`u[\bar x] \prec F`, [A(R`u[\bar x]`, R`the upper point of the box at the instance $\bar x$`), aF]);
unf('E-Send.unfold', R`{!}(\bar\iota.\,T).S`);
unf('E-Recv.unfold', R`{?}(\bar\iota.\,T).S`);
unf('E-Close.unfold', R`\mathsf{Close}`);
unf('E-Select.unfold', R`\oplus(S_1, S_2)`);
unf('E-Branch.unfold', R`\&(S_1, S_2)`);
sa('E-Send.heads', R`x \prec T \iff \forall y \in \mathsf{heads}(T).\ \Gamma \vdash x \prec y`, [aX, A('T', R`a held value, in E-Send the payload $T[x\cdot i]$`), A('y', R`a partner point of an end in $T$, or $\bot$ for hidden ends, which no $x$ lies below`)]);
sa('E-Send.floor', R`T' - 1 \leq T[x\cdot i]`, [A(R`T'`, R`the type of the payload value`), A(R`T[x\cdot i]`, R`the payload type of the protocol at the fields of $x$`)]);
sa('E-Link.dual', R`\ldots \vdash e : (S@x)^{a_1} \otimes (\overline{S}@\overline{x})^{a_2}`, [A('S@x', R`the first linked end`), A(R`\overline{S}@\overline{x}`, R`the second, at the dual type and dual point`)]);
sa('E-SpawnLam.age', R`\Delta - 1`, [A(R`\Delta`, R`the context handed to the child`)]);
sa('E-SpawnLam.body', R`\Gamma ; \Delta\annot{ - 1}, \ast \vdash^{(\varnothing, \cdot)} e : \ast\annot{\ !\ (c', \vartheta')}`, [A(R`\ast`, R`the unit argument of the thunk`)]);
sa('E-SpawnLam.future', R`F = (\varnothing, \cdot)`, [A(R`(\varnothing, \cdot)`, R`the future with no point, no variable and no $\bot$`)]);
sa('E-Spawn.credit', R`a \geq 1`, [A('a', R`the credit of the closure value spawned`)]);
sa('E-New.bot', R`\exists^{\bot}`, [A(R`\bot`, R`the lower bound of the existential, no point of the context lies below its ends`)]);
sa('E-New.facts', R`C \subseteq \mathsf{Point} \times \mathsf{Point}`, [A('C', R`the facts of the creation, chosen by the derivation`)]);
sa('E-New.pos', R`\pi \in \mathsf{Point}`, [A(R`\rho`, R`the point variable bound by the existential`), A(R`x, \kappa`, R`a point of the context and a field label`)]);
sa('E-New.strict', R`\mathsf{strict}(\Gamma \cup C) : \mathsf{Prop}`, [A(R`\Gamma`, R`the fact context`), A('C', R`the facts of the creation`)]);
sa('E-New.dual', R`(S@\pi)^{N} \otimes (\overline{S}@\overline{\pi})^{N}`, [A('S', R`any session type, chosen by the derivation`), aN]);
sa('E-Sub.cost', R`\varepsilon \leq \varepsilon' \iff c \leq c' \land \vartheta \leq \vartheta'`, [A(R`\varepsilon = (c, \vartheta)`, R`the effect derived`), A(R`\varepsilon' = (c', \vartheta')`, R`the weaker one concluded`)]);
sa('E-Weak.drop', R`\Delta' \preceq_{\mathsf{wk}} \Delta`, [A(R`\Delta'`, R`the context of the premise`), A(R`\Delta`, R`the context of the conclusion, with additional unlimited entries`)]);
sa('E-Pack.lb', R`l = \bot \lor l \preccurlyeq T[\bar x]`, [A('l', R`the lower bound of the existential`), A(R`\bar x`, R`the witness points`)]);
sa('E-Open.entry', R`\Delta(i) = \exists^{l}\bar\iota.\,C.\,T \land \neg\mathsf{unlimited}\,T`, [A('i', R`the de Bruijn index of the opened variable`)]);
sa('E-Open.body', R`\Gamma, C(\bar\iota) ; \Delta[i \mapsto T] \vdash^{F} e : U\ !\ \varepsilon`, [A(R`\bar\iota`, R`the fresh point variables of the existential`), A('U', R`the result type, which mentions no $\bar\iota$`)]);
sa('pfree', R`\mathsf{pfree}\,\Sigma \iff \forall o \in \mathrm{dom}\,\Sigma.\ \overline{o} \notin \mathrm{dom}\,\Sigma`, [aSi]);
sa('P-Term.C0', R`\forall o.\ o \in \mathrm{dom}\,\Theta_B \iff \mathsf{ech}(o) \in C_0`, [A(R`\Theta_B`, R`the entries of the restricted ends`), A(R`C_0`, R`the restricted channels of the thread`)]);
sa('P-Term.disj', R`\mathsf{chans}\,\Sigma \cap C_0 = \varnothing`, [aSi, A(R`C_0`, R`the restricted channels`)]);
sa('P-Term.pairs', R`\forall c \in C_0.\ \exists S\,x.\ \Theta_B(c^{+}) = S@x^{N} \land \Theta_B(c^{-}) = \overline{S}@\overline{x}^{N}`, [A('c', R`a restricted channel`), A('S, x', R`the type and point of its positive end`)]);
sa('P-Term.typed', R`\varnothing ; \Sigma^{N}, \Theta_B \vdash^{(\varnothing,\cdot)}_{W,N} t : T\annot{\ !\ (c, \vartheta)}`, [A('t', R`the thread`), A(R`\Sigma^{N}`, R`the interface at credit $N$`)]);
sa('P-Term.future', R`F = (\varnothing, \cdot)`, [A('F', R`the future of a top-level thread`)]);
sa('lf.meets', R`N \in \mathbb{N} \Rightarrow \vartheta(0) \in \mathbb{N}`, [aN, A(R`\vartheta`, R`the ticket need of the thread, read at reserve $0$`)]);
sa('lf.N', R`N \in \mathbb{N}`, [aN]);
sa('P-Connect.left', R`\Sigma_1 \cup \Sigma_C \vdash^{N}_{W_1} (C_1, E_1) : T`, [A(R`\Sigma_1`, R`the interface kept outside`), A(R`\Sigma_C`, R`the cut, the ends connected to the right component`)]);
sa('P-Connect.right', R`\Sigma_2 \cup \overline{\Sigma_C} \vdash^{N}_{W_2} (C_2, E_2) : \ast`, [A(R`\Sigma_2`, R`the interface kept outside`), A(R`\overline{\Sigma_C}`, R`the partners of the cut`)]);
sa('P-Connect.cut', R`\overline{\Sigma_C} = \{\overline{o} \mapsto \overline{S}@\overline{x} \mid (o \mapsto S@x) \in \Sigma_C\}`, [A(R`\Sigma_C`, R`the cut`)]);
sa('P-Connect.disj', R`\mathsf{chans}\,\Sigma_1, \mathsf{chans}\,\Sigma_2, \mathsf{chans}\,\Sigma_C, C_1, C_2\ \text{pairwise disjoint}`, [A(R`C_1, C_2`, R`the restricted channels of the components`)]);
sa('P-Connect.cutfree', R`\mathsf{pfree}\,\Sigma_C`, [A(R`\Sigma_C`, R`the cut`)]);
sa('P-Connect.strict', R`\mathsf{strict}(W_1|_S \sqcup W_2|_S),\ S = A_{W_1} \cap A_{W_2}`, [A(R`A_{W}`, R`the roots of $W$`), A(R`W|_S`, R`the facts of $\prec_W$ between points with roots in $S$`)]);
sa('P-Term.strict', R`\mathsf{strict}\,W`, [A('W', R`the world of the thread`)]);
sa('P-Connect.join', R`W_1 \sqcup W_2`, [A(R`W_1, W_2`, R`the worlds of the components`)]);
sa('guard.judg', R`\Lambda \vdash\!\triangleright t \subseteq \mathsf{bool}^{*} \times \mathsf{Expr}`, [aLam, A('t', R`the term checked`)]);
sa('guard.marks', R`\Lambda : \mathsf{bool}^{*}`, [A(R`\Lambda(y)`, R`the mark of variable $y$, $\mathsf{true}$ for the self of an enclosing box not yet passed by an action`)]);
sa('guard.var', R`\Lambda(y) = \mathsf{false}`, [A('y', R`the variable used`), aLam]);
sa('guard.lam', R`\mathsf{false}.\Lambda \vdash\!\triangleright b`, [A('b', R`the body of the $\lambda$`), A(R`\mathsf{false}.\Lambda`, R`$\Lambda$ with the unmarked argument at index $0$`)]);
sa('guard.box', R`\mathsf{true}.\Lambda \vdash\!\triangleright b`, [A('b', R`the body of the box`), A(R`\mathsf{true}.\Lambda`, R`$\Lambda$ with the self at index $0$ marked`)]);
sa('guard.cong', R`\Lambda \vdash\!\triangleright e_1 \land \mathsf{kmarks}\,\Lambda\,\Lambda'\,e_1 \land \Lambda' \vdash\!\triangleright e_2`, [A(R`e_1, e_2`, R`the subterms of a frame`), aLam, A(R`\Lambda'`, R`the marks after $e_1$`)]);
sa('guard.tick', R`\mathsf{kmarks}\,\Lambda\,\Lambda'\,e \iff \Lambda' = \Lambda \lor (\Lambda' = \varnothing \land \mathsf{acts}\,e)`, [aLam, A(R`\Lambda'`, R`the marks for the rest`), A('e', R`the term that runs first`)]);
sa('guard.bind', R`\mathsf{false}.\mathsf{false}.\Lambda' \vdash\!\triangleright e_2`, [A(R`e_2`, R`the body, with the two bound variables unmarked`), A(R`\Lambda'`, R`the marks after the bound term`)]);
sa('guard.acts', R`\mathsf{acts} : \mathsf{Expr} \to \mathsf{Prop}`, [A('e', R`a term`), A('k', R`an operator, acting when $k \in \{\mathsf{send}, \mathsf{recv}, \mathsf{close}, \mathsf{select}_i, \mathsf{branch}\}$`)]);
sa('guard.proc', R`\vdash\!\triangleright p \iff \forall t \in E.\ \varnothing \vdash\!\triangleright t`, [aP, A('t', R`a thread of $p = (C, E)$`)]);
sa('tp.Sigma', R`\Sigma : \mathsf{End} \rightharpoonup_{\mathrm{fin}} \mathsf{Sty} \times \mathsf{Pt}`, [A('o', R`an end offered to the environment`), A(R`S@x`, R`its session type and point`)]);
sa('tp.pjudg', PJ, [aSi, aW, aN, aP, aPT]);
sa('tp.lfjudg', R`\Sigma \Vdash^{N}_{W} p : T \iff N \in \mathbb{N} \land \Sigma \vdash^{N}_{W} p : T \land \vdash\!\triangleright p`, [aSi, aW, aN, aP, aPT]);
sa('tp.chans', R`\mathsf{chans} : (\mathsf{End} \rightharpoonup X) \to \mathcal{P}(\mathsf{Chan})`, [A(R`\Sigma`, R`a finite map of ends`), A(R`\mathsf{chans}\,\Sigma`, R`$\{\mathsf{ech}(o) \mid o \in \mathrm{dom}\,\Sigma\}$`)]);
sa('tp.ends', R`\mathsf{ends} : \mathcal{P}(\mathsf{Chan}) \to \mathcal{P}(\mathsf{End})`, [A('C', R`a set of channels`)]);
sa('tp.lift', R`\Sigma^{N} : \mathsf{End} \rightharpoonup \mathsf{Sty} \times \mathsf{Pt} \times \mathsf{Fuel}`, [aSi, aN]);
sa('E-Box.fresh', R`\bar\iota \cap \mathsf{pvars}(\Gamma, \Delta, F, U) = \varnothing`, [A(R`\bar\iota`, R`the bound point variables`)]);
sa('tp.pinst', R`T[\bar x]`, [A('T', R`a type over the bound point variables $\bar\iota$`), A(R`\bar x`, R`the points substituted, $|\bar x| = |\bar\iota|$`)]);
sa('tp.sinst', R`U[\bar s]`, [A('U', R`a type over the session variables $\bar\alpha$`), A(R`\bar s`, R`the session types substituted`)]);
sa('tp.sinsts', R`\mathsf{sinsts} : \mathsf{Fuel} \to \mathsf{Sty}^{*} \to \mathsf{Prop}`, [aN, A(R`\bar s`, R`a list of session types`)]);
sa('tp.max', R`\max : \mathsf{Eff} \times \mathsf{Eff} \to \mathsf{Eff}`, [A(R`\varepsilon_1, \varepsilon_2`, R`the effects of the two branches`)]);
sa('tp.vdash', JG, JA);
sa('tp.msunion', R`\uplus : \mathcal{M}(\mathsf{Expr}) \times \mathcal{M}(\mathsf{Expr}) \to \mathcal{M}(\mathsf{Expr})`, [A(R`E_1, E_2`, R`the thread multisets of the two components`)]);
