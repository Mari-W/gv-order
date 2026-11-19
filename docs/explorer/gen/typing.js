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
  erase: 'proc.erase', 'lf\\_next': 'sp.next', sinsts: 'tp.sinsts', pscoped: 'ty.pscoped', hbot: 'ty.hbot',
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
  'This section introduces the typing judgment $\\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W,N} e : T^{a} \\triangleright c ; \\vartheta$, its contexts $\\Theta$, $\\Gamma$, $\\Delta$ and the future $F$, the side conditions on points, aging $\\Gamma - c$ and capture of credits, subtyping, one rule per term former, the process judgment $\\Sigma \\vdash^{N}_{W} p : T$ with the rules P-Term and P-Connect, the lock-free judgment $\\Sigma \\Vdash^{N}_{W} p : T$, and the guard $\\Lambda \\vdash\\!\\triangleright t$. Deadlock-free typing is the instance $N = \\infty$ with every annotation erased, live typing adds the guard, and lock-free typing takes $N \\in \\mathbb{N}$ and the guard.');

// judgment builders
const J = (Th, G, D, F, e, T, a, c, t) => R`${Th} ; ${G} ; ${D} \vdash^{${F}}_{W,N} ${e} : ${T}^{${a}} \triangleright ${c} ; ${t}`;
const DJ = (Th, G, D, F, e, T) => R`${Th} ; ${G} ; ${D} \vdash^{${F}}_{W} ${e} : ${T}`;
const act = h('side.act', R`x \prec F`);
const refill = (t) => R`(${t})^{${h('act.refill', 'N')}}`;

block(s, {
  id: 't-judgment', title: 'The merged judgment', rocq: 'static/Typing.v: typed, dftyped',
  tex: R`${h('tj.Theta', R`\Theta`)} ; ${h('tj.Gamma', R`\Gamma`)} ; ${h('tj.Delta', R`\Delta`)} \vdash^{${h('tj.F', 'F')}}_{${h('tj.W', 'W')},${h('tj.N', 'N')}} e : T^{${h('ty.credit', 'a')}} \triangleright ${h('tj.cost', 'c')} ; ${h('tj.tix', R`\vartheta`)}`,
  variants: {
    df: R`${h('tj.Theta', R`\Theta`)} ; ${h('tj.Gamma', R`\Gamma`)} ; ${h('tj.Delta', R`\Delta`)} \vdash^{${h('tj.F', 'F')}}_{${h('tj.W', 'W')}} t : T`,
  },
  caption: '$\\Theta$ maps ends, $\\Gamma$ holds facts, $\\Delta$ variables, $F$ is the future, $N$ the refill, $c$ the cost and $\\vartheta$ the ticket need.'
});
block(s, {
  id: 't-contexts', title: 'Contexts and the fact theory', rocq: 'static/Contexts.v: tentry, tsplit, lenv_split, hctx, fl, sfuture',
  tex: lrows(R`${h('tj.Theta', R`\Theta : o \mapsto S@x^{a}`)} \qquad ${h('ctx.tsplit', R`\Theta = \Theta_1 \uplus \Theta_2`)} \qquad ${h('ctx.lsplit', R`\Delta = \Delta_1 \sqcup \Delta_2`)}`, R`${h('tj.Gamma', R`\Gamma = (${h('ctx.hyps', R`(C, \bar x)^{*}`)}, ${h('ctx.fvar', R`\varphi \mapsto u`)})`)} \qquad ${h('ctx.slt', R`\Gamma \vdash x \prec y`)}`, R`${h('tj.F', R`F = (X, ${h('ctx.fvarF', R`\varphi`)} \mid ${h('ctx.bot', R`\bot`)})`)}`),
  caption: 'Every order fact a rule reads is a judgment $\\Gamma \\vdash x \\prec y$, the least transitive relation containing $\\prec_W$, the facts $C[\\bar x]$ of the instances in $\\Gamma$, and $u \\prec \\varphi$ for every $\\varphi \\mapsto u$ in $\\Gamma$.'
});
block(s, {
  id: 't-side', title: 'Side conditions on points', rocq: 'static/Contexts.v: ub_below_s, lbx_below_h, lbound_of, hold_at',
  tex: lrows(h('side.ub', R`u \prec F \iff \forall y \in X.\ \Gamma \vdash u \prec y,\ \Gamma \vdash u \prec \varphi,\ \neg\bot`), R`${h('side.lb', R`l \preccurlyeq H \text{ and } \neg\bot`)} \qquad ${h('side.hold', R`\Gamma \vdash C[\bar x]`)}`),
  caption: '$u \\prec F$ states that $u$ lies below every point of $F$, $l \\preccurlyeq H$ that $l$ lies at or below every point of $H$, and $\\Gamma \\vdash C[\\bar x]$ that every fact of $C$ at $\\bar x$ is derivable.'
});
block(s, {
  id: 't-age', title: 'Aging $\\Gamma - c$', rocq: 'static/Contexts.v: tage, lage, thage, types/Types.v: idle', modes: ['lf'],
  tex: rows(R`${rule('Age-Free', h('age.free', R`${h('ty.tfree', R`\mathsf{tfree}`)}\,T`), R`(T, a) - c = (T, a)`)} \qquad ${rule('Age-Credit', h('age.credit', R`c \leq a`), R`(T, a) - c = (T, a - c)`)}`, rule('Age-Idle', h('age.idle', R`${h('fu.idle', R`\mathsf{idle}`)}\,S`), R`(S@x, a) - c = (S@x, \max(a - c, 0))`), rule('Age-Agg', h('age.agg', R`(T_i, a + a_i) - c = (T_i', a_i')`), R`(T_1^{a_1} \otimes T_2^{a_2}, a) - c = (T_1'^{a_1'} \otimes T_2'^{a_2'}, 0)`)),
  caption: '$(T, a) - c$ lowers every credit by $c$, asks $c \\leq a$ of every end that is not idle, and keeps entries with $\\mathsf{tfree}\\,T$.'
});
block(s, {
  id: 't-cap', title: 'Capture at E-Abs', rocq: 'static/Contexts.v: tcap, thcap', modes: ['lf'],
  tex: rows(rule('Cap-Sess', h('cap.sess', R`h + a \leq a_0`), R`(S@x, a_0) \leadsto_{h,a} (S@x, h)`), rule('Cap-Arr', h('cap.arr', R`h_0 \leq h \quad h + a \leq h_0 + a_0`), R`(T \multimap[\ldots;h_0] U, a_0) \leadsto_{h,a} (\ldots, h - h_0)`)),
  caption: 'A captured end needs credit at least $h + a$, and the body sees it at credit $h$.'
});
const SUBC = h('tp.sub-credit', R`a' \leq a`);
const SUBK = (c, t) => h('tp.sub-cost', R`${c} \leq ${c}',\ ${t} \leq ${t}'`);
const SUBH = h('tp.sub-floor', R`h \leq h',\ h' + a' \leq h + a`);
const LE = (x, y) => h('sub.tsub', R`${x} \leq ${y}`);
const SUBLF = rows(
  R`${rule('Sub-Unit', SUBC, LE(R`\ast^{a}`, R`\ast^{a'}`))} \qquad ${rule('Sub-Sess', R`${h('tp.sub-sess', R`S ${h('sty.sequiv', R`\simeq`)} S'`)}${Q}${SUBC}`, LE(R`(S@x)^{a}`, R`(S'@x)^{a'}`))}`,
  rule('Sub-Arr', R`\begin{array}{c}${SUBK('c', R`\vartheta`)}${Q}${SUBH} \\ ${h('tp.sub-var', R`${LE(R`T_1'^{a_1'}`, R`T_1^{a_1}`)} \quad ${LE(R`U^{a_2}`, R`U'^{a_2'}`)}`)}\end{array}`,
    R`\begin{array}{c}(T_1^{a_1} \multimap^{u}_{l}[c;\vartheta;h]\,U^{a_2})^{a} \\ \leq (T_1'^{a_1'} \multimap^{u}_{l}[c';\vartheta';h']\,U'^{a_2'})^{a'}\end{array}`),
  rule('Sub-Prod, Sub-Sum', h('tp.sub-agg', R`T_i^{a + a_i} \leq T_i'^{a' + a_i'}\ \ (i = 1, 2)`), R`(T_1^{a_1} \otimes T_2^{a_2})^{a} \leq (T_1'^{a_1'} \otimes T_2'^{a_2'})^{a'}`),
  rule('Sub-Box', R`${SUBK('c', R`\vartheta`)}${Q}${h('tp.sub-teq', R`U \equiv U'`)}`, R`\Box(\forall \bar\iota\,\bar\alpha.\ C.\ \ast \multimap^{u}[c;\vartheta]\,U)^{a} \leq \Box(\ldots[c';\vartheta']\,U')^{a'}`),
  rule('Sub-Ex', R`${h('tp.sub-ex', R`\mathsf{facts}\,C' \subseteq \mathsf{facts}\,C`)}${Q}${h('tp.sub-teq', R`T \equiv T'`)}${Q}${h('tp.sub-credit', R`a' + a_T' \leq a + a_T`)}`, R`(\exists^{l}\bar\iota.\,C.\,T^{a_T})^{a} \leq (\exists^{l}\bar\iota.\,C'.\,T'^{a_T'})^{a'}`));
const SUBDF = rows(
  R`${rule('Sub-Sess', h('tp.sub-sess', R`S ${h('sty.seqv', R`\approx`)} S'`), LE(R`S@x`, R`S'@x`))} \qquad ${rule('Sub-Ex', R`${h('tp.sub-ex', R`\mathsf{facts}\,C' \subseteq \mathsf{facts}\,C`)}${Q}${h('tp.sub-teq', R`T \equiv T'`)}`, LE(R`\exists^{l}\bar\iota.\,C.\,T`, R`\exists^{l}\bar\iota.\,C'.\,T'`))}`,
  h('tp.sub-var', R`\text{componentwise on } \otimes, \oplus, \Box,\ \text{contravariant in the argument of } \multimap`),
  rule('D-Conv', h('sub.dconv', R`${h('ann.tydf', R`\mathsf{ty\_df}`)}\,T \leq \mathsf{ty\_df}\,T'`), R`t : T \Rightarrow t : T'`));
block(s, {
  id: 't-sub', title: 'Subtyping', rocq: 'static/Contexts.v: tsub, static/Typing.v: e_sub, d_conv',
  tex: SUBLF,
  variants: { df: SUBDF, live: SUBDF },
  caption: 'At annotations $\\infty$ subtyping is $\\approx$ on sessions plus dropping facts of $\\exists$, and at finite $N$ credits fall while costs, ticket needs and floors rise.'
});

// ---- term rules ----
const T = (id, title, rocq, merged, erased, caption) => block(s, { id, title, rocq, tex: merged, variants: { df: erased, live: erased }, caption });

T('r-unit', 'E-Unit', 'static/Typing.v: e_unit',
  rule('E-Unit', h('ctx.empty', R`\Delta\ \text{unlimited}`), J(R`\varnothing`, R`\Gamma`, R`\Delta`, 'F', R`\ast`, R`\ast`, h('ann.fuel', R`\infty`), '0', h('ann.tid', R`\hat 1`))),
  rule('D-Unit', h('ctx.empty', R`\Delta\ \text{unlimited}`), DJ(R`\varnothing`, R`\Gamma`, R`\Delta`, 'F', R`\ast`, R`\ast`)),
  '$\\ast$ holds no end, has cost $0$ and ticket need $\\hat 1$.');
T('r-var', 'E-Var', 'static/Typing.v: e_var',
  rule('E-Var', h('ctx.only', R`\Delta = \{x : T^{a}\}`), J(R`\varnothing`, R`\Gamma`, R`\Delta`, 'F', 'x', 'T', 'a', '0', R`\hat 1`)),
  rule('D-Var', h('ctx.only', R`\Delta = \{x : T\}`), DJ(R`\varnothing`, R`\Gamma`, R`\Delta`, 'F', 'x', 'T')),
  '$x$ is the only non-empty entry of $\\Delta$.');
T('r-chan', 'E-Chan', 'static/Typing.v: e_chan',
  rule('E-Chan', h('ctx.empty', R`\Delta\ \text{unlimited}`), J(R`\{o : S@x^{a}\}`, R`\Gamma`, R`\Delta`, 'F', 'o', R`(S@x)`, 'a', '0', R`\hat 1`)),
  rule('D-Chan', h('ctx.empty', R`\Delta\ \text{unlimited}`), DJ(R`\{o : S@x\}`, R`\Gamma`, R`\Delta`, 'F', 'o', R`S@x`)),
  'The value $o$ is typed with $\\Theta = \\{o \\mapsto S@x^{a}\\}$, exactly its own entry.');
T('r-abs', 'E-Abs', 'static/Typing.v: e_abs',
  rule('E-Abs', R`${h('E-Abs.phi', R`\varphi\ \text{fresh}`)}${Q}${h('E-Abs.lb', R`l \preccurlyeq \mathsf{heads}(\Theta, \Delta),\ \neg\bot_\Delta`)}${Q}${h('E-Abs.cap', R`\Theta \leadsto_{h,a} \Theta^{h},\ \Delta \leadsto_{h,a} \Delta^{h}`)}${Q}${h('E-Abs.body', J(R`\Theta^{h}`, R`\Gamma, u \prec \varphi`, R`\Delta^{h}, T^{a_T}`, R`(\varnothing, \varphi)`, 'e', 'U', R`a_U`, 'c', R`\vartheta`))}`,
    J(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', R`\lambda e`, R`(T^{a_T} \multimap^{u}_{l}[c;\vartheta;h]\, U^{a_U})`, 'a', '0', R`\hat 1`)),
  rule('D-Abs', R`${h('E-Abs.phi', R`\varphi\ \text{fresh}`)}${Q}${h('E-Abs.lb', R`l \preccurlyeq \mathsf{heads}(\Theta, \Delta),\ \neg\bot_\Delta`)}${Q}${h('E-Abs.body', DJ(R`\Theta`, R`\Gamma, u \prec \varphi`, R`\Delta, T`, R`(\varnothing,\varphi)`, 'e', 'U'))}`,
    DJ(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', R`\lambda e`, R`T \multimap^{u}_{l} U`)),
  'The body runs under a fresh $\\varphi$ with $u \\prec \\varphi$ and captures $\\Theta$ and $\\Delta$ with $l \\preccurlyeq \\mathsf{heads}(\\Theta, \\Delta)$.');
T('r-app', 'E-App', 'static/Typing.v: e_app',
  rule('E-App', R`\begin{array}{c}${h('ctx.tsplit', R`\Theta = \Theta_1 \uplus \Theta_2`)}${Q}${h('ctx.lsplit', R`\Delta = \Delta_1 \sqcup \Delta_2`)}${Q}${h('E-App.ub', R`u \prec F`)} \\ ${h('E-App.fut1', J(R`\Theta_1`, R`\Gamma`, R`\Delta_1`, R`F \cup ${h('ty.heads', R`\mathsf{heads}`)}(\Theta_2,\Delta_2)`, R`e_1`, R`(T^{a_T} \multimap^{u}_{l}[c;\vartheta;h]\,U^{a_U})`, R`a_1`, R`c_1`, R`\vartheta_1`))} \\ ${h('age.ctx', R`\Theta_2' = \Theta_2 - c_1,\ \Delta_2' = \Delta_2 - c_1`)}${Q}${h('E-App.fut2', J(R`\Theta_2'`, R`\Gamma`, R`\Delta_2'`, R`F \cup \{l\}`, R`e_2`, 'T', R`a_T`, R`c_2`, R`\vartheta_2`))} \\ ${h('E-App.credit', R`c_2 \leq a_1`)}${Q}${h('ann.tok', R`\mathsf{tok}`)}\end{array}`,
    J(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', R`e_1\,e_2`, 'U', R`a_U`, h('E-App.cost', R`c_1 + c_2 + c`), R`\vartheta_1 \circ \vartheta_2 \circ \vartheta`)),
  rule('D-App', R`\begin{array}{c}${h('ctx.tsplit', R`\Theta = \Theta_1 \uplus \Theta_2`)}${Q}${h('ctx.lsplit', R`\Delta = \Delta_1 \sqcup \Delta_2`)}${Q}${h('E-App.ub', R`u \prec F`)} \\ ${h('E-App.fut1', DJ(R`\Theta_1`, R`\Gamma`, R`\Delta_1`, R`F \cup ${h('ty.heads', R`\mathsf{heads}`)}(\Theta_2,\Delta_2)`, R`e_1`, R`T \multimap^{u}_{l} U`))}${Q}${h('E-App.fut2', DJ(R`\Theta_2`, R`\Gamma`, R`\Delta_2`, R`F \cup \{l\}`, R`e_2`, 'T'))}\end{array}`,
    DJ(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', R`e_1\,e_2`, 'U')),
  '$e_1$ runs while $\\Theta_2$ and $\\Delta_2$ are held, $e_2$ runs while the closure is held, and the body runs under $F$ with $u \\prec F$.');
T('r-pair', 'E-Pair', 'static/Typing.v: e_pair',
  rule('E-Pair', R`\begin{array}{c}${h('ctx.tsplit', R`\Theta = \Theta_1 \uplus \Theta_2`)}${Q}${h('E-App.fut1', J(R`\Theta_1`, R`\Gamma`, R`\Delta_1`, R`F \cup ${h('ty.heads', R`\mathsf{heads}`)}(\Theta_2,\Delta_2)`, R`e_1`, R`T_1`, R`a_1`, R`c_1`, R`\vartheta_1`))} \\ ${h('age.ctx', R`\Theta_2 - c_1,\ \Delta_2 - c_1`)}${Q}${h('E-Pair.fut2', J(R`\Theta_2'`, R`\Gamma`, R`\Delta_2'`, R`F \cup \mathsf{heads}(T_1)`, R`e_2`, R`T_2`, R`a_2`, R`c_2`, R`\vartheta_2`))}${Q}${h('E-Pair.age1', R`(T_1, a_1) - c_2 = (T_1', a_1')`)}\end{array}`,
    J(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', R`\langle e_1, e_2\rangle`, R`(T_1'^{a_1'} \otimes T_2^{a_2})`, '0', R`c_1 + c_2`, R`\vartheta_1 \circ \vartheta_2`)),
  rule('D-Pair', R`${h('ctx.tsplit', R`\Theta = \Theta_1 \uplus \Theta_2`)}${Q}${h('E-App.fut1', DJ(R`\Theta_1`, R`\Gamma`, R`\Delta_1`, R`F \cup ${h('ty.heads', R`\mathsf{heads}`)}(\Theta_2,\Delta_2)`, R`e_1`, R`T_1`))}${Q}${h('E-Pair.fut2', DJ(R`\Theta_2`, R`\Gamma`, R`\Delta_2`, R`F \cup \mathsf{heads}(T_1)`, R`e_2`, R`T_2`))}`,
    DJ(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', R`\langle e_1, e_2\rangle`, R`T_1 \otimes T_2`)),
  'The value of $e_1$ is held while $e_2$ runs, so $e_2$ runs under $F \\cup \\mathsf{heads}(T_1)$ and $T_1$ ages by $c_2$.');
T('r-let', 'E-LetP, E-LetU', 'static/Typing.v: e_letp, e_letu',
  rows(rule('E-LetP', R`${h('E-App.fut1', J(R`\Theta_1`, R`\Gamma`, R`\Delta_1`, R`F \cup ${h('ty.heads', R`\mathsf{heads}`)}(\Theta_2,\Delta_2)`, R`e_1`, R`(T_1^{a_1} \otimes T_2^{a_2})`, 'a', R`c_1`, R`\vartheta_1`))}${Q}${h('age.ctx', R`\Theta_2' = \Theta_2 - c_1,\ \Delta_2' = \Delta_2 - c_1`)}${Q}${h('tp.letp', J(R`\Theta_2'`, R`\Gamma`, R`T_2^{a+a_2}, T_1^{a+a_1}, \Delta_2'`, 'F', R`e_2`, 'T', R`a_T`, R`c_2`, R`\vartheta_2`))}`,
    J(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', R`\mathsf{let}\ \langle a, b\rangle = e_1\ \mathsf{in}\ e_2`, 'T', R`a_T`, R`c_1 + c_2`, R`\vartheta_1 \circ \vartheta_2`)),
    rule('E-LetU', R`${h('E-App.fut1', J(R`\Theta_1`, R`\Gamma`, R`\Delta_1`, R`F \cup \mathsf{heads}(\Theta_2,\Delta_2)`, R`e_1`, R`\ast`, 'a', R`c_1`, R`\vartheta_1`))}${Q}${h('age.ctx', R`\Theta_2' = \Theta_2 - c_1,\ \Delta_2' = \Delta_2 - c_1`)}${Q}${h('tp.letu', J(R`\Theta_2'`, R`\Gamma`, R`\Delta_2'`, 'F', R`e_2`, 'T', R`a_T`, R`c_2`, R`\vartheta_2`))}`,
    J(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', R`\mathsf{let}\ \ast = e_1\ \mathsf{in}\ e_2`, 'T', R`a_T`, R`c_1 + c_2`, R`\vartheta_1 \circ \vartheta_2`))),
  rows(rule('D-LetP', R`${h('E-App.fut1', DJ(R`\Theta_1`, R`\Gamma`, R`\Delta_1`, R`F \cup ${h('ty.heads', R`\mathsf{heads}`)}(\Theta_2,\Delta_2)`, R`e_1`, R`T_1 \otimes T_2`))}${Q}${h('tp.letp', DJ(R`\Theta_2`, R`\Gamma`, R`T_2, T_1, \Delta_2`, 'F', R`e_2`, 'T'))}`,
    DJ(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', R`\mathsf{let}\ \langle a, b\rangle = e_1\ \mathsf{in}\ e_2`, 'T')),
    rule('D-LetU', R`${h('E-App.fut1', DJ(R`\Theta_1`, R`\Gamma`, R`\Delta_1`, R`F \cup \mathsf{heads}(\Theta_2,\Delta_2)`, R`e_1`, R`\ast`))}${Q}${h('tp.letu', DJ(R`\Theta_2`, R`\Gamma`, R`\Delta_2`, 'F', R`e_2`, 'T'))}`,
    DJ(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', R`\mathsf{let}\ \ast = e_1\ \mathsf{in}\ e_2`, 'T'))),
  '$\\mathsf{let}\\ x = e_1\\ \\mathsf{in}\\ e_2$ abbreviates a pair elimination followed by a unit elimination and types by E-LetP, E-Pair and E-LetU.');
T('r-case', 'E-Inj, E-Case', 'static/Typing.v: e_inj, e_case',
  rows(rule('E-Inj', J(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', 'e', R`T_i`, R`a_i`, 'c', R`\vartheta`), J(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', h('syn.inj', R`\mathsf{inj}_i\,e`), R`(T_1^{a_1} \oplus T_2^{a_2})`, '0', 'c', R`\vartheta`)), rule('E-Case', R`${h('E-App.fut1', J(R`\Theta_1`, R`\Gamma`, R`\Delta_1`, R`F \cup ${h('ty.heads', R`\mathsf{heads}`)}(\Theta_2,\Delta_2)`, 'e', R`(T_1^{a_1} \oplus T_2^{a_2})`, 'a', R`c_0`, R`\vartheta_0`))}${Q}${h('E-Case.branches', R`\Theta_2' ; \Gamma ; T_i^{a+a_i}, \Delta_2' \vdash^{F} e_i : T^{a_T} \triangleright c_i ; \vartheta_i`)}`,
    J(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', R`\mathsf{case}\ e\,(e_1)\,(e_2)`, 'T', R`a_T`, R`c_0 + \max(c_1,c_2)`, R`\vartheta_0 \circ ${h('tp.max', R`\max`)}(\vartheta_1,\vartheta_2)`))),
  rows(rule('D-Inj', DJ(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', 'e', R`T_i`), DJ(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', h('syn.inj', R`\mathsf{inj}_i\,e`), R`T_1 \oplus T_2`)), rule('D-Case', R`${h('E-App.fut1', DJ(R`\Theta_1`, R`\Gamma`, R`\Delta_1`, R`F \cup ${h('ty.heads', R`\mathsf{heads}`)}(\Theta_2,\Delta_2)`, 'e', R`T_1 \oplus T_2`))}${Q}${h('E-Case.branches', R`\Theta_2 ; \Gamma ; T_i, \Delta_2 \vdash^{F} e_i : T`)}`,
    DJ(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', R`\mathsf{case}\ e\,(e_1)\,(e_2)`, 'T'))),
  'An injection keeps the context, cost and ticket need of its argument. Both branches of a case type under one context at one result, at cost $\\max(c_1, c_2)$.');
T('r-box', 'E-Box', 'static/Typing.v: e_box',
  rule('E-Box', R`${h('E-Box.unl', R`\Delta\ \text{unlimited}`)}${Q}${h('E-Abs.phi', R`\varphi\ \text{fresh}`)}${Q}${h('E-Box.inst', R`\forall \bar s.\ |\bar s| = k,\ ${h('tp.sinsts', R`\mathsf{sinsts}`)}\,N\,\bar s`)}${Q}${h('E-Box.body', J(R`\varnothing`, h('E-Box.open', R`\Gamma${h('tp.shift', R`{\uparrow^m}`)}, C(\bar\iota), u \prec \varphi`), h('E-Box.self', R`\Delta{\uparrow^m}, f : \Box(\ldots)^{\infty}`), R`(\varnothing,\varphi)`, 'e', h('tp.sinst', R`U[\bar s]`), R`a_U`, 'c', R`\vartheta`))}`,
    J(R`\varnothing`, R`\Gamma`, R`\Delta`, 'F', R`!e`, R`\Box(\forall \bar\iota\,\bar\alpha.\ C.\ \ast \multimap^{u}[c;\vartheta]\,U^{a_U})`, R`\infty`, '0', R`\hat 1`)),
  rule('D-Box', R`${h('E-Box.unl', R`\Delta\ \text{unlimited}`)}${Q}${h('E-Abs.phi', R`\varphi\ \text{fresh}`)}${Q}${h('E-Box.inst', R`\forall \bar s\ (N = \infty\ \text{instances})`)}${Q}${h('E-Box.body', DJ(R`\varnothing`, h('E-Box.open', R`\Gamma${h('tp.shift', R`{\uparrow^m}`)}, C(\bar\iota), u \prec \varphi`), h('E-Box.self', R`\Delta{\uparrow^m}, f : \Box(\ldots)`), R`(\varnothing,\varphi)`, 'e', R`U[\bar s]`))}`,
    DJ(R`\varnothing`, R`\Gamma`, R`\Delta`, 'F', R`!e`, R`\Box(\forall \bar\iota\,\bar\alpha.\ C.\ \ast \multimap^{u} U)`)),
  'The body is typed with $\\Theta = \\varnothing$ under $m$ fresh point variables $\\bar\\iota$, the hypothesis $C(\\bar\\iota)$, the box itself at index $0$, and a fresh future variable.');
T('r-force', 'E-Force', 'static/Typing.v: e_force',
  rule('E-Force', R`${h('E-Force.hold', R`|\bar x| = m,\ \Gamma \vdash C[\bar x]`)}${Q}${h('E-Box.inst', R`|\bar s| = k,\ \mathsf{sinsts}\,N\,\bar s`)}${Q}${h('E-Force.ub', R`u[\bar x] \prec F`)}${Q}${J(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', 'e', R`\Box(\forall\bar\iota\,\bar\alpha.\ C.\ \ast\multimap^{u}[c;\vartheta]\,U^{a_U})`, 'a', R`c_0`, R`\vartheta_0`)}`,
    J(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', R`\mathsf{force}\,e`, R`${h('tp.sinst', R`U[\bar s]`)}${h('tp.pinst', R`[\bar x]`)}`, R`a_U`, R`c_0 + c`, R`\vartheta_0 \circ \vartheta`)),
  rule('D-Force', R`${h('E-Force.hold', R`\Gamma \vdash C[\bar x]`)}${Q}${h('E-Force.ub', R`u[\bar x] \prec F`)}${Q}${DJ(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', 'e', R`\Box(\forall\bar\iota\,\bar\alpha.\ C.\ \ast\multimap^{u} U)`)}`,
    DJ(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', R`\mathsf{force}\,e`, R`U[\bar s][\bar x]`)),
  'Forcing chooses $\\bar x$ with $\\Gamma \\vdash C[\\bar x]$ and session types $\\bar s$, and asks $u[\\bar x] \\prec F$.');
block(s, {
  id: 't-consts', title: 'Types of constants', rocq: 'static/Typing.v: e_send, e_recv, e_close, e_select, e_branch, e_link, e_spawn, e_force, e_new',
  tex: R`\begin{array}{lll}
\mathsf{send} & : T[x\cdot i] \otimes S_0@x \multimap^{x} S@${h('pt.shift', R`x^{+}`)} & ${h('E-Send.unfold', R`${h('sty.unfold', R`\mathsf{unfold}`)}(S_0) = {!}(\bar\iota.\,T).S`)},\ \mathsf{pscoped}\,\bar\iota\,T,\ \neg\mathsf{hbot}\,T,\ ${h('E-Send.heads', R`x \prec \mathsf{heads}(T[x\cdot i])`)} \\
\mathsf{recv} & : S_0@x \multimap^{x} T[x\cdot i] \otimes S@x^{+} & ${h('E-Recv.unfold', R`${h('sty.unfold', R`\mathsf{unfold}`)}(S_0) = {?}(\bar\iota.\,T).S`)},\ \mathsf{pscoped}\,\bar\iota\,T \\
\mathsf{close} & : S_0@x \multimap^{x} \ast & ${h('E-Close.unfold', R`${h('sty.unfold', R`\mathsf{unfold}`)}(S_0) = \mathsf{Close}`)} \\
\mathsf{select}_i & : S_0@x \multimap^{x} S_i@${h('pt.sel', R`\overline{x\cdot\kappa_i}`)} & ${h('E-Select.unfold', R`${h('sty.unfold', R`\mathsf{unfold}`)}(S_0) = \oplus(S_1,S_2)`)} \\
\mathsf{branch} & : S_0@x \multimap^{x} S_1@${h('pt.bra', R`x\cdot\kappa_1`)} \oplus S_2@x\cdot\kappa_2 & ${h('E-Branch.unfold', R`${h('sty.unfold', R`\mathsf{unfold}`)}(S_0) = \&(S_1,S_2)`)} \\
\mathsf{link} & : ${h('E-Link.dual', R`S@x \otimes \overline{S}@\overline{x}`)} \multimap \ast & \\
\mathsf{spawn} & : (\ast \multimap^{u}_{l} \ast) \multimap \ast & \\
\mathsf{force} & : \Box(\forall\bar\iota\,\bar\alpha.\ C.\ \ast\multimap^{u} U) \multimap^{u[\bar x]} U[\bar s][\bar x] & ${h('E-Force.hold', R`\Gamma \vdash C[\bar x]`)} \\
\mathsf{new} & : \exists^{\bot}\bar\iota.\ ${h('E-New.facts', 'C')}.\ (S@\pi \otimes \overline{S}@\overline{\pi}) & ${h('E-New.pos', R`(\bar\iota, \pi) \in \{(\rho, \rho)\} \cup \{(\varepsilon, x\cdot\kappa)\}`)},\ ${h('E-New.strict', R`\mathsf{strict}(\Gamma \cup C)`)}
\end{array}`,
  caption: 'Each constant has the type of its eta-expansion $\\lambda y.\\,k\\,y$, for every instance of its variables that meets the conditions on the right, shown without credits, cost and ticket need. An action on $x$ has upper point $x$, so it runs only below the future of its caller. $\\mathsf{new}$ is a term and has the type of E-New.'
});
T('r-send', 'E-Send', 'static/Typing.v: e_send',
  rule('E-Send', R`\begin{array}{c}${h('E-Send.unfold', R`${h('sty.unfold', R`\mathsf{unfold}`)}(S_0) = {!}(\bar\iota.\,T).S`)}${Q}${h('ty.pscoped', R`\mathsf{pscoped}\,\bar\iota\,T`)}${Q}${h('E-Send.nobot', R`\neg${h('ty.hbot', R`\mathsf{hbot}`)}\,T`)} \\ ${h('E-Send.heads', R`\forall y \in \mathsf{heads}(${h('ty.payload-at', R`T[x\cdot i]`)}).\ \Gamma \vdash x \prec y`)}${Q}${act}${Q}${J(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', 'e', R`(T[x\cdot i]^{a_p} \otimes (S_0@x)^{a_S})`, R`a_0`, R`c_0`, R`\vartheta_0`)} \\ ${h('E-Send.floor', R`(T[x\cdot i], a_0 + a_p) - 1 \leq T[x\cdot i]^{b}`)}\end{array}`,
    J(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', R`\mathsf{send}\,e`, R`(S@${h('pt.shift', R`x^{+}`)})`, h('act.refill', 'N'), R`c_0 + 1`, R`\vartheta_0`)),
  rule('D-Send', R`${h('E-Send.unfold', R`${h('sty.unfold', R`\mathsf{unfold}`)}(S_0) = {!}(\bar\iota.\,T).S`)}${Q}${h('ty.pscoped', R`\mathsf{pscoped}\,\bar\iota\,T`)}${Q}${h('E-Send.nobot', R`\neg${h('ty.hbot', R`\mathsf{hbot}`)}\,T`)}${Q}${h('E-Send.heads', R`x \prec \mathsf{heads}(T[x\cdot i])`)}${Q}${act}${Q}${DJ(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', 'e', R`T[x\cdot i] \otimes S_0@x`)}`,
    DJ(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', R`\mathsf{send}\,e`, R`S@${h('pt.shift', R`x^{+}`)}`)),
  'The sender holds the payload while it waits at $x$, so $x \\prec \\mathsf{heads}$ of the payload, and the end returns at $x^{+}$ with credit $N$.');
T('r-recv', 'E-Recv', 'static/Typing.v: e_recv',
  rule('E-Recv', R`${h('E-Recv.unfold', R`${h('sty.unfold', R`\mathsf{unfold}`)}(S_0) = {?}(\bar\iota.\,T).S`)}${Q}${h('ty.pscoped', R`\mathsf{pscoped}\,\bar\iota\,T`)}${Q}${act}${Q}${J(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', 'e', R`(S_0@x)`, 'a', R`c_0`, R`\vartheta_0`)}`,
    J(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', R`\mathsf{recv}\,e`, R`(T[x\cdot i] \otimes ${refill(R`S@${h('pt.shift', R`x^{+}`)}`)})`, '0', R`c_0 + 1`, R`\vartheta_0`)),
  rule('D-Recv', R`${h('E-Recv.unfold', R`${h('sty.unfold', R`\mathsf{unfold}`)}(S_0) = {?}(\bar\iota.\,T).S`)}${Q}${h('ty.pscoped', R`\mathsf{pscoped}\,\bar\iota\,T`)}${Q}${act}${Q}${DJ(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', 'e', R`S_0@x`)}`,
    DJ(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', R`\mathsf{recv}\,e`, R`T[x\cdot i] \otimes S@${h('pt.shift', R`x^{+}`)}`)),
  'The payload arrives at credit $b$ with its ends at $x \\cdot i$, and the end returns at $x^{+}$ with credit $N$.');
T('r-close', 'E-Close', 'static/Typing.v: e_close',
  rule('E-Close', R`${h('E-Close.unfold', R`${h('sty.unfold', R`\mathsf{unfold}`)}(S_0) = \mathsf{Close}`)}${Q}${act}${Q}${J(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', 'e', R`(S_0@x)`, 'a', R`c_0`, R`\vartheta_0`)}`,
    J(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', R`\mathsf{close}\,e`, R`\ast`, R`\infty`, R`c_0 + 1`, R`\vartheta_0`)),
  rule('D-Close', R`${h('E-Close.unfold', R`${h('sty.unfold', R`\mathsf{unfold}`)}(S_0) = \mathsf{Close}`)}${Q}${act}${Q}${DJ(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', 'e', R`S_0@x`)}`,
    DJ(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', R`\mathsf{close}\,e`, R`\ast`)),
  'A close is an action at $x$ of cost $1$.');
T('r-select', 'E-Select', 'static/Typing.v: e_select',
  rule('E-Select', R`${h('E-Select.unfold', R`${h('sty.unfold', R`\mathsf{unfold}`)}(S_0) = \oplus(S_1,S_2)`)}${Q}${act}${Q}${J(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', 'e', R`(S_0@x)`, 'a', R`c_0`, R`\vartheta_0`)}`,
    J(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', R`\mathsf{select}_i\,e`, R`(S_i@${h('pt.sel', R`\overline{x\cdot\kappa_i}`)})`, h('act.refill', 'N'), R`c_0 + 1`, R`\vartheta_0`)),
  rule('D-Select', R`${h('E-Select.unfold', R`${h('sty.unfold', R`\mathsf{unfold}`)}(S_0) = \oplus(S_1,S_2)`)}${Q}${act}${Q}${DJ(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', 'e', R`S_0@x`)}`,
    DJ(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', R`\mathsf{select}_i\,e`, R`S_i@${h('pt.sel', R`\overline{x\cdot\kappa_i}`)}`)),
  'The selecting end continues at $\\overline{x\\cdot\\kappa_i}$, and the rule asks $\\Gamma \\vdash x \\prec x\\cdot\\kappa_i$.');
T('r-branch', 'E-Branch', 'static/Typing.v: e_branch',
  rule('E-Branch', R`${h('E-Branch.unfold', R`${h('sty.unfold', R`\mathsf{unfold}`)}(S_0) = \&(S_1,S_2)`)}${Q}${act}${Q}${J(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', 'e', R`(S_0@x)`, 'a', R`c_0`, R`\vartheta_0`)}`,
    J(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', R`\mathsf{branch}\,e`, R`((S_1@${h('pt.bra', R`x\cdot\kappa_1`)})^{N} \oplus (S_2@x\cdot\kappa_2)^{N})`, '0', R`c_0 + 1`, R`\vartheta_0`)),
  rule('D-Branch', R`${h('E-Branch.unfold', R`${h('sty.unfold', R`\mathsf{unfold}`)}(S_0) = \&(S_1,S_2)`)}${Q}${act}${Q}${DJ(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', 'e', R`S_0@x`)}`,
    DJ(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', R`\mathsf{branch}\,e`, R`S_1@${h('pt.bra', R`x\cdot\kappa_1`)} \oplus S_2@x\cdot\kappa_2`)),
  'The branching end continues at $x\\cdot\\kappa_i$, and the rule asks $\\Gamma \\vdash x \\prec \\overline{x\\cdot\\kappa_i}$ for both $i$.');
T('r-link', 'E-Link', 'static/Typing.v: e_link',
  rule('E-Link', R`${h('E-Link.dual', J(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', 'e', R`((S@x)^{a_1} \otimes (\overline{S}@\overline{x})^{a_2})`, R`a_0`, R`c_0`, R`\vartheta_0`))}${Q}${h('ann.tok', R`\mathsf{tok}`)}`,
    J(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', R`\mathsf{link}\,e`, R`\ast`, R`\infty`, R`c_0`, R`\vartheta_0 \circ ${h('ann.tlink', R`\mathsf{tlink}\,\hat 1`)}`)),
  rule('D-Link', h('E-Link.dual', DJ(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', 'e', R`S@x \otimes \overline{S}@\overline{x}`)),
    DJ(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', R`\mathsf{link}\,e`, R`\ast`)),
  'A link asks no order fact, costs $0$ and spends one ticket.');
T('r-spawnlam', 'E-SpawnLam', 'static/Typing.v: e_spawn_lam',
  rule('E-SpawnLam', R`${h('E-SpawnLam.age', R`\Theta' = \Theta - 1,\ \Delta' = \Delta - 1`)}${Q}${h('E-SpawnLam.body', J(R`\Theta'`, R`\Gamma`, R`\ast^{a_1}, \Delta'`, h('E-SpawnLam.future', R`(\varnothing, \cdot)`), 'e', R`\ast`, R`a_U`, R`c'`, R`\vartheta'`))}`,
    J(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', R`\mathsf{spawn}\,(\lambda e)`, R`\ast`, R`\infty`, '0', h('ann.tspawn', R`\mathsf{tspawn}(\vartheta'(0))\,\hat 1`))),
  rule('D-SpawnLam', h('E-SpawnLam.body', DJ(R`\Theta`, R`\Gamma`, R`\ast, \Delta`, h('E-SpawnLam.future', R`(\varnothing, \cdot)`), 'e', R`\ast`)),
    DJ(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', R`\mathsf{spawn}\,(\lambda e)`, R`\ast`)),
  'The child body runs under the empty future, and every handed entry ages by $1$.');
T('r-spawn', 'E-Spawn', 'static/Typing.v: e_spawn',
  rule('E-Spawn', R`${J(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', 'e', R`(\ast^{a_1} \multimap^{u}_{l}[c';\vartheta';h]\,\ast^{a_U})`, 'a', R`c_0`, R`\vartheta_0`)}${Q}${h('E-Spawn.credit', R`a \geq 1`)}${Q}${h('ann.tok', R`\mathsf{tok}`)}`,
    J(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', R`\mathsf{spawn}\,e`, R`\ast`, R`\infty`, R`c_0`, R`\vartheta_0 \circ ${h('ann.tspawn', R`\mathsf{tspawn}(\vartheta'(0))\,\hat 1`)}`)),
  rule('D-Spawn', DJ(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', 'e', R`\ast \multimap^{u}_{l} \ast`), DJ(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', R`\mathsf{spawn}\,e`, R`\ast`)),
  'Spawning a closure value hands over its captured ends and asks its credit $a \\geq 1$.');
T('r-new', 'E-New', 'static/Typing.v: e_new',
  rule('E-New', R`${h('ctx.empty', R`\Delta\ \text{unlimited}`)}${Q}${h('E-New.pos', R`(\bar\iota, \pi) \in \{(\rho, \rho)\} \cup \{(\varepsilon, x\cdot\kappa)\}`)}${Q}${h('E-New.strict', R`${h('w.strict', R`\mathsf{strict}`)}(\Gamma \cup C)`)}`,
    J(R`\varnothing`, R`\Gamma`, R`\Delta`, 'F', R`\mathsf{new}`, R`(\exists^{${h('E-New.bot', R`\bot`)}}\bar\iota.\ ${h('E-New.facts', 'C')}.\ ${h('E-New.dual', R`((S@\pi)^{N} \otimes (${h('sty.dual', R`\overline{S}`)}@\overline{\pi})^{N})`)}^{0})`, '0', '0', R`\hat 1`)),
  rule('D-New', R`${h('ctx.empty', R`\Delta\ \text{unlimited}`)}${Q}${h('E-New.pos', R`(\bar\iota, \pi) \in \{(\rho, \rho)\} \cup \{(\varepsilon, x\cdot\kappa)\}`)}${Q}${h('E-New.strict', R`${h('w.strict', R`\mathsf{strict}`)}(\Gamma \cup C)`)}`,
    DJ(R`\varnothing`, R`\Gamma`, R`\Delta`, 'F', R`\mathsf{new}`, R`\exists^{${h('E-New.bot', R`\bot`)}}\bar\iota.\ ${h('E-New.facts', 'C')}.\ ${h('E-New.dual', R`S@\pi \otimes \overline{S}@\overline{\pi}`)}`)),
  'The pair sits at a fresh root $\\rho$ or at a field $x\\cdot\\kappa$, with facts $C$ that keep the order strict and lower bound $\\bot$.');
T('r-struct', 'E-Sub', 'static/Typing.v: e_sub',
  rule('E-Sub', R`e : T^{a} \triangleright c ; \vartheta${Q}${h('sub.tsub', R`T^{a} \leq T'^{a'}`)}${Q}${h('E-Sub.cost', R`c \leq c',\ \vartheta \leq \vartheta'`)}`, R`e : T'^{a'} \triangleright c' ; \vartheta'`),
  rule('D-Conv', h('sub.dconv', R`${h('ann.tydf', R`\mathsf{ty\_df}`)}\,T \leq \mathsf{ty\_df}\,T'`), R`t : T \Rightarrow t : T'`),
  'A type may lose credit and a cost or ticket need may rise.');
T('r-admis', 'E-Weak, E-Contract (admissible)', 'static/Weakening.v: e_weak, e_contract, d_weak, d_contract, typed_rename',
  rows(rule('E-Weak', h('E-Weak.drop', R`\Delta' \preceq_{\mathsf{wk}} \Delta`), R`\Delta' \vdash e \Rightarrow \Delta \vdash e`), rule('E-Contract', h('ty.unlimited', R`\mathsf{unlimited}\,U`), R`U, U, \Delta \vdash e \Rightarrow U, \Delta \vdash e[x/x']`)),
  rows(rule('D-Weak', h('E-Weak.drop', R`\Delta' \preceq_{\mathsf{wk}} \Delta`), R`\Delta' \vdash t \Rightarrow \Delta \vdash t`), rule('D-Contract', h('ty.unlimited', R`\mathsf{unlimited}\,U`), R`U, U, \Delta \vdash t \Rightarrow U, \Delta \vdash t`)),
  'Both are renamings of the variables, the identity and the map $x \\mapsto x - 1$. They hold because E-Unit, E-Var, E-Chan and E-New accept unused entries of unlimited type.');
T('r-ex', 'E-Pack, E-Open', 'static/Typing.v: e_pack, e_open',
  rows(rule('E-Pack', R`${h('E-Force.hold', R`|\bar x| = m,\ \Gamma \vdash C[\bar x]`)}${Q}${h('E-Pack.lb', R`l \preccurlyeq \mathsf{heads}(${h('tp.pinst', R`T[\bar x]`)})`)}${Q}e : T[\bar x]^{a}`, R`e : (\exists^{l}\bar\iota.\,C.\,T^{a})^{0}`), rule('E-Open', R`${h('E-Open.entry', R`\Delta(i) = (\exists^{l}\bar\iota.\,C.\,T^{a_T})^{a},\ \neg\mathsf{unlimited}\,T`)}${Q}${h('E-Open.body', R`\Theta${h('tp.shift', R`{\uparrow}`)}; \Gamma{\uparrow}, C; \Delta{\uparrow}[i \mapsto T^{a+a_T}] \vdash^{F\uparrow} e : U{\uparrow}`)}`, R`\Theta;\Gamma;\Delta \vdash^{F} e : U`)),
  rows(rule('D-Pack', R`${h('E-Force.hold', R`\Gamma \vdash C[\bar x]`)}${Q}${h('E-Pack.lb', R`l \preccurlyeq \mathsf{heads}(${h('tp.pinst', R`T[\bar x]`)})`)}${Q}t : T[\bar x]`, R`t : \exists^{l}\bar\iota.\,C.\,T`), rule('D-Open', R`${h('E-Open.entry', R`\Delta(i) = \exists^{l}\bar\iota.\,C.\,T`)}${Q}${h('E-Open.body', R`\Theta${h('tp.shift', R`{\uparrow}`)}; \Gamma{\uparrow}, C; \Delta{\uparrow}[i \mapsto T] \vdash t : U{\uparrow}`)}`, R`\Theta;\Gamma;\Delta \vdash t : U`)),
  'Packing chooses $\\bar x$ with $\\Gamma \\vdash C[\\bar x]$, and opening adds $m$ fresh point variables with hypothesis $C$.');

// ---- process rules ----
const MEETSP = R`${h('lf.meets', R`N \in \mathbb{N} \Rightarrow \exists\, tk.\ ${h('ann.meets', R`\mathsf{meets}`)}\,\vartheta\,0\,${h('fu.tk', 'tk')}`)}`;
const PTERM = (m) => rule('P-Term', R`\begin{array}{c}${h('ty.prim', R`\mathsf{prim}\,T`)}${Q}${h('P-Term.C0', R`\mathrm{dom}\,\Theta_B = ${h('tp.ends', R`\mathsf{ends}`)}(C_0)`)}${Q}${h('P-Term.disj', R`${h('tp.chans', R`\mathsf{chans}`)}\,${h('tp.Sigma', R`\Sigma`)} \cap C_0 = \varnothing`)}${Q}${h('pfree', R`\mathsf{pfree}\,\Sigma`)} \\ ${h('P-Term.pairs', R`\forall c \in C_0.\ \Theta_B(c^{+}) = S@x^{N},\ \Theta_B(c^{-}) = \overline{S}@\overline{x}^{N}`)} \\ ${h('P-Term.typed', R`${h('tp.lift', R`\Sigma^{N}`)} \cup \Theta_B ; \varnothing ; \varnothing \vdash^{${h('P-Term.future', R`(\varnothing,\cdot)`)}}_{W,N} t : T^{a} \triangleright c ; \vartheta`)}\annraw{ \\ }\annot{${m(MEETSP)}}\end{array}`, R`\Sigma ${h('tp.pjudg', R`\vdash^{N}_W`)} (C_0, \{t\}) : T`);
const PCONN = R`\begin{array}{c}${h('P-Connect.left', R`\Sigma_1 \cup \Sigma_C \vdash^{N}_{W_1} (C_1, E_1) : T`)} \\ ${h('P-Connect.right', R`\Sigma_2 \cup ${h('P-Connect.cut', R`\overline{\Sigma_C}`)} \vdash^{N}_{W_2} (C_2, E_2) : \ast`)} \\ ${h('P-Connect.disj', R`\text{the channels of } \Sigma_1, \Sigma_2, \Sigma_C, C_1, C_2 \text{ pairwise disjoint}`)} \\ ${h('P-Connect.cutfree', R`\mathsf{pfree}\,\Sigma_C`)}${Q}${h('w.wf', R`\mathsf{world\_wf}\,W_1, W_2`)} \\ ${h('P-Connect.strict', R`${h('w.strict', R`\mathsf{strict}`)}(W_1 \sqcup W_2)`)}\end{array}`;
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
  id: 'p-join', title: 'P-Join (admissible)', rocq: 'static/Typing.v: p_join',
  tex: rule('P-Join', R`\begin{array}{c}\text{premises of P-Connect with} \\ ${h('P-Join.lemma', R`\mathsf{strict}\,W_1,\ \mathsf{strict}\,W_2,\ \mathsf{strict}(${h('w.restrict', R`W_1|_S`)} \sqcup W_2|_S)`)}\end{array}`, R`\begin{array}{c}\Sigma_1 \cup \Sigma_2 \vdash^{N}_{W_1 \sqcup W_2} \\ (C_1 \cup C_2 \cup \mathsf{chans}\,\Sigma_C, E_1 \uplus E_2) : T\end{array}`),
  caption: 'For well-formed $W_1$, $W_2$, $\\mathsf{strict}(W_1 \\sqcup W_2)$ iff both are strict and so is the join of their restrictions to the shared constants.'
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

// ---- notes ----
n("tj.Theta", "$\\Theta$, the end environment", "$\\Theta$ is a finite map from ends $o$ to entries $S@x^{a}$ with a session type $S$, a point $x$ and a credit $a$.", "Each end has its own name, so $\\Theta(c^{+})$ and $\\Theta(c^{-})$ are two separate entries and no entry needs a side bit.", DEF, "$\\Theta = \\{a \\mapsto S_a@\\rho^{N},\\ b \\mapsto S_b@(\\rho\\cdot 0)^{N}\\}$.", "static/Contexts.v: tentry, tenv");
n("tj.Gamma", "$\\Gamma$, facts and future hypotheses", "$\\Gamma$ consists of a list of constraint instances $(C, \\bar x)$ and a finite map of future variables $\\varphi \\mapsto u$, read as $u \\prec \\varphi$.", "Every order fact a rule may use beyond $\\prec_W$ is recorded in $\\Gamma$. The derivable facts are exactly the judgments $\\Gamma \\vdash x \\prec y$.", DEF, "In the body of the client loop $\\Gamma$ holds $(C, [\\iota, \\kappa, \\zeta])$.", "static/Contexts.v: hctx");
n("tj.Delta", "$\\Delta$, the variable context", "$\\Delta$ is a list indexed by de Bruijn indices whose entries are empty or a credited type $T^{a}$.", "A split puts an empty entry at index $i$ in the half that does not own variable $i$. Hence $i$ denotes the same variable in $\\Delta$, $\\Delta_1$ and $\\Delta_2$, and no index is shifted.", DEF, "$\\Delta = [(S_1@\\iota \\otimes S_2@\\kappa)^{0}]$ for the argument of a loop body.", "static/Contexts.v: lenv");
n("tj.F", "The future $F$", "$F = (X, \\varphi)$, $(X, \\bot)$ or $(X, \\cdot)$ with $X$ the points the context acts at after the term, $\\varphi$ an unknown rest above a known point and $\\bot$ a rest at hidden points.", "Every action at $x$ asks $x \\prec F$. Hence a term never waits at a point above a point at which its own context still acts.", "Without $F$ the thread $\\mathsf{let}\\ \\ast = \\mathsf{close}\\,c\\ \\mathsf{in}\\ \\mathsf{close}\\,d$ types for every placement of $c$ and $d$, and beside a partner that closes $d$ before $c$ both threads wait forever.", "$e_1$ of E-App runs under $F \\cup \\mathsf{heads}(\\Theta_2, \\Delta_2)$.", "static/Contexts.v: sfuture");
n("tj.W", "The world $W$", "The world whose order $\\prec_W$ the rules read.", "Every point fact a rule uses comes from $\\prec_W$ or from $\\Gamma$. Typing is monotone in $W$, so a program typed in $W$ is typed in every $W' \\sqsupseteq W$.", DEF, "E-New asks $\\mathsf{strict}(\\Gamma \\cup C)$ over $\\prec_W$.", "static/Typing.v: typed W");
n("tj.N", "The refill $N$", "$N \\in \\mathbb{N} \\cup \\{\\infty\\}$ is the credit of a fresh end and of an end after an action on it.", "A credit is a lower bound on a counter, and each action of a holder on another end lowers the counter by $1$. A finite $N$ bounds the number of such actions between two actions on one end, which lock freedom needs, and $N = \\infty$ gives deadlock-free typing.", DEF, "The client and server loop types at $N = 3$.", "static/Typing.v: typed N");
n("tj.cost", "The cost $c$", "$c \\in \\mathbb{N} \\cup \\{\\infty\\}$ is an upper bound on the number of session actions $e$ performs before it returns.", "Every entry held while $e$ runs ages by $c$. Hence $e$ performs at most as many actions as the credits of the held ends allow.", DEF, "$\\mathsf{send}\\,e$ has cost $c_0 + 1$.", "static/Typing.v: typed c");
n("tj.tix", "The ticket need $\\vartheta$", "$\\vartheta(r)$ is the number of link tickets $e$ needs to return with $r$ tickets left, and $\\mathsf{meets}\\,\\vartheta\\,r\\,tk \\iff \\vartheta(r) \\leq tk$.", "A link performs no session action, so the cost does not bound links. Tickets bound them, and $\\vartheta$ counts the tickets.", DEF, "$\\mathsf{link}\\,e$ has ticket need $\\vartheta_0 \\circ \\mathsf{tlink}\\,\\hat 1$.", "static/Typing.v: typed ϑ");
n("ctx.tsplit", "$\\Theta = \\Theta_1 \\uplus \\Theta_2$", "$\\mathrm{dom}\\,\\Theta_1 \\cap \\mathrm{dom}\\,\\Theta_2 = \\varnothing$ and $\\Theta = \\Theta_1 \\cup \\Theta_2$.", "Each end has exactly one owner. Two subterms therefore never act on the same end.", DEF, "In E-App $\\Theta_1$ holds the ends of $e_1$ and $\\Theta_2$ those of $e_2$.", "static/Contexts.v: tsplit");
n("ctx.lsplit", "$\\Delta = \\Delta_1 \\sqcup \\Delta_2$", "For every index $i$, a linear entry $\\Delta(i)$ is in exactly one of $\\Delta_1(i)$ and $\\Delta_2(i)$ and the other is empty, and an entry of unlimited type is in both.", "A linear entry may hold ends and is used exactly once. An entry of unlimited type holds no end, so using it twice duplicates no end.", DEF, "A box variable $f$ may be forced in both $e_1$ and $e_2$.", "static/Contexts.v: lenv_split");
n("ctx.hyps", "Constraint instances $(C, \\bar x)$", "A constraint $C$ with the points $\\bar x$ it is instantiated at, added by E-Box and E-Open.", "A box body and the scope of an opened existential know their points only through these instances. The facts $C[\\bar x]$ are all they may assume about them.", DEF, "$(C, [\\iota, \\kappa, \\zeta])$ in the body of the client loop.", "static/Contexts.v: hyps, hc_open");
n("ctx.fvar", "Future variables $\\varphi \\mapsto u$", "$\\varphi \\mapsto u \\in \\Gamma$ states $u \\prec \\varphi$ for an unknown future $\\varphi$ above $u$.", "A $\\lambda$ or box body is typed once for all its callers. By E-App every caller future $F$ satisfies $u \\prec F$, and $\\varphi$ stands for every such $F$.", DEF, "A $\\lambda$-body under $(\\varnothing, \\varphi)$ with $u \\prec \\varphi$.", "static/Contexts.v: hc_fvar");
n("ctx.fvarF", "The variable $\\varphi$ in $F$", "The unknown part of a future, read only through $\\Gamma \\vdash u \\prec \\varphi$.", "In the semantics $\\varphi$ denotes an arbitrary set of points above $u$. A body typed under $\\varphi$ is therefore correct for every caller future above $u$.", DEF, "$F = (\\varnothing, \\varphi)$.", "static/Contexts.v: futrest");
n("ctx.bot", "The flag $\\bot$ in $F$", "$\\bot$ states that the context holds ends at points unknown to the term, which then performs no session action.", "Every action asks $u \\prec F$, which requires $F$ to have no $\\bot$. No point is known to lie below a hidden point, so an action under $\\bot$ could wait above it.", DEF, "$e_1$ beside a context that holds an unopened $\\exists^{\\bot}$.", "static/Contexts.v: FBot, fs_bot");
n("ctx.slt", "$\\Gamma \\vdash x \\prec y$", "The least transitive relation containing $\\prec_W$, the facts $C[\\bar x]$ of the instances $(C, \\bar x)$ in $\\Gamma$, and $u \\prec \\varphi$ for every $\\varphi \\mapsto u$ in $\\Gamma$.", "Every order fact a typing rule reads is a judgment $\\Gamma \\vdash x \\prec y$.", DEF, "$\\Gamma \\vdash x \\prec x^{+}$ for every $\\Gamma$ and $x$.", "static/Contexts.v: fl, slt");
n("ctx.empty", "$\\Delta$ unlimited", "Every non-empty entry of $\\Delta$ has unlimited type.", "A value that mentions no variable uses no linear entry, and an unlimited entry may go unused.", DEF, "$\\ast$ types under every $\\Delta$ whose entries are empty or unlimited.", "static/Contexts.v: lenv_unl");
n("ctx.only", "$\\Delta = \\{x : T^{a}\\}$", "$\\Delta(x) = T^{a}$ and every other non-empty entry of $\\Delta$ has unlimited type.", "Every linear entry is used exactly once, and an unlimited entry may go unused.", DEF, "$x = 0$ types under $\\Delta = [T^{a}]$.", "static/Contexts.v: lenv_only");
n("side.act", "$x \\prec F$ at an action", "For an action at $x$ under $F = (X, \\cdot)$, $\\Gamma \\vdash x \\prec y$ for every $y \\in X$, $\\Gamma \\vdash x \\prec \\varphi$ when $F$ has a variable $\\varphi$, and $F$ has no $\\bot$.", "While the term waits at $x$, every point at which its context acts later lies above $x$. This is readiness against the future.", "Without it a term may wait at $x$ while its context must first act at a point below $x$, and the thread waits on itself through the partner end.", "E-Close at $x$ asks $x \\prec F$.", "static/Contexts.v: ub_below_s");
n("act.refill", "Refill $N$ after an action", "An end returned by an action, or created fresh, has credit $N$.", "The fuel layer sets the counter of an end to $N$ at every action on it, and the static credit is a lower bound on that counter.", DEF, "$\\mathsf{send}$ returns $(S@x^{+})^{N}$.", "static/Typing.v: e_send, e_recv, e_select, e_branch, e_new");
n("side.ub", "$u \\prec F$", "$u \\prec F \\iff (\\forall y \\in X.\\ \\Gamma \\vdash u \\prec y) \\land \\Gamma \\vdash u \\prec \\varphi \\land \\bot \\notin F$, true for absent $u$.", "It is the condition $x \\prec F$ of an action, stated for the upper point $u$ up to which a callee may wait.", DEF, "E-App asks $u \\prec F$ of the upper point $u$ of the closure.", "static/Contexts.v: ub_below_s");
n("side.lb", "$l \\preccurlyeq H$", "$l \\preccurlyeq H \\iff \\forall y \\in H.\\ l = y \\lor \\Gamma \\vdash l \\prec y$ for a point $l$, and $H = \\varnothing$ for absent $l$.", "A holder of a closure sees the heads of its ends only through $l$. Hence $l$ must be a lower bound of those heads.", DEF, "$\\overline{\\rho} \\preccurlyeq \\{\\overline{\\rho}\\}$.", "static/Contexts.v: lbx_below_h, lbound_of");
n("side.hold", "$\\Gamma \\vdash C[\\bar x]$", "For every fact $y \\prec z$ of $C$ instantiated at $\\bar x$, $\\Gamma \\vdash y \\prec z$.", "E-Force and E-Pack choose an instance $\\bar x$, and the box body or the packed value relies on $C[\\bar x]$.", DEF, "The self call of the client loop instantiates $C$ at $(\\iota^{+}, \\kappa^{+}, \\zeta)$.", "static/Contexts.v: hold_at");
n("age.free", "Aging an entry without ends", "$(T, a) - c = (T, a)$ when $\\mathsf{tfree}\\,T$.", "An entry without ends has no counter that could fall, so its credit bounds nothing.", DEF, "A box variable never ages.", "static/Contexts.v: age_free");
n("age.credit", "Aging an entry", "$(T, a) - c = (T, a - c)$, defined when $c \\leq a$.", "While a term of cost $c$ runs, the holder performs up to $c$ actions on other ends, and each lowers the counter of every held end by $1$. The premise $c \\leq a$ keeps the credit a lower bound on the counter.", "Without $c \\leq a$ a server holds its client end while it runs a callback of cost $\\infty$ at finite $N$, and the client waits without bound.", "$(S@x, 3) - 1 = (S@x, 2)$.", "static/Contexts.v: age_credit");
n("age.idle", "Aging an idle end", "$(S@x, a) - c = (S@x, \\max(a - c, 0))$ when $\\mathsf{unfold}(S) = \\mathsf{Skip}$.", "No thread acts on an idle end, so no action refills it. Truncation keeps its credit at or below its counter, which ticks and truncates at $0$ in the same way.", "With $c \\leq a$ required an idle end held across a loop loses credit every round and no finite $N$ types the loop. Keeping the credit instead exceeds the counter after one tick.", "$(\\mathsf{Skip}@\\chi, 0) - 1 = (\\mathsf{Skip}@\\chi, 0)$.", "static/Contexts.v: age_idle");
n("age.agg", "Aging an aggregate", "For a product, a sum or an existential, $(T, a) - c$ ages every part $(T_i, a + a_i)$ and returns credit $0$.", "The credit of an aggregate is a common share of its parts, so aging moves it into the parts and ages them.", DEF, "$(T^{1} \\otimes U^{1}, 1) - 1 = (T^{1} \\otimes U^{1}, 0)$.", "static/Contexts.v: age_prod, age_sum, age_ex");
n("age.ctx", "Aging the frame", "$\\Theta_2 - c_1$ and $\\Delta_2 - c_1$ age every entry by the cost $c_1$ of the first subterm.", "$\\Theta_2$ and $\\Delta_2$ are held while $e_1$ runs, and each action of $e_1$ lowers their counters by $1$.", "Without aging a thread holds an end across unboundedly many actions on other ends, and the partner of that end waits without bound.", "In the cycle example main loses $1$ of the credit of $d$ while it closes $c$.", "static/Contexts.v: thage, lage");
n("cap.sess", "Capturing an end", "$(S@x, a_0) \\leadsto_{h,a} (S@x, h)$, defined when $h + a \\leq a_0$.", "The closure itself has credit $a$ and ages by up to $a$ before its body runs. The body may assume credit $h$ on the end, so the end needs $h + a$.", DEF, "$h = 1$ and $a = 1$ need $a_0 \\geq 2$.", "static/Contexts.v: cap_sess");
n("cap.arr", "Capturing a closure", "$(T \\multimap[\\ldots;h_0] U, a_0) \\leadsto_{h,a} (T \\multimap[\\ldots;h_0] U, h - h_0)$, defined when $h_0 \\leq h$ and $h + a \\leq h_0 + a_0$.", "A captured closure guarantees credit $h_0 + a_0$ on its own ends, and the premise asks this to cover $h + a$. The new credit $h - h_0$ places those ends at exactly the floor $h$ of the outer closure.", DEF, "A callback with $h_0 = 1$ and $a_0 = 2$, captured at $h = 2$ and $a = 1$, gets credit $1$.", "static/Contexts.v: cap_arr");
n("sub.tsub", "Subtyping $T^{a} \\leq T'^{a'}$", "The least relation closed under Sub-Unit, Sub-Sess, Sub-Arr, Sub-Prod, Sub-Sum, Sub-Box and Sub-Ex, used by E-Sub.", "The branches of $\\mathsf{case}$ and of a received choice need one common type, and the credit $N$ of $\\mathsf{new}_\\ell$ must fall to what a protocol asks. Every clause weakens what a value promises, so $V$ at $T^{a}$ is contained in $V$ at $T'^{a'}$.", "Without E-Sub the client loop could not pass the fresh ends at credit $N = 3$ to a parameter that asks credits $1$ and $2$.", "$(S@x)^{3} \\leq (S@x)^{1}$ and $\\exists^{\\bot}\\rho.\\,\\{\\rho \\prec \\overline{\\rho\\cdot 0}\\}.\\,T \\leq \\exists^{\\bot}\\rho.\\,\\varnothing.\\,T$.", "static/Contexts.v: tsub");
n("sub.dconv", "D-Conv", "If $\\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W} t : T$ and $\\mathsf{ty\\_df}\\,T \\leq \\mathsf{ty\\_df}\\,T'$ at annotations $\\infty$, then $\\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W} t : T'$.", "Deadlock-free typing reads no credit, cost or ticket need. At annotations $\\infty$ every clause of $\\leq$ on credits, costs, ticket needs and floors holds, and $\\leq$ reduces to $\\approx$ on session types and dropping facts of existentials.", DEF, "$\\exists^{\\bot}\\rho.\\,\\Lambda_0(\\rho).\\,T$ converts to $\\exists^{\\bot}\\rho.\\,\\varnothing.\\,T$.", "static/Typing.v: d_conv");
n("tp.sub-credit", "Credits may fall", "$a' \\leq a$, and $a' + a_T' \\leq a + a_T$ at an existential.", "A credit is a lower bound on the counter of every end inside the value, so a smaller credit promises less. $\\mathsf{new}_\\ell$ and every action return credit $N$, and the protocol of a parameter or a payload asks a fixed credit $b \\leq N$.", "Without it a fresh end at credit $N$ fits only a parameter at credit exactly $N$, and no loop that ages an end before its self call types.", "$(S@x)^{3} \\leq (S@x)^{2}$.", "static/Contexts.v: tsub");
n("tp.sub-cost", "Costs and ticket needs may rise", "$c \\leq c'$ in $\\mathbb{N} \\cup \\{\\infty\\}$ and $\\vartheta \\leq \\vartheta'$ pointwise, for the cost and ticket need of an arrow, a box and, in E-Sub, of the term.", "$c$ and $\\vartheta$ are upper bounds on actions and tickets. The branches of $\\mathsf{case}$ and closures passed to one parameter have different costs, and the larger bound covers both.", DEF, "A closure of cost $1$ passes where cost $\\infty$ is expected.", "static/Contexts.v: tsub, types/Costs.v: tle");
n("tp.sub-floor", "The wait bound of an arrow", "$h \\leq h'$ and $h' + a' \\leq h + a$ for the floors $h, h'$ and credits $a, a'$ of two arrows.", "The body of a closure may assume that every captured end has credit $h$, and the holder guarantees $h + a$ in total. Raising the floor to $h'$ is sound only when the guarantee $h' + a'$ does not exceed the old $h + a$.", "Without $h' + a' \\leq h + a$ a closure could claim a floor above the credit its captured ends have.", "$h = 1, a = 1$ converts to $h' = 2, a' = 0$.", "static/Contexts.v: tsub");
n("tp.sub-sess", "Session types up to equivalence", "$S \\simeq S'$, bisimilar head normal forms with equal annotations, which is $S \\approx S'$ at annotations $\\infty$.", "With $\\mathsf{Skip}$, sequencing and $\\mu$ one protocol has many spellings, e.g. $\\mathsf{Skip}.S \\simeq S$. Rules compare protocols by behaviour.", "Without it an unfolded recursive protocol and its folded form would be different types, and no loop that acts once and recurses would type.", "$\\mu\\alpha.\\,!\\ast.\\alpha \\leq\\ !\\ast.\\mu\\alpha.\\,!\\ast.\\alpha$ at the same point.", "static/Contexts.v: sub_sess, types/Types.v: sequiv");
n("tp.sub-ex", "An existential may drop facts", "$\\mathsf{facts}\\,C' \\subseteq \\mathsf{facts}\\,C$, the constraint $C'$ of the supertype states a subset of the facts of $C$ over the same variables.", "E-New states the facts $C$ of a creation in its existential. Two branches of a $\\mathsf{case}$ or two creations that serve one type then agree on the facts both state, by dropping the rest.", "Without it, two branches that create a channel with different facts have different result types, and the $\\mathsf{case}$ does not type.", "$\\exists^{\\bot}\\rho.\\,\\{\\rho \\prec \\overline{\\rho\\cdot 0}\\}.\\,T \\leq \\exists^{\\bot}\\rho.\\,\\varnothing.\\,T$.", "static/Contexts.v: sub_ex");
n("tp.sub-var", "Variance", "$\\leq$ is contravariant in the argument and covariant in the result of $\\multimap$, and covariant in the components of $\\otimes$ and $\\oplus$, whose credits add before comparison.", "A closure that accepts more and returns less can stand for one that accepts less and returns more.", DEF, "$(T^{1} \\multimap U^{3}) \\leq (T^{2} \\multimap U^{1})$.", "static/Contexts.v: sub_arr, sub_prod, sub_sum");
n("tp.sub-agg", "Products and sums", "$T_i^{a + a_i} \\leq T_i'^{a' + a_i'}$ for $i = 1, 2$.", "The credit of an aggregate pushes inward, so the parts are compared at the credits they carry inside the aggregate.", DEF, "$(T^{1} \\otimes U^{1})^{1} \\leq (T^{2} \\otimes U^{0})^{0}$ needs $T^{2} \\leq T^{2}$ and $U^{2} \\leq U^{0}$.", "static/Contexts.v: sub_prod, sub_sum");
n("tp.sub-teq", "Equal up to $\\simeq$", "$T \\equiv T'$, the two types have the same shape and their session types are pairwise $\\simeq$.", "The body of a box and of an existential is compared exactly up to protocol spellings. Credits inside it are not lowered, because a box is copied and an existential is opened at its own credit.", DEF, "$\\Box(\\ldots\\,(\\mathsf{Skip}.S)@x) \\leq \\Box(\\ldots\\,S@x)$.", "types/Types.v: teq");
n("E-Abs.phi", "Fresh future variable", "The body is typed under $(\\varnothing, \\varphi)$ for a $\\varphi \\notin \\mathrm{dom}\\,\\Gamma$ with $u \\prec \\varphi$.", "The body runs when a caller applies the closure, and by E-App every caller future $F$ satisfies $u \\prec F$. Typing under a fresh $\\varphi$ covers all such $F$.", "A body typed under the future of its definition is checked against facts that fail at another call site.", "The body of $\\mathsf{between}$ runs under $\\varphi$ with $\\kappa \\prec \\varphi$.", "static/Typing.v: e_abs, e_box");
n("E-Abs.lb", "Lower point of a closure", "$l \\preccurlyeq \\mathsf{heads}(\\Theta, \\Delta)$ and $\\Delta$ carries no $\\bot$.", "A holder of the closure reads the heads of its ends only through $l$. A hidden point has no lower bound, so $\\bot$ is excluded.", "A thread holding ends at the unrelated points $1$ and $2$ has no common lower point, so E-Abs rejects a $\\lambda$ that captures both. E-SpawnLam types the spawn of such a $\\lambda$.", "Capturing $a^{+}$ at $\\rho$ gives $l = \\overline{\\rho}$.", "static/Contexts.v: lbx_below_h, lbound_of");
n("E-Abs.cap", "Capture", "$\\Theta \\leadsto_{h,a} \\Theta^{h}$ and $\\Delta \\leadsto_{h,a} \\Delta^{h}$ restate every captured entry at the floor $h$.", "The closure has credit $a$, and its body may assume credit $h$ on every captured end. Capture asks $h + a$ of each captured credit.", DEF, "$a^{+}$ at credit $2$ captured with $h = 1$ and $a = 1$ is seen at credit $1$.", "static/Contexts.v: thcap, lcap");
n("E-Abs.body", "Body of a $\\lambda$", "$e$ is typed under $\\Theta^{h}$, $\\Gamma$ extended by $u \\prec \\varphi$, $\\Delta^{h}$ extended by the argument $T^{a_T}$, and the future $(\\varnothing, \\varphi)$.", "The body runs at a later call. It may rely only on its captured entries, its argument and $u \\prec \\varphi$, and E-App establishes $u \\prec F$ at every call.", DEF, "The body of the client loop with argument $(S_1@\\iota \\otimes S_2@\\kappa)^{0}$.", "static/Typing.v: e_abs");
n("E-App.ub", "$u \\prec F$ at a call", "The upper point $u$ of the closure satisfies $u \\prec F$.", "The callee waits only at points up to $u$. Every point at which the caller acts afterwards lies above $u$.", "A call of a closure that waits at $\\kappa$, while the caller must still act at a point below $\\kappa$, makes the caller wait on itself.", "main forces $\\mathsf{between}$ last, so $F = \\varnothing$.", "static/Typing.v: e_app");
n("E-App.fut1", "Future of the first subterm", "$e_1$ is typed under $F \\cup \\mathsf{heads}(\\Theta_2, \\Delta_2)$, with $\\bot$ added when $\\Delta_2$ carries $\\bot$.", "The entries of the second subterm are held while $e_1$ runs. Hence $e_1$ must not wait above their heads.", "$\\mathsf{let}\\ \\ast = \\mathsf{close}\\,c\\ \\mathsf{in}\\ \\mathsf{close}\\,d$ beside a partner that closes $d$ before $c$ deadlocks. E-LetU rejects the first thread unless $x_c \\prec \\overline{x_d}$.", "The cycle example needs $\\rho \\prec \\overline{\\rho\\cdot 0}$ for $\\mathsf{close}\\,c$ while $d$ is held.", "static/Typing.v: e_app, e_pair, e_letp, e_letu, e_case");
n("E-App.fut2", "Future of the argument", "$e_2$ is typed under $F \\cup \\{l\\}$ with $l$ the lower point of the closure.", "The closure is held while $e_2$ runs, and $l$ bounds the heads of its ends from below.", DEF, "$f\\,(\\mathsf{close}\\,c)$ with $f$ capturing $d$.", "static/Typing.v: e_app");
n("E-App.credit", "$c_2 \\leq a_1$", "The credit $a_1$ of the closure is at least the cost $c_2$ of the argument.", "The closure is held while $e_2$ runs, and each action of $e_2$ lowers the counters of the captured ends by $1$.", DEF, "A closure at credit $\\infty$ admits an argument of every cost.", "static/Typing.v: e_app");
n("E-App.cost", "Cost of a call", "$e_1\\,e_2$ has cost $c_1 + c_2 + c$ with $c$ the cost of the arrow.", "The call runs $e_1$, then $e_2$, then the body, and $c$ bounds the actions of the body.", DEF, "$f\\,v$ with $f$ and $v$ values and $f : T \\multimap[2;\\ldots] U$ has cost $2$.", "static/Typing.v: e_app");
n("E-Pair.fut2", "Future of the second component", "$e_2$ is typed under $F \\cup \\mathsf{heads}(T_1)$.", "The value of $e_1$ is held while $e_2$ runs.", DEF, "$\\langle c, \\mathsf{close}\\,d\\rangle$ needs $x_d \\prec \\overline{x_c}$.", "static/Typing.v: e_pair");
n("E-Pair.age1", "Aging the first component", "$(T_1, a_1) - c_2 = (T_1', a_1')$.", "The value of $e_1$ is held while $e_2$ runs, so it ages by $c_2$.", DEF, "$\\langle c, \\mathsf{send}\\,\\langle\\ast, d\\rangle\\rangle$ ages $c$ by $1$.", "static/Typing.v: e_pair");
n("tp.letp", "Body of a pair elimination", "$e_2$ is typed under the aged $\\Theta_2'$, $\\Delta_2'$ extended by $T_2^{a+a_2}$ at index $0$ and $T_1^{a+a_1}$ at index $1$, under $F$.", "The credit $a$ of the pair is a common share of both components, so each bound variable gets $a$ added to its own credit.", DEF, "$\\mathsf{let}\\ \\langle v, c\\rangle = \\mathsf{recv}\\,c\\ \\mathsf{in}\\ e$ binds the received value and the continuation end.", "static/Typing.v: e_letp");
n("tp.letu", "Body of a unit elimination", "$e_2$ is typed under the aged $\\Theta_2'$ and $\\Delta_2'$, under $F$, after $e_1$ returned $\\ast$.", "$\\ast$ holds no end, so nothing is bound. The rule sequences $e_1$ before $e_2$.", DEF, "$\\mathsf{let}\\ \\ast = \\mathsf{close}\\,c\\ \\mathsf{in}\\ \\mathsf{close}\\,d$.", "static/Typing.v: e_letu");
n("E-Case.branches", "Branches", "$\\Theta_2' ; \\Gamma ; T_i^{a + a_i}, \\Delta_2' \\vdash e_i : T^{a_T}$ for $i = 1, 2$, with cost $c_0 + \\max(c_1, c_2)$.", "Exactly one branch runs, and the choice is known only at run time. Both branches must fit the same continuation, and the cost bounds either.", DEF, "$\\mathsf{case}\\,(\\mathsf{branch}\\,o)\\,(a.\\,\\mathsf{close}\\,a)\\,(a.\\,\\mathsf{close}\\,a)$.", "static/Typing.v: e_case");
n("E-Box.unl", "$\\Delta$ unlimited", "Every non-empty entry of $\\Delta$ has unlimited type, and $\\Theta = \\varnothing$.", "A box value is copied freely. If it held an end, a copy would duplicate that end.", DEF, "$\\mathsf{ring}$ captures no variable.", "static/Contexts.v: lenv_unl");
n("E-Box.inst", "Session instances", "The body is typed for every list $\\bar s$ of $k$ session types with $\\mathsf{sinsts}\\,N\\,\\bar s$.", "A box is polymorphic in its $k$ session variables, and each force may choose another instance. At $N = \\infty$ only erased instances are admitted, because an end received at a finite credit cannot age by $\\infty$.", DEF, "$k = 0$ in every example.", "static/Contexts.v: sinsts");
n("E-Box.body", "Body of a box", "The body is typed with $\\Theta = \\varnothing$, the context shifted past $m$ fresh point variables $\\bar\\iota$, the hypothesis $C(\\bar\\iota)$, the box at index $0$, and the future $(\\varnothing, \\varphi)$.", "Each force instantiates $\\bar\\iota$ and the session variables anew. The body may assume only $C(\\bar\\iota)$ and $u \\prec \\varphi$.", DEF, "The body of the client loop.", "static/Typing.v: e_box");
n("E-Box.open", "Opened constraint", "$\\Gamma{\\uparrow^m}$ extended by the instance $(C, \\bar\\iota)$.", "The body relies on $C$ at its own point variables, and every force checks $C$ at the chosen instance.", "Without $C$ the client loop cannot order the points of two consecutive rounds.", "$\\Gamma{\\uparrow^3}$ extended by $C(\\iota, \\kappa, \\zeta)$.", "static/Contexts.v: hc_open");
n("E-Box.self", "The self", "The body binds the box at index $0$, at its own type and credit $\\infty$.", "This is recursion. A box holds no end, so its credit bounds nothing and is $\\infty$.", DEF, "$(\\mathsf{force}\\,f)\\,\\langle a, b\\rangle$ calls the self $f$.", "static/Typing.v: e_box");
n("E-Force.hold", "The instance meets $C$", "$|\\bar x| = m$ and $\\Gamma \\vdash C[\\bar x]$.", "The body was typed under $C(\\bar\\iota)$. Running it at $\\bar x$ is correct only when $C[\\bar x]$ holds.", DEF, "main forces $\\mathsf{between}$ at $(\\rho, \\rho\\cdot 1)$, where $\\Lambda_0$ gives $C$.", "static/Typing.v: e_force, e_pack");
n("E-Force.ub", "$u[\\bar x] \\prec F$", "The instantiated upper point $u[\\bar x]$ of the box satisfies $u[\\bar x] \\prec F$.", "The forced body waits only at points up to $u[\\bar x]$, and the caller acts afterwards at $F$.", DEF, "The self call of a loop at $\\zeta$ under $F = \\varnothing$.", "static/Typing.v: e_force");
n("E-Send.unfold", "Send head", "$\\mathsf{unfold}(S_0) = {!}(\\bar\\iota.\\,T).S$.", "Rules read the first action of $S_0$ after unfolding, so a recursive protocol $\\mu\\alpha.S$ needs no rule of its own.", DEF, "$S_0 = \\mu\\alpha.\\,{!}\\ast.\\alpha$ unfolds to ${!}\\ast.(\\mu\\alpha.\\,{!}\\ast.\\alpha)$.", "static/Typing.v: e_send");
n("E-Send.nobot", "No $\\bot$ in the payload", "$\\mathsf{hbot}\\,T = \\mathsf{false}$, so the payload contains no existential with lower bound $\\bot$.", "While the sender waits at $x$ it holds the payload, so every end $o$ of the payload at point $y$ needs $x \\prec \\overline{y}$. These ends are bounded only through the heads of $T$, and an existential at $\\bot$ has ends at points that no head bounds, so the readiness of the send fails.", DEF, "$\\mathsf{send}\\,\\langle \\mathsf{new}_\\ell, o\\rangle$ with the unopened pair of $\\mathsf{new}_\\ell$ as payload is rejected.", "static/Typing.v: e_send");
n("E-Send.heads", "$x$ below the payload heads", "$\\Gamma \\vdash x \\prec y$ for every $y \\in \\mathsf{heads}(T[x\\cdot i])$.", "The sender holds the payload while it waits at $x$ and does not offer the payload ends. Readiness asks $x$ below the partner point of each such end, and the heads bound those partner points from below.", DEF, "The growing ring needs $Y \\prec \\overline{Y\\cdot 0}$ for the payload $a$ of the send on $y$ at $Y$.", "static/Typing.v: e_send");
n("E-Send.floor", "Payload floor", "$(T[x\\cdot i], a_0 + a_p) - 1 \\leq T[x\\cdot i]^{b}$, so the payload aged by $1$ still meets the floor $b$ of the protocol.", "A handed end loses $1$ of its counter at the send. Requiring $b$ after the loss bounds how often one end may be handed on.", "Without the loss of $1$, an end at floor $b$ is handed on forever, and its partner waits forever.", "The growing ring sends $a'$ at credit $4$ against floor $2$.", "static/Typing.v: e_send");
n("E-Recv.unfold", "Receive head", "$\\mathsf{unfold}(S_0) = {?}(\\bar\\iota.\\,T).S$.", "Rules read the first action of $S_0$ after unfolding, so recursive protocols need no rule of their own.", DEF, "$\\mu\\alpha.\\,{?}\\ast.\\alpha$ unfolds to ${?}\\ast.(\\mu\\alpha.\\,{?}\\ast.\\alpha)$.", "static/Typing.v: e_recv");
n("E-Close.unfold", "Close head", "$\\mathsf{unfold}(S_0) = \\mathsf{Close}$.", "Rules read the first action of $S_0$ after unfolding.", DEF, "$\\mathsf{Close}@x$.", "static/Typing.v: e_close");
n("E-Select.unfold", "Select head", "$\\mathsf{unfold}(S_0) = \\oplus(S_1, S_2)$.", "Rules read the first action of $S_0$ after unfolding.", DEF, "$\\oplus(\\mathsf{Close}, \\mathsf{Close})$.", "static/Typing.v: e_select");
n("E-Branch.unfold", "Branch head", "$\\mathsf{unfold}(S_0) = \\&(S_1, S_2)$.", "Rules read the first action of $S_0$ after unfolding.", DEF, "$\\&(\\mathsf{Close}, \\mathsf{Close})$.", "static/Typing.v: e_branch");
n("E-Link.dual", "Linked ends dual", "$e$ returns $(S@x)^{a_1} \\otimes (\\overline{S}@\\overline{x})^{a_2}$, two ends at dual types and dual points.", "After the link the partners of the two ends form one channel. They are a well-typed pair only when the linked ends are exactly dual at dual points.", DEF, "$\\mathsf{link}\\,\\langle c^{+}, d^{-}\\rangle$ with $c^{+} : S@x$ and $d^{-} : \\overline{S}@\\overline{x}$.", "static/Typing.v: e_link");
n("E-SpawnLam.age", "Handed ends lose $1$", "$\\Theta' = \\Theta - 1$ and $\\Delta' = \\Delta - 1$.", "A hand-over passes each counter minus $1$. A spawn is no action, so this loss is the only bound on how often an end is handed on by spawns.", "Under truncation a counter $0$ is handed on as $0$ again, and an end travels from thread to thread forever.", "In the cycle example the thunk receives $d'$ with credit $1$ less.", "static/Typing.v: e_spawn_lam");
n("E-SpawnLam.body", "Body of a spawned $\\lambda$", "$e$ is typed under $\\Theta'$, $\\Delta'$ extended by the argument $\\ast^{a_1}$, and the empty future.", "A spawned $\\lambda$ needs no lower point, because no thread holds it as a closure. Each spawned body therefore gets its own floor.", DEF, "$\\mathsf{spawn}\\,(\\lambda u.\\,\\mathsf{let}\\ \\ast = u\\ \\mathsf{in}\\ \\mathsf{close}\\,d')$.", "static/Typing.v: e_spawn_lam");
n("E-SpawnLam.future", "Empty future of the child", "The child body runs under $(\\varnothing, \\cdot)$, a future with no point, no variable and no $\\bot$.", "The child is a new thread with no context, so no point of any context lies in its future.", "Typing the child under every future above an upper point fails for a body that creates a channel at a fresh root and waits on it.", "P-Term types every thread under $(\\varnothing, \\cdot)$.", "static/Typing.v: e_spawn_lam");
n("E-Spawn.credit", "Closure credit $a \\geq 1$", "A spawned closure value has credit $a \\geq 1$.", "Spawning hands over the captured ends with their counters minus $1$, and $a \\geq 1$ pays for that loss.", DEF, "$\\mathsf{spawn}\\,f$ with $f$ at credit $1$.", "static/Typing.v: e_spawn");
n("E-New.bot", "Lower bound $\\bot$", "The pair sits at a root $\\rho$ that no point of the context is related to.", "$\\exists^{\\bot}$ records that the ends of the value sit at points without a known lower bound, and $\\bot$ propagates into every future that holds the value.", DEF, "$\\mathsf{mk}_0$ returns $\\exists^{\\bot}\\iota.\\,C.\\,({?}\\ast.\\mathsf{Close})@\\overline{\\iota}$.", "static/Typing.v: e_new");
n("E-New.facts", "The constraint $C$", "A set of facts, possibly infinite, over $\\pi$, its shifts and fields, and points of $\\Gamma$.", "The derivation chooses the facts the new channel needs, and an interval $l \\prec \\pi \\prec u$ is the simplest case. Opening the existential adds $C$ to $\\Gamma$.", "With facts limited to finitely many bounds by held ends, a client and server loop that orders the two channels at every round, $\\iota^{+k} \\prec \\overline{\\kappa^{+k}}$ for all $k$, does not type.", "$C = \\{\\rho \\prec \\overline{\\rho\\cdot 0},\\ \\overline{\\rho} \\prec \\rho\\cdot 0\\}$ in the cycle example.", "static/Typing.v: e_new");
n("E-New.pos", "Position $\\pi$", "Either $\\pi = \\rho$, bound by the existential, or $\\pi = x\\cdot\\kappa$ for a point $x$ of the context.", "A channel created to be sent on an end at $x$ lands at the field $x\\cdot j$ where the receiver expects its $j$-th payload end.", DEF, "$d$ at $\\iota\\cdot 0$ in the example with a channel between two box arguments.", "static/Typing.v: e_new");
n("E-New.strict", "$\\mathsf{strict}(\\Gamma \\cup C)$", "The facts of $\\Gamma$, the order $\\prec_W$ and $C$ together derive no $x \\prec x$.", "Every creation grows the world by $C$, and the results ask a strict world. The check keeps every grown world strict.", "Facts $\\overline{\\rho} \\prec \\rho\\cdot 0$ and $\\rho\\cdot 0 \\prec \\overline{\\rho}$ in one $C$ give a cycle, and two threads waiting on each other would both count as ready.", "$\\{\\rho \\prec \\overline{\\rho\\cdot 0}\\}$ is strict.", "static/Typing.v: e_new");
n("E-New.dual", "Dual pair at $N$", "$c^{+}$ has type $S@\\pi$ and $c^{-}$ type $\\overline{S}@\\overline{\\pi}$, both at credit $N$.", "The fuel layer starts both counters of a new channel at $N$, and the credits are lower bounds on them.", DEF, "$(S_a@\\pi)^{N} \\otimes (S_b@\\overline{\\pi})^{N}$ with $S_b = \\overline{S_a}$.", "static/Typing.v: e_new");
n("E-Sub.cost", "Weakening costs", "$c \\leq c'$ and $\\vartheta \\leq \\vartheta'$.", "The cost and the ticket need are upper bounds, so a larger bound is also correct.", DEF, "Every cost may rise to $\\infty$.", "static/Typing.v: e_sub");
n("E-Weak.drop", "Weakening", "$\\Delta'$ arises from $\\Delta$ by emptying entries of unlimited type only.", "A linear entry may hold ends that must be used, so only entries of unlimited type are dropped.", DEF, "Dropping an unused box variable.", "static/Contexts.v: lenv_wk");
n("E-Pack.lb", "Lower bound of a pack", "$l = \\bot$, or $l \\preccurlyeq \\mathsf{heads}(T[\\bar x])$ and $T[\\bar x]$ carries no $\\bot$.", "After packing, a holder sees the ends only through $l$, so $l$ must bound the heads of the packed value from below. The value relation at an existential states exactly this bound.", DEF, "Packing a fresh pair at $\\bot$.", "static/Contexts.v: lbx_below_h");
n("E-Open.entry", "Opened entry", "$\\Delta(i) = (\\exists^{l}\\bar\\iota.\\,C.\\,T^{a_T})^{a}$ and $T$ is not unlimited.", "Opening replaces entry $i$ in place. Variable renaming, used for contraction, maps distinct linear entries to distinct indices, and this needs the opened entry to be linear.", DEF, "Opening the result of $\\mathsf{new}_\\ell$.", "static/Typing.v: e_open");
n("E-Open.body", "Body after opening", "$\\Theta$, $\\Gamma$, $\\Delta$, $F$ and $U$ shift past $m$ fresh point variables, $C$ joins $\\Gamma$, and entry $i$ becomes $T^{a + a_T}$.", "The fresh variables stand for the unknown witness, and $C$ is all the scope knows about it. The credit of the existential moves into its body.", DEF, "$\\mathsf{let}\\ p = (\\mathsf{force}\\,\\mathsf{mk}_0)\\,\\ast\\ \\mathsf{in}\\ \\ldots$ opens at $\\iota$.", "static/Typing.v: e_open");
n("pfree", "$\\mathsf{pfree}\\,\\Sigma$", "For every $o \\in \\mathrm{dom}\\,\\Sigma$, $\\overline{o} \\notin \\mathrm{dom}\\,\\Sigma$.", "P-Term puts every channel whose two ends the thread holds into $C_0$. Hence an interface never holds both ends of a channel, which the semantic P-Connect needs.", "No program is lost, because such a channel always moves into $C_0$.", "$\\Sigma = \\{c^{+}, c^{-}\\}$ is rejected, and $(\\{c\\}, \\ldots)$ with $\\Sigma = \\varnothing$ types instead.", "static/Typing.v: pfree");
n("P-Term.C0", "$\\mathrm{dom}\\,\\Theta_B = \\mathsf{ends}(C_0)$", "$o \\in \\mathrm{dom}\\,\\Theta_B$ iff the channel of $o$ is in $C_0$.", "Every end of the thread is an interface end or an end of a restricted channel, and the second kind is exactly $\\Theta_B$.", DEF, "$C_0 = \\varnothing$ and $\\Theta_B = \\varnothing$ for a source program.", "static/Typing.v: p_term");
n("P-Term.disj", "$\\mathsf{chans}\\,\\Sigma \\cap C_0 = \\varnothing$", "No channel of the interface is restricted.", "Then every end of $\\Sigma^{N} \\cup \\Theta_B$ lies in exactly one part, and the interface is the environment restricted to the channels outside $C_0$.", DEF, "$\\Sigma = \\{c^{+} \\mapsto \\mathsf{Close}@x\\}$ with $C_0 = \\varnothing$.", "static/Typing.v: p_term");
n("P-Term.pairs", "Restricted pairs dual", "For every $c \\in C_0$ there are $S$ and $x$ with $\\Theta_B(c^{+}) = S@x^{N}$ and $\\Theta_B(c^{-}) = \\overline{S}@\\overline{x}^{N}$.", "A restricted channel has both ends inside the process. They synchronize with each other only, so they need dual types at dual points.", DEF, "$c^{+} : S@x$ and $c^{-} : \\overline{S}@\\overline{x}$.", "static/Typing.v: p_term");
n("P-Term.typed", "Thread typing", "$t$ is typed under $\\Sigma^{N} \\cup \\Theta_B$, empty $\\Gamma$ and $\\Delta$, and the empty future, at $W$ and $N$.", "The process judgment has static premises only. Its semantic content comes from the fundamental theorems.", DEF, "The client and server main at $N = \\infty$.", "static/Typing.v: p_term");
n("P-Term.future", "Empty future", "A thread at top level runs under $(\\varnothing, \\cdot)$.", "A thread has no context, so no point lies in its future.", DEF, "$(\\varnothing, \\cdot)$.", "static/Typing.v: p_term");
n("lf.meets", "$N \\in \\mathbb{N} \\Rightarrow \\exists\\, tk.\\ \\mathsf{meets}\\,\\vartheta\\,0\\,tk$", "$N \\in \\mathbb{N} \\Rightarrow \\exists\\, tk.\\ \\vartheta(0) \\leq tk$, trivial at $N = \\infty$.", "Lock freedom needs a finite number of link tickets per thread, and typing at a finite $N$ does not give one, because a ticket need may have offset $\\infty$.", "A loop that links once per round has no finite ticket count and is rejected at finite $N$.", "$\\mathsf{meets}\\,\\vartheta\\,0\\,0$ in the examples without links.", "static/Typing.v: p_term");
n("lf.N", "$N \\in \\mathbb{N}$", "The refill of lock-free typing is a natural number.", "Lock freedom ranks waiting threads by counters as natural numbers, and at $N = \\infty$ every counter is $\\infty$.", DEF, "$N = 4$ for the growing ring.", "static/Typing.v: ptyped");
n("P-Connect.left", "Left component", "$(C_1, E_1)$ is typed over $\\Sigma_1 \\cup \\Sigma_C$ in $W_1$ at result $T$.", "The main thread lies on the left, so the left side carries the result $T$ and the right side returns $\\ast$.", DEF, "$\\mathsf{close}\\,c^{+}$ at $T = \\ast$.", "static/Typing.v: p_connect");
n("P-Connect.right", "Right component at $\\ast$", "$(C_2, E_2)$ is typed over $\\Sigma_2 \\cup \\overline{\\Sigma_C}$ in $W_2$ at result $\\ast$.", "Only the main thread returns a value, and every other thread returns $\\ast$.", DEF, "$\\mathsf{close}\\,c^{-}$.", "static/Typing.v: p_connect");
n("P-Connect.cut", "Exact dual cut $\\overline{\\Sigma_C}$", "$\\overline{\\Sigma_C}$ maps $\\overline{o}$ to $\\overline{S}@\\overline{x}$ for every $o \\mapsto S@x$ in $\\Sigma_C$.", "After composition the two ends of each cut channel are restricted, and lock freedom asks their protocols dual up to annotations. An exact dual gives this, a dual up to annotations does not.", "An annotation mismatch on a cut channel breaks the payload credit of a later message.", "$\\overline{\\{c^{+} \\mapsto \\mathsf{Close}@x\\}} = \\{c^{-} \\mapsto \\mathsf{Close}@\\overline{x}\\}$.", "static/Typing.v: senv_dual");
n("P-Connect.disj", "Disjoint channels", "$\\mathrm{dom}\\,\\Sigma_1 \\cap \\mathrm{dom}\\,\\Sigma_C = \\varnothing$, $\\mathrm{dom}\\,\\Sigma_2 \\cap \\mathrm{dom}\\,\\overline{\\Sigma_C} = \\varnothing$, the channel sets of $\\Sigma_1$, $\\Sigma_2$, $\\Sigma_C$ are pairwise disjoint, $C_1 \\cap C_2 = \\varnothing$, and each $C_i$ is disjoint from the channels of $\\Sigma_1$, $\\Sigma_2$, $\\Sigma_C$.", "Every channel then lives in one place. The cut $\\Sigma_C$ is the only channel set both sides use, so composition merges no two channels.", DEF, "Two closes cut at $c$ with $\\Sigma_1 = \\Sigma_2 = \\varnothing$ and $C_1 = C_2 = \\varnothing$.", "static/Typing.v: p_connect");
n("P-Connect.cutfree", "$\\mathsf{pfree}\\,\\Sigma_C$", "The cut holds no partner pair.", "The composite interface stays partner-free, which P-Term establishes for single threads.", DEF, "$\\Sigma_C = \\{c^{+} \\mapsto \\mathsf{Close}@x\\}$.", "static/Typing.v: p_connect");
n("P-Connect.strict", "$\\mathsf{strict}(W_1 \\sqcup W_2)$", "The joined world is strict, $\\prec_{W_1 \\sqcup W_2}$ is irreflexive.", "A cycle in the join lets each component be ready round the cycle while no thread can step.", "With a cyclic join two threads each wait on the other although each side alone is ready.", "The join of two worlds without facts.", "static/Typing.v: p_connect");
n("P-Connect.join", "Result in $W_1 \\sqcup W_2$", "The composite is typed in the join of the two worlds.", "Each component keeps its own facts, and the join contains the facts of both.", DEF, "Two closes land in the join of their two worlds.", "static/Typing.v: p_connect");
n("P-Join.lemma", "Side conditions of P-Join", "$\\mathsf{strict}\\,W_1$, $\\mathsf{strict}\\,W_2$ and $\\mathsf{strict}(W_1|_S \\sqcup W_2|_S)$ with $S$ the shared constants.", "For well-formed worlds these three conditions are equivalent to $\\mathsf{strict}(W_1 \\sqcup W_2)$. Hence P-Join is derivable from P-Connect.", DEF, "Two worlds with no shared constant.", "static/Typing.v: p_join, p_join_iff_connect");
n("guard.judg", "The guard $\\varnothing \\vdash\\!\\triangleright t$", "$\\Lambda \\vdash\\!\\triangleright t$ holds iff the self of every box in $t$ is used only after a session action of the body.", "$\\kappa_L$ makes $\\beta$ free, so without the guard $!(f = \\mathsf{force}\\,f)$ types and diverges on free steps. Deadlock-free typing does not use it.", "$!(f = \\mathsf{force}\\,f)$ types and is in no live relation.", "$!(f = \\lambda x.\\,\\mathsf{let}\\ \\langle v, x'\\rangle = \\mathsf{recv}\\,x\\ \\mathsf{in}\\ (\\mathsf{force}\\,f)\\,x')$ is guarded.", "static/Guard.v: lguard");
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
n("tp.shift", "Shift ${\\uparrow^m}$", "Shifts every point variable of a context, type or future past $m$ fresh point variables.", "The fresh variables get indices $0, \\ldots, m-1$, so existing variables move up by $m$.", DEF, "$\\iota_0{\\uparrow^1} = \\iota_1$.", "types/Points.v: pshift");
n("tp.pinst", "Point instance $T[\\bar x]$", "Replaces the point variables $\\bar\\iota$ of $T$ by the points $\\bar x$.", "Forcing and packing choose concrete points for the bound variables.", DEF, "$(S@\\iota)[\\rho] = S@\\rho$.", "types/Types.v: ty_inst");
n("tp.sinst", "Session instance $U[\\bar s]$", "Replaces the session variables of $U$ by the session types $\\bar s$.", "A box is polymorphic in its session variables, and each force chooses an instance.", DEF, "$({\\alpha}@x)[\\mathsf{Close}] = \\mathsf{Close}@x$.", "types/Types.v: sinst_ty");
n("tp.sinsts", "$\\mathsf{sinsts}\\,N\\,\\bar s$", "Every $s \\in \\bar s$ is hereditarily contractive, and at $N = \\infty$ every $s$ equals its erasure.", "Contractive instances keep unfolding well defined. At $N = \\infty$ the body is typed only at erased instances.", DEF, "$\\mathsf{sinsts}\\,N\\,[\\mathsf{Close}]$.", "static/Contexts.v: sinsts");
n("tp.max", "$\\max(\\vartheta_1, \\vartheta_2)$", "The pointwise maximum of two ticket needs.", "Only one branch of a case runs, so its ticket need is bounded by the larger of the two.", DEF, "$\\max(\\hat 1, \\mathsf{tlink}\\,\\hat 1) = \\mathsf{tlink}\\,\\hat 1$.", "types/Costs.v: fmax, tmax");
n("tp.vdash", "The term turnstile $\\vdash$", "The least relation closed under E-Unit to E-Open, with erased form $\\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W} t : T$, defined as $\\Theta_{df} ; \\Gamma ; \\Delta_{df} \\vdash^{F}_{W,\\infty} t : T_{df}^{a_{df}} \\triangleright \\infty ; (\\infty, \\infty)$ with the annotations of $N = \\infty$. D-Unit to D-Open are lemmas.", "One relation carries the session type, the points, the credit, the cost and the ticket need of $e$, so every mode reads its premises off one derivation.", DEF, "$\\varnothing ; \\varnothing ; \\varnothing \\vdash^{(\\varnothing,\\cdot)}_{W,N} \\ast : \\ast^{\\infty} \\triangleright 0 ; \\hat 1$.", "static/Typing.v: typed, dftyped");
n("tp.tri", "Cost and ticket need $\\triangleright c ; \\vartheta$", "In $e : T^{a} \\triangleright c ; \\vartheta$ the part after $\\triangleright$ states that $e$ performs at most $c$ channel actions before it returns and needs tickets as described by $\\vartheta$.", "The fuel layer reads $c$ to age the frame and $\\vartheta$ to bound the tickets of links.", DEF, "$\\mathsf{send}\\,e : (S@x^{+})^{N} \\triangleright c_0 + 1 ; \\vartheta_0$.", "static/Typing.v: typed");
n("tp.msunion", "Multiset union $E_1 \\uplus E_2$", "$E_1 \\uplus E_2$, the multiset sum, counts every thread as often as $E_1$ and $E_2$ together.", "A composite process runs the threads of both components side by side.", DEF, "$\\{t_1\\} \\uplus \\{t_2\\} = \\{t_1, t_2\\}$.", "lang/Syntax.v: proc");

// ---- signatures and arguments ----
const A = (name, meaning) => ({ name, meaning });
const aTh = A(R`\Theta`, R`the finite map from the ends held by the term to entries $S@x^{a}$`);
const aGa = A(R`\Gamma`, R`the hypotheses, constraint instances $(C, \bar x)$ and future variables $\varphi \mapsto u$`);
const aDe = A(R`\Delta`, R`the de Bruijn list of optional credited types of the variables`);
const aF = A('F', R`the future, the points at which the context acts after the term`);
const aW = A('W', R`the world whose order $\prec_W$ the rule reads`);
const aN = A('N', R`the refill, $N \in \mathbb{N} \cup \{\infty\}$`);
const aE = A('e', R`the term`);
const aT = A(R`T^{a}`, R`the result type $T$ with credit $a \in \mathbb{N} \cup \{\infty\}$`);
const aC = A('c', R`the cost, an upper bound in $\mathbb{N} \cup \{\infty\}$ on the session actions of $e$`);
const aV = A(R`\vartheta`, R`the ticket need of $e$`);
const aX = A('x', R`the point of the end the action is on`);
const aS0 = A(R`S_0`, R`the session type of the end before the action`);
const JG = R`\Theta ; \Gamma ; \Delta \vdash^{F}_{W,N} e : T^{a} \triangleright c ; \vartheta`;
const JA = [aTh, aGa, aDe, aF, aW, aN, aE, aT, aC, aV];
const PJ = R`\Sigma \vdash^{N}_{W} p : T`;
const aSi = A(R`\Sigma`, R`the interface, a finite map from the ends the process offers to its environment to $S@x$`);
const aP = A('p', R`the process $(C, E)$, restricted channels $C$ and a multiset $E$ of threads`);
const aPT = A('T', R`the result type of the main thread`);
const aLam = A(R`\Lambda`, R`the marks, a list mapping each variable to $\mathsf{true}$ (unusable) or $\mathsf{false}$`);
const unf = (k, form) => sa(k, R`\mathsf{unfold}(S_0) = ${form}`, [aS0, A(R`\mathsf{unfold}`, R`the head normal form, which unfolds $\mu$ and removes leading $\mathsf{Skip}$`)]);

sa('tj.Theta', R`\Theta : \mathsf{End} \rightharpoonup_{\mathrm{fin}} \mathsf{Sty} \times \mathsf{Pt} \times (\mathbb{N} \cup \{\infty\})`, [A('o', R`an end $c^{\pm}$ held by the term`), A(R`S@x^{a}`, R`the entry of $o$, its session type $S$, its point $x$ and its credit $a$`)]);
sa('tj.Gamma', R`\Gamma : (\mathsf{Bcs} \times \mathsf{Pt}^{*})^{*} \times (\mathsf{FVar} \rightharpoonup_{\mathrm{fin}} \mathsf{Pt})`, [A(R`(C, \bar x)`, R`a constraint $C$ instantiated at the list of points $\bar x$`), A(R`\varphi \mapsto u`, R`a future variable $\varphi$ with the fact $u \prec \varphi$`)]);
sa('tj.Delta', R`\Delta : (\mathsf{Ty} \times (\mathbb{N} \cup \{\infty\}))_{\bot}^{*}`, [A(R`\Delta(i)`, R`the entry of de Bruijn index $i$, empty or a credited type $T^{a}$`)]);
sa('tj.F', R`F : \mathcal{P}_{\mathrm{fin}}(\mathsf{Pt}) \times (\mathsf{FVar} + \{\bot, \cdot\})`, [A('X', R`the finite set of points the context acts at after the term`), A(R`\varphi`, R`a future variable standing for an unknown set of points above its bound`), A(R`\bot`, R`the flag that the context holds ends at points unknown to the term`)]);
sa('tj.W', R`W : \mathsf{World}`, [A('W', R`a world $(A, \prec_A)$ of roots and facts`)]);
sa('tj.N', R`N \in \mathbb{N} \cup \{\infty\}`, [A('N', R`the credit of a fresh end and of an end after an action on it, $\infty$ for deadlock-free typing`)]);
sa('tj.cost', R`c \in \mathbb{N} \cup \{\infty\}`, [A('c', R`an upper bound on the session actions $e$ performs before it returns`)]);
sa('tj.tix', R`\vartheta : \mathbb{N} \to \mathbb{N} \cup \{\infty\}`, [A('r', R`a reserve, the tickets $e$ must still hold when it returns`), A(R`\vartheta(r)`, R`the tickets $e$ needs to return with $r$ left`)]);
sa('ctx.tsplit', R`\Theta = \Theta_1 \uplus \Theta_2 \iff \mathrm{dom}\,\Theta_1 \cap \mathrm{dom}\,\Theta_2 = \varnothing \land \Theta = \Theta_1 \cup \Theta_2`, [aTh, A(R`\Theta_1, \Theta_2`, R`the ends given to the first and to the second subterm`)]);
sa('ctx.lsplit', R`\Delta = \Delta_1 \sqcup \Delta_2`, [aDe, A(R`\Delta_1, \Delta_2`, R`the variable contexts of the two subterms, of the same length as $\Delta$`), A('i', R`a de Bruijn index, linear entries go to one side, unlimited entries to both`)]);
sa('ctx.hyps', R`(C, \bar x) \in \Gamma`, [A('C', R`a box constraint, a set of facts over $m$ point variables`), A(R`\bar x`, R`the points $C$ is instantiated at, fresh point variables $\bar\iota$ inside a box or an opened existential`)]);
sa('ctx.fvar', R`(\varphi \mapsto u) \in \Gamma`, [A(R`\varphi`, R`a future variable naming the unknown future of a caller`), A('u', R`the upper point of the closure or box, with $u \prec \varphi$`)]);
sa('ctx.fvarF', R`F = (X, \varphi)`, [A(R`\varphi`, R`the variable part of the future`), A('X', R`the known points of the future`)]);
sa('ctx.bot', R`F = (X, \bot)`, [A(R`\bot`, R`the flag that some held end of the context has a point unknown to the term`), A('X', R`the known points of the future`)]);
sa('ctx.slt', R`\Gamma \vdash x \prec y \subseteq \mathsf{Hctx} \times \mathsf{Pt} \times \mathsf{Pt}`, [aGa, A('x, y', R`points, the judgment states that $x$ lies strictly below $y$`)]);
sa('ctx.empty', R`\Delta\ \text{unlimited} \iff \forall i.\ \Delta(i) = \bot \lor \mathsf{unlimited}\,\Delta(i)`, [aDe]);
sa('ctx.only', R`\Delta = \{x : T^{a}\} \iff \Delta(x) = T^{a} \land \forall i \neq x.\ \Delta(i) = \bot \lor \mathsf{unlimited}\,\Delta(i)`, [A('x', R`the de Bruijn index of the variable`), A(R`T^{a}`, R`its credited type`)]);
sa('side.act', R`x \prec F \iff (\forall y \in X.\ \Gamma \vdash x \prec y) \land (F = (X, \varphi) \Rightarrow \Gamma \vdash x \prec \varphi) \land F \neq (X, \bot)`, [aX, aF, aGa]);
sa('act.refill', R`(S@x)^{N}`, [A('S@x', R`the end after the action, at its new point`), aN]);
sa('side.ub', R`u \prec F \iff (\forall y \in X.\ \Gamma \vdash u \prec y) \land (F = (X, \varphi) \Rightarrow \Gamma \vdash u \prec \varphi) \land F \neq (X, \bot)`, [A('u', R`the upper point of a closure or box, the highest point its body waits at`), aF, aGa]);
sa('side.lb', R`l \preccurlyeq H \iff (l = \bot \Rightarrow H = \varnothing) \land \forall y \in H.\ l = y \lor \Gamma \vdash l \prec y`, [A('l', R`a lower point or absent`), A('H', R`a set of heads, partner points of held ends`)]);
sa('side.hold', R`\Gamma \vdash C[\bar x] \iff \forall (y \prec z) \in C[\bar x].\ \Gamma \vdash y \prec z`, [A('C', R`a constraint over $m$ point variables`), A(R`\bar x`, R`a list of $m$ points, the instance`), aGa]);
sa('age.free', R`\mathsf{tfree}\,T \Rightarrow (T, a) - c = (T, a)`, [A('T', R`a type holding no end`), A('a', R`its credit`), A('c', R`the cost of what runs meanwhile`)]);
sa('age.idle', R`\mathsf{idle}\,S \Rightarrow (S@x, a) - c = (S@x, \max(a - c, 0))`, [A('S', R`a session type with $\mathsf{unfold}(S) = \mathsf{Skip}$`), A('x', R`the point of the end`), A('a', R`its credit`), A('c', R`the cost of what runs while the end is held`)]);
sa('age.credit', R`c \leq a \Rightarrow (T, a) - c = (T, a - c)`, [A('T', R`a type holding ends, an end type or an arrow`), A('a', R`its credit`), A('c', R`the cost of what runs while the entry is held`)]);
sa('age.agg', R`(T_1^{a_1} \otimes T_2^{a_2}, a) - c = (T_1'^{a_1'} \otimes T_2'^{a_2'}, 0)`, [A(R`T_i, a_i`, R`the components and their inner credits`), A('a', R`the outer credit, added to each $a_i$ before aging`), A(R`(T_i', a_i')`, R`the aged components, $(T_i, a + a_i) - c = (T_i', a_i')$`)]);
sa('age.ctx', R`\Theta - c,\ \Delta - c`, [A(R`\Theta, \Delta`, R`the ends and variables held while a subterm runs`), A('c', R`the cost of that subterm`)]);
sa('cap.sess', R`h + a \leq a_0 \Rightarrow (S@x, a_0) \leadsto_{h,a} (S@x, h)`, [A('h', R`the floor of the closure, the credit its body may assume of every captured end`), A('a', R`the credit of the closure`), A(R`a_0`, R`the credit of the captured end`)]);
sa('cap.arr', R`h_0 \leq h \land h + a \leq h_0 + a_0 \Rightarrow (T \multimap[\ldots;h_0] U, a_0) \leadsto_{h,a} (\ldots, h - h_0)`, [A(R`h_0`, R`the floor of the captured closure`), A(R`a_0`, R`its credit`), A('h, a', R`the floor and credit of the capturing closure`)]);
sa('sub.tsub', R`T^{a} \leq T'^{a'} \subseteq (\mathsf{Ty} \times \mathsf{Fuel})^{2}`, [A(R`T^{a}`, R`the type and credit a value has`), A(R`T'^{a'}`, R`the type and credit it is used at`)]);
sa('sub.dconv', R`\mathsf{ty\_df}\,T \leq \mathsf{ty\_df}\,T' \Rightarrow (t : T \Rightarrow t : T')`, [A(R`T, T'`, R`erased types`), A('t', R`the term`)]);
sa('tp.sub-credit', R`a' \leq a`, [A('a', R`the credit of the subtype`), A(R`a'`, R`the credit of the supertype`)]);
sa('tp.sub-cost', R`c \leq c' \land \vartheta \leq \vartheta'`, [A(R`c, \vartheta`, R`cost and ticket need of the subtype`), A(R`c', \vartheta'`, R`cost and ticket need of the supertype, pointwise larger`)]);
sa('tp.sub-floor', R`h \leq h' \land h' + a' \leq h + a`, [A('h, a', R`floor and credit of the arrow subtype`), A(R`h', a'`, R`floor and credit of the arrow supertype`)]);
sa('tp.sub-sess', R`S \simeq S'`, [A(R`S, S'`, R`session types at the same point $x$`)]);
sa('tp.sub-ex', R`\mathsf{facts}\,C' \subseteq \mathsf{facts}\,C`, [A('C', R`the constraint of the subtype existential`), A(R`C'`, R`the constraint of the supertype existential, over the same variables`)]);
sa('tp.sub-var', R`T_1'^{a_1'} \leq T_1^{a_1} \land U^{a_2} \leq U'^{a_2'}`, [A(R`T_1, T_1'`, R`the argument types, compared contravariantly`), A(R`U, U'`, R`the result types, compared covariantly`)]);
sa('tp.sub-agg', R`T_i^{a + a_i} \leq T_i'^{a' + a_i'}`, [A('i', R`$1$ or $2$, the component`), A(R`a, a'`, R`the outer credits`), A(R`a_i, a_i'`, R`the inner credits`)]);
sa('tp.sub-teq', R`T \equiv T'`, [A(R`T, T'`, R`types of the same shape whose session types are pairwise $\simeq$`)]);
sa('E-Abs.phi', R`\varphi \notin \mathrm{dom}\,\Gamma`, [A(R`\varphi`, R`the future variable of the body`), aGa]);
sa('E-Abs.lb', R`l \preccurlyeq \mathsf{heads}(\Theta, \Delta) \land \neg\bot_{\Delta}`, [A('l', R`the lower point of the arrow`), A(R`\mathsf{heads}(\Theta, \Delta)`, R`the partner points of every captured end`), A(R`\bot_\Delta`, R`whether $\Delta$ holds an unopened existential at $\bot$`)]);
sa('E-Abs.cap', R`\Theta \leadsto_{h,a} \Theta^{h} \land \Delta \leadsto_{h,a} \Delta^{h}`, [A('h', R`the floor of the arrow`), A('a', R`the credit of the closure`), A(R`\Theta^{h}, \Delta^{h}`, R`the captured context restated at floor $h$`)]);
sa('E-Abs.body', R`\Theta^{h} ; \Gamma, u \prec \varphi ; \Delta^{h}, T^{a_T} \vdash^{(\varnothing, \varphi)}_{W,N} e : U^{a_U} \triangleright c ; \vartheta`, [A(R`T^{a_T}`, R`the argument at index $0$`), A(R`U^{a_U}`, R`the result of the body`), A(R`c, \vartheta`, R`the cost and ticket need recorded on the arrow`)]);
sa('E-App.ub', R`u \prec F`, [A('u', R`the upper point of the arrow type of $e_1$`), aF]);
sa('E-App.fut1', R`\Theta_1 ; \Gamma ; \Delta_1 \vdash^{F \cup \mathsf{heads}(\Theta_2, \Delta_2)}_{W,N} e_1 : \ldots`, [A(R`\Theta_1, \Delta_1`, R`the part of the context given to $e_1$`), A(R`\mathsf{heads}(\Theta_2, \Delta_2)`, R`the partner points of the ends held for the rest of the term`)]);
sa('E-App.fut2', R`\Theta_2' ; \Gamma ; \Delta_2' \vdash^{F \cup \{l\}}_{W,N} e_2 : T^{a_T} \triangleright c_2 ; \vartheta_2`, [A('l', R`the lower point of the closure, held while $e_2$ runs`), A(R`\Theta_2', \Delta_2'`, R`the aged context of $e_2$`)]);
sa('E-App.credit', R`c_2 \leq a_1`, [A(R`c_2`, R`the cost of the argument`), A(R`a_1`, R`the credit of the closure value of $e_1$`)]);
sa('E-App.cost', R`c_1 + c_2 + c`, [A(R`c_1, c_2`, R`the costs of $e_1$ and $e_2$`), A('c', R`the cost of the arrow, the cost of the body`)]);
sa('E-Pair.fut2', R`\ldots \vdash^{F \cup \mathsf{heads}(T_1)}_{W,N} e_2 : T_2^{a_2} \triangleright c_2 ; \vartheta_2`, [A(R`\mathsf{heads}(T_1)`, R`the partner points of the ends of the first component`)]);
sa('E-Pair.age1', R`(T_1, a_1) - c_2 = (T_1', a_1')`, [A(R`T_1^{a_1}`, R`the type of the first component`), A(R`c_2`, R`the cost of the second component`)]);
sa('tp.letp', R`\Theta_2' ; \Gamma ; T_2^{a+a_2}, T_1^{a+a_1}, \Delta_2' \vdash^{F}_{W,N} e_2 : T^{a_T} \triangleright c_2 ; \vartheta_2`, [A(R`T_1^{a_1} \otimes T_2^{a_2}`, R`the type of $e_1$ with outer credit $a$`), A(R`a + a_i`, R`the credit of the bound component`)]);
sa('tp.letu', R`\Theta_2' ; \Gamma ; \Delta_2' \vdash^{F}_{W,N} e_2 : T^{a_T} \triangleright c_2 ; \vartheta_2`, [A(R`\Theta_2', \Delta_2'`, R`the context of $e_2$ aged by the cost $c_1$ of $e_1$`)]);
sa('E-Case.branches', R`\Theta_2' ; \Gamma ; T_i^{a+a_i}, \Delta_2' \vdash^{F}_{W,N} e_i : T^{a_T} \triangleright c_i ; \vartheta_i`, [A('i', R`$1$ or $2$, the branch`), A(R`T_i^{a+a_i}`, R`the payload of injection $i$ at index $0$`)]);
sa('E-Box.unl', R`\Theta = \varnothing \land \forall i.\ \Delta(i) = T^{a} \Rightarrow \mathsf{unlimited}\,T`, [aDe]);
sa('E-Box.inst', R`\forall \bar s.\ |\bar s| = k \land \mathsf{sinsts}\,N\,\bar s \Rightarrow \ldots`, [A(R`\bar s`, R`a list of session types for the $k$ session variables $\bar\alpha$ of the box`), A('k', R`the number of session variables`)]);
sa('E-Box.body', R`\varnothing ; \Gamma{\uparrow^m}, C(\bar\iota), u \prec \varphi ; \Delta{\uparrow^m}, f \vdash^{(\varnothing, \varphi)}_{W,N} e : U[\bar s]^{a_U} \triangleright c ; \vartheta`, [A(R`\bar\iota`, R`the $m$ fresh point variables of the box`), A('f', R`the box itself at index $0$`), A(R`\varphi`, R`the future variable of the caller`)]);
sa('E-Box.open', R`\Gamma{\uparrow^m}, (C, \bar\iota)`, [A(R`\Gamma{\uparrow^m}`, R`$\Gamma$ shifted past $m$ point variables`), A(R`(C, \bar\iota)`, R`the constraint at the fresh variables`)]);
sa('E-Box.self', R`f : \Box(\forall \bar\iota\,\bar\alpha.\ C.\ \ast \multimap^{u}[c;\vartheta]\,U^{a_U})^{\infty}`, [A('f', R`the variable at index $0$ bound to the box itself`)]);
sa('E-Force.hold', R`|\bar x| = m \land \Gamma \vdash C[\bar x]`, [A(R`\bar x`, R`the points the force instantiates $\bar\iota$ with`), A('m', R`the number of point variables of the box`)]);
sa('E-Force.ub', R`u[\bar x] \prec F`, [A(R`u[\bar x]`, R`the upper point of the box at the instance $\bar x$`), aF]);
unf('E-Send.unfold', R`{!}(\bar\iota.\,T).S`);
unf('E-Recv.unfold', R`{?}(\bar\iota.\,T).S`);
unf('E-Close.unfold', R`\mathsf{Close}`);
unf('E-Select.unfold', R`\oplus(S_1, S_2)`);
unf('E-Branch.unfold', R`\&(S_1, S_2)`);
sa('E-Send.nobot', R`\mathsf{hbot}\,T = \mathsf{false}`, [A('T', R`the payload type`), A(R`\mathsf{hbot}`, R`whether an existential at $\bot$ is reachable through $\otimes$ and $\oplus$`)]);
sa('E-Send.heads', R`\forall y \in \mathsf{heads}(T[x \cdot i]).\ \Gamma \vdash x \prec y`, [aX, A(R`T[x\cdot i]`, R`the payload with its $i$-th point variable at the field $x \cdot i$`), A('y', R`a head of the payload`)]);
sa('E-Send.floor', R`(T[x\cdot i], a_0 + a_p) - 1 \leq T[x\cdot i]^{b}`, [A(R`a_0 + a_p`, R`the credit of the payload inside the pair`), A('b', R`the payload credit the protocol asks`)]);
sa('E-Link.dual', R`\ldots \vdash e : (S@x)^{a_1} \otimes (\overline{S}@\overline{x})^{a_2}`, [A('S@x', R`the first linked end`), A(R`\overline{S}@\overline{x}`, R`the second, at the dual type and dual point`)]);
sa('E-SpawnLam.age', R`\Theta' = \Theta - 1 \land \Delta' = \Delta - 1`, [A(R`\Theta, \Delta`, R`the context handed to the child`)]);
sa('E-SpawnLam.body', R`\Theta' ; \Gamma ; \ast^{a_1}, \Delta' \vdash^{(\varnothing, \cdot)}_{W,N} e : \ast^{a_U} \triangleright c' ; \vartheta'`, [A(R`\ast^{a_1}`, R`the unit argument of the thunk`), A(R`c', \vartheta'`, R`cost and ticket need of the child`)]);
sa('E-SpawnLam.future', R`F = (\varnothing, \cdot)`, [A(R`(\varnothing, \cdot)`, R`the future with no point, no variable and no $\bot$`)]);
sa('E-Spawn.credit', R`a \geq 1`, [A('a', R`the credit of the closure value spawned`)]);
sa('E-New.bot', R`\exists^{\bot}`, [A(R`\bot`, R`the lower bound of the existential, no point of the context lies below its ends`)]);
sa('E-New.facts', R`C \subseteq \mathsf{Point} \times \mathsf{Point}`, [A('C', R`the facts of the creation, chosen by the derivation`)]);
sa('E-New.pos', R`\pi \in \mathsf{Point}`, [A(R`\rho`, R`the point variable bound by the existential`), A(R`x, \kappa`, R`a point of the context and a field label`)]);
sa('E-New.strict', R`\mathsf{strict}(\Gamma \cup C) : \mathsf{Prop}`, [A(R`\Gamma`, R`the fact context`), A('C', R`the facts of the creation`)]);
sa('E-New.dual', R`(S@\pi)^{N} \otimes (\overline{S}@\overline{\pi})^{N}`, [A('S', R`any session type, chosen by the derivation`), aN]);
sa('E-Sub.cost', R`c \leq c' \land \vartheta \leq \vartheta'`, [A(R`c, \vartheta`, R`the cost and ticket need derived`), A(R`c', \vartheta'`, R`the weaker ones concluded`)]);
sa('E-Weak.drop', R`\Delta' \preceq_{\mathsf{wk}} \Delta`, [A(R`\Delta'`, R`the context of the premise`), A(R`\Delta`, R`the context of the conclusion, with additional unlimited entries`)]);
sa('E-Pack.lb', R`l = \bot \lor (l \preccurlyeq \mathsf{heads}(T[\bar x]) \land \neg\mathsf{hbot}\,T[\bar x])`, [A('l', R`the lower bound of the existential`), A(R`\bar x`, R`the witness points`)]);
sa('E-Open.entry', R`\Delta(i) = (\exists^{l}\bar\iota.\,C.\,T^{a_T})^{a} \land \neg\mathsf{unlimited}\,T`, [A('i', R`the de Bruijn index of the opened variable`), A(R`a, a_T`, R`the outer and inner credits`)]);
sa('E-Open.body', R`\Theta{\uparrow} ; \Gamma{\uparrow}, C ; \Delta{\uparrow}[i \mapsto T^{a + a_T}] \vdash^{F\uparrow}_{W,N} e : U{\uparrow}`, [A(R`{\uparrow}`, R`the shift past the $m$ fresh point variables of the existential`), A('U', R`the result type, which mentions no opened variable`)]);
sa('pfree', R`\mathsf{pfree}\,\Sigma \iff \forall o \in \mathrm{dom}\,\Sigma.\ \overline{o} \notin \mathrm{dom}\,\Sigma`, [aSi]);
sa('P-Term.C0', R`\forall o.\ o \in \mathrm{dom}\,\Theta_B \iff \mathsf{ech}(o) \in C_0`, [A(R`\Theta_B`, R`the entries of the restricted ends`), A(R`C_0`, R`the restricted channels of the thread`)]);
sa('P-Term.disj', R`\mathsf{chans}\,\Sigma \cap C_0 = \varnothing`, [aSi, A(R`C_0`, R`the restricted channels`)]);
sa('P-Term.pairs', R`\forall c \in C_0.\ \exists S\,x.\ \Theta_B(c^{+}) = S@x^{N} \land \Theta_B(c^{-}) = \overline{S}@\overline{x}^{N}`, [A('c', R`a restricted channel`), A('S, x', R`the type and point of its positive end`)]);
sa('P-Term.typed', R`\Sigma^{N} \cup \Theta_B ; \varnothing ; \varnothing \vdash^{(\varnothing,\cdot)}_{W,N} t : T^{a} \triangleright c ; \vartheta`, [A('t', R`the thread`), A(R`\Sigma^{N}`, R`the interface at credit $N$`)]);
sa('P-Term.future', R`F = (\varnothing, \cdot)`, [A('F', R`the future of a top-level thread`)]);
sa('lf.meets', R`N \in \mathbb{N} \Rightarrow \exists\, tk.\ \mathsf{meets}\,\vartheta\,0\,tk`, [aN, A('tk', R`a ticket count of the thread`), A(R`\vartheta`, R`the ticket need of the thread, read at reserve $0$`)]);
sa('lf.N', R`N \in \mathbb{N}`, [aN]);
sa('P-Connect.left', R`\Sigma_1 \cup \Sigma_C \vdash^{N}_{W_1} (C_1, E_1) : T`, [A(R`\Sigma_1`, R`the interface kept outside`), A(R`\Sigma_C`, R`the cut, the ends connected to the right component`)]);
sa('P-Connect.right', R`\Sigma_2 \cup \overline{\Sigma_C} \vdash^{N}_{W_2} (C_2, E_2) : \ast`, [A(R`\Sigma_2`, R`the interface kept outside`), A(R`\overline{\Sigma_C}`, R`the partners of the cut`)]);
sa('P-Connect.cut', R`\overline{\Sigma_C} = \{\overline{o} \mapsto \overline{S}@\overline{x} \mid (o \mapsto S@x) \in \Sigma_C\}`, [A(R`\Sigma_C`, R`the cut`)]);
sa('P-Connect.disj', R`\mathsf{chans}\,\Sigma_1, \mathsf{chans}\,\Sigma_2, \mathsf{chans}\,\Sigma_C, C_1, C_2\ \text{pairwise disjoint}`, [A(R`C_1, C_2`, R`the restricted channels of the components`)]);
sa('P-Connect.cutfree', R`\mathsf{pfree}\,\Sigma_C`, [A(R`\Sigma_C`, R`the cut`)]);
sa('P-Connect.strict', R`\mathsf{strict}(W_1 \sqcup W_2)`, [A(R`W_1 \sqcup W_2`, R`the join of the two worlds`)]);
sa('P-Connect.join', R`W_1 \sqcup W_2`, [A(R`W_1, W_2`, R`the worlds of the components`)]);
sa('P-Join.lemma', R`\mathsf{strict}\,W_1 \land \mathsf{strict}\,W_2 \land \mathsf{strict}(W_1|_S \sqcup W_2|_S)`, [A('S', R`the constants shared by $W_1$ and $W_2$`), A(R`W|_S`, R`the restriction of $W$ to facts over $S$`)]);
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
sa('tp.shift', R`{\uparrow^m} : X \to X`, [A('m', R`the number of fresh point variables`), A('X', R`a context, type or future`)]);
sa('tp.pinst', R`T[\bar x]`, [A('T', R`a type over the bound point variables $\bar\iota$`), A(R`\bar x`, R`the points substituted, $|\bar x| = |\bar\iota|$`)]);
sa('tp.sinst', R`U[\bar s]`, [A('U', R`a type over the session variables $\bar\alpha$`), A(R`\bar s`, R`the session types substituted`)]);
sa('tp.sinsts', R`\mathsf{sinsts} : \mathsf{Fuel} \to \mathsf{Sty}^{*} \to \mathsf{Prop}`, [aN, A(R`\bar s`, R`a list of session types`)]);
sa('tp.max', R`\max : \mathsf{Tix} \times \mathsf{Tix} \to \mathsf{Tix}`, [A(R`\vartheta_1, \vartheta_2`, R`the ticket needs of the two branches`)]);
sa('tp.vdash', JG, JA);
sa('tp.tri', R`e : T^{a} \triangleright c ; \vartheta`, [aE, aT, aC, aV]);
sa('tp.msunion', R`\uplus : \mathcal{M}(\mathsf{Expr}) \times \mathcal{M}(\mathsf{Expr}) \to \mathcal{M}(\mathsf{Expr})`, [A(R`E_1, E_2`, R`the thread multisets of the two components`)]);
