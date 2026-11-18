const core = require('./core');
const { R, h, n, section, block, DEF } = core;
// premises stack one per line above the bar
const Q = R`\\ `;
const rule = (name, prem, concl) =>
  core.rule(name, prem.startsWith(R`\begin{array}`) ? prem : R`\begin{array}{c}${prem}\end{array}`, concl);
const rows = (...rs) => R`\begin{array}{c}${rs.join(R` \\[2ex] `)}\end{array}`;
const lrows = (...rs) => R`\begin{array}{l}${rs.join(R` \\ `)}\end{array}`;

const s = section('typing', 'Typing',
  'This section introduces the typing judgment, its contexts Θ, Γ, Δ and the future F, the side conditions on points, aging and capture of credits, subtyping, one rule per term former, the process rules P-Term and P-Connect, and the guard. One judgment types sessions and costs at once. Deadlock-free and live typing are its instance N = ∞ with every annotation erased, live typing adds the guard, and lock-free typing uses a finite N.');

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
    live: R`${h('tj.Theta', R`\Theta`)} ; ${h('tj.Gamma', R`\Gamma`)} ; ${h('tj.Delta', R`\Delta`)} \vdash^{${h('tj.F', 'F')}}_{${h('tj.W', 'W')}} t : T \quad\text{and}\quad ${h('guard.judg', R`\varnothing \vdash\!\triangleright t`)}`
  },
  caption: 'Θ holds ends, Γ facts and future hypotheses, Δ variables, F the future. N is the refill, c the cost and ϑ the transformer.'
});
block(s, {
  id: 't-contexts', title: 'Contexts and the fact theory', rocq: 'static/Contexts.v: tentry, tsplit, lenv_split, hctx, fl, sfuture',
  tex: lrows(R`${h('tj.Theta', R`\Theta : o \mapsto S@x^{a}`)} \qquad ${h('ctx.tsplit', R`\Theta = \Theta_1 \uplus \Theta_2`)} \qquad ${h('ctx.lsplit', R`\Delta = \Delta_1 \sqcup \Delta_2`)}`, R`${h('tj.Gamma', R`\Gamma = (${h('ctx.hyps', R`(C, \bar x)^{*}`)}, ${h('ctx.fvar', R`\varphi \mapsto u`)})`)} \qquad ${h('ctx.slt', R`\Gamma \vdash x \prec y`)}`, R`${h('tj.F', R`F = (X, ${h('ctx.fvarF', R`\varphi`)} \mid ${h('ctx.bot', R`\bot`)})`)}`),
  caption: 'Every fact a rule reads comes from Γ ⊢ x ≺ y, the least transitive relation over ≺_W, the instantiated box constraints and u ≺ φ.'
});
block(s, {
  id: 't-side', title: 'Side conditions on points', rocq: 'static/Contexts.v: ub_below_s, lb_below_hb, lbx_below_h, hold_at',
  tex: lrows(h('side.ub', R`u \prec F \iff \forall y \in X.\ \Gamma \vdash u \prec y,\ \Gamma \vdash u \prec \varphi,\ \neg\bot`), R`${h('side.lb', R`l \preccurlyeq H \text{ and } \neg\bot`)} \qquad ${h('side.hold', R`\Gamma \vdash C[\bar x]`)}`),
  caption: 'u ≺ F bounds the future from below, l ≼ H bounds heads from below, and C[x̄] states a constraint at an instance.'
});
block(s, {
  id: 't-age', title: 'Aging Γ − c', rocq: 'static/Contexts.v: tage, lage, thage', modes: ['lf'],
  tex: rows(R`${rule('Age-Free', h('age.free', R`${h('ty.tfree', R`\mathsf{tfree}`)}\,T`), R`(T, a) - c = (T, a)`)} \qquad ${rule('Age-Credit', h('age.credit', R`c \leq a`), R`(T, a) - c = (T, a - c)`)}`, rule('Age-Agg', h('age.agg', R`(T_i, a + a_i) - c = (T_i', a_i')`), R`(T_1^{a_1} \otimes T_2^{a_2}, a) - c = (T_1'^{a_1'} \otimes T_2'^{a_2'}, 0)`)),
  caption: 'Every entry that holds an end must cover the cost of what runs while it is held, and loses it.'
});
block(s, {
  id: 't-cap', title: 'Capture at E-Abs', rocq: 'static/Contexts.v: tcap, thcap', modes: ['lf'],
  tex: rows(rule('Cap-Sess', h('cap.sess', R`h + a \leq a_0`), R`(S@x, a_0) \leadsto_{h,a} (S@x, h)`), rule('Cap-Arr', h('cap.arr', R`h_0 \leq h \quad h + a \leq h_0 + a_0`), R`(T \multimap[\ldots;h_0] U, a_0) \leadsto_{h,a} (\ldots, h - h_0)`)),
  caption: 'A captured end must have credit at least h + a, and the body sees it at exactly the floor h.'
});
block(s, {
  id: 't-sub', title: 'Subtyping', rocq: 'static/Contexts.v: tsub',
  tex: h('sub.tsub', R`\begin{array}{l} T^{a} \leq T'^{a'}:\ a' \leq a,\ c \leq c',\ \vartheta \leq \vartheta',\ h \leq h',\ h' + a' \leq h + a, \\ \quad \text{argument contra, result co},\ S \simeq S',\ \exists \text{ may drop facts}\end{array}`),
  variants: { df: h('sub.dconv', R`\mathsf{D\text{-}Conv}:\ \mathsf{ty\_df}\,T \leq \mathsf{ty\_df}\,T'`), live: h('sub.dconv', R`\mathsf{D\text{-}Conv}:\ \mathsf{ty\_df}\,T \leq \mathsf{ty\_df}\,T'`) },
  caption: 'Credits may fall, costs and transformers may rise, and an existential may forget facts of its constraint.'
});

// ---- term rules ----
const T = (id, title, rocq, merged, erased, caption) => block(s, { id, title, rocq, tex: merged, variants: { df: erased, live: erased }, caption });

T('r-unit', 'E-Unit', 'static/Typing.v: e_unit',
  rule('E-Unit', h('ctx.empty', R`\Delta\ \text{empty}`), J(R`\varnothing`, R`\Gamma`, R`\Delta`, 'F', R`\ast`, R`\ast`, R`\infty`, '0', R`\hat 1`)),
  rule('D-Unit', h('ctx.empty', R`\Delta\ \text{empty}`), DJ(R`\varnothing`, R`\Gamma`, R`\Delta`, 'F', R`\ast`, R`\ast`)),
  'Unit holds no end and costs nothing.');
T('r-var', 'E-Var', 'static/Typing.v: e_var',
  rule('E-Var', h('ctx.only', R`\Delta = \{x : T^{a}\}`), J(R`\varnothing`, R`\Gamma`, R`\Delta`, 'F', 'x', 'T', 'a', '0', R`\hat 1`)),
  rule('D-Var', h('ctx.only', R`\Delta = \{x : T\}`), DJ(R`\varnothing`, R`\Gamma`, R`\Delta`, 'F', 'x', 'T')),
  'A variable is used exactly once. Unlimited entries drop by E-Weak.');
T('r-chan', 'E-Chan', 'static/Typing.v: e_chan',
  rule('E-Chan', h('ctx.empty', R`\Delta\ \text{empty}`), J(R`\{o : S@x^{a}\}`, R`\Gamma`, R`\Delta`, 'F', 'o', R`(S@x)`, 'a', '0', R`\hat 1`)),
  rule('D-Chan', h('ctx.empty', R`\Delta\ \text{empty}`), DJ(R`\{o : S@x\}`, R`\Gamma`, R`\Delta`, 'F', 'o', R`S@x`)),
  'An end value holds exactly its own entry of Θ.');
T('r-abs', 'E-Abs', 'static/Typing.v: e_abs',
  rule('E-Abs', R`${h('E-Abs.phi', R`\varphi\ \text{fresh}`)}${Q}${h('E-Abs.lb', R`l \preccurlyeq \mathsf{heads}(\Theta, \Delta),\ \neg\bot_\Delta`)}${Q}${h('E-Abs.cap', R`\Theta \leadsto_{h,a} \Theta^{h},\ \Delta \leadsto_{h,a} \Delta^{h}`)}${Q}${h('E-Abs.body', J(R`\Theta^{h}`, R`\Gamma, u \prec \varphi`, R`\Delta^{h}, T^{a_T}`, R`(\varnothing, \varphi)`, 'e', 'U', R`a_U`, 'c', R`\vartheta`))}`,
    J(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', R`\lambda e`, R`(T^{a_T} \multimap^{u}_{l}[c;\vartheta;h]\, U^{a_U})`, 'a', '0', R`\hat 1`)),
  rule('D-Abs', R`${h('E-Abs.phi', R`\varphi\ \text{fresh}`)}${Q}${h('E-Abs.lb', R`l \preccurlyeq \mathsf{heads}(\Theta, \Delta),\ \neg\bot_\Delta`)}${Q}${h('E-Abs.body', DJ(R`\Theta`, R`\Gamma, u \prec \varphi`, R`\Delta, T`, R`(\varnothing,\varphi)`, 'e', 'U'))}`,
    DJ(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', R`\lambda e`, R`T \multimap^{u}_{l} U`)),
  'The body runs under an unknown future φ above u. The closure captures all of Θ and Δ, bounded below by l.');
T('r-app', 'E-App', 'static/Typing.v: e_app',
  rule('E-App', R`\begin{array}{c}${h('ctx.tsplit', R`\Theta = \Theta_1 \uplus \Theta_2`)}${Q}${h('ctx.lsplit', R`\Delta = \Delta_1 \sqcup \Delta_2`)}${Q}${h('E-App.ub', R`u \prec F`)} \\ ${h('E-App.fut1', J(R`\Theta_1`, R`\Gamma`, R`\Delta_1`, R`F \cup ${h('ty.heads', R`\mathsf{heads}`)}(\Theta_2,\Delta_2)`, R`e_1`, R`(T^{a_T} \multimap^{u}_{l}[c;\vartheta;h]\,U^{a_U})`, R`a_1`, R`c_1`, R`\vartheta_1`))} \\ ${h('age.ctx', R`\Theta_2' = \Theta_2 - c_1,\ \Delta_2' = \Delta_2 - c_1`)}${Q}${h('E-App.fut2', J(R`\Theta_2'`, R`\Gamma`, R`\Delta_2'`, R`F \cup \{l\}`, R`e_2`, 'T', R`a_T`, R`c_2`, R`\vartheta_2`))} \\ ${h('E-App.credit', R`c_2 \leq a_1`)}${Q}${h('ann.tok', R`\mathsf{tok}`)}\end{array}`,
    J(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', R`e_1\,e_2`, 'U', R`a_U`, h('E-App.cost', R`c_1 + c_2 + c`), R`\vartheta_1 \circ \vartheta_2 \circ \vartheta`)),
  rule('D-App', R`\begin{array}{c}${h('ctx.tsplit', R`\Theta = \Theta_1 \uplus \Theta_2`)}${Q}${h('ctx.lsplit', R`\Delta = \Delta_1 \sqcup \Delta_2`)}${Q}${h('E-App.ub', R`u \prec F`)} \\ ${h('E-App.fut1', DJ(R`\Theta_1`, R`\Gamma`, R`\Delta_1`, R`F \cup ${h('ty.heads', R`\mathsf{heads}`)}(\Theta_2,\Delta_2)`, R`e_1`, R`T \multimap^{u}_{l} U`))}${Q}${h('E-App.fut2', DJ(R`\Theta_2`, R`\Gamma`, R`\Delta_2`, R`F \cup \{l\}`, R`e_2`, 'T'))}\end{array}`,
    DJ(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', R`e_1\,e_2`, 'U')),
  'e₁ runs while the context still holds what e₂ needs, e₂ runs while the closure is held, and the call runs under F.');
T('r-pair', 'E-Pair', 'static/Typing.v: e_pair',
  rule('E-Pair', R`\begin{array}{c}${h('ctx.tsplit', R`\Theta = \Theta_1 \uplus \Theta_2`)}${Q}${h('E-App.fut1', J(R`\Theta_1`, R`\Gamma`, R`\Delta_1`, R`F \cup ${h('ty.heads', R`\mathsf{heads}`)}(\Theta_2,\Delta_2)`, R`e_1`, R`T_1`, R`a_1`, R`c_1`, R`\vartheta_1`))} \\ ${h('age.ctx', R`\Theta_2 - c_1,\ \Delta_2 - c_1`)}${Q}${h('E-Pair.fut2', J(R`\Theta_2'`, R`\Gamma`, R`\Delta_2'`, R`F \cup \mathsf{heads}(T_1)`, R`e_2`, R`T_2`, R`a_2`, R`c_2`, R`\vartheta_2`))}${Q}${h('E-Pair.age1', R`(T_1, a_1) - c_2 = (T_1', a_1')`)}\end{array}`,
    J(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', R`\langle e_1, e_2\rangle`, R`(T_1'^{a_1'} \otimes T_2^{a_2})`, '0', R`c_1 + c_2`, R`\vartheta_1 \circ \vartheta_2`)),
  rule('D-Pair', R`${h('ctx.tsplit', R`\Theta = \Theta_1 \uplus \Theta_2`)}${Q}${h('E-App.fut1', DJ(R`\Theta_1`, R`\Gamma`, R`\Delta_1`, R`F \cup ${h('ty.heads', R`\mathsf{heads}`)}(\Theta_2,\Delta_2)`, R`e_1`, R`T_1`))}${Q}${h('E-Pair.fut2', DJ(R`\Theta_2`, R`\Gamma`, R`\Delta_2`, R`F \cup \mathsf{heads}(T_1)`, R`e_2`, R`T_2`))}`,
    DJ(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', R`\langle e_1, e_2\rangle`, R`T_1 \otimes T_2`)),
  'The first component is held while the second runs.');
T('r-let', 'E-LetU, E-LetP, E-Let', 'static/Typing.v: e_letu, e_letp, e_let',
  rule('E-Let', R`${h('E-App.fut1', J(R`\Theta_1`, R`\Gamma`, R`\Delta_1`, R`F \cup ${h('ty.heads', R`\mathsf{heads}`)}(\Theta_2,\Delta_2)`, R`e_1`, R`T_1`, R`a_1`, R`c_1`, R`\vartheta_1`))}${Q}${h('age.ctx', R`\Theta_2 - c_1,\ \Delta_2 - c_1`)}${Q}${h('E-Let.body', J(R`\Theta_2'`, R`\Gamma`, R`T_1^{a_1}, \Delta_2'`, 'F', R`e_2`, 'T', R`a_T`, R`c_2`, R`\vartheta_2`))}`,
    J(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', h('syn.let', R`\mathsf{let}\ a = e_1\ \mathsf{in}\ e_2`), 'T', R`a_T`, R`c_1 + c_2`, R`\vartheta_1 \circ \vartheta_2`)),
  rule('D-Let', R`${h('E-App.fut1', DJ(R`\Theta_1`, R`\Gamma`, R`\Delta_1`, R`F \cup ${h('ty.heads', R`\mathsf{heads}`)}(\Theta_2,\Delta_2)`, R`e_1`, R`T_1`))}${Q}${h('E-Let.body', DJ(R`\Theta_2`, R`\Gamma`, R`T_1, \Delta_2`, 'F', R`e_2`, 'T'))}`,
    DJ(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', h('syn.let', R`\mathsf{let}\ a = e_1\ \mathsf{in}\ e_2`), 'T')),
  'One shape for the three lets. E-LetP binds the components at credit a + aᵢ.');
T('r-case', 'E-Inj, E-Case', 'static/Typing.v: e_inj1, e_inj2, e_case',
  rule('E-Case', R`${h('E-App.fut1', J(R`\Theta_1`, R`\Gamma`, R`\Delta_1`, R`F \cup ${h('ty.heads', R`\mathsf{heads}`)}(\Theta_2,\Delta_2)`, 'e', R`(T_1^{a_1} \oplus T_2^{a_2})`, 'a', R`c_0`, R`\vartheta_0`))}${Q}${h('E-Case.branches', R`\Theta_2' ; \Gamma ; T_i^{a+a_i}, \Delta_2' \vdash^{F} e_i : T^{a_T} \triangleright c_i ; \vartheta_i`)}`,
    J(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', R`\mathsf{case}\ e\,(e_1)\,(e_2)`, 'T', R`a_T`, R`c_0 + \max(c_1,c_2)`, R`\vartheta_0 \circ ${h('tp.max', R`\max`)}(\vartheta_1,\vartheta_2)`)),
  rule('D-Case', R`${h('E-App.fut1', DJ(R`\Theta_1`, R`\Gamma`, R`\Delta_1`, R`F \cup ${h('ty.heads', R`\mathsf{heads}`)}(\Theta_2,\Delta_2)`, 'e', R`T_1 \oplus T_2`))}${Q}${h('E-Case.branches', R`\Theta_2 ; \Gamma ; T_i, \Delta_2 \vdash^{F} e_i : T`)}`,
    DJ(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', R`\mathsf{case}\ e\,(e_1)\,(e_2)`, 'T')),
  'An injection types at credit 0. Both branches share the context and the result.');
T('r-box', 'E-Box', 'static/Typing.v: e_box',
  rule('E-Box', R`${h('E-Box.unl', R`\Delta\ \text{unlimited}`)}${Q}${h('E-Abs.phi', R`\varphi\ \text{fresh}`)}${Q}${h('E-Box.inst', R`\forall \bar s.\ |\bar s| = k,\ ${h('tp.sinsts', R`\mathsf{sinsts}`)}\,N\,\bar s`)}${Q}${h('E-Box.body', J(R`\varnothing`, h('E-Box.open', R`\Gamma${h('tp.shift', R`{\uparrow^m}`)}, C(\bar\iota), u \prec \varphi`), h('E-Box.self', R`\Delta{\uparrow^m}, f : \Box(\ldots)^{\infty}`), R`(\varnothing,\varphi)`, 'e', h('tp.sinst', R`U[\bar s]`), R`a_U`, 'c', R`\vartheta`))}`,
    J(R`\varnothing`, R`\Gamma`, R`\Delta`, 'F', R`!e`, R`\Box(\forall \bar\iota\,\bar\alpha.\ C.\ \ast \multimap^{u}[c;\vartheta]\,U^{a_U})`, R`\infty`, '0', R`\hat 1`)),
  rule('D-Box', R`${h('E-Box.unl', R`\Delta\ \text{unlimited}`)}${Q}${h('E-Abs.phi', R`\varphi\ \text{fresh}`)}${Q}${h('E-Box.inst', R`\forall \bar s\ (N = \infty\ \text{instances})`)}${Q}${h('E-Box.body', DJ(R`\varnothing`, h('E-Box.open', R`\Gamma${h('tp.shift', R`{\uparrow^m}`)}, C(\bar\iota), u \prec \varphi`), h('E-Box.self', R`\Delta{\uparrow^m}, f : \Box(\ldots)`), R`(\varnothing,\varphi)`, 'e', R`U[\bar s]`))}`,
    DJ(R`\varnothing`, R`\Gamma`, R`\Delta`, 'F', R`!e`, R`\Box(\forall \bar\iota\,\bar\alpha.\ C.\ \ast \multimap^{u} U)`)),
  'The body sees its own box, the constraint as hypotheses, and fresh point variables. It holds no end.');
T('r-force', 'E-Force', 'static/Typing.v: e_force',
  rule('E-Force', R`${h('E-Force.hold', R`|\bar x| = m,\ \Gamma \vdash C[\bar x]`)}${Q}${h('E-Box.inst', R`|\bar s| = k,\ \mathsf{sinsts}\,N\,\bar s`)}${Q}${h('E-Force.ub', R`u[\bar x] \prec F`)}${Q}${J(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', 'e', R`\Box(\forall\bar\iota\,\bar\alpha.\ C.\ \ast\multimap^{u}[c;\vartheta]\,U^{a_U})`, 'a', R`c_0`, R`\vartheta_0`)}`,
    J(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', R`\mathsf{force}\,e`, R`${h('tp.sinst', R`U[\bar s]`)}${h('tp.pinst', R`[\bar x]`)}`, R`a_U`, R`c_0 + c`, R`\vartheta_0 \circ \vartheta`)),
  rule('D-Force', R`${h('E-Force.hold', R`\Gamma \vdash C[\bar x]`)}${Q}${h('E-Force.ub', R`u[\bar x] \prec F`)}${Q}${DJ(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', 'e', R`\Box(\forall\bar\iota\,\bar\alpha.\ C.\ \ast\multimap^{u} U)`)}`,
    DJ(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', R`\mathsf{force}\,e`, R`U[\bar s][\bar x]`)),
  'Forcing picks an instance that meets the constraint and runs the body under the caller\'s future.');
T('r-send', 'E-Send', 'static/Typing.v: e_send',
  rule('E-Send', R`\begin{array}{c}${h('E-Send.unfold', R`${h('sty.unfold', R`\mathsf{unfold}`)}(S_0) = {!}(\exists^{m}.\,T^{b});S`)}${Q}${h('ty.pscoped', R`\mathsf{pscoped}\,m\,T`)}${Q}${h('E-Send.nobot', R`\neg\mathsf{hbot}\,T`)} \\ ${h('E-Send.heads', R`\forall y \in \mathsf{heads}(${h('ty.payload-at', R`T[x\cdot i]`)}).\ \Gamma \vdash x \prec y`)}${Q}${act}${Q}${J(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', 'e', R`(T[x\cdot i]^{a_p} \otimes (S_0@x)^{a_S})`, R`a_0`, R`c_0`, R`\vartheta_0`)} \\ ${h('E-Send.floor', R`(T[x\cdot i], a_0 + a_p) - 1 \leq T[x\cdot i]^{b}`)}\end{array}`,
    J(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', R`\mathsf{send}\,e`, R`(S@${h('pt.shift', R`x^{+}`)})`, h('act.refill', 'N'), R`c_0 + 1`, R`\vartheta_0`)),
  rule('D-Send', R`${h('E-Send.unfold', R`${h('sty.unfold', R`\mathsf{unfold}`)}(S_0) = {!}(\exists^{m}.\,T);S`)}${Q}${h('ty.pscoped', R`\mathsf{pscoped}\,m\,T`)}${Q}${h('E-Send.nobot', R`\neg\mathsf{hbot}\,T`)}${Q}${h('E-Send.heads', R`x \prec \mathsf{heads}(T[x\cdot i])`)}${Q}${act}${Q}${DJ(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', 'e', R`T[x\cdot i] \otimes S_0@x`)}`,
    DJ(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', R`\mathsf{send}\,e`, R`S@${h('pt.shift', R`x^{+}`)}`)),
  'The payload is held while the sender blocks at x, so x lies below its heads. The end returns at x⁺ with the refill N.');
T('r-recv', 'E-Recv', 'static/Typing.v: e_recv',
  rule('E-Recv', R`${h('E-Recv.unfold', R`${h('sty.unfold', R`\mathsf{unfold}`)}(S_0) = {?}(\exists^{m}.\,T^{b});S`)}${Q}${h('ty.pscoped', R`\mathsf{pscoped}\,m\,T`)}${Q}${act}${Q}${J(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', 'e', R`(S_0@x)`, 'a', R`c_0`, R`\vartheta_0`)}`,
    J(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', R`\mathsf{recv}\,e`, R`(T[x\cdot i]^{${h('sty.payload-credit', 'b')}} \otimes ${refill(R`S@${h('pt.shift', R`x^{+}`)}`)})`, '0', R`c_0 + 1`, R`\vartheta_0`)),
  rule('D-Recv', R`${h('E-Recv.unfold', R`${h('sty.unfold', R`\mathsf{unfold}`)}(S_0) = {?}(\exists^{m}.\,T);S`)}${Q}${h('ty.pscoped', R`\mathsf{pscoped}\,m\,T`)}${Q}${act}${Q}${DJ(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', 'e', R`S_0@x`)}`,
    DJ(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', R`\mathsf{recv}\,e`, R`T[x\cdot i] \otimes S@${h('pt.shift', R`x^{+}`)}`)),
  'The payload arrives at its floor b and at the payload fields of x.');
T('r-close', 'E-Close', 'static/Typing.v: e_close',
  rule('E-Close', R`${h('E-Close.unfold', R`${h('sty.unfold', R`\mathsf{unfold}`)}(S_0) = \mathsf{Close}`)}${Q}${act}${Q}${J(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', 'e', R`(S_0@x)`, 'a', R`c_0`, R`\vartheta_0`)}`,
    J(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', R`\mathsf{close}\,e`, R`\ast`, R`\infty`, R`c_0 + 1`, R`\vartheta_0`)),
  rule('D-Close', R`${h('E-Close.unfold', R`${h('sty.unfold', R`\mathsf{unfold}`)}(S_0) = \mathsf{Close}`)}${Q}${act}${Q}${DJ(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', 'e', R`S_0@x`)}`,
    DJ(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', R`\mathsf{close}\,e`, R`\ast`)),
  'A close is an action at x and costs one.');
T('r-select', 'E-Select', 'static/Typing.v: e_select',
  rule('E-Select', R`${h('E-Select.unfold', R`${h('sty.unfold', R`\mathsf{unfold}`)}(S_0) = \oplus(S_1,S_2)`)}${Q}${h('E-Select.order', R`\Gamma \vdash x \prec x\cdot\kappa_i`)}${Q}${act}${Q}${J(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', 'e', R`(S_0@x)`, 'a', R`c_0`, R`\vartheta_0`)}`,
    J(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', R`\mathsf{select}_i\,e`, R`(S_i@${h('pt.sel', R`\overline{x\cdot\kappa_i}`)})`, h('act.refill', 'N'), R`c_0 + 1`, R`\vartheta_0`)),
  rule('D-Select', R`${h('E-Select.unfold', R`${h('sty.unfold', R`\mathsf{unfold}`)}(S_0) = \oplus(S_1,S_2)`)}${Q}${h('E-Select.order', R`\Gamma \vdash x \prec x\cdot\kappa_i`)}${Q}${act}${Q}${DJ(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', 'e', R`S_0@x`)}`,
    DJ(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', R`\mathsf{select}_i\,e`, R`S_i@${h('pt.sel', R`\overline{x\cdot\kappa_i}`)}`)),
  'The selecting end continues at (x·κᵢ)‾. Its partner point x·κᵢ must lie above x.');
T('r-branch', 'E-Branch', 'static/Typing.v: e_branch',
  rule('E-Branch', R`${h('E-Branch.unfold', R`${h('sty.unfold', R`\mathsf{unfold}`)}(S_0) = \&(S_1,S_2)`)}${Q}${h('E-Branch.order', R`\Gamma \vdash x \prec \overline{x\cdot\kappa_1},\ x \prec \overline{x\cdot\kappa_2}`)}${Q}${act}${Q}${J(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', 'e', R`(S_0@x)`, 'a', R`c_0`, R`\vartheta_0`)}`,
    J(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', R`\mathsf{branch}\,e`, R`((S_1@${h('pt.bra', R`x\cdot\kappa_1`)})^{N} \oplus (S_2@x\cdot\kappa_2)^{N})`, '0', R`c_0 + 1`, R`\vartheta_0`)),
  rule('D-Branch', R`${h('E-Branch.unfold', R`${h('sty.unfold', R`\mathsf{unfold}`)}(S_0) = \&(S_1,S_2)`)}${Q}${h('E-Branch.order', R`\Gamma \vdash x \prec \overline{x\cdot\kappa_i}`)}${Q}${act}${Q}${DJ(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', 'e', R`S_0@x`)}`,
    DJ(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', R`\mathsf{branch}\,e`, R`S_1@${h('pt.bra', R`x\cdot\kappa_1`)} \oplus S_2@x\cdot\kappa_2`)),
  'The branching end continues at x·κᵢ. Its partner point (x·κᵢ)‾ must lie above x for both i.');
T('r-link', 'E-Link', 'static/Typing.v: e_link',
  rule('E-Link', R`${h('E-Link.dual', J(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', 'e', R`((S@x)^{a_1} \otimes (\overline{S}@\overline{x})^{a_2})`, R`a_0`, R`c_0`, R`\vartheta_0`))}${Q}${h('ann.tok', R`\mathsf{tok}`)}`,
    J(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', R`\mathsf{link}\,e`, R`\ast`, R`\infty`, R`c_0`, R`\vartheta_0 \circ ${h('ann.tlink', R`\mathsf{tlink}\,\hat 1`)}`)),
  rule('D-Link', h('E-Link.dual', DJ(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', 'e', R`S@x \otimes \overline{S}@\overline{x}`)),
    DJ(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', R`\mathsf{link}\,e`, R`\ast`)),
  'A link asks no future fact and costs no action. It spends one ticket.');
T('r-spawnlam', 'E-SpawnLam', 'static/Typing.v: e_spawn_lam',
  rule('E-SpawnLam', R`${h('E-SpawnLam.age', R`\Theta' = \Theta - 1,\ \Delta' = \Delta - 1`)}${Q}${h('E-SpawnLam.body', J(R`\Theta'`, R`\Gamma`, R`\ast^{a_1}, \Delta'`, h('E-SpawnLam.future', R`(\varnothing, \cdot)`), 'e', R`\ast`, R`a_U`, R`c'`, R`\vartheta'`))}`,
    J(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', R`\mathsf{spawn}\,(\lambda e)`, R`\ast`, R`\infty`, '0', h('ann.tspawn', R`\mathsf{tspawn}(\vartheta'(0))\,\hat 1`))),
  rule('D-SpawnLam', h('E-SpawnLam.body', DJ(R`\Theta`, R`\Gamma`, R`\ast, \Delta`, h('E-SpawnLam.future', R`(\varnothing, \cdot)`), 'e', R`\ast`)),
    DJ(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', R`\mathsf{spawn}\,(\lambda e)`, R`\ast`)),
  'Spawning a λ directly asks no lower point. The child starts at the empty future with every handed end one unit lower.');
T('r-spawn', 'E-Spawn', 'static/Typing.v: e_spawn',
  rule('E-Spawn', R`${J(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', 'e', R`(\ast^{a_1} \multimap^{u}_{l}[c';\vartheta';h]\,\ast^{a_U})`, 'a', R`c_0`, R`\vartheta_0`)}${Q}${h('E-Spawn.credit', R`a \geq 1`)}${Q}${h('ann.tok', R`\mathsf{tok}`)}`,
    J(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', R`\mathsf{spawn}\,e`, R`\ast`, R`\infty`, R`c_0`, R`\vartheta_0 \circ ${h('ann.tspawn', R`\mathsf{tspawn}(\vartheta'(0))\,\hat 1`)}`)),
  rule('D-Spawn', DJ(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', 'e', R`\ast \multimap^{u}_{l} \ast`), DJ(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', R`\mathsf{spawn}\,e`, R`\ast`)),
  'Spawning a closure value hands over its captured ends, which must have one unit to spare.');
T('r-new', 'E-New', 'static/Typing.v: e_new',
  rule('E-New', R`${h('ctx.empty', R`\Delta\ \text{empty}`)}${Q}${h('E-New.fam', R`\ell \in L_W`)}`,
    J(R`\varnothing`, R`\Gamma`, R`\Delta`, 'F', R`\mathsf{new}_\ell`, R`(\exists^{${h('E-New.bot', R`\bot`)}}\rho.\ ${h('E-New.laws', R`\Lambda_\ell(\rho)`)}.\ ${h('E-New.dual', R`((S@\rho)^{N} \otimes (\overline{S}@\overline{\rho})^{N})`)}^{0})`, '0', '0', R`\hat 1`)),
  rule('D-New', R`${h('ctx.empty', R`\Delta\ \text{empty}`)}${Q}${h('E-New.fam', R`\ell \in L_W`)}`,
    DJ(R`\varnothing`, R`\Gamma`, R`\Delta`, 'F', R`\mathsf{new}_\ell`, R`\exists^{${h('E-New.bot', R`\bot`)}}\rho.\ ${h('E-New.laws', R`\Lambda_\ell(\rho)`)}.\ ${h('E-New.dual', R`S@\rho \otimes \overline{S}@\overline{\rho}`)}`)),
  'A fresh root opens with the laws of its family. The context does not know it, hence the ⊥ bound.');
T('r-newat', 'E-NewAt', 'static/Typing.v: e_new_at',
  rule('E-NewAt', h('E-NewAt.anchor', J(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', 'e', R`(S_0@x)`, 'a', R`c_0`, R`\vartheta_0`)),
    J(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', R`\mathsf{new}_\kappa\,e`, R`((S_0@x)^{a} \otimes ${h('E-NewAt.field', R`((S@x\cdot\kappa)^{N} \otimes (\overline{S}@\overline{x\cdot\kappa})^{N})`)}^{0})`, '0', R`c_0`, R`\vartheta_0`)),
  rule('D-NewAt', h('E-NewAt.anchor', DJ(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', 'e', R`S_0@x`)),
    DJ(R`\Theta`, R`\Gamma`, R`\Delta`, 'F', R`\mathsf{new}_\kappa\,e`, R`S_0@x \otimes ${h('E-NewAt.field', R`(S@x\cdot\kappa \otimes \overline{S}@\overline{x\cdot\kappa})`)}`)),
  'The anchor comes back unchanged. The channel sits at its field κ, where box constraints or W supply the facts.');
T('r-struct', 'E-Sub, E-Weak, E-Contract', 'static/Typing.v: e_sub, e_weak, e_contract',
  rows(rule('E-Sub', R`e : T^{a} \triangleright c ; \vartheta${Q}${h('sub.tsub', R`T^{a} \leq T'^{a'}`)}${Q}${h('E-Sub.cost', R`c \leq c',\ \vartheta \leq \vartheta'`)}`, R`e : T'^{a'} \triangleright c' ; \vartheta'`), rule('E-Weak', h('E-Weak.drop', R`\Delta' \preceq_{\mathsf{wk}} \Delta`), R`\Delta' \vdash e \Rightarrow \Delta \vdash e`), rule('E-Contract', h('ty.unlimited', R`\mathsf{unlimited}\,U`), R`U, U, \Delta \vdash e \Rightarrow U, \Delta \vdash e[x/x']`)),
  rows(rule('D-Conv', h('sub.dconv', R`${h('ann.tydf', R`\mathsf{ty\_df}`)}\,T \leq \mathsf{ty\_df}\,T'`), R`t : T \Rightarrow t : T'`), rule('D-Weak', h('E-Weak.drop', R`\Delta' \preceq_{\mathsf{wk}} \Delta`), R`\Delta' \vdash t \Rightarrow \Delta \vdash t`), rule('D-Contract', h('ty.unlimited', R`\mathsf{unlimited}\,U`), R`U, U, \Delta \vdash t \Rightarrow U, \Delta \vdash t`)),
  'Weakening and contraction apply to box variables only.');
T('r-ex', 'E-Pack, E-Open', 'static/Typing.v: e_pack, e_open',
  rows(rule('E-Pack', R`${h('E-Force.hold', R`|\bar x| = m,\ \Gamma \vdash C[\bar x]`)}${Q}${h('E-Pack.lb', R`l \preccurlyeq \mathsf{heads}(${h('tp.pinst', R`T[\bar x]`)})`)}${Q}e : T[\bar x]^{a}`, R`e : (\exists^{l}\bar\iota.\,C.\,T^{a})^{0}`), rule('E-Open', R`${h('E-Open.entry', R`\Delta(i) = (\exists^{l}\bar\iota.\,C.\,T^{a_T})^{a},\ \neg\mathsf{unlimited}\,T`)}${Q}${h('E-Open.body', R`\Theta${h('tp.shift', R`{\uparrow}`)}; \Gamma{\uparrow}, C; \Delta{\uparrow}[i \mapsto T^{a+a_T}] \vdash^{F\uparrow} e : U{\uparrow}`)}`, R`\Theta;\Gamma;\Delta \vdash^{F} e : U`)),
  rows(rule('D-Pack', R`${h('E-Force.hold', R`\Gamma \vdash C[\bar x]`)}${Q}${h('E-Pack.lb', R`l \preccurlyeq \mathsf{heads}(${h('tp.pinst', R`T[\bar x]`)})`)}${Q}t : T[\bar x]`, R`t : \exists^{l}\bar\iota.\,C.\,T`), rule('D-Open', R`${h('E-Open.entry', R`\Delta(i) = \exists^{l}\bar\iota.\,C.\,T`)}${Q}${h('E-Open.body', R`\Theta${h('tp.shift', R`{\uparrow}`)}; \Gamma{\uparrow}, C; \Delta{\uparrow}[i \mapsto T] \vdash t : U{\uparrow}`)}`, R`\Theta;\Gamma;\Delta \vdash t : U`)),
  'Packing picks a witness that meets C. Opening a variable adds fresh point variables with C as hypotheses.');

// ---- process rules ----
block(s, {
  id: 'p-term', title: 'P-Term', rocq: 'static/Typing.v: p_term, soup/LFTyped.v: lf_term',
  tex: rule('P-Term', R`\begin{array}{c}${h('ty.prim', R`\mathsf{prim}\,T`)}${Q}${h('P-Term.C0', R`\mathsf{dom}\,\Theta_B = ${h('tp.ends', R`\mathsf{ends}`)}(C_0)`)}${Q}${h('P-Term.disj', R`${h('tp.chans', R`\mathsf{chans}`)}\,${h('tp.Sigma', R`\Sigma`)} \cap C_0 = \varnothing`)}${Q}${h('pfree', R`\mathsf{pfree}\,\Sigma`)} \\ ${h('P-Term.pairs', R`\forall c \in C_0.\ \Theta_B(c^{+}) = S@x^{\infty},\ \Theta_B(c^{-}) = \overline{S}@\overline{x}^{\infty}`)} \\ ${h('P-Term.typed', R`${h('tp.lift', R`\Sigma^{\infty}`)} \cup \Theta_B ; \varnothing ; \varnothing \vdash^{${h('P-Term.future', R`(\varnothing,\cdot)`)}}_{W,\infty} t : T^{a} \triangleright c ; \vartheta`)}\end{array}`, R`\Sigma ${h('tp.pjudg', R`\vdash_W`)} (C_0, \{t\}) : T`),
  variants: {
    lf: rule('lf_term', R`\begin{array}{c}${h('ty.prim', R`\mathsf{prim}\,T`)}${Q}${h('P-Term.C0', R`\mathsf{dom}\,\Theta_B = \mathsf{ends}(C_0)`)}${Q}${h('P-Term.disj', R`\mathsf{chans}\,\Sigma \cap C_0 = \varnothing`)}${Q}${h('pfree', R`\mathsf{pfree}\,\Sigma`)} \\ ${h('P-Term.pairs', R`\forall c \in C_0.\ \Theta_B(c^{+}) = S@x^{N},\ \Theta_B(c^{-}) = \overline{S}@\overline{x}^{N}`)} \\ ${h('lf.typedN', R`\Sigma^{N} \cup \Theta_B ; \varnothing ; \varnothing \vdash^{${h('P-Term.future', R`(\varnothing,\cdot)`)}}_{W,${h('lf.N', 'N')}} t : T^{a} \triangleright c ; \vartheta`)}${Q}${h('guard.judg', R`\varnothing \vdash\!\triangleright t`)}${Q}${h('lf.meets', R`${h('ann.meets', R`\mathsf{meets}`)}\,\vartheta\,0\,${h('fu.tk', 'tk')}`)}\end{array}`, R`\Sigma ${h('tp.lfjudg', R`\Vdash^{N}_W`)} (C_0, \{t\}) : T`)
  },
  caption: 'A single thread with the channels C₀ restricted. Its interface Σ holds no partner pair, and the thread holds both ends of every channel of C₀.'
});
block(s, {
  id: 'p-connect', title: 'P-Connect', rocq: 'static/Typing.v: p_connect, soup/LFTyped.v: lf_connect',
  tex: rule('P-Connect', R`\begin{array}{c}${h('P-Connect.left', R`\Sigma_1 \cup \Sigma_C \vdash_{W_1} (C_1, E_1) : T`)}${Q}${h('P-Connect.right', R`\Sigma_2 \cup ${h('P-Connect.cut', R`\overline{\Sigma_C}`)} \vdash_{W_2} (C_2, E_2) : \ast`)} \\ ${h('P-Connect.disj', R`\text{ends and channels apart}`)}${Q}${h('P-Connect.cutfree', R`\mathsf{pfree}\,\Sigma_C`)}${Q}${h('w.wf', R`\mathsf{world\_wf}\,W_1, W_2`)}${Q}${h('P-Connect.fams', R`${h('w.fams', 'L_1')} \cap L_2 = \varnothing`)}${Q}${h('P-Connect.strict', R`${h('w.strict', R`\mathsf{strict}`)}(W_1 \sqcup W_2)`)}\end{array}`, R`\begin{array}{c}\Sigma_1 \cup \Sigma_2 \vdash_{${h('P-Connect.join', R`W_1 ${h('w.join', R`\sqcup`)} W_2`)}} \\ (C_1 \cup C_2 \cup ${h('tp.chans', R`\mathsf{chans}`)}\,\Sigma_C, E_1 \uplus E_2) : T\end{array}`),
  variants: {
    lf: rule('lf_connect', R`\begin{array}{c}${h('P-Connect.left', R`\Sigma_1 \cup \Sigma_C \Vdash^{N}_{W_1} (C_1, E_1) : T`)}${Q}${h('P-Connect.right', R`\Sigma_2 \cup ${h('P-Connect.cut', R`\overline{\Sigma_C}`)} \Vdash^{N}_{W_2} (C_2, E_2) : \ast`)} \\ ${h('P-Connect.disj', R`\text{ends and channels apart}`)}${Q}${h('P-Connect.cutfree', R`\mathsf{pfree}\,\Sigma_C`)}${Q}${h('w.wf', R`\mathsf{world\_wf}\,W_1, W_2`)}${Q}${h('P-Connect.fams', R`${h('w.fams', 'L_1')} \cap L_2 = \varnothing`)}${Q}${h('P-Connect.strict', R`${h('w.strict', R`\mathsf{strict}`)}(W_1 \sqcup W_2)`)}\end{array}`, R`\begin{array}{c}\Sigma_1 \cup \Sigma_2 \Vdash^{N}_{${h('P-Connect.join', R`W_1 \sqcup W_2`)}} \\ (C_1 \cup C_2 \cup \mathsf{chans}\,\Sigma_C, E_1 \uplus E_2) : T\end{array}`)
  },
  caption: 'Two components, each in its own world, cut at Σ_C against its exact dual. The main thread lives on the left.'
});
block(s, {
  id: 'p-join', title: 'P-Join (admissible)', rocq: 'static/Typing.v: p_join, soup/LFTyped.v: lf_join',
  tex: rule('P-Join', R`\begin{array}{c}\text{premises of P-Connect with} \\ ${h('P-Join.lemma', R`\mathsf{strict}\,W_1,\ \mathsf{strict}\,W_2,\ \mathsf{strict}(${h('w.restrict', R`W_1|_S`)} \sqcup W_2|_S)`)}\end{array}`, R`\begin{array}{c}\Sigma_1 \cup \Sigma_2 \vdash_{W_1 \sqcup W_2} \\ (C_1 \cup C_2 \cup \mathsf{chans}\,\Sigma_C, E_1 \uplus E_2) : T\end{array}`),
  caption: 'A lemma, not a rule. Strictness of each world and of the join of their shared parts is the same as strictness of the whole join, so P-Connect covers it.'
});
block(s, {
  id: 'g-acts', title: 'Terms that act', rocq: 'static/Guard.v: sprim, acts',
  modes: ['live', 'lf'],
  tex: h('guard.acts', R`\begin{array}{l}\mathsf{acts}\,e \iff e \text{ contains, in evaluation position,} \\ \quad \text{an operator } k \in \{\mathsf{send}, \mathsf{recv}, \mathsf{close}, \mathsf{select}_i, \mathsf{branch}\}\end{array}`),
  caption: 'An acting term performs a channel action before it returns.'
});
block(s, {
  id: 'g-rules', title: 'The guard Λ ⊢▷ t', rocq: 'static/Guard.v: lguard',
  modes: ['live', 'lf'],
  tex: R`\begin{array}{c}
${rule('gl_var', h('guard.var', R`\Lambda(y) = \mathsf{false}`), R`${h('guard.marks', R`\Lambda`)} \vdash\!\triangleright y`)} \quad ${rule('gl_lam', h('guard.lam', R`\mathsf{false}.\Lambda \vdash\!\triangleright b`), R`\Lambda \vdash\!\triangleright \lambda b`)} \quad ${rule('gl_box', h('guard.box', R`\mathsf{true}.\Lambda \vdash\!\triangleright b`), R`\Lambda \vdash\!\triangleright\ !b`)} \\[2ex]
${rule('gl_app', h('guard.cong', R`\Lambda \vdash\!\triangleright e_1 \quad \Lambda \vdash\!\triangleright e_2`), R`\Lambda \vdash\!\triangleright e_1\,e_2`)} \quad ${rule('gl_tick_app', R`\Lambda \vdash\!\triangleright e_1${Q}${h('guard.acts', R`\mathsf{acts}\,e_1`)}${Q}${h('guard.tick', R`\varnothing \vdash\!\triangleright e_2`)}`, R`\Lambda \vdash\!\triangleright e_1\,e_2`)} \\[2ex]
${rule('gl_let', h('guard.bind', R`\Lambda \vdash\!\triangleright e_1 \quad \mathsf{false}.\Lambda \vdash\!\triangleright e_2`), R`\Lambda \vdash\!\triangleright \mathsf{let}\ a = e_1\ \mathsf{in}\ e_2`)}
\end{array}`,
  caption: 'Guarded recursion. A box puts its self at ▷, a marked variable cannot be used, and an acting term clears every mark for what runs after it.'
});
block(s, {
  id: 'g-proc', title: 'Guard of a process', rocq: 'static/FundamentalProc.v: pguard',
  modes: ['live', 'lf'],
  tex: h('guard.proc', R`\vdash\!\triangleright p \iff \forall t \in p.\ \varnothing \vdash\!\triangleright t`),
  caption: 'Every thread is guarded with no marks.'
});

// ---- notes ----
n('tj.Theta', 'Θ, the end environment', 'Maps each held end to its session type, point and credit, one entry per end.', 'B9. One entry per end replaces the One and Both entries keyed by a side bit (K3).', DEF, '{a : Sa@ρ^N, b : Sb@ρ·0^N}.', 'static/Contexts.v: tentry, tenv');
n('tj.Gamma', 'Γ, facts and future hypotheses', 'The box constraints in force with their instances, and future variables φ with an upper point u ≺ φ.', 'A.5. One Γ replaces the two hypothesis contexts Φ and Ψ of the old typed.', DEF, 'Inside cli, Γ holds C at (ι, κ, ζ).', 'static/Contexts.v: hctx');
n('tj.Delta', 'Δ, the variable context', 'A de Bruijn list of optional credited types T^a.', 'Not documented.', DEF, '[Some (S1@ι ⊗ S2@κ, 0)].', 'static/Contexts.v: lenv');
n('tj.F', 'Future F', 'The points the context still acts on after the term, with a future variable φ or the ⊥ flag.', 'Inventory row S4 and proposal §2.16. Every action at x asks x ≺ F, so the term never blocks above something its context must do first.', 'Without futures, e₁ in let ∗ = close c in close d could block above d, which the context holds, a circular wait within one thread.', 'e₁ of E-App runs under F ∪ heads(Θ₂, Δ₂).', 'static/Contexts.v: sfuture');
n('tj.W', 'World W', 'The world whose order and families the rule reads.', 'Not documented beyond §2.4.', DEF, 'E-New asks ℓ ∈ L_W.', 'static/Typing.v: typed W');
n('tj.N', 'Refill N', 'The credit of a fresh end and of an end after an action. DF typing is N = ∞, lock-free typing a finite N.', 'Q4 and Q11. One refill per judgment, the maximum at composition.', DEF, 'LFClientServer types at N = 3.', 'static/Typing.v: typed N');
n('tj.cost', 'Cost c', 'An upper bound on the channel actions the term performs before it returns.', 'Q11, from the old cost judgment. Read only by fuel.', DEF, 'send e costs c₀ + 1.', 'static/Typing.v: typed c');
n('tj.tix', 'Transformer ϑ', 'The ticket transformer of the term.', 'F13 and T2.', DEF, 'link e has ϑ₀ ∘ tlink 1̂.', 'static/Typing.v: typed ϑ');
n('ctx.tsplit', 'Θ = Θ₁ ⊎ Θ₂', 'A disjoint split of the ends.', 'Ends are never shared.', DEF, 'E-App splits the ends of e₁ and e₂.', 'static/Contexts.v: tsplit');
n('ctx.lsplit', 'Δ split', 'Each linear variable goes left or right. Unlimited ones go both ways.', 'Not documented.', DEF, 'A box variable may occur in both halves.', 'static/Contexts.v: lenv_split');
n('ctx.hyps', 'Hypotheses', 'Pairs of a box constraint and an instance, from E-Box, E-Open and E-New.', 'Not documented.', DEF, '(C, [ι; κ; ζ]) inside a box body.', 'static/Contexts.v: hyps, hc_open');
n('ctx.fvar', 'Future variables', 'φ ↦ u records u ≺ φ. A body under φ runs under an unknown future above u.', 'E-Abs and E-Box name the future of the caller by a variable (proposal §2.16).', DEF, 'λ-body under (∅, φ) with u ≺ φ.', 'static/Contexts.v: hc_fvar');
n('ctx.fvarF', 'Future variable in F', 'The unknown part of a future, read through Γ ⊢ u ≺ φ.', 'Semantically φ stands for an arbitrary set (sf_den, progress.md S4 static futures).', DEF, 'F = (∅, φ).', 'static/Contexts.v: futrest');
n('ctx.bot', '⊥ flag in F', 'The context holds ends whose points are hidden. A term under ⊥ performs no session action.', 'Every action asks ub_below_s, which asks the flag off. Semantically ⊥ stands for an arbitrary set B (progress.md, S4 static futures).', DEF, 'e₁ under a context holding an unopened ∃^⊥.', 'static/Contexts.v: FBot, fs_bot');
n('ctx.slt', 'Γ ⊢ x ≺ y', 'The least transitive relation over ≺_W, the facts of the hypotheses and u ≺ φ.', 'Every fact a rule reads comes from here (comment in Contexts.v).', DEF, 'Γ ⊢ x ≺ x⁺ always.', 'static/Contexts.v: fl, slt');
n('ctx.empty', 'Δ empty', 'Every entry of Δ is None.', 'Values with no variable use none.', DEF, '∗ types in any Δ of Nones.', 'static/Contexts.v: lenv_empty');
n('ctx.only', 'Δ = {x : T^a}', 'x is the only entry of Δ.', 'Linearity. E-Weak drops unlimited entries first.', DEF, 'Var 0 in [Some T].', 'static/Contexts.v: lenv_only');
n('side.act', 'x ≺ F at an action', 'An action at x lies below every point of the future and below the future variable, and the ⊥ flag is off.', 'Readiness against the future (B2). It is the static form of below_rest against F.', 'A term that blocks at x while its context must still act at a point below x waits on itself through the partner.', 'E-Close asks x ≺ F.', 'static/Contexts.v: ub_below_s');
n('act.refill', 'Refill N after an action', 'An end that has just acted, or is fresh, returns at credit N.', 'Fuel refills an end at an action on it (F8). The static credit mirrors that.', DEF, 'send returns (S@x⁺)^N.', 'static/Typing.v: e_send, e_recv, e_select, e_branch, e_new');
n('side.ub', 'u ≺ F', 'Γ ⊢ u ≺ y for every y in F, u ≺ φ for its variable, and no ⊥ flag. Trivial for an absent u.', 'See side.act.', DEF, 'E-App asks u ≺ F of the closure\'s upper point.', 'static/Contexts.v: ub_below_s');
n('side.lb', 'l ≼ H', 'l is at or below every head in H, and H is empty when l is absent. lb_below_hb also asks no ⊥ flag.', 'See E-Abs.lb.', DEF, 'l ≼ {ρ̄}.', 'static/Contexts.v: lb_below_h, lb_below_hb');
n('side.hold', 'Γ ⊢ C[x̄]', 'Every fact of C at the instance x̄ follows from Γ.', 'E-Force and E-Pack check the constraint at their witness.', DEF, 'The self call of cli instantiates C at (ι⁺, κ⁺, ζ).', 'static/Contexts.v: hold_at');
n('age.free', 'Aging a free entry', 'An entry that holds no end stays.', 'Its credit says nothing.', DEF, 'A box variable is never aged.', 'static/Contexts.v: age_free');
n('age.credit', 'Aging an entry', 'An entry holding ends needs credit at least c and loses c.', 'Appendix B #7, postponement, is handled by F-Tick and aging in the cost judgment. F-Tick ticks every other held end at each action (§2.10), and aging charges a held entry the cost c of what runs meanwhile.', 'cb_inf_not_aged (#17). A server that runs a callback of cost ∞ while holding its client end fails aging by ∞ at finite N. An idle end ages by truncation at 0 instead (age_idle, decided 2026-11-18), which lets the controller retype.', '(S@x, 3) − 1 = (S@x, 2).', 'static/Contexts.v: age_credit');
n('age.agg', 'Aging an aggregate', 'Products, sums and existentials age their parts after adding their credit, and keep credit 0.', 'Credits of aggregates push inward (progress.md, S2).', DEF, '((T^1 ⊗ U^1), 1) − 1.', 'static/Contexts.v: age_prod, age_sum, age_ex');
n('age.ctx', 'Aging the frame', 'What the second part of the term needs is held while the first part runs, so it ages by c₁.', 'Proposal §2.17, Γ − c ages every entry that holds an end by c.', 'Without aging, a context could hold an end across arbitrarily many actions and starve its partner (#7).', 'In LFCycle main loses 1 on d while it closes c.', 'static/Contexts.v: thage, lage');
n('cap.sess', 'Capturing an end', 'A captured end needs credit h + a and is seen by the body at h.', 'The floor is the counter the body may assume. a is the closure\'s own credit (proposal §2.17, E-Abs).', DEF, 'h = 1, a = 1 needs credit 2.', 'static/Contexts.v: cap_sess');
n('cap.arr', 'Capturing a closure', 'A captured closure with floor h₀ ≤ h restates its credit relative to h.', 'Not documented beyond the rule.', DEF, 'Capturing a callback inside a closure.', 'static/Contexts.v: cap_arr');
n('sub.tsub', 'Subtyping', 'Costs, transformers and floors covariant, arguments contravariant, sessions up to ≃, credits may fall, an existential may drop facts.', 'An existential drops facts so that world extension preserves E-New, whose result names the laws of W (progress.md, S2 subtyping).', DEF, 'LFClientServer passes credits 2 and 3 where 1 and 2 are expected.', 'static/Contexts.v: tsub');
n('sub.dconv', 'D-Conv', 'DF typing converts by subtyping of erased types.', 'Progress.md, S2 subtyping and S5 D-Conv.', DEF, 'Dropping a fact from an ∃.', 'static/Typing.v: d_conv');
n('E-Abs.phi', 'Fresh future variable', 'The body runs under future (∅, φ) with u ≺ φ for a fresh φ.', 'The body does not know who calls it, only that the caller\'s future lies above u (proposal §2.16).', 'If the body were typed under the definer\'s F, a closure called from a different context would block against facts that do not hold there.', 'λ-body of between under φ with κ ≺ φ.', 'static/Typing.v: e_abs, e_box');
n('E-Abs.lb', 'Lower point of a closure', 'l lies at or below every head of the captured Θ and Δ, and Δ carries no ⊥ flag.', 'The closure is a held value whose heads its holder reads through l. The ⊥ flag is excluded because hidden points have no lower bound.', 'SpawnGap. A thread holding ends at unrelated points 1 and 2 has no common lower point, so E-Abs rejects a λ that closes both. E-SpawnLam avoids that (spawn_gap).', 'Capturing a⁺ at ρ gives l = ρ̄.', 'static/Contexts.v: lb_below_hb');
n('E-Abs.cap', 'Capture', 'Captured ends and closures are restated at the floor h.', 'Proposal §2.17, h + a ≤ every captured credit.', DEF, 'See cap.sess.', 'static/Contexts.v: thcap, lcap');
n('E-Abs.body', 'Body of a λ', 'The body types under the captured context, the argument at its credit, and the fresh future.', 'Not documented.', DEF, 'λp. let (a, b) = p in … in cli.', 'static/Typing.v: e_abs');
n('E-App.ub', 'u ≺ F at a call', 'The callee may block up to u, which must lie below what the caller still does.', 'Arrow bounds, inventory row S4 (proposal §1.3).', 'Calling a closure that blocks at κ while the caller still has to act at a point below κ.', 'main forces between last, so F = ∅.', 'static/Typing.v: e_app');
n('E-App.fut1', 'Future of the first part', 'e₁ runs under F plus the heads of what the second part holds, and the ⊥ flag of Δ₂.', 'The ends of e₂ are held while e₁ runs, so e₁ must not block above them.', 'A thread running let ∗ = close c in close d beside a partner that closes d before c deadlocks. E-LetU rejects the first thread unless the point of c lies below the partner point of d.', 'Cycle needs ρ ≺ (ρ·0)‾ for close c while d is held.', 'static/Typing.v: e_app, e_pair, e_let, e_case');
n('E-App.fut2', 'Future of the argument', 'e₂ runs under F plus the lower point of the closure that is held meanwhile.', 'The closure\'s ends are held while e₂ runs, and l stands for their heads.', DEF, 'f (close c) with f capturing d.', 'static/Typing.v: e_app');
n('E-App.credit', 'c₂ ≤ a₁', 'The credit of the closure covers the actions of the argument.', 'The closure is held while e₂ runs (proposal §2.17, E-App a₁ ≥ c₂). Its captured counters tick at each action.', DEF, 'A closure at credit ∞ allows any argument.', 'static/Typing.v: e_app');
n('E-App.cost', 'Cost of a call', 'The cost of both parts plus the arrow\'s cost.', 'Not documented.', DEF, 'c₁ + c₂ + c.', 'static/Typing.v: e_app');
n('E-Pair.fut2', 'Future of the second component', 'e₂ runs under F plus the heads of the first component, which is held.', 'Same reason as E-App.fut1.', DEF, '⟨close c, close d⟩ needs d̄ above c and so on.', 'static/Typing.v: e_pair');
n('E-Pair.age1', 'Aging the first component', 'The first component ages by the cost of the second.', 'It is held while e₂ runs.', DEF, '⟨c, send ⟨∗, d⟩⟩ ages c by 1.', 'static/Typing.v: e_pair');
n('E-Let.body', 'Body of a let', 'e₂ types under the aged context with the bound variable at its credit, under F unchanged.', 'Decision Q13. A let is no closure, so it captures every end and needs no lower point.', 'Under the S2 redex rule, let (a, a′) = new_ℓ in e had no typing that captures more than one end.', 'let (a, ⟨b, b′⟩) = new_κ a in … in ClientServer.', 'static/Typing.v: e_let, e_letp, e_letu');
n('E-Case.branches', 'Branches', 'Both branches type under the same context with the payload at credit a + aᵢ.', 'Not documented.', DEF, 'case (branch o) (a. close a) (a. close a).', 'static/Typing.v: e_case');
n('E-Box.unl', 'Δ unlimited', 'A box captures only box variables, and Θ is empty.', 'A box holds no end (Q14), so it is replicable.', DEF, 'ring captures nothing.', 'static/Contexts.v: lenv_unl');
n('E-Box.inst', 'Session instances', 'The body types at every list of k hereditarily contractive session types, and at N = ∞ only at instances with the N = ∞ annotations.', 'Progress.md, S2 session instances. Otherwise a body typed at N = ∞ would have to type at finite payload credits, where an end received at a finite credit cannot be aged by ∞.', DEF, 'k = 0 for the examples.', 'static/Contexts.v: sinsts');
n('E-Box.body', 'Body of a box', 'The body types with no ends, under fresh point variables, the constraint and a fresh future.', 'Not documented.', DEF, 'The body of cli.', 'static/Typing.v: e_box');
n('E-Box.open', 'Opened constraint', 'Γ shifted by m point variables, plus C over them.', 'The body may rely on C at its own point variables.', 'Without C the loop cannot order rounds (#47, ord_no_constraint).', 'hc_open 3 cs_C Γ.', 'static/Contexts.v: hc_open');
n('E-Box.self', 'The self', 'The box binds itself at index 0, at its own type and credit ∞.', 'Recursion. The guard marks it at ▷ for live and LF.', DEF, '(force f) ⟨a, b⟩ calls the self.', 'static/Typing.v: e_box');
n('E-Force.hold', 'Instance meets C', 'The chosen points x̄ satisfy the constraint under Γ.', 'A box is usable only at instances meeting C.', DEF, 'main forces between at (ρ, ρ·1), where Λ₀ gives C.', 'static/Typing.v: e_force, e_pack');
n('E-Force.ub', 'u[x̄] ≺ F', 'The instantiated upper point of the box lies below the future.', 'The forced body may block up to u.', DEF, 'The self call of a loop at ζ.', 'static/Typing.v: e_force');
n('E-Send.unfold', 'Send head', 'S₀ unfolds to a send of an m-point payload T at floor b, then S.', 'Not documented.', DEF, 'Sa = µα.!∗.α.', 'static/Typing.v: e_send');
n('E-Send.nobot', 'No ⊥ in the payload', 'The payload holds no unopened existential at ⊥.', 'Not documented in proposal.md or progress.md.', DEF, 'Sending an unopened new pair is rejected.', 'static/Typing.v: e_send');
n('E-Send.heads', 'x below the payload heads', 'The sender holds the payload while it blocks at x, so x lies below every head of the payload at its fields.', 'It is below_rest for the payload ends, which the sender holds and does not offer while it blocks at x.', DEF, 'GrowRing needs Y ≺ (Y·0)‾ for the payload a of the send on y.', 'static/Typing.v: e_send');
n('E-Send.floor', 'Payload floor', 'The payload, aged by one, must still meet the floor b of the session type.', 'Progress.md, S2 credits of aggregates, and starve_not_spare (#8). A forwarded end at floor b would need b ≥ b + 1.', 'Endless delegation, Padovani\'s Example (2) (#8).', 'LFGrowRing sends a′ at credit 4 against floor 2.', 'static/Typing.v: e_send');
n('E-Recv.unfold', 'Receive head', 'S₀ unfolds to a receive.', 'Not documented.', DEF, 'Sb = µα.?∗.α.', 'static/Typing.v: e_recv');
n('E-Close.unfold', 'Close head', 'S₀ unfolds to Close.', 'Not documented.', DEF, 'Close@x.', 'static/Typing.v: e_close');
n('E-Select.unfold', 'Select head', 'S₀ unfolds to ⊕(S₁, S₂).', 'Not documented.', DEF, '⊕(Close, Close).', 'static/Typing.v: e_select');
n('E-Select.order', 'x ≺ x·κᵢ', 'The partner point of the continuation (x·κᵢ)‾ lies above x.', 'The rule asks it explicitly because W does not order fields against x. For send and receive the built-in x ≺ x̄⁺ plays this role. The rationale is not stated in proposal.md or progress.md.', DEF, 'select_false at x asks x ≺ x·0.', 'static/Typing.v: e_select');
n('E-Branch.unfold', 'Branch head', 'S₀ unfolds to &(S₁, S₂).', 'Not documented.', DEF, '&(Close, Close).', 'static/Typing.v: e_branch');
n('E-Branch.order', 'x ≺ (x·κᵢ)‾', 'The partner point of each possible continuation lies above x.', 'As E-Select.order. Not documented beyond the rule.', DEF, 'branch at x asks x ≺ (x·0)‾ and x ≺ (x·1)‾.', 'static/Typing.v: e_branch');
n('E-Link.dual', 'Linked ends dual', 'The two ends have dual types at dual points.', 'O-Link and F-Link compare them. E-Link types them exactly dual, so link_redex proves plink (decision after S8.3).', DEF, 'link ⟨c⁺ : S@x, d : S̄@x̄⟩.', 'static/Typing.v: e_link');
n('E-SpawnLam.age', 'Handed ends lose one', 'Every end handed to the child loses one unit of credit.', 'A hand-over passes the counter minus one (F-Spawn, proposal §2.10). φ|M ≥ 1 at spawn is the only enforcement there.', 'A hop at counter 0 under truncation passes 0 again for free (#9).', 'LFCycle. The thunk loses 1 at the spawn.', 'static/Typing.v: e_spawn_lam');
n('E-SpawnLam.body', 'Body of a spawned λ', 'The child body types with the handed context and an argument ∗.', 'Q8 (a), C-SpawnLam beside C-Spawn. GrowRing needs one floor per closure (#30).', DEF, 'spawn (λu. let ∗ = u in close d′).', 'static/Typing.v: e_spawn_lam');
n('E-SpawnLam.future', 'Empty future of the child', 'The child starts with no context, so its future is empty and has no variable.', 'Decision after S5.6. O-Spawn reads the thunk body at the empty future only.', 'Reading every F above u fails for a body that creates a channel at a fresh root and blocks on it.', 'P-Term spawns threads at the empty future.', 'static/Typing.v: e_spawn_lam');
n('E-Spawn.credit', 'Closure credit ≥ 1', 'A spawned closure value has credit at least 1.', 'Its captured ends are handed over with counter minus one.', DEF, 'spawn f with f at credit 1.', 'static/Typing.v: e_spawn');
n('E-New.fam', 'ℓ ∈ L', 'The family is known to W.', 'Q2 (d).', 'A new of an unknown family has no laws to open.', 'new_0 in W_cy.', 'static/Typing.v: e_new');
n('E-New.bot', '⊥ bound', 'The pair sits at a root the context does not know.', 'The ⊥ flag says a value may hold an unopened existential whose ends sit at points not known from outside (comment on heads in Types.v).', DEF, 'mk₀ returns ∃^⊥.', 'static/Typing.v: e_new');
n('E-New.laws', 'Laws as the constraint', 'The existential carries the laws Λ_ℓ at the fresh root as its constraint.', 'Proposal §2.4. A fresh root needs facts only from the laws of its family.', 'Option (b), built-in laws only, fails the client and server cycle (§2.5).', 'Opening new_0 in Cycle gives ρ with Λ₀(ρ).', 'static/Typing.v: e_new');
n('E-New.dual', 'Dual pair at N', 'c⁺ at S@ρ and c⁻ at S̄@ρ̄, both at credit N.', 'Fresh ends start at N (C-New, proposal §2.11).', DEF, '(Sa@ρ)^N ⊗ (Sb@ρ̄)^N.', 'static/Typing.v: e_new');
n('E-NewAt.anchor', 'The anchor', 'The anchor end is typed and returned unchanged at its credit.', 'Proposal §2.5. The anchor must be held at the moment of creation.', 'GrowRing created b after closing x, with no anchor. The reordering creates b by new_1 x before recv x (Appendix B.1).', 'new_0 c in Cycle.', 'static/Typing.v: e_new_at');
n('E-NewAt.field', 'Channel at the field', 'The new ends sit at x·κ and (x·κ)‾, at credit N.', 'Proposal §2.3. The field is the payload field on purpose.', DEF, 'd at ρ·0, d′ at (ρ·0)‾.', 'static/Typing.v: e_new_at');
n('E-Sub.cost', 'Weakening costs', 'A cost may rise and a transformer may weaken.', 'Not documented.', DEF, 'Every call cost may rise to ∞.', 'static/Typing.v: e_sub');
n('E-Weak.drop', 'Weakening', 'Only unlimited entries may be dropped.', 'Linear ends must be used.', DEF, 'Dropping an unused box variable.', 'static/Contexts.v: lenv_wk');
n('E-Pack.lb', 'Lower bound of a pack', 'The bound l lies at or below the heads of the instance, or is ⊥.', 'Not documented.', DEF, 'Packing a fresh pair at ⊥.', 'static/Contexts.v: lbx_below_h');
n('E-Open.entry', 'Opened entry', 'A linear variable of existential type, not unlimited.', 'Not documented.', DEF, 'Opening the result of new_ℓ.', 'static/Typing.v: e_open');
n('E-Open.body', 'Body after opening', 'Everything shifts past m fresh point variables, C joins Γ, and the entry becomes T at credit a + a_T.', 'Not documented.', DEF, 'let p = (force mk₀) ∗ opens at ι.', 'static/Typing.v: e_open');
n('pfree', 'pfree Σ', 'No end of the interface has its partner in the interface.', 'Decision of 2026-11-18. P-Term internalizes every pair, so a channel whose two ends the thread holds goes into C₀. It discharges the pfree side condition of sem_p_connect at typed processes.', 'No program is lost, because such a channel can always move into C₀.', 'Σ = {c⁺, c⁻} is rejected, ({c}, …) with Σ = ∅ is used instead.', 'static/Typing.v: pfree');
n('P-Term.C0', 'Θ_B covers C₀', 'The thread holds exactly the ends of the restricted channels C₀ besides its interface.', 'Not documented beyond the rule.', DEF, 'C₀ = ∅ for a source program.', 'static/Typing.v: p_term');
n('P-Term.disj', 'Interface apart from C₀', 'No interface channel is restricted.', 'Not documented.', DEF, 'Σ = {c⁺ ↦ (Close, x)} with C₀ = ∅.', 'static/Typing.v: p_term');
n('P-Term.pairs', 'Restricted pairs dual', 'Both ends of each channel of C₀ are held, at dual types and dual points, at credit N.', 'Not documented beyond the rule.', DEF, 'c⁺ : S@x, c⁻ : S̄@x̄.', 'static/Typing.v: p_term');
n('P-Term.typed', 'Thread typing', 'The thread types with the interface at credit N plus Θ_B, empty Γ and Δ, and the empty future.', 'P-Term asks no semantic premise (no semantics in static judgments, 2026-11-18).', DEF, 'cs_typed at N = ∞.', 'static/Typing.v: p_term');
n('P-Term.future', 'Empty future', 'A thread at top level has no context, so nothing lies in its future.', 'Decision after S5.6.', DEF, '(∅, None).', 'static/Typing.v: p_term');
n('lf.typedN', 'Thread typing at Some N', 'The merged judgment at a finite refill.', 'Decision 2026-11-18. ⊩ has static premises only. fsem^N comes from cost_fundamental and fsem_of_cost inside the proof.', DEF, 'cy_typedN at N = 2.', 'soup/LFTyped.v: lf_term');
n('lf.N', 'Finite N', 'The refill of LF is a natural number.', 'Progress.md, S8. The measure of adequacy reads counters as natural numbers, and at N = ∞ every counter is ∞.', DEF, 'N = 4 for GrowRing.', 'soup/LFTyped.v: lfptyped N');
n('lf.meets', 'meets ϑ 0 tk', 'Some ticket count meets the thread\'s transformer at reserve 0.', 'Progress.md, S9. typed at a finite N does not give it, because an offset may be ∞.', 'A link loop has no finite ticket count (c3_link_loop_not_tix, #5).', 'meets ϑ 0 0 in the examples.', 'soup/LFTyped.v: lf_term');
n('P-Connect.left', 'Left component', 'The component with the main thread, at result T.', 'Not documented.', DEF, 'cl c⁺ at T = ∗.', 'static/Typing.v: p_connect');
n('P-Connect.right', 'Right component at ∗', 'The other component returns ∗, as every spawned thread does.', 'P-Stop asks a value of the main thread and ∗ of every other thread.', DEF, 'cl c⁻.', 'static/Typing.v: p_connect');
n('P-Connect.cut', 'Exact dual cut', 'The right component holds the partners of Σ_C at exactly dual types and dual points.', 'Progress.md, S9 the exact cut, and decision 2026-11-18. The soup pairs protocols of a restricted channel up to ≈ with annotations, which a cut dual only up to annotations does not give.', 'An annotation mismatch breaks the payload credit of a later message (S8, F-Link).', 'senv_dual {c⁺ ↦ (Close, x)} = {c⁻ ↦ (Close, x̄)}.', 'static/Typing.v: senv_dual');
n('P-Connect.disj', 'Disjointness', 'Interfaces, cut and restricted sets of the two sides use distinct channels.', 'Not documented.', DEF, 'LFClose cuts c with Σ₁ = Σ₂ = ∅ and C₁ = C₂ = ∅.', 'static/Typing.v: p_connect');
n('P-Connect.cutfree', 'Cut partner-free', 'The cut holds no pair of partners.', 'Keeps the composite partner-free (pfree decision of 2026-11-18).', DEF, 'Σ_C = {c⁺ ↦ (Close, x)} in LFClose.', 'static/Typing.v: p_connect');
n('P-Connect.fams', 'Families apart', 'The two worlds share no family label.', 'Families are renamed apart at composition (§2.4, #42). Renaming apart is typed_gmap applied before the join.', 'Two components with contradicting laws in one family make the join non-strict (review point 3).', 'W_cl has no families, so W_cl ⊔ W_cl passes.', 'static/Typing.v: p_connect');
n('P-Connect.strict', 'strict(W₁ ⊔ W₂)', 'The joined world is strict.', 'Two-world composition (W7). By R7 it is the strictness of the shared constants.', 'A cyclic join makes both sides ready round the cycle.', 'W_cl ⊔ W_cl.', 'static/Typing.v: p_connect');
n('P-Connect.join', 'Result in W₁ ⊔ W₂', 'The composite lives in the join of the two worlds.', 'A.5. P-Connect is two-world in Rocq and paper.', DEF, 'LFClose lands in W_cl ⊔ W_cl.', 'static/Typing.v: p_connect');
n('P-Join.lemma', 'P-Join side conditions', 'Each world strict, and the join of their restrictions to the shared constants strict.', 'Cleanup C.2. P-Join is admissible because the conditions agree with strict(W₁ ⊔ W₂) by R7 (p_join_iff_connect).', DEF, 'Two worlds with no shared constants.', 'static/Typing.v: p_join, p_join_iff_connect');
n('guard.judg', 'The guard ∅ ⊢▷ t', 'A judgment beside typing that keeps the self of a box unused until the body has acted on a channel.', 'Inventory row S8 (proposal §1.3) and decision 2026-11-18 (guard as guarded recursion). κ_L makes β free, so without it !(f = force f) is typable and τ-divergent (#13, #14). DF typing does not use it.', 'live_fundamental_false (#14). div_not_guarded rejects !(f = force f).', 'loop_guarded. !(f = λx. let ⟨v, x′⟩ = recv x in (force f) x′).', 'static/Guard.v: lguard');
n('guard.marks', 'Marks Λ', 'The variables at ▷, later.', 'Guarded recursion reading (decision 2026-11-18).', DEF, 'true.∅ marks the self.', 'static/Guard.v: lguard');
n('guard.var', 'Marked variables unusable', 'A variable at ▷ cannot be used.', 'Guarded recursion.', '!(f = λx. (force f) x) uses f under a λ before any action (pn_fix_not_guarded, #13).', 'gl_var.', 'static/Guard.v: gl_var');
n('guard.lam', 'λ keeps marks', 'A λ keeps the marks of its scope and adds an unmarked argument.', 'Its body may run at the level where the λ is a value (comment in Guard.v). This replaces the old premise that a λ captures no marked variable.', DEF, 'λx. (force f) x is still unguarded.', 'static/Guard.v: gl_lam');
n('guard.box', 'Box marks its self', 'A box puts its self at ▷.', 'Guarded recursion.', DEF, '!b checks b under true.Λ.', 'static/Guard.v: gl_box');
n('guard.cong', 'Congruence', 'Without an action, both parts keep the marks.', 'Not documented.', DEF, 'gl_app, gl_pair.', 'static/Guard.v: gl_app');
n('guard.tick', 'Tick', 'After an acting e₁, the rest is checked with no marks.', 'The rest runs one level lower, where the selves are in V (comment in Guard.v).', 'Without ticks no loop that recurses after an action is guarded.', 'let ⟨v, x′⟩ = recv x in (force f) x′.', 'static/Guard.v: gl_tick_app and siblings');
n('guard.bind', 'Binders unmarked', 'Variables bound by let, let-pair and case are unmarked.', 'Not documented.', DEF, 'gl_let.', 'static/Guard.v: gl_let, gl_letp, gl_case');
n('guard.acts', 'acts', 'The term performs a send, receive, close, select or branch in evaluation position before it returns.', 'An action costs at least one level in κ_L.', DEF, 'acts (recv x).', 'static/Guard.v: acts, sprim');
n('guard.proc', 'Process guard ⊢▷ p', 'Every thread is guarded.', 'live_soundness asks it beside ∅ ⊢_W p : T.', DEF, 'cs_guarded for the client and server main.', 'static/FundamentalProc.v: pguard');
