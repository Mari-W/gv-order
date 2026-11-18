const { R, h, n, section, block, DEF } = require('./core');

const s = section('syntax', 'Syntax',
  'This section introduces terms, values, primitives, channel ends, processes, and the points that types use to order ends. No term mentions a point. A channel has two named ends c⁺ and c⁻, and the only labels a program writes are family labels ℓ, field labels κ and branch indices.');

block(s, {
  id: 'syn-terms', title: 'Terms', rocq: 'lang/Syntax.v: expr',
  tex: R`\begin{array}{rl}
e ::= & ${h('syn.var', 'x')} \mid ${h('syn.unit', R`\ast`)} \mid ${h('syn.end', 'o')} \mid ${h('syn.lam', R`\lambda e`)} \mid ${h('syn.app', R`e_1\,e_2`)} \mid ${h('syn.pair', R`\langle e_1, e_2\rangle`)} \\
\mid & ${h('syn.letu', R`\mathsf{let}\ \ast = e_1\ \mathsf{in}\ e_2`)} \mid ${h('syn.letp', R`\mathsf{let}\ \langle a,b\rangle = e_1\ \mathsf{in}\ e_2`)} \\
\mid & ${h('syn.let', R`\mathsf{let}\ a = e_1\ \mathsf{in}\ e_2`)} \mid ${h('syn.inj', R`\mathsf{inj}_i\,e`)} \mid ${h('syn.case', R`\mathsf{case}\ e\,(a.e_1)\,(a.e_2)`)} \\
\mid & ${h('syn.box', R`!e`)} \mid ${h('syn.new', R`\mathsf{new}_\ell`)} \mid ${h('syn.op', R`k\,e`)}
\end{array}`,
  caption: 'Fourteen term formers. Variables are de Bruijn indices, written with names here. A box can refer to itself, a let binds one variable without making a closure, and every primitive k is applied to one argument.'
});
block(s, {
  id: 'syn-prims', title: 'Saturated primitives', rocq: 'lang/Syntax.v: prim',
  tex: R`\begin{array}{rl}
k ::= & ${h('prim.send', R`\mathsf{send}`)} \mid ${h('prim.recv', R`\mathsf{recv}`)} \mid ${h('prim.close', R`\mathsf{close}`)} \mid ${h('prim.select', R`\mathsf{select}_i`)} \mid ${h('prim.branch', R`\mathsf{branch}`)} \\
\mid & ${h('prim.link', R`\mathsf{link}`)} \mid ${h('prim.spawn', R`\mathsf{spawn}`)} \mid ${h('prim.force', R`\mathsf{force}`)} \mid ${h('prim.newat', R`\mathsf{new}_\kappa`)}
\end{array}`,
  caption: 'The primitives k of a term k e. send takes a pair ⟨v, o⟩, link a pair of ends, spawn a thunk, new_κ an end.'
});
block(s, {
  id: 'syn-values', title: 'Values', rocq: 'lang/Syntax.v: is_val',
  tex: h('syn.values', R`v ::= \ast \mid o \mid \lambda e \mid\ !e \mid \langle v_1, v_2\rangle \mid \mathsf{inj}_i\,v`),
  caption: 'A primitive alone is not a value. A value of arrow type is always a λ.'
});
block(s, {
  id: 'syn-consts', title: 'Constants as λ-values', rocq: 'lang/Syntax.v: k_send, k_new, k_new_at',
  tex: h('syn.consts', R`\begin{array}{l}
\mathsf{k\_send} := \lambda x.\,\mathsf{send}\,x \\
\mathsf{k\_new}_\ell := \lambda x.\,\mathsf{let}\ \ast = x\ \mathsf{in}\ \mathsf{new}_\ell \\
\mathsf{k\_new}_\kappa := \lambda x.\,\mathsf{new}_\kappa\,x
\end{array}`),
  caption: 'A function such as send, passed as an argument, is a λ over its primitive.'
});
block(s, {
  id: 'syn-ends', title: 'Ends', rocq: 'lang/Syntax.v: cend, edual, ech',
  tex: R`${h('end.cend', R`o ::= c^{+} \mid c^{-}`)} \qquad ${h('end.dual', R`\overline{c^{+}} = c^{-}\quad \overline{c^{-}} = c^{+}`)} \qquad ${h('end.ech', R`\mathsf{ech}(c^{\pm}) = c`)}`,
  caption: 'An end names one side of a channel. Its name never depends on a point. ō is the partner end and ech o the channel.'
});
block(s, {
  id: 'syn-fends', title: 'Ends a term mentions', rocq: 'lang/Syntax.v: fends, fchans',
  tex: R`${h('syn.fends', R`\mathsf{fends}(e)`)} \qquad ${h('syn.fchans', R`\mathsf{fchans}(e) = \mathsf{ech}[\mathsf{fends}(e)]`)}`,
  caption: 'The syntactic set of ends in a term. Terms bind no channel.'
});
block(s, {
  id: 'syn-procs', title: 'Processes and configurations', rocq: 'lang/Syntax.v: proc, lang/Process.v: config, erase',
  tex: R`\begin{array}{l}
${h('proc.proc', R`p = (C, E)`)} \qquad ${h('proc.config', R`q = (C, M),\ M : \mathbb{N} \rightharpoonup e`)} \\
${h('proc.erase', R`\mathsf{erase}(C, M) = (C, \{\!|\, M(i) \mid i \,|\!\})`)}
\end{array}`,
  caption: 'A process is a set C of restricted channels and a multiset E of threads. A configuration names its threads by identifiers.'
});
block(s, {
  id: 'syn-points', title: 'Points', rocq: 'types/Points.v: pname, point',
  tex: R`\begin{array}{l}
r ::= ${h('pt.const', 'a')} \mid ${h('pt.gen', R`g_\ell`)} \mid ${h('pt.var', R`\iota`)} \qquad x ::= r \mid ${h('pt.shift', R`x^{+}`)} \mid ${h('pt.field', R`x\cdot\kappa`)} \mid ${h('pt.dual', R`\overline{x}`)} \\
${h('pt.laws', R`\overline{\overline{x}} = x \quad \overline{x}\cdot\kappa = x\cdot\kappa \quad \overline{x^{+}} = \overline{x}^{+}`)}
\end{array}`,
  caption: 'A point x marks where an end acts next. It has a root r, a polarity flipped by x̄, an offset raised by x⁺, and fields x·κ below it.'
});
block(s, {
  id: 'syn-moves', title: 'Where an end moves', rocq: 'types/Points.v: sel_pt, bra_pt, payload_pts',
  tex: R`\begin{array}{l}
${h('pt.shift', R`\text{action at } x \text{ moves to } x^{+}`)} \qquad ${h('sx.kappai', R`\kappa_{\mathsf{false}} = 0,\ \kappa_{\mathsf{true}} = 1`)} \\
${h('pt.sel', R`\mathsf{sel\_pt}\,x\,i = \overline{x\cdot\kappa_i}`)} \qquad ${h('pt.bra', R`\mathsf{bra\_pt}\,x\,i = x\cdot\kappa_i`)} \qquad ${h('pt.payload', R`\text{payload } j \text{ at } x\cdot j`)}
\end{array}`,
  caption: 'An action moves an end from x to x⁺. Select and branch move to a field, and the ends a message carries sit at fields of the carrier point.'
});
block(s, {
  id: 'syn-labels', title: 'Labels in programs and steps', rocq: 'lang/Syntax.v: family, field, lang/Semantics.v: ltransfer_ok',
  tex: R`${h('lbl.family', R`\ell \in \mathbb{N}`)} \qquad ${h('lbl.field', R`\kappa \in \mathbb{N}`)} \qquad ${h('lbl.transfer', R`M = \mathsf{fends}(v)`)}`,
  caption: 'Family and field labels are plain numbers, like a branch index. The transfer set M of a send or spawn is the set of ends of the value that leaves.'
});
block(s, {
  id: 'syn-csub', title: 'Link substitution', rocq: 'lang/Syntax.v: csub',
  tex: h('link.csub', R`\mathsf{csub}\,o_1\,o_2 :\ \overline{o_1} \mapsto o_2,\quad o_1 \mapsto \overline{o_2},\quad o \mapsto o\ \text{otherwise}`),
  caption: 'The renaming a link applies to every thread. The holder of the partner of o₁ ends up holding o₂.'
});

// ---- notes ----
n('syn.var', 'Variable', 'A variable, written as a de Bruijn index that counts the binders between it and its binder.', 'A plain term former. De Bruijn indices make substitution and renaming need no fresh names.', DEF, 'λ x is the identity, with x the index 0.', 'lang/Syntax.v: Var');
n('syn.unit', 'Unit value ∗', 'The unit value ∗. It carries no information and holds no end.', 'A plain term former. Close, link and spawn return ∗, and a spawned thread ends as ∗.', DEF, 'close o reduces to ∗.', 'lang/Syntax.v: EUnit');
n('syn.end', 'End value o', 'The value o names one end of a channel. It is the only place a channel appears in a term.', 'Each end has its own name c⁺ or c⁻. A select or branch hands back the same name, so running a program never needs to know where an end sits in the order.', DEF, 'c⁺ and c⁻ are the two values new returns.', 'lang/Syntax.v: Chan');
n('syn.lam', 'λ-abstraction', 'A one-argument closure. It suspends evaluation, so no evaluation frame reaches under it.', 'Every value of arrow type is a λ. The value relation then has one case per type and no case for built-in constants.', DEF, 'λx. send x is the send function k_send.', 'lang/Syntax.v: Lam');
n('syn.app', 'Application', 'Application, evaluated left to right. A β step fires when both sides are values.', 'A plain term former. Calling a closure is how a thread runs code it received or built.', DEF, '(λx. e) v steps to e with v for x.', 'lang/Syntax.v: App, lang/Semantics.v: t_act_app');
n('syn.pair', 'Pair', 'A pair, evaluated left to right.', 'A plain term former. Send takes a pair of payload and end, and receive returns one.', DEF, 'send takes ⟨v, o⟩.', 'lang/Syntax.v: Pair');
n('syn.letu', 'Unit elimination', 'let ∗ = e₁ in e₂ runs e₁ to ∗ and then runs e₂.', 'A plain term former. It sequences two computations when the first returns nothing, such as two closes.', DEF, 'let ∗ = close c in close d closes c and then d.', 'lang/Syntax.v: LetU');
n('syn.letp', 'Pair elimination', 'let ⟨a, b⟩ = e₁ in e₂ splits a pair into two variables.', 'A plain term former. It is the only way to take a pair apart, for example the value and continuation end a receive returns.', DEF, 'let ⟨v, c⟩ = recv c in e receives a value and keeps the end.', 'lang/Syntax.v: LetP');
n('syn.let', 'Primitive let', 'let a = e₁ in e₂ evaluates e₁ and substitutes its value into e₂. It builds no closure.', 'A let is no closure, so it may keep every end of its context, however unrelated their points are. No typing rule then has to recognize a λ applied to a value as a let.', 'Written as (λa. e₂) e₁, the λ must bound all the ends it captures by one lower point. After let ⟨a, a′⟩ = new in e the two ends of the fresh channel have no common lower point, and the program would not type.', 'let p = force mk ∗ in e keeps every end of the context in e.', 'lang/Syntax.v: ELet, lang/Semantics.v: t_act_let');
n('syn.inj', 'Injection', 'inj₁ or inj₂ of a value. Branch returns its end inside an injection.', 'A plain term former. Sums let branch report which choice arrived.', DEF, 'branch o steps to inj₂ o when the partner selected the second branch.', 'lang/Syntax.v: Inj1, Inj2');
n('syn.case', 'Case', 'case e (a.e₁) (a.e₂) runs e₁ or e₂ depending on the injection, binding its content to a.', 'A plain term former. It consumes the result of branch.', DEF, 'case (branch o) (a. close a) (a. close a).', 'lang/Syntax.v: Case');
n('syn.box', 'Box !e', 'A recursive thunk value. Its body may refer to the box itself, and force (!e) runs the body with the box for itself.', 'Recursion and replication come from one former. A box holds no end, so copying it is safe.', DEF, '!(f = λx. let ⟨v, x′⟩ = recv x in force f x′) is a server loop.', 'lang/Syntax.v: EBox');
n('syn.new', 'new_ℓ', 'Creates a channel at a fresh point of family ℓ and returns its two ends ⟨c⁺, c⁻⟩. Programs with one family write plain new.', 'The family label picks which order facts the fresh point gets. Running the program ignores it.', 'Without families, two channels created by new could never be ordered against each other. A client and a server that use two fresh channels in a fixed order would not type.', 'let ⟨a, a′⟩ = new₀ in e.', 'lang/Syntax.v: ENew');
n('syn.op', 'Saturated operator', 'k e applies a primitive k to one argument. The argument is evaluated first, then the primitive acts.', 'A primitive is never a value on its own. Every value of arrow type is then a λ, and the value relation needs no case per primitive.', 'With primitives as values, the value relation at arrow types would need one extra case for each primitive, with its own proof obligations.', 'send ⟨∗, o⟩ applies send to a pair.', 'lang/Syntax.v: Op');
n('prim.send', 'send', 'send ⟨v, o⟩ emits v on o and returns o. Its step records the set of ends that v carries.', 'The recorded set tells who owns which end after the message, without looking at the program again.', DEF, 'close (send ⟨∗, c⟩) sends unit and then closes.', 'lang/Syntax.v: PSend, lang/Semantics.v: t_act_send');
n('prim.recv', 'recv', 'recv o takes any value v and returns ⟨v, o⟩.', 'A receive accepts whatever the partner sends. The type, not the step, says what may arrive.', DEF, 'let ⟨u, b⟩ = recv b in e in a client loop.', 'lang/Syntax.v: PRecv');
n('prim.close', 'close', 'close o meets close ō in the partner thread and returns ∗. The channel then disappears.', 'A plain primitive. Every protocol ends with a close, so both sides know the channel is finished.', DEF, 'close c⁺ in one thread and close c⁻ in another.', 'lang/Syntax.v: PClose');
n('prim.select', 'select_i', 'select_i o offers branch i on o and returns o. i is false for the first branch and true for the second.', 'The point where the end continues depends on i, so the two branches can be ordered separately.', DEF, 'select_true o.', 'lang/Syntax.v: PSel');
n('prim.branch', 'branch', 'branch o receives a choice i and returns inj_i o.', 'A plain primitive, the partner of select. The injection tells the program which branch the partner chose.', DEF, 'case (branch o) (a. e₁) (a. e₂).', 'lang/Syntax.v: PBra');
n('prim.link', 'link', 'link ⟨o₁, o₂⟩ joins two ends and returns ∗. Whoever held the partner of o₁ now holds o₂.', 'A link forwards a conversation without copying messages. It costs no action, and in the lock-free system it spends one link ticket.', DEF, 'link ⟨c⁺, d⁻⟩.', 'lang/Syntax.v: PLink');
n('prim.spawn', 'spawn', 'spawn v starts a new thread running v ∗ and returns ∗. Its step records the ends of v.', 'The recorded set fixes which ends go to the child and which stay with the parent.', DEF, 'spawn (λu. let ∗ = u in close d′).', 'lang/Syntax.v: PSpawn');
n('prim.force', 'force', 'force (!e) runs the body e with the box itself in place of its self variable.', 'A plain primitive. It is how a box is used, once per call, and how a loop calls itself again.', DEF, 'force f ⟨a, b⟩ runs the loop again.', 'lang/Syntax.v: PForce');
n('prim.newat', 'new_κ (anchored creation)', 'new_κ o takes a held end o, returns it untouched, and creates a channel at the field x·κ of the point x of o. The result is ⟨o, ⟨c⁺, c⁻⟩⟩.', 'A channel that must sit next to a held end is created at a field of that end, so no program names a point. The field is the one a message on o uses for its payload, so a channel created to be sent on o lands where the receiver expects it.', 'Without anchors a function that creates a channel between two existing ones would need a point parameter, and programs would have to mention points.', 'let ⟨c, ⟨d, d′⟩⟩ = new₀ c in e.', 'lang/Syntax.v: PNewAt, lang/Semantics.v: t_act_new_at');
n('syn.values', 'Values', 'Unit, an end, a λ, a box, and pairs and injections of values.', 'Primitives are not values, so every value of arrow type is a λ.', DEF, '⟨∗, c⁺⟩ is a value.', 'lang/Syntax.v: is_val');
n('syn.consts', 'Constants', 'The functions of GV such as send and new are λ-terms over the primitives.', 'A function like send passed as an argument is just a λ, and it types like any λ.', 'Without them a program that passes send to a higher-order function would need primitives as values.', 'k_new = λx. let ∗ = x in new.', 'lang/Syntax.v: k_send … k_new_at');
n('end.cend', 'End', 'An end c⁺ or c⁻ of channel c. Environments have one entry per end.', 'The two ends have independent names. A select or branch keeps the name of its end, so the two ends of a channel never share one name with a side bit.', DEF, 'new returns ⟨c⁺, c⁻⟩.', 'lang/Syntax.v: cend');
n('end.dual', 'Partner end ō', 'The other end of the same channel.', 'A send on o meets a receive on ō, so every synchronizing rule pairs an end with its partner.', DEF, 'A send on c⁺ meets a receive on c⁻.', 'lang/Syntax.v: edual');
n('end.ech', 'Channel of an end', 'The channel name of an end.', 'Restricted channels and the subjects of an offer are sets of channels, not of ends.', DEF, 'ech c⁻ = c.', 'lang/Syntax.v: ech');
n('syn.fends', 'fends', 'The ends a term mentions.', 'A closure or a box owns exactly the ends its code mentions, and a send or spawn moves exactly the ends of the value that leaves.', DEF, 'fends (λ_. close a) = {a}.', 'lang/Syntax.v: fends');
n('syn.fchans', 'fchans', 'The channels a term mentions.', 'A new channel must not clash with a channel any thread mentions.', DEF, 'fchans ⟨c⁺, d⁻⟩ = {c, d}.', 'lang/Syntax.v: fchans');
n('proc.proc', 'Process (C, E)', 'C is the set of restricted channels, E a multiset of threads.', 'A plain definition. A channel in C has both ends inside the process, a channel outside C talks to the environment.', DEF, '({c}, {close c⁺, close c⁻}).', 'lang/Syntax.v: proc');
n('proc.config', 'Configuration', 'A finite map from thread identifiers to terms, over a set C of restricted channels.', 'Fairness and lock freedom speak about one thread across many steps, so threads need names.', DEF, '(∅, {0 ↦ main}).', 'lang/Process.v: config');
n('proc.erase', 'erase', 'Forgets the thread identifiers.', 'Process steps are defined once, on configurations. The steps of a process are the steps of any configuration that erases to it.', DEF, 'erase (C, {0 ↦ e, 1 ↦ f}) = (C, {e, f}).', 'lang/Process.v: erase');
n('pt.const', 'Constant root a', 'A root known to the world with facts of its own.', 'The channels a component shares with its environment exist before the program runs. Constants give their points, and the world states their facts directly.', DEF, 'Two constants 1 and 2 with the fact 1 ≺ 2̄.', 'types/Points.v: NConst');
n('pt.gen', 'Generated root g_ℓ', 'A root of family ℓ, created at run time by new_ℓ. It obeys the laws Λ_ℓ of the world.', 'A fresh point gets its facts from the laws of its family, never from the run. Every point created by new_ℓ is ordered the same way.', 'If the facts of a fresh point were chosen during the run, the order could change from run to run, and lock freedom could not rank waiting threads by one fixed order.', 'new₀ places c⁺ at a fresh root g of family 0.', 'types/Points.v: NGen');
n('pt.var', 'Point variable ι', 'A point variable, bound by a box, by an existential, or by the existential new_ℓ returns. It occurs only in types.', 'Programs never mention points. Types quantify over them instead.', DEF, 'A loop box binds three point variables ι, κ, ζ.', 'types/Points.v: NVar');
n('pt.shift', 'Shift x⁺', 'Raises the offset of a point by one and keeps its polarity. An action on an end at x moves it to x⁺.', 'Every world has x ≺ x⁺, so the actions of one end are ordered in program order.', DEF, 'After a send at x the end sits at x⁺.', 'types/Points.v: pt_shift');
n('pt.field', 'Field x·κ', 'A new name below x. Payload ends, branch continuations and anchored channels sit at fields.', 'A payload field and the continuation of a choice share one family of fields. A channel created at a field lands where a message on that end delivers it.', 'With a separate kind of field for anchored channels, a reply channel created to be sent would sit away from the payload field, and request and reply programs would not type.', 'new₀ c with c at ρ places d at ρ·0.', 'types/Points.v: pt_field');
n('pt.dual', 'Dual point x̄', 'Flips the polarity. The two ends of a channel sit at x and x̄.', 'A thread blocked at u that holds an end at v must have u ≺ v̄, the point of the partner end.', DEF, 'new_ℓ places c⁺ at ρ and c⁻ at ρ̄.', 'types/Points.v: pt_dual');
n('pt.laws', 'Point laws', 'Dual is an involution, fields ignore polarity, and shift keeps polarity.', 'Fields ignore polarity so the sender and the receiver of a message compute the same payload point.', 'If x̄·κ differed from x·κ, the ends a message carries would sit at different points for sender and receiver.', 'ρ̄·0 = ρ·0.', 'types/Points.v: pt_dual_dual, pt_field_dual');
n('sx.kappai', 'Field of a choice κᵢ', 'Choice false continues at field 0 and choice true at field 1.', 'The two branches of a choice continue at different points, so they can be ordered separately against other ends.', DEF, 'branch at x̄ continues at x·0 or x·1.', 'types/Points.v: bfield');
n('pt.sel', 'Select continuation', 'A select of branch i moves the end to the dual of x·κᵢ.', 'The selecting end and the branching end continue at the two sides of one field point.', DEF, 'select_false o at x continues at the dual of x·0.', 'types/Points.v: sel_pt');
n('pt.bra', 'Branch continuation', 'A branch of choice i moves the end to x·κᵢ.', 'It is the partner point of the selecting side.', DEF, 'branch at x̄ continues at x·κᵢ.', 'types/Points.v: bra_pt');
n('pt.payload', 'Payload fields', 'The j-th end of a message sent at x sits at x·j.', 'Both ends of the carrier compute the same payload point, so sender and receiver agree where the delivered ends sit.', DEF, 'A message on y at Y delivers its end at Y·0.', 'types/Points.v: payload_pts');
n('lbl.family', 'Family label ℓ', 'Selects the laws Λ_ℓ of the world for a new root.', 'Two components can each use their own families. Their labels are renamed apart when they are composed, so contradicting laws never meet.', DEF, 'new₀ and new₁ in a program with two families.', 'lang/Syntax.v: family');
n('lbl.field', 'Field label κ', 'Selects the field x·κ for new_κ.', 'Distinct labels, or an action on the anchor in between, give distinct points.', 'Two new_κ o with one label and no action on o give two channels at one point. A thread holding one could then never wait on the other.', 'new₀ c and new₁ c create two channels at different fields of c.', 'lang/Syntax.v: field');
n('lbl.transfer', 'Transfer set M', 'The set fends(v) of the value a send or spawn moves out of the thread.', 'The ends that leave are exactly the ends the value mentions. That fixes who owns which end after the step, the same way every time.', 'Without it, an end that neither the parent nor the child mentions could be given to either side, and ownership would not follow the program.', 'spawn (λ_. close d′) moves {d′}.', 'lang/Semantics.v: ltransfer_ok, tstep_transfer');
n('link.csub', 'csub', 'Maps ō₁ to o₂ and o₁ to ō₂ and leaves every other end alone. The process applies it to every thread after a link.', 'After the link, whoever held the partner of o₁ talks to the partner of o₂ directly, so it now holds o₂. The renaming merges ō₁ and o₂ into one name, so it is not a bijection.', DEF, 'After link ⟨c⁺, d⁻⟩ the holder of c⁻ holds d⁻.', 'lang/Syntax.v: csub');
