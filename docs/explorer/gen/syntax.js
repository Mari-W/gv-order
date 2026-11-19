const { R, h, n, section, block, DEF } = require('./core');

const s = section('syntax', 'Syntax',
  'Terms $e$, values, constants, ends, points and processes, where no term mentions a point.');

block(s, {
  id: 'syn-terms', title: 'Terms', rocq: 'lang/Syntax.v: expr',
  tex: R`\begin{array}{rl}
e ::= & ${h('syn.var', 'x')} \mid ${h('syn.unit', R`\ast`)} \mid ${h('syn.end', 'o')} \mid ${h('syn.lam', R`\lambda e`)} \mid ${h('syn.app', R`e_1\,e_2`)} \mid ${h('syn.pair', R`\langle e_1, e_2\rangle`)} \\
\mid & ${h('syn.letu', R`\mathsf{let}\ \ast = e_1\ \mathsf{in}\ e_2`)} \mid ${h('syn.letp', R`\mathsf{let}\ \langle a,b\rangle = e_1\ \mathsf{in}\ e_2`)} \\
\mid & ${h('syn.inj', R`\mathsf{inj}_i\,e`)} \mid ${h('syn.case', R`\mathsf{case}\ e\,(a.e_1)\,(a.e_2)`)} \\
\mid & ${h('syn.box', R`!e`)} \mid ${h('syn.new', R`\mathsf{new}`)} \mid ${h('syn.op', 'k')}
\end{array}`,
  caption: 'Thirteen term formers with de Bruijn variables, a box $!e$ binding itself in $e$, and the constants $k$.'
});
block(s, {
  id: 'syn-let', title: 'Derived let', rocq: 'lang/Syntax.v: ELet (notation)',
  tex: h('syn.let', R`\begin{array}{l}
\mathsf{let}\ a = e_1\ \mathsf{in}\ e_2 \ \triangleq\ {} \\
\qquad \mathsf{let}\ \langle a, u\rangle = \langle e_1, \ast\rangle\ \mathsf{in}\ \mathsf{let}\ \ast = u\ \mathsf{in}\ e_2
\end{array}`),
  caption: 'The one-variable $\\mathsf{let}$ is notation over pairs and unit with $u$ fresh.'
});
block(s, {
  id: 'syn-prims', title: 'Constants', rocq: 'lang/Syntax.v: prim',
  tex: R`\begin{array}{rl}
k ::= & ${h('prim.send', R`\mathsf{send}`)} \mid ${h('prim.recv', R`\mathsf{recv}`)} \mid ${h('prim.close', R`\mathsf{close}`)} \mid ${h('prim.select', R`\mathsf{select}_i`)} \mid ${h('prim.branch', R`\mathsf{branch}`)} \\
\mid & ${h('prim.link', R`\mathsf{link}`)} \mid ${h('prim.spawn', R`\mathsf{spawn}`)} \mid ${h('prim.force', R`\mathsf{force}`)}
\end{array}`,
  caption: 'The constants $k$, with $\\mathsf{send}$ on $\\langle v, o\\rangle$, $\\mathsf{link}$ on two ends and $\\mathsf{spawn}$ on a thunk.'
});
block(s, {
  id: 'syn-values', title: 'Values', rocq: 'lang/Syntax.v: is_val',
  tex: h('syn.values', R`v ::= \ast \mid o \mid k \mid \lambda e \mid\ !e \mid \langle v_1, v_2\rangle \mid \mathsf{inj}_i\,v`),
  caption: 'Unit, ends, constants, abstractions, boxes, and pairs and injections of values.'
});
block(s, {
  id: 'syn-ends', title: 'Ends', rocq: 'lang/Syntax.v: cend, edual, ech',
  tex: R`${h('end.cend', R`o ::= c^{+} \mid c^{-}`)} \qquad ${h('end.dual', R`\overline{c^{+}} = c^{-}\quad \overline{c^{-}} = c^{+}`)} \qquad ${h('end.ech', R`\mathsf{ech}(c^{\pm}) = c`)}`,
  caption: 'An end $o$ of the channel $\\mathsf{ech}\\,o$ with partner $\\overline{o}$, named independently of any point.'
});
block(s, {
  id: 'syn-fends', title: 'Ends a term mentions', rocq: 'lang/Syntax.v: fends, fchans',
  tex: R`${h('syn.fends', R`\mathsf{fends}(e)`)} \qquad ${h('syn.fchans', R`\mathsf{fchans}(e) = \mathsf{ech}[\mathsf{fends}(e)]`)}`,
  caption: '$\\mathsf{fends}(e)$ is the set of ends in $e$ and $\\mathsf{fchans}(e) = \\mathsf{ech}[\\mathsf{fends}(e)]$.'
});
block(s, {
  id: 'syn-procs', title: 'Processes and configurations', rocq: 'lang/Syntax.v: proc, lang/Process.v: config, erase',
  tex: R`\begin{array}{l}
${h('proc.proc', R`p = (C, E)`)} \qquad ${h('proc.config', R`q = (C, M),\ M : \mathbb{N} \rightharpoonup e`)} \\
${h('proc.erase', R`\mathsf{erase}(C, M) = (C, \{\!|\, M(i) \mid i \,|\!\})`)}
\end{array}`,
  caption: 'A process is a finite set $C$ of restricted channels with a finite multiset $E$ of threads, and a configuration names threads by $i \\in \\mathrm{dom}\\,M$.'
});
block(s, {
  id: 'syn-points', title: 'Points', rocq: 'types/Points.v: pname, point',
  tex: R`\begin{array}{l}
r ::= ${h('pt.const', 'a')} \mid ${h('pt.var', R`\iota`)} \qquad x ::= r \mid ${h('pt.shift', R`x^{+}`)} \mid ${h('pt.field', R`x\cdot\kappa`)} \mid ${h('pt.dual', R`\overline{x}`)} \\
${h('pt.laws', R`\overline{\overline{x}} = x \quad \overline{x}\cdot\kappa = x\cdot\kappa \quad \overline{x^{+}} = \overline{x}^{+}`)}
\end{array}`,
  caption: 'A point $x$ has a root $a$ or $\\iota$, a polarity flipped by $\\overline{x}$, an offset raised by $x^{+}$ and fields $x\\cdot\\kappa$.'
});
block(s, {
  id: 'syn-moves', title: 'Where an end moves', rocq: 'types/Points.v: sel_pt, bra_pt, payload_pts',
  tex: R`\begin{array}{l}
x \;\mapsto\; ${h('pt.shift', R`x^{+}`)} \qquad ${h('sx.kappai', R`\kappa_{\mathsf{false}} = 0 \quad \kappa_{\mathsf{true}} = 1`)} \\
${h('pt.sel', R`\mathsf{sel\_pt}\,x\,i = \overline{x\cdot\kappa_i}`)} \qquad ${h('pt.bra', R`\mathsf{bra\_pt}\,x\,i = x\cdot\kappa_i`)} \qquad ${h('pt.payload', R`\mathsf{payload\_pts}\,x\,m = (x\cdot 0, \dots, x\cdot(m-1))`)}
\end{array}`,
  caption: 'An action moves an end from $x$ to $x^{+}$, a choice to a field, and the $j$-th payload end of a message at $x$ sits at $x\\cdot j$.'
});
block(s, {
  id: 'syn-labels', title: 'Field labels', rocq: 'lang/Syntax.v: field',
  tex: h('lbl.field', R`\kappa \in \mathbb{N}`),
  caption: 'Field labels $\\kappa$ are natural numbers and name the fields $x\\cdot\\kappa$ of a point.'
});
block(s, {
  id: 'syn-csub', title: 'Link substitution', rocq: 'lang/Syntax.v: csub',
  tex: h('link.csub', R`\mathsf{csub}\,o_1\,o_2 :\ \overline{o_1} \mapsto o_2,\quad o_1 \mapsto \overline{o_2},\quad o \mapsto o\ \text{otherwise}`),
  caption: 'The renaming a link applies to every thread, so the holder of $\\overline{o_1}$ ends up holding $o_2$.'
});

// ---- notes ----
n('syn.var', 'Variable', 'A de Bruijn index $x \\in \\mathbb{N}$, the number of binders between the occurrence and its binder.', 'A plain term former. With de Bruijn indices, substitution $e[v]$ and renaming need no side condition on fresh names.', DEF, '$\\lambda x.\\,x$ is the identity, where $x$ is the index $0$.', 'lang/Syntax.v: Var');
n('syn.unit', 'Unit value $\\ast$', 'The unit value $\\ast$, with $V\\llbracket\\Theta \\vdash \\ast\\rrbracket$ only at $\\Theta = \\varnothing$.', 'A plain term former. $\\mathsf{close}$, $\\mathsf{link}$ and $\\mathsf{spawn}$ return $\\ast$, and a terminated process has $\\ast$ in every thread except the main thread.', DEF, '$\\mathsf{close}\\,o \\xrightarrow{o\\,\\mathsf{end}} \\ast$.', 'lang/Syntax.v: EUnit');
n('syn.end', 'End value $o$', 'The value $o$ names one end of a channel, the only channel name in terms.', 'Each end has its own name $c^{+}$ or $c^{-}$, and $\\mathsf{select}_i\\,o$ and $\\mathsf{branch}\\,o$ return the same name $o$. Hence no step of the semantics reads a point.', DEF, '$\\mathsf{new} \\xrightarrow{\\mathsf{new}\\,c} \\langle c^{+}, c^{-}\\rangle$ returns the two end values of $c$.', 'lang/Syntax.v: Chan');
n('syn.lam', '$\\lambda$-abstraction', 'A one-argument closure $\\lambda e$, a value for every $e$ because no frame has its hole under $\\lambda$.', 'A plain term former and the value form of every user function.', DEF, '$\\lambda x.\\,\\mathsf{send}\\,x$ is $\\mathsf{send}$ as a function value.', 'lang/Syntax.v: Lam');
n('syn.app', 'Application', 'Application, left to right, with $(\\lambda e)\\,v \\xrightarrow{\\beta} e[v]$.', 'A plain term former. It is the only way to run a closure, received or built.', DEF, '$(\\lambda x.\\,\\mathsf{close}\\,x)\\,c^{+} \\xrightarrow{\\beta} \\mathsf{close}\\,c^{+}$.', 'lang/Syntax.v: App, lang/Semantics.v: t_act_app');
n('syn.pair', 'Pair', 'A pair $\\langle e_1, e_2\\rangle$, evaluated left to right, a value iff both components are values.', 'A plain term former. $\\mathsf{send}$ takes a pair $\\langle v, o\\rangle$ and $\\mathsf{recv}$ returns one.', DEF, '$\\mathsf{send}\\,\\langle \\ast, o\\rangle$.', 'lang/Syntax.v: Pair');
n('syn.letu', 'Unit elimination', '$\\mathsf{let}\\ \\ast = e_1\\ \\mathsf{in}\\ e_2$ evaluates $e_1$ to $\\ast$ and then steps to $e_2$ by $\\beta$.', 'A plain term former. It sequences $e_1$ before $e_2$ when $e_1$ returns $\\ast$, and the derived $\\mathsf{let}$ uses it to discard its unit component.', DEF, '$\\mathsf{let}\\ \\ast = \\mathsf{close}\\,c^{+}\\ \\mathsf{in}\\ \\mathsf{close}\\,d^{+}$ closes $c^{+}$ and then $d^{+}$.', 'lang/Syntax.v: LetU');
n('syn.letp', 'Pair elimination', '$\\mathsf{let}\\ \\langle a, b\\rangle = e_1\\ \\mathsf{in}\\ e_2$ evaluates $e_1$ to $\\langle v_1, v_2\\rangle$ and steps to $e_2[v_1, v_2]$ by $\\beta$.', 'A plain term former and the only eliminator of $\\otimes$. A $\\mathsf{recv}$ returns $\\langle v, o\\rangle$, and the continuation reads $v$ and $o$ through it.', DEF, '$\\mathsf{let}\\ \\langle v, c\\rangle = \\mathsf{recv}\\,c\\ \\mathsf{in}\\ e$.', 'lang/Syntax.v: LetP');
n('syn.let', 'Derived let', '$\\mathsf{let}\\ a = e_1\\ \\mathsf{in}\\ e_2 := \\mathsf{let}\\ \\langle a, u\\rangle = \\langle e_1, \\ast\\rangle\\ \\mathsf{in}\\ \\mathsf{let}\\ \\ast = u\\ \\mathsf{in}\\ e_2$ with $u$ fresh.', 'The abbreviation binds one variable without a $\\lambda$, so its body keeps every end of the context and the typing needs no lower point $l$ for them. It uses only $\\otimes$ and $\\ast$, which every system already has.', 'Written as $(\\lambda a.\\,e_2)\\,e_1$ instead, the $\\lambda$ must bound the partner points of all ends it captures by one lower point $l$. After $\\mathsf{let}\\ \\langle a, a\'\\rangle = \\mathsf{new}_\\ell$ the ends $a, a\'$ sit at $\\rho$ and $\\overline{\\rho}$, which have no common lower bound, and the body does not type.', '$\\mathsf{let}\\ p = \\mathsf{force}\\,mk\\,\\ast\\ \\mathsf{in}\\ e$ keeps every end of the context in $e$.', 'lang/Syntax.v: ELet, lang/Semantics.v: t_act_let');
n('syn.inj', 'Injection', '$\\mathsf{inj}_i\\,e$ for $i \\in \\{1, 2\\}$, a value when $e$ is a value.', 'A plain term former. $\\mathsf{branch}\\,o$ returns $\\mathsf{inj}_i\\,o$, and $i$ records which choice arrived.', DEF, '$\\mathsf{branch}\\,o \\xrightarrow{o \\rhd \\mathsf{true}} \\mathsf{inj}_2\\,o$.', 'lang/Syntax.v: Inj');
n('syn.case', 'Case', '$\\mathsf{case}\\ e\\,(a.e_1)\\,(a.e_2)$ evaluates $e$ to $\\mathsf{inj}_i\\,v$ and steps to $e_i[v]$ by $\\beta$.', 'A plain term former and the only eliminator of $\\oplus$. It consumes the result of $\\mathsf{branch}$.', DEF, '$\\mathsf{case}\\ (\\mathsf{branch}\\,o)\\,(a.\\,\\mathsf{close}\\,a)\\,(a.\\,\\mathsf{close}\\,a)$.', 'lang/Syntax.v: Case');
n('syn.box', 'Box $!e$', 'A recursive thunk value whose body binds the box at index $0$, $\\mathsf{force}\\,(!e) \\xrightarrow{\\beta} e[!e]$.', 'One former gives recursion and replication. The value relation asks $\\Theta = \\varnothing$ and $\\mathsf{fends}(e) = \\varnothing$ of a box, so copying a box duplicates no end.', DEF, '$!(f = \\lambda x.\\,\\mathsf{let}\\ \\langle v, x\'\\rangle = \\mathsf{recv}\\,x\\ \\mathsf{in}\\ \\mathsf{force}\\,f\\,x\')$ is a server loop.', 'lang/Syntax.v: EBox');
n('syn.new', '$\\mathsf{new}$', '$\\mathsf{new} \\xrightarrow{\\mathsf{new}\\,c} \\langle c^{+}, c^{-}\\rangle$ for a fresh channel $c$. The typing places $c^{+}$ at a position $\\pi$, a fresh root or a field $x\\cdot\\kappa$, places $c^{-}$ at $\\overline{\\pi}$, and states a constraint $C$ on both.', 'The term names no point. Position and constraint live in the existential type of $\\mathsf{new}$, chosen by the typing derivation, so every ordering of a new channel is available without program syntax for it.', 'With the position or the facts in the term, every held end that the facts mention is an argument that $\\mathsf{new}$ takes and returns, because ends are linear.', '$\\mathsf{let}\\ \\langle a, a\'\\rangle = \\mathsf{new}\\ \\mathsf{in}\\ e$.', 'lang/Syntax.v: ENew');
n('syn.op', 'Constant $k$', 'A constant $k$ is a value, and $k\\,v$ takes the head step of $k$ on the value $v$.', 'The constants are the operations on channels, boxes and threads. Application $k\\,e$ evaluates $e$ first like any application.', DEF, '$\\mathsf{send}\\,\\langle \\ast, o\\rangle$ applies $\\mathsf{send}$ to a pair.', 'lang/Syntax.v: Op (the value $k$ is $\\lambda x.\\,k\\,x$)');
n('prim.send', '$\\mathsf{send}$', '$\\mathsf{send}\\,\\langle v, o\\rangle \\xrightarrow{o!v} o$.', 'The label carries the payload $v$. The value relation is exact, $\\mathrm{dom}\\,\\Theta = \\mathsf{fends}(v)$ for $v$ in $V$ at $\\Theta$, so the ends that leave the thread are determined by $v$.', DEF, '$\\mathsf{close}\\,(\\mathsf{send}\\,\\langle \\ast, c^{+}\\rangle)$ sends $\\ast$ and then closes.', 'lang/Syntax.v: PSend, lang/Semantics.v: t_act_send');
n('prim.recv', '$\\mathsf{recv}$', '$\\mathsf{recv}\\,o \\xrightarrow{o?v} \\langle v, o\\rangle$ for every value $v$.', 'The step admits every $v$, so a receive meets every send of the partner. The session type of $o$ restricts the $v$ the relation considers.', DEF, '$\\mathsf{let}\\ \\langle u, b\\rangle = \\mathsf{recv}\\,b\\ \\mathsf{in}\\ e$.', 'lang/Syntax.v: PRecv');
n('prim.close', '$\\mathsf{close}$', '$\\mathsf{close}\\,o \\xrightarrow{o\\,\\mathsf{end}} \\ast$. The process step pairs it with $\\mathsf{close}\\,\\overline{o}$ and removes $\\mathsf{ech}\\,o$ from $C$.', 'A plain constant. A session type ends in $\\mathsf{Close}$, and after both closes no thread holds an end of the channel.', DEF, '$\\mathsf{close}\\,c^{+}$ in one thread and $\\mathsf{close}\\,c^{-}$ in another.', 'lang/Syntax.v: PClose');
n('prim.select', '$\\mathsf{select}_i$', '$\\mathsf{select}_i\\,o \\xrightarrow{o \\lhd i} o$ for $i \\in \\{\\mathsf{false}, \\mathsf{true}\\}$, where $\\mathsf{false}$ selects the first branch.', 'The end continues at $\\overline{x\\cdot\\kappa_i}$, a point that depends on $i$. Hence the two branches are ordered independently.', DEF, '$\\mathsf{select}_{\\mathsf{true}}\\,o$.', 'lang/Syntax.v: PSel');
n('prim.branch', '$\\mathsf{branch}$', '$\\mathsf{branch}\\,o \\xrightarrow{o \\rhd i} \\mathsf{inj}_i\\,o$ for both $i$.', 'A plain constant, the partner of $\\mathsf{select}_i$. The injection $\\mathsf{inj}_i$ passes the chosen $i$ to the program.', DEF, '$\\mathsf{case}\\ (\\mathsf{branch}\\,o)\\,(a.\\,e_1)\\,(a.\\,e_2)$.', 'lang/Syntax.v: PBra');
n('prim.link', '$\\mathsf{link}$', '$\\mathsf{link}\\,\\langle o_1, o_2\\rangle \\xrightarrow{\\leftrightarrow\\{o_1, o_2\\}} \\ast$. The process step removes $\\mathsf{ech}\\,o_1$ and renames every thread by $\\mathsf{csub}\\,o_1\\,o_2$.', 'A link forwards a conversation without relaying messages. It acts on no protocol, so it costs $0$ in both cost tables, and in the fuel layer it spends one link ticket.', DEF, '$\\mathsf{link}\\,\\langle c^{+}, d^{-}\\rangle$.', 'lang/Syntax.v: PLink');
n('prim.spawn', '$\\mathsf{spawn}$', '$\\mathsf{spawn}\\,v \\xrightarrow{\\mathsf{spawn}\\,v} \\ast$, and the process starts a thread running $v\\,\\ast$.', 'The label carries the thunk $v$. The value relation is exact, so the child holds exactly the ends $\\mathsf{fends}(v)$ and the parent keeps the rest.', DEF, '$\\mathsf{spawn}\\,(\\lambda u.\\,\\mathsf{let}\\ \\ast = u\\ \\mathsf{in}\\ \\mathsf{close}\\,d\')$ hands $d\'$ to the child.', 'lang/Syntax.v: PSpawn');
n('prim.force', '$\\mathsf{force}$', '$\\mathsf{force}\\,(!e) \\xrightarrow{\\beta} e[!e]$.', 'A plain constant. It is the only use of a box, and a loop calls itself by $\\mathsf{force}$ of its own self variable.', DEF, '$\\mathsf{force}\\,f\\,\\langle a, b\\rangle$ runs the loop $f$ again.', 'lang/Syntax.v: PForce');
n('syn.values', 'Values', '$v ::= \\ast \\mid o \\mid k \\mid \\lambda e \\mid\\ !e \\mid \\langle v_1, v_2\\rangle \\mid \\mathsf{inj}_i\\,v$.', 'The results of evaluation. A thread that is a value has finished.', DEF, '$\\langle \\ast, c^{+}\\rangle$ and $\\mathsf{send}$ are values.', 'lang/Syntax.v: is_val');
n('end.cend', 'End', 'An end $o \\in \\{c^{+}, c^{-}\\}$ of a channel $c$, with one entry per end in every environment.', 'The two ends have independent names, and $\\mathsf{select}$ and $\\mathsf{branch}$ return the name they received. Hence an environment entry is determined by the end alone.', DEF, '$\\mathsf{new}$ returns $\\langle c^{+}, c^{-}\\rangle$.', 'lang/Syntax.v: cend');
n('end.dual', 'Partner end $\\overline{o}$', '$\\overline{c^{+}} = c^{-}$ and $\\overline{c^{-}} = c^{+}$, so $\\overline{\\overline{o}} = o$.', 'A message on $o$ synchronizes with an action on $\\overline{o}$. Every two-thread process step pairs an end with its partner.', DEF, 'A send on $c^{+}$ meets a receive on $c^{-}$.', 'lang/Syntax.v: edual');
n('end.ech', 'Channel of an end', '$\\mathsf{ech}(c^{+}) = \\mathsf{ech}(c^{-}) = c$.', 'Restricted sets $C$ and the subjects of an offer are sets of channels, so the rules map ends to channels by $\\mathsf{ech}$.', DEF, '$\\mathsf{ech}(c^{-}) = c$.', 'lang/Syntax.v: ech');
n('syn.fends', '$\\mathsf{fends}$', '$\\mathsf{fends}(e)$ is the finite set of ends that occur in $e$.', 'The value relation asks $\\mathrm{dom}\\,\\Theta = \\mathsf{fends}(\\lambda e)$ of a closure and $\\mathsf{fends}(e) = \\varnothing$ of a box. Hence for $v$ in $V$ at $\\Theta$ the ends a send or spawn of $v$ moves are $\\mathrm{dom}\\,\\Theta = \\mathsf{fends}(v)$, and ownership follows the syntax of values.', DEF, '$\\mathsf{fends}(\\lambda u.\\,\\mathsf{close}\\,a) = \\{a\\}$.', 'lang/Syntax.v: fends');
n('syn.fchans', '$\\mathsf{fchans}$', '$\\mathsf{fchans}(e) = \\{\\mathsf{ech}\\,o \\mid o \\in \\mathsf{fends}(e)\\}$.', 'A created channel $c$ must satisfy $c \\notin \\mathsf{fchans}(e)$ for every thread $e$, or two channels share a name.', DEF, '$\\mathsf{fchans}(\\langle c^{+}, d^{-}\\rangle) = \\{c, d\\}$.', 'lang/Syntax.v: fchans');
n('proc.proc', 'Process $(C, E)$', 'A process is a pair of a finite set $C$ of restricted channels and a finite multiset $E$ of threads.', 'A channel $c \\in C$ has both ends inside the process. An end $o$ with $\\mathsf{ech}\\,o \\notin C$ belongs to the interface with the environment.', DEF, '$(\\{c\\}, \\{\\!|\\,\\mathsf{close}\\,c^{+}, \\mathsf{close}\\,c^{-}\\,|\\!\\})$.', 'lang/Syntax.v: proc');
n('proc.config', 'Configuration', 'A configuration $q = (C, M)$ has a finite partial map $M : \\mathbb{N} \\rightharpoonup e$ from thread identifiers to terms.', 'Weak fairness and lock freedom speak about one thread $t$ across a run, so threads carry identifiers.', DEF, '$(\\varnothing, \\{0 \\mapsto main\\})$.', 'lang/Process.v: config');
n('proc.erase', '$\\mathsf{erase}$', '$\\mathsf{erase}(C, M) = (C, \\{\\!|\\, M(i) \\mid i \\in \\mathrm{dom}\\,M \\,|\\!\\})$ forgets the identifiers.', 'Steps are defined once, on configurations. A process $p$ steps to $p\'$ when some $q$ with $\\mathsf{erase}(q) = p$ steps to some $q\'$ with $\\mathsf{erase}(q\') = p\'$.', DEF, '$\\mathsf{erase}(C, \\{0 \\mapsto e, 1 \\mapsto f\\}) = (C, \\{\\!|\\,e, f\\,|\\!\\})$.', 'lang/Process.v: erase');
n('pt.const', 'Root $a$', 'A root $a \\in A$ of the world $W$, either shared with the environment or added to $W$ by the creation of a channel.', 'Every point of a held end has a root in $A$. The facts $\\prec_A$ mention only such points.', DEF, 'Roots $1, 2$ with the fact $1 \\prec \\overline{2}$.', 'types/Points.v: NConst');
n('pt.var', 'Point variable $\\iota$', 'A de Bruijn point variable, bound by $\\Box\\forall\\bar\\iota$, by $\\exists^m\\bar\\iota$ or by the existential of $\\mathsf{new}$, and absent from terms.', 'No term mentions a point. Types quantify over points instead.', DEF, '$\\Box\\forall \\iota\\,\\kappa\\,\\zeta.\\ C.\\ \\ast \\multimap U$ binds three point variables.', 'types/Points.v: NVar');
n('pt.shift', 'Shift $x^{+}$', '$x^{+}$ raises the offset of $x$ by $1$, so an action on an end at $x$ moves it to $x^{+}$.', 'For every $W$ and $x$, $x \\prec_W x^{+}$. Hence the actions of one end are ordered in program order.', DEF, 'After $\\mathsf{send}$ at $x$ the end sits at $x^{+}$.', 'types/Points.v: pt_shift');
n('pt.field', 'Field $x\\cdot\\kappa$', '$x\\cdot\\kappa$ is a name below $x$ with offset $0$ and positive polarity, where payloads, branch continuations and channels created at a field sit.', 'The $j$-th payload end of a message at $x$ sits at $x\\cdot j$, and the continuation of choice $i$ at $x\\cdot\\kappa_i$. $\\mathsf{new}$ may place a channel at the same fields, so a channel created to be sent lands where the message delivers it.', 'With a separate sort of point for created channels, a reply channel created to be sent sits away from the payload field, and request and reply programs do not type.', '$\\mathsf{new}$ at the position $\\rho\\cdot 0$ places $d^{+}$ at $\\rho\\cdot 0$ and $d^{-}$ at $\\overline{\\rho\\cdot 0}$.', 'types/Points.v: pt_field');
n('pt.dual', 'Dual point $\\overline{x}$', '$\\overline{x}$ flips the polarity of $x$, and the two ends of a channel sit at $x$ and $\\overline{x}$.', 'A thread blocked at $u$ that holds an end at $v$ must satisfy $u \\prec \\overline{v}$, the point of the partner end.', DEF, '$\\mathsf{new}$ places $c^{+}$ at $\\rho$ and $c^{-}$ at $\\overline{\\rho}$.', 'types/Points.v: pt_dual');
n('pt.laws', 'Point laws', 'For every $x$ and $\\kappa$, $\\overline{\\overline{x}} = x$, $\\overline{x}\\cdot\\kappa = x\\cdot\\kappa$ and $\\overline{x^{+}} = \\overline{x}^{+}$.', '$\\overline{x}\\cdot\\kappa = x\\cdot\\kappa$ makes the payload points $x\\cdot j$ of sender and receiver equal, although the two ends sit at $x$ and $\\overline{x}$.', 'If $\\overline{x}\\cdot\\kappa \\neq x\\cdot\\kappa$, the ends a message carries sit at different points for sender and receiver, and the received value is not in the value relation at its type.', '$\\overline{\\rho}\\cdot 0 = \\rho\\cdot 0$.', 'types/Points.v: pt_dual_dual, pt_field_dual');
n('sx.kappai', 'Field of a choice $\\kappa_i$', '$\\kappa_{\\mathsf{false}} = 0$ and $\\kappa_{\\mathsf{true}} = 1$.', 'The two continuations of a choice sit at distinct fields $x\\cdot 0 \\neq x\\cdot 1$, so facts order them independently.', DEF, '$\\mathsf{branch}$ at $\\overline{x}$ continues at $x\\cdot 0$ or $x\\cdot 1$.', 'types/Points.v: bfield');
n('pt.sel', 'Select continuation', '$\\mathsf{sel\\_pt}\\,x\\,i = \\overline{x\\cdot\\kappa_i}$, the point of the end after $\\mathsf{select}_i$ at $x$.', 'Selecting end and branching end continue at the two sides $\\overline{x\\cdot\\kappa_i}$ and $x\\cdot\\kappa_i$ of one field.', DEF, '$\\mathsf{select}_{\\mathsf{false}}\\,o$ at $x$ continues at $\\overline{x\\cdot 0}$.', 'types/Points.v: sel_pt');
n('pt.bra', 'Branch continuation', '$\\mathsf{bra\\_pt}\\,x\\,i = x\\cdot\\kappa_i$, the point of the end after $\\mathsf{branch}$ at $\\overline{x}$ receives $i$.', 'It is $\\overline{\\mathsf{sel\\_pt}\\,x\\,i}$, the partner point of the selecting side.', DEF, '$\\mathsf{branch}$ at $\\overline{x}$ continues at $x\\cdot\\kappa_i$.', 'types/Points.v: bra_pt');
n('pt.payload', 'Payload fields', 'The $j$-th end of a message sent at $x$ sits at $x\\cdot j$.', '$\\overline{x}\\cdot j = x\\cdot j$, so sender at $x$ and receiver at $\\overline{x}$ compute the same points for the delivered ends.', DEF, 'A message on $y$ at $Y$ delivers its end at $Y\\cdot 0$.', 'types/Points.v: payload_pts');
n('lbl.field', 'Field label $\\kappa$', '$\\kappa \\in \\mathbb{N}$ selects the field $x\\cdot\\kappa$ of a point $x$.', 'Payloads, choices and the position of a new channel use fields. $x\\cdot\\kappa = x\\cdot\\kappa\'$ iff $\\kappa = \\kappa\'$.', 'Two channels created at one field $x\\cdot\\kappa$ sit at the same points $x\\cdot\\kappa$ and $\\overline{x\\cdot\\kappa}$, so no fact orders one before the other.', '$\\mathsf{bra\\_pt}\\,x\\,\\mathsf{true} = x\\cdot 1$.', 'lang/Syntax.v: field');
n('link.csub', '$\\mathsf{csub}$', '$\\mathsf{csub}\\,o_1\\,o_2 = \\{\\overline{o_1} \\mapsto o_2,\\ o_1 \\mapsto \\overline{o_2}\\}$, the identity elsewhere, applied to every thread after a link.', 'After the link, the holder of $\\overline{o_1}$ talks to the holder of $\\overline{o_2}$, so it holds $o_2$. The map identifies $\\overline{o_1}$ with $o_2$, so it is no bijection.', DEF, 'After $\\mathsf{link}\\,\\langle c^{+}, d^{-}\\rangle$ the holder of $c^{-}$ holds $d^{-}$.', 'lang/Syntax.v: csub');

// ---- signatures and arguments ----
const { sa } = require('./core');
const A = (name, meaning) => ({ name, meaning });
const E1 = A(R`e_1, e_2`, R`Subterms, $e_1, e_2 \in \mathsf{Expr}$.`);
sa('syn.var', R`x \in \mathsf{Expr}`, [A('x', R`A de Bruijn index $x \in \mathbb{N}$, the number of binders between the occurrence and its binder.`)]);
sa('syn.unit', R`\ast \in \mathsf{Val}`, []);
sa('syn.end', R`o \in \mathsf{Val}`, [A('o', R`An end $o \in \mathsf{End}$, one of $c^{+}, c^{-}$ for a channel $c$.`)]);
sa('syn.lam', R`\lambda e \in \mathsf{Val}`, [A('e', R`The body, $e \in \mathsf{Expr}$, with the argument as index $0$.`)]);
sa('syn.app', R`e_1\,e_2 \in \mathsf{Expr}`, [A('e_1', R`The function, evaluated first.`), A('e_2', R`The argument, evaluated once $e_1$ is a value.`)]);
sa('syn.pair', R`\langle e_1, e_2\rangle \in \mathsf{Expr}`, [E1]);
sa('syn.letu', R`\mathsf{let}\ \ast = e_1\ \mathsf{in}\ e_2 \in \mathsf{Expr}`, [A('e_1', R`A term of type $\ast$, evaluated first.`), A('e_2', R`The continuation, run after $e_1$ returns $\ast$.`)]);
sa('syn.letp', R`\mathsf{let}\ \langle a, b\rangle = e_1\ \mathsf{in}\ e_2 \in \mathsf{Expr}`, [A('e_1', R`A term that returns a pair $\langle v_1, v_2\rangle$.`), A(R`a, b`, R`The bound variables, $a$ at index $1$ for $v_1$ and $b$ at index $0$ for $v_2$.`), A('e_2', R`The body, in scope of $a$ and $b$.`)]);
sa('syn.let', R`\mathsf{let}\ a = e_1\ \mathsf{in}\ e_2 \in \mathsf{Expr}`, [A('a', R`The bound variable, standing for the value of $e_1$.`), A('u', R`A variable not free in $e_2$, bound to the unit component.`), E1]);
sa('syn.inj', R`\mathsf{inj}_i\,e \in \mathsf{Expr}`, [A('i', R`The side, $i \in \{1, 2\}$.`), A('e', R`The injected term.`)]);
sa('syn.case', R`\mathsf{case}\ e\,(a.e_1)\,(a.e_2) \in \mathsf{Expr}`, [A('e', R`The scrutinee, a term that returns $\mathsf{inj}_i\,v$.`), A('a', R`The variable bound to $v$ in each branch, index $0$.`), A(R`e_1, e_2`, R`The branches, $e_i$ runs when $e$ returns $\mathsf{inj}_i\,v$.`)]);
sa('syn.box', R`!e \in \mathsf{Val}`, [A('e', R`The body, with the box itself as index $0$.`)]);
sa('syn.new', R`\mathsf{new} \in \mathsf{Expr}`, []);
sa('syn.op', R`k \in \mathsf{Val}`, [A('k', R`A constant, $k \in \mathsf{Const}$.`)]);
const OA = A('o', R`The end acted on, $o \in \mathsf{End}$.`);
sa('prim.send', R`\mathsf{send} \in \mathsf{Const},\quad \mathsf{send}\,\langle v, o\rangle \xrightarrow{o!v} o`, [A('v', R`The payload, a value.`), OA]);
sa('prim.recv', R`\mathsf{recv} \in \mathsf{Const},\quad \mathsf{recv}\,o \xrightarrow{o?v} \langle v, o\rangle`, [OA, A('v', R`The received value, universally quantified over all values.`)]);
sa('prim.close', R`\mathsf{close} \in \mathsf{Const},\quad \mathsf{close}\,o \xrightarrow{o\,\mathsf{end}} \ast`, [OA]);
sa('prim.select', R`\mathsf{select}_i \in \mathsf{Const},\quad \mathsf{select}_i\,o \xrightarrow{o \lhd i} o`, [A('i', R`The chosen branch, $i \in \{\mathsf{false}, \mathsf{true}\}$.`), OA]);
sa('prim.branch', R`\mathsf{branch} \in \mathsf{Const},\quad \mathsf{branch}\,o \xrightarrow{o \rhd i} \mathsf{inj}_i\,o`, [OA, A('i', R`The received choice, quantified over both values.`)]);
sa('prim.link', R`\mathsf{link} \in \mathsf{Const},\quad \mathsf{link}\,\langle o_1, o_2\rangle \xrightarrow{\leftrightarrow\{o_1, o_2\}} \ast`, [A(R`o_1, o_2`, R`The two linked ends.`)]);
sa('prim.spawn', R`\mathsf{spawn} \in \mathsf{Const},\quad \mathsf{spawn}\,v \xrightarrow{\mathsf{spawn}\,v} \ast`, [A('v', R`The thunk, a value whose application $v\,\ast$ is the child thread.`)]);
sa('prim.force', R`\mathsf{force} \in \mathsf{Const},\quad \mathsf{force}\,(!e) \xrightarrow{\beta} e[!e]`, [A('e', R`The body of the forced box.`)]);
sa('syn.values', R`v \in \mathsf{Val} \subseteq \mathsf{Expr}`, [A(R`v_1, v_2`, R`Values.`), A('e', R`An arbitrary body.`), A('i', R`The side of an injection.`)]);
sa('end.cend', R`o \in \mathsf{End} = \{c^{+}, c^{-} \mid c \in \mathsf{Chan}\}`, [A('c', R`A channel name.`)]);
sa('end.dual', R`\overline{\cdot} : \mathsf{End} \to \mathsf{End}`, [A('o', R`An end, $\overline{o}$ is the other end of $\mathsf{ech}\,o$.`)]);
sa('end.ech', R`\mathsf{ech} : \mathsf{End} \to \mathsf{Chan}`, [A('o', R`An end, $\mathsf{ech}\,o$ is its channel.`)]);
sa('syn.fends', R`\mathsf{fends} : \mathsf{Expr} \to \mathcal{P}_{\mathrm{fin}}(\mathsf{End})`, [A('e', R`A term, $\mathsf{fends}(e)$ is the set of ends occurring in $e$.`)]);
sa('syn.fchans', R`\mathsf{fchans} : \mathsf{Expr} \to \mathcal{P}_{\mathrm{fin}}(\mathsf{Chan})`, [A('e', R`A term, $\mathsf{fchans}(e) = \mathsf{ech}[\mathsf{fends}(e)]$.`)]);
sa('proc.proc', R`p = (C, E) \in \mathsf{Proc} = \mathcal{P}_{\mathrm{fin}}(\mathsf{Chan}) \times \mathcal{M}_{\mathrm{fin}}(\mathsf{Expr})`, [A('C', R`The restricted channels.`), A('E', R`The threads, a finite multiset of terms.`)]);
sa('proc.config', R`q = (C, M) \in \mathsf{Config} = \mathcal{P}_{\mathrm{fin}}(\mathsf{Chan}) \times (\mathbb{N} \rightharpoonup_{\mathrm{fin}} \mathsf{Expr})`, [A('C', R`The restricted channels.`), A('M', R`The thread map, $M(i)$ the term of thread $i \in \mathrm{dom}\,M$.`)]);
sa('proc.erase', R`\mathsf{erase} : \mathsf{Config} \to \mathsf{Proc}`, [A(R`(C, M)`, R`A configuration, $\mathsf{erase}(C, M)$ keeps $C$ and the multiset of the terms $M(i)$.`), A('i', R`Ranges over $\mathrm{dom}\,M$.`)]);
sa('pt.const', R`a \in \mathsf{Root}`, [A('a', R`A root, $a \in A$ for the world $W$ in use.`)]);
sa('pt.var', R`\iota \in \mathsf{Root}`, [A(R`\iota`, R`A de Bruijn index over points, bound by $\Box\forall\bar\iota$, by $\exists^m\bar\iota$ or by the existential of $\mathsf{new}$.`)]);
sa('pt.shift', R`(\cdot)^{+} : \mathsf{Point} \to \mathsf{Point}`, [A('x', R`A point, $x^{+}$ has the offset of $x$ plus $1$.`)]);
sa('pt.field', R`(\cdot)\cdot\kappa : \mathsf{Point} \times \mathbb{N} \to \mathsf{Point}`, [A('x', R`The parent point.`), A(R`\kappa`, R`The field label, $\kappa \in \mathbb{N}$.`)]);
sa('pt.dual', R`\overline{\cdot} : \mathsf{Point} \to \mathsf{Point}`, [A('x', R`A point, $\overline{x}$ has the opposite polarity.`)]);
sa('pt.laws', R`\forall x \in \mathsf{Point}, \kappa \in \mathbb{N}.\ \overline{\overline{x}} = x \land \overline{x}\cdot\kappa = x\cdot\kappa \land \overline{x^{+}} = \overline{x}^{+}`, [A('x', R`An arbitrary point.`), A(R`\kappa`, R`An arbitrary field label.`)]);
sa('sx.kappai', R`\kappa_{(\cdot)} : \mathbb{B} \to \mathbb{N}`, [A('i', R`A choice, $i \in \{\mathsf{false}, \mathsf{true}\}$.`)]);
sa('pt.sel', R`\mathsf{sel\_pt} : \mathsf{Point} \to \mathbb{B} \to \mathsf{Point}`, [A('x', R`The point of the selecting end before the step.`), A('i', R`The selected branch.`)]);
sa('pt.bra', R`\mathsf{bra\_pt} : \mathsf{Point} \to \mathbb{B} \to \mathsf{Point}`, [A('x', R`The point of the selecting partner, the branching end sits at $\overline{x}$.`), A('i', R`The received choice.`)]);
sa('pt.payload', R`\mathsf{payload\_pts} : \mathsf{Point} \to \mathbb{N} \to \mathsf{Point}^{*}`, [A('x', R`The point of the carrier end at the send.`), A('m', R`The number of point variables the payload binds.`)]);
sa('lbl.field', R`\kappa \in \mathbb{N}`, [A(R`\kappa`, R`A field label.`)]);
sa('link.csub', R`\mathsf{csub} : \mathsf{End} \to \mathsf{End} \to \mathsf{End} \to \mathsf{End}`, [A(R`o_1, o_2`, R`The linked ends, the channel of $o_1$ disappears.`), A('o', R`The end being renamed.`)]);
