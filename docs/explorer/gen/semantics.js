const { R, h, n, section, block, rule, Q, DEF } = require('./core');

const s = section('semantics', 'Semantics',
  'This section introduces thread labels $\\alpha$ and session labels $\\sigma$, head steps $e \\xrightarrow{\\alpha} e\'$, frames $f[e]$, substitution $e[v]$, configuration steps $(C, M) \\to (C\', M\')$ with events $ev$ and participants $\\mathsf{parts}(ev)$, runs $(r, l)$, and the properties $\\mathsf{deadlock\\_free}$, $\\mathsf{no\\_tau\\_divergence}$ and $\\mathsf{lock\\_free}$. Signatures name the sorts $\\mathsf{TLabel}$ and $\\mathsf{SLabel}$ of thread and session labels, $\\mathsf{Frame}$ of frames, $\\mathsf{Event}$ of events and $\\mathsf{Run}$ of runs.');

const step = (a) => R`\xrightarrow{${a}}`;
block(s, {
  id: 'sem-labels', title: 'Thread labels', rocq: 'lang/Semantics.v: tlabel, slabel',
  tex: R`\begin{array}{rl}
\alpha ::= & ${h('lbl.beta', R`\beta`)} \mid ${h('lbl.new', R`\mathsf{new}\,c`)} \mid ${h('lbl.spawn', R`\mathsf{spawn}\,v`)} \mid ${h('se.slabel', R`\sigma`)} \\
\sigma ::= & ${h('lbl.send', R`o!v`)} \mid ${h('lbl.recv', R`o?v`)} \mid ${h('lbl.close', R`o\,\mathsf{end}`)} \mid ${h('lbl.sel', R`o \lhd i`)} \mid ${h('lbl.bra', R`o \rhd i`)} \mid ${h('lbl.link', R`\leftrightarrow\{o_1,o_2\}`)}
\end{array}`,
  caption: '$\\beta$ covers application, unit and pair elimination, case and force, and session labels $\\sigma$ are offers on ends.'
});
block(s, {
  id: 'sem-head', title: 'Head steps (T-Act rules)', rocq: 'lang/Semantics.v: head_step',
  tex: R`\begin{array}{l}
${h('T-Act-App', R`(\lambda e)\,v ${step(R`\beta`)} ${h('se.subst', R`e[v]`)}`)} \\
${h('T-Act-Force', R`\mathsf{force}\,(!e) ${step(R`\beta`)} e[!e]`)} \qquad ${h('T-Act-New', R`\mathsf{new} ${step(R`\mathsf{new}\,c`)} \langle c^{+}, c^{-}\rangle`)} \\
${h('T-Act-Spawn', R`\mathsf{spawn}\,v ${step(R`\mathsf{spawn}\,v`)} \ast`)} \\
${h('T-Act-Send', R`\mathsf{send}\,\langle v, o\rangle ${step(R`o!v`)} o`)} \\
${h('T-Act-Recv', R`\mathsf{recv}\,o ${step(R`o?v`)} \langle v, o\rangle`)} \qquad ${h('T-Act-Close', R`\mathsf{close}\,o ${step(R`o\,\mathsf{end}`)} \ast`)} \\
${h('T-Act-Select', R`\mathsf{select}_i\,o ${step(R`o\lhd i`)} o`)} \qquad ${h('T-Act-Branch', R`\mathsf{branch}\,o ${step(R`o\rhd i`)} \mathsf{inj}_i\,o`)} \\
${h('T-Act-Link', R`\mathsf{link}\,\langle o_1, o_2\rangle ${step(R`\leftrightarrow\{o_1,o_2\}`)} \ast`)}
\end{array}`,
  caption: 'One head rule per redex, where $\\mathsf{recv}\\,o$ has a step for every value $v$.'
});
block(s, {
  id: 'sem-ctx', title: 'Evaluation frames (T-Act-Ctx)', rocq: 'lang/Semantics.v: tstep, frame_val',
  tex: rule('T-Act-Ctx', R`${h('T-Act-Ctx', R`e ${step(R`\alpha`)} e'`)}${Q}${h('sem.frameval', R`\mathsf{frame\_val}\,f`)}`, R`${h('se.frame', R`f[e]`)} ${step(R`\alpha`)} f[e']`),
  caption: 'Steps lift through one evaluation frame $f$ at a time, never under $\\lambda$ or $!$.'
});
block(s, {
  id: 'sem-proc', title: 'Process steps (P-Act rules)', rocq: 'lang/Process.v: istep',
  tex: R`\begin{array}{l}
${h('P-Act-Beta', R`M(i) ${step(R`\beta`)} e'`)} \\ \qquad \Rightarrow\ (C, ${h('se.upd', R`M[i \mapsto e']`)}) \\[4pt]
${h('P-Act-New', R`M(i) ${step(R`\mathsf{new}\,c`)} e',\ ${h('sem.fresh-global', R`c \notin C \cup ${h('se.echans', R`\mathsf{echans}(M)`)}`)}`)} \\ \qquad \Rightarrow\ (C \cup \{c\}, M[i\mapsto e']) \\[4pt]
${h('P-Act-Spawn', R`M(i) ${step(R`\mathsf{spawn}\,v`)} e',\ j \notin \mathsf{dom}\,M`)} \\ \qquad \Rightarrow\ (C, M[i\mapsto e'][j \mapsto v\,\ast]) \\[4pt]
${h('P-Act-Msg', R`M(i) ${step(R`o!v`)} e',\ M(j) ${step(R`\overline{o}?v`)} f',\ i \neq j`)} \\ \qquad \Rightarrow\ (C, M[i\mapsto e'][j\mapsto f']) \\[4pt]
${h('P-Act-Close', R`M(i) ${step(R`o\,\mathsf{end}`)} e',\ M(j) ${step(R`\overline{o}\,\mathsf{end}`)} f',\ i \neq j,\ ${h('end.ech', R`\mathsf{ech}`)}\,o \in C`)} \\ \qquad \Rightarrow\ (C \setminus \{${h('end.ech', R`\mathsf{ech}`)}\,o\}, M[i\mapsto e'][j\mapsto f']) \\[4pt]
${h('P-Act-Choice', R`M(i) ${step(R`o\lhd b`)} e',\ M(j) ${step(R`\overline{o}\rhd b`)} f',\ i \neq j`)} \\ \qquad \Rightarrow\ (C, M[i\mapsto e'][j\mapsto f']) \\[4pt]
${h('P-Act-Link', R`M(i) ${step(R`\leftrightarrow\{o_1,o_2\}`)} e',\ ${h('end.ech', R`\mathsf{ech}`)}\,o_1 \in C`)} \\ \qquad \Rightarrow\ (C\setminus\{${h('end.ech', R`\mathsf{ech}`)}\,o_1\}, ${h('link.csub', R`\mathsf{csub}\,o_1\,o_2`)} \circ M[i\mapsto e']) \\[4pt]
${h('P-Act-Session', R`M(i) ${step(R`\sigma`)} e',\ ${h('se.subj', R`\mathsf{subj}\,\sigma`)} \cap C = \varnothing`)} \\ \qquad \Rightarrow\ (C \setminus ${h('sem.sentc', R`\mathsf{sentc}\,\sigma`)}, M[i\mapsto e'])
\end{array}`,
  caption: 'Each rule turns steps of one or two threads into a step of $(C, M)$.'
});
block(s, {
  id: 'sem-events', title: 'Events', rocq: 'lang/Process.v: event, ev_parts, ev_admin, ev_tau',
  tex: R`\begin{array}{l}
${h('ev.event', R`ev ::= \mathsf{solo}_i\,\alpha\,k \mid \mathsf{sync}_{i,j}\,\sigma \mid \mathsf{offer}_i\,\sigma`)} \qquad ${h('ev.pick', R`k ::= \cdot \mid j \mid (o_1, o_2)`)} \\
${h('ev.admin', R`\mathsf{admin} = \{\mathsf{solo}_i\,\alpha\,k\}`)} \qquad ${h('ev.tau', R`\tau = \mathsf{Event} \setminus \{\mathsf{offer}_i\,\sigma\}`)} \qquad ${h('se.parts', R`\mathsf{parts}(ev)`)}
\end{array}`,
  caption: 'An event names the threads $\\mathsf{parts}(ev)$ and the labels they take.'
});
block(s, {
  id: 'sem-props', title: 'Properties', rocq: 'lang/Safety.v: deadlock_free, lockfree/TauThread.v: no_tau_divergence, lockfree/Fair.v: lock_free',
  tex: R`\begin{array}{l}
${h('prop.terminated', R`\mathsf{terminated}\,p \iff p = (\varnothing, \{v\} \uplus E),\ E \subseteq \{\ast\}`)} \\
${h('prop.df', R`\mathsf{deadlock\_free}\,p \iff \forall p'.\ p ${h('se.reach', R`\to^{*}`)} p' \Rightarrow \mathsf{terminated}\,p' \lor \exists p''.\ p' \to p''`)}
\annraw{ \\ }\annot{${h('prop.notau', R`\mathsf{no\_tau\_divergence}\,p \iff \forall q.\ p \to^{*} q \Rightarrow ${h('se.acc', R`\mathsf{Acc}`)}\ ${h('prop.padmin', R`\to_{\mathsf{admin}}`)}\ q`)}}
\annraw{ \\ }\annot{${h('prop.lf', R`\begin{array}{l} \mathsf{lock\_free}\,p \iff \forall ${h('se.run', R`(r, l) \in \mathsf{Run}`)}.\ ${h('se.r0', R`${h('proc.erase', R`\mathsf{erase}`)}(r_0) = p`)} \Rightarrow ${h('prop.maximal', R`\mathsf{maximal}\,r\,l`)} \Rightarrow ${h('prop.wfair', R`\mathsf{wfair}\,r\,l`)} \Rightarrow {} \\ \qquad ${h('prop.lfrun', R`\forall i\,t.\ ${h('prop.pend', R`\mathsf{pend}(r_i, t)`)} \Rightarrow \exists j \geq i.\ t \in ${h('se.parts', R`\mathsf{parts}(l_j)`)}`)} \end{array}`)}}
\end{array}`,
  caption: 'Termination and deadlock freedom, and for lock freedom also absence of internal divergence and lock freedom over weakly fair maximal runs $(r, l)$.'
});

// ---- notes ----
n('se.slabel', 'Session label $\\sigma$', 'A label $\\sigma$ of a step that acts on an end and synchronizes with a partner thread or with the environment.', 'Session labels are exactly the steps a thread can wait on. Readiness and the obligations of the relation are stated over session labels.', DEF, '$o?v$ and $o\\,\\mathsf{end}$ are session labels, $\\beta$ is none.', 'lang/Semantics.v: slabel');
n('se.subst', 'Substitution $e[v]$', '$e[v]$ is $e$ with the value $v$ for the variable of index $0$, and the other indices lowered by one.', 'A plain definition. Application, the two lets, case and force step by substitution.', DEF, '$(\\mathsf{close}\\,x)[c^{+}] = \\mathsf{close}\\,c^{+}$.', 'lang/Syntax.v: subst1');
n('se.frame', 'Frame filling $f[e]$', 'An evaluation frame $f$ is a term with one hole in evaluation position, and $f[e]$ fills the hole with $e$.', 'A plain definition. The frames fix where the next step of a term happens.', DEF, 'For $f = \\mathsf{let}\\ \\ast = \\square\\ \\mathsf{in}\\ e_2$, $f[\\mathsf{close}\\,c^{+}] = \\mathsf{let}\\ \\ast = \\mathsf{close}\\,c^{+}\\ \\mathsf{in}\\ e_2$.', 'lang/Semantics.v: frame, fill_frame');
n('se.upd', 'Map update $M[i \\mapsto e]$', '$M[i \\mapsto e]$ maps $i$ to $e$ and every $j \\neq i$ to $M(j)$.', 'A plain definition.', DEF, '$\\{0 \\mapsto e\\}[0 \\mapsto e\'] = \\{0 \\mapsto e\'\\}$.', 'lang/Process.v: istep');
n('se.echans', '$\\mathsf{echans}(M)$', '$\\mathsf{echans}(M) = \\bigcup_{i \\in \\mathrm{dom}\\,M} \\mathsf{fchans}(M(i))$, the channels some thread mentions.', 'A created channel $c$ satisfies $c \\notin \\mathsf{echans}(M)$, so it differs from every channel a thread mentions.', DEF, '$\\mathsf{echans}\\{0 \\mapsto \\mathsf{close}\\,c^{+}, 1 \\mapsto \\mathsf{close}\\,d^{-}\\} = \\{c, d\\}$.', 'lang/Syntax.v: echans');
n('se.subj', 'Subjects $\\mathsf{subj}\\,\\sigma$', '$\\mathsf{subj}\\,\\sigma$ is the set of channels $\\sigma$ acts on, $\\{\\mathsf{ech}\\,o\\}$ for an action on $o$ and $\\{\\mathsf{ech}\\,o_1, \\mathsf{ech}\\,o_2\\}$ for a link.', 'An offer to the environment requires $\\mathsf{subj}\\,\\sigma \\cap C = \\varnothing$, so it uses only interface channels.', DEF, '$\\mathsf{subj}(o?v) = \\{\\mathsf{ech}\\,o\\}$.', 'lang/Semantics.v: subjs');
n('se.parts', 'Participants $\\mathsf{parts}(ev)$', '$\\mathsf{parts}(\\mathsf{sync}_{i,j}\\,\\sigma) = \\{i, j\\}$, $\\mathsf{parts}(\\mathsf{solo}_i\\,\\alpha\\,k) = \\mathsf{parts}(\\mathsf{offer}_i\\,\\sigma) = \\{i\\}$, and $\\mathsf{parts}(\\bot) = \\varnothing$ for a stutter. A spawn names only the parent $i$.', 'A thread takes part in a step iff it is in $\\mathsf{parts}$ of its event. Weak fairness and lock freedom ask whether $t \\in \\mathsf{parts}(l_j)$ for some position $j$.', DEF, '$\\mathsf{parts}(\\mathsf{sync}_{0,1}\\,(a^{+}!\\ast)) = \\{0, 1\\}$.', 'lang/Process.v: ev_parts, lockfree/Fair.v: lparts');
n('se.reach', 'Reachability $\\to^{*}$', '$p \\to^{*} p\'$ when $p$ reaches $p\'$ in finitely many $\\tau$ steps.', 'A plain definition. Deadlock freedom and absence of internal divergence quantify over all $p\'$ with $p \\to^{*} p\'$.', DEF, '$p \\to^{*} p$ for every $p$.', 'lang/Process.v: pred_star');
n('se.acc', 'Accessibility $\\mathsf{Acc}$', '$\\mathsf{Acc}\\,R\\,q$ holds when every $R$-chain $q = q_0\\,R\\,q_1\\,R \\cdots$ is finite, inductively, when $\\mathsf{Acc}\\,R\\,q\'$ for every $q\'$ with $q\\,R\\,q\'$.', 'It states the absence of infinite $R$-chains from $q$ by induction, so proofs consume it by well-founded induction.', DEF, 'If every administrative chain from $q$ has length at most $2$, then $\\mathsf{Acc}\\ {\\to_{\\mathsf{admin}}}\\ q$.', 'Coq.Init.Wf: Acc');
n('se.r0', 'The run starts at $p$', '$r_0$ is the configuration at position $0$ of the run, and $\\mathsf{erase}(r_0) = p$ states that forgetting its thread names gives the process $p$.', 'Lock freedom is a property of a process, and runs are sequences of configurations, so the run must start at a configuration of $p$. Any naming of the threads of $p$ is allowed.', DEF, '$r_0 = (\\{c\\}, \\{0 \\mapsto \\mathsf{close}\\,c^{+},\\ 1 \\mapsto \\mathsf{close}\\,c^{-}\\})$ for $p = (\\{c\\}, \\{\\!|\\mathsf{close}\\,c^{+}, \\mathsf{close}\\,c^{-}|\\!\\})$.', 'lockfree/Fair.v: lock_free');
n('se.run', 'Runs $r$ and $l$', 'A run is a pair of sequences, $r_i$ the configuration at position $i$ and $l_i$ the event of the step from $r_i$ to $r_{i+1}$, or none when $r_{i+1} = r_i$ stutters.', 'Lock freedom quantifies over infinite runs and speaks of positions $i \\leq j$ in a run.', DEF, '$r_0 = (\\varnothing, \\{0 \\mapsto main\\})$.', 'lockfree/Fair.v: run_step');
n('lbl.beta', '$\\beta$ label', 'The label of application, unit and pair elimination, case and force.', 'These steps have the same cost $\\kappa(\\beta)$ in each cost table, so one label covers these steps.', DEF, '$\\mathsf{force}\\,(!e) \\xrightarrow{\\beta} e[!e]$.', 'lang/Semantics.v: LBeta');
n('lbl.new', 'Label $\\mathsf{new}\\,c$', 'It contains the name $c$ of the new channel.', 'The process rule reads $c$ to keep names fresh. Position and facts of $c$ are no part of the label, and the relation chooses position and facts.', DEF, '$\\mathsf{new} \\xrightarrow{\\mathsf{new}\\,c} \\langle c^{+}, c^{-}\\rangle$.', 'lang/Semantics.v: LNew');
n('lbl.spawn', 'Label $\\mathsf{spawn}\\,v$', 'It contains the thunk $v$ that starts the child thread $v\\,\\ast$.', 'The relation splits the environment of the parent as $\\Theta = \\Theta_c \\uplus \\Theta_r$ with $v$ in the thunk relation at $\\Theta_c$. Exactness of $V$ gives $\\mathrm{dom}\\,\\Theta_c = \\mathsf{fends}(v)$, so the split is determined by $v$.', DEF, '$\\mathsf{spawn}\\,(\\lambda u.\\,\\mathsf{close}\\,d\')$ transfers $d\'$ to the child.', 'lang/Semantics.v: LSpawn');
n('lbl.send', 'Send label $o!v$', 'An offer to send the value $v$ on the end $o$.', 'The relation, the fuel layer and scope extrusion read the ends that leave as $\\mathsf{fends}(v)$. For $v$ in $V$ at $\\Theta_v$ this set is $\\mathrm{dom}\\,\\Theta_v$.', DEF, 'Sending the end $a$ on $o$ has the label $o!a$.', 'lang/Semantics.v: SSend');
n('lbl.recv', 'Receive label $o?v$', 'An offer to receive $v$ on $o$, for every value $v$.', 'A receive must meet every send of a partner, so its labels range over all values.', DEF, '$\\mathsf{recv}\\,o \\xrightarrow{o?\\ast} \\langle \\ast, o\\rangle$.', 'lang/Semantics.v: SRecv');
n('lbl.close', 'Close label $o\\,\\mathsf{end}$', 'An offer to close $o$.', 'A plain label. Its obligation removes $o$ from the environment $\\Theta$, so after a close $o \\notin \\mathrm{dom}\\,\\Theta$.', DEF, '$\\mathsf{close}\\,c^{+} \\xrightarrow{c^{+}\\,\\mathsf{end}} \\ast$.', 'lang/Semantics.v: SClose');
n('lbl.sel', 'Select label $o \\lhd i$', 'An offer to select branch $i$ on $o$.', 'A plain label. Its obligation moves $o$ from $x$ to $\\overline{x\\cdot\\kappa_i}$.', DEF, '$\\mathsf{select}_{\\mathsf{true}}\\,o \\xrightarrow{o \\lhd \\mathsf{true}} o$.', 'lang/Semantics.v: SSel');
n('lbl.bra', 'Branch label $o \\rhd i$', 'An offer to receive the choice $i$ on $o$, for both $i$.', 'A plain label. $\\mathsf{branch}$ must meet either choice of the partner, so it has a step for each $i$, and the obligation moves $o$ to $x\\cdot\\kappa_i$.', DEF, '$\\mathsf{branch}\\,o$ has the labels $o \\rhd \\mathsf{false}$ and $o \\rhd \\mathsf{true}$.', 'lang/Semantics.v: SBra');
n('lbl.link', 'Link label $\\leftrightarrow\\{o_1, o_2\\}$', 'An unordered pair $\\{o_1, o_2\\}$ of ends, possibly with $o_1 = o_2$.', 'The label is a set, so one process rule removes the channel of either end.', DEF, '$\\leftrightarrow\\{c^{+}, d^{-}\\}$.', 'lang/Semantics.v: SLink');
n('T-Act-App', 'T-Act-App', '$(\\lambda e)\\,v \\xrightarrow{\\beta} e[v]$.', 'Call by value. The argument is a value before the body runs.', DEF, '$(\\lambda x.\\,\\mathsf{close}\\,x)\\,c^{+} \\xrightarrow{\\beta} \\mathsf{close}\\,c^{+}$.', 'lang/Semantics.v: t_act_app');
n('T-Act-Force', 'T-Act-Force', '$\\mathsf{force}\\,(!e) \\xrightarrow{\\beta} e[!e]$, so the body runs with the box for its self.', 'It is the only rule that unrolls a definition, so recursion and replication go through force steps.', DEF, '$\\mathsf{force}\\,!(f = \\mathsf{force}\\,f)$ steps to itself by $\\beta$ forever.', 'lang/Semantics.v: t_act_force');
n('T-Act-New', 'T-Act-New', '$\\mathsf{new} \\xrightarrow{\\mathsf{new}\\,c} \\langle c^{+}, c^{-}\\rangle$ for every $c$, and the process rule picks $c$.', 'The step of a single thread cannot determine which channel names are in use. The process rule asks $c \\notin C \\cup \\mathsf{echans}(M)$.', DEF, '$\\mathsf{new} \\xrightarrow{\\mathsf{new}\\,c} \\langle c^{+}, c^{-}\\rangle$.', 'lang/Semantics.v: t_act_new');
n('T-Act-Spawn', 'T-Act-Spawn', '$\\mathsf{spawn}\\,v \\xrightarrow{\\mathsf{spawn}\\,v} \\ast$.', 'The label contains $v$, so the process rule can start the thread $v\\,\\ast$.', DEF, '$\\mathsf{spawn}\\,(\\lambda u.\\,\\mathsf{close}\\,d\') \\xrightarrow{\\mathsf{spawn}\\,(\\lambda u.\\,\\mathsf{close}\\,d\')} \\ast$.', 'lang/Semantics.v: t_act_spawn');
n('T-Act-Send', 'T-Act-Send', '$\\mathsf{send}\\,\\langle v, o\\rangle \\xrightarrow{o!v} o$.', 'The label contains the payload $v$, which the receiving thread obtains by the process rule.', DEF, '$\\mathsf{send}\\,\\langle \\ast, c^{+}\\rangle \\xrightarrow{c^{+}!\\ast} c^{+}$.', 'lang/Semantics.v: t_act_send');
n('T-Act-Recv', 'T-Act-Recv', '$\\mathsf{recv}\\,o \\xrightarrow{o?v} \\langle v, o\\rangle$ for every value $v$.', 'The step of a single thread does not depend on what the partner sends, so it has a step for each $v$. The receive obligation quantifies only over $v$ in the value relation at the payload type.', DEF, '$\\mathsf{recv}\\,b \\xrightarrow{b?\\ast} \\langle \\ast, b\\rangle$.', 'lang/Semantics.v: t_act_recv');
n('T-Act-Close', 'T-Act-Close', '$\\mathsf{close}\\,o \\xrightarrow{o\\,\\mathsf{end}} \\ast$.', 'A plain rule. The process rule pairs it with $\\overline{o}\\,\\mathsf{end}$ in another thread.', DEF, '$\\mathsf{close}\\,c^{+} \\xrightarrow{c^{+}\\,\\mathsf{end}} \\ast$.', 'lang/Semantics.v: t_act_close');
n('T-Act-Select', 'T-Act-Select', '$\\mathsf{select}_i\\,o \\xrightarrow{o \\lhd i} o$, returning the same end name.', 'The end keeps its name $o$, so no step reads a point.', DEF, '$\\mathsf{select}_{\\mathsf{true}}\\,o \\xrightarrow{o \\lhd \\mathsf{true}} o$.', 'lang/Semantics.v: t_act_select');
n('T-Act-Branch', 'T-Act-Branch', '$\\mathsf{branch}\\,o \\xrightarrow{o \\rhd i} \\mathsf{inj}_i\\,o$ for both $i$.', 'Either choice may arrive, so the thread has one step for each $i$.', DEF, '$\\mathsf{branch}\\,o \\xrightarrow{o \\rhd \\mathsf{true}} \\mathsf{inj}_2\\,o$.', 'lang/Semantics.v: t_act_branch');
n('T-Act-Link', 'T-Act-Link', '$\\mathsf{link}\\,\\langle o_1, o_2\\rangle \\xrightarrow{\\leftrightarrow\\{o_1, o_2\\}} \\ast$. The label is a set, so $\\langle o_1, o_2\\rangle$ and $\\langle o_2, o_1\\rangle$ give one label.', 'The renaming $\\mathsf{csub}\\,o_1\\,o_2$ concerns other threads, so the process rule performs the renaming.', DEF, '$\\mathsf{link}\\,\\langle c^{+}, d^{-}\\rangle \\xrightarrow{\\leftrightarrow\\{c^{+}, d^{-}\\}} \\ast$.', 'lang/Semantics.v: t_act_link');
n('T-Act-Ctx', 'T-Act-Ctx', 'If $e \\xrightarrow{\\alpha} e\'$ and $\\mathsf{frame\\_val}\\,f$, then $f[e] \\xrightarrow{\\alpha} f[e\']$.', 'No frame has its hole under $\\lambda$ or $!$, so the bodies of closures and boxes take no step before they are called.', DEF, '$\\mathsf{let}\\ \\ast = \\mathsf{close}\\,c^{+}\\ \\mathsf{in}\\ e$ steps when $\\mathsf{close}\\,c^{+}$ does.', 'lang/Semantics.v: t_act_ctx');
n('sem.frameval', '$\\mathsf{frame\\_val}$', '$\\mathsf{frame\\_val}\\,f$ holds when every subterm of $f$ left of the hole is a value.', 'It fixes left-to-right evaluation, so every term has at most one redex position.', DEF, '$\\mathsf{frame\\_val}(v_1\\,\\square)$ requires $v_1$ to be a value.', 'lang/Semantics.v: frame_val');
n('P-Act-Beta', 'P-Act-Beta', 'If $M(i) \\xrightarrow{\\beta} e\'$, then $(C, M) \\to (C, M[i \\mapsto e\'])$ with event $\\mathsf{solo}_i\\,\\beta\\,\\cdot$.', 'A plain rule. A $\\beta$ step changes only thread $i$.', DEF, 'A $\\beta$ step of thread $0$.', 'lang/Process.v: p_act_beta');
n('P-Act-New', 'P-Act-New', 'If $M(i) \\xrightarrow{\\mathsf{new}\\,c} e\'$ and $c \\notin C \\cup \\mathsf{echans}(M)$, then $(C, M) \\to (C \\cup \\{c\\}, M[i \\mapsto e\'])$.', 'Both ends of $c$ start in thread $i$, so $c$ is internal to the process and joins $C$.', DEF, '$\\mathsf{new}$ creates $c$ with $c \\notin C$.', 'lang/Process.v: p_act_new');
n('sem.fresh-global', 'Global freshness', '$c \\notin C \\cup \\mathsf{echans}(M)$, so $c$ is neither restricted nor mentioned by any thread.', 'Channel names are global. If $c \\in \\mathsf{fchans}(M(j))$ for some $j$, the new channel would share its name with a channel thread $j$ uses.', 'Reusing a name some thread still mentions merges two channels into one, and an action on one channel synchronizes with an action on the other.', '$c \\notin C \\cup \\mathsf{echans}(M)$.', 'lang/Process.v: p_act_new');
n('P-Act-Spawn', 'P-Act-Spawn', 'If $M(i) \\xrightarrow{\\mathsf{spawn}\\,v} e\'$ and $j \\notin \\mathrm{dom}\\,M$, then $M$ becomes $M[i \\mapsto e\'][j \\mapsto v\\,\\ast]$.', 'The event is $\\mathsf{solo}_i\\,(\\mathsf{spawn}\\,v)\\,j$, so only thread $i$ takes part.', DEF, '$\\mathsf{spawn}\\,(\\lambda u.\\,e)$ adds a thread $j$ running $(\\lambda u.\\,e)\\,\\ast$.', 'lang/Process.v: p_act_spawn');
n('P-Act-Msg', 'P-Act-Msg', '$M(i) \\xrightarrow{o!v} e\'$, $M(j) \\xrightarrow{\\overline{o}?v} f\'$, $i \\neq j$ give $M[i \\mapsto e\'][j \\mapsto f\']$, with no condition on $C$.', 'In a typed process both ends of $c$ are held inside only when $c \\in C$, so dropping the condition $\\mathsf{ech}\\,o \\in C$ adds no step to typed processes.', DEF, 'The client sends on $a$ and the server receives on $a\'$.', 'lang/Process.v: p_act_msg');
n('P-Act-Close', 'P-Act-Close', 'If $M(i) \\xrightarrow{o\\,\\mathsf{end}} e\'$, $M(j) \\xrightarrow{\\overline{o}\\,\\mathsf{end}} f\'$ and $\\mathsf{ech}\\,o \\in C$, then $C$ becomes $C \\setminus \\{\\mathsf{ech}\\,o\\}$.', 'After both closes no thread holds an end of $\\mathsf{ech}\\,o$, so the channel leaves $C$.', DEF, '$\\mathsf{close}\\,c^{+}$ and $\\mathsf{close}\\,c^{-}$ in two threads remove $c$.', 'lang/Process.v: p_act_close');
n('P-Act-Choice', 'P-Act-Choice', 'If $M(i) \\xrightarrow{o \\lhd b} e\'$ and $M(j) \\xrightarrow{\\overline{o} \\rhd b} f\'$ with the same $b$, then $M$ becomes $M[i \\mapsto e\'][j \\mapsto f\']$.', 'Requiring the same $b$ passes the choice of thread $i$ to thread $j$.', DEF, '$\\mathsf{select}_{\\mathsf{true}}\\,o$ meets $\\mathsf{branch}\\,\\overline{o}$, which steps to $\\mathsf{inj}_2\\,\\overline{o}$.', 'lang/Process.v: p_act_choice');
n('P-Act-Link', 'P-Act-Link', 'If $M(i) \\xrightarrow{\\leftrightarrow\\{o_1, o_2\\}} e\'$ and $\\mathsf{ech}\\,o_1 \\in C$, then $C$ loses $\\mathsf{ech}\\,o_1$ and every thread of $M[i \\mapsto e\']$ is renamed by $\\mathsf{csub}\\,o_1\\,o_2$.', 'The label is unordered, so the rule applies with either end as $o_1$ and removes the channel of either end.', DEF, '$\\mathsf{link}\\,\\langle c^{+}, d^{-}\\rangle$ with $c \\in C$.', 'lang/Process.v: p_act_link');
n('P-Act-Session', 'P-Act-Session', 'If $M(i) \\xrightarrow{\\sigma} e\'$ and $\\mathsf{subj}\\,\\sigma \\cap C = \\varnothing$, then $(C, M) \\to (C \\setminus \\mathsf{sentc}\\,\\sigma, M[i \\mapsto e\'])$, an offer to the environment.', 'A send of $v$ to the environment moves the ends $\\mathsf{fends}(v)$, so their channels leave $C$. The process and the relation compute the extruded channels from the same $v$.', DEF, 'An external send of a restricted $d^{+}$ removes $d$ from $C$.', 'lang/Process.v: p_act_session');
n('sem.sentc', '$\\mathsf{sentc}$', '$\\mathsf{sentc}(o!v) = \\mathsf{fchans}(v) = \\{\\mathsf{ech}\\,o\' \\mid o\' \\in \\mathsf{fends}(v)\\}$, and $\\mathsf{sentc}\\,\\sigma = \\varnothing$ for every other $\\sigma$.', 'These are the channels a message to the environment moves out of the process.', DEF, '$\\mathsf{sentc}(o!d^{+}) = \\{d\\}$.', 'lang/Semantics.v: sentc');
n('ev.event', 'Event', '$\\mathsf{solo}_i\\,\\alpha\\,k$ is a step of thread $i$ alone with thread label $\\alpha$. $\\mathsf{sync}_{i,j}\\,\\sigma$ is a step in which thread $i$ takes the send, close or select $\\sigma$ on an end $o$ and thread $j$ the matching receive, close or branch on $\\overline{o}$. $\\mathsf{offer}_i\\,\\sigma$ is an offer of thread $i$ to the environment.', 'Weak fairness asks of each thread $t$ that $t \\in \\mathsf{parts}(l_j)$ for some $j$, so every step names its threads.', DEF, '$\\mathsf{sync}_{0,1}\\,(a^{+}!\\ast)$.', 'lang/Process.v: event');
n('ev.pick', 'Pick $k$', 'What a process rule chooses beyond the thread label. $k = j$ names the new thread of a spawn. $k = (o_1, o_2)$ orders the ends of a link, so the channel of $o_1$ goes and the thread with $\\overline{o_1}$ then holds $o_2$. Every other solo step has $k = \\cdot$.', 'The thread label of a link is the unordered set $\\{o_1, o_2\\}$, and the thread label of a spawn names no thread, so the event records the choice the rule makes.', DEF, '$\\mathsf{solo}_0\\,(\\leftrightarrow\\{c^{+}, d^{-}\\})\\,(c^{+}, d^{-})$ removes $c$.', 'lang/Process.v: pick');
n('ev.admin', 'Administrative events', '$\\mathsf{admin}$ is the set of solo events $\\mathsf{solo}_i\\,\\alpha\\,k$, the steps by $\\beta$, $\\mathsf{new}$, $\\mathsf{spawn}$ and $\\mathsf{link}$, each of cost $0$ in $\\kappa_L$.', 'They act on no protocol. Absence of internal divergence states that every chain of them is finite.', DEF, 'An unbounded chain of spawns takes only administrative steps.', 'lang/Process.v: ev_admin');
n('ev.tau', '$\\tau$ events', 'Every event except $\\mathsf{offer}_i\\,\\sigma$, an offer to the environment.', 'A closed configuration has no environment, so all its steps are $\\tau$ steps.', DEF, '$\\mathsf{sync}_{0,1}\\,(a^{+}!\\ast)$ is a $\\tau$ event.', 'lang/Process.v: ev_tau, itstep');
n('prop.terminated', '$\\mathsf{terminated}$', '$\\mathsf{terminated}\\,p$ iff $p = (\\varnothing, \\{\\!|v|\\!\\} \\uplus E)$ with $v$ a value and $e = \\ast$ for every $e \\in E$.', 'At the end $C = \\varnothing$, so every channel is used up, and only the main thread returns a value.', DEF, '$(\\varnothing, \\{\\!|\\ast, \\ast|\\!\\})$.', 'lang/Safety.v: terminated');
n('prop.df', '$\\mathsf{deadlock\\_free}$', '$\\mathsf{deadlock\\_free}\\,p$ iff for every $p\'$ with $p \\to^{*} p\'$, $\\mathsf{terminated}\\,p\'$ or $p\' \\to p\'\'$ for some $p\'\'$.', 'It is the safety property the deadlock-freedom system proves of closed typed processes.', DEF, '$(\\{c\\}, \\{\\!|\\mathsf{close}\\,c^{+}, \\mathsf{close}\\,c^{-}|\\!\\})$ is deadlock free.', 'lang/Safety.v: deadlock_free');
n('prop.notau', '$\\mathsf{no\\_tau\\_divergence}$', 'For every $q$ with $p \\to^{*} q$, $\\mathsf{Acc}\\ {\\to_{\\mathsf{admin}}}\\ q$, so no infinite chain of administrative steps starts at $q$.', 'Lock freedom requires that a thread eventually performs its next action. An infinite chain of $\\beta$, spawn or link steps never performs one.', '$\\mathsf{force}\\,!(f = \\mathsf{force}\\,f)$ takes $\\beta$ steps forever, and a forwarder that spawns a new forwarder at each round spawns forever.', '$\\mathsf{force}\\,!(f = \\mathsf{force}\\,f)$ violates the property.', 'lockfree/TauThread.v: no_tau_divergence');
n('prop.padmin', 'Administrative step', '$q \\to_{\\mathsf{admin}} q\'$ when $q \\to q\'$ with an administrative event.', 'It is the relation that absence of internal divergence asks to be well-founded.', DEF, 'A $\\beta$ step of any thread.', 'lockfree/TauThread.v: padmin');
n('prop.lf', '$\\mathsf{lock\\_free}$', 'For every run $(r, l)$ with $\\mathsf{erase}(r_0) = p$ that is maximal and weakly fair, every thread $t$ pending at a position $i$ has $t \\in \\mathsf{parts}(l_j)$ for some $j \\geq i$.', 'Deadlock freedom allows a thread to wait forever while other threads step. Lock freedom excludes it, and its definition mentions no type.', 'A server that serves one client forever while a second client waits is deadlock free and not lock free.', '$(\\{c\\}, \\{\\!|\\mathsf{close}\\,c^{+}, \\mathsf{close}\\,c^{-}|\\!\\})$ is lock free.', 'lockfree/Fair.v: lock_free');
n('prop.maximal', 'Maximal run', 'For every $i$, either $r_i \\to r_{i+1}$ by a $\\tau$ event $l_i$, or $r_i$ has no $\\tau$ step and $r_{i+1} = r_i$.', 'A run that stutters while a step is possible would satisfy lock freedom vacuously, so the definition quantifies over maximal runs only.', DEF, 'A run that stutters at $r_i$ while $r_i$ has a $\\tau$ step is not maximal.', 'lockfree/Fair.v: maximal');
n('prop.wfair', 'Weak fairness', 'For every position $i$ and thread $t$, there is $j \\geq i$ with $t \\in \\mathsf{parts}(l_j)$ or $t$ disabled at $r_j$.', 'Without fairness a scheduler may never run an enabled thread $t$, and no program with two threads is lock free.', DEF, 'A run that never schedules an enabled thread is not weakly fair.', 'lockfree/Fair.v: wfair');
n('prop.pend', 'Pending thread', '$\\mathsf{pend}(q, t)$ holds when thread $t$ of $q$ has a session label as its next step.', 'Lock freedom guarantees progress exactly to the pending threads.', DEF, 'A thread at $\\mathsf{recv}\\,b$ is pending.', 'lockfree/Fair.v: pend');
n('prop.lfrun', '$\\mathsf{lf\\_run}$', 'For every $i$ and $t$, $\\mathsf{pend}(r_i, t)$ implies $t \\in \\mathsf{parts}(l_j)$ for some $j \\geq i$.', 'It is the condition on one run, and $\\mathsf{lock\\_free}\\,p$ asks it of every maximal weakly fair run from $p$.', DEF, 'Every message the client sends is received by the server at a later position.', 'lockfree/Fair.v: lf_run');

// ---- signatures and arguments ----
const { sa } = require('./core');
const A = (name, meaning) => ({ name, meaning });
const Oa = A('o', R`The end the offer acts on, $o \in \mathsf{End}$.`);
const Ii = A('i', R`A choice, $i \in \{\mathsf{false}, \mathsf{true}\}$.`);
const CM = A(R`(C, M)`, R`The configuration before the step, $C$ its restricted channels and $M$ its thread map.`);
const Ith = A('i', R`The identifier of the acting thread, $i \in \mathrm{dom}\,M$.`);
const Ep = A(R`e'`, R`The term of thread $i$ after its step.`);
const Jth = A('j', R`The identifier of the partner thread, $j \in \mathrm{dom}\,M$ with $j \neq i$.`);
const Fp = A(R`f'`, R`The term of thread $j$ after its step.`);
const RL = A(R`(r, l)`, R`A run, $r_i \in \mathsf{Config}$ the configuration and $l_i$ the event or stutter at position $i \in \mathbb{N}$.`);
sa('se.slabel', R`\sigma \in \mathsf{SLabel} \subseteq \mathsf{TLabel}`, [Oa, A('v', R`The value sent or received, where present.`), Ii]);
sa('se.subst', R`\cdot[\cdot] : \mathsf{Expr} \to \mathsf{Val} \to \mathsf{Expr}`, [A('e', R`The body, with a free index $0$.`), A('v', R`The value substituted for index $0$.`)]);
sa('se.frame', R`\cdot[\cdot] : \mathsf{Frame} \to \mathsf{Expr} \to \mathsf{Expr}`, [A('f', R`An evaluation frame, a term with one hole $\square$ in evaluation position.`), A('e', R`The term placed in the hole.`)]);
sa('se.upd', R`\cdot[\cdot \mapsto \cdot] : (\mathbb{N} \rightharpoonup \mathsf{Expr}) \to \mathbb{N} \to \mathsf{Expr} \to (\mathbb{N} \rightharpoonup \mathsf{Expr})`, [A('M', R`The thread map.`), A('i', R`The updated identifier.`), A('e', R`The new term of thread $i$.`)]);
sa('se.echans', R`\mathsf{echans} : (\mathbb{N} \rightharpoonup \mathsf{Expr}) \to \mathcal{P}_{\mathrm{fin}}(\mathsf{Chan})`, [A('M', R`A thread map, $\mathsf{echans}(M) = \bigcup_{i \in \mathrm{dom}\,M} \mathsf{fchans}(M(i))$.`)]);
sa('se.subj', R`\mathsf{subj} : \mathsf{SLabel} \to \mathcal{P}_{\mathrm{fin}}(\mathsf{Chan})`, [A(R`\sigma`, R`A session label.`)]);
sa('se.parts', R`\mathsf{parts} : \mathsf{Event} \to \mathcal{P}_{\mathrm{fin}}(\mathbb{N})`, [A('ev', R`An event. $\mathsf{parts}(ev)$ is the set of identifiers of the threads that take part in the step of $ev$.`)]);
sa('se.reach', R`\cdot \to^{*} \cdot \subseteq \mathsf{Proc} \times \mathsf{Proc}`, [A(R`p, p'`, R`Processes, $p \to^{*} p'$ iff a finite sequence of $\tau$ steps leads from $p$ to $p'$.`)]);
sa('se.acc', R`\mathsf{Acc} : (X \to X \to \mathsf{Prop}) \to X \to \mathsf{Prop}`, [A('R', R`A relation on $X$, instantiated with $\to_{\mathsf{admin}}$ on processes.`), A('q', R`The start element, instantiated with a process reachable from $p$.`)]);
sa('se.r0', R`\mathsf{erase}(r_0) = p`, [A(R`r_0`, R`The first configuration of the run, $r$ applied to $0$.`), A('p', R`The process whose lock freedom is stated.`)]);
sa('se.run', R`(r, l) \in \mathsf{Run} = (\mathbb{N} \to \mathsf{Config}) \times (\mathbb{N} \to \mathsf{Event}_{\bot})`, [A(R`r_i`, R`The configuration at position $i$.`), A(R`l_i`, R`The event of the step $r_i \to r_{i+1}$, or $\bot$ when $r_{i+1} = r_i$.`)]);
sa('lbl.beta', R`\beta \in \mathsf{TLabel}`, []);
sa('lbl.new', R`\mathsf{new}\,c \in \mathsf{TLabel}`, [A('c', R`The name of the new channel.`)]);
sa('lbl.spawn', R`\mathsf{spawn}\,v \in \mathsf{TLabel}`, [A('v', R`The thunk, the child thread is $v\,\ast$.`)]);
sa('lbl.send', R`o!v \in \mathsf{SLabel}`, [Oa, A('v', R`The payload.`)]);
sa('lbl.recv', R`o?v \in \mathsf{SLabel}`, [Oa, A('v', R`The received value, any value.`)]);
sa('lbl.close', R`o\,\mathsf{end} \in \mathsf{SLabel}`, [Oa]);
sa('lbl.sel', R`o \lhd i \in \mathsf{SLabel}`, [Oa, A('i', R`The selected branch.`)]);
sa('lbl.bra', R`o \rhd i \in \mathsf{SLabel}`, [Oa, A('i', R`The received choice.`)]);
sa('lbl.link', R`\leftrightarrow\{o_1, o_2\} \in \mathsf{SLabel}`, [A(R`o_1, o_2`, R`The linked ends, an unordered pair.`)]);
const STEP = R`\cdot \xrightarrow{\cdot} \cdot \subseteq \mathsf{Expr} \times \mathsf{TLabel} \times \mathsf{Expr}`;
sa('T-Act-App', STEP, [A('e', R`The body of the $\lambda$.`), A('v', R`The argument, a value.`)]);
sa('T-Act-Force', STEP, [A('e', R`The body of the box, substituted with the box itself.`)]);
sa('T-Act-New', STEP, [A('c', R`Any channel name, restricted by the process rule.`)]);
sa('T-Act-Spawn', STEP, [A('v', R`The thunk.`)]);
sa('T-Act-Send', STEP, [A('v', R`The payload.`), A('o', R`The end sent on, returned.`)]);
sa('T-Act-Recv', STEP, [A('o', R`The end received on.`), A('v', R`Any value, one step for each.`)]);
sa('T-Act-Close', STEP, [A('o', R`The closed end.`)]);
sa('T-Act-Select', STEP, [A('i', R`The selected branch.`), A('o', R`The end, returned under the same name.`)]);
sa('T-Act-Branch', STEP, [A('o', R`The end.`), A('i', R`The received choice, one step for each $i$.`)]);
sa('T-Act-Link', STEP, [A(R`o_1, o_2`, R`The linked ends.`)]);
sa('T-Act-Ctx', R`\dfrac{e \xrightarrow{\alpha} e' \quad \mathsf{frame\_val}\,f}{f[e] \xrightarrow{\alpha} f[e']}`, [A(R`e, e'`, R`The term in the hole before and after the step.`), A(R`\alpha`, R`The label, passed through unchanged.`), A('f', R`An evaluation frame whose subterms left of the hole are values.`)]);
sa('sem.frameval', R`\mathsf{frame\_val} : \mathsf{Frame} \to \mathsf{Prop}`, [A('f', R`A frame, $\mathsf{frame\_val}\,f$ iff every subterm of $f$ left of the hole is a value.`)]);
const PSTEP = R`(C, M) \xrightarrow{ev} (C', M') \subseteq \mathsf{Config} \times \mathsf{Event} \times \mathsf{Config}`;
sa('P-Act-Beta', PSTEP, [CM, Ith, Ep]);
sa('P-Act-New', PSTEP, [CM, Ith, Ep, A('c', R`The new channel, with $c \notin C \cup \mathsf{echans}(M)$.`)]);
sa('sem.fresh-global', R`c \notin C \cup \mathsf{echans}(M)`, [A('c', R`The name of the channel being created.`), A('C', R`The restricted channels of the configuration.`), A('M', R`The thread map of the configuration.`)]);
sa('P-Act-Spawn', PSTEP, [CM, Ith, Ep, A('v', R`The thunk.`), A('j', R`The identifier of the new thread, $j \notin \mathrm{dom}\,M$.`)]);
sa('P-Act-Msg', PSTEP, [CM, Ith, Jth, A('o', R`The end of the sender, the receiver acts on $\overline{o}$.`), A('v', R`The payload, the same value in both labels.`), Ep, Fp]);
sa('P-Act-Close', PSTEP, [CM, Ith, Jth, A('o', R`The end closed by $i$, with $\mathsf{ech}\,o \in C$.`), Ep, Fp]);
sa('P-Act-Choice', PSTEP, [CM, Ith, Jth, A('o', R`The selecting end, the partner branches on $\overline{o}$.`), A('b', R`The choice, the same in both labels.`), Ep, Fp]);
sa('P-Act-Link', PSTEP, [CM, Ith, A(R`o_1, o_2`, R`The linked ends, with $\mathsf{ech}\,o_1 \in C$.`), Ep]);
sa('P-Act-Session', PSTEP, [CM, Ith, A(R`\sigma`, R`A session label with $\mathsf{subj}\,\sigma \cap C = \varnothing$, an offer to the environment.`), Ep]);
sa('sem.sentc', R`\mathsf{sentc} : \mathsf{SLabel} \to \mathcal{P}_{\mathrm{fin}}(\mathsf{Chan})`, [A(R`\sigma`, R`A session label, $\mathsf{sentc}(o!v) = \mathsf{fchans}(v)$ and $\varnothing$ otherwise.`)]);
sa('ev.event', R`ev \in \mathsf{Event}`, [A(R`i, j`, R`Thread identifiers of the participants.`), A(R`\alpha`, R`The thread label of a solo step.`), A('k', R`The pick of a solo step.`), A(R`\sigma`, R`The session label of thread $i$, in a synchronization or an offer to the environment.`)]);
sa('ev.pick', R`k \in \mathbb{N}_{\bot} \cup \mathsf{End} \times \mathsf{End}`, [A('j', R`The identifier of a spawned thread.`), A(R`o_1, o_2`, R`The ends of a link, the channel of $o_1$ goes.`)]);
sa('ev.admin', R`\mathsf{admin} \subseteq \mathsf{Event}`, []);
sa('ev.tau', R`\tau \subseteq \mathsf{Event}`, []);
sa('prop.terminated', R`\mathsf{terminated} : \mathsf{Proc} \to \mathsf{Prop}`, [A('p', R`A process.`), A('v', R`The result of the main thread, a value.`), A('E', R`The multiset of the other threads, each equal to $\ast$.`)]);
sa('prop.df', R`\mathsf{deadlock\_free} : \mathsf{Proc} \to \mathsf{Prop}`, [A('p', R`The process.`), A(R`p'`, R`Ranges over all processes with $p \to^{*} p'$.`), A(R`p''`, R`A successor of $p'$, existentially quantified.`)]);
sa('prop.notau', R`\mathsf{no\_tau\_divergence} : \mathsf{Proc} \to \mathsf{Prop}`, [A('p', R`The process.`), A('q', R`Ranges over all processes with $p \to^{*} q$.`)]);
sa('prop.padmin', R`\cdot \to_{\mathsf{admin}} \cdot \subseteq \mathsf{Proc} \times \mathsf{Proc}`, [A(R`q, q'`, R`Processes with $q \to q'$ by an event in $\mathsf{admin}$.`)]);
sa('prop.lf', R`\mathsf{lock\_free} : \mathsf{Proc} \to \mathsf{Prop}`, [A('p', R`The process.`), RL, A('i', R`A position of the run.`), A('t', R`A thread identifier.`), A('j', R`A position with $j \ge i$, existentially quantified.`)]);
sa('prop.maximal', R`\mathsf{maximal} : \mathsf{Run} \to \mathsf{Prop}`, [RL, A('i', R`Ranges over all positions.`)]);
sa('prop.wfair', R`\mathsf{wfair} : \mathsf{Run} \to \mathsf{Prop}`, [RL, A('i', R`Ranges over all positions.`), A('t', R`Ranges over all thread identifiers.`), A('j', R`A position with $j \ge i$, existentially quantified.`)]);
sa('prop.pend', R`\mathsf{pend} : \mathsf{Config} \to \mathbb{N} \to \mathsf{Prop}`, [A('q', R`A configuration, instantiated with $r_i$.`), A('t', R`A thread identifier of $q$.`)]);
sa('prop.lfrun', R`\mathsf{lf\_run} : \mathsf{Run} \to \mathsf{Prop}`, [RL, A(R`i, t`, R`Range over all positions and thread identifiers.`), A('j', R`A position with $j \ge i$, existentially quantified.`)]);
