const { R, h, n, section, block, rule, Q, DEF } = require('./core');

const s = section('semantics', 'Semantics',
  'Thread steps carry labels that say what the relation reads. Process steps carry events that name the threads involved. A send and a spawn carry the transfer set of their value.');

const step = (a) => R`\xrightarrow{${a}}`;
block(s, {
  id: 'sem-labels', title: 'Thread labels', rocq: 'lang/Semantics.v: tlabel, slabel',
  tex: R`\alpha ::= ${h('lbl.beta', R`\beta`)} \mid ${h('lbl.new', R`\mathsf{new}_\ell\,c`)} \mid ${h('lbl.newat', R`\mathsf{new}_\kappa\,o\,c`)} \mid ${h('lbl.spawn', R`\mathsf{spawn}_{${h('lbl.transfer', 'M')}}\,v`)} \mid \sigma \qquad \sigma ::= ${h('lbl.send', R`o!_{M}v`)} \mid ${h('lbl.recv', R`o?v`)} \mid ${h('lbl.close', R`o\,\mathsf{end}`)} \mid ${h('lbl.sel', R`o \lhd i`)} \mid ${h('lbl.bra', R`o \rhd i`)} \mid ${h('lbl.link', R`\leftrightarrow\{o_1,o_2\}`)}`,
  caption: 'β covers application, let, case and force. Session labels σ are offers on ends.'
});
block(s, {
  id: 'sem-head', title: 'Head steps (T-Act rules)', rocq: 'lang/Semantics.v: head_step',
  tex: R`\begin{array}{ll}
${h('T-Act-App', R`(\lambda e)\,v ${step(R`\beta`)} e[v]`)} & ${h('T-Act-Let', R`\mathsf{let}\ a = v\ \mathsf{in}\ e ${step(R`\beta`)} e[v]`)} \\
${h('T-Act-Force', R`\mathsf{force}\,(!e) ${step(R`\beta`)} e[!e]`)} & ${h('T-Act-New', R`\mathsf{new}_\ell ${step(R`\mathsf{new}_\ell\,c`)} \langle c^{+}, c^{-}\rangle`)} \\
${h('T-Act-NewAt', R`\mathsf{new}_\kappa\,o ${step(R`\mathsf{new}_\kappa\,o\,c`)} \langle o, \langle c^{+}, c^{-}\rangle\rangle`)} & ${h('T-Act-Spawn', R`\mathsf{spawn}\,v ${step(R`\mathsf{spawn}_{\mathsf{fends}(v)}\,v`)} \ast`)} \\
${h('T-Act-Send', R`\mathsf{send}\,\langle v, o\rangle ${step(R`o!_{\mathsf{fends}(v)}v`)} o`)} & ${h('T-Act-Recv', R`\mathsf{recv}\,o ${step(R`o?v`)} \langle v, o\rangle`)} \\
${h('T-Act-Close', R`\mathsf{close}\,o ${step(R`o\,\mathsf{end}`)} \ast`)} & ${h('T-Act-Select', R`\mathsf{select}_i\,o ${step(R`o\lhd i`)} o`)} \\
${h('T-Act-Branch', R`\mathsf{branch}\,o ${step(R`o\rhd i`)} \mathsf{inj}_i\,o`)} & ${h('T-Act-Link', R`\mathsf{link}\,\langle o_1, o_2\rangle ${step(R`\leftrightarrow\{o_1,o_2\}`)} \ast`)}
\end{array}`,
  caption: 'One head rule per redex. Select and branch keep their end, and a receive takes any value.'
});
block(s, {
  id: 'sem-ctx', title: 'Evaluation frames (T-Act-Ctx)', rocq: 'lang/Semantics.v: tstep, frame_val',
  tex: rule('T-Act-Ctx', R`${h('T-Act-Ctx', R`e ${step(R`\alpha`)} e'`)}${Q}${h('sem.frameval', R`\mathsf{frame\_val}\,f`)}`, R`f[e] ${step(R`\alpha`)} f[e']`),
  caption: 'One frame at a time, never under λ or a box. A right frame waits for a value on its left.'
});
block(s, {
  id: 'sem-proc', title: 'Process steps (P-Act rules)', rocq: 'lang/Process.v: istep',
  tex: R`\begin{array}{l}
${h('P-Act-Beta', R`M(i) ${step(R`\beta`)} e' \;\Rightarrow\; (C, M) ${step(R`\beta_i`)} (C, M[i \mapsto e'])`)} \\
${h('P-Act-New', R`M(i) ${step(R`\mathsf{new}\,c`)} e',\ ${h('sem.fresh-global', R`c \notin C \cup \mathsf{echans}(M)`)} \;\Rightarrow\; (C \cup \{c\}, M[i\mapsto e'])`)} \\
${h('P-Act-Spawn', R`M(i) ${step(R`\mathsf{spawn}_M v`)} e',\ j \notin \mathsf{dom}\,M \;\Rightarrow\; (C, M[i\mapsto e'][j \mapsto v\,\ast])`)} \\
${h('P-Act-Msg', R`M(i) ${step(R`o!_M v`)} e',\ M(j) ${step(R`\overline{o}?v`)} f',\ i \neq j \;\Rightarrow\; (C, M[i\mapsto e'][j\mapsto f'])`)} \\
${h('P-Act-Close', R`M(i) ${step(R`o\,\mathsf{end}`)} e',\ M(j) ${step(R`\overline{o}\,\mathsf{end}`)} f',\ \mathsf{ech}\,o \in C \;\Rightarrow\; (C \setminus \{\mathsf{ech}\,o\}, \ldots)`)} \\
${h('P-Act-Choice', R`M(i) ${step(R`o\lhd b`)} e',\ M(j) ${step(R`\overline{o}\rhd b`)} f' \;\Rightarrow\; (C, M[i\mapsto e'][j\mapsto f'])`)} \\
${h('P-Act-Link', R`M(i) ${step(R`\leftrightarrow\{o_1,o_2\}`)} e',\ \mathsf{ech}\,o_1 \in C \;\Rightarrow\; (C\setminus\{\mathsf{ech}\,o_1\}, ${h('link.csub', R`\mathsf{csub}\,o_1\,o_2`)} \langle\$\rangle\, M[i\mapsto e'])`)} \\
${h('P-Act-Session', R`M(i) ${step(R`\sigma`)} e',\ \mathsf{subj}\,\sigma \cap C = \varnothing \;\Rightarrow\; (C \setminus ${h('sem.sentc', R`\mathsf{sentc}\,\sigma`)}, M[i\mapsto e'])`)}
\end{array}`,
  caption: 'The only definition of process steps. A message may use a free channel, a close and a link need a restricted one, and an external offer extrudes its transfer set.'
});
block(s, {
  id: 'sem-events', title: 'Events', rocq: 'lang/Process.v: event, ev_parts, ev_admin, ev_tau',
  tex: R`${h('ev.event', R`ev ::= \beta_i \mid \mathsf{new}_i\,\ell\,c \mid \mathsf{newat}_i\,\kappa\,o\,c \mid \mathsf{spawn}_{i,j}\,M \mid \mathsf{msg}_{i,j}\,o\,M \mid \mathsf{close}_{i,j}\,o \mid \mathsf{choice}_{i,j}\,o\,b \mid \mathsf{link}_i\,o_1\,o_2 \mid \mathsf{sess}_i\,\sigma`)} \qquad ${h('ev.admin', R`\mathsf{admin} = \{\beta, \mathsf{new}, \mathsf{newat}, \mathsf{spawn}, \mathsf{link}\}`)} \qquad ${h('ev.tau', R`\tau = \text{all but } \mathsf{sess}`)}`,
  caption: 'An event names the participating threads and carries the creation label, the transfer set or the ends acted on.'
});
block(s, {
  id: 'sem-props', title: 'Safety properties', rocq: 'lang/Safety.v: deadlock_free, lockfree/TauThread.v: no_tau_divergence, lockfree/Fair.v: lock_free',
  tex: R`\begin{array}{l}
${h('prop.terminated', R`\mathsf{terminated}\,p \iff p = (\varnothing, \{v\} \uplus E),\ E \subseteq \{\ast\}`)} \\
${h('prop.df', R`\mathsf{deadlock\_free}\,p \iff \forall p'.\ p \to^{*} p' \Rightarrow \mathsf{terminated}\,p' \lor \exists p''.\ p' \to p''`)} \\
${h('prop.notau', R`\mathsf{no\_tau\_divergence}\,p \iff \forall q.\ p \to^{*} q \Rightarrow \mathsf{Acc}\ ${h('prop.padmin', R`\to_{\mathsf{admin}}`)}\ q`)} \\
${h('prop.lf', R`\mathsf{lock\_free}\,p \iff \forall r\,l.\ \mathsf{erase}(r_0) = p \Rightarrow ${h('prop.maximal', R`\mathsf{maximal}\,r\,l`)} \Rightarrow ${h('prop.wfair', R`\mathsf{wfair}\,r\,l`)} \Rightarrow ${h('prop.lfrun', R`\forall i\,t.\ ${h('prop.pend', R`\mathsf{pend}(r_i, t)`)} \Rightarrow \exists j \geq i.\ t \in \mathsf{parts}(l_j)`)}`)}
\end{array}`,
  caption: 'Deadlock freedom, absence of internal divergence, and lock freedom over weakly fair maximal runs.'
});

// ---- notes ----
n('lbl.beta', 'β label', 'The label of application, let, unit and pair elimination, case and force.', 'All of these steps cost the same in every cost table, so one label covers them.', DEF, 'force (!e) steps with β.', 'lang/Semantics.v: LBeta');
n('lbl.new', 'new_ℓ c label', 'Carries the family ℓ and the name c of the new channel.', 'The relation reads ℓ to place the new channel at a fresh root of that family.', DEF, 'new₀ creating c.', 'lang/Semantics.v: LNew');
n('lbl.newat', 'new_κ o c label', 'Carries the field, the anchor end and the new name.', 'The relation reads the anchor to find the point x where the new channel goes.', DEF, 'new₀ c⁺ creating d at x·0.', 'lang/Semantics.v: LNewAt');
n('lbl.spawn', 'spawn label', 'Carries the transfer set M = fends(v) and the thunk v.', 'The relation splits the ends of the parent along M.', DEF, 'spawn (λ_. close d′) carries M = {d′}.', 'lang/Semantics.v: LSpawn');
n('lbl.send', 'send label o!_M v', 'An offer to send v on o, moving the ends M.', 'The relation, the fuel layer and scope extrusion all read M off the label instead of inspecting v.', DEF, 'An offer to send the end a on o moves M = {a}.', 'lang/Semantics.v: SSend');
n('lbl.recv', 'receive label o?v', 'An offer to receive v on o. Any value can appear.', 'A receive must be able to meet whatever a partner sends.', DEF, 'o?∗.', 'lang/Semantics.v: SRecv');
n('lbl.close', 'close label', 'An offer to close o.', 'A plain label. The relation removes o from the environment of the thread.', DEF, 'close c⁺ offers c⁺ end.', 'lang/Semantics.v: SClose');
n('lbl.sel', 'select label', 'An offer to select branch i on o.', 'A plain label. The relation moves o to the continuation point of branch i.', DEF, 'select_true o offers o ◁ true.', 'lang/Semantics.v: SSel');
n('lbl.bra', 'branch label', 'An offer to receive choice i on o. Either choice can appear.', 'A plain label. Branch must be able to meet whichever choice the partner sends.', DEF, 'branch o offers o ▷ false and o ▷ true.', 'lang/Semantics.v: SBra');
n('lbl.link', 'link label', 'An unordered pair of ends. It may be degenerate, and the relation rejects a link of an end with itself.', 'The label is a set, so one process rule can remove the channel of either end.', DEF, '↔{c⁺, d⁻}.', 'lang/Semantics.v: SLink');
n('T-Act-App', 'T-Act-App', 'β-reduces a λ applied to a value.', 'Plain call by value.', DEF, '(λx. close x) c⁺ steps to close c⁺.', 'lang/Semantics.v: t_act_app');
n('T-Act-Let', 'T-Act-Let', 'Substitutes the value of a let. No closure is built.', 'A let keeps every end of its context, so it must not go through a λ.', DEF, 'let a = c⁺ in close a steps to close c⁺.', 'lang/Semantics.v: t_act_let');
n('T-Act-Force', 'T-Act-Force', 'Unrolls a box once. The body resumes with the box for its self.', 'This is the only source of recursion and replication.', DEF, 'force !(f = force f) steps to itself and never acts.', 'lang/Semantics.v: t_act_force');
n('T-Act-New', 'T-Act-New', 'Creates a channel c and returns both ends. The process rule chooses c.', 'A thread cannot see which names are taken. The process rule picks a name no thread uses.', DEF, 'new₀ steps to ⟨c⁺, c⁻⟩.', 'lang/Semantics.v: t_act_new');
n('T-Act-NewAt', 'T-Act-NewAt', 'Returns the anchor untouched beside the new pair.', 'The anchor is passed in and handed back, so the thread keeps it.', DEF, 'new₁ x steps to ⟨x, ⟨b, b′⟩⟩.', 'lang/Semantics.v: t_act_new_at');
n('T-Act-Spawn', 'T-Act-Spawn', 'Emits the thunk with its transfer set and returns ∗.', 'The label carries what the child takes.', DEF, 'spawn (λ_. close d′) steps to ∗.', 'lang/Semantics.v: t_act_spawn');
n('T-Act-Send', 'T-Act-Send', 'Emits the payload with its transfer set and returns the end.', 'The label carries what leaves the thread.', DEF, 'send ⟨∗, c⟩ steps to c.', 'lang/Semantics.v: t_act_send');
n('T-Act-Recv', 'T-Act-Recv', 'Receives any value and returns it paired with the end.', 'The thread cannot know what the partner sends, so its step admits every value. The type of the end restricts what the relation has to consider.', DEF, 'recv b steps to ⟨∗, b⟩.', 'lang/Semantics.v: t_act_recv');
n('T-Act-Close', 'T-Act-Close', 'Closes an end.', 'A plain rule. The matching process rule needs the partner to close too.', DEF, 'close c⁺ steps to ∗.', 'lang/Semantics.v: t_act_close');
n('T-Act-Select', 'T-Act-Select', 'Selects branch i and returns the same end name.', 'Ends keep their names, so running a program never reads a point.', DEF, 'select_true o steps to o.', 'lang/Semantics.v: t_act_select');
n('T-Act-Branch', 'T-Act-Branch', 'Receives a choice and returns the end in the matching injection.', 'Either choice may arrive, so the thread has one step for each.', DEF, 'branch o steps to inj₂ o.', 'lang/Semantics.v: t_act_branch');
n('T-Act-Link', 'T-Act-Link', 'Forwards o₁ to o₂. The label is a set, so the order of the two ends does not matter.', 'The renaming happens at the process level, where the other threads are visible.', DEF, 'link ⟨c⁺, d⁻⟩ steps to ∗.', 'lang/Semantics.v: t_act_link');
n('T-Act-Ctx', 'T-Act-Ctx', 'Lifts a step through one evaluation frame.', 'No frame goes under λ or a box, because both suspend evaluation.', DEF, 'let ∗ = close c in e steps when close c does.', 'lang/Semantics.v: t_act_ctx');
n('sem.frameval', 'frame_val', 'A frame whose hole is on the right asks a value on its left.', 'It fixes left-to-right evaluation.', DEF, 'In v₁ applied to a hole, v₁ must be a value.', 'lang/Semantics.v: frame_val');
n('P-Act-Beta', 'P-Act-Beta', 'One thread takes a β step.', 'A plain rule. Internal computation of one thread involves nobody else.', DEF, 'A β step of the main thread.', 'lang/Process.v: p_act_beta');
n('P-Act-New', 'P-Act-New and P-Act-NewAt', 'One thread creates a channel with a name no thread uses. The channel becomes restricted.', 'Both ends start in the creating thread, so the channel is internal to the process.', DEF, 'new₀ creates c with c ∉ C.', 'lang/Process.v: p_act_new, p_act_new_at');
n('sem.fresh-global', 'Global freshness', 'The new name is neither restricted nor mentioned by any thread.', 'Channel names are global. A name one thread still uses must not be reused by another.', 'Reusing a name a thread still mentions would merge two channels into one.', 'c ∉ C ∪ echans(M).', 'lang/Process.v: p_act_new');
n('P-Act-Spawn', 'P-Act-Spawn', 'The parent continues and a new thread j runs v ∗.', 'Only the parent takes part in the step.', DEF, 'spawn (λu. e) adds a thread j running (λu. e) ∗.', 'lang/Process.v: p_act_spawn');
n('P-Act-Msg', 'P-Act-Msg', 'A send on o meets a receive on ō in another thread. The channel may be free.', 'The rule asks nothing of C. In a typed process both ends of a channel sit inside the process only when the channel is restricted, so the extra generality admits no new behaviour.', DEF, 'The client sends on a and the server receives on a′.', 'lang/Process.v: p_act_msg');
n('P-Act-Close', 'P-Act-Close', 'Both ends close and the channel leaves C.', 'After a close nobody holds an end of the channel, so it disappears.', DEF, 'close c⁺ and close c⁻ in two threads remove c.', 'lang/Process.v: p_act_close');
n('P-Act-Choice', 'P-Act-Choice', 'A select on o meets a branch on ō with the same choice.', 'The branching thread learns the choice the selecting thread made.', DEF, 'select_true o meets branch ō, which steps to inj₂ ō.', 'lang/Process.v: p_act_choice');
n('P-Act-Link', 'P-Act-Link', 'The channel of o₁ goes. Every thread is renamed, so the holder of ō₁ now holds o₂.', 'The unordered label lets one rule remove the channel of either end.', DEF, 'link ⟨c⁺, d⁻⟩ with c restricted.', 'lang/Process.v: p_act_link');
n('P-Act-Session', 'P-Act-Session', 'An offer on a free channel to the environment. A send also frees the channels of the ends it moves out.', 'Scope extrusion follows the transfer set of the label, so the process and the relation agree on which channels leave.', DEF, 'An external send of a restricted end d⁺ frees d.', 'lang/Process.v: p_act_session');
n('sem.sentc', 'sentc', 'The channels of the transfer set of a send label, empty for other labels.', 'They are the channels a message to the environment moves out of the process.', DEF, 'sentc of a send moving d⁺ is {d}.', 'lang/Semantics.v: sentc');
n('ev.event', 'Event', 'The label of a process step, with the thread identifiers taking part.', 'Fairness asks of each thread that it takes part in steps, so steps must name their threads.', DEF, 'msg between threads 0 and 1 on a⁺.', 'lang/Process.v: event');
n('ev.admin', 'Administrative events', 'β, creation, spawn and link. They cost nothing in the liveness cost table.', 'These are the steps that make no progress on any protocol. Absence of internal divergence speaks about them.', DEF, 'A chain of spawns takes only administrative steps.', 'lang/Process.v: ev_admin');
n('ev.tau', 'τ events', 'Every event except an offer to the environment.', 'A closed program takes only τ steps.', DEF, 'A closed configuration takes only τ events.', 'lang/Process.v: ev_tau, itstep');
n('prop.terminated', 'terminated', 'No restricted channel, the main thread is a value and every other thread is ∗.', 'A finished program has used up every channel, and only the main thread returns a result.', DEF, '(∅, {∗, ∗}).', 'lang/Safety.v: terminated');
n('prop.df', 'deadlock_free', 'Every reachable process is terminated or can take a step.', 'The target of deadlock freedom.', DEF, 'close c⁺ and close c⁻ in two threads are deadlock free.', 'lang/Safety.v: deadlock_free');
n('prop.notau', 'no_tau_divergence', 'From every reachable state there is no infinite sequence of administrative steps.', 'Lock freedom needs the program to reach its next action. An endless chain of β steps, spawns or links never does.', 'A box that only calls itself, and a forwarder that spawns forever, run forever without acting.', 'force !(f = force f) is ruled out.', 'lockfree/TauThread.v: no_tau_divergence');
n('prop.padmin', 'Administrative step', 'A process step whose event is administrative.', 'It names the steps that absence of internal divergence counts.', DEF, 'A β step of any thread.', 'lockfree/TauThread.v: padmin');
n('prop.lf', 'lock_free', 'In every maximal weakly fair run, every thread that waits to act eventually takes part in a step.', 'Deadlock freedom allows a thread to wait forever while others keep running. Lock freedom rules that out. The definition mentions no type.', 'A server that keeps serving one client while another client waits forever is deadlock free and not lock free.', 'Two threads that close c⁺ and c⁻ are lock free.', 'lockfree/Fair.v: lock_free');
n('prop.maximal', 'maximal run', 'Each position steps by a τ event, or the state is stuck and stays.', 'Lock freedom quantifies over runs that never stop early. A run that stops while a step is possible proves nothing.', DEF, 'A run that stops while a thread can still step is not maximal.', 'lockfree/Fair.v: maximal');
n('prop.wfair', 'weak fairness', 'Each thread eventually takes part in a step or is disabled.', 'Without fairness a scheduler could ignore one thread forever, and no program would be lock free.', DEF, 'A scheduler that never runs an enabled thread is not fair.', 'lockfree/Fair.v: wfair');
n('prop.pend', 'pending thread', 'A thread whose next step is a session action.', 'These are the threads lock freedom promises progress for.', DEF, 'A thread at recv b.', 'lockfree/Fair.v: pend');
n('prop.lfrun', 'lf_run', 'Every thread pending at position i takes part in some step at a position j ≥ i.', 'It says what a single run must satisfy. Lock freedom asks it of every fair maximal run.', DEF, 'Every message the client sends is received by the server at some later step.', 'lockfree/Fair.v: lf_run');
