const core = require('./core');
const { R, h, n, sa, section, examples, DEF } = core;
const { awb } = require('./typing');
const block = (sec, b) => core.block(sec, awb(b));

const s = section('theorems', 'Theorems',
  "The main results, closed under the global context, and the relations $V$, $E$, $P$ and the lock-free process relation $S$ they mention.");

const TH = (id, title, rocq, modes, tex, caption) => block(s, { id, title, rocq, modes, tex, caption });
const imp = R`\;\Longrightarrow\;`;
const L = R`\mathrel{|\!\!\vDash}`;

// shorthands, each linked to its definition
const IM = (p, c) => R`\begin{array}{l}${p} \\ \quad\Longrightarrow\ ${c}\end{array}`;
const AL = (...rs) => R`\begin{array}{l}${rs.join(R` \\ `)}\end{array}`;
// rows that only the lock-free mode shows (and colours): the lock-free results and those stated over the annotated judgment
const LFROWS = /^\\htmlData\{k=th\.(lf-[\w-]+|live-[\w-]+|fundamental-typed|conservative|typed-dftyped|adequacy-gen)\}/;
const ROWS = (...rs) => R`\begin{array}{l}${rs.map((r, i) => { const sep = i ? R` \\[1.5ex] ` : ''; return LFROWS.test(r) ? (sep ? R`\annraw{${sep}}` : '') + R`\annot{${r}}` : sep + r; }).join('')}\end{array}`;
const STRICT = h('w.strict', R`\mathsf{strict}`);
const WFW = h('th.wfworld', R`\mathsf{wfworld}`);
const LFW = R`${STRICT}\,W \land ${WFW}\,W`;
const DFP = h('prop.df', R`\mathsf{deadlock\_free}`);
const NOTAU = h('prop.notau', R`\mathsf{no\_tau\_divergence}`);
const LOCKF = h('prop.lf', R`\mathsf{lock\_free}`);
const PSEM = h('sj.proc', R`\vDash`);
const PLIVE = h('sj.proc', L);
const TSEM = h('sj.term', R`\vDash`);
const TLIVE = h('sj.term', L);
const LFS = h('sp.lfsem', R`\Vvdash`);
const PT = h('tp.pjudg', R`\vdash^{\infty}_W`);
const PLF = h('tp.lfjudg', R`\Vdash^{N}_W`);
const DF = (x) => h('th.df', R`${x}_{df}`);
const PR = (k, W, n, body) => h('th.Prel', R`P\annot{[${k}]}^{${W}}_{${n}}\llbracket ${body}\rrbracket`);
const P0 = (W, n, body) => h('th.Prel', R`P^{${W}}_{${n}}\llbracket ${body}\rrbracket`);
const ER = (k, W, n, body, F) => h('th.Erel', R`E\annot{[${k}]}^{${W}}_{${n}}\llbracket ${body}\rrbracket^{${F}}`);
const E0 = (W, n, body, F) => h('th.Erel', R`E^{${W}}_{${n}}\llbracket ${body}\rrbracket^{${F}}`);
const SOUP = (n) => h('th.soup', R`S^{N,W}_{${n}}\llbracket\varnothing \vdash T\rrbracket`);
// the need of a whole thread is finite, so some ticket count covers it
const MEETS = h('ann.fin0', R`\vartheta(0) \in \mathbb{N}`);
// every credit of a context is at most the counter bound
const CRN = (D) => h('th.crle', R`\mathsf{cr}(${D}) \leq N`);
const CTY = (D, t) => R`\varnothing ; ${D} \vdash^{\varnothing}_{W,N} ${t} : T\ !\ (c, \vartheta)`;
const GRD = (t) => h('guard.judg', R`\varnothing \vdash\!\triangleright ${t}`);
const PRIM = R`${h('ty.prim', R`\mathsf{prim}`)}\,T`;

const BY = (name, k) => R`\overset{${h(k, R`\textsf{${name}}`)}}{\Longrightarrow}`;
TH('th-chain', 'How the results fit together', 'static/FundamentalProc.v: fundamental_proc, soundness; relation/Adequacy.v: adequacy; static/Fundamental.v: live_fundamental; cost/CostFund.v: fsem_of_cost; soup/LFTyped.v: lf_fundamental; soup/LFAdequacy.v: lf_adequacy', ['df', 'lf'],
  R`\begin{array}{rcl}
\Sigma ${PT} p : T & ${BY('fundamental\\_proc', 'th.fundamental-proc')} & \Sigma ${PSEM}_W p : T \\[1ex]
\varnothing ${PSEM}_W p : T & ${BY('adequacy', 'th.adequacy')} & ${DFP}\,p
\annraw{\\[3ex]}\annot{${CTY(R`\Delta`, 't')} \land ${GRD('t')}}\annraw{&}\annot{${BY('live\\_fundamental', 'th.live-fundamental')}}\annraw{&}\annot{\Delta ${TLIVE}^{\varnothing}_W t : T}
\annraw{\\[1ex]}\annot{${CTY(R`\Delta`, 't')} \land ${CRN(R`\Delta`)} \land ${MEETS}}\annraw{&}\annot{${BY('fsem\\_of\\_cost', 'th.fsem-of-cost')}}\annraw{&}\annot{${h('fu.fsem', R`\mathsf{fsem}\,N\,${h('th.styof', R`\Delta^{N}`)}\,t`)}}
\annraw{\\[1ex]}\annot{\Sigma ${PLF} p : T}\annraw{&}\annot{${BY('lf\\_fundamental', 'th.lf-fundamental')}}\annraw{&}\annot{\Sigma ${LFS}_W p : T}
\annraw{\\[1ex]}\annot{\varnothing ${LFS}_W p : T \land ${WFW}\,W}\annraw{&}\annot{${BY('lf\\_adequacy', 'th.lf-adequacy')}}\annraw{&}\annot{${LOCKF}\,p}
\end{array}`,
  'Typing gives the semantic judgment, and the semantic judgment gives deadlock freedom. Both steps use the one relation $(V, E, P)$ at the step costs $\\kappa_{DF}$. \\annp{Lock freedom uses the same relation at $\\kappa_L$, which rules out $\\tau$-divergence, and adds fuel, the counters and tickets of each thread, which read no point. The lock-free process relation holds both halves of every thread over one ownership map. A thread $t$ waits on $o$, and every step of the thread holding $\\overline{o}$ on another end decrements $\\varphi(\\overline{o})$, which F-Count keeps at $1$ or more, while every link uses a ticket. So $\\mu(t) = (\\sum_s tk_s, \\varphi(\\overline{o}))$ falls until the holding thread acts on $\\overline{o}$.}');
TH('th-adequacy', 'Adequacy', 'relation/Adequacy.v: adequacy, live_adequacy, adequacy_gen', ['df', 'live'],
  ROWS(
    h('th.adequacy', IM(R`${STRICT}\,W \land \varnothing ${PSEM}_W p : T`, R`${DFP}\,p`))),
  'What it tells you. A closed process in the semantic judgment is deadlock free, in every strict world. \\annp{In a strict and well-founded world, a closed process in the lock-free judgment is lock free, and every thread progresses on every weakly fair run.}');
TH('th-lf-adequacy', 'Lock-free adequacy', 'soup/LFAdequacy.v: lf_adequacy, lf_thread_progress; soup/SoupTau.v: soup_no_tau_divergence; soup/SoupRun.v: lfsoup_step', ['lf'],
  ROWS(
    h('th.lf-adequacy', IM(R`${LFW} \land \varnothing ${LFS}_W p : T`, R`${LOCKF}\,p`)),
    h('th.lf-thread-progress', IM(R`\mathsf{strict}\,W \land \mathsf{wfworld}\,W \land \varnothing \Vvdash_W p : T`, AL(R`\forall (r, l).\ ${h('proc.erase', R`\mathsf{erase}`)}\,(${h('se.run', R`r\,0`)}) = p \land ${h('prop.maximal', R`\mathsf{maximal}`)}\,(r, l) \land ${h('prop.wfair', R`\mathsf{wfair}`)}\,(r, l)`, R`\quad \Longrightarrow\ ${h('th.tpr', R`\mathsf{thread\_progress\_run}`)}\,(r, l)`)))),
  'What it tells you. In a strict and well-founded world, a closed process in the lock-free judgment is lock free, and every thread progresses on every weakly fair run.');
TH('th-fund-term', 'Fundamental theorems for terms', 'static/Fundamental.v: typed_sem, fundamental, fundamental_typed, live_fundamental, live_fundamental_typed', ['df', 'live', 'lf'],
  ROWS(
    h('th.fundamental', IM(R`${STRICT}\,W \land \varnothing ; \Delta \vdash^{F}_{W} t : T`, R`\Delta ${TSEM}^{F}_W t : T`)),
    h('th.fundamental-typed', IM(R`\mathsf{strict}\,W \land \varnothing ; \Delta \vdash^{F}_{W,N} t : T\ !\ \varepsilon`, R`${DF(R`\Delta`)} \vDash^{F}_W t : T_{df}`)),
    h('th.live-fundamental', IM(R`\mathsf{strict}\,W \land \varnothing ; \Delta \vdash^{F}_{W} t : T \land ${h('guard.judg', R`\varnothing \vdash\!\triangleright t`)}`, R`\Delta ${TLIVE}^{F}_W t : T`)),
    h('th.live-fundamental-typed', IM(AL(R`\mathsf{strict}\,W \land \varnothing ; \Delta \vdash^{F}_{W,N} t : T\ !\ \varepsilon`, R`\land\ \varnothing \vdash\!\triangleright t`), R`\Delta_{df} ${L}^{F}_W t : T_{df}`))),
  'For strict $W$, typing with empty $\\Gamma$ implies the semantic term judgment. \\annp{With the guard $\\varnothing \\vdash\\!\\triangleright t$ it implies the live judgment.}');
TH('th-fund-proc', 'Fundamental theorem', 'static/FundamentalProc.v: fundamental_proc, live_fundamental_proc; soup/LFTyped.v: lf_fundamental', ['df', 'live', 'lf'],
  ROWS(
    h('th.fundamental-proc', IM(R`${STRICT}\,W \land \Sigma ${PT} p : T`, R`\Sigma ${PSEM}_W p : T`)),
    h('th.lf-fundamental', IM(R`\mathsf{strict}\,W \land \Sigma ${PLF} p : T`, R`\Sigma ${LFS}_W p : T`))),
  'What it tells you. Every typed process is in the semantic judgment, so every typed process is safe in the sense of the relation. The proof is an induction over P-Term and P-Connect, using the composition rules above.');
TH('th-compose', 'Semantic composition rules', 'compat/PTerm.v: sem_p_term; compat/ConnectP.v: sem_p_connect; soup/LFCompose.v: lf_p_term, lf_p_connect', ['df', 'live', 'lf'],
  ROWS(
    h('th.sem-p-term', IM(AL(R`${PRIM} \land ${h('th.sth', R`\mathsf{sth}\,\Theta\,\Sigma\,\Theta_B\,C`)}`, R`\land\ t \in ${ER(R`\kappa`, 'W', 'n', R`\Theta \vdash T`, R`\varnothing`)}`), R`(C, \{t\}) \in ${PR(R`\kappa`, 'W', 'n', R`\Sigma \vdash T`)}`)),
    h('th.sem-p-connect', IM(AL(R`\mathsf{prim}\,T \land ${h('th.conn', R`\mathsf{conn}`)}`, R`\land\ p_1 \in ${P0(R`W_1`, 'n', R`\Sigma_1 \cup \Sigma_C \vdash T`)}`, R`\land\ p_2 \in ${P0(R`W_2`, 'n', R`\Sigma_2 \cup \Sigma_D \vdash \ast`)}`), R`${h('th.par', R`p_1 \parallel_{\Sigma_C} p_2`)} \in ${P0(R`W_1 \sqcup W_2`, 'n', R`\Sigma_1 \cup \Sigma_2 \vdash T`)}`)),
    h('th.lf-p-term', IM(R`\mathsf{strict}\,W \land \Sigma \Vdash^{N}_{W} (C_0, \{t\}) : T`, R`\Sigma \Vvdash_W (C_0, \{t\}) : T`))),
  'What it tells you. Composition is semantic. A single safe thread is a safe process, and two safe processes connected at dual interfaces are a safe process. So any component proved safe by hand, without typing, composes with typed ones. \\annp{The same holds in the lock-free process relation.}');
TH('th-bind', 'The bind lemma', 'compat/Bind.v: Erel_bind', ['df', 'live', 'lf'],
  h('th.Erel-bind', IM(AL(
      R`e \in ${E0('W', 'n', R`\Theta_1 \vdash T`, R`F \cup ${h('ty.heads', R`\mathsf{heads}`)}\,\Theta_2`)}`,
      R`\land\ \forall W' ${h('w.ext', R`\sqsupseteq`)} W,\ j \leq n,\ v \in ${h('th.Vrel', R`V^{W'}_j\llbracket\Theta_v \vdash T\rrbracket`)}.`,
      R`\qquad ${h('se.frame', 'f[v]')} \in ${E0(R`W'`, 'j', R`\Theta_v \cup \Theta_2 \vdash U`, 'F')}`),
    R`${h('se.frame', 'f[e]')} \in ${E0('W', 'n', R`\Theta_1 \cup \Theta_2 \vdash U`, 'F')}`)),
  '$E$ is closed under frames $f$, with the hole under $F \\cup \\mathsf{heads}\\,\\Theta_2$. \\annp{This holds for every cost table $\\kappa$.}');
TH('th-sound', 'Soundness', 'static/FundamentalProc.v: soundness; soup/LFTyped.v: lf_soundness', ['df', 'live', 'lf'],
  ROWS(
    h('th.soundness', IM(R`${STRICT}\,W \land \varnothing ${PT} p : T`, R`${DFP}\,p`)),
    h('th.lf-soundness', IM(R`${LFW} \land \varnothing ${PLF} p : T`, R`${LOCKF}\,p`))),
  'What it tells you. A closed typed process is deadlock free in every strict world. \\annp{A closed process typed at a finite counter bound with every thread guarded is lock free in every strict and well-founded world.}');
TH('th-sound-src', 'Soundness for a single program', 'static/FundamentalProc.v: soundness_source; soup/LFCompose.v: lf_soundness_source', ['df', 'live', 'lf'],
  ROWS(
    h('th.soundness-source', IM(R`\mathsf{strict}\,W \land ${PRIM} \land \varnothing ; \varnothing \vdash^{\varnothing}_W t : T`, R`\mathsf{deadlock\_free}(\varnothing, \{t\})`)),
    h('th.lf-soundness-source', IM(AL(R`\mathsf{strict}\,W \land \mathsf{wfworld}\,W \land N \in \mathbb{N} \land ${PRIM}`, R`\land\ ${CTY(R`\varnothing`, 't')} \land ${MEETS} \land ${GRD('t')}`), R`\mathsf{lock\_free}(\varnothing, \{t\})`))),
  'A closed program $t$ typed at a $\\mathsf{prim}$ result runs deadlock free as the one-thread process $(\\varnothing, \\{t\\})$. \\annp{With a finite counter bound, enough tickets and the guard it runs lock free.}');
TH('th-conserv', 'Conservativity', 'static/Conservativity.v: conservative, typed_dftyped, dftyped_typed', ['lf'],
  ROWS(
    h('th.conservative', AL(R`(\exists \varepsilon.\ \Gamma;${DF(R`\Delta`)} \vdash^{F}_{W,\infty} e : T_{df}\ !\ \varepsilon)`, R`\quad\iff\ \Gamma ; \Delta_{df} \vdash^{F}_{W} e : T_{df}`)),
    h('th.typed-dftyped', IM(R`\Gamma ; \Delta \vdash^{F}_{W,N} e : T\ !\ \varepsilon`, R`\Gamma ; \Delta_{df} \vdash^{F}_W e : T_{df}`))),
  'What it tells you. Lock-free typing loses no deadlock-free program. The annotated judgment at $N = \\infty$ types exactly what deadlock-free typing types, and erasing the annotations of any lock-free typing gives a deadlock-free typing.');
TH('th-cost', 'Cost', 'cost/CostFund.v: cost_fundamental, fsem_of_cost', ['lf'],
  ROWS(
    h('th.cost-fundamental', IM(R`\Gamma ; \Delta \vdash^{F}_{W,N} e : T\ !\ \varepsilon`, h('cs.csem', R`\Delta \vDash^{N} e : T\ !\ \varepsilon`))),
    h('th.fsem-of-cost', IM(R`${CTY(R`\Delta`, 'e')} \land ${PRIM} \land ${CRN(R`\Delta`)} \land ${MEETS}`, h('fu.fsem', R`\mathsf{fsem}\,N\,${h('th.styof', R`\Delta^{N}`)}\,e`)))),
  'A typed closed thread with all credits at most $N$ has fuel with every counter at $N$.');

// ---- notes ----
n("th.adequacy", "Adequacy", "For strict $W$, if $\\varnothing \\vDash_W p : T$ then $p$ is deadlock free.", "It turns the semantic judgment into the safety property. In a world with a cycle in $\\prec_W$ readiness holds vacuously for threads waiting round the cycle, so strictness is needed.", "Without $\\mathsf{strict}\\,W$ the premise holds for a cyclic world in which two threads wait on each other.", "Two threads closing the two ends of $c$ are deadlock free.", "relation/Adequacy.v: adequacy");
n("th.lf-adequacy", "Lock-free adequacy", "For $W$ with $\\mathsf{strict}\\,W$ and $\\mathsf{wfworld}\\,W$, if $\\varnothing \\Vvdash_W p : T$ then $p$ is lock free.", "A pending thread waits for the thread holding the partner of its end. The proof follows this chain of waiting threads and shows it is finite, by a measure of the point of the awaited end, the tickets left and the counter, which decreases because $\\prec_W$ is well-founded.", "Without $\\mathsf{wfworld}\\,W$ an infinite descending chain of points lets a thread wait forever along an infinite chain of holding threads.", "Two threads closing the two ends of $c$ are lock free.", "soup/LFAdequacy.v: lf_adequacy");
n("th.lf-thread-progress", "Thread progress", "Under the premises of lock-free adequacy, every run $(r, l)$ with $\\mathsf{erase}(r\\,0) = p$, $\\mathsf{maximal}\\,(r, l)$ and $\\mathsf{wfair}\\,(r, l)$ satisfies $\\mathsf{thread\\_progress\\_run}\\,(r, l)$.", "Every thread eventually returns a value or takes part in a session step, so no thread, pending or not, is postponed forever.", DEF, "Every lock-free example.", "soup/LFAdequacy.v: lf_thread_progress");
n("th.fundamental", "Fundamental theorem", "For strict $W$, $\\varnothing ; \\Delta \\vdash^{F}_{W} t : T$ implies $\\Delta \\vDash^{F}_{W} t : T$.", "Each typing rule has a semantic counterpart that holds at every level, and the theorem is the induction on the derivation.", DEF, "The main thread of the cycle example satisfies the semantic judgment.", "static/Fundamental.v: fundamental");
n("th.fundamental-typed", "Fundamental theorem for annotated typing", "For strict $W$ and every $N$, the annotated typing judgment implies the semantic judgment at $\\Delta_{df}$ and $T_{df}$.", "Erasing the annotations of an annotated derivation gives a deadlock-free derivation, to which the fundamental theorem applies.", DEF, "The client and server main at $N = \\infty$.", "static/Fundamental.v: fundamental_typed");
n("th.live-fundamental", "Live fundamental theorem", "For strict $W$, $\\varnothing ; \\Delta \\vdash^{F}_{W} t : T$ and $\\varnothing \\vdash\\!\\triangleright t$ imply $\\Delta \\mathrel{|\\!\\!\\vDash}^{F}_{W} t : T$.", "The guard lets a box recurse only after an action, so every recursive call is read at a lower level, as the least fixpoint of the relation at $\kappa_L$ requires.", "Without the guard the statement is false, $!(f = \\mathsf{force}\\,f)$ types and satisfies no live judgment.", "The guarded receive loop.", "static/LiveFundamental.v: live_fundamental");
n("th.live-fundamental-typed", "Live fundamental theorem for annotated typing", "For strict $W$, the annotated typing judgment with $\\varnothing \\vdash\\!\\triangleright t$ implies the live judgment at erased environments and type.", "Lock-free soundness obtains the relation at $\kappa_L$ of each thread from this theorem.", DEF, "A thread typed by P-Term at finite $N$.", "static/LiveFundamental.v: live_fundamental_typed");
n("th.fundamental-proc", "Fundamental theorem for processes", "For strict $W$, $\\Sigma \\vdash^{\\infty}_{W} p : T$ implies $\\Sigma \\vDash_W p : T$.", "It is an induction on the process derivation with the semantic P-Term and P-Connect as cases.", DEF, "Two threads closing the two ends of $c$.", "static/FundamentalProc.v: fundamental_proc");
n("th.lf-fundamental", "Lock-free fundamental theorem", "For strict $W$, $\\Sigma \\Vdash^{N}_{W} p : T$ implies $\\Sigma \\Vvdash_W p : T$.", "The fuel of each thread comes from its cost typing at finite $N$ with the ticket premise of P-Term, and its relation at $\kappa_L$ from its guarded typing.", DEF, "The cycle example.", "soup/LFTyped.v: lf_fundamental");
n("th.sem-p-term", "Semantic P-Term", "If $\\mathsf{prim}\\,T$, $\\mathsf{sth}\\,\\Theta\\,\\Sigma\\,\\Theta_B\\,C$ and $t \\in E[\\kappa]^{W}_{n}\\llbracket\\Theta \\vdash T\\rrbracket^{\\varnothing}$, then $(C, \\{t\\}) \\in P[\\kappa]^{W}_{n}\\llbracket\\Sigma \\vdash T\\rrbracket$.", "It is P-Term in the relation. When $t$ spawns $v$, the child receives exactly the ends $\\mathsf{fends}(v)$, which $V$ fixes by $\\mathrm{dom}\\,\\Theta = \\mathsf{fends}(v)$, and the proof composes parent and child as P-Connect does.", DEF, "A single thread with $\\Sigma = \\varnothing$ and $C = \\varnothing$.", "compat/PTerm.v: sem_p_term");
n("th.sth", "$\\mathsf{sth}\\,\\Theta\\,\\Sigma\\,\\Theta_B\\,C$", "$\\Theta = \\Sigma \\cup \\Theta_B$, $\\mathrm{dom}\\,\\Theta_B = \\mathsf{ends}(C)$, $\\mathsf{chans}\\,\\Sigma \\cap C = \\varnothing$, $\\mathsf{pfree}\\,\\Sigma$, and for every $c \\in C$ the two entries of $\\Theta_B$ are dual at dual points.", "These are the environment premises of P-Term, as the semantic proof uses these premises.", DEF, "$\\Sigma = \\varnothing$ and $C = \\varnothing$ for a source program.", "compat/PTerm.v: sth");
n("th.sem-p-connect", "Semantic P-Connect", "If $\\mathsf{prim}\\,T$, $\\mathsf{conn}$, $p_1 \\in P^{W_1}_n\\llbracket\\Sigma_1 \\cup \\Sigma_C \\vdash T\\rrbracket$ and $p_2 \\in P^{W_2}_n\\llbracket\\Sigma_2 \\cup \\Sigma_D \\vdash \\ast\\rrbracket$, then $p_1 \\parallel_{\\Sigma_C} p_2 \\in P^{W_1 \\sqcup W_2}_n\\llbracket\\Sigma_1 \\cup \\Sigma_2 \\vdash T\\rrbracket$.", "It is P-Connect in the relation, for every level $n$ and every cost table.", DEF, "Two threads closing $c^{+}$ and $c^{-}$, cut at $c$.", "compat/ConnectP.v: sem_p_connect");
n("th.lf-p-term", "P-Term in the lock-free process relation", "For strict $W$, a thread with $\\Sigma \\Vdash^{N}_{W} (C_0, \\{t\\}) : T$ derived by P-Term satisfies $\\Sigma \\Vvdash_W (C_0, \\{t\\}) : T$.", "It is P-Term read in the lock-free process relation.", DEF, "One thread closing its end $c^{+}$.", "soup/LFCompose.v: lf_p_term");
n("th.Erel-bind", "Bind", "For every cost table, if $e \\in E^{W}_{n}\\llbracket\\Theta_1 \\vdash T\\rrbracket^{F \\cup \\mathsf{heads}\\,\\Theta_2}$ and $f[v] \\in E^{W'}_{j}\\llbracket\\Theta_v \\cup \\Theta_2 \\vdash U\\rrbracket^{F}$ for all $W' \\sqsupseteq W$, $j \\leq n$ and $v \\in V^{W'}_{j}\\llbracket\\Theta_v \\vdash T\\rrbracket$, then $f[e] \\in E^{W}_{n}\\llbracket\\Theta_1 \\cup \\Theta_2 \\vdash U\\rrbracket^{F}$.", "Every rule with a subterm runs the subterm first. The frame holds $\\Theta_2$ while the hole runs, so the hole must not wait above $\\mathsf{heads}\\,\\Theta_2$.", DEF, "$\\mathsf{let}\\ \\ast = \\mathsf{close}\\,c\\ \\mathsf{in}\\ \\mathsf{close}\\,d$ runs $\\mathsf{close}\\,c$ with $\\overline{x_d}$ in its future.", "compat/Bind.v: Erel_bind");
n("th.soundness", "Soundness", "For strict $W$, $\\varnothing \\vdash^{\\infty}_{W} p : T$ implies that $p$ is deadlock free.", "The fundamental theorem for processes followed by adequacy.", DEF, "The cycle example is deadlock free.", "static/FundamentalProc.v: soundness");
n("th.soundness-source", "Soundness for source terms", "For strict $W$, $\\mathsf{prim}\\,T$ and $\\varnothing ; \\varnothing \\vdash^{\\varnothing}_{W} t : T$, the process $(\\varnothing, \\{t\\})$ is deadlock free.", "A source term creates channels only at fresh roots and at fields of held ends, so it is P-Term with $\\Sigma = \\varnothing$ and $C_0 = \\varnothing$.", DEF, "Every deadlock-free example.", "static/FundamentalProc.v: soundness_source");
n("th.lf-soundness", "Lock-free soundness", "For $W$ with $\\mathsf{strict}\\,W$ and $\\mathsf{wfworld}\\,W$, $\\varnothing \\Vdash^{N}_{W} p : T$ implies that $p$ is lock free.", "The lock-free fundamental theorem followed by lock-free adequacy.", DEF, "The cycle example is lock free.", "soup/LFTyped.v: lf_soundness");
n("th.lf-soundness-source", "Lock-free soundness for source terms", "For $W$ with $\\mathsf{strict}\\,W$ and $\\mathsf{wfworld}\\,W$, $N \\in \\mathbb{N}$, $\\mathsf{prim}\\,T$, a typing $\\varnothing ; \\varnothing \\vdash^{\\varnothing}_{W,N} t : T\\ !\\ (c, \\vartheta)$, $\\vartheta(0) \\in \\mathbb{N}$, and $\\varnothing \\vdash\\!\\triangleright t$, the process $(\\varnothing, \\{t\\})$ is lock free.", "The premises are those of P-Term at finite $N$ with $\\Sigma = \\varnothing$ and $C_0 = \\varnothing$, plus the guard. Lock-free soundness then applies.", DEF, "Every lock-free example.", "soup/LFCompose.v: lf_soundness_source");
n("th.conservative", "Conservativity", "The annotated typing judgment at $N = \\infty$ derives some $T_{df}\\ !\\ \\varepsilon$ iff the deadlock-free judgment derives $T_{df}$, at erased contexts.", "Deadlock-free typing is the annotated typing judgment with credits, costs and ticket needs ignored, so one set of rules serves both.", DEF, "The client and server main.", "static/Conservativity.v: conservative");
n("th.typed-dftyped", "Erasure to deadlock-free typing", "For every $N$, erasing the annotations of an annotated derivation gives a deadlock-free derivation.", "Hence every lock-free typing is also a deadlock-free typing.", DEF, "The cycle at $N = 2$ erases to its deadlock-free typing.", "static/Conservativity.v: typed_dftyped");
n("th.wfworld", "$\\mathsf{wfworld}\\,W$", "$\\prec_W$ is well-founded, there is no infinite descending chain $x_0 \\succ_W x_1 \\succ_W \\cdots$.", "A chain of waiting threads descends in $\\prec_W$, so well-foundedness makes it finite. Deadlock freedom does not need well-foundedness.", DEF, "Every world of the lock-free examples is well-founded.", "types/Worlds.v: wfworld");
n("th.cost-fundamental", "Cost fundamental theorem", "The annotated typing judgment implies the semantic cost judgment $\\Delta \\vDash^{N} e : T\\ !\\ \\varepsilon$.", "It is the cost half of the annotated typing judgment, proved rule by rule.", DEF, "The forwarder $\\mathsf{fw}$.", "cost/CostFund.v: cost_fundamental");
n("th.fsem-of-cost", "Fuel from cost typing", "If $\\varnothing ; \\Delta \\vdash^{\\varnothing}_{W,N} e : T\\ !\\ (c, \\vartheta)$, $\\mathsf{prim}\\,T$, $\\mathsf{cr}(\\Delta) \\leq N$ and $\\vartheta(0) \\in \\mathbb{N}$, then $\\mathsf{fsem}\\,N\\,(\\mathsf{sty} \\circ \\Delta)\\,e$.", "P-Term gives every end credit $N$, so the cost judgment yields the per-thread fuel that lock freedom needs.", "If a closure could mention an end it does not own, the forwarder could receive a closure that owns nothing and would have no fuel after spawning the closure.", "The forwarder $\\mathsf{fw}$.", "cost/CostFund.v: fsem_of_cost");
n('th.crle', R`$\mathsf{cr}(\Delta) \leq N$`, R`Every credit in $\Delta$ is at most the counter bound $N$, that is $a \leq N$ for every entry $(S@x)^{a}$ or $(T \multimap U)^{a}$ of $\Delta$.`, R`A thread starts with every counter at $N$, so its credits may guarantee no more than $N$.`, R`A credit above $N$ would allow more postponement than a fresh counter allows.`, R`$\mathsf{cr}(\{o \mapsto (S@x)^{2}\}) \leq 3$.`, 'cost/CostFund.v: fsem_of_cost');
n('ann.fin0', R`$\vartheta(0) \in \mathbb{N}$`, R`The ticket need of a whole thread, which keeps no reserve, is a finite number.`, R`Then some ticket count $tk \geq \vartheta(0)$ covers every link of the thread.`, R`A need that is $\infty$ at reserve $0$ belongs to a thread that may link without bound.`, R`$(0, 1)(0) = 1$, one link.`, 'types/Costs.v: meets, tapp');
n("th.Prel", "The process relation $P$", "$P[\\kappa]^{W}_{n}\\llbracket\\Sigma \\vdash T\\rrbracket$, the processes in the relation at table $\\kappa$, world $W$, level $n$, interface $\\Sigma$ and result $T$.", "The semantic process judgment asks membership at every level $n$.", DEF, "Two threads closing $c^{+}$ and $c^{-}$ lie in $P^{W}_{n}\\llbracket\\varnothing \\vdash \\ast\\rrbracket$ for every $n$.", "relation/Relation.v: Prel");
n("th.Erel", "The term relation $E$", "$E[\\kappa]^{W}_{n}\\llbracket\\Theta \\vdash T\\rrbracket^{F}$ is the set of terms in the relation at cost table $\\kappa$, world $W$ and level $n$, for ends $\\Theta$, result $T$ and future $F$.", "The semantic term judgment asks membership at each level and for each grounding of the variables.", DEF, "$\\mathsf{close}\\,c^{+} \\in E^{W}_{n}\\llbracket\\{c^{+} \\mapsto \\mathsf{Close}@x\\} \\vdash \\ast\\rrbracket^{\\varnothing}$.", "relation/Relation.v: Erel");
n("th.Vrel", "The value relation $V$", "$V^{W}_{j}\\llbracket\\Theta \\vdash T\\rrbracket$ is the set of values in the relation at world $W$ and level $j$, for ends $\\Theta$ and type $T$.", "A term in $E$ that is irreducible is a value in $V$.", DEF, "$c^{+} \\in V^{W}_{j}\\llbracket\\{c^{+} \\mapsto \\mathsf{Close}@x\\} \\vdash \\mathsf{Close}@x\\rrbracket$.", "relation/Relation.v: Vrel");
n("th.soup", "The lock-free process relation $S^{N,W}_{n}$", "$a \\in S^{N,W}_{n}\\llbracket\\Sigma \\vdash T\\rrbracket$ holds of a annotated configuration $a$ when every thread of $a$ is in the relation at $\kappa_L$ and has fuel at index $n$, with the ownership, points and counters that $a$ records.", "The state $a$ is fixed outside the index, so ownership is the same at every index $n$.", DEF, "The state of two threads closing $c^{+}$ and $c^{-}$.", "soup/Soup.v: Soup");
n("th.qa", "$q_a$", "The configuration of the annotated configuration $a$.", "An annotated configuration is a configuration together with ownership and tickets.", DEF, "$q_a = (C, M)$.", "soup/State.v: s_q");
n("th.conn", "$\\mathsf{conn}$", "The side conditions of P-Connect, with $\\Sigma_D$ the partners of $\\Sigma_C$ dual up to $\\approx$ at dual points.", "They make the composite a process in which every channel belongs to one side.", DEF, "$\\Sigma_C = \\{c^{+} \\mapsto \\mathsf{Close}@x\\}$ and $\\Sigma_D = \\{c^{-} \\mapsto \\mathsf{Close}@\\overline{x}\\}$.", "compat/Connect.v: conn, cut_dual");
n("th.par", "$p_1 \\parallel_{\\Sigma_C} p_2$", "The composite $(C_1 \\cup C_2 \\cup \\mathsf{chans}\\,\\Sigma_C, E_1 \\uplus E_2)$ of $p_1 = (C_1, E_1)$ and $p_2 = (C_2, E_2)$.", "After composition the two sides communicate on the cut, which no outside process holds.", DEF, "$\\mathsf{close}\\,c^{+} \\parallel \\mathsf{close}\\,c^{-}$ restricts $c$.", "compat/Connect.v: pconn");
n("th.df", "Erasure $X_{df}$", "$\\Delta_{df}$ and $T_{df}$ drop every credit, cost and ticket need and keep session types, points and facts.", "Deadlock-free typing and the relations read no annotation.", DEF, "$(S@x)^{3}$ erases to $S@x$.", "types/Types.v: ty_df, static/Contexts.v: tenv_df, lenv_df");
n("th.styof", "$\\Delta^{N}$", "The held ends of $\\Delta$ for fuel, each at counter $N$. An entry $o \\mapsto (S@x)^{a}$ of $\\Delta$ becomes $o \\mapsto S^{N}$.", "Fuel reads protocols and counters and ignores points and credits. A thread starts with each counter at $N$.", DEF, "$\\{a \\mapsto (S@x)^{2}\\}^{N} = \\{a \\mapsto S^{N}\\}$.", "cost/CostFund.v: fsem_of_cost");

// ---- examples ----
examples.push(
  { id: 'ex-cs', title: 'Client and server cycle', modes: ['df', 'live', 'lf'],
    code: `main = let ⟨a, a′⟩ = new in                    -- a at ρ
       let ⟨b, b′⟩ = new in                    -- b at ρ·0, facts C at (ρ, ρ·0, ρ·1)
       let ∗ = spawn (λu. let ∗ = u in (force srv) ⟨a′, b′⟩) in
       (force cli) ⟨a, b⟩
cli  = !(f = λp. let ⟨a, b⟩ = p in let a = send ⟨∗, a⟩ in
                let ⟨u, b⟩ = recv b in let ∗ = u in (force f) ⟨a, b⟩)
srv  = !(g = λp. let ⟨a, b⟩ = p in let ⟨u, a⟩ = recv a in let ∗ = u in
                let b = send ⟨∗, b⟩ in (force g) ⟨a, b⟩)
-- both boxes : □∀ι κ ζ. C. ∗ ⊸ (S1@ι ⊗ S2@κ ⊸^ζ ∗)
-- C = {ι+k ≺ (κ+k)‾, κ+k ≺ (ι+k+1)‾, ι+k ≺ ζ, κ+k ≺ ζ | k}`,
    shows: "The second $\\mathsf{new}$ places $b$ at $\\rho\\cdot 0$ and states $C$ at $(\\rho, \\rho\\cdot 0, \\rho\\cdot 1)$, the facts the self call at $(\\iota^{+}, \\kappa^{+}, \\zeta)$ needs.",
    rocq: 'examples/ClientServer.v: cs_typed; examples/LFClientServer.v: cs_lftyped, cs_lock_free',
    accepts: { df: { ok: true, rocq: 'cs_dftyped, cs_typed' }, live: { ok: true, rocq: 'cs_dftyped, cs_guarded' }, lf: { ok: true, N: 3, rocq: 'cs_lftyped, cs_lock_free' } } },
  { id: 'ex-cycle', title: 'Cycle', modes: ['df', 'live', 'lf'],
    code: `cycle = let ⟨c, c′⟩ = new in          -- c at ρ
        let ⟨d, d′⟩ = new in          -- d at ρ·0, C = {ρ ≺ (ρ·0)‾, ρ‾ ≺ ρ·0}
        let ∗ = spawn (λu. let ∗ = u in let ∗ = close c′ in close d′) in
        let ∗ = close c in close d`,
    shows: "The second $\\mathsf{new}$ states exactly $\\rho \\prec \\overline{\\rho\\cdot 0}$ and $\\overline{\\rho} \\prec \\rho\\cdot 0$, the two facts the two threads need.",
    rocq: 'examples/Cycle.v: cy_typed; examples/LFCycle.v: cy_lftyped, cy_lock_free',
    accepts: { df: { ok: true, rocq: 'cy_dftyped, cy_typed' }, live: { ok: true, rocq: 'cy_dftyped, cy_guarded' }, lf: { ok: true, N: 2, rocq: 'cy_lftyped, cy_lock_free' } } },
  { id: 'ex-between', title: 'A channel between two box arguments', modes: ['df', 'live', 'lf'],
    code: `between : □(∀ι κ. C. ∗ ⊸ Close@ι ⊗ Close@κ ⊸^κ ∗)
between = !(f = λp. let ⟨c, e⟩ = p in
                    let ⟨d, d′⟩ = new in        -- d at ι·0
                    let ∗ = spawn (λu. let ∗ = u in close d′) in
                    let ∗ = close c in let ∗ = close d in close e)
-- C = {ι ≺ κ, ι ≺ κ‾, ι ≺ δ‾, δ ≺ κ, δ ≺ κ‾},  δ = ι·0
main: c by new at ρ, e by new at ρ·1, force between at (ρ, ρ·1)`,
    shows: "The box places its new channel at the field $\\iota\\cdot 0$ of the point of $c$, so no point between two box points is needed.",
    rocq: 'examples/FreshBetween.v: fb_typed; examples/LFFreshBetween.v: fb_lftyped, fb_lock_free',
    accepts: { df: { ok: true, rocq: 'fb_dftyped, fb_typed' }, live: { ok: true, rocq: 'fb_dftyped, fb_guarded' }, lf: { ok: true, N: 2, rocq: 'fb_lftyped, fb_lock_free' } } },
  { id: 'ex-many', title: 'A channel that acts several times', modes: ['df', 'live', 'lf'],
    code: `many = !(f = λp. let ⟨c, e⟩ = p in
                 let ⟨d, d′⟩ = new in         -- d at δ
                 let ∗ = spawn (λu. let ∗ = u in
                                     let ⟨v, d′⟩ = recv d′ in let ∗ = v in
                                     let ⟨w, d′⟩ = recv d′ in let ∗ = w in close d′) in
                 let ∗ = close c in
                 let ∗ = close (send ⟨∗, send ⟨∗, d⟩⟩) in close e)
-- C = {ι ≺ κ, ι ≺ κ‾, ι ≺ δ‾} ∪ {δ+k ≺ κ, δ+k ≺ κ‾ | k},  δ = ι·0`,
    shows: "An infinite box constraint lets $d$ act at $\\delta, \\delta^{+}, \\delta^{++}$ while $e$ is held at $\\kappa$.",
    rocq: 'examples/FreshMany.v: fm_typed; examples/LFFreshMany.v: fm_lftyped, fm_lock_free',
    accepts: { df: { ok: true, rocq: 'fm_dftyped, fm_typed' }, live: { ok: true, rocq: 'fm_dftyped, fm_guarded' }, lf: { ok: true, N: 4, rocq: 'fm_lftyped, fm_lock_free' } } },
  { id: 'ex-factory', title: 'The factory', modes: ['df', 'live', 'lf'],
    code: `mk₀  = !(f = λu. let ∗ = u in let ⟨c, c′⟩ = new in
                let ∗ = spawn (λv. let ∗ = v in close (send ⟨∗, c⟩)) in c′)
mk₁  = !(f = λp. let ⟨c, c′⟩ = new in
                let ∗ = spawn (λv. let ∗ = v in close (send ⟨∗, c⟩)) in ⟨p, c′⟩)
main = let p = (force mk₀) ∗ in let ⟨p, q⟩ = (force mk₁) p in
       let ∗ = recvclose p in recvclose q
-- mk₀ places c at a fresh ρ with C(ρ) = {ρ‾ ≺ ρ·0, ρ‾⁺ ≺ ρ·0}, mk₁ at ι·0 for p at ι
-- mk₀ : □(∗ ⊸ ∃^⊥ ι. C(ι). (?∗.Close)@ι‾)`,
    shows: "The first call creates at a fresh root and the second at a field of the end it receives, two typings of the same creation.",
    rocq: 'examples/FactoryEx.v: fx_typed; examples/LFFactoryEx.v: fx_lftyped, fx_lock_free',
    accepts: { df: { ok: true, rocq: 'fx_dftyped, fx_typed' }, live: { ok: true, rocq: 'fx_dftyped, fx_guarded' }, lf: { ok: true, N: 2, rocq: 'fx_lftyped, fx_lock_free' } } },
  { id: 'ex-ring', title: 'The growing ring', modes: ['df', 'live', 'lf'],
    code: `Sch  = µα. ?(κ. α@κ).Close
ring : □(∀ι₁ ι₂. Cr. ∗ ⊸ (Sch@ι₁ ⊗ S̄ch@ι₂ ⊸^{ι₁+1} ∗))
ring = !(f = λp. let ⟨x, y⟩ = p in
           let ⟨a, a′⟩ = new in                -- a at ι₂·0
           let ∗ = spawn (λw. let ∗ = w in close (send ⟨a, y⟩)) in
           let ⟨b, b′⟩ = new in                -- b at ι₁·1
           let ⟨z, x⟩ = recv x in let ∗ = close x in
           let ∗ = spawn (λw. let ∗ = w in (force f) ⟨z, b′⟩) in
           spawn (λw. let ∗ = w in (force f) ⟨b, a′⟩))
main = let ⟨e, e′⟩ = new in (force ring) ⟨e, e′⟩`,
    shows: "$b$ is created at $\\iota_1\\cdot 1$ before the receive on $x$, while $x$ is held at $\\iota_1$.",
    rocq: 'examples/GrowRing.v: rg_typed; examples/LFGrowRing.v: rg_lftyped, rg_lock_free',
    accepts: { df: { ok: true, rocq: 'rg_dftyped, rg_typed' }, live: { ok: true, rocq: 'rg_dftyped, rg_guarded' }, lf: { ok: true, N: 4, rocq: 'rg_lftyped, rg_lock_free' } } },
  { id: 'ex-close', title: 'Two threads closing one channel', modes: ['lf'],
    code: `cl c⁺ ∥ cl c⁻,   cl o = close o
-- each thread by P-Term at every finite N over its end, cut c by P-Connect at exactly dual types`,
    shows: "The smallest use of P-Term and P-Connect, cutting $c$ at exactly dual types in a world without facts.",
    rocq: 'examples/LFClose.v: cl_lftyped, cl_lock_free',
    accepts: { lf: { ok: true, N: 'every', rocq: 'cl_lftyped, cl_lock_free' } } },
  { id: 'ex-guard-neg', title: 'Guard rejections', modes: ['live', 'lf'],
    code: `div_box     = !(f = force f)                         -- loops on β steps
pn_fix      = !(f = λx. (force f) x)                  -- fix λx.x
cx_box      = !(f = let ∗ = (force f) ∗ in λy. y)     -- recurses before returning
spawn_loop  = !(f = λc. spawn (λ_. (force f) c))      -- spawns forever`,
    shows: "Each box uses its self before any session action, so $\\varnothing \\vdash\\!\\triangleright t$ fails for every $t$ listed.",
    rocq: 'examples/GuardEx.v: div_not_guarded, pn_fix_not_guarded, cx_not_guarded, spawn_loop_not_guarded',
    accepts: { live: { ok: false, part: 'guard', rocq: 'div_not_guarded, pn_fix_not_guarded, cx_not_guarded, spawn_loop_not_guarded' }, lf: { ok: false, part: 'guard', rocq: 'div_not_guarded, pn_fix_not_guarded, cx_not_guarded, spawn_loop_not_guarded' } } },
  { id: 'ex-guard-pos', title: 'Guard acceptances', modes: ['live', 'lf'],
    code: `loop  = !(f = λx. let ⟨v, x′⟩ = recv x in (force f) x′)
stage = !(f = λin. let ⟨v, in⟩ = recv in in let ∗ = close in in
                  let ⟨a, b⟩ = new in let ∗ = spawn (λ_. (force f) b) in
                  close (send ⟨v, a⟩))                  -- a pipeline stage`,
    shows: "$\\mathsf{recv}$ acts, so the rest of the body is checked under $\\varnothing$ and the self is unmarked when it is forced.",
    rocq: 'examples/GuardEx.v: loop_guarded, stage_guarded',
    accepts: { live: { ok: true, part: 'guard', rocq: 'loop_guarded, stage_guarded' }, lf: { ok: true, part: 'guard', rocq: 'loop_guarded, stage_guarded' } } },
  { id: 'ex-forwarder', title: 'The spawn forwarder', modes: ['lf'],
    code: `fw o = let ⟨w, c⟩ = recv o in let ∗ = close c in spawn w
o : ?((∗ ⊸ ∗)^2).Close
dead_thunk q = λ_. let ∗ = Ω in close q`,
    shows: "$\\mathsf{dead\\_thunk}\\,q$ mentions $q$ and owns nothing, so it is not in the fuel relation and $\\mathsf{fw}$ has fuel for every closure it receives.",
    rocq: 'cost/Forwarder.v: dead_thunk_rejected, fw_ptyped; cost/CostFund.v: fw_fsem',
    accepts: { lf: { ok: true, N: 'every', part: 'typing and fuel', rocq: 'fw_ptyped, fw_fsem, dead_thunk_rejected' } } },
  { id: 'ex-controller', title: 'The controller', modes: ['lf'],
    code: `main = let ⟨a, a′⟩ = new in let ⟨b, b′⟩ = new in   -- a at ρ, b at ρ·0
       let ⟨c, c′⟩ = new in                              -- c at ρ·2
       let ∗ = spawn (λu. let ∗ = u in (force srv) ⟨⟨a′, b′⟩, c′⟩) in
       (force cli) ⟨⟨a, b⟩, c⟩
cli  = !(f = λp. let ⟨q, k⟩ = p in let ⟨a, b⟩ = q in
                let a = send ⟨∗, a⟩ in let ⟨u, b⟩ = recv b in
                let ∗ = u in (force f) ⟨⟨a, b⟩, k⟩)
-- c sits at Skip on each side, an idle end`,
    shows: "The idle end $k$ at $\\mathsf{Skip}@\\chi$ is held across every round at credit $0$, because $(\\mathsf{Skip}@\\chi)^{a} - c = (\\mathsf{Skip}@\\chi)^{\\max(a - c, 0)}$ asks no $c \\leq a$.",
    rocq: 'examples/LFController.v: ctl_typedN, ctl_guarded, ctl_lftyped, ctl_lock_free',
    accepts: { lf: { ok: true, N: 3, rocq: 'ctl_lftyped' } } },
  { id: 'ex-flag', title: 'Self-computed flag', modes: ['df', 'live', 'lf'],
    code: `not     = λz. case z of inl w ⇒ inj₂ w | inr w ⇒ inj₁ w
thread  = case not (inj₂ ∗) of
            inl _ ⇒ let ∗ = close c in close d      -- runs
          | inr _ ⇒ let ∗ = close d in close c      -- never runs
partner = let ∗ = close c̄ in close d̄
-- the process ({c, d}, {thread, partner}), c at x, d at y`,
    rocq: 'examples/SemBranch.v: sb_thread_E, sb_deadlock_free',
    accepts: { df: { ok: false, part: 'P-Connect', rocq: 'argued in docs/redesign/semantic-example.md, no Rocq proof' }, sem: { ok: true, rocq: 'sb_thread_E, sb_deadlock_free' } } }
);

n("th.tpr", "$\\mathsf{thread\\_progress\\_run}$", "For a run $(r, l)$, $\\mathsf{thread\\_progress\\_run}\\,(r, l)$ holds iff each thread $t$ of each position $i$ later stops or acts. That is, some $j \\geq i$ exists at which $t$ is a value in $r\\,j$ or takes part in the step $l\\,j$ by a session action.", "It states lock freedom per run for each thread, including the threads that are not pending. A thread that is neither stopped nor acting forever would be postponed without end.", DEF, "In a run of two threads closing $c^{+}$ and $c^{-}$, both threads take part in the close step.", "lockfree/ThreadProgress.v: thread_progress_run");

// ---- signatures and arguments ----
const A = (name, meaning) => ({ name, meaning });
const aW = A('W', R`a world, the order $\prec_W$ the semantic judgments read`);
const aP = A('p', R`a closed process $(C, E)$`);
const aT = A('T', R`the result type of the main thread`);
const aK = A(R`\kappa`, R`a cost table, $\kappa_{DF}$ for deadlock freedom and $\kappa_L$ for liveness`);
const aN = A('n', R`the level, a natural number`);
const aSi = A(R`\Sigma`, R`the interface of the process`);
const aTh = A(R`\Theta`, R`the ends held by the term`);
const aDe = A(R`\Delta`, R`the linear context of ends and variables`);
const aF = A('F', R`the future`);
const aNf = A('N', R`the counter bound, a natural number for lock freedom`);
const run = [A(R`(r, l)`, R`a run, $r\,i$ the configuration and $l\,i$ the event at position $i$`)];
sa('th.adequacy', R`\mathsf{strict}\,W \land \varnothing \vDash_W p : T \Rightarrow \mathsf{deadlock\_free}\,p`, [aW, aP, aT]);
sa('th.lf-adequacy', R`\mathsf{strict}\,W \land \mathsf{wfworld}\,W \land \varnothing \Vvdash_W p : T \Rightarrow \mathsf{lock\_free}\,p`, [aW, aP, aT]);
sa('th.lf-thread-progress', R`\ldots \Rightarrow \forall (r, l).\ \mathsf{erase}(r\,0) = p \land \mathsf{maximal}\,(r, l) \land \mathsf{wfair}\,(r, l) \Rightarrow \mathsf{thread\_progress\_run}\,(r, l)`, [aW, aP, ...run]);
sa('th.fundamental', R`\mathsf{strict}\,W \land \varnothing ; \Delta \vdash^{F}_{W} t : T \Rightarrow \Delta \vDash^{F}_{W} t : T`, [aW, aDe, aF, A('t', R`the term`), A('T', R`its type`)]);
sa('th.fundamental-typed', R`\mathsf{strict}\,W \land \varnothing ; \Delta \vdash^{F}_{W,N} t : T\ !\ \varepsilon \Rightarrow \Delta_{df} \vDash^{F}_{W} t : T_{df}`, [aW, aDe, A('N', R`any counter bound`)]);
sa('th.live-fundamental', R`\mathsf{strict}\,W \land \varnothing ; \Delta \vdash^{F}_{W} t : T \land \varnothing \vdash\!\triangleright t \Rightarrow \Delta \mathrel{|\!\!\vDash}^{F}_{W} t : T`, [aW, aDe, aF, A('t', R`the guarded term`)]);
sa('th.live-fundamental-typed', R`\mathsf{strict}\,W \land \ldots \vdash^{F}_{W,N} t : T\ !\ \varepsilon \land \varnothing \vdash\!\triangleright t \Rightarrow \Delta_{df} \mathrel{|\!\!\vDash}^{F}_{W} t : T_{df}`, [aW, A('N', R`any counter bound`), A('t', R`the guarded term`)]);
sa('th.fundamental-proc', R`\mathsf{strict}\,W \land \Sigma \vdash^{\infty}_{W} p : T \Rightarrow \Sigma \vDash_W p : T`, [aW, aSi, aP, aT]);
sa('th.lf-fundamental', R`\mathsf{strict}\,W \land \Sigma \Vdash^{N}_{W} p : T \Rightarrow \Sigma \Vvdash_W p : T`, [aW, aSi, aNf, aP, aT]);
sa('th.sem-p-term', R`\mathsf{prim}\,T \land \mathsf{sth}\,\Theta\,\Sigma\,\Theta_B\,C \land t \in E[\kappa]^{W}_{n}\llbracket\Theta \vdash T\rrbracket^{\varnothing} \Rightarrow (C, \{t\}) \in P[\kappa]^{W}_{n}\llbracket\Sigma \vdash T\rrbracket`, [aK, aN, aSi, A(R`\Theta_B`, R`the entries of the restricted ends`), A('C', R`the restricted channels`), A('t', R`the thread`)]);
sa('th.sth', R`\mathsf{sth} : \mathsf{Env} \to \mathsf{Env} \to \mathsf{Env} \to \mathcal{P}(\mathsf{Chan}) \to \mathsf{Prop}`, [aTh, aSi, A(R`\Theta_B`, R`the entries of the ends of restricted channels`), A('C', R`the restricted channels`)]);
sa('th.sem-p-connect', R`\mathsf{prim}\,T \land \mathsf{conn} \land p_1 \in P^{W_1}_{n}\llbracket\Sigma_1 \cup \Sigma_C \vdash T\rrbracket \land p_2 \in P^{W_2}_{n}\llbracket\Sigma_2 \cup \Sigma_D \vdash \ast\rrbracket \Rightarrow p_1 \parallel_{\Sigma_C} p_2 \in P^{W_1 \sqcup W_2}_{n}\llbracket\Sigma_1 \cup \Sigma_2 \vdash T\rrbracket`, [aN, A(R`\Sigma_C, \Sigma_D`, R`the cut and its partners`), A(R`p_1, p_2`, R`the two components`)]);
sa('th.lf-p-term', R`\mathsf{strict}\,W \land \Sigma \Vdash^{N}_{W} (C_0, \{t\}) : T \Rightarrow \Sigma \Vvdash_W (C_0, \{t\}) : T`, [aW, aSi, A('t', R`the single thread`), A(R`C_0`, R`its restricted channels`)]);
sa('th.Erel-bind', R`e \in E^{W}_{n}\llbracket\Theta_1 \vdash T\rrbracket^{F \cup \mathsf{heads}\,\Theta_2} \land (\forall W' \sqsupseteq W, j \leq n, v.\ \ldots) \Rightarrow f[e] \in E^{W}_{n}\llbracket\Theta_1 \cup \Theta_2 \vdash U\rrbracket^{F}`, [A('f', R`an evaluation frame`), A(R`\Theta_2`, R`the ends the frame holds while $e$ runs`), A(R`W', j, v`, R`every later world, every level $j \leq n$ and every value $v$ in $V^{W'}_{j}$ that $e$ may return`)]);
sa('th.soundness', R`\mathsf{strict}\,W \land \varnothing \vdash^{\infty}_{W} p : T \Rightarrow \mathsf{deadlock\_free}\,p`, [aW, aP, aT]);
sa('th.soundness-source', R`\mathsf{strict}\,W \land \mathsf{prim}\,T \land \varnothing ; \varnothing \vdash^{\varnothing}_{W} t : T \Rightarrow \mathsf{deadlock\_free}(\varnothing, \{t\})`, [aW, A('t', R`a source term, the main thread`), aT]);
sa('th.lf-soundness', R`\mathsf{strict}\,W \land \mathsf{wfworld}\,W \land \varnothing \Vdash^{N}_{W} p : T \Rightarrow \mathsf{lock\_free}\,p`, [aW, aNf, aP, aT]);
sa('th.lf-soundness-source', R`\mathsf{strict}\,W \land \mathsf{wfworld}\,W \land N \in \mathbb{N} \land \ldots \Rightarrow \mathsf{lock\_free}(\varnothing, \{t\})`, [aW, aNf, A('t', R`the source term`), A('tk', R`a ticket count with $\vartheta(0) \in \mathbb{N}$`)]);
sa('th.conservative', R`(\exists \varepsilon.\ \ldots \vdash^{F}_{W,\infty} e : T_{df}\ !\ \varepsilon) \iff \ldots \vdash^{F}_{W} e : T_{df}`, [A(R`a, c, \vartheta`, R`some credit, cost and ticket need`), A('e', R`the term`)]);
sa('th.typed-dftyped', R`\Gamma ; \Delta \vdash^{F}_{W,N} e : T\ !\ \varepsilon \Rightarrow \Gamma ; \Delta_{df} \vdash^{F}_{W} e : T_{df}`, [A('N', R`any counter bound`)]);
sa('th.wfworld', R`\mathsf{wfworld} : \mathsf{World} \to \mathsf{Prop}`, [aW]);
sa('th.cost-fundamental', R`\Gamma ; \Delta \vdash^{F}_{W,N} e : T\ !\ \varepsilon \Rightarrow \Delta \vDash^{N} e : T\ !\ \varepsilon`, [A('N', R`the counter bound`), A('e', R`the term`)]);
sa('th.fsem-of-cost', R`\varnothing ; \Delta \vdash^{\varnothing}_{W,N} e : T\ !\ (c, \vartheta) \land \mathsf{prim}\,T \land \mathsf{cr}(\Delta) \leq N \land \vartheta(0) \in \mathbb{N} \Rightarrow \mathsf{fsem}\,N\,\Delta^{N}\,e`, [A(R`\Delta`, R`the ends of the thread with their credits`)]);
sa('th.crle', R`\mathsf{cr} : \mathsf{TEnv} \to \mathbb{N} \cup \{\infty\}`, [A(R`\Delta`, R`a context`), A('N', R`the counter bound`)]);
sa('ann.fin0', R`\vartheta(0) \in \mathbb{N} : \mathsf{Prop}`, [A(R`\vartheta`, R`the ticket need of the thread`)]);
sa('th.Prel', R`P[\kappa]^{W}_{n}\llbracket\Sigma \vdash T\rrbracket \subseteq \mathsf{Proc}`, [aK, aW, aN, aSi, aT]);
sa('th.Erel', R`E[\kappa]^{W}_{n}\llbracket\Theta \vdash T\rrbracket^{F} \subseteq \mathsf{Expr}`, [aK, aW, aN, aTh, A('T', R`the result type`), aF]);
sa('th.Vrel', R`V^{W}_{j}\llbracket\Theta \vdash T\rrbracket \subseteq \mathsf{Val}`, [aW, A('j', R`the level`), aTh, A('T', R`the type`)]);
sa('th.soup', R`S^{N,W}_{n}\llbracket\Sigma \vdash T\rrbracket \subseteq \mathsf{LFState}`, [aNf, aW, aN, aSi, aT]);
sa('th.qa', R`q_a : \mathsf{Config}`, [A('a', R`a annotated configuration`)]);
sa('th.conn', R`\mathsf{conn}\,\Sigma_1\,\Sigma_C\,C_1\,\Sigma_2\,\Sigma_D\,C_2`, [A(R`\Sigma_1, \Sigma_2`, R`the outer interfaces`), A(R`\Sigma_C, \Sigma_D`, R`the cut and its partners`), A(R`C_1, C_2`, R`the restricted channels of the two sides`)]);
sa('th.par', R`p_1 \parallel_{\Sigma_C} p_2 = (C_1 \cup C_2 \cup \mathsf{chans}\,\Sigma_C, E_1 \uplus E_2)`, [A(R`p_i = (C_i, E_i)`, R`the two components`), A(R`\Sigma_C`, R`the cut`)]);
sa('th.df', R`X \mapsto X_{df}`, [A('X', R`an end environment, a variable context or a type`)]);
sa('th.styof', R`\Delta^{N} : \mathsf{End} \rightharpoonup \mathsf{STy} \times \mathbb{N}`, [aDe]);
sa('th.tpr', R`\mathsf{thread\_progress\_run} : (\mathbb{N} \to \mathsf{Config}) \to (\mathbb{N} \to \mathsf{Event}_{\bot}) \to \mathsf{Prop}`, [...run, A('i, j', R`positions with $i \leq j$`), A('t', R`a thread identifier`)]);
