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
const LFROWS = /^\\htmlData\{k=th\.(lf-[\w-]+|live-[\w-]+|fundamental-typed|conservative|typed-dftyped|adequacy-gen|fair-run-exists)\}/;
const ROWS = (...rs) => R`\begin{array}{l}${rs.map((r, i) => { const sep = i ? R` \\[1.5ex] ` : ''; return LFROWS.test(r) ? (sep ? R`\annraw{${sep}}` : '') + R`\annot{${r}}` : sep + r; }).join('')}\end{array}`;
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
// the classical hypotheses of lock-free adequacy over ordinal indices
const CLASS = R`${h('th.em', R`\mathsf{EM}`)} \land ${h('th.ac', R`\mathsf{FC}`)}`;
// every credit of a context is at most the tickets of its end
const CRN = (D) => h('th.crle', R`\mathsf{cr}(${D}) \leq N`);
const CTY = (D, t) => R`\varnothing ; ${D} \vdash^{\varnothing}_{W,N} ${t} : T\ !\ c`;
const GRD = (t) => h('guard.judg', R`\varnothing \vdash\!\triangleright ${t}`);
const PRIM = R`${h('ty.tfree', R`\mathsf{tfree}`)}\,T`;

const BY = (name, k) => R`\overset{${h(k, R`\textsf{${name}}`)}}{\Longrightarrow}`;
const PSW = h('sj.sw', R`\vDash`);
const PH = h('sj.h', R`\vDash^{h}`);
const LFH = h('sp.lfsemh', R`\Vvdash^{N,h}`);
const LFSN = h('sp.lfsem', R`\Vvdash^{N}`);
const MOD = R`${h('w.sat', R`R \vDash W`)} \land ${h('w.kind', R`\mathsf{strict}`)}\,R`;
const RNK = R`${h('w.kind', R`\mathsf{ranked}`)}\,R`;
const WFW = (p) => R`${h('w.wf', R`\mathsf{world\_wf}`)}\,W \land ${h(p === 'acyc' ? 'w.acyc' : 'w.lfworld', p === 'acyc' ? R`\mathsf{acyc}` : R`\mathsf{wf}`)}\,W`;
const EMR = h('th.em', R`\mathsf{EM}`);
const PTN = h('tp.pjudg', R`\vdash^{N}_W`);
const PCOMPS = (n) => h('th.pcomps', R`\mathsf{comps}_{${n}}(\bar W, p, T)`);
const JOINS = R`(W_1 \sqcup \cdots \sqcup W_n)`;
TH('th-chain', 'How the results fit together', 'static/FundamentalProc.v: fundamental_proc_h, adequacy_h, soundness_h; static/Fundamental.v: live_fundamental_ranked; cost/CostFund.v: fsem_of_cost; soup/LFTyped.v: lf_fundamental_h; soup/LFCompose.v: lf_sems_adequacy; soup/LFAdequacy.v: lf_adequacy', ['df', 'lf'],
  R`\begin{array}{rcl}
\Sigma ${PT} p : T & ${BY('fundamental\\_proc\\_h', 'th.fundamental-proc')} & \Sigma ${PH}_W p : T \\[1ex]
\varnothing ${PH}_W p : T & ${BY('adequacy\\_h', 'th.adequacy-h')} & ${DFP}\,p
\annraw{\\[3ex]}\annot{${EMR} \land ${CTY(R`\Delta`, 't')} \land ${GRD('t')} \land ${h('w.sat', R`R \vDash W`)}}\annraw{&}\annot{${BY('live\\_fundamental\\_ranked', 'th.live-fundamental-ranked')}}\annraw{&}\annot{${DF(R`\Delta`)} ${TLIVE}^{\varnothing}_R t : T_{df}}
\annraw{\\[1ex]}\annot{${CTY(R`\Delta`, 't')} \land ${PRIM} \land ${CRN(R`\Delta`)}}\annraw{&}\annot{${BY('fsem\\_of\\_cost', 'th.fsem-of-cost')}}\annraw{&}\annot{${h('fu.fsem', R`\mathsf{fsem}\,N\,${h('th.styof', R`\Delta^{N}`)}\,t`)}}
\annraw{\\[1ex]}\annot{${EMR} \land \Sigma ${PTN} p : T \land ${h('guard.proc', R`\vdash\!\triangleright p`)}}\annraw{&}\annot{${BY('lf\\_fundamental\\_h', 'th.lf-fundamental')}}\annraw{&}\annot{\Sigma ${LFH}_W p : T}
\annraw{\\[1ex]}\annot{${RNK} \land \varnothing ${LFSN}_R p : T}\annraw{&}\annot{${BY('lf\\_adequacy', 'th.lf-adequacy')}}\annraw{&}\annot{${LOCKF}\,p}
\end{array}`,
  '');
TH('th-adequacy', 'Adequacy', 'relation/Adequacy.v: adequacy, live_adequacy, adequacy_gen; static/FundamentalProc.v: adequacy_h, live_adequacy_h', ['df', 'live'],
  ROWS(
    h('th.adequacy', IM(R`\varnothing ${PSEM}_R p : T`, R`${DFP}\,p`)),
    h('th.adequacy-h', IM(R`\varnothing ${PH}_W p : T`, R`${DFP}\,p`))),
  '');
TH('th-lf-adequacy', 'Lock-free adequacy', 'soup/LFAdequacy.v: lf_adequacy, lf_thread_progress; soup/LFCompose.v: lf_sems_adequacy; soup/SoupTau.v: soup_no_tau_divergence; soup/SoupRun.v: lfsoup_step', ['lf'],
  ROWS(
    h('th.lf-adequacy', IM(R`${RNK} \land \varnothing ${LFSN}_R p : T`, R`${LOCKF}\,p`)),
    h('th.lf-thread-progress', IM(R`${RNK} \land \varnothing ${LFSN}_R p : T`, AL(R`\forall (r, l).\ ${h('proc.erase', R`\mathsf{erase}`)}\,(${h('se.run', R`r\,0`)}) = p \land ${h('prop.maximal', R`\mathsf{maximal}`)}\,(r, l) \land ${h('prop.wfair', R`\mathsf{wfair}`)}\,(r, l)`, R`\quad \Longrightarrow\ ${h('th.tpr', R`\mathsf{thread\_progress\_run}`)}\,(r, l)`))),
    h('th.lf-sems-adequacy', IM(R`${CLASS} \land ${WFW('wf')} \land \varnothing ${LFSN}_W p : T`, R`${LOCKF}\,p`))),
  '');
TH('th-fund-term', 'Fundamental theorems for terms', 'static/Fundamental.v: typed_sem, wfit, fundamental, fundamental_typed, live_fundamental, live_fundamental_typed, live_fundamental_ranked', ['df', 'live', 'lf'],
  ROWS(
    h('th.fundamental', IM(R`\mathsf{world\_wf}\,W \land \varnothing ; \Delta \vdash^{F}_{W} t : T \land ${MOD}`, R`\Delta ${TSEM}^{F}_R t : T`)),
    h('th.fundamental-typed', IM(R`\mathsf{world\_wf}\,W \land \varnothing ; \Delta \vdash^{F}_{W,N} t : T\ !\ \varepsilon \land ${MOD}`, R`${DF(R`\Delta`)} \vDash^{F}_R t : T_{df}`)),
    h('th.live-fundamental', IM(R`\mathsf{world\_wf}\,W \land \varnothing ; \Delta \vdash^{F}_{W} t : T \land ${h('guard.judg', R`\varnothing \vdash\!\triangleright t`)} \land ${MOD}`, R`\Delta ${TLIVE}^{F}_R t : T`)),
    h('th.live-fundamental-typed', IM(AL(R`\mathsf{world\_wf}\,W \land \varnothing ; \Delta \vdash^{F}_{W,N} t : T\ !\ \varepsilon`, R`\land\ \varnothing \vdash\!\triangleright t \land ${MOD}`), R`\Delta_{df} ${L}^{F}_R t : T_{df}`)),
    h('th.live-fundamental-ranked', IM(AL(R`${EMR} \land \mathsf{world\_wf}\,W \land \varnothing ; \Delta \vdash^{F}_{W,N} t : T\ !\ \varepsilon`, R`\land\ N \in \mathbb{N} \land \varnothing \vdash\!\triangleright t \land ${h('w.sat', R`R \vDash W`)}`), R`\Delta_{df} ${L}^{F}_R t : T_{df}`))),
  '');
TH('th-fund-proc', 'Fundamental theorem', 'static/FundamentalProc.v: fundamental_proc_h, live_fundamental_proc_h, fundamental_proc, live_fundamental_proc; soup/LFTyped.v: lf_fundamental_h, lf_fundamental; static/Hiding.v: ptyped_full, fptyped_ptyped', ['df', 'live', 'lf'],
  ROWS(
    h('th.fundamental-proc', IM(R`\Sigma ${PT} p : T`, R`\Sigma ${PH}_W p : T`)),
    h('th.live-fundamental-proc', IM(R`\Sigma ${PT} p : T \land ${h('guard.proc', R`\vdash\!\triangleright p`)}`, R`\Sigma ${h('sj.h', R`\mathrel{|\!\!\vDash}^{h}`)}_W p : T`)),
    h('th.lf-fundamental', IM(R`${EMR} \land \Sigma ${PTN} p : T \land N \in \mathbb{N} \land \vdash\!\triangleright p`, R`\Sigma ${LFH}_W p : T`))),
  '');
TH('th-compose', 'Semantic composition rules', 'compat/PTerm.v: sem_p_term; compat/ConnectP.v: sem_p_connect; static/FundamentalProc.v: sem_p_connect_sw, sem_p_connect_h; soup/LFCompose.v: lf_p_term, lf_p_connect, join_models, lf_connect_adequacy; soup/LFTyped.v: lf_p_connect_h; static/Hiding.v: connect_hidden', ['df', 'live', 'lf'],
  ROWS(
    h('th.sem-p-term', IM(AL(R`${PRIM} \land ${h('th.sth', R`\mathsf{sth}\,\Theta\,\Sigma\,\Theta_B\,C`)}`, R`\land\ t \in ${ER(R`\kappa`, 'R', R`\alpha`, R`\Theta \vdash T`, R`\varnothing`)}`), R`(C, \{t\}) \in ${PR(R`\kappa`, 'R', R`\alpha`, R`\Sigma \vdash T`)}`)),
    h('th.sem-p-connect', IM(AL(R`\mathsf{tfree}\,T \land ${h('th.conn', R`\mathsf{conn}`)}`, R`\land\ p_1 \in ${P0('R', R`\alpha`, R`\Sigma_1 \cup \Sigma_C \vdash T`)}`, R`\land\ p_2 \in ${P0('R', R`\alpha`, R`\Sigma_2 \cup \Sigma_D \vdash \ast`)}`), R`${h('th.par', R`p_1 \parallel_{\Sigma_C} p_2`)} \in ${P0('R', R`\alpha`, R`\Sigma_1 \cup \Sigma_2 \vdash T`)}`)),
    h('th.sem-p-connect-sw', IM(AL(R`\mathsf{tfree}\,T \land \mathsf{conn} \land \Sigma_1 \cup \Sigma_C ${PSW}_{W_1} p_1 : T`, R`\land\ \Sigma_2 \cup \Sigma_D ${PSW}_{W_2} p_2 : \ast`), R`\Sigma_1 \cup \Sigma_2 ${PSW}_{W_1 \sqcup W_2} p_1 \parallel_{\Sigma_C} p_2 : T`)),
    h('th.lf-p-term', IM(AL(R`${EMR} \land N \in \mathbb{N} \land ${h('th.ptermprem', R`\mathsf{pterm}_N(\Sigma, C_0, t, T)`)}`, R`\land\ ${h('guard.judg', R`\varnothing \vdash\!\triangleright t`)}`), R`\Sigma ${LFSN}_W (C_0, \{t\}) : T`)),
    h('th.lf-p-connect', IM(AL(R`\mathsf{conn} \land \Sigma_1 \cup \Sigma_C ${LFSN}_{W_1} p_1 : T`, R`\land\ \Sigma_2 \cup \Sigma_D ${LFSN}_{W_2} p_2 : \ast`), R`\Sigma_1 \cup \Sigma_2 ${LFSN}_{W_1 \sqcup W_2} p_1 \parallel_{\Sigma_C} p_2 : T`))),
  '');
TH('th-bind', 'The bind lemma', 'compat/Bind.v: Erel_bind', ['df', 'live', 'lf'],
  h('th.Erel-bind', IM(AL(
      R`e \in ${E0('R', R`\alpha`, R`\Theta_1 \vdash T`, R`F \cup ${h('ty.heads', R`\mathsf{ap}`)}\,\Theta_2`)}`,
      R`\land\ \forall R' ${h('w.ext', R`\sqsupseteq`)} R,\ \beta \leq \alpha,\ v \in ${h('th.Vrel', R`V^{R'}_{\beta}\llbracket\Theta_v \vdash T\rrbracket`)}.`,
      R`\qquad ${h('se.frame', 'f[v]')} \in ${E0(R`R'`, R`\beta`, R`\Theta_v \cup \Theta_2 \vdash U`, 'F')}`),
    R`${h('se.frame', 'f[e]')} \in ${E0('R', R`\alpha`, R`\Theta_1 \cup \Theta_2 \vdash U`, 'F')}`)),
  '');
TH('th-sound', 'Soundness', 'static/FundamentalProc.v: soundness_h, soundness, live_soundness_h, live_soundness; static/ConnectN.v: connect_n_soundness, connect_n_live_soundness; soup/LFTyped.v: lf_soundness_h, lf_soundness, lf_soundness_run, lf_soundness_padovani; soup/LFConnectN.v: connect_n_lf_soundness; lockfree/FairRun.v: fair_run_exists, lock_free_padovani', ['df', 'live', 'lf'],
  ROWS(
    h('th.soundness', IM(R`\varnothing ${PT} p : T`, R`${DFP}\,p`)),
    h('th.connect-n', IM(R`${PCOMPS(R`\infty`)} \land ${h('w.acyc', R`\mathsf{acyc}`)}\,${JOINS}`, R`${DFP}\,p`)),
    h('th.live-soundness', IM(R`\varnothing ${PT} p : T \land ${h('guard.proc', R`\vdash\!\triangleright p`)}`, R`${DFP}\,p \land ${NOTAU}\,p`)),
    h('th.lf-soundness', IM(R`${CLASS} \land \varnothing ${PTN} p : T \land N \in \mathbb{N} \land \vdash\!\triangleright p`, R`${LOCKF}\,p`)),
    h('th.lf-connect-n', IM(R`${CLASS} \land ${PCOMPS('N')} \land ${h('w.lfworld', R`\mathsf{wf}`)}\,${JOINS} \land \vdash\!\triangleright p`, R`${LOCKF}\,p`)),
    h('th.fair-run-exists', IM(R`\mathsf{EM} \land ${h('th.dc', R`\mathsf{DC}`)}`, R`\exists (r, l).\ ${h('proc.erase', R`\mathsf{erase}`)}\,(r\,0) = p \land ${h('prop.maximal', R`\mathsf{maximal}`)}\,(r, l) \land ${h('prop.wfair', R`\mathsf{wfair}`)}\,(r, l)`)),
    h('th.lf-padovani', IM(AL(R`\mathsf{EM} \land \mathsf{DC} \land ${LOCKF}\,p \land \mathsf{erase}\,q_0 = p`, R`\land\ q_0 \to^{*} q \land ${h('prop.pend', R`\mathsf{pend}(q, t)`)}`), R`\exists q_1\,ev\,q_2.\ q \to^{*} q_1 \xrightarrow{ev} q_2 \land t \in ${h('se.parts', R`\mathsf{parts}(ev)`)}`))),
  '');
TH('th-sound-src', 'Soundness for a single program', 'static/FundamentalProc.v: soundness_source; soup/LFCompose.v: lf_soundness_source', ['df', 'live', 'lf'],
  ROWS(
    h('th.soundness-source', IM(R`${WFW('acyc')} \land ${PRIM} \land \varnothing ; \varnothing \vdash^{\varnothing}_W t : T`, R`\mathsf{deadlock\_free}(\varnothing, \{t\})`)),
    h('th.lf-soundness-source', IM(AL(R`${CLASS} \land ${WFW('wf')} \land N \in \mathbb{N} \land ${PRIM}`, R`\land\ ${CTY(R`\varnothing`, 't')} \land ${GRD('t')}`), R`\mathsf{lock\_free}(\varnothing, \{t\})`))),
  '');
TH('th-conserv', 'Conservativity', 'static/Conservativity.v: conservative, typed_dftyped, dftyped_typed', ['lf'],
  ROWS(
    h('th.conservative', AL(R`(\exists \varepsilon.\ \Gamma;${DF(R`\Delta`)} \vdash^{F}_{W,\infty} e : T_{df}\ !\ \varepsilon)`, R`\quad\iff\ \Gamma ; \Delta_{df} \vdash^{F}_{W} e : T_{df}`)),
    h('th.typed-dftyped', IM(R`\Gamma ; \Delta \vdash^{F}_{W,N} e : T\ !\ \varepsilon`, R`\Gamma ; \Delta_{df} \vdash^{F}_W e : T_{df}`))),
  '');
TH('th-cost', 'Cost', 'cost/CostFund.v: cost_fundamental, fsem_of_cost', ['lf'],
  ROWS(
    h('th.cost-fundamental', IM(R`\Gamma ; \Delta \vdash^{F}_{W,N} e : T\ !\ \varepsilon`, h('cs.csem', R`\Delta \vDash^{N} e : T\ !\ \varepsilon`))),
    h('th.fsem-of-cost', IM(R`${CTY(R`\Delta`, 'e')} \land ${PRIM} \land ${CRN(R`\Delta`)}`, h('fu.fsem', R`\mathsf{fsem}\,N\,${h('th.styof', R`\Delta^{N}`)}\,e`)))),
  'A typed closed thread with all credits at most $N$ has fuel with every counter at its tickets.');

// ---- notes ----
n('th.adequacy', R`Adequacy`, R`If $\varnothing \vDash_R p : T$ at a world $R$ then $p$ is deadlock free.`, R`It turns the semantic judgment into the safety property. A stuck closed process has finitely many waiting threads, and readiness puts each wait below the dual points of the waiting thread in the strict order of $R$. A minimal wait has its partner able to act.`, R`With a cyclic order the premise would hold for two threads that wait on each other.`, R`Two threads closing the two ends of $c$ are deadlock free.`, 'relation/Adequacy.v: adequacy');
n('th.lf-adequacy', R`Lock-free adequacy`, R`If $R$ is ranked and $\varnothing \Vvdash^{N}_R p : T$, then $p$ is lock free.`, R`A pending thread waits for the thread holding the partner of its end. The proof follows this chain of waiting threads and shows it is finite. Its measure ranks a waiting thread by the ordinal $\varrho(\mathsf{pt}\,o)$ of the end $o$ it waits on and then by the counter of the dual end. Ranks never change along a run, so the chain is finite, and a link moves a waiting thread to a partner with a lower counter.`, R`Without ranks an infinite descending chain of points lets a thread wait forever along an infinite chain of holding threads.`, R`Two threads closing the two ends of $c$ are lock free.`, 'soup/LFAdequacy.v: lf_adequacy, wk_ranked; types/Worlds.v: wchain_lt_wf');
n('th.lf-thread-progress', R`Thread progress`, R`Under the premises of lock-free adequacy, each run $(r, l)$ with $\mathsf{erase}(r\,0) = p$, $\mathsf{maximal}\,(r, l)$ and $\mathsf{wfair}\,(r, l)$ satisfies $\mathsf{thread\_progress\_run}\,(r, l)$.`, R`Each thread eventually returns a value or takes part in a session step, so no thread, pending or not, is postponed forever.`, DEF, R`Each lock-free example.`, 'soup/LFAdequacy.v: lf_thread_progress');
n('th.fundamental', R`Fundamental theorem`, R`If $W$ is well formed and $\varnothing ; \Delta \vdash^{F}_{W} t : T$, then $\Delta \vDash^{F}_{R} t : T$ at each strict world $R \vDash W$.`, R`Each typing rule has a semantic counterpart that holds at every index, and the theorem is the induction on the derivation. A creation grows the strict world by the facts of $C$. No excluded middle and no choice enter the proof.`, DEF, R`The main thread of the cycle example satisfies the semantic judgment.`, 'static/Fundamental.v: fundamental, typed_sem, wfit; compat/Redex.v: Erel_new_acyc');
n('th.fundamental-typed', R`Fundamental theorem for annotated typing`, R`For each $N$, the annotated typing judgment implies the semantic judgment at $\Delta_{df}$ and $T_{df}$, at each strict world that models $W$.`, R`Erasing the annotations of an annotated derivation gives a deadlock-free derivation, to which the fundamental theorem applies. No excluded middle and no choice enter the proof.`, DEF, R`The client and server main at $N = \infty$.`, 'static/Fundamental.v: fundamental_typed, sem_later_df');
n('th.live-fundamental', R`Live fundamental theorem`, R`$\varnothing ; \Delta \vdash^{F}_{W} t : T$ and $\varnothing \vdash\!\triangleright t$ imply $\Delta \mathrel{|\!\!\vDash}^{F}_{R} t : T$ at each strict world $R \vDash W$.`, R`The guard lets a box recurse only after an action, so each recursive call is read at a lower index, as the least fixpoint of the relation at $\kappa_L$ requires. No excluded middle and no choice enter the proof.`, R`Without the guard the statement is false, $!(f = \mathsf{force}\,f)$ types and satisfies no live judgment.`, R`The guarded receive loop.`, 'static/Fundamental.v: live_fundamental');
n('th.live-fundamental-typed', R`Live fundamental theorem for annotated typing`, R`The annotated typing judgment with $\varnothing \vdash\!\triangleright t$ implies the live judgment at erased environments and type, at each strict world that models $W$.`, R`It is the live fundamental theorem after erasure. No excluded middle and no choice enter the proof.`, DEF, R`A thread typed by P-Term at finite $N$.`, 'static/Fundamental.v: live_fundamental_typed');
n('th.fundamental-proc', R`Fundamental theorem for processes`, R`$\Sigma \vdash^{\infty}_{W} p : T$ implies $\Sigma \vDash^{h}_{W} p : T$. Some well-formed acyclic world $W\^{\prime}$ hides to $W$ on $\mathsf{I}(\Sigma, T)$, and the process is in the semantic judgment at each strict model of $W\^{\prime}$.`, R`The hidden derivation gives a derivation of the full judgment with whole worlds, whose private constants are renamed apart at each P-Connect. Its world $W\^{\prime}$ is acyclic, and the order $W\^{\prime}$ derives between interface points lies in $W$. On that derivation the theorem is an induction with the semantic P-Term and P-Connect as cases. No excluded middle and no choice enter the proof.`, DEF, R`Two threads closing the two ends of $c$.`, 'static/FundamentalProc.v: fundamental_proc_h, fundamental_proc, sem_ptyped_h; static/Hiding.v: ptyped_full');
n('th.lf-fundamental', R`Lock-free fundamental theorem`, R`Under excluded middle, $\Sigma \vdash^{N}_{W} p : T$ at a finite $N$ with each thread guarded implies $\Sigma \Vvdash^{N,h}_{W} p : T$. Some well-formed well-founded world $W\^{\prime}$ hides to $W$, and the lock-free judgment holds at each ranked model of $W\^{\prime}$.`, R`The fuel of each thread comes from its cost typing at finite $N$, and its relation at $\kappa_L$ from its guarded typing, read at ranked worlds. Excluded middle enters through the creations under $\mathsf{gen\_new}$, which choose the largest of finitely many ranks.`, DEF, R`The cycle example.`, 'soup/LFTyped.v: lf_fundamental_h, lf_fundamental, lf_sems_h; soup/LFCompose.v: typed_live, lf_p_term');
n("th.sem-p-term", "Semantic P-Term", "If $\\mathsf{tfree}\\,T$, $\\mathsf{sth}\\,\\Theta\\,\\Sigma\\,\\Theta_B\\,C$ and $t \\in E[\\kappa]^{R}_{\\alpha}\\llbracket\\Theta \\vdash T\\rrbracket^{\\varnothing}$, then $(C, \\{t\\}) \\in P[\\kappa]^{R}_{\\alpha}\\llbracket\\Sigma \\vdash T\\rrbracket$.", "It is P-Term in the relation. When $t$ spawns $v$, the child receives exactly the ends $\\mathsf{fends}(v)$, which $V$ fixes by $\\mathrm{dom}\\,\\Theta = \\mathsf{fends}(v)$, and the proof composes parent and child as P-Connect does.", DEF, "A single thread with $\\Sigma = \\varnothing$ and $C = \\varnothing$.", "compat/PTerm.v: sem_p_term");
n("th.sth", "$\\mathsf{sth}\\,\\Theta\\,\\Sigma\\,\\Theta_B\\,C$", "$\\Theta = \\Sigma \\cup \\Theta_B$, $\\mathrm{dom}\\,\\Theta_B = \\mathsf{ends}(C)$, $\\mathsf{chans}\\,\\Sigma \\cap C = \\varnothing$, $\\mathsf{pfree}\\,\\Sigma$, and for every $c \\in C$ the two entries of $\\Theta_B$ are dual at dual points.", "These are the environment premises of P-Term, as the semantic proof uses these premises.", DEF, "$\\Sigma = \\varnothing$ and $C = \\varnothing$ for a source program.", "compat/PTerm.v: sth");
n('th.sem-p-connect', R`Semantic P-Connect`, R`If $\mathsf{tfree}\,T$, $\mathsf{conn}$, $p_1 \in P^{R}_{\alpha}\llbracket\Sigma_1 \cup \Sigma_C \vdash T\rrbracket$ and $p_2 \in P^{R}_{\alpha}\llbracket\Sigma_2 \cup \Sigma_D \vdash \ast\rrbracket$, then $p_1 \parallel_{\Sigma_C} p_2 \in P^{R}_{\alpha}\llbracket\Sigma_1 \cup \Sigma_2 \vdash T\rrbracket$, with both components at one world $R$.`, R`It is P-Connect in the relation, for each index and each cost table. Both components are read at one world, so two orders are never reconciled, and a fresh root of either side is fresh for that world.`, DEF, R`Two threads closing $c^{+}$ and $c^{-}$, cut at $c$.`, 'compat/ConnectP.v: sem_p_connect');
n("th.lf-p-connect", "P-Connect in the lock-free judgment", "If $\\mathsf{conn}$, $\\Sigma_1 \\cup \\Sigma_C \\Vvdash^{N}_{W_1} p_1 : T$ and $\\Sigma_2 \\cup \\Sigma_D \\Vvdash^{N}_{W_2} p_2 : \\ast$, then $\\Sigma_1 \\cup \\Sigma_2 \\Vvdash^{N}_{W_1 \\sqcup W_2} p_1 \\parallel_{\\Sigma_C} p_2 : T$. With $\\mathsf{wf}\\,W_1$, $\\mathsf{wf}\\,W_2$ and $\\mathsf{wf}\\,(W_1|_S \\sqcup W_2|_S)$ a closed composite is lock free. With hiding the components sit at whole worlds that hide to their interface worlds, with private constants apart, and the premise reads $\\mathsf{wf}$ of the join of the two interface worlds.", "Each component is read at the ranked worlds of its own static world. A ranked world $R$ of the join satisfies both. The first component starts at some $R_1 \\sqsupseteq R$, the second is read at $R_1$ and starts at some $R_2 \\sqsupseteq R_1$, and the first moves up to $R_2$ because the relation is monotone in the world. A ranked world of the join exists exactly when the join is well-founded, which the condition on the shared roots gives. Its ranks come from the order of the join, never from the ranks of a component.", "Two components at fixed ranked worlds $R_1$ and $R_2$ do not compose, because the two rankings may order shared points that no fact relates in opposite directions.", "The client at $W_{cli}$ and the server at $W_{srv}$, which share the root $\\rho$, compose over the cut $\\{a, b\\}$.", "soup/LFCompose.v: lf_p_connect, lf_soup_connect, join_models, lf_connect_adequacy; examples/LFClientServerSplit.v: cs_split_lock_free; soup/LFTyped.v: lf_p_connect_h");
n('th.lf-p-term', R`P-Term in the lock-free judgment`, R`Under excluded middle, a thread that meets the premises of P-Term at a finite $N$ and is guarded satisfies $\Sigma \Vvdash^{N}_W (C_0, \{t\}) : T$.`, R`It is P-Term read in the lock-free process relation. The relation of the thread at each ranked world comes from the live fundamental theorem at ranked worlds.`, DEF, R`One thread closing its end $c^{+}$.`, 'soup/LFCompose.v: lf_p_term, typed_live; static/Fundamental.v: live_fundamental_ranked');
n("th.Erel-bind", "Bind", "For every cost table, if $e \\in E^{R}_{\\alpha}\\llbracket\\Theta_1 \\vdash T\\rrbracket^{F \\cup \\mathsf{ap}\\,\\Theta_2}$ and $f[v] \\in E^{R'}_{\\beta}\\llbracket\\Theta_v \\cup \\Theta_2 \\vdash U\\rrbracket^{F}$ for all $R' \\sqsupseteq R$, $\\beta \\leq \\alpha$ and $v \\in V^{R'}_{\\beta}\\llbracket\\Theta_v \\vdash T\\rrbracket$, then $f[e] \\in E^{R}_{\\alpha}\\llbracket\\Theta_1 \\cup \\Theta_2 \\vdash U\\rrbracket^{F}$.", "Every rule with a subterm runs the subterm first. The frame holds $\\Theta_2$ while the hole runs, so the hole must not wait above $\\mathsf{ap}\\,\\Theta_2$.", DEF, "$\\mathsf{let}\\ \\ast = \\mathsf{close}\\,c\\ \\mathsf{in}\\ \\mathsf{close}\\,d$ runs $\\mathsf{close}\\,c$ with $\\overline{x_d}$ in its future.", "compat/Bind.v: Erel_bind");
n('th.soundness', R`Soundness`, R`$\varnothing \vdash^{\infty}_{W} p : T$ implies that $p$ is deadlock free.`, R`The fundamental theorem for processes followed by adequacy. No excluded middle and no choice enter the proof.`, DEF, R`The cycle example is deadlock free.`, 'static/FundamentalProc.v: soundness_h, soundness');
n('th.soundness-source', R`Soundness for source terms`, R`For a well-formed acyclic $W$, $\mathsf{tfree}\,T$ and $\varnothing ; \varnothing \vdash^{\varnothing}_{W} t : T$, the process $(\varnothing, \{t\})$ is deadlock free.`, R`The program is P-Term with $\Sigma = \varnothing$ and $C_0 = \varnothing$. No excluded middle and no choice enter the proof.`, DEF, R`The fork-join examples.`, 'static/FundamentalProc.v: soundness_source');
n('th.lf-soundness', R`Lock-free soundness`, R`Under excluded middle and functional choice, $\varnothing \vdash^{N}_{W} p : T$ at a finite $N$ with each thread guarded implies that $p$ is lock free.`, R`The lock-free fundamental theorem, a ranked model of the whole world, and lock-free adequacy. The choice fixes one annotated configuration for all indices.`, DEF, R`The cycle example is lock free.`, 'soup/LFTyped.v: lf_soundness_h, lf_soundness');
n('th.lf-soundness-source', R`Lock-free soundness for source terms`, R`Under excluded middle and functional choice, for a well-formed well-founded $W$, $N \in \mathbb{N}$, $\mathsf{tfree}\,T$, a typing $\varnothing ; \varnothing \vdash^{\varnothing}_{W,N} t : T\ !\ c$ and $\varnothing \vdash\!\triangleright t$, the process $(\varnothing, \{t\})$ is lock free.`, R`The premises are those of P-Term at finite $N$ with $\Sigma = \varnothing$ and $C_0 = \varnothing$, plus the guard.`, DEF, R`Each lock-free example.`, 'soup/LFCompose.v: lf_soundness_source');
n("th.fair-run-exists", "A maximal weakly fair run exists", "Assume excluded middle and dependent choice. For every configuration $q$ there is a run $(r, l)$ with $r\\,0 = q$, $\\mathsf{maximal}\\,(r, l)$ and $\\mathsf{wfair}\\,(r, l)$. Hence every process $p$ has such a run with $\\mathsf{erase}(r\\,0) = p$, and lock-free soundness also gives one for every typed $p$.", "The scheduler goes round robin over thread numbers and at each position takes a step of the targeted thread when that thread is enabled. Dependent choice picks the steps and excluded middle decides enabledness. Lock freedom still quantifies over every such run.", DEF, "Two threads $\\ast$ and $\\ast$ start a maximal weakly fair run.", "lockfree/FairRun.v: fair_run_exists, fair_run_exists_proc; soup/LFTyped.v: lf_soundness_run");
n("th.lf-padovani", "Lock freedom in reachability form", "Assume excluded middle and dependent choice. If $p$ is lock free, $\\mathsf{erase}\\,q_0 = p$, $q_0 \\to^{*} q$ and thread $t$ is pending in $q$, then there are $q_1$ and a step $q_1 \\to q_2$ with event $ev$ such that $q \\to^{*} q_1$ and $t \\in \\mathsf{parts}(ev)$.", "It is the reachability form of lock freedom, stated per thread. A maximal weakly fair run from $q$, prefixed with the steps from $q_0$, is a run from $p$, and lock freedom of that run makes $t$ take part in a later step.", DEF, "Every lock-free example.", "lockfree/FairRun.v: lock_free_padovani; soup/LFTyped.v: lf_soundness_padovani");
n("th.conservative", "Conservativity", "The annotated typing judgment at $N = \\infty$ derives some $T_{df}\\ !\\ \\varepsilon$ iff the deadlock-free judgment derives $T_{df}$, at erased contexts.", "Deadlock-free typing is the annotated typing judgment with credits, costs and tickets ignored, so one set of rules serves both.", DEF, "The client and server main.", "static/Conservativity.v: conservative");
n("th.typed-dftyped", "Erasure to deadlock-free typing", "For every $N$, erasing the annotations of an annotated derivation gives a deadlock-free derivation.", "Hence every lock-free typing is also a deadlock-free typing.", DEF, "The cycle at $N = 2$ erases to its deadlock-free typing.", "static/Conservativity.v: typed_dftyped");
n("th.cost-fundamental", "Cost fundamental theorem", "The annotated typing judgment implies the semantic cost judgment $\\Delta \\vDash^{N} e : T\\ !\\ \\varepsilon$.", "It is the cost half of the annotated typing judgment, proved rule by rule.", DEF, "The forwarder $\\mathsf{fw}$.", "cost/CostFund.v: cost_fundamental");
n("th.fsem-of-cost", "Fuel from cost typing", "If $\\varnothing ; \\Delta \\vdash^{\\varnothing}_{W,N} e : T\\ !\\ c$, $\\mathsf{tfree}\\,T$ and $\\mathsf{cr}(\\Delta) \\leq N$, then $\\mathsf{fsem}\\,N\\,\\Delta^{N}\\,e$.", "P-Term gives every end credit equal to its tickets, so the cost judgment yields the per-thread fuel that lock freedom needs.", "If a closure could mention an end it does not own, the forwarder could receive a closure that owns nothing and would have no fuel after spawning the closure.", "The forwarder $\\mathsf{fw}$.", "cost/CostFund.v: fsem_of_cost");
n('th.crle', R`$\mathsf{cr}(\Delta) \leq N$`, R`Every credit in $\Delta$ is at most the bound $N$, that is $a \leq N$ for every entry $(S@x)^{a}_{m}$ or $(T \multimap U)^{a}$ of $\Delta$.`, R`A thread starts with every counter at its tickets, which are at most $N$, so its credits may guarantee no more than $N$.`, R`A credit above $N$ would allow more postponement than a fresh counter allows.`, R`$\mathsf{cr}(\{o \mapsto (S@x)^{2}_{3}\}) \leq 4$.`, 'cost/CostFund.v: fsem_of_cost');
n('th.Prel', R`The process relation $P$`, R`$P[\kappa]^{R}_{\alpha}\llbracket\Sigma \vdash T\rrbracket$, the processes in the relation at table $\kappa$, world $R$, ordinal index $\alpha$, interface $\Sigma$ and result $T$.`, R`The semantic process judgment asks membership at every index.`, DEF, R`Two threads closing $c^{+}$ and $c^{-}$ lie in $P^{R}_{\alpha}\llbracket\varnothing \vdash \ast\rrbracket$ for each $\alpha$.`, 'relation/Relation.v: Prel');
n('th.Erel', R`The term relation $E$`, R`$E[\kappa]^{R}_{\alpha}\llbracket\Theta \vdash T\rrbracket^{F}$ is the set of terms in the relation at cost table $\kappa$, world $R$ and ordinal index $\alpha$, for ends $\Theta$, result $T$ and future $F$.`, R`The semantic term judgment asks membership at each index and for each grounding of the variables.`, DEF, R`$\mathsf{close}\,c^{+} \in E^{R}_{\alpha}\llbracket\{c^{+} \mapsto \mathsf{Close}@x\} \vdash \ast\rrbracket^{\varnothing}$.`, 'relation/Relation.v: Erel');
n('th.Vrel', R`The value relation $V$`, R`$V^{R}_{\beta}\llbracket\Theta \vdash T\rrbracket$ is the set of values in the relation at world $R$ and ordinal index $\beta$, for ends $\Theta$ and type $T$.`, R`A term in $E$ that is irreducible is a value in $V$.`, DEF, R`$c^{+} \in V^{R}_{\beta}\llbracket\{c^{+} \mapsto \mathsf{Close}@x\} \vdash \mathsf{Close}@x\rrbracket$.`, 'relation/Relation.v: Vrel');
n("th.soup", "The lock-free process relation $S^{N,R}_{\\alpha}$", "$a \\in S^{N,R}_{\\alpha}\\llbracket\\Sigma \\vdash T\\rrbracket$ holds of an annotated configuration $a$ when each thread of $a$ is in the relation at $\\kappa_L$ and has fuel at the ordinal index $\\alpha$. Ownership, points, counters and tickets are those that $a$ records.", "The lock-free judgment chooses $a$ at each index, and the existential property gives one $a$ for every index.", DEF, "The state of two threads closing $c^{+}$ and $c^{-}$.", "soup/Soup.v: Soup, lf_sem; soup/SoupRun.v: lfsoup_step, lfsoup_step_all, lfsoup_run");
n("th.qa", "$q_a$", "The configuration of the annotated configuration $a$.", "An annotated configuration is a configuration together with ownership, counters and tickets.", DEF, "$q_a = (C, M)$.", "soup/State.v: s_q");
n('th.em', R`Excluded middle $\mathsf{EM}$`, R`Each proposition holds or fails, $\forall P.\ P \lor \neg P$, as an explicit hypothesis and no axiom.`, R`It is a hypothesis of the lock-free results only. The existential property of ordinal indices is proved by contradiction, and a creation under $\mathsf{gen\_new}$ takes the largest of finitely many ranks. The deadlock-free, live, hidden and n-ary soundness results take no excluded middle.`, R`Without it a creation at a ranked world cannot pick a rank at or above two given ranks, and the annotated configuration chosen at each index does not give one for all indices.`, R`Transfinite Iris assumes it in its model.`, 'lockfree/FairRun.v: excluded_middle; relation/ExProp.v: exist_prop; relation/Ranks.v: ole_total, two_below_gd');
n('th.ac', R`Functional choice $\mathsf{FC}$`, R`A total relation contains a function, as an explicit hypothesis and no axiom.`, R`The existential property picks one failing index per witness, and the run picks one creation choice per state and position, from which a recursion builds the states of the run.`, R`Without it the states chosen per index do not form one sequence along the run.`, R`One creation choice per position of a run of the lock-free process relation.`, 'lockfree/FairRun.v: functional_choice; relation/ExProp.v: exist_prop; soup/SoupRun.v: lfsoup_run');
n("th.conn", "$\\mathsf{conn}$", "The side conditions of P-Connect, with $\\Sigma_D$ the partners of $\\Sigma_C$ dual up to $\\approx$ at dual points.", "They make the composite a process in which every channel belongs to one side.", DEF, "$\\Sigma_C = \\{c^{+} \\mapsto \\mathsf{Close}@x\\}$ and $\\Sigma_D = \\{c^{-} \\mapsto \\mathsf{Close}@\\overline{x}\\}$.", "compat/Connect.v: conn, cut_dual");
n("th.par", "$p_1 \\parallel_{\\Sigma_C} p_2$", "The composite $(C_1 \\cup C_2 \\cup \\mathsf{chans}\\,\\Sigma_C, E_1 \\uplus E_2)$ of $p_1 = (C_1, E_1)$ and $p_2 = (C_2, E_2)$.", "After composition the two sides communicate on the cut, which no outside process holds.", DEF, "$\\mathsf{close}\\,c^{+} \\parallel \\mathsf{close}\\,c^{-}$ restricts $c$.", "compat/Connect.v: pconn");
n("th.df", "Erasure $X_{df}$", "$\\Delta_{df}$ and $T_{df}$ drop every credit, ticket and cost and keep session types, points and facts.", "Deadlock-free typing and the relations read no annotation.", DEF, "$(S@x)^{3}$ erases to $S@x$.", "types/Types.v: ty_df, static/Contexts.v: tenv_df, lenv_df");
n("th.styof", "$\\Delta^{N}$", "The held ends of $\\Delta$ for fuel, each counter at its tickets. An entry $o \\mapsto (S@x)^{a}_{m}$ of $\\Delta$ becomes $o \\mapsto S^{m}_{m}$.", "Fuel reads protocols, counters and tickets and ignores points and credits. A thread starts with each counter at its tickets.", DEF, "$\\{a \\mapsto (S@x)^{2}_{3}\\}^{N} = \\{a \\mapsto S^{3}_{3}\\}$.", "cost/CostFund.v: fsem_of_cost");

n('th.adequacy-h', R`Adequacy for the hidden judgment`, R`If $\varnothing \vDash^{h}_W p : T$, then $p$ is deadlock free.`, R`The hidden judgment gives an acyclic whole world, which has a strict model, and adequacy applies there.`, DEF, R`The two closes over the empty interface.`, 'static/FundamentalProc.v: adequacy_h, live_adequacy_h; types/Worlds.v: dmodels_exists');
n('th.lf-sems-adequacy', R`Lock-free adequacy at a static world`, R`Under excluded middle and functional choice, if $W$ is well formed and well-founded and $\varnothing \Vvdash^{N}_W p : T$, then $p$ is lock free.`, R`A well-founded static world has a ranked model, at which lock-free adequacy applies.`, DEF, R`The split client and server program, two components at their own static worlds.`, 'soup/LFCompose.v: lf_sems_adequacy, lf_connect_adequacy, join_models');
n('th.live-fundamental-ranked', R`Live fundamental theorem at ranked worlds`, R`Under excluded middle, a derivation at a finite bound $N$ of a guarded term gives the live judgment at erased environments and type, at each world $R \vDash W$ of either kind.`, R`The lock-free process relation reads each thread at a ranked world. At a finite bound the creations meet $\mathsf{gen\_new}$, which finds ranks for the new tree.`, DEF, R`Each thread of a lock-free example.`, 'static/Fundamental.v: live_fundamental_ranked, wfit; compat/Redex.v: Erel_new_any');
n('th.live-fundamental-proc', R`Live fundamental theorem for processes`, R`$\Sigma \vdash^{\infty}_{W} p : T$ with each thread guarded implies the hidden live judgment at $W$.`, R`The live counterpart of the fundamental theorem for processes, read at $\kappa_L$. No excluded middle and no choice enter the proof.`, DEF, R`The guarded receive loop.`, 'static/FundamentalProc.v: live_fundamental_proc_h, live_fundamental_proc');
n('th.sem-p-connect-sw', R`Semantic P-Connect at static worlds`, R`If $\mathsf{tfree}\,T$, $\mathsf{conn}$, $\Sigma_1 \cup \Sigma_C \vDash_{W_1} p_1 : T$ and $\Sigma_2 \cup \Sigma_D \vDash_{W_2} p_2 : \ast$, then the composite is in the semantic judgment at $W_1 \sqcup W_2$.`, R`A strict model of the join models both static worlds, so both components hold there and semantic P-Connect applies at that one world. With hiding the components sit at whole worlds that hide to their interface worlds with private constants apart.`, DEF, R`Two threads closing $c^{+}$ and $c^{-}$.`, 'static/FundamentalProc.v: sem_p_connect_sw, sem_p_connect_h');
n('th.connect-n', R`Soundness of the n-ary connect`, R`If the components $\bar W, p, T$ of the n-ary connect at $N = \infty$ are closed and the join of their hidden worlds is acyclic, then $p$ is deadlock free.`, R`It folds the binary P-Connect through the admissible n-ary rule and applies hidden soundness. No excluded middle and no choice enter the proof.`, DEF, R`The acyclic variant of the ring of three threads.`, 'static/ConnectN.v: connect_n_soundness, connect_n_live_soundness, p_connect_n');
n('th.live-soundness', R`Live soundness`, R`$\varnothing \vdash^{\infty}_{W} p : T$ with each thread guarded implies that $p$ is deadlock free and has no internal divergence.`, R`The live fundamental theorem for processes followed by adequacy at $\kappa_L$. No excluded middle and no choice enter the proof.`, DEF, R`The guarded receive loop.`, 'static/FundamentalProc.v: live_soundness_h, live_soundness');
n('th.lf-connect-n', R`Lock-free soundness of the n-ary connect`, R`Under excluded middle and functional choice, closed components at a finite $N$ whose hidden worlds join to a well-founded world, with each thread guarded, compose to a lock-free process.`, R`The n-ary rule followed by hidden lock-free soundness.`, DEF, R`Three components typed at a finite bound.`, 'soup/LFConnectN.v: connect_n_lf_soundness');
n('th.dc', R`Dependent choice $\mathsf{DC}$`, R`A total relation has an infinite path from each start, as an explicit hypothesis and no axiom.`, R`A maximal weakly fair run picks one step at each position, which dependent choice provides.`, DEF, R`Round robin over threads picks the next step.`, 'lockfree/FairRun.v: dependent_choice');
n('th.pcomps', R`Components $\mathsf{comps}_N(\bar W, p, T)$`, R`Components $p_1, \ldots, p_n$ typed at hidden worlds $\bar W = W_1, \ldots, W_n$ at the bound $N$, each connected over a cut to the composite of the ones before it, with the side conditions of P-Connect and no condition on worlds.`, R`It collects the premises of the n-ary connect. The one condition on worlds is checked once, on the join.`, DEF, R`The three threads of the ring.`, 'static/ConnectN.v: pcomps');
n('th.ptermprem', R`$\mathsf{pterm}_N(\Sigma, C_0, t, T)$`, R`The premises of P-Term at the bound $N$ for the thread $t$ over the interface $\Sigma$ with restricted channels $C_0$ and result $T$, except the condition on the world.`, R`The lock-free judgment reads the thread at each ranked model, so the world needs no condition here.`, DEF, R`One thread closing its end $c^{+}$ with $C_0 = \varnothing$.`, 'soup/LFCompose.v: lf_p_term');

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
    shows: "The second $\\mathsf{new}$ places $b$ at $\\rho\\cdot 0$ and states $C$ at $(\\rho, \\rho\\cdot 0, \\rho\\cdot 1)$, the facts the recursive call at $(\\iota^{+}, \\kappa^{+}, \\zeta)$ needs.",
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
    shows: "Each box uses its own variable before any session action, so $\\varnothing \\vdash\\!\\triangleright t$ fails for every $t$ listed.",
    rocq: 'examples/GuardEx.v: div_not_guarded, pn_fix_not_guarded, cx_not_guarded, spawn_loop_not_guarded',
    accepts: { live: { ok: false, part: 'guard', rocq: 'div_not_guarded, pn_fix_not_guarded, cx_not_guarded, spawn_loop_not_guarded' }, lf: { ok: false, part: 'guard', rocq: 'div_not_guarded, pn_fix_not_guarded, cx_not_guarded, spawn_loop_not_guarded' } } },
  { id: 'ex-guard-pos', title: 'Guard acceptances', modes: ['live', 'lf'],
    code: `loop  = !(f = λx. let ⟨v, x′⟩ = recv x in (force f) x′)
stage = !(f = λin. let ⟨v, in⟩ = recv in in let ∗ = close in in
                  let ⟨a, b⟩ = new in let ∗ = spawn (λ_. (force f) b) in
                  close (send ⟨v, a⟩))                  -- a pipeline stage`,
    shows: "$\\mathsf{recv}$ acts, so the rest of the body is checked under $\\varnothing$ and the box variable is unmarked when it is forced.",
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
            inl w ⇒ let ∗ = w in let ∗ = close c in close d      -- runs
          | inr w ⇒ let ∗ = w in let ∗ = close d in close c      -- never runs
partner = let ∗ = close c̄ in close d̄
-- the process ({c, d}, {thread, partner}), c at x, d at y`,
    rocq: 'examples/SemBranch.v: sbv_thread_E, sbv_deadlock_free, sbv_rejected, Tbad_not_cons',
    accepts: { df: { ok: false, part: 'P-Connect', rocq: 'sbv_rejected, for every world and every bound. E-Open asks cons, so the dead arm needs y ≺ x̄ from its own world, and the joined world has the cycle y ≺ x̄ ≺ y' }, sem: { ok: true, rocq: 'sbv_thread_E and sbv_deadlock_free' } } },
  { id: 'ex-flagpair', title: 'Two threads on one received flag', modes: ['df', 'live', 'lf'],
    code: `A = case z of inl _ ⇒ let ∗ = close a in close b
             | inr _ ⇒ let ∗ = close b in close a
B = case z of inl _ ⇒ let ∗ = close ā in close b̄
             | inr _ ⇒ let ∗ = close b̄ in close ā
-- a at x, b at y, both threads receive the same flag z`,
    rocq: 'examples/FlagPair.v: fp_gate, fp_unrealizable',
    accepts: { df: { ok: false, part: 'P-Connect' }, sem: { ok: true, part: 'the whole process, by its reductions', rocq: 'argued, no Rocq proof. Thread by thread it fails: fp_unrealizable' } } }
);

n("th.tpr", "$\\mathsf{thread\\_progress\\_run}$", "For a run $(r, l)$, $\\mathsf{thread\\_progress\\_run}\\,(r, l)$ holds iff each thread $t$ of each position $i$ later stops or acts. That is, some $j \\geq i$ exists at which $t$ is a value in $r\\,j$ or takes part in the step $l\\,j$ by a session action.", "It states lock freedom per run for each thread, including the threads that are not pending. A thread that is neither stopped nor acting forever would be postponed without end.", DEF, "In a run of two threads closing $c^{+}$ and $c^{-}$, both threads take part in the close step.", "lockfree/ThreadProgress.v: thread_progress_run");

// ---- signatures and arguments ----
const A = (name, meaning) => ({ name, meaning });
const aW = A('W', R`a static world`);
const aR = A('R', R`a world of the relation`);
const aP = A('p', R`a closed process $(C, E)$`);
const aT = A('T', R`the result type of the main thread`);
const aK = A(R`\kappa`, R`a cost table, $\kappa_{DF}$ for deadlock freedom and $\kappa_L$ for liveness`);
const aN = A(R`\alpha`, R`the level, an ordinal`);
const aSi = A(R`\Sigma`, R`the interface of the process`);
const aTh = A(R`\Theta`, R`the ends held by the term`);
const aDe = A(R`\Delta`, R`the linear context of ends and variables`);
const aF = A('F', R`the future`);
const aNf = A('N', R`the bound on the tickets of a channel, a natural number for lock freedom`);
const run = [A(R`(r, l)`, R`a run, $r\,i$ the configuration and $l\,i$ the event at position $i$`)];
sa('th.adequacy', R`\varnothing \vDash_R p : T \Rightarrow \mathsf{deadlock\_free}\,p`, [aR, aP, aT]);
sa('th.adequacy-h', R`\varnothing \vDash^{h}_W p : T \Rightarrow \mathsf{deadlock\_free}\,p`, [aW, aP, aT]);
sa('th.lf-sems-adequacy', R`\mathsf{EM} \land \mathsf{FC} \land \mathsf{world\_wf}\,W \land \mathsf{wf}\,W \land \varnothing \Vvdash^{N}_W p : T \Rightarrow \mathsf{lock\_free}\,p`, [aW, aNf, aP, aT]);
sa('th.live-fundamental-ranked', R`\mathsf{EM} \land \mathsf{world\_wf}\,W \land \varnothing ; \Delta \vdash^{F}_{W,N} t : T\ !\ c \land \varnothing \vdash\!\triangleright t \land R \vDash W \Rightarrow \Delta_{df} \mathrel{|\!\!\vDash}^{F}_{R} t : T_{df}`, [aW, aR, aNf, aDe, aF]);
sa('th.live-fundamental-proc', R`\Sigma \vdash^{\infty}_{W} p : T \land \vdash\!\triangleright p \Rightarrow \Sigma \mathrel{|\!\!\vDash}^{h}_{W} p : T`, [aW, aSi, aP, aT]);
sa('th.sem-p-connect-sw', R`\mathsf{tfree}\,T \land \mathsf{conn} \land \Sigma_1 \cup \Sigma_C \vDash_{W_1} p_1 : T \land \Sigma_2 \cup \Sigma_D \vDash_{W_2} p_2 : \ast \Rightarrow \Sigma_1 \cup \Sigma_2 \vDash_{W_1 \sqcup W_2} p_1 \parallel_{\Sigma_C} p_2 : T`, [A(R`W_1, W_2`, R`the static worlds of the components`)]);
sa('th.connect-n', R`\mathsf{comps}_{\infty}(\bar W, p, T) \land \mathsf{acyc}(W_1 \sqcup \cdots \sqcup W_n) \Rightarrow \mathsf{deadlock\_free}\,p`, [A(R`\bar W`, R`the hidden worlds of the components`), aP, aT]);
sa('th.live-soundness', R`\varnothing \vdash^{\infty}_{W} p : T \land \vdash\!\triangleright p \Rightarrow \mathsf{deadlock\_free}\,p \land \mathsf{no\_tau\_divergence}\,p`, [aW, aP, aT]);
sa('th.lf-connect-n', R`\mathsf{EM} \land \mathsf{FC} \land \mathsf{comps}_{N}(\bar W, p, T) \land \mathsf{wf}(W_1 \sqcup \cdots \sqcup W_n) \land \vdash\!\triangleright p \Rightarrow \mathsf{lock\_free}\,p`, [A(R`\bar W`, R`the hidden worlds of the components`), aNf, aP]);
sa('th.dc', R`\mathsf{DC} := \forall A\,(R : A \to A \to \mathsf{Prop}).\ (\forall x.\ \exists y.\ R\,x\,y) \Rightarrow \forall x_0.\ \exists f.\ f\,0 = x_0 \land \forall n.\ R\,(f\,n)\,(f\,(n{+}1))`, [A('R', R`a total relation`), A('f', R`an infinite path`)]);
sa('th.pcomps', R`\mathsf{comps}_N : \mathsf{SWorld}^{*} \to \mathsf{Proc} \to \mathsf{Ty} \to \mathsf{Prop}`, [A(R`\bar W`, R`the hidden worlds of the components`), aNf]);
sa('th.ptermprem', R`\mathsf{pterm}_N(\Sigma, C_0, t, T) : \mathsf{Prop}`, [aSi, A(R`C_0`, R`the restricted channels`), A('t', R`the thread`), aT]);
sa('th.lf-adequacy', R`\mathsf{ranked}\,R \land \varnothing \Vvdash^{N}_R p : T \Rightarrow \mathsf{lock\_free}\,p`, [aR, aNf, aP, aT]);
sa('th.em', R`\mathsf{EM} := \forall P : \mathsf{Prop}.\ P \lor \neg P`, [A('P', R`a proposition`)]);
sa('th.ac', R`\mathsf{FC} := \forall X\,Y\,(R : X \to Y \to \mathsf{Prop}).\ (\forall x.\ \exists y.\ R\,x\,y) \Rightarrow \exists f.\ \forall x.\ R\,x\,(f\,x)`, [A('R', R`a total relation`), A('f', R`a choice function`), A(R`X, Y`, R`two types`)]);
sa('th.lf-thread-progress', R`\ldots \Rightarrow \forall (r, l).\ \mathsf{erase}(r\,0) = p \land \mathsf{maximal}\,(r, l) \land \mathsf{wfair}\,(r, l) \Rightarrow \mathsf{thread\_progress\_run}\,(r, l)`, [aW, aP, ...run]);
sa('th.fundamental', R`\mathsf{world\_wf}\,W \land \varnothing ; \Delta \vdash^{F}_{W} t : T \land R \vDash W \land \mathsf{strict}\,R \Rightarrow \Delta \vDash^{F}_{R} t : T`, [aW, aR, aDe, aF, A('t', R`the term`), A('T', R`its type`)]);
sa('th.fundamental-typed', R`\mathsf{world\_wf}\,W \land \varnothing ; \Delta \vdash^{F}_{W,N} t : T\ !\ \varepsilon \land R \vDash W \land \mathsf{strict}\,R \Rightarrow \Delta_{df} \vDash^{F}_{R} t : T_{df}`, [aW, aR, aDe, A('N', R`any bound on tickets`)]);
sa('th.live-fundamental', R`\mathsf{world\_wf}\,W \land \varnothing ; \Delta \vdash^{F}_{W} t : T \land \varnothing \vdash\!\triangleright t \land R \vDash W \land \mathsf{strict}\,R \Rightarrow \Delta \mathrel{|\!\!\vDash}^{F}_{R} t : T`, [aW, aR, aDe, aF, A('t', R`the guarded term`)]);
sa('th.live-fundamental-typed', R`\mathsf{strict}\,W \land \ldots \vdash^{F}_{W,N} t : T\ !\ \varepsilon \land \varnothing \vdash\!\triangleright t \Rightarrow \Delta_{df} \mathrel{|\!\!\vDash}^{F}_{W} t : T_{df}`, [aW, A('N', R`any bound on tickets`), A('t', R`the guarded term`)]);
sa('th.fundamental-proc', R`\Sigma \vdash^{\infty}_{W} p : T \Rightarrow \Sigma \vDash^{h}_{W} p : T`, [aW, aSi, aP, aT]);
sa('th.lf-fundamental', R`\mathsf{EM} \land \Sigma \vdash^{N}_{W} p : T \land N \in \mathbb{N} \land \vdash\!\triangleright p \Rightarrow \Sigma \Vvdash^{N,h}_{W} p : T`, [aW, aSi, aNf, aP, aT]);
sa('th.sem-p-term', R`\mathsf{tfree}\,T \land \mathsf{sth}\,\Theta\,\Sigma\,\Theta_B\,C \land t \in E[\kappa]^{R}_{\alpha}\llbracket\Theta \vdash T\rrbracket^{\varnothing} \Rightarrow (C, \{t\}) \in P[\kappa]^{R}_{\alpha}\llbracket\Sigma \vdash T\rrbracket`, [aK, aN, aSi, A(R`\Theta_B`, R`the entries of the restricted ends`), A('C', R`the restricted channels`), A('t', R`the thread`)]);
sa('th.sth', R`\mathsf{sth} : \mathsf{Env} \to \mathsf{Env} \to \mathsf{Env} \to \mathcal{P}(\mathsf{Chan}) \to \mathsf{Prop}`, [aTh, aSi, A(R`\Theta_B`, R`the entries of the ends of restricted channels`), A('C', R`the restricted channels`)]);
sa('th.sem-p-connect', R`\mathsf{tfree}\,T \land \mathsf{conn} \land p_1 \in P^{R}_{\alpha}\llbracket\Sigma_1 \cup \Sigma_C \vdash T\rrbracket \land p_2 \in P^{R}_{\alpha}\llbracket\Sigma_2 \cup \Sigma_D \vdash \ast\rrbracket \Rightarrow p_1 \parallel_{\Sigma_C} p_2 \in P^{W}_{\alpha}\llbracket\Sigma_1 \cup \Sigma_2 \vdash T\rrbracket`, [aN, A('W', R`one ranked world for both components`), A(R`\Sigma_C, \Sigma_D`, R`the cut and its partners`), A(R`p_1, p_2`, R`the two components`)]);
sa('th.lf-p-connect', R`\mathsf{conn} \land \Sigma_1 \cup \Sigma_C \Vvdash^{N}_{W_1} p_1 : T \land \Sigma_2 \cup \Sigma_D \Vvdash^{N}_{W_2} p_2 : \ast \Rightarrow \Sigma_1 \cup \Sigma_2 \Vvdash^{N}_{W_1 \sqcup W_2} p_1 \parallel_{\Sigma_C} p_2 : T`, [A(R`W_1, W_2`, R`the static worlds of the two components`), aNf]);
sa('th.lf-p-term', R`\mathsf{EM} \land N \in \mathbb{N} \land \mathsf{pterm}_N(\Sigma, C_0, t, T) \land \varnothing \vdash\!\triangleright t \Rightarrow \Sigma \Vvdash^{N}_W (C_0, \{t\}) : T`, [aW, aSi, A('t', R`the single thread`), A(R`C_0`, R`its restricted channels`)]);
sa('th.Erel-bind', R`e \in E^{R}_{\alpha}\llbracket\Theta_1 \vdash T\rrbracket^{F \cup \mathsf{ap}\,\Theta_2} \land (\forall R' \sqsupseteq R, \beta \leq \alpha, v.\ \ldots) \Rightarrow f[e] \in E^{R}_{\alpha}\llbracket\Theta_1 \cup \Theta_2 \vdash U\rrbracket^{F}`, [A('f', R`an evaluation frame`), A(R`\Theta_2`, R`the ends the frame holds while $e$ runs`), A(R`W', j, v`, R`every later world, every level $\beta \leq \alpha$ and every value $v$ in $V^{W'}_{\beta}$ that $e$ may return`)]);
sa('th.soundness', R`\varnothing \vdash^{\infty}_{W} p : T \Rightarrow \mathsf{deadlock\_free}\,p`, [aW, aP, aT]);
sa('th.soundness-source', R`\mathsf{world\_wf}\,W \land \mathsf{acyc}\,W \land \mathsf{tfree}\,T \land \varnothing ; \varnothing \vdash^{\varnothing}_{W} t : T \Rightarrow \mathsf{deadlock\_free}(\varnothing, \{t\})`, [aW, A('t', R`a source term, the main thread`), aT]);
sa('th.lf-soundness', R`\mathsf{EM} \land \mathsf{FC} \land \varnothing \vdash^{N}_{W} p : T \land N \in \mathbb{N} \land \vdash\!\triangleright p \Rightarrow \mathsf{lock\_free}\,p`, [aW, aNf, aP, aT]);
const aEM = A(R`\mathsf{EM}`, R`excluded middle, $P \lor \lnot P$ for every proposition $P$, a hypothesis and no axiom`);
const aDC = A(R`\mathsf{DC}`, R`dependent choice, a total relation on a type has an infinite chain from every element, a hypothesis and no axiom`);
sa('th.fair-run-exists', R`\mathsf{EM} \land \mathsf{DC} \Rightarrow \exists (r, l).\ r\,0 = q \land \mathsf{maximal}\,(r, l) \land \mathsf{wfair}\,(r, l)`, [aEM, aDC, A('q', R`a configuration, a lifting of $p$ for the process form`), ...run]);
sa('th.lf-padovani', R`\mathsf{EM} \land \mathsf{DC} \land \mathsf{lock\_free}\,p \land \mathsf{erase}\,q_0 = p \land q_0 \to^{*} q \land \mathsf{pend}(q, t) \Rightarrow \exists q_1\,ev\,q_2.\ q \to^{*} q_1 \xrightarrow{ev} q_2 \land t \in \mathsf{parts}(ev)`, [aEM, aDC, aP, A('t', R`a thread pending in the reachable configuration $q$`)]);
sa('th.lf-soundness-source', R`\mathsf{EM} \land \mathsf{FC} \land \mathsf{world\_wf}\,W \land \mathsf{wf}\,W \land N \in \mathbb{N} \land \ldots \Rightarrow \mathsf{lock\_free}(\varnothing, \{t\})`, [aW, aNf, A('t', R`the source term`)]);
sa('th.conservative', R`(\exists \varepsilon.\ \ldots \vdash^{F}_{W,\infty} e : T_{df}\ !\ \varepsilon) \iff \ldots \vdash^{F}_{W} e : T_{df}`, [A(R`\varepsilon`, R`some cost`), A('e', R`the term`)]);
sa('th.typed-dftyped', R`\Gamma ; \Delta \vdash^{F}_{W,N} e : T\ !\ \varepsilon \Rightarrow \Gamma ; \Delta_{df} \vdash^{F}_{W} e : T_{df}`, [A('N', R`any bound on tickets`)]);
sa('th.cost-fundamental', R`\Gamma ; \Delta \vdash^{F}_{W,N} e : T\ !\ \varepsilon \Rightarrow \Delta \vDash^{N} e : T\ !\ \varepsilon`, [A('N', R`the bound on the tickets of a channel`), A('e', R`the term`)]);
sa('th.fsem-of-cost', R`\varnothing ; \Delta \vdash^{\varnothing}_{W,N} e : T\ !\ c \land \mathsf{tfree}\,T \land \mathsf{cr}(\Delta) \leq N \Rightarrow \mathsf{fsem}\,N\,\Delta^{N}\,e`, [A(R`\Delta`, R`the ends of the thread with their credits and tickets`)]);
sa('th.crle', R`\mathsf{cr} : \mathsf{TEnv} \to \mathbb{N} \cup \{\infty\}`, [A(R`\Delta`, R`a context`), A('N', R`the bound on the tickets of a channel`)]);
sa('th.Prel', R`P[\kappa]^{R}_{\alpha}\llbracket\Sigma \vdash T\rrbracket \subseteq \mathsf{Proc}`, [aK, aR, aN, aSi, aT]);
sa('th.Erel', R`E[\kappa]^{R}_{\alpha}\llbracket\Theta \vdash T\rrbracket^{F} \subseteq \mathsf{Expr}`, [aK, aR, aN, aTh, A('T', R`the result type`), aF]);
sa('th.Vrel', R`V^{R}_{\beta}\llbracket\Theta \vdash T\rrbracket \subseteq \mathsf{Val}`, [aR, A(R`\beta`, R`the ordinal index`), aTh, A('T', R`the type`)]);
sa('th.soup', R`S^{N,R}_{\alpha}\llbracket\Sigma \vdash T\rrbracket \subseteq \mathsf{LFState}`, [aNf, A('R', R`a ranked world, which the world of each configuration extends`), A(R`\alpha`, R`the ordinal index`), aSi, aT]);
sa('th.qa', R`q_a : \mathsf{Config}`, [A('a', R`an annotated configuration`)]);
sa('th.conn', R`\mathsf{conn}\,\Sigma_1\,\Sigma_C\,C_1\,\Sigma_2\,\Sigma_D\,C_2`, [A(R`\Sigma_1, \Sigma_2`, R`the outer interfaces`), A(R`\Sigma_C, \Sigma_D`, R`the cut and its partners`), A(R`C_1, C_2`, R`the restricted channels of the two sides`)]);
sa('th.par', R`p_1 \parallel_{\Sigma_C} p_2 = (C_1 \cup C_2 \cup \mathsf{chans}\,\Sigma_C, E_1 \uplus E_2)`, [A(R`p_i = (C_i, E_i)`, R`the two components`), A(R`\Sigma_C`, R`the cut`)]);
sa('th.df', R`X \mapsto X_{df}`, [A('X', R`an end environment, a variable context or a type`)]);
sa('th.styof', R`\Delta^{N} : \mathsf{End} \rightharpoonup \mathsf{STy} \times \mathbb{N} \times \mathbb{N}`, [aDe]);
sa('th.tpr', R`\mathsf{thread\_progress\_run} : (\mathbb{N} \to \mathsf{Config}) \to (\mathbb{N} \to \mathsf{Event}_{\bot}) \to \mathsf{Prop}`, [...run, A('i, j', R`positions with $i \leq j$`), A('t', R`a thread identifier`)]);
