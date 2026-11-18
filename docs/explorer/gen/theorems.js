const { R, h, n, section, block, examples, DEF } = require('./core');

const s = section('theorems', 'Theorems',
  'The main results listed in CheckAll.v, each closed under the global context. Adequacy turns the semantic judgments into safety properties, the fundamental theorems turn typing into the semantic judgments, and soundness composes the two.');

const TH = (id, title, rocq, modes, tex, caption) => block(s, { id, title, rocq, modes, tex, caption });
const imp = R`\;\Longrightarrow\;`;
const L = R`\mathrel{|\!\!\vDash}`;

TH('th-adequacy', 'Adequacy', 'relation/Adequacy.v: adequacy, live_adequacy, adequacy_gen', ['df', 'live'],
  R`\begin{array}{l}
${h('th.adequacy', R`${h('w.strict', R`\mathsf{strict}\,W`)} \land \varnothing \vDash_W p : T ${imp} \mathsf{deadlock\_free}\,p`)} \\
${h('th.live-adequacy', R`\mathsf{strict}\,W \land \varnothing ${L}_W p : T ${imp} \mathsf{deadlock\_free}\,p \land \mathsf{no\_tau\_divergence}\,p`)} \\
${h('th.adequacy-gen', R`\forall \kappa.\ \mathsf{strict}\,W \land \forall n.\ p \in P[\kappa]^W_n\llbracket\varnothing \vdash T\rrbracket ${imp} \mathsf{deadlock\_free}\,p`)}
\end{array}`,
  'A closed process in P at every level is deadlock free, for every cost table. In κ_L it also has no τ-divergence.');
TH('th-lf-adequacy', 'Lock-free adequacy', 'soup/LFAdequacy.v: lf_adequacy, lf_thread_progress; soup/SoupTau.v: soup_no_tau_divergence; soup/SoupRun.v: lfsoup_step', ['lf'],
  R`\begin{array}{l}
${h('th.lf-adequacy', R`${h('w.lfworld', R`\mathsf{lfworld}\,W`)} \land \varnothing \Vvdash_W p : T ${imp} \mathsf{lock\_free}\,p`)} \\
${h('th.lf-thread-progress', R`\mathsf{lfworld}\,W \land \varnothing \Vvdash_W p : T ${imp} \text{every weakly fair maximal run makes every thread progress}`)} \\
${h('th.soup-no-tau', R`(\forall n.\ a \in S^{N,W}_n\llbracket\varnothing \vdash T\rrbracket) ${imp} \mathsf{no\_tau\_divergence}(\mathsf{erase}\,q_a)`)} \\
${h('th.lfsoup-step', R`a \in S^{N,W}_{n+1}\llbracket\varnothing \vdash T\rrbracket \land q_a \xrightarrow{ev} q' ${imp} \mathsf{lf\_next}\,N\,a\,ev\,q' \in S^{N,W}_n\llbracket\varnothing \vdash T\rrbracket`)}
\end{array}`,
  'The soup alone gives lock freedom in a well-founded strict world.');
TH('th-fund-term', 'Fundamental theorems for terms', 'static/Fundamental.v: fundamental, fundamental_typed; static/LiveFundamental.v: live_fundamental, live_fundamental_typed', ['df', 'live', 'lf'],
  R`\begin{array}{l}
${h('th.fundamental', R`\mathsf{strict}\,W \land \Theta ; \varnothing ; \Delta \vdash^{F}_{W} t : T ${imp} \Theta ; \Delta \vDash^{F}_W t : T`)} \\
${h('th.fundamental-typed', R`\mathsf{strict}\,W \land \Theta ; \varnothing ; \Delta \vdash^{F}_{W,N} t : T^{a} \triangleright c ; \vartheta ${imp} \Theta_{df} ; \Delta_{df} \vDash^{F}_W t : T_{df}`)} \\
${h('th.live-fundamental', R`\mathsf{strict}\,W \land \Theta ; \varnothing ; \Delta \vdash^{F}_{W} t : T \land ${h('guard.judg', R`\varnothing \vdash\!\triangleright t`)} ${imp} \Theta ; \Delta ${L}^{F}_W t : T`)} \\
${h('th.live-fundamental-typed', R`\mathsf{strict}\,W \land \Theta ; \varnothing ; \Delta \vdash^{F}_{W,N} t : T^{a} \triangleright c ; \vartheta \land \varnothing \vdash\!\triangleright t ${imp} \Theta_{df} ; \Delta_{df} ${L}^{F}_W t : T_{df}`)}
\end{array}`,
  'Typing implies the semantic term judgment. The live versions add the guard.');
TH('th-fund-proc', 'Fundamental theorems for processes', 'static/FundamentalProc.v: fundamental_proc, live_fundamental_proc; soup/LFTyped.v: lf_fundamental', ['df', 'live', 'lf'],
  R`\begin{array}{l}
${h('th.fundamental-proc', R`\mathsf{strict}\,W \land \Sigma \vdash_W p : T ${imp} \Sigma \vDash_W p : T`)} \\
${h('th.live-fundamental-proc', R`\mathsf{strict}\,W \land \Sigma \vdash_W p : T \land ${h('guard.proc', R`\vdash\!\triangleright p`)} ${imp} \Sigma ${L}_W p : T`)} \\
${h('th.lf-fundamental', R`\mathsf{strict}\,W \land \Sigma \Vdash^{N}_W p : T ${imp} \Sigma \Vvdash_W p : T`)}
\end{array}`,
  'One induction on process typing per judgment, using the semantic P-Term and P-Connect.');
TH('th-compose', 'Semantic composition rules', 'compat/PTerm.v: sem_p_term; compat/ConnectP.v: sem_p_connect; soup/LFCompose.v: lf_p_term, lf_p_connect', ['df', 'live', 'lf'],
  R`\begin{array}{l}
${h('th.sem-p-term', R`\mathsf{prim}\,T \land ${h('th.sth', R`\mathsf{sth}\,\Theta\,\Sigma\,\Theta_B\,C`)} \land t \in E[\kappa]^W_n\llbracket\Theta \vdash T\rrbracket^{\varnothing} ${imp} (C, \{t\}) \in P[\kappa]^W_n\llbracket\Sigma \vdash T\rrbracket`)} \\
${h('th.sem-p-connect', R`\mathsf{prim}\,T \land p_1 \in P_n^{W_1}\llbracket\Sigma_1 \cup \Sigma_C \vdash T\rrbracket \land p_2 \in P_n^{W_2}\llbracket\Sigma_2 \cup \Sigma_D \vdash \ast\rrbracket \land \mathsf{conn} ${imp} p_1 \parallel_{\Sigma_C} p_2 \in P_n^{W_1 \sqcup W_2}\llbracket\Sigma_1 \cup \Sigma_2 \vdash T\rrbracket`)} \\
${h('th.lf-p-term', R`\text{premises of lf\_term} \land \mathsf{strict}\,W ${imp} \Sigma \Vvdash_W (C_0, \{t\}) : T`)}
\end{array}`,
  'P-Term and P-Connect hold semantically at every level and every cost table. The LF versions are lemmas about the soup.');
TH('th-bind', 'The bind lemma', 'compat/Bind.v: Erel_bind', ['df', 'live', 'lf'],
  h('th.Erel-bind', R`e \in E^W_n\llbracket\Theta_1 \vdash T\rrbracket^{F \cup \mathsf{heads}\,\Theta_2} \land \big(\forall W' \sqsupseteq W, j \leq n, v \in V^{W'}_j\llbracket\Theta_v \vdash T\rrbracket.\ f[v] \in E^{W'}_j\llbracket\Theta_v \cup \Theta_2 \vdash U\rrbracket^{F}\big) ${imp} f[e] \in E^W_n\llbracket\Theta_1 \cup \Theta_2 \vdash U\rrbracket^{F}`),
  'One bind lemma for every cost table. The hole\'s future holds the heads of the frame\'s environment.');
TH('th-sound', 'Soundness', 'static/FundamentalProc.v: soundness, live_soundness, soundness_source; soup/LFTyped.v: lf_soundness; soup/LFCompose.v: lf_soundness_source', ['df', 'live', 'lf'],
  R`\begin{array}{l}
${h('th.soundness', R`\mathsf{strict}\,W \land \varnothing \vdash_W p : T ${imp} \mathsf{deadlock\_free}\,p`)} \\
${h('th.live-soundness', R`\mathsf{strict}\,W \land \varnothing \vdash_W p : T \land \vdash\!\triangleright p ${imp} \mathsf{deadlock\_free}\,p \land \mathsf{no\_tau\_divergence}\,p`)} \\
${h('th.soundness-source', R`\mathsf{strict}\,W \land \mathsf{prim}\,T \land \varnothing ; \varnothing ; \varnothing \vdash^{\varnothing}_W t : T ${imp} \mathsf{deadlock\_free}(\varnothing, \{t\})`)} \\
${h('th.lf-soundness', R`\mathsf{lfworld}\,W \land \varnothing \Vdash^{N}_W p : T ${imp} \mathsf{lock\_free}\,p`)} \\
${h('th.lf-soundness-source', R`\mathsf{lfworld}\,W \land \varnothing \vdash\!\triangleright t \land \mathsf{prim}\,T \land \varnothing;\varnothing;\varnothing \vdash^{\varnothing}_{W,N} t : T^{a} \triangleright c ; \vartheta \land \mathsf{meets}\,\vartheta\,0\,tk ${imp} \mathsf{lock\_free}(\varnothing, \{t\})`)}
\end{array}`,
  'Typing implies the safety property. Source programs need no creation constraint.');
TH('th-conserv', 'Conservativity and live ⊆ DF', 'static/Conservativity.v: conservative, typed_dftyped, dftyped_typed; compat/LiveDF.v: live_sub_df', ['df', 'live', 'lf'],
  R`\begin{array}{l}
${h('th.conservative', R`(\exists a\,c\,\vartheta.\ \Theta_{df};\Gamma;\Delta_{df} \vdash^{F}_{W,\infty} e : T_{df}^{a} \triangleright c ; \vartheta) \iff \Theta_{df};\Gamma;\Delta_{df} \vdash^{F}_{W} e : T_{df}`)} \\
${h('th.typed-dftyped', R`\Theta;\Gamma;\Delta \vdash^{F}_{W,N} e : T^{a} \triangleright c ; \vartheta ${imp} \Theta_{df};\Gamma;\Delta_{df} \vdash^{F}_W e : T_{df}`)} \\
${h('th.live-sub-df', R`${h('th.tshape', R`\mathsf{tshape}\,T`)} \land \varnothing ${L}_W p : T ${imp} \varnothing \vDash_W p : T`)}
\end{array}`,
  'DF typing is the merged judgment at N = ∞, and erasing annotations of any derivation gives a DF derivation.');
TH('th-cost', 'Cost', 'cost/CostFund.v: cost_fundamental, fsem_of_cost', ['lf'],
  R`\begin{array}{l}
${h('th.cost-fundamental', R`\Theta;\Gamma;\Delta \vdash^{F}_{W,N} e : T^{a} \triangleright c ; \vartheta ${imp} ${h('cs.csem', R`\Theta;\Delta \vDash^{N} e : T^{a} \triangleright c ; \vartheta`)}`)} \\
${h('th.fsem-of-cost', R`\Theta;\varnothing;\varnothing \vdash^{\varnothing}_{W,N} e : T^{a} \triangleright c ; \vartheta \land \mathsf{prim}\,T \land \text{credits of } \Theta \leq N \land \mathsf{meets}\,\vartheta\,0\,tk ${imp} ${h('fu.fsem', R`\mathsf{fsem}\,N\,(\mathsf{sty} \langle\$\rangle \Theta)\,e`)}`)}
\end{array}`,
  'The cost half of the merged judgment. A typed closed thread has fuel with every end at N.');

// ---- notes ----
n('th.adequacy', 'adequacy', 'A closed process in the DF process relation at every level, in a strict world, is deadlock free.', 'A.3. strict W was added after S4.15, because P at a non-strict world is vacuous.', 'Without strict W the premise holds vacuously at a cyclic world.', 'soundness uses it.', 'relation/Adequacy.v: adequacy');
n('th.live-adequacy', 'live_adequacy', 'The same at κ_L, plus no τ-divergence.', 'Administrative steps cost nothing in κ_L and are read inside the least fixpoint, so no reachable state admits an infinite sequence of them (comment in Adequacy.v).', DEF, 'live_soundness uses it.', 'relation/Adequacy.v: live_adequacy');
n('th.adequacy-gen', 'adequacy_gen', 'Adequacy for every cost table.', 'A τ step lowers the level by at most cmax κ, so the level reaches every state of a run.', DEF, 'Instantiated at κ_DF and κ_L.', 'relation/Adequacy.v: adequacy_gen');
n('th.lf-adequacy', 'lf_adequacy', 'A closed soup in a lock-free world is lock free.', 'Proposal §2.13. The proof instantiates lf_run_criterion with the rank of a pending thread, the point of the end it offers, and the measure (tickets left, counter).', DEF, 'cl_lock_free.', 'soup/LFAdequacy.v: lf_adequacy');
n('th.lf-thread-progress', 'lf_thread_progress', 'Every weakly fair maximal run makes every thread progress.', 'A.3.', DEF, 'Each LF example.', 'soup/LFAdequacy.v: lf_thread_progress');
n('th.soup-no-tau', 'soup_no_tau_divergence', 'A closed soup at every index has no τ-divergence.', 'Q12. It gives what the live process conjunct of LF was kept for, so ⊪ is the soup alone.', DEF, 'The infinite spawn chain is rejected per thread.', 'soup/SoupTau.v: soup_no_tau_divergence');
n('th.lfsoup-step', 'lfsoup_step', 'A closed step moves the soup from index n + 1 to n along lf_next.', 'Progress.md, S8 one clock. Each thread pays its own side of a synchronization.', DEF, 'lfsoup_run iterates it.', 'soup/SoupRun.v: lfsoup_step');
n('th.fundamental', 'fundamental', 'DF typing under empty Γ in a strict world implies ⊨.', 'A.3.', DEF, 'spawn_gap refuted it before the O-Spawn decisions.', 'static/Fundamental.v: fundamental');
n('th.fundamental-typed', 'fundamental_typed', 'The merged judgment at any N implies ⊨ at the erased environments and type.', 'Progress.md, S5. The merged judgment enters by typed_dftyped.', DEF, 'cs_typed at N = ∞.', 'static/Fundamental.v: fundamental_typed');
n('th.live-fundamental', 'live_fundamental', 'DF typing with the guard implies ⊫.', 'A.3 and decision on the guard (2026-11-18).', 'Without the guard, live_fundamental_false (#14).', 'loop_guarded.', 'static/LiveFundamental.v: live_fundamental');
n('th.live-fundamental-typed', 'live_fundamental_typed', 'The merged judgment with the guard implies ⊫ at erased types.', 'lf_p_term uses it at Some N.', DEF, 'P-Term of ⊩.', 'static/LiveFundamental.v: live_fundamental_typed');
n('th.fundamental-proc', 'fundamental_proc', 'Process typing implies ⊨_W.', 'One induction on ptyped using sem_p_term and sem_p_connect.', DEF, 'soundness.', 'static/FundamentalProc.v: fundamental_proc');
n('th.live-fundamental-proc', 'live_fundamental_proc', 'Process typing with ⊢▷ p implies ⊫_W.', 'A.3.', DEF, 'live_soundness.', 'static/FundamentalProc.v: live_fundamental_proc');
n('th.lf-fundamental', 'lf_fundamental', 'Lock-free process typing implies ⊪_W.', 'The proof reads fsem^N off the typing through fsem_of_cost and the live relation through live_fundamental_typed (comment in LFTyped.v).', DEF, 'lf_soundness.', 'soup/LFTyped.v: lf_fundamental');
n('th.sem-p-term', 'sem_p_term', 'A thread in E at the empty future with a well-formed split of its ends is a process in P.', 'Progress.md, S4.33. A spawn splits the environment by O-Spawn and P-Connect composes parent and child.', DEF, 'P-Term of ⊢ and ⊩.', 'compat/PTerm.v: sem_p_term');
n('th.sth', 'sth', 'The environment of a single thread. Θ = Σ ∪ Θ_B, Θ_B covers C, Σ apart from C, pfree Σ, and dpairs C Θ_B.', 'pfree is the decision of 2026-11-18.', DEF, 'Σ = ∅, C = ∅ for a source program.', 'compat/PTerm.v: sth');
n('th.sem-p-connect', 'sem_p_connect', 'Two components in P in their worlds compose in the join, given conn.', 'Two-world composition (W7).', DEF, 'LFClose composes two closes.', 'compat/ConnectP.v: sem_p_connect');
n('th.lf-p-term', 'lf_p_term', 'The premises of lf_term in a strict world give ⊪ for one thread.', 'A.4 names.', DEF, 'cl_term.', 'soup/LFCompose.v: lf_p_term');
n('th.Erel-bind', 'Erel_bind', 'E is closed under evaluation frames, for every κ, with the frame\'s heads in the hole\'s future.', 'Proposal §2.8 and progress.md S4 bind. No strictness and no bound on the frame\'s heads. The ends a hole acts on are its own (Erel_sends).', DEF, 'Every compatibility lemma with a subterm.', 'compat/Bind.v: Erel_bind');
n('th.soundness', 'soundness', 'A closed typed process in a strict world is deadlock free.', 'fundamental_proc then adequacy.', DEF, 'Through typed_dftyped and soundness_source, cy_typed gives Cycle deadlock free.', 'static/FundamentalProc.v: soundness');
n('th.live-soundness', 'live_soundness', 'With the guard, also no τ-divergence.', 'live_fundamental_proc then live_adequacy.', DEF, 'loop and stage are guarded.', 'static/FundamentalProc.v: live_soundness');
n('th.soundness-source', 'soundness_source', 'A closed source term of prim type typed in a strict world is deadlock free. No creation constraint.', 'A.5. Fresh roots replace the created hypotheses of inventory row S6 (proposal §1.3), so one theorem without a constraint remains.', DEF, 'Every DF example.', 'static/FundamentalProc.v: soundness_source');
n('th.lf-soundness', 'lf_soundness', 'A closed process typed by ⊩ in a lock-free world is lock free.', 'lf_fundamental then lf_adequacy.', DEF, 'cy_lock_free and the other LF examples.', 'soup/LFTyped.v: lf_soundness');
n('th.lf-soundness-source', 'lf_soundness_source', 'A guarded closed source term typed at Some N with a ticket count meeting ϑ is lock free.', 'A.3.', DEF, 'The six LF examples.', 'soup/LFCompose.v: lf_soundness_source');
n('th.conservative', 'conservative', 'The merged judgment at N = ∞ and the DF judgment type the same erased programs.', 'Q11. DF typing is the instance N = ∞.', DEF, 'cs_typed from cs_dftyped.', 'static/Conservativity.v: conservative');
n('th.typed-dftyped', 'typed_dftyped', 'Erasing annotations of a merged derivation at any N gives a DF derivation.', 'Proposal §2.17.', DEF, 'LF typings imply DF typings.', 'static/Conservativity.v: typed_dftyped');
n('th.live-sub-df', 'live_sub_df', 'At first-order result types, ⊫ implies ⊨.', 'Quirk G2. live ⊆ DF stays at box-free results (author, 2026-11-18).', DEF, 'Every example with result ∗.', 'compat/LiveDF.v: live_sub_df');
n('th.tshape', 'tshape', 'Built from ∗, S@x, ⊗, ⊕ and ∃. No arrow and no box.', 'For such T, V reads no E, so V is the same for both tables at every level (Vrel_shape).', DEF, 'tshape ∗.', 'compat/LiveDF.v: tshape');
n('th.cost-fundamental', 'cost_fundamental', 'The merged judgment implies the semantic cost judgment.', 'S7. E-Abs, E-Box and E-SpawnLam take the facts of their term from typed_tfacts.', DEF, 'fw_fsem.', 'cost/CostFund.v: cost_fundamental');
n('th.fsem-of-cost', 'fsem_of_cost', 'A closed typed thread with credits at most N and a ticket count meeting ϑ at reserve 0 has fsem with the session types of its ends.', 'Progress.md, S7. P-Term gives credit N to every end.', 'Before Q15, fw o was typed and had no fsem (fw_counterexample).', 'fw_fsem.', 'cost/CostFund.v: fsem_of_cost');

// ---- examples ----
examples.push(
  { id: 'ex-cs', title: 'Client and server cycle (ClientServer)', modes: ['df', 'live', 'lf'],
    code: `main = let (a, a′) = new_0 in
       let (a, ⟨b, b′⟩) = new_κ a in
       let () = spawn (λu. let () = u in (force srv) ⟨a′, b′⟩) in
       (force cli) ⟨a, b⟩
cli  = !(f = λp. let (a, b) = p in let a = send ⟨∗, a⟩ in
                let (u, b) = recv b in let () = u in (force f) ⟨a, b⟩)
srv  = !(g = λp. let (a, b) = p in let (u, a) = recv a in let () = u in
                let b = send ⟨∗, b⟩ in (force g) ⟨a, b⟩)
-- both boxes : □∀ι κ ζ. C. ∗ ⊸ (S1@ι ⊗ S2@κ ⊸^ζ ∗)
-- C = {ι+k ≺ (κ+k)‾, κ+k ≺ (ι+k+1)‾, ι+k ≺ ζ, κ+k ≺ ζ | k}`,
    shows: 'A cycle created by main types under family laws (Q2 (d)). a sits at a fresh root ρ, b at ρ·0 by anchoring, and Λ₀ states C at (ρ, ρ·0, ρ·1). The self call instantiates C at (ι⁺, κ⁺, ζ). Under ⊩ it types at N = 3 with credits 1 and 2 on the loop arguments, and the world is a lock-free world by a measure.',
    rocq: 'examples/ClientServer.v: cs_typed; examples/LFClientServer.v: cs_lftyped, cs_lock_free' },
  { id: 'ex-cycle', title: 'Cycle', modes: ['df', 'live', 'lf'],
    code: `cycle = let (c, c′) = new_0 in
        let (c, ⟨d, d′⟩) = new_0 c in
        let () = spawn (λu. let () = u in let () = close c′ in close d′) in
        let () = close c in close d
-- Λ₀(r) = {r ≺ (r·0)‾, r‾ ≺ r·0}`,
    shows: 'Main closes c while it holds d, so it needs ρ ≺ (ρ·0)‾. The thunk closes c′ while it holds d′, so it needs ρ̄ ≺ ρ·0. The laws of family 0 state exactly these facts. Under ⊩ it types at N = 2 with transformer offset 0.',
    rocq: 'examples/Cycle.v: cy_typed; examples/LFCycle.v: cy_lftyped, cy_lock_free' },
  { id: 'ex-between', title: 'A channel between two box arguments (FreshBetween)', modes: ['df', 'live', 'lf'],
    code: `between : □(∀ι κ. C. ∗ ⊸ Close@ι ⊗ Close@κ ⊸^κ ∗)
between = !(f = λp. let (c, e) = p in
                    let (c, ⟨d, d′⟩) = new_0 c in
                    let () = spawn (λu. let () = u in close d′) in
                    let () = close c in let () = close d in close e)
-- C = {ι ≺ κ, ι ≺ κ‾, ι ≺ δ‾, δ ≺ κ, δ ≺ κ‾},  δ = ι·0
main: c by new_0 at ρ, e by new_1 c at ρ·1, force between at (ρ, ρ·1)`,
    shows: 'The box anchors the new channel at the end it receives at ι, so no point between two box points is needed (#52, fb_between_underivable). Lock free at N = 2.',
    rocq: 'examples/FreshBetween.v: fb_typed; examples/LFFreshBetween.v: fb_lftyped, fb_lock_free' },
  { id: 'ex-many', title: 'A channel that acts several times (FreshMany)', modes: ['df', 'live', 'lf'],
    code: `many = !(f = λp. let (c, e) = p in
                 let (c, ⟨d, d′⟩) = new_0 c in
                 let () = spawn (λu. let () = u in
                                     let (v, d′) = recv d′ in let () = v in
                                     let (w, d′) = recv d′ in let () = w in close d′) in
                 let () = close c in
                 let () = close (send ⟨∗, send ⟨∗, d⟩⟩) in close e)
-- C = {ι ≺ κ, ι ≺ κ‾, ι ≺ δ‾} ∪ {δ+k ≺ κ, δ+k ≺ κ‾ | k},  δ = ι·0`,
    shows: 'An infinite box constraint. d acts at δ, δ+1 and δ+2 while e is held at κ. Lock free at N = 4, e loses 1 while c closes and 3 while d sends twice and closes.',
    rocq: 'examples/FreshMany.v: fm_typed; examples/LFFreshMany.v: fm_lftyped, fm_lock_free' },
  { id: 'ex-factory', title: 'The factory (FactoryEx)', modes: ['df', 'live', 'lf'],
    code: `mk₀  = !(f = λu. let () = u in let (c, c′) = new_0 in
                let () = spawn (λv. let () = v in close (send ⟨∗, c⟩)) in c′)
mk₁  = !(f = λp. let (p, ⟨c, c′⟩) = new_0 p in
                let () = spawn (λv. let () = v in close (send ⟨∗, c⟩)) in ⟨p, c′⟩)
main = let p = (force mk₀) ∗ in let ⟨p, q⟩ = (force mk₁) p in
       let () = recvclose p in recvclose q
-- Λ₀(r) = {r‾ ≺ r·0, r‾⁺ ≺ r·0}
-- mk₀ : □(∗ ⊸ ∃^⊥ ι. Λ₀(ι). (?∗.Close)@ι‾)`,
    shows: 'The first call creates at a fresh root and needs no point (#51, fx_no_first_call). The second anchors at the end it receives. Two variants of mk replace one term with two types. Lock free at N = 2.',
    rocq: 'examples/FactoryEx.v: fx_typed; examples/LFFactoryEx.v: fx_lftyped, fx_lock_free' },
  { id: 'ex-ring', title: 'The growing ring (GrowRing, Padovani 2014 Ex. III.7)', modes: ['df', 'live', 'lf'],
    code: `Sch  = µα. ?(∃κ. α@κ).Close
ring : □(∀ι₁ ι₂. Cr. ∗ ⊸ (Sch@ι₁ ⊗ S̄ch@ι₂ ⊸^{ι₁+1} ∗))
ring = !(f = λp. let (x, y) = p in
           let (y, ⟨a, a′⟩) = new_0 y in
           let () = spawn (λw. let () = w in close (send ⟨a, y⟩)) in
           let (x, ⟨b, b′⟩) = new_1 x in
           let (z, x) = recv x in let () = close x in
           let () = spawn (λw. let () = w in (force f) ⟨z, b′⟩) in
           spawn (λw. let () = w in (force f) ⟨b, a′⟩))
main = let (e, e′) = new_0 in (force ring) ⟨e, e′⟩`,
    shows: 'b is created by new_1 x before the receive on x, so it is anchored while x is held (the reordering of Appendix B.1). Cr holds five facts at every reachable pair. Lock free at N = 4 once the payload of Sch carries credit 2.',
    rocq: 'examples/GrowRing.v: rg_typed; examples/LFGrowRing.v: rg_lftyped, rg_lock_free' },
  { id: 'ex-close', title: 'Two threads closing one channel (LFClose)', modes: ['lf'],
    code: `cl c⁺ ∥ cl c⁻,   cl o = close o
-- each thread by lf_term over its end, cut c by lf_connect at exactly dual types`,
    shows: 'The smallest use of P-Term and P-Connect of ⊩. The world has no facts and no families, which makes it a lock-free world (lfworld_bare).',
    rocq: 'examples/LFClose.v: cl_lftyped, cl_lock_free' },
  { id: 'ex-guard-neg', title: 'Guard rejections (GuardEx)', modes: ['live', 'lf'],
    code: `div_box     = !(f = force f)                         -- #14
pn_fix      = !(f = λx. (force f) x)                  -- PN's ⟨fix λx.x⟩, #13
cx_box      = !(f = let ∗ = (force f) ∗ in λy. y)     -- GuardCex, #15
spawn_loop  = !(f = λc. spawn (λ_. (force f) c))      -- KobForwarder shape, #12, #40`,
    shows: 'Each box uses its self before any channel action, so ∅ ⊢▷ fails. The DF system keeps their typings, for instance PN\'s ⟨fix λx.x⟩.',
    rocq: 'examples/GuardEx.v: div_not_guarded, pn_fix_not_guarded, cx_not_guarded, spawn_loop_not_guarded' },
  { id: 'ex-guard-pos', title: 'Guard acceptances (GuardEx)', modes: ['live', 'lf'],
    code: `loop  = !(f = λx. let ⟨v, x′⟩ = recv x in (force f) x′)
stage = !(f = λin. let ⟨v, in⟩ = recv in in let ∗ = close in in
                  let ⟨a, b⟩ = new in let ∗ = spawn (λ_. (force f) b) in
                  close (send ⟨v, a⟩))                  -- C2 pipeline, B.1 #4`,
    shows: 'The receive ticks the context, so the self is unmarked when it is forced.',
    rocq: 'examples/GuardEx.v: loop_guarded, stage_guarded' },
  { id: 'ex-forwarder', title: 'The spawn forwarder (cost/Forwarder.v)', modes: ['lf'],
    code: `fw o = let ⟨w, c⟩ = recv o in let ∗ = close c in spawn w
o : ?(∗ ⊸ ∗)^2.end
dead_thunk q = λ_. let ∗ = Ω in close q`,
    shows: 'Before Q15, dead_thunk q was in FV with no ends, and fw had no fsem after receiving it (fw_counterexample, S7.1). Q15 rejects dead_thunk, and fw gets its fsem from fsem_of_cost.',
    rocq: 'cost/Forwarder.v: dead_thunk_rejected, fw_ptyped; cost/CostFund.v: fw_fsem' },
  { id: 'ex-controller', title: 'The controller under ⊩ (LFController, being retyped)', modes: ['lf'],
    code: `main = let (c, c′) = new_1 in
       let (a, a′) = new_0 in let (a, ⟨b, b′⟩) = new_κ a in
       let () = spawn (λu. let () = u in (force srv) ⟨⟨a′, b′⟩, c′⟩) in
       (force cli) ⟨⟨a, b⟩, c⟩
cli  = !(f = λp. let (q, k) = p in let (a, b) = q in
                let a = send ⟨∗, a⟩ in let (u, b) = recv b in
                let () = u in (force f) ⟨⟨a, b⟩, k⟩)
-- c sits at Skip on each side, an idle end`,
    shows: 'The controller (#20) is being retyped with age_idle. An idle end ages without the premise c ≤ a, and its credit falls to max(a − c, 0). With the old aging k lost credit at every step and reached the call below the parameter credit (C.6). The fuel layer already accepts idle ends, because their counters tick but skip the checks ≥ 1.',
    rocq: 'examples/LFController.v: sess_ages, idle_credit_falls, sess_sub_credit' }
);
