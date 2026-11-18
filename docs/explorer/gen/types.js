const { R, h, n, section, block, rule, Q, DEF } = require('./core');

const s = section('types', 'Types and worlds',
  'Types carry points and, under the merged judgment of Q11, cost annotations. The relations of deadlock freedom and liveness read no annotation. A world orders points and holds nothing else.');

block(s, {
  id: 'ty-grammar', title: 'Types', rocq: 'types/Types.v: ty',
  tex: R`T, U ::= ${h('ty.unit', R`\ast`)} \mid ${h('ty.arrow', R`T^{a} \multimap^{${h('ty.arrow.ub', 'u')}}_{${h('ty.arrow.lb', 'l')}}[${h('ty.arrow.cost', 'c')} ; ${h('ty.arrow.tix', R`\vartheta`)} ; ${h('ty.arrow.floor', 'h')}]\, U^{b}`)} \mid ${h('ty.prod', R`T^{a} \otimes U^{b}`)} \mid ${h('ty.sum', R`T^{a} \oplus U^{b}`)} \mid ${h('ty.sess', R`S@x`)} \mid ${h('ty.box', R`\Box(\forall ${h('pt.var', R`\bar\iota`)}\, ${h('ty.box.svars', R`\bar\alpha`)}.\ ${h('ty.box.constraint', 'C')}.\ \ast \multimap^{u}[c ; \vartheta]\, U^{b})`)} \mid ${h('ty.ex', R`\exists^{${h('ty.ex.lb', 'l')}} \bar\iota.\ C.\ T^{a}`)}`,
  variants: { df: R`T, U ::= ${h('ty.unit', R`\ast`)} \mid ${h('ty.arrow', R`T \multimap^{${h('ty.arrow.ub', 'u')}}_{${h('ty.arrow.lb', 'l')}} U`)} \mid ${h('ty.prod', R`T \otimes U`)} \mid ${h('ty.sum', R`T \oplus U`)} \mid ${h('ty.sess', R`S@x`)} \mid ${h('ty.box', R`\Box(\forall \bar\iota\, ${h('ty.box.svars', R`\bar\alpha`)}.\ ${h('ty.box.constraint', 'C')}.\ \ast \multimap^{u} U)`)} \mid ${h('ty.ex', R`\exists^{${h('ty.ex.lb', 'l')}} \bar\iota.\ C.\ T`)}`,
    live: R`T, U ::= ${h('ty.unit', R`\ast`)} \mid ${h('ty.arrow', R`T \multimap^{${h('ty.arrow.ub', 'u')}}_{${h('ty.arrow.lb', 'l')}} U`)} \mid ${h('ty.prod', R`T \otimes U`)} \mid ${h('ty.sum', R`T \oplus U`)} \mid ${h('ty.sess', R`S@x`)} \mid ${h('ty.box', R`\Box(\forall \bar\iota\, ${h('ty.box.svars', R`\bar\alpha`)}.\ ${h('ty.box.constraint', 'C')}.\ \ast \multimap^{u} U)`)} \mid ${h('ty.ex', R`\exists^{${h('ty.ex.lb', 'l')}} \bar\iota.\ C.\ T`)}` },
  caption: 'Superscripts a, b are credits. DF and live read the same types with every annotation erased (ty_df).'
});
block(s, {
  id: 'ty-credit', title: 'Credits', rocq: 'types/Costs.v: fuel',
  modes: ['lf'],
  tex: R`${h('ty.credit', R`T^{a},\ a \in \mathbb{N} \cup \{\infty\}`)} \qquad ${h('ty.credit-agg', R`(T^{a_1} \otimes U^{a_2})^{a} \text{ gives } a + a_1,\ a + a_2`)}`,
  caption: 'A credit is a lower bound on the counters of the ends a value holds. The credit of an aggregate adds to its parts.'
});
block(s, {
  id: 'ty-session', title: 'Session types', rocq: 'types/Types.v: sty, unfoldS',
  tex: R`S ::= ${h('sty.skip', R`\mathsf{Skip}`)} \mid ${h('sty.seq', R`S ; S`)} \mid ${h('sty.recv', R`?(\exists^{m}\bar\iota.\ T^{${h('sty.payload-credit', 'b')}})`)} \mid ${h('sty.send', R`!(\exists^{m}\bar\iota.\ T^{b})`)} \mid ${h('sty.plus', R`\oplus(S_1, S_2)`)} \mid ${h('sty.with', R`\&(S_1, S_2)`)} \mid ${h('sty.close', R`\mathsf{Close}`)} \mid ${h('sty.mu', R`\mu\alpha.S`)} \mid ${h('sty.var', R`\alpha`)} \mid ${h('sty.vard', R`\overline{\alpha}`)} \qquad ${h('sty.unfold', R`\mathsf{unfold}(S)`)}`,
  caption: 'Context-free session types, read through their head normal form. A payload binds m point variables that land on the payload fields of the carrier.'
});
block(s, {
  id: 'ty-dual', title: 'Duality', rocq: 'types/Types.v: dual, sflip',
  tex: h('sty.dual', R`\mathsf{dual}(!P) = ?P \quad \mathsf{dual}(?P) = !P \quad \mathsf{dual}(\oplus(S_1,S_2)) = \&(\mathsf{dual}\,S_1,\mathsf{dual}\,S_2) \quad \mathsf{dual}(S_1;S_2) = \mathsf{dual}\,S_1;\mathsf{dual}\,S_2 \quad \mathsf{dual}(\alpha) = \overline{\alpha} \quad \mathsf{dual}(\mu\alpha.S) = \mu\alpha.\,${h('sty.flip', R`\mathsf{flip}_\alpha`)}(\mathsf{dual}\,S)`),
  caption: 'Polarized duality. Payloads stay unchanged, Skip and Close are self-dual.'
});
block(s, {
  id: 'ty-equiv', title: 'Session equivalence', rocq: 'types/Types.v: sequiv, relation/Relation.v: seqv, sdual',
  tex: R`${h('sty.sequiv', R`S \simeq S'`)} \qquad ${h('sty.seqv', R`S \approx S' \iff \mathsf{sty\_df}(S) \simeq \mathsf{sty\_df}(S')`)} \qquad ${h('sty.sdual', R`\mathsf{sdual}\,S\,S' \iff S' \approx \overline{S}`)}`,
  caption: 'Bisimilarity of head normal forms, and the same up to annotations, which is what the relation compares.'
});
block(s, {
  id: 'ty-heads', title: 'Heads, ⊥ flag, lower bounds', rocq: 'types/Types.v: heads, hbot, types/Points.v: lbound',
  tex: R`${h('ty.heads', R`\mathsf{heads}(S@x) = \{\overline{x}\} \quad \mathsf{heads}(T \multimap_{l} U) = \{l\} \quad \mathsf{heads}(\exists^{l}) = \{l\} \quad \mathsf{heads}(\Box\ldots) = \varnothing`)} \qquad ${h('ty.hbot', R`\mathsf{hbot}(T)`)} \qquad ${h('ty.lbound', R`l ::= \cdot \mid \bot \mid x`)}`,
  caption: 'The heads of a type are the partner points a thread holding a value of it owes readiness facts against.'
});
block(s, {
  id: 'ty-payload', title: 'Payloads', rocq: 'types/Types.v: payload_at, pscoped',
  tex: R`${h('ty.payload-at', R`\mathsf{payload\_at}\,m\,T\,x = T[x\cdot 0, \ldots, x\cdot(m{-}1) / \iota_0, \ldots, \iota_{m-1}]`)} \qquad ${h('ty.pscoped', R`\mathsf{pscoped}\,m\,T`)}`,
  caption: 'A payload is point-closed below its own binder and is placed at the fields of the carrier point.'
});
block(s, {
  id: 'ty-annot', title: 'Costs and ticket transformers', rocq: 'types/Costs.v: tix, meets, tspawn, tlink, tseq, tok',
  modes: ['lf'],
  tex: R`\begin{array}{l}
${h('ann.fuel', R`a, c, h \in \mathbb{N}\cup\{\infty\}`)} \qquad ${h('ann.tix', R`\vartheta = (s, b) : r \mapsto 2^{s} r + b`)} \qquad ${h('ann.tid', R`\hat 1 = (0, 0)`)} \qquad ${h('ann.meets', R`\mathsf{meets}\,\vartheta\,r\,tk \iff \vartheta(r) \leq tk`)} \\
${h('ann.tspawn', R`\mathsf{tspawn}\,b_c\,\vartheta = (s{+}1, \max(2b, 2b_c{-}1))`)} \qquad ${h('ann.tlink', R`\mathsf{tlink}\,\vartheta = (s, b{+}1)`)} \qquad ${h('ann.tseq', R`\vartheta_1 \circ \vartheta_2`)} \qquad ${h('ann.tok', R`\mathsf{tok}\,\vartheta_1\,\vartheta_2 \iff b_2 = 0 \lor s_1 \neq \infty \lor b_1 = \infty`)}
\end{array}`,
  caption: 'A transformer says how many link tickets a term needs given the reserve r it must still hold when it returns.'
});
block(s, {
  id: 'ty-df', title: 'Annotations of N = ∞', rocq: 'types/Types.v: ty_df, cr_df',
  tex: h('ann.tydf', R`\mathsf{ty\_df}(T):\ \text{credits } \infty\ (0 \text{ on } \otimes, \oplus, \exists),\ \text{costs } \infty,\ \vartheta = (\infty,\infty),\ \text{floors } \infty`),
  caption: 'The deadlock-freedom instance of every annotation.'
});
block(s, {
  id: 'ty-kinds', title: 'Kinds of types', rocq: 'types/Types.v: prim, unlimited, tfree',
  tex: R`${h('ty.prim', R`\mathsf{prim}\,T ::= \ast \mid \mathsf{prim} \otimes \mathsf{prim} \mid \mathsf{prim} \oplus \mathsf{prim} \mid \Box(\ldots \mathsf{prim})`)} \qquad ${h('ty.unlimited', R`\mathsf{unlimited}\,T \iff T = \Box\ldots`)} \qquad ${h('ty.tfree', R`\mathsf{tfree}\,T`)}`,
  caption: 'prim is the shape of a process result, unlimited the types that admit weakening and contraction, tfree the types that hold no end.'
});
block(s, {
  id: 'w-world', title: 'Worlds', rocq: 'types/Worlds.v: world',
  tex: h('w.world', R`W = (${h('w.consts', 'A')}, ${h('w.facts', R`\prec_A`)}, ${h('w.fams', 'L')}, ${h('w.laws', R`(\Lambda_\ell)_{\ell \in L}`)})`),
  caption: 'Constants, facts between constant points, family labels and the laws of each family over one root variable.'
});
block(s, {
  id: 'w-order', title: 'The order ≺_W', rocq: 'types/Worlds.v: wstep, w_lt',
  tex: h('w.lt', R`\prec_W\ =\ \mathsf{tc}\big(${h('w.ws-fact', R`\prec_A`)} \;\cup\; ${h('w.ws-law', R`\textstyle\bigcup_{\ell \in L,\, g} \Lambda_\ell(g_\ell)`)} \;\cup\; ${h('w.ws-po', R`\{x \prec x^{+}\}`)} \;\cup\; ${h('w.ws-dpo', R`\{x \prec \overline{x}^{+}\}`)}\big)`),
  caption: 'The laws hold at every generated root of their family, so W is constant along a run that creates roots.'
});
block(s, {
  id: 'w-wf', title: 'Well-formed, strict and lock-free worlds', rocq: 'types/Worlds.v: world_wf, strict, lfworld',
  tex: R`${h('w.wf', R`\mathsf{world\_wf}\,W`)} \qquad ${h('w.strict', R`\mathsf{strict}\,W \iff \mathsf{world\_wf}\,W \land \forall x.\ W \nvdash x \prec x`)} \qquad ${h('w.lfworld', R`\mathsf{lfworld}\,W \iff \mathsf{strict}\,W \land \mathsf{well\_founded}(\prec_W)`)}`,
  caption: 'Deadlock freedom needs an irreflexive order. Lock freedom also needs no infinite descending chain.'
});
block(s, {
  id: 'w-ext', title: 'Extension, join, restriction', rocq: 'types/Worlds.v: wext, wjoin, wrestrict, strict_join_iff',
  tex: R`${h('w.ext', R`W \sqsubseteq W'`)} \qquad ${h('w.join', R`W_1 \sqcup W_2`)} \qquad ${h('w.R7', R`\mathsf{strict}(W_1 \sqcup W_2) \iff \mathsf{strict}\,W_1 \land \mathsf{strict}\,W_2 \land \mathsf{strict}(${h('w.restrict', R`W_1|_S`)} \sqcup W_2|_S),\ S = A_1 \cap A_2`)}`,
  caption: 'Kripke extension, the union of two worlds, and the R7 characterization of a strict join by the shared constants.'
});

// ---- notes ----
n('ty.unit', 'Unit type ∗', 'The type of ∗. A value of it holds no end.', 'A plain type. Close, link and spawn return it, and every spawned thread returns it.', DEF, 'close returns ∗.', 'types/Types.v: TUnit');
n('ty.arrow', 'Arrow', 'A closure type with an upper point u and a lower point l. In the lock-free system it also carries a cost c, a ticket transformer ϑ, a floor h and credits on argument and result.', 'Calling a closure runs code that may block, so the type must say where it may block and what ends it holds.', DEF, '∗ ⊸ ∗ for a spawned thunk.', 'types/Types.v: TLolli');
n('ty.arrow.ub', 'Upper point u', 'The latest point at which a call may block. A caller may run the closure only when everything it still has to do lies above u.', 'The caller cannot see inside the closure. u summarizes where the closure may wait.', 'Without it, a closure that blocks above the caller\'s remaining actions could be called before those actions, and the thread would wait on itself.', 'A function that blocks on an end at κ has u = κ.', 'types/Types.v: TLolli ub');
n('ty.arrow.lb', 'Lower point l', 'A lower bound on the partner points of the ends the closure holds. Absent when it holds none.', 'A closure is a held value. A thread that holds it must not block above the ends inside, and l stands for those ends.', 'Without it, a thread could block at a point above an end captured in a closure it holds.', 'A closure capturing a⁺ at ρ has l = ρ̄.', 'types/Types.v: TLolli lb');
n('ty.arrow.cost', 'Arrow cost c', 'At most c channel actions before the closure returns. Only the lock-free system reads it.', 'A thread that holds an end while it runs other code delays that end. The cost bounds the delay.', 'A thread holding an end while it calls a function that never returns would starve the partner of that end. A cost ∞ makes the held end fail aging.', 'A loop body that never returns costs ∞.', 'types/Types.v: TLolli c');
n('ty.arrow.tix', 'Arrow transformer ϑ', 'How many link tickets a call needs for a given reserve.', 'Links take no action on any protocol. Tickets bound how many links a thread may perform.', 'A box that links once per round forever needs infinitely many tickets and is rejected.', 'One link needs one ticket more than the reserve.', 'types/Types.v: TLolli t');
n('ty.arrow.floor', 'Floor h', 'Every captured counter must be at least h for the body to work. The body sees captured ends at credit h.', 'The body cannot know the counters of the ends it captured. h is what it may assume.', DEF, 'Deadlock-freedom typing takes h = ∞.', 'types/Types.v: TLolli h');
n('ty.credit', 'Credit a', 'A lower bound on the counters of the ends a value holds.', 'A counter says how many more actions of others an end may wait through. A credit lets the type promise a minimum.', 'A send of an end whose counter may be 0 would let it travel forever while its partner waits.', 'A fresh end has credit N.', 'types/Types.v: ty (fuel fields)');
n('ty.credit-agg', 'Credit of an aggregate', 'A credit on a product, sum or existential is added to its parts. Aging, capture and subtyping push it inward.', 'A pair at credit 1 whose parts have credit 1 and 2 holds ends with at least 2 and 3.', DEF, '(T¹ ⊗ U²)¹ gives T at 2 and U at 3.', 'static/Contexts.v: tage, tcap, tsub');
n('ty.prod', 'Product', 'A pair of values. The two components hold different ends.', 'A plain type. Send takes a pair and receive returns one.', DEF, 'S₁@ι ⊗ S₂@κ for two ends of a client.', 'types/Types.v: TProd');
n('ty.sum', 'Sum', 'One of two injections.', 'A plain type. Branch returns a sum that tells which choice arrived.', DEF, 'branch returns S₁@x·κ₁ ⊕ S₂@x·κ₂.', 'types/Types.v: TSum');
n('ty.sess', 'End type S@x', 'An end running protocol S that acts next at point x.', 'Points carry the order that rules out circular waiting.', DEF, '(!∗.Close)@ρ.', 'types/Types.v: TSess');
n('ty.box', 'Box type', 'A replicable thunk, usable at every instance of its point variables that meets C and at every instance of its session variables. Its body has type ∗ ⊸^u U.', 'A loop needs a fresh point for each round. Quantifying over points under a box gives every call its own points.', DEF, 'A client loop has type □∀ι κ ζ. C. ∗ ⊸ (S₁@ι ⊗ S₂@κ ⊸^ζ ∗).', 'types/Types.v: TBox');
n('ty.box.svars', 'Session variables of a box', 'k session variables, instantiated at every force.', 'One box can serve every protocol the caller plugs in. Only protocols whose recursion always passes an action may be plugged in.', DEF, 'A forwarder box that works for any protocol α.', 'types/Types.v: TBox k');
n('ty.box.constraint', 'Box constraint C', 'A set of facts over the bound point variables and some outer points. It may be infinite.', 'A loop orders the points of all its rounds at once. An infinite set states the facts of every round.', 'Without a constraint a box cannot type a loop that waits on one end while it holds another across rounds.', 'C states ι ≺ κ̄ for the points of every round of a client loop.', 'types/Points.v: bcs');
n('ty.ex', 'Existential', '∃^l ῑ. C. T is T at some instance meeting C, with lower bound l on its partner points.', 'A fresh point is not known outside the term that made it. new_ℓ returns an existential over it, and payloads bind their points the same way.', DEF, 'new₀ returns ∃^⊥ ι. Λ₀(ι). (S@ι ⊗ S̄@ῑ).', 'types/Types.v: TEx');
n('ty.ex.lb', 'Lower bound of an existential', 'Absent when the value holds no end, ⊥ when its ends sit at points unknown outside, a point x when every end lies at or above x.', 'The ⊥ bound stands for a fresh point the context does not know.', 'Without ⊥, a closure could capture an unopened fresh pair and claim a lower point no fact supports.', 'new_ℓ has type ∃^⊥.', 'types/Points.v: lbound');
n('sty.skip', 'Skip', 'The empty protocol. An end at Skip is idle and no rule acts on it.', 'An idle end may be held forever without anybody waiting on it. The lock-free system drops its checks that counters are at least 1.', DEF, 'A control end that is passed around but never used sits at Skip.', 'types/Types.v: SSkip, fuel/Fuel.v: idle');
n('sty.seq', 'Sequencing', 'S.S′ runs S and then S′. unfold normalizes it to the first action.', 'Sequencing composes protocols, so recursion need not end in tail position.', DEF, '(!∗).Close.', 'types/Types.v: SSeq');
n('sty.recv', 'Receive', '?(∃^m ῑ. T^b) receives a payload whose m point variables land on the fields of the carrier.', 'A plain protocol action. Binding the payload points lets a message carry ends whose points the receiver learns on arrival.', DEF, 'µα. ?(∃κ. α@κ).Close receives an end of the same protocol at a field.', 'types/Types.v: SRcv');
n('sty.send', 'Send', '!(∃^m ῑ. T^b) sends a payload at credit b.', 'A plain protocol action, the dual of receive.', DEF, '!∗.Close.', 'types/Types.v: SSnd');
n('sty.payload-credit', 'Payload credit b', 'The floor the receiver may assume for the counters of the ends the message carries. The sender must supply b after aging by one.', 'A forwarded end loses one at each hop. Asking b + 1 of the sender when the receiver gets b rules out endless forwarding.', 'Without floors, two threads could pass an end back and forth forever, and its partner would wait forever.', 'A payload at credit 2.', 'types/Types.v: SRcv b, SSnd b');
n('sty.plus', 'Internal choice', '⊕(S₁, S₂). The selecting side picks.', 'A plain protocol action. Internal choice lets a thread decide how the conversation continues.', DEF, '⊕(Close, !∗.Close).', 'types/Types.v: SPlus');
n('sty.with', 'External choice', '&(S₁, S₂). The branching side receives the choice.', 'A plain protocol action, the dual of internal choice.', DEF, '&(Close, ?∗.Close).', 'types/Types.v: SWith');
n('sty.close', 'Close', 'The end must close next.', 'A plain protocol action. Every finite protocol ends with it.', DEF, 'Close@x⁺ after one send at x.', 'types/Types.v: SEnd');
n('sty.mu', 'Recursion µα.S', 'A recursive protocol.', 'A plain former. Loops run protocols that repeat.', DEF, 'µα.!∗.α sends units forever.', 'types/Types.v: SMu');
n('sty.var', 'Session variable α', 'A recursion variable or a session variable of a box.', 'A plain former. It refers back to an enclosing µ or to a protocol plugged into a box.', DEF, 'α in µα.!∗.α.', 'types/Types.v: SVar');
n('sty.vard', 'Dual variable ᾱ', 'The dual of a variable. It enters only through dual.', 'The dual of a protocol plugged in for α is only known once α is. ᾱ marks that.', DEF, 'dual α = ᾱ.', 'types/Types.v: SVarD');
n('sty.unfold', 'Head normal form', 'unfold(S) unrolls µ and normalizes sequencing until the first action.', 'Every rule reads the first action of a session type.', DEF, 'unfold (µα.!∗.α) = !∗.(µα.!∗.α).', 'types/Types.v: unfoldS');
n('sty.dual', 'Duality', 'Swaps send and receive and the two choices. Payloads stay.', 'The two ends of a channel run dual protocols.', DEF, 'dual (!∗.Close) = ?∗.Close.', 'types/Types.v: dual');
n('sty.flip', 'flip', 'Swaps α and ᾱ at one level. Dual uses it under a µ.', 'Inside µα.S the variable α names the whole recursive protocol. After dualizing the body, α must name the dual µ again, so the ᾱ that dual introduced turn back into α.', DEF, 'dual (µα.!∗.α) = µα.?∗.α.', 'types/Types.v: sflip');
n('sty.sequiv', 'Session equivalence ≃', 'Two protocols are equivalent when their first actions agree and their continuations are again equivalent. Annotations count.', 'One protocol has many spellings, unrolled or not. Rules compare protocols by behaviour, not by spelling.', DEF, 'µα.!∗.α ≃ !∗.µα.!∗.α.', 'types/Types.v: sequiv');
n('sty.seqv', 'Up to annotations ≈', 'Equivalence after erasing annotations. The value relation compares session types this way.', 'The deadlock-freedom and liveness relations ignore credits. One relation then serves every refill N.', DEF, '!(∗²).Close ≈ !(∗^∞).Close.', 'relation/Relation.v: seqv');
n('sty.sdual', 'Dual up to annotations', 'S′ is the dual of S up to annotations.', 'The relation compares dual protocols up to annotations.', DEF, 'A link of ends at S and S′ asks sdual S S′.', 'relation/Relation.v: sdual');
n('ty.heads', 'heads', 'The points a held value owes readiness facts against. An end at x contributes x̄, the point of its partner.', 'A thread blocked at u that holds an end at v needs u ≺ v̄. Otherwise the partner of that end could be waiting for the thread.', DEF, 'heads (Close@ρ ⊗ Close@ρ·0) = {ρ̄, (ρ·0)‾}.', 'types/Types.v: heads');
n('ty.hbot', 'The ⊥ flag of a type', 'True when the value may hold an unopened existential at ⊥.', 'Ends at unknown points give no fact to block against. A term whose context holds such ends may not block.', DEF, 'hbot (∃^⊥ ι. T) = true.', 'types/Types.v: hbot');
n('ty.lbound', 'lbound', 'The lower bound of an existential. Absent, ⊥, or a point.', 'It says how much a holder knows about where the hidden ends sit.', DEF, '⊥ for new_ℓ.', 'types/Points.v: lbound');
n('ty.payload-at', 'payload_at', 'Places the m bound points of a payload at the fields x·0 … x·(m−1) of the carrier x.', 'Fields ignore polarity, so sender and receiver compute the same points.', DEF, 'A payload α@κ sent at Y lands at Y·0.', 'types/Types.v: payload_at');
n('ty.pscoped', 'pscoped', 'Every point variable of T is bound by the payload itself. Send and receive check it.', 'A payload mentions only its own points, so unrolling a recursive protocol never captures an outer point.', 'A free outer point inside a µ-body would be captured on unrolling, and substituting points would go wrong.', 'pscoped 1 (S@ι₀).', 'types/Types.v: pscoped');
n('ann.fuel', 'ℕ ∪ {∞}', 'Credits, costs, floors and counters range over the naturals and ∞.', 'Deadlock-freedom typing is the case where every fresh and refilled counter is ∞. Subtracting from ∞ keeps ∞.', DEF, '∞ − c = ∞.', 'types/Costs.v: fuel');
n('ann.tix', 'Ticket transformer', 'ϑ = (s, b) stands for r ↦ 2^s·r + b. Slope s and offset b range over the naturals and ∞.', 'Spawning splits the tickets in half, so needs grow by doubling. The offset ∞ marks a term no finite ticket count serves, which is what deadlock-freedom typing uses.', 'Without the offset ∞, the transformer of deadlock-freedom typing could not be composed with the one ticket a link needs.', '(0, 1) needs one ticket more than its reserve.', 'types/Costs.v: tix, tapp');
n('ann.tid', '1̂', 'The identity transformer r ↦ r.', 'A value performs no link, so it needs exactly the reserve it holds.', DEF, 'Every value types at 1̂.', 'types/Costs.v: tid');
n('ann.meets', 'meets', 'A ticket count tk meets ϑ at reserve r when ϑ(r) ≤ tk.', 'A thread starts with some finite ticket count, which must cover what its transformer asks at reserve 0.', DEF, 'meets (0, 1) 0 1.', 'types/Costs.v: meets');
n('ann.tspawn', 'tspawn', 'The transformer of a spawn. The child gets ⌈tk/2⌉ and needs b_c, the parent keeps ⌊tk/2⌋.', 'A fixed split needs no knowledge of the future and is the same in every run.', DEF, 'A spawn of a child that links once.', 'types/Costs.v: tspawn');
n('ann.tlink', 'tlink', 'One ticket, then ϑ.', 'A link spends a ticket. Tickets are never created, so two threads cannot take turns linking an end forever.', DEF, 'A link composes with tlink 1̂.', 'types/Costs.v: tlink');
n('ann.tseq', 'Sequencing ϑ₁ ∘ ϑ₂', 'First ϑ₁, then ϑ₂. (ϑ₁ ∘ ϑ₂)(r) = ϑ₁(ϑ₂(r)).', 'The first part of a term must leave enough tickets for the rest.', DEF, 'An application composes the transformers of function, argument and call.', 'types/Costs.v: tseq');
n('ann.tok', 'tok', 'ϑ₁ ∘ ϑ₂ is sound when ϑ₂ needs nothing at 0, ϑ₁ has a finite slope, or ϑ₁ has offset ∞.', 'Composition through an infinite slope is only meaningful in these cases.', 'A sequence of an infinite-slope transformer after one that needs tickets at 0 would claim a finite need it does not have.', 'An application asks tok of its parts.', 'types/Costs.v: tok');
n('ann.tydf', 'ty_df', 'Sets every annotation to its value at N = ∞.', 'Deadlock-freedom typing is the merged judgment with infinite refill, so its types carry these annotations.', DEF, 'ty_df (S@x) sets the payload credits of S to ∞.', 'types/Types.v: ty_df');
n('ty.prim', 'prim', 'Types built from ∗, ⊗, ⊕ and boxes. Every process result has this shape.', 'A process result holds no end, so no thread is left waiting on the result.', 'A main thread that returns an end holds it forever, and its partner waits forever.', 'prim (∗ ⊗ ∗).', 'types/Types.v: prim');
n('ty.unlimited', 'unlimited', 'Box types. Variables of these types may be copied and dropped.', 'A box holds no end, so copying or dropping it loses or duplicates nothing.', DEF, 'The self of a box is unlimited.', 'types/Types.v: unlimited');
n('ty.tfree', 'tfree', 'Types built from ∗, boxes, pairs and sums that hold no end.', 'Aging and capture adjust credits of entries that hold ends. An entry of such a type holds none, so they leave its credit alone.', DEF, 'tfree (∗ ⊗ □…).', 'types/Types.v: tfree');
n('w.world', 'World', 'Constants, facts, families and laws. Nothing else.', 'Points carry the order, and the world is the order.', DEF, 'A world with no constants and one family 0 with laws Λ₀.', 'types/Worlds.v: world');
n('w.consts', 'Constants A', 'The finite set of constant roots.', 'Facts may mention only constants, and two worlds are compared at composition through the constants they share.', DEF, 'A world with constants 1 and 2.', 'types/Worlds.v: w_consts');
n('w.facts', 'Facts ≺_A', 'Facts between points with constant roots.', 'They order the channels a component shares with its environment.', DEF, '1 ≺ 2̄.', 'types/Worlds.v: w_facts');
n('w.fams', 'Families L', 'The family labels the world knows. new_ℓ types only for ℓ in L.', 'A family label names a set of laws.', DEF, '{0} for one family.', 'types/Worlds.v: w_fams');
n('w.laws', 'Laws Λ_ℓ', 'Facts over one root variable ι₀ of family ℓ, holding at every generated root of ℓ.', 'A law speaks of one root, so two generated roots are never ordered against each other. W is strict exactly when its facts and each family of laws are.', 'With one set of laws for all fresh points, two components with different needs could not be composed, because their joined world would be cyclic.', 'Λ₀(r) = {r ≺ (r·0)‾, r̄ ≺ r·0}.', 'types/Worlds.v: w_laws');
n('w.lt', '≺_W', 'The transitive closure of the four kinds of generator.', 'A plain definition. Waiting chains combine many facts, so the order is transitive.', DEF, 'W ⊢ x ≺ x⁺⁺.', 'types/Worlds.v: w_lt');
n('w.ws-fact', 'Facts generator', 'Every fact of ≺_A is an order fact.', 'A plain generator. The facts of the world hold.', DEF, '1 ≺ 2̄.', 'types/Worlds.v: ws_fact');
n('w.ws-law', 'Laws generator', 'Every law of family ℓ in L holds at every generated root g of ℓ.', 'Every generated root is known up front, so the world stays the same along a run that creates channels.', DEF, 'Λ₀ at g gives g ≺ (g·0)‾.', 'types/Worlds.v: ws_law, law_inst');
n('w.ws-po', 'x ≺ x⁺', 'Program order of one end.', 'An end acts at x before it acts at x⁺.', DEF, 'ρ ≺ ρ⁺.', 'types/Worlds.v: ws_po');
n('w.ws-dpo', 'x ≺ x̄⁺', 'An action at x precedes the next action of the partner.', 'It holds in every run. The action at x synchronizes with the partner at x̄, and the partner acts again at x̄⁺ only afterwards, so programs may use it without stating it.', DEF, 'ρ ≺ ρ̄⁺.', 'types/Worlds.v: ws_dpo');
n('w.wf', 'world_wf', 'Facts mention constants of A, and laws mention only the root variable ι₀.', 'A law that mentions another root would order fresh points against each other.', DEF, 'A law ι₀ ≺ g′ with another root g′ is not well formed.', 'types/Worlds.v: world_wf');
n('w.strict', 'strict', 'Well formed and irreflexive.', 'An irreflexive order cannot let two threads each wait on the other.', 'In a cyclic world two threads that wait on each other both count as ready, and a deadlock types.', 'A world whose only fact is 1 ≺ 2̄.', 'types/Worlds.v: strict');
n('w.lfworld', 'lfworld', 'Strict and well founded.', 'Lock freedom ranks a waiting thread by the point of the end it waits on. Waiting chains must then descend in a well-founded order.', 'Without it, waiting could descend forever. Each thread waits on one below it, new threads keep appearing below, and the top thread never proceeds.', 'A world with no facts and no families.', 'types/Worlds.v: lfworld');
n('w.ext', 'World extension ⊑', 'More constants, facts, families and laws.', 'A program keeps working when its world grows, for example after composition with another component.', DEF, 'W ⊑ W ⊔ W′.', 'types/Worlds.v: wext');
n('w.join', 'Join ⊔', 'The union of constants, facts, families and laws.', 'Two components typed in their own worlds compose in the union. Their families must be disjoint.', DEF, 'W ⊔ W.', 'types/Worlds.v: wjoin');
n('w.restrict', 'Restriction W|_S', 'The facts of ≺_W between points with constant roots in S, without families.', 'It is the part of a world that another component can see through shared constants.', DEF, 'W restricted to its shared constants.', 'types/Worlds.v: wrestrict');
n('w.R7', 'Strict join', 'A join is strict exactly when both worlds are and their orders restricted to the shared constants are acyclic together.', 'Composition can check strictness of the join by looking only at the shared constants.', DEF, 'Two strict worlds with no shared constants join strictly.', 'types/Worlds.v: strict_join_iff');
