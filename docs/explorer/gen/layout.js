// Which blocks exist and in which order. The rules are in ../BLOCKS.md. The section files define
// fine-grained blocks, and this file groups them: one block per definition or per rule group of
// one construct, lock-free additions inside the block they extend, lock-free blocks of their own
// only for notions without a deadlock-free counterpart.
const core = require('./core');
const { R, sections } = core;

// old block id -> the block that now holds it, for links and "used in" lists
const alias = {};
const SEP = R`\\[3ex]`;

function locate(id) {
  for (const s of sections) { const b = s.blocks.find(x => x.id === id); if (b) return [s, b]; }
  throw new Error('layout: no block ' + id);
}
const lfOnly = b => !b.modes.includes('df');
const lfTex = b => (b.variants && b.variants.lf) || b.tex;
const dfTex = b => (b.variants && b.variants.df) || b.tex;

// sentences of a caption that speak about the lock-free mode only, hidden in the deadlock-free mode
function lfSentences(t) {
  if (typeof t !== 'string') return t;
  const out = []; let cur = '', inM = false, depth = 0;
  for (let i = 0; i < t.length; i++) {
    const c = t[i]; cur += c;
    if (c === '$' && t[i - 1] !== '\\') inM = !inM;
    if (!inM && c === '{') depth++; if (!inM && c === '}') depth--;
    if (!inM && !depth && c === '.' && (t[i + 1] === ' ' || i === t.length - 1)) { out.push(cur); cur = ''; }
  }
  if (cur) out.push(cur);
  return out.map(s => /^\s*In the lock-free mode\b/.test(s) ? s.replace(/^(\s*)([\s\S]*)$/, (m, sp, b) => sp + '\\annp{' + b + '}') : s).join('');
}

// replace the blocks ids by one block, at the place of the first of them
function merge(id, title, ids, opts = {}) {
  const parts = ids.map(locate);
  const bs = parts.map(p => p[1]);
  const [s0] = parts[0];
  const modes = [...new Set(bs.flatMap(b => b.modes))];
  const mixed = modes.includes('df');
  const tex = bs.map((b, i) => {
    const sep = i ? SEP : '';
    return mixed && lfOnly(b) ? R`\annraw{${sep}}\annot{${lfTex(b)}}` : sep + lfTex(b);
  }).join('');
  const nb = {
    id, title, modes,
    rocq: bs.map(b => b.rocq).filter(Boolean).join('; '),
    tex: R`\begin{array}{c}${tex}\end{array}`,
    caption: opts.caption !== undefined ? opts.caption : bs.map(b => mixed && lfOnly(b) ? R`\annp{${b.caption}}` : b.caption).join(' ')
  };
  if (mixed && bs.some(b => b.variants && (b.variants.df || b.variants.lf)))
    nb.variants = { df: R`\begin{array}{c}${bs.filter(b => !lfOnly(b)).map(dfTex).join(SEP)}\end{array}` };
  const used = [...new Set(bs.flatMap(b => (b.about && b.about.used) || []))].filter(x => !ids.includes(x));
  nb.about = { why: opts.why || (bs[0].about && bs[0].about.why) || '', used };
  if (opts.example) nb.about.example = opts.example;
  const at = s0.blocks.indexOf(bs[0]);
  for (const [s, b] of parts) s.blocks.splice(s.blocks.indexOf(b), 1);
  s0.blocks.splice(at, 0, nb);
  for (const x of ids) alias[x] = id;
  return nb;
}
// drop a block whose content another block states
function drop(id, into) { const [s, b] = locate(id); s.blocks.splice(s.blocks.indexOf(b), 1); alias[id] = into; }
// put the blocks of a section in the given order, the unnamed ones after
function order(sec, ids) {
  const s = sections.find(x => x.id === sec);
  const named = ids.map(id => { const b = s.blocks.find(x => x.id === id); if (!b) throw new Error('layout: order ' + id); return b; });
  s.blocks = [...named, ...s.blocks.filter(b => !ids.includes(b.id))];
}
const set = (id, f) => f(locate(id)[1]);

// ---- types and worlds ----
set('ty-grammar', b => {
  b.caption = R`$S@x$ is an end at the point $x$. \annp{Credits $a$ sit on ends and on closures, the two places where a value holds ends of its own. The credit of an end bounds its counter from below, and the credit of a closure bounds the captured counters from below and bounds what they lose before a call. Pairs, sums, existentials and payloads carry no credit, their ends carry their own.}`;
});
drop('ty-credit', 'ty-grammar');
merge('ty-ann', 'Annotations and tickets', ['ty-annot', 'ty-tix', 'ty-df'], {
  caption: R`Credits $a$, costs $c$, tickets $m$ and the bound $N$ are numbers, and $\infty$ means unbounded. An end has $m$ tickets with $a \leq m$, and the tickets of the two ends of a channel sum to at most $N$. Deadlock-free typing is the instance $\mathsf{ty\_df}$ with every annotation unbounded.`,
  why: 'The numbers lock-free typing adds to types and judgments. At their unbounded values every premise about them holds, which is how deadlock-free typing is an instance.'
});

// ---- typing ----
merge('t-agecap', 'Aging', ['t-age'], {
  why: 'Aging is how typing charges a held value for the actions that run while it is held. A closure at credit $a$ ages its captured ends by $a$ for its body.'
});
merge('r-base', 'Unit, variables and ends', ['r-unit', 'r-var', 'r-chan'], {
  caption: R`$\ast$ uses no entry of $\Delta$, a variable and an end are typed by their own entry, and every other entry must be unlimited.`,
  why: 'The leaves of a derivation. They are where unused unlimited entries are dropped.'
});
merge('r-fun', 'Functions', ['r-abs', 'r-app'], {
  why: 'A closure delays its body to its call. Its type records the bounds the body needs, so the call site can check them.'
});
merge('r-data', 'Products, sums and let', ['r-pair', 'r-let', 'r-case'], {
  why: 'Data holds values while other code runs. The pair rule is where holding a value costs order facts.'
});
merge('r-boxes', 'Boxes', ['r-box', 'r-force'], {
  why: 'Boxes are the only recursion and the only polymorphism over points and protocols. Each force picks an instance.'
});
set('r-ex', b => { b.title = 'Existentials'; });
set('r-new', b => { b.title = 'Creation'; });
merge('r-act', 'Actions and link', ['r-send', 'r-recv', 'r-close', 'r-select', 'r-branch', 'r-link'], {
  caption: R`An action on an end at $x$ waits at $x$ while the thread holds the rest of $\Delta$, so $x$ lies below the future and below the dual points of what is held. Send and receive move the end to $x^{+}$ and the payload to the fields of $x$, a choice moves it to the field of the branch, and a link asks no order fact. \annp{In the lock-free mode every action returns the end reset to its tickets $m$ and costs one, and a link asks the credit of each linked end to exceed the partner bound of the other.}`,
  why: 'The session primitives. Every order fact the type system asks for is asked here, at the moment a thread waits.'
});
merge('r-threads', 'Spawn', ['r-spawn'], {
  why: 'A spawn transfers ends to a new thread that starts with nothing after it, so the child body is read at the empty future.'
});
merge('t-subs', 'Subtyping and structural rules', ['t-sub', 'r-struct', 'r-admis'], {
  why: 'Subtyping lets a value lose facts it does not need. Weakening and contraction are admissible, so the rules state no structural rule of their own.'
});
merge('p-typing', 'Process typing', ['p-term', 'p-connect', 'p-lf'], {
  caption: R`P-Term types one thread $t$ that holds both ends of every channel in $C_0$, at dual types and points, over a partner-free interface $\Sigma$. P-Connect cuts two components at $\Sigma_C$ against $\overline{\Sigma_C}$, the left one carrying $T$, and compares only the shared roots of the two worlds. \annp{Lock-free typing is process typing at finite $N$ with every thread guarded.}`,
  why: 'Processes are built from single threads by P-Term and composed by P-Connect, which cuts channels between two components.'
});
merge('g-guard', 'The guard', ['g-acts', 'g-rules', 'g-proc'], {
  why: 'Lock freedom needs every thread to keep acting. The guard rejects recursion that can loop without a session action.'
});
order('typing', ['t-lf-credits', 't-lf-tickets', 't-lf-guard', 't-lf-wf', 't-judgment', 't-contexts', 't-side', 't-agecap', 'r-base', 'r-fun', 'r-data', 'r-boxes', 'r-ex', 't-consts', 'r-act', 'r-threads', 'r-new', 't-subs', 'p-typing', 'g-guard']);

// ---- semantic typing ----
merge('ct-costs', 'Step costs', ['ct-two', 'ct-table']);
merge('v-rel', 'The value relation', ['v-base', 'v-arrow', 'v-box', 'v-ex', 'v-size'], {
  caption: R`Each rule is one clause of $V$, read as an equivalence, by recursion on the type inside the level. $\Theta$ maps exactly the ends the value owns. A closure is safe to call in every later world, at every lower level, with every argument and every caller future above $u$. A thunk that $\mathsf{spawn}$ runs is a closure at upper point $\top$, read at the empty future because the child has nothing after it. A box owns no end and is safe when $\mathsf{thunk}(e) = \lambda\_.\,e[!e]$ is safe at every instance. An existential is a value of its body at witness points whose facts hold.`,
  why: 'What a safe value is at each type. Arrows and boxes quantify over every later world and lower level, which is what makes the relation compositional.'
});
merge('e-rel', 'The term relation', ['e-body', 'rel-atcost'], {
  caption: R`A term in $E$ is a value in $V$ when irreducible, ready when reducible, and every step meets its obligation. A successor is read at the level the step leaves, inside the least fixpoint $X$ of level $n$.`
});
merge('e-obl', 'Obligations of term steps', ['e-obl-admin', 'e-obl-msg', 'e-obl-other'], {
  caption: R`Each step $e \xrightarrow{\alpha} e'$ of a term holding $\Theta$ must meet $\mathsf{Obl}_\alpha(e')$. A $\beta$ step keeps the ends, a spawn gives the child exactly the ends of its thunk, a creation adds two dual ends at a fresh root or a field. A send gives away exactly the ends of its payload, a receive is safe for every incoming value, a close drops the end, a choice moves it to the field of the branch, and a link drops two dual ends.`,
  why: 'The obligations say what each step does to ownership and points. They are the only place the relation looks at the step labels.'
});
merge('rd', 'Readiness', ['rd-term', 'rd-proc'], {
  why: 'Readiness is the progress half of the relation, the condition on a stuck thread or process that adequacy turns into deadlock freedom.'
});
merge('p-rel', 'The process relation', ['p-body', 'p-fuse']);
merge('p-obls', 'Obligations of process steps', ['p-obl', 'p-msg']);
merge('fu', 'Fuel', ['fu-def', 'fu-fsem'], {
  caption: R`$e \in F^N_\alpha\llbracket \Phi \vdash \sigma\ !\ d\rrbracket$ says that the thread $e$, holding the ends $\Phi$, each with its protocol, counter and tickets $S^f_m$, has fuel at the ordinal index $\alpha$ to return at $\sigma$ within $d$ actions. At $\alpha > 0$ it returns a value in $FV$, or every step meets its fuel obligation at every $\beta < \alpha$. An action on $o$ asks $o$ held and not idle and a positive counter on every other live end and on the frame, then sets $o$ back to its tickets and decrements the other counters, $\Phi{\downarrow}[o \mapsto S^{m}_{m}]$. A thread has fuel, $\mathsf{fsem}$, when it has fuel at every index with every end at its tickets. Fuel reads no point, no world and no relation.`,
  why: 'Fuel is the lock-free half of a thread, its counters and tickets, kept apart from the relation so that it reads no point and no world. Lock-free adequacy measures waiting with it.'
});
merge('fu-obls', 'Fuel obligations', ['fu-act', 'fu-obl-int', 'fu-obl'], {
  caption: R`Internal steps decrement no counter. A new channel starts each end at its tickets, a spawn transfers the ends of the thunk to the child with counters one lower, and a link drops two dual ends whose counters exceed the partner bounds of each other. Every action uses one unit of the frame, advances the protocol of $o$, resets the counter of $o$ to its tickets and decrements the counters of the other ends. A send transfers its payload ends with counters one lower, and a receive continues for every value in $FV$ that may arrive.`
});
merge('soup', 'The lock-free process relation', ['sp-state', 'sp-inv'], {
  caption: R`An annotated configuration $a = (q, K)$ is a configuration with an ownership map $K$ from held ends to holding thread, point, counter and tickets. It is in the lock-free process relation at index $\alpha$ when every thread is in the relation $E[\kappa_L]$ at the ends it owns and has fuel at their counters. The rest, $\mathsf{consistent}$ keeps $K$, $A$ and $\Pi$ in agreement. The lock-free process relation is the only place fuel is used.`,
  why: 'The lock-free process relation joins the two halves of every thread, its relation at $\\kappa_L$ and its fuel, over one ownership map fixed outside the level. Lock-free adequacy reads the counters and points it records.'
});
merge('sj-all', 'Semantic judgments', ['sj', 'sp-lf'], {
  why: 'The semantic judgments are what the fundamental theorems conclude and what adequacy consumes. \\annp{The lock-free judgment is the lock-free process relation at every ordinal index, with the bound $N$ chosen once and the annotated configuration chosen at each index.}'
});
order('semantic', ['sr-reading', 'ct-costs', 'v-rel', 'e-rel', 'e-obl', 'rd', 'p-rel', 'p-obls', 'fu-vs', 'fu', 'fu-obls', 'fv', 'soup', 'sj-all']);

// ---- theorems ----
merge('th-terms', 'Lemmas about terms', ['th-sound-src', 'th-fund-term', 'th-bind', 'th-cost'], {
  caption: R`The statements the process theorems are built from. A single closed program is sound as a one-thread process. Typing a term implies the semantic term judgment, and $E$ is closed under evaluation frames, which every rule with a subterm uses. \annp{With the guard a typed term is in the relation at $\kappa_L$, and a typed term at a finite counter bound has fuel.}`,
  why: 'They are the per-thread layer under the process results. Each is proved once, rule by rule, and used by the fundamental theorem for processes.'
});
merge('th-adeq', 'Adequacy', ['th-adequacy', 'th-lf-adequacy'], {
  caption: R`For strict $W$, a closed process in the semantic judgment is deadlock free. \annp{For strict and well-founded $W$, a closed process in the lock-free judgment is lock free, and every thread progresses on every weakly fair maximal run.}`,
  why: 'Adequacy is the only place the relation meets the safety property.'
});
order('theorems', ['th-chain', 'th-sound', 'th-compose', 'th-fund-proc', 'th-adeq', 'th-conserv', 'th-terms']);

// decided or proposed on the map, not yet in the Rocq: the block shows a "planned" tag with this text
const NEW2 = 'Plain new, with position, facts and the tickets of its ends in its type and worlds that grow, is planned (docs/redesign/pending.md, entry 2). The Rocq creates with new_ℓ at generated roots of families with laws Λ_ℓ fixed in the world, its ends at N/2 and N − N/2 tickets, and with new_κ o at a field, its ends at the tickets m of o and N − m.';
const TRANSFINITE = 'Transfinite step indices are planned (docs/redesign/check-transfinite.md). Indices are ordinals α, a step of cost c obliges the successor at every β with β + c ≤ α, the creation choice is an ordinary existential inside O-New, and lock-free adequacy takes excluded middle and choice as hypotheses. The creation choice χ of the proposal of 2026-11-20 is gone. The Rocq still indexes by natural numbers.';
const planned = { 'fv': TRANSFINITE, 'v-rel': TRANSFINITE,
  'syn-terms': NEW2, 'syn-points': NEW2, 'sem-labels': NEW2, 'sem-head': NEW2, 'sem-proc': NEW2,
  't-consts': NEW2, 'w-world': NEW2, 'w-order': NEW2, 'w-ext': NEW2, 'r-new': NEW2, 'e-obl': NEW2 + ' ' + TRANSFINITE,
  'soup': NEW2 + ' ' + TRANSFINITE,
  'sj-all': NEW2 + ' ' + TRANSFINITE,
  'fu-vs': TRANSFINITE, 'fu': TRANSFINITE, 'fu-obls': NEW2 + ' ' + TRANSFINITE,
  'sr-reading': TRANSFINITE, 'e-rel': TRANSFINITE,
  'th-chain': TRANSFINITE, 'th-adeq': TRANSFINITE,
};
for (const [id, why] of Object.entries(planned)) set(id, b => { b.planned = why; });

// every caption sentence about the lock-free mode hides in the deadlock-free mode
for (const s of sections) for (const b of s.blocks) if (b.modes.includes('df')) b.caption = lfSentences(b.caption);

// after about.js: point every "used in" list at the blocks that exist now
function remap() {
  const ids = new Set(sections.flatMap(s => s.blocks.map(b => b.id)));
  for (const s of sections) for (const b of s.blocks) if (b.about && b.about.used)
    b.about.used = [...new Set(b.about.used.map(x => alias[x] || x))].filter(x => x !== b.id && ids.has(x));
}
module.exports = { alias, remap };
