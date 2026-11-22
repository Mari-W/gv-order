// Checker extension of the GV relation map (docs/explorer/map.json). Builds on tools/proof-map.
//
// 1. The author's writing rules, ported from .claude/tools/lint-map.py and the prose checks of the
//    retired gen/gen.js. The base checker already runs semicolon, not X but, this/here opener,
//    colon, since and the sentence length, so this module adds the rest.
// 2. DF-LEAK, ported from gen/gen.js: nothing about the lock-free view (credits, costs, ticket
//    needs, the guard, fuel, ranked worlds, lock freedom itself) shows in the deadlock-free mode,
//    in a formula, a caption, a table or the prose of a note a deadlock-free reader reaches.
// 3. Unicode math in prose outside $..$, as gen/gen.js counted it.
// 4. The verdicts of examples, x-gv-accepts: judgments df, sem and lf, a boolean ok, and Rocq
//    names behind them that exist.
'use strict';

// the full list of gen/gen.js
const LEAK = [
  /lock[- ]free|lock freedom|\\kappa_L|\bfuel\b|\branked\b|excluded middle|functional choice/i,
  /_(?:\{[^{}]*\}|[A-Za-z])\^\{[^{}]*,/,
  /\^\{\\sym\{[^}]*\}\{[ab]/,
  /\^\{[ab](_|'|\}|\s*\+)/,
  /(?<!\\!)\\triangleright\}*\s*(c|\\infty|\d)/,
  /\\vartheta/,
  /\[c\s*;/,
  /\\hat\s*1/,
  /\\mathsf\{(tok|meets|tix|tspawn|tlink|tseq)\}/,
  /\\vdash\}*\^\{N\}/,
  /credit/i
];
// Greek letters, arrows, relations, sub- and superscripts and combining marks
const UMATH = /[Ͱ-Ͽ⁰-₟←-⋿⟨-⟯⨀-⫿̀-ͯ]/;
const JUDGMENTS = ['df', 'sem', 'lf'];

module.exports = {
  proseRules: [
    // lint-map.py, "metaphor". leverage, crucial, notably, essentially, simply and indeed are in
    // the base rule "filler word" and left out here, so a hit counts once.
    { name: 'metaphor', re: /\b(paid|pays?|price|cheap|for free|in return|budget|spend|spends|spent|lives? in|rests? on|reach(es)?|sits?|lands? in|stands? at|talks?|tells?|knows?|sees?|answers?|promises?|behaves?|carries|carry|travels?|hands? (over|on)|owes?|thus|just)\b/gi, why: 'Say what the definition does, without a picture.' },
    { name: 'like', re: /\b[Ll]ike\b(?! to)/g, why: 'Write "such as" or name the case.' },
    { name: 'pronoun ending', re: /\b(it|them)\.(\s|$)/g, why: 'End on the noun that carries the weight.' },
    { name: 'every/any/all', re: /\b(every|any|all)\b/gi, why: 'Quantify only where the definition quantifies.' },
    // lint-map.py, "coined lingo", with the words gen/gen.js banned (slot, gate, priority)
    { name: 'coined lingo', re: /\b(soup|bookkeeping|hops?|hand-overs?|handed|ticks?|ticked|refill(s|ed)?|spare|holders?|starves?|waiters?|fueled|live relation|partner (end|point)s?|chatter|glue|slots?|gates?|priority)\b/gi, why: 'Use the standard term of the field.' }
  ],
  proseSkip: ['Nothing. It is a definition.'],
  categories: {
    'gv:df-leak': 'lock-free material visible in the deadlock-free mode (DF-LEAK)',
    'gv:unicode-math': 'a Greek letter, arrow or relation in prose outside $..$',
    'gv:accepts': 'a verdict of an example names an unknown judgment or has no boolean ok',
    'gv:verdict-name': 'a Rocq name behind a verdict badge does not exist'
  },
  check(ctx) {
    const { tex: T, report } = ctx;
    const dfKeys = new Set();
    const leak = (where, s) => {
      const t = T.resolve(String(s || ''), 'df');
      for (const r of LEAK) if (r.test(t)) { report('gv:df-leak', 'error', where, String(r)); return; }
    };
    const keysOf = t => { for (const x of T.syms(T.resolve(String(t || ''), 'df'))) dfKeys.add(x.key); };
    for (const { where, it, kind } of ctx.items) {
      if (kind !== 'block' || (it.modes && !it.modes.includes('df'))) continue;
      const f = (it.variants && it.variants.df) || it.formula;
      if (f) { leak(where, f); keysOf(f); }
      leak(where + '.caption', it.caption);
      for (const s of T.proseMath(it.caption || '', 'df')) keysOf(s);
      // a table: the rows a deadlock-free reader sees, their formulas, labels and sentences
      for (const r of T.tableRows(it, 'df')) {
        if (r.label) leak(where + '.row label', r.label);
        for (const c of T.cellsOf(r)) {
          if (typeof c.formula === 'string') { leak(where + '.row', c.formula); keysOf(c.formula); }
          if (typeof c.text === 'string') { leak(where + '.row', c.text); for (const s of T.proseMath(c.text, 'df')) keysOf(s); }
        }
        if (r.labelKey) dfKeys.add(r.labelKey);
      }
      for (const h of (it.table && it.table.header) || []) leak(where + '.head', h);
    }
    for (const k of dfKeys) {
      const n = ctx.notes[k]; if (!n) continue;
      for (const f of ['signature', 'meaning', 'why', 'breaks', 'example']) leak(`note ${k}.${f}`, n[f]);
      for (const a of n.args || []) if (!a.modes || a.modes.includes('df')) leak(`note ${k}.arg`, a.name + ' ' + a.meaning);
    }
    // Unicode math outside $..$ and `..`
    for (const [where, t] of ctx.prose) {
      const words = String(t).replace(/(?<!\\)\$[^$]*\$/g, ' ').replace(/`[^`]*`/g, ' ');
      const m = UMATH.exec(words);
      if (m) report('gv:unicode-math', 'warning', where, `"${m[0]}" outside $..$`);
    }
    // verdicts of examples
    for (const x of ctx.examples) for (const [m, a] of Object.entries(x['x-gv-accepts'] || {})) {
      if (!JUDGMENTS.includes(m) || !a || typeof a.ok !== 'boolean') report('gv:accepts', 'error', `example ${x.id}`, m);
      // the text mixes names and prose: names are the snake_case words
      if (ctx.idx) for (const n of String((a && a.rocq) || '').match(/\b[\p{L}][\p{L}\p{N}']*_[\p{L}\p{N}_']*/gu) || [])
        if (!ctx.idx.byName.has(n)) report('gv:verdict-name', 'error', `example ${x.id} ${m}`, n);
    }
  }
};
