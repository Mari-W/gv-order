// Checker extension of the GV relation map.
// 1. Coined lingo the author forbids in this project.
// 2. Nothing about annotations (credits, costs, ticket needs, the guard) shows in the
//    deadlock-free mode, in formulas or in the prose of notes a deadlock-free reader reaches.
// 3. The Rocq names behind the verdict badges of examples exist.
'use strict';
const LEAK = [/\^\{\\sym\{[^}]*\}\{[ab]/, /\^\{[ab](_|'|\}|\s*\+)/, /(?<!\\!)\\triangleright\}*\s*(c|\\infty|\d)/, /\\vartheta/, /\[c\s*;/, /\\hat\s*1/, /\\mathsf\{(tok|meets|tix|tspawn|tlink|tseq)\}/, /\\vdash\}*\^\{N\}/, /credit/i];

module.exports = {
  proseRules: [
    { name: 'coined lingo', re: /\b(soup|bookkeeping|hops?|hand-overs?|handed|ticks?|ticked|refill(s|ed)?|spare|holders?|starves?|waiters?|fueled|live relation|partner (end|point)s?|chatter|glue)\b/gi, why: 'Use the standard term (docs/explorer lint map).' }
  ],
  proseSkip: ['Nothing. It is a definition.'],
  categories: {
    'gv:df-leak': 'lock-free material visible in the deadlock-free mode',
    'gv:verdict-name': 'a Rocq name behind a verdict badge does not exist'
  },
  check(ctx) {
    const { tex: T, report } = ctx;
    const dfKeys = new Set();
    const leak = (where, s) => { const t = T.resolve(String(s || ''), 'df'); for (const r of LEAK) if (r.test(t)) { report('gv:df-leak', 'error', where, String(r)); return; } };
    for (const { where, it, kind } of ctx.items) {
      if (kind !== 'block' || (it.modes && !it.modes.includes('df'))) continue;
      const f = (it.variants && it.variants.df) || it.formula;
      leak(where, f);
      leak(where + '.caption', it.caption);
      for (const x of T.syms(T.resolve(f, 'df'))) dfKeys.add(x.key);
    }
    for (const k of dfKeys) {
      const n = ctx.notes[k]; if (!n) continue;
      for (const f of ['signature', 'meaning', 'why', 'breaks', 'example']) leak(`note ${k}.${f}`, n[f]);
      for (const a of n.args || []) if (!a.modes || a.modes.includes('df')) leak(`note ${k}.arg`, a.name + ' ' + a.meaning);
    }
    if (ctx.idx) for (const x of ctx.examples) for (const [m, a] of Object.entries(x['x-gv-accepts'] || {}))
      // the text mixes names and prose: names are the snake_case words
      for (const n of String(a.rocq || '').match(/\b[\p{L}][\p{L}\p{N}']*_[\p{L}\p{N}_']*/gu) || [])
        if (!ctx.idx.byName.has(n)) report('gv:verdict-name', 'error', `example ${x.id} ${m}`, n);
  }
};
