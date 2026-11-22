#!/usr/bin/env node
// Compare the old explorer data (attic/data.js, the last output of attic/gen/) with map.json, item
// by item and mode by mode, and report everything the move to proof-map/1 lost or changed.
//
// usage: node docs/explorer/attic/compare.js [--list]
//
// For each mode (df, lf) it renders what a reader of the old page and of the new page sees:
//   sections   id, title, intro
//   blocks     which blocks a mode shows, their order, title, formula (variants and tables
//              included), the parts coloured as lock-free, the hover keys, caption, why, breaks,
//              example, usedIn, Rocq citations
//   notes      title, signature, arguments (with the lock-free ones), meaning, why, breaks,
//              example, usedIn, Rocq citations
//   examples   which examples a mode shows, title, lead, code, meaning, verdict badges, citations
// A formula of a non-table block must match character for character after the markup is renamed
// (\htmlData{k=K} to \sym{K}, \annot to \inmode{lf}, \annraw to \inmodeplain{lf}, \dfo to
// \inmodeplain{df}). A table must hold the same symbols in the same order once layout (&, \\,
// \text, spacing, braces, $) is removed. Prose must match exactly. Known, intended changes are
// listed under INTENDED and counted apart.
'use strict';
const fs = require('fs');
const path = require('path');
const here = __dirname;
const T = require(path.join(here, '..', '..', '..', 'tools/proof-map/lib/tex.js'));
const LIST = process.argv.includes('--list');

const src = fs.readFileSync(path.join(here, 'data.js'), 'utf8');
const OLD = JSON.parse(src.slice(src.indexOf('=') + 1).trim().replace(/;\s*$/, ''));
const NEW = JSON.parse(fs.readFileSync(path.join(here, '..', 'map.json'), 'utf8'));
const MODES = ['df', 'lf'];

// ---------- rendering ----------
const C0 = '⟦', C1 = '⟧';           // ⟦ ⟧ around a coloured part
function group(s, open) { return T.closeGroup(s, open); }
// old markup for one mode: \annot{X} and \annp{X} coloured in lf, \annraw{X} plain in lf, \dfo{X} outside lf
function oldRender(s, m) {
  s = String(s ?? ''); let out = '', i = 0;
  for (;;) {
    const r = /\\(annot|annraw|annp|dfo)\{/.exec(s.slice(i)); if (!r) return out + s.slice(i);
    const j = i + r.index, open = j + r[0].length - 1, k = group(s, open);
    const inner = oldRender(s.slice(open + 1, k - 1), m);
    const w = r[1];
    out += s.slice(i, j) + (w === 'dfo' ? (m !== 'lf' ? inner : '') : m !== 'lf' ? '' : w === 'annraw' ? inner : C0 + inner + C1);
    i = k;
  }
}
const oldTeX = s => String(s ?? '').replace(/\\htmlData\{k=([A-Za-z0-9.\-_]+)\}\{/g, '\\sym{$1}{');
const O = (s, m) => oldRender(oldTeX(s), m);
const N = (s, m) => T.resolve(String(s ?? ''), m, { colour: x => C0 + x + C1 });
// layout-free form of TeX and prose, for tables
const flat = s => String(s ?? '')
  .replace(/\\sym\s*\{[^}]*\}/g, '').replace(/\\text\s*(?=\{)/g, '').replace(/\\begin\{array\}\{[^}]*\}|\\end\{array\}|\\hline/g, '')
  .replace(/\\\\(\[[^\]]*\])?/g, '').replace(/\\(qquad|quad)(?![A-Za-z])|\\[ ,;!]/g, '').replace(/[&${}\s]/g, '').replace(/[⟦⟧]/g, '');
const keys = s => [...new Set([...String(s ?? '').matchAll(/\\sym\s*\{([^}]*)\}/g)].map(x => x[1]))].sort();
const coloured = s => { const out = []; const re = new RegExp(C0 + '([^' + C0 + C1 + ']*)' + C1, 'g'); let t = String(s); for (let r; (r = re.exec(t));) out.push(flat(r[1])); return out.join('|'); };

// ---------- findings ----------
const INTENDED = [
  // [what, test] — a difference accepted because the phase C brief asks for it
  ['W\\^{\\prime} in prose became W^{\\prime}, a TeX error MathJax rejects', (o, n) => o.split('W\\^{\\prime}').join('W^{\\prime}') === n],
  ['the overview tables sr-reading, fu-vs and soup became native tables', null]
];
const diffs = [], intended = new Map(), counts = {};
const count = k => { counts[k] = (counts[k] || 0) + 1; };
function same(where, o, n, cmp = (a, b) => a === b) {
  count('compared');
  if (cmp(o, n)) return true;
  for (const [what, test] of INTENDED) if (test && typeof o === 'string' && typeof n === 'string' && test(o, n)) { intended.set(what, (intended.get(what) || 0) + 1); return true; }
  diffs.push({ where, o: String(o).slice(0, 300), n: String(n).slice(0, 300) });
  return false;
}
const eqJSON = (a, b) => JSON.stringify(a) === JSON.stringify(b);

// citations: every word of the old Rocq text must appear among the new citations and deviations
const words = s => new Set((String(s ?? '').match(/[A-Za-z_][\w'.]*/g) || []).map(w => w.toLowerCase().replace(/\.+$/, '')));
function citesSame(where, oldRocq, it) {
  const have = new Set();
  for (const r of it.source || []) { for (const w of words(r.file)) have.add(w); for (const nm of r.names) for (const w of words(nm)) have.add(w); for (const w of words(r.qualifier)) have.add(w); }
  for (const d of it.deviations || []) for (const w of words(d.kind + ' ' + (d.names || []).join(' ') + ' ' + d.reason + ' ' + (d.part || ''))) have.add(w);
  for (const w of words(oldRocq)) { count('citation words'); if (!have.has(w) && !have.has(w.replace(/\.v$/, ''))) diffs.push({ where: where + ' rocq', o: w, n: '(missing)' }); }
}

// ---------- sections and blocks ----------
const nb = new Map(NEW.sections.flatMap(s => s.blocks.map(b => [b.id, b])));
const tables = new Set();
same('section ids', OLD.sections.map(s => s.id).join(' '), NEW.sections.map(s => s.id).join(' '));
for (const os of OLD.sections) {
  const ns = NEW.sections.find(s => s.id === os.id); if (!ns) { diffs.push({ where: 'section ' + os.id, o: 'present', n: 'missing' }); continue; }
  same(`section ${os.id}.title`, os.title, ns.title);
  for (const m of MODES) same(`section ${os.id}.intro (${m})`, O(os.intro, m), N(ns.intro, m));
  for (const m of MODES) same(`section ${os.id} blocks (${m})`, os.blocks.filter(b => (b.modes || MODES).includes(m)).map(b => b.id).join(' '), ns.blocks.filter(b => !b.modes || b.modes.includes(m)).map(b => b.id).join(' '));
  for (const ob of os.blocks) {
    const b = nb.get(ob.id); if (!b) { diffs.push({ where: 'block ' + ob.id, o: 'present', n: 'missing' }); continue; }
    count('blocks');
    const w = `block ${ob.id}`;
    same(w + '.title', ob.title, b.title);
    const a = ob.about || {};
    same(w + '.usedIn', a.used || [], b.usedIn || [], eqJSON);
    citesSame(w, ob.rocq, b);
    if (ob.planned) same(w + '.planned', true, (b.deviations || []).some(d => d.kind === 'planned' && d.reason === ob.planned));
    for (const m of MODES) {
      if (!(ob.modes || MODES).includes(m)) continue;
      count('block views');
      const ot = O((ob.variants && ob.variants[m]) || ob.tex, m);
      let nt;
      if (b.table && !(b.variants && b.variants[m])) {
        tables.add(b.id);
        // the table as a reader sees it, in reading order: head, then per row the label and the cells
        const t = b.table, parts = [...(t.header || []).map(h => N(h, m))];
        for (const r of T.tableRows(b, m)) {
          const row = [r.label ? N(r.label, m) : '', ...T.cellsOf(r).map(c => N(c.formula !== undefined ? c.formula : c.text, m))].join(' ');
          parts.push(r.modes && r.modes.length < MODES.length ? C0 + row + C1 : row);
          if (r.labelKey) parts.push('\\sym{' + r.labelKey + '}{}');
        }
        nt = parts.join(' ');
        same(w + ` table symbols (${m})`, flat(ot), flat(nt));
        same(w + ` table colours (${m})`, coloured(ot).replace(/\|/g, ''), coloured(nt).replace(/\|/g, ''));
      } else {
        nt = N((b.variants && b.variants[m]) || b.formula, m);
        same(w + ` formula (${m})`, ot, nt);
        same(w + ` colours (${m})`, coloured(ot), coloured(nt));
      }
      same(w + ` hovers (${m})`, keys(ot).join(' '), keys(nt).join(' '));
      count('hover keys ' + m); counts['hover keys ' + m] += keys(nt).length - 1;
      for (const f of ['caption']) same(w + `.${f} (${m})`, O(ob[f], m), N(b[f], m));
      for (const f of ['why', 'breaks', 'example']) same(w + `.${f} (${m})`, O(a[f], m), N(b[f], m));
    }
  }
}
same('block count', OLD.sections.reduce((x, s) => x + s.blocks.length, 0), NEW.sections.reduce((x, s) => x + s.blocks.length, 0));

// ---------- notes ----------
const onotes = Object.entries(OLD.notes).filter(([k]) => !k.startsWith('@'));
same('note keys', onotes.map(([k]) => k).sort().join(' '), Object.keys(NEW.notes).sort().join(' '));
let addedDevs = 0;
for (const [k, on] of onotes) {
  const n = NEW.notes[k]; if (!n) continue;
  count('notes');
  const w = `note ${k}`;
  same(w + '.usedIn', on.used || [], n.usedIn || [], eqJSON);
  citesSame(w, on.rocq, n);
  addedDevs += (n.deviations || []).filter(d => ['renamed', 'merged'].includes(d.kind)).length;
  for (const m of MODES) {
    same(w + `.title (${m})`, O(on.title || k, m), N(n.title, m));
    same(w + `.signature (${m})`, O(on.sig, m), N(n.signature, m));
    for (const [of, nf] of [['what', 'meaning'], ['why', 'why'], ['breaks', 'breaks'], ['example', 'example']]) same(w + `.${nf} (${m})`, O(on[of], m), N(n[nf], m));
    const oa = (on.args || []).filter(x => !x.ann || m === 'lf').map(x => O(x.name, m) + ' :: ' + O(x.meaning, m));
    const na = (n.args || []).filter(x => !x.modes || x.modes.includes(m)).map(x => N(x.name, m) + ' :: ' + N(x.meaning, m));
    same(w + `.args (${m})`, oa.join('\n'), na.join('\n'));
  }
}

// ---------- examples ----------
same('example ids', (OLD.examples || []).map(x => x.id).join(' '), (NEW.examples || []).map(x => x.id).join(' '));
for (const ox of OLD.examples || []) {
  const x = (NEW.examples || []).find(e => e.id === ox.id); if (!x) continue;
  count('examples');
  const w = `example ${ox.id}`;
  same(w + '.title', ox.title, x.title);
  same(w + '.code', ox.code, x.code);
  same(w + '.modes', (ox.modes || MODES).join(' '), (x.modes || MODES).join(' '));
  same(w + '.badges', ox.accepts || null, x['x-gv-accepts'] || null, eqJSON);
  citesSame(w, ox.rocq, x);
  for (const m of MODES) { same(w + `.lead (${m})`, O(ox.lead, m), N(x.lead, m)); same(w + `.meaning (${m})`, O(ox.shows, m), N(x.meaning, m)); }
}

// ---------- report ----------
const nOld = OLD.sections.reduce((x, s) => x + s.blocks.length, 0);
console.log('old data.js   ', `${OLD.sections.length} sections, ${nOld} blocks, ${onotes.length} notes, ${(OLD.examples || []).length} examples`);
console.log('new map.json  ', `${NEW.sections.length} sections, ${NEW.sections.reduce((x, s) => x + s.blocks.length, 0)} blocks, ${Object.keys(NEW.notes).length} notes, ${(NEW.examples || []).length} examples`);
console.log('compared      ', `${counts.compared} fields: ${counts['block views']} block views (block x mode), ${counts.notes} notes x 2 modes, ${counts.examples} examples x 2 modes, ${counts['citation words']} citation words, hover keys df ${counts['hover keys df']} lf ${counts['hover keys lf']}`);
console.log('tables        ', [...tables].join(', '), 'compared by symbols in order, colours and hovers');
console.log('added         ', `${addedDevs} renamed or merged deviations on notes`);
for (const [what, n] of intended) console.log('intended      ', `${n} x ${what}`);
console.log('differences   ', diffs.length);
for (const d of LIST ? diffs : diffs.slice(0, 20)) console.log(`  ${d.where}\n    old: ${d.o}\n    new: ${d.n}`);
if (!LIST && diffs.length > 20) console.log(`  … ${diffs.length - 20} more (--list)`);
process.exit(diffs.length ? 1 : 0);
