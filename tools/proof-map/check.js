#!/usr/bin/env node
// Check a proof map against its schema, against itself and against the Rocq code it cites.
//
// usage: node check.js <map.json> [options]
//   --root DIR        Rocq source tree (default: source.root of the map, relative to the map file)
//   --list [CAT]      print every finding, or every finding of one category
//   --max N           findings printed per category without --list (default 3)
//   --json FILE       write all findings as JSON
//   --stamp [IDS]     record the current statement fingerprints as reviewed, for all items or the
//                     comma-separated block, note and example ids, and rewrite the map file
//   --mathjax DIR     a node_modules directory with mathjax-full, to render every formula
//   --strict          exit with status 1 on warnings too
//
// Exit status 1 when an error is found, 0 otherwise. No network access.
'use strict';
const fs = require('fs');
const path = require('path');
const { indexTree, statementHash, lookup } = require('./lib/rocq-index');
const T = require('./lib/tex');
const P = require('./lib/prose-rules');
const { validate } = require('./lib/validate');

// ---------- arguments ----------
const argv = process.argv.slice(2);
const flag = n => { const i = argv.indexOf(n); if (i < 0) return false; argv.splice(i, 1); return true; };
const opt = n => { const i = argv.indexOf(n); if (i < 0) return undefined; const v = argv[i + 1]; argv.splice(i, v === undefined || v.startsWith('--') ? 1 : 2); return v === undefined || v.startsWith('--') ? true : v; };
const o = { root: opt('--root'), list: opt('--list'), max: Number(opt('--max') || 3), json: opt('--json'), stamp: opt('--stamp'), mathjax: opt('--mathjax'), strict: flag('--strict') };
const mapFile = argv[0];
if (!mapFile) { console.error('usage: node check.js <map.json> [--root DIR] [--list [CAT]] [--max N] [--json FILE] [--stamp [IDS]] [--mathjax DIR] [--strict]'); process.exit(2); }

const readMap = f => { const s = fs.readFileSync(f, 'utf8'); return JSON.parse(f.endsWith('.js') ? s.slice(s.indexOf('=') + 1).trim().replace(/;\s*$/, '') : s); };
const MAP = readMap(mapFile);
const mapDir = path.dirname(path.resolve(mapFile));

// ---------- findings ----------
const findings = [];
const CATS = {};
function report(cat, sev, where, msg) { findings.push({ cat, sev, where, msg }); }
function describe(cat, text) { CATS[cat] = text; }
describe('schema', 'the map does not match schema.json');
describe('dup-id', 'two sections, blocks or examples share an id');
describe('file-missing', 'a cited .v file does not exist under the source root');
describe('name-missing', 'a cited Rocq name is not defined in the cited file or anywhere');
describe('name-elsewhere', 'a cited Rocq name is defined, but in another file');
describe('external', 'a citation of a library module, not checked');
describe('unsourced', 'a block cites no Rocq definition and has no planned or unsourced deviation');
describe('note-missing', 'a formula hovers a key without a note');
describe('unhovered', 'a named symbol or relation in a formula has no hover');
describe('note-unused', 'a note no formula, signature or argument refers to');
describe('var-before-intro', 'a variable is used before a block introduces it, in reading order of a mode');
describe('prose-in-formula', 'words inside \\text in a formula');
describe('bare-word', 'a word of three or more letters set as a product of variables');
describe('dead-link', 'a usedIn entry or a [[link]] names no block or section');
describe('mode-unknown', 'a mode that the map does not declare');
describe('reason-missing', 'a deviation whose reason is missing or reads REASON MISSING');
describe('planned-no-reason', 'a formula marks a part \\planned but the item has no planned deviation');
describe('rename-undeclared', 'a hovered name differs from the Rocq names its note cites, without a deviation');
describe('statement-changed', 'a cited statement changed since it was stamped as reviewed');
describe('unreviewed', 'a citation never stamped as reviewed');
describe('uncovered', 'a constructor of a cited inductive that the map never cites');
describe('dollar', 'unbalanced $ in prose');
describe('mathjax', 'MathJax fails to render a formula');

// ---------- extensions ----------
const ext = { proseRules: [], disableProse: new Set(), proseSkip: new Set(), operators: [], checks: [] };
for (const rel of (MAP.extensions && MAP.extensions.check) || []) {
  const file = path.resolve(mapDir, rel);
  let m;
  try { m = require(file); } catch (e) { report('extension', 'error', rel, 'cannot load: ' + e.message); continue; }
  for (const r of m.proseRules || []) ext.proseRules.push(r);
  for (const n of m.disableProse || []) ext.disableProse.add(n);
  for (const s of m.proseSkip || []) ext.proseSkip.add(s);
  for (const op of m.operators || []) ext.operators.push(op);
  for (const [cat, text] of Object.entries(m.categories || {})) describe(cat, text);
  if (typeof m.check === 'function') ext.checks.push(m.check);
}

// ---------- schema ----------
const schema = JSON.parse(fs.readFileSync(path.join(__dirname, 'schema.json'), 'utf8'));
for (const e of validate(schema, MAP)) report('schema', 'error', e.split(':')[0], e.slice(e.indexOf(':') + 2));

// ---------- the items of the map ----------
const sections = MAP.sections || [];
const notes = MAP.notes || {};
const examples = MAP.examples || [];
const modeIds = MAP.modes ? MAP.modes.options.map(m => m.id) : [];
const blocks = sections.flatMap(s => (s.blocks || []).map(b => ({ s, b })));
const blockById = new Map(blocks.map(x => [x.b.id, x]));
const items = [
  ...blocks.map(({ s, b }) => ({ kind: 'block', id: b.id, where: `${s.id}/${b.id}`, it: b })),
  ...Object.entries(notes).map(([k, n]) => ({ kind: 'note', id: k, where: `note ${k}`, it: n })),
  ...examples.map(x => ({ kind: 'example', id: x.id, where: `example ${x.id}`, it: x }))
];
const rowsOf = b => (b.table && b.table.rows) || [];
const formulas = b => [b.formula, ...Object.values(b.variants || {}), ...rowsOf(b).map(r => r.formula)].filter(x => typeof x === 'string');
// the formula a reader of one mode sees, a table counting as its formulas one below the other
const formulaIn = (b, mode) => (mode && b.variants && b.variants[mode]) || b.formula || rowsOf(b).map(r => r.formula).join(' \\\\ ');
const visibleIn = (x, m) => !x.modes || x.modes.includes(m);

// ---------- ids, links, modes ----------
{
  const seen = new Map();
  for (const x of [...sections.map(s => ['section', s.id]), ...blocks.map(({ b }) => ['block', b.id]), ...examples.map(e => ['example', e.id])]) {
    if (seen.has(x[1])) report('dup-id', 'error', x[1], `${x[0]} id also used by a ${seen.get(x[1])}`);
    else seen.set(x[1], x[0]);
  }
}
const sectionIds = new Set(sections.map(s => s.id));
const linkOk = id => blockById.has(id) || sectionIds.has(id) || examples.some(e => e.id === id);
for (const { where, it } of items) for (const id of it.usedIn || []) if (!linkOk(id)) report('dead-link', 'error', where, `usedIn names ${id}`);
function proseFields() {
  const out = [];
  if (MAP.subtitle) out.push(['map subtitle', MAP.subtitle]);
  for (const c of MAP.conventions || []) out.push([`convention ${c.symbol}`, c.meaning]);
  for (const r of MAP.deviationRules || []) out.push([`deviation rule ${r.kind}`, r.reason]);
  for (const m of (MAP.modes && MAP.modes.options) || []) if (m.description) out.push([`mode ${m.id}`, m.description]);
  for (const s of sections) if (s.intro) out.push([`${s.id}.intro`, s.intro]);
  for (const { kind, where, it } of items) {
    const f = kind === 'block' ? ['caption', 'why', 'breaks', 'example'] : kind === 'note' ? ['title', 'meaning', 'why', 'breaks', 'example'] : ['lead', 'meaning'];
    for (const k of f) if (typeof it[k] === 'string' && it[k].trim()) out.push([`${where}.${k}`, it[k]]);
    for (const a of it.args || []) if (a.meaning) out.push([`${where}.arg ${a.name}`, a.meaning]);
    rowsOf(it).forEach((r, i) => { if (r.text) out.push([`${where}.row ${i + 1}`, r.text]); });
    for (const d of it.deviations || []) if (d.reason && d.reason !== 'REASON MISSING') out.push([`${where}.deviation`, d.reason]);
  }
  return out;
}
const PROSE = proseFields();
for (const [where, t] of PROSE) for (const m of t.matchAll(/\[\[([^\]|]+)(?:\|[^\]]*)?\]\]/g)) if (!linkOk(m[1].replace(/^#/, ''))) report('dead-link', 'error', where, `[[${m[1]}]]`);
{
  const known = new Set(modeIds);
  const chk = (where, ms) => { for (const m of ms) if (!known.has(m)) report('mode-unknown', 'error', where, m); };
  for (const { where, it } of items) {
    if (it.modes) chk(where, it.modes);
    if (it.variants) chk(where + ' variants', Object.keys(it.variants));
    for (const a of it.args || []) if (a.modes) chk(where + ' arg', a.modes);
    for (const t of [...formulas(it), it.signature, ...(it.args || []).map(a => a.name)]) if (t) chk(where, T.modesMentioned(t));
  }
  for (const [where, t] of PROSE) chk(where, T.modesMentioned(t));
  if (MAP.modes && !known.has(MAP.modes.default)) report('mode-unknown', 'error', 'modes.default', MAP.modes.default);
}

// ---------- deviations ----------
for (const { where, it } of items) {
  for (const d of it.deviations || []) if (!d.reason || !String(d.reason).trim() || /REASON MISSING/.test(d.reason))
    report('reason-missing', 'error', where, `${d.kind}${d.names ? ' ' + d.names.join(', ') : ''}${d.part ? ' (' + d.part.slice(0, 60) + ')' : ''}`);
  const planned = (it.deviations || []).some(d => d.kind === 'planned');
  if (!planned && [...formulas(it), it.signature || ''].some(t => /\\planned\b/.test(t))) report('planned-no-reason', 'error', where, 'formula has \\planned parts');
}

// ---------- hovers and notes ----------
const OPS = ['\\vdash', '\\vDash', '\\Vdash', '\\Vvdash', '\\models', '\\prec', '\\preccurlyeq', '\\sqsubseteq', '\\sqsupseteq', '\\sqcup', '\\sqcap', '\\uplus',
  '\\llbracket', '\\triangleright', '\\approx', '\\simeq', '\\cong', '\\equiv', '\\multimap', '\\leadsto', '\\Downarrow', '\\Uparrow', '\\rightsquigarrow', ...ext.operators];
const usedKeys = new Set();
{
  const named = new RegExp('\\\\(?:mathsf|mathit|operatorname|mathcal)\\s*\\{[^}]*\\}|' + OPS.map(x => x.replace(/\\/g, '\\\\') + '(?![a-zA-Z])').join('|'), 'g');
  for (const { where, it } of items) {
    const texs = [...formulas(it), it.signature, ...(it.args || []).map(a => a.name)].filter(Boolean);
    for (const t of texs) for (const x of T.syms(t)) {
      usedKeys.add(x.key);
      if (!notes[x.key]) report('note-missing', 'error', where, x.key);
    }
    for (const r of rowsOf(it)) if (r.labelKey) { usedKeys.add(r.labelKey); if (!notes[r.labelKey]) report('note-missing', 'error', where, r.labelKey); }
    for (const t of formulas(it)) {
      const cov = T.covered(t), miss = new Set();
      for (const m of t.matchAll(named)) if (!cov[m.index]) miss.add(m[0]);
      if (miss.size) report('unhovered', 'warning', where, [...miss].join(' '));
      for (const w of T.proseInFormula(t)) report('prose-in-formula', 'warning', where, `\\text{${w}}`);
      for (const w of new Set(T.words(t))) report('bare-word', 'warning', where, w);
    }
  }
  for (const k of Object.keys(notes)) if (!usedKeys.has(k)) report('note-unused', 'info', `note ${k}`, notes[k].title || '');
}

// ---------- variables in reading order ----------
{
  const base = s => { const t = T.tokens(s).find(x => x.t === 'var'); return t ? t.base : s.trim(); };
  const conv = new Set((MAP.conventions || []).flatMap(c => T.tokens(c.symbol).filter(x => x.t === 'var').map(x => x.base)));
  // where each variable is introduced, for the message
  const introAt = new Map();
  for (const { s, b } of blocks) for (const v of T.introducedBy(b)) if (!introAt.has(v)) introAt.set(v, `${s.id}/${b.id}`);
  const hits = new Map();
  for (const mode of modeIds.length ? modeIds : [null]) {
    const known = new Set(conv);
    for (const { s, b } of blocks) {
      if (mode && !visibleIn(b, mode)) continue;
      const tex = T.resolve(formulaIn(b, mode), mode);
      const own = T.introducedBy(b, mode);
      const { used, bound } = T.variables(tex);
      for (const v of used.keys()) {
        if (known.has(v) || own.has(v) || bound.has(v)) continue;
        const key = `${s.id}/${b.id} ${v}`;
        if (!hits.has(key)) hits.set(key, { where: `${s.id}/${b.id}`, v, modes: [] });
        hits.get(key).modes.push(mode);
      }
      for (const v of own) known.add(v);
    }
  }
  for (const h of hits.values()) {
    const later = introAt.get(h.v);
    report('var-before-intro', 'warning', h.where, `${h.v}${modeIds.length && h.modes.length < modeIds.length ? ' (' + h.modes.join(', ') + ')' : ''} ${later ? 'is introduced later in ' + later : 'is introduced by no block'}`);
  }
}

// ---------- prose ----------
{
  const active = [...P.rules, ...ext.proseRules].filter(r => !ext.disableProse.has(r.name));
  for (const [where, t] of PROSE) {
    if (ext.proseSkip.has(t.trim())) continue;
    if ((t.match(/(?<!\\)\$/g) || []).length % 2) { report('dollar', 'error', where, t.slice(0, 80)); continue; }
    for (const h of P.lint(t, active)) report('prose:' + h.rule, h.severity, where, `"${h.match}" ${h.why}`);
  }
  for (const r of active) describe('prose:' + r.name, 'prose rule. ' + (r.why || ''));
  describe('prose:sentence > ' + P.MAX_WORDS + ' words', 'prose rule. Split long sentences.');
}

// ---------- the Rocq code ----------
const rootDir = o.root ? path.resolve(o.root) : MAP.source && MAP.source.root ? path.resolve(mapDir, MAP.source.root) : null;
let idx = null;
if (!rootDir) report('file-missing', 'error', 'source.root', 'no Rocq root: set source.root in the map or pass --root');
else if (!fs.existsSync(rootDir)) report('file-missing', 'error', 'source.root', `${rootDir} does not exist`);
else idx = indexTree(rootDir);
let nRefs = 0, nReviewed = 0;
const cited = new Set();
if (idx) {
  for (const { kind, where, it } of items) {
    const devNames = new Set((it.deviations || []).flatMap(d => d.names || []));
    for (const r of it.source || []) {
      if (!/\.v$/.test(r.file)) { report('external', 'info', where, `${r.file}: ${r.names.join(', ')}`); continue; }
      const fileOk = idx.files.has(r.file);
      if (!fileOk) report('file-missing', 'error', where, r.file);
      for (const n of r.names) {
        nRefs++;
        cited.add(n);
        const e = lookup(idx, n, fileOk ? r.file : null);
        if (!e) {
          const any = lookup(idx, n, null);
          if (any && fileOk) report('name-elsewhere', 'error', where, `${n} is in ${any.file}:${any.line}, not in ${r.file}`);
          else if (!any && !devNames.has(n)) report('name-missing', 'error', where, `${r.file}: ${n}`);
          continue;
        }
        const h = statementHash(e);
        const rev = r.reviewed && r.reviewed[n];
        if (rev) { nReviewed++; if (rev !== h) report('statement-changed', 'warning', where, `${n} at ${e.file}:${e.line} (reviewed ${rev}, now ${h})`); }
        if (o.stamp && (o.stamp === true || String(o.stamp).split(',').includes(it.id || ''))) { r.reviewed = r.reviewed || {}; r.reviewed[n] = h; }
      }
    }
    if (kind === 'block' && !(it.source || []).length && !(it.deviations || []).some(d => d.kind === 'planned' || d.kind === 'unsourced'))
      report('unsourced', 'error', where, it.title);
  }
  if (nRefs - nReviewed) report('unreviewed', 'info', 'map', `${nRefs - nReviewed} of ${nRefs} cited names carry no reviewed fingerprint. Stamp them with --stamp after a review.`);
  // constructors of cited inductives that no item cites
  const parents = new Set();
  for (const n of cited) for (const e of idx.byName.get(n) || []) parents.add(e.kind === 'constructor' ? e.parent : n);
  for (const p of parents) {
    const ctors = idx.entries.filter(e => e.kind === 'constructor' && e.parent === p);
    if (ctors.length < 2 || !ctors.some(c => cited.has(c.name))) continue;
    const miss = ctors.filter(c => !cited.has(c.name)).map(c => c.name);
    if (miss.length) report('uncovered', 'info', `${ctors[0].file}: ${p}`, miss.join(', '));
  }
}

// ---------- names shown differently from the Rocq ----------
// a map-wide deviation rule covers a note by its key pattern, or because it cites a constructor
function ruleCovers(k, n) {
  return (MAP.deviationRules || []).some(r => {
    if (r.appliesTo === 'constructors') return !!idx && (n.source || []).some(ref => ref.names.some(name => (idx.byName.get(name) || []).some(e => e.kind === 'constructor')));
    return ((r.appliesTo && r.appliesTo.keys) || []).some(p => new RegExp('^' + p.replace(/[.+?^${}()|[\]\\]/g, '\\$&').replace(/\*/g, '.*') + '$').test(k));
  });
}
{
  const norm = s => s.toLowerCase().normalize('NFD').replace(/[^a-z0-9]/g, '');
  const shown = new Map();
  for (const { it } of items) for (const t of [...formulas(it), it.signature || '']) for (const x of T.syms(t)) {
    // the body without nested hovers, which belong to other notes
    let body = x.body;
    for (const y of T.syms(body).reverse()) body = body.slice(0, y.start) + body.slice(y.end);
    for (const m of body.matchAll(/\\(?:mathsf|operatorname|textsf)\s*\{([^}]*)\}/g)) {
      if (!shown.has(x.key)) shown.set(x.key, new Set());
      shown.get(x.key).add(m[1]);
    }
  }
  for (const [k, names] of shown) {
    const n = notes[k];
    if (!n || !(n.source || []).length) continue;
    if ((n.deviations || []).some(d => ['renamed', 'notation', 'simplified', 'merged'].includes(d.kind))) continue;
    if (ruleCovers(k, n)) continue;
    const rocq = n.source.flatMap(r => r.names).map(norm);
    const disp = [...names].map(s => s.replace(/\\[A-Za-z]+|[{}\\_^]/g, '')).filter(s => /[A-Za-z]{2,}/.test(s));
    if (!disp.length) continue;
    if (!disp.some(d => rocq.some(r => r === norm(d) || r.startsWith(norm(d)) || r.endsWith(norm(d)))))
      report('rename-undeclared', 'warning', `note ${k}`, `shown as ${disp.map(d => '\\mathsf{' + d + '}').join(', ')}, Rocq ${n.source.flatMap(r => r.names).join(', ')}`);
  }
}

// ---------- MathJax ----------
function mathjax() {
  const dirs = [o.mathjax, process.env.PROOF_MAP_MATHJAX, path.join(__dirname, 'node_modules')].filter(x => typeof x === 'string');
  let base = null;
  for (const d of dirs) if (fs.existsSync(path.join(d, 'mathjax-full', 'js', 'mathjax.js'))) { base = path.join(d, 'mathjax-full', 'js'); break; }
  if (!base) return false;
  const { mathjax: MJ } = require(path.join(base, 'mathjax.js'));
  const { TeX } = require(path.join(base, 'input/tex.js'));
  const { SVG } = require(path.join(base, 'output/svg.js'));
  const { liteAdaptor } = require(path.join(base, 'adaptors/liteAdaptor.js'));
  const { RegisterHTMLHandler } = require(path.join(base, 'handlers/html.js'));
  const { AllPackages } = require(path.join(base, 'input/tex/AllPackages.js'));
  RegisterHTMLHandler(liteAdaptor());
  const macros = Object.assign({}, (MAP.tex && MAP.tex.macros) || {});
  const doc = MJ.document('', { InputJax: new TeX({ packages: AllPackages, macros, formatError: (j, e) => { throw e; } }), OutputJax: new SVG() });
  const toMJ = (t, m) => T.resolve(t, m, { colour: (x, md) => `\\class{mode-${md}}{${x}}` }).replace(/\\sym\s*\{([^}]*)\}\s*\{/g, (_, k) => `\\class{k-${k.replace(/[^A-Za-z0-9_-]/g, '_')}}{`).replace(/\\planned\s*\{/g, '\\class{planned}{');
  for (const mode of modeIds.length ? modeIds : [null]) for (const { where, it } of items) {
    if (mode && !visibleIn(it, mode)) continue;
    const t = (mode && it.variants && it.variants[mode]) || it.formula;
    for (const [what, x] of [['formula', t], ['signature', it.signature], ...rowsOf(it).map((r, i) => ['row ' + (i + 1), r.formula])]) {
      if (!x) continue;
      try { doc.convert(toMJ(x, mode), { display: true }); } catch (e) { report('mathjax', 'error', `${where} ${what}${mode ? ' (' + mode + ')' : ''}`, String(e.message).slice(0, 140)); }
    }
  }
  return true;
}
const mjRan = mathjax();

// ---------- extension checks ----------
const ctx = { map: MAP, mapDir, idx, items, blocks, notes, sections, examples, modeIds, report, describe, tex: T, prose: PROSE, formulas };
for (const c of ext.checks) { try { c(ctx); } catch (e) { report('extension', 'error', 'check', e.stack.split('\n').slice(0, 2).join(' ')); } }

// ---------- stamp ----------
if (o.stamp && idx) {
  fs.writeFileSync(mapFile, JSON.stringify(MAP, null, 1) + '\n');
  console.log('stamped reviewed fingerprints into', mapFile);
}

// ---------- output ----------
const SEV = ['error', 'warning', 'info'];
const byCat = new Map();
for (const f of findings) { if (!byCat.has(f.cat)) byCat.set(f.cat, []); byCat.get(f.cat).push(f); }
const nBlocks = blocks.length;
console.log(`map     ${MAP.title}  (${sections.length} sections, ${nBlocks} blocks, ${Object.keys(notes).length} notes, ${examples.length} examples)`);
console.log(`source  ${rootDir ? path.relative(process.cwd(), rootDir) || '.' : '-'}${idx ? `  (${idx.files.size} files, ${idx.entries.length} names, ${nRefs} citations)` : ''}`);
console.log(`mathjax ${mjRan ? 'rendered every formula in every mode' : 'skipped (pass --mathjax <node_modules with mathjax-full>)'}`);
for (const sev of SEV) {
  const cats = [...byCat.entries()].filter(([, fs]) => fs[0].sev === sev).sort((a, b) => b[1].length - a[1].length);
  if (!cats.length) continue;
  console.log(`\n${sev === 'error' ? 'errors' : sev === 'warning' ? 'warnings' : 'info'}`);
  for (const [cat, fs] of cats) {
    console.log(`${String(fs.length).padStart(6)}  ${cat.padEnd(26)} ${CATS[cat] || ''}`);
    const all = o.list === true || o.list === cat;
    for (const f of all ? fs : fs.slice(0, o.max)) console.log(`          ${f.where}: ${f.msg}`);
    if (!all && fs.length > o.max) console.log(`          … ${fs.length - o.max} more (--list ${cat})`);
  }
}
if (o.json) fs.writeFileSync(o.json, JSON.stringify(findings, null, 1) + '\n');
const nErr = findings.filter(f => f.sev === 'error').length, nWarn = findings.filter(f => f.sev === 'warning').length;
console.log(`\n${nErr} errors, ${nWarn} warnings, ${findings.length - nErr - nWarn} info`);
process.exit(nErr || (o.strict && nWarn) ? 1 : 0);
