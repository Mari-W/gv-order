#!/usr/bin/env node
// Convert a map in the older explorer format (a data.js that sets window.MAP, with
// \htmlData{k=..}{..} hovers and \annot, \annraw, \dfo, \annp mode markers) into proof-map/1 JSON.
//
// usage: node convert-explorer.js <data.js> <out.json> [--root <rocq root relative to out.json>]
//
// The conversion is mechanical. It infers a deviation only where the old data states one: a
// "planned" text becomes a planned deviation with that text as its reason, and a Rocq citation
// marked "(notation)" becomes a notation deviation whose reason reads REASON MISSING.
'use strict';
const fs = require('fs');
const path = require('path');

const args = process.argv.slice(2);
const opt = (name, dflt) => { const i = args.indexOf(name); if (i < 0) return dflt; const v = args[i + 1]; args.splice(i, 2); return v; };
const root = opt('--root', null);
const [inFile, outFile] = args;
if (!inFile || !outFile) { console.error('usage: node convert-explorer.js <data.js> <out.json> [--root <dir>]'); process.exit(2); }

const src = fs.readFileSync(inFile, 'utf8');
const OLD = JSON.parse(src.slice(src.indexOf('=') + 1).trim().replace(/;\s*$/, ''));
const MISSING = 'REASON MISSING';

// TeX and prose markup
const tex = t => typeof t !== 'string' ? t : t
  .replace(/\\htmlData\{k=([A-Za-z0-9.\-_]+)\}\{/g, '\\sym{$1}{')
  .replace(/\\annot\{/g, '\\inmode{lf}{')
  .replace(/\\annraw\{/g, '\\inmodeplain{lf}{')
  .replace(/\\dfo\{/g, '\\inmodeplain{df}{');
const prose = t => typeof t !== 'string' || !t.trim() ? undefined : tex(t).replace(/\\annp\{/g, '\\inmode{lf}{');

// "lang/Syntax.v: expr, Var; types/Types.v: ty (notation)" -> source references and deviations
function refs(s) {
  const out = [], devs = [];
  if (typeof s !== 'string' || !s.trim()) return { out, devs };
  let file = null;
  // "not yet in the Rocq (reason), today F.v: names" states a planned item and what the Rocq has now
  const plan = /^(not yet in the Rocq(?: \([^)]*\))?|to be mechanized)(?:,\s*(.*))?$/.exec(s.trim());
  if (plan) {
    devs.push({ kind: 'planned', reason: plan[1].replace(/^not yet in the Rocq \((.*)\)$/, 'Not yet in the Rocq, see $1.').replace(/^to be mechanized$/, 'To be mechanized.') });
    s = plan[2] || '';
    if (/^today\s+/.test(s)) s = s.replace(/^today\s+/, '');
    else if (s) { devs[devs.length - 1].reason += ' ' + s[0].toUpperCase() + s.slice(1) + '.'; s = ''; }
  }
  // a library module such as Coq.Init.Wf
  const lib = /^((?:Coq|Stdlib|Corelib|Rocq)(?:\.\w+)+):\s*(.*)$/.exec(s.trim());
  if (lib) { out.push({ file: lib[1], names: lib[2].split(/\s*,\s*/) }); return { out, devs }; }
  const push = (f, name, qual) => {
    let r = out.find(x => x.file === f && (x.qualifier || null) === (qual || null));
    if (!r) { r = { file: f, names: [] }; if (qual) r.qualifier = qual; out.push(r); }
    if (!r.names.includes(name)) r.names.push(name);
  };
  // split at ; and , outside brackets and $..$
  const toks = []; let cur = '', depth = 0, inM = false;
  for (const c of s) {
    if (c === '$') inM = !inM;
    if (!inM && c === '(') depth++;
    if (!inM && c === ')') depth--;
    if (!inM && !depth && (c === ';' || c === ',')) { toks.push(cur); cur = ''; } else cur += c;
  }
  toks.push(cur);
  for (let tok of toks) {
    tok = tok.trim();
    if (!tok) continue;
    const m = /^(\S+\.v):\s*(.*)$/.exec(tok);
    if (m) { file = m[1]; tok = m[2].trim(); if (!tok) continue; }
    const q = /^(.*?)\s*\(([^)]*)\)\s*$/.exec(tok) || /^(\S+)\s+(.+)$/.exec(tok);
    let name = tok, qual = null;
    if (q) { name = q[1]; qual = q[2]; }
    if (!file) { devs.push({ kind: 'other', reason: MISSING, names: [name], part: 'citation without a file: ' + tok }); continue; }
    if (qual === 'notation') { devs.push({ kind: 'notation', reason: MISSING, names: [name] }); qual = null; }
    push(file, name, qual);
  }
  return { out, devs };
}

// metavariables a grammar line introduces: the left-hand sides of ::=
function introduces(t) {
  const out = new Set();
  if (typeof t !== 'string') return [];
  const plain = t.replace(/\\sym\{[^}]*\}\{/g, '{');
  for (const m of plain.matchAll(/((?:\\[A-Za-z]+|[A-Za-z])(?:\s*_\{?[A-Za-z0-9]+\}?|')*(?:\s*,\s*(?:\\[A-Za-z]+|[A-Za-z])(?:\s*_\{?[A-Za-z0-9]+\}?|')*)*)\s*(?:&\s*)?::=/g))
    for (const v of m[1].split(',')) {
      const b = /^\s*(\\[A-Za-z]+|[A-Za-z])/.exec(v);
      if (b && !/^\\(mid|quad|qquad|;|,)$/.test(b[1])) out.add(b[1]);
    }
  return [...out];
}

const ALL = ['df', 'lf'];
const modesOf = ms => {
  const m = [...new Set((ms || ALL).map(x => x === 'live' ? 'lf' : x))];
  return ALL.every(x => m.includes(x)) ? undefined : m;
};
const clean = o => { for (const k of Object.keys(o)) if (o[k] === undefined || (Array.isArray(o[k]) && !o[k].length)) delete o[k]; return o; };

const sections = OLD.sections.map(s => clean({
  id: s.id,
  title: s.title,
  intro: prose(s.intro),
  blocks: s.blocks.map(b => {
    const { out, devs } = refs(b.rocq);
    const a = b.about || {};
    if (b.planned) devs.unshift({ kind: 'planned', reason: b.planned });
    if (!out.length) devs.push({ kind: 'unsourced', reason: MISSING });
    const variants = b.variants ? Object.fromEntries(Object.entries(b.variants).filter(([m]) => m !== 'live').map(([m, t]) => [m, tex(t)])) : undefined;
    const formula = tex(b.tex);
    return clean({
      id: b.id,
      title: b.title,
      formula,
      variants: variants && Object.keys(variants).length ? variants : undefined,
      caption: prose(b.caption),
      why: prose(a.why),
      breaks: prose(a.breaks),
      example: prose(a.example),
      modes: modesOf(b.modes),
      source: out,
      usedIn: a.used,
      introduces: introduces([formula, ...Object.values(variants || {})].join(' ')),
      deviations: devs
    });
  })
}));
// an empty source list is still required by the schema
for (const s of sections) for (const b of s.blocks) if (!b.source) b.source = [];

const notes = {};
for (const [k, n] of Object.entries(OLD.notes)) {
  if (k.startsWith('@')) continue;
  const { out, devs } = refs(n.rocq);
  notes[k] = clean({
    title: tex(n.title) || k,
    meaning: prose(n.what),
    why: prose(n.why),
    breaks: prose(n.breaks),
    example: prose(n.example),
    signature: tex(n.sig),
    args: (n.args || []).map(x => clean({ name: tex(x.name), meaning: prose(x.meaning) || '', modes: x.ann ? ['lf'] : undefined })),
    source: out,
    usedIn: n.used,
    deviations: devs
  });
}

const examples = (OLD.examples || []).map(x => {
  const { out, devs } = refs(x.rocq);
  return clean({
    id: x.id,
    title: x.title,
    lead: prose(x.lead),
    code: x.code,
    meaning: prose(x.shows),
    modes: modesOf(x.modes),
    source: out,
    deviations: devs,
    'x-gv-accepts': x.accepts
  });
});

const map = {
  $schema: path.relative(path.dirname(path.resolve(outFile)), path.join(__dirname, 'schema.json')),
  format: 'proof-map/1',
  title: 'GV Relation Map',
  subtitle: 'Definitions, rules and theorems of the v2 development',
  source: root ? { root, language: 'rocq' } : undefined,
  tex: { macros: { llbracket: '[\\![', rrbracket: ']\\!]' } },
  syntax: {
    keywords: ['let', 'in', 'new', 'spawn', 'send', 'recv', 'close', 'select', 'branch', 'link', 'force', 'case', 'of', 'inl', 'inr', 'fix', 'box', 'fun', 'if', 'then', 'else', 'end', 'skip', 'rec'],
    comment: ['(* *)', '--']
  },
  modes: {
    label: 'Instance',
    default: 'df',
    options: [
      { id: 'df', label: 'Deadlock free', short: 'DF', description: 'The relation and typing for deadlock freedom.', color: { light: '#3b5b92', dark: '#93acdc' } },
      { id: 'lf', label: 'Lock free', short: 'LF', description: 'Deadlock freedom plus credits, ticket needs, the guard and fuel.', color: { light: '#7b4d8f', dark: '#c6a2dc' } }
    ]
  },
  sections,
  notes,
  examples,
  extensions: { page: ['ext/gv-page.js'], check: ['ext/gv-check.js'] }
};
clean(map);
fs.writeFileSync(outFile, JSON.stringify(map, null, 1) + '\n');
const nb = sections.reduce((a, s) => a + s.blocks.length, 0);
const nd = [...sections.flatMap(s => s.blocks), ...Object.values(notes), ...examples].reduce((a, x) => a + (x.deviations || []).length, 0);
const nm = [...sections.flatMap(s => s.blocks), ...Object.values(notes), ...examples].reduce((a, x) => a + (x.deviations || []).filter(d => d.reason === MISSING).length, 0);
console.log(`${sections.length} sections, ${nb} blocks, ${Object.keys(notes).length} notes, ${examples.length} examples, ${nd} deviations (${nm} with ${MISSING})`);
