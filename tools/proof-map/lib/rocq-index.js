// Index the names a Rocq source tree defines, with the statement text of each, by parsing the
// .v files. No compiled .vo files and no Rocq installation are needed.
//
// A name is anything a map may cite: inductive types and their constructors, records with their
// constructor and fields, definitions, fixpoints, lemmas and theorems, instances, axioms,
// parameters, notations (by their string) and abbreviations, modules and sections.
//
// Library use:   const { indexTree, statementHash } = require('./rocq-index');
// Command line:  node rocq-index.js <root> [name ...]   prints the entries of the names, or a summary
'use strict';
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');

// Replace comments and string literals by spaces, keeping offsets and line numbers.
// Comments nest. Strings use "" as the escaped quote.
function blank(src) {
  const out = src.split('');
  let i = 0, depth = 0;
  while (i < src.length) {
    if (src.startsWith('(*', i)) { depth++; out[i] = out[i + 1] = ' '; i += 2; continue; }
    if (depth && src.startsWith('*)', i)) { depth--; out[i] = out[i + 1] = ' '; i += 2; continue; }
    if (depth) { if (src[i] !== '\n') out[i] = ' '; i++; continue; }
    if (src[i] === '"') {
      let j = i + 1;
      while (j < src.length) { if (src[j] === '"') { if (src[j + 1] === '"') { j += 2; continue; } break; } j++; }
      for (let k = i + 1; k < j && k < src.length; k++) if (src[k] !== '\n') out[k] = ' ';
      i = j + 1; continue;
    }
    i++;
  }
  return out.join('');
}

// Sentences end at a period followed by white space or the end of the file, outside brackets
// such as {| |} and outside a run of periods ("..").
function sentences(clean) {
  const res = [];
  let start = 0;
  for (let i = 0; i < clean.length; i++) {
    if (clean[i] !== '.') continue;
    const next = clean[i + 1];
    if (next !== undefined && !/\s/.test(next)) continue;
    if (clean[i - 1] === '.') continue;
    res.push([start, i + 1]);
    start = i + 1;
  }
  if (clean.slice(start).trim()) res.push([start, clean.length]);
  return res;
}

const IDENT = String.raw`[\p{L}_][\p{L}\p{N}_']*`;
const ATTR = String.raw`(?:#\[[^\]]*\]\s*)*(?:(?:Local|Global|Polymorphic|Monomorphic|Program|Private|Cumulative|NonCumulative|Unset\s+\S+|Set\s+\S+)\s+)*`;
const KINDS = ['Inductive', 'CoInductive', 'Variant', 'Record', 'Structure', 'Class', 'Definition', 'Fixpoint', 'CoFixpoint',
  'Lemma', 'Theorem', 'Corollary', 'Proposition', 'Fact', 'Remark', 'Example', 'Property', 'Instance', 'Let', 'Axiom', 'Axioms',
  'Parameter', 'Parameters', 'Conjecture', 'Hypothesis', 'Hypotheses', 'Variable', 'Variables', 'Context', 'Notation', 'Infix',
  'Module', 'Section', 'Equations', 'Function', 'Ltac', 'Ltac2', 'Canonical', 'Coercion', 'Abbreviation'];
const HEAD = new RegExp('^\\s*' + ATTR + '(' + KINDS.join('|') + ')\\b\\s*', 'u');
const ID_AT = new RegExp('^(?:Type\\s+)?(' + IDENT + ')', 'u');

const lineOf = (src, off) => { let n = 1; for (let i = 0; i < off; i++) if (src.charCodeAt(i) === 10) n++; return n; };
const squash = s => s.replace(/\s+/g, ' ').trim();

// The bracketed groups at depth zero of a binder list "(x : T) {y : U} `(H : P)".
function topGroups(s) {
  const out = [];
  let depth = 0, start = -1;
  for (let i = 0; i < s.length; i++) {
    const c = s[i];
    if ('({['.includes(c)) { if (depth++ === 0) start = i; }
    else if (')}]'.includes(c) && depth > 0 && --depth === 0) out.push(s.slice(start, i + 1));
  }
  return out;
}

// Split mutual bodies at "with" outside brackets and outside match ... with ... end.
function splitWith(s) {
  const out = [];
  let depth = 0, matches = 0, last = 0;
  const re = /[(){}\[\]]|\b(match|end|with|let)\b/g;
  let m;
  while ((m = re.exec(s))) {
    const t = m[0];
    if ('({['.includes(t)) depth++;
    else if (')}]'.includes(t)) depth--;
    else if (depth === 0 && t === 'match') matches++;
    else if (depth === 0 && t === 'end' && matches > 0) matches--;
    else if (depth === 0 && t === 'with') { if (matches > 0) continue; out.push(s.slice(last, m.index)); last = m.index + 4; }
  }
  out.push(s.slice(last));
  return out;
}

// The constructors of one inductive body "name binders : sort := | C1 ... | C2 ...".
function constructors(body) {
  const at = body.indexOf(':=');
  if (at < 0) return [];
  const rhs = body.slice(at + 2);
  const ctors = [];
  // a constructor follows the start of the body or a bar at bracket depth zero, and its clause
  // runs to the next such bar
  let depth = 0, expect = true;
  for (let i = 0; i < rhs.length; i++) {
    const c = rhs[i];
    if (c === '(' || c === '{' || c === '[') depth++;
    else if (c === ')' || c === '}' || c === ']') depth--;
    else if (c === '|' && depth === 0 && rhs[i + 1] !== '|' && rhs[i - 1] !== '|') {
      if (ctors.length && ctors[ctors.length - 1].end < 0) ctors[ctors.length - 1].end = i;
      expect = true;
    } else if (expect && /\S/.test(c)) {
      const m = new RegExp('^' + IDENT, 'u').exec(rhs.slice(i));
      if (m) ctors.push({ name: m[0], start: i, end: -1 });
      expect = false;
    }
  }
  return ctors.map(k => ({ name: k.name, text: rhs.slice(k.start, k.end < 0 ? rhs.length : k.end).replace(/\.\s*$/, '') }));
}

// The constructor and fields of a record body "name binders : sort := Build { f : T ; g : T }".
function recordParts(name, body) {
  const at = body.indexOf(':=');
  const out = [];
  if (at < 0) return out;
  const rhs = body.slice(at + 2).trim();
  const ctor = new RegExp('^(' + IDENT + ')?\\s*\\{', 'u').exec(rhs);
  out.push({ name: (ctor && ctor[1]) || 'Build_' + name, kind: 'constructor' });
  const open = rhs.indexOf('{'), close = rhs.lastIndexOf('}');
  if (open >= 0 && close > open) {
    for (const f of rhs.slice(open + 1, close).split(';')) {
      const m = new RegExp('^\\s*(' + IDENT + ')(?:\\s+[^:;]*?)?\\s*(?::>?(?!:)|:=)', 'u').exec(f);
      if (m) out.push({ name: m[1], kind: 'field', text: f });
    }
  }
  return out;
}

function indexFile(root, rel) {
  const src = fs.readFileSync(path.join(root, rel), 'utf8');
  const clean = blank(src);
  const entries = [];
  const add = (name, kind, off, text, parent) => entries.push({ name, kind, file: rel, line: lineOf(src, off), statement: squash(text), parent });
  for (const [a, b] of sentences(clean)) {
    const text = clean.slice(a, b);
    const m = HEAD.exec(text);
    if (!m) continue;
    const kind = m[1];
    const off = a + m.index + m[0].length;
    const rest = text.slice(m[0].length);
    if (kind === 'Notation' || kind === 'Infix') {
      // the notation string is blanked in the clean text, read it from the source
      const raw = src.slice(off, b);
      const s = /^"((?:[^"]|"")*)"/.exec(raw);
      if (s) add(s[1].replace(/""/g, '"'), 'notation', off, raw);
      else { const id = ID_AT.exec(rest); if (id) add(id[1], 'abbreviation', off, src.slice(off, b)); }
      continue;
    }
    if (kind === 'Ltac' || kind === 'Ltac2' || kind === 'Canonical' || kind === 'Coercion') {
      const id = ID_AT.exec(rest.replace(/^Structure\s+/, '')); if (id) add(id[1], kind.toLowerCase(), off, rest);
      continue;
    }
    if (kind === 'Variables' || kind === 'Variable' || kind === 'Parameters' || kind === 'Parameter' || kind === 'Hypotheses' || kind === 'Hypothesis' || kind === 'Axioms' || kind === 'Context') {
      // "Variable x y : T." or "Context (x : T) (y : U)." declares several names
      const groups = topGroups(rest);
      for (const g of groups.length ? groups : [rest]) {
        const lhs = g.replace(/^[({\[]|[)}\]]$/g, '').replace(/^!/, '').split(':')[0];
        for (const id of lhs.trim().split(/\s+/)) if (new RegExp('^' + IDENT + '$', 'u').test(id)) add(id, kind.toLowerCase().replace(/s$/, ''), off, g);
      }
      continue;
    }
    // mutual definitions are separated by "with"
    const bodies = splitWith(rest);
    let pos = off;
    for (let k = 0; k < bodies.length; k++) {
      const body = bodies[k];
      const id = ID_AT.exec(body.trimStart());
      if (!id || (k > 0 && !/^(Inductive|CoInductive|Fixpoint|CoFixpoint|Variant)$/.test(kind))) { pos += body.length + 4; continue; }
      const name = id[1];
      const stmt = text.slice(0, m[0].length).trim() + ' ' + body;
      add(name, kind.toLowerCase(), pos + body.indexOf(name), stmt);
      if (/^(Inductive|CoInductive|Variant)$/.test(kind)) for (const c of constructors(body)) add(c.name, 'constructor', pos + Math.max(0, body.indexOf(c.text)), c.text, name);
      if (/^(Record|Structure|Class)$/.test(kind)) for (const p of recordParts(name, body)) add(p.name, p.kind, pos + Math.max(0, body.indexOf(p.text || p.name)), p.text || stmt, name);
      pos += body.length + 4;
    }
  }
  return entries;
}

function listV(root, dir = '') {
  const out = [];
  for (const e of fs.readdirSync(path.join(root, dir), { withFileTypes: true })) {
    if (e.name.startsWith('.') || e.name === 'node_modules' || e.name === '_build') continue;
    const rel = dir ? dir + '/' + e.name : e.name;
    if (e.isDirectory()) out.push(...listV(root, rel));
    else if (e.name.endsWith('.v')) out.push(rel);
  }
  return out.sort();
}

// { files: Set of relative paths, byName: Map name -> [entry], entries: [entry] }
function indexTree(root) {
  const files = listV(root);
  const entries = files.flatMap(f => indexFile(root, f));
  const byName = new Map();
  for (const e of entries) { if (!byName.has(e.name)) byName.set(e.name, []); byName.get(e.name).push(e); }
  return { root, files: new Set(files), entries, byName };
}

// A short fingerprint of a statement. It ignores white space and comments, so only a change of
// the Rocq text itself changes it.
const statementHash = e => crypto.createHash('sha1').update(e.statement).digest('hex').slice(0, 10);

// The entry a reference means: the name in the cited file, or anywhere when the file is absent.
function lookup(idx, name, file) {
  const all = idx.byName.get(name) || [];
  if (!file) return all[0] || null;
  return all.find(e => e.file === file) || null;
}

module.exports = { indexTree, indexFile, statementHash, lookup, blank, sentences };

if (require.main === module) {
  const [root, ...names] = process.argv.slice(2);
  if (!root) { console.error('usage: node rocq-index.js <root> [name ...]'); process.exit(2); }
  const idx = indexTree(root);
  if (!names.length) {
    const kinds = Object.create(null);
    for (const e of idx.entries) kinds[e.kind] = (kinds[e.kind] || 0) + 1;
    console.log(`${idx.files.size} files, ${idx.entries.length} names`);
    for (const [k, v] of Object.entries(kinds).sort((a, b) => b[1] - a[1])) console.log(String(v).padStart(6), k);
  }
  for (const n of names) {
    const es = idx.byName.get(n) || [];
    if (!es.length) console.log(`${n}: not found`);
    for (const e of es) console.log(`${e.file}:${e.line}  ${e.kind}${e.parent ? ' of ' + e.parent : ''}  ${n}  [${statementHash(e)}]\n  ${e.statement.slice(0, 600)}${e.statement.length > 600 ? ' …' : ''}\n`);
  }
}
