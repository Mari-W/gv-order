const path = require('path');
const fs = require('fs');
const core = require('./core');
require('./syntax'); require('./semantics'); require('./types'); require('./typing'); require('./semrel'); require('./theorems');
const katex = require('/home/mari/.vscode-server/extensions/goessner.mdmath-2.7.4/node_modules/katex/dist/katex.js');
const { sections, notes, examples, sigs } = core;
for (const [k, v] of Object.entries(sigs)) { if (!notes[k]) { console.log('SIG-NO-NOTE', k); } else { notes[k].sig = v.sig; notes[k].args = v.args; } }
const used = new Set(); let errs = 0;
function scan(tex, where) {
  for (const m of tex.matchAll(/\\htmlData\{k=([^}]*)\}/g)) {
    used.add(m[1]);
    if (!/^[A-Za-z0-9.\-]+$/.test(m[1])) { console.log('BADKEY', m[1], where); errs++; }
    if (!notes[m[1]]) { console.log('MISSING', m[1], where); errs++; }
  }
  try { katex.renderToString(tex, { trust: true, strict: 'ignore', throwOnError: true, displayMode: true }); }
  catch (e) { console.log('KATEX', where, e.message.slice(0, 200)); errs++; }
}
// ranges of tex covered by the body of some \htmlData{k=..}{BODY}
function covered(tex) {
  const cov = new Uint8Array(tex.length);
  const re = /\\htmlData\{k=[^}]*\}\{/g; let m;
  while ((m = re.exec(tex))) {
    let i = re.lastIndex, d = 1;
    while (i < tex.length && d > 0) { if (tex[i] === '\\') { i += 2; continue; } if (tex[i] === '{') d++; else if (tex[i] === '}') d--; i++; }
    for (let j = m.index; j < i; j++) cov[j] = 1;
  }
  return cov;
}
const OPS = ['\\vdash', '\\vDash', '\\Vdash', '\\Vvdash', '\\prec', '\\preccurlyeq', '\\sqsubseteq', '\\sqsupseteq', '\\sqcup', '\\uplus', '\\llbracket', '\\triangleright', '\\approx', '\\simeq', '\\multimap'];
let nHover = 0;
function hover(tex, where) {
  const cov = covered(tex);
  const re = new RegExp('\\\\(?:mathsf|mathit|operatorname)\\{[^}]*\\}|' + OPS.map(o => o.replace(/\\/g, '\\\\') + '(?![a-zA-Z])').join('|'), 'g');
  let m; const miss = new Set();
  while ((m = re.exec(tex))) if (!cov[m.index]) miss.add(m[0]);
  if (miss.size) { nHover += miss.size; if (process.env.HOV) console.log('UNHOVERED', where, [...miss].join(' ')); }
}
const ids = new Set();
for (const s of sections) for (const b of s.blocks) {
  if (ids.has(b.id)) { console.log('DUPID', b.id); errs++; } ids.add(b.id);
  scan(b.tex, b.id); hover(b.tex, b.id);
  for (const [m, t] of Object.entries(b.variants || {})) { scan(t, b.id + '/' + m); hover(t, b.id + '/' + m); if (!b.modes.includes(m)) console.log('VARIANT-NOT-IN-MODES', b.id, m); }
}
const unused = Object.keys(notes).filter(k => !used.has(k));
if (unused.length) console.log('UNUSED', unused.join(' '));
// prose checks
const bad = [/[;—]/, /\bsince\b/i, /\bslots?\b/i, /\bgates?\b/i, /\bpriority\b/i, /\b(novel|significant|comprehensive|robust|crucial|seamless|leverage|delve|pivotal|substantial)\b/i];
const MAC = { '\\llbracket': '[\\![', '\\rrbracket': ']\\!]', '\\annot': '#1' };
// Unicode math left outside $…$ (Greek letters, arrows, relations, sub/superscripts)
const umath = /[\u0370-\u03FF\u2070-\u209F\u2190-\u22FF\u27E8-\u27EF\u2A00-\u2AFF\u0300-\u036F]/;
let nUni = 0;
function prose(t, where) {
  if (t === undefined) return;
  const parts = t.split('$');
  if (parts.length % 2 === 0) { console.log('DOLLAR', where, '::', t.slice(0, 140)); errs++; return; }
  for (let i = 1; i < parts.length; i += 2) {
    if (/\\htmlData/.test(parts[i])) { console.log('HTMLDATA-IN-PROSE', where); errs++; }
    try { katex.renderToString(parts[i], { trust: true, strict: 'ignore', throwOnError: true, macros: { ...MAC } }); }
    catch (e) { console.log('KATEX-PROSE', where, e.message.slice(0, 160)); errs++; }
  }
  const txt = parts.filter((_, i) => i % 2 === 0).join(' ').replace(/`[^`]*`/g, ' ');
  for (const r of bad) if (r.test(txt)) console.log('PROSE', where, r, '::', t.slice(0, 140));
  if (/:\s/.test(txt)) console.log('COLON?', where, '::', t.slice(0, 140));
  if (umath.test(txt)) { nUni++; if (process.env.UNI) console.log('UNICODE-MATH', where, '::', txt.match(umath)[0], '::', t.slice(0, 120)); }
}
for (const s of sections) { prose(s.intro, s.id); for (const b of s.blocks) { prose(b.caption, b.id); prose(b.title, b.id + '.title'); } }
for (const [k, v] of Object.entries(notes)) for (const f of ['title', 'what', 'why', 'breaks', 'example']) prose(v[f], k + '.' + f);
for (const e of examples) { prose(e.shows, e.id); prose(e.title, e.id + '.title'); }
// credits a, b, a_i, a' and sums a + ... are annotations: mark them so the page shows them only in the lock-free mode
const CR = /\^\{((?:a|b)(?:_\{?[A-Za-z0-9]+\}?)?'*(?:\s*\+[^{}]*)?)\}/g;
const ann = t => typeof t === 'string' ? t.replace(CR, '\\annot{^{$1}}') : t;
for (const s of sections) for (const b of s.blocks) { b.tex = ann(b.tex); if (b.variants) for (const k of Object.keys(b.variants)) b.variants[k] = ann(b.variants[k]); }
for (const v of Object.values(notes)) { for (const f of ['title', 'what', 'why', 'breaks', 'example', 'sig']) v[f] = ann(v[f]); for (const a of v.args || []) { if (/^(a|b)(_\{?\w+\}?)?'*$/.test(a.name) && /credit/i.test(a.meaning)) a.ann = true; a.name = ann(a.name); a.meaning = ann(a.meaning); } }
const out = { sections, notes, examples };
const file = path.join(__dirname, '..', 'data.js');
fs.writeFileSync(file, 'window.MAP = ' + JSON.stringify(out, null, 1) + ';\n');
const nb = sections.reduce((a, s) => a + s.blocks.length, 0);
console.log('unicode-math fields (UNI=1 lists them)', nUni);
const noSig = Object.keys(notes).filter(k => !notes[k].sig);
console.log('unhovered symbols (HOV=1 lists them)', nHover, '| notes without sig (SIG=1 lists them)', noSig.length);
if (process.env.SIG) console.log('NOSIG', noSig.join(' '));
for (const [k, v] of Object.entries(notes)) { if (v.sig) { try { katex.renderToString(v.sig, { trust: true, strict: 'ignore', throwOnError: true, macros: { ...MAC } }); } catch (e) { console.log('KATEX-SIG', k, e.message.slice(0, 120)); errs++; } for (const a of v.args || []) { try { katex.renderToString(a.name, { trust: true, strict: 'ignore', throwOnError: true, macros: { ...MAC } }); } catch (e) { console.log('KATEX-ARG', k, e.message.slice(0, 120)); errs++; } prose(a.meaning, k + '.arg'); } } }
for (const e of examples) if (e.accepts) for (const [m, a] of Object.entries(e.accepts)) { if (!['df', 'live', 'lf'].includes(m) || typeof a.ok !== 'boolean') { console.log('BAD-ACCEPTS', e.id, m); errs++; } }
console.log('sections', sections.length, 'blocks', nb, 'notes', Object.keys(notes).length, 'examples', examples.length, 'errors', errs);
