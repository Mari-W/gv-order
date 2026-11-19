const path = require('path');
const fs = require('fs');
const core = require('./core');
require('./syntax'); require('./semantics'); require('./types'); require('./typing'); require('./semrel'); require('./theorems'); require('./rejects'); require('./about'); require('./layout').remap(); require('./prose').apply();
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
  try { katex.renderToString(tex, { trust: true, strict: 'ignore', throwOnError: true, displayMode: true, macros: { '\\annot': '#1', '\\annraw': '#1', '\\dfo': '#1' } }); }
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
const MAC = { '\\llbracket': '[\\![', '\\rrbracket': ']\\!]', '\\annot': '#1', '\\annraw': '#1', '\\dfo': '#1' };
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
const CRH = /\^\{\\htmlData\{k=[^}]*\}\{(?:a|b)(?:_\{?\w+\}?)?'*\}\}/g;
// costs and ticket needs after a judgment, arrow and box annotations, refills on types
const TRI = /(\\mathbin\{\\htmlData\{k=tp\.tri\}\{\\triangleright\}\}|(?<!\\!)\\triangleright)\s*(c(?:_\{?\w+\}?)?'?|\\infty|\d+)\s*;\s*(\\vartheta(?:_\{?\w+\}?)?'?|\\hat\s*1|\d+|r|\([^()]*\))/g;
const BRK = /\[(?:\\htmlData\{k=[^}]*\}\{)?c(?:_\{?\w+\}?)?'?\}?\s*;[^\]]*\]/g;
const REF = /\^\{(N|0)\}/g;
// a superscript N or 0 on a judgment or on F, P, E, V is an index, elsewhere a refill or credit
const isIndex = (s, i) => /(Vdash|vDash)\}*$/.test(s.slice(Math.max(0, i - 12), i)) || /(^|[^\\A-Za-z])(FV|F|P|E|V)$/.test(s.slice(Math.max(0, i - 4), i));
const ann = t => typeof t !== 'string' ? t : t.replace(CRH, m => '\\annot{' + m + '}').replace(CR, '\\annot{^{$1}}')
  .replace(TRI, m => '\\annot{' + m + '}').replace(BRK, m => '\\annot{' + m + '}')
  .replace(/\\vdash(\}*)\^\{(N|\\infty)\}/g, '\\vdash$1\\annot{^{$2}}').replace(/_\{(W(?:_\d)?),(N|\\infty)\}/g, '_{$1\\annot{,$2}}')
  .replace(REF, (m, x, i, s) => isIndex(s, i) ? m : '\\annot{' + m + '}');
// one toggle: liveness is deadlock freedom plus the guard, which only lock freedom needs, so live material shows with lock freedom
const unlive = ms => [...new Set((ms || ['df', 'lf']).map(m => m === 'live' ? 'lf' : m))];
for (const s of sections) for (const b of s.blocks) { b.modes = unlive(b.modes); if (b.variants) delete b.variants.live; }
for (const e of examples) e.modes = unlive(e.modes);
for (const s of sections) for (const b of s.blocks) { b.tex = ann(b.tex); if (b.variants) for (const k of Object.keys(b.variants)) b.variants[k] = ann(b.variants[k]); }
// in a block with its own deadlock-free form, every hoverable part of the lock-free form whose key the deadlock-free form lacks is a lock-free addition
// keys the deadlock-free forms write without a hover but that are no lock-free addition
const SAME = new Set(['ty.payload-at', 'ctx.slt', 'sty.dual', 'tp.sinsts', 'tp.sinst', 'tp.pinst', 'ty.unlimited', 'sty.sequiv', 'sub.tsub']);
function markNew(tex, known) {
  let out = '', i = 0;
  const close = j => { let d = 1, k = j; while (k < tex.length && d) { if (tex[k] === '\\') { k += 2; continue; } if (tex[k] === '{') d++; else if (tex[k] === '}') d--; k++; } return k; };
  for (;;) {
    const m = /\\ann(?:ot|raw)\{|\\htmlData\{k=([^}]*)\}\{/.exec(tex.slice(i)); if (!m) return out + tex.slice(i);
    const j = i + m.index, open = j + m[0].length;
    if (!m[1]) { const k = close(open); out += tex.slice(i, k); i = k; continue; }
    if (known.has(m[1]) || SAME.has(m[1])) { out += tex.slice(i, open); i = open; continue; }
    const k = close(open); out += tex.slice(i, j) + '\\annot{' + tex.slice(j, k) + '}'; i = k;
  }
}
for (const s of sections) for (const b of s.blocks) if (b.variants && b.variants.df && b.modes.includes('df')) {
  const known = new Set([...b.variants.df.matchAll(/\\htmlData\{k=([^}]*)\}/g)].map(m => m[1]));
  if (b.variants.lf) b.variants.lf = markNew(b.variants.lf, known); else b.tex = markNew(b.tex, known);
}
// prose of notes reachable in the deadlock-free mode: phrases and sentences about annotations become \annp{…}
const KW = /credit|ticket need|ticket|\\vartheta|\\mathsf\{meets\}|refill|\bfloor\b|\\hat\s*1/i;
const PHR = /,? (?:and|with) (?:its|their|the|a|outer and inner|payload)? ?credits?\b|,? credits? and |,? at (?:payload )?credit \$[^$]*\$/gi;
const stripAnn = s => { let o = '', i = 0; for (;;) { const m = /\\ann(ot|raw|p)\{/.exec(s.slice(i)); if (!m) return o + s.slice(i); const j = i + m.index; let d = 1, k = j + m[0].length; while (k < s.length && d) { if (s[k] === '\\') { k += 2; continue; } if (s[k] === '{') d++; else if (s[k] === '}') d--; k++; } o += s.slice(i, j); i = k; } };
function annProse(t) {
  if (typeof t !== 'string' || !KW.test(t)) return t;
  t = t.replace(PHR, m => '\\annp{' + m + '}');
  // sentences end at '. ' outside $…$
  const out = []; let cur = '', inM = false;
  for (let i = 0; i < t.length; i++) { const c = t[i]; cur += c; if (c === '$' && t[i - 1] !== '\\') inM = !inM; if (!inM && c === '.' && (t[i + 1] === ' ' || i === t.length - 1)) { out.push(cur); cur = ''; } }
  if (cur) out.push(cur);
  return out.map(snt => KW.test(stripAnn(snt)) ? snt.replace(/^(\s*)([\s\S]*)$/, (m, sp, body) => sp + '\\annp{' + body + '}') : snt).join('');
}
const dfKeys = new Set();
for (const s of sections) for (const b of s.blocks) if (b.modes.includes('df')) for (const m of stripAnn(ann((b.variants && b.variants.df) || b.tex)).matchAll(/\\htmlData\{k=([^}]*)\}/g)) dfKeys.add(m[1]);
for (const s of sections) { s.intro = annProse(ann(s.intro)); for (const b of s.blocks) if (b.modes.includes('df')) b.caption = annProse(ann(b.caption)); }
for (const [k, v] of Object.entries(notes)) if (dfKeys.has(k)) {
  for (const f of ['what', 'why', 'breaks', 'example']) v[f] = annProse(v[f]);
  for (const a of v.args || []) if (KW.test(a.meaning)) { const onlyAnn = a.name.split(',').every(x => /^\s*(a|b|c|h|tk|r|\\vartheta)(_\{?\w+\}?)?'*\s*$/.test(x)); if (onlyAnn) a.ann = true; else a.meaning = annProse(a.meaning); }
}
for (const v of Object.values(notes)) { for (const f of ['title', 'what', 'why', 'breaks', 'example', 'sig']) v[f] = ann(v[f]); for (const a of v.args || []) { if (/^(a|b)(_\{?\w+\}?)?'*$/.test(a.name) && /credit/i.test(a.meaning)) a.ann = true; a.name = ann(a.name); a.meaning = ann(a.meaning); } }
const out = { sections, notes, examples };
const file = path.join(__dirname, '..', 'data.js');
fs.writeFileSync(file, 'window.MAP = ' + JSON.stringify(out, null, 1) + ';\n');
// explorer.html, the page serve.sh opens, is index.html with a document skeleton, rebuilt every time so the two never drift
{
  const dir = path.join(__dirname, '..');
  const page = fs.readFileSync(path.join(dir, 'index.html'), 'utf8');
  fs.writeFileSync(path.join(dir, 'explorer.html'), '<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover"></head><body>\n' + page + '\n</body></html>\n');
}
const nb = sections.reduce((a, s) => a + s.blocks.length, 0);
console.log('unicode-math fields (UNI=1 lists them)', nUni);
const noSig = Object.keys(notes).filter(k => !notes[k].sig);
console.log('unhovered symbols (HOV=1 lists them)', nHover, '| notes without sig (SIG=1 lists them)', noSig.length);
if (process.env.SIG) console.log('NOSIG', noSig.join(' '));
for (const [k, v] of Object.entries(notes)) { if (v.sig) { try { katex.renderToString(v.sig, { trust: true, strict: 'ignore', throwOnError: true, macros: { ...MAC } }); } catch (e) { console.log('KATEX-SIG', k, e.message.slice(0, 120)); errs++; } for (const a of v.args || []) { try { katex.renderToString(a.name, { trust: true, strict: 'ignore', throwOnError: true, macros: { ...MAC } }); } catch (e) { console.log('KATEX-ARG', k, e.message.slice(0, 120)); errs++; } prose(a.meaning, k + '.arg'); } } }
for (const e of examples) if (e.accepts) for (const [m, a] of Object.entries(e.accepts)) { if (!['df', 'live', 'lf'].includes(m) || typeof a.ok !== 'boolean') { console.log('BAD-ACCEPTS', e.id, m); errs++; } }
// nothing about annotations may show in the deadlock-free mode
{
  const LEAK = [/\^\{\\htmlData\{k=[^}]*\}\{[ab]/, /\^\{[ab](_|'|\}|\s*\+)/, /(?<!\\!)\\triangleright\}*\s*(c|\\infty|\d)/, /\\vartheta/, /\[c\s*;/, /\\hat\s*1/, /\\mathsf\{(tok|meets|tix|tspawn|tlink|tseq)\}/, /\\vdash\}*\^\{N\}/, /credit/i];
  const leak = (x, where) => { const t = stripAnn(String(x || '')); for (const r of LEAK) if (r.test(t)) { console.log('DF-LEAK', where, r); errs++; return; } };
  for (const s of sections) for (const b of s.blocks) if (b.modes.includes('df')) { leak((b.variants && b.variants.df) || b.tex, b.id); leak(b.caption, b.id + '.caption'); }
  for (const k of dfKeys) { const v = notes[k]; if (!v) continue; for (const f of ['sig', 'what', 'why', 'breaks', 'example']) leak(v[f], k + '.' + f); for (const a of v.args || []) if (!a.ann) leak(a.name + ' ' + a.meaning, k + '.arg'); }
}
console.log('sections', sections.length, 'blocks', nb, 'notes', Object.keys(notes).length, 'examples', examples.length, 'errors', errs);
