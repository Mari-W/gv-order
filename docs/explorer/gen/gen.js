const path = require('path');
const fs = require('fs');
const core = require('./core');
require('./syntax'); require('./semantics'); require('./types'); require('./typing'); require('./semrel'); require('./theorems');
const katex = require('/home/mari/.vscode-server/extensions/goessner.mdmath-2.7.4/node_modules/katex/dist/katex.js');
const { sections, notes, examples } = core;
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
const ids = new Set();
for (const s of sections) for (const b of s.blocks) {
  if (ids.has(b.id)) { console.log('DUPID', b.id); errs++; } ids.add(b.id);
  scan(b.tex, b.id);
  for (const [m, t] of Object.entries(b.variants || {})) { scan(t, b.id + '/' + m); if (!b.modes.includes(m)) console.log('VARIANT-NOT-IN-MODES', b.id, m); }
}
const unused = Object.keys(notes).filter(k => !used.has(k));
if (unused.length) console.log('UNUSED', unused.join(' '));
// prose checks
const bad = [/[;—]/, /\bsince\b/i, /\bslots?\b/i, /\bgates?\b/i, /\bpriority\b/i, /\b(novel|significant|comprehensive|robust|crucial|seamless|leverage|delve|pivotal|substantial)\b/i];
function prose(t, where) { for (const r of bad) if (r.test(t)) console.log('PROSE', where, r, '::', t.slice(0, 140)); if (/:\s/.test(t)) console.log('COLON?', where, '::', t.slice(0, 140)); }
for (const s of sections) { prose(s.intro, s.id); for (const b of s.blocks) { prose(b.caption, b.id); prose(b.title, b.id + '.title'); } }
for (const [k, v] of Object.entries(notes)) for (const f of ['title', 'what', 'why', 'breaks', 'example']) prose(v[f], k + '.' + f);
for (const e of examples) { prose(e.shows, e.id); prose(e.title, e.id + '.title'); }
const out = { sections, notes, examples };
const file = path.join(__dirname, '..', 'data.js');
fs.writeFileSync(file, 'window.MAP = ' + JSON.stringify(out, null, 1) + ';\n');
const nb = sections.reduce((a, s) => a + s.blocks.length, 0);
console.log('sections', sections.length, 'blocks', nb, 'notes', Object.keys(notes).length, 'examples', examples.length, 'errors', errs);
