// Generator core: helpers shared by every part.
const R = String.raw;
const h = (k, t) => `\\htmlData{k=${k}}{${t}}`;
const notes = {};
const sections = [];
const examples = [];
const DEF = 'Nothing. It is a definition.';
function n(k, title, what, why, breaks, example, rocq) {
  if (notes[k]) throw new Error('duplicate note ' + k);
  notes[k] = { title, what, why, breaks, example, rocq };
}
// sig: TeX signature of the symbol (or its syntactic category), args: [{name: TeX, meaning: prose with $…$}]
const sigs = {};
function sa(k, sig, args) {
  if (sigs[k]) throw new Error('duplicate sig ' + k);
  sigs[k] = { sig, args: args || [] };
}
function section(id, title, intro) {
  const s = { id, title, intro, blocks: [] };
  sections.push(s);
  return s;
}
function block(s, b) {
  if (!b.modes) b.modes = ['df', 'lf'];
  s.blocks.push(b);
}
const rule = (name, prem, concl) =>
  R`\dfrac{${prem}}{${concl}}\;\textsf{${name.replace(/_/g, '\\_')}}`;
const Q = R`\quad `;
module.exports = { R, h, n, sa, sigs, notes, sections, examples, section, block, rule, Q, DEF };
