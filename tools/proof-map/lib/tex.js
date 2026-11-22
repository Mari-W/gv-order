// TeX helpers shared by the checker and extensions: brace matching, the map markup
// (\sym, \inmode, \inmodeplain, \planned), mode resolution and variable extraction.
'use strict';

// index just past the group that opens at s[open] === '{'
function closeGroup(s, open) {
  let d = 1, k = open + 1;
  while (k < s.length && d) {
    if (s[k] === '\\') { k += 2; continue; }
    if (s[k] === '{') d++; else if (s[k] === '}') d--;
    k++;
  }
  return k;
}

// read a braced argument at s[i] (after spaces): [content, index after]
function arg(s, i) {
  while (s[i] === ' ') i++;
  if (s[i] !== '{') return [null, i];
  const k = closeGroup(s, i);
  return [s.slice(i + 1, k - 1), k];
}

// The formula as a reader of one mode sees it. \inmode{ms}{X} and \inmodeplain{ms}{X} keep X when
// the mode is in ms. With colour, \inmode wraps X in \class{mode-M}{..}. A mode of null keeps
// every part, which is what checks that look at all modes at once use.
function resolve(s, mode, opts = {}) {
  s = String(s || '');
  let out = '', i = 0;
  const re = /\\(inmode|inmodeplain)\s*\{/g;
  for (;;) {
    re.lastIndex = i;
    const m = re.exec(s);
    if (!m) return out + s.slice(i);
    const [ms, k1] = arg(s, m.index + m[1].length + 1);
    const [body, k2] = arg(s, k1);
    if (body === null) { out += s.slice(i, k1); i = k1; continue; }
    const inner = resolve(body, mode, opts);
    const list = ms.split(',').map(x => x.trim());
    const keep = mode === null || list.includes(mode);
    let piece = '';
    if (keep) piece = m[1] === 'inmode' && opts.colour ? opts.colour(inner, mode) : inner;
    out += s.slice(i, m.index) + piece;
    i = k2;
  }
}

// every \sym{key}{...}: [{key, start, end, body}]
function syms(s) {
  const out = [];
  const re = /\\sym\s*\{([^}]*)\}\s*\{/g;
  let m;
  while ((m = re.exec(s))) {
    const open = re.lastIndex - 1, end = closeGroup(s, open);
    out.push({ key: m[1], start: m.index, end, body: s.slice(open + 1, end - 1) });
  }
  return out;
}

// a mask of the characters inside some \sym body
function covered(s) {
  const cov = new Uint8Array(s.length);
  for (const x of syms(s)) for (let j = x.start; j < x.end; j++) cov[j] = 1;
  return cov;
}

// the modes \inmode and \inmodeplain mention
function modesMentioned(s) {
  const out = new Set();
  for (const m of String(s || '').matchAll(/\\inmode(?:plain)?\s*\{([^}]*)\}/g)) for (const x of m[1].split(',')) out.add(x.trim());
  return out;
}

const GREEK = ['alpha', 'beta', 'gamma', 'delta', 'epsilon', 'varepsilon', 'zeta', 'eta', 'theta', 'vartheta', 'iota', 'kappa', 'varkappa',
  'rho', 'varrho', 'sigma', 'varsigma', 'tau', 'upsilon', 'phi', 'varphi', 'chi', 'psi', 'omega', 'xi', 'nu', 'pi', 'varpi',
  'Gamma', 'Delta', 'Theta', 'Lambda', 'Xi', 'Pi', 'Sigma', 'Upsilon', 'Phi', 'Psi', 'Omega'];
const GREEK_SET = new Set(GREEK);
// commands whose argument is a name or layout, never a variable
const NAMEY = /\\(?:mathsf|textsf|mathrm|textrm|text|mbox|mathit|textit|mathtt|texttt|operatorname|mathbb|mathbf|textbf|begin|end|hspace|vspace|label|color|class|htmlData|cssId|style|textup|textnormal|sym)\s*\{[^{}]*\}/g;
const BINDERS = /^\\(forall|exists|lambda|Lambda|mu|nu)$/;

// Tokens of a formula: [{t: 'var'|'word'|'cmd'|'other', v, base, at}]. A variable is one Latin
// letter or one Greek letter command, its base drops primes, subscripts and superscripts.
function tokens(s) {
  s = String(s || '')
    .replace(/\\(inmode|inmodeplain)\s*\{[^}]*\}/g, '')
    .replace(/\\planned\b/g, '')
    .replace(/\\begin\{array\}\s*\{[^}]*\}/g, ' ')
    .replace(/\\\\\s*\[[^\]]*\]/g, ' ')
    .replace(NAMEY, m => ' '.repeat(m.length));
  const out = [];
  const re = /\\[A-Za-z]+|[A-Za-z]+|\S/g;
  let m;
  while ((m = re.exec(s))) {
    const v = m[0];
    if (v[0] === '\\') out.push({ t: GREEK_SET.has(v.slice(1)) ? 'var' : 'cmd', v, base: v, at: m.index });
    else if (/^[A-Za-z]+$/.test(v)) {
      if (v.length === 1) out.push({ t: 'var', v, base: v, at: m.index });
      else if (v.length === 2) for (let j = 0; j < 2; j++) out.push({ t: 'var', v: v[j], base: v[j], at: m.index + j });
      else out.push({ t: 'word', v, at: m.index });
    } else out.push({ t: 'other', v, at: m.index });
  }
  return out;
}

// variables a formula uses, and the ones a binder (\forall x, \lambda x., \exists x) binds locally
function variables(s) {
  const toks = tokens(s);
  const used = new Map(), bound = new Set();
  for (let i = 0; i < toks.length; i++) {
    const tk = toks[i];
    if (tk.t === 'cmd' && BINDERS.test(tk.v)) {
      for (let j = i + 1; j < toks.length; j++) {
        const u = toks[j];
        if (u.t === 'var') { bound.add(u.base); continue; }
        if (u.t === 'other' && /[_{}'^0-9]/.test(u.v)) continue;
        if (u.t === 'cmd' && /^\\(,|;|!|:)$/.test(u.v)) continue;
        break;
      }
      continue;
    }
    if (tk.t === 'var' && !/^\\(lambda|mu)$/.test(tk.v) && !used.has(tk.base)) used.set(tk.base, tk.at);
  }
  return { used, bound };
}

// bare words of three or more letters outside \mathsf, \text and friends
const words = s => tokens(s).filter(t => t.t === 'word').map(t => t.v);

// \text{...} and friends with words in them
function proseInFormula(s) {
  const out = [];
  for (const m of String(s || '').matchAll(/\\(?:text|mbox|textrm|textit|textnormal)\s*\{([^{}]*)\}/g))
    if (/[A-Za-z]{2,}/.test(m[1])) out.push(m[1].trim());
  return out;
}

// Tables. A row holds a formula and a text, or a list of cells, each a formula or a text.
const cellsOf = r => r.cells || [{ formula: r.formula }, ...(r.text !== undefined ? [{ text: r.text }] : [])];
const rowVisible = (r, mode) => mode === null || mode === undefined || !r.modes || r.modes.includes(mode);
// the rows a reader of one mode sees (all rows for a mode of null)
const tableRows = (b, mode = null) => ((b.table && b.table.rows) || []).filter(r => rowVisible(r, mode));
// the formulas of the rows, in reading order
const tableFormulas = (b, mode = null) => tableRows(b, mode).flatMap(r => cellsOf(r).filter(c => typeof c.formula === 'string').map(c => c.formula));
// the prose of a table: head, labels and text cells, as [where, text]
function tableTexts(b) {
  const out = [];
  ((b.table && b.table.header) || []).forEach((h, i) => { if (h) out.push(['head ' + (i + 1), h]); });
  ((b.table && b.table.rows) || []).forEach((r, i) => {
    if (r.label) out.push(['row ' + (i + 1) + ' label', r.label]);
    cellsOf(r).forEach((c, j) => { if (typeof c.text === 'string' && c.text.trim()) out.push(['row ' + (i + 1) + (r.cells ? ' cell ' + (j + 1) : ''), c.text]); });
  });
  return out;
}
// $..$ segments of prose, after resolving the modes
const proseMath = (t, mode = null) => [...resolve(t, mode).matchAll(/(?<!\\)\$([^$]+)\$/g)].map(m => m[1]);

// Names written as a letter with a subscript, such as \kappa_L or \kappa_{DF}, that a block lists
// under introduces. The checker reads such a name as one symbol, and its subscript as no variable.
const compoundNames = blocks => [...new Set(blocks.flatMap(b => (b.introduces || []).filter(v => /_/.test(v)).map(v => v.trim())))];
function stripNames(s, names) {
  let out = String(s || '');
  for (const n of names) {
    const [head, sub] = n.split(/_(.*)/s);
    const subRe = sub.replace(/^\{(.*)\}$/s, '$1').replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
    const headRe = head.replace(/[.*+?^${}()|[\]\\]/g, '\\$&') + (/^\\[A-Za-z]+$/.test(head) ? '(?![A-Za-z])' : '');
    out = out.replace(new RegExp(headRe + '\\s*_\\s*(?:\\{\\s*' + subRe + '\\s*\\}' + (sub.replace(/^\{(.*)\}$/s, '$1').length === 1 ? '|' + subRe + '(?![A-Za-z0-9])' : '') + ')', 'g'), ' ');
  }
  return out;
}

// The variables a block introduces: its introduces list, the left-hand sides of ::= in its
// formula, and the variables its caption sets alone in math, such as $x$, $x, y$ or $i \in S$.
function introducedBy(b, mode = null) {
  const out = new Set();
  const baseOf = s => { const t = tokens(s).find(x => x.t === 'var'); return t ? t.base : null; };
  for (const v of b.introduces || []) { const x = baseOf(v); if (x) out.add(x); }
  const f = resolve((mode && b.variants && b.variants[mode]) || b.formula || tableFormulas(b, mode).join(' '), mode).replace(/\\sym\s*\{[^}]*\}/g, '');
  const VAR = String.raw`(?:\\[A-Za-z]+|[A-Za-z])(?:\s*_\{?[A-Za-z0-9]+\}?|\s*'|\s*\^\{?[A-Za-z0-9+]+\}?)*`;
  for (const m of f.matchAll(new RegExp('(' + VAR + '(?:\\s*,\\s*' + VAR + ')*)\\s*\\}*\\s*(?:&\\s*)?::=', 'g')))
    for (const v of m[1].split(',')) { const x = baseOf(v.replace(/[{}]/g, '')); if (x) out.add(x); }
  const cap = resolve(b.caption || '', mode);
  const ONE = new RegExp('^\\s*' + VAR + '(?:\\s*,\\s*' + VAR + ')*\\s*(?:(?:\\\\in|:|\\\\subseteq)\\s.*)?$');
  for (const m of cap.matchAll(/\$([^$]+)\$/g)) {
    const seg = m[1].replace(/\\sym\s*\{[^}]*\}\s*\{([^{}]*)\}/g, '$1');
    if (!ONE.test(seg)) continue;
    const head = seg.split(/\\in\b|:|\\subseteq/)[0];
    for (const v of head.split(',')) { const x = baseOf(v); if (x) out.add(x); }
  }
  return out;
}

module.exports = { cellsOf, rowVisible, tableRows, tableFormulas, tableTexts, proseMath, compoundNames, stripNames, introducedBy, closeGroup, arg, resolve, syms, covered, modesMentioned, tokens, variables, words, proseInFormula, GREEK };
