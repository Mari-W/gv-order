#!/usr/bin/env node
// One-time move of the explorer map to proof-map/1 (phase C, 2026-11-22). Kept for the record:
// docs/explorer/map.json is the source now, and this script is not run again.
//
// usage: node docs/explorer/attic/migrate.js
//
// 1. tools/proof-map/convert-explorer.js converts attic/data.js, the last output of attic/gen/,
//    with attic/overlay.json.
// 2. Mechanical fixes on the result:
//    - the overview blocks sr-reading, fu-vs and soup become native tables, each \text{..} of a
//      cell a sentence with the math between the words in $..$;
//    - a renamed or merged deviation with a reason for each note whose display name differs from
//      the Rocq name (the rename-undeclared warnings), from RENAMED below;
//    - ct-costs introduces the names \kappa_{DF} and \kappa_L;
//    - W\^{\prime} in prose, an escaped caret that MathJax rejects, becomes W^{\prime};
//    - the highlighting of example code keeps the operators and capitalised names of the old page.
'use strict';
const fs = require('fs');
const path = require('path');
const { execFileSync } = require('child_process');

const here = __dirname;
const explorer = path.join(here, '..');
const repo = path.join(explorer, '..', '..');
const out = path.join(explorer, 'map.json');
execFileSync('node', [path.join(repo, 'tools/proof-map/convert-explorer.js'), path.join(here, 'data.js'), out, '--root', '../../v2', '--overlay', path.join(here, 'overlay.json')], { stdio: 'inherit' });
const MAP = JSON.parse(fs.readFileSync(out, 'utf8'));
const T = require(path.join(repo, 'tools/proof-map/lib/tex.js'));

// ---------- tables ----------
// split at the separator outside groups and environments, as convert-explorer.js does
function topSplit(body, sep) {
  const res = []; let depth = 0, last = 0;
  for (let i = 0; i < body.length; i++) {
    if (body.startsWith('\\begin{', i)) { depth++; i += 5; continue; }
    if (body.startsWith('\\end{', i)) { depth--; i += 3; continue; }
    const c = body[i];
    if (sep === '\\\\' && c === '\\' && body[i + 1] === '\\' && depth === 0) {
      res.push(body.slice(last, i)); i += 2;
      const o = /^\s*\[[^\]]*\]/.exec(body.slice(i)); if (o) i += o[0].length;
      last = i; i--; continue;
    }
    if (c === '\\') { i++; continue; }
    if (c === '{') depth++; else if (c === '}') depth--;
    else if (sep === '&' && c === '&' && depth === 0) { res.push(body.slice(last, i)); last = i + 1; }
  }
  res.push(body.slice(last));
  return res;
}
// the body of \begin{array}{..} .. \end{array}
function arrayBody(t) {
  const m = /^\s*\\begin\{array\}\{[^}]*\}([\s\S]*)\\end\{array\}\s*$/.exec(t);
  if (!m) throw new Error('not an array: ' + t.slice(0, 60));
  return m[1];
}
// a cell of \text{..} groups and math between them -> prose with the math in $..$
function textCell(tex) {
  let s = tex.trim(), outS = '', i = 0;
  for (;;) {
    const j = s.indexOf('\\text{', i);
    const math = (j < 0 ? s.slice(i) : s.slice(i, j)).trim();
    if (math) outS += '$' + math + '$';
    if (j < 0) break;
    const open = j + 5, k = T.closeGroup(s, open);
    outS += s.slice(open + 1, k - 1);
    i = k;
  }
  return outS.replace(/\s+/g, ' ').trim();
}
const LF = '\u0001LF\u0001';
// rows of cells; a row the old map wrote as \inmodeplain{lf}{\\}\inmode{lf}{..}\inmodeplain{lf}{&}\inmode{lf}{..} is lock-free only
function rowsOf(body) {
  const b = body.replace(/\\inmodeplain\{lf\}\{\\\\\}/g, '\\\\' + LF).replace(/\\inmodeplain\{lf\}\{&\}/g, '&');
  return topSplit(b, '\\\\').filter(r => r.trim() && r.trim() !== '\\hline').map(r => {
    const lf = r.includes(LF);
    const cells = topSplit(r.replace(LF, ''), '&').map(c => {
      c = c.replace(/\\hline/g, '').trim();
      const m = /^\\inmode\{lf\}\{([\s\S]*)\}$/.exec(c);
      return m && T.closeGroup(c, c.indexOf('{', 8)) === c.length ? m[1].trim() : c;
    });
    return { lf, cells };
  });
}
const cell = c => /\\text\s*\{/.test(c) ? { text: textCell(c) } : c ? { formula: c } : { text: '' };
const trimRight = cs => { while (cs.length > 1 && cs[cs.length - 1].text === '') cs.pop(); return cs; };
const block = id => MAP.sections.flatMap(s => s.blocks).find(b => b.id === id);
const done = new Set();
function toTable(id, table) {
  const b = block(id);
  b.table = table; delete b.formula; done.add(id);
}

// sr-reading: a formula and a sentence per row
{
  const rows = rowsOf(arrayBody(block('sr-reading').formula)).map(({ lf, cells }) => {
    if (cells.length !== 2) throw new Error('sr-reading row with ' + cells.length + ' cells');
    const r = { formula: cells[0], text: textCell(cells[1]) };
    if (lf) r.modes = ['lf'];
    return r;
  });
  toTable('sr-reading', { rows });
}
// fu-vs: a head row, then a label and two cells per row
{
  const rows = rowsOf(arrayBody(block('fu-vs').formula));
  const [head, ...rest] = rows;
  toTable('fu-vs', {
    header: head.cells.map(c => c ? textCell(c) : ''),
    rows: rest.map(({ cells }) => ({ label: textCell(cells[0]), cells: cells.slice(1).map(cell) }))
  });
}
// soup: the state and its step on top, then the definition, its lines in four aligned columns
{
  const f = block('soup').formula;
  const outer = topSplit(arrayBody(f), '\\\\');
  if (outer.length !== 2) throw new Error('soup: expected two parts');
  const top = topSplit(arrayBody(outer[0].trim()), '\\\\').filter(r => r.trim()).map(r => ({ cells: [{ formula: r.trim() }] }));
  const main = rowsOf(arrayBody(outer[1].trim())).map(({ cells }) => {
    // a formula that ends in words: the words move to the comment column when it is empty
    const k = cells.findIndex(c => /\\text\s*\{/.test(c) && !/^\\text/.test(c.trim()));
    if (k >= 0 && k + 1 < cells.length && !cells[k + 1].trim()) {
      const at = cells[k].indexOf('\\text');
      cells[k + 1] = cells[k].slice(at); cells[k] = cells[k].slice(0, at).trim();
    }
    return { cells: trimRight(cells.map(cell)) };
  });
  toTable('soup', { align: 'rcll', rows: [...top, ...main] });
}

// ---------- names shown differently from the Rocq ----------
// note key -> [kind, reason]
const RENAMED = {
  'syn.values': ['renamed', 'The Rocq writes the injections as `Inj`, shown as $\\mathsf{inj}_i$, and `is_val` decides which terms are values.'],
  'proc.config': ['renamed', 'The Rocq type `gmap nat expr` of the thread map is shown as $\\mathbb{N} \\rightharpoonup \\mathsf{Expr}$, with $\\mathsf{Expr}$ for the type `expr` of terms.'],
  'sx.kappai': ['renamed', '`bfield false` is $0$ and `bfield true` is $1$, shown as the fields $\\kappa_{\\mathsf{false}}$ and $\\kappa_{\\mathsf{true}}$.'],
  'ev.event': ['renamed', 'The constructors `EvSolo`, `EvSync` and `EvOffer` of `event` are shown as $\\mathsf{solo}$, $\\mathsf{sync}$ and $\\mathsf{offer}$.'],
  'ev.tau': ['renamed', '`ev_tau` holds of the events whose process label is `PTau`, shown as a set of events. $\\mathsf{Event}$ is the type `event`.'],
  'sty.seqv': ['renamed', 'The relation `seqv` is shown as $\\approx$, and $\\mathsf{sty\\_df}$ inside it is the Rocq function `sty_df`.'],
  'ty.heads': ['renamed', 'The paper writes $\\mathsf{ap}$ for the Rocq function `heads`.'],
  'ann.tsum': ['renamed', '$\\mathsf{tk}(o)$ reads the tickets of the end $o$, and `tsum_ok` states the bound on their sum.'],
  'w.rord': ['renamed', '$<_R$ is the field `w_ord` of the world, and $\\mathsf{Point}_B$ is the set of points whose root lies in $B$.'],
  'w.lt': ['renamed', '`sw_lt` is defined as `tc (swstep W)`, shown as $\\mathsf{tc}$ of the facts and program order.'],
  'w.models': ['renamed', '$\\mathsf{world\\_wf}$, $\\mathsf{acyc}$ and $\\mathsf{wf}$ stand for `sworld_wf`, `sacyc` and `swf`, without the prefix for static worlds.'],
  'w.grow': ['renamed', '$\\mathsf{tc}$ and $\\mathsf{po}$ name the transitive closure and program order that the Rocq growth uses.'],
  'tj.hage': ['renamed', '$\\mathsf{def}(H - c)$ stands for the Rocq relations `thage` and `lage`, which age the ends and the closures of $H$ by $c$.'],
  'lfi.measure': ['renamed', '$\\mathsf{pt}\\,o$ is the point of $o$ that `we` reads from the ownership map.'],
  'w.tree': ['renamed', '$\\mathsf{tree}(a)$ is the set of points with root $a$, which `in_tree0` states for the root of the variable $0$.'],
  'ord.exprop': ['renamed', '$\\mathsf{EM}$ and $\\mathsf{FC}$ abbreviate `excluded_middle` and `functional_choice` of `FairRun.v`.'],
  'ct.give': ['renamed', 'The cost field `c_give` applies to $\\mathsf{send}$, $\\mathsf{select}$ and $\\mathsf{close}$, which the formula names by their keywords.'],
  'ct.takek': ['renamed', 'The cost field `c_take` applies to $\\mathsf{recv}$ and $\\mathsf{branch}$, which the formula names by their keywords.'],
  'rel.vsize': ['renamed', 'The Rocq builds the levels with `osfix` and measures types with `tsize`, and the formula names the measure and the ordinals $\\mathsf{measure}$ and $\\mathsf{Ord}$.'],
  'E.stop': ['renamed', '$(\\mathsf{stop})$ labels the first clause of `Ebody`.'],
  'E.ready': ['renamed', '$(\\mathsf{ready})$ labels the second clause of `Ebody`, and $\\mathsf{irred}$ is the Rocq predicate `irred`.'],
  'E.step': ['renamed', '$(\\mathsf{step})$ labels the clause that `Esteps` and `Eobl` state.'],
  'rel.lfp': ['renamed', '$(\\mathsf{lfp})$ marks the least fixpoints, the inductive types `Eind` and `Pind`.'],
  'rd.value': ['renamed', '$\\mathsf{done}$ labels the first conjunct of `ready_t`, and $\\mathsf{Val}$ is the set of terms that `is_val` accepts.'],
  'rd.below-rest': ['renamed', '$\\mathsf{ordered}$ labels the condition `below_rest`.'],
  'rd.p-term': ['renamed', '$\\mathsf{done}$ labels the first conjunct of `ready_p`.'],
  'rd.above-offered': ['renamed', '$\\mathsf{covered}$ labels the condition `above_offered`.'],
  'P-Stop': ['renamed', '$(\\mathsf{stop})$ labels the first clause of `Pclauses`.'],
  'P-Ready': ['renamed', '$(\\mathsf{ready})$ labels the second clause of `Pclauses`, and $\\mathsf{pirred}$ is the Rocq predicate `pirred`.'],
  'P-Step': ['renamed', '$(\\mathsf{step})$ labels the clause that `Psteps` states.'],
  'fuse.inj': ['renamed', '$\\mathsf{held}$ is the set of ends that `pheld` accepts in `fuse_ok`.'],
  'fuse.partners': ['renamed', '$\\mathsf{held}$ is the set of ends that `pheld` accepts in `fuse_ok`.'],
  'sr.pfuse': ['renamed', '$(h, D) \\cdot p$ is `pfuse h D p`, which renames the channels with `gch h`.'],
  'Q-Link': ['renamed', 'Q-Close, Q-Select, Q-Branch and Q-Link are the clauses `q_close`, `q_select`, `q_branch` and `q_link`, shown as the term obligations they repeat.'],
  'fu.rename': ['renamed', '$\\mathsf{injective}(g|_{\\mathrm{dom}\\,\\Phi})$ is `kinj g φ`, and `renk` renames the map.'],
  'fu.val': ['renamed', '$(\\mathsf{stop})$ labels the value clause of `Fdef`, and $\\mathsf{Val}$ is the set of terms that `is_val` accepts.'],
  'fu.step': ['renamed', '$(\\mathsf{step})$ labels the step clause of `Fdef`, stated through `Fobl`.'],
  'fu.Phi': ['merged', 'The Rocq keeps the protocols in a map `penv` and the counters and tickets in a map `cenv`, and the formula shows both in one map $\\Phi$ from $\\mathsf{End}$ to $\\mathsf{STy} \\times \\mathbb{N} \\times \\mathbb{N}$.'],
  'fu.rty': ['renamed', '$\\mathsf{thread}$ is the constructor `RThread` of `rty`.'],
  'fu.fspare': ['renamed', '$\\mathsf{positive}$ is the Rocq predicate `fspare`, and $\\mathsf{idle}$ is `idle_at`.'],
  'F-Beta': ['renamed', '$\\mathsf{Fobl}_\\beta$ is the clause `f_beta` of the fuel obligation.'],
  'sp.hold': ['renamed', '$K$ maps an end to a record `hold` of thread, point, counter and tickets, shown as a tuple in $\\mathbb{N} \\times \\mathsf{Point} \\times \\mathbb{N} \\times \\mathbb{N}$.'],
  'sp.own': ['renamed', '$\\mathsf{consistent}$ names the conjuncts of the record `soup_gen` about ownership.'],
  'sp.lfsemh': ['renamed', '$\\mathsf{world\\_wf}$ is `sworld_wf`, without the prefix for static worlds.'],
  'th.em': ['renamed', '$\\mathsf{EM}$ abbreviates `excluded_middle`.'],
  'th.crle': ['renamed', '$\\mathsf{cr}(\\Delta)$ reads the credits of $\\Delta$, a notation of the map with no Rocq function of this name.'],
  'th.ac': ['renamed', '$\\mathsf{FC}$ abbreviates `functional_choice`.'],
  'th.fair-run-exists': ['renamed', '$\\mathsf{EM}$ and $\\mathsf{DC}$ abbreviate the hypotheses `excluded_middle` and `dependent_choice`.'],
  'th.dc': ['renamed', '$\\mathsf{DC}$ abbreviates `dependent_choice`.'],
  'th.lf-padovani': ['renamed', '$\\mathsf{EM}$ and $\\mathsf{DC}$ abbreviate the hypotheses `excluded_middle` and `dependent_choice`.'],
  'th.chprem': ['renamed', '$\\mathsf{chan}_N$ names the premises of `lf_soup_term` on the channels $C_0$.'],
  'sr.FE': ['renamed', '$\\mathsf{thread}$ is the constructor `RThread` of `rty`, the result of a thread.']
};
for (const [k, [kind, reason]] of Object.entries(RENAMED)) {
  const n = MAP.notes[k];
  if (!n) throw new Error('no note ' + k);
  n.deviations = [...(n.deviations || []), { kind, reason, names: (n.source || []).flatMap(r => r.names) }];
}

// ---------- the rest ----------
block('ct-costs').introduces = ['\\kappa_{DF}', '\\kappa_L'];
let fixedCaret = 0;
const fix = t => typeof t === 'string' && t.includes('W\\^{\\prime}') ? (fixedCaret++, t.split('W\\^{\\prime}').join('W^{\\prime}')) : t;
for (const n of Object.values(MAP.notes)) for (const f of ['meaning', 'why', 'breaks', 'example']) n[f] = fix(n[f]);
MAP.syntax.operators = 'λ!?⊸⊗⊕→↦=<>|⟨⟩;.,+-';
MAP.syntax.constructors = true;
MAP.source.revision = execFileSync('git', ['-C', repo, 'rev-parse', '--short', 'HEAD']).toString().trim();

fs.writeFileSync(out, JSON.stringify(MAP, null, 1) + '\n');
console.log(`tables: ${[...done].join(', ')}; renamed deviations: ${Object.keys(RENAMED).length}; W\\^{\\prime} fixed in ${fixedCaret} fields`);
