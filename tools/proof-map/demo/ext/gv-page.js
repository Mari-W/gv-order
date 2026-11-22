// Page extension of the GV relation map: verdict badges on examples.
// Each example may carry "x-gv-accepts": {df|sem|live|lf: {ok, N?, part?, rocq?}}, one verdict per
// judgment. The deadlock-free mode shows the deadlock-free verdicts only.
ProofMap.register({
  name: 'gv-verdicts',
  css: `
.gv-badges { display: flex; flex-wrap: wrap; gap: 6px; margin: 8px 0 2px; }
.gv-badge { display: inline-flex; align-items: baseline; gap: 5px; font: 500 0.8rem var(--body); padding: 1px 9px; border-radius: 999px; border: 1px solid var(--line); background: var(--bg); }
.gv-badge .mk { font-weight: 700; }
.gv-badge.yes { border-color: color-mix(in srgb, var(--accent) 45%, var(--line)); }
.gv-badge.yes .mk { color: var(--accent); }
.gv-badge.no { border-color: color-mix(in srgb, var(--warn) 45%, var(--line)); background: var(--warn-soft); }
.gv-badge.no .mk { color: var(--warn); }
.gv-badge .nm { color: var(--muted); }`,
  exampleHeader(x, { mode, esc }) {
    const acc = x['x-gv-accepts'];
    if (!acc) return '';
    const J = [['df', 'statically typed', 'deadlock free'], ['sem', 'semantically typed', 'deadlock free'], ['live', 'typed and guarded', 'live'], ['lf', 'statically typed', 'lock free']];
    return `<div class="gv-badges">${J.map(([m, judg, prop]) => {
      const a = acc[m];
      if (a === undefined || (mode === 'df' && m !== 'df' && m !== 'sem')) return '';
      const st = a.ok === true ? 'yes' : a.ok === false ? 'no' : 'na';
      const at = a.N !== undefined ? ` <span class="nm">at ${a.N === 'every' ? 'every N' : 'N = ' + esc(a.N)}</span>` : '';
      const part = a.part ? ` <span class="nm">(${st === 'no' ? 'fails at ' : ''}${esc(a.part)})</span>` : '';
      return `<span class="gv-badge ${st}" title="${esc(a.rocq || '')}"><span class="mk">${st === 'yes' ? '✓' : st === 'no' ? '✗' : '–'}</span>${st === 'no' ? 'not ' : ''}${judg}, <span class="nm">${prop}</span>${at}${part}</span>`;
    }).join('')}</div>`;
  }
});
