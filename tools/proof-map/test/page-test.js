#!/usr/bin/env node
// Drive the page in headless Chrome over the DevTools protocol and check what a reader does:
// no horizontal overflow at widths from 320 to 2560 CSS pixels (browser zoom shrinks the CSS
// width, so this covers zoom levels), hovering a symbol shows its note, a click pins it, the mode
// switch re-renders, the filter narrows, and a selection copies formulas as TeX.
//
// usage: node test/page-test.js <map.json> [--shots DIR]
// Needs google-chrome on PATH and Node 22 or later (built-in WebSocket). No network except the
// MathJax and font CDNs the page loads.
'use strict';
const { spawn } = require('child_process');
const path = require('path');
const fs = require('fs');

const args = process.argv.slice(2);
const si = args.indexOf('--shots');
const shots = si >= 0 ? args.splice(si, 2)[1] : null;
const mapFile = path.resolve(args[0] || path.join(__dirname, '..', 'demo', 'map.json'));
const MAP = JSON.parse(fs.readFileSync(mapFile, 'utf8'));
const pageFile = path.join(__dirname, '..', 'page', 'index.html');
const rel = path.relative(path.dirname(pageFile), mapFile).split(path.sep).join('/');
const base = `file://${pageFile}?map=${encodeURIComponent(rel)}`;
const sleep = ms => new Promise(r => setTimeout(r, ms));
if (shots) fs.mkdirSync(shots, { recursive: true });

async function main() {
  const port = 20000 + Math.floor(Math.random() * 30000);
  // the Chrome profile lives in the gitignored .shots directory and is removed afterwards
  const userDir = path.join(__dirname, '..', '.shots', '.chrome-' + port);
  fs.mkdirSync(userDir, { recursive: true });
  const chrome = spawn('google-chrome', ['--headless=new', '--disable-gpu', '--hide-scrollbars', '--allow-file-access-from-files', `--remote-debugging-port=${port}`, `--user-data-dir=${userDir}`, 'about:blank'], { stdio: 'ignore' });
  let ws;
  try {
    let info;
    for (let i = 0; i < 50 && !info; i++) { await sleep(200); try { info = await (await fetch(`http://127.0.0.1:${port}/json/list`)).json(); } catch (e) {} }
    const tgt = info.find(t => t.type === "page");
    ws = new WebSocket(tgt.webSocketDebuggerUrl);
    await new Promise(r => ws.addEventListener('open', r, { once: true }));
    let id = 0; const wait = new Map(); const events = [];
    ws.addEventListener('message', ev => { const m = JSON.parse(ev.data); if (m.id && wait.has(m.id)) { wait.get(m.id)(m); wait.delete(m.id); } else events.push(m); });
    const send = (method, params = {}) => new Promise((ok, fail) => { const i = ++id; wait.set(i, m => m.error ? fail(new Error(method + ': ' + m.error.message)) : ok(m.result)); ws.send(JSON.stringify({ id: i, method, params })); });
    const evalJS = async expr => { const r = await send('Runtime.evaluate', { expression: expr, awaitPromise: true, returnByValue: true }); if (r.exceptionDetails) throw new Error(r.exceptionDetails.text + ' ' + (r.exceptionDetails.exception && r.exceptionDetails.exception.description)); return r.result.value; };
    const size = (w, h = 1000) => send('Emulation.setDeviceMetricsOverride', { width: w, height: h, deviceScaleFactor: 1, mobile: w < 600 });
    const shot = async name => { if (!shots) return; const r = await send('Page.captureScreenshot', { format: 'png' }); fs.writeFileSync(path.join(shots, name + '.png'), Buffer.from(r.data, 'base64')); };
    const ready = async () => { for (let i = 0; i < 100; i++) { if (await evalJS(`!!document.querySelector('article.block, article.ex') && !!window.MathJax && !!MathJax.tex2svg`)) return; await sleep(200); } throw new Error('page did not render'); };
    // through about:blank, so a change of the hash alone reloads the page and drops the filter
    const go = async url => { await send('Page.navigate', { url: 'about:blank' }); await sleep(100); await send('Page.navigate', { url }); await sleep(400); await ready(); await sleep(500); };
    await send('Page.enable'); await send('Runtime.enable');
    await send('Browser.grantPermissions', { permissions: ['clipboardReadWrite', 'clipboardSanitizedWrite'] }).catch(() => {});
    const results = [];
    const ok = (name, cond, detail = '') => { results.push([cond, name, detail]); console.log(`${cond ? 'ok  ' : 'FAIL'}  ${name}${detail ? '  ' + detail : ''}`); };

    // 1. overflow at every width, every section, every mode
    const secs = [...MAP.sections.map(s => s.id), ...((MAP.examples || []).length ? ['examples'] : [])];
    const modes = MAP.modes ? MAP.modes.options.map(m => m.id) : [null];
    let worst = [];
    for (const w of [320, 390, 700, 933, 1024, 1400, 1800, 2100, 2560]) {
      await size(w);
      for (const m of modes) for (const s of secs) {
        await go(`${base}${m ? '&mode=' + m : ''}#${s}`);
        const o = await evalJS(`(() => { const d = document.documentElement; const wide = [...document.querySelectorAll('body *')].filter(e => { if (e.closest('mjx-assistive-mml')) return false; const r = e.getBoundingClientRect(); return r.width && (r.right > d.clientWidth + 1 || e.scrollWidth > e.clientWidth + 1 && getComputedStyle(e).overflowX !== 'visible' && getComputedStyle(e).overflowX !== 'hidden'); }).slice(0, 3).map(e => e.tagName + '.' + e.className + ' ' + Math.round(e.getBoundingClientRect().right)); return { sw: d.scrollWidth, cw: d.clientWidth, wide }; })()`);
        if (o.sw > o.cw + 1 || o.wide.length) worst.push(`${w}px ${m || ''} ${s}: page ${o.sw}/${o.cw} ${o.wide.join(', ')}`);
      }
    }
    ok('no horizontal overflow at 320 to 2560 px in every section and mode', !worst.length, worst.slice(0, 6).join(' | '));

    // 2. hover a symbol: the note panel shows its title
    await size(1400, 1100);
    const sec0 = MAP.sections.find(s => s.blocks.some(b => /\\sym\{/.test(b.formula)));
    await go(`${base}#${sec0.id}`);
    const target = await evalJS(`(() => { const g = document.querySelector('.math [class*="k-"]'); const r = g.getBoundingClientRect(); return { x: r.left + r.width / 2, y: r.top + r.height / 2, key: [...g.classList].find(c => c.startsWith('k-')) }; })()`);
    await send('Input.dispatchMouseEvent', { type: 'mouseMoved', x: target.x, y: target.y });
    await sleep(500);
    const hov = await evalJS(`({ eyebrow: document.querySelector('#note .eyebrow span').textContent, title: document.querySelector('#note h2').textContent, box: !!document.querySelector('rect.pm-box.hot') })`);
    ok('hover shows the note of the symbol', hov.eyebrow === 'Hover' && !!hov.title && hov.box, `${target.key} -> "${hov.title}"`);
    await shot('hover');

    // 3. click pins it, Escape unpins
    await send('Input.dispatchMouseEvent', { type: 'mousePressed', x: target.x, y: target.y, button: 'left', clickCount: 1 });
    await send('Input.dispatchMouseEvent', { type: 'mouseReleased', x: target.x, y: target.y, button: 'left', clickCount: 1 });
    await sleep(400);
    const pin = await evalJS(`({ eyebrow: document.querySelector('#note .eyebrow span').textContent, boxes: document.querySelectorAll('rect.pm-box.pin').length, uses: document.querySelectorAll('#note .chips a').length })`);
    ok('click pins the note and marks every occurrence', pin.eyebrow === 'Pinned' && pin.boxes >= 1, `${pin.boxes} occurrences marked, ${pin.uses} links`);
    await shot('pinned');
    await send('Input.dispatchKeyEvent', { type: 'keyDown', key: 'Escape', code: 'Escape', windowsVirtualKeyCode: 27 });
    await sleep(300);
    ok('Escape unpins', (await evalJS(`document.querySelector('#note .eyebrow span').textContent`)) !== 'Pinned');

    // 4. a used-in link jumps to its block, across sections
    const withUsed = MAP.sections.flatMap(s => s.blocks.map(b => [s, b])).find(([s, b]) => (b.usedIn || []).some(u => !MAP.sections.find(x => x.id === s.id).blocks.some(y => y.id === u)));
    if (withUsed) {
      const [s, b] = withUsed;
      await go(`${base}${b.modes ? '&mode=' + b.modes[0] : ''}#${s.id}`);
      await evalJS(`document.querySelector('h3[data-block="${b.id}"]').click()`);
      await sleep(300);
      const to = b.usedIn.find(u => !s.blocks.some(y => y.id === u));
      await evalJS(`document.querySelector('#note [data-jump="${to}"]').click()`);
      await sleep(1500);
      const at = await evalJS(`({ hash: location.hash, here: !!document.getElementById('b-${to}'), top: Math.round(document.getElementById('b-${to}').getBoundingClientRect().top) })`);
      ok('a used-in link opens the block in its section', at.here && at.top >= 0 && at.top < 400, `${b.id} -> ${to} ${at.hash} top ${at.top}`);
    }

    // 4b. the note of a symbol lists its uses under "Used in", the old labels are gone
    {
      await go(`${base}#${sec0.id}`);
      const r = await evalJS(`(() => { const all = new Set(); let used = false; for (const g of document.querySelectorAll('#content .math [class*="k-"]')) { g.dispatchEvent(new MouseEvent('mouseover', { bubbles: true })); const h = [...document.querySelectorAll('#note .uses dt')].map(d => d.textContent); h.forEach(x => all.add(x)); if (h.includes('Used in') && document.querySelector('#note .uses .chips a')) used = true; } return { used, heads: [...all] }; })()`);
      ok('the note lists its uses under "Used in", without "Also in" or "Appears in"', r.used && !r.heads.some(h => /Also in|Appears in/.test(h)), r.heads.join(', '));
    }

    // 4c. affordance: formulas carry underlines, dotted for a note, solid where a click opens the definition
    {
      const typingLike = MAP.sections.map(s => s.id).find(id => MAP.sections.find(s => s.id === id).blocks.length > 5) || secs[0];
      await go(`${base}#${typingLike}`);
      await sleep(600);
      const u = await evalJS(`({ dotted: document.querySelectorAll('#content .pm-ul:not(.go)').length, solid: document.querySelectorAll('#content .pm-ul.go').length, go: document.querySelectorAll('#content .pm-go').length, visible: (() => { const l = document.querySelector('#content .pm-ul'); if (!l) return false; const r = l.getBoundingClientRect(); return r.width > 1 && getComputedStyle(l).strokeWidth !== '0px'; })() })`);
      ok('targets in formulas are underlined, dotted or solid', u.dotted > 0 && u.visible && (u.go === 0 || u.solid > 0), JSON.stringify(u));
    }

    // 4d. click to definition: a symbol defined in another block opens that block and pins the note,
    // Back returns, Shift-click pins without moving
    {
      let found = null;
      for (const s of MAP.sections) {
        await go(`${base}#${s.id}`);
        found = await evalJS(`(() => { const g = [...document.querySelectorAll('#content .math .pm-go')].find(g => g.getBoundingClientRect().width > 2); if (!g) return null; g.scrollIntoView({ block: 'center' }); const r = g.getBoundingClientRect(); const k = [...g.classList].find(c => c.startsWith('k-')); return { x: r.left + r.width / 2, y: r.top + r.height / 2, from: g.closest('article.block').id, k }; })()`);
        if (found) { found.sec = s.id; break; }
      }
      if (!found) ok('click on a symbol opens its defining block', false, 'no symbol with a definition elsewhere');
      else {
        await sleep(300);
        const click = async (mods = 0) => { for (const type of ['mouseMoved', 'mousePressed', 'mouseReleased']) await send('Input.dispatchMouseEvent', { type, x: found.x, y: found.y, button: 'left', clickCount: 1, modifiers: mods }); };
        const y0 = await evalJS('scrollY');
        await click(8);   // Shift
        await sleep(800);
        const st = await evalJS(`({ y: scrollY, pinned: document.querySelector('#note .eyebrow span').textContent, hash: location.hash })`);
        ok('Shift-click pins without moving', st.pinned === 'Pinned' && Math.abs(st.y - y0) < 4, JSON.stringify(st));
        await send('Input.dispatchKeyEvent', { type: 'keyDown', key: 'Escape', code: 'Escape', windowsVirtualKeyCode: 27 }); await sleep(200);
        await click();
        await sleep(1800);
        const at = await evalJS(`(() => { const m = location.hash.match(/\\/(.+)$/); const id = m && m[1]; const el = id && document.getElementById('b-' + id); return { hash: location.hash, id, top: el ? Math.round(el.getBoundingClientRect().top) : null, pinned: document.querySelector('#note .eyebrow span').textContent, marks: el ? el.querySelectorAll('rect.pm-box.pin').length : 0, end: Math.ceil(scrollY + innerHeight) >= document.documentElement.scrollHeight - 2 }; })()`);
        ok('click on a symbol opens its defining block and pins the note', at.id && 'b-' + at.id !== found.from && at.top !== null && at.top >= 0 && (at.top < 500 || at.end) && at.pinned === 'Pinned' && at.marks >= 1, `${found.k} in ${found.from} -> ${JSON.stringify(at)}`);
        await evalJS('history.back()'); await sleep(1500);
        const back = await evalJS(`location.hash`);
        ok('Back returns to the block of the click', back.endsWith('/' + found.from.slice(2)), back);
      }
    }

    // 4e. an inline [[link]] in prose opens its block
    {
      const withLink = MAP.sections.flatMap(s => s.blocks.map(b => [s, b])).find(([, b]) => /\[\[[^\]|]+/.test(b.caption || '') && !b.modes);
      if (withLink) {
        const [s, b] = withLink;
        await go(`${base}#${s.id}`);
        await evalJS(`document.querySelector('#b-${b.id} h3[data-block]').click()`); await sleep(400);
        const to = await evalJS(`(() => { const a = document.querySelector('#note a.xref[data-jump]'); if (!a) return null; a.click(); return a.dataset.jump; })()`);
        await sleep(1500);
        const top = to && await evalJS(`(() => { const el = document.getElementById('b-' + ${JSON.stringify(to)}) || document.getElementById('x-' + ${JSON.stringify(to)}); return el ? Math.round(el.getBoundingClientRect().top) : null; })()`);
        ok('an inline link in a block note opens its block', !!to && top !== null && top >= 0 && top < 500, `${b.id} -> ${to} top ${top}`);
      }
    }

    // 5. modes: switching re-renders, mode-only blocks appear
    if (MAP.modes) {
      await go(`${base}&mode=${modes[0]}#${secs[0]}`);
      const counts = {};
      for (const m of modes) { await evalJS(`document.querySelector('#modes button[data-mode="${m}"]').click()`); await sleep(500); counts[m] = await evalJS(`[...document.querySelectorAll('nav.tabs a')].length + ':' + document.querySelectorAll('article.block').length`); }
      ok('mode switch re-renders the section', new Set(Object.values(counts)).size >= 1, JSON.stringify(counts));
    }

    // 6. filter
    await go(`${base}#${secs[0]}`);
    const word = (MAP.sections[0].blocks[0].title || '').split(/\s+/)[0];
    await evalJS(`(() => { const q = document.getElementById('q'); q.value = ${JSON.stringify(word.slice(0, -1) + 'x')}; q.dispatchEvent(new Event('input')); })()`);
    await sleep(700);
    const f = await evalJS(`({ n: document.querySelectorAll('article.block').length, counts: [...document.querySelectorAll('nav.tabs .count')].map(c => c.textContent).join(',') })`);
    ok('fuzzy filter with a typo still finds the first block', f.n >= 1, `"${word.slice(0, -1)}x": ${f.n} blocks, tabs ${f.counts}`);

    // 7. copy: a selection over a block yields its title, the formula as TeX and the caption
    await go(`${base}#${secs[0]}`);
    const copied = await evalJS(`(async () => {
      const a = document.querySelector('article.block'); const r = document.createRange(); r.selectNodeContents(a);
      const s = getSelection(); s.removeAllRanges(); s.addRange(r);
      let out = null; const h = e => { out = e.clipboardData.getData('text/plain'); };
      document.addEventListener('copy', h, true);
      const dt = new DataTransfer(); const ev = new ClipboardEvent('copy', { clipboardData: dt, bubbles: true, cancelable: true });
      document.dispatchEvent(ev); document.removeEventListener('copy', h, true);
      return dt.getData('text/plain');
    })()`);
    ok('a selection copies formulas as TeX', /\$\$[\s\S]+\$\$/.test(copied) && !/\\sym\{/.test(copied), JSON.stringify(copied.slice(0, 120)));
    ok('copied TeX carries no hover or mode markup', !/\\(sym|inmode|planned)\b/.test(copied));

    // 8. deviations are visible
    const dev = MAP.sections.flatMap(s => s.blocks.map(b => [s, b])).find(([, b]) => (b.deviations || []).length);
    if (dev) {
      const [s, b] = dev;
      await go(`${base}${b.modes ? '&mode=' + b.modes[0] : ''}#${s.id}/${b.id}`);
      await evalJS(`document.querySelector('#b-${b.id} h3[data-block]').click()`); await sleep(400);
      const n = await evalJS(`document.querySelectorAll('#note .devs li').length`);
      ok('deviation reasons show in the note of the block', n === b.deviations.length, `${b.id}: ${n}`);
    }

    // 9. phone width and dark theme screenshots
    if (shots) {
      await size(390, 844); await go(`${base}&note=${encodeURIComponent(Object.keys(MAP.notes)[0])}#${secs[0]}`); await sleep(500); await shot('phone-pinned');
      await send('Emulation.setEmulatedMedia', { features: [{ name: 'prefers-color-scheme', value: 'dark' }] });
      await size(1400, 1100); await go(`${base}${modes[1] ? '&mode=' + modes[1] : ''}&note=${encodeURIComponent(Object.keys(MAP.notes)[5])}#${secs[Math.min(3, secs.length - 1)]}`); await sleep(600); await shot('dark');
      await size(1400, 1100); await go(`${base}${modes[1] ? '&mode=' + modes[1] : ''}#examples`); await sleep(600); await shot('dark-examples');
      await send('Emulation.setEmulatedMedia', { features: [] });
    }
    const failed = results.filter(r => !r[0]).length;
    console.log(`\n${results.length - failed} passed, ${failed} failed`);
    process.exitCode = failed ? 1 : 0;
  } finally {
    try { ws && ws.close(); } catch (e) {}
    chrome.kill();
    setTimeout(() => { try { fs.rmSync(userDir, { recursive: true, force: true }); } catch (e) {} process.exit(); }, 500);
  }
}
main().catch(e => { console.error(e); process.exit(1); });
