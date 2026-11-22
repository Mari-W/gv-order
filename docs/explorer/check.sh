#!/bin/sh
# Check the relation map in one command: docs/explorer/check.sh [--list CATEGORY|--list]
#
# Runs tools/proof-map/check.js once on map.json against v2/ with the private extension in ext/,
# and prints one table with five steps in order:
#   1 schema       the JSON against tools/proof-map/schema.json, and the extension loads
#   2 proof-map    names against the Rocq sources, hovers, links, deviations, variables
#   3 DF-LEAK      nothing of the lock-free view shows in the deadlock-free mode
#   4 writing      the prose rules of the base and of ext/gv-check.js
#   5 MathJax      every formula and every $..$ in every mode renders
# MAP_FILE=path checks another map with the same steps.
# Exit status 1 when a step has an error. Warnings and info do not fail the check.
# --list prints every finding of one category (or of all) after the table.
#
# MathJax needs mathjax-full in tools/proof-map/node_modules (gitignored):
#   npm install --prefix tools/proof-map --no-save --no-package-lock mathjax-full@3.2.2
here=$(cd "$(dirname "$0")" && pwd)
repo=$(cd "$here/../.." && pwd)
pm="$repo/tools/proof-map"
tmp=$(mktemp -d "${TMPDIR:-/tmp}/map-check.XXXXXX") || exit 2
trap 'rm -rf "$tmp"' EXIT
list=""
if [ "$1" = "--list" ]; then list="--list"; [ -n "$2" ] && list="--list $2"; fi
mj=""
[ -f "$pm/node_modules/mathjax-full/js/mathjax.js" ] && mj="--mathjax $pm/node_modules"
# shellcheck disable=SC2086
node "$pm/check.js" "${MAP_FILE:-$here/map.json}" --root "$repo/v2" --json "$tmp/findings.json" $mj $list --max 0 > "$tmp/out.txt"
status=$?
[ -f "$tmp/findings.json" ] || { cat "$tmp/out.txt"; echo "check.js failed (status $status)"; exit 2; }
[ -n "$list" ] && sed -n '/^errors\|^warnings\|^info/,$p' "$tmp/out.txt" | grep -v '^ *… ' | sed '$d'
MJ_RAN=$([ -n "$mj" ] && echo 1 || echo 0) node - "$tmp/findings.json" <<'EOF'
const f = require(process.argv[2]);
const steps = [
  ['1 schema', c => c === 'schema' || c === 'extension'],
  ['3 DF-LEAK', c => c === 'gv:df-leak'],
  ['4 writing', c => c.startsWith('prose:') || c === 'gv:unicode-math'],
  ['5 MathJax', c => c === 'mathjax'],
  ['2 proof-map', () => true]
];
const of = c => steps.find(([, t]) => t(c))[0];
const rows = new Map(steps.map(([n]) => [n, { error: 0, warning: 0, info: 0, cats: new Map() }]).sort());
for (const x of f) { const r = rows.get(of(x.cat)); r[x.sev]++; r.cats.set(x.cat + ' (' + x.sev[0] + ')', (r.cats.get(x.cat + ' (' + x.sev[0] + ')') || 0) + 1); }
if (process.env.MJ_RAN !== '1') rows.get('5 MathJax').skipped = true;
const pad = (s, n) => String(s).padEnd(n), lpad = (s, n) => String(s).padStart(n);
console.log(`${pad('step', 13)}${lpad('errors', 7)}${lpad('warn', 7)}${lpad('info', 7)}  status  categories`);
console.log('-'.repeat(100));
let bad = 0;
for (const [name, r] of rows) {
  const st = r.skipped ? 'ERROR' : r.error ? 'FAIL' : 'ok';
  if (r.skipped || r.error) bad++;
  const cats = r.skipped ? 'mathjax-full not installed, see the head of check.sh' : [...r.cats].sort((a, b) => b[1] - a[1]).map(([c, n]) => `${c} ${n}`).join(', ');
  console.log(`${pad(name, 13)}${lpad(r.error, 7)}${lpad(r.warning, 7)}${lpad(r.info, 7)}  ${pad(st, 6)}  ${cats}`);
}
const tot = k => [...rows.values()].reduce((a, r) => a + r[k], 0);
console.log('-'.repeat(100));
console.log(`${pad('total', 13)}${lpad(tot('error'), 7)}${lpad(tot('warning'), 7)}${lpad(tot('info'), 7)}  ${bad ? 'FAIL' : 'ok'}`);
console.log('details: node tools/proof-map/check.js docs/explorer/map.json --list CATEGORY  (or docs/explorer/check.sh --list CATEGORY)');
process.exit(bad ? 1 : 0);
EOF
