"""Write .claude/notes/map-faithfulness.md: every recorded difference between the map and the Rocq, by kind.

Run from the repo root after each map change: python3 .claude/notes/map-faithfulness.py
"""
import json, collections, subprocess
m = json.load(open('docs/explorer/map.json'))
rev = subprocess.run(['git', 'rev-parse', '--short', 'HEAD'], capture_output=True, text=True).stdout.strip()
ORDER = [('other', 'Statements with no Rocq counterpart'),
         ('simplified', 'The map says less than the Rocq'),
         ('merged', 'One notion in the map, two in the Rocq'),
         ('planned', 'Planned, not in the Rocq yet'),
         ('renamed', 'Renamed'),
         ('notation', 'Notation')]
by = collections.defaultdict(list)
def collect(o, where):
  for d in o.get('deviations') or []:
    by[d['kind']].append((where, d.get('names', []), d['reason']))
for s in m['sections']:
  for b in s['blocks']: collect(b, 'block ' + b['id'])
for k, n in m['notes'].items(): collect(n, 'note ' + k)
out = ['# Faithfulness of the map', '',
       f'Generated from docs/explorer/map.json at {rev} by map-faithfulness.py. Do not edit by hand.', '',
       'check.sh confirms that every cited Rocq name exists. No tool compares a formula with the statement it cites. '
       'The formulas are checked by hand. The differences below are the recorded ones.', '',
       '| kind | count |', '|---|---|'] + [f'| {k} | {len(by[k])} |' for k, _ in ORDER if by[k]] + ['']
for k, title in ORDER:
  if not by[k]: continue
  out += [f'## {title} ({k}, {len(by[k])})', '']
  for where, names, reason in by[k]:
    nm = f" ({', '.join('`' + x + '`' for x in names)})" if names else ''
    out.append(f'- **{where}**{nm}. ' + reason.replace('\n', ' '))
  out.append('')
open('.claude/notes/map-faithfulness.md', 'w').write('\n'.join(out))
print({k: len(by[k]) for k, _ in ORDER})
