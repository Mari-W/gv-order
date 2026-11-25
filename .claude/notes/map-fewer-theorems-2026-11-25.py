"""Fewer theorems, 2026-11-25: keep the statements the soundness proof chains, drop variants and the overview block."""
import json, re, sys
p = sys.argv[1]; m = json.load(open(p)); n = m['notes']
sec = {s['id']: s for s in m['sections']}
bl = {b['id']: b for s in m['sections'] for b in s['blocks']}

def close(s, o):
  d = 1; t = o + 1
  while d:
    if s[t] == '\\': t += 2; continue
    d += {'{': 1, '}': -1}.get(s[t], 0); t += 1
  return t
def grab(f, key):
  pre = r'\sym{' + key + '}'
  i = f.index(pre); return f[i:close(f, i + len(pre))]
SEP = r' \\[1.5ex] '
LF = lambda x: r'\inmodeplain{lf}{ \\[1.5ex] }\inmode{lf}{' + x + '}'
def rows(*xs): return r'\begin{array}{l}' + ''.join(xs) + r'\end{array}'

# overview block goes
th = sec['theorems']['blocks']; th[:] = [b for b in th if b['id'] != 'th-chain']

# adequacy: the forms soundness uses
f = bl['th-adeq']['formula']
bl['th-adeq']['formula'] = rows(grab(f, 'th.adequacy-h'), LF(grab(f, 'th.lf-sems-adequacy')))
bl['th-adeq']['caption'] = r"A closed process in the semantic judgment of [[sj-all]] at a consistent world is deadlock free. The proof reads the readiness of [[rd]]. \inmode{lf}{A closed process in the lock-free judgment at a [[t-lf-wf|ranked world]] is lock free, as [[sem-props]] defines. The measure is the rank of the awaited point and the counter of the [[soup|lock-free process relation]].}"

# composition: P-Term and P-Connect at the worlds of typing
f = bl['th-compose']['formula']
bl['th-compose']['formula'] = rows(grab(f, 'th.sem-p-term'), SEP, grab(f, 'th.sem-p-connect-sw'), LF(grab(f, 'th.lf-p-term')), LF(grab(f, 'th.lf-p-connect')))
bl['th-compose']['caption'] = r"A safe thread is a safe process, and two safe processes connected at dual interfaces form a safe process at the join of their worlds, in the [[p-rel|process relation]]. A component proved safe without typing therefore composes with typed components. \inmode{lf}{The same holds for the lock-free judgment.}"

# terms: the fundamental theorem, and at kappa_L
f = bl['th-terms']['formula']
bl['th-terms']['formula'] = rows(grab(f, 'th.fundamental'), LF(grab(f, 'th.live-fundamental-ranked')))
bl['th-terms']['caption'] = r"A typed term is in the semantic term judgment of [[sj-all]] at each consistent extension of its world. The proof is one induction on the derivation. \inmode{lf}{A term typed at a finite bound is in the judgment at $\kappa_L$, and it has [[fu|fuel]] under the annotations of [[ty-ann]].}"

# conservativity: one statement
f = bl['th-conserv']['formula']
bl['th-conserv']['formula'] = rows(r'\inmode{lf}{' + grab(f, 'th.conservative') + '}')
bl['th-conserv']['caption'] = r"The annotated judgment at $N = \infty$, with the annotations of [[ty-ann]] at $\infty$, types the same terms as deadlock-free typing. Erasing the annotations of a lock-free typing gives a deadlock-free typing."

# drop notes nothing uses any more
txt = json.dumps(m, ensure_ascii=False)
for k in ['th.adequacy', 'th.lf-adequacy', 'th.sem-p-connect', 'th.fsem-of-cost', 'th.typed-dftyped']:
  if txt.count('sym{' + k + '}') == 0: n.pop(k, None)
for s in m['sections']:
  for b in s['blocks']:
    if 'usedIn' in b: b['usedIn'] = [u for u in b['usedIn'] if u != 'th-chain']
json.dump(m, open(p, 'w'), ensure_ascii=False, indent=1); open(p, 'a').write('\n')
