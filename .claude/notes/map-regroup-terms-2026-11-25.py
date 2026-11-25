"""Split the block "Lemmas about terms" (th-terms) by topic, 2026-11-25.

th-terms keeps the fundamental theorem for terms and, in LF mode, fuel of typed terms.
Soundness of one program joins th-sound. The two static lemmas (two closes, instantiation)
become a block in the typing section. The bind lemma joins the semantic section after e-obl.
The let x = e in x remark leaves the map."""
import json, sys
p = sys.argv[1]; m = json.load(open(p)); n = m['notes']
sec = {s['id']: s for s in m['sections']}
bl = {b['id']: (s, b) for s in m['sections'] for b in s['blocks']}

def close(s, o):
  d = 1; t = o + 1
  while d:
    if s[t] == '\\': t += 2; continue
    d += {'{': 1, '}': -1}.get(s[t], 0); t += 1
  return t
def grab(f, key, wrap=None):
  """the text of \\sym{key}{...}, or of \\inmode{lf}{\\sym{key}{...}} when wrap is given"""
  pre = (wrap or '') + r'\sym{' + key + '}'
  i = f.index(pre); o = i + len(pre)
  assert f[o] == '{', key
  e = close(f, o)
  if wrap: e = close(f, i + len(r'\inmode{lf}') )
  return f[i:e]

_, tt = bl['th-terms']; f = tt['formula']
src = grab(f, 'th.soundness-source')
lfsrc = grab(f, 'th.lf-soundness-source', r'\inmode{lf}{')
wfit = grab(f, 'th.wfit', r'\inmode{lf}{')
fund = grab(f, 'th.fundamental')
fundt = grab(f, 'th.fundamental-typed', r'\inmode{lf}{')
live = grab(f, 'th.live-fundamental', r'\inmode{lf}{')
livet = grab(f, 'th.live-fundamental-typed', r'\inmode{lf}{')
liver = grab(f, 'th.live-fundamental-ranked', r'\inmode{lf}{')
cl2 = grab(f, 'th.cl2-needs')
bind = grab(f, 'th.Erel-bind')
i = f.index(r'\inmode{lf}{\begin{array}{l}\sym{th.cost-fundamental}'); cost = f[i:close(f, i + len(r'\inmode{lf}'))]
pinst = grab(f, 'th.pinst')
assert 'th.let-var' in f

SEP = r' \\[1.5ex] '
LSEP = r'\inmodeplain{lf}{ \\[1.5ex] }'
tt['title'] = 'Fundamental theorem for terms'
tt['formula'] = r'\begin{array}{l}' + fund + LSEP + fundt + LSEP + live + LSEP + livet + LSEP + liver + LSEP + wfit + LSEP + cost[len(r'\inmode{lf}{\begin{array}{l}'):-len(r'\end{array}}')].replace(r'\sym{th.cost-fundamental}', r'\inmode{lf}{\sym{th.cost-fundamental}', 1).replace(r' \\[1.5ex] \sym{th.fsem-of-cost}', r'}' + LSEP + r'\inmode{lf}{\sym{th.fsem-of-cost}', 1) + '}' + r'\end{array}'
tt['caption'] = r"A typed term is in the semantic term judgment of [[sj-all]] at each consistent extension of its world. The proof is one induction on the derivation, with one compatibility lemma per rule. \inmode{lf}{The same holds at $\kappa_L$, at a finite bound and under excluded middle also at ranked extensions, and a typed term at a finite bound has [[fu|fuel]] with its values in [[fv]].}"
tt['why'] = r"The case of P-Term in the fundamental theorem for processes is this theorem."
keep = {'static/Fundamental.v', 'cost/CostFund.v'}
tt['source'] = [r for r in tt['source'] if r['file'] in keep]

# soundness of one program joins th-sound
_, ts = bl['th-sound']
assert ts['formula'].endswith(r'\end{array}')
ts['formula'] = ts['formula'][:-len(r'\end{array}')] + SEP + src + LSEP + lfsrc + r'\end{array}'
ts['caption'] += r" A closed term typed over a consistent world is deadlock free as a one-thread process\inmode{lf}{, and lock free at a finite bound over a ranked world}."
ts['source'] = ts['source'] + [{"file": "static/FundamentalProc.v", "names": ["soundness_source"]}, {"file": "soup/LFCompose.v", "names": ["lf_soundness_source"]}]

# the two static lemmas join the typing section
sl = {"id": "t-lemmas", "title": "Two static lemmas",
  "formula": r'\begin{array}{l}' + cl2 + SEP + pinst + r'\end{array}',
  "caption": r"Two closes in sequence need the point of the first below the dual point of the second, which the rejections of the [[ex-flag|self-computed flag]] and of the [[ex-gennew|creations with exits]] use. A derivation stays a derivation when a substitution $\sigma$ instantiates its point variables, over each context $\Gamma'$ that derives the instantiated facts.\inmode{lf}{ The rejection of [[ex-forkjoin|recursive fork-join]] at a finite bound uses the first lemma.}",
  "why": "Both are inversions or substitutions of the static system, with no reference to the relation.",
  "source": [{"file": "examples/SemBranch.v", "names": ["cl2_needs"]}, {"file": "examples/ForkJoin.v", "names": ["fj_wait_needs"]}, {"file": "static/PointSubstTyped.v", "names": ["typed_pinst"]}]}
ty = sec['typing']['blocks']; ty.insert([b['id'] for b in ty].index('p-typing'), sl)

# the bind lemma joins the semantic section
bd = {"id": "e-bind", "title": "The bind lemma", "formula": bind,
  "caption": r"$E$ is closed under the evaluation frames of [[sem-ctx]]. The case of [[r-fun|E-App]] and the other rules with subterms use it.",
  "why": r"A frame waits for the value of its hole, so the term relation of the frame follows from the term relation of the hole and of each value it may return.",
  "source": [{"file": "compat/Bind.v", "names": ["Erel_bind"]}]}
se = sec['semantic']['blocks']; se.insert([b['id'] for b in se].index('e-obl') + 1, bd)

n.pop('th.let-var', None)
json.dump(m, open(p, 'w'), ensure_ascii=False, indent=1); open(p, 'a').write('\n')
