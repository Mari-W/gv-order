"""Map fixes of 2026-11-25: step labels are l, the order judgment carries W, osfix leaves the formula, the cost of an event explained."""
import json, sys
p = sys.argv[1]; m = json.load(open(p)); n = m['notes']
bl = {b['id']: b for s in m['sections'] for b in s['blocks']}
def R(obj, key, a, b, cnt=None):
  s = obj[key]; c = s.count(a)
  assert c and (cnt is None or c == cnt), (key, a, c); obj[key] = s.replace(a, b)

# 1. labels: alpha is the ordinal index, step labels are \ell
R(bl['sem-labels'], 'formula', r'\alpha ::= ', r'\ell ::= ', 1)
R(bl['sem-ctx'], 'formula', r'\xrightarrow{\alpha}', r'\xrightarrow{\ell}', 2)
R(bl['sem-events'], 'formula', r'\mathsf{solo}_i\,\alpha\,k', r'\mathsf{solo}_i\,\ell\,k', 2)
R(n['se.parts'], 'meaning', r'\mathsf{solo}_i\,\alpha\,k', r'\mathsf{solo}_i\,\ell\,k')
for f in ['meaning', 'signature']: R(n['T-Act-Ctx'], f, r'\xrightarrow{\alpha}', r'\xrightarrow{\ell}')
for a in n['T-Act-Ctx']['args']:
  if a['name'] == r'\alpha': a['name'] = r'\ell'
R(n['rd.stable'], 'meaning', r"\forall \alpha, t'.\ t \xrightarrow{\alpha} t' \Rightarrow \alpha", r"\forall \ell, t'.\ t \xrightarrow{\ell} t' \Rightarrow \ell", 1)
R(n['sr.irred'], 'meaning', r"\exists \alpha, e'.\ e \xrightarrow{\alpha} e'", r"\exists \ell, e'.\ e \xrightarrow{\ell} e'", 1)

# 2. the order judgment reads the world: Gamma |-_W x < y
VD = '\\vdash'
def fix(s):
  # a \vdash without sub- or superscript, preceded in the same formula by \Gamma and
  # followed by \prec or \preccurlyeq before any colon, row break or column: the order judgment
  out = []; k = 0
  while True:
    t = s.find(VD, k)
    if t < 0:
      out.append(s[k:]); return ''.join(out)
    e = t + len(VD)
    nxt = s[e:e + 1]
    seg_b = s[max(0, t - 40):t].split('$')[-1]
    seg_a = s[e:e + 60].split('$')[0]
    cuts = [x for x in (seg_a.find(':'), seg_a.find('\\\\'), seg_a.find('&')) if x >= 0]
    seg_a = seg_a[:min(cuts)] if cuts else seg_a
    ok = nxt not in ('_', '^') and '\\Gamma' in seg_b and VD not in seg_b and '\\prec' in seg_a
    out.append(s[k:e] + ('_W' if ok else '')); k = e
def walk(x):
  if isinstance(x, dict): return {k: walk(v) for k, v in x.items()}
  if isinstance(x, list): return [walk(v) for v in x]
  if isinstance(x, str): return fix(x)
  return x
before = json.dumps(m, ensure_ascii=False).count('vdash_W')
m = walk(m); n = m['notes']; bl = {b['id']: b for s in m['sections'] for b in s['blocks']}
print('vdash_W added:', json.dumps(m, ensure_ascii=False).count('vdash_W') - before)
n['ctx.slt']['signature'] = r'\Gamma \vdash_W x \prec y \subseteq \mathsf{World} \times \mathsf{Hctx} \times \mathsf{Pt} \times \mathsf{Pt}'
if n['ctx.slt']['args'][0]['name'] != 'W':
  n['ctx.slt']['args'] = [{"name": "W", "meaning": "the world of the derivation, whose order Ord-World reads"}] + n['ctx.slt']['args']

# 3. osfix leaves the formula
def close(s, o):
  d = 1; t = o + 1
  while d:
    if s[t] == '\\': t += 2; continue
    d += {'{': 1, '}': -1}.get(s[t], 0); t += 1
  return t
f = bl['sr-ord']['formula']
i = f.index(r'\qquad \sym{ord.fix}{')
q = i + len(r'\qquad \sym{ord.fix}')
bl['sr-ord']['formula'] = f[:i] + f[close(f, q):]
R(bl['sr-ord'], 'caption', r'so the relation is defined by recursion on the index with $\mathsf{osfix}$.', r'so the relation is defined by well-founded recursion on the index.')
del n['ord.fix']

# 4. the cost of an event
n['ct.sync'].update({
  "title": r"Cost of an event $\kappa(ev)$",
  "meaning": r"An event of one thread costs the entry of the table for its label, for instance $\kappa(\mathsf{solo}_i\,\beta\,k) = \kappa_\beta$. A synchronization joins the giving action of one thread, a send, select or close, with the taking action of another, a receive or branch, and costs $\kappa_{\mathrm{give}} + \kappa_{\mathrm{take}}$. An offer to the environment costs the entry of its action.",
  "why": r"Both threads of a synchronization step at once, so the process step costs the two entries together. In $\kappa_{DF}$ the sum is $0 + 1 = 1$\inmode{lf}{, in $\kappa_L$ it is $1 + 1 = 2$}.",
  "example": r"A message between two threads costs $1$ under $\kappa_{DF}$\inmode{lf}{ and $2$ under $\kappa_L$}.",
  "signature": r"\kappa(\mathsf{solo}_i\,\ell\,k) = \kappa_{\ell} \qquad \kappa(\mathsf{sync}_{i,j}\,\sigma) = \kappa_{\mathrm{give}} + \kappa_{\mathrm{take}} \qquad \kappa(\mathsf{offer}_i\,\sigma) = \kappa_{\sigma}",
  "args": [{"name": r"\kappa_{\ell}", "meaning": r"the entry of the table for the kind of the label $\ell$, one of $\kappa_\beta, \kappa_{\mathrm{force}}, \kappa_{\mathrm{new}}, \kappa_{\mathrm{spawn}}, \kappa_{\mathrm{link}}, \kappa_{\mathrm{give}}, \kappa_{\mathrm{take}}$"},
           {"name": "ev", "meaning": r"an event of the instrumented semantics, $\mathsf{solo}$, $\mathsf{sync}$ or $\mathsf{offer}$"}],
  "deviations": [{"kind": "renamed", "reason": r"$\kappa_\ell$ is `tcost κ ℓ` and $\kappa_\sigma$ is `scost κ σ`.", "names": ["ev_cost"]}]})
json.dump(m, open(p, 'w'), ensure_ascii=False, indent=1); open(p, 'a').write('\n')
