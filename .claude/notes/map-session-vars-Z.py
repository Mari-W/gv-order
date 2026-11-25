"""Session-type variables become Z (and Z' for a second one): alpha is the ordinal index, beta a step label."""
import json, re, sys
p = sys.argv[1]; m = json.load(open(p))
FULL_B = {'ty-grammar','ty-session','ty-dual','ty-heads','ty-kinds','r-boxes','t-consts','t-subs'}
FULL_N = {'prim.force','ty.box','ty.box.svars','sty.recv','sty.mu','sty.var','sty.vard','sty.unfold','sty.contr','sty.flip','sty.sequiv','sty.seqv','ty.payload-at','tp.sub-sess','tp.sub-boxc','E-Box.inst','E-New.contr','E-Box.self','E-Send.unfold','E-Recv.unfold','tp.sinst','tp.sinsts','sr.head'}
BAR_ONLY_B = {'v-rel','fv'}
BETA_N = {'sty.contr','tp.sub-boxc'}
def full(s, beta=False):
  s = s.replace('\\bar\\alpha', '\\bar Z')
  s = re.sub(r'\\(mu|forall)\\alpha', r'\\\1 Z', s)
  s = re.sub(r'\\(mu|forall)\\beta', r"\\\1 Z'", s) if beta else s
  s = re.sub(r'\\alpha(?![A-Za-z])', 'Z', s)
  if beta: s = re.sub(r'\\beta(?![A-Za-z])', "Z'", s)
  return s
def walk(x, f):
  if isinstance(x, dict): return {k: walk(v, f) for k, v in x.items()}
  if isinstance(x, list): return [walk(v, f) for v in x]
  if isinstance(x, str): return f(x)
  return x
for s in m['sections']:
  s['blocks'] = [walk(b, full) if b['id'] in FULL_B else walk(b, lambda t: t.replace('\\bar\\alpha', '\\bar Z')) if b['id'] in BAR_ONLY_B else b for b in s['blocks']]
for k in list(m['notes']):
  if k in FULL_N: m['notes'][k] = walk(m['notes'][k], lambda t, k=k: full(t, k in BETA_N))
json.dump(m, open(p, 'w'), ensure_ascii=False, indent=1); open(p, 'a').write('\n')
