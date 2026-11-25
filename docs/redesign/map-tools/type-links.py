"""Type names in note signatures and argument texts become links to the note of the type.

Each type T gets a note type.T whose def is the block that introduces T. Inside each
signature (after the colon) and inside $...$ of argument texts, \\mathsf{T} becomes
\\sym{type.T}{\\mathsf{T}}. Idempotent."""
import json, re, sys
p = sys.argv[1]
m = json.load(open(p)); n = m['notes']
TYPES = {
  'Expr': ('syn-terms', 'The terms of the language.'),
  'Val': ('syn-values', 'The values, the terms that do not step.'),
  'End': ('syn-ends', 'The ends of channels, $c^{+}$ and $c^{-}$.'),
  'Chan': ('syn-ends', 'The channel names.'),
  'Point': ('syn-points', 'The points at which ends act.'),
  'Pt': ('syn-points', 'The points at which ends act.'),
  'PVar': ('syn-points', 'The point variables.'),
  'Proc': ('syn-procs', 'The processes, a set of restricted channels with a multiset of threads.'),
  'Config': ('syn-procs', 'The configurations, processes whose threads have numbers.'),
  'Event': ('sem-events', 'The events of process steps.'),
  'Run': ('sem-props', 'The runs of a configuration.'),
  'TLabel': ('sem-labels', 'The labels of thread steps.'),
  'SLabel': ('sem-labels', 'The session labels, the actions of a thread on its ends.'),
  'Frame': ('sem-ctx', 'The evaluation frames.'),
  'Ty': ('ty-grammar', 'The types.'),
  'STy': ('ty-session', 'The session types.'),
  'Sty': ('ty-session', 'The session types.'),
  'Env': ('sr-reading', 'The environments of the relation, finite maps from ends to a session type and a point.'),
  'TEnv': ('t-judgment', 'The typing environments of ends.'),
  'Ctx': ('t-contexts', 'The static contexts of facts.'),
  'World': ('w-world', 'The worlds, bases with facts.'),
  'Base': ('w-world', 'The bases of a world.'),
  'Ord': ('sr-ord', 'The ordinal indices of the relation.'),
  'LFState': ('soup', 'The states of the lock-free process relation.'),
}
blocks = {b['id'] for s in m['sections'] for b in s['blocks']}
for t, (d, mean) in TYPES.items():
  assert d in blocks, d
  k = 'type.' + t
  n.setdefault(k, {})
  n[k].update({'title': r'$\mathsf{' + t + '}$', 'meaning': mean, 'def': d})
def link(tex):
  for t in TYPES:
    tex = re.sub(r'(?<!\\sym\{type\.' + t + r'\}\{)\\mathsf\{' + t + r'\}', lambda _m, t=t: r'\sym{type.' + t + r'}{\mathsf{' + t + '}}', tex)
  return tex
def in_math(s):
  return re.sub(r'\$([^$]*)\$', lambda mm: '$' + link(mm.group(1)) + '$', s)
for k, v in n.items():
  if k.startswith('type.'): continue
  sig = v.get('signature')
  if sig and ':' in sig:
    i = sig.index(':'); v['signature'] = sig[:i + 1] + link(sig[i + 1:])
  for a in v.get('args', []):
    a['meaning'] = in_math(a['meaning'])
json.dump(m, open(p, 'w'), ensure_ascii=False, indent=1); open(p, 'a').write('\n')
