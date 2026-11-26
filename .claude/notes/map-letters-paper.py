"""The map takes the letters of the paper: type variables alpha (was Z), ordinal
indices beta and gamma (were alpha and beta). A beta that names a beta step keeps
its letter, a thread label alpha becomes ell. Run from the repo root.

    python3 .claude/notes/map-letters-paper.py
"""
import json, re
P = 'docs/explorer/map.json'
m = json.load(open(P))
FIELDS = {'formula', 'df', 'lf', 'caption', 'why', 'breaks', 'example', 'meaning', 'signature',
          'title', 'name', 'text', 'reason', 'label', 'header', 'lead', 'intro', 'part', 'claim',
          'introduces', 'assumes', 'symbol', 'subtitle', 'description'}
SKIP_EX = {'ex-sinst'}   # its text names the session variable alpha of its code already

PROTECT = [  # (pattern, placeholder text after renaming)
    (r'\\mu\\beta\.\s*\\beta', r"\mu\alpha'.\alpha'"),
    (r'\\sym\{lbl\.beta\}\{\\beta\}', r'\sym{lbl.beta}{\beta}'),
    (r'\\sym\{ct\.beta\}\{\\beta\}', r'\sym{ct.beta}{\beta}'),
    (r'\\xrightarrow\{\\beta\}', r'\xrightarrow{\beta}'),
    (r'\\kappa_\\beta', r'\kappa_\beta'),
    (r'\\kappa_\{\\beta\}', r'\kappa_{\beta}'),
    (r'\\mathsf\{solo\}_i\\,\\beta', r'\mathsf{solo}_i\,\beta'),
    (r'\\mathsf\{solo\}_i\\,\\alpha', r'\mathsf{solo}_i\,\ell'),
    (r'thread label \$\\alpha\$', r'thread label $\ell$'),
    (r'\\mathsf\{(?:F?obl|Obl|Fobl)\}_\{?\\beta\}?', None),
    (r'\\beta \\in \\mathsf\{TLabel\}', r'\beta \in \mathsf{TLabel}'),
    (r'\$\\beta\$(?=[- ](?:step|steps|label|is free|is none|and \$\\mathsf|, \$\\mathsf|, force|itself))', r'$\beta$'),
    (r'(?<=by )\$\\beta\$', r'$\beta$'),
    (r'(?:(?<=The label )|(?<=the label )|(?<=the rest )|(?<=costs of )|(?<=apart from ))\$\\beta\$', r'$\beta$'),
    (r'(?<=include )\$\\beta\$', r'$\beta$'),
    (r'(?<=label )\$\\beta\$', r'$\beta$'),
]

def conv(s, ordgamma=False):
    keep = []
    def stash(mm, rep):
        keep.append(rep if rep is not None else mm.group(0))
        return f'@K{len(keep) - 1}@'
    # backtick code stays as it is
    s = re.sub(r'`[^`]*`', lambda mm: stash(mm, None), s)
    for pat, rep in PROTECT:
        s = re.sub(pat, lambda mm, rep=rep: stash(mm, rep), s)
    if ordgamma:
        s = re.sub(r'\\gamma(?![A-Za-z])', r'\\delta', s)
    s = re.sub(r'\\beta(?![A-Za-z])', r'\\gamma', s)
    s = re.sub(r'\\alpha(?![A-Za-z])', r'\\beta', s)
    s = re.sub(r"(?<![A-Za-z\\])Z'", r"\\alpha'", s)
    s = re.sub(r'(?<![A-Za-z\\])Z(?![A-Za-z])', r'{\\alpha}', s)
    # {\alpha} is needed only after a letter-ending macro or a ^/_; tidy the rest
    s = re.sub(r'(?<![A-Za-z^_])\{\\alpha\}', r'\\alpha', s)
    s = re.sub(r'(\\[A-Za-z]+)\\alpha', r'\1 \\alpha', s)
    for i in range(len(keep) - 1, -1, -1):
        s = s.replace(f'@K{i}@', keep[i])
    return s

ORDGAMMA = set()  # (note key, field) whose gamma is an ordinal
def walk(x, key=None, og=False):
    if isinstance(x, dict):
        return {k: walk(v, k, og) for k, v in x.items()}
    if isinstance(x, list):
        return [walk(v, key, og) for v in x]
    if isinstance(x, str) and key in FIELDS:
        return conv(x, og)
    return x

for s in m['sections']:
    s['blocks'] = [walk(b) for b in s['blocks']]
    for f in ('title', 'intro'):
        if f in s: s[f] = conv(s[f])
for k in list(m['notes']):
    m['notes'][k] = walk(m['notes'][k], None, k in ('rel.atcost', 'F-Recv', 'F-Recv.forall'))
m['examples'] = [e if e['id'] in SKIP_EX else walk(e) for e in m['examples']]
for e in m['examples']:
    if e['id'] == 'ex-sinst':
        e['code'] = e['code'].replace('µβ.β', 'µα′.α′')
    if e['id'] == 'rx-delegate':  # a credit, not an index
        e['meaning'] = e['meaning'].replace(r'\gamma', 'b')
m['conventions'] = walk(m['conventions'])
json.dump(m, open(P, 'w'), ensure_ascii=False, indent=1)
open(P, 'a').write('\n')
