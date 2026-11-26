"""Processes have named threads, written P (P', P_1, ...), and the counter
relation is written Z (paper revision 6). Run from the repo root.

The Rocq has two kinds, `proc` (channels with a multiset of terms) and
`config` (channels with a finite map from thread names to terms), related by
`erase`. The map shows one kind, processes with named threads, and records
the departures as deviations.
"""
import json
import re

PATH = 'docs/explorer/map.json'
m = json.load(open(PATH, encoding='utf-8'))

# ------------------------------------------------------------------ helpers

PROTECT = re.compile(
    r'\\sym\s*\{[^}]*\}'                       # hover keys
    r'|\[\[[^|\]]*\|'                          # link targets
    r'|\[\[[^\]]*\]\]'                         # bare links
    r'|\\(?:mathsf|textsf|mathrm|text|textit|texttt|operatorname)\s*\{[^{}]*\}'
    r'|\\[A-Za-z]+'                            # control words
    r'|`[^`]*`'                                # Rocq names in prose
)


def sub_math(s, fn):
    """Apply fn to the unprotected parts of a math string."""
    out, last = [], 0
    for mm in PROTECT.finditer(s):
        out.append(fn(s[last:mm.start()]))
        out.append(mm.group(0))
        last = mm.end()
    out.append(fn(s[last:]))
    return ''.join(out)


def sub_prose(s, fn):
    """Apply fn inside the $..$ parts of a prose string."""
    parts = re.split(r'(\$[^$]*\$)', s)
    return ''.join(sub_math(p, fn) if p.startswith('$') else p for p in parts)


MATH_FIELDS = {'formula', 'signature', 'df', 'lf'}


def walk(x, fn, path=''):
    """fn(string, path, is_math) on every string of x, returns the new x."""
    if isinstance(x, dict):
        out = {}
        for k, v in x.items():
            p = path + '/' + k
            if isinstance(v, str):
                is_math = k in MATH_FIELDS or (k == 'name' and '/args/' in p)
                out[k] = fn(v, p, is_math)
            else:
                out[k] = walk(v, fn, p)
        return out
    if isinstance(x, list):
        res = []
        for i, v in enumerate(x):
            tag = v.get('id') if isinstance(v, dict) and 'id' in v else str(i)
            p = path + '/' + tag
            res.append(fn(v, p, False) if isinstance(v, str) else walk(v, fn, p))
        return res
    return x


def apply_math(s, is_math, fn):
    return sub_math(s, fn) if is_math else sub_prose(s, fn)


# ------------------------------------------------------- 1. p becomes P

# p is a point, an end, a code variable or a payload credit in these items.
P_SKIP = ('/sections/typing/blocks/r-new', '/notes/E-New.pos', '/notes/E-New.dual',
          '/notes/E-Send.heads', '/notes/E-Open.body', '/notes/syn.let', '/examples/',
          '/notes/proc.config', '/notes/proc.erase', '/notes/type.Config')
P_TOK = re.compile(r"(?<![A-Za-z0-9])p(?![A-Za-z])")


def rename_p(s, path, is_math):
    if any(k in path for k in P_SKIP) or '/source/' in path or '/usedIn/' in path or path.endswith('/id'):
        return s
    return apply_math(s, is_math, lambda t: P_TOK.sub('P', t))


m = walk(m, rename_p)

# ------------------------------------------- 2. configurations q become P

# Where a process P is already in scope, the configuration is the successor P'.
Q_PRIME = ('/sections/semantics/blocks/sem-props', '/notes/prop.notau', '/notes/prop.nofree')
Q_PLAIN = ('/notes/prop.padmin', '/notes/prop.pend', '/notes/se.acc')
Q_TOK = re.compile(r"(?<![A-Za-z0-9])q(?![A-Za-z])")
Q_PRIME_TOK = re.compile(r"(?<![A-Za-z0-9])q(?![A-Za-z'])")


def rename_q(s, path, is_math):
    if '/source/' in path:
        return s
    if any(k in path for k in Q_PRIME):
        return apply_math(s, is_math, lambda t: Q_PRIME_TOK.sub("P'", t))
    if any(k in path for k in Q_PLAIN):
        return apply_math(s, is_math, lambda t: Q_TOK.sub('P', t))
    if any(k in path for k in ('/notes/sp.', '/sections/semantic/blocks/soup', '/notes/th.qa',
                               '/sections/semantic/blocks/sj-all', '/notes/lfi.')):
        return apply_math(s, is_math, lambda t: re.sub(r'(?<![A-Za-z0-9])q(_a)?(?![A-Za-z])', 'P_a', t))
    return s


m = walk(m, rename_q)

# ------------------------------------------ 3. the thread map M becomes E

M_KEYS = ('/sections/semantics/blocks/sem-proc', '/notes/P-Act-', '/notes/sem.fresh-global')
M_TOK = re.compile(r'(?<![A-Za-z0-9])M(?![A-Za-z])')


def rename_m(s, path, is_math):
    if '/source/' in path or not any(k in path for k in M_KEYS):
        return s
    return apply_math(s, is_math, lambda t: M_TOK.sub('E', t))


m = walk(m, rename_m)

# --------------------------------------------- 4. words and the type name

WORDS = [
    (r'\\sym\{type\.Config\}\{\\mathsf\{Config\}\}', r'\\sym{type.Proc}{\\mathsf{Proc}}'),
    (r'\\mathsf\{Config\}', r'\\mathsf{Proc}'),
    (r'\bconfigurations\b', 'processes'),
    (r'\bConfigurations\b', 'Processes'),
    (r'\bconfiguration\b', 'process'),
    (r'\bConfiguration\b', 'Process'),
    (r'\bthread identifiers\b', 'thread names'),
    (r'\bthread identifier\b', 'thread name'),
    (r'\bthread map\b', 'threads'),
]


def rename_words(s, path, is_math):
    if '/source/' in path:
        return s
    for a, b in WORDS:
        s = re.sub(a, b, s)
    return s


m = walk(m, rename_words)

# -------------------------------------------- 5. the counter letter is Z

Z_TOK = re.compile(r'(?<![A-Za-z0-9])F(V?)(?=\^\{?[N0-9]|\\llbracket|\$|\s|\)|,|\.|$)')


def rename_z(s, path, is_math):
    if '/source/' in path:
        return s
    if not any(k in path for k in ('/sections/semantic/blocks/fu', '/sections/semantic/blocks/fv',
                                   '/sections/semantic/blocks/soup', '/sections/semantic/blocks/sr-reading',
                                   '/notes/sr.FE', '/notes/sr.FV', '/notes/sp.', '/notes/fu.', '/notes/fv.',
                                   '/notes/fo.', '/notes/Fo-', '/notes/FV-', '/notes/F-', '/examples/',
                                   '/notes/sr.fobl', '/notes/lfi.')):
        return s

    def f(t):
        t = Z_TOK.sub(lambda mm: 'Z' + mm.group(1), t)
        return t.replace('^{F}_t', '^{Z}_t')
    return apply_math(s, is_math, f)


m = walk(m, rename_z)

json.dump(m, open(PATH, 'w', encoding='utf-8'), ensure_ascii=False, indent=1)
open(PATH, 'a', encoding='utf-8').write('\n')
