#!/usr/bin/env python3
"""Generate LaTeX from the proof map (docs/explorer/map.json).

    python3 paper/tools/map2tex.py [--map PATH] [--out DIR]

Writes into paper/gen/ (default):

  defs.tex        \\mapblock{id}, \\mapblockdf{id}, \\mapblocklf{id},
                  \\maprule{Name}, \\maptable{id} for every block of the map
  appendix.tex    every section and block of the map as a display
  notes.tex       the signature of every note, as an index
  examples/ID.tex the code of each example as a Verbatim listing
  unicode.tex     \\newunicodechar for the characters of the listings

Formulas keep the map's TeX. \\sym{key}{X} becomes X. \\inmode{lf}{X}
becomes \\lfadd{X}, \\inmodeplain{lf}{X} becomes X, and a deadlock-free
replacement \\inmodeplain{df}{X}\\inmode{lf}{Y} becomes \\lfalt{X}{Y}.
The combined form (\\mapblock, \\maprule) shows both instances at once,
with the lock-free additions coloured. \\mapblockdf drops the lock-free
parts (or uses the map's df variant) and \\mapblocklf drops the
deadlock-free replacements.

Rerun after every change of the map. The output is deterministic.
"""

import argparse
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
PAPER = os.path.dirname(HERE)
ROOT = os.path.dirname(PAPER)


# ---------------------------------------------------------------- TeX scanning

def close(s, i):
    """Index just past the group that opens at s[i] == '{'."""
    d, k = 1, i + 1
    while k < len(s) and d:
        c = s[k]
        if c == '\\':
            k += 2
            continue
        if c == '{':
            d += 1
        elif c == '}':
            d -= 1
        k += 1
    if d:
        raise ValueError('unbalanced group: ' + s[i:i + 80])
    return k


def arg(s, i):
    """(content, end) of the braced argument at or after i, or (None, i)."""
    while i < len(s) and s[i] == ' ':
        i += 1
    if i >= len(s) or s[i] != '{':
        return None, i
    k = close(s, i)
    return s[i + 1:k - 1], k


MODE_RE = re.compile(r'\\(inmode|inmodeplain)\s*\{')


def highlight(body):
    """\\lfadd around body, keeping a leading ^ or _ attached to its base."""
    b = body.strip()
    if not b:
        return body
    if b[0] in '^_':
        op = b[0]
        rest = b[1:].lstrip()
        if rest.startswith('{'):
            k = close(rest, 0)
            first, tail = rest[1:k - 1], rest[k:]
        elif rest.startswith('\\'):
            m = re.match(r'\\[A-Za-z]+|\\.', rest)
            first, tail = m.group(0), rest[m.end():]
        else:
            first, tail = rest[0], rest[1:]
        out = op + '{\\lfadd{' + first + '}}'
        if tail.strip():
            out += highlight(tail)
        return out
    return '\\lfadd{' + body + '}'


def resolve(s, mode):
    """Resolve the mode markers. mode is 'df', 'lf' or 'both'."""
    out, i = [], 0
    while True:
        m = MODE_RE.search(s, i)
        if not m:
            out.append(s[i:])
            return ''.join(out)
        ms, k1 = arg(s, m.end() - 1)
        body, k2 = arg(s, k1)
        out.append(s[i:m.start()])
        modes = [x.strip() for x in ms.split(',')]
        kind = m.group(1)
        inner_df = resolve(body, mode)
        if kind == 'inmode':
            # coloured, lock-free only in the map
            if 'lf' in modes and 'df' not in modes:
                if mode == 'df':
                    pass
                else:
                    out.append(highlight(inner_df))
            else:
                out.append(inner_df)
            i = k2
            continue
        # inmodeplain
        if modes == ['lf']:
            if mode != 'df':
                out.append(inner_df)
            i = k2
            continue
        if modes == ['df']:
            if mode == 'df':
                out.append(inner_df)
                i = k2
                continue
            if mode == 'lf':
                i = k2
                continue
            # both: a replacement when an \inmode{lf} follows at once
            m2 = re.compile(r'\s*\\inmode(?:plain)?\s*\{lf\}\s*\{').match(s, k2)
            if m2:
                lfbody, k3 = arg(s, m2.end() - 1)
                out.append('\\lfalt{' + inner_df + '}{' + resolve(lfbody, mode) + '}')
                i = k3
                continue
            print('warning: lone \\inmodeplain{df} kept in combined view', file=sys.stderr)
            out.append(inner_df)
            i = k2
            continue
        out.append(inner_df)
        i = k2


SYM_RE = re.compile(r'\\sym\s*\{([^}]*)\}\s*\{')


def strip_sym(s):
    """\\sym{key}{X} -> X, or {X} where dropping the braces is unsafe."""
    while True:
        m = SYM_RE.search(s)
        if not m:
            return s
        open_ = m.end() - 1
        k = close(s, open_)
        inner = s[open_ + 1:k - 1]
        before = s[:m.start()]
        keep = bool(re.search(r'([\^_]\s*|\\[A-Za-z]+\s*)$', before))
        rep = '{' + inner + '}' if keep else inner
        s = before + rep + s[k:]


def tex(s, mode):
    return strip_sym(resolve(s or '', mode))


# ---------------------------------------------------------------- splitting

ARRAY_OPEN = re.compile(r'\s*\\begin\{array\}\{[^}]*\}')


def top_level_split(s, sep_re):
    """Split s at matches of sep_re that sit outside groups and environments."""
    parts, depth, env, last, i = [], 0, 0, 0, 0
    while i < len(s):
        c = s[i]
        if c == '\\':
            if s.startswith('\\begin{', i):
                env += 1
            elif s.startswith('\\end{', i):
                env -= 1
            elif depth == 0 and env == 0:
                m = sep_re.match(s, i)
                if m:
                    parts.append(s[last:i])
                    last = m.end()
                    i = m.end()
                    continue
            i += 2
            continue
        if c == '{':
            depth += 1
        elif c == '}':
            depth -= 1
        i += 1
    parts.append(s[last:])
    return parts


def unwrap_array(s):
    """The body of s when s is exactly one array environment, else None."""
    m = ARRAY_OPEN.match(s)
    if not m:
        return None
    t = s.strip()
    if not t.endswith('\\end{array}'):
        return None
    body = s[m.end():s.rstrip().rfind('\\end{array}')]
    # the closing \end{array} must match the opening one
    depth = 0
    for mm in re.finditer(r'\\(begin|end)\{', body):
        depth += 1 if mm.group(1) == 'begin' else -1
        if depth < 0:
            return None
    return body if depth == 0 else None


ROWSEP = re.compile(r'\\\\(\s*\[[^\]]*\])?')
QQUAD = re.compile(r'\\qquad')
NAME_RE = re.compile(r'\\;\s*\{?\\textsf\{([^{}]*(?:\{[^{}]*\}[^{}]*)*)\}\}?\s*$')


def rules_of(formula):
    """[(name, raw tex)] for each named rule of a block formula."""
    found = []

    def named(s):
        return NAME_RE.search(strip_sym(s).strip())

    def walk(s):
        t = s.strip()
        if t.startswith('{') and close(t, 0) == len(t):
            walk(t[1:-1])
            return
        body = unwrap_array(s)
        if body is not None:
            for row in top_level_split(body, ROWSEP):
                walk(row)
            return
        cols = top_level_split(s, QQUAD)
        if len(cols) > 1 and sum(bool(named(c)) for c in cols) > 1:
            for c in cols:
                walk(c)
            return
        m = named(s)
        if m:
            found.append((m.group(1), s.strip()))
            return
        # a row that starts with an environment and goes on: walk the environments
        for env in top_level_envs(s):
            if env.strip() != t and env.startswith('\\begin{array}'):
                walk(env)
    walk(formula or '')
    return found


def top_level_envs(s):
    """The array environments of s that sit outside groups and other environments."""
    out, depth, env, i, start = [], 0, 0, 0, None
    while i < len(s):
        if s.startswith('\\begin{', i):
            if env == 0 and depth == 0:
                start = i
            env += 1
            i = s.index('}', i) + 1
            continue
        if s.startswith('\\end{', i):
            env -= 1
            j = s.index('}', i) + 1
            if env == 0 and depth == 0 and start is not None:
                out.append(s[start:j])
                start = None
            i = j
            continue
        c = s[i]
        if c == '\\':
            i += 2
            continue
        if c == '{':
            depth += 1
        elif c == '}':
            depth -= 1
        i += 1
    return out


def rule_key(name):
    return re.sub(r'[^A-Za-z0-9-]+', '', name.replace(', ', '-').replace('$^{n}$', '-n'))


# ---------------------------------------------------------------- prose cells

def prose(s, mode='both'):
    """Map prose (table cells) to LaTeX text."""
    s = resolve(s or '', mode)
    s = strip_sym(s)
    s = re.sub(r'\[\[([^\]|]*)\|([^\]]*)\]\]', r'\2', s)
    s = re.sub(r'\[\[([^\]]*)\]\]', r'\1', s)
    out = []
    for j, part in enumerate(re.split(r'(\$[^$]*\$)', s)):
        if j % 2:
            out.append(part)
        else:
            part = re.sub(r'`([^`]*)`', lambda m: '\\texttt{' + m.group(1).replace('_', '\\_') + '}', part)
            part = part.replace('&', '\\&').replace('%', '\\%').replace('#', '\\#')
            part = re.sub(r'(?<!\\)_', r'\\_', part)
            out.append(part)
    return ''.join(out)


# ---------------------------------------------------------------- output

def define(lines, kind, key, body):
    if '#' in body.replace('\\#', ''):
        raise ValueError(f'{kind}:{key} contains #')
    lines.append(f'\\expandafter\\gdef\\csname map@{kind}@{key}\\endcsname{{{body}}}%')


def table_tex(b):
    t = b['table']
    rows = t['rows']
    out = []
    if 'header' in t:
        ncol = len(t['header'])
        out.append('\\begin{tabular}{l' + 'l' * (ncol - 1) + '}')
        out.append(' & '.join('\\textit{' + prose(h) + '}' for h in t['header']) + ' \\\\ \\hline')
        for r in rows:
            cells = [prose(r.get('label', ''))]
            for c in r['cells']:
                cells.append('$' + tex(c['formula'], 'both') + '$' if 'formula' in c else prose(c.get('text', '')))
            out.append(' & '.join(cells) + ' \\\\')
        out.append('\\end{tabular}')
        return '\n'.join(out)
    if rows and 'cells' in rows[0]:
        ncol = max(len(r['cells']) for r in rows)
        out.append('\\begin{tabular}{' + 'l' * ncol + '}')
        for r in rows:
            cells = []
            for c in r['cells']:
                cells.append('$\\displaystyle ' + tex(c['formula'], 'both') + '$' if 'formula' in c else prose(c.get('text', '')))
            cells += [''] * (ncol - len(cells))
            out.append(' & '.join(cells) + ' \\\\[0.5ex]')
        out.append('\\end{tabular}')
        return '\n'.join(out)
    out.append('\\begin{tabular}{lp{0.45\\linewidth}}')
    for r in rows:
        f = '$\\displaystyle ' + tex(r['formula'], 'both') + '$'
        if r.get('modes') == ['lf']:
            f = '\\lfadd{' + f + '}'
        out.append(f + ' & ' + prose(r.get('text', '')) + ' \\\\[0.5ex]')
    out.append('\\end{tabular}')
    return '\n'.join(out)


UNICODE = {
    'µ': r'\ensuremath{\mu}', '·': r'\ensuremath{\cdot}', 'ā': r'\ensuremath{\bar a}',
    'ō': r'\ensuremath{\bar o}', '\u0304': r'\ensuremath{^{-}}', 'Ω': r'\ensuremath{\Omega}',
    'α': r'\ensuremath{\alpha}', 'β': r'\ensuremath{\beta}', 'δ': r'\ensuremath{\delta}',
    'ζ': r'\ensuremath{\zeta}', 'η': r'\ensuremath{\eta}', 'ι': r'\ensuremath{\iota}',
    'κ': r'\ensuremath{\kappa}', 'λ': r'\ensuremath{\lambda}', 'π': r'\ensuremath{\pi}',
    'ρ': r'\ensuremath{\rho}', 'ᵢ': r'\ensuremath{_i}', 'ḡ': r'\ensuremath{\bar g}',
    '′': r'\ensuremath{{}^{\prime}}', '‾': r'\ensuremath{^{-}}', '⁺': r'\ensuremath{^{+}}',
    '⁻': r'\ensuremath{^{-}}', '₀': r'\ensuremath{_0}', '₁': r'\ensuremath{_1}',
    '₂': r'\ensuremath{_2}', '⇒': r'\ensuremath{\Rightarrow}', '∀': r'\ensuremath{\forall}',
    '∃': r'\ensuremath{\exists}', '∗': r'\ensuremath{\ast}', '∥': r'\ensuremath{\parallel}',
    '∪': r'\ensuremath{\cup}', '≈': r'\ensuremath{\approx}', '≺': r'\ensuremath{\prec}',
    '⊗': r'\ensuremath{\otimes}', '⊢': r'\ensuremath{\vdash}', '⊥': r'\ensuremath{\bot}',
    '⊸': r'\ensuremath{\multimap}', '□': r'\ensuremath{\Box}', '⟨': r'\ensuremath{\langle}',
    '⟩': r'\ensuremath{\rangle}',
}


def highlight_code(code, keywords):
    """Code of an example as the body of a highlighted maplisting.

    Keywords become \\lstkw{..}, comments (-- to the end of the line, or
    (* .. *)) become \\lstcmt{..}, and the TeX specials \\ { } are escaped
    for a Verbatim with commandchars=\\\\\\{\\}."""
    specials = {'\\': '\\textbackslash{}', '{': '\\textbraceleft{}', '}': '\\textbraceright{}'}

    def esc(t):
        return re.sub(r'[\\{}]', lambda mm: specials[mm.group(0)], t)
    kw = re.compile(r'(?<![\w′])(' + '|'.join(sorted(map(re.escape, keywords), key=len, reverse=True)) + r')(?![\w′])')
    out = []
    for line in code.split('\n'):
        m = re.search(r'--|\(\*', line)
        body, cmt = (line[:m.start()], line[m.start():]) if m else (line, '')
        parts = []
        for j, piece in enumerate(kw.split(body)):
            parts.append('\\lstkw{' + esc(piece) + '}' if j % 2 else esc(piece))
        if cmt:
            parts.append('\\lstcmt{' + esc(cmt) + '}')
        out.append(''.join(parts))
    return '\n'.join(out)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--map', default=os.path.join(ROOT, 'docs', 'explorer', 'map.json'))
    ap.add_argument('--out', default=os.path.join(PAPER, 'gen'))
    a = ap.parse_args()
    m = json.load(open(a.map, encoding='utf-8'))
    os.makedirs(os.path.join(a.out, 'examples'), exist_ok=True)

    defs = ['% Generated by paper/tools/map2tex.py from docs/explorer/map.json. Do not edit.',
            f"% map source revision {m.get('source', {}).get('revision', '?')}", '']
    app = ['% Generated by paper/tools/map2tex.py from docs/explorer/map.json. Do not edit.', '']
    rules_seen = {}

    for s in m['sections']:
        app.append(f"\\section{{{prose(s['title'])}}}\\label{{app:{s['id']}}}")
        app.append('')
        for b in s['blocks']:
            bid = b['id']
            lfonly = b.get('modes') == ['lf']
            title = prose(b['title'])
            src = '; '.join(f"{x['file']}: " + ', '.join(x.get('names', [])) for x in b.get('source', []))
            app.append(f"\\mapblockhead{{{title}}}{{{bid}}}{{{'lf' if lfonly else ''}}}")
            if 'table' in b:
                define(defs, 'table', bid, table_tex(b))
                app.append(f'\\mapfittext{{\\maptable{{{bid}}}}}')
            if b.get('formula'):
                f = b['formula']
                both = tex(f, 'both')
                df = tex(b.get('variants', {}).get('df', f), 'df')
                lf = tex(f, 'lf')
                define(defs, 'block', bid, both)
                define(defs, 'blockdf', bid, df)
                define(defs, 'blocklf', bid, lf)
                app.append(f'\\mapfit{{\\mapblock{{{bid}}}}}')
                stripped = tex(f, 'df')
                if 'variants' in b and 'df' in b['variants'] and \
                        re.sub(r'\s+', '', df) != re.sub(r'\s+', '', stripped):
                    app.append('\\mapdfvariant')
                    app.append(f'\\mapfit{{\\mapblockdf{{{bid}}}}}')
                for name, raw in rules_of(f):
                    key = rule_key(name)
                    if key in rules_seen:
                        raise ValueError(f'rule {name} in {bid} and {rules_seen[key]}')
                    rules_seen[key] = bid
                    define(defs, 'rule', key, tex(raw, 'both'))
                    define(defs, 'ruledf', key, tex(raw, 'df'))
            app.append(f"\\mapsource{{{prose(src)}}}")
            app.append('')

    defs.append('')
    defs.append('% rules: ' + ', '.join(f'{k} ({v})' for k, v in rules_seen.items()))
    with open(os.path.join(a.out, 'defs.tex'), 'w', encoding='utf-8') as fh:
        fh.write('\n'.join(defs) + '\n')
    with open(os.path.join(a.out, 'appendix.tex'), 'w', encoding='utf-8') as fh:
        fh.write('\n'.join(app) + '\n')

    # notes index
    notes = ['% Generated by paper/tools/map2tex.py. Do not edit.',
             '\\begin{longtable}{p{0.38\\linewidth}p{0.56\\linewidth}}']
    for k in sorted(m['notes']):
        v = m['notes'][k]
        if 'signature' not in v:
            continue
        sig = tex(v['signature'], 'both')
        notes.append(prose(v['title']) + f' & $\\displaystyle {sig}$ \\\\')
    notes.append('\\end{longtable}')
    with open(os.path.join(a.out, 'notes.tex'), 'w', encoding='utf-8') as fh:
        fh.write('\n'.join(notes) + '\n')

    # examples
    missing = set()
    extra = {}
    for e in m['examples']:
        code = e['code']
        # a combining macron becomes a private-use character per base letter
        def bar(mm):
            pu = chr(0xE000 + ord(mm.group(1)))
            extra[pu] = '\\ensuremath{\\bar{' + mm.group(1) + '}}'
            return pu
        code = re.sub('(.)\u0304', bar, code)
        for ch in code:
            if ord(ch) > 127 and ch not in UNICODE and ch not in extra:
                missing.add(ch)
        with open(os.path.join(a.out, 'examples', e['id'] + '.tex'), 'w', encoding='utf-8') as fh:
            fh.write(f"% Generated from map example {e['id']} ({e['title']}). Do not edit.\n")
            body = highlight_code(code.rstrip('\n'), m.get('syntax', {}).get('keywords', []))
            fh.write('\\leavevmode\\par\\nobreak\\noindent\n\\begin{minipage}{\\linewidth}\n\\begin{maplisting}\n' + body + '\n\\end{maplisting}\n\\end{minipage}\n')
    exapp = ['% Generated by paper/tools/map2tex.py. Do not edit.']
    for e in m['examples']:
        exapp.append(f"\\mapexamplehead{{{prose(e['title'])}}}{{{e['id']}}}")
        exapp.append(f"\\input{{gen/examples/{e['id']}}}")
        exapp.append('')
    with open(os.path.join(a.out, 'examples.tex'), 'w', encoding='utf-8') as fh:
        fh.write('\n'.join(exapp) + '\n')
    if missing:
        sys.exit('no \\newunicodechar for: ' + ' '.join(f'{c} U+{ord(c):04X}' for c in sorted(missing)))
    with open(os.path.join(a.out, 'unicode.tex'), 'w', encoding='utf-8') as fh:
        fh.write('% Generated by paper/tools/map2tex.py. Do not edit.\n')
        for ch in sorted(UNICODE):
            if ch == '\u0304':
                continue  # combining macron, replaced per base letter below
            fh.write(f'\\newunicodechar{{{ch}}}{{{UNICODE[ch]}}}\n')
        for ch in sorted(extra):
            fh.write(f'\\newunicodechar{{{ch}}}{{{extra[ch]}}}\n')
    print(f"wrote {a.out}: {sum(len(s['blocks']) for s in m['sections'])} blocks, "
          f"{len(rules_seen)} rules, {len(m['examples'])} examples", file=sys.stderr)


if __name__ == '__main__':
    main()
