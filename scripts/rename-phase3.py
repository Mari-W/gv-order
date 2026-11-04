#!/usr/bin/env python3
"""Phase-3 renaming of the Rocq development (docs/RENAMES.md).

slot -> payload, frame (in the sense of the future of a thread) -> future,
typing constructors aligned with the rule names of the paper.

Usage: scripts/rename-phase3.py [FILE.v ...]
Without arguments it rewrites every .v file under theories/.
The script is idempotent, so it can be rerun on files added later.

Code and comments are told apart by a lexer for nested Rocq comments.
Evaluation-context frames (lang/Semantics.v: frame, fill_frame,
frame_val, ...) keep their names, and comments in theories/lang/ keep the
word frame.
"""
import re, sys, pathlib

# identifiers renamed exactly (word boundaries), in code and in comments
EXACT = {
    # slot -> payload, where the plain substring rule would clash
    'slots': 'payload_pts',
    'slots_sw': 'payload_pts_sw',
    'fslot': 'futrest',
    # future (formerly frame)
    'sframe': 'sfuture',
    'frame_roots': 'future_roots',
    'frame_roots_sw': 'future_roots_sw',
    'frame_pinst': 'future_pinst',
    'below_rest_frame': 'below_rest_future',
    'op_ub_frame': 'op_ub_future',
    'ready_t_frame': 'ready_t_future',
    'po_frame': 'po_future',
    'Erel_frame': 'Erel_future',
    # typing constructors after the rule names of the paper
    't_konst': 't_const',     # E-Const
    't_lam': 't_abs',         # E-Abs
    't_box': 't_exp',         # E-Exp
    't_wk': 't_weak',         # E-Weak
    't_chan': 't_ch',         # E-Ch
    't_letp': 't_letpair',    # E-LetPair
    't_letu': 't_letstar',    # E-Let*
}

IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")

def rename_ident(w):
    if w in EXACT:
        return EXACT[w]
    if 'slot' in w or 'Slot' in w:
        return w.replace('slot', 'payload').replace('Slot', 'Payload')
    return w

def rename_code(s, in_lang):
    out = IDENT.sub(lambda m: rename_ident(m.group(0)), s)
    # Section frames / End frames (the future helpers of ExampleTools, MPTranslate)
    if not in_lang:
        out = re.sub(r'\b(Section|End) frames\.', r'\1 futures.', out)
    return out

KEEP_FRAME = re.compile(r'(evaluation|one-level|right-of-value|multi)[ -]frames?|frames? of Semantics', re.I)

def rename_comment(s, in_lang):
    s = IDENT.sub(lambda m: rename_ident(m.group(0)), s)
    s = re.sub(r'\bslots\b', 'payload points', s)
    s = re.sub(r'\bslot\b', 'payload point', s)
    s = re.sub(r'\bSlots\b', 'Payload points', s)
    s = re.sub(r'\bSlot\b', 'Payload point', s)
    if in_lang:
        return s
    def fr(m):
        w = m.group(0)
        return {'frame': 'future', 'frames': 'futures',
                'Frame': 'Future', 'Frames': 'Futures'}[w]
    # protect evaluation frames
    keep = {}
    def prot(m):
        k = '\x00%d\x00' % len(keep); keep[k] = m.group(0); return k
    s = KEEP_FRAME.sub(prot, s)
    s = re.sub(r'\b[Ff]rames?\b', fr, s)
    for k, v in keep.items():
        s = s.replace(k, v)
    return s

def split_regions(text):
    """Yield (is_comment, chunk). Handles nested comments and strings."""
    i, n, depth, start = 0, len(text), 0, 0
    in_str = False
    while i < n:
        if depth == 0 and not in_str and text[i] == '"':
            in_str = True; i += 1; continue
        if in_str:
            if text[i] == '"':
                in_str = False
            i += 1; continue
        if text.startswith('(*', i):
            if depth == 0:
                if i > start: yield (False, text[start:i])
                start = i
            depth += 1; i += 2; continue
        if depth > 0 and text.startswith('*)', i):
            depth -= 1; i += 2
            if depth == 0:
                yield (True, text[start:i]); start = i
            continue
        i += 1
    if start < n:
        yield (depth > 0, text[start:])

def process(path):
    p = pathlib.Path(path)
    in_lang = '/lang/' in str(p).replace('\\', '/')
    text = p.read_text(encoding='utf-8')
    new = ''.join(rename_comment(c, in_lang) if is_c else rename_code(c, in_lang)
                  for is_c, c in split_regions(text))
    if new != text:
        p.write_text(new, encoding='utf-8')
        return True
    return False

if __name__ == '__main__':
    files = sys.argv[1:] or [str(f) for f in pathlib.Path('theories').rglob('*.v')]
    changed = [f for f in files if process(f)]
    for f in changed:
        print('renamed', f)
