#!/usr/bin/env python3
"""Check that the claims of the development are closed under the global context.

    python3 artifact/check.py [--rocq ROCQ] [--list]

Run it from the repository root after `make`.  It

  1. collects the names to check (see TARGETS below) from theories/ and
     from the \\rocq{...} references of paper/*.tex,
  2. writes _build/check/Check.v with one `Redirect ... Print Assumptions`
     per name, by fully qualified name,
  3. compiles it against the built theories, and
  4. fails unless every output reads "Closed under the global context".

It also fails if theories/ contains `Admitted.`, `admit.` or a top-level
Axiom, Parameter or Conjecture.

The list is recomputed from the sources on every run, so renamed or new
theorems are picked up without editing this file.  A name in CORE that no
longer exists is an error.  A \\rocq{...} reference that resolves to no
declaration is reported as a warning (the paper's own `make -C paper
check` treats it as an error).
"""

import os
import re
import subprocess
import sys
import importlib.util

sys.dont_write_bytecode = True  # do not leave paper/__pycache__ behind

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(ROOT, '_build', 'check')

# The main results, by name.  Each must exist.
CORE = [
    'soundness', 'soundness_source',            # static/Fundamental.v
    'fundamental', 'fundamental_proc',          # static/Fundamental.v
    'sem_rules_fundamental',                    # rules/SemanticRules.v
    'adequacy',                                 # relation/LogicalRelation.v
    'styped_typed', 'typed_styped', 'styped_iff',  # static/Source.v
    'harmony',                                  # lang/Harmony.v
    'Prel_term', 'Prel_indep', 'Prel_connect', 'Prel_connect_n',
    'Prel_internalize', 'Erel_bind',
    'pgv_translate', 'pgv_deadlock_free', 'pgv_deadlock_free_source',
    'pn_translate', 'pn_translate_source', 'pn_deadlock_free',
    'pn_deadlock_free_source',
    'mp_translate', 'mp_deadlock_free',
    'mp2_translate', 'mp2_deadlock_free', 'mp2_deadlock_free_source',
    'mp3_translate', 'mp3_deadlock_free', 'mp3_deadlock_free_source',
]

# \rocq{...} references of the paper that name no declaration, and the
# declaration they mean (see ARTIFACT.md, section 4.3).  These are checked
# too, if the target exists.
PAPER_RENAMED = {
    'kfw_ok': 'LRGV.examples.KobForwarder.fw_ok',
    'kfw_sub': 'LRGV.examples.KobForwarder.fw_sub',
    'kfw_typed': 'LRGV.examples.KobForwarder.fw_typed',
    'kfw_deadlock_free': 'LRGV.examples.KobForwarder.fw_deadlock_free_kob',
}

PROOF_KINDS = ('Lemma', 'Theorem', 'Corollary', 'Example')

DECL = re.compile(
    r'^\s*(Lemma|Theorem|Corollary|Definition|Example|Inductive|Fixpoint|'
    r'Instance|Record|Notation|CoInductive|CoFixpoint|Program\s+\w+)\s+'
    r'([A-Za-z_][A-Za-z0-9_\']*)')


def load_rocqrefs():
    path = os.path.join(ROOT, 'paper', 'rocqrefs.py')
    spec = importlib.util.spec_from_file_location('rocqrefs', path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def module_of(rel):
    """theories/a/B.v -> LRGV.a.B"""
    parts = os.path.splitext(rel)[0].split(os.sep)
    assert parts[0] == 'theories'
    return '.'.join(['LRGV'] + parts[1:])


def vfiles():
    """The .v files of _CoqProject, in order, relative to ROOT."""
    out = []
    with open(os.path.join(ROOT, '_CoqProject')) as f:
        for line in f:
            line = line.strip()
            if line.endswith('.v'):
                out.append(line)
    return out


def scan():
    """[(kind, name, rel, line)] for every top-level declaration."""
    decls = []
    for rel in vfiles():
        with open(os.path.join(ROOT, rel), encoding='utf-8') as f:
            for i, line in enumerate(f, start=1):
                m = DECL.match(line)
                if m:
                    decls.append((m.group(1).split()[-1], m.group(2), rel, i))
    return decls


def paper_refs(rr):
    """[(tex file, line, name)] for every \\rocq{...} in paper/*.tex."""
    import glob
    out = []
    for path in sorted(glob.glob(os.path.join(ROOT, 'paper', '*.tex'))):
        if os.path.basename(path) == 'rocqrefs.tex':
            continue
        with open(path, encoding='utf-8') as f:
            for i, line in enumerate(f, start=1):
                for name in rr.USE_PLAIN.findall(line) + rr.USE_AS.findall(line):
                    out.append((os.path.relpath(path, ROOT), i, name))
    return out


def forbidden():
    bad = []
    pat = re.compile(r'\bAdmitted\s*\.|\badmit\s*\.|^\s*(Axiom|Parameter|'
                     r'Conjecture|Axioms|Parameters)\b')
    for rel in vfiles():
        with open(os.path.join(ROOT, rel), encoding='utf-8') as f:
            for i, line in enumerate(f, start=1):
                if pat.search(line):
                    bad.append('%s:%d: %s' % (rel, i, line.strip()))
    return bad


def targets():
    """Ordered dict: fully qualified name -> list of reasons."""
    rr = load_rocqrefs()
    decls = scan()
    by_name = {}
    for kind, name, rel, line in decls:
        by_name.setdefault(name, []).append((kind, rel, line))
    sel = {}
    errors = []

    def add(kind, name, rel, why):
        if kind == 'Notation':
            return
        fq = module_of(rel) + '.' + name
        sel.setdefault(fq, [])
        if why not in sel[fq]:
            sel[fq].append(why)

    for name in CORE:
        if name not in by_name:
            errors.append('core result %s: no such declaration' % name)
        for kind, rel, _ in by_name.get(name, []):
            add(kind, name, rel, 'core')
    for kind, name, rel, _ in decls:
        if kind == 'Theorem':
            add(kind, name, rel, 'theorem')
        if kind in PROOF_KINDS and re.search(
                r'deadlock_free|untypable|underivable|_translate', name):
            add(kind, name, rel, 'deadlock freedom / translation')
        if kind in PROOF_KINDS and rel.split(os.sep)[1] in ('pgv', 'pn', 'mp') \
                and re.search(r'deadlock|translate|simulat|_typed$', name):
            add(kind, name, rel, 'pgv/pn/mp')
    # Paper references resolve the way paper/rocqrefs.py resolves them:
    # to the first declaration of the name, constructors included.
    pdecls = rr.declarations()
    unresolved = []
    for tex, line, name in paper_refs(rr):
        if name not in pdecls:
            fq = PAPER_RENAMED.get(name)
            mod, _, short = (fq or '..').rpartition('.')
            rel = os.path.join('theories', *mod.split('.')[1:]) + '.v'
            if fq and any(r == rel for _, r, _ in by_name.get(short, [])):
                sel.setdefault(fq, []).append('paper (as %s)' % name)
                note = ', checked as ' + fq
            else:
                note = ''
            unresolved.append('%s:%d: \\rocq{%s} has no declaration%s'
                              % (tex, line, name, note))
            continue
        rel, _, dline = pdecls[name]
        kind = 'ctor'
        for k, r, l in by_name.get(name, []):
            if r == rel and l == dline:
                kind = k
        add(kind, name, rel, 'paper')
        # A name declared in several files: check every declaration, as
        # the paper's link picks one by path order.
        for k, r, _ in by_name.get(name, []):
            if r != rel:
                add(k, name, r, 'paper (same name)')
    return sel, errors, unresolved


def main():
    argv = sys.argv[1:]
    rocq = 'rocq'
    if '--rocq' in argv:
        rocq = argv[argv.index('--rocq') + 1]
    sel, errors, unresolved = targets()
    if '--list' in argv:
        for fq, why in sel.items():
            print('%s\t%s' % (fq, ', '.join(why)))
        return 0
    os.makedirs(OUT, exist_ok=True)
    for f in os.listdir(OUT):
        if f.endswith('.out'):
            os.remove(os.path.join(OUT, f))
    names = list(sel)
    with open(os.path.join(OUT, 'Check.v'), 'w') as f:
        f.write('(* Generated by artifact/check.py -- do not edit. *)\n')
        mods = sorted({fq.rsplit('.', 1)[0] for fq in names})
        for m in mods:
            f.write('Require %s.\n' % m)
        for i, fq in enumerate(names):
            f.write('Redirect "_build/check/a%04d" Print Assumptions %s.\n'
                    % (i, fq))
    cmd = [rocq, 'c', '-R', os.path.join(ROOT, 'theories'), 'LRGV',
           '-w', '-notation-overridden',
           os.path.join(OUT, 'Check.v')]
    print('checking %d names: %s' % (len(names), ' '.join(cmd[:2] + ['...'])))
    r = subprocess.run(cmd, cwd=ROOT)
    if r.returncode != 0:
        print('FAIL: rocq exited with %d' % r.returncode)
        return 1
    open_ = []
    with open(os.path.join(OUT, 'report.txt'), 'w') as rep:
        for i, fq in enumerate(names):
            path = os.path.join(OUT, 'a%04d.out' % i)
            try:
                with open(path) as g:
                    text = g.read().strip()
            except FileNotFoundError:
                text = '(no output)'
            ok = text == 'Closed under the global context'
            rep.write('%s\t%s\t%s\n' % ('closed' if ok else 'OPEN', fq,
                                         ', '.join(sel[fq])))
            if not ok:
                open_.append((fq, text))
    bad = forbidden()
    for w in unresolved:
        print('warning: ' + w)
    for e in errors:
        print('error: ' + e)
    for b in bad:
        print('error: forbidden command: ' + b)
    for fq, text in open_:
        print('error: %s is not closed:\n%s' % (fq, text))
    print('%d names checked, %d closed, %d open; report in %s'
          % (len(names), len(names) - len(open_), len(open_),
             os.path.relpath(os.path.join(OUT, 'report.txt'), ROOT)))
    if errors or bad or open_:
        print('FAIL')
        return 1
    print('OK: every checked name is closed under the global context')
    return 0


if __name__ == '__main__':
    sys.exit(main())
