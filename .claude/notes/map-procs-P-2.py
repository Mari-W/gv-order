"""Second pass of the processes-with-names change (paper revision 6): the
syntax block, the properties, the runs moved next to the events, the
lock-free judgment through P_a ~ P, and the deviations. Run from the repo
root after map-procs-P.py."""
import json

PATH = 'docs/explorer/map.json'
m = json.load(open(PATH, encoding='utf-8'))
B = {b['id']: b for s in m['sections'] for b in s['blocks']}
N = m['notes']


def rep(obj, key, old, new):
    assert obj[key].count(old) == 1, (key, old[:60])
    obj[key] = obj[key].replace(old, new)


# ------------------------------------------------------------ conventions

for c in m['conventions']:
    if c['symbol'] == 'M':
        c['symbol'] = 'E'
        c['meaning'] = ('The threads of a process, a finite map from thread names to terms. '
                        'Inside $E^{W}_{\\beta}\\llbracket \\cdot \\rrbracket$ it names the term relation.')

# ------------------------------------------------------------ syn-procs

b = B['syn-procs']
b['title'] = 'Processes'
b['formula'] = ('\\begin{array}{l}\n'
                '\\sym{proc.proc}{P = (C, E),\\ E : \\mathbb{N} \\rightharpoonup \\mathsf{Expr}} \\\\\n'
                "\\sym{proc.same}{P \\sim P' \\iff C = C' \\land \\exists \\pi : \\mathrm{dom}\\,E \\to \\mathrm{dom}\\,E' \\text{ bijective}.\\ \\forall t.\\ E(t) = E'(\\pi(t))}\n"
                '\\end{array}')
b['caption'] = ('A process $P = (C, E)$ is a finite set $C$ of restricted channels and a finite map $E$ from thread names to terms, its threads. '
                '$P(t)$ is the thread $t$, and $(C, \\{e_1, \\ldots, e_n\\})$ is the process whose threads $e_1, \\ldots, e_n$ have distinct names. '
                "$P \\sim P'$ holds when $P' = (C', E')$ is $P$ with its threads renamed. "
                '[[sem-proc|Process steps]] are defined on processes. '
                '[[p-typing|Process typing]], the [[p-rel|process relation]] and [[sem-props|deadlock freedom]] read only the restricted channels and the terms of a process, '
                "so they hold of $P$ exactly when they hold of each $P' \\sim P$.")
b['deviations'] = [
    {'kind': 'merged', 'part': 'P',
     'reason': 'The Rocq has two kinds of processes. `proc` pairs a set of channels with a multiset of terms, `config` with a finite map from thread names to terms, '
               'and `erase` forgets the names. The map shows one kind, `config`. Where the Rocq states a definition for `proc`, the map states it for $P$ and means `erase` of $P$.',
     'names': ['proc', 'config', 'erase']},
    {'kind': 'notation', 'part': '\\sim',
     'reason': "$P \\sim P'$ stands for `erase` $P$ $=$ `erase` $P'$. Two finite maps have the same multiset of terms exactly when a bijection of their domains carries one to the other.",
     'names': ['erase']},
]

n = N['proc.proc']
n['title'] = 'Process $P = (C, E)$'
n['meaning'] = ('A process is a pair of a finite set $C$ of restricted channels and a finite map $E$ from thread names to terms, its threads. '
                '$P(t) = E(t)$ is the thread $t$ of $P$, and $(C, \\{e_1, \\ldots, e_n\\})$ is the process with the threads $e_1, \\ldots, e_n$ at distinct names.')
n['example'] = '$(\\{c\\}, \\{0 \\mapsto \\mathsf{close}\\,c^{+},\\ 1 \\mapsto \\mathsf{close}\\,c^{-}\\})$.'
n['signature'] = 'P = (C, E) \\in \\mathsf{Proc} = \\mathcal{P}_{\\mathrm{fin}}(\\mathsf{Chan}) \\times (\\mathbb{N} \\rightharpoonup_{\\mathrm{fin}} \\mathsf{Expr})'
n['args'] = [{'name': 'C', 'meaning': 'The restricted channels.'},
             {'name': 'E', 'meaning': 'The threads, a finite map from thread names to terms.'}]
n['source'] = [{'file': 'lang/Process.v', 'names': ['config']}, {'file': 'lang/Syntax.v', 'names': ['proc']}]
n['deviations'] = [
    {'kind': 'merged',
     'reason': 'The Rocq keeps `proc`, with a multiset of terms, beside `config`, with named threads. The map shows `config` and reads each definition on `proc` at the erasure of $P$.',
     'names': ['proc', 'config']},
    {'kind': 'renamed',
     'reason': 'The Rocq type `gmap nat expr` of the threads is shown as $\\mathbb{N} \\rightharpoonup \\mathsf{Expr}$, with $\\mathsf{Expr}$ for the type `expr` of terms.',
     'names': ['config']},
]
N['proc.same'] = {
    'title': "$P \\sim P'$",
    'meaning': "$P \\sim P'$ holds when $P$ and $P'$ have the same restricted channels and a bijection $\\pi$ of thread names carries the threads of $P$ to those of $P'$.",
    'why': 'Process typing, the process relation and deadlock freedom read only the terms of the threads, and the lock-free judgment chooses the names of the threads at each index.',
    'breaks': 'Nothing. It is a definition.',
    'example': '$(\\{c\\}, \\{0 \\mapsto e,\\ 1 \\mapsto f\\}) \\sim (\\{c\\}, \\{1 \\mapsto e,\\ 0 \\mapsto f\\})$.',
    'signature': "P \\sim P' \\iff C = C' \\land \\exists \\pi.\\ \\forall t.\\ E(t) = E'(\\pi(t))",
    'args': [{'name': 'P = (C, E)', 'meaning': 'A process.'},
             {'name': "P' = (C', E')", 'meaning': 'A process.'},
             {'name': '\\pi', 'meaning': "A bijection $\\mathrm{dom}\\,E \\to \\mathrm{dom}\\,E'$."}],
    'source': [{'file': 'lang/Process.v', 'names': ['erase']}],
    'deviations': [{'kind': 'notation',
                    'reason': "The Rocq writes `erase` $P$ $=$ `erase` $P'$.",
                    'names': ['erase']}],
}
for k in ('proc.config', 'proc.erase', 'type.Config'):
    del N[k]
N['type.Proc']['meaning'] = 'The processes, a set of restricted channels with a finite map from thread names to terms.'

# thread maps of the semantics notes
n = N['se.echans']
for k in ('title', 'meaning', 'why', 'example'):
    n[k] = n[k].replace('(M)', '(E)').replace('\\,M}', '\\,E}').replace('M(i)', 'E(i)')
n['args'] = [{'name': 'E', 'meaning': 'The threads of a process, $\\mathsf{echans}(E) = \\bigcup_{i \\in \\mathrm{dom}\\,E} \\mathsf{fchans}(E(i))$.'}]
n = N['se.upd']
n['title'] = 'Map update $E[i \\mapsto e]$'
n['meaning'] = '$E[i \\mapsto e]$ maps $i$ to $e$ and each $j \\neq i$ to $E(j)$.'
n['args'] = [{'name': 'E', 'meaning': 'The threads.'},
             {'name': 'i', 'meaning': 'The updated thread name.'},
             {'name': 'e', 'meaning': 'The new term of thread $i$.'}]

# ------------------------------------------------------------ events and runs

b = B['sem-events']
b['title'] = 'Events and runs'
rep(b, 'formula', '\\sym{se.parts}{\\mathsf{parts}(ev)}\n\\end{array}',
    '\\sym{se.parts}{\\mathsf{parts}(ev)}'
    '\\inmodeplain{lf}{ \\\\ }\\inmode{lf}{\\sym{se.run}{(r, l) \\in \\mathsf{Run}} \\qquad \\sym{prop.maximal}{\\mathsf{maximal}\\,r\\,l} \\qquad '
    '\\sym{prop.wfair}{\\mathsf{wfair}\\,r\\,l} \\qquad \\sym{prop.pend}{\\mathsf{pend}(P, t)}}\n\\end{array}')
b['caption'] += (' \\inmode{lf}{A run $(r, l)$ is a sequence of processes $r_i$ with the event $l_i$ of the $\\tau$ step from $r_i$ to $r_{i+1}$, or none when $r_{i+1} = r_i$. '
                 'It is maximal when $r_{i+1} = r_i$ only where $r_i$ has no $\\tau$ step. '
                 'It is weakly fair when each thread $t$ at each position $i$ takes part in the step of some $l_j$ with $j \\geq i$ or takes part in no $\\tau$ step of $r_j$. '
                 'A thread $t$ is pending in $P$ when the next step of $P(t)$ is a session action.}')
b['source'].append({'file': 'lockfree/Fair.v', 'names': ['run_step', 'maximal', 'wfair', 'pend']})
N['type.Run']['def'] = 'sem-events'

# ------------------------------------------------------------ properties

b = B['sem-props']
rep(b, 'formula', '\\mathsf{terminated}\\,P \\iff P = (\\varnothing, \\{v\\} \\uplus E),\\ E \\subseteq \\{\\ast\\}',
    "\\mathsf{terminated}\\,(C, E) \\iff C = \\varnothing \\land \\exists t.\\ E(t) \\in \\mathsf{Val} \\land \\forall t' \\neq t.\\ E(t') = \\ast")
rep(b, 'formula', '\\sym{se.r0}{\\sym{proc.erase}{\\mathsf{erase}}(r_0) = P}', '\\sym{se.r0}{r_0 = P}')
rep(b, 'caption', ' A run is a sequence of processes $r$, and $l$ gives the [[sem-events|event]] between consecutive processes.', '')
rep(b, 'caption', 'on each weakly fair maximal run,', 'on each weakly fair maximal [[sem-events|run]] from it,')
n = N['prop.terminated']
n['meaning'] = "$\\mathsf{terminated}\\,(C, E)$ iff $C = \\varnothing$, some thread $E(t)$ is a value and $E(t') = \\ast$ for each other thread $t'$."
n['args'] = [{'name': '(C, E)', 'meaning': 'A process.'},
             {'name': 't', 'meaning': 'The thread whose term is a value.'},
             {'name': "t'", 'meaning': 'Ranges over the other threads, each equal to $\\ast$.'}]
n = N['prop.lf']
rep(n, 'meaning', '$\\mathsf{erase}(r_0) = P$', '$r_0 = P$')
n = N['se.r0']
n['title'] = 'The run starts at $P$'
n['meaning'] = '$r_0$ is the process at position $0$ of the run, and the run starts at $P$.'
n['why'] = 'Lock freedom is a property of a process, so each run it reads starts at that process.'
n['example'] = '$r_0 = P = (\\{c\\}, \\{0 \\mapsto \\mathsf{close}\\,c^{+},\\ 1 \\mapsto \\mathsf{close}\\,c^{-}\\})$.'
n['signature'] = 'r_0 = P'
n['deviations'] = [{'kind': 'simplified',
                    'reason': '`lock_free` asks `erase (r 0) = p` of the `config` `r 0` and the `proc` `p`, so a run may start at each naming of the threads of $P$. '
                              'The map starts it at $P$. The Rocq form implies the map form, which takes $r_0 = P$.',
                    'names': ['lock_free', 'erase']}]

# ------------------------------------------------------------ the process relation

b = B['p-rel']
rep(b, 'formula', 'P = (\\varnothing, \\{v\\} \\mathbin{\\sym{tp.msunion}{\\uplus}} E) \\land v \\in \\sym{th.Vrel}{V^{W\'}_{\\beta}\\llbracket \\Sigma \\vdash T \\rrbracket} \\land E \\subseteq \\{\\ast\\}',
    "P = (\\varnothing, E) \\land \\exists t.\\ E(t) \\in \\sym{th.Vrel}{V^{W'}_{\\beta}\\llbracket \\Sigma \\vdash T \\rrbracket} \\land \\forall t' \\neq t.\\ E(t') = \\ast")
n = N['P-Stop']
n['meaning'] = "$\\mathsf{pirred}\\,P \\Rightarrow P = (\\varnothing, E) \\land \\exists t.\\ E(t) \\in V\\llbracket\\Sigma \\vdash T\\rrbracket \\land \\forall t' \\neq t.\\ E(t') = \\ast$."
n['signature'] = "\\mathsf{pirred}\\,P \\Rightarrow P = (\\varnothing, E) \\land \\exists t.\\ E(t) \\in V\\llbracket\\Sigma \\vdash T\\rrbracket \\land \\ldots"
n['args'] = [{'name': 'P', 'meaning': 'the process'},
             {'name': 't', 'meaning': 'the thread whose term is a value'},
             {'name': "t'", 'meaning': 'the other threads, each $\\ast$'}]
n = N['P-Step']
n['meaning'] = "Each step $P \\xrightarrow{ev} P'$ meets $\\mathsf{Pobl}_{ev}$."

# ------------------------------------------------------------ composition of thread maps

n = N['tp.msunion']
n['title'] = 'Union of threads $E_1 \\uplus E_2$'
n['meaning'] = '$E_1 \\uplus E_2$ is the union of the threads of two processes, at disjoint thread names.'
n['signature'] = ('\\uplus : (\\mathbb{N} \\rightharpoonup \\sym{type.Expr}{\\mathsf{Expr}}) \\times (\\mathbb{N} \\rightharpoonup \\sym{type.Expr}{\\mathsf{Expr}}) '
                  '\\to (\\mathbb{N} \\rightharpoonup \\sym{type.Expr}{\\mathsf{Expr}})')
n['args'] = [{'name': 'E_1, E_2', 'meaning': 'the threads of the two components, at disjoint thread names'}]
n['deviations'] = [{'kind': 'simplified',
                    'reason': 'The Rocq composes two `proc`s and adds their multisets of terms. The map composes processes at disjoint thread names, whose union erases to that sum.',
                    'names': ['proc', 'erase']}]
for k in ('tp.pjudg', 'tp.lfjudg'):
    for a in N[k]['args']:
        if a['name'] == 'P':
            a['meaning'] = 'the process $(C, E)$, restricted channels $C$ and threads $E$'

# ------------------------------------------------------------ the lock-free judgment

b = B['sj-all']
rep(b, 'formula', '\\sym{proc.erase}{\\mathsf{erase}}(\\sym{th.qa}{P_a}) = P', '\\sym{proc.same}{\\sym{th.qa}{P_a} \\sim P}')
for k in ('sp.lfsem', 'sp.exists-before-forall'):
    for f in ('meaning', 'signature'):
        N[k][f] = N[k][f].replace('\\mathsf{erase}(P_a) = P', 'P_a \\sim P')
N['th.qa']['example'] = '$P_a = (C, E)$.'
for d in N['sp.lfsem'].get('deviations', []):
    pass
N['sp.lfsem'].setdefault('deviations', []).append(
    {'kind': 'notation',
     'reason': "$P_a \\sim P$ stands for `erase (s_q a) = p`, the process of $a$ with its threads renamed.",
     'names': ['lf_sem', 's_q', 'erase']})

# ------------------------------------------------------------ the counter letter

b = B['sr-reading']
row = b['table']['rows'][1]
row['text'] = row['text'].replace('acting at $Z$', 'acting at $F$')
b = B['fu']
for d in b['deviations']:
    if d.get('part') == 'F, FV, d':
        d['part'] = 'Z, ZV, d'
        d['reason'] = ('The Rocq calls $Z$ and $ZV$ fuel (`FuelE`, `Vfuel`, `fsem`) and the argument $d$ the frame. '
                       'The map calls $Z$ the counter relation, $ZV$ the counters of values and $d$ the cost bound, because $d$ bounds the actions of the term as its cost does. '
                       'The letter $Z$ keeps $F$ for futures.')

# ------------------------------------------------------------ one rule for the definitions on proc

m['deviationRules'].append({
    'kind': 'simplified',
    'reason': 'The Rocq states deadlock freedom, process typing, the process relation, readiness, the obligations of process steps and the semantic judgments for `proc`, '
              'a set of channels with a multiset of terms. The map states them for a process $P$ with named threads and reads them at the erasure of $P$ (`erase`). '
              'They read only the restricted channels and the terms, and the steps of the erasure are the erasures of the steps of $P$ (`istep_pspec`, `pspec_lift`).',
    'appliesTo': {'keys': ['prop.df', 'prop.terminated', 'prop.notau', 'prop.nofree', 'prop.padmin', 'se.reach', 'se.acc',
                           'tp.pjudg', 'tp.lfjudg', 'P-Term*', 'P-Connect*', 'th.par', 'P.*', 'P-Stop', 'P-Ready', 'P-Step',
                           'sr.pirred', 'sr.readyp', 'sr.pobl', 'rd.p-*', 'rd.above-offered', 'rd.offered', 'rd.link', 'Q-*',
                           'sj.sw', 'sj.proc', 'sp.lfsem', 'th.soundness', 'th.adequacy-h', 'th.fundamental-proc', 'th.lf-*',
                           'th.sem-p-*', 'syn-procs', 'sem-props', 'p-typing', 'p-rel', 'rd', 'p-obls', 'sj-all',
                           'th-sound', 'th-adeq', 'th-fund-proc', 'th-compose']},
})

# ------------------------------------------------------------ fixes after the check

N['proc.same']['why'] = ('Process typing, the process relation and deadlock freedom read only the terms of the threads.'
                         '\\inmode{lf}{ The lock-free judgment chooses the names of the threads at each index.}')
N['proc.same']['meaning'] = N['proc.same']['meaning'].replace("carries the threads of $P$ to those of $P'$", "maps the threads of $P$ to those of $P'$")
for d in B['syn-procs']['deviations']:
    d['reason'] = d['reason'].replace('carries one to the other', 'maps one to the other')
B['syn-procs']['formula'] = B['syn-procs']['formula'].replace(
    "\\exists \\pi : \\mathrm{dom}\\,E \\to \\mathrm{dom}\\,E' \\text{ bijective}.", "\\exists \\pi : \\mathrm{dom}\\,E \\cong \\mathrm{dom}\\,E'.")
m['conventions'].append({'symbol': 'M', 'meaning': 'As a subscript, the part of an environment that a message or a spawn moves.'})
B['sr-reading'].setdefault('introduces', []).append('Z')

json.dump(m, open(PATH, 'w', encoding='utf-8'), ensure_ascii=False, indent=1)
open(PATH, 'a', encoding='utf-8').write('\n')
