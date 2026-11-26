"""Backport to the map the presentation changes of paper revisions 3 to 5
(PLAN.md, section "Map backport"). Run from the repo root."""
import json
import re

PATH = 'docs/explorer/map.json'
m = json.load(open(PATH, encoding='utf-8'))
B = {b['id']: b for s in m['sections'] for b in s['blocks']}
N = m['notes']


def rep(obj, key, old, new, count=1):
    assert obj[key].count(old) == count, (key, old[:70], obj[key].count(old))
    obj[key] = obj[key].replace(old, new)


def walk(x, fn):
    if isinstance(x, dict):
        return {k: (walk(v, fn) if k not in ('source', 'id', 'usedIn', 'names') else v) for k, v in x.items()}
    if isinstance(x, list):
        return [walk(v, fn) for v in x]
    if isinstance(x, str):
        return fn(x)
    return x


# ------------------------------------------- 1. Milner's scheduler leads

ex = m['examples']
ex.sort(key=lambda e: 0 if e['id'] == 'ex-milner' else 1)

# ------------------------------------------- 2. signal and wait

for e in ex:
    if re.search(r'(send|recv)close', e['code']):
        e['code'] = re.sub(r'(?<![\w′])sendclose(?![\w′])', 'signal', e['code'])
        e['code'] = re.sub(r'(?<![\w′])recvclose(?![\w′])', 'wait', e['code'])
        e.setdefault('deviations', []).append({
            'kind': 'renamed',
            'reason': 'The listing calls the helpers `sendclose` and `recvclose` of the Rocq signal and wait.',
            'names': ['sendclose', 'recvclose']})

# ------------------------------------------- 3. disjointness by convention

b = B['p-typing']
rep(b, 'formula', '\\sym{P-Term.C0}{\\mathrm{dom}\\,\\Theta_B = \\sym{tp.ends}{\\mathsf{ends}}(C_0)}\\quad \\sym{P-Term.disj}{\\sym{tp.chans}{\\mathsf{chans}}\\,\\sym{tp.Sigma}{\\Sigma} \\cap C_0 = \\varnothing} \\\\ '
    '\\sym{P-Term.pairs}{\\forall c \\in C_0.\\ \\Theta_B(c^{+}) = \\sym{ty.sess}{S_x\\inmode{lf}{^{m,m}}},\\ \\Theta_B(c^{-}) = \\sym{ty.sess}{\\overline{S}_{\\overline{x}}\\inmode{lf}{^{m\',m\'}}}\\inmode{lf}{,\\ m + m\' \\leq N}}',
    '\\sym{P-Term.pairs}{\\mathsf{pairs}\\inmode{lf}{^{N}}(\\Theta_B, C_0)}')
rep(b, 'formula', '\\sym{P-Connect.disj}{\\mathsf{disjoint}(\\sym{tp.chans}{\\mathsf{chans}}\\,\\Sigma_1, \\sym{tp.chans}{\\mathsf{chans}}\\,\\Sigma_2, \\sym{tp.chans}{\\mathsf{chans}}\\,\\Sigma_C, C_1, C_2)} \\\\ ', '')
rep(b, 'formula', '\\inmodeplain{lf}{\\\\[3ex]}\\inmode{lf}{\\sym{tp.lfjudg}',
    '\\\\[3ex]\\sym{P-Term.pairs}{\\mathsf{pairs}\\inmode{lf}{^{N}}(\\Theta_B, C_0) \\iff \\sym{P-Term.C0}{\\mathrm{dom}\\,\\Theta_B = \\sym{tp.ends}{\\mathsf{ends}}(C_0)} \\land {}} \\\\ '
    '\\quad \\sym{P-Term.pairs}{\\forall c \\in C_0.\\ \\Theta_B(c^{+}) = \\sym{ty.sess}{S_x\\inmode{lf}{^{m,m}}} \\land \\Theta_B(c^{-}) = \\sym{ty.sess}{\\overline{S}_{\\overline{x}}\\inmode{lf}{^{m\',m\'}}}\\inmode{lf}{ \\land m + m\' \\leq N}}'
    '\\inmodeplain{lf}{\\\\[3ex]}\\inmode{lf}{\\sym{tp.tk}{\\mathsf{tk}(o) = m \\iff \\Sigma(o) = S_x^{a,m}} \\qquad \\sym{tp.lfjudg}')
for k in ('P-Term.disj', 'P-Connect.disj'):
    N.pop(k, None)
n = N['P-Term.pairs']
n['title'] = '$\\mathsf{pairs}\\inmode{lf}{^{N}}(\\Theta_B, C_0)$'
n['meaning'] = ('$\\Theta_B$ holds exactly the two ends of each channel of $C_0$, the restricted channels of the thread, at dual points and dual session types'
                '\\inmode{lf}{, each end with credit equal to its tickets and the two tickets summing to at most $N$}.')

b = B['p-obls']
rep(b, 'formula', "C' \\cap \\sym{tp.chans}{\\mathsf{chans}}\\,\\Sigma = \\varnothing\\quad ", '')
rep(b, 'formula', '\\sym{end.ech}{\\mathsf{ech}}[\\mathrm{dom}\\,\\Theta_2] \\cap C = \\varnothing,\\ ', '')

m['conventions'].append({'symbol': '\\cup, \\uplus',
                         'meaning': 'Contexts, interfaces and channel sets combined in one rule are disjoint, and the rules leave this premise implicit.'})
m['deviationRules'].append({
    'kind': 'omitted',
    'reason': 'The Rocq states the disjointness of the contexts and channel sets a rule combines as premises (`disjoint`, `chans`, `##`). '
              'The map leaves them to the convention on $\\cup$ and $\\uplus$.',
    'appliesTo': {'keys': ['p-typing', 'p-obls', 'P-Term*', 'P-Connect*', 'Q-Tau', 'Q-Recv*']}})

# ------------------------------------------- 4. the interface carries its annotations

b = B['p-typing']
b['formula'] = b['formula'].replace('\\inmode{lf}{^{N,\\eta}}', '\\inmode{lf}{^{N}}').replace('\\vdash\\inmode{lf}{^{N}}', '\\vdash\\inmode{lf}{^{N}}')
rep(b, 'formula', '\\sym{P-Term.ann}{\\forall o \\in \\mathrm{dom}\\,\\Sigma.\\ \\eta(o) = (a, m),\\ m \\leq N}',
    '\\sym{P-Term.ann}{\\forall o \\in \\mathrm{dom}\\,\\Sigma.\\ \\sym{tp.tk}{\\mathsf{tk}}(o) \\leq N}')
rep(b, 'formula', '\\sym{tp.lift}{\\Sigma\\inmode{lf}{^{\\eta}}}', '\\Sigma')
rep(b, 'formula', '\\sym{P-Connect.tsum}{\\forall o \\in \\mathrm{dom}\\,\\Sigma_C.\\ \\eta(o)_2 + \\eta(\\overline{o})_2 \\leq N}',
    '\\sym{P-Connect.tsum}{\\forall o \\in \\mathrm{dom}\\,\\Sigma_C.\\ \\mathsf{tk}(o) + \\mathsf{tk}(\\overline{o}) \\leq N}')
rep(b, 'formula', '\\Vdash^{N,\\eta}_W', '\\Vdash^{N}_W')
assert '\\eta' not in b['formula'], b['formula']
c = b['caption']
i = c.index('The interface annotations $\\eta$ give')
j = c.index('as the [[t-lf-counters|counters block]] explains.', i) + len('as the [[t-lf-counters|counters block]] explains.')
c = c[:i] + 'Each interface end $o : S_x^{a,m}$ of $\\Sigma$ carries a credit $a$ and tickets $\\mathsf{tk}(o) = m \\leq N$, as the [[t-lf-counters|counters block]] explains.' + c[j:]
i = c.index('Under the annotation $\\eta(o)')
j = c.index('and $\\eta_2$ elsewhere.', i) + len('and $\\eta_2$ elsewhere.')
c = c[:i] + 'With $\\lfloor N/2 \\rfloor$ tickets at each interface end the ticket premise of P-Connect holds at each cut. The dual interface $\\overline{\\Sigma_C}$ carries credits and tickets of its own.' + c[j:]
c = c.replace('Disjoint channel sets make the maps disjoint, and the left premise lets $\\Sigma_C$ hold no two dual ends, so the rule asks neither.',
              'The left premise lets $\\Sigma_C$ hold no two dual ends, so the rule does not ask it.')
assert '\\eta' not in c
b['caption'] = c
b.setdefault('deviations', []).append({
    'kind': 'simplified', 'modes': ['lf'],
    'reason': 'The Rocq keeps the credits and tickets of the interface ends in a map `iann` beside $\\Sigma$ and lifts $\\Sigma$ to a context of ends by `tenv_ofk`. '
              'The map writes them into $\\Sigma$, $o : S_x^{a,m}$ with $\\mathsf{tk}(o) = m$. A derivation reads `iann` only at the ends of its interface and of its restricted channels '
              '(`ptyped_iann_local`, `p_connect_iann`), so each component carries the annotations of its own interface.',
    'names': ['iann', 'tenv_ofk', 'ptyped_iann_local', 'p_connect_iann']})

N['tp.tk'] = {
    'title': '$\\mathsf{tk}(o)$',
    'meaning': '$\\mathsf{tk}(o) = m$ is the number of tickets of an end $o : S_x^{a,m}$ of the interface.',
    'why': 'P-Term bounds the tickets of each interface end by $N$, and P-Connect bounds the tickets of the two ends of each cut channel.',
    'breaks': 'Nothing. It is a definition.',
    'example': '$\\mathsf{tk}(c^{+}) = 2$ for $c^{+} : \\mathsf{Close}_x^{2,2}$.',
    'signature': '\\mathsf{tk}(o) = m \\iff \\Sigma(o) = S_x^{a,m}',
    'args': [{'name': 'o', 'meaning': 'an end of the interface $\\Sigma$'}, {'name': 'a, m', 'meaning': 'its credit and tickets'}],
    'source': [{'file': 'types/Types.v', 'names': ['iann']}],
    'deviations': [{'kind': 'simplified', 'reason': 'The Rocq reads the tickets as the second component of `iann` at $o$.', 'names': ['iann']}],
    'modes': ['lf'],
}
n = N['P-Term.ann']
n['title'] = 'Interface tickets'
n['meaning'] = 'Each end $o : S_x^{a,m}$ of $\\Sigma$ has at most $N$ tickets, $\\mathsf{tk}(o) = m \\leq N$, and the thread holds $o$ at $S_x^{a,m}$.'
n['example'] = '$c^{+}, d^{-}$ at credit and tickets $N$, and $c^{-}, d^{+}$ at $0$, for the [[ex-link|link]] closed by two threads that close the dual ends.'
n['signature'] = '\\forall o \\in \\mathrm{dom}\\,\\Sigma.\\ \\mathsf{tk}(o) \\leq N'
n['args'] = [{'name': '\\Sigma', 'meaning': 'the interface, each end $o$ at $S_x^{a,m}$'}, {'name': 'a, m', 'meaning': 'the credit and the tickets of the end $o$'}]
n['deviations'] = [{'kind': 'simplified', 'reason': 'The Rocq reads the credit and tickets from `iann`, the map from the entry of $\\Sigma$.', 'names': ['iann', 'p_term']}]
n = N['P-Connect.tsum']
n['meaning'] = 'For each end $o$ of $\\Sigma_C$ the tickets $\\mathsf{tk}(o)$ of $o$ and $\\mathsf{tk}(\\overline{o})$ of its dual end in $\\overline{\\Sigma_C}$ sum to at most $N$.'
n['signature'] = '\\forall o \\in \\mathrm{dom}\\,\\Sigma_C.\\ \\mathsf{tk}(o) + \\mathsf{tk}(\\overline{o}) \\leq N'
n = N['P-Term.typed']
n['signature'] = '\\varnothing ; \\Sigma, \\Theta_B \\vdash^{\\varnothing}_{W\\inmode{lf}{,N}} t : T\\inmode{lf}{\\ !\\ c}'
n['args'] = [{'name': 't', 'meaning': 'the thread'}, {'name': '\\Sigma', 'meaning': 'the interface as a context of ends\\inmode{lf}{, each end at its credit and tickets}'}]
N.pop('tp.lift', None)
for k in ('tp.pjudg', 'tp.lfjudg'):
    n = N[k]
    for f in ('title', 'meaning', 'signature', 'example'):
        if f in n:
            n[f] = n[f].replace('^{N,\\eta}', '^{N}').replace('^{\\infty,\\eta}', '^{\\infty}').replace('\\inmode{lf}{ with interface annotations $\\eta$}', '')
    n['args'] = [a for a in n.get('args', []) if a['name'] != '\\eta']
    for a in n['args']:
        if a['name'] == '\\Sigma':
            a['meaning'] = 'the interface, a finite map from the ends the process offers to its environment to $S_x\\inmode{lf}{^{a,m}}$'
    assert '\\eta' not in json.dumps(n), k
rep(B['t-lf-counters'], 'caption', 'An interface end takes its credit and tickets from the annotations $\\eta$ of [[p-typing|P-Term]],',
    'An interface end carries its credit and tickets in $\\Sigma$, $o : S_x^{a,m}$, which [[p-typing|P-Term]] reads,')
for d in N['sp.lfsem']['deviations']:
    d['reason'] = d['reason'].replace('`lf_sems` reads `lf_semk`, the judgment at the annotations $\\eta$ of the interface. The map leaves $\\eta$ implicit here and in the theorem rows, because it is fixed with the interface.',
                                      '`lf_sems` reads `lf_semk`, the judgment at the annotations `iann` of the interface, which the map writes into $\\Sigma$.')
    assert '\\eta' not in d['reason']

# ------------------------------------------- 5. corrections of revision 4

n = N['sp.own']
rep(n, 'meaning', 'and at most $\\lfloor N/2 \\rfloor$ tickets.', 'and at most the tickets of that entry.')
n['deviations'] = [d for d in n['deviations'] if 'khalf' not in d['reason']]
n['deviations'].append({
    'kind': 'notation',
    'reason': 'The map reads `soup_invk`, which bounds the tickets of an interface end by the tickets of its entry of $\\Sigma$, as `SoupK` and `lf_sems` do. '
              '`soup_inv` and `lf_sem` fix the bound to $\\lfloor N/2 \\rfloor$ by `khalf`.',
    'names': ['soup_invk', 'SoupK', 'soup_inv', 'khalf']})
for s_ in N['sp.own']['source']:
    if s_['file'] == 'soup/Soup.v' and 'soup_invk' not in s_['names']:
        s_['names'].append('soup_invk')
for s_ in B['soup']['source']:
    if s_['file'] == 'soup/Soup.v':
        for x in ('SoupK', 'soup_invk'):
            if x not in s_['names']:
                s_['names'].append(x)

b = B['th-compose']
rep(b, 'formula', '\\land\\ \\Sigma_2 \\cup \\overline{\\Sigma_C} \\sym{sp.lfsem}{\\Vvdash\\inmode{lf}{^{N}}}_{W_2} P_2 : \\ast\\end{array}',
    '\\land\\ \\Sigma_2 \\cup \\overline{\\Sigma_C} \\sym{sp.lfsem}{\\Vvdash\\inmode{lf}{^{N}}}_{W_2} P_2 : \\ast \\\\ \\land\\ \\forall o \\in \\mathrm{dom}\\,\\Sigma_C.\\ \\sym{tp.tk}{\\mathsf{tk}}(o) + \\mathsf{tk}(\\overline{o}) \\leq N\\end{array}')
n = N['th.lf-p-connect']
rep(n, 'meaning', 'and $\\Sigma_2 \\cup \\Sigma_D \\Vvdash\\inmode{lf}{^{N}}_{W_2} P_2 : \\ast$,',
    '$\\Sigma_2 \\cup \\Sigma_D \\Vvdash\\inmode{lf}{^{N}}_{W_2} P_2 : \\ast$ and $\\mathsf{tk}(o) + \\mathsf{tk}(\\overline{o}) \\leq N$ for each $o \\in \\mathrm{dom}\\,\\Sigma_C$,')
rep(n, 'signature', '\\Sigma_2 \\cup \\Sigma_D \\Vvdash\\inmode{lf}{^{N}}_{W_2} P_2 : \\ast \\Rightarrow',
    '\\Sigma_2 \\cup \\Sigma_D \\Vvdash\\inmode{lf}{^{N}}_{W_2} P_2 : \\ast \\land \\forall o \\in \\mathrm{dom}\\,\\Sigma_C.\\ \\mathsf{tk}(o) + \\mathsf{tk}(\\overline{o}) \\leq N \\Rightarrow')

# ------------------------------------------- 6. the obligations name their conditions

RN = [('\\mathsf{send\\_split}', '\\mathsf{opened}', 'send_split', 'Q-Send.split'),
      ('\\mathsf{recv\\_ok}', '\\mathsf{matches}', 'recv_ok', 'Q-Recv.ok'),
      ('\\mathsf{recv\\_back}', '\\mathsf{closed}', 'recv_back', 'Q-Recv.back'),
      ('\\mathsf{recv\\_env}', '\\mathsf{iface}', 'recv_env', 'Q-Recv.env')]
for old, new, rocq, key in RN:
    m = walk(m, lambda s, o=old, n_=new: s.replace(o, n_))
B = {b['id']: b for s in m['sections'] for b in s['blocks']}
N = m['notes']
for old, new, rocq, key in RN:
    N[key].setdefault('deviations', []).append({'kind': 'renamed', 'reason': f'The Rocq calls ${new}$ `{rocq}`.', 'names': [rocq]})

# ------------------------------------------- 7. ech is chan

m = walk(m, lambda s: s.replace('\\mathsf{ech}', '\\mathsf{chan}'))
B = {b['id']: b for s in m['sections'] for b in s['blocks']}
N = m['notes']
N['end.ech'].setdefault('deviations', []).append({'kind': 'renamed', 'reason': 'The Rocq calls $\\mathsf{chan}$ `ech`.', 'names': ['ech']})

# ------------------------------------------- 8. E and P as rules, read inductively at a fixed index

b = B['e-rel']
f = b['formula']
i = f.index('\\begin{array}{l}\ne \\in \\sym{th.Erel}')
j = f.index('\\end{array}', i) + len('\\end{array}')
old = f[i:j]
lines = old.split('\n')
assert lines[1].startswith('e \\in \\sym{th.Erel}{E^{W}_{\\beta}\\llbracket \\Theta \\vdash T \\rrbracket^{F}} \\iff '), lines[1]
concl = 'e \\in \\sym{th.Erel}{E^{W}_{\\beta}\\llbracket \\Theta \\vdash T \\rrbracket^{F}}'
kripke = lines[1].split(' \\iff ')[1].rstrip(' \\').rstrip()
assert kripke.endswith('.'), kripke
stop = lines[2].strip().rstrip('\\').strip()
ready = lines[3].strip().rstrip('\\').strip()
step = lines[4].replace('\\qquad \\sym{rel.lfp}{(\\mathsf{lfp})}', '').strip()
new = ('\\dfrac{\\begin{array}{l}' + kripke + ' \\\\ ' + stop + ' \\\\ ' + ready + ' \\\\ ' + step + '\\end{array}}{' + concl + '}\\;\\textsf{E}')
b['formula'] = f[:i] + new + f[j:]
b['caption'] += (' At a fixed index the rule is read inductively, so $E_\\beta$ is the least relation closed under it. '
                 'This matters only for the steps of cost $0$, whose successor is read at $\\beta$ itself.')

b = B['p-rel']
f = b['formula']
rep(b, 'formula', '\\sym{P.zero}{\\forall P.\\ P \\in \\sym{th.Prel}{P^{W}_{0}\\llbracket \\Sigma \\vdash T \\rrbracket}} \\\\',
    '\\dfrac{\\begin{array}{c}\\phantom{x}\\end{array}}{\\sym{P.zero}{P \\in \\sym{th.Prel}{P^{W}_{0}\\llbracket \\Sigma \\vdash T \\rrbracket}}}\\;\\textsf{P-Zero} \\\\[2ex]')
f = b['formula']
i = f.index("P \\in \\sym{th.Prel}{P^{W}_{\\beta}\\llbracket \\Sigma \\vdash T \\rrbracket},\\ \\beta > 0 \\iff ")
j = f.index('\\end{array}', i)
body = f[i:j]
head, rest = body.split(' \\iff ', 1)
parts = [x.strip().rstrip('\\').strip() for x in rest.split('\n') if x.strip()]
parts[-1] = parts[-1].replace('\\qquad \\sym{rel.lfp}{(\\mathsf{lfp})}', '').strip()
kr = parts[0]
assert kr.endswith('.'), kr
newp = ('\\dfrac{\\begin{array}{l}\\beta > 0 \\qquad ' + kr + ' \\\\ ' + ' \\\\ '.join(parts[1:]) + '\\end{array}}{P \\in \\sym{th.Prel}{P^{W}_{\\beta}\\llbracket \\Sigma \\vdash T \\rrbracket}}\\;\\textsf{P}\n')
b['formula'] = f[:i] + newp + f[j:]
b['formula'] = b['formula'].replace('\\begin{array}{l}\n\\dfrac', '\\begin{array}{c}\n\\dfrac', 1)
assert 'lfp' not in b['formula'], b['formula']
b['caption'] += ' At a fixed index the rules are read inductively, as the [[e-rel|term relation]] is.'
N['P.zero']['example'] = '$P \\in P^{W}_0\\llbracket\\Sigma \\vdash T\\rrbracket$ for each process $P$.'
n = N['rel.lfp']
n['meaning'] = '$E_\\beta$ and $P_\\beta$ are read inductively at a fixed index, as the least relations closed under their rules. Only the steps of cost $0$ read the relation at $\\beta$ itself.'

# ------------------------------------------- 9. futures as sets of points, Z in a signature

b = B['t-contexts']
rep(b, 'caption', 'The future $F$ says where the thread still acts after the term returns, and an action at $x$ asks $x \\prec F$.',
    'The future $F$ says where the thread still acts after the term returns, and an action at $x$ asks $x \\prec F$. '
    'Most futures are finite sets of points, and $x \\prec F$ then says that $x$ lies below each of them. The general form follows.')
for k, n in N.items():
    if n.get('signature', '').startswith('FV \\text{ at }'):
        n['signature'] = n['signature'].replace('FV \\text{ at }', 'ZV\\ \\mathsf{at}\\ ')

# ------------------------------------------- fixes after the check

N.pop('tp.Sigma', None)
N['tp.tk'].pop('modes', None)
N['tp.tk']['title'] = '\\inmode{lf}{$\\mathsf{tk}(o)$}'
for k in ('meaning', 'why', 'example'):
    N['tp.tk'][k] = '\\inmode{lf}{' + N['tp.tk'][k] + '}'


def nocarry(s):
    return (s.replace('carries a credit $a$ and tickets', 'has a credit $a$ and tickets')
             .replace('The dual interface $\\overline{\\Sigma_C}$ carries credits and tickets of its own.', 'The dual interface $\\overline{\\Sigma_C}$ has credits and tickets of its own.')
             .replace('An interface end carries its credit and tickets in $\\Sigma$', 'An interface end has its credit and tickets in $\\Sigma$')
             .replace('so each component carries the annotations of its own interface.', 'so each component may annotate its own interface.')
             .replace('so the rule does not ask it.', 'so the rule does not ask for this condition.')
             .replace('$x$ lies below each of them.', 'each point of $F$ lies above $x$.')
             .replace('the least relation closed under it.', 'the least relation closed under the rule.'))


m = walk(m, nocarry)
B = {b['id']: b for s in m['sections'] for b in s['blocks']}
N = m['notes']
N['P-Term.pairs']['meaning'] = ('$\\Theta_B$ holds exactly the two ends of each channel of $C_0$, the restricted channels of the thread, at dual points and dual session types.'
                                '\\inmode{lf}{ Each end has credit equal to its tickets, and the two tickets sum to at most $N$.}')

json.dump(m, open(PATH, 'w', encoding='utf-8'), ensure_ascii=False, indent=1)
open(PATH, 'a', encoding='utf-8').write('\n')
