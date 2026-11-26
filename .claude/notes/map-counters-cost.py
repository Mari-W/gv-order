"""Lock-free presentation in two styles, per-end counters and cost (author, 2026-11-26).

Credit = the counter of an end as typing knows it (a lower bound), tickets = the
reset value of the counter. Fuel becomes the counter relation, its frame the cost
bound, aging becomes "the credits drop by the cost" (rules Lower-*). The Rocq keeps
FuelE, Vfuel, fsem, tage, lage, thage. Run from the repo root.
"""
import json
P = 'docs/explorer/map.json'
m = json.load(open(P))
B = {b['id']: b for s in m['sections'] for b in s['blocks']}
N = m['notes']
X = {e['id']: e for e in m['examples']}
S = {s['id']: s for s in m['sections']}


def obj(item):
    kind, key = item.split(':', 1)
    return {'B': B, 'N': N, 'X': X, 'S': S}[kind][key]


def get(o, path):
    *head, last = path.split('/')
    for p in head:
        o = o[int(p)] if isinstance(o, list) else o[p]
    return o, (int(last) if isinstance(o, list) else last)


def rep(item, path, old, new, count=1):
    o, k = get(obj(item), path)
    s = o[k]
    assert s.count(old) == count, (item, path, old[:60], s.count(old))
    o[k] = s.replace(old, new)


def put(item, path, new):
    o, k = get(obj(item), path)
    o[k] = new


def dev(item, d):
    o = obj(item)
    o.setdefault('deviations', []).append(d)


AGING = r'\inmode{lf}{The Rocq calls $T - c$ aging.}'

# ---------------------------------------------------------------- types and typing
rep('B:ty-ann', 'caption', '[[t-agecap|aging]]', '[[t-agecap|a cost]]')
rep('B:ty-ann', 'caption', 'The [[t-lf-counters|counters block]] says what the two numbers of an end do.',
    'The credit is the counter of the end as typing knows it, a lower bound, and the tickets are the reset value of the counter. The [[t-lf-counters|counters block]] says what the two numbers do.')
rep('B:ty-kinds', 'caption', '[[t-agecap|Aging]] leaves a $\\mathsf{tfree}$ type unchanged.',
    'A [[t-agecap|cost]] leaves a $\\mathsf{tfree}$ type unchanged.')
rep('B:ty-kinds', 'why', 'Values without ends do not age.', 'A cost lowers no credit of a value without ends.')
rep('B:t-judgment', 'caption', 'and [[t-agecap|aging]] subtracts it from what is held.',
    'and the credits of what is held drop by it, as [[t-agecap]] defines.')
put('B:t-lf-counters', 'caption',
    'Each held end $o$ has a counter $f(o)$ at run time, the number of actions the thread holding $o$ may still perform on other ends before it acts on $o$. '
    'An action on $o$ resets $f(o)$ to its reset value, and each action of the thread lowers the counters of its other ends by one. '
    'Typing knows two numbers of each end, those of [[ty-ann]]. The credit $a$ is the counter as typing knows it, a lower bound on $f(o)$. '
    'A cost $c$ lowers it to $a - c$ by [[t-agecap]], so the holding thread postpones $o$ only finitely often. '
    'The tickets $m$ are the reset value, the value an [[r-act|action]] on $o$ resets the counter to, and so an upper bound on the counter. '
    'The two ends of a channel have at most $N$ tickets together, so the dual end of an end with $m$ tickets has a counter of at most $N - m$. '
    'A link acts on no end and gives a waiting end a new dual end. [[r-act|E-Link]] asks $a_1 + m_2 > N$ and $a_2 + m_1 > N$ of the two linked ends, so the new dual end has a lower counter than the old one, and a wait meets at most $N$ links. '
    '[[r-fun|Closures]] have a credit, the counter of their captured ends. A [[r-threads|spawn]] is no action and costs nothing, so the child takes the captured ends at their counters. '
    'A [[r-new|creation]] splits $N$ tickets between the two new ends. An interface end takes its credit and tickets from the annotations $\\eta$ of [[p-typing|P-Term]], and P-Connect asks the tickets of the two ends of each cut channel to sum to at most $N$. '
    'The [[fv|counters of values]] and the [[soup|lock-free process relation]] read these numbers at run time.')
rep('B:t-lf-counters', 'why', 'cannot be lowered by aging, because aging must keep a true statement true.',
    'cannot be lowered by a cost, because lowering by a cost must keep a true statement true.')
put('B:t-agecap', 'title', 'Credits after a cost')
for a, b in [('Age-Free', 'Lower-Free'), ('Age-Credit', 'Lower-Credit'), ('Age-Idle', 'Lower-Idle'), ('Age-Arr', 'Lower-Arr')]:
    rep('B:t-agecap', 'formula', '\\textsf{' + a + '}', '\\textsf{' + b + '}')
put('B:t-agecap', 'caption',
    '$T - c$ lowers the credits of [[ty-ann]] on the ends and closures in $T$ by the cost $c$. It requires $c \\leq a$ for ends that are not idle and for closures, and leaves $\\mathsf{tfree}$ types of [[ty-kinds]] unchanged. '
    'Lower-Idle applies to an end type held by a variable and to an entry $o : S_x^{a,m}$ of $\\Delta$ for an end the term names directly. '
    'A closure at credit $a$ captures its context lowered by $a$, so its body is typed with each captured end at its own credit minus $a$. '
    'The [[t-judgment|judgment]] lowers the credits of what is held by the cost of the term that runs, and [[r-fun|E-Abs]] and [[r-data|E-Pair]] show the two uses. '
    'Lowering a context of ends also asks $a \\leq m$ of each end, which together with [[r-base|E-Chan]] keeps $a \\leq m$ on each end of a context that types a term.')
rep('B:t-agecap', 'why', 'Aging records this on the types of held values', '$T - c$ records this on the types of held values')
dev('B:t-agecap', {'kind': 'renamed', 'part': 'T - c, Lower-Free, Lower-Credit, Lower-Idle, Lower-Arr',
                   'reason': 'The Rocq calls $T - c$ aging (`tage`, `lage`, `thage`). The map says that the credits drop by the cost and names the rules Lower-Free, Lower-Credit, Lower-Idle and Lower-Arr.',
                   'names': ['tage', 'lage', 'thage']})
rep('B:r-fun', 'caption', 'Holding it while $e_2$ runs [[t-agecap|ages]] it by the cost of $e_2$, which needs a credit $a \\geq \\varepsilon_2$, and its [[t-lf-counters|credit]] $a$ ages the captured entries.',
    'Holding it while $e_2$ runs lowers its credit by the cost of $e_2$ as in [[t-agecap]], which needs a credit $a \\geq \\varepsilon_2$, and its [[t-lf-counters|credit]] $a$ lowers the credits of the captured entries.')
rep('B:r-data', 'caption', 'The held value [[t-agecap|ages]] by the cost of $e_2$.', 'The credits of the held value drop by the cost of $e_2$, as in [[t-agecap]].')
rep('B:r-boxes', 'caption', 'so the enclosing rules age what the thread holds across it by one.', 'so the enclosing rules lower the credits of what the thread holds across it by one.')
rep('B:alg-judgment', 'why', 'which has no active point and ages to itself, so handing it to both sides changes neither future nor aging.',
    'which has no active point and no credit that a cost lowers, so handing it to both sides changes neither future nor credits.')
rep('B:alg-elim', 'caption', 'The futures and the aging are those of', 'The futures and the costs are those of')

# ---------------------------------------------------------------- the relation
rep('B:sr-reading', 'caption', 'Fuel is a second predicate on each thread, which holds the ends $\\Phi$ with their counters and returns within $d$ actions.',
    'The counter relation is a second predicate on each thread, which holds the ends $\\Phi$ with their counters and returns within $d$ actions, the cost bound.')
put('B:sr-reading', 'table/rows/5/text', 'the thread $e$, holding $\\Phi$ with counters and tickets, keeps its counters at index $\\beta$')
put('B:sr-reading', 'table/rows/6/text', 'each thread of $a$ is in $E[\\kappa_L]$ and in the counter relation, under one ownership map')
put('B:fu-vs', 'title', 'The relation and the counters side by side')
put('B:fu-vs', 'caption',
    'The counter relation has the clauses $(\\mathsf{stop})$ and $(\\mathsf{step})$ of the relation and one obligation per step label, each with the same change of held ends as its counterpart. '
    'It has no $(\\mathsf{ready})$, reads no world and no point, adds counters, tickets and a cost bound, and lowers the index at each step. '
    'The relation gives each end a point, $S_x$, and the [[fu|counter relation]] gives it a counter and tickets, $S^{f,m}$. The [[soup|lock-free process relation]] asks both of each thread. '
    'The Rocq keeps the two as separate predicates, and the map does too, because one judgment with a counter component is a different fixed point.')
put('B:fu-vs', 'why', 'The relation makes a stuck thread ready, and the counters bound how often the thread holding a dual end acts on other ends first. Lock freedom needs both.')
put('B:fu-vs', 'table/header/2', 'counters')
put('B:fu', 'title', 'Counters of a term')
put('B:fu', 'caption',
    'The counter relation is a predicate on one thread with the clauses $(\\mathsf{stop})$ and $(\\mathsf{step})$ of the [[e-rel|term relation]] and without $(\\mathsf{ready})$. '
    '$e \\in F^N_\\beta\\llbracket \\Phi \\vdash \\sigma\\ !\\ d\\rrbracket$ says that the thread $e$, which holds the ends $\\Phi$ with their counters and tickets, returns at $\\sigma$ within $d$ actions. '
    'The cost bound $d$ is the cost of the [[t-judgment|judgment]] at run time. A value is in $FV$ of [[fv]]. '
    'Each step meets its [[fu-obls|counter obligation]], which reads the successor at each $\\gamma < \\beta$, so each step lowers the index. [[fu-vs]] sets the counter relation beside the relation.')
put('B:fu', 'why', 'The counters bound how often a thread acts on other ends before it acts on an end it holds. Lock-free adequacy measures waits with these counters and tickets. The counter relation reads no point and no world. It is the run-time form of the [[t-lf-counters|counters]] of typing.')
dev('B:fu', {'kind': 'renamed', 'part': 'F, FV, d',
             'reason': 'The Rocq calls $F$ and $FV$ fuel (`FuelE`, `Vfuel`, `fsem`) and the argument $d$ the frame. The map calls $F$ the counter relation, $FV$ the counters of values and $d$ the cost bound, because $d$ bounds the actions of the term as its cost does.',
             'names': ['FuelE', 'Vfuel', 'fsem']})
put('B:fu-obls', 'title', 'Counter obligations')
rep('B:fu-obls', 'caption', 'Counters, tickets and the frame are the only addition.', 'Counters, tickets and the cost bound are the only addition.')
rep('B:fu-obls', 'caption', 'uses one unit of the frame', 'uses one unit of the cost bound')
rep('B:fu-obls', 'caption', 'lowers each counter and the frame.', 'lowers each counter and the cost bound.')
put('B:fv', 'title', 'Counters of values')
put('B:fv', 'caption',
    'The counters of a value, by recursion on the type. The counter of an end is at least its [[t-lf-counters|credit]]. '
    'A closure keeps the counters of its captured ends that are not idle at least at its credit $a$. Its body is in the counter relation at each call whose counters are at least the counters at creation minus $a$. '
    'A box holds no end, and its body is in the counter relation at each force. The [[fu-obls|counter obligations]] read $FV$ at payloads and thunks.')
put('B:fv', 'why', 'The counters of values connect credits in types with counters at run time.')
rep('B:soup', 'caption', 'and has [[fu|fuel]] at their counters.', 'and in the [[fu|counter relation]] at their counters.')
rep('B:soup', 'caption', 'a protocol for fuel.', 'a protocol for the counter relation.')
rep('B:soup', 'caption', 'Fuel occurs only in this definition.', 'The counter relation occurs only in this definition.')
rep('B:soup', 'why', 'combines the relation and the fuel of each thread', 'combines the relation and the counters of each thread')
put('B:soup', 'table/rows/3/cells/3/text', 'the counter relation at their counters')
rep('B:soup', 'deviations/0/reason', 'a protocol map `Π` of fuel', 'a protocol map `Π` of the counter relation')
rep('B:th-terms', 'caption', 'and it has [[fu|fuel]] under', 'and it is in the [[fu|counter relation]] under')

# ---------------------------------------------------------------- notes
rep('N:prim.link', 'why', 'and in the fuel layer it lowers no counter', 'and it lowers no counter')
rep('N:lbl.send', 'why', 'The relation, the fuel layer and scope extrusion', 'The relation, the counter relation and scope extrusion')
rep('N:ty.arrow.cost', 'why', 'Aging subtracts $c$ from the credit of $o$.', 'The credit of $o$ drops by $c$.')
rep('N:sty.skip', 'why', 'The fuel layer drops', 'The counter relation drops')
rep('N:sty.send', 'meaning', 'the sender ages the payload by one transfer', 'the sender lowers the credits of the payload by one')
rep('N:ann.fuel', 'example', 'aged by $3$', 'lowered by $3$')
rep('N:ty.tfree', 'why', 'Aging and capture leave', 'A cost and capture leave')
put('N:tj.hage', 'title', '$\\mathsf{def}(H - c)$, the credits of what is held after a cost')
rep('N:tj.hage', 'meaning', '$H - c$ ages each entry of $H$ by the cost $c$ of $e$.', '$H - c$ lowers the credit of each entry of $H$ by the cost $c$ of $e$.')
rep('N:tj.hage', 'deviations/0/reason', 'which age the ends and the closures of $H$ by $c$.', 'which lower the credits of the ends and the closures of $H$ by $c$ and which the Rocq calls aging.')
rep('N:lfi.credit', 'why', 'and aging lowers the credit by the same amount', 'and the cost lowers the credit by the same amount')
put('N:lfi.credit', 'title', 'Credits, the counter as typing knows it')
put('N:lfi.tickets', 'title', 'Tickets, the reset value of the counter')
rep('N:ty.tickets', 'meaning', 'bounds the counter of the end from above', 'is the reset value of the counter of the end and bounds the counter from above')
put('N:lfi.cost', 'title', 'Cost, credits and tickets, the counting')
rep('N:lfi.cost', 'meaning', 'ages $\\Delta$ by that cost, $\\Delta - c$, which asks', 'lowers the credits of $\\Delta$ by that cost, $\\Delta - c$, which asks')
rep('N:lfi.cost', 'meaning', 'age without the check', 'lose credit without the check')
rep('N:lfi.cost', 'why', 'aging applies it to everything held', '$\\Delta - c$ applies it to everything held')
rep('N:lfi.cost', 'example', 'ages $c$ by $1$', 'lowers the credit of $c$ by $1$')
rep('N:tj.eff', 'why', 'Aging reads the cost.', '$\\Delta - c$ reads the cost.')
rep('N:act.refill', 'why', 'The fuel layer sets', 'The counter relation sets')
put('N:age.free', 'title', 'Lowering a type without ends')
rep('N:age.free', 'why', 'so aging changes nothing.', 'so a cost changes nothing.')
put('N:age.free', 'example', 'A box variable keeps its type under each cost.')
put('N:age.credit', 'title', 'Lowering an end or a closure')
put('N:age.idle', 'title', 'Lowering an idle end')
put('N:age.agg', 'title', 'Lowering a product, sum or existential')
rep('N:age.agg', 'meaning', 'Aging goes into the parts.', 'A cost goes into the parts.')
rep('N:age.agg', 'meaning', 'ages its body.', 'lowers its body.')
rep('N:age.agg', 'why', 'so a compound type ages by aging the ends and closures it contains.', 'so a cost lowers a compound type by lowering the ends and closures it contains.')
put('N:age.ctx', 'title', 'The credits of what is held after a cost')
put('N:age.ctx', 'meaning', '$\\Delta - \\varepsilon$ lowers the credit of each entry of $\\Delta$ by the cost $\\varepsilon$.')
rep('N:age.ctx', 'breaks', 'Without aging a thread', 'Without it a thread')
rep('N:age.ctx', 'args/1/meaning', 'which ages each entry', 'which lowers the credit of each entry')
rep('N:tp.sub-credit', 'breaks', 'no loop that ages an end before', 'no loop that lowers the credit of an end before')
put('N:E-Abs.cap', 'title', 'Capture lowers the credits')
rep('N:E-Abs.body', 'meaning', 'the captured entries are aged by the credit $a$', 'the credits of the captured entries drop by the credit $a$')
rep('N:E-App.fut2', 'meaning', 'the closure ages by the cost of $e_2$, which needs that much credit', 'the credit of the closure drops by the cost of $e_2$, which needs that much credit')
rep('N:E-Pair.fut2', 'meaning', '$T_1$ ages by the cost of $e_2$', 'the credits of $T_1$ drop by the cost of $e_2$')
rep('N:tp.letp', 'meaning', ', aged by $e_1$ in the lock-free mode,', ', lowered by the cost of $e_1$ in the lock-free mode,')
rep('N:tp.letu', 'meaning', ', aged by $e_1$ in the lock-free mode,', ', lowered by the cost of $e_1$ in the lock-free mode,')
rep('N:tp.letu', 'args/0/meaning', ' aged by the cost of $e_1$', ' lowered by the cost of $e_1$')
rep('N:E-Send.floor', 'meaning', ', aged by one transfer,', ', lowered by one,')
rep('N:E-Send.floor', 'meaning', 'The payload value aged by one transfer still has', 'The payload value lowered by one still has')
rep('N:E-Chan.crtk', 'why', 'typed by E-Chan or aged, and both ask', 'typed by E-Chan or lowered by a cost, and both ask')
rep('N:E-Chan.crtk', 'why', '[[th-terms|fuel from cost typing]]', '[[th-terms|the counters read off typing]]')
rep('N:E-New.dual', 'why', 'Fuel starts each counter', 'The counter relation starts each counter')
rep('N:V-Sess', 'why', 'for the fuel layer', 'for the counter relation')
rep('N:FV-Arrow.call', 'why', 'Aging a closure by', 'Lowering a closure by')
rep('N:rel.vsize', 'deviations/0/reason', 'with the fuel $\\mathsf{size}\\,T + 1$', 'with the bound $\\mathsf{size}\\,T + 1$')
put('N:fu.frame', 'title', 'Cost bound $d$')
put('N:fu.frame', 'why', 'Each action asks $1 \\leq d$ and lowers $d$ by one, so $d$ bounds how often the context lowers its own counters during the term.')
put('N:fu.frame', 'example', 'A thread has cost bound $\\infty$.')
rep('N:fu.Phi', 'why', 'Where the relation gives an end a point, fuel gives it a counter and tickets.', 'Where the relation gives an end a point, the counter relation gives it a counter and tickets.')
rep('N:fu.val', 'why', 'the bind lemma of fuel consumes', 'the bind lemma of the counter relation consumes')
put('N:F-Tick.frame', 'meaning', 'The cost bound has a unit for the action.')
put('N:F-Tick.frame', 'why', 'The cost bound limits the decrements of the counters of the context during the term.')
put('N:F-Tick.frame', 'args/0/meaning', 'the cost bound')
rep('N:fu.idle', 'why', 'The typing ages idle ends by truncation at $0$', 'Typing lowers the credit of an idle end with truncation at $0$')
rep('N:F-Beta', 'args/4/meaning', 'the frame,', 'the cost bound,')
rep('N:F-Beta', 'deviations/0/reason', 'of the fuel obligation', 'of the counter obligation')
rep('N:F-Spawn.child', 'why', 'it must have thread fuel at exactly', 'it must be in the counter relation as a thread at exactly')
for k, o in [('F-Close', 'O-Close'), ('F-Select', 'O-Select'), ('F-Branch', 'O-Branch')]:
    rep('N:' + k, 'meaning', 'one unit of the frame', 'one unit of the cost bound')
    rep('N:' + k, 'why', 'It is the fuel form of ' + o, 'It is the counter form of ' + o)
rep('N:FV-Sess', 'why', 'those fuel resets the counter to', 'those the counter relation resets the counter to')
put('N:FV-Sess.counter', 'breaks', 'Without it the credit of an end could exceed its counter, and F-Count would fail on an end whose credit typing treats as positive.')
rep('N:FV-Arrow', 'meaning', 'A closure whose body has fuel at each lower level, counters at or above', 'A closure whose body is in the counter relation at each lower level, with counters at or above')
rep('N:FV-Arrow.exact', 'why', 'to read fuel off typing', 'to read the counters off typing')
put('N:FV-Arrow.body', 'title', 'Counters of the body')
rep('N:FV-Arrow.body', 'why', 'the body guarantees fuel with frame $c$', 'the body is in the counter relation with cost bound $c$')
rep('N:FV-Arrow.body', 'args/3/meaning', 'the frame,', 'the cost bound,')
rep('N:FV-Box', 'meaning', 'whose body has fuel per force', 'whose body is in the counter relation per force')
rep('N:FV-Box.body', 'args/2/meaning', 'the frame,', 'the cost bound,')
put('N:fu.fsem', 'why', 'It is the counter relation of a thread that the lock-free process relation requires, and the cost fundamental theorem derives it from typing. It is the one statement about counters that holds at each index.')
put('N:sp.fuel', 'title', 'Each thread keeps its counters')
put('N:sr.FE', 'title', 'Counter relation $F^N_\\beta\\llbracket\\Phi \\vdash \\sigma\\ !\\ d\\rrbracket$')
put('N:sr.FE', 'meaning', 'The thread holds the ends $\\Phi$, each with counter and tickets, and at the ordinal index $\\beta$ it returns at $\\sigma$ within $d$ actions.')
rep('N:sr.FE', 'args/4/meaning', 'the frame,', 'the cost bound,')
put('N:sr.FV', 'title', 'Counters of values, $FV^N_{\\beta}\\llbracket\\Phi \\vdash \\sigma\\rrbracket$')
rep('N:sr.act', 'meaning', 'and so has the frame.', 'and so has the cost bound.')
put('N:sr.act', 'args/2/meaning', 'the cost bound')
rep('N:sr.fobl', 'meaning', 'The fuel obligation of', 'The counter obligation of')
put('N:sr.fobl', 'why', 'Each label has its own counter update.')
rep('N:th.lf-fundamental', 'why', 'The fuel of each thread comes from its cost typing', 'The counters of each thread come from its typing')
rep('N:th.soup', 'meaning', 'and has fuel at the ordinal index', 'and in the counter relation at the ordinal index')
rep('N:F-Force', 'meaning', 'and a positive frame, and continues with each counter and the frame one lower.', 'and a positive cost bound, and continues with each counter and the cost bound one lower.')
rep('N:F-Force.spare', 'meaning', 'and so has the frame $d$', 'and so has the cost bound $d$')
rep('N:F-Force.spare', 'why', 'which ages the held context', 'which lowers the credits of the held context')
rep('N:E-Force.one', 'why', 'ages the end by the effect, so a loop that holds a non-idle end has effect $\\infty$ and fails the aging check at a finite bound.',
    'lowers the credit of the end by the effect, so a loop that holds a non-idle end has effect $\\infty$ and fails the check $c \\leq a$ at a finite bound.')
rep('N:E-Force.one', 'example', 'ages $\\langle a, b\\rangle$ by one', 'lowers the credits of $\\langle a, b\\rangle$ by one')
rep('N:sp.delta', 'meaning', 'for fuel,', 'for the counter relation,')
put('N:sp.delta', 'why', 'The relation and the counter relation read the same held ends, the first with points and the second with counters. O-New and F-New choose the session type of a new channel in separate existentials, so $S$ and $P$ are two entries.')
rep('N:sp.delta', 'deviations/0/reason', 'a protocol map `Π` of fuel', 'a protocol map `Π` of the counter relation')
rep('N:fu.at', 'meaning', 'has fuel at the held ends $\\Phi\'$ and the frame $d\'$', 'is in the counter relation at the held ends $\\Phi\'$ and the cost bound $d\'$')
rep('N:fu.at', 'why', 'Each step of fuel lowers', 'Each step of the counter relation lowers')
put('N:fu.at', 'args/2/meaning', 'the cost bound after the step')

# ---------------------------------------------------------------- examples, modes, sections
rep('X:ex-guard-neg', 'meaning', 'so the aging of [[t-agecap]] asks nothing', 'so the cost of [[t-agecap]] asks nothing')
put('X:ex-guard-pos', 'lead', 'A loop that holds a non-idle end across its force is rejected, because each force lowers the credit of the end.')
rep('X:ex-guard-pos', 'meaning', 'so [[r-fun|E-App]] ages the type of $c$ by one', 'so [[r-fun|E-App]] lowers the credit of $c$ by one')
rep('X:ex-forwarder', 'lead', 'and has fuel at each counter bound', 'and is in the counter relation at each bound on its counters')
rep('X:ex-forwarder', 'lead', '[[fv|values with fuel]]', '[[fv|counters of values]]')
rep('X:ex-forwarder', 'meaning', 'has fuel at each counter bound', 'is in the counter relation at each bound on its counters')
rep('X:ex-controller', 'lead', 'because [[t-agecap|aging]] truncates the credit', 'because a [[t-agecap|cost]] truncates the credit')
rep('X:ex-controller', 'meaning', 'Aging requires', 'A cost requires')
rep('X:rx-postpone', 'lead', '[[t-agecap|Aging]] rejects the program', 'The [[t-agecap|credits after a cost]] reject the program')
rep('X:rx-postpone', 'meaning', 'so aging asks the cost', 'so typing asks the cost')
rep('X:rx-delegate', 'meaning', 'E-Send ages the payload by $1$', 'E-Send lowers the credit of the payload by $1$')
for e in m['examples']:
    for mo, v in (e.get('x-gv-accepts') or {}).items():
        if isinstance(v, dict) and 'part' in v:
            v['part'] = {'aging': 'credits after a cost',
                         'typing and fuel of the open thread, no closed program': 'typing and counters of the open thread, no closed program'}.get(v['part'], v['part'])
m['modes']['options'][1]['description'] = 'Deadlock freedom plus counters, with credits, tickets and costs.'
rep('S:semantic', 'intro', 'add fuel to each thread', 'add counters to each thread')

json.dump(m, open(P, 'w'), ensure_ascii=False, indent=1)
open(P, 'a').write('\n')
