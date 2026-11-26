"""Second pass of map-counters-cost.py: the writing rules of check.sh. Run from the repo root."""
import json
P = 'docs/explorer/map.json'
m = json.load(open(P))
B = {b['id']: b for s in m['sections'] for b in s['blocks']}
N = m['notes']


def rep(o, k, old, new):
    assert o[k].count(old) == 1, (k, old[:60], o[k].count(old))
    o[k] = o[k].replace(old, new)


rep(B['ty-ann'], 'caption', 'The credit is the counter of the end as typing knows it, a lower bound, and the tickets', 'The credit is a static lower bound on the counter of the end, and the tickets')
rep(B['t-lf-counters'], 'caption', 'Typing knows two numbers of each end, those of [[ty-ann]]. The credit $a$ is the counter as typing knows it, a lower bound on $f(o)$.',
    'Typing gives each end two numbers, those of [[ty-ann]]. The credit $a$ is a static lower bound on $f(o)$.')
N['lfi.credit']['title'] = 'Credits, a static lower bound on the counter'
rep(B['r-fun'], 'caption', 'which needs a credit $a \\geq \\varepsilon_2$, and its [[t-lf-counters|credit]] $a$ lowers', 'which needs a credit $a \\geq \\varepsilon_2$. Its [[t-lf-counters|credit]] $a$ lowers')
rep(N['F-Spawn.child'], 'why', ', so it must be in the counter relation', '. So it must be in the counter relation')
rep(N['E-Force.one'], 'why', 'lowers the credit of the end by the effect, so a loop', 'lowers the credit of the end by the effect. So a loop')
json.dump(m, open(P, 'w'), ensure_ascii=False, indent=1)
open(P, 'a').write('\n')
