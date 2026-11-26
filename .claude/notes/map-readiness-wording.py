"""The readiness caption takes the three cases of the paper (def:readiness). Run from the repo root."""
import json
P = 'docs/explorer/map.json'
m = json.load(open(P))
B = {b['id']: b for s in m['sections'] for b in s['blocks']}
old = 'A stuck term offers below everything it keeps and below its future. A stuck process has an offer below each end it keeps. '
new = ('A term that is not stable is ready. A stable term is ready in three cases. It is a value. It offers an end of $\\Theta$ and is at a link. '
       'It offers an end of $\\Theta$, and each end of $\\Theta$ it offers has its point below each point of $F$ and below the dual point of each end of $\\Theta$ it does not offer. '
       'A process that is not stable is ready, and a stable one is ready in three cases. It is at a link. It is terminated and $\\Sigma$ is empty. '
       'It offers an end of $\\Sigma$, and each end of $\\Sigma$ it does not offer has below its dual point the point of an end of $\\Sigma$ it offers. ')
c = B['rd']['caption']
assert c.count(old) == 1
B['rd']['caption'] = c.replace(old, new)
json.dump(m, open(P, 'w'), ensure_ascii=False, indent=1)
open(P, 'a').write('\n')
