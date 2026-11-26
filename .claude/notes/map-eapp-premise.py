"""E-App shows the premise c2 <= a1 of e_app (fle c2 a1) in the lock-free mode,
as Syn-App of alg-elim does. Run from the repo root."""
import json
P = 'docs/explorer/map.json'
m = json.load(open(P))
b = [b for s in m['sections'] for b in s['blocks'] if b['id'] == 'r-fun'][0]
old = r'\quad \sym{E-App.ub}{u \prec F}\end{array}}'
new = r'\quad \sym{E-App.ub}{u \prec F}\inmodeplain{lf}{\quad }\inmode{lf}{\varepsilon_2 \leq a}\end{array}}'
assert b['formula'].count(old) == 1
b['formula'] = b['formula'].replace(old, new)
json.dump(m, open(P, 'w'), ensure_ascii=False, indent=1)
open(P, 'a').write('\n')
