import json, re, sys
P = 'docs/explorer/map.json'
m = json.load(open(P))
B = {b['id']: b for s in m['sections'] for b in s['blocks']}
N = m['notes']
S = {s['id']: s for s in m['sections']}

def sub(s, old, new, count=1):
    assert s.count(old) == count, (old[:80], s.count(old))
    return s.replace(old, new)

# ---------------------------------------------------------------- fu
fu = B['fu']
fu['formula'] = r"""\begin{array}{l}
e \in \sym{sr.FE}{F^{N}_{\alpha}\llbracket \sym{fu.Phi}{\Phi} \vdash \sym{fu.rty}{\sigma}\ !\ \sym{fu.frame}{d} \rrbracket} \iff \\
\quad \sym{fu.val}{(\mathsf{stop})\ e \in \mathsf{Val} \Rightarrow e \in \sym{sr.FV}{FV^{N}_{\alpha}\llbracket \Phi \vdash \sigma \rrbracket}} \\
\quad \sym{fu.step}{(\mathsf{step})\ \forall \ell, e'.\ e \xrightarrow{\ell} e' \Rightarrow \sym{sr.fobl}{\mathsf{Fobl}_{\ell}(e')}} \\[6pt]
\sym{fu.at}{e'\ \mathsf{at}\ \Phi'\ !\ d' \iff \forall \beta < \alpha.\ e' \in \sym{sr.FE}{F^{N}_{\beta}\llbracket \Phi' \vdash \sigma\ !\ d' \rrbracket}} \\
\sym{fu.Phi}{\Phi : \mathsf{End} \rightharpoonup \mathsf{STy} \times \mathbb{N} \times \mathbb{N},\quad \Phi(o) = S^{f,m}} \\[6pt]
\sym{fu.fsem}{\mathsf{fsem}\,N\,\Phi\,e \iff \forall \alpha.\ e \in \sym{sr.FE}{F^{N}_{\alpha}\llbracket \Phi \vdash \sym{fu.rty}{\mathsf{thread}}\ !\ \infty \rrbracket}}
\end{array}"""
fu['caption'] = r"Fuel is a predicate on one thread with the clauses $(\mathsf{stop})$ and $(\mathsf{step})$ of the [[e-rel|term relation]] and without $(\mathsf{ready})$. $e \in F^N_\alpha\llbracket \Phi \vdash \sigma\ !\ d\rrbracket$ says that the thread $e$, which holds the ends $\Phi$ with their counters and tickets, returns at $\sigma$ within $d$ actions. A value is in $FV$ of [[fv]]. Each step meets its [[fu-obls|fuel obligation]], which reads the successor at each $\beta < \alpha$, so each step lowers the index. [[fu-vs]] sets fuel beside the relation."
fu['why'] = r"Fuel bounds how often a thread acts on other ends before it acts on an end it holds. Lock-free adequacy measures waits with these counters and tickets. Fuel reads no point and no world. It is the run-time form of the [[t-lf-counters|counters]] of typing."
fu['source'] = [{"file": "fuel/Fuel.v", "names": ["Fdef", "FuelE", "FLevA", "fsem"]}]
fu['deviations'] = [
    {"kind": "simplified", "part": "(stop), (step)",
     "reason": r"`Fdef` states both clauses for each renaming `g` of ends injective on the held ends (`kinj`, `renk`), at the term `emap g e`. The map shows the identity renaming. The closure under renamings is a proof device for a link, which renames the dual end of a removed end in another thread.",
     "names": ["Fdef", "kinj", "renk"]},
    {"kind": "notation", "part": "at",
     "reason": r"$e'\ \mathsf{at}\ \Phi'\ !\ d'$ abbreviates the premise that each obligation of `Fobl` states for its successor, `FuelE` at each lower level.",
     "names": ["Fobl"]},
]

# ---------------------------------------------------------------- fu-obls
fo = B['fu-obls']
ACT = r"\sym{sr.act}{\mathsf{act}}\,o"
AT = r"\sym{fu.at}{e'\ \mathsf{at}}\ "
DM = r"\ !\ d \mathbin{\dot-} 1"
fo['formula'] = (r"""\begin{array}{c}\begin{array}{rcl}
\sym{sr.act}{\mathsf{act}}\,o & \iff & \sym{F-Wait}{\Phi(o) = S^{f,m} \land \neg \sym{fu.idle}{\mathsf{idle}}\,S} \land \sym{F-Tick}{\sym{fu.fspare}{\mathsf{positive}}(\Phi \setminus o) \land \sym{F-Tick.frame}{1 \leq d}} \\
\sym{fu.fspare}{\mathsf{positive}}(\Phi) & \iff & \sym{fu.fspare}{\forall o \mapsto S^{f,m} \in \Phi.\ \neg\mathsf{idle}\,S \Rightarrow 1 \leq f} \\
\sym{fu.tick}{\Phi{\downarrow}} & = & \sym{fu.tick}{\{o \mapsto S^{f \mathbin{\dot-} 1,\,m} \mid o \mapsto S^{f,m} \in \Phi\}} \\
\sym{fu.idle}{\mathsf{idle}}\,S & \iff & \sym{sty.unfold}{\mathsf{unfold}}\,S = \sym{sty.skip}{\mathsf{Skip}}
\end{array}\\[3ex]\begin{array}{c}
\dfrac{""" + AT + r"""\Phi\ !\ d}{\sym{F-Beta}{\sym{sr.fobl}{\mathsf{Fobl}_{\beta}(e')}}}\;\textsf{F-Beta} \qquad
\dfrac{\begin{array}{c}\sym{F-Spawn.held}{\Phi = \Phi_M \uplus \Phi_r,\ \mathrm{dom}\,\Phi_M = \sym{syn.fends}{\mathsf{fends}}(v)} \\ \sym{F-Spawn.child}{\forall \beta < \alpha.\ v\,\ast \in \sym{sr.FE}{F^{N}_{\beta}\llbracket \Phi_M \vdash \sym{fu.rty}{\mathsf{thread}}\ !\ \infty \rrbracket}}\quad """ + AT + r"""\Phi_r\ !\ d\end{array}}{\sym{F-Spawn}{\sym{sr.fobl}{\mathsf{Fobl}_{\mathsf{spawn}\,v}(e')}}}\;\textsf{F-Spawn} \\[2ex]
\dfrac{\begin{array}{c}\sym{F-New.fresh}{c^{\pm} \notin \mathrm{dom}\,\Phi} \\ \Rightarrow \exists S, m_1, m_2.\ m_1 + m_2 \leq N,\ """ + AT + r"""\sym{F-New.cnew}{\Phi[c^{+} \mapsto S^{m_1,m_1},\ c^{-} \mapsto \overline{S}^{m_2,m_2}]}\ !\ d\end{array}}{\sym{F-New}{\sym{sr.fobl}{\mathsf{Fobl}_{\mathsf{new}\,c}(e')}}}\;\textsf{F-New} \qquad
\dfrac{\sym{F-Force.spare}{\sym{fu.fspare}{\mathsf{positive}}(\Phi) \land 1 \leq d}\quad """ + AT + r"""\sym{fu.tick}{\Phi{\downarrow}}""" + DM + r"""}{\sym{F-Force}{\sym{sr.fobl}{\mathsf{Fobl}_{\mathsf{force}}(e')}}}\;\textsf{F-Force}
\end{array}\\[3ex]\begin{array}{c}
\dfrac{\begin{array}{c}""" + ACT + r"""\quad \sym{fu.head}{\Phi(o) \doteq (\sym{sty.send}{!(\bar\iota.\ T)}.S)^{f,m}}\quad \sym{F-Send.notsubj}{\Phi \setminus o = \Phi_M \uplus \Phi_r,\ \mathrm{dom}\,\Phi_M = \sym{syn.fends}{\mathsf{fends}}(w)} \\ \sym{fu.fspare}{\mathsf{positive}}(\Phi_M)\quad \sym{F-Send.payload}{\forall \beta < \alpha.\ w \in \sym{sr.FV}{FV^{N}_{\beta}\llbracket \sym{fu.tick}{\Phi_M{\downarrow}} \vdash T \rrbracket}}\quad """ + AT + r"""\sym{fu.tick}{\Phi_r{\downarrow}}[o \mapsto S^{m,m}]""" + DM + r"""\end{array}}{\sym{F-Send}{\sym{sr.fobl}{\mathsf{Fobl}_{\mathsf{send}\,o\,w}(e')}}}\;\textsf{F-Send} \\[2ex]
\dfrac{\begin{array}{c}""" + ACT + r"""\quad \sym{fu.head}{\Phi(o) \doteq (\sym{sty.recv}{?(\bar\iota.\ T)}.S)^{f,m}} \\ \sym{F-Recv.forall}{\forall \beta, \Phi_{in}.\ \beta < \alpha,\ \Phi_{in} \mathbin{\#} \Phi,\ w \in \sym{sr.FV}{FV^{N}_{\beta}\llbracket \Phi_{in} \vdash T \rrbracket}} \ \Longrightarrow\ e' \in \sym{sr.FE}{F^{N}_{\beta}\llbracket \sym{fu.tick}{\Phi{\downarrow}}[o \mapsto S^{m,m}] \cup \Phi_{in} \vdash \sigma""" + DM + r""" \rrbracket}\end{array}}{\sym{F-Recv}{\sym{sr.fobl}{\mathsf{Fobl}_{\mathsf{recv}\,o\,w}(e')}}}\;\textsf{F-Recv}
\end{array}\\[3ex]\begin{array}{c}
\dfrac{""" + ACT + r"""\quad \sym{fu.head}{\Phi(o) \doteq \sym{sty.close}{\mathsf{Close}}^{f,m}}\quad """ + AT + r"""\sym{fu.tick}{(\Phi \setminus o){\downarrow}}""" + DM + r"""}{\sym{F-Close}{\sym{sr.fobl}{\mathsf{Fobl}_{\mathsf{close}\,o}(e')}}}\;\textsf{F-Close} \qquad
\dfrac{\begin{array}{c}\sym{F-Link.plink}{o_1 \neq o_2,\ \Phi(o_1) = S^{f_1,m_1},\ \Phi(o_2) = S'^{f_2,m_2},\ S \mathrel{\sym{sty.ssub}{\sqsubseteq}} \overline{S'}} \\ \sym{F-Link.ticket}{f_1 + m_2 > N,\ f_2 + m_1 > N}\quad """ + AT + r"""\Phi \setminus \{o_1, o_2\}\ !\ d\end{array}}{\sym{F-Link}{\sym{sr.fobl}{\mathsf{Fobl}_{\mathsf{link}\,o_1\,o_2}(e')}}}\;\textsf{F-Link} \\[2ex]
\dfrac{""" + ACT + r"""\quad \sym{fu.head}{\Phi(o) \doteq \sym{sty.plus}{\oplus(S',S'')}^{f,m}}\quad """ + AT + r"""\sym{fu.tick}{\Phi{\downarrow}}[o \mapsto \sym{sty.choice}{(\mathsf{if}\ i\ \mathsf{then}\ S''\ \mathsf{else}\ S')}^{m,m}]""" + DM + r"""}{\sym{F-Select}{\sym{sr.fobl}{\mathsf{Fobl}_{\mathsf{select}_i\,o}(e')}}}\;\textsf{F-Select} \\[2ex]
\dfrac{""" + ACT + r"""\quad \sym{fu.head}{\Phi(o) \doteq \sym{sty.with}{\&(S',S'')}^{f,m}}\quad """ + AT + r"""\sym{fu.tick}{\Phi{\downarrow}}[o \mapsto \sym{sty.choice}{(\mathsf{if}\ i\ \mathsf{then}\ S''\ \mathsf{else}\ S')}^{m,m}]""" + DM + r"""}{\sym{F-Branch}{\sym{sr.fobl}{\mathsf{Fobl}_{\mathsf{branch}_i\,o}(e')}}}\;\textsf{F-Branch}
\end{array}\end{array}""")
fo['caption'] = r"Each rule has the name and the shape of the obligation of [[e-obl]] with O in place of F, and it changes the held ends in the same way. Counters, tickets and the frame are the only addition. An action on $o$ asks $\mathsf{act}\,o$, uses one unit of the frame, lowers the other counters by $\Phi{\downarrow}$ and resets the counter of $o$ to its tickets $m$. A force keeps the ends, as a $\beta$ step does, and lowers each counter and the frame. A $\beta$ step, a spawn, a creation and a link lower no counter. A creation starts each new end at its tickets. A send hands the ends of its payload on with their counters minus one, read in [[fv]]. A link asks the counter of each linked end to exceed $N$ minus the tickets of the other. [[fu]] asks these obligations at each step."
fo['why'] = r"Each kind of step changes the held ends, counters and tickets in one way, the same at each index. The rules of the [[t-lf-counters|counters block]] are their static images, credit for the counter and the same resets, decrements and link condition."
fo['source'] = [{"file": "fuel/Fuel.v", "names": ["Fobl", "f_act", "fspare", "idle_at", "refill", "ftick", "ctick", "fhand", "f_beta", "f_force", "f_new", "f_spawn", "f_link", "plink", "lok", "f_send", "f_recv", "f_close", "f_select", "f_branch"]}]
fo['deviations'] = [
    {"kind": "notation", "part": "updates",
     "reason": r"$\Phi{\downarrow}[o \mapsto S^{m,m}]$ is `refill o φ` with the protocol of $o$ updated in the map `Π`, and $\Phi_M{\downarrow}$ is `fhand`. $\Phi = \Phi_M \uplus \Phi_r$ with $\mathrm{dom}\,\Phi_M = \mathsf{fends}(v)$ states the inclusion of `fends v` in the held ends and the maps `mres` and `mrem`.",
     "names": ["refill", "fhand", "mres", "mrem"]},
]

# ---------------------------------------------------------------- fu-vs
fv = B['fu-vs']
fv['caption'] = r"Fuel has the clauses $(\mathsf{stop})$ and $(\mathsf{step})$ of the relation and one obligation per step label, each with the same change of held ends as its counterpart. It has no $(\mathsf{ready})$, reads no world and no point, adds counters, tickets and a frame, and lowers the index at each step. The relation gives each end a point, $S_x$, and [[fu|fuel]] gives it a counter and tickets, $S^{f,m}$. The [[soup|lock-free process relation]] asks both of each thread. The Rocq keeps the two as separate predicates, and the map does too, because one judgment with a fuel component is a different fixed point."
fv['why'] = r"The relation makes a stuck thread ready, and fuel bounds how often the thread holding a dual end acts on other ends first. Lock freedom needs both."
fv['table'] = {
    "header": ["", "the relation", "fuel"],
    "rows": [
        {"label": "a thread", "cells": [
            {"formula": r"e \in \sym{th.Erel}{E^{W}_{\alpha}\llbracket \Theta \vdash T \rrbracket^{F}}"},
            {"formula": r"e \in \sym{sr.FE}{F^{N}_{\alpha}\llbracket \sym{fu.Phi}{\Phi} \vdash \sigma\ !\ d \rrbracket}"}]},
        {"label": "an end", "cells": [
            {"text": r"$o \mapsto S_x$ in $\Theta$"},
            {"text": r"$o \mapsto S^{f,m}$ in $\Phi$"}]},
        {"label": "a value", "cells": [
            {"formula": r"v \in \sym{th.Vrel}{V^{W}_{\alpha}\llbracket \Theta \vdash T \rrbracket}"},
            {"formula": r"v \in \sym{sr.FV}{FV^{N}_{\alpha}\llbracket \sym{fu.Phi}{\Phi} \vdash T^{a} \rrbracket}"}]},
        {"label": r"a step $e \xrightarrow{\ell} e'$", "cells": [
            {"text": r"$\sym{sr.obl}{\mathsf{Obl}_\ell(e')}$, the successor at each $\beta$ with $\beta + c \leq \alpha$, or at $\alpha$ after a free step"},
            {"text": r"$\sym{sr.fobl}{\mathsf{Fobl}_\ell(e')}$, the successor at each $\beta < \alpha$"}]},
        {"label": "a reducible term", "cells": [
            {"text": "ready"},
            {"text": "no condition"}]},
        {"label": "worlds", "cells": [
            {"text": r"each extension $W' \sqsupseteq W$"},
            {"text": "none"}]},
    ]}
fv['deviations'] = [
    {"kind": "other", "part": "the two columns",
     "reason": r"The Rocq proves no lemma that merges `Erel` and `FuelE` into one fixed point. Such a fixed point would read at a receive only the values in both $V$ and $FV$, and it would choose one session type at a creation where O-New and F-New choose one each. Its equivalence with the conjunction is unproved.",
     "names": ["Erel", "FuelE", "o_recv", "f_recv", "o_new", "f_new"]},
]

# ---------------------------------------------------------------- soup
sp = B['soup']
sp['caption'] = r"An annotated configuration $a = (q, K, W_a)$ is in the lock-free process relation at the ordinal index $\alpha$ when each thread is in $E[\kappa_L]$ at the ends it owns and has [[fu|fuel]] at their counters, the two columns of [[fu-vs]]. $K$ gives each held end its owner, point, counter and tickets, and $W_a$ is the ranked world of the run so far. The annotations $\Delta$ add to each end of $K$ a session type for the relation and a protocol for fuel. $\mathsf{wa}$ asks them to fit $q$ and $\Sigma$, and it bounds the tickets by $N$ of the [[t-lf-counters|counters block]]. Fuel occurs only in this definition."
sp['why'] = r"The lock-free process relation combines the relation and the fuel of each thread over one ownership map. Lock-free adequacy reads the points and counters that $K$ records, and the bound on tickets makes the measure fall at a link."
sp['source'] = [{"file": "soup/State.v", "names": ["hold", "lfstate", "soup_gen", "soup_consistent", "kres", "ctrs"]},
                {"file": "soup/Soup.v", "names": ["soup_inv", "Soup"]}]
sp['table'] = {"align": "rcll", "rows": [
    {"cells": [{"formula": r"\sym{sp.state}{a = (q, K, W_a)} \qquad \sym{sp.hold}{K(o) = (t, x, f, m)}"}]},
    {"cells": [
        {"formula": r"a \in \sym{th.soup}{S^{N,W}_\alpha\llbracket\Sigma \vdash T\rrbracket}"},
        {"formula": r"\iff"},
        {"formula": r"\sym{sp.world}{W \sqsubseteq W_a} \land \sym{sp.tfree}{\sym{ty.tfree}{\mathsf{tfree}}\,T} \land \sym{sp.exists}{\exists \sym{sp.delta}{\Delta : K},\ U}.\ \sym{sp.own}{\mathsf{wa}^{N}_{\Sigma}(a, \Delta)} \land \forall t.\ q(t) = e \Rightarrow"},
        {"text": ""}]},
    {"cells": [
        {"text": ""}, {"text": ""},
        {"formula": r"\quad \sym{sp.rel}{e \in \sym{th.Erel}{E[\kappa_L]^{W_a}_\alpha\llbracket \Delta^{E}_t \vdash U_t\rrbracket^{\varnothing}}}"},
        {"text": "the relation at the ends $t$ owns"}]},
    {"cells": [
        {"text": ""}, {"text": ""},
        {"formula": r"\quad {}\land \sym{sp.fuel}{e \in \sym{sr.FE}{F^{N}_{\alpha}\llbracket \Delta^{F}_t \vdash \sym{fu.rty}{\mathsf{thread}}\ !\ \infty \rrbracket}}"},
        {"text": "fuel at their counters"}]},
    {"cells": [
        {"formula": r"\sym{sp.delta}{\Delta : K}"},
        {"formula": r"\iff"},
        {"formula": r"\sym{sp.delta}{\mathrm{dom}\,\Delta = \mathrm{dom}\,K \land (K(o) = (t, x, f, m) \Rightarrow \Delta(o) = (S_x, P^{f,m}))}"},
        {"formula": r"\sym{sp.ty}{U_t \in \{T, \ast\}}"}]},
    {"cells": [
        {"formula": r"\sym{sp.delta}{\Delta^{E}_t,\ \Delta^{F}_t}"},
        {"text": ""},
        {"text": r"the maps $o \mapsto S_x$ and $o \mapsto P^{f,m}$ on the ends that $K$ gives $t$"}]},
]}
sp['deviations'] = [
    {"kind": "merged", "part": r"\Delta : K",
     "reason": r"The Rocq chooses an environment `A` of the relation and a protocol map `Π` of fuel per index, and reads counters and tickets off `K` by `ctrs`. The map writes them as one map $\Delta$. `sp_pts` and `sp_dom` make this exact, because they give `A` the points of `K` and give `A`, `Π` and `K` one domain.",
     "names": ["sp_pts", "sp_dom", "ctrs", "kres"]},
    {"kind": "simplified", "part": r"\mathsf{wa}",
     "reason": r"$\mathsf{wa}$ names the other eleven conjuncts of `soup_consistent`, the fields `sp_owner` to `sp_sigcap` of `soup_gen`. Its note lists them.",
     "names": ["soup_consistent", "soup_gen"]},
]

# ---------------------------------------------------------------- t-lf-wf
tw = B['t-lf-wf']
for r in tw['table']['rows']:
    if 'w.lfworld' in r.get('formula', ''):
        r['formula'] = r"\sym{w.lfworld}{\mathsf{ranked}\,W}"
        r['text'] = "process typing at a finite bound asks a ranked world"
tw['caption'] = sub(tw['caption'], "[[p-typing|Typing at a finite bound]] keeps ranks possible,", "[[p-typing|Typing at a finite bound]] asks a ranked world,")
tw['source'] = [x for x in tw['source']]
for x in tw['source']:
    if x['file'] == 'static/Contexts.v':
        x['names'] = ['gen_new']
    if x['file'] == 'types/Worlds.v':
        x['names'] = ['wranked', 'swf', 'wchain_lt_wf', 'wmodels_exists']
tw['deviations'] = [
    {"kind": "simplified",
     "reason": r"The Rocq asks `wok N W` of process typing, which is `swf W` at a finite bound, and the induction behind the fundamental theorems reads worlds under `wfit N W`, which is `wstrict W` or `wranked W` with $N$ finite and excluded middle. The lock-free view shows the ranked case only.",
     "names": ["wok", "swf", "wfit", "wstrict", "wranked"]},
]

# ---------------------------------------------------------------- w-wf
ww = B['w-wf']
old_lf = ww['formula'][ww['formula'].index(r"\inmode{lf}{\sym{w.lfworld}"):]
assert old_lf.endswith("\n\\end{array}")
ww['formula'] = ww['formula'].replace(old_lf, r"\inmode{lf}{\sym{w.lfworld}{\mathsf{ranked}\,W \iff \mathsf{world\_wf}\,W \land \exists \sym{w.rank}{\varrho} : \sym{type.Point}{\mathsf{Point}} \to \sym{type.Ord}{\mathsf{Ord}}.\ \forall x, y.\ x \prec_W y \Rightarrow \varrho(x) < \varrho(y)}}" + "\n\\end{array}")
ww['caption'] = sub(ww['caption'], r"\inmode{lf}{Process typing at a finite bound $N$ asks a well-founded world instead, and $\mathsf{ok}_N$ picks the condition by $N$.}", r"\inmode{lf}{Process typing at a finite bound $N$ asks a ranked world instead, whose order has ranks in the ordinals.}")
ww['why'] = sub(ww['why'], r"\inmode{lf}{Consistent and well-founded differ only on infinite worlds.", r"\inmode{lf}{Consistent and ranked differ only on infinite worlds.")
for x in ww['source']:
    if x['file'] == 'types/Worlds.v':
        x['names'] = ["sworld_wf", "sacyc", "swf", "swf_sacyc"]
ww['source'] = [x for x in ww['source'] if x['file'] != 'static/Contexts.v']
for d in ww['deviations']:
    if d['kind'] == 'notation':
        d['reason'] = r"The map folds `sworld_wf` into $\mathsf{cons}$ and $\mathsf{ranked}$. The Rocq states `sworld_wf W` as a separate conjunct next to `sacyc W` and `swf W`, and the term-level theorems ask `sworld_wf W` alone, which the map writes $\mathsf{world\_wf}\,W$."
ww['deviations'].append({"kind": "renamed", "modes": ["lf"],
    "reason": r"$\mathsf{ranked}$ for a world of typing is `swf`, which is `wf` of relation/Ranks.v at the order of the world, the existence of a rank function.",
    "names": ["swf"]})

# ---------------------------------------------------------------- p-typing
pt = B['p-typing']
pt['formula'] = sub(pt['formula'], r"\inmode{lf}{\sym{w.wok}{\mathsf{ok}_N}}", r"\inmode{lf}{\sym{w.lfworld}{\mathsf{ranked}}}", 3)
pt['caption'] = sub(pt['caption'], "The worlds must then be well-founded in place of consistent, which [[t-lf-wf]] explains.", "The worlds must then be ranked in place of consistent, which [[t-lf-wf]] explains.")
pt.setdefault('deviations', []).append({"kind": "simplified", "modes": ["lf"],
    "reason": r"The Rocq premise is `wok N W`, which is `sacyc W` at $N = \infty$ and `swf W` at a finite $N$. The lock-free view shows the finite case as $\mathsf{ranked}\,W$, and the deadlock-free view the case $N = \infty$ as $\mathsf{cons}\,W$.",
    "names": ["wok", "sacyc", "swf"]})

json.dump(m, open(P, 'w'), ensure_ascii=False, indent=1)
open(P, 'a').write('\n')
print('ok part 1')
