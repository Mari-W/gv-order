import json,sys
p=sys.argv[1]; m=json.load(open(p)); n=m['notes']
sec={s['id']:s for s in m['sections']}
blk={b['id']:(s,b) for s in m['sections'] for b in s['blocks']}
s,b=blk['p-rel']
f=b['formula']; i=f.index(r'\end{array}\\[3ex]\begin{array}{rcll}')
fusion=f[i+len(r'\end{array}\\[3ex]'):]
assert fusion.endswith(r'\end{array}\end{array}'); fusion=fusion[:-len(r'\end{array}')]
b['formula']=r"""\begin{array}{l}
\sym{P.zero}{\forall p.\ p \in \sym{th.Prel}{P^{W}_{0}\llbracket \Sigma \vdash T \rrbracket}} \\
p \in \sym{th.Prel}{P^{W}_{\alpha}\llbracket \Sigma \vdash T \rrbracket},\ \alpha > 0 \iff \sym{P.strict}{\forall W' \mathrel{\sym{w.ext}{\sqsupseteq}} W}. \\
\quad \sym{P-Stop}{(\mathsf{stop})\ \sym{sr.pirred}{\mathsf{pirred}}\,p \Rightarrow p = (\varnothing, \{v\} \mathbin{\sym{tp.msunion}{\uplus}} E) \land v \in \sym{th.Vrel}{V^{W'}_{\alpha}\llbracket \Sigma \vdash T \rrbracket} \land E \subseteq \{\ast\}} \\
\quad \sym{P-Ready}{(\mathsf{ready})\ \neg\mathsf{pirred}\,p \Rightarrow \sym{sr.readyp}{\mathsf{ready}_{W'}(\Sigma, p)}} \\
\quad \sym{P-Step}{(\mathsf{step})\ p \xrightarrow{ev} p' \Rightarrow \sym{sr.pobl}{\mathsf{Pobl}_{ev}(p')}} \qquad \sym{rel.lfp}{(\mathsf{lfp})}
\end{array}"""
b['caption']=r"""A [[syn-procs|process]] at an index $\alpha > 0$ satisfies the three clauses of a term, stop, [[rd|ready]] and step with the [[p-obls|process obligations]], in each larger world of [[w-ext]]. At index $0$ it holds of each process. A terminated process has a [[v-rel|value]] in its main thread. [[sem-proc|Process steps]] drive the step clause, and [[sr-reading]] says the clauses in words. Renaming held ends and restricting dual pairs of interface ends preserve the relation by the theorem of [[th-fuse]]."""
b['why']=r"""The relation reads a process only at its interface. Closure under renaming and restriction is a theorem, and the semantic P-Connect is proved by an induction over the steps of both components that uses it."""
b['source']=[{"file":"relation/Relation.v","names":["Pbody","Pclauses","Pind","Ptop"]}]
b['usedIn']=sorted(set(b['usedIn'])|{'th-fuse'})
# new block
s2,bc=blk['th-compose']
nb={"id":"th-fuse","title":"Renaming and restricting ends",
"formula":r"""\begin{array}{c}\sym{th.gfuse}{\begin{array}{l}p \in \sym{th.Prel}{P^{W}_{\alpha}\llbracket \Sigma \vdash T\rrbracket} \land C \cap \sym{tp.chans}{\mathsf{chans}}\,\Sigma = \varnothing \land (D \neq \varnothing \Rightarrow \sym{ty.tfree}{\mathsf{tfree}}\,T \land \sym{pfree}{\mathsf{pfree}}\,\Sigma) \\ \land\ (h, D) \in \sym{sr.fuseok}{\mathsf{Fus}}(\Sigma, p) \land q \in \sym{sr.pfuse}{(h, D) \cdot p} \\ \quad\Longrightarrow\ q \in \sym{th.Prel}{P^{W}_{\alpha}\llbracket \sym{sr.sdrop}{(h, D) \cdot \Sigma} \vdash T\rrbracket} \qquad p = (C, E)\end{array}}\\[3ex]"""+fusion.replace(r"\sym{sr.pfuse}{(h, D) \cdot (C, E)} & = & \sym{sr.pfuse}{(\mathsf{gch}_h[C] \cup D,\ h[E])}", r"\sym{sr.pfuse}{q \in (h, D) \cdot (C, E)} & \iff & \sym{sr.pfuse}{q = (\mathsf{gch}_h[C] \cup D,\ E') \land E \mathrel{\sym{th.occ}{\sim_h}} E'}")+r"""\end{array}""",
"caption":r"""A map $h$ of ends together with a set $D$ of channels renames the held ends of a process and restricts the channels of $D$, whose two ends are a dual pair of the interface. The relation is preserved. $E \sim_h E'$ says that the threads $E'$ arise from the threads $E$ by replacing each occurrence of a held end $o$ with $h(o)$ and each occurrence of another end with some end. $D = \varnothing$ is a renaming, and $h = \mathsf{id}$ restricts pairs of the interface. A link step renames by a map that sends two ends to one, which is the case that needs the occurrences. A restriction asks $\mathsf{tfree}\,T$ because the final value of a process may otherwise hold both ends of a channel of $D$. [[th-compose|P-Connect]] uses the theorem when a component links two ends of the cut.""",
"why":r"""The proof of P-Connect follows the steps of both components, and after a link or a send across the cut the residual is a composite over a renamed cut. This theorem states that the residual components are again in the relation.""",
"source":[{"file":"compat/Fusion.v","names":["Prel_gfuse","gfuse"]},{"file":"compat/Occ.v","names":[]},{"file":"relation/Relation.v","names":["fuse_ok","pheld","pfuse","sdrop","dpairs","gch"]}],
"usedIn":["th-compose","p-rel"]}
nb['source']=[x for x in nb['source'] if x['names']]
i=s2['blocks'].index(bc); s2['blocks'].insert(i+1,nb)
bc['why']=bc['why'].replace(r"The fusion clause of the process relation is what makes the connect rule a lemma rather than a new induction.", r"The connect rule is proved by an induction over the steps of both components, with the theorem of [[th-fuse]] for the residuals.")
# notes
del n['P.fuse']
n['th.gfuse']={"title":"Fusion preserves the process relation","meaning":r"Renaming held ends by $h$ and restricting the channels $D$ maps $P^W_\alpha\llbracket \Sigma \vdash T\rrbracket$ into $P^W_\alpha\llbracket (h, D)\cdot\Sigma \vdash T\rrbracket$.","why":"The residuals in the proof of P-Connect are fusions of the components.","breaks":r"Without $\mathsf{tfree}\,T$ a restriction could close a channel both of whose ends sit in the final value.","example":r"$(\mathsf{id}, \{c\})$ restricts the pair $c^{+}, c^{-}$ of $\Sigma$.","signature":r"p \in P \land \ldots \Rightarrow q \in P","source":[{"file":"compat/Fusion.v","names":["Prel_gfuse"]}]}
n['th.occ']={"title":r"$E \sim_h E'$","meaning":r"The threads $E'$ arise from $E$ by replacing each occurrence of a held end $o$ with $h(o)$ and each occurrence of another end with some end.","why":"A link renames ends that the process does not hold, and their images are not determined by $h$.","breaks":"Nothing. It is a definition.","example":r"$\mathsf{close}\,a \sim_h \mathsf{close}\,h(a)$ for a held end $a$.","signature":r"\sim_h \subseteq \mathcal{M}(\mathsf{Expr}) \times \mathcal{M}(\mathsf{Expr})","source":[{"file":"compat/Fusion.v","names":["gfuse"]}]}
n['sr.pfuse']['title']=r"$q \in (h, D)\cdot p$"
n['sr.pfuse']['meaning']=r"$q$ restricts $\mathsf{gch}_h[C] \cup D$ and its threads are related to those of $p$ by $\sim_h$."
n['sr.pfuse']['signature']=r"(h, D)\cdot p \subseteq \mathsf{Proc}"
n['sr.pfuse']['source']=[{"file":"compat/Fusion.v","names":["gfuse"]},{"file":"relation/Relation.v","names":["pfuse"]}]
n['sr.pfuse'].pop('deviations',None)
n['sr.fuseok']['why']="One notion covers renaming, restricting pairs and the renaming of a link."
for k in ['P.clauses']:
  if json.dumps(m).count('sym{'+k+'}')==0: n[k]['why']="$P$ asks them in each larger world, and a term asks the same three of itself."
json.dump(m,open(p,'w'),ensure_ascii=False,indent=1); open(p,'a').write('\n')
m=json.load(open(p)); n=m['notes']
blk={b['id']:(s,b) for s in m['sections'] for b in s['blocks']}
s,b=blk["th-fuse"]
sec=s; bl=sec['blocks']; bl.remove(b); bl.insert([x['id'] for x in bl].index('th-compose'),b)
b['caption']=b['caption'].replace("The relation is preserved.","The [[p-rel|process relation]] is preserved.")
s,pr=blk['p-rel']; pr['why']=r"The relation reads a process only at its interface. The semantic P-Connect is proved by an induction over the steps of both components, and closure under renaming and restriction is a theorem that this induction uses for the residual components."
n['th.gfuse']['breaks']=r"Without $\mathsf{tfree}\,T$ a restriction could close a channel whose two ends are both held by the final value."
n['sr.pfuse']['deviations']=[{"kind":"renamed","reason":r"$q \in (h, D)\cdot p$ is the last two conjuncts of `gfuse`, and $\mathsf{gch}_h$ is `gch h`.","names":["gfuse"]}]
json.dump(m,open(p,'w'),ensure_ascii=False,indent=1); open(p,'a').write('\n')
# the author: not an interesting theorem. No block, one sentence at P.
m=json.load(open(p)); n=m['notes']
blk={b['id']:(s,b) for s in m['sections'] for b in s['blocks']}
s,b=blk['th-fuse']; s['blocks'].remove(b)
for k in ['th.gfuse','th.occ','sr.fuseok','sr.pfuse','sr.sdrop','sr.held','sr.gch','fuse.dcomm','fuse.inj','fuse.partners','fuse.D','fuse.dpairs']:
  n.pop(k,None)
s,pr=blk['p-rel']
pr['caption']=pr['caption'].replace(r"Renaming held ends and restricting dual pairs of interface ends preserve the relation by the theorem of [[th-fuse]].", r"Renaming the ends a process holds and restricting dual pairs of its interface preserve the relation.")
pr['source'].append({"file":"compat/Fusion.v","names":["Prel_gfuse"]})
pr['usedIn']=[u for u in pr['usedIn'] if u!='th-fuse']
s,bc=blk['th-compose']
bc['why']=bc['why'].replace(r"The connect rule is proved by an induction over the steps of both components, with the theorem of [[th-fuse]] for the residuals.", r"The connect rule is proved by an induction over the steps of both components.")
pr['why']=r"The relation reads a process only at its interface. The semantic P-Connect is proved by an induction over the steps of both components."
json.dump(m,open(p,'w'),ensure_ascii=False,indent=1); open(p,'a').write('\n')
m=json.load(open(p))
for s in m['sections']:
  for b in s['blocks']:
    if b['id']=='th-compose':
      b['formula']=b['formula'].replace(r"\Sigma_2 \cup \Sigma_D", r"\Sigma_2 \cup \overline{\Sigma_C}")
json.dump(m,open(p,'w'),ensure_ascii=False,indent=1); open(p,'a').write('\n')
# clause notes: no fusion, no primes
m=json.load(open(p)); n=m['notes']
def sub(s): return s.replace("p''","PPP").replace("\\Sigma'","\\Sigma").replace("p'","p").replace("PPP","p'")
for k in ['P-Stop','P-Ready','P-Step']:
  v=n[k]
  for f in ['meaning','signature','example']:
    if f in v and not (k=='P-Step' and f=='meaning'): v[f]=sub(v[f])
  for a in v.get('args',[]): a['name']=sub(a['name']); a['meaning']=a['meaning'].replace('the fused interface and process','the interface and the process').replace('the fused process','the process')
n['P-Step']['meaning']=r"Each step $p \xrightarrow{ev} p'$ meets $\mathsf{Pobl}_{ev}$. A process steps when some numbering of its threads steps, $p \xrightarrow{ev} p' \iff \exists q, q'.\ \mathsf{erase}\,q = p \land q \xrightarrow{ev} q' \land \mathsf{erase}\,q' = p'$."
n['P.clauses']['why']="$P$ asks them in each larger world, and a term asks the same three of itself."
n['P.clauses']['title']=r"$\mathsf{clauses}_{W'}(\Sigma, p)$"
n['P.clauses']['meaning']=r"The stop, ready and step clauses of $p$ at the interface $\Sigma$ in the world $W'$."
n['P.clauses']['args']=[{"name":"W'","meaning":"the later world"},{"name":"\\Sigma","meaning":"the interface"},{"name":"p","meaning":"the process"}]
json.dump(m,open(p,'w'),ensure_ascii=False,indent=1); open(p,'a').write('\n')
