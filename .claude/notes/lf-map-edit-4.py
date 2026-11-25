import json
P='docs/explorer/map.json'
m=json.load(open(P)); B={b['id']:b for s in m['sections'] for b in s['blocks']}; N=m['notes']
def sub(s,o,n,c=1):
    assert s.count(o)==c,(o[:70],s.count(o)); return s.replace(o,n)
R = r"\mathsf{ranked}"
# w-ext
we=B['w-ext']
we['formula']=sub(we['formula'], r"\sym{w.models}{\sym{w.lfworld}{\mathsf{wf}}\,W \Rightarrow", r"\sym{w.models}{\sym{w.lfworld}{\mathsf{ranked}}\,W \Rightarrow")
we['formula']=sub(we['formula'], r"\sym{w.R7}{\sym{w.lfworld}{\mathsf{wf}}(W_1 \sqcup W_2) \iff \mathsf{wf}\,W_1 \land \mathsf{wf}\,W_2 \land \mathsf{wf}(W_1|_S \sqcup W_2|_S)}",
    r"\sym{w.R7}{\sym{w.lfworld}{\mathsf{ranked}}(W_1 \sqcup W_2) \iff \mathsf{ranked}\,W_1 \land \mathsf{ranked}\,W_2 \land \mathsf{ranked}(W_1|_S \sqcup W_2|_S)}")
we['caption']=sub(we['caption'], r"\inmode{lf}{A well-formed well-founded world has a ranked extension, ranked by the rank function of its order.}", r"\inmode{lf}{A well-formed ranked world of typing has a ranked extension, ranked by the rank function of its order.}")
n=N['w.R7']; n['meaning']=sub(n['meaning'], r"The same holds for $\mathsf{wf}$ in place of $\mathsf{cons}$.", r"The same holds for $\mathsf{ranked}$ in place of $\mathsf{cons}$.")
n=N['w.models']; n['meaning']=sub(n['meaning'], r"A well-formed well-founded world has a ranked extension,", r"A well-formed ranked world has a ranked extension,")
n['deviations'][0]['reason']=sub(n['deviations'][0]['reason'], r"and $\mathsf{wf}$ for `swf`", r"and $\mathsf{ranked}$ for `swf`")
# r-new: wf of the tree order is a relation, not a world
rn=B['r-new']
rn['formula']=sub(rn['formula'], r"\sym{w.lfworld}{\mathsf{wf}}(\sym{new.step}{\prec^{\rho}_{C}})", r"\sym{new.wf}{\mathsf{wf}}(\sym{new.step}{\prec^{\rho}_{C}})")
N['new.wf']={"title": r"$\mathsf{wf}$ of a relation",
  "meaning": r"$\mathsf{wf}(R)$ when the relation $R$ has no infinite descending chain $\cdots \mathrel{R} x_2 \mathrel{R} x_1 \mathrel{R} x_0$.",
  "why": r"E-New at a finite bound asks it of the order $\prec^{\rho}_{C}$ on the new tree, so that ranks for the tree exist.",
  "breaks": "Nothing. It is a definition.",
  "example": r"The program order on a finite tree is well-founded.",
  "signature": r"\mathsf{wf} : (\sym{type.Point}{\mathsf{Point}} \to \sym{type.Point}{\mathsf{Point}} \to \mathsf{Prop}) \to \mathsf{Prop}",
  "args": [{"name": "R", "meaning": "a relation on points"}],
  "source": [{"file": "static/Contexts.v", "names": ["new_ok"]}],
  "deviations": [{"kind": "renamed", "reason": r"$\mathsf{wf}$ is `well_founded` of the Rocq standard library, which `new_ok` applies to `new_step C`.", "names": ["new_ok"]}]}
# process typing premises
n=N['P-Term.wf']
n['title']=r"$\inmodeplain{df}{\mathsf{cons}}\inmode{lf}{\mathsf{ranked}}\,W$"
n['meaning']=r"The world of a single thread is consistent\inmode{lf}{, or ranked at a finite bound}, well-formedness included."
n['signature']=r"\inmodeplain{df}{\mathsf{cons}}\inmode{lf}{\mathsf{ranked}}\,W"
n['deviations'][0]['reason']=r"`p_term` asks `sworld_wf W ∧ wok N W`. The map folds `sworld_wf` into $\mathsf{cons}$\inmode{lf}{ and $\mathsf{ranked}$}, and it shows `wok N W` as $\mathsf{cons}$ at $N = \infty$\inmode{lf}{ and as $\mathsf{ranked}$ at a finite bound}."
n=N['P-Connect.wf']
n['meaning']=r"$\mathsf{cons}(W_1 \sqcup W_2)$\inmode{lf}{, or $\mathsf{ranked}(W_1 \sqcup W_2)$ at a finite bound}, where $W_1$ and $W_2$ are the worlds of the two components."
n['signature']=r"\inmodeplain{df}{\mathsf{cons}}\inmode{lf}{\mathsf{ranked}}(W_1 \sqcup W_2)"
n['deviations'][0]['reason']=sub(n['deviations'][0]['reason'], r"so the folded $\mathsf{cons}$ and $\mathsf{wf}$ of the join ask nothing more.", r"so the folded $\mathsf{cons}$\inmode{lf}{ and $\mathsf{ranked}$} of the join ask nothing more.")
n=N['lfi.wf']; n['meaning']=sub(n['meaning'], r"process typing asks $\mathsf{wf}$ of its world,", r"process typing asks a ranked world of typing,")
n=N['sp.allR']; n['why']=sub(n['why'], r"through $\mathsf{wf}\,(W_1|_S \sqcup W_2|_S)$,", r"through $\mathsf{ranked}\,(W_1|_S \sqcup W_2|_S)$,")
n=N['w.acyc']; n['example']=sub(n['example'], r"\inmode{lf}{ and not well-founded}", r"\inmode{lf}{ and not ranked}")
# existential property: axioms become a tag
so=B['sr-ord']
so['formula']=sub(so['formula'], r"\sym{ord.exprop}{\mathsf{EM} \land \mathsf{FC} \land (\forall \alpha.", r"\sym{ord.exprop}{(\forall \alpha.")
n=N['ord.exprop']
n['meaning']=r"A family $P\,x\,\alpha$ closed downwards in $\alpha$ with a witness at each index has one witness that serves each index."
n['signature']=r"(\forall \alpha.\ \exists x.\ P\,x\,\alpha) \land (\beta \leq \alpha \land P\,x\,\alpha \Rightarrow P\,x\,\beta) \Rightarrow \exists x.\ \forall \alpha.\ P\,x\,\alpha"
n['assumes']=["EM","FC"]
n.pop('deviations',None)
json.dump(m,open(P,'w'),ensure_ascii=False,indent=1); open(P,'a').write('\n'); print('ok')
