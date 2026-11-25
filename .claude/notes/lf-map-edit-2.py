import json, re
P = 'docs/explorer/map.json'
m = json.load(open(P))
B = {b['id']: b for s in m['sections'] for b in s['blocks']}
N = m['notes']
S = {s['id']: s for s in m['sections']}

def sub(s, old, new, count=1):
    assert s.count(old) == count, (old[:90], s.count(old))
    return s.replace(old, new)

# ---------------------------------------------------------------- theorems intro
th = S['theorems']
th['intro'] = sub(th['intro'], r"The deadlock-free results, binary and n-ary, take no classical hypothesis. \inmode{lf}{The lock-free results stand next to their deadlock-free counterparts and take excluded middle and functional choice as explicit hypotheses.}",
                  r"The deadlock-free results take no classical hypothesis. \inmode{lf}{The lock-free results stand next to their deadlock-free counterparts, and a tag on each names the classical hypotheses it takes.}")

# ---------------------------------------------------------------- th-chain
ch = B['th-chain']
f = ch['formula']
i = f.index(r"\inmodeplain{lf}{\\[3ex]}")
ch['formula'] = f[:i] + r"""\inmodeplain{lf}{\\[3ex]}\inmode{lf}{\Sigma \sym{tp.pjudg}{\vdash\inmode{lf}{^{N}}_W} p : T \land N \in \mathbb{N}}\inmodeplain{lf}{&}\inmode{lf}{\overset{\sym{th.lf-fundamental}{\textsf{lf\_fundamental}}}{\Longrightarrow}}\inmodeplain{lf}{&}\inmode{lf}{\Sigma \mathrel{\sym{sp.lfsem}{\Vvdash}}^{N}_{W} p : T}
\inmodeplain{lf}{\\[1ex]}\inmode{lf}{\sym{w.lfworld}{\mathsf{ranked}}\,W \land \varnothing \mathrel{\sym{sp.lfsem}{\Vvdash}}^{N}_{W} p : T}\inmodeplain{lf}{&}\inmode{lf}{\overset{\sym{th.lf-sems-adequacy}{\textsf{lf\_sems\_adequacy}}}{\Longrightarrow}}\inmodeplain{lf}{&}\inmode{lf}{\sym{prop.lf}{\mathsf{lock\_free}}\,p}
\end{array}"""
ch['caption'] = sub(ch['caption'], " The arrows are proved in [[th-fund-proc]], [[th-adeq]] and [[th-terms]].", " The arrows are proved in [[th-fund-proc]] and [[th-adeq]], and the case of P-Term rests on [[th-terms]].")
ch['caption'] = sub(ch['caption'], r"\inmode{lf}{Lock freedom uses the same relation at $\kappa_L$", r"\inmode{lf}{Lock freedom takes the same two steps at a finite bound over ranked worlds. It uses the relation at $\kappa_L$")
ch['caption'] = sub(ch['caption'], r"together with fuel, over ranked worlds, the two columns of [[fu-vs]].", r"together with fuel, the two columns of [[fu-vs]].")
ch['why'] = r"Each arrow is one theorem of this section."
ch['source'] = [
    {"file": "static/FundamentalProc.v", "names": ["fundamental_proc", "adequacy_sw", "soundness"]},
    {"file": "soup/LFTyped.v", "names": ["lf_fundamental", "lf_soundness"]},
    {"file": "soup/LFCompose.v", "names": ["lf_sems_adequacy"]},
]

# ---------------------------------------------------------------- th-sound
sd = B['th-sound']
sd['formula'] = r"""\begin{array}{l}\sym{th.soundness}{\begin{array}{l}\varnothing \sym{tp.pjudg}{\vdash\inmode{lf}{^{\infty}}_W} p : T \\ \quad\Longrightarrow\ \sym{prop.df}{\mathsf{deadlock\_free}}\,p\end{array}}\inmodeplain{lf}{ \\[1.5ex] }\inmode{lf}{\sym{th.lf-soundness}{\begin{array}{l}\varnothing \sym{tp.pjudg}{\vdash\inmode{lf}{^{N}}_W} p : T \land N \in \mathbb{N} \\ \quad\Longrightarrow\ \sym{prop.lf}{\mathsf{lock\_free}}\,p\end{array}}}\end{array}"""
sd['caption'] = r"A closed typed process is deadlock free, the property of [[sem-props]], and no classical hypothesis enters. The proof combines [[th-fund-proc]] and [[th-adeq]] for the rules of [[p-typing]]. \inmode{lf}{A closed process typed at a finite bound $N$ over a [[t-lf-wf|ranked world]] is lock free.} The Rocq also proves soundness for n-ary composites and for one closed thread\inmode{lf}{, the absence of divergence by free steps, the existence of a weakly fair maximal run and lock freedom in reachability form}."
sd['why'] = r"These are the main results. Each one composes a fundamental theorem with adequacy."
sd['source'] = [
    {"file": "static/FundamentalProc.v", "names": ["soundness"]},
    {"file": "soup/LFTyped.v", "names": ["lf_soundness"]},
]

# ---------------------------------------------------------------- th-compose
cp = B['th-compose']
f = cp['formula']
i = f.index(r"\inmodeplain{lf}{ \\[1.5ex] }\inmode{lf}{\sym{th.lf-soup-term}")
cp['formula'] = f[:i] + r"\end{array}"
cp['formula'] = sub(cp['formula'], r"\sym{th.em}{\mathsf{EM}} \land N \in \mathbb{N}", r"N \in \mathbb{N}")
cp['source'] = [x for x in cp['source'] if x['file'] != 'soup/LFCompose.v'] + [{"file": "soup/LFCompose.v", "names": ["lf_p_term", "lf_p_connect"]}]

# ---------------------------------------------------------------- th-fund-proc
fp = B['th-fund-proc']
fp['formula'] = r"""\begin{array}{l}\sym{th.fundamental-proc}{\begin{array}{l}\Sigma \sym{tp.pjudg}{\vdash\inmode{lf}{^{\infty}}_W} p : T \\ \quad\Longrightarrow\ \Sigma \mathrel{\sym{sj.sw}{\vDash}}_{W} p : T\end{array}}\inmodeplain{lf}{ \\[1.5ex] }\inmode{lf}{\sym{th.lf-fundamental}{\begin{array}{l}\Sigma \sym{tp.pjudg}{\vdash\inmode{lf}{^{N}}_W} p : T \land N \in \mathbb{N} \\ \quad\Longrightarrow\ \Sigma \mathrel{\sym{sp.lfsem}{\Vvdash}}^{N}_{W} p : T\end{array}}}\end{array}"""
fp['caption'] = sub(fp['caption'], r"\inmode{lf}{Under excluded middle the same holds at a finite bound, with the lock-free judgment.}", r"\inmode{lf}{The same holds at a finite bound, with the lock-free judgment.}")
fp['caption'] = fp['caption'] + r" \inmode{lf}{The Rocq also proves the form at $\kappa_L$.}"
fp['source'] = [
    {"file": "static/FundamentalProc.v", "names": ["fundamental_proc"]},
    {"file": "soup/LFTyped.v", "names": ["lf_fundamental"]},
]

# ---------------------------------------------------------------- th-adeq
ad = B['th-adeq']
ad['formula'] = r"""\begin{array}{c}\begin{array}{l}\sym{th.adequacy}{\begin{array}{l}\sym{w.acyc}{\mathsf{cons}}\,W \land \sym{sj.proc}{\forall \alpha.\ p \in \sym{th.Prel}{P^{W}_{\alpha}\llbracket \varnothing \vdash T \rrbracket}} \\ \quad\Longrightarrow\ \sym{prop.df}{\mathsf{deadlock\_free}}\,p\end{array}} \\[1.5ex] \sym{th.adequacy-h}{\begin{array}{l}\sym{w.acyc}{\mathsf{cons}}\,W \land \varnothing \mathrel{\sym{sj.sw}{\vDash}}_W p : T \\ \quad\Longrightarrow\ \sym{prop.df}{\mathsf{deadlock\_free}}\,p\end{array}}\end{array}\inmodeplain{lf}{\\[3ex]}\inmode{lf}{\begin{array}{l}\sym{th.lf-adequacy}{\begin{array}{l}\sym{w.kind}{\mathsf{ranked}}\,W \land \forall \alpha.\ \exists a.\ \sym{proc.erase}{\mathsf{erase}}(\sym{th.qa}{q_a}) = p \land a \in \sym{th.soup}{S^{N,W}_{\alpha}\llbracket \varnothing \vdash T \rrbracket} \\ \quad\Longrightarrow\ \sym{prop.lf}{\mathsf{lock\_free}}\,p\end{array}} \\[1.5ex] \sym{th.lf-sems-adequacy}{\begin{array}{l}\sym{w.lfworld}{\mathsf{ranked}}\,W \land \varnothing \mathrel{\sym{sp.lfsem}{\Vvdash}}^{N}_W p : T \\ \quad\Longrightarrow\ \sym{prop.lf}{\mathsf{lock\_free}}\,p\end{array}}\end{array}}\end{array}"""
ad['caption'] = r"A closed process in the process relation at each index at a consistent world is deadlock free. So is a closed process in the semantic judgment of [[sj-all]] at a well-formed consistent world, which is its own consistent extension by [[w-ext]]. The proof reads the readiness of [[rd]]. \inmode{lf}{A closed process in the [[soup|lock-free process relation]] at each index at a [[t-lf-wf|ranked world]] is lock free, as [[sem-props]] defines over the [[sem-events|events]] of a run. The measure is the rank of the awaited point and the counter that the relation records. So is a closed process in the lock-free judgment at a ranked world of typing. The Rocq also derives that each thread progresses on each weakly fair maximal run when $p$ has no internal divergence.}"
ad['source'] = [
    {"file": "relation/Adequacy.v", "names": ["adequacy", "adequacy_gen"]},
    {"file": "static/FundamentalProc.v", "names": ["adequacy_sw"]},
    {"file": "soup/LFAdequacy.v", "names": ["lf_adequacy"]},
    {"file": "soup/LFCompose.v", "names": ["lf_sems_adequacy"]},
]

# ---------------------------------------------------------------- th-terms
tt = B['th-terms']
f = tt['formula']
j = f.index(r"\inmodeplain{lf}{ \\[1.5ex] }")
dfrow = f[len(r"\begin{array}{l}"):j]
k = f.index(r"\inmode{lf}{\sym{th.fsem-of-cost}")
fsemrow = f[k:-len(r"\end{array}")]
assert fsemrow.endswith("}}") and dfrow.startswith(r"\sym{th.fundamental}")
lfr = r"""\inmode{lf}{\sym{th.live-fundamental-ranked}{\begin{array}{l}\begin{array}{l}\sym{w.wf}{\mathsf{world\_wf}}\,W \land \varnothing ; \Delta \mathrel{\sym{tp.vdash}{\vdash}}^{F}_{W\inmode{lf}{,N}} t : T\ !\ \varepsilon \\ \land\ N \in \mathbb{N} \land W \mathrel{\sym{w.ext}{\sqsubseteq}} W' \land \sym{w.acyc}{\mathsf{cons}}\,W'\end{array} \\ \quad\Longrightarrow\ \sym{th.df}{\Delta_{df}} \mathrel{\sym{sj.term}{\vDash[\kappa_L]}}^{F}_{W'} t : T_{df}\end{array}}}"""
tt['formula'] = r"\begin{array}{l}" + dfrow + r"\inmodeplain{lf}{ \\[1.5ex] }" + lfr + r"\inmodeplain{lf}{ \\[1.5ex] }" + fsemrow + r"\end{array}"
tt['caption'] = r"A typed term is in the semantic term judgment of [[sj-all]] at each consistent extension of its world. The proof is one induction on the derivation, with one compatibility lemma per rule. \inmode{lf}{A term typed at a finite bound is in the judgment at $\kappa_L$ at each consistent extension, strict or ranked, and it has [[fu|fuel]] with its values in [[fv]], under the annotations of [[ty-ann]]. The Rocq also proves the forms at $\kappa_L$ over strict worlds, the forms for annotated typing and the cost judgment behind fuel.}"
tt['source'] = [
    {"file": "static/Fundamental.v", "names": ["typed_sem", "fundamental", "live_fundamental_ranked"]},
    {"file": "cost/CostFund.v", "names": ["fsem_of_cost"]},
]

# ---------------------------------------------------------------- notes: assumes and statements
def note(k): return N[k]
n = note('th.lf-soundness')
n['meaning'] = r"$\varnothing \vdash\inmode{lf}{^{N}}_{W} p : T$ at a finite $N$ implies that $p$ is lock free."
n['why'] = r"The lock-free fundamental theorem, a ranked extension of the world of the derivation, and lock-free adequacy. The choice fixes one annotated configuration that serves each index."
n['signature'] = r"\varnothing \vdash\inmode{lf}{^{N}}_{W} p : T \land N \in \mathbb{N} \Rightarrow \mathsf{lock\_free}\,p"
n['assumes'] = ["EM", "FC"]
n = note('th.lf-fundamental')
n['meaning'] = r"$\Sigma \vdash\inmode{lf}{^{N}}_{W} p : T$ at a finite $N$ implies $\Sigma \Vvdash^{N}_{W} p : T$, the lock-free judgment at each ranked extension of $W$."
n['signature'] = r"\Sigma \vdash\inmode{lf}{^{N}}_{W} p : T \land N \in \mathbb{N} \Rightarrow \Sigma \Vvdash^{N}_{W} p : T"
n['assumes'] = ["EM"]
n = note('th.lf-p-term')
n['meaning'] = r"A thread that meets the premises of P-Term at a finite $N$ satisfies $\Sigma \Vvdash\inmode{lf}{^{N}}_W (C_0, \{t\}) : T$."
n['signature'] = r"N \in \mathbb{N} \land \mathsf{world\_wf}\,W \land \mathsf{pterm}_N(\Sigma, C_0, t, T) \Rightarrow \Sigma \Vvdash\inmode{lf}{^{N}}_W (C_0, \{t\}) : T"
n['assumes'] = ["EM"]
n = note('th.lf-p-connect')
n['meaning'] = sub(n['meaning'], r"With $\mathsf{wf}\,W_1$, $\mathsf{wf}\,W_2$ and $\mathsf{wf}\,(W_1|_S \sqcup W_2|_S)$ a closed composite is lock free.", r"With $W_1$, $W_2$ and $W_1|_S \sqcup W_2|_S$ ranked, a closed composite is lock free.")
n['why'] = sub(n['why'], "A ranked extension of the join exists exactly when the join is well-founded, which the condition on the shared bases gives.", "A ranked extension of the join exists exactly when the join is ranked, which the condition on the shared bases gives.")
n = note('th.lf-sems-adequacy')
n['meaning'] = r"If $W$ is ranked and $\varnothing \Vvdash\inmode{lf}{^{N}}_W p : T$, then $p$ is lock free."
n['why'] = r"A ranked world of typing has a ranked extension, at which lock-free adequacy applies."
n['signature'] = r"\mathsf{ranked}\,W \land \varnothing \Vvdash\inmode{lf}{^{N}}_W p : T \Rightarrow \mathsf{lock\_free}\,p"
n['assumes'] = ["EM", "FC"]
n = note('th.live-fundamental-ranked')
n['title'] = r"Fundamental theorem for lock-free typing"
n['meaning'] = r"A derivation at a finite bound $N$ gives the semantic judgment at $\kappa_L$ at erased environments and type, at each consistent extension $W'$ of $W$ of either kind."
n['signature'] = r"\mathsf{world\_wf}\,W \land \varnothing ; \Delta \vdash^{F}_{W\inmode{lf}{,N}} t : T\ !\ c \land N \in \mathbb{N} \land W \sqsubseteq W' \land \mathsf{cons}\,W' \Rightarrow \Delta_{df} \mathrel{\vDash[\kappa_L]}^{F}_{W'} t : T_{df}"
n['assumes'] = ["EM"]
n = note('th.lf-adequacy')
n['assumes'] = ["EM", "FC"]
n['deviations'] = [d for d in n.get('deviations', [])]

# ---------------------------------------------------------------- w.lfworld, sp notes, fuel notes
n = note('w.lfworld')
n['title'] = r"$\mathsf{ranked}$ for a world of typing"
n['meaning'] = r"$\mathsf{ranked}\,W$ when $W$ is well formed and its order has a rank function $\varrho$ into the ordinals, $\varrho(x) < \varrho(y)$ whenever $x \prec_W y$. So no infinite chain $\cdots \prec x_2 \prec x_1 \prec x_0$ exists."
n['why'] = r"A world of typing has a ranked extension exactly when its order has ranks, and these ranks give the extension. Process typing at a finite bound asks a ranked world."
n['breaks'] = r"A world whose order holds an infinite descending chain has no ranks, and lock-free adequacy would have no measure."
n['example'] = r"$W$ with no facts is ranked."
n['signature'] = r"\mathsf{ranked} : \sym{type.World}{\mathsf{World}} \to \mathsf{Prop}"
n['source'] = [{"file": "types/Worlds.v", "names": ["swf", "wmodels_exists"]}, {"file": "relation/Ranks.v", "names": ["ranked", "wf"]}]
n['deviations'] = [
    {"kind": "notation", "reason": r"Well-formedness `sworld_wf` is a separate conjunct in the Rocq, folded in here.", "names": ["sworld_wf"]},
    {"kind": "renamed", "reason": r"$\mathsf{ranked}$ is `swf`, which is `wf` of relation/Ranks.v at the order of the world.", "names": ["swf", "wf"]},
]

n = note('sp.own')
n['title'] = r"Well annotated, $\mathsf{wa}^{N}_{\Sigma}(a, \Delta)$"
n['meaning'] = r"The annotations $\Delta$ fit the configuration $q$ of $a$ and the interface $\Sigma$. Each held end belongs to a thread of $q$ and is restricted in $q$ or in $\Sigma$. Both ends of a restricted channel are held. Their types in $\Delta$ have dual points and session types dual up to annotations, and their protocols are dual up to $\sqsubseteq$. Their tickets sum to at most $N$. Each counter is finite and at most its tickets, and the tickets are at most $N$. An end of $\Sigma$ has its entry of $\Sigma$ as its type, the session type of that entry as its protocol, and at most $\lfloor N/2 \rfloor$ tickets."
n['why'] = r"Lock-free adequacy reads the thread holding an end, its point and its counter from $K$, and concludes that the dual end of a restricted end is held by some thread at the dual protocol."
n['breaks'] = r"Without it a thread could wait on an end whose dual end no thread holds, and the chain of waits in the proof of adequacy would break off."
n['example'] = r"Two threads closing $c^{+}$ and $c^{-}$, each holding one end, with $C = \{c\}$."
n['signature'] = r"\mathsf{wa}^{N}_{\Sigma} : \sym{type.LFState}{\mathsf{LFState}} \to (\sym{type.End}{\mathsf{End}} \rightharpoonup (\sym{type.STy}{\mathsf{STy}} \times \sym{type.Point}{\mathsf{Point}}) \times (\sym{type.STy}{\mathsf{STy}} \times \mathbb{N} \times \mathbb{N})) \to \mathsf{Prop}"
n['args'] = [{"name": "N", "meaning": "the bound on the tickets of a channel"}, {"name": r"\Sigma", "meaning": "the interface"}, {"name": "a", "meaning": r"the annotated configuration $(q, K, W_a)$"}, {"name": r"\Delta", "meaning": "the annotations of the held ends"}]
n['source'] = [{"file": "soup/State.v", "names": ["soup_consistent", "sp_owner", "sp_closed", "sp_pair", "sp_sdual", "sp_pdual", "sp_sig", "sp_fin", "sp_psig", "sp_cap", "sp_tsum", "sp_sigcap"]}, {"file": "soup/Soup.v", "names": ["soup_inv"]}, {"file": "types/Types.v", "names": ["khalf"]}]
n['deviations'] = [
    {"kind": "renamed", "reason": r"$\mathsf{wa}$ names the conjuncts of `soup_consistent` other than `sp_pts` and `sp_dom`, which $\Delta : K$ states.", "names": ["soup_consistent"]},
    {"kind": "simplified", "reason": r"The interface annotation $\eta$ of `soup_gen` gives the bound on the tickets of an interface end. `soup_inv` fixes it to $\lfloor N/2 \rfloor$ at each end by `khalf`, and the map writes that bound.", "names": ["soup_inv", "khalf", "sp_sigcap"]},
]

N['sp.delta'] = {
    "title": r"Annotations $\Delta : K$",
    "meaning": r"$\Delta$ gives each end $o$ with $K(o) = (t, x, f, m)$ a session type $S$ at the point $x$ for the relation and a protocol $P$ at the counter $f$ and tickets $m$ for fuel, $\Delta(o) = (S_x, P^{f,m})$. $\Delta^{E}_t$ and $\Delta^{F}_t$ are its two parts on the ends that $K$ gives $t$.",
    "why": r"The relation and fuel read the same held ends, the relation with points and fuel with counters. O-New and F-New choose the session type of a new channel in separate existentials, so $S$ and $P$ are two entries.",
    "breaks": "Nothing. It is a definition.",
    "example": r"$K(c^{+}) = (0, x, 2, 3)$ and $\Delta(c^{+}) = (\mathsf{Close}_x, \mathsf{Close}^{2,3})$.",
    "signature": r"\Delta : \sym{type.End}{\mathsf{End}} \rightharpoonup (\sym{type.STy}{\mathsf{STy}} \times \sym{type.Point}{\mathsf{Point}}) \times (\sym{type.STy}{\mathsf{STy}} \times \mathbb{N} \times \mathbb{N})",
    "args": [{"name": "K", "meaning": "the ownership map of the annotated configuration"}, {"name": "t", "meaning": "a thread"}],
    "source": [{"file": "soup/State.v", "names": ["soup_gen", "sp_pts", "sp_dom", "kres", "ctrs"]}, {"file": "soup/Soup.v", "names": ["Soup"]}],
    "deviations": [{"kind": "merged", "reason": r"The Rocq keeps an environment `A` of the relation and a protocol map `Π` of fuel, chosen per index, and the counters and tickets in `K`. `sp_pts` and `sp_dom` give them one domain and the points of `K`, so one map $\Delta$ states them.", "names": ["sp_pts", "sp_dom"]}],
}
n = note('sp.exists')
n['meaning'] = r"$\exists \Delta : K,\ U$, the annotations of the held ends and the result type of each thread, chosen at each index."
n['example'] = r"$\Delta(c^{+}) = (\mathsf{Close}_x, \mathsf{Close}^{2,3})$ and $U_0 = T$."
n['signature'] = r"\exists \Delta : K,\ U : \mathbb{N} \to \sym{type.Ty}{\mathsf{Ty}}"
n['args'] = [{"name": r"\Delta", "meaning": "the annotations of the held ends"}, {"name": "U", "meaning": "the result type of each thread"}]
n['source'] = [{"file": "soup/Soup.v", "names": ["Soup"]}]
n = note('sp.rel')
n['meaning'] = r"$\forall t.\ q(t) = e \Rightarrow e \in E[\kappa_L]^{W_a}_\alpha\llbracket \Delta^{E}_t \vdash U_t\rrbracket^{\varnothing}$, where $\Delta^{E}_t$ maps the ends that $K$ gives $t$ to their types."
n['example'] = r"$q(0) \in E[\kappa_L]^{W_a}_\alpha\llbracket \Delta^{E}_0 \vdash T\rrbracket^{\varnothing}$."
n['signature'] = r"\forall t, e.\ q(t) = e \Rightarrow e \in E[\kappa_L]^{W_a}_{\alpha}\llbracket \Delta^{E}_t \vdash U_t \rrbracket^{\varnothing}"
n['args'] = [{"name": "t", "meaning": "a thread"}, {"name": r"\Delta^{E}_t", "meaning": r"the types of the ends held by $t$"}]
n = note('sp.fuel')
n['meaning'] = r"$\forall t.\ q(t) = e \Rightarrow e \in F^N_\alpha\llbracket \Delta^{F}_t \vdash \mathsf{thread}\ !\ \infty\rrbracket$, where $\Delta^{F}_t$ maps the ends that $K$ gives $t$ to their protocols, counters and tickets."
n['why'] = r"The counters and tickets of $\Delta^{F}_t$ are those recorded in $K$."
n['example'] = r"$\Delta^{F}_0 = \{a \mapsto S^{2,3}\}$."
n['signature'] = r"e \in F^{N}_{\alpha}\llbracket \Delta^{F}_t \vdash \mathsf{thread}\ !\ \infty \rrbracket"
n['args'] = [{"name": "t", "meaning": "a thread"}, {"name": r"\Delta^{F}_t", "meaning": r"the protocols, counters and tickets of the ends held by $t$"}]

# fuel notes
n = note('fu.val')
n['title'] = r"$(\mathsf{stop})$"
n['meaning'] = r"$e \in \mathsf{Val} \Rightarrow e \in FV^{N}_{\alpha}\llbracket \Phi \vdash \sigma\rrbracket$."
n['signature'] = r"e \in \mathsf{Val} \Rightarrow e \in FV^{N}_{\alpha}\llbracket \Phi \vdash \sigma \rrbracket"
n['args'] = [{"name": "e", "meaning": "the term"}]
n = note('fu.step')
n['meaning'] = r"$\forall \ell, e'.\ e \xrightarrow{\ell} e' \Rightarrow \mathsf{Fobl}_\ell(e')$, whose rules read $e'$ at each ordinal $\beta < \alpha$."
n['signature'] = r"\forall \ell, e'.\ e \xrightarrow{\ell} e' \Rightarrow \mathsf{Fobl}_{\ell}(e')"
n['args'] = [{"name": r"\ell, e'", "meaning": "the step label and the successor"}]
N['fu.at'] = {
    "title": r"$e'\ \mathsf{at}\ \Phi'\ !\ d'$",
    "meaning": r"The successor $e'$ has fuel at the held ends $\Phi'$ and the frame $d'$ at each index $\beta < \alpha$, at the result $\sigma$ of the thread.",
    "why": r"Each step of fuel lowers the index, whatever its kind. The counterpart $e'\ \mathsf{at}\ \Theta'$ of the relation reads the cost of the step instead.",
    "breaks": "Nothing. It is a definition.",
    "example": r"F-Close reads $e'\ \mathsf{at}\ (\Phi \setminus o){\downarrow}\ !\ d \mathbin{\dot-} 1$.",
    "signature": r"e'\ \mathsf{at}\ \Phi'\ !\ d' \iff \forall \beta < \alpha.\ e' \in F^{N}_{\beta}\llbracket \Phi' \vdash \sigma\ !\ d' \rrbracket",
    "args": [{"name": "e'", "meaning": "the successor"}, {"name": r"\Phi'", "meaning": "the held ends after the step"}, {"name": "d'", "meaning": "the frame after the step"}],
    "source": [{"file": "fuel/Fuel.v", "names": ["Fobl"]}],
    "deviations": [{"kind": "notation", "reason": r"The Rocq repeats the premise in each obligation of `Fobl`, as `FuelE` at each lower level.", "names": ["Fobl"]}],
}
N['fu.head'] = {
    "title": r"Head of a held end $\Phi(o) \doteq H^{f,m}$",
    "meaning": r"$\Phi(o) \doteq H^{f,m}$ states $\Phi(o) = S^{f,m}$ for some protocol $S$ with $\mathsf{unfold}\,S = H$.",
    "why": r"An action reads the first action of the protocol of its end, as $\Theta(o) \doteq H_x$ does in the relation.",
    "breaks": "Nothing. It is a definition.",
    "example": r"$\Phi(o) \doteq \mathsf{Close}^{1,2}$ at $\Phi(o) = \mathsf{Close}^{1,2}$.",
    "signature": r"\Phi(o) \doteq H^{f,m} \iff \exists S.\ \Phi(o) = S^{f,m} \land \mathsf{unfold}\,S = H",
    "args": [{"name": r"\Phi", "meaning": "the held ends"}, {"name": "o", "meaning": "the subject end"}, {"name": "H", "meaning": "the head of the protocol"}],
    "source": [{"file": "fuel/Fuel.v", "names": ["f_send", "f_recv", "f_close", "f_select", "f_branch"]}],
}
n = note('sr.act')
n['meaning'] = r"$\mathsf{act}\,o$ is the shared premise of each action on $o$. The end is held and not idle, each other end that is not idle has a counter of at least $1$, and so has the frame."
n['why'] = r"Send, receive, close, select and branch share this premise, F-Wait and F-Count together."
n['example'] = r"$\mathsf{act}\,a$ holds at $\Phi = \{a \mapsto S^{0,2}, b \mapsto S'^{1,2}\}$ and $d = 1$."
n['signature'] = r"\mathsf{act}\,o \iff \Phi(o) = S^{f,m} \land \neg\mathsf{idle}\,S \land \mathsf{positive}(\Phi \setminus o) \land 1 \leq d"
n = note('F-Spawn.held')
n['title'] = r"$\Phi = \Phi_M \uplus \Phi_r$"
n['meaning'] = r"The child takes exactly the held ends of its thunk, $\mathrm{dom}\,\Phi_M = \mathsf{fends}(v)$, and the parent keeps $\Phi_r$."
n['example'] = r"$\Phi_M = \{d^{+} \mapsto S^{2,3}\}$."
n['signature'] = r"\Phi = \Phi_M \uplus \Phi_r,\ \mathrm{dom}\,\Phi_M = \mathsf{fends}(v)"
n['args'] = [{"name": r"\Phi_M", "meaning": "the ends of the thunk"}, {"name": r"\Phi_r", "meaning": "the ends the parent keeps"}]
n['source'] = [{"file": "fuel/Fuel.v", "names": ["f_spawn", "mres", "mrem"]}]
n = note('F-Spawn.child')
n['meaning'] = r"$v\,\ast \in F^N_\beta\llbracket\Phi_M \vdash \mathsf{thread}\ !\ \infty\rrbracket$ at each $\beta < \alpha$."
n['signature'] = r"\forall \beta < \alpha.\ v\,\ast \in F^{N}_{\beta}\llbracket \Phi_M \vdash \mathsf{thread}\ !\ \infty \rrbracket"
n = note('F-Send.notsubj')
n['title'] = r"$\Phi \setminus o = \Phi_M \uplus \Phi_r$"
n['meaning'] = r"A send gives away exactly the held ends of its payload, $\mathrm{dom}\,\Phi_M = \mathsf{fends}(w)$, other than its subject."
n['example'] = r"$\Phi_M = \{a \mapsto S^{1,2}\}$."
n['signature'] = r"\Phi \setminus o = \Phi_M \uplus \Phi_r,\ \mathrm{dom}\,\Phi_M = \mathsf{fends}(w)"
n['args'] = [{"name": r"\Phi_M", "meaning": "the transferred ends"}, {"name": "o", "meaning": r"the subject end, $o \in \sym{type.End}{\mathsf{End}}$"}]
n['source'] = [{"file": "fuel/Fuel.v", "names": ["f_send", "mres", "mrem"]}]
n = note('F-Send.payload')
n['meaning'] = r"$w \in FV^N_{\beta}\llbracket\Phi_M{\downarrow} \vdash T\rrbracket$ at each $\beta < \alpha$, with each transferred counter lowered by one."
n['signature'] = r"\forall \beta < \alpha.\ w \in FV^{N}_{\beta}\llbracket \Phi_M{\downarrow} \vdash T \rrbracket"
n = note('F-Recv.forall')
n['meaning'] = r"$\forall \beta < \alpha, \Phi_{in}.\ w \in FV^N_\beta\llbracket\Phi_{in} \vdash T\rrbracket$, for each value that may arrive with ends disjoint from $\Phi$."
n['signature'] = r"\forall \beta, \Phi_{in}.\ \beta < \alpha,\ \Phi_{in} \mathbin{\#} \Phi,\ w \in FV^{N}_{\beta}\llbracket \Phi_{in} \vdash T \rrbracket \Rightarrow \ldots"
n = note('F-Close')
n['title'] = "F-Close"
n['meaning'] = r"A close drops $o$, lowers the other counters and uses one unit of the frame."
n['why'] = r"It is the fuel form of O-Close, and it is an action, so F-Count applies."
n['signature'] = r"\mathsf{f\_close} : \sym{type.End}{\mathsf{End}} \to \sym{type.Expr}{\mathsf{Expr}} \to \mathsf{Prop}"
n['args'] = [{"name": "o", "meaning": r"the subject end, $o \in \sym{type.End}{\mathsf{End}}$"}]
n['source'] = [{"file": "fuel/Fuel.v", "names": ["f_close"]}]
for key, name, rn, sty in [('F-Select', 'select', 'f_select', r'\oplus'), ('F-Branch', 'branch', 'f_branch', r'\&')]:
    N[key] = {
        "title": key,
        "meaning": r"A " + name + r" on $o$ advances the protocol of $o$ to the chosen continuation, resets its counter to its tickets $m$, lowers the other counters and uses one unit of the frame.",
        "why": r"It is the fuel form of O-" + key[2:] + r", and it is an action, so F-Count applies.",
        "breaks": "Nothing. It is a definition.",
        "example": r"$\mathsf{" + name + r"}_{0}\,c^{+}$ at $\Phi(c^{+}) \doteq " + sty + r"(S', S'')^{1,2}$ continues at $S'^{2,2}$.",
        "signature": r"\mathsf{f\_" + name + r"} : \sym{type.End}{\mathsf{End}} \to \mathbb{B} \to \sym{type.Expr}{\mathsf{Expr}} \to \mathsf{Prop}",
        "args": [{"name": "o", "meaning": r"the subject end, $o \in \sym{type.End}{\mathsf{End}}$"}, {"name": "i", "meaning": "the choice"}],
        "source": [{"file": "fuel/Fuel.v", "names": [rn, "refill"]}],
    }
n = note('sr.fobl')
n['title'] = r"$\mathsf{Fobl}_\ell(e')$"
n['meaning'] = r"The fuel obligation of the step label $\ell$, one rule of [[fu-obls]] per label."
n['signature'] = r"\mathsf{Fobl} : \sym{type.TLabel}{\mathsf{TLabel}} \to \sym{type.Expr}{\mathsf{Expr}} \to \mathsf{Prop}"
n = note('fu.tick')
n['signature'] = r"\Phi{\downarrow} = \{o \mapsto S^{f \mathbin{\dot-} 1,\,m} \mid o \mapsto S^{f,m} \in \Phi\}"
n['source'] = [{"file": "fuel/Fuel.v", "names": ["ftick", "ctick"]}]
n = note('fu.Phi')
n['meaning'] = r"$\Phi$ maps each end the thread holds to its protocol $S$, a session type with annotations, its counter $f$ and its tickets $m$, written $o \mapsto S^{f,m}$."
n['args'] = [{"name": "S^{f,m}", "meaning": r"the protocol $S$, counter $f$ and tickets $m$ of an end"}]
n['deviations'].append({"kind": "simplified", "reason": r"Counters and tickets range over $\mathbb{N} \cup \{\infty\}$, the type `fuel`. The map writes $\mathbb{N}$, and the lock-free process relation keeps both finite by `sp_fin` and `sp_cap`.", "names": ["sp_fin", "sp_cap"]})

# "tickets m >= f" in argument texts: FuelE does not enforce it
cnt = 0
for k, v in N.items():
    for a in v.get('args', []):
        if 'and tickets $m \\geq f$' in a.get('meaning', ''):
            a['meaning'] = a['meaning'].replace('and tickets $m \\geq f$', 'and tickets $m$'); cnt += 1
print('m>=f fixed', cnt)

json.dump(m, open(P, 'w'), ensure_ascii=False, indent=1)
open(P, 'a').write('\n')
print('ok part 2')
