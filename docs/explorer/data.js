window.MAP = {
 "sections": [
  {
   "id": "syntax",
   "title": "Syntax",
   "intro": "This section introduces terms, values, primitives, channel ends, processes, and the points that types use to order ends. No term mentions a point. A channel has two named ends c⁺ and c⁻, and the only labels a program writes are family labels ℓ, field labels κ and branch indices.",
   "blocks": [
    {
     "id": "syn-terms",
     "title": "Terms",
     "rocq": "lang/Syntax.v: expr",
     "tex": "\\begin{array}{rl}\ne ::= & \\htmlData{k=syn.var}{x} \\mid \\htmlData{k=syn.unit}{\\ast} \\mid \\htmlData{k=syn.end}{o} \\mid \\htmlData{k=syn.lam}{\\lambda e} \\mid \\htmlData{k=syn.app}{e_1\\,e_2} \\mid \\htmlData{k=syn.pair}{\\langle e_1, e_2\\rangle} \\\\\n\\mid & \\htmlData{k=syn.letu}{\\mathsf{let}\\ \\ast = e_1\\ \\mathsf{in}\\ e_2} \\mid \\htmlData{k=syn.letp}{\\mathsf{let}\\ \\langle a,b\\rangle = e_1\\ \\mathsf{in}\\ e_2} \\\\\n\\mid & \\htmlData{k=syn.let}{\\mathsf{let}\\ a = e_1\\ \\mathsf{in}\\ e_2} \\mid \\htmlData{k=syn.inj}{\\mathsf{inj}_i\\,e} \\mid \\htmlData{k=syn.case}{\\mathsf{case}\\ e\\,(a.e_1)\\,(a.e_2)} \\\\\n\\mid & \\htmlData{k=syn.box}{!e} \\mid \\htmlData{k=syn.new}{\\mathsf{new}_\\ell} \\mid \\htmlData{k=syn.op}{k\\,e}\n\\end{array}",
     "caption": "Fourteen term formers. Variables are de Bruijn indices, written with names here. A box can refer to itself, a let binds one variable without making a closure, and every primitive k is applied to one argument.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "syn-prims",
     "title": "Saturated primitives",
     "rocq": "lang/Syntax.v: prim",
     "tex": "\\begin{array}{rl}\nk ::= & \\htmlData{k=prim.send}{\\mathsf{send}} \\mid \\htmlData{k=prim.recv}{\\mathsf{recv}} \\mid \\htmlData{k=prim.close}{\\mathsf{close}} \\mid \\htmlData{k=prim.select}{\\mathsf{select}_i} \\mid \\htmlData{k=prim.branch}{\\mathsf{branch}} \\\\\n\\mid & \\htmlData{k=prim.link}{\\mathsf{link}} \\mid \\htmlData{k=prim.spawn}{\\mathsf{spawn}} \\mid \\htmlData{k=prim.force}{\\mathsf{force}} \\mid \\htmlData{k=prim.newat}{\\mathsf{new}_\\kappa}\n\\end{array}",
     "caption": "The primitives k of a term k e. send takes a pair ⟨v, o⟩, link a pair of ends, spawn a thunk, new_κ an end.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "syn-values",
     "title": "Values",
     "rocq": "lang/Syntax.v: is_val",
     "tex": "\\htmlData{k=syn.values}{v ::= \\ast \\mid o \\mid \\lambda e \\mid\\ !e \\mid \\langle v_1, v_2\\rangle \\mid \\mathsf{inj}_i\\,v}",
     "caption": "A primitive alone is not a value. A value of arrow type is always a λ.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "syn-consts",
     "title": "Constants as λ-values",
     "rocq": "lang/Syntax.v: k_send, k_new, k_new_at",
     "tex": "\\htmlData{k=syn.consts}{\\begin{array}{l}\n\\mathsf{k\\_send} := \\lambda x.\\,\\mathsf{send}\\,x \\\\\n\\mathsf{k\\_new}_\\ell := \\lambda x.\\,\\mathsf{let}\\ \\ast = x\\ \\mathsf{in}\\ \\mathsf{new}_\\ell \\\\\n\\mathsf{k\\_new}_\\kappa := \\lambda x.\\,\\mathsf{new}_\\kappa\\,x\n\\end{array}}",
     "caption": "A function such as send, passed as an argument, is a λ over its primitive.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "syn-ends",
     "title": "Ends",
     "rocq": "lang/Syntax.v: cend, edual, ech",
     "tex": "\\htmlData{k=end.cend}{o ::= c^{+} \\mid c^{-}} \\qquad \\htmlData{k=end.dual}{\\overline{c^{+}} = c^{-}\\quad \\overline{c^{-}} = c^{+}} \\qquad \\htmlData{k=end.ech}{\\mathsf{ech}(c^{\\pm}) = c}",
     "caption": "An end names one side of a channel. Its name never depends on a point. ō is the partner end and ech o the channel.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "syn-fends",
     "title": "Ends a term mentions",
     "rocq": "lang/Syntax.v: fends, fchans",
     "tex": "\\htmlData{k=syn.fends}{\\mathsf{fends}(e)} \\qquad \\htmlData{k=syn.fchans}{\\mathsf{fchans}(e) = \\mathsf{ech}[\\mathsf{fends}(e)]}",
     "caption": "The syntactic set of ends in a term. Terms bind no channel.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "syn-procs",
     "title": "Processes and configurations",
     "rocq": "lang/Syntax.v: proc, lang/Process.v: config, erase",
     "tex": "\\begin{array}{l}\n\\htmlData{k=proc.proc}{p = (C, E)} \\qquad \\htmlData{k=proc.config}{q = (C, M),\\ M : \\mathbb{N} \\rightharpoonup e} \\\\\n\\htmlData{k=proc.erase}{\\mathsf{erase}(C, M) = (C, \\{\\!|\\, M(i) \\mid i \\,|\\!\\})}\n\\end{array}",
     "caption": "A process is a set C of restricted channels and a multiset E of threads. A configuration names its threads by identifiers.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "syn-points",
     "title": "Points",
     "rocq": "types/Points.v: pname, point",
     "tex": "\\begin{array}{l}\nr ::= \\htmlData{k=pt.const}{a} \\mid \\htmlData{k=pt.gen}{g_\\ell} \\mid \\htmlData{k=pt.var}{\\iota} \\qquad x ::= r \\mid \\htmlData{k=pt.shift}{x^{+}} \\mid \\htmlData{k=pt.field}{x\\cdot\\kappa} \\mid \\htmlData{k=pt.dual}{\\overline{x}} \\\\\n\\htmlData{k=pt.laws}{\\overline{\\overline{x}} = x \\quad \\overline{x}\\cdot\\kappa = x\\cdot\\kappa \\quad \\overline{x^{+}} = \\overline{x}^{+}}\n\\end{array}",
     "caption": "A point x marks where an end acts next. It has a root r, a polarity flipped by x̄, an offset raised by x⁺, and fields x·κ below it.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "syn-moves",
     "title": "Where an end moves",
     "rocq": "types/Points.v: sel_pt, bra_pt, payload_pts",
     "tex": "\\begin{array}{l}\n\\htmlData{k=pt.shift}{\\text{action at } x \\text{ moves to } x^{+}} \\qquad \\htmlData{k=sx.kappai}{\\kappa_{\\mathsf{false}} = 0,\\ \\kappa_{\\mathsf{true}} = 1} \\\\\n\\htmlData{k=pt.sel}{\\mathsf{sel\\_pt}\\,x\\,i = \\overline{x\\cdot\\kappa_i}} \\qquad \\htmlData{k=pt.bra}{\\mathsf{bra\\_pt}\\,x\\,i = x\\cdot\\kappa_i} \\qquad \\htmlData{k=pt.payload}{\\text{payload } j \\text{ at } x\\cdot j}\n\\end{array}",
     "caption": "An action moves an end from x to x⁺. Select and branch move to a field, and the ends a message carries sit at fields of the carrier point.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "syn-labels",
     "title": "Labels in programs and steps",
     "rocq": "lang/Syntax.v: family, field, lang/Semantics.v: ltransfer_ok",
     "tex": "\\htmlData{k=lbl.family}{\\ell \\in \\mathbb{N}} \\qquad \\htmlData{k=lbl.field}{\\kappa \\in \\mathbb{N}} \\qquad \\htmlData{k=lbl.transfer}{M = \\mathsf{fends}(v)}",
     "caption": "Family and field labels are plain numbers, like a branch index. The transfer set M of a send or spawn is the set of ends of the value that leaves.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "syn-csub",
     "title": "Link substitution",
     "rocq": "lang/Syntax.v: csub",
     "tex": "\\htmlData{k=link.csub}{\\mathsf{csub}\\,o_1\\,o_2 :\\ \\overline{o_1} \\mapsto o_2,\\quad o_1 \\mapsto \\overline{o_2},\\quad o \\mapsto o\\ \\text{otherwise}}",
     "caption": "The renaming a link applies to every thread. The holder of the partner of o₁ ends up holding o₂.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    }
   ]
  },
  {
   "id": "semantics",
   "title": "Semantics",
   "intro": "Thread steps carry labels that say what the relation reads. Process steps carry events that name the threads involved. A send and a spawn carry the transfer set of their value.",
   "blocks": [
    {
     "id": "sem-labels",
     "title": "Thread labels",
     "rocq": "lang/Semantics.v: tlabel, slabel",
     "tex": "\\alpha ::= \\htmlData{k=lbl.beta}{\\beta} \\mid \\htmlData{k=lbl.new}{\\mathsf{new}_\\ell\\,c} \\mid \\htmlData{k=lbl.newat}{\\mathsf{new}_\\kappa\\,o\\,c} \\mid \\htmlData{k=lbl.spawn}{\\mathsf{spawn}_{\\htmlData{k=lbl.transfer}{M}}\\,v} \\mid \\sigma \\qquad \\sigma ::= \\htmlData{k=lbl.send}{o!_{M}v} \\mid \\htmlData{k=lbl.recv}{o?v} \\mid \\htmlData{k=lbl.close}{o\\,\\mathsf{end}} \\mid \\htmlData{k=lbl.sel}{o \\lhd i} \\mid \\htmlData{k=lbl.bra}{o \\rhd i} \\mid \\htmlData{k=lbl.link}{\\leftrightarrow\\{o_1,o_2\\}}",
     "caption": "β covers application, let, case and force. Session labels σ are offers on ends.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "sem-head",
     "title": "Head steps (T-Act rules)",
     "rocq": "lang/Semantics.v: head_step",
     "tex": "\\begin{array}{ll}\n\\htmlData{k=T-Act-App}{(\\lambda e)\\,v \\xrightarrow{\\beta} e[v]} & \\htmlData{k=T-Act-Let}{\\mathsf{let}\\ a = v\\ \\mathsf{in}\\ e \\xrightarrow{\\beta} e[v]} \\\\\n\\htmlData{k=T-Act-Force}{\\mathsf{force}\\,(!e) \\xrightarrow{\\beta} e[!e]} & \\htmlData{k=T-Act-New}{\\mathsf{new}_\\ell \\xrightarrow{\\mathsf{new}_\\ell\\,c} \\langle c^{+}, c^{-}\\rangle} \\\\\n\\htmlData{k=T-Act-NewAt}{\\mathsf{new}_\\kappa\\,o \\xrightarrow{\\mathsf{new}_\\kappa\\,o\\,c} \\langle o, \\langle c^{+}, c^{-}\\rangle\\rangle} & \\htmlData{k=T-Act-Spawn}{\\mathsf{spawn}\\,v \\xrightarrow{\\mathsf{spawn}_{\\mathsf{fends}(v)}\\,v} \\ast} \\\\\n\\htmlData{k=T-Act-Send}{\\mathsf{send}\\,\\langle v, o\\rangle \\xrightarrow{o!_{\\mathsf{fends}(v)}v} o} & \\htmlData{k=T-Act-Recv}{\\mathsf{recv}\\,o \\xrightarrow{o?v} \\langle v, o\\rangle} \\\\\n\\htmlData{k=T-Act-Close}{\\mathsf{close}\\,o \\xrightarrow{o\\,\\mathsf{end}} \\ast} & \\htmlData{k=T-Act-Select}{\\mathsf{select}_i\\,o \\xrightarrow{o\\lhd i} o} \\\\\n\\htmlData{k=T-Act-Branch}{\\mathsf{branch}\\,o \\xrightarrow{o\\rhd i} \\mathsf{inj}_i\\,o} & \\htmlData{k=T-Act-Link}{\\mathsf{link}\\,\\langle o_1, o_2\\rangle \\xrightarrow{\\leftrightarrow\\{o_1,o_2\\}} \\ast}\n\\end{array}",
     "caption": "One head rule per redex. Select and branch keep their end, and a receive takes any value.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "sem-ctx",
     "title": "Evaluation frames (T-Act-Ctx)",
     "rocq": "lang/Semantics.v: tstep, frame_val",
     "tex": "\\dfrac{\\htmlData{k=T-Act-Ctx}{e \\xrightarrow{\\alpha} e'}\\quad \\htmlData{k=sem.frameval}{\\mathsf{frame\\_val}\\,f}}{f[e] \\xrightarrow{\\alpha} f[e']}\\;\\textsf{T-Act-Ctx}",
     "caption": "One frame at a time, never under λ or a box. A right frame waits for a value on its left.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "sem-proc",
     "title": "Process steps (P-Act rules)",
     "rocq": "lang/Process.v: istep",
     "tex": "\\begin{array}{l}\n\\htmlData{k=P-Act-Beta}{M(i) \\xrightarrow{\\beta} e' \\;\\Rightarrow\\; (C, M) \\xrightarrow{\\beta_i} (C, M[i \\mapsto e'])} \\\\\n\\htmlData{k=P-Act-New}{M(i) \\xrightarrow{\\mathsf{new}\\,c} e',\\ \\htmlData{k=sem.fresh-global}{c \\notin C \\cup \\mathsf{echans}(M)} \\;\\Rightarrow\\; (C \\cup \\{c\\}, M[i\\mapsto e'])} \\\\\n\\htmlData{k=P-Act-Spawn}{M(i) \\xrightarrow{\\mathsf{spawn}_M v} e',\\ j \\notin \\mathsf{dom}\\,M \\;\\Rightarrow\\; (C, M[i\\mapsto e'][j \\mapsto v\\,\\ast])} \\\\\n\\htmlData{k=P-Act-Msg}{M(i) \\xrightarrow{o!_M v} e',\\ M(j) \\xrightarrow{\\overline{o}?v} f',\\ i \\neq j \\;\\Rightarrow\\; (C, M[i\\mapsto e'][j\\mapsto f'])} \\\\\n\\htmlData{k=P-Act-Close}{M(i) \\xrightarrow{o\\,\\mathsf{end}} e',\\ M(j) \\xrightarrow{\\overline{o}\\,\\mathsf{end}} f',\\ \\mathsf{ech}\\,o \\in C \\;\\Rightarrow\\; (C \\setminus \\{\\mathsf{ech}\\,o\\}, \\ldots)} \\\\\n\\htmlData{k=P-Act-Choice}{M(i) \\xrightarrow{o\\lhd b} e',\\ M(j) \\xrightarrow{\\overline{o}\\rhd b} f' \\;\\Rightarrow\\; (C, M[i\\mapsto e'][j\\mapsto f'])} \\\\\n\\htmlData{k=P-Act-Link}{M(i) \\xrightarrow{\\leftrightarrow\\{o_1,o_2\\}} e',\\ \\mathsf{ech}\\,o_1 \\in C \\;\\Rightarrow\\; (C\\setminus\\{\\mathsf{ech}\\,o_1\\}, \\htmlData{k=link.csub}{\\mathsf{csub}\\,o_1\\,o_2} \\langle\\$\\rangle\\, M[i\\mapsto e'])} \\\\\n\\htmlData{k=P-Act-Session}{M(i) \\xrightarrow{\\sigma} e',\\ \\mathsf{subj}\\,\\sigma \\cap C = \\varnothing \\;\\Rightarrow\\; (C \\setminus \\htmlData{k=sem.sentc}{\\mathsf{sentc}\\,\\sigma}, M[i\\mapsto e'])}\n\\end{array}",
     "caption": "The only definition of process steps. A message may use a free channel, a close and a link need a restricted one, and an external offer extrudes its transfer set.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "sem-events",
     "title": "Events",
     "rocq": "lang/Process.v: event, ev_parts, ev_admin, ev_tau",
     "tex": "\\htmlData{k=ev.event}{ev ::= \\beta_i \\mid \\mathsf{new}_i\\,\\ell\\,c \\mid \\mathsf{newat}_i\\,\\kappa\\,o\\,c \\mid \\mathsf{spawn}_{i,j}\\,M \\mid \\mathsf{msg}_{i,j}\\,o\\,M \\mid \\mathsf{close}_{i,j}\\,o \\mid \\mathsf{choice}_{i,j}\\,o\\,b \\mid \\mathsf{link}_i\\,o_1\\,o_2 \\mid \\mathsf{sess}_i\\,\\sigma} \\qquad \\htmlData{k=ev.admin}{\\mathsf{admin} = \\{\\beta, \\mathsf{new}, \\mathsf{newat}, \\mathsf{spawn}, \\mathsf{link}\\}} \\qquad \\htmlData{k=ev.tau}{\\tau = \\text{all but } \\mathsf{sess}}",
     "caption": "An event names the participating threads and carries the creation label, the transfer set or the ends acted on.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "sem-props",
     "title": "Safety properties",
     "rocq": "lang/Safety.v: deadlock_free, lockfree/TauThread.v: no_tau_divergence, lockfree/Fair.v: lock_free",
     "tex": "\\begin{array}{l}\n\\htmlData{k=prop.terminated}{\\mathsf{terminated}\\,p \\iff p = (\\varnothing, \\{v\\} \\uplus E),\\ E \\subseteq \\{\\ast\\}} \\\\\n\\htmlData{k=prop.df}{\\mathsf{deadlock\\_free}\\,p \\iff \\forall p'.\\ p \\to^{*} p' \\Rightarrow \\mathsf{terminated}\\,p' \\lor \\exists p''.\\ p' \\to p''} \\\\\n\\htmlData{k=prop.notau}{\\mathsf{no\\_tau\\_divergence}\\,p \\iff \\forall q.\\ p \\to^{*} q \\Rightarrow \\mathsf{Acc}\\ \\htmlData{k=prop.padmin}{\\to_{\\mathsf{admin}}}\\ q} \\\\\n\\htmlData{k=prop.lf}{\\mathsf{lock\\_free}\\,p \\iff \\forall r\\,l.\\ \\mathsf{erase}(r_0) = p \\Rightarrow \\htmlData{k=prop.maximal}{\\mathsf{maximal}\\,r\\,l} \\Rightarrow \\htmlData{k=prop.wfair}{\\mathsf{wfair}\\,r\\,l} \\Rightarrow \\htmlData{k=prop.lfrun}{\\forall i\\,t.\\ \\htmlData{k=prop.pend}{\\mathsf{pend}(r_i, t)} \\Rightarrow \\exists j \\geq i.\\ t \\in \\mathsf{parts}(l_j)}}\n\\end{array}",
     "caption": "Deadlock freedom, absence of internal divergence, and lock freedom over weakly fair maximal runs.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    }
   ]
  },
  {
   "id": "types",
   "title": "Types and worlds",
   "intro": "Types carry points and, under the merged judgment of Q11, cost annotations. The relations of deadlock freedom and liveness read no annotation. A world orders points and holds nothing else.",
   "blocks": [
    {
     "id": "ty-grammar",
     "title": "Types",
     "rocq": "types/Types.v: ty",
     "tex": "T, U ::= \\htmlData{k=ty.unit}{\\ast} \\mid \\htmlData{k=ty.arrow}{T^{a} \\multimap^{\\htmlData{k=ty.arrow.ub}{u}}_{\\htmlData{k=ty.arrow.lb}{l}}[\\htmlData{k=ty.arrow.cost}{c} ; \\htmlData{k=ty.arrow.tix}{\\vartheta} ; \\htmlData{k=ty.arrow.floor}{h}]\\, U^{b}} \\mid \\htmlData{k=ty.prod}{T^{a} \\otimes U^{b}} \\mid \\htmlData{k=ty.sum}{T^{a} \\oplus U^{b}} \\mid \\htmlData{k=ty.sess}{S@x} \\mid \\htmlData{k=ty.box}{\\Box(\\forall \\htmlData{k=pt.var}{\\bar\\iota}\\, \\htmlData{k=ty.box.svars}{\\bar\\alpha}.\\ \\htmlData{k=ty.box.constraint}{C}.\\ \\ast \\multimap^{u}[c ; \\vartheta]\\, U^{b})} \\mid \\htmlData{k=ty.ex}{\\exists^{\\htmlData{k=ty.ex.lb}{l}} \\bar\\iota.\\ C.\\ T^{a}}",
     "variants": {
      "df": "T, U ::= \\htmlData{k=ty.unit}{\\ast} \\mid \\htmlData{k=ty.arrow}{T \\multimap^{\\htmlData{k=ty.arrow.ub}{u}}_{\\htmlData{k=ty.arrow.lb}{l}} U} \\mid \\htmlData{k=ty.prod}{T \\otimes U} \\mid \\htmlData{k=ty.sum}{T \\oplus U} \\mid \\htmlData{k=ty.sess}{S@x} \\mid \\htmlData{k=ty.box}{\\Box(\\forall \\bar\\iota\\, \\htmlData{k=ty.box.svars}{\\bar\\alpha}.\\ \\htmlData{k=ty.box.constraint}{C}.\\ \\ast \\multimap^{u} U)} \\mid \\htmlData{k=ty.ex}{\\exists^{\\htmlData{k=ty.ex.lb}{l}} \\bar\\iota.\\ C.\\ T}",
      "live": "T, U ::= \\htmlData{k=ty.unit}{\\ast} \\mid \\htmlData{k=ty.arrow}{T \\multimap^{\\htmlData{k=ty.arrow.ub}{u}}_{\\htmlData{k=ty.arrow.lb}{l}} U} \\mid \\htmlData{k=ty.prod}{T \\otimes U} \\mid \\htmlData{k=ty.sum}{T \\oplus U} \\mid \\htmlData{k=ty.sess}{S@x} \\mid \\htmlData{k=ty.box}{\\Box(\\forall \\bar\\iota\\, \\htmlData{k=ty.box.svars}{\\bar\\alpha}.\\ \\htmlData{k=ty.box.constraint}{C}.\\ \\ast \\multimap^{u} U)} \\mid \\htmlData{k=ty.ex}{\\exists^{\\htmlData{k=ty.ex.lb}{l}} \\bar\\iota.\\ C.\\ T}"
     },
     "caption": "Superscripts a, b are credits. DF and live read the same types with every annotation erased (ty_df).",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "ty-credit",
     "title": "Credits",
     "rocq": "types/Costs.v: fuel",
     "modes": [
      "lf"
     ],
     "tex": "\\htmlData{k=ty.credit}{T^{a},\\ a \\in \\mathbb{N} \\cup \\{\\infty\\}} \\qquad \\htmlData{k=ty.credit-agg}{(T^{a_1} \\otimes U^{a_2})^{a} \\text{ gives } a + a_1,\\ a + a_2}",
     "caption": "A credit is a lower bound on the counters of the ends a value holds. The credit of an aggregate adds to its parts."
    },
    {
     "id": "ty-session",
     "title": "Session types",
     "rocq": "types/Types.v: sty, unfoldS",
     "tex": "S ::= \\htmlData{k=sty.skip}{\\mathsf{Skip}} \\mid \\htmlData{k=sty.seq}{S ; S} \\mid \\htmlData{k=sty.recv}{?(\\exists^{m}\\bar\\iota.\\ T^{\\htmlData{k=sty.payload-credit}{b}})} \\mid \\htmlData{k=sty.send}{!(\\exists^{m}\\bar\\iota.\\ T^{b})} \\mid \\htmlData{k=sty.plus}{\\oplus(S_1, S_2)} \\mid \\htmlData{k=sty.with}{\\&(S_1, S_2)} \\mid \\htmlData{k=sty.close}{\\mathsf{Close}} \\mid \\htmlData{k=sty.mu}{\\mu\\alpha.S} \\mid \\htmlData{k=sty.var}{\\alpha} \\mid \\htmlData{k=sty.vard}{\\overline{\\alpha}} \\qquad \\htmlData{k=sty.unfold}{\\mathsf{unfold}(S)}",
     "caption": "Context-free session types, read through their head normal form. A payload binds m point variables that land on the payload fields of the carrier.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "ty-dual",
     "title": "Duality",
     "rocq": "types/Types.v: dual, sflip",
     "tex": "\\htmlData{k=sty.dual}{\\mathsf{dual}(!P) = ?P \\quad \\mathsf{dual}(?P) = !P \\quad \\mathsf{dual}(\\oplus(S_1,S_2)) = \\&(\\mathsf{dual}\\,S_1,\\mathsf{dual}\\,S_2) \\quad \\mathsf{dual}(S_1;S_2) = \\mathsf{dual}\\,S_1;\\mathsf{dual}\\,S_2 \\quad \\mathsf{dual}(\\alpha) = \\overline{\\alpha} \\quad \\mathsf{dual}(\\mu\\alpha.S) = \\mu\\alpha.\\,\\htmlData{k=sty.flip}{\\mathsf{flip}_\\alpha}(\\mathsf{dual}\\,S)}",
     "caption": "Polarized duality. Payloads stay unchanged, Skip and Close are self-dual.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "ty-equiv",
     "title": "Session equivalence",
     "rocq": "types/Types.v: sequiv, relation/Relation.v: seqv, sdual",
     "tex": "\\htmlData{k=sty.sequiv}{S \\simeq S'} \\qquad \\htmlData{k=sty.seqv}{S \\approx S' \\iff \\mathsf{sty\\_df}(S) \\simeq \\mathsf{sty\\_df}(S')} \\qquad \\htmlData{k=sty.sdual}{\\mathsf{sdual}\\,S\\,S' \\iff S' \\approx \\overline{S}}",
     "caption": "Bisimilarity of head normal forms, and the same up to annotations, which is what the relation compares.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "ty-heads",
     "title": "Heads, ⊥ flag, lower bounds",
     "rocq": "types/Types.v: heads, hbot, types/Points.v: lbound",
     "tex": "\\htmlData{k=ty.heads}{\\mathsf{heads}(S@x) = \\{\\overline{x}\\} \\quad \\mathsf{heads}(T \\multimap_{l} U) = \\{l\\} \\quad \\mathsf{heads}(\\exists^{l}) = \\{l\\} \\quad \\mathsf{heads}(\\Box\\ldots) = \\varnothing} \\qquad \\htmlData{k=ty.hbot}{\\mathsf{hbot}(T)} \\qquad \\htmlData{k=ty.lbound}{l ::= \\cdot \\mid \\bot \\mid x}",
     "caption": "The heads of a type are the partner points a thread holding a value of it owes readiness facts against.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "ty-payload",
     "title": "Payloads",
     "rocq": "types/Types.v: payload_at, pscoped",
     "tex": "\\htmlData{k=ty.payload-at}{\\mathsf{payload\\_at}\\,m\\,T\\,x = T[x\\cdot 0, \\ldots, x\\cdot(m{-}1) / \\iota_0, \\ldots, \\iota_{m-1}]} \\qquad \\htmlData{k=ty.pscoped}{\\mathsf{pscoped}\\,m\\,T}",
     "caption": "A payload is point-closed below its own binder and is placed at the fields of the carrier point.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "ty-annot",
     "title": "Costs and ticket transformers",
     "rocq": "types/Costs.v: tix, meets, tspawn, tlink, tseq, tok",
     "modes": [
      "lf"
     ],
     "tex": "\\begin{array}{l}\n\\htmlData{k=ann.fuel}{a, c, h \\in \\mathbb{N}\\cup\\{\\infty\\}} \\qquad \\htmlData{k=ann.tix}{\\vartheta = (s, b) : r \\mapsto 2^{s} r + b} \\qquad \\htmlData{k=ann.tid}{\\hat 1 = (0, 0)} \\qquad \\htmlData{k=ann.meets}{\\mathsf{meets}\\,\\vartheta\\,r\\,tk \\iff \\vartheta(r) \\leq tk} \\\\\n\\htmlData{k=ann.tspawn}{\\mathsf{tspawn}\\,b_c\\,\\vartheta = (s{+}1, \\max(2b, 2b_c{-}1))} \\qquad \\htmlData{k=ann.tlink}{\\mathsf{tlink}\\,\\vartheta = (s, b{+}1)} \\qquad \\htmlData{k=ann.tseq}{\\vartheta_1 \\circ \\vartheta_2} \\qquad \\htmlData{k=ann.tok}{\\mathsf{tok}\\,\\vartheta_1\\,\\vartheta_2 \\iff b_2 = 0 \\lor s_1 \\neq \\infty \\lor b_1 = \\infty}\n\\end{array}",
     "caption": "A transformer says how many link tickets a term needs given the reserve r it must still hold when it returns."
    },
    {
     "id": "ty-df",
     "title": "Annotations of N = ∞",
     "rocq": "types/Types.v: ty_df, cr_df",
     "tex": "\\htmlData{k=ann.tydf}{\\mathsf{ty\\_df}(T):\\ \\text{credits } \\infty\\ (0 \\text{ on } \\otimes, \\oplus, \\exists),\\ \\text{costs } \\infty,\\ \\vartheta = (\\infty,\\infty),\\ \\text{floors } \\infty}",
     "caption": "The deadlock-freedom instance of every annotation.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "ty-kinds",
     "title": "Kinds of types",
     "rocq": "types/Types.v: prim, unlimited, tfree",
     "tex": "\\htmlData{k=ty.prim}{\\mathsf{prim}\\,T ::= \\ast \\mid \\mathsf{prim} \\otimes \\mathsf{prim} \\mid \\mathsf{prim} \\oplus \\mathsf{prim} \\mid \\Box(\\ldots \\mathsf{prim})} \\qquad \\htmlData{k=ty.unlimited}{\\mathsf{unlimited}\\,T \\iff T = \\Box\\ldots} \\qquad \\htmlData{k=ty.tfree}{\\mathsf{tfree}\\,T}",
     "caption": "prim is the shape of a process result, unlimited the types that admit weakening and contraction, tfree the types that hold no end.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "w-world",
     "title": "Worlds",
     "rocq": "types/Worlds.v: world",
     "tex": "\\htmlData{k=w.world}{W = (\\htmlData{k=w.consts}{A}, \\htmlData{k=w.facts}{\\prec_A}, \\htmlData{k=w.fams}{L}, \\htmlData{k=w.laws}{(\\Lambda_\\ell)_{\\ell \\in L}})}",
     "caption": "Constants, facts between constant points, family labels and the laws of each family over one root variable.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "w-order",
     "title": "The order ≺_W",
     "rocq": "types/Worlds.v: wstep, w_lt",
     "tex": "\\htmlData{k=w.lt}{\\prec_W\\ =\\ \\mathsf{tc}\\big(\\htmlData{k=w.ws-fact}{\\prec_A} \\;\\cup\\; \\htmlData{k=w.ws-law}{\\textstyle\\bigcup_{\\ell \\in L,\\, g} \\Lambda_\\ell(g_\\ell)} \\;\\cup\\; \\htmlData{k=w.ws-po}{\\{x \\prec x^{+}\\}} \\;\\cup\\; \\htmlData{k=w.ws-dpo}{\\{x \\prec \\overline{x}^{+}\\}}\\big)}",
     "caption": "The laws hold at every generated root of their family, so W is constant along a run that creates roots.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "w-wf",
     "title": "Well-formed, strict and lock-free worlds",
     "rocq": "types/Worlds.v: world_wf, strict, lfworld",
     "tex": "\\htmlData{k=w.wf}{\\mathsf{world\\_wf}\\,W} \\qquad \\htmlData{k=w.strict}{\\mathsf{strict}\\,W \\iff \\mathsf{world\\_wf}\\,W \\land \\forall x.\\ W \\nvdash x \\prec x} \\qquad \\htmlData{k=w.lfworld}{\\mathsf{lfworld}\\,W \\iff \\mathsf{strict}\\,W \\land \\mathsf{well\\_founded}(\\prec_W)}",
     "caption": "Deadlock freedom needs an irreflexive order. Lock freedom also needs no infinite descending chain.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "w-ext",
     "title": "Extension, join, restriction",
     "rocq": "types/Worlds.v: wext, wjoin, wrestrict, strict_join_iff",
     "tex": "\\htmlData{k=w.ext}{W \\sqsubseteq W'} \\qquad \\htmlData{k=w.join}{W_1 \\sqcup W_2} \\qquad \\htmlData{k=w.R7}{\\mathsf{strict}(W_1 \\sqcup W_2) \\iff \\mathsf{strict}\\,W_1 \\land \\mathsf{strict}\\,W_2 \\land \\mathsf{strict}(\\htmlData{k=w.restrict}{W_1|_S} \\sqcup W_2|_S),\\ S = A_1 \\cap A_2}",
     "caption": "Kripke extension, the union of two worlds, and the R7 characterization of a strict join by the shared constants.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    }
   ]
  },
  {
   "id": "typing",
   "title": "Typing",
   "intro": "This section introduces the typing judgment, its contexts Θ, Γ, Δ and the future F, the side conditions on points, aging and capture of credits, subtyping, one rule per term former, the process rules P-Term and P-Connect, and the guard. One judgment types sessions and costs at once. Deadlock-free and live typing are its instance N = ∞ with every annotation erased, live typing adds the guard, and lock-free typing uses a finite N.",
   "blocks": [
    {
     "id": "t-judgment",
     "title": "The merged judgment",
     "rocq": "static/Typing.v: typed, dftyped",
     "tex": "\\htmlData{k=tj.Theta}{\\Theta} ; \\htmlData{k=tj.Gamma}{\\Gamma} ; \\htmlData{k=tj.Delta}{\\Delta} \\vdash^{\\htmlData{k=tj.F}{F}}_{\\htmlData{k=tj.W}{W},\\htmlData{k=tj.N}{N}} e : T^{\\htmlData{k=ty.credit}{a}} \\triangleright \\htmlData{k=tj.cost}{c} ; \\htmlData{k=tj.tix}{\\vartheta}",
     "variants": {
      "df": "\\htmlData{k=tj.Theta}{\\Theta} ; \\htmlData{k=tj.Gamma}{\\Gamma} ; \\htmlData{k=tj.Delta}{\\Delta} \\vdash^{\\htmlData{k=tj.F}{F}}_{\\htmlData{k=tj.W}{W}} t : T",
      "live": "\\htmlData{k=tj.Theta}{\\Theta} ; \\htmlData{k=tj.Gamma}{\\Gamma} ; \\htmlData{k=tj.Delta}{\\Delta} \\vdash^{\\htmlData{k=tj.F}{F}}_{\\htmlData{k=tj.W}{W}} t : T \\quad\\text{and}\\quad \\htmlData{k=guard.judg}{\\varnothing \\vdash\\!\\triangleright t}"
     },
     "caption": "Θ holds ends, Γ facts and future hypotheses, Δ variables, F the future. N is the refill, c the cost and ϑ the transformer.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "t-contexts",
     "title": "Contexts and the fact theory",
     "rocq": "static/Contexts.v: tentry, tsplit, lenv_split, hctx, fl, sfuture",
     "tex": "\\begin{array}{l}\\htmlData{k=tj.Theta}{\\Theta : o \\mapsto S@x^{a}} \\qquad \\htmlData{k=ctx.tsplit}{\\Theta = \\Theta_1 \\uplus \\Theta_2} \\qquad \\htmlData{k=ctx.lsplit}{\\Delta = \\Delta_1 \\sqcup \\Delta_2} \\\\ \\htmlData{k=tj.Gamma}{\\Gamma = (\\htmlData{k=ctx.hyps}{(C, \\bar x)^{*}}, \\htmlData{k=ctx.fvar}{\\varphi \\mapsto u})} \\qquad \\htmlData{k=ctx.slt}{\\Gamma \\vdash x \\prec y} \\\\ \\htmlData{k=tj.F}{F = (X, \\htmlData{k=ctx.fvarF}{\\varphi} \\mid \\htmlData{k=ctx.bot}{\\bot})}\\end{array}",
     "caption": "Every fact a rule reads comes from Γ ⊢ x ≺ y, the least transitive relation over ≺_W, the instantiated box constraints and u ≺ φ.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "t-side",
     "title": "Side conditions on points",
     "rocq": "static/Contexts.v: ub_below_s, lb_below_hb, lbx_below_h, hold_at",
     "tex": "\\begin{array}{l}\\htmlData{k=side.ub}{u \\prec F \\iff \\forall y \\in X.\\ \\Gamma \\vdash u \\prec y,\\ \\Gamma \\vdash u \\prec \\varphi,\\ \\neg\\bot} \\\\ \\htmlData{k=side.lb}{l \\preccurlyeq H \\text{ and } \\neg\\bot} \\qquad \\htmlData{k=side.hold}{\\Gamma \\vdash C[\\bar x]}\\end{array}",
     "caption": "u ≺ F bounds the future from below, l ≼ H bounds heads from below, and C[x̄] states a constraint at an instance.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "t-age",
     "title": "Aging Γ − c",
     "rocq": "static/Contexts.v: tage, lage, thage",
     "modes": [
      "lf"
     ],
     "tex": "\\begin{array}{c}\\dfrac{\\begin{array}{c}\\htmlData{k=age.free}{\\htmlData{k=ty.tfree}{\\mathsf{tfree}}\\,T}\\end{array}}{(T, a) - c = (T, a)}\\;\\textsf{Age-Free} \\qquad \\dfrac{\\begin{array}{c}\\htmlData{k=age.credit}{c \\leq a}\\end{array}}{(T, a) - c = (T, a - c)}\\;\\textsf{Age-Credit} \\\\[2ex] \\dfrac{\\begin{array}{c}\\htmlData{k=age.agg}{(T_i, a + a_i) - c = (T_i', a_i')}\\end{array}}{(T_1^{a_1} \\otimes T_2^{a_2}, a) - c = (T_1'^{a_1'} \\otimes T_2'^{a_2'}, 0)}\\;\\textsf{Age-Agg}\\end{array}",
     "caption": "Every entry that holds an end must cover the cost of what runs while it is held, and loses it."
    },
    {
     "id": "t-cap",
     "title": "Capture at E-Abs",
     "rocq": "static/Contexts.v: tcap, thcap",
     "modes": [
      "lf"
     ],
     "tex": "\\begin{array}{c}\\dfrac{\\begin{array}{c}\\htmlData{k=cap.sess}{h + a \\leq a_0}\\end{array}}{(S@x, a_0) \\leadsto_{h,a} (S@x, h)}\\;\\textsf{Cap-Sess} \\\\[2ex] \\dfrac{\\begin{array}{c}\\htmlData{k=cap.arr}{h_0 \\leq h \\quad h + a \\leq h_0 + a_0}\\end{array}}{(T \\multimap[\\ldots;h_0] U, a_0) \\leadsto_{h,a} (\\ldots, h - h_0)}\\;\\textsf{Cap-Arr}\\end{array}",
     "caption": "A captured end must have credit at least h + a, and the body sees it at exactly the floor h."
    },
    {
     "id": "t-sub",
     "title": "Subtyping",
     "rocq": "static/Contexts.v: tsub",
     "tex": "\\htmlData{k=sub.tsub}{\\begin{array}{l} T^{a} \\leq T'^{a'}:\\ a' \\leq a,\\ c \\leq c',\\ \\vartheta \\leq \\vartheta',\\ h \\leq h',\\ h' + a' \\leq h + a, \\\\ \\quad \\text{argument contra, result co},\\ S \\simeq S',\\ \\exists \\text{ may drop facts}\\end{array}}",
     "variants": {
      "df": "\\htmlData{k=sub.dconv}{\\mathsf{D\\text{-}Conv}:\\ \\mathsf{ty\\_df}\\,T \\leq \\mathsf{ty\\_df}\\,T'}",
      "live": "\\htmlData{k=sub.dconv}{\\mathsf{D\\text{-}Conv}:\\ \\mathsf{ty\\_df}\\,T \\leq \\mathsf{ty\\_df}\\,T'}"
     },
     "caption": "Credits may fall, costs and transformers may rise, and an existential may forget facts of its constraint.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "r-unit",
     "title": "E-Unit",
     "rocq": "static/Typing.v: e_unit",
     "tex": "\\dfrac{\\begin{array}{c}\\htmlData{k=ctx.empty}{\\Delta\\ \\text{empty}}\\end{array}}{\\varnothing ; \\Gamma ; \\Delta \\vdash^{F}_{W,N} \\ast : \\ast^{\\infty} \\triangleright 0 ; \\hat 1}\\;\\textsf{E-Unit}",
     "variants": {
      "df": "\\dfrac{\\begin{array}{c}\\htmlData{k=ctx.empty}{\\Delta\\ \\text{empty}}\\end{array}}{\\varnothing ; \\Gamma ; \\Delta \\vdash^{F}_{W} \\ast : \\ast}\\;\\textsf{D-Unit}",
      "live": "\\dfrac{\\begin{array}{c}\\htmlData{k=ctx.empty}{\\Delta\\ \\text{empty}}\\end{array}}{\\varnothing ; \\Gamma ; \\Delta \\vdash^{F}_{W} \\ast : \\ast}\\;\\textsf{D-Unit}"
     },
     "caption": "Unit holds no end and costs nothing.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "r-var",
     "title": "E-Var",
     "rocq": "static/Typing.v: e_var",
     "tex": "\\dfrac{\\begin{array}{c}\\htmlData{k=ctx.only}{\\Delta = \\{x : T^{a}\\}}\\end{array}}{\\varnothing ; \\Gamma ; \\Delta \\vdash^{F}_{W,N} x : T^{a} \\triangleright 0 ; \\hat 1}\\;\\textsf{E-Var}",
     "variants": {
      "df": "\\dfrac{\\begin{array}{c}\\htmlData{k=ctx.only}{\\Delta = \\{x : T\\}}\\end{array}}{\\varnothing ; \\Gamma ; \\Delta \\vdash^{F}_{W} x : T}\\;\\textsf{D-Var}",
      "live": "\\dfrac{\\begin{array}{c}\\htmlData{k=ctx.only}{\\Delta = \\{x : T\\}}\\end{array}}{\\varnothing ; \\Gamma ; \\Delta \\vdash^{F}_{W} x : T}\\;\\textsf{D-Var}"
     },
     "caption": "A variable is used exactly once. Unlimited entries drop by E-Weak.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "r-chan",
     "title": "E-Chan",
     "rocq": "static/Typing.v: e_chan",
     "tex": "\\dfrac{\\begin{array}{c}\\htmlData{k=ctx.empty}{\\Delta\\ \\text{empty}}\\end{array}}{\\{o : S@x^{a}\\} ; \\Gamma ; \\Delta \\vdash^{F}_{W,N} o : (S@x)^{a} \\triangleright 0 ; \\hat 1}\\;\\textsf{E-Chan}",
     "variants": {
      "df": "\\dfrac{\\begin{array}{c}\\htmlData{k=ctx.empty}{\\Delta\\ \\text{empty}}\\end{array}}{\\{o : S@x\\} ; \\Gamma ; \\Delta \\vdash^{F}_{W} o : S@x}\\;\\textsf{D-Chan}",
      "live": "\\dfrac{\\begin{array}{c}\\htmlData{k=ctx.empty}{\\Delta\\ \\text{empty}}\\end{array}}{\\{o : S@x\\} ; \\Gamma ; \\Delta \\vdash^{F}_{W} o : S@x}\\;\\textsf{D-Chan}"
     },
     "caption": "An end value holds exactly its own entry of Θ.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "r-abs",
     "title": "E-Abs",
     "rocq": "static/Typing.v: e_abs",
     "tex": "\\dfrac{\\begin{array}{c}\\htmlData{k=E-Abs.phi}{\\varphi\\ \\text{fresh}}\\\\ \\htmlData{k=E-Abs.lb}{l \\preccurlyeq \\mathsf{heads}(\\Theta, \\Delta),\\ \\neg\\bot_\\Delta}\\\\ \\htmlData{k=E-Abs.cap}{\\Theta \\leadsto_{h,a} \\Theta^{h},\\ \\Delta \\leadsto_{h,a} \\Delta^{h}}\\\\ \\htmlData{k=E-Abs.body}{\\Theta^{h} ; \\Gamma, u \\prec \\varphi ; \\Delta^{h}, T^{a_T} \\vdash^{(\\varnothing, \\varphi)}_{W,N} e : U^{a_U} \\triangleright c ; \\vartheta}\\end{array}}{\\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W,N} \\lambda e : (T^{a_T} \\multimap^{u}_{l}[c;\\vartheta;h]\\, U^{a_U})^{a} \\triangleright 0 ; \\hat 1}\\;\\textsf{E-Abs}",
     "variants": {
      "df": "\\dfrac{\\begin{array}{c}\\htmlData{k=E-Abs.phi}{\\varphi\\ \\text{fresh}}\\\\ \\htmlData{k=E-Abs.lb}{l \\preccurlyeq \\mathsf{heads}(\\Theta, \\Delta),\\ \\neg\\bot_\\Delta}\\\\ \\htmlData{k=E-Abs.body}{\\Theta ; \\Gamma, u \\prec \\varphi ; \\Delta, T \\vdash^{(\\varnothing,\\varphi)}_{W} e : U}\\end{array}}{\\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W} \\lambda e : T \\multimap^{u}_{l} U}\\;\\textsf{D-Abs}",
      "live": "\\dfrac{\\begin{array}{c}\\htmlData{k=E-Abs.phi}{\\varphi\\ \\text{fresh}}\\\\ \\htmlData{k=E-Abs.lb}{l \\preccurlyeq \\mathsf{heads}(\\Theta, \\Delta),\\ \\neg\\bot_\\Delta}\\\\ \\htmlData{k=E-Abs.body}{\\Theta ; \\Gamma, u \\prec \\varphi ; \\Delta, T \\vdash^{(\\varnothing,\\varphi)}_{W} e : U}\\end{array}}{\\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W} \\lambda e : T \\multimap^{u}_{l} U}\\;\\textsf{D-Abs}"
     },
     "caption": "The body runs under an unknown future φ above u. The closure captures all of Θ and Δ, bounded below by l.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "r-app",
     "title": "E-App",
     "rocq": "static/Typing.v: e_app",
     "tex": "\\dfrac{\\begin{array}{c}\\htmlData{k=ctx.tsplit}{\\Theta = \\Theta_1 \\uplus \\Theta_2}\\\\ \\htmlData{k=ctx.lsplit}{\\Delta = \\Delta_1 \\sqcup \\Delta_2}\\\\ \\htmlData{k=E-App.ub}{u \\prec F} \\\\ \\htmlData{k=E-App.fut1}{\\Theta_1 ; \\Gamma ; \\Delta_1 \\vdash^{F \\cup \\htmlData{k=ty.heads}{\\mathsf{heads}}(\\Theta_2,\\Delta_2)}_{W,N} e_1 : (T^{a_T} \\multimap^{u}_{l}[c;\\vartheta;h]\\,U^{a_U})^{a_1} \\triangleright c_1 ; \\vartheta_1} \\\\ \\htmlData{k=age.ctx}{\\Theta_2' = \\Theta_2 - c_1,\\ \\Delta_2' = \\Delta_2 - c_1}\\\\ \\htmlData{k=E-App.fut2}{\\Theta_2' ; \\Gamma ; \\Delta_2' \\vdash^{F \\cup \\{l\\}}_{W,N} e_2 : T^{a_T} \\triangleright c_2 ; \\vartheta_2} \\\\ \\htmlData{k=E-App.credit}{c_2 \\leq a_1}\\\\ \\htmlData{k=ann.tok}{\\mathsf{tok}}\\end{array}}{\\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W,N} e_1\\,e_2 : U^{a_U} \\triangleright \\htmlData{k=E-App.cost}{c_1 + c_2 + c} ; \\vartheta_1 \\circ \\vartheta_2 \\circ \\vartheta}\\;\\textsf{E-App}",
     "variants": {
      "df": "\\dfrac{\\begin{array}{c}\\htmlData{k=ctx.tsplit}{\\Theta = \\Theta_1 \\uplus \\Theta_2}\\\\ \\htmlData{k=ctx.lsplit}{\\Delta = \\Delta_1 \\sqcup \\Delta_2}\\\\ \\htmlData{k=E-App.ub}{u \\prec F} \\\\ \\htmlData{k=E-App.fut1}{\\Theta_1 ; \\Gamma ; \\Delta_1 \\vdash^{F \\cup \\htmlData{k=ty.heads}{\\mathsf{heads}}(\\Theta_2,\\Delta_2)}_{W} e_1 : T \\multimap^{u}_{l} U}\\\\ \\htmlData{k=E-App.fut2}{\\Theta_2 ; \\Gamma ; \\Delta_2 \\vdash^{F \\cup \\{l\\}}_{W} e_2 : T}\\end{array}}{\\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W} e_1\\,e_2 : U}\\;\\textsf{D-App}",
      "live": "\\dfrac{\\begin{array}{c}\\htmlData{k=ctx.tsplit}{\\Theta = \\Theta_1 \\uplus \\Theta_2}\\\\ \\htmlData{k=ctx.lsplit}{\\Delta = \\Delta_1 \\sqcup \\Delta_2}\\\\ \\htmlData{k=E-App.ub}{u \\prec F} \\\\ \\htmlData{k=E-App.fut1}{\\Theta_1 ; \\Gamma ; \\Delta_1 \\vdash^{F \\cup \\htmlData{k=ty.heads}{\\mathsf{heads}}(\\Theta_2,\\Delta_2)}_{W} e_1 : T \\multimap^{u}_{l} U}\\\\ \\htmlData{k=E-App.fut2}{\\Theta_2 ; \\Gamma ; \\Delta_2 \\vdash^{F \\cup \\{l\\}}_{W} e_2 : T}\\end{array}}{\\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W} e_1\\,e_2 : U}\\;\\textsf{D-App}"
     },
     "caption": "e₁ runs while the context still holds what e₂ needs, e₂ runs while the closure is held, and the call runs under F.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "r-pair",
     "title": "E-Pair",
     "rocq": "static/Typing.v: e_pair",
     "tex": "\\dfrac{\\begin{array}{c}\\htmlData{k=ctx.tsplit}{\\Theta = \\Theta_1 \\uplus \\Theta_2}\\\\ \\htmlData{k=E-App.fut1}{\\Theta_1 ; \\Gamma ; \\Delta_1 \\vdash^{F \\cup \\htmlData{k=ty.heads}{\\mathsf{heads}}(\\Theta_2,\\Delta_2)}_{W,N} e_1 : T_1^{a_1} \\triangleright c_1 ; \\vartheta_1} \\\\ \\htmlData{k=age.ctx}{\\Theta_2 - c_1,\\ \\Delta_2 - c_1}\\\\ \\htmlData{k=E-Pair.fut2}{\\Theta_2' ; \\Gamma ; \\Delta_2' \\vdash^{F \\cup \\mathsf{heads}(T_1)}_{W,N} e_2 : T_2^{a_2} \\triangleright c_2 ; \\vartheta_2}\\\\ \\htmlData{k=E-Pair.age1}{(T_1, a_1) - c_2 = (T_1', a_1')}\\end{array}}{\\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W,N} \\langle e_1, e_2\\rangle : (T_1'^{a_1'} \\otimes T_2^{a_2})^{0} \\triangleright c_1 + c_2 ; \\vartheta_1 \\circ \\vartheta_2}\\;\\textsf{E-Pair}",
     "variants": {
      "df": "\\dfrac{\\begin{array}{c}\\htmlData{k=ctx.tsplit}{\\Theta = \\Theta_1 \\uplus \\Theta_2}\\\\ \\htmlData{k=E-App.fut1}{\\Theta_1 ; \\Gamma ; \\Delta_1 \\vdash^{F \\cup \\htmlData{k=ty.heads}{\\mathsf{heads}}(\\Theta_2,\\Delta_2)}_{W} e_1 : T_1}\\\\ \\htmlData{k=E-Pair.fut2}{\\Theta_2 ; \\Gamma ; \\Delta_2 \\vdash^{F \\cup \\mathsf{heads}(T_1)}_{W} e_2 : T_2}\\end{array}}{\\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W} \\langle e_1, e_2\\rangle : T_1 \\otimes T_2}\\;\\textsf{D-Pair}",
      "live": "\\dfrac{\\begin{array}{c}\\htmlData{k=ctx.tsplit}{\\Theta = \\Theta_1 \\uplus \\Theta_2}\\\\ \\htmlData{k=E-App.fut1}{\\Theta_1 ; \\Gamma ; \\Delta_1 \\vdash^{F \\cup \\htmlData{k=ty.heads}{\\mathsf{heads}}(\\Theta_2,\\Delta_2)}_{W} e_1 : T_1}\\\\ \\htmlData{k=E-Pair.fut2}{\\Theta_2 ; \\Gamma ; \\Delta_2 \\vdash^{F \\cup \\mathsf{heads}(T_1)}_{W} e_2 : T_2}\\end{array}}{\\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W} \\langle e_1, e_2\\rangle : T_1 \\otimes T_2}\\;\\textsf{D-Pair}"
     },
     "caption": "The first component is held while the second runs.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "r-let",
     "title": "E-LetU, E-LetP, E-Let",
     "rocq": "static/Typing.v: e_letu, e_letp, e_let",
     "tex": "\\dfrac{\\begin{array}{c}\\htmlData{k=E-App.fut1}{\\Theta_1 ; \\Gamma ; \\Delta_1 \\vdash^{F \\cup \\htmlData{k=ty.heads}{\\mathsf{heads}}(\\Theta_2,\\Delta_2)}_{W,N} e_1 : T_1^{a_1} \\triangleright c_1 ; \\vartheta_1}\\\\ \\htmlData{k=age.ctx}{\\Theta_2 - c_1,\\ \\Delta_2 - c_1}\\\\ \\htmlData{k=E-Let.body}{\\Theta_2' ; \\Gamma ; T_1^{a_1}, \\Delta_2' \\vdash^{F}_{W,N} e_2 : T^{a_T} \\triangleright c_2 ; \\vartheta_2}\\end{array}}{\\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W,N} \\htmlData{k=syn.let}{\\mathsf{let}\\ a = e_1\\ \\mathsf{in}\\ e_2} : T^{a_T} \\triangleright c_1 + c_2 ; \\vartheta_1 \\circ \\vartheta_2}\\;\\textsf{E-Let}",
     "variants": {
      "df": "\\dfrac{\\begin{array}{c}\\htmlData{k=E-App.fut1}{\\Theta_1 ; \\Gamma ; \\Delta_1 \\vdash^{F \\cup \\htmlData{k=ty.heads}{\\mathsf{heads}}(\\Theta_2,\\Delta_2)}_{W} e_1 : T_1}\\\\ \\htmlData{k=E-Let.body}{\\Theta_2 ; \\Gamma ; T_1, \\Delta_2 \\vdash^{F}_{W} e_2 : T}\\end{array}}{\\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W} \\htmlData{k=syn.let}{\\mathsf{let}\\ a = e_1\\ \\mathsf{in}\\ e_2} : T}\\;\\textsf{D-Let}",
      "live": "\\dfrac{\\begin{array}{c}\\htmlData{k=E-App.fut1}{\\Theta_1 ; \\Gamma ; \\Delta_1 \\vdash^{F \\cup \\htmlData{k=ty.heads}{\\mathsf{heads}}(\\Theta_2,\\Delta_2)}_{W} e_1 : T_1}\\\\ \\htmlData{k=E-Let.body}{\\Theta_2 ; \\Gamma ; T_1, \\Delta_2 \\vdash^{F}_{W} e_2 : T}\\end{array}}{\\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W} \\htmlData{k=syn.let}{\\mathsf{let}\\ a = e_1\\ \\mathsf{in}\\ e_2} : T}\\;\\textsf{D-Let}"
     },
     "caption": "One shape for the three lets. E-LetP binds the components at credit a + aᵢ.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "r-case",
     "title": "E-Inj, E-Case",
     "rocq": "static/Typing.v: e_inj1, e_inj2, e_case",
     "tex": "\\dfrac{\\begin{array}{c}\\htmlData{k=E-App.fut1}{\\Theta_1 ; \\Gamma ; \\Delta_1 \\vdash^{F \\cup \\htmlData{k=ty.heads}{\\mathsf{heads}}(\\Theta_2,\\Delta_2)}_{W,N} e : (T_1^{a_1} \\oplus T_2^{a_2})^{a} \\triangleright c_0 ; \\vartheta_0}\\\\ \\htmlData{k=E-Case.branches}{\\Theta_2' ; \\Gamma ; T_i^{a+a_i}, \\Delta_2' \\vdash^{F} e_i : T^{a_T} \\triangleright c_i ; \\vartheta_i}\\end{array}}{\\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W,N} \\mathsf{case}\\ e\\,(e_1)\\,(e_2) : T^{a_T} \\triangleright c_0 + \\max(c_1,c_2) ; \\vartheta_0 \\circ \\htmlData{k=tp.max}{\\max}(\\vartheta_1,\\vartheta_2)}\\;\\textsf{E-Case}",
     "variants": {
      "df": "\\dfrac{\\begin{array}{c}\\htmlData{k=E-App.fut1}{\\Theta_1 ; \\Gamma ; \\Delta_1 \\vdash^{F \\cup \\htmlData{k=ty.heads}{\\mathsf{heads}}(\\Theta_2,\\Delta_2)}_{W} e : T_1 \\oplus T_2}\\\\ \\htmlData{k=E-Case.branches}{\\Theta_2 ; \\Gamma ; T_i, \\Delta_2 \\vdash^{F} e_i : T}\\end{array}}{\\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W} \\mathsf{case}\\ e\\,(e_1)\\,(e_2) : T}\\;\\textsf{D-Case}",
      "live": "\\dfrac{\\begin{array}{c}\\htmlData{k=E-App.fut1}{\\Theta_1 ; \\Gamma ; \\Delta_1 \\vdash^{F \\cup \\htmlData{k=ty.heads}{\\mathsf{heads}}(\\Theta_2,\\Delta_2)}_{W} e : T_1 \\oplus T_2}\\\\ \\htmlData{k=E-Case.branches}{\\Theta_2 ; \\Gamma ; T_i, \\Delta_2 \\vdash^{F} e_i : T}\\end{array}}{\\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W} \\mathsf{case}\\ e\\,(e_1)\\,(e_2) : T}\\;\\textsf{D-Case}"
     },
     "caption": "An injection types at credit 0. Both branches share the context and the result.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "r-box",
     "title": "E-Box",
     "rocq": "static/Typing.v: e_box",
     "tex": "\\dfrac{\\begin{array}{c}\\htmlData{k=E-Box.unl}{\\Delta\\ \\text{unlimited}}\\\\ \\htmlData{k=E-Abs.phi}{\\varphi\\ \\text{fresh}}\\\\ \\htmlData{k=E-Box.inst}{\\forall \\bar s.\\ |\\bar s| = k,\\ \\htmlData{k=tp.sinsts}{\\mathsf{sinsts}}\\,N\\,\\bar s}\\\\ \\htmlData{k=E-Box.body}{\\varnothing ; \\htmlData{k=E-Box.open}{\\Gamma\\htmlData{k=tp.shift}{{\\uparrow^m}}, C(\\bar\\iota), u \\prec \\varphi} ; \\htmlData{k=E-Box.self}{\\Delta{\\uparrow^m}, f : \\Box(\\ldots)^{\\infty}} \\vdash^{(\\varnothing,\\varphi)}_{W,N} e : \\htmlData{k=tp.sinst}{U[\\bar s]}^{a_U} \\triangleright c ; \\vartheta}\\end{array}}{\\varnothing ; \\Gamma ; \\Delta \\vdash^{F}_{W,N} !e : \\Box(\\forall \\bar\\iota\\,\\bar\\alpha.\\ C.\\ \\ast \\multimap^{u}[c;\\vartheta]\\,U^{a_U})^{\\infty} \\triangleright 0 ; \\hat 1}\\;\\textsf{E-Box}",
     "variants": {
      "df": "\\dfrac{\\begin{array}{c}\\htmlData{k=E-Box.unl}{\\Delta\\ \\text{unlimited}}\\\\ \\htmlData{k=E-Abs.phi}{\\varphi\\ \\text{fresh}}\\\\ \\htmlData{k=E-Box.inst}{\\forall \\bar s\\ (N = \\infty\\ \\text{instances})}\\\\ \\htmlData{k=E-Box.body}{\\varnothing ; \\htmlData{k=E-Box.open}{\\Gamma\\htmlData{k=tp.shift}{{\\uparrow^m}}, C(\\bar\\iota), u \\prec \\varphi} ; \\htmlData{k=E-Box.self}{\\Delta{\\uparrow^m}, f : \\Box(\\ldots)} \\vdash^{(\\varnothing,\\varphi)}_{W} e : U[\\bar s]}\\end{array}}{\\varnothing ; \\Gamma ; \\Delta \\vdash^{F}_{W} !e : \\Box(\\forall \\bar\\iota\\,\\bar\\alpha.\\ C.\\ \\ast \\multimap^{u} U)}\\;\\textsf{D-Box}",
      "live": "\\dfrac{\\begin{array}{c}\\htmlData{k=E-Box.unl}{\\Delta\\ \\text{unlimited}}\\\\ \\htmlData{k=E-Abs.phi}{\\varphi\\ \\text{fresh}}\\\\ \\htmlData{k=E-Box.inst}{\\forall \\bar s\\ (N = \\infty\\ \\text{instances})}\\\\ \\htmlData{k=E-Box.body}{\\varnothing ; \\htmlData{k=E-Box.open}{\\Gamma\\htmlData{k=tp.shift}{{\\uparrow^m}}, C(\\bar\\iota), u \\prec \\varphi} ; \\htmlData{k=E-Box.self}{\\Delta{\\uparrow^m}, f : \\Box(\\ldots)} \\vdash^{(\\varnothing,\\varphi)}_{W} e : U[\\bar s]}\\end{array}}{\\varnothing ; \\Gamma ; \\Delta \\vdash^{F}_{W} !e : \\Box(\\forall \\bar\\iota\\,\\bar\\alpha.\\ C.\\ \\ast \\multimap^{u} U)}\\;\\textsf{D-Box}"
     },
     "caption": "The body sees its own box, the constraint as hypotheses, and fresh point variables. It holds no end.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "r-force",
     "title": "E-Force",
     "rocq": "static/Typing.v: e_force",
     "tex": "\\dfrac{\\begin{array}{c}\\htmlData{k=E-Force.hold}{|\\bar x| = m,\\ \\Gamma \\vdash C[\\bar x]}\\\\ \\htmlData{k=E-Box.inst}{|\\bar s| = k,\\ \\mathsf{sinsts}\\,N\\,\\bar s}\\\\ \\htmlData{k=E-Force.ub}{u[\\bar x] \\prec F}\\\\ \\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W,N} e : \\Box(\\forall\\bar\\iota\\,\\bar\\alpha.\\ C.\\ \\ast\\multimap^{u}[c;\\vartheta]\\,U^{a_U})^{a} \\triangleright c_0 ; \\vartheta_0\\end{array}}{\\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W,N} \\mathsf{force}\\,e : \\htmlData{k=tp.sinst}{U[\\bar s]}\\htmlData{k=tp.pinst}{[\\bar x]}^{a_U} \\triangleright c_0 + c ; \\vartheta_0 \\circ \\vartheta}\\;\\textsf{E-Force}",
     "variants": {
      "df": "\\dfrac{\\begin{array}{c}\\htmlData{k=E-Force.hold}{\\Gamma \\vdash C[\\bar x]}\\\\ \\htmlData{k=E-Force.ub}{u[\\bar x] \\prec F}\\\\ \\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W} e : \\Box(\\forall\\bar\\iota\\,\\bar\\alpha.\\ C.\\ \\ast\\multimap^{u} U)\\end{array}}{\\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W} \\mathsf{force}\\,e : U[\\bar s][\\bar x]}\\;\\textsf{D-Force}",
      "live": "\\dfrac{\\begin{array}{c}\\htmlData{k=E-Force.hold}{\\Gamma \\vdash C[\\bar x]}\\\\ \\htmlData{k=E-Force.ub}{u[\\bar x] \\prec F}\\\\ \\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W} e : \\Box(\\forall\\bar\\iota\\,\\bar\\alpha.\\ C.\\ \\ast\\multimap^{u} U)\\end{array}}{\\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W} \\mathsf{force}\\,e : U[\\bar s][\\bar x]}\\;\\textsf{D-Force}"
     },
     "caption": "Forcing picks an instance that meets the constraint and runs the body under the caller's future.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "r-send",
     "title": "E-Send",
     "rocq": "static/Typing.v: e_send",
     "tex": "\\dfrac{\\begin{array}{c}\\htmlData{k=E-Send.unfold}{\\htmlData{k=sty.unfold}{\\mathsf{unfold}}(S_0) = {!}(\\exists^{m}.\\,T^{b});S}\\\\ \\htmlData{k=ty.pscoped}{\\mathsf{pscoped}\\,m\\,T}\\\\ \\htmlData{k=E-Send.nobot}{\\neg\\mathsf{hbot}\\,T} \\\\ \\htmlData{k=E-Send.heads}{\\forall y \\in \\mathsf{heads}(\\htmlData{k=ty.payload-at}{T[x\\cdot i]}).\\ \\Gamma \\vdash x \\prec y}\\\\ \\htmlData{k=side.act}{x \\prec F}\\\\ \\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W,N} e : (T[x\\cdot i]^{a_p} \\otimes (S_0@x)^{a_S})^{a_0} \\triangleright c_0 ; \\vartheta_0 \\\\ \\htmlData{k=E-Send.floor}{(T[x\\cdot i], a_0 + a_p) - 1 \\leq T[x\\cdot i]^{b}}\\end{array}}{\\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W,N} \\mathsf{send}\\,e : (S@\\htmlData{k=pt.shift}{x^{+}})^{\\htmlData{k=act.refill}{N}} \\triangleright c_0 + 1 ; \\vartheta_0}\\;\\textsf{E-Send}",
     "variants": {
      "df": "\\dfrac{\\begin{array}{c}\\htmlData{k=E-Send.unfold}{\\htmlData{k=sty.unfold}{\\mathsf{unfold}}(S_0) = {!}(\\exists^{m}.\\,T);S}\\\\ \\htmlData{k=ty.pscoped}{\\mathsf{pscoped}\\,m\\,T}\\\\ \\htmlData{k=E-Send.nobot}{\\neg\\mathsf{hbot}\\,T}\\\\ \\htmlData{k=E-Send.heads}{x \\prec \\mathsf{heads}(T[x\\cdot i])}\\\\ \\htmlData{k=side.act}{x \\prec F}\\\\ \\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W} e : T[x\\cdot i] \\otimes S_0@x\\end{array}}{\\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W} \\mathsf{send}\\,e : S@\\htmlData{k=pt.shift}{x^{+}}}\\;\\textsf{D-Send}",
      "live": "\\dfrac{\\begin{array}{c}\\htmlData{k=E-Send.unfold}{\\htmlData{k=sty.unfold}{\\mathsf{unfold}}(S_0) = {!}(\\exists^{m}.\\,T);S}\\\\ \\htmlData{k=ty.pscoped}{\\mathsf{pscoped}\\,m\\,T}\\\\ \\htmlData{k=E-Send.nobot}{\\neg\\mathsf{hbot}\\,T}\\\\ \\htmlData{k=E-Send.heads}{x \\prec \\mathsf{heads}(T[x\\cdot i])}\\\\ \\htmlData{k=side.act}{x \\prec F}\\\\ \\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W} e : T[x\\cdot i] \\otimes S_0@x\\end{array}}{\\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W} \\mathsf{send}\\,e : S@\\htmlData{k=pt.shift}{x^{+}}}\\;\\textsf{D-Send}"
     },
     "caption": "The payload is held while the sender blocks at x, so x lies below its heads. The end returns at x⁺ with the refill N.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "r-recv",
     "title": "E-Recv",
     "rocq": "static/Typing.v: e_recv",
     "tex": "\\dfrac{\\begin{array}{c}\\htmlData{k=E-Recv.unfold}{\\htmlData{k=sty.unfold}{\\mathsf{unfold}}(S_0) = {?}(\\exists^{m}.\\,T^{b});S}\\\\ \\htmlData{k=ty.pscoped}{\\mathsf{pscoped}\\,m\\,T}\\\\ \\htmlData{k=side.act}{x \\prec F}\\\\ \\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W,N} e : (S_0@x)^{a} \\triangleright c_0 ; \\vartheta_0\\end{array}}{\\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W,N} \\mathsf{recv}\\,e : (T[x\\cdot i]^{\\htmlData{k=sty.payload-credit}{b}} \\otimes (S@\\htmlData{k=pt.shift}{x^{+}})^{\\htmlData{k=act.refill}{N}})^{0} \\triangleright c_0 + 1 ; \\vartheta_0}\\;\\textsf{E-Recv}",
     "variants": {
      "df": "\\dfrac{\\begin{array}{c}\\htmlData{k=E-Recv.unfold}{\\htmlData{k=sty.unfold}{\\mathsf{unfold}}(S_0) = {?}(\\exists^{m}.\\,T);S}\\\\ \\htmlData{k=ty.pscoped}{\\mathsf{pscoped}\\,m\\,T}\\\\ \\htmlData{k=side.act}{x \\prec F}\\\\ \\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W} e : S_0@x\\end{array}}{\\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W} \\mathsf{recv}\\,e : T[x\\cdot i] \\otimes S@\\htmlData{k=pt.shift}{x^{+}}}\\;\\textsf{D-Recv}",
      "live": "\\dfrac{\\begin{array}{c}\\htmlData{k=E-Recv.unfold}{\\htmlData{k=sty.unfold}{\\mathsf{unfold}}(S_0) = {?}(\\exists^{m}.\\,T);S}\\\\ \\htmlData{k=ty.pscoped}{\\mathsf{pscoped}\\,m\\,T}\\\\ \\htmlData{k=side.act}{x \\prec F}\\\\ \\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W} e : S_0@x\\end{array}}{\\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W} \\mathsf{recv}\\,e : T[x\\cdot i] \\otimes S@\\htmlData{k=pt.shift}{x^{+}}}\\;\\textsf{D-Recv}"
     },
     "caption": "The payload arrives at its floor b and at the payload fields of x.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "r-close",
     "title": "E-Close",
     "rocq": "static/Typing.v: e_close",
     "tex": "\\dfrac{\\begin{array}{c}\\htmlData{k=E-Close.unfold}{\\htmlData{k=sty.unfold}{\\mathsf{unfold}}(S_0) = \\mathsf{Close}}\\\\ \\htmlData{k=side.act}{x \\prec F}\\\\ \\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W,N} e : (S_0@x)^{a} \\triangleright c_0 ; \\vartheta_0\\end{array}}{\\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W,N} \\mathsf{close}\\,e : \\ast^{\\infty} \\triangleright c_0 + 1 ; \\vartheta_0}\\;\\textsf{E-Close}",
     "variants": {
      "df": "\\dfrac{\\begin{array}{c}\\htmlData{k=E-Close.unfold}{\\htmlData{k=sty.unfold}{\\mathsf{unfold}}(S_0) = \\mathsf{Close}}\\\\ \\htmlData{k=side.act}{x \\prec F}\\\\ \\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W} e : S_0@x\\end{array}}{\\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W} \\mathsf{close}\\,e : \\ast}\\;\\textsf{D-Close}",
      "live": "\\dfrac{\\begin{array}{c}\\htmlData{k=E-Close.unfold}{\\htmlData{k=sty.unfold}{\\mathsf{unfold}}(S_0) = \\mathsf{Close}}\\\\ \\htmlData{k=side.act}{x \\prec F}\\\\ \\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W} e : S_0@x\\end{array}}{\\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W} \\mathsf{close}\\,e : \\ast}\\;\\textsf{D-Close}"
     },
     "caption": "A close is an action at x and costs one.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "r-select",
     "title": "E-Select",
     "rocq": "static/Typing.v: e_select",
     "tex": "\\dfrac{\\begin{array}{c}\\htmlData{k=E-Select.unfold}{\\htmlData{k=sty.unfold}{\\mathsf{unfold}}(S_0) = \\oplus(S_1,S_2)}\\\\ \\htmlData{k=E-Select.order}{\\Gamma \\vdash x \\prec x\\cdot\\kappa_i}\\\\ \\htmlData{k=side.act}{x \\prec F}\\\\ \\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W,N} e : (S_0@x)^{a} \\triangleright c_0 ; \\vartheta_0\\end{array}}{\\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W,N} \\mathsf{select}_i\\,e : (S_i@\\htmlData{k=pt.sel}{\\overline{x\\cdot\\kappa_i}})^{\\htmlData{k=act.refill}{N}} \\triangleright c_0 + 1 ; \\vartheta_0}\\;\\textsf{E-Select}",
     "variants": {
      "df": "\\dfrac{\\begin{array}{c}\\htmlData{k=E-Select.unfold}{\\htmlData{k=sty.unfold}{\\mathsf{unfold}}(S_0) = \\oplus(S_1,S_2)}\\\\ \\htmlData{k=E-Select.order}{\\Gamma \\vdash x \\prec x\\cdot\\kappa_i}\\\\ \\htmlData{k=side.act}{x \\prec F}\\\\ \\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W} e : S_0@x\\end{array}}{\\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W} \\mathsf{select}_i\\,e : S_i@\\htmlData{k=pt.sel}{\\overline{x\\cdot\\kappa_i}}}\\;\\textsf{D-Select}",
      "live": "\\dfrac{\\begin{array}{c}\\htmlData{k=E-Select.unfold}{\\htmlData{k=sty.unfold}{\\mathsf{unfold}}(S_0) = \\oplus(S_1,S_2)}\\\\ \\htmlData{k=E-Select.order}{\\Gamma \\vdash x \\prec x\\cdot\\kappa_i}\\\\ \\htmlData{k=side.act}{x \\prec F}\\\\ \\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W} e : S_0@x\\end{array}}{\\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W} \\mathsf{select}_i\\,e : S_i@\\htmlData{k=pt.sel}{\\overline{x\\cdot\\kappa_i}}}\\;\\textsf{D-Select}"
     },
     "caption": "The selecting end continues at (x·κᵢ)‾. Its partner point x·κᵢ must lie above x.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "r-branch",
     "title": "E-Branch",
     "rocq": "static/Typing.v: e_branch",
     "tex": "\\dfrac{\\begin{array}{c}\\htmlData{k=E-Branch.unfold}{\\htmlData{k=sty.unfold}{\\mathsf{unfold}}(S_0) = \\&(S_1,S_2)}\\\\ \\htmlData{k=E-Branch.order}{\\Gamma \\vdash x \\prec \\overline{x\\cdot\\kappa_1},\\ x \\prec \\overline{x\\cdot\\kappa_2}}\\\\ \\htmlData{k=side.act}{x \\prec F}\\\\ \\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W,N} e : (S_0@x)^{a} \\triangleright c_0 ; \\vartheta_0\\end{array}}{\\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W,N} \\mathsf{branch}\\,e : ((S_1@\\htmlData{k=pt.bra}{x\\cdot\\kappa_1})^{N} \\oplus (S_2@x\\cdot\\kappa_2)^{N})^{0} \\triangleright c_0 + 1 ; \\vartheta_0}\\;\\textsf{E-Branch}",
     "variants": {
      "df": "\\dfrac{\\begin{array}{c}\\htmlData{k=E-Branch.unfold}{\\htmlData{k=sty.unfold}{\\mathsf{unfold}}(S_0) = \\&(S_1,S_2)}\\\\ \\htmlData{k=E-Branch.order}{\\Gamma \\vdash x \\prec \\overline{x\\cdot\\kappa_i}}\\\\ \\htmlData{k=side.act}{x \\prec F}\\\\ \\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W} e : S_0@x\\end{array}}{\\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W} \\mathsf{branch}\\,e : S_1@\\htmlData{k=pt.bra}{x\\cdot\\kappa_1} \\oplus S_2@x\\cdot\\kappa_2}\\;\\textsf{D-Branch}",
      "live": "\\dfrac{\\begin{array}{c}\\htmlData{k=E-Branch.unfold}{\\htmlData{k=sty.unfold}{\\mathsf{unfold}}(S_0) = \\&(S_1,S_2)}\\\\ \\htmlData{k=E-Branch.order}{\\Gamma \\vdash x \\prec \\overline{x\\cdot\\kappa_i}}\\\\ \\htmlData{k=side.act}{x \\prec F}\\\\ \\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W} e : S_0@x\\end{array}}{\\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W} \\mathsf{branch}\\,e : S_1@\\htmlData{k=pt.bra}{x\\cdot\\kappa_1} \\oplus S_2@x\\cdot\\kappa_2}\\;\\textsf{D-Branch}"
     },
     "caption": "The branching end continues at x·κᵢ. Its partner point (x·κᵢ)‾ must lie above x for both i.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "r-link",
     "title": "E-Link",
     "rocq": "static/Typing.v: e_link",
     "tex": "\\dfrac{\\begin{array}{c}\\htmlData{k=E-Link.dual}{\\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W,N} e : ((S@x)^{a_1} \\otimes (\\overline{S}@\\overline{x})^{a_2})^{a_0} \\triangleright c_0 ; \\vartheta_0}\\\\ \\htmlData{k=ann.tok}{\\mathsf{tok}}\\end{array}}{\\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W,N} \\mathsf{link}\\,e : \\ast^{\\infty} \\triangleright c_0 ; \\vartheta_0 \\circ \\htmlData{k=ann.tlink}{\\mathsf{tlink}\\,\\hat 1}}\\;\\textsf{E-Link}",
     "variants": {
      "df": "\\dfrac{\\begin{array}{c}\\htmlData{k=E-Link.dual}{\\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W} e : S@x \\otimes \\overline{S}@\\overline{x}}\\end{array}}{\\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W} \\mathsf{link}\\,e : \\ast}\\;\\textsf{D-Link}",
      "live": "\\dfrac{\\begin{array}{c}\\htmlData{k=E-Link.dual}{\\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W} e : S@x \\otimes \\overline{S}@\\overline{x}}\\end{array}}{\\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W} \\mathsf{link}\\,e : \\ast}\\;\\textsf{D-Link}"
     },
     "caption": "A link asks no future fact and costs no action. It spends one ticket.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "r-spawnlam",
     "title": "E-SpawnLam",
     "rocq": "static/Typing.v: e_spawn_lam",
     "tex": "\\dfrac{\\begin{array}{c}\\htmlData{k=E-SpawnLam.age}{\\Theta' = \\Theta - 1,\\ \\Delta' = \\Delta - 1}\\\\ \\htmlData{k=E-SpawnLam.body}{\\Theta' ; \\Gamma ; \\ast^{a_1}, \\Delta' \\vdash^{\\htmlData{k=E-SpawnLam.future}{(\\varnothing, \\cdot)}}_{W,N} e : \\ast^{a_U} \\triangleright c' ; \\vartheta'}\\end{array}}{\\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W,N} \\mathsf{spawn}\\,(\\lambda e) : \\ast^{\\infty} \\triangleright 0 ; \\htmlData{k=ann.tspawn}{\\mathsf{tspawn}(\\vartheta'(0))\\,\\hat 1}}\\;\\textsf{E-SpawnLam}",
     "variants": {
      "df": "\\dfrac{\\begin{array}{c}\\htmlData{k=E-SpawnLam.body}{\\Theta ; \\Gamma ; \\ast, \\Delta \\vdash^{\\htmlData{k=E-SpawnLam.future}{(\\varnothing, \\cdot)}}_{W} e : \\ast}\\end{array}}{\\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W} \\mathsf{spawn}\\,(\\lambda e) : \\ast}\\;\\textsf{D-SpawnLam}",
      "live": "\\dfrac{\\begin{array}{c}\\htmlData{k=E-SpawnLam.body}{\\Theta ; \\Gamma ; \\ast, \\Delta \\vdash^{\\htmlData{k=E-SpawnLam.future}{(\\varnothing, \\cdot)}}_{W} e : \\ast}\\end{array}}{\\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W} \\mathsf{spawn}\\,(\\lambda e) : \\ast}\\;\\textsf{D-SpawnLam}"
     },
     "caption": "Spawning a λ directly asks no lower point. The child starts at the empty future with every handed end one unit lower.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "r-spawn",
     "title": "E-Spawn",
     "rocq": "static/Typing.v: e_spawn",
     "tex": "\\dfrac{\\begin{array}{c}\\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W,N} e : (\\ast^{a_1} \\multimap^{u}_{l}[c';\\vartheta';h]\\,\\ast^{a_U})^{a} \\triangleright c_0 ; \\vartheta_0\\\\ \\htmlData{k=E-Spawn.credit}{a \\geq 1}\\\\ \\htmlData{k=ann.tok}{\\mathsf{tok}}\\end{array}}{\\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W,N} \\mathsf{spawn}\\,e : \\ast^{\\infty} \\triangleright c_0 ; \\vartheta_0 \\circ \\htmlData{k=ann.tspawn}{\\mathsf{tspawn}(\\vartheta'(0))\\,\\hat 1}}\\;\\textsf{E-Spawn}",
     "variants": {
      "df": "\\dfrac{\\begin{array}{c}\\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W} e : \\ast \\multimap^{u}_{l} \\ast\\end{array}}{\\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W} \\mathsf{spawn}\\,e : \\ast}\\;\\textsf{D-Spawn}",
      "live": "\\dfrac{\\begin{array}{c}\\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W} e : \\ast \\multimap^{u}_{l} \\ast\\end{array}}{\\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W} \\mathsf{spawn}\\,e : \\ast}\\;\\textsf{D-Spawn}"
     },
     "caption": "Spawning a closure value hands over its captured ends, which must have one unit to spare.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "r-new",
     "title": "E-New",
     "rocq": "static/Typing.v: e_new",
     "tex": "\\dfrac{\\begin{array}{c}\\htmlData{k=ctx.empty}{\\Delta\\ \\text{empty}}\\\\ \\htmlData{k=E-New.fam}{\\ell \\in L_W}\\end{array}}{\\varnothing ; \\Gamma ; \\Delta \\vdash^{F}_{W,N} \\mathsf{new}_\\ell : (\\exists^{\\htmlData{k=E-New.bot}{\\bot}}\\rho.\\ \\htmlData{k=E-New.laws}{\\Lambda_\\ell(\\rho)}.\\ \\htmlData{k=E-New.dual}{((S@\\rho)^{N} \\otimes (\\overline{S}@\\overline{\\rho})^{N})}^{0})^{0} \\triangleright 0 ; \\hat 1}\\;\\textsf{E-New}",
     "variants": {
      "df": "\\dfrac{\\begin{array}{c}\\htmlData{k=ctx.empty}{\\Delta\\ \\text{empty}}\\\\ \\htmlData{k=E-New.fam}{\\ell \\in L_W}\\end{array}}{\\varnothing ; \\Gamma ; \\Delta \\vdash^{F}_{W} \\mathsf{new}_\\ell : \\exists^{\\htmlData{k=E-New.bot}{\\bot}}\\rho.\\ \\htmlData{k=E-New.laws}{\\Lambda_\\ell(\\rho)}.\\ \\htmlData{k=E-New.dual}{S@\\rho \\otimes \\overline{S}@\\overline{\\rho}}}\\;\\textsf{D-New}",
      "live": "\\dfrac{\\begin{array}{c}\\htmlData{k=ctx.empty}{\\Delta\\ \\text{empty}}\\\\ \\htmlData{k=E-New.fam}{\\ell \\in L_W}\\end{array}}{\\varnothing ; \\Gamma ; \\Delta \\vdash^{F}_{W} \\mathsf{new}_\\ell : \\exists^{\\htmlData{k=E-New.bot}{\\bot}}\\rho.\\ \\htmlData{k=E-New.laws}{\\Lambda_\\ell(\\rho)}.\\ \\htmlData{k=E-New.dual}{S@\\rho \\otimes \\overline{S}@\\overline{\\rho}}}\\;\\textsf{D-New}"
     },
     "caption": "A fresh root opens with the laws of its family. The context does not know it, hence the ⊥ bound.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "r-newat",
     "title": "E-NewAt",
     "rocq": "static/Typing.v: e_new_at",
     "tex": "\\dfrac{\\begin{array}{c}\\htmlData{k=E-NewAt.anchor}{\\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W,N} e : (S_0@x)^{a} \\triangleright c_0 ; \\vartheta_0}\\end{array}}{\\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W,N} \\mathsf{new}_\\kappa\\,e : ((S_0@x)^{a} \\otimes \\htmlData{k=E-NewAt.field}{((S@x\\cdot\\kappa)^{N} \\otimes (\\overline{S}@\\overline{x\\cdot\\kappa})^{N})}^{0})^{0} \\triangleright c_0 ; \\vartheta_0}\\;\\textsf{E-NewAt}",
     "variants": {
      "df": "\\dfrac{\\begin{array}{c}\\htmlData{k=E-NewAt.anchor}{\\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W} e : S_0@x}\\end{array}}{\\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W} \\mathsf{new}_\\kappa\\,e : S_0@x \\otimes \\htmlData{k=E-NewAt.field}{(S@x\\cdot\\kappa \\otimes \\overline{S}@\\overline{x\\cdot\\kappa})}}\\;\\textsf{D-NewAt}",
      "live": "\\dfrac{\\begin{array}{c}\\htmlData{k=E-NewAt.anchor}{\\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W} e : S_0@x}\\end{array}}{\\Theta ; \\Gamma ; \\Delta \\vdash^{F}_{W} \\mathsf{new}_\\kappa\\,e : S_0@x \\otimes \\htmlData{k=E-NewAt.field}{(S@x\\cdot\\kappa \\otimes \\overline{S}@\\overline{x\\cdot\\kappa})}}\\;\\textsf{D-NewAt}"
     },
     "caption": "The anchor comes back unchanged. The channel sits at its field κ, where box constraints or W supply the facts.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "r-struct",
     "title": "E-Sub, E-Weak, E-Contract",
     "rocq": "static/Typing.v: e_sub, e_weak, e_contract",
     "tex": "\\begin{array}{c}\\dfrac{\\begin{array}{c}e : T^{a} \\triangleright c ; \\vartheta\\\\ \\htmlData{k=sub.tsub}{T^{a} \\leq T'^{a'}}\\\\ \\htmlData{k=E-Sub.cost}{c \\leq c',\\ \\vartheta \\leq \\vartheta'}\\end{array}}{e : T'^{a'} \\triangleright c' ; \\vartheta'}\\;\\textsf{E-Sub} \\\\[2ex] \\dfrac{\\begin{array}{c}\\htmlData{k=E-Weak.drop}{\\Delta' \\preceq_{\\mathsf{wk}} \\Delta}\\end{array}}{\\Delta' \\vdash e \\Rightarrow \\Delta \\vdash e}\\;\\textsf{E-Weak} \\\\[2ex] \\dfrac{\\begin{array}{c}\\htmlData{k=ty.unlimited}{\\mathsf{unlimited}\\,U}\\end{array}}{U, U, \\Delta \\vdash e \\Rightarrow U, \\Delta \\vdash e[x/x']}\\;\\textsf{E-Contract}\\end{array}",
     "variants": {
      "df": "\\begin{array}{c}\\dfrac{\\begin{array}{c}\\htmlData{k=sub.dconv}{\\htmlData{k=ann.tydf}{\\mathsf{ty\\_df}}\\,T \\leq \\mathsf{ty\\_df}\\,T'}\\end{array}}{t : T \\Rightarrow t : T'}\\;\\textsf{D-Conv} \\\\[2ex] \\dfrac{\\begin{array}{c}\\htmlData{k=E-Weak.drop}{\\Delta' \\preceq_{\\mathsf{wk}} \\Delta}\\end{array}}{\\Delta' \\vdash t \\Rightarrow \\Delta \\vdash t}\\;\\textsf{D-Weak} \\\\[2ex] \\dfrac{\\begin{array}{c}\\htmlData{k=ty.unlimited}{\\mathsf{unlimited}\\,U}\\end{array}}{U, U, \\Delta \\vdash t \\Rightarrow U, \\Delta \\vdash t}\\;\\textsf{D-Contract}\\end{array}",
      "live": "\\begin{array}{c}\\dfrac{\\begin{array}{c}\\htmlData{k=sub.dconv}{\\htmlData{k=ann.tydf}{\\mathsf{ty\\_df}}\\,T \\leq \\mathsf{ty\\_df}\\,T'}\\end{array}}{t : T \\Rightarrow t : T'}\\;\\textsf{D-Conv} \\\\[2ex] \\dfrac{\\begin{array}{c}\\htmlData{k=E-Weak.drop}{\\Delta' \\preceq_{\\mathsf{wk}} \\Delta}\\end{array}}{\\Delta' \\vdash t \\Rightarrow \\Delta \\vdash t}\\;\\textsf{D-Weak} \\\\[2ex] \\dfrac{\\begin{array}{c}\\htmlData{k=ty.unlimited}{\\mathsf{unlimited}\\,U}\\end{array}}{U, U, \\Delta \\vdash t \\Rightarrow U, \\Delta \\vdash t}\\;\\textsf{D-Contract}\\end{array}"
     },
     "caption": "Weakening and contraction apply to box variables only.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "r-ex",
     "title": "E-Pack, E-Open",
     "rocq": "static/Typing.v: e_pack, e_open",
     "tex": "\\begin{array}{c}\\dfrac{\\begin{array}{c}\\htmlData{k=E-Force.hold}{|\\bar x| = m,\\ \\Gamma \\vdash C[\\bar x]}\\\\ \\htmlData{k=E-Pack.lb}{l \\preccurlyeq \\mathsf{heads}(\\htmlData{k=tp.pinst}{T[\\bar x]})}\\\\ e : T[\\bar x]^{a}\\end{array}}{e : (\\exists^{l}\\bar\\iota.\\,C.\\,T^{a})^{0}}\\;\\textsf{E-Pack} \\\\[2ex] \\dfrac{\\begin{array}{c}\\htmlData{k=E-Open.entry}{\\Delta(i) = (\\exists^{l}\\bar\\iota.\\,C.\\,T^{a_T})^{a},\\ \\neg\\mathsf{unlimited}\\,T}\\\\ \\htmlData{k=E-Open.body}{\\Theta\\htmlData{k=tp.shift}{{\\uparrow}}; \\Gamma{\\uparrow}, C; \\Delta{\\uparrow}[i \\mapsto T^{a+a_T}] \\vdash^{F\\uparrow} e : U{\\uparrow}}\\end{array}}{\\Theta;\\Gamma;\\Delta \\vdash^{F} e : U}\\;\\textsf{E-Open}\\end{array}",
     "variants": {
      "df": "\\begin{array}{c}\\dfrac{\\begin{array}{c}\\htmlData{k=E-Force.hold}{\\Gamma \\vdash C[\\bar x]}\\\\ \\htmlData{k=E-Pack.lb}{l \\preccurlyeq \\mathsf{heads}(\\htmlData{k=tp.pinst}{T[\\bar x]})}\\\\ t : T[\\bar x]\\end{array}}{t : \\exists^{l}\\bar\\iota.\\,C.\\,T}\\;\\textsf{D-Pack} \\\\[2ex] \\dfrac{\\begin{array}{c}\\htmlData{k=E-Open.entry}{\\Delta(i) = \\exists^{l}\\bar\\iota.\\,C.\\,T}\\\\ \\htmlData{k=E-Open.body}{\\Theta\\htmlData{k=tp.shift}{{\\uparrow}}; \\Gamma{\\uparrow}, C; \\Delta{\\uparrow}[i \\mapsto T] \\vdash t : U{\\uparrow}}\\end{array}}{\\Theta;\\Gamma;\\Delta \\vdash t : U}\\;\\textsf{D-Open}\\end{array}",
      "live": "\\begin{array}{c}\\dfrac{\\begin{array}{c}\\htmlData{k=E-Force.hold}{\\Gamma \\vdash C[\\bar x]}\\\\ \\htmlData{k=E-Pack.lb}{l \\preccurlyeq \\mathsf{heads}(\\htmlData{k=tp.pinst}{T[\\bar x]})}\\\\ t : T[\\bar x]\\end{array}}{t : \\exists^{l}\\bar\\iota.\\,C.\\,T}\\;\\textsf{D-Pack} \\\\[2ex] \\dfrac{\\begin{array}{c}\\htmlData{k=E-Open.entry}{\\Delta(i) = \\exists^{l}\\bar\\iota.\\,C.\\,T}\\\\ \\htmlData{k=E-Open.body}{\\Theta\\htmlData{k=tp.shift}{{\\uparrow}}; \\Gamma{\\uparrow}, C; \\Delta{\\uparrow}[i \\mapsto T] \\vdash t : U{\\uparrow}}\\end{array}}{\\Theta;\\Gamma;\\Delta \\vdash t : U}\\;\\textsf{D-Open}\\end{array}"
     },
     "caption": "Packing picks a witness that meets C. Opening a variable adds fresh point variables with C as hypotheses.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "p-term",
     "title": "P-Term",
     "rocq": "static/Typing.v: p_term, soup/LFTyped.v: lf_term",
     "tex": "\\dfrac{\\begin{array}{c}\\htmlData{k=ty.prim}{\\mathsf{prim}\\,T}\\\\ \\htmlData{k=P-Term.C0}{\\mathsf{dom}\\,\\Theta_B = \\htmlData{k=tp.ends}{\\mathsf{ends}}(C_0)}\\\\ \\htmlData{k=P-Term.disj}{\\htmlData{k=tp.chans}{\\mathsf{chans}}\\,\\htmlData{k=tp.Sigma}{\\Sigma} \\cap C_0 = \\varnothing}\\\\ \\htmlData{k=pfree}{\\mathsf{pfree}\\,\\Sigma} \\\\ \\htmlData{k=P-Term.pairs}{\\forall c \\in C_0.\\ \\Theta_B(c^{+}) = S@x^{\\infty},\\ \\Theta_B(c^{-}) = \\overline{S}@\\overline{x}^{\\infty}} \\\\ \\htmlData{k=P-Term.typed}{\\htmlData{k=tp.lift}{\\Sigma^{\\infty}} \\cup \\Theta_B ; \\varnothing ; \\varnothing \\vdash^{\\htmlData{k=P-Term.future}{(\\varnothing,\\cdot)}}_{W,\\infty} t : T^{a} \\triangleright c ; \\vartheta}\\end{array}}{\\Sigma \\htmlData{k=tp.pjudg}{\\vdash_W} (C_0, \\{t\\}) : T}\\;\\textsf{P-Term}",
     "variants": {
      "lf": "\\dfrac{\\begin{array}{c}\\htmlData{k=ty.prim}{\\mathsf{prim}\\,T}\\\\ \\htmlData{k=P-Term.C0}{\\mathsf{dom}\\,\\Theta_B = \\mathsf{ends}(C_0)}\\\\ \\htmlData{k=P-Term.disj}{\\mathsf{chans}\\,\\Sigma \\cap C_0 = \\varnothing}\\\\ \\htmlData{k=pfree}{\\mathsf{pfree}\\,\\Sigma} \\\\ \\htmlData{k=P-Term.pairs}{\\forall c \\in C_0.\\ \\Theta_B(c^{+}) = S@x^{N},\\ \\Theta_B(c^{-}) = \\overline{S}@\\overline{x}^{N}} \\\\ \\htmlData{k=lf.typedN}{\\Sigma^{N} \\cup \\Theta_B ; \\varnothing ; \\varnothing \\vdash^{\\htmlData{k=P-Term.future}{(\\varnothing,\\cdot)}}_{W,\\htmlData{k=lf.N}{N}} t : T^{a} \\triangleright c ; \\vartheta}\\\\ \\htmlData{k=guard.judg}{\\varnothing \\vdash\\!\\triangleright t}\\\\ \\htmlData{k=lf.meets}{\\htmlData{k=ann.meets}{\\mathsf{meets}}\\,\\vartheta\\,0\\,\\htmlData{k=fu.tk}{tk}}\\end{array}}{\\Sigma \\htmlData{k=tp.lfjudg}{\\Vdash^{N}_W} (C_0, \\{t\\}) : T}\\;\\textsf{lf\\_term}"
     },
     "caption": "A single thread with the channels C₀ restricted. Its interface Σ holds no partner pair, and the thread holds both ends of every channel of C₀.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "p-connect",
     "title": "P-Connect",
     "rocq": "static/Typing.v: p_connect, soup/LFTyped.v: lf_connect",
     "tex": "\\dfrac{\\begin{array}{c}\\htmlData{k=P-Connect.left}{\\Sigma_1 \\cup \\Sigma_C \\vdash_{W_1} (C_1, E_1) : T}\\\\ \\htmlData{k=P-Connect.right}{\\Sigma_2 \\cup \\htmlData{k=P-Connect.cut}{\\overline{\\Sigma_C}} \\vdash_{W_2} (C_2, E_2) : \\ast} \\\\ \\htmlData{k=P-Connect.disj}{\\text{ends and channels apart}}\\\\ \\htmlData{k=P-Connect.cutfree}{\\mathsf{pfree}\\,\\Sigma_C}\\\\ \\htmlData{k=w.wf}{\\mathsf{world\\_wf}\\,W_1, W_2}\\\\ \\htmlData{k=P-Connect.fams}{\\htmlData{k=w.fams}{L_1} \\cap L_2 = \\varnothing}\\\\ \\htmlData{k=P-Connect.strict}{\\htmlData{k=w.strict}{\\mathsf{strict}}(W_1 \\sqcup W_2)}\\end{array}}{\\begin{array}{c}\\Sigma_1 \\cup \\Sigma_2 \\vdash_{\\htmlData{k=P-Connect.join}{W_1 \\htmlData{k=w.join}{\\sqcup} W_2}} \\\\ (C_1 \\cup C_2 \\cup \\htmlData{k=tp.chans}{\\mathsf{chans}}\\,\\Sigma_C, E_1 \\uplus E_2) : T\\end{array}}\\;\\textsf{P-Connect}",
     "variants": {
      "lf": "\\dfrac{\\begin{array}{c}\\htmlData{k=P-Connect.left}{\\Sigma_1 \\cup \\Sigma_C \\Vdash^{N}_{W_1} (C_1, E_1) : T}\\\\ \\htmlData{k=P-Connect.right}{\\Sigma_2 \\cup \\htmlData{k=P-Connect.cut}{\\overline{\\Sigma_C}} \\Vdash^{N}_{W_2} (C_2, E_2) : \\ast} \\\\ \\htmlData{k=P-Connect.disj}{\\text{ends and channels apart}}\\\\ \\htmlData{k=P-Connect.cutfree}{\\mathsf{pfree}\\,\\Sigma_C}\\\\ \\htmlData{k=w.wf}{\\mathsf{world\\_wf}\\,W_1, W_2}\\\\ \\htmlData{k=P-Connect.fams}{\\htmlData{k=w.fams}{L_1} \\cap L_2 = \\varnothing}\\\\ \\htmlData{k=P-Connect.strict}{\\htmlData{k=w.strict}{\\mathsf{strict}}(W_1 \\sqcup W_2)}\\end{array}}{\\begin{array}{c}\\Sigma_1 \\cup \\Sigma_2 \\Vdash^{N}_{\\htmlData{k=P-Connect.join}{W_1 \\sqcup W_2}} \\\\ (C_1 \\cup C_2 \\cup \\mathsf{chans}\\,\\Sigma_C, E_1 \\uplus E_2) : T\\end{array}}\\;\\textsf{lf\\_connect}"
     },
     "caption": "Two components, each in its own world, cut at Σ_C against its exact dual. The main thread lives on the left.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "p-join",
     "title": "P-Join (admissible)",
     "rocq": "static/Typing.v: p_join, soup/LFTyped.v: lf_join",
     "tex": "\\dfrac{\\begin{array}{c}\\text{premises of P-Connect with} \\\\ \\htmlData{k=P-Join.lemma}{\\mathsf{strict}\\,W_1,\\ \\mathsf{strict}\\,W_2,\\ \\mathsf{strict}(\\htmlData{k=w.restrict}{W_1|_S} \\sqcup W_2|_S)}\\end{array}}{\\begin{array}{c}\\Sigma_1 \\cup \\Sigma_2 \\vdash_{W_1 \\sqcup W_2} \\\\ (C_1 \\cup C_2 \\cup \\mathsf{chans}\\,\\Sigma_C, E_1 \\uplus E_2) : T\\end{array}}\\;\\textsf{P-Join}",
     "caption": "A lemma, not a rule. Strictness of each world and of the join of their shared parts is the same as strictness of the whole join, so P-Connect covers it.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "g-acts",
     "title": "Terms that act",
     "rocq": "static/Guard.v: sprim, acts",
     "modes": [
      "live",
      "lf"
     ],
     "tex": "\\htmlData{k=guard.acts}{\\begin{array}{l}\\mathsf{acts}\\,e \\iff e \\text{ contains, in evaluation position,} \\\\ \\quad \\text{an operator } k \\in \\{\\mathsf{send}, \\mathsf{recv}, \\mathsf{close}, \\mathsf{select}_i, \\mathsf{branch}\\}\\end{array}}",
     "caption": "An acting term performs a channel action before it returns."
    },
    {
     "id": "g-rules",
     "title": "The guard Λ ⊢▷ t",
     "rocq": "static/Guard.v: lguard",
     "modes": [
      "live",
      "lf"
     ],
     "tex": "\\begin{array}{c}\n\\dfrac{\\begin{array}{c}\\htmlData{k=guard.var}{\\Lambda(y) = \\mathsf{false}}\\end{array}}{\\htmlData{k=guard.marks}{\\Lambda} \\vdash\\!\\triangleright y}\\;\\textsf{gl\\_var} \\quad \\dfrac{\\begin{array}{c}\\htmlData{k=guard.lam}{\\mathsf{false}.\\Lambda \\vdash\\!\\triangleright b}\\end{array}}{\\Lambda \\vdash\\!\\triangleright \\lambda b}\\;\\textsf{gl\\_lam} \\quad \\dfrac{\\begin{array}{c}\\htmlData{k=guard.box}{\\mathsf{true}.\\Lambda \\vdash\\!\\triangleright b}\\end{array}}{\\Lambda \\vdash\\!\\triangleright\\ !b}\\;\\textsf{gl\\_box} \\\\[2ex]\n\\dfrac{\\begin{array}{c}\\htmlData{k=guard.cong}{\\Lambda \\vdash\\!\\triangleright e_1 \\quad \\Lambda \\vdash\\!\\triangleright e_2}\\end{array}}{\\Lambda \\vdash\\!\\triangleright e_1\\,e_2}\\;\\textsf{gl\\_app} \\quad \\dfrac{\\begin{array}{c}\\Lambda \\vdash\\!\\triangleright e_1\\\\ \\htmlData{k=guard.acts}{\\mathsf{acts}\\,e_1}\\\\ \\htmlData{k=guard.tick}{\\varnothing \\vdash\\!\\triangleright e_2}\\end{array}}{\\Lambda \\vdash\\!\\triangleright e_1\\,e_2}\\;\\textsf{gl\\_tick\\_app} \\\\[2ex]\n\\dfrac{\\begin{array}{c}\\htmlData{k=guard.bind}{\\Lambda \\vdash\\!\\triangleright e_1 \\quad \\mathsf{false}.\\Lambda \\vdash\\!\\triangleright e_2}\\end{array}}{\\Lambda \\vdash\\!\\triangleright \\mathsf{let}\\ a = e_1\\ \\mathsf{in}\\ e_2}\\;\\textsf{gl\\_let}\n\\end{array}",
     "caption": "Guarded recursion. A box puts its self at ▷, a marked variable cannot be used, and an acting term clears every mark for what runs after it."
    },
    {
     "id": "g-proc",
     "title": "Guard of a process",
     "rocq": "static/FundamentalProc.v: pguard",
     "modes": [
      "live",
      "lf"
     ],
     "tex": "\\htmlData{k=guard.proc}{\\vdash\\!\\triangleright p \\iff \\forall t \\in p.\\ \\varnothing \\vdash\\!\\triangleright t}",
     "caption": "Every thread is guarded with no marks."
    }
   ]
  },
  {
   "id": "semantic",
   "title": "Semantic typing",
   "intro": "One step-indexed relation R^κ with a cost table κ gives deadlock freedom (κ_DF) and liveness (κ_L). Fuel adds per-thread counters and tickets, and the soup fixes ownership outside the index for lock freedom.",
   "blocks": [
    {
     "id": "ct-table",
     "title": "Cost tables",
     "rocq": "relation/CostTable.v: ctable",
     "tex": "\\htmlData{k=ct.table}{\\kappa = (\\kappa_\\beta, \\kappa_{new}, \\kappa_{spawn}, \\kappa_{link}, \\kappa_{give}, \\kappa_{take})} \\qquad \\htmlData{k=ct.take-pos}{1 \\leq \\kappa_{take}} \\qquad \\htmlData{k=ct.give-pos}{\\kappa_\\beta = 0 \\Rightarrow 1 \\leq \\kappa_{give}} \\qquad \\htmlData{k=ct.give-take}{\\kappa_{give} \\leq \\kappa_{take}}",
     "caption": "A step of cost c taken at level n carries its obligation at level n − c. Three side conditions make the generic relation well defined and composable.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "ct-two",
     "title": "κ_DF and κ_L",
     "rocq": "relation/CostTable.v: κ_DF, κ_L",
     "tex": "\\begin{array}{lcc}\n & \\htmlData{k=ct.DF}{\\kappa_{DF}} & \\htmlData{k=ct.L}{\\kappa_L} \\\\ \\hline\n\\htmlData{k=ct.beta}{\\beta,\\ \\mathsf{let},\\ \\mathsf{case},\\ \\mathsf{force}} & 1 & 0 \\\\\n\\htmlData{k=ct.new}{\\mathsf{new}_\\ell,\\ \\mathsf{new}_\\kappa} & 1 & 0 \\\\\n\\htmlData{k=ct.spawn}{\\mathsf{spawn}} & 1 & 0 \\\\\n\\htmlData{k=ct.link}{\\mathsf{link}} & 0 & 0 \\\\\n\\htmlData{k=ct.give}{\\mathsf{send},\\ \\mathsf{select},\\ \\mathsf{close}} & 0 & 1 \\\\\n\\htmlData{k=ct.takek}{\\mathsf{recv},\\ \\mathsf{branch}} & 1 & 1 \\\\\n\\htmlData{k=ct.sync}{\\text{synchronization}} & 1 & 2\n\\end{array}",
     "variants": {
      "df": "\\begin{array}{lc}\n & \\htmlData{k=ct.DF}{\\kappa_{DF}} \\\\ \\hline\n\\htmlData{k=ct.beta}{\\beta,\\ \\mathsf{let},\\ \\mathsf{case},\\ \\mathsf{force}} & 1 \\\\\n\\htmlData{k=ct.new}{\\mathsf{new}_\\ell,\\ \\mathsf{new}_\\kappa} & 1 \\\\\n\\htmlData{k=ct.spawn}{\\mathsf{spawn}} & 1 \\\\\n\\htmlData{k=ct.link}{\\mathsf{link}} & 0 \\\\\n\\htmlData{k=ct.give}{\\mathsf{send},\\ \\mathsf{select},\\ \\mathsf{close}} & 0 \\\\\n\\htmlData{k=ct.takek}{\\mathsf{recv},\\ \\mathsf{branch}} & 1 \\\\\n\\htmlData{k=ct.sync}{\\text{synchronization}} & 1\n\\end{array}",
      "live": "\\begin{array}{lc}\n & \\htmlData{k=ct.L}{\\kappa_L} \\\\ \\hline\n\\htmlData{k=ct.beta}{\\beta,\\ \\mathsf{let},\\ \\mathsf{case},\\ \\mathsf{force}} & 0 \\\\\n\\htmlData{k=ct.new}{\\mathsf{new}_\\ell,\\ \\mathsf{new}_\\kappa} & 0 \\\\\n\\htmlData{k=ct.spawn}{\\mathsf{spawn}} & 0 \\\\\n\\htmlData{k=ct.link}{\\mathsf{link}} & 0 \\\\\n\\htmlData{k=ct.give}{\\mathsf{send},\\ \\mathsf{select},\\ \\mathsf{close}} & 1 \\\\\n\\htmlData{k=ct.takek}{\\mathsf{recv},\\ \\mathsf{branch}} & 1 \\\\\n\\htmlData{k=ct.sync}{\\text{synchronization}} & 2\n\\end{array}"
     },
     "caption": "Steps of cost 0 are read inductively inside a level. In κ_DF they shrink the term, in κ_L they are the τ steps.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "rel-atcost",
     "title": "After a step",
     "rocq": "relation/Relation.v: at_cost_E, at_cost_V, at_cost_P",
     "tex": "\\htmlData{k=rel.atcost}{e' \\text{ at } \\Theta' \\iff \\begin{cases} \\htmlData{k=rel.lfp}{X(\\Theta', e')} & \\kappa(\\alpha) = 0 \\\\ e' \\in E[\\kappa]^{W}_{n-\\kappa(\\alpha)}\\llbracket \\Theta' \\vdash T \\rrbracket^{F} & \\kappa(\\alpha) > 0 \\end{cases}}",
     "caption": "X is the least fixpoint being defined. Cost-0 steps stay inside the level.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "v-base",
     "title": "V at ∗, S@x, ⊗, ⊕",
     "rocq": "relation/Relation.v: Vbody",
     "tex": "\\begin{array}{l}\n\\htmlData{k=V-Unit}{\\ast \\in V[\\kappa]^{W}_{n}\\llbracket \\varnothing \\vdash \\ast \\rrbracket} \\\\\n\\htmlData{k=V-Sess}{o \\in V[\\kappa]^{W}_{n}\\llbracket \\htmlData{k=V-Sess.exact}{\\{o \\mapsto S'@x\\}} \\vdash S@x \\rrbracket \\iff \\htmlData{k=sty.seqv}{S' \\approx S}} \\\\\n\\htmlData{k=V-Prod}{\\langle v_1, v_2\\rangle \\in V[\\kappa]^{W}_{n}\\llbracket \\htmlData{k=V-Prod.split}{\\Theta_1 \\uplus \\Theta_2} \\vdash T_1 \\otimes T_2 \\rrbracket \\iff v_i \\in V[\\kappa]^{W}_{n}\\llbracket \\Theta_i \\vdash T_i \\rrbracket} \\\\\n\\htmlData{k=V-Sum}{\\mathsf{inj}_i\\,v \\in V[\\kappa]^{W}_{n}\\llbracket \\Theta \\vdash T_1 \\oplus T_2 \\rrbracket \\iff v \\in V[\\kappa]^{W}_{n}\\llbracket \\Theta \\vdash T_i \\rrbracket}\n\\end{array}",
     "caption": "Values hold exactly the ends of their environment. An end value holds its own entry at the same point.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "v-arrow",
     "title": "V at an arrow",
     "rocq": "relation/Relation.v: Varr, Varr_rel",
     "tex": "\\lambda e \\in V[\\kappa]^{W}_{n}\\llbracket \\Theta \\vdash T \\multimap^{u}_{l} U \\rrbracket \\iff \\htmlData{k=V-Arrow.exact}{\\mathsf{dom}\\,\\Theta = \\mathsf{fends}(e)} \\land \\htmlData{k=V-Arrow.lb}{l \\preccurlyeq \\mathsf{heads}\\,\\Theta} \\land \\htmlData{k=V-Arrow.kripke}{\\forall W' \\sqsupseteq W},\\ \\htmlData{k=V-Arrow.level}{j + \\kappa_\\beta \\leq n},\\ \\Theta' \\mathbin{\\#} \\Theta,\\ \\htmlData{k=V-Arrow.ub}{u \\prec F},\\ w \\in V[\\kappa]^{W'}_{j}\\llbracket \\Theta' \\vdash T \\rrbracket.\\ \\htmlData{k=V-Arrow.body}{e[w] \\in E[\\kappa]^{W'}_{j}\\llbracket \\Theta \\cup \\Theta' \\vdash U \\rrbracket^{F}}",
     "caption": "One arrow for both tables. κ_DF reads the body at j < n, κ_L at j ≤ n. Costs, transformers, floors and credits are not read.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "v-thunk",
     "title": "The thunk of O-Spawn",
     "rocq": "relation/Relation.v: Vthunk",
     "tex": "\\lambda e \\in \\mathsf{Vthunk}^{W}_{n}(\\Theta) \\iff \\htmlData{k=V-Arrow.exact}{\\mathsf{dom}\\,\\Theta = \\mathsf{fends}(e)} \\land \\forall W' \\sqsupseteq W,\\ j + \\kappa_\\beta \\leq n,\\ \\Theta' \\mathbin{\\#} \\Theta,\\ w \\in V[\\kappa]^{W'}_{j}\\llbracket \\Theta' \\vdash \\ast \\rrbracket.\\ e[w] \\in E[\\kappa]^{W'}_{j}\\llbracket \\Theta \\cup \\Theta' \\vdash \\ast \\rrbracket^{\\htmlData{k=V-Thunk.empty}{\\varnothing}}",
     "caption": "An arrow ∗ ⊸ ∗ without lower point and without upper point, its body read at the empty future.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "v-box",
     "title": "V at a box",
     "rocq": "relation/Relation.v: Vbody (TBox), Vrel_box_iff",
     "tex": "!e \\in V[\\kappa]^{W}_{n}\\llbracket \\htmlData{k=V-Box.empty}{\\varnothing} \\vdash \\Box(\\forall\\bar\\iota\\,\\bar\\alpha.\\,C.\\,\\ast \\multimap^{u} U) \\rrbracket \\iff \\htmlData{k=V-Box.noends}{\\mathsf{fends}(e) = \\varnothing} \\land \\htmlData{k=V-Box.kripke}{\\forall W' \\sqsupseteq W},\\ \\htmlData{k=V-Box.inst}{\\bar x,\\ W' \\vdash C[\\bar x]},\\ \\htmlData{k=V-Box.hc}{\\bar s\\ \\text{hcontractive}}.\\ \\htmlData{k=V-Box.thunk}{\\mathsf{thunk}(e) \\in V[\\kappa]^{W'}_{n}\\llbracket \\varnothing \\vdash \\ast \\multimap^{u[\\bar x]} U[\\bar s][\\bar x] \\rrbracket}",
     "caption": "A box is in V when its thunk λ_. e[!e] is, at every later world and every instance meeting C, at the same level.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "v-ex",
     "title": "V at an existential",
     "rocq": "relation/Relation.v: Vbody (TEx), Vrel_ex_iff",
     "tex": "v \\in V[\\kappa]^{W}_{n}\\llbracket \\Theta \\vdash \\exists^{l}\\bar\\iota.\\,C.\\,T \\rrbracket \\iff \\htmlData{k=V-Ex.lb}{l \\preccurlyeq \\mathsf{heads}\\,\\Theta} \\land \\htmlData{k=V-Ex.witness}{\\exists \\bar x.\\ W \\vdash C[\\bar x] \\land v \\in V[\\kappa]^{W}_{n}\\llbracket \\Theta \\vdash T[\\bar x] \\rrbracket}",
     "caption": "Some instance in W meets C. ⊥ bounds nothing.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "v-size",
     "title": "Recursion of V",
     "rocq": "relation/Relation.v: tsize, Vtop, sfix",
     "tex": "\\htmlData{k=rel.vsize}{V_n \\text{ by recursion on } (n, \\mathsf{size}\\,T),\\quad \\mathsf{size}(\\Box\\ldots) = 3 + \\mathsf{size}\\,U,\\quad \\text{levels by one } \\mathsf{sfix}}",
     "caption": "For κ_L, V at level n reads E at level n, so V recurses on the size of the type inside a level.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "e-body",
     "title": "The term relation E",
     "rocq": "relation/Relation.v: Ebody, Eind, Etop",
     "tex": "\\begin{array}{l}\n\\htmlData{k=E.zero}{e \\in E[\\kappa]^{W}_{0}\\llbracket \\Theta \\vdash T \\rrbracket^{F}} \\\\\ne \\in E[\\kappa]^{W}_{n{+}1}\\llbracket \\Theta \\vdash T \\rrbracket^{F} \\iff \\htmlData{k=E.kripke}{\\forall W_1 \\sqsupseteq W}. \\\\\n\\quad \\htmlData{k=E.stop}{(\\mathsf{stop})\\ \\mathsf{irred}\\,e \\Rightarrow e \\in V[\\kappa]^{W_1}_{n{+}1}\\llbracket \\Theta \\vdash T \\rrbracket} \\\\\n\\quad \\htmlData{k=E.ready}{(\\mathsf{ready})\\ \\neg\\mathsf{irred}\\,e \\Rightarrow \\mathsf{ready}_{W_1}(\\Theta \\mid F, e)} \\\\\n\\quad \\htmlData{k=E.step}{(\\mathsf{step})\\ e \\xrightarrow{\\alpha} e' \\Rightarrow \\mathsf{Obl}_\\alpha(e')} \\qquad \\htmlData{k=rel.lfp}{\\text{least fixpoint}}\n\\end{array}",
     "caption": "A term either stops at a value in V, or is ready and every step meets its obligation.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "e-obl-admin",
     "title": "Obligations of τ steps",
     "rocq": "relation/Relation.v: o_beta, o_new, o_new_at, o_spawn",
     "tex": "\\begin{array}{ll}\n\\htmlData{k=O-Beta}{\\textsf{O-Beta}} & e' \\text{ at } \\Theta \\\\\n\\htmlData{k=O-New}{\\textsf{O-New}} & \\htmlData{k=O-New.cfresh}{c\\ \\text{fresh for}\\ \\Theta} \\Rightarrow \\htmlData{k=O-New.forall}{\\forall g.\\ \\htmlData{k=O-New.gfresh}{g\\ \\text{fresh for}\\ \\Theta}} \\Rightarrow \\exists S.\\ e' \\text{ at } \\Theta, \\htmlData{k=O-New.dual}{c^{+} : S@g_\\ell,\\ c^{-} : \\overline{S}@\\overline{g_\\ell}} \\\\\n\\htmlData{k=O-NewAt}{\\textsf{O-NewAt}} & \\htmlData{k=O-NewAt.held}{\\Theta(o) = S_0@x},\\ \\exists S.\\ e' \\text{ at } \\Theta, c^{+} : S@x\\cdot\\kappa,\\ c^{-} : \\overline{S}@\\overline{x\\cdot\\kappa} \\\\\n\\htmlData{k=O-Spawn}{\\textsf{O-Spawn}} & \\htmlData{k=O-Spawn.split}{\\Theta = \\Theta_M \\uplus \\Theta_r},\\ \\htmlData{k=O-Spawn.transfer}{\\mathsf{dom}\\,\\Theta_M = M},\\ \\htmlData{k=O-Spawn.thunk}{v \\in \\mathsf{Vthunk}_n(\\Theta_M)},\\ e' \\text{ at } \\Theta_r\n\\end{array}",
     "caption": "Creation places the new channel deterministically. A spawn splits the environment by the transfer set.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "e-obl-msg",
     "title": "Obligations of send and receive",
     "rocq": "relation/Relation.v: o_send, o_recv",
     "tex": "\\begin{array}{ll}\n\\htmlData{k=O-Send}{\\textsf{O-Send}} & \\Theta(o) = S_0@x,\\ \\mathsf{unfold}\\,S_0 = {!}(\\exists^m.U^b);S,\\ \\htmlData{k=O-Send.split}{\\Theta \\setminus o = \\Theta_M \\uplus \\Theta_r},\\ \\htmlData{k=O-Spawn.transfer}{\\mathsf{dom}\\,\\Theta_M = M}, \\\\\n & \\htmlData{k=O-Send.payload}{w \\in V_{n-\\kappa_{give}}\\llbracket \\Theta_M \\vdash U[x\\cdot i]\\rrbracket},\\ e' \\text{ at } \\Theta_r, \\htmlData{k=O-Send.shift}{o : S@x^{+}} \\\\\n\\htmlData{k=O-Recv}{\\textsf{O-Recv}} & \\Theta(o) = S_0@x,\\ \\mathsf{unfold}\\,S_0 = {?}(\\exists^m.U^b);S,\\ \\htmlData{k=O-Recv.forall}{\\forall j + \\kappa_{take} \\leq n,\\ \\Theta_{in} \\mathbin{\\#} \\Theta,\\ w \\in V_j\\llbracket\\Theta_{in} \\vdash U[x\\cdot i]\\rrbracket}. \\\\\n & \\htmlData{k=O-Recv.level}{e' \\in E_j\\llbracket \\Theta[o \\mapsto S@x^{+}] \\cup \\Theta_{in} \\vdash T\\rrbracket^{F}}\n\\end{array}",
     "caption": "The sender gives up exactly the ends of its transfer set. The receiver continues for every incoming value at every lower level.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "e-obl-other",
     "title": "Obligations of close, choice and link",
     "rocq": "relation/Relation.v: o_close, o_select, o_branch, o_link",
     "tex": "\\begin{array}{ll}\n\\htmlData{k=O-Close}{\\textsf{O-Close}} & \\Theta(o) = S_0@x,\\ \\mathsf{unfold}\\,S_0 = \\mathsf{Close},\\ e' \\text{ at } \\Theta \\setminus o \\\\\n\\htmlData{k=O-Select}{\\textsf{O-Select}} & \\mathsf{unfold}\\,S_0 = \\oplus(S_1,S_2),\\ e' \\text{ at } \\Theta[o \\mapsto S_i@\\htmlData{k=pt.sel}{\\overline{x\\cdot\\kappa_i}}] \\\\\n\\htmlData{k=O-Branch}{\\textsf{O-Branch}} & \\mathsf{unfold}\\,S_0 = \\&(S_1,S_2),\\ e' \\text{ at } \\Theta[o \\mapsto S_i@\\htmlData{k=pt.bra}{x\\cdot\\kappa_i}] \\\\\n\\htmlData{k=O-Link}{\\textsf{O-Link}} & \\htmlData{k=O-Link.distinct}{o_1 \\neq o_2},\\ \\htmlData{k=O-Link.dual}{\\Theta(o_1) = S_1@x,\\ \\Theta(o_2) = S_2@\\overline{x},\\ \\mathsf{sdual}\\,S_1\\,S_2},\\ e' \\text{ at } \\Theta \\setminus \\{o_1, o_2\\}\n\\end{array}",
     "caption": "Every obligation reads the subject's own entry, so a frame's ends are never touched.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "rd-term",
     "title": "Readiness of a term",
     "rocq": "relation/Readiness.v: ready_t, below_rest, offered_t",
     "tex": "\\begin{array}{l}\n\\mathsf{ready}_W(\\Theta \\mid F, t) \\iff \\htmlData{k=rd.stable}{\\mathsf{stable}\\,t} \\Rightarrow (\\htmlData{k=rd.value}{(\\forall o.\\ \\neg\\htmlData{k=rd.offered}{\\mathsf{offered}\\,o}) \\Rightarrow t\\ \\text{value}}) \\land (\\htmlData{k=rd.link}{\\mathsf{link}\\,t} \\lor \\htmlData{k=rd.below-rest}{\\mathsf{below\\_rest}}) \\\\\n\\htmlData{k=rd.below-rest}{\\mathsf{below\\_rest}} \\iff \\forall o\\ \\text{offered at } x.\\ \\htmlData{k=rd.below-held}{\\forall o'\\ \\text{held, not offered, at } x'.\\ W \\vdash x \\prec \\overline{x'}} \\land \\htmlData{k=rd.below-future}{\\forall y \\in F.\\ W \\vdash x \\prec y}\n\\end{array}",
     "caption": "A stable reducible term offers some held ends, each below the partner point of every other held end and below the future.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "rd-proc",
     "title": "Readiness of a process",
     "rocq": "relation/Readiness.v: ready_p, above_offered",
     "tex": "\\mathsf{ready}_W(\\Sigma, p) \\iff \\htmlData{k=rd.p-stable}{\\mathsf{stable}\\,p} \\Rightarrow \\mathsf{link}\\,p \\lor \\big(\\htmlData{k=rd.p-term}{(\\text{no offer} \\Rightarrow \\mathsf{terminated}\\,p)} \\land \\htmlData{k=rd.above-offered}{\\forall o \\in \\Sigma\\ \\text{not offered at } x.\\ \\exists o'\\ \\text{offered at } x'.\\ W \\vdash x' \\prec \\overline{x}}\\big)",
     "caption": "A stable process offers some interface end, and every interface end it does not offer has an offered end below its partner point.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "p-body",
     "title": "The process relation P",
     "rocq": "relation/Relation.v: Pbody, Pclauses, Pind",
     "tex": "\\begin{array}{l}\np \\in P[\\kappa]^{W}_{n{+}1}\\llbracket \\Sigma \\vdash T \\rrbracket \\iff \\htmlData{k=P.strict}{\\forall W_1 \\sqsupseteq W,\\ \\mathsf{strict}\\,W_1},\\ \\htmlData{k=P.fuse}{\\forall h\\,D.\\ \\mathsf{fuse\\_ok}\\,h\\,D\\,\\Sigma\\,p} \\Rightarrow \\text{clauses at } W_1,\\ \\mathsf{sdrop}\\,D\\,(h\\,\\Sigma),\\ \\mathsf{pfuse}\\,h\\,D\\,p \\\\\n\\quad \\htmlData{k=P-Stop}{(\\textsf{P-Stop})\\ \\mathsf{pirred}\\,p \\Rightarrow p = (\\varnothing, \\{v\\} \\uplus E),\\ v \\in V\\llbracket\\Sigma \\vdash T\\rrbracket,\\ E \\subseteq \\{\\ast\\}} \\\\\n\\quad \\htmlData{k=P-Ready}{(\\textsf{P-Ready})\\ \\neg\\mathsf{pirred}\\,p \\Rightarrow \\mathsf{ready}_{W_1}(\\Sigma, p)} \\\\\n\\quad \\htmlData{k=P-Step}{(\\textsf{P-Step})\\ \\text{every instrumented step of every lifting meets } \\mathsf{Pobl}} \\qquad \\htmlData{k=rel.lfp}{\\text{least fixpoint}}\n\\end{array}",
     "caption": "P is Kripke over strict later worlds only and closed under fusions of held ends by definition.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "p-fuse",
     "title": "Fusions of held ends",
     "rocq": "relation/Relation.v: fuse_ok, pfuse, sdrop, dpairs",
     "tex": "\\mathsf{fuse\\_ok}\\,h\\,D\\,\\Sigma\\,p \\iff \\htmlData{k=fuse.dcomm}{h(\\overline{o}) = \\overline{h(o)}} \\land \\htmlData{k=fuse.inj}{h\\ \\text{injective on held ends}} \\land \\htmlData{k=fuse.partners}{h(o_2) = \\overline{h(o_1)} \\Rightarrow o_2 = \\overline{o_1} \\lor \\mathsf{ech}(h\\,o_1) \\in D} \\land \\htmlData{k=fuse.D}{D \\mathbin{\\#} h[C]} \\land \\htmlData{k=fuse.dpairs}{\\mathsf{dpairs}\\,D\\,(h\\,\\Sigma)}",
     "caption": "D = ∅ is a renaming, h = id internalizes pairs of Σ. One concept covers renaming, Internalize and the link case of P-Connect.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "p-obl",
     "title": "Obligations of process steps",
     "rocq": "relation/Relation.v: q_tau, q_send, q_recv, send_split, recv_ok, recv_back, recv_env",
     "tex": "\\begin{array}{ll}\n\\htmlData{k=Q-Tau}{\\textsf{Q-Tau}} & p'.1 \\mathbin{\\#} \\mathsf{chans}\\,\\Sigma \\Rightarrow p' \\text{ at } \\Sigma \\text{ after cost } \\kappa(ev) \\\\\n\\htmlData{k=Q-Send}{\\textsf{Q-Send}} & \\Sigma \\setminus o = \\Sigma_v \\uplus \\Sigma_r,\\ \\htmlData{k=Q-Send.theta-e}{\\mathsf{dom}\\,\\Theta_e = M \\cap \\mathsf{ends}(C)},\\ M = \\mathsf{dom}\\,\\Sigma_v \\cup \\mathsf{dom}\\,\\Theta_e,\\ \\htmlData{k=Q-Send.split}{\\mathsf{send\\_split}\\,\\Sigma\\,\\Sigma_e\\,\\Theta_e}, \\\\\n & w \\in V\\llbracket\\Sigma_v \\cup \\Theta_e \\vdash U[x\\cdot i]\\rrbracket,\\ p' \\text{ at } (\\Sigma_r \\cup \\htmlData{k=Q-Send.sigma-e}{\\Sigma_e})[o \\mapsto S@x^{+}] \\\\\n\\htmlData{k=Q-Recv}{\\textsf{Q-Recv}} & \\forall j + \\kappa_{take} \\leq n,\\ \\Theta_2,\\ \\htmlData{k=Q-Recv.ok}{\\mathsf{recv\\_ok}\\,\\Sigma'\\,\\Theta_2},\\ w \\in V_j\\llbracket\\Theta_2 \\vdash U[x\\cdot i]\\rrbracket \\Rightarrow \\\\\n & (p'.1 \\cup \\htmlData{k=Q-Recv.back}{\\mathsf{recv\\_back}\\,\\Sigma'\\,\\Theta_2}, p'.2) \\in P_j\\llbracket \\htmlData{k=Q-Recv.env}{\\mathsf{recv\\_env}\\,\\Sigma'\\,\\Theta_2} \\vdash T\\rrbracket \\\\\n\\htmlData{k=Q-Link}{\\textsf{Q-Close, Q-Select, Q-Branch, Q-Link}} & \\text{as for terms, on } \\Sigma\n\\end{array}",
     "caption": "External messages move restricted ends in and out of the interface. A τ step keeps the interface.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "sj",
     "title": "Semantic judgments ⊨, ⊫",
     "rocq": "compat/SemTyped.v: Grel, sem_typed_at, sf_den, sem_typed; relation/Adequacy.v: sem_ptyped",
     "tex": "\\begin{array}{l}\n\\htmlData{k=sj.at}{\\Theta;\\Delta \\vDash^{X}_W t : T \\iff \\forall n\\,W' \\sqsupseteq W\\,\\Theta'\\,\\gamma.\\ \\htmlData{k=sj.grel}{\\gamma \\in G_n^{W'}\\llbracket\\Theta' \\vdash \\Delta\\rrbracket} \\Rightarrow \\gamma(t) \\in E_n^{W'}\\llbracket \\Theta \\cup \\Theta' \\vdash T\\rrbracket^{X}} \\\\\n\\htmlData{k=sj.term}{\\Theta;\\Delta \\vDash^{F}_W t : T \\iff \\forall \\rho\\,B.\\ \\Theta;\\Delta \\vDash^{\\htmlData{k=sj.den}{\\mathsf{den}_{\\rho,B}(F)}}_W t : T \\qquad (\\mathrel{|\\!\\!\\vDash} \\text{ at } \\kappa_L)} \\\\\n\\htmlData{k=sj.proc}{\\Sigma \\vDash_W p : T \\iff \\forall n.\\ p \\in P_n^W\\llbracket\\Sigma \\vdash T\\rrbracket \\qquad (\\mathrel{|\\!\\!\\vDash}_W \\text{ at } \\kappa_L)}\n\\end{array}",
     "variants": {
      "df": "\\begin{array}{l}\n\\htmlData{k=sj.at}{\\Theta;\\Delta \\vDash^{X}_W t : T \\iff \\forall n\\,W' \\sqsupseteq W\\,\\Theta'\\,\\gamma.\\ \\htmlData{k=sj.grel}{\\gamma \\in G_n^{W'}\\llbracket\\Theta' \\vdash \\Delta\\rrbracket} \\Rightarrow \\gamma(t) \\in E_n^{W'}\\llbracket \\Theta \\cup \\Theta' \\vdash T\\rrbracket^{X}} \\\\\n\\htmlData{k=sj.term}{\\Theta;\\Delta \\vDash^{F}_W t : T \\iff \\forall \\rho\\,B.\\ \\Theta;\\Delta \\vDash^{\\htmlData{k=sj.den}{\\mathsf{den}_{\\rho,B}(F)}}_W t : T} \\\\\n\\htmlData{k=sj.proc}{\\Sigma \\vDash_W p : T \\iff \\forall n.\\ p \\in P_n^W\\llbracket\\Sigma \\vdash T\\rrbracket}\n\\end{array}",
      "live": "\\begin{array}{l}\n\\htmlData{k=sj.at}{\\Theta;\\Delta \\mathrel{|\\!\\!\\vDash}^{X}_W t : T \\iff \\forall n\\,W' \\sqsupseteq W\\,\\Theta'\\,\\gamma.\\ \\htmlData{k=sj.grel}{\\gamma \\in G[\\kappa_L]_n^{W'}\\llbracket\\Theta' \\vdash \\Delta\\rrbracket} \\Rightarrow \\gamma(t) \\in E[\\kappa_L]_n^{W'}\\llbracket \\Theta \\cup \\Theta' \\vdash T\\rrbracket^{X}} \\\\\n\\htmlData{k=sj.term}{\\Theta;\\Delta \\mathrel{|\\!\\!\\vDash}^{F}_W t : T \\iff \\forall \\rho\\,B.\\ \\Theta;\\Delta \\mathrel{|\\!\\!\\vDash}^{\\htmlData{k=sj.den}{\\mathsf{den}_{\\rho,B}(F)}}_W t : T} \\\\\n\\htmlData{k=sj.proc}{\\Sigma \\mathrel{|\\!\\!\\vDash}_W p : T \\iff \\forall n.\\ p \\in P[\\kappa_L]_n^W\\llbracket\\Sigma \\vdash T\\rrbracket}\n\\end{array}"
     },
     "caption": "The semantic judgments quantify over every level, later world and grounding. The static future is read with its variable and ⊥ flag as arbitrary sets.",
     "modes": [
      "df",
      "live",
      "lf"
     ]
    },
    {
     "id": "fu-def",
     "title": "Fuel F^N",
     "rocq": "fuel/Fuel.v: Fdef, FuelE, FLev",
     "modes": [
      "lf"
     ],
     "tex": "\\begin{array}{l}\n\\htmlData{k=fu.zero}{e \\in F^N_0\\llbracket\\ldots\\rrbracket} \\\\\ne \\in F^N_{n+1}\\llbracket \\htmlData{k=fu.rty}{\\sigma} \\triangleright \\htmlData{k=fu.frame}{d} ; \\htmlData{k=fu.reserve}{r} \\rrbracket(\\htmlData{k=fu.Pi}{\\Pi}, \\htmlData{k=fu.phi}{\\varphi}, \\htmlData{k=fu.tk}{tk}) \\iff \\htmlData{k=fu.refill-kripke}{\\forall N' \\geq_{\\mathsf{rle}} N},\\ \\htmlData{k=fu.rename}{g\\ \\text{injective on}\\ \\mathsf{dom}\\,\\Pi, \\mathsf{dom}\\,\\varphi}. \\\\\n\\quad \\htmlData{k=fu.val}{(\\mathsf{val})\\ g(e)\\ \\text{value} \\Rightarrow r \\leq tk \\land g(e) \\in FV^{N'}_{n+1}\\llbracket\\sigma\\rrbracket(g\\Pi, g\\varphi)} \\\\\n\\quad \\htmlData{k=fu.step}{(\\mathsf{step})\\ g(e) \\xrightarrow{\\alpha} e' \\Rightarrow \\mathsf{Fobl}_\\alpha \\text{ at level } n} \\qquad \\htmlData{k=fu.oneclock}{\\text{every step costs one level}}\n\\end{array}",
     "caption": "A per-thread predicate on counters, protocols and tickets. It reads no point, no world and no relation."
    },
    {
     "id": "fu-act",
     "title": "An action on o (F-Wait, F-Tick)",
     "rocq": "fuel/Fuel.v: f_act, fspare, idle, refill",
     "modes": [
      "lf"
     ],
     "tex": "\\mathsf{act}\\,o \\iff \\htmlData{k=F-Wait}{\\neg\\mathsf{idle}(\\Pi\\,o)} \\land o \\in \\mathsf{dom}\\,\\varphi \\land \\htmlData{k=F-Tick}{\\mathsf{fspare}\\,\\Pi\\,\\varphi\\,(\\mathsf{dom}\\,\\varphi \\setminus o)} \\land \\htmlData{k=F-Tick.frame}{1 \\leq d} \\qquad \\htmlData{k=fu.refillop}{\\mathsf{refill}\\,N\\,o\\,\\varphi = \\varphi[o \\mapsto N]\\ \\text{and every other counter} - 1} \\qquad \\htmlData{k=fu.idle}{\\mathsf{idle}\\,S \\iff \\mathsf{unfold}\\,S = \\mathsf{Skip}}",
     "caption": "An action refills its end and ticks every other end of the thread. Each other end that is not idle must have a unit to spare."
    },
    {
     "id": "fu-obl",
     "title": "Fuel obligations",
     "rocq": "fuel/Fuel.v: f_beta, f_new, f_spawn, f_send, f_recv, f_close, f_select, f_branch, f_link",
     "modes": [
      "lf"
     ],
     "tex": "\\begin{array}{ll}\n\\htmlData{k=F-Beta}{\\textsf{F-Beta}} & e' \\text{ at the same state} \\\\\n\\htmlData{k=F-New}{\\textsf{F-New}} & \\htmlData{k=F-New.fresh}{c\\ \\text{fresh for}\\ \\Pi, \\varphi} \\Rightarrow \\exists S.\\ e' \\text{ at } \\Pi + \\{c^{+} : S, c^{-} : \\overline{S}\\},\\ \\htmlData{k=F-New.cnew}{\\varphi + \\{c^{\\pm} \\mapsto N\\}} \\\\\n\\htmlData{k=F-Spawn}{\\textsf{F-Spawn}} & \\htmlData{k=F-Spawn.held}{M \\subseteq \\mathsf{dom}\\,\\varphi},\\ \\htmlData{k=fu.fspare}{\\mathsf{fspare}\\,M},\\ \\htmlData{k=F-Spawn.child}{v\\,\\ast \\in F^N\\llbracket\\mathsf{thread}\\rrbracket(\\Pi|_M, \\htmlData{k=fu.fhand}{(\\varphi - 1)|_M}, \\lceil tk/2\\rceil)},\\ e' \\text{ at } \\Pi \\setminus M, \\varphi \\setminus M, \\htmlData{k=F-Spawn.tickets}{\\lfloor tk/2 \\rfloor} \\\\\n\\htmlData{k=F-Send}{\\textsf{F-Send}} & \\mathsf{act}\\,o,\\ \\htmlData{k=F-Send.notsubj}{M \\subseteq \\mathsf{dom}\\,\\varphi \\setminus o},\\ \\htmlData{k=fu.fspare}{\\mathsf{fspare}\\,M},\\ \\htmlData{k=F-Send.payload}{w \\in FV^N\\llbracket T^{b}\\rrbracket(\\Pi|_M, (\\varphi-1)|_M)},\\ e' \\text{ at } d-1,\\ \\Pi[o \\mapsto S] \\setminus M,\\ \\htmlData{k=fu.refillop}{\\mathsf{refill}\\,N\\,o}(\\varphi \\setminus M) \\\\\n\\htmlData{k=F-Recv}{\\textsf{F-Recv}} & \\mathsf{act}\\,o,\\ \\htmlData{k=F-Recv.forall}{\\forall j \\leq n,\\ \\Pi_i,\\ \\varphi_i,\\ w \\in FV^N_j\\llbracket T^{b}\\rrbracket(\\Pi_i, \\varphi_i)}.\\ e' \\text{ at level } j,\\ \\Pi[o\\mapsto S] \\cup \\Pi_i,\\ \\mathsf{refill}\\,N\\,o\\,\\varphi \\cup \\varphi_i \\\\\n\\htmlData{k=F-Close}{\\textsf{F-Close, F-Select, F-Branch}} & \\mathsf{act}\\,o,\\ \\text{advance } \\Pi\\,o,\\ \\text{tick or refill, frame } d - 1 \\\\\n\\htmlData{k=F-Link}{\\textsf{F-Link}} & \\htmlData{k=F-Link.plink}{\\Pi(o_1), \\Pi(o_2)\\ \\text{dual}},\\ \\{o_1,o_2\\} \\subseteq \\mathsf{dom}\\,\\varphi,\\ \\htmlData{k=F-Link.ticket}{1 \\leq tk},\\ e' \\text{ at } \\Pi \\setminus \\{o_1,o_2\\}, tk - 1\n\\end{array}",
     "caption": "Counters evolve by one update at every index. Hand-overs pass the counter minus one, links spend a ticket."
    },
    {
     "id": "fv",
     "title": "Values at a credited type FV^N",
     "rocq": "fuel/Fuel.v: Vty, Vres",
     "modes": [
      "lf"
     ],
     "tex": "\\begin{array}{l}\n\\htmlData{k=FV-Sess}{o \\in FV\\llbracket (S@x)^{a}\\rrbracket(\\{o : S'\\}, \\{o : f\\}) \\iff S' \\simeq S \\land \\htmlData{k=FV-Sess.counter}{a \\leq f}} \\\\\n\\htmlData{k=FV-Arrow}{\\lambda e \\in FV_n\\llbracket (T^{a_1} \\multimap[c;\\vartheta;h] U^{a_2})^{a}\\rrbracket(\\Pi,\\varphi) \\iff \\htmlData{k=FV-Arrow.exact}{\\mathsf{fends}\\,e = \\mathsf{dom}\\,\\Pi} \\land \\htmlData{k=FV-Arrow.floor}{\\varphi \\geq h + a} \\land {}} \\\\\n\\quad \\htmlData{k=FV-Arrow.body}{\\forall N' \\geq_{\\mathsf{rle}} N,\\ j < n,\\ \\varphi' \\geq h,\\ u \\in FV_j\\llbracket T^{a_1}\\rrbracket,\\ \\mathsf{meets}\\,\\vartheta\\,r\\,tk.\\ e[u] \\in F^{N'}_j\\llbracket U^{a_2} \\triangleright c ; r\\rrbracket(\\Pi \\cup \\Pi_u, \\varphi' \\cup \\varphi_u, tk)} \\\\\n\\htmlData{k=FV-Box}{!e \\in FV_n\\llbracket \\Box(\\ldots)\\rrbracket(\\varnothing,\\varnothing) \\iff \\htmlData{k=FV-Box.noends}{\\mathsf{fends}\\,e = \\varnothing} \\land \\htmlData{k=FV-Box.body}{\\forall N', j < n, \\bar s \\in \\mathsf{sinsts}\\,N', \\mathsf{meets}\\,\\vartheta\\,r\\,tk.\\ e[!e] \\in F^{N'}_j\\llbracket U[\\bar s] \\triangleright c ; r\\rrbracket(\\varnothing,\\varnothing,tk)}} \\\\\n\\htmlData{k=FV-Thread}{v \\in FV\\llbracket\\mathsf{thread}\\rrbracket(\\Pi,\\varphi) \\iff \\Pi = \\varphi = \\varnothing} \\qquad \\otimes, \\oplus, \\exists:\\ \\text{credit added to the parts, maps split}\n\\end{array}",
     "caption": "By recursion on the type. Points, bounds and constraints are not read."
    },
    {
     "id": "fu-fsem",
     "title": "fsem and the semantic cost judgment",
     "rocq": "fuel/Fuel.v: fsem; cost/CostSem.v: csem, thfuel, gfuel",
     "modes": [
      "lf"
     ],
     "tex": "\\htmlData{k=fu.fsem}{\\mathsf{fsem}\\,N\\,\\Pi\\,e \\iff \\exists tk\\,\\forall n.\\ e \\in F^N_n\\llbracket\\mathsf{thread} \\triangleright \\infty ; 0\\rrbracket(\\Pi, N \\text{ on } \\mathsf{dom}\\,\\Pi, tk)} \\qquad \\htmlData{k=cs.csem}{\\Theta;\\Delta \\vDash^{N} e : T^{a} \\triangleright c ; \\vartheta}",
     "caption": "Every held end starts at N, at one ticket count for every index. csem is the cost half of the merged judgment read semantically."
    },
    {
     "id": "sp-state",
     "title": "Soup states",
     "rocq": "soup/State.v: hold, lfstate",
     "modes": [
      "lf"
     ],
     "tex": "\\htmlData{k=sp.state}{a = (q, K, tk)} \\qquad \\htmlData{k=sp.hold}{K : o \\mapsto (t, x, f)} \\qquad \\htmlData{k=sp.tk}{tk : t \\mapsto \\mathbb{N}}",
     "caption": "The configuration, the ownership (holder, point, counter of each held end) and the tickets per thread, fixed outside the index."
    },
    {
     "id": "sp-inv",
     "title": "The soup S^{N,W}_n",
     "rocq": "soup/State.v: soup_gen, soup/Soup.v: soup_inv, Soup",
     "modes": [
      "lf"
     ],
     "tex": "\\begin{array}{l}\na \\in S^{N,W}_n\\llbracket\\Sigma \\vdash T\\rrbracket \\iff \\htmlData{k=sp.exists}{\\exists A\\,\\Pi\\,U}. \\\\\n\\quad \\htmlData{k=sp.prim}{\\mathsf{prim}\\,T} \\quad \\htmlData{k=sp.rel}{\\forall t.\\ q(t) \\in E[\\kappa_L]^W_n\\llbracket A|_t \\vdash U_t\\rrbracket^{\\varnothing}} \\quad \\htmlData{k=sp.ty}{U_t \\in \\{T, \\ast\\}} \\\\\n\\quad \\htmlData{k=sp.fuel}{\\forall t.\\ q(t) \\in F^N_n\\llbracket\\mathsf{thread}\\rrbracket(\\Pi|_t, \\mathsf{ctrs}\\,K\\,t, tk_t)} \\quad \\htmlData{k=sp.pts}{\\text{points of } A = \\text{points of } K} \\quad \\htmlData{k=sp.dom}{\\mathsf{dom}\\,\\Pi = \\mathsf{dom}\\,K} \\\\\n\\quad \\htmlData{k=sp.owner}{\\text{holders exist}} \\quad \\htmlData{k=sp.closed}{o \\in K \\Rightarrow \\mathsf{ech}\\,o \\in C \\lor o \\in \\Sigma} \\quad \\htmlData{k=sp.pair}{o \\in K,\\ \\mathsf{ech}\\,o \\in C \\Rightarrow \\overline{o} \\in K} \\\\\n\\quad \\htmlData{k=sp.sdual}{\\text{internal partners at } x, \\overline{x},\\ \\text{types dual up to annotations}} \\quad \\htmlData{k=sp.pdual}{\\Pi(\\overline{o}) \\simeq \\overline{\\Pi(o)}} \\\\\n\\quad \\htmlData{k=sp.sig}{\\Sigma(o) = A(o)} \\quad \\htmlData{k=sp.psig}{\\Sigma(o) = (S, x) \\Rightarrow \\Pi(o) = S} \\quad \\htmlData{k=sp.fin}{\\text{every counter finite}}\n\\end{array}",
     "caption": "Per index, every thread is live and fueled at its part of A and Π. Ends, points and counters come from K and are the same at every index."
    },
    {
     "id": "sp-lf",
     "title": "The lock-free semantic judgment ⊪",
     "rocq": "soup/Soup.v: lf_sem, lf_next",
     "modes": [
      "lf"
     ],
     "tex": "\\htmlData{k=sp.lfsem}{\\Sigma \\Vvdash_W p : T \\iff \\htmlData{k=sp.exists-before-forall}{\\exists N\\,a.\\ \\mathsf{erase}(q_a) = p \\land \\forall n}.\\ a \\in S^{N,W}_n\\llbracket\\Sigma \\vdash T\\rrbracket} \\qquad \\htmlData{k=sp.next}{\\mathsf{lf\\_next}\\,N\\,a\\,ev\\,q'}",
     "caption": "The soup alone. The state is chosen once, before the index, and follows events by one index-free update."
    }
   ]
  },
  {
   "id": "theorems",
   "title": "Theorems",
   "intro": "The main results listed in CheckAll.v, each closed under the global context. Adequacy turns the semantic judgments into safety properties, the fundamental theorems turn typing into the semantic judgments, and soundness composes the two.",
   "blocks": [
    {
     "id": "th-adequacy",
     "title": "Adequacy",
     "rocq": "relation/Adequacy.v: adequacy, live_adequacy, adequacy_gen",
     "modes": [
      "df",
      "live"
     ],
     "tex": "\\begin{array}{l}\n\\htmlData{k=th.adequacy}{\\htmlData{k=w.strict}{\\mathsf{strict}\\,W} \\land \\varnothing \\vDash_W p : T \\;\\Longrightarrow\\; \\mathsf{deadlock\\_free}\\,p} \\\\\n\\htmlData{k=th.live-adequacy}{\\mathsf{strict}\\,W \\land \\varnothing \\mathrel{|\\!\\!\\vDash}_W p : T \\;\\Longrightarrow\\; \\mathsf{deadlock\\_free}\\,p \\land \\mathsf{no\\_tau\\_divergence}\\,p} \\\\\n\\htmlData{k=th.adequacy-gen}{\\forall \\kappa.\\ \\mathsf{strict}\\,W \\land \\forall n.\\ p \\in P[\\kappa]^W_n\\llbracket\\varnothing \\vdash T\\rrbracket \\;\\Longrightarrow\\; \\mathsf{deadlock\\_free}\\,p}\n\\end{array}",
     "caption": "A closed process in P at every level is deadlock free, for every cost table. In κ_L it also has no τ-divergence."
    },
    {
     "id": "th-lf-adequacy",
     "title": "Lock-free adequacy",
     "rocq": "soup/LFAdequacy.v: lf_adequacy, lf_thread_progress; soup/SoupTau.v: soup_no_tau_divergence; soup/SoupRun.v: lfsoup_step",
     "modes": [
      "lf"
     ],
     "tex": "\\begin{array}{l}\n\\htmlData{k=th.lf-adequacy}{\\htmlData{k=w.lfworld}{\\mathsf{lfworld}\\,W} \\land \\varnothing \\Vvdash_W p : T \\;\\Longrightarrow\\; \\mathsf{lock\\_free}\\,p} \\\\\n\\htmlData{k=th.lf-thread-progress}{\\mathsf{lfworld}\\,W \\land \\varnothing \\Vvdash_W p : T \\;\\Longrightarrow\\; \\text{every weakly fair maximal run makes every thread progress}} \\\\\n\\htmlData{k=th.soup-no-tau}{(\\forall n.\\ a \\in S^{N,W}_n\\llbracket\\varnothing \\vdash T\\rrbracket) \\;\\Longrightarrow\\; \\mathsf{no\\_tau\\_divergence}(\\mathsf{erase}\\,q_a)} \\\\\n\\htmlData{k=th.lfsoup-step}{a \\in S^{N,W}_{n+1}\\llbracket\\varnothing \\vdash T\\rrbracket \\land q_a \\xrightarrow{ev} q' \\;\\Longrightarrow\\; \\mathsf{lf\\_next}\\,N\\,a\\,ev\\,q' \\in S^{N,W}_n\\llbracket\\varnothing \\vdash T\\rrbracket}\n\\end{array}",
     "caption": "The soup alone gives lock freedom in a well-founded strict world."
    },
    {
     "id": "th-fund-term",
     "title": "Fundamental theorems for terms",
     "rocq": "static/Fundamental.v: fundamental, fundamental_typed; static/LiveFundamental.v: live_fundamental, live_fundamental_typed",
     "modes": [
      "df",
      "live",
      "lf"
     ],
     "tex": "\\begin{array}{l}\n\\htmlData{k=th.fundamental}{\\mathsf{strict}\\,W \\land \\Theta ; \\varnothing ; \\Delta \\vdash^{F}_{W} t : T \\;\\Longrightarrow\\; \\Theta ; \\Delta \\vDash^{F}_W t : T} \\\\\n\\htmlData{k=th.fundamental-typed}{\\mathsf{strict}\\,W \\land \\Theta ; \\varnothing ; \\Delta \\vdash^{F}_{W,N} t : T^{a} \\triangleright c ; \\vartheta \\;\\Longrightarrow\\; \\Theta_{df} ; \\Delta_{df} \\vDash^{F}_W t : T_{df}} \\\\\n\\htmlData{k=th.live-fundamental}{\\mathsf{strict}\\,W \\land \\Theta ; \\varnothing ; \\Delta \\vdash^{F}_{W} t : T \\land \\htmlData{k=guard.judg}{\\varnothing \\vdash\\!\\triangleright t} \\;\\Longrightarrow\\; \\Theta ; \\Delta \\mathrel{|\\!\\!\\vDash}^{F}_W t : T} \\\\\n\\htmlData{k=th.live-fundamental-typed}{\\mathsf{strict}\\,W \\land \\Theta ; \\varnothing ; \\Delta \\vdash^{F}_{W,N} t : T^{a} \\triangleright c ; \\vartheta \\land \\varnothing \\vdash\\!\\triangleright t \\;\\Longrightarrow\\; \\Theta_{df} ; \\Delta_{df} \\mathrel{|\\!\\!\\vDash}^{F}_W t : T_{df}}\n\\end{array}",
     "caption": "Typing implies the semantic term judgment. The live versions add the guard."
    },
    {
     "id": "th-fund-proc",
     "title": "Fundamental theorems for processes",
     "rocq": "static/FundamentalProc.v: fundamental_proc, live_fundamental_proc; soup/LFTyped.v: lf_fundamental",
     "modes": [
      "df",
      "live",
      "lf"
     ],
     "tex": "\\begin{array}{l}\n\\htmlData{k=th.fundamental-proc}{\\mathsf{strict}\\,W \\land \\Sigma \\vdash_W p : T \\;\\Longrightarrow\\; \\Sigma \\vDash_W p : T} \\\\\n\\htmlData{k=th.live-fundamental-proc}{\\mathsf{strict}\\,W \\land \\Sigma \\vdash_W p : T \\land \\htmlData{k=guard.proc}{\\vdash\\!\\triangleright p} \\;\\Longrightarrow\\; \\Sigma \\mathrel{|\\!\\!\\vDash}_W p : T} \\\\\n\\htmlData{k=th.lf-fundamental}{\\mathsf{strict}\\,W \\land \\Sigma \\Vdash^{N}_W p : T \\;\\Longrightarrow\\; \\Sigma \\Vvdash_W p : T}\n\\end{array}",
     "caption": "One induction on process typing per judgment, using the semantic P-Term and P-Connect."
    },
    {
     "id": "th-compose",
     "title": "Semantic composition rules",
     "rocq": "compat/PTerm.v: sem_p_term; compat/ConnectP.v: sem_p_connect; soup/LFCompose.v: lf_p_term, lf_p_connect",
     "modes": [
      "df",
      "live",
      "lf"
     ],
     "tex": "\\begin{array}{l}\n\\htmlData{k=th.sem-p-term}{\\mathsf{prim}\\,T \\land \\htmlData{k=th.sth}{\\mathsf{sth}\\,\\Theta\\,\\Sigma\\,\\Theta_B\\,C} \\land t \\in E[\\kappa]^W_n\\llbracket\\Theta \\vdash T\\rrbracket^{\\varnothing} \\;\\Longrightarrow\\; (C, \\{t\\}) \\in P[\\kappa]^W_n\\llbracket\\Sigma \\vdash T\\rrbracket} \\\\\n\\htmlData{k=th.sem-p-connect}{\\mathsf{prim}\\,T \\land p_1 \\in P_n^{W_1}\\llbracket\\Sigma_1 \\cup \\Sigma_C \\vdash T\\rrbracket \\land p_2 \\in P_n^{W_2}\\llbracket\\Sigma_2 \\cup \\Sigma_D \\vdash \\ast\\rrbracket \\land \\mathsf{conn} \\;\\Longrightarrow\\; p_1 \\parallel_{\\Sigma_C} p_2 \\in P_n^{W_1 \\sqcup W_2}\\llbracket\\Sigma_1 \\cup \\Sigma_2 \\vdash T\\rrbracket} \\\\\n\\htmlData{k=th.lf-p-term}{\\text{premises of lf\\_term} \\land \\mathsf{strict}\\,W \\;\\Longrightarrow\\; \\Sigma \\Vvdash_W (C_0, \\{t\\}) : T}\n\\end{array}",
     "caption": "P-Term and P-Connect hold semantically at every level and every cost table. The LF versions are lemmas about the soup."
    },
    {
     "id": "th-bind",
     "title": "The bind lemma",
     "rocq": "compat/Bind.v: Erel_bind",
     "modes": [
      "df",
      "live",
      "lf"
     ],
     "tex": "\\htmlData{k=th.Erel-bind}{e \\in E^W_n\\llbracket\\Theta_1 \\vdash T\\rrbracket^{F \\cup \\mathsf{heads}\\,\\Theta_2} \\land \\big(\\forall W' \\sqsupseteq W, j \\leq n, v \\in V^{W'}_j\\llbracket\\Theta_v \\vdash T\\rrbracket.\\ f[v] \\in E^{W'}_j\\llbracket\\Theta_v \\cup \\Theta_2 \\vdash U\\rrbracket^{F}\\big) \\;\\Longrightarrow\\; f[e] \\in E^W_n\\llbracket\\Theta_1 \\cup \\Theta_2 \\vdash U\\rrbracket^{F}}",
     "caption": "One bind lemma for every cost table. The hole's future holds the heads of the frame's environment."
    },
    {
     "id": "th-sound",
     "title": "Soundness",
     "rocq": "static/FundamentalProc.v: soundness, live_soundness, soundness_source; soup/LFTyped.v: lf_soundness; soup/LFCompose.v: lf_soundness_source",
     "modes": [
      "df",
      "live",
      "lf"
     ],
     "tex": "\\begin{array}{l}\n\\htmlData{k=th.soundness}{\\mathsf{strict}\\,W \\land \\varnothing \\vdash_W p : T \\;\\Longrightarrow\\; \\mathsf{deadlock\\_free}\\,p} \\\\\n\\htmlData{k=th.live-soundness}{\\mathsf{strict}\\,W \\land \\varnothing \\vdash_W p : T \\land \\vdash\\!\\triangleright p \\;\\Longrightarrow\\; \\mathsf{deadlock\\_free}\\,p \\land \\mathsf{no\\_tau\\_divergence}\\,p} \\\\\n\\htmlData{k=th.soundness-source}{\\mathsf{strict}\\,W \\land \\mathsf{prim}\\,T \\land \\varnothing ; \\varnothing ; \\varnothing \\vdash^{\\varnothing}_W t : T \\;\\Longrightarrow\\; \\mathsf{deadlock\\_free}(\\varnothing, \\{t\\})} \\\\\n\\htmlData{k=th.lf-soundness}{\\mathsf{lfworld}\\,W \\land \\varnothing \\Vdash^{N}_W p : T \\;\\Longrightarrow\\; \\mathsf{lock\\_free}\\,p} \\\\\n\\htmlData{k=th.lf-soundness-source}{\\mathsf{lfworld}\\,W \\land \\varnothing \\vdash\\!\\triangleright t \\land \\mathsf{prim}\\,T \\land \\varnothing;\\varnothing;\\varnothing \\vdash^{\\varnothing}_{W,N} t : T^{a} \\triangleright c ; \\vartheta \\land \\mathsf{meets}\\,\\vartheta\\,0\\,tk \\;\\Longrightarrow\\; \\mathsf{lock\\_free}(\\varnothing, \\{t\\})}\n\\end{array}",
     "caption": "Typing implies the safety property. Source programs need no creation constraint."
    },
    {
     "id": "th-conserv",
     "title": "Conservativity and live ⊆ DF",
     "rocq": "static/Conservativity.v: conservative, typed_dftyped, dftyped_typed; compat/LiveDF.v: live_sub_df",
     "modes": [
      "df",
      "live",
      "lf"
     ],
     "tex": "\\begin{array}{l}\n\\htmlData{k=th.conservative}{(\\exists a\\,c\\,\\vartheta.\\ \\Theta_{df};\\Gamma;\\Delta_{df} \\vdash^{F}_{W,\\infty} e : T_{df}^{a} \\triangleright c ; \\vartheta) \\iff \\Theta_{df};\\Gamma;\\Delta_{df} \\vdash^{F}_{W} e : T_{df}} \\\\\n\\htmlData{k=th.typed-dftyped}{\\Theta;\\Gamma;\\Delta \\vdash^{F}_{W,N} e : T^{a} \\triangleright c ; \\vartheta \\;\\Longrightarrow\\; \\Theta_{df};\\Gamma;\\Delta_{df} \\vdash^{F}_W e : T_{df}} \\\\\n\\htmlData{k=th.live-sub-df}{\\htmlData{k=th.tshape}{\\mathsf{tshape}\\,T} \\land \\varnothing \\mathrel{|\\!\\!\\vDash}_W p : T \\;\\Longrightarrow\\; \\varnothing \\vDash_W p : T}\n\\end{array}",
     "caption": "DF typing is the merged judgment at N = ∞, and erasing annotations of any derivation gives a DF derivation."
    },
    {
     "id": "th-cost",
     "title": "Cost",
     "rocq": "cost/CostFund.v: cost_fundamental, fsem_of_cost",
     "modes": [
      "lf"
     ],
     "tex": "\\begin{array}{l}\n\\htmlData{k=th.cost-fundamental}{\\Theta;\\Gamma;\\Delta \\vdash^{F}_{W,N} e : T^{a} \\triangleright c ; \\vartheta \\;\\Longrightarrow\\; \\htmlData{k=cs.csem}{\\Theta;\\Delta \\vDash^{N} e : T^{a} \\triangleright c ; \\vartheta}} \\\\\n\\htmlData{k=th.fsem-of-cost}{\\Theta;\\varnothing;\\varnothing \\vdash^{\\varnothing}_{W,N} e : T^{a} \\triangleright c ; \\vartheta \\land \\mathsf{prim}\\,T \\land \\text{credits of } \\Theta \\leq N \\land \\mathsf{meets}\\,\\vartheta\\,0\\,tk \\;\\Longrightarrow\\; \\htmlData{k=fu.fsem}{\\mathsf{fsem}\\,N\\,(\\mathsf{sty} \\langle\\$\\rangle \\Theta)\\,e}}\n\\end{array}",
     "caption": "The cost half of the merged judgment. A typed closed thread has fuel with every end at N."
    }
   ]
  }
 ],
 "notes": {
  "syn.var": {
   "title": "Variable",
   "what": "A variable, written as a de Bruijn index that counts the binders between it and its binder.",
   "why": "A plain term former. De Bruijn indices make substitution and renaming need no fresh names.",
   "breaks": "Nothing. It is a definition.",
   "example": "λ x is the identity, with x the index 0.",
   "rocq": "lang/Syntax.v: Var"
  },
  "syn.unit": {
   "title": "Unit value ∗",
   "what": "The unit value ∗. It carries no information and holds no end.",
   "why": "A plain term former. Close, link and spawn return ∗, and a spawned thread ends as ∗.",
   "breaks": "Nothing. It is a definition.",
   "example": "close o reduces to ∗.",
   "rocq": "lang/Syntax.v: EUnit"
  },
  "syn.end": {
   "title": "End value o",
   "what": "The value o names one end of a channel. It is the only place a channel appears in a term.",
   "why": "Each end has its own name c⁺ or c⁻. A select or branch hands back the same name, so running a program never needs to know where an end sits in the order.",
   "breaks": "Nothing. It is a definition.",
   "example": "c⁺ and c⁻ are the two values new returns.",
   "rocq": "lang/Syntax.v: Chan"
  },
  "syn.lam": {
   "title": "λ-abstraction",
   "what": "A one-argument closure. It suspends evaluation, so no evaluation frame reaches under it.",
   "why": "Every value of arrow type is a λ. The value relation then has one case per type and no case for built-in constants.",
   "breaks": "Nothing. It is a definition.",
   "example": "λx. send x is the send function k_send.",
   "rocq": "lang/Syntax.v: Lam"
  },
  "syn.app": {
   "title": "Application",
   "what": "Application, evaluated left to right. A β step fires when both sides are values.",
   "why": "A plain term former. Calling a closure is how a thread runs code it received or built.",
   "breaks": "Nothing. It is a definition.",
   "example": "(λx. e) v steps to e with v for x.",
   "rocq": "lang/Syntax.v: App, lang/Semantics.v: t_act_app"
  },
  "syn.pair": {
   "title": "Pair",
   "what": "A pair, evaluated left to right.",
   "why": "A plain term former. Send takes a pair of payload and end, and receive returns one.",
   "breaks": "Nothing. It is a definition.",
   "example": "send takes ⟨v, o⟩.",
   "rocq": "lang/Syntax.v: Pair"
  },
  "syn.letu": {
   "title": "Unit elimination",
   "what": "let ∗ = e₁ in e₂ runs e₁ to ∗ and then runs e₂.",
   "why": "A plain term former. It sequences two computations when the first returns nothing, such as two closes.",
   "breaks": "Nothing. It is a definition.",
   "example": "let ∗ = close c in close d closes c and then d.",
   "rocq": "lang/Syntax.v: LetU"
  },
  "syn.letp": {
   "title": "Pair elimination",
   "what": "let ⟨a, b⟩ = e₁ in e₂ splits a pair into two variables.",
   "why": "A plain term former. It is the only way to take a pair apart, for example the value and continuation end a receive returns.",
   "breaks": "Nothing. It is a definition.",
   "example": "let ⟨v, c⟩ = recv c in e receives a value and keeps the end.",
   "rocq": "lang/Syntax.v: LetP"
  },
  "syn.let": {
   "title": "Primitive let",
   "what": "let a = e₁ in e₂ evaluates e₁ and substitutes its value into e₂. It builds no closure.",
   "why": "A let is no closure, so it may keep every end of its context, however unrelated their points are. No typing rule then has to recognize a λ applied to a value as a let.",
   "breaks": "Written as (λa. e₂) e₁, the λ must bound all the ends it captures by one lower point. After let ⟨a, a′⟩ = new in e the two ends of the fresh channel have no common lower point, and the program would not type.",
   "example": "let p = force mk ∗ in e keeps every end of the context in e.",
   "rocq": "lang/Syntax.v: ELet, lang/Semantics.v: t_act_let"
  },
  "syn.inj": {
   "title": "Injection",
   "what": "inj₁ or inj₂ of a value. Branch returns its end inside an injection.",
   "why": "A plain term former. Sums let branch report which choice arrived.",
   "breaks": "Nothing. It is a definition.",
   "example": "branch o steps to inj₂ o when the partner selected the second branch.",
   "rocq": "lang/Syntax.v: Inj1, Inj2"
  },
  "syn.case": {
   "title": "Case",
   "what": "case e (a.e₁) (a.e₂) runs e₁ or e₂ depending on the injection, binding its content to a.",
   "why": "A plain term former. It consumes the result of branch.",
   "breaks": "Nothing. It is a definition.",
   "example": "case (branch o) (a. close a) (a. close a).",
   "rocq": "lang/Syntax.v: Case"
  },
  "syn.box": {
   "title": "Box !e",
   "what": "A recursive thunk value. Its body may refer to the box itself, and force (!e) runs the body with the box for itself.",
   "why": "Recursion and replication come from one former. A box holds no end, so copying it is safe.",
   "breaks": "Nothing. It is a definition.",
   "example": "!(f = λx. let ⟨v, x′⟩ = recv x in force f x′) is a server loop.",
   "rocq": "lang/Syntax.v: EBox"
  },
  "syn.new": {
   "title": "new_ℓ",
   "what": "Creates a channel at a fresh point of family ℓ and returns its two ends ⟨c⁺, c⁻⟩. Programs with one family write plain new.",
   "why": "The family label picks which order facts the fresh point gets. Running the program ignores it.",
   "breaks": "Without families, two channels created by new could never be ordered against each other. A client and a server that use two fresh channels in a fixed order would not type.",
   "example": "let ⟨a, a′⟩ = new₀ in e.",
   "rocq": "lang/Syntax.v: ENew"
  },
  "syn.op": {
   "title": "Saturated operator",
   "what": "k e applies a primitive k to one argument. The argument is evaluated first, then the primitive acts.",
   "why": "A primitive is never a value on its own. Every value of arrow type is then a λ, and the value relation needs no case per primitive.",
   "breaks": "With primitives as values, the value relation at arrow types would need one extra case for each primitive, with its own proof obligations.",
   "example": "send ⟨∗, o⟩ applies send to a pair.",
   "rocq": "lang/Syntax.v: Op"
  },
  "prim.send": {
   "title": "send",
   "what": "send ⟨v, o⟩ emits v on o and returns o. Its step records the set of ends that v carries.",
   "why": "The recorded set tells who owns which end after the message, without looking at the program again.",
   "breaks": "Nothing. It is a definition.",
   "example": "close (send ⟨∗, c⟩) sends unit and then closes.",
   "rocq": "lang/Syntax.v: PSend, lang/Semantics.v: t_act_send"
  },
  "prim.recv": {
   "title": "recv",
   "what": "recv o takes any value v and returns ⟨v, o⟩.",
   "why": "A receive accepts whatever the partner sends. The type, not the step, says what may arrive.",
   "breaks": "Nothing. It is a definition.",
   "example": "let ⟨u, b⟩ = recv b in e in a client loop.",
   "rocq": "lang/Syntax.v: PRecv"
  },
  "prim.close": {
   "title": "close",
   "what": "close o meets close ō in the partner thread and returns ∗. The channel then disappears.",
   "why": "A plain primitive. Every protocol ends with a close, so both sides know the channel is finished.",
   "breaks": "Nothing. It is a definition.",
   "example": "close c⁺ in one thread and close c⁻ in another.",
   "rocq": "lang/Syntax.v: PClose"
  },
  "prim.select": {
   "title": "select_i",
   "what": "select_i o offers branch i on o and returns o. i is false for the first branch and true for the second.",
   "why": "The point where the end continues depends on i, so the two branches can be ordered separately.",
   "breaks": "Nothing. It is a definition.",
   "example": "select_true o.",
   "rocq": "lang/Syntax.v: PSel"
  },
  "prim.branch": {
   "title": "branch",
   "what": "branch o receives a choice i and returns inj_i o.",
   "why": "A plain primitive, the partner of select. The injection tells the program which branch the partner chose.",
   "breaks": "Nothing. It is a definition.",
   "example": "case (branch o) (a. e₁) (a. e₂).",
   "rocq": "lang/Syntax.v: PBra"
  },
  "prim.link": {
   "title": "link",
   "what": "link ⟨o₁, o₂⟩ joins two ends and returns ∗. Whoever held the partner of o₁ now holds o₂.",
   "why": "A link forwards a conversation without copying messages. It costs no action, and in the lock-free system it spends one link ticket.",
   "breaks": "Nothing. It is a definition.",
   "example": "link ⟨c⁺, d⁻⟩.",
   "rocq": "lang/Syntax.v: PLink"
  },
  "prim.spawn": {
   "title": "spawn",
   "what": "spawn v starts a new thread running v ∗ and returns ∗. Its step records the ends of v.",
   "why": "The recorded set fixes which ends go to the child and which stay with the parent.",
   "breaks": "Nothing. It is a definition.",
   "example": "spawn (λu. let ∗ = u in close d′).",
   "rocq": "lang/Syntax.v: PSpawn"
  },
  "prim.force": {
   "title": "force",
   "what": "force (!e) runs the body e with the box itself in place of its self variable.",
   "why": "A plain primitive. It is how a box is used, once per call, and how a loop calls itself again.",
   "breaks": "Nothing. It is a definition.",
   "example": "force f ⟨a, b⟩ runs the loop again.",
   "rocq": "lang/Syntax.v: PForce"
  },
  "prim.newat": {
   "title": "new_κ (anchored creation)",
   "what": "new_κ o takes a held end o, returns it untouched, and creates a channel at the field x·κ of the point x of o. The result is ⟨o, ⟨c⁺, c⁻⟩⟩.",
   "why": "A channel that must sit next to a held end is created at a field of that end, so no program names a point. The field is the one a message on o uses for its payload, so a channel created to be sent on o lands where the receiver expects it.",
   "breaks": "Without anchors a function that creates a channel between two existing ones would need a point parameter, and programs would have to mention points.",
   "example": "let ⟨c, ⟨d, d′⟩⟩ = new₀ c in e.",
   "rocq": "lang/Syntax.v: PNewAt, lang/Semantics.v: t_act_new_at"
  },
  "syn.values": {
   "title": "Values",
   "what": "Unit, an end, a λ, a box, and pairs and injections of values.",
   "why": "Primitives are not values, so every value of arrow type is a λ.",
   "breaks": "Nothing. It is a definition.",
   "example": "⟨∗, c⁺⟩ is a value.",
   "rocq": "lang/Syntax.v: is_val"
  },
  "syn.consts": {
   "title": "Constants",
   "what": "The functions of GV such as send and new are λ-terms over the primitives.",
   "why": "A function like send passed as an argument is just a λ, and it types like any λ.",
   "breaks": "Without them a program that passes send to a higher-order function would need primitives as values.",
   "example": "k_new = λx. let ∗ = x in new.",
   "rocq": "lang/Syntax.v: k_send … k_new_at"
  },
  "end.cend": {
   "title": "End",
   "what": "An end c⁺ or c⁻ of channel c. Environments have one entry per end.",
   "why": "The two ends have independent names. A select or branch keeps the name of its end, so the two ends of a channel never share one name with a side bit.",
   "breaks": "Nothing. It is a definition.",
   "example": "new returns ⟨c⁺, c⁻⟩.",
   "rocq": "lang/Syntax.v: cend"
  },
  "end.dual": {
   "title": "Partner end ō",
   "what": "The other end of the same channel.",
   "why": "A send on o meets a receive on ō, so every synchronizing rule pairs an end with its partner.",
   "breaks": "Nothing. It is a definition.",
   "example": "A send on c⁺ meets a receive on c⁻.",
   "rocq": "lang/Syntax.v: edual"
  },
  "end.ech": {
   "title": "Channel of an end",
   "what": "The channel name of an end.",
   "why": "Restricted channels and the subjects of an offer are sets of channels, not of ends.",
   "breaks": "Nothing. It is a definition.",
   "example": "ech c⁻ = c.",
   "rocq": "lang/Syntax.v: ech"
  },
  "syn.fends": {
   "title": "fends",
   "what": "The ends a term mentions.",
   "why": "A closure or a box owns exactly the ends its code mentions, and a send or spawn moves exactly the ends of the value that leaves.",
   "breaks": "Nothing. It is a definition.",
   "example": "fends (λ_. close a) = {a}.",
   "rocq": "lang/Syntax.v: fends"
  },
  "syn.fchans": {
   "title": "fchans",
   "what": "The channels a term mentions.",
   "why": "A new channel must not clash with a channel any thread mentions.",
   "breaks": "Nothing. It is a definition.",
   "example": "fchans ⟨c⁺, d⁻⟩ = {c, d}.",
   "rocq": "lang/Syntax.v: fchans"
  },
  "proc.proc": {
   "title": "Process (C, E)",
   "what": "C is the set of restricted channels, E a multiset of threads.",
   "why": "A plain definition. A channel in C has both ends inside the process, a channel outside C talks to the environment.",
   "breaks": "Nothing. It is a definition.",
   "example": "({c}, {close c⁺, close c⁻}).",
   "rocq": "lang/Syntax.v: proc"
  },
  "proc.config": {
   "title": "Configuration",
   "what": "A finite map from thread identifiers to terms, over a set C of restricted channels.",
   "why": "Fairness and lock freedom speak about one thread across many steps, so threads need names.",
   "breaks": "Nothing. It is a definition.",
   "example": "(∅, {0 ↦ main}).",
   "rocq": "lang/Process.v: config"
  },
  "proc.erase": {
   "title": "erase",
   "what": "Forgets the thread identifiers.",
   "why": "Process steps are defined once, on configurations. The steps of a process are the steps of any configuration that erases to it.",
   "breaks": "Nothing. It is a definition.",
   "example": "erase (C, {0 ↦ e, 1 ↦ f}) = (C, {e, f}).",
   "rocq": "lang/Process.v: erase"
  },
  "pt.const": {
   "title": "Constant root a",
   "what": "A root known to the world with facts of its own.",
   "why": "The channels a component shares with its environment exist before the program runs. Constants give their points, and the world states their facts directly.",
   "breaks": "Nothing. It is a definition.",
   "example": "Two constants 1 and 2 with the fact 1 ≺ 2̄.",
   "rocq": "types/Points.v: NConst"
  },
  "pt.gen": {
   "title": "Generated root g_ℓ",
   "what": "A root of family ℓ, created at run time by new_ℓ. It obeys the laws Λ_ℓ of the world.",
   "why": "A fresh point gets its facts from the laws of its family, never from the run. Every point created by new_ℓ is ordered the same way.",
   "breaks": "If the facts of a fresh point were chosen during the run, the order could change from run to run, and lock freedom could not rank waiting threads by one fixed order.",
   "example": "new₀ places c⁺ at a fresh root g of family 0.",
   "rocq": "types/Points.v: NGen"
  },
  "pt.var": {
   "title": "Point variable ι",
   "what": "A point variable, bound by a box, by an existential, or by the existential new_ℓ returns. It occurs only in types.",
   "why": "Programs never mention points. Types quantify over them instead.",
   "breaks": "Nothing. It is a definition.",
   "example": "A loop box binds three point variables ι, κ, ζ.",
   "rocq": "types/Points.v: NVar"
  },
  "pt.shift": {
   "title": "Shift x⁺",
   "what": "Raises the offset of a point by one and keeps its polarity. An action on an end at x moves it to x⁺.",
   "why": "Every world has x ≺ x⁺, so the actions of one end are ordered in program order.",
   "breaks": "Nothing. It is a definition.",
   "example": "After a send at x the end sits at x⁺.",
   "rocq": "types/Points.v: pt_shift"
  },
  "pt.field": {
   "title": "Field x·κ",
   "what": "A new name below x. Payload ends, branch continuations and anchored channels sit at fields.",
   "why": "A payload field and the continuation of a choice share one family of fields. A channel created at a field lands where a message on that end delivers it.",
   "breaks": "With a separate kind of field for anchored channels, a reply channel created to be sent would sit away from the payload field, and request and reply programs would not type.",
   "example": "new₀ c with c at ρ places d at ρ·0.",
   "rocq": "types/Points.v: pt_field"
  },
  "pt.dual": {
   "title": "Dual point x̄",
   "what": "Flips the polarity. The two ends of a channel sit at x and x̄.",
   "why": "A thread blocked at u that holds an end at v must have u ≺ v̄, the point of the partner end.",
   "breaks": "Nothing. It is a definition.",
   "example": "new_ℓ places c⁺ at ρ and c⁻ at ρ̄.",
   "rocq": "types/Points.v: pt_dual"
  },
  "pt.laws": {
   "title": "Point laws",
   "what": "Dual is an involution, fields ignore polarity, and shift keeps polarity.",
   "why": "Fields ignore polarity so the sender and the receiver of a message compute the same payload point.",
   "breaks": "If x̄·κ differed from x·κ, the ends a message carries would sit at different points for sender and receiver.",
   "example": "ρ̄·0 = ρ·0.",
   "rocq": "types/Points.v: pt_dual_dual, pt_field_dual"
  },
  "sx.kappai": {
   "title": "Field of a choice κᵢ",
   "what": "Choice false continues at field 0 and choice true at field 1.",
   "why": "The two branches of a choice continue at different points, so they can be ordered separately against other ends.",
   "breaks": "Nothing. It is a definition.",
   "example": "branch at x̄ continues at x·0 or x·1.",
   "rocq": "types/Points.v: bfield"
  },
  "pt.sel": {
   "title": "Select continuation",
   "what": "A select of branch i moves the end to the dual of x·κᵢ.",
   "why": "The selecting end and the branching end continue at the two sides of one field point.",
   "breaks": "Nothing. It is a definition.",
   "example": "select_false o at x continues at the dual of x·0.",
   "rocq": "types/Points.v: sel_pt"
  },
  "pt.bra": {
   "title": "Branch continuation",
   "what": "A branch of choice i moves the end to x·κᵢ.",
   "why": "It is the partner point of the selecting side.",
   "breaks": "Nothing. It is a definition.",
   "example": "branch at x̄ continues at x·κᵢ.",
   "rocq": "types/Points.v: bra_pt"
  },
  "pt.payload": {
   "title": "Payload fields",
   "what": "The j-th end of a message sent at x sits at x·j.",
   "why": "Both ends of the carrier compute the same payload point, so sender and receiver agree where the delivered ends sit.",
   "breaks": "Nothing. It is a definition.",
   "example": "A message on y at Y delivers its end at Y·0.",
   "rocq": "types/Points.v: payload_pts"
  },
  "lbl.family": {
   "title": "Family label ℓ",
   "what": "Selects the laws Λ_ℓ of the world for a new root.",
   "why": "Two components can each use their own families. Their labels are renamed apart when they are composed, so contradicting laws never meet.",
   "breaks": "Nothing. It is a definition.",
   "example": "new₀ and new₁ in a program with two families.",
   "rocq": "lang/Syntax.v: family"
  },
  "lbl.field": {
   "title": "Field label κ",
   "what": "Selects the field x·κ for new_κ.",
   "why": "Distinct labels, or an action on the anchor in between, give distinct points.",
   "breaks": "Two new_κ o with one label and no action on o give two channels at one point. A thread holding one could then never wait on the other.",
   "example": "new₀ c and new₁ c create two channels at different fields of c.",
   "rocq": "lang/Syntax.v: field"
  },
  "lbl.transfer": {
   "title": "Transfer set M",
   "what": "The set fends(v) of the value a send or spawn moves out of the thread.",
   "why": "The ends that leave are exactly the ends the value mentions. That fixes who owns which end after the step, the same way every time.",
   "breaks": "Without it, an end that neither the parent nor the child mentions could be given to either side, and ownership would not follow the program.",
   "example": "spawn (λ_. close d′) moves {d′}.",
   "rocq": "lang/Semantics.v: ltransfer_ok, tstep_transfer"
  },
  "link.csub": {
   "title": "csub",
   "what": "Maps ō₁ to o₂ and o₁ to ō₂ and leaves every other end alone. The process applies it to every thread after a link.",
   "why": "After the link, whoever held the partner of o₁ talks to the partner of o₂ directly, so it now holds o₂. The renaming merges ō₁ and o₂ into one name, so it is not a bijection.",
   "breaks": "Nothing. It is a definition.",
   "example": "After link ⟨c⁺, d⁻⟩ the holder of c⁻ holds d⁻.",
   "rocq": "lang/Syntax.v: csub"
  },
  "lbl.beta": {
   "title": "β label",
   "what": "The label of application, let, unit and pair elimination, case and force.",
   "why": "All of these steps cost the same in every cost table, so one label covers them.",
   "breaks": "Nothing. It is a definition.",
   "example": "force (!e) steps with β.",
   "rocq": "lang/Semantics.v: LBeta"
  },
  "lbl.new": {
   "title": "new_ℓ c label",
   "what": "Carries the family ℓ and the name c of the new channel.",
   "why": "The relation reads ℓ to place the new channel at a fresh root of that family.",
   "breaks": "Nothing. It is a definition.",
   "example": "new₀ creating c.",
   "rocq": "lang/Semantics.v: LNew"
  },
  "lbl.newat": {
   "title": "new_κ o c label",
   "what": "Carries the field, the anchor end and the new name.",
   "why": "The relation reads the anchor to find the point x where the new channel goes.",
   "breaks": "Nothing. It is a definition.",
   "example": "new₀ c⁺ creating d at x·0.",
   "rocq": "lang/Semantics.v: LNewAt"
  },
  "lbl.spawn": {
   "title": "spawn label",
   "what": "Carries the transfer set M = fends(v) and the thunk v.",
   "why": "The relation splits the ends of the parent along M.",
   "breaks": "Nothing. It is a definition.",
   "example": "spawn (λ_. close d′) carries M = {d′}.",
   "rocq": "lang/Semantics.v: LSpawn"
  },
  "lbl.send": {
   "title": "send label o!_M v",
   "what": "An offer to send v on o, moving the ends M.",
   "why": "The relation, the fuel layer and scope extrusion all read M off the label instead of inspecting v.",
   "breaks": "Nothing. It is a definition.",
   "example": "An offer to send the end a on o moves M = {a}.",
   "rocq": "lang/Semantics.v: SSend"
  },
  "lbl.recv": {
   "title": "receive label o?v",
   "what": "An offer to receive v on o. Any value can appear.",
   "why": "A receive must be able to meet whatever a partner sends.",
   "breaks": "Nothing. It is a definition.",
   "example": "o?∗.",
   "rocq": "lang/Semantics.v: SRecv"
  },
  "lbl.close": {
   "title": "close label",
   "what": "An offer to close o.",
   "why": "A plain label. The relation removes o from the environment of the thread.",
   "breaks": "Nothing. It is a definition.",
   "example": "close c⁺ offers c⁺ end.",
   "rocq": "lang/Semantics.v: SClose"
  },
  "lbl.sel": {
   "title": "select label",
   "what": "An offer to select branch i on o.",
   "why": "A plain label. The relation moves o to the continuation point of branch i.",
   "breaks": "Nothing. It is a definition.",
   "example": "select_true o offers o ◁ true.",
   "rocq": "lang/Semantics.v: SSel"
  },
  "lbl.bra": {
   "title": "branch label",
   "what": "An offer to receive choice i on o. Either choice can appear.",
   "why": "A plain label. Branch must be able to meet whichever choice the partner sends.",
   "breaks": "Nothing. It is a definition.",
   "example": "branch o offers o ▷ false and o ▷ true.",
   "rocq": "lang/Semantics.v: SBra"
  },
  "lbl.link": {
   "title": "link label",
   "what": "An unordered pair of ends. It may be degenerate, and the relation rejects a link of an end with itself.",
   "why": "The label is a set, so one process rule can remove the channel of either end.",
   "breaks": "Nothing. It is a definition.",
   "example": "↔{c⁺, d⁻}.",
   "rocq": "lang/Semantics.v: SLink"
  },
  "T-Act-App": {
   "title": "T-Act-App",
   "what": "β-reduces a λ applied to a value.",
   "why": "Plain call by value.",
   "breaks": "Nothing. It is a definition.",
   "example": "(λx. close x) c⁺ steps to close c⁺.",
   "rocq": "lang/Semantics.v: t_act_app"
  },
  "T-Act-Let": {
   "title": "T-Act-Let",
   "what": "Substitutes the value of a let. No closure is built.",
   "why": "A let keeps every end of its context, so it must not go through a λ.",
   "breaks": "Nothing. It is a definition.",
   "example": "let a = c⁺ in close a steps to close c⁺.",
   "rocq": "lang/Semantics.v: t_act_let"
  },
  "T-Act-Force": {
   "title": "T-Act-Force",
   "what": "Unrolls a box once. The body resumes with the box for its self.",
   "why": "This is the only source of recursion and replication.",
   "breaks": "Nothing. It is a definition.",
   "example": "force !(f = force f) steps to itself and never acts.",
   "rocq": "lang/Semantics.v: t_act_force"
  },
  "T-Act-New": {
   "title": "T-Act-New",
   "what": "Creates a channel c and returns both ends. The process rule chooses c.",
   "why": "A thread cannot see which names are taken. The process rule picks a name no thread uses.",
   "breaks": "Nothing. It is a definition.",
   "example": "new₀ steps to ⟨c⁺, c⁻⟩.",
   "rocq": "lang/Semantics.v: t_act_new"
  },
  "T-Act-NewAt": {
   "title": "T-Act-NewAt",
   "what": "Returns the anchor untouched beside the new pair.",
   "why": "The anchor is passed in and handed back, so the thread keeps it.",
   "breaks": "Nothing. It is a definition.",
   "example": "new₁ x steps to ⟨x, ⟨b, b′⟩⟩.",
   "rocq": "lang/Semantics.v: t_act_new_at"
  },
  "T-Act-Spawn": {
   "title": "T-Act-Spawn",
   "what": "Emits the thunk with its transfer set and returns ∗.",
   "why": "The label carries what the child takes.",
   "breaks": "Nothing. It is a definition.",
   "example": "spawn (λ_. close d′) steps to ∗.",
   "rocq": "lang/Semantics.v: t_act_spawn"
  },
  "T-Act-Send": {
   "title": "T-Act-Send",
   "what": "Emits the payload with its transfer set and returns the end.",
   "why": "The label carries what leaves the thread.",
   "breaks": "Nothing. It is a definition.",
   "example": "send ⟨∗, c⟩ steps to c.",
   "rocq": "lang/Semantics.v: t_act_send"
  },
  "T-Act-Recv": {
   "title": "T-Act-Recv",
   "what": "Receives any value and returns it paired with the end.",
   "why": "The thread cannot know what the partner sends, so its step admits every value. The type of the end restricts what the relation has to consider.",
   "breaks": "Nothing. It is a definition.",
   "example": "recv b steps to ⟨∗, b⟩.",
   "rocq": "lang/Semantics.v: t_act_recv"
  },
  "T-Act-Close": {
   "title": "T-Act-Close",
   "what": "Closes an end.",
   "why": "A plain rule. The matching process rule needs the partner to close too.",
   "breaks": "Nothing. It is a definition.",
   "example": "close c⁺ steps to ∗.",
   "rocq": "lang/Semantics.v: t_act_close"
  },
  "T-Act-Select": {
   "title": "T-Act-Select",
   "what": "Selects branch i and returns the same end name.",
   "why": "Ends keep their names, so running a program never reads a point.",
   "breaks": "Nothing. It is a definition.",
   "example": "select_true o steps to o.",
   "rocq": "lang/Semantics.v: t_act_select"
  },
  "T-Act-Branch": {
   "title": "T-Act-Branch",
   "what": "Receives a choice and returns the end in the matching injection.",
   "why": "Either choice may arrive, so the thread has one step for each.",
   "breaks": "Nothing. It is a definition.",
   "example": "branch o steps to inj₂ o.",
   "rocq": "lang/Semantics.v: t_act_branch"
  },
  "T-Act-Link": {
   "title": "T-Act-Link",
   "what": "Forwards o₁ to o₂. The label is a set, so the order of the two ends does not matter.",
   "why": "The renaming happens at the process level, where the other threads are visible.",
   "breaks": "Nothing. It is a definition.",
   "example": "link ⟨c⁺, d⁻⟩ steps to ∗.",
   "rocq": "lang/Semantics.v: t_act_link"
  },
  "T-Act-Ctx": {
   "title": "T-Act-Ctx",
   "what": "Lifts a step through one evaluation frame.",
   "why": "No frame goes under λ or a box, because both suspend evaluation.",
   "breaks": "Nothing. It is a definition.",
   "example": "let ∗ = close c in e steps when close c does.",
   "rocq": "lang/Semantics.v: t_act_ctx"
  },
  "sem.frameval": {
   "title": "frame_val",
   "what": "A frame whose hole is on the right asks a value on its left.",
   "why": "It fixes left-to-right evaluation.",
   "breaks": "Nothing. It is a definition.",
   "example": "In v₁ applied to a hole, v₁ must be a value.",
   "rocq": "lang/Semantics.v: frame_val"
  },
  "P-Act-Beta": {
   "title": "P-Act-Beta",
   "what": "One thread takes a β step.",
   "why": "A plain rule. Internal computation of one thread involves nobody else.",
   "breaks": "Nothing. It is a definition.",
   "example": "A β step of the main thread.",
   "rocq": "lang/Process.v: p_act_beta"
  },
  "P-Act-New": {
   "title": "P-Act-New and P-Act-NewAt",
   "what": "One thread creates a channel with a name no thread uses. The channel becomes restricted.",
   "why": "Both ends start in the creating thread, so the channel is internal to the process.",
   "breaks": "Nothing. It is a definition.",
   "example": "new₀ creates c with c ∉ C.",
   "rocq": "lang/Process.v: p_act_new, p_act_new_at"
  },
  "sem.fresh-global": {
   "title": "Global freshness",
   "what": "The new name is neither restricted nor mentioned by any thread.",
   "why": "Channel names are global. A name one thread still uses must not be reused by another.",
   "breaks": "Reusing a name a thread still mentions would merge two channels into one.",
   "example": "c ∉ C ∪ echans(M).",
   "rocq": "lang/Process.v: p_act_new"
  },
  "P-Act-Spawn": {
   "title": "P-Act-Spawn",
   "what": "The parent continues and a new thread j runs v ∗.",
   "why": "Only the parent takes part in the step.",
   "breaks": "Nothing. It is a definition.",
   "example": "spawn (λu. e) adds a thread j running (λu. e) ∗.",
   "rocq": "lang/Process.v: p_act_spawn"
  },
  "P-Act-Msg": {
   "title": "P-Act-Msg",
   "what": "A send on o meets a receive on ō in another thread. The channel may be free.",
   "why": "The rule asks nothing of C. In a typed process both ends of a channel sit inside the process only when the channel is restricted, so the extra generality admits no new behaviour.",
   "breaks": "Nothing. It is a definition.",
   "example": "The client sends on a and the server receives on a′.",
   "rocq": "lang/Process.v: p_act_msg"
  },
  "P-Act-Close": {
   "title": "P-Act-Close",
   "what": "Both ends close and the channel leaves C.",
   "why": "After a close nobody holds an end of the channel, so it disappears.",
   "breaks": "Nothing. It is a definition.",
   "example": "close c⁺ and close c⁻ in two threads remove c.",
   "rocq": "lang/Process.v: p_act_close"
  },
  "P-Act-Choice": {
   "title": "P-Act-Choice",
   "what": "A select on o meets a branch on ō with the same choice.",
   "why": "The branching thread learns the choice the selecting thread made.",
   "breaks": "Nothing. It is a definition.",
   "example": "select_true o meets branch ō, which steps to inj₂ ō.",
   "rocq": "lang/Process.v: p_act_choice"
  },
  "P-Act-Link": {
   "title": "P-Act-Link",
   "what": "The channel of o₁ goes. Every thread is renamed, so the holder of ō₁ now holds o₂.",
   "why": "The unordered label lets one rule remove the channel of either end.",
   "breaks": "Nothing. It is a definition.",
   "example": "link ⟨c⁺, d⁻⟩ with c restricted.",
   "rocq": "lang/Process.v: p_act_link"
  },
  "P-Act-Session": {
   "title": "P-Act-Session",
   "what": "An offer on a free channel to the environment. A send also frees the channels of the ends it moves out.",
   "why": "Scope extrusion follows the transfer set of the label, so the process and the relation agree on which channels leave.",
   "breaks": "Nothing. It is a definition.",
   "example": "An external send of a restricted end d⁺ frees d.",
   "rocq": "lang/Process.v: p_act_session"
  },
  "sem.sentc": {
   "title": "sentc",
   "what": "The channels of the transfer set of a send label, empty for other labels.",
   "why": "They are the channels a message to the environment moves out of the process.",
   "breaks": "Nothing. It is a definition.",
   "example": "sentc of a send moving d⁺ is {d}.",
   "rocq": "lang/Semantics.v: sentc"
  },
  "ev.event": {
   "title": "Event",
   "what": "The label of a process step, with the thread identifiers taking part.",
   "why": "Fairness asks of each thread that it takes part in steps, so steps must name their threads.",
   "breaks": "Nothing. It is a definition.",
   "example": "msg between threads 0 and 1 on a⁺.",
   "rocq": "lang/Process.v: event"
  },
  "ev.admin": {
   "title": "Administrative events",
   "what": "β, creation, spawn and link. They cost nothing in the liveness cost table.",
   "why": "These are the steps that make no progress on any protocol. Absence of internal divergence speaks about them.",
   "breaks": "Nothing. It is a definition.",
   "example": "A chain of spawns takes only administrative steps.",
   "rocq": "lang/Process.v: ev_admin"
  },
  "ev.tau": {
   "title": "τ events",
   "what": "Every event except an offer to the environment.",
   "why": "A closed program takes only τ steps.",
   "breaks": "Nothing. It is a definition.",
   "example": "A closed configuration takes only τ events.",
   "rocq": "lang/Process.v: ev_tau, itstep"
  },
  "prop.terminated": {
   "title": "terminated",
   "what": "No restricted channel, the main thread is a value and every other thread is ∗.",
   "why": "A finished program has used up every channel, and only the main thread returns a result.",
   "breaks": "Nothing. It is a definition.",
   "example": "(∅, {∗, ∗}).",
   "rocq": "lang/Safety.v: terminated"
  },
  "prop.df": {
   "title": "deadlock_free",
   "what": "Every reachable process is terminated or can take a step.",
   "why": "The target of deadlock freedom.",
   "breaks": "Nothing. It is a definition.",
   "example": "close c⁺ and close c⁻ in two threads are deadlock free.",
   "rocq": "lang/Safety.v: deadlock_free"
  },
  "prop.notau": {
   "title": "no_tau_divergence",
   "what": "From every reachable state there is no infinite sequence of administrative steps.",
   "why": "Lock freedom needs the program to reach its next action. An endless chain of β steps, spawns or links never does.",
   "breaks": "A box that only calls itself, and a forwarder that spawns forever, run forever without acting.",
   "example": "force !(f = force f) is ruled out.",
   "rocq": "lockfree/TauThread.v: no_tau_divergence"
  },
  "prop.padmin": {
   "title": "Administrative step",
   "what": "A process step whose event is administrative.",
   "why": "It names the steps that absence of internal divergence counts.",
   "breaks": "Nothing. It is a definition.",
   "example": "A β step of any thread.",
   "rocq": "lockfree/TauThread.v: padmin"
  },
  "prop.lf": {
   "title": "lock_free",
   "what": "In every maximal weakly fair run, every thread that waits to act eventually takes part in a step.",
   "why": "Deadlock freedom allows a thread to wait forever while others keep running. Lock freedom rules that out. The definition mentions no type.",
   "breaks": "A server that keeps serving one client while another client waits forever is deadlock free and not lock free.",
   "example": "Two threads that close c⁺ and c⁻ are lock free.",
   "rocq": "lockfree/Fair.v: lock_free"
  },
  "prop.maximal": {
   "title": "maximal run",
   "what": "Each position steps by a τ event, or the state is stuck and stays.",
   "why": "Lock freedom quantifies over runs that never stop early. A run that stops while a step is possible proves nothing.",
   "breaks": "Nothing. It is a definition.",
   "example": "A run that stops while a thread can still step is not maximal.",
   "rocq": "lockfree/Fair.v: maximal"
  },
  "prop.wfair": {
   "title": "weak fairness",
   "what": "Each thread eventually takes part in a step or is disabled.",
   "why": "Without fairness a scheduler could ignore one thread forever, and no program would be lock free.",
   "breaks": "Nothing. It is a definition.",
   "example": "A scheduler that never runs an enabled thread is not fair.",
   "rocq": "lockfree/Fair.v: wfair"
  },
  "prop.pend": {
   "title": "pending thread",
   "what": "A thread whose next step is a session action.",
   "why": "These are the threads lock freedom promises progress for.",
   "breaks": "Nothing. It is a definition.",
   "example": "A thread at recv b.",
   "rocq": "lockfree/Fair.v: pend"
  },
  "prop.lfrun": {
   "title": "lf_run",
   "what": "Every thread pending at position i takes part in some step at a position j ≥ i.",
   "why": "It says what a single run must satisfy. Lock freedom asks it of every fair maximal run.",
   "breaks": "Nothing. It is a definition.",
   "example": "Every message the client sends is received by the server at some later step.",
   "rocq": "lockfree/Fair.v: lf_run"
  },
  "ty.unit": {
   "title": "Unit type ∗",
   "what": "The type of ∗. A value of it holds no end.",
   "why": "A plain type. Close, link and spawn return it, and every spawned thread returns it.",
   "breaks": "Nothing. It is a definition.",
   "example": "close returns ∗.",
   "rocq": "types/Types.v: TUnit"
  },
  "ty.arrow": {
   "title": "Arrow",
   "what": "A closure type with an upper point u and a lower point l. In the lock-free system it also carries a cost c, a ticket transformer ϑ, a floor h and credits on argument and result.",
   "why": "Calling a closure runs code that may block, so the type must say where it may block and what ends it holds.",
   "breaks": "Nothing. It is a definition.",
   "example": "∗ ⊸ ∗ for a spawned thunk.",
   "rocq": "types/Types.v: TLolli"
  },
  "ty.arrow.ub": {
   "title": "Upper point u",
   "what": "The latest point at which a call may block. A caller may run the closure only when everything it still has to do lies above u.",
   "why": "The caller cannot see inside the closure. u summarizes where the closure may wait.",
   "breaks": "Without it, a closure that blocks above the caller's remaining actions could be called before those actions, and the thread would wait on itself.",
   "example": "A function that blocks on an end at κ has u = κ.",
   "rocq": "types/Types.v: TLolli ub"
  },
  "ty.arrow.lb": {
   "title": "Lower point l",
   "what": "A lower bound on the partner points of the ends the closure holds. Absent when it holds none.",
   "why": "A closure is a held value. A thread that holds it must not block above the ends inside, and l stands for those ends.",
   "breaks": "Without it, a thread could block at a point above an end captured in a closure it holds.",
   "example": "A closure capturing a⁺ at ρ has l = ρ̄.",
   "rocq": "types/Types.v: TLolli lb"
  },
  "ty.arrow.cost": {
   "title": "Arrow cost c",
   "what": "At most c channel actions before the closure returns. Only the lock-free system reads it.",
   "why": "A thread that holds an end while it runs other code delays that end. The cost bounds the delay.",
   "breaks": "A thread holding an end while it calls a function that never returns would starve the partner of that end. A cost ∞ makes the held end fail aging.",
   "example": "A loop body that never returns costs ∞.",
   "rocq": "types/Types.v: TLolli c"
  },
  "ty.arrow.tix": {
   "title": "Arrow transformer ϑ",
   "what": "How many link tickets a call needs for a given reserve.",
   "why": "Links take no action on any protocol. Tickets bound how many links a thread may perform.",
   "breaks": "A box that links once per round forever needs infinitely many tickets and is rejected.",
   "example": "One link needs one ticket more than the reserve.",
   "rocq": "types/Types.v: TLolli t"
  },
  "ty.arrow.floor": {
   "title": "Floor h",
   "what": "Every captured counter must be at least h for the body to work. The body sees captured ends at credit h.",
   "why": "The body cannot know the counters of the ends it captured. h is what it may assume.",
   "breaks": "Nothing. It is a definition.",
   "example": "Deadlock-freedom typing takes h = ∞.",
   "rocq": "types/Types.v: TLolli h"
  },
  "ty.credit": {
   "title": "Credit a",
   "what": "A lower bound on the counters of the ends a value holds.",
   "why": "A counter says how many more actions of others an end may wait through. A credit lets the type promise a minimum.",
   "breaks": "A send of an end whose counter may be 0 would let it travel forever while its partner waits.",
   "example": "A fresh end has credit N.",
   "rocq": "types/Types.v: ty (fuel fields)"
  },
  "ty.credit-agg": {
   "title": "Credit of an aggregate",
   "what": "A credit on a product, sum or existential is added to its parts. Aging, capture and subtyping push it inward.",
   "why": "A pair at credit 1 whose parts have credit 1 and 2 holds ends with at least 2 and 3.",
   "breaks": "Nothing. It is a definition.",
   "example": "(T¹ ⊗ U²)¹ gives T at 2 and U at 3.",
   "rocq": "static/Contexts.v: tage, tcap, tsub"
  },
  "ty.prod": {
   "title": "Product",
   "what": "A pair of values. The two components hold different ends.",
   "why": "A plain type. Send takes a pair and receive returns one.",
   "breaks": "Nothing. It is a definition.",
   "example": "S₁@ι ⊗ S₂@κ for two ends of a client.",
   "rocq": "types/Types.v: TProd"
  },
  "ty.sum": {
   "title": "Sum",
   "what": "One of two injections.",
   "why": "A plain type. Branch returns a sum that tells which choice arrived.",
   "breaks": "Nothing. It is a definition.",
   "example": "branch returns S₁@x·κ₁ ⊕ S₂@x·κ₂.",
   "rocq": "types/Types.v: TSum"
  },
  "ty.sess": {
   "title": "End type S@x",
   "what": "An end running protocol S that acts next at point x.",
   "why": "Points carry the order that rules out circular waiting.",
   "breaks": "Nothing. It is a definition.",
   "example": "(!∗.Close)@ρ.",
   "rocq": "types/Types.v: TSess"
  },
  "ty.box": {
   "title": "Box type",
   "what": "A replicable thunk, usable at every instance of its point variables that meets C and at every instance of its session variables. Its body has type ∗ ⊸^u U.",
   "why": "A loop needs a fresh point for each round. Quantifying over points under a box gives every call its own points.",
   "breaks": "Nothing. It is a definition.",
   "example": "A client loop has type □∀ι κ ζ. C. ∗ ⊸ (S₁@ι ⊗ S₂@κ ⊸^ζ ∗).",
   "rocq": "types/Types.v: TBox"
  },
  "ty.box.svars": {
   "title": "Session variables of a box",
   "what": "k session variables, instantiated at every force.",
   "why": "One box can serve every protocol the caller plugs in. Only protocols whose recursion always passes an action may be plugged in.",
   "breaks": "Nothing. It is a definition.",
   "example": "A forwarder box that works for any protocol α.",
   "rocq": "types/Types.v: TBox k"
  },
  "ty.box.constraint": {
   "title": "Box constraint C",
   "what": "A set of facts over the bound point variables and some outer points. It may be infinite.",
   "why": "A loop orders the points of all its rounds at once. An infinite set states the facts of every round.",
   "breaks": "Without a constraint a box cannot type a loop that waits on one end while it holds another across rounds.",
   "example": "C states ι ≺ κ̄ for the points of every round of a client loop.",
   "rocq": "types/Points.v: bcs"
  },
  "ty.ex": {
   "title": "Existential",
   "what": "∃^l ῑ. C. T is T at some instance meeting C, with lower bound l on its partner points.",
   "why": "A fresh point is not known outside the term that made it. new_ℓ returns an existential over it, and payloads bind their points the same way.",
   "breaks": "Nothing. It is a definition.",
   "example": "new₀ returns ∃^⊥ ι. Λ₀(ι). (S@ι ⊗ S̄@ῑ).",
   "rocq": "types/Types.v: TEx"
  },
  "ty.ex.lb": {
   "title": "Lower bound of an existential",
   "what": "Absent when the value holds no end, ⊥ when its ends sit at points unknown outside, a point x when every end lies at or above x.",
   "why": "The ⊥ bound stands for a fresh point the context does not know.",
   "breaks": "Without ⊥, a closure could capture an unopened fresh pair and claim a lower point no fact supports.",
   "example": "new_ℓ has type ∃^⊥.",
   "rocq": "types/Points.v: lbound"
  },
  "sty.skip": {
   "title": "Skip",
   "what": "The empty protocol. An end at Skip is idle and no rule acts on it.",
   "why": "An idle end may be held forever without anybody waiting on it. The lock-free system drops its checks that counters are at least 1.",
   "breaks": "Nothing. It is a definition.",
   "example": "A control end that is passed around but never used sits at Skip.",
   "rocq": "types/Types.v: SSkip, fuel/Fuel.v: idle"
  },
  "sty.seq": {
   "title": "Sequencing",
   "what": "S.S′ runs S and then S′. unfold normalizes it to the first action.",
   "why": "Sequencing composes protocols, so recursion need not end in tail position.",
   "breaks": "Nothing. It is a definition.",
   "example": "(!∗).Close.",
   "rocq": "types/Types.v: SSeq"
  },
  "sty.recv": {
   "title": "Receive",
   "what": "?(∃^m ῑ. T^b) receives a payload whose m point variables land on the fields of the carrier.",
   "why": "A plain protocol action. Binding the payload points lets a message carry ends whose points the receiver learns on arrival.",
   "breaks": "Nothing. It is a definition.",
   "example": "µα. ?(∃κ. α@κ).Close receives an end of the same protocol at a field.",
   "rocq": "types/Types.v: SRcv"
  },
  "sty.send": {
   "title": "Send",
   "what": "!(∃^m ῑ. T^b) sends a payload at credit b.",
   "why": "A plain protocol action, the dual of receive.",
   "breaks": "Nothing. It is a definition.",
   "example": "!∗.Close.",
   "rocq": "types/Types.v: SSnd"
  },
  "sty.payload-credit": {
   "title": "Payload credit b",
   "what": "The floor the receiver may assume for the counters of the ends the message carries. The sender must supply b after aging by one.",
   "why": "A forwarded end loses one at each hop. Asking b + 1 of the sender when the receiver gets b rules out endless forwarding.",
   "breaks": "Without floors, two threads could pass an end back and forth forever, and its partner would wait forever.",
   "example": "A payload at credit 2.",
   "rocq": "types/Types.v: SRcv b, SSnd b"
  },
  "sty.plus": {
   "title": "Internal choice",
   "what": "⊕(S₁, S₂). The selecting side picks.",
   "why": "A plain protocol action. Internal choice lets a thread decide how the conversation continues.",
   "breaks": "Nothing. It is a definition.",
   "example": "⊕(Close, !∗.Close).",
   "rocq": "types/Types.v: SPlus"
  },
  "sty.with": {
   "title": "External choice",
   "what": "&(S₁, S₂). The branching side receives the choice.",
   "why": "A plain protocol action, the dual of internal choice.",
   "breaks": "Nothing. It is a definition.",
   "example": "&(Close, ?∗.Close).",
   "rocq": "types/Types.v: SWith"
  },
  "sty.close": {
   "title": "Close",
   "what": "The end must close next.",
   "why": "A plain protocol action. Every finite protocol ends with it.",
   "breaks": "Nothing. It is a definition.",
   "example": "Close@x⁺ after one send at x.",
   "rocq": "types/Types.v: SEnd"
  },
  "sty.mu": {
   "title": "Recursion µα.S",
   "what": "A recursive protocol.",
   "why": "A plain former. Loops run protocols that repeat.",
   "breaks": "Nothing. It is a definition.",
   "example": "µα.!∗.α sends units forever.",
   "rocq": "types/Types.v: SMu"
  },
  "sty.var": {
   "title": "Session variable α",
   "what": "A recursion variable or a session variable of a box.",
   "why": "A plain former. It refers back to an enclosing µ or to a protocol plugged into a box.",
   "breaks": "Nothing. It is a definition.",
   "example": "α in µα.!∗.α.",
   "rocq": "types/Types.v: SVar"
  },
  "sty.vard": {
   "title": "Dual variable ᾱ",
   "what": "The dual of a variable. It enters only through dual.",
   "why": "The dual of a protocol plugged in for α is only known once α is. ᾱ marks that.",
   "breaks": "Nothing. It is a definition.",
   "example": "dual α = ᾱ.",
   "rocq": "types/Types.v: SVarD"
  },
  "sty.unfold": {
   "title": "Head normal form",
   "what": "unfold(S) unrolls µ and normalizes sequencing until the first action.",
   "why": "Every rule reads the first action of a session type.",
   "breaks": "Nothing. It is a definition.",
   "example": "unfold (µα.!∗.α) = !∗.(µα.!∗.α).",
   "rocq": "types/Types.v: unfoldS"
  },
  "sty.dual": {
   "title": "Duality",
   "what": "Swaps send and receive and the two choices. Payloads stay.",
   "why": "The two ends of a channel run dual protocols.",
   "breaks": "Nothing. It is a definition.",
   "example": "dual (!∗.Close) = ?∗.Close.",
   "rocq": "types/Types.v: dual"
  },
  "sty.flip": {
   "title": "flip",
   "what": "Swaps α and ᾱ at one level. Dual uses it under a µ.",
   "why": "Inside µα.S the variable α names the whole recursive protocol. After dualizing the body, α must name the dual µ again, so the ᾱ that dual introduced turn back into α.",
   "breaks": "Nothing. It is a definition.",
   "example": "dual (µα.!∗.α) = µα.?∗.α.",
   "rocq": "types/Types.v: sflip"
  },
  "sty.sequiv": {
   "title": "Session equivalence ≃",
   "what": "Two protocols are equivalent when their first actions agree and their continuations are again equivalent. Annotations count.",
   "why": "One protocol has many spellings, unrolled or not. Rules compare protocols by behaviour, not by spelling.",
   "breaks": "Nothing. It is a definition.",
   "example": "µα.!∗.α ≃ !∗.µα.!∗.α.",
   "rocq": "types/Types.v: sequiv"
  },
  "sty.seqv": {
   "title": "Up to annotations ≈",
   "what": "Equivalence after erasing annotations. The value relation compares session types this way.",
   "why": "The deadlock-freedom and liveness relations ignore credits. One relation then serves every refill N.",
   "breaks": "Nothing. It is a definition.",
   "example": "!(∗²).Close ≈ !(∗^∞).Close.",
   "rocq": "relation/Relation.v: seqv"
  },
  "sty.sdual": {
   "title": "Dual up to annotations",
   "what": "S′ is the dual of S up to annotations.",
   "why": "The relation compares dual protocols up to annotations.",
   "breaks": "Nothing. It is a definition.",
   "example": "A link of ends at S and S′ asks sdual S S′.",
   "rocq": "relation/Relation.v: sdual"
  },
  "ty.heads": {
   "title": "heads",
   "what": "The points a held value owes readiness facts against. An end at x contributes x̄, the point of its partner.",
   "why": "A thread blocked at u that holds an end at v needs u ≺ v̄. Otherwise the partner of that end could be waiting for the thread.",
   "breaks": "Nothing. It is a definition.",
   "example": "heads (Close@ρ ⊗ Close@ρ·0) = {ρ̄, (ρ·0)‾}.",
   "rocq": "types/Types.v: heads"
  },
  "ty.hbot": {
   "title": "The ⊥ flag of a type",
   "what": "True when the value may hold an unopened existential at ⊥.",
   "why": "Ends at unknown points give no fact to block against. A term whose context holds such ends may not block.",
   "breaks": "Nothing. It is a definition.",
   "example": "hbot (∃^⊥ ι. T) = true.",
   "rocq": "types/Types.v: hbot"
  },
  "ty.lbound": {
   "title": "lbound",
   "what": "The lower bound of an existential. Absent, ⊥, or a point.",
   "why": "It says how much a holder knows about where the hidden ends sit.",
   "breaks": "Nothing. It is a definition.",
   "example": "⊥ for new_ℓ.",
   "rocq": "types/Points.v: lbound"
  },
  "ty.payload-at": {
   "title": "payload_at",
   "what": "Places the m bound points of a payload at the fields x·0 … x·(m−1) of the carrier x.",
   "why": "Fields ignore polarity, so sender and receiver compute the same points.",
   "breaks": "Nothing. It is a definition.",
   "example": "A payload α@κ sent at Y lands at Y·0.",
   "rocq": "types/Types.v: payload_at"
  },
  "ty.pscoped": {
   "title": "pscoped",
   "what": "Every point variable of T is bound by the payload itself. Send and receive check it.",
   "why": "A payload mentions only its own points, so unrolling a recursive protocol never captures an outer point.",
   "breaks": "A free outer point inside a µ-body would be captured on unrolling, and substituting points would go wrong.",
   "example": "pscoped 1 (S@ι₀).",
   "rocq": "types/Types.v: pscoped"
  },
  "ann.fuel": {
   "title": "ℕ ∪ {∞}",
   "what": "Credits, costs, floors and counters range over the naturals and ∞.",
   "why": "Deadlock-freedom typing is the case where every fresh and refilled counter is ∞. Subtracting from ∞ keeps ∞.",
   "breaks": "Nothing. It is a definition.",
   "example": "∞ − c = ∞.",
   "rocq": "types/Costs.v: fuel"
  },
  "ann.tix": {
   "title": "Ticket transformer",
   "what": "ϑ = (s, b) stands for r ↦ 2^s·r + b. Slope s and offset b range over the naturals and ∞.",
   "why": "Spawning splits the tickets in half, so needs grow by doubling. The offset ∞ marks a term no finite ticket count serves, which is what deadlock-freedom typing uses.",
   "breaks": "Without the offset ∞, the transformer of deadlock-freedom typing could not be composed with the one ticket a link needs.",
   "example": "(0, 1) needs one ticket more than its reserve.",
   "rocq": "types/Costs.v: tix, tapp"
  },
  "ann.tid": {
   "title": "1̂",
   "what": "The identity transformer r ↦ r.",
   "why": "A value performs no link, so it needs exactly the reserve it holds.",
   "breaks": "Nothing. It is a definition.",
   "example": "Every value types at 1̂.",
   "rocq": "types/Costs.v: tid"
  },
  "ann.meets": {
   "title": "meets",
   "what": "A ticket count tk meets ϑ at reserve r when ϑ(r) ≤ tk.",
   "why": "A thread starts with some finite ticket count, which must cover what its transformer asks at reserve 0.",
   "breaks": "Nothing. It is a definition.",
   "example": "meets (0, 1) 0 1.",
   "rocq": "types/Costs.v: meets"
  },
  "ann.tspawn": {
   "title": "tspawn",
   "what": "The transformer of a spawn. The child gets ⌈tk/2⌉ and needs b_c, the parent keeps ⌊tk/2⌋.",
   "why": "A fixed split needs no knowledge of the future and is the same in every run.",
   "breaks": "Nothing. It is a definition.",
   "example": "A spawn of a child that links once.",
   "rocq": "types/Costs.v: tspawn"
  },
  "ann.tlink": {
   "title": "tlink",
   "what": "One ticket, then ϑ.",
   "why": "A link spends a ticket. Tickets are never created, so two threads cannot take turns linking an end forever.",
   "breaks": "Nothing. It is a definition.",
   "example": "A link composes with tlink 1̂.",
   "rocq": "types/Costs.v: tlink"
  },
  "ann.tseq": {
   "title": "Sequencing ϑ₁ ∘ ϑ₂",
   "what": "First ϑ₁, then ϑ₂. (ϑ₁ ∘ ϑ₂)(r) = ϑ₁(ϑ₂(r)).",
   "why": "The first part of a term must leave enough tickets for the rest.",
   "breaks": "Nothing. It is a definition.",
   "example": "An application composes the transformers of function, argument and call.",
   "rocq": "types/Costs.v: tseq"
  },
  "ann.tok": {
   "title": "tok",
   "what": "ϑ₁ ∘ ϑ₂ is sound when ϑ₂ needs nothing at 0, ϑ₁ has a finite slope, or ϑ₁ has offset ∞.",
   "why": "Composition through an infinite slope is only meaningful in these cases.",
   "breaks": "A sequence of an infinite-slope transformer after one that needs tickets at 0 would claim a finite need it does not have.",
   "example": "An application asks tok of its parts.",
   "rocq": "types/Costs.v: tok"
  },
  "ann.tydf": {
   "title": "ty_df",
   "what": "Sets every annotation to its value at N = ∞.",
   "why": "Deadlock-freedom typing is the merged judgment with infinite refill, so its types carry these annotations.",
   "breaks": "Nothing. It is a definition.",
   "example": "ty_df (S@x) sets the payload credits of S to ∞.",
   "rocq": "types/Types.v: ty_df"
  },
  "ty.prim": {
   "title": "prim",
   "what": "Types built from ∗, ⊗, ⊕ and boxes. Every process result has this shape.",
   "why": "A process result holds no end, so no thread is left waiting on the result.",
   "breaks": "A main thread that returns an end holds it forever, and its partner waits forever.",
   "example": "prim (∗ ⊗ ∗).",
   "rocq": "types/Types.v: prim"
  },
  "ty.unlimited": {
   "title": "unlimited",
   "what": "Box types. Variables of these types may be copied and dropped.",
   "why": "A box holds no end, so copying or dropping it loses or duplicates nothing.",
   "breaks": "Nothing. It is a definition.",
   "example": "The self of a box is unlimited.",
   "rocq": "types/Types.v: unlimited"
  },
  "ty.tfree": {
   "title": "tfree",
   "what": "Types built from ∗, boxes, pairs and sums that hold no end.",
   "why": "Aging and capture adjust credits of entries that hold ends. An entry of such a type holds none, so they leave its credit alone.",
   "breaks": "Nothing. It is a definition.",
   "example": "tfree (∗ ⊗ □…).",
   "rocq": "types/Types.v: tfree"
  },
  "w.world": {
   "title": "World",
   "what": "Constants, facts, families and laws. Nothing else.",
   "why": "Points carry the order, and the world is the order.",
   "breaks": "Nothing. It is a definition.",
   "example": "A world with no constants and one family 0 with laws Λ₀.",
   "rocq": "types/Worlds.v: world"
  },
  "w.consts": {
   "title": "Constants A",
   "what": "The finite set of constant roots.",
   "why": "Facts may mention only constants, and two worlds are compared at composition through the constants they share.",
   "breaks": "Nothing. It is a definition.",
   "example": "A world with constants 1 and 2.",
   "rocq": "types/Worlds.v: w_consts"
  },
  "w.facts": {
   "title": "Facts ≺_A",
   "what": "Facts between points with constant roots.",
   "why": "They order the channels a component shares with its environment.",
   "breaks": "Nothing. It is a definition.",
   "example": "1 ≺ 2̄.",
   "rocq": "types/Worlds.v: w_facts"
  },
  "w.fams": {
   "title": "Families L",
   "what": "The family labels the world knows. new_ℓ types only for ℓ in L.",
   "why": "A family label names a set of laws.",
   "breaks": "Nothing. It is a definition.",
   "example": "{0} for one family.",
   "rocq": "types/Worlds.v: w_fams"
  },
  "w.laws": {
   "title": "Laws Λ_ℓ",
   "what": "Facts over one root variable ι₀ of family ℓ, holding at every generated root of ℓ.",
   "why": "A law speaks of one root, so two generated roots are never ordered against each other. W is strict exactly when its facts and each family of laws are.",
   "breaks": "With one set of laws for all fresh points, two components with different needs could not be composed, because their joined world would be cyclic.",
   "example": "Λ₀(r) = {r ≺ (r·0)‾, r̄ ≺ r·0}.",
   "rocq": "types/Worlds.v: w_laws"
  },
  "w.lt": {
   "title": "≺_W",
   "what": "The transitive closure of the four kinds of generator.",
   "why": "A plain definition. Waiting chains combine many facts, so the order is transitive.",
   "breaks": "Nothing. It is a definition.",
   "example": "W ⊢ x ≺ x⁺⁺.",
   "rocq": "types/Worlds.v: w_lt"
  },
  "w.ws-fact": {
   "title": "Facts generator",
   "what": "Every fact of ≺_A is an order fact.",
   "why": "A plain generator. The facts of the world hold.",
   "breaks": "Nothing. It is a definition.",
   "example": "1 ≺ 2̄.",
   "rocq": "types/Worlds.v: ws_fact"
  },
  "w.ws-law": {
   "title": "Laws generator",
   "what": "Every law of family ℓ in L holds at every generated root g of ℓ.",
   "why": "Every generated root is known up front, so the world stays the same along a run that creates channels.",
   "breaks": "Nothing. It is a definition.",
   "example": "Λ₀ at g gives g ≺ (g·0)‾.",
   "rocq": "types/Worlds.v: ws_law, law_inst"
  },
  "w.ws-po": {
   "title": "x ≺ x⁺",
   "what": "Program order of one end.",
   "why": "An end acts at x before it acts at x⁺.",
   "breaks": "Nothing. It is a definition.",
   "example": "ρ ≺ ρ⁺.",
   "rocq": "types/Worlds.v: ws_po"
  },
  "w.ws-dpo": {
   "title": "x ≺ x̄⁺",
   "what": "An action at x precedes the next action of the partner.",
   "why": "It holds in every run. The action at x synchronizes with the partner at x̄, and the partner acts again at x̄⁺ only afterwards, so programs may use it without stating it.",
   "breaks": "Nothing. It is a definition.",
   "example": "ρ ≺ ρ̄⁺.",
   "rocq": "types/Worlds.v: ws_dpo"
  },
  "w.wf": {
   "title": "world_wf",
   "what": "Facts mention constants of A, and laws mention only the root variable ι₀.",
   "why": "A law that mentions another root would order fresh points against each other.",
   "breaks": "Nothing. It is a definition.",
   "example": "A law ι₀ ≺ g′ with another root g′ is not well formed.",
   "rocq": "types/Worlds.v: world_wf"
  },
  "w.strict": {
   "title": "strict",
   "what": "Well formed and irreflexive.",
   "why": "An irreflexive order cannot let two threads each wait on the other.",
   "breaks": "In a cyclic world two threads that wait on each other both count as ready, and a deadlock types.",
   "example": "A world whose only fact is 1 ≺ 2̄.",
   "rocq": "types/Worlds.v: strict"
  },
  "w.lfworld": {
   "title": "lfworld",
   "what": "Strict and well founded.",
   "why": "Lock freedom ranks a waiting thread by the point of the end it waits on. Waiting chains must then descend in a well-founded order.",
   "breaks": "Without it, waiting could descend forever. Each thread waits on one below it, new threads keep appearing below, and the top thread never proceeds.",
   "example": "A world with no facts and no families.",
   "rocq": "types/Worlds.v: lfworld"
  },
  "w.ext": {
   "title": "World extension ⊑",
   "what": "More constants, facts, families and laws.",
   "why": "A program keeps working when its world grows, for example after composition with another component.",
   "breaks": "Nothing. It is a definition.",
   "example": "W ⊑ W ⊔ W′.",
   "rocq": "types/Worlds.v: wext"
  },
  "w.join": {
   "title": "Join ⊔",
   "what": "The union of constants, facts, families and laws.",
   "why": "Two components typed in their own worlds compose in the union. Their families must be disjoint.",
   "breaks": "Nothing. It is a definition.",
   "example": "W ⊔ W.",
   "rocq": "types/Worlds.v: wjoin"
  },
  "w.restrict": {
   "title": "Restriction W|_S",
   "what": "The facts of ≺_W between points with constant roots in S, without families.",
   "why": "It is the part of a world that another component can see through shared constants.",
   "breaks": "Nothing. It is a definition.",
   "example": "W restricted to its shared constants.",
   "rocq": "types/Worlds.v: wrestrict"
  },
  "w.R7": {
   "title": "Strict join",
   "what": "A join is strict exactly when both worlds are and their orders restricted to the shared constants are acyclic together.",
   "why": "Composition can check strictness of the join by looking only at the shared constants.",
   "breaks": "Nothing. It is a definition.",
   "example": "Two strict worlds with no shared constants join strictly.",
   "rocq": "types/Worlds.v: strict_join_iff"
  },
  "tj.Theta": {
   "title": "Θ, the end environment",
   "what": "Maps each held end to its session type, point and credit, one entry per end.",
   "why": "B9. One entry per end replaces the One and Both entries keyed by a side bit (K3).",
   "breaks": "Nothing. It is a definition.",
   "example": "{a : Sa@ρ^N, b : Sb@ρ·0^N}.",
   "rocq": "static/Contexts.v: tentry, tenv"
  },
  "tj.Gamma": {
   "title": "Γ, facts and future hypotheses",
   "what": "The box constraints in force with their instances, and future variables φ with an upper point u ≺ φ.",
   "why": "A.5. One Γ replaces the two hypothesis contexts Φ and Ψ of the old typed.",
   "breaks": "Nothing. It is a definition.",
   "example": "Inside cli, Γ holds C at (ι, κ, ζ).",
   "rocq": "static/Contexts.v: hctx"
  },
  "tj.Delta": {
   "title": "Δ, the variable context",
   "what": "A de Bruijn list of optional credited types T^a.",
   "why": "Not documented.",
   "breaks": "Nothing. It is a definition.",
   "example": "[Some (S1@ι ⊗ S2@κ, 0)].",
   "rocq": "static/Contexts.v: lenv"
  },
  "tj.F": {
   "title": "Future F",
   "what": "The points the context still acts on after the term, with a future variable φ or the ⊥ flag.",
   "why": "Inventory row S4 and proposal §2.16. Every action at x asks x ≺ F, so the term never blocks above something its context must do first.",
   "breaks": "Without futures, e₁ in let ∗ = close c in close d could block above d, which the context holds, a circular wait within one thread.",
   "example": "e₁ of E-App runs under F ∪ heads(Θ₂, Δ₂).",
   "rocq": "static/Contexts.v: sfuture"
  },
  "tj.W": {
   "title": "World W",
   "what": "The world whose order and families the rule reads.",
   "why": "Not documented beyond §2.4.",
   "breaks": "Nothing. It is a definition.",
   "example": "E-New asks ℓ ∈ L_W.",
   "rocq": "static/Typing.v: typed W"
  },
  "tj.N": {
   "title": "Refill N",
   "what": "The credit of a fresh end and of an end after an action. DF typing is N = ∞, lock-free typing a finite N.",
   "why": "Q4 and Q11. One refill per judgment, the maximum at composition.",
   "breaks": "Nothing. It is a definition.",
   "example": "LFClientServer types at N = 3.",
   "rocq": "static/Typing.v: typed N"
  },
  "tj.cost": {
   "title": "Cost c",
   "what": "An upper bound on the channel actions the term performs before it returns.",
   "why": "Q11, from the old cost judgment. Read only by fuel.",
   "breaks": "Nothing. It is a definition.",
   "example": "send e costs c₀ + 1.",
   "rocq": "static/Typing.v: typed c"
  },
  "tj.tix": {
   "title": "Transformer ϑ",
   "what": "The ticket transformer of the term.",
   "why": "F13 and T2.",
   "breaks": "Nothing. It is a definition.",
   "example": "link e has ϑ₀ ∘ tlink 1̂.",
   "rocq": "static/Typing.v: typed ϑ"
  },
  "ctx.tsplit": {
   "title": "Θ = Θ₁ ⊎ Θ₂",
   "what": "A disjoint split of the ends.",
   "why": "Ends are never shared.",
   "breaks": "Nothing. It is a definition.",
   "example": "E-App splits the ends of e₁ and e₂.",
   "rocq": "static/Contexts.v: tsplit"
  },
  "ctx.lsplit": {
   "title": "Δ split",
   "what": "Each linear variable goes left or right. Unlimited ones go both ways.",
   "why": "Not documented.",
   "breaks": "Nothing. It is a definition.",
   "example": "A box variable may occur in both halves.",
   "rocq": "static/Contexts.v: lenv_split"
  },
  "ctx.hyps": {
   "title": "Hypotheses",
   "what": "Pairs of a box constraint and an instance, from E-Box, E-Open and E-New.",
   "why": "Not documented.",
   "breaks": "Nothing. It is a definition.",
   "example": "(C, [ι; κ; ζ]) inside a box body.",
   "rocq": "static/Contexts.v: hyps, hc_open"
  },
  "ctx.fvar": {
   "title": "Future variables",
   "what": "φ ↦ u records u ≺ φ. A body under φ runs under an unknown future above u.",
   "why": "E-Abs and E-Box name the future of the caller by a variable (proposal §2.16).",
   "breaks": "Nothing. It is a definition.",
   "example": "λ-body under (∅, φ) with u ≺ φ.",
   "rocq": "static/Contexts.v: hc_fvar"
  },
  "ctx.fvarF": {
   "title": "Future variable in F",
   "what": "The unknown part of a future, read through Γ ⊢ u ≺ φ.",
   "why": "Semantically φ stands for an arbitrary set (sf_den, progress.md S4 static futures).",
   "breaks": "Nothing. It is a definition.",
   "example": "F = (∅, φ).",
   "rocq": "static/Contexts.v: futrest"
  },
  "ctx.bot": {
   "title": "⊥ flag in F",
   "what": "The context holds ends whose points are hidden. A term under ⊥ performs no session action.",
   "why": "Every action asks ub_below_s, which asks the flag off. Semantically ⊥ stands for an arbitrary set B (progress.md, S4 static futures).",
   "breaks": "Nothing. It is a definition.",
   "example": "e₁ under a context holding an unopened ∃^⊥.",
   "rocq": "static/Contexts.v: FBot, fs_bot"
  },
  "ctx.slt": {
   "title": "Γ ⊢ x ≺ y",
   "what": "The least transitive relation over ≺_W, the facts of the hypotheses and u ≺ φ.",
   "why": "Every fact a rule reads comes from here (comment in Contexts.v).",
   "breaks": "Nothing. It is a definition.",
   "example": "Γ ⊢ x ≺ x⁺ always.",
   "rocq": "static/Contexts.v: fl, slt"
  },
  "ctx.empty": {
   "title": "Δ empty",
   "what": "Every entry of Δ is None.",
   "why": "Values with no variable use none.",
   "breaks": "Nothing. It is a definition.",
   "example": "∗ types in any Δ of Nones.",
   "rocq": "static/Contexts.v: lenv_empty"
  },
  "ctx.only": {
   "title": "Δ = {x : T^a}",
   "what": "x is the only entry of Δ.",
   "why": "Linearity. E-Weak drops unlimited entries first.",
   "breaks": "Nothing. It is a definition.",
   "example": "Var 0 in [Some T].",
   "rocq": "static/Contexts.v: lenv_only"
  },
  "side.act": {
   "title": "x ≺ F at an action",
   "what": "An action at x lies below every point of the future and below the future variable, and the ⊥ flag is off.",
   "why": "Readiness against the future (B2). It is the static form of below_rest against F.",
   "breaks": "A term that blocks at x while its context must still act at a point below x waits on itself through the partner.",
   "example": "E-Close asks x ≺ F.",
   "rocq": "static/Contexts.v: ub_below_s"
  },
  "act.refill": {
   "title": "Refill N after an action",
   "what": "An end that has just acted, or is fresh, returns at credit N.",
   "why": "Fuel refills an end at an action on it (F8). The static credit mirrors that.",
   "breaks": "Nothing. It is a definition.",
   "example": "send returns (S@x⁺)^N.",
   "rocq": "static/Typing.v: e_send, e_recv, e_select, e_branch, e_new"
  },
  "side.ub": {
   "title": "u ≺ F",
   "what": "Γ ⊢ u ≺ y for every y in F, u ≺ φ for its variable, and no ⊥ flag. Trivial for an absent u.",
   "why": "See side.act.",
   "breaks": "Nothing. It is a definition.",
   "example": "E-App asks u ≺ F of the closure's upper point.",
   "rocq": "static/Contexts.v: ub_below_s"
  },
  "side.lb": {
   "title": "l ≼ H",
   "what": "l is at or below every head in H, and H is empty when l is absent. lb_below_hb also asks no ⊥ flag.",
   "why": "See E-Abs.lb.",
   "breaks": "Nothing. It is a definition.",
   "example": "l ≼ {ρ̄}.",
   "rocq": "static/Contexts.v: lb_below_h, lb_below_hb"
  },
  "side.hold": {
   "title": "Γ ⊢ C[x̄]",
   "what": "Every fact of C at the instance x̄ follows from Γ.",
   "why": "E-Force and E-Pack check the constraint at their witness.",
   "breaks": "Nothing. It is a definition.",
   "example": "The self call of cli instantiates C at (ι⁺, κ⁺, ζ).",
   "rocq": "static/Contexts.v: hold_at"
  },
  "age.free": {
   "title": "Aging a free entry",
   "what": "An entry that holds no end stays.",
   "why": "Its credit says nothing.",
   "breaks": "Nothing. It is a definition.",
   "example": "A box variable is never aged.",
   "rocq": "static/Contexts.v: age_free"
  },
  "age.credit": {
   "title": "Aging an entry",
   "what": "An entry holding ends needs credit at least c and loses c.",
   "why": "Appendix B #7, postponement, is handled by F-Tick and aging in the cost judgment. F-Tick ticks every other held end at each action (§2.10), and aging charges a held entry the cost c of what runs meanwhile.",
   "breaks": "cb_inf_not_aged (#17). A server that runs a callback of cost ∞ while holding its client end fails aging by ∞ at finite N. An idle end ages by truncation at 0 instead (age_idle, decided 2026-11-18), which lets the controller retype.",
   "example": "(S@x, 3) − 1 = (S@x, 2).",
   "rocq": "static/Contexts.v: age_credit"
  },
  "age.agg": {
   "title": "Aging an aggregate",
   "what": "Products, sums and existentials age their parts after adding their credit, and keep credit 0.",
   "why": "Credits of aggregates push inward (progress.md, S2).",
   "breaks": "Nothing. It is a definition.",
   "example": "((T^1 ⊗ U^1), 1) − 1.",
   "rocq": "static/Contexts.v: age_prod, age_sum, age_ex"
  },
  "age.ctx": {
   "title": "Aging the frame",
   "what": "What the second part of the term needs is held while the first part runs, so it ages by c₁.",
   "why": "Proposal §2.17, Γ − c ages every entry that holds an end by c.",
   "breaks": "Without aging, a context could hold an end across arbitrarily many actions and starve its partner (#7).",
   "example": "In LFCycle main loses 1 on d while it closes c.",
   "rocq": "static/Contexts.v: thage, lage"
  },
  "cap.sess": {
   "title": "Capturing an end",
   "what": "A captured end needs credit h + a and is seen by the body at h.",
   "why": "The floor is the counter the body may assume. a is the closure's own credit (proposal §2.17, E-Abs).",
   "breaks": "Nothing. It is a definition.",
   "example": "h = 1, a = 1 needs credit 2.",
   "rocq": "static/Contexts.v: cap_sess"
  },
  "cap.arr": {
   "title": "Capturing a closure",
   "what": "A captured closure with floor h₀ ≤ h restates its credit relative to h.",
   "why": "Not documented beyond the rule.",
   "breaks": "Nothing. It is a definition.",
   "example": "Capturing a callback inside a closure.",
   "rocq": "static/Contexts.v: cap_arr"
  },
  "sub.tsub": {
   "title": "Subtyping",
   "what": "Costs, transformers and floors covariant, arguments contravariant, sessions up to ≃, credits may fall, an existential may drop facts.",
   "why": "An existential drops facts so that world extension preserves E-New, whose result names the laws of W (progress.md, S2 subtyping).",
   "breaks": "Nothing. It is a definition.",
   "example": "LFClientServer passes credits 2 and 3 where 1 and 2 are expected.",
   "rocq": "static/Contexts.v: tsub"
  },
  "sub.dconv": {
   "title": "D-Conv",
   "what": "DF typing converts by subtyping of erased types.",
   "why": "Progress.md, S2 subtyping and S5 D-Conv.",
   "breaks": "Nothing. It is a definition.",
   "example": "Dropping a fact from an ∃.",
   "rocq": "static/Typing.v: d_conv"
  },
  "E-Abs.phi": {
   "title": "Fresh future variable",
   "what": "The body runs under future (∅, φ) with u ≺ φ for a fresh φ.",
   "why": "The body does not know who calls it, only that the caller's future lies above u (proposal §2.16).",
   "breaks": "If the body were typed under the definer's F, a closure called from a different context would block against facts that do not hold there.",
   "example": "λ-body of between under φ with κ ≺ φ.",
   "rocq": "static/Typing.v: e_abs, e_box"
  },
  "E-Abs.lb": {
   "title": "Lower point of a closure",
   "what": "l lies at or below every head of the captured Θ and Δ, and Δ carries no ⊥ flag.",
   "why": "The closure is a held value whose heads its holder reads through l. The ⊥ flag is excluded because hidden points have no lower bound.",
   "breaks": "SpawnGap. A thread holding ends at unrelated points 1 and 2 has no common lower point, so E-Abs rejects a λ that closes both. E-SpawnLam avoids that (spawn_gap).",
   "example": "Capturing a⁺ at ρ gives l = ρ̄.",
   "rocq": "static/Contexts.v: lb_below_hb"
  },
  "E-Abs.cap": {
   "title": "Capture",
   "what": "Captured ends and closures are restated at the floor h.",
   "why": "Proposal §2.17, h + a ≤ every captured credit.",
   "breaks": "Nothing. It is a definition.",
   "example": "See cap.sess.",
   "rocq": "static/Contexts.v: thcap, lcap"
  },
  "E-Abs.body": {
   "title": "Body of a λ",
   "what": "The body types under the captured context, the argument at its credit, and the fresh future.",
   "why": "Not documented.",
   "breaks": "Nothing. It is a definition.",
   "example": "λp. let (a, b) = p in … in cli.",
   "rocq": "static/Typing.v: e_abs"
  },
  "E-App.ub": {
   "title": "u ≺ F at a call",
   "what": "The callee may block up to u, which must lie below what the caller still does.",
   "why": "Arrow bounds, inventory row S4 (proposal §1.3).",
   "breaks": "Calling a closure that blocks at κ while the caller still has to act at a point below κ.",
   "example": "main forces between last, so F = ∅.",
   "rocq": "static/Typing.v: e_app"
  },
  "E-App.fut1": {
   "title": "Future of the first part",
   "what": "e₁ runs under F plus the heads of what the second part holds, and the ⊥ flag of Δ₂.",
   "why": "The ends of e₂ are held while e₁ runs, so e₁ must not block above them.",
   "breaks": "A thread running let ∗ = close c in close d beside a partner that closes d before c deadlocks. E-LetU rejects the first thread unless the point of c lies below the partner point of d.",
   "example": "Cycle needs ρ ≺ (ρ·0)‾ for close c while d is held.",
   "rocq": "static/Typing.v: e_app, e_pair, e_let, e_case"
  },
  "E-App.fut2": {
   "title": "Future of the argument",
   "what": "e₂ runs under F plus the lower point of the closure that is held meanwhile.",
   "why": "The closure's ends are held while e₂ runs, and l stands for their heads.",
   "breaks": "Nothing. It is a definition.",
   "example": "f (close c) with f capturing d.",
   "rocq": "static/Typing.v: e_app"
  },
  "E-App.credit": {
   "title": "c₂ ≤ a₁",
   "what": "The credit of the closure covers the actions of the argument.",
   "why": "The closure is held while e₂ runs (proposal §2.17, E-App a₁ ≥ c₂). Its captured counters tick at each action.",
   "breaks": "Nothing. It is a definition.",
   "example": "A closure at credit ∞ allows any argument.",
   "rocq": "static/Typing.v: e_app"
  },
  "E-App.cost": {
   "title": "Cost of a call",
   "what": "The cost of both parts plus the arrow's cost.",
   "why": "Not documented.",
   "breaks": "Nothing. It is a definition.",
   "example": "c₁ + c₂ + c.",
   "rocq": "static/Typing.v: e_app"
  },
  "E-Pair.fut2": {
   "title": "Future of the second component",
   "what": "e₂ runs under F plus the heads of the first component, which is held.",
   "why": "Same reason as E-App.fut1.",
   "breaks": "Nothing. It is a definition.",
   "example": "⟨close c, close d⟩ needs d̄ above c and so on.",
   "rocq": "static/Typing.v: e_pair"
  },
  "E-Pair.age1": {
   "title": "Aging the first component",
   "what": "The first component ages by the cost of the second.",
   "why": "It is held while e₂ runs.",
   "breaks": "Nothing. It is a definition.",
   "example": "⟨c, send ⟨∗, d⟩⟩ ages c by 1.",
   "rocq": "static/Typing.v: e_pair"
  },
  "E-Let.body": {
   "title": "Body of a let",
   "what": "e₂ types under the aged context with the bound variable at its credit, under F unchanged.",
   "why": "Decision Q13. A let is no closure, so it captures every end and needs no lower point.",
   "breaks": "Under the S2 redex rule, let (a, a′) = new_ℓ in e had no typing that captures more than one end.",
   "example": "let (a, ⟨b, b′⟩) = new_κ a in … in ClientServer.",
   "rocq": "static/Typing.v: e_let, e_letp, e_letu"
  },
  "E-Case.branches": {
   "title": "Branches",
   "what": "Both branches type under the same context with the payload at credit a + aᵢ.",
   "why": "Not documented.",
   "breaks": "Nothing. It is a definition.",
   "example": "case (branch o) (a. close a) (a. close a).",
   "rocq": "static/Typing.v: e_case"
  },
  "E-Box.unl": {
   "title": "Δ unlimited",
   "what": "A box captures only box variables, and Θ is empty.",
   "why": "A box holds no end (Q14), so it is replicable.",
   "breaks": "Nothing. It is a definition.",
   "example": "ring captures nothing.",
   "rocq": "static/Contexts.v: lenv_unl"
  },
  "E-Box.inst": {
   "title": "Session instances",
   "what": "The body types at every list of k hereditarily contractive session types, and at N = ∞ only at instances with the N = ∞ annotations.",
   "why": "Progress.md, S2 session instances. Otherwise a body typed at N = ∞ would have to type at finite payload credits, where an end received at a finite credit cannot be aged by ∞.",
   "breaks": "Nothing. It is a definition.",
   "example": "k = 0 for the examples.",
   "rocq": "static/Contexts.v: sinsts"
  },
  "E-Box.body": {
   "title": "Body of a box",
   "what": "The body types with no ends, under fresh point variables, the constraint and a fresh future.",
   "why": "Not documented.",
   "breaks": "Nothing. It is a definition.",
   "example": "The body of cli.",
   "rocq": "static/Typing.v: e_box"
  },
  "E-Box.open": {
   "title": "Opened constraint",
   "what": "Γ shifted by m point variables, plus C over them.",
   "why": "The body may rely on C at its own point variables.",
   "breaks": "Without C the loop cannot order rounds (#47, ord_no_constraint).",
   "example": "hc_open 3 cs_C Γ.",
   "rocq": "static/Contexts.v: hc_open"
  },
  "E-Box.self": {
   "title": "The self",
   "what": "The box binds itself at index 0, at its own type and credit ∞.",
   "why": "Recursion. The guard marks it at ▷ for live and LF.",
   "breaks": "Nothing. It is a definition.",
   "example": "(force f) ⟨a, b⟩ calls the self.",
   "rocq": "static/Typing.v: e_box"
  },
  "E-Force.hold": {
   "title": "Instance meets C",
   "what": "The chosen points x̄ satisfy the constraint under Γ.",
   "why": "A box is usable only at instances meeting C.",
   "breaks": "Nothing. It is a definition.",
   "example": "main forces between at (ρ, ρ·1), where Λ₀ gives C.",
   "rocq": "static/Typing.v: e_force, e_pack"
  },
  "E-Force.ub": {
   "title": "u[x̄] ≺ F",
   "what": "The instantiated upper point of the box lies below the future.",
   "why": "The forced body may block up to u.",
   "breaks": "Nothing. It is a definition.",
   "example": "The self call of a loop at ζ.",
   "rocq": "static/Typing.v: e_force"
  },
  "E-Send.unfold": {
   "title": "Send head",
   "what": "S₀ unfolds to a send of an m-point payload T at floor b, then S.",
   "why": "Not documented.",
   "breaks": "Nothing. It is a definition.",
   "example": "Sa = µα.!∗.α.",
   "rocq": "static/Typing.v: e_send"
  },
  "E-Send.nobot": {
   "title": "No ⊥ in the payload",
   "what": "The payload holds no unopened existential at ⊥.",
   "why": "Not documented in proposal.md or progress.md.",
   "breaks": "Nothing. It is a definition.",
   "example": "Sending an unopened new pair is rejected.",
   "rocq": "static/Typing.v: e_send"
  },
  "E-Send.heads": {
   "title": "x below the payload heads",
   "what": "The sender holds the payload while it blocks at x, so x lies below every head of the payload at its fields.",
   "why": "It is below_rest for the payload ends, which the sender holds and does not offer while it blocks at x.",
   "breaks": "Nothing. It is a definition.",
   "example": "GrowRing needs Y ≺ (Y·0)‾ for the payload a of the send on y.",
   "rocq": "static/Typing.v: e_send"
  },
  "E-Send.floor": {
   "title": "Payload floor",
   "what": "The payload, aged by one, must still meet the floor b of the session type.",
   "why": "Progress.md, S2 credits of aggregates, and starve_not_spare (#8). A forwarded end at floor b would need b ≥ b + 1.",
   "breaks": "Endless delegation, Padovani's Example (2) (#8).",
   "example": "LFGrowRing sends a′ at credit 4 against floor 2.",
   "rocq": "static/Typing.v: e_send"
  },
  "E-Recv.unfold": {
   "title": "Receive head",
   "what": "S₀ unfolds to a receive.",
   "why": "Not documented.",
   "breaks": "Nothing. It is a definition.",
   "example": "Sb = µα.?∗.α.",
   "rocq": "static/Typing.v: e_recv"
  },
  "E-Close.unfold": {
   "title": "Close head",
   "what": "S₀ unfolds to Close.",
   "why": "Not documented.",
   "breaks": "Nothing. It is a definition.",
   "example": "Close@x.",
   "rocq": "static/Typing.v: e_close"
  },
  "E-Select.unfold": {
   "title": "Select head",
   "what": "S₀ unfolds to ⊕(S₁, S₂).",
   "why": "Not documented.",
   "breaks": "Nothing. It is a definition.",
   "example": "⊕(Close, Close).",
   "rocq": "static/Typing.v: e_select"
  },
  "E-Select.order": {
   "title": "x ≺ x·κᵢ",
   "what": "The partner point of the continuation (x·κᵢ)‾ lies above x.",
   "why": "The rule asks it explicitly because W does not order fields against x. For send and receive the built-in x ≺ x̄⁺ plays this role. The rationale is not stated in proposal.md or progress.md.",
   "breaks": "Nothing. It is a definition.",
   "example": "select_false at x asks x ≺ x·0.",
   "rocq": "static/Typing.v: e_select"
  },
  "E-Branch.unfold": {
   "title": "Branch head",
   "what": "S₀ unfolds to &(S₁, S₂).",
   "why": "Not documented.",
   "breaks": "Nothing. It is a definition.",
   "example": "&(Close, Close).",
   "rocq": "static/Typing.v: e_branch"
  },
  "E-Branch.order": {
   "title": "x ≺ (x·κᵢ)‾",
   "what": "The partner point of each possible continuation lies above x.",
   "why": "As E-Select.order. Not documented beyond the rule.",
   "breaks": "Nothing. It is a definition.",
   "example": "branch at x asks x ≺ (x·0)‾ and x ≺ (x·1)‾.",
   "rocq": "static/Typing.v: e_branch"
  },
  "E-Link.dual": {
   "title": "Linked ends dual",
   "what": "The two ends have dual types at dual points.",
   "why": "O-Link and F-Link compare them. E-Link types them exactly dual, so link_redex proves plink (decision after S8.3).",
   "breaks": "Nothing. It is a definition.",
   "example": "link ⟨c⁺ : S@x, d : S̄@x̄⟩.",
   "rocq": "static/Typing.v: e_link"
  },
  "E-SpawnLam.age": {
   "title": "Handed ends lose one",
   "what": "Every end handed to the child loses one unit of credit.",
   "why": "A hand-over passes the counter minus one (F-Spawn, proposal §2.10). φ|M ≥ 1 at spawn is the only enforcement there.",
   "breaks": "A hop at counter 0 under truncation passes 0 again for free (#9).",
   "example": "LFCycle. The thunk loses 1 at the spawn.",
   "rocq": "static/Typing.v: e_spawn_lam"
  },
  "E-SpawnLam.body": {
   "title": "Body of a spawned λ",
   "what": "The child body types with the handed context and an argument ∗.",
   "why": "Q8 (a), C-SpawnLam beside C-Spawn. GrowRing needs one floor per closure (#30).",
   "breaks": "Nothing. It is a definition.",
   "example": "spawn (λu. let ∗ = u in close d′).",
   "rocq": "static/Typing.v: e_spawn_lam"
  },
  "E-SpawnLam.future": {
   "title": "Empty future of the child",
   "what": "The child starts with no context, so its future is empty and has no variable.",
   "why": "Decision after S5.6. O-Spawn reads the thunk body at the empty future only.",
   "breaks": "Reading every F above u fails for a body that creates a channel at a fresh root and blocks on it.",
   "example": "P-Term spawns threads at the empty future.",
   "rocq": "static/Typing.v: e_spawn_lam"
  },
  "E-Spawn.credit": {
   "title": "Closure credit ≥ 1",
   "what": "A spawned closure value has credit at least 1.",
   "why": "Its captured ends are handed over with counter minus one.",
   "breaks": "Nothing. It is a definition.",
   "example": "spawn f with f at credit 1.",
   "rocq": "static/Typing.v: e_spawn"
  },
  "E-New.fam": {
   "title": "ℓ ∈ L",
   "what": "The family is known to W.",
   "why": "Q2 (d).",
   "breaks": "A new of an unknown family has no laws to open.",
   "example": "new_0 in W_cy.",
   "rocq": "static/Typing.v: e_new"
  },
  "E-New.bot": {
   "title": "⊥ bound",
   "what": "The pair sits at a root the context does not know.",
   "why": "The ⊥ flag says a value may hold an unopened existential whose ends sit at points not known from outside (comment on heads in Types.v).",
   "breaks": "Nothing. It is a definition.",
   "example": "mk₀ returns ∃^⊥.",
   "rocq": "static/Typing.v: e_new"
  },
  "E-New.laws": {
   "title": "Laws as the constraint",
   "what": "The existential carries the laws Λ_ℓ at the fresh root as its constraint.",
   "why": "Proposal §2.4. A fresh root needs facts only from the laws of its family.",
   "breaks": "Option (b), built-in laws only, fails the client and server cycle (§2.5).",
   "example": "Opening new_0 in Cycle gives ρ with Λ₀(ρ).",
   "rocq": "static/Typing.v: e_new"
  },
  "E-New.dual": {
   "title": "Dual pair at N",
   "what": "c⁺ at S@ρ and c⁻ at S̄@ρ̄, both at credit N.",
   "why": "Fresh ends start at N (C-New, proposal §2.11).",
   "breaks": "Nothing. It is a definition.",
   "example": "(Sa@ρ)^N ⊗ (Sb@ρ̄)^N.",
   "rocq": "static/Typing.v: e_new"
  },
  "E-NewAt.anchor": {
   "title": "The anchor",
   "what": "The anchor end is typed and returned unchanged at its credit.",
   "why": "Proposal §2.5. The anchor must be held at the moment of creation.",
   "breaks": "GrowRing created b after closing x, with no anchor. The reordering creates b by new_1 x before recv x (Appendix B.1).",
   "example": "new_0 c in Cycle.",
   "rocq": "static/Typing.v: e_new_at"
  },
  "E-NewAt.field": {
   "title": "Channel at the field",
   "what": "The new ends sit at x·κ and (x·κ)‾, at credit N.",
   "why": "Proposal §2.3. The field is the payload field on purpose.",
   "breaks": "Nothing. It is a definition.",
   "example": "d at ρ·0, d′ at (ρ·0)‾.",
   "rocq": "static/Typing.v: e_new_at"
  },
  "E-Sub.cost": {
   "title": "Weakening costs",
   "what": "A cost may rise and a transformer may weaken.",
   "why": "Not documented.",
   "breaks": "Nothing. It is a definition.",
   "example": "Every call cost may rise to ∞.",
   "rocq": "static/Typing.v: e_sub"
  },
  "E-Weak.drop": {
   "title": "Weakening",
   "what": "Only unlimited entries may be dropped.",
   "why": "Linear ends must be used.",
   "breaks": "Nothing. It is a definition.",
   "example": "Dropping an unused box variable.",
   "rocq": "static/Contexts.v: lenv_wk"
  },
  "E-Pack.lb": {
   "title": "Lower bound of a pack",
   "what": "The bound l lies at or below the heads of the instance, or is ⊥.",
   "why": "Not documented.",
   "breaks": "Nothing. It is a definition.",
   "example": "Packing a fresh pair at ⊥.",
   "rocq": "static/Contexts.v: lbx_below_h"
  },
  "E-Open.entry": {
   "title": "Opened entry",
   "what": "A linear variable of existential type, not unlimited.",
   "why": "Not documented.",
   "breaks": "Nothing. It is a definition.",
   "example": "Opening the result of new_ℓ.",
   "rocq": "static/Typing.v: e_open"
  },
  "E-Open.body": {
   "title": "Body after opening",
   "what": "Everything shifts past m fresh point variables, C joins Γ, and the entry becomes T at credit a + a_T.",
   "why": "Not documented.",
   "breaks": "Nothing. It is a definition.",
   "example": "let p = (force mk₀) ∗ opens at ι.",
   "rocq": "static/Typing.v: e_open"
  },
  "pfree": {
   "title": "pfree Σ",
   "what": "No end of the interface has its partner in the interface.",
   "why": "Decision of 2026-11-18. P-Term internalizes every pair, so a channel whose two ends the thread holds goes into C₀. It discharges the pfree side condition of sem_p_connect at typed processes.",
   "breaks": "No program is lost, because such a channel can always move into C₀.",
   "example": "Σ = {c⁺, c⁻} is rejected, ({c}, …) with Σ = ∅ is used instead.",
   "rocq": "static/Typing.v: pfree"
  },
  "P-Term.C0": {
   "title": "Θ_B covers C₀",
   "what": "The thread holds exactly the ends of the restricted channels C₀ besides its interface.",
   "why": "Not documented beyond the rule.",
   "breaks": "Nothing. It is a definition.",
   "example": "C₀ = ∅ for a source program.",
   "rocq": "static/Typing.v: p_term"
  },
  "P-Term.disj": {
   "title": "Interface apart from C₀",
   "what": "No interface channel is restricted.",
   "why": "Not documented.",
   "breaks": "Nothing. It is a definition.",
   "example": "Σ = {c⁺ ↦ (Close, x)} with C₀ = ∅.",
   "rocq": "static/Typing.v: p_term"
  },
  "P-Term.pairs": {
   "title": "Restricted pairs dual",
   "what": "Both ends of each channel of C₀ are held, at dual types and dual points, at credit N.",
   "why": "Not documented beyond the rule.",
   "breaks": "Nothing. It is a definition.",
   "example": "c⁺ : S@x, c⁻ : S̄@x̄.",
   "rocq": "static/Typing.v: p_term"
  },
  "P-Term.typed": {
   "title": "Thread typing",
   "what": "The thread types with the interface at credit N plus Θ_B, empty Γ and Δ, and the empty future.",
   "why": "P-Term asks no semantic premise (no semantics in static judgments, 2026-11-18).",
   "breaks": "Nothing. It is a definition.",
   "example": "cs_typed at N = ∞.",
   "rocq": "static/Typing.v: p_term"
  },
  "P-Term.future": {
   "title": "Empty future",
   "what": "A thread at top level has no context, so nothing lies in its future.",
   "why": "Decision after S5.6.",
   "breaks": "Nothing. It is a definition.",
   "example": "(∅, None).",
   "rocq": "static/Typing.v: p_term"
  },
  "lf.typedN": {
   "title": "Thread typing at Some N",
   "what": "The merged judgment at a finite refill.",
   "why": "Decision 2026-11-18. ⊩ has static premises only. fsem^N comes from cost_fundamental and fsem_of_cost inside the proof.",
   "breaks": "Nothing. It is a definition.",
   "example": "cy_typedN at N = 2.",
   "rocq": "soup/LFTyped.v: lf_term"
  },
  "lf.N": {
   "title": "Finite N",
   "what": "The refill of LF is a natural number.",
   "why": "Progress.md, S8. The measure of adequacy reads counters as natural numbers, and at N = ∞ every counter is ∞.",
   "breaks": "Nothing. It is a definition.",
   "example": "N = 4 for GrowRing.",
   "rocq": "soup/LFTyped.v: lfptyped N"
  },
  "lf.meets": {
   "title": "meets ϑ 0 tk",
   "what": "Some ticket count meets the thread's transformer at reserve 0.",
   "why": "Progress.md, S9. typed at a finite N does not give it, because an offset may be ∞.",
   "breaks": "A link loop has no finite ticket count (c3_link_loop_not_tix, #5).",
   "example": "meets ϑ 0 0 in the examples.",
   "rocq": "soup/LFTyped.v: lf_term"
  },
  "P-Connect.left": {
   "title": "Left component",
   "what": "The component with the main thread, at result T.",
   "why": "Not documented.",
   "breaks": "Nothing. It is a definition.",
   "example": "cl c⁺ at T = ∗.",
   "rocq": "static/Typing.v: p_connect"
  },
  "P-Connect.right": {
   "title": "Right component at ∗",
   "what": "The other component returns ∗, as every spawned thread does.",
   "why": "P-Stop asks a value of the main thread and ∗ of every other thread.",
   "breaks": "Nothing. It is a definition.",
   "example": "cl c⁻.",
   "rocq": "static/Typing.v: p_connect"
  },
  "P-Connect.cut": {
   "title": "Exact dual cut",
   "what": "The right component holds the partners of Σ_C at exactly dual types and dual points.",
   "why": "Progress.md, S9 the exact cut, and decision 2026-11-18. The soup pairs protocols of a restricted channel up to ≈ with annotations, which a cut dual only up to annotations does not give.",
   "breaks": "An annotation mismatch breaks the payload credit of a later message (S8, F-Link).",
   "example": "senv_dual {c⁺ ↦ (Close, x)} = {c⁻ ↦ (Close, x̄)}.",
   "rocq": "static/Typing.v: senv_dual"
  },
  "P-Connect.disj": {
   "title": "Disjointness",
   "what": "Interfaces, cut and restricted sets of the two sides use distinct channels.",
   "why": "Not documented.",
   "breaks": "Nothing. It is a definition.",
   "example": "LFClose cuts c with Σ₁ = Σ₂ = ∅ and C₁ = C₂ = ∅.",
   "rocq": "static/Typing.v: p_connect"
  },
  "P-Connect.cutfree": {
   "title": "Cut partner-free",
   "what": "The cut holds no pair of partners.",
   "why": "Keeps the composite partner-free (pfree decision of 2026-11-18).",
   "breaks": "Nothing. It is a definition.",
   "example": "Σ_C = {c⁺ ↦ (Close, x)} in LFClose.",
   "rocq": "static/Typing.v: p_connect"
  },
  "P-Connect.fams": {
   "title": "Families apart",
   "what": "The two worlds share no family label.",
   "why": "Families are renamed apart at composition (§2.4, #42). Renaming apart is typed_gmap applied before the join.",
   "breaks": "Two components with contradicting laws in one family make the join non-strict (review point 3).",
   "example": "W_cl has no families, so W_cl ⊔ W_cl passes.",
   "rocq": "static/Typing.v: p_connect"
  },
  "P-Connect.strict": {
   "title": "strict(W₁ ⊔ W₂)",
   "what": "The joined world is strict.",
   "why": "Two-world composition (W7). By R7 it is the strictness of the shared constants.",
   "breaks": "A cyclic join makes both sides ready round the cycle.",
   "example": "W_cl ⊔ W_cl.",
   "rocq": "static/Typing.v: p_connect"
  },
  "P-Connect.join": {
   "title": "Result in W₁ ⊔ W₂",
   "what": "The composite lives in the join of the two worlds.",
   "why": "A.5. P-Connect is two-world in Rocq and paper.",
   "breaks": "Nothing. It is a definition.",
   "example": "LFClose lands in W_cl ⊔ W_cl.",
   "rocq": "static/Typing.v: p_connect"
  },
  "P-Join.lemma": {
   "title": "P-Join side conditions",
   "what": "Each world strict, and the join of their restrictions to the shared constants strict.",
   "why": "Cleanup C.2. P-Join is admissible because the conditions agree with strict(W₁ ⊔ W₂) by R7 (p_join_iff_connect).",
   "breaks": "Nothing. It is a definition.",
   "example": "Two worlds with no shared constants.",
   "rocq": "static/Typing.v: p_join, p_join_iff_connect"
  },
  "guard.judg": {
   "title": "The guard ∅ ⊢▷ t",
   "what": "A judgment beside typing that keeps the self of a box unused until the body has acted on a channel.",
   "why": "Inventory row S8 (proposal §1.3) and decision 2026-11-18 (guard as guarded recursion). κ_L makes β free, so without it !(f = force f) is typable and τ-divergent (#13, #14). DF typing does not use it.",
   "breaks": "live_fundamental_false (#14). div_not_guarded rejects !(f = force f).",
   "example": "loop_guarded. !(f = λx. let ⟨v, x′⟩ = recv x in (force f) x′).",
   "rocq": "static/Guard.v: lguard"
  },
  "guard.marks": {
   "title": "Marks Λ",
   "what": "The variables at ▷, later.",
   "why": "Guarded recursion reading (decision 2026-11-18).",
   "breaks": "Nothing. It is a definition.",
   "example": "true.∅ marks the self.",
   "rocq": "static/Guard.v: lguard"
  },
  "guard.var": {
   "title": "Marked variables unusable",
   "what": "A variable at ▷ cannot be used.",
   "why": "Guarded recursion.",
   "breaks": "!(f = λx. (force f) x) uses f under a λ before any action (pn_fix_not_guarded, #13).",
   "example": "gl_var.",
   "rocq": "static/Guard.v: gl_var"
  },
  "guard.lam": {
   "title": "λ keeps marks",
   "what": "A λ keeps the marks of its scope and adds an unmarked argument.",
   "why": "Its body may run at the level where the λ is a value (comment in Guard.v). This replaces the old premise that a λ captures no marked variable.",
   "breaks": "Nothing. It is a definition.",
   "example": "λx. (force f) x is still unguarded.",
   "rocq": "static/Guard.v: gl_lam"
  },
  "guard.box": {
   "title": "Box marks its self",
   "what": "A box puts its self at ▷.",
   "why": "Guarded recursion.",
   "breaks": "Nothing. It is a definition.",
   "example": "!b checks b under true.Λ.",
   "rocq": "static/Guard.v: gl_box"
  },
  "guard.cong": {
   "title": "Congruence",
   "what": "Without an action, both parts keep the marks.",
   "why": "Not documented.",
   "breaks": "Nothing. It is a definition.",
   "example": "gl_app, gl_pair.",
   "rocq": "static/Guard.v: gl_app"
  },
  "guard.tick": {
   "title": "Tick",
   "what": "After an acting e₁, the rest is checked with no marks.",
   "why": "The rest runs one level lower, where the selves are in V (comment in Guard.v).",
   "breaks": "Without ticks no loop that recurses after an action is guarded.",
   "example": "let ⟨v, x′⟩ = recv x in (force f) x′.",
   "rocq": "static/Guard.v: gl_tick_app and siblings"
  },
  "guard.bind": {
   "title": "Binders unmarked",
   "what": "Variables bound by let, let-pair and case are unmarked.",
   "why": "Not documented.",
   "breaks": "Nothing. It is a definition.",
   "example": "gl_let.",
   "rocq": "static/Guard.v: gl_let, gl_letp, gl_case"
  },
  "guard.acts": {
   "title": "acts",
   "what": "The term performs a send, receive, close, select or branch in evaluation position before it returns.",
   "why": "An action costs at least one level in κ_L.",
   "breaks": "Nothing. It is a definition.",
   "example": "acts (recv x).",
   "rocq": "static/Guard.v: acts, sprim"
  },
  "guard.proc": {
   "title": "Process guard ⊢▷ p",
   "what": "Every thread is guarded.",
   "why": "live_soundness asks it beside ∅ ⊢_W p : T.",
   "breaks": "Nothing. It is a definition.",
   "example": "cs_guarded for the client and server main.",
   "rocq": "static/FundamentalProc.v: pguard"
  },
  "ct.table": {
   "title": "Cost table κ",
   "what": "The cost of each kind of step. A step of cost 0 is read inside the least fixpoint of the level, a step of cost c > 0 at level n − c.",
   "why": "L6 and quirk A4. The live relation was a copy of the base relation. One relation with a cost table gives both (proposal §2.8).",
   "breaks": "Nothing. It is a definition.",
   "example": "κ_DF = (1, 1, 1, 0, 0, 1).",
   "rocq": "relation/CostTable.v: ctable"
  },
  "ct.take-pos": {
   "title": "κ(take) ≥ 1",
   "what": "Receive and branch cost at least one level.",
   "why": "Progress.md, S3 cost tables. A receive reads V of its payload at the level of its continuation in a negative position, so that level must lie below n.",
   "breaks": "With a free receive, V at level n would quantify negatively over itself.",
   "example": "Both tables charge 1.",
   "rocq": "relation/CostTable.v: c_take_pos"
  },
  "ct.give-pos": {
   "title": "κ(β) = 0 ⇒ κ(give) ≥ 1",
   "what": "When β is free, a send costs at least one.",
   "why": "Progress.md, S3. When β is free, V at level n is defined together with E at level n by fuel on the size of the type, and a free send would read V at level n at a payload of unbounded size.",
   "breaks": "Nothing. It is a definition.",
   "example": "κ_L charges send 1.",
   "rocq": "relation/CostTable.v: c_give_pos"
  },
  "ct.give-take": {
   "title": "κ(give) ≤ κ(take)",
   "what": "A give costs at most a take.",
   "why": "Decision after S4.18 (fusion). A synchronization of two closes costs κ(send) + κ(recv), and composition pays it with two gives (comment in CostTable.v).",
   "breaks": "Nothing. It is a definition.",
   "example": "κ_DF 0 ≤ 1, κ_L 1 ≤ 1.",
   "rocq": "relation/CostTable.v: c_give_take"
  },
  "ct.DF": {
   "title": "κ_DF",
   "what": "The deadlock-freedom table. Giving steps and links cost 0 and shrink the term, so the fixpoint is a size recursion.",
   "why": "B3 (proposal §2.8).",
   "breaks": "Nothing. It is a definition.",
   "example": "adequacy at κ_DF.",
   "rocq": "relation/CostTable.v: κ_DF"
  },
  "ct.L": {
   "title": "κ_L",
   "what": "The live table. τ steps cost 0, channel actions 1, a synchronization 2.",
   "why": "L1 and L2. The least fixpoint over τ steps is the content of liveness (proposal §2.8).",
   "breaks": "Nothing. It is a definition.",
   "example": "live_adequacy at κ_L.",
   "rocq": "relation/CostTable.v: κ_L"
  },
  "ct.beta": {
   "title": "Cost of β",
   "what": "1 in κ_DF, 0 in κ_L. An arrow reads its body at j + κ(β) ≤ n.",
   "why": "One arrow for both tables (proposal §2.8). For κ_L the body sits at the current level.",
   "breaks": "Nothing. It is a definition.",
   "example": "κ_L reads λ bodies at level n.",
   "rocq": "relation/CostTable.v: c_beta"
  },
  "ct.new": {
   "title": "Cost of creation",
   "what": "1 in κ_DF, 0 in κ_L.",
   "why": "Proposal §2.8 table.",
   "breaks": "Nothing. It is a definition.",
   "example": "new_0 is free in κ_L.",
   "rocq": "relation/CostTable.v: c_new"
  },
  "ct.spawn": {
   "title": "Cost of spawn",
   "what": "1 in κ_DF, 0 in κ_L. In κ_L the child is read inside the parent's least fixpoint.",
   "why": "Proposal §2.12. This is how κ_L rejects the infinite spawn chain (#40, kob_not_live).",
   "breaks": "Nothing. It is a definition.",
   "example": "O-Spawn reads the thunk at level n.",
   "rocq": "relation/CostTable.v: c_spawn"
  },
  "ct.link": {
   "title": "Cost of link",
   "what": "0 in both tables.",
   "why": "L2, decision 2026-11-08, quirk A5.",
   "breaks": "Link loops are τ-divergence in κ_L (#11).",
   "example": "rec f. new; link; f () τ-diverges.",
   "rocq": "relation/CostTable.v: c_link"
  },
  "ct.give": {
   "title": "Cost of a give",
   "what": "send, select and close. 0 in κ_DF, 1 in κ_L.",
   "why": "Proposal §2.8.",
   "breaks": "Nothing. It is a definition.",
   "example": "O-Send at n − κ(give).",
   "rocq": "relation/CostTable.v: c_give"
  },
  "ct.takek": {
   "title": "Cost of a take",
   "what": "recv and branch. 1 in both.",
   "why": "Proposal §2.8 and c_take_pos.",
   "breaks": "Nothing. It is a definition.",
   "example": "O-Recv at j ≤ n − 1.",
   "rocq": "relation/CostTable.v: c_take"
  },
  "ct.sync": {
   "title": "Cost of a synchronization",
   "what": "κ(give) + κ(take). 1 in κ_DF, 2 in κ_L.",
   "why": "Sharp edge 44 (#16). κ_L charges 2, so the index does not halve at a synchronization.",
   "breaks": "Nothing. It is a definition.",
   "example": "P-Act-Msg costs ev_cost.",
   "rocq": "relation/CostTable.v: ev_cost"
  },
  "rel.atcost": {
   "title": "e′ at Θ′",
   "what": "After a step of cost 0, the term must be in the fixpoint X at the same level. After a positive cost, in E at the lower level.",
   "why": "Stated as two implications, so X occurs strictly positively (comment in Relation.v).",
   "breaks": "Nothing. It is a definition.",
   "example": "A β step in κ_L stays at level n.",
   "rocq": "relation/Relation.v: at_cost_E"
  },
  "rel.lfp": {
   "title": "Least fixpoint",
   "what": "E and P at a level are least fixpoints over cost-0 steps.",
   "why": "In κ_DF the cost-0 steps shrink the term, in κ_L the least fixpoint excludes infinite τ sequences (proposal §2.8).",
   "breaks": "A greatest fixpoint would admit !(f = force f) in κ_L, which only takes β steps.",
   "example": "Erel_S_ind is its induction principle.",
   "rocq": "relation/Relation.v: Eind, Pind"
  },
  "V-Unit": {
   "title": "V at ∗",
   "what": "Only ∗, with an empty environment.",
   "why": "Not documented.",
   "breaks": "Nothing. It is a definition.",
   "example": "∗ ∈ V⟦∅ ⊢ ∗⟧.",
   "rocq": "relation/Relation.v: Vbody TUnit"
  },
  "V-Sess": {
   "title": "V at S@x",
   "what": "The value is an end o, the environment holds exactly o at the same point x, at a session type equal to S up to annotations.",
   "why": "Progress.md, S3 annotations. The environment keeps its annotations for the fuel layer, V compares erased.",
   "breaks": "Nothing. It is a definition.",
   "example": "c⁺ ∈ V⟦{c⁺ ↦ (S′, ρ)} ⊢ S@ρ⟧ when S′ ≈ S.",
   "rocq": "relation/Relation.v: Vbody TSess"
  },
  "V-Sess.exact": {
   "title": "Exactly one entry",
   "what": "Θ is the singleton {o ↦ S′@x}.",
   "why": "Values own exactly their ends. The point is the same, no alias (W2, no-eq).",
   "breaks": "Nothing. It is a definition.",
   "example": "Θ = {c⁺ ↦ (S, ρ)}.",
   "rocq": "relation/Relation.v: Vbody TSess"
  },
  "V-Prod": {
   "title": "V at ⊗",
   "what": "Components split the environment disjointly.",
   "why": "Not documented.",
   "breaks": "Nothing. It is a definition.",
   "example": "⟨c⁺, d⁻⟩ splits {c⁺, d⁻}.",
   "rocq": "relation/Relation.v: Vbody TProd"
  },
  "V-Prod.split": {
   "title": "Disjoint split",
   "what": "Θ = Θ₁ ⊎ Θ₂.",
   "why": "F19, a pair splits its ends into disjoint parts. A renaming that pushes a held end into a box inside a pair is ruled out by the split (#36).",
   "breaks": "Nothing. It is a definition.",
   "example": "{c⁺} ⊎ {d⁻}.",
   "rocq": "relation/Relation.v: Vbody TProd"
  },
  "V-Sum": {
   "title": "V at ⊕",
   "what": "An injection into one side.",
   "why": "Not documented.",
   "breaks": "Nothing. It is a definition.",
   "example": "inj₁ c⁺.",
   "rocq": "relation/Relation.v: Vbody TSum"
  },
  "V-Arrow.exact": {
   "title": "dom Θ = fends(e)",
   "what": "A closure holds exactly the ends its body mentions.",
   "why": "Decision Q14, agreed explicitly. It is the clause V already has at an end value.",
   "breaks": "send_gap (v2/compat/SendGap.v, S4.3). λ_. let ∗ = Ω in close q⁺ mentions q⁺, owns nothing, and is in V at every level, so send ⟨w′, d⁺⟩ is not in E at level 1 and E-Send fails.",
   "example": "λ_. close a holds {a}.",
   "rocq": "relation/Relation.v: Varr"
  },
  "V-Arrow.lb": {
   "title": "l ≼ heads Θ",
   "what": "The lower point bounds the heads of the closure's ends.",
   "why": "The holder reads the closure's heads through l.",
   "breaks": "Nothing. It is a definition.",
   "example": "A closure over a at ρ has l ≼ ρ̄.",
   "rocq": "relation/Relation.v: Varr, lb_le"
  },
  "V-Arrow.kripke": {
   "title": "Every later world",
   "what": "The body works in every W′ ⊒ W.",
   "why": "Monotonicity in the world. A closure may be called after the world grew.",
   "breaks": "Nothing. It is a definition.",
   "example": "Calling a received closure in W ⊔ W′.",
   "rocq": "relation/Relation.v: Varr"
  },
  "V-Arrow.level": {
   "title": "j + κ(β) ≤ n",
   "what": "The body is read at every level up to n − κ(β).",
   "why": "One arrow for both tables. κ_DF gives j < n, κ_L gives j ≤ n (proposal §2.8).",
   "breaks": "Nothing. It is a definition.",
   "example": "κ_L reads the body at level n.",
   "rocq": "relation/Relation.v: Varr"
  },
  "V-Arrow.ub": {
   "title": "u ≺ F",
   "what": "The body runs under every future above u.",
   "why": "Futures and the upper point are one concept in presentation (proposal §2.16).",
   "breaks": "Nothing. It is a definition.",
   "example": "ub_lt W' u F.",
   "rocq": "relation/Readiness.v: ub_lt"
  },
  "V-Arrow.body": {
   "title": "Body in E",
   "what": "e[w] is in E with the union of the closure's and the argument's ends.",
   "why": "Not documented.",
   "breaks": "Nothing. It is a definition.",
   "example": "The body of cli at ⟨a, b⟩.",
   "rocq": "relation/Relation.v: Varr"
  },
  "V-Thunk.empty": {
   "title": "Empty future of the thunk",
   "what": "The spawned thunk is read without lower and upper point, at the empty future.",
   "why": "Decisions after S5.5 and S5.6. The thunk leaves the parent, so no readiness of the parent reads its heads, and a thread with no context waits for nothing in a future.",
   "breaks": "spawn_gap (v2/compat/SpawnGap.v). With the lower point, a thread holding ends at unrelated points 1 and 2 cannot spawn a thunk that closes both, and fundamental fails.",
   "example": "Vthunk_of_Vrel gives Erel_spawn.",
   "rocq": "relation/Relation.v: Vthunk"
  },
  "V-Box.empty": {
   "title": "Θ = ∅",
   "what": "A box owns no end.",
   "why": "Not documented beyond Q14.",
   "breaks": "Nothing. It is a definition.",
   "example": "!(…) with Θ = ∅.",
   "rocq": "relation/Relation.v: Vbody TBox"
  },
  "V-Box.noends": {
   "title": "fends(e) = ∅",
   "what": "A box mentions no end.",
   "why": "Decision Q14. Implied by the clause at its thunk, kept because Q14 states it (progress.md, S4 Q14).",
   "breaks": "A box hiding an end under an empty map could be copied with the end inside (#32).",
   "example": "ring mentions no end.",
   "rocq": "relation/Relation.v: Vbody TBox"
  },
  "V-Box.kripke": {
   "title": "Every later world",
   "what": "The box works in every W′ ⊒ W.",
   "why": "Not documented.",
   "breaks": "Nothing. It is a definition.",
   "example": "Forcing a received box later.",
   "rocq": "relation/Relation.v: Vbody TBox"
  },
  "V-Box.inst": {
   "title": "Instances meeting C",
   "what": "Every point instance x̄ whose constraint holds in W′.",
   "why": "Not documented.",
   "breaks": "Nothing. It is a definition.",
   "example": "The self call of cli at (ι⁺, κ⁺, ζ).",
   "rocq": "relation/Readiness.v: wholds"
  },
  "V-Box.hc": {
   "title": "Hereditarily contractive instances",
   "what": "Every session instance that is hcontractive.",
   "why": "Progress.md, S3. V-Box quantifies over every hcontractive instance, D-Box only over the N = ∞ ones, and blindness bridges the two.",
   "breaks": "Nothing. It is a definition.",
   "example": "k = 0 in the examples.",
   "rocq": "types/Types.v: hcontractive"
  },
  "V-Box.thunk": {
   "title": "The thunk at the same level",
   "what": "λ_. e[!e] is in V at the instantiated arrow at level n.",
   "why": "A box counts three in tsize so that V of a box reads V of its thunk type inside the level (comment in Relation.v).",
   "breaks": "Nothing. It is a definition.",
   "example": "thunk e := λ. e[!e].",
   "rocq": "relation/Relation.v: thunk, tthunk"
  },
  "V-Ex.lb": {
   "title": "l ≼ heads Θ",
   "what": "The lower bound holds of the actual ends, trivially for ⊥.",
   "why": "Not documented.",
   "breaks": "Nothing. It is a definition.",
   "example": "⊥ for new.",
   "rocq": "relation/Readiness.v: lbx_le"
  },
  "V-Ex.witness": {
   "title": "A witness in W",
   "what": "Some instance meets C in W, and the value is in V at that instance.",
   "why": "Not documented.",
   "breaks": "Nothing. It is a definition.",
   "example": "The fresh root g with Λ_ℓ(g).",
   "rocq": "relation/Relation.v: Vbody TEx"
  },
  "rel.vsize": {
   "title": "Recursion on (n, size T)",
   "what": "V at level n recurses on the type size inside the level. Levels come from one generic course-of-values fixpoint sfix.",
   "why": "B1 and proposal §2.8. Instantiation keeps the size (tsize_sinst), so the box clause stays inside the recursion.",
   "breaks": "Nothing. It is a definition.",
   "example": "size(□…) = 3 + size U.",
   "rocq": "relation/Relation.v: tsize, Vtop; relation/Sfix.v: sfix"
  },
  "E.zero": {
   "title": "Level 0",
   "what": "Every term is in E at level 0.",
   "why": "Step indexing.",
   "breaks": "Nothing. It is a definition.",
   "example": "Erel_0.",
   "rocq": "relation/Relation.v: Etop, Erel_0"
  },
  "E.kripke": {
   "title": "Every later world",
   "what": "Each unfolding of E holds in every W₁ ⊒ W.",
   "why": "Decision Q9 (a). E is monotone in the world by definition. The receive clause needs no quantifier of its own.",
   "breaks": "Nothing. It is a definition.",
   "example": "Erel_mono.",
   "rocq": "relation/Relation.v: Ebody"
  },
  "E.stop": {
   "title": "(stop)",
   "what": "An irreducible term is a value in V at the current level.",
   "why": "Not documented.",
   "breaks": "A stuck non-value term would count as typed.",
   "example": "close c⁺ alone is reducible by its offer, not stuck.",
   "rocq": "relation/Relation.v: Ebody"
  },
  "E.ready": {
   "title": "(ready)",
   "what": "A reducible term is ready against its environment and future.",
   "why": "B2. Readiness excludes circular waiting.",
   "breaks": "Two threads each waiting on the other's second end.",
   "example": "ready_t W (Θ ∣ F, e).",
   "rocq": "relation/Relation.v: Ebody"
  },
  "E.step": {
   "title": "(step)",
   "what": "Every labelled step meets its obligation.",
   "why": "One conjunct per label so that X occurs strictly positively (progress.md, S3 the step clause).",
   "breaks": "Nothing. It is a definition.",
   "example": "Esteps, Eobl.",
   "rocq": "relation/Relation.v: Esteps, Eobl"
  },
  "O-Beta": {
   "title": "O-Beta",
   "what": "The continuation at the same environment.",
   "why": "Not documented.",
   "breaks": "Nothing. It is a definition.",
   "example": "β in κ_L stays at level n.",
   "rocq": "relation/Relation.v: o_beta"
  },
  "O-New": {
   "title": "O-New",
   "what": "For every generated root fresh for Θ, some S places c⁺ at S@g and c⁻ at S̄@ḡ.",
   "why": "Proposal §2.5. The clause is universal over fresh roots, harmless because all roots of a family obey the same laws. The soup picks the least unused root.",
   "breaks": "Nothing. It is a definition.",
   "example": "new_0 in Cycle.",
   "rocq": "relation/Relation.v: o_new"
  },
  "O-New.cfresh": {
   "title": "c fresh for Θ",
   "what": "The new name is no end of Θ.",
   "why": "As the old O-New (progress.md, S3 creation).",
   "breaks": "Nothing. It is a definition.",
   "example": "c⁺, c⁻ ∉ dom Θ.",
   "rocq": "relation/Relation.v: cfresh"
  },
  "O-New.forall": {
   "title": "For every fresh root",
   "what": "The obligation holds at every fresh root of the family.",
   "why": "Placement is a function of the run, the same at every index (§4).",
   "breaks": "Choosing the point per index breaks lock freedom (C1, §4.2).",
   "example": "∀ g, gfresh ℓ g Θ.",
   "rocq": "relation/Relation.v: o_new"
  },
  "O-New.gfresh": {
   "title": "g fresh for Θ",
   "what": "g is the root of no point of Θ.",
   "why": "A generated root reused after a link renamed its channel is ruled out by roots from a supply separate from channel names (#41).",
   "breaks": "Nothing. It is a definition.",
   "example": "gfresh ℓ g Θ.",
   "rocq": "relation/Relation.v: gfresh"
  },
  "O-New.dual": {
   "title": "Dual placement",
   "what": "c⁺ at S@g, c⁻ at dual S at ḡ.",
   "why": "Not documented.",
   "breaks": "Nothing. It is a definition.",
   "example": "new_env c S (pgen ℓ g) Θ.",
   "rocq": "relation/Relation.v: new_env"
  },
  "O-NewAt": {
   "title": "O-NewAt",
   "what": "The anchor is held at x, and the new channel goes to x·κ and (x·κ)‾.",
   "why": "Nothing to pick, placement is deterministic (proposal §2.5).",
   "breaks": "Nothing. It is a definition.",
   "example": "new_0 c at ρ gives d at ρ·0.",
   "rocq": "relation/Relation.v: o_new_at"
  },
  "O-NewAt.held": {
   "title": "Anchor held",
   "what": "Θ holds the anchor and gives its point.",
   "why": "Progress.md, S3 creation.",
   "breaks": "Nothing. It is a definition.",
   "example": "Θ(c) = S₀@ρ.",
   "rocq": "relation/Relation.v: o_new_at"
  },
  "O-Spawn": {
   "title": "O-Spawn",
   "what": "Θ splits into the child's part, whose ends are exactly M, and the parent's rest. The thunk is in Vthunk at the parent's level.",
   "why": "Q3 and the decisions after S5.5 and S5.6.",
   "breaks": "Nothing. It is a definition.",
   "example": "spawn (λ_. close d′) gives the child {d′}.",
   "rocq": "relation/Relation.v: o_spawn"
  },
  "O-Spawn.split": {
   "title": "Θ = Θ_M ⊎ Θ_r",
   "what": "A disjoint split between child and parent.",
   "why": "Not documented beyond §2.7.",
   "breaks": "Nothing. It is a definition.",
   "example": "Θ_M = {d′}.",
   "rocq": "relation/Relation.v: o_spawn"
  },
  "O-Spawn.transfer": {
   "title": "dom Θ_M = M",
   "what": "The part that leaves is exactly the transfer set of the label.",
   "why": "Decision Q3. The transfer set is the one index-free source of the split.",
   "breaks": "Without it, a thread can give an end neither side mentions to either side at different indices, so ownership is not the same at every index (§2.7).",
   "example": "O-Send and O-Spawn read M off the label.",
   "rocq": "relation/Relation.v: o_spawn, o_send"
  },
  "O-Spawn.thunk": {
   "title": "Thunk in Vthunk",
   "what": "The thunk is a λ in Vthunk at the parent's level.",
   "why": "Progress.md, S3 spawn. In κ_L the child is read inside the parent's fixpoint, which rejects the infinite spawn chain (#40).",
   "breaks": "Nothing. It is a definition.",
   "example": "Vthunk n … ΘM v.",
   "rocq": "relation/Relation.v: o_spawn"
  },
  "O-Send": {
   "title": "O-Send",
   "what": "The subject is at a send head. The rest of Θ splits into the payload's ends M and the remainder. The payload is in V at the payload type, the continuation at the rest with o at S@x⁺.",
   "why": "Q3. Ownership at a send follows the transfer set.",
   "breaks": "Nothing. It is a definition.",
   "example": "send ⟨a, y⟩ in GrowRing.",
   "rocq": "relation/Relation.v: o_send"
  },
  "O-Send.split": {
   "title": "Θ ∖ o = Θ_M ⊎ Θ_r",
   "what": "The subject is not part of the payload.",
   "why": "A send hands on held ends other than its subject (F17).",
   "breaks": "A hole that sends its own subject (#34).",
   "example": "delete o Θ = ΘM ∪ Θr.",
   "rocq": "relation/Relation.v: o_send"
  },
  "O-Send.payload": {
   "title": "Payload level",
   "what": "The payload is read at the level of the continuation, n − κ(give). n in κ_DF, n − 1 in κ_L.",
   "why": "Progress.md, S3 payload level.",
   "breaks": "Nothing. It is a definition.",
   "example": "at_cost_V n (c_give κ).",
   "rocq": "relation/Relation.v: o_send"
  },
  "O-Send.shift": {
   "title": "o moves to x⁺",
   "what": "The subject continues at S@x⁺.",
   "why": "Program order of one end.",
   "breaks": "Nothing. It is a definition.",
   "example": "<[o := (S, x⁺)]> Θr.",
   "rocq": "relation/Relation.v: o_send"
  },
  "O-Recv": {
   "title": "O-Recv",
   "what": "For every lower level and every incoming value in V with fresh ends, the continuation is in E with those ends added.",
   "why": "Not documented beyond §2.8.",
   "breaks": "Nothing. It is a definition.",
   "example": "let ⟨u, b⟩ = recv b in … in cli.",
   "rocq": "relation/Relation.v: o_recv"
  },
  "O-Recv.forall": {
   "title": "Every incoming value",
   "what": "Any value in V at the payload type at level j ≤ n − κ(take) with ends disjoint from Θ.",
   "why": "c_take_pos keeps this read below n.",
   "breaks": "Nothing. It is a definition.",
   "example": "∀ j Θin.",
   "rocq": "relation/Relation.v: o_recv"
  },
  "O-Recv.level": {
   "title": "Continuation at level j",
   "what": "The continuation is in E at level j, the subject at S@x⁺ and the incoming ends added.",
   "why": "Not documented.",
   "breaks": "Nothing. It is a definition.",
   "example": "El j W (<[o := (S, x⁺)]> Θ ∪ Θin).",
   "rocq": "relation/Relation.v: o_recv"
  },
  "O-Close": {
   "title": "O-Close",
   "what": "The end leaves the environment.",
   "why": "Not documented.",
   "breaks": "Nothing. It is a definition.",
   "example": "close c⁺.",
   "rocq": "relation/Relation.v: o_close"
  },
  "O-Select": {
   "title": "O-Select",
   "what": "The end moves to (x·κᵢ)‾ at Sᵢ.",
   "why": "Not documented.",
   "breaks": "Nothing. It is a definition.",
   "example": "select_true o.",
   "rocq": "relation/Relation.v: o_select"
  },
  "O-Branch": {
   "title": "O-Branch",
   "what": "For the choice the step took, the end moves to x·κᵢ at Sᵢ. It costs κ(take).",
   "why": "Not documented.",
   "breaks": "Nothing. It is a definition.",
   "example": "branch o.",
   "rocq": "relation/Relation.v: o_branch"
  },
  "O-Link": {
   "title": "O-Link",
   "what": "Both linked ends leave the environment.",
   "why": "Not documented.",
   "breaks": "Nothing. It is a definition.",
   "example": "link ⟨c⁺, d⁻⟩.",
   "rocq": "relation/Relation.v: o_link"
  },
  "O-Link.distinct": {
   "title": "o₁ ≠ o₂",
   "what": "A self link is rejected.",
   "why": "The label may be degenerate (comment in Semantics.v).",
   "breaks": "Nothing. It is a definition.",
   "example": "link ⟨c⁺, c⁺⟩ is in no E.",
   "rocq": "relation/Relation.v: o_link"
  },
  "O-Link.dual": {
   "title": "Dual at dual points",
   "what": "The ends sit at x and x̄ with dual types up to annotations.",
   "why": "Not documented beyond §2.8.",
   "breaks": "Nothing. It is a definition.",
   "example": "c⁺ at S@x, d⁻ at S̄@x̄.",
   "rocq": "relation/Relation.v: o_link"
  },
  "rd.stable": {
   "title": "stable",
   "what": "Every step of the term is a session offer.",
   "why": "Readiness speaks of terms that wait.",
   "breaks": "Nothing. It is a definition.",
   "example": "recv b is stable, (λx.x) ∗ is not.",
   "rocq": "relation/Readiness.v: stable_t"
  },
  "rd.offered": {
   "title": "offered",
   "what": "o is held and is a subject of some step of the term.",
   "why": "Progress.md, S3 readiness. Each end has one entry, so no shape test picks an entry.",
   "breaks": "Nothing. It is a definition.",
   "example": "recv b offers b.",
   "rocq": "relation/Readiness.v: offered_t"
  },
  "rd.value": {
   "title": "No offer means a value",
   "what": "A stable term that offers no held end is a value.",
   "why": "A stable term offering only on ends it does not hold would be stuck.",
   "breaks": "Nothing. It is a definition.",
   "example": "close q with q not held is not ready.",
   "rocq": "relation/Readiness.v: ready_t"
  },
  "rd.link": {
   "title": "A link redex compares nothing",
   "what": "A term at a link is ready.",
   "why": "Proposal §2.6 states that a link redex compares nothing. A further rationale is not documented.",
   "breaks": "Nothing. It is a definition.",
   "example": "link ⟨c⁺, d⁻⟩.",
   "rocq": "relation/Readiness.v: link_t"
  },
  "rd.below-rest": {
   "title": "below_rest",
   "what": "Every offered end lies below the partner point of every held end it does not offer, and below every point of the future.",
   "why": "Proposal §2.6. It excludes circular waiting.",
   "breaks": "Client and server each blocked on their second channel while holding the first, if the order were cyclic.",
   "example": "Cycle. close c at ρ while d is held at ρ·0 needs ρ ≺ (ρ·0)‾.",
   "rocq": "relation/Readiness.v: below_rest"
  },
  "rd.below-held": {
   "title": "Below held partners",
   "what": "x ≺ x̄′ for every held end o′ at x′ that is not offered.",
   "why": "End points (W1). Readiness asks u ≺ v̄.",
   "breaks": "Nothing. It is a definition.",
   "example": "ρ ≺ (ρ·0)‾.",
   "rocq": "relation/Readiness.v: below_rest"
  },
  "rd.below-future": {
   "title": "Below the future",
   "what": "x ≺ y for every y in F.",
   "why": "The context acts at F after the term.",
   "breaks": "Nothing. It is a definition.",
   "example": "κ ≺ φ in between.",
   "rocq": "relation/Readiness.v: below_rest"
  },
  "rd.p-stable": {
   "title": "stable process",
   "what": "The process takes no τ step.",
   "why": "Not documented.",
   "breaks": "Nothing. It is a definition.",
   "example": "A thread at an external recv.",
   "rocq": "relation/Readiness.v: stable_p"
  },
  "rd.p-term": {
   "title": "No offer means terminated",
   "what": "A stable process that offers no interface end is terminated.",
   "why": "Not documented.",
   "breaks": "Nothing. It is a definition.",
   "example": "(∅, {∗}).",
   "rocq": "relation/Readiness.v: ready_p"
  },
  "rd.above-offered": {
   "title": "above_offered",
   "what": "Every interface end not offered has an offered end below its partner point.",
   "why": "Proposal §2.6.",
   "breaks": "Nothing. It is a definition.",
   "example": "above_offered W Σ off.",
   "rocq": "relation/Readiness.v: above_offered"
  },
  "P.strict": {
   "title": "Strict later worlds only",
   "what": "Each unfolding of P holds in every strict W₁ ⊒ W.",
   "why": "Decision after S4.15. With every W₁ ⊒ W, Q-Recv can deliver ends at points only a cyclic world orders, each component is ready round the cycle, and P-Connect and Internalize fail. adequacy and live_adequacy gain strict W.",
   "breaks": "S4.15. p₁ holding r⁺ and a⁺, p₂ holding a⁻ and d⁺, in W′ with x ≺ z the composite after receiving d⁻ on r⁺ is stuck.",
   "example": "Pbody asks strict W1.",
   "rocq": "relation/Relation.v: Pbody"
  },
  "P.fuse": {
   "title": "(fuse)",
   "what": "Every unfolding of P holds after every fusion h, D with fuse_ok, at sdrop D (h Σ) and pfuse h D p.",
   "why": "Decision after S4.18. With (rename) alone, h may join two unrelated interface ends into one channel and P-Connect fails. Closure by definition makes the renaming of P a projection (Q16, after S4.12).",
   "breaks": "S4.18. close (send ⟨∗, d⁺⟩) ∥ let ⟨u, y⟩ = recv e⁺ in close y, with h mapping d and e onto one channel, has a τ message at unadvanced interface types.",
   "example": "Prel_fuse, Prel_internalize.",
   "rocq": "relation/Relation.v: Pbody"
  },
  "P-Stop": {
   "title": "P-Stop",
   "what": "An irreducible process has no restricted channel, a main value in V and only ∗ elsewhere.",
   "why": "Not documented.",
   "breaks": "Nothing. It is a definition.",
   "example": "(∅, {∗, ∗}) at T = ∗.",
   "rocq": "relation/Relation.v: Pclauses"
  },
  "P-Ready": {
   "title": "P-Ready",
   "what": "A reducible process is ready against its interface.",
   "why": "B2.",
   "breaks": "Nothing. It is a definition.",
   "example": "ready_p W1 Σ p.",
   "rocq": "relation/Relation.v: Pclauses"
  },
  "P-Step": {
   "title": "P-Step",
   "what": "Every instrumented step of every lifting meets its obligation.",
   "why": "Progress.md, S3 process steps. P quantifies over istep of every lifting, not over pspec.",
   "breaks": "Nothing. It is a definition.",
   "example": "Psteps.",
   "rocq": "relation/Relation.v: Psteps"
  },
  "fuse.dcomm": {
   "title": "h commutes with duality",
   "what": "h(ō) is the partner of h(o).",
   "why": "Q16. Needed for P, where restricted channels and the partners of Q-Send and Q-Recv enter (progress.md, S4 Q16 for terms).",
   "breaks": "Nothing. It is a definition.",
   "example": "csub o₁ o₂ commutes with duality.",
   "rocq": "relation/Relation.v: dcomm"
  },
  "fuse.inj": {
   "title": "Injective on held ends",
   "what": "h never merges two held ends.",
   "why": "Q16 refinement after S4.10. csub fuses ō₁ and o₂, so no bijection covers it, but it is injective on the other component's held ends.",
   "breaks": "Nothing. It is a definition.",
   "example": "pren_ok_csub.",
   "rocq": "relation/Relation.v: fuse_ok"
  },
  "fuse.partners": {
   "title": "Partners only on D",
   "what": "Two held ends become partners only if they were, or their channel lies in D.",
   "why": "S4.18. Without it, h joins unrelated interface ends into one channel.",
   "breaks": "The S4.18 counterexample.",
   "example": "D = ∅ forbids new pairs.",
   "rocq": "relation/Relation.v: fuse_ok"
  },
  "fuse.D": {
   "title": "D apart from C",
   "what": "The newly restricted channels are new.",
   "why": "Not documented.",
   "breaks": "Nothing. It is a definition.",
   "example": "D ## set_map (gch h) p.1.",
   "rocq": "relation/Relation.v: fuse_ok"
  },
  "fuse.dpairs": {
   "title": "dpairs",
   "what": "Both ends of every channel of D are in the renamed interface, at dual points and dual types.",
   "why": "They become restricted, so they must be a well-typed pair.",
   "breaks": "Nothing. It is a definition.",
   "example": "Internalizing c with c⁺ : S@x, c⁻ : S̄@x̄.",
   "rocq": "relation/Relation.v: dpairs"
  },
  "Q-Tau": {
   "title": "Q-Tau (Q-Admin, Q-Comm)",
   "what": "A τ step keeps the interface and costs ev_cost.",
   "why": "Progress.md, S3. Q-Admin and Q-Comm are one clause.",
   "breaks": "Nothing. It is a definition.",
   "example": "msg between two threads costs κ(give) + κ(take).",
   "rocq": "relation/Relation.v: q_tau"
  },
  "Q-Send": {
   "title": "Q-Send",
   "what": "An external send. Interface ends of the payload leave Σ, restricted ends of the payload leave C, and the partners left behind join the interface.",
   "why": "Not documented beyond §2.8.",
   "breaks": "Nothing. It is a definition.",
   "example": "Sending a restricted end d⁺ puts d⁻ into the interface.",
   "rocq": "relation/Relation.v: q_send"
  },
  "Q-Send.theta-e": {
   "title": "dom Θ_e = M ∩ ends(C)",
   "what": "The restricted ends that leave are those of the transfer set.",
   "why": "B8. Read from the transfer set of the label.",
   "breaks": "Nothing. It is a definition.",
   "example": "Θe = {d⁺}.",
   "rocq": "relation/Relation.v: q_send"
  },
  "Q-Send.split": {
   "title": "send_split",
   "what": "Θ_e and its partners Σ_e at dual types and points, Σ_e for those partners that stay.",
   "why": "Not documented.",
   "breaks": "Nothing. It is a definition.",
   "example": "Σe = {d⁻}.",
   "rocq": "relation/Relation.v: send_split"
  },
  "Q-Send.sigma-e": {
   "title": "Σ_e joins the interface",
   "what": "Partners of extruded ends become interface ends.",
   "why": "Scope extrusion.",
   "breaks": "Nothing. It is a definition.",
   "example": "d⁻ joins Σ.",
   "rocq": "relation/Relation.v: q_send"
  },
  "Q-Recv": {
   "title": "Q-Recv",
   "what": "For every incoming environment and value, the process continues with the received ends added and the channels both of whose ends it now holds restricted.",
   "why": "Not documented beyond §2.8.",
   "breaks": "Nothing. It is a definition.",
   "example": "Receiving d⁻ while holding d⁺ restricts d.",
   "rocq": "relation/Relation.v: q_recv"
  },
  "Q-Recv.ok": {
   "title": "recv_ok",
   "what": "Incoming ends are new, and those whose partner is held are dual at dual points.",
   "why": "Not documented.",
   "breaks": "Nothing. It is a definition.",
   "example": "recv_ok Σ Θ2.",
   "rocq": "relation/Relation.v: recv_ok"
  },
  "Q-Recv.back": {
   "title": "recv_back",
   "what": "Channels whose partner end the process holds or receives along become restricted.",
   "why": "Not documented.",
   "breaks": "Nothing. It is a definition.",
   "example": "recv_back Σ Θ2.",
   "rocq": "relation/Relation.v: recv_back"
  },
  "Q-Recv.env": {
   "title": "recv_env",
   "what": "The interface after the receive, without the ends that became internal.",
   "why": "Not documented.",
   "breaks": "Nothing. It is a definition.",
   "example": "recv_env Σ Θ2.",
   "rocq": "relation/Relation.v: recv_env"
  },
  "Q-Link": {
   "title": "Q-Close, Q-Select, Q-Branch, Q-Link",
   "what": "The interface versions of the term obligations.",
   "why": "Not documented.",
   "breaks": "Nothing. It is a definition.",
   "example": "q_link removes both ends from Σ.",
   "rocq": "relation/Relation.v: q_close, q_select, q_branch, q_link"
  },
  "sj.at": {
   "title": "Judgment at a set of points",
   "what": "In every later world, at every level, for every grounding disjoint from Θ, the instance is in E at the union of environments.",
   "why": "Progress.md, S4. The form of the old semantic rules.",
   "breaks": "Nothing. It is a definition.",
   "example": "sem_typed_at.",
   "rocq": "compat/SemTyped.v: sem_typed_at"
  },
  "sj.grel": {
   "title": "Grounding G",
   "what": "A substitution of values in V for Δ that splits an environment among them.",
   "why": "Progress.md, S4 groundings. It has no notation in Appendix A.",
   "breaks": "Nothing. It is a definition.",
   "example": "Grel κ n W Θ Δ γ.",
   "rocq": "compat/SemTyped.v: Grel"
  },
  "sj.den": {
   "title": "Denotation of a static future",
   "what": "The future variable stands for an arbitrary set ρ φ, the ⊥ flag for an arbitrary set B.",
   "why": "Progress.md, S4 static futures. pbot (W8) is not used, because a point no world orders does not survive the Kripke quantifier of E.",
   "breaks": "Nothing. It is a definition.",
   "example": "sf_den ρ B F.",
   "rocq": "compat/SemTyped.v: sf_den"
  },
  "sj.term": {
   "title": "Θ ; Δ ⊨ t : T and ⊫",
   "what": "The semantic term judgment, ⊨ at κ_DF and ⊫ at κ_L.",
   "why": "A.2. Θ enters erased of credits.",
   "breaks": "Nothing. It is a definition.",
   "example": "fundamental concludes it.",
   "rocq": "compat/SemTyped.v: sem_typed"
  },
  "sj.proc": {
   "title": "Σ ⊨_W p : T and ⊫_W",
   "what": "p is in P at every level.",
   "why": "A.2.",
   "breaks": "Nothing. It is a definition.",
   "example": "fundamental_proc concludes it.",
   "rocq": "relation/Adequacy.v: sem_ptyped"
  },
  "fu.zero": {
   "title": "Fuel at level 0",
   "what": "Every term has fuel at level 0.",
   "why": "Step indexing.",
   "breaks": "Nothing. It is a definition.",
   "example": "FuelE_0.",
   "rocq": "fuel/Fuel.v: mk_flevel"
  },
  "fu.rty": {
   "title": "Result σ",
   "what": "The credited type of the returned value, or thread, which returns holding no end.",
   "why": "Progress.md, S6 threads. RThread replaces CAny (T4, #37).",
   "breaks": "Nothing. It is a definition.",
   "example": "RThread for a soup thread.",
   "rocq": "fuel/Fuel.v: rty"
  },
  "fu.frame": {
   "title": "Frame d",
   "what": "The channel actions the term may still perform before it returns.",
   "why": "Frame.v, bind_needs_bound (#28). Context ticks need a frame.",
   "breaks": "Nothing. It is a definition.",
   "example": "A thread has frame ∞.",
   "rocq": "fuel/Fuel.v: Fdef"
  },
  "fu.reserve": {
   "title": "Reserve r",
   "what": "The tickets the term must still hold when it returns.",
   "why": "Not documented beyond the comment in Fuel.v.",
   "breaks": "Nothing. It is a definition.",
   "example": "A thread has reserve 0.",
   "rocq": "fuel/Fuel.v: Fdef"
  },
  "fu.Pi": {
   "title": "Protocols Π",
   "what": "The session type of each held end, with annotations.",
   "why": "Q11 and S6 protocols. Π is chosen per index next to the live environment A in the soup (decision after S8).",
   "breaks": "Nothing. It is a definition.",
   "example": "Π = {a ↦ Sa}.",
   "rocq": "fuel/Fuel.v: penv"
  },
  "fu.phi": {
   "title": "Counters φ",
   "what": "A counter per held end, in ℕ ∪ {∞}.",
   "why": "F8 and A10. Counters belong to held ends, only the holder writes them.",
   "breaks": "Nothing. It is a definition.",
   "example": "φ = {a ↦ 3}.",
   "rocq": "fuel/Fuel.v: cenv"
  },
  "fu.tk": {
   "title": "Tickets tk",
   "what": "The thread's count of link tickets.",
   "why": "F13. Tickets bound link chatter (#5, #39).",
   "breaks": "Nothing. It is a definition.",
   "example": "tk = 0 in the examples.",
   "rocq": "fuel/Fuel.v: Fdef"
  },
  "fu.refill-kripke": {
   "title": "Every refill above N",
   "what": "FuelE holds at every refill N′ above N in the order rle, finite refills by ≤ and ∞ above ∞ only.",
   "why": "Decision \"fuel is Kripke in the refill\" and its refinement after S7.5. Plain monotonicity in N fails at receive, and ≥ on ℕ ∪ {∞} lets a finite refill jump to ∞, where a received box promises nothing at finite instances.",
   "breaks": "S7.5. A thread at N = 2 forcing a received box at a finite instance has no fsem when the refill may jump to ∞.",
   "example": "rle (Some 2) (Some 3).",
   "rocq": "fuel/Fuel.v: rle, Fdef"
  },
  "fu.rename": {
   "title": "Injective renamings",
   "what": "FuelE holds for every renaming g injective on the held ends.",
   "why": "F15 and S6 renamings. A link renames the partner of the removed end in another thread.",
   "breaks": "Merging two held ends by a renaming (#25).",
   "example": "kinj g Π.",
   "rocq": "fuel/Fuel.v: kinj, renk"
  },
  "fu.val": {
   "title": "(val)",
   "what": "A value holds the reserve and is in FV at σ.",
   "why": "Not documented.",
   "breaks": "Nothing. It is a definition.",
   "example": "r ≤ tk.",
   "rocq": "fuel/Fuel.v: Fdef"
  },
  "fu.step": {
   "title": "(step)",
   "what": "Every step meets its fuel obligation at level n.",
   "why": "Not documented.",
   "breaks": "Nothing. It is a definition.",
   "example": "Fobl.",
   "rocq": "fuel/Fuel.v: Fdef, Fobl"
  },
  "fu.oneclock": {
   "title": "Every step costs one level",
   "what": "β, new, spawn and link included.",
   "why": "Decision Q10 (b), after S6. One clock fails at E-Box. The box !(f = force f) types at cost 0 and only takes β steps, so cost_fundamental would need a guard premise.",
   "breaks": "Nothing. It is a definition.",
   "example": "F-Beta at level n.",
   "rocq": "fuel/Fuel.v: Fdef"
  },
  "F-Wait": {
   "title": "F-Wait",
   "what": "No action on an idle end.",
   "why": "Decision Q5 (b), corrected form.",
   "breaks": "Nothing. It is a definition.",
   "example": "An end at Skip cannot act.",
   "rocq": "fuel/Fuel.v: f_act"
  },
  "F-Tick": {
   "title": "F-Tick",
   "what": "An action on o asks every other non-idle end of the thread to have a counter of at least 1.",
   "why": "F8. Endless postponement (#7) and endless delegation (#8). A send is an action on o, so F-Tick enforces φ|M ≥ 1 at a send (proposal §2.10).",
   "breaks": "A holder that loops on other ends forever while its partner waits (#7).",
   "example": "fuel_tick, fuel_zero_act.",
   "rocq": "fuel/Fuel.v: f_act, fspare"
  },
  "F-Tick.frame": {
   "title": "Frame ≥ 1",
   "what": "The frame has a unit for the action.",
   "why": "Context ticks without a frame (#28).",
   "breaks": "Nothing. It is a definition.",
   "example": "fle (Some 1) d.",
   "rocq": "fuel/Fuel.v: f_act"
  },
  "fu.refillop": {
   "title": "refill",
   "what": "o goes to N, every other counter ticks by one, truncated at 0.",
   "why": "F8. Counters evolve by one index-free update (§4.4).",
   "breaks": "Nothing. It is a definition.",
   "example": "refill 3 a {a ↦ 1, b ↦ 2} = {a ↦ 3, b ↦ 1}.",
   "rocq": "fuel/Fuel.v: refill"
  },
  "fu.idle": {
   "title": "idle",
   "what": "A session type that unfolds to Skip.",
   "why": "Q5 (b). Idleness only removes the ≥ 1 checks, never changes how a counter evolves (#44).",
   "breaks": "An idle end whose credit stayed fixed while its counter ticks would exceed the counter (idle_age_cex). So the typing ages idle ends by truncation at 0 (age_idle), and the controller (#20) is being retyped with it.",
   "example": "idle Skip.",
   "rocq": "fuel/Fuel.v: idle"
  },
  "F-Beta": {
   "title": "F-Beta",
   "what": "The continuation at the same state, one level lower.",
   "why": "Q10 (b).",
   "breaks": "Nothing. It is a definition.",
   "example": "f_beta.",
   "rocq": "fuel/Fuel.v: f_beta"
  },
  "F-New": {
   "title": "F-New",
   "what": "Both new ends at N with dual protocols.",
   "why": "Not documented beyond §2.10.",
   "breaks": "Nothing. It is a definition.",
   "example": "new_0 adds c± at N.",
   "rocq": "fuel/Fuel.v: f_new"
  },
  "F-New.fresh": {
   "title": "Fresh against the thread",
   "what": "The new name is fresh against the thread's own maps.",
   "why": "F16. new reusing a held name (#26, Collide.v).",
   "breaks": "Nothing. It is a definition.",
   "example": "ffresh c Π φ.",
   "rocq": "fuel/Fuel.v: ffresh"
  },
  "F-New.cnew": {
   "title": "New counters N",
   "what": "c⁺ and c⁻ start at N.",
   "why": "One refill (Q4).",
   "breaks": "Nothing. It is a definition.",
   "example": "cnew N c φ.",
   "rocq": "fuel/Fuel.v: cnew"
  },
  "F-Spawn": {
   "title": "F-Spawn",
   "what": "The child takes M with counters minus one and ⌈tk/2⌉ tickets and runs as a thread, the parent keeps ⌊tk/2⌋.",
   "why": "F13 and Q3.",
   "breaks": "Nothing. It is a definition.",
   "example": "LFCycle. The thunk takes d′ at 1.",
   "rocq": "fuel/Fuel.v: f_spawn"
  },
  "F-Spawn.held": {
   "title": "M ⊆ dom φ",
   "what": "Only held ends are handed on.",
   "why": "F17.",
   "breaks": "A box hiding channel constants (#32).",
   "example": "M = {d′}.",
   "rocq": "fuel/Fuel.v: f_spawn"
  },
  "fu.fspare": {
   "title": "fspare M",
   "what": "Every handed counter of a non-idle end is at least 1.",
   "why": "Proposal §2.10, no hand-over at counter 0. A spawn is no action, so this is the only enforcement there.",
   "breaks": "A hop at counter 0 under truncation passes 0 again for free and an end travels forever (#9).",
   "example": "fuel_zero_nospawn, fuel_zero_nosend.",
   "rocq": "fuel/Fuel.v: fspare"
  },
  "F-Spawn.child": {
   "title": "The child",
   "what": "v ∗ has thread fuel at its part of Π, counters minus one, ⌈tk/2⌉ tickets.",
   "why": "Not documented beyond §2.10.",
   "breaks": "Nothing. It is a definition.",
   "example": "App v EUnit.",
   "rocq": "fuel/Fuel.v: f_spawn"
  },
  "fu.fhand": {
   "title": "fhand",
   "what": "Handed counters lose one.",
   "why": "Every counter passed on is the holder's minus one with no truncation, which fuel_step of adequacy uses.",
   "breaks": "Nothing. It is a definition.",
   "example": "fhand {a} {a ↦ 3} = {a ↦ 2}.",
   "rocq": "fuel/Fuel.v: fhand"
  },
  "F-Spawn.tickets": {
   "title": "Ticket split",
   "what": "Child ⌈tk/2⌉, parent ⌊tk/2⌋.",
   "why": "F13. The fixed split is the only index-free split (proposal §3.4).",
   "breaks": "Nothing. It is a definition.",
   "example": "tk = 3 gives 2 and 1.",
   "rocq": "fuel/Fuel.v: f_spawn"
  },
  "F-Send": {
   "title": "F-Send",
   "what": "An action on o that hands on M with counters minus one, the payload in FV at its type and floor, the continuation with o refilled.",
   "why": "Proposal §2.10.",
   "breaks": "Nothing. It is a definition.",
   "example": "send ⟨a, y⟩ in LFGrowRing.",
   "rocq": "fuel/Fuel.v: f_send"
  },
  "F-Send.notsubj": {
   "title": "M ⊆ dom φ ∖ {o}",
   "what": "A send hands on held ends other than its subject.",
   "why": "F17 and #34.",
   "breaks": "A hole that sends its own subject or an end its context holds (#34).",
   "example": "M = {a}.",
   "rocq": "fuel/Fuel.v: f_send"
  },
  "F-Send.payload": {
   "title": "Payload in FV",
   "what": "The payload is in FV at the raw payload type T^b with its handed maps.",
   "why": "Progress.md, S6 payloads. FV reads no point, so the raw type and payload_at agree.",
   "breaks": "Nothing. It is a definition.",
   "example": "Vl n′ N (RTy T b).",
   "rocq": "fuel/Fuel.v: f_send"
  },
  "F-Recv": {
   "title": "F-Recv",
   "what": "An action on o that continues for every incoming value in FV at every lower level.",
   "why": "Not documented beyond §2.10.",
   "breaks": "Nothing. It is a definition.",
   "example": "recv b in the client loop.",
   "rocq": "fuel/Fuel.v: f_recv"
  },
  "F-Recv.forall": {
   "title": "Every incoming value",
   "what": "Any value at level j ≤ n with fresh maps.",
   "why": "Q15 makes every value of FV exact, so incoming closures hold what they mention.",
   "breaks": "fw_counterexample (S7.1). dead_thunk o is in FV, and after receiving it fw cannot spawn it.",
   "example": "∀ j Πi φi.",
   "rocq": "fuel/Fuel.v: f_recv"
  },
  "F-Close": {
   "title": "F-Close, F-Select, F-Branch",
   "what": "Actions that advance Π at o and refill o, or drop o and tick the rest at a close.",
   "why": "Not documented.",
   "breaks": "Nothing. It is a definition.",
   "example": "close c⁺.",
   "rocq": "fuel/Fuel.v: f_close, f_select, f_branch"
  },
  "F-Link": {
   "title": "F-Link",
   "what": "Linked ends must be held at dual protocols, and one ticket is spent.",
   "why": "F13 and the decision after S8.3.",
   "breaks": "Nothing. It is a definition.",
   "example": "link_tickets_fall.",
   "rocq": "fuel/Fuel.v: f_link"
  },
  "F-Link.plink": {
   "title": "plink",
   "what": "The two ends hold dual protocols up to ≃ with annotations.",
   "why": "Decision after S8.3. O-Link compares only up to annotations, and a credit mismatch at a link breaks the payload credit of a later message in the soup.",
   "breaks": "After linking o₁ and o₂ the partners form one channel, dual only if o₁ and o₂ were.",
   "example": "plink Π {o1; o2}.",
   "rocq": "fuel/Fuel.v: plink"
  },
  "F-Link.ticket": {
   "title": "tk ≥ 1",
   "what": "A link spends one ticket.",
   "why": "F13. Tickets are conserved and spent (#39).",
   "breaks": "A box that links once per round forever (c3_link_loop_not_tix, #5).",
   "example": "tk − 1.",
   "rocq": "fuel/Fuel.v: f_link"
  },
  "FV-Sess": {
   "title": "FV at S@x",
   "what": "An end with protocol S′ ≃ S and counter at least the credit.",
   "why": "Credits are lower bounds on counters (§2.11).",
   "breaks": "Nothing. It is a definition.",
   "example": "o at (S@x)^2 with counter 3.",
   "rocq": "fuel/Fuel.v: Vty TSess"
  },
  "FV-Sess.counter": {
   "title": "a ≤ f",
   "what": "The counter meets the credit.",
   "why": "Not documented beyond §2.11.",
   "breaks": "Nothing. It is a definition.",
   "example": "2 ≤ 3.",
   "rocq": "fuel/Fuel.v: Vty TSess"
  },
  "FV-Arrow": {
   "title": "FV at an arrow",
   "what": "A closure whose body has fuel for every argument, refill above N, lower level and counters at or above the floor.",
   "why": "Proposal §2.11.",
   "breaks": "Nothing. It is a definition.",
   "example": "A loop body at cost ∞.",
   "rocq": "fuel/Fuel.v: Vty TLolli"
  },
  "FV-Arrow.exact": {
   "title": "fends e = dom Π",
   "what": "The closure holds exactly the ends it mentions.",
   "why": "Decision Q15, agreed explicitly. It mirrors Q14.",
   "breaks": "fw_counterexample (v2/cost/FuelGap.v on redesign-s7). Without it fsem_of_cost is false.",
   "example": "dead_thunk_rejected.",
   "rocq": "fuel/Fuel.v: Vty TLolli"
  },
  "FV-Arrow.floor": {
   "title": "Counters ≥ h + a",
   "what": "Captured counters meet floor plus credit.",
   "why": "T2.",
   "breaks": "Nothing. It is a definition.",
   "example": "h = 1, a = 1.",
   "rocq": "fuel/Fuel.v: Vty TLolli"
  },
  "FV-Arrow.body": {
   "title": "Body fuel",
   "what": "The body has fuel at U with frame c for every ticket count that meets ϑ.",
   "why": "Not documented beyond §2.11.",
   "breaks": "Nothing. It is a definition.",
   "example": "meets t r tk.",
   "rocq": "fuel/Fuel.v: Vty TLolli"
  },
  "FV-Box": {
   "title": "FV at a box",
   "what": "A box with no ends whose body has fuel per force at every session instance.",
   "why": "Progress.md, S6 boxes.",
   "breaks": "Nothing. It is a definition.",
   "example": "ring at N = 4.",
   "rocq": "fuel/Fuel.v: Vty TBox"
  },
  "FV-Box.noends": {
   "title": "fends e = ∅",
   "what": "A box mentions no end.",
   "why": "Decision Q15.",
   "breaks": "Nothing. It is a definition.",
   "example": "ring.",
   "rocq": "fuel/Fuel.v: Vty TBox"
  },
  "FV-Box.body": {
   "title": "Body per force",
   "what": "e[!e] has fuel for every refill above N, lower level and instance in sinsts N′.",
   "why": "Progress.md, S6 boxes and S7.5.",
   "breaks": "Nothing. It is a definition.",
   "example": "sinsts N′ ss.",
   "rocq": "fuel/Fuel.v: Vty TBox"
  },
  "FV-Thread": {
   "title": "Thread result",
   "what": "A finished thread holds no end.",
   "why": "Replaces CAny (T4).",
   "breaks": "Nothing. It is a definition.",
   "example": "Π = φ = ∅.",
   "rocq": "fuel/Fuel.v: Vres"
  },
  "fu.fsem": {
   "title": "fsem",
   "what": "A thread has fuel at every level with every held end at N and one ticket count.",
   "why": "The per-thread fuel premise LF needs, obtained from typing by fsem_of_cost, never asked by ⊩ (2026-11-18).",
   "breaks": "Nothing. It is a definition.",
   "example": "fw_fsem.",
   "rocq": "fuel/Fuel.v: fsem"
  },
  "cs.csem": {
   "title": "csem",
   "what": "For every refill above N, level, injective renaming of Θ, grounding in FV and ticket count meeting ϑ, the instance has fuel at T^a with frame c.",
   "why": "Progress.md, S7 the semantic judgment. It reads no Γ, world or future, because FuelE reads none of them.",
   "breaks": "Nothing. It is a definition.",
   "example": "cost_fundamental concludes it.",
   "rocq": "cost/CostSem.v: csem"
  },
  "sp.state": {
   "title": "Soup state",
   "what": "q a configuration with thread ids, K the ownership, tk the tickets per thread.",
   "why": "F20 and progress.md S8 ownership. Rank and counters of adequacy are read off owners, so ownership is fixed outside the index.",
   "breaks": "Placement per index starves main in C1 (§4.2).",
   "example": "LFState q K tk.",
   "rocq": "soup/State.v: lfstate"
  },
  "sp.hold": {
   "title": "hold",
   "what": "The holder thread, point and counter of a held end.",
   "why": "Progress.md, S8 ownership.",
   "breaks": "Nothing. It is a definition.",
   "example": "Hold 0 ρ (Some 2).",
   "rocq": "soup/State.v: hold"
  },
  "sp.tk": {
   "title": "Tickets per thread",
   "what": "tk t for each thread.",
   "why": "Not documented.",
   "breaks": "Nothing. It is a definition.",
   "example": "s_tk a t.",
   "rocq": "soup/State.v: s_tk"
  },
  "sp.exists": {
   "title": "Chosen per index",
   "what": "The environment A, the protocols Π and the result types U are chosen at each index.",
   "why": "Decision after S8. O-New and F-New pick the session type of a new channel by separate existentials, so Π cannot be read off A.",
   "breaks": "Nothing. It is a definition.",
   "example": "∃ A Π U.",
   "rocq": "soup/Soup.v: Soup"
  },
  "sp.prim": {
   "title": "sp_prim",
   "what": "The result type is prim.",
   "why": "F22.",
   "breaks": "main returning an end (#19).",
   "example": "prim ∗.",
   "rocq": "soup/State.v: sp_prim"
  },
  "sp.rel": {
   "title": "sp_rel",
   "what": "Every thread is in E[live] at its part of A, at the empty future.",
   "why": "Proposal §2.12. The per-thread live relation rejects the infinite spawn chain (#40).",
   "breaks": "Nothing. It is a definition.",
   "example": "Erl (kres K t A) (U t) e.",
   "rocq": "soup/State.v: sp_rel"
  },
  "sp.ty": {
   "title": "sp_ty",
   "what": "Each thread returns T or ∗.",
   "why": "Not documented.",
   "breaks": "Nothing. It is a definition.",
   "example": "main at T, spawned at ∗.",
   "rocq": "soup/State.v: sp_ty"
  },
  "sp.fuel": {
   "title": "sp_fuel",
   "what": "Every thread has thread fuel at its part of Π, its counters from K and its tickets.",
   "why": "Proposal §2.12.",
   "breaks": "Nothing. It is a definition.",
   "example": "Frl (kres K t Π) (ctrs K t) (tk t) e.",
   "rocq": "soup/State.v: sp_fuel"
  },
  "sp.pts": {
   "title": "sp_pts",
   "what": "The points of A are those of K.",
   "why": "Points are fixed outside the index (§4.2).",
   "breaks": "Nothing. It is a definition.",
   "example": "snd <$> A = h_pt <$> K.",
   "rocq": "soup/State.v: sp_pts"
  },
  "sp.dom": {
   "title": "sp_dom",
   "what": "Π and K have the same ends.",
   "why": "Not documented.",
   "breaks": "Nothing. It is a definition.",
   "example": "dom Π = dom K.",
   "rocq": "soup/State.v: sp_dom"
  },
  "sp.owner": {
   "title": "sp_owner",
   "what": "Every holder is a thread of q.",
   "why": "Not documented.",
   "breaks": "Nothing. It is a definition.",
   "example": "is_Some (q.2 !! h_th).",
   "rocq": "soup/State.v: sp_owner"
  },
  "sp.closed": {
   "title": "sp_closed",
   "what": "A held end is restricted or in the interface.",
   "why": "Not documented.",
   "breaks": "Nothing. It is a definition.",
   "example": "ech o ∈ C ∨ o ∈ Σ.",
   "rocq": "soup/State.v: sp_closed"
  },
  "sp.pair": {
   "title": "sp_pair",
   "what": "An internal end's partner is held.",
   "why": "Proposal §2.12, per channel.",
   "breaks": "Nothing. It is a definition.",
   "example": "Both ends of c in LFClose.",
   "rocq": "soup/State.v: sp_pair"
  },
  "sp.sdual": {
   "title": "sp_sdual",
   "what": "Internal partners sit at dual points with session types dual up to annotations.",
   "why": "Proposal §2.12.",
   "breaks": "Nothing. It is a definition.",
   "example": "x′ = x̄.",
   "rocq": "soup/State.v: sp_sdual"
  },
  "sp.pdual": {
   "title": "sp_pdual",
   "what": "Internal partners hold protocols dual up to ≃ with annotations.",
   "why": "Progress.md, S8 the protocol map. Adequacy reads idleness off Π, and idle_dual transfers it across a pair.",
   "breaks": "Nothing. It is a definition.",
   "example": "Π(c⁻) ≃ dual Π(c⁺).",
   "rocq": "soup/State.v: sp_pdual"
  },
  "sp.sig": {
   "title": "sp_sig",
   "what": "Interface ends are held at their entry of Σ.",
   "why": "Not documented.",
   "breaks": "Nothing. It is a definition.",
   "example": "A !! o = Σ !! o.",
   "rocq": "soup/State.v: sp_sig"
  },
  "sp.psig": {
   "title": "sp_psig",
   "what": "Interface ends hold their session type of Σ in Π.",
   "why": "Progress.md, S9 the exact cut.",
   "breaks": "Nothing. It is a definition.",
   "example": "Π !! o = Some S.",
   "rocq": "soup/State.v: sp_psig"
  },
  "sp.fin": {
   "title": "sp_fin",
   "what": "Every counter in K is finite.",
   "why": "Progress.md, S8 finite counters. The measure of adequacy reads a counter as a natural number.",
   "breaks": "Nothing. It is a definition.",
   "example": "is_Some h_ctr.",
   "rocq": "soup/State.v: sp_fin"
  },
  "sp.lfsem": {
   "title": "Σ ⊪_W p : T",
   "what": "Some refill and state erase to p, and the state is in the soup at every index.",
   "why": "Q12, decided 2026-11-18. LF drops the process conjunct, and soup_no_tau_divergence gives what it was kept for.",
   "breaks": "Nothing. It is a definition.",
   "example": "lf_fundamental concludes it.",
   "rocq": "soup/Soup.v: lf_sem"
  },
  "sp.exists-before-forall": {
   "title": "∃ before ∀ n",
   "what": "N and the state a are fixed before the index quantifier.",
   "why": "F20. Ownership, points and counters must be the same at every index (§4.2).",
   "breaks": "C1 without a ceiling. A placement chosen per index lets main starve in every fair run (§4.2).",
   "example": "∃ N a, … ∀ n.",
   "rocq": "soup/Soup.v: lf_sem"
  },
  "sp.next": {
   "title": "lf_next",
   "what": "The index-free update along an event. Creation places new ends with counter N, actions move and refill, transfers move with counter minus one, links spend a ticket and rename, spawns split tickets.",
   "why": "Proposal §2.12. lfsoup_step preserves the soup along it.",
   "breaks": "Nothing. It is a definition.",
   "example": "lfsoup_step.",
   "rocq": "soup/Soup.v: lf_next"
  },
  "th.adequacy": {
   "title": "adequacy",
   "what": "A closed process in the DF process relation at every level, in a strict world, is deadlock free.",
   "why": "A.3. strict W was added after S4.15, because P at a non-strict world is vacuous.",
   "breaks": "Without strict W the premise holds vacuously at a cyclic world.",
   "example": "soundness uses it.",
   "rocq": "relation/Adequacy.v: adequacy"
  },
  "th.live-adequacy": {
   "title": "live_adequacy",
   "what": "The same at κ_L, plus no τ-divergence.",
   "why": "Administrative steps cost nothing in κ_L and are read inside the least fixpoint, so no reachable state admits an infinite sequence of them (comment in Adequacy.v).",
   "breaks": "Nothing. It is a definition.",
   "example": "live_soundness uses it.",
   "rocq": "relation/Adequacy.v: live_adequacy"
  },
  "th.adequacy-gen": {
   "title": "adequacy_gen",
   "what": "Adequacy for every cost table.",
   "why": "A τ step lowers the level by at most cmax κ, so the level reaches every state of a run.",
   "breaks": "Nothing. It is a definition.",
   "example": "Instantiated at κ_DF and κ_L.",
   "rocq": "relation/Adequacy.v: adequacy_gen"
  },
  "th.lf-adequacy": {
   "title": "lf_adequacy",
   "what": "A closed soup in a lock-free world is lock free.",
   "why": "Proposal §2.13. The proof instantiates lf_run_criterion with the rank of a pending thread, the point of the end it offers, and the measure (tickets left, counter).",
   "breaks": "Nothing. It is a definition.",
   "example": "cl_lock_free.",
   "rocq": "soup/LFAdequacy.v: lf_adequacy"
  },
  "th.lf-thread-progress": {
   "title": "lf_thread_progress",
   "what": "Every weakly fair maximal run makes every thread progress.",
   "why": "A.3.",
   "breaks": "Nothing. It is a definition.",
   "example": "Each LF example.",
   "rocq": "soup/LFAdequacy.v: lf_thread_progress"
  },
  "th.soup-no-tau": {
   "title": "soup_no_tau_divergence",
   "what": "A closed soup at every index has no τ-divergence.",
   "why": "Q12. It gives what the live process conjunct of LF was kept for, so ⊪ is the soup alone.",
   "breaks": "Nothing. It is a definition.",
   "example": "The infinite spawn chain is rejected per thread.",
   "rocq": "soup/SoupTau.v: soup_no_tau_divergence"
  },
  "th.lfsoup-step": {
   "title": "lfsoup_step",
   "what": "A closed step moves the soup from index n + 1 to n along lf_next.",
   "why": "Progress.md, S8 one clock. Each thread pays its own side of a synchronization.",
   "breaks": "Nothing. It is a definition.",
   "example": "lfsoup_run iterates it.",
   "rocq": "soup/SoupRun.v: lfsoup_step"
  },
  "th.fundamental": {
   "title": "fundamental",
   "what": "DF typing under empty Γ in a strict world implies ⊨.",
   "why": "A.3.",
   "breaks": "Nothing. It is a definition.",
   "example": "spawn_gap refuted it before the O-Spawn decisions.",
   "rocq": "static/Fundamental.v: fundamental"
  },
  "th.fundamental-typed": {
   "title": "fundamental_typed",
   "what": "The merged judgment at any N implies ⊨ at the erased environments and type.",
   "why": "Progress.md, S5. The merged judgment enters by typed_dftyped.",
   "breaks": "Nothing. It is a definition.",
   "example": "cs_typed at N = ∞.",
   "rocq": "static/Fundamental.v: fundamental_typed"
  },
  "th.live-fundamental": {
   "title": "live_fundamental",
   "what": "DF typing with the guard implies ⊫.",
   "why": "A.3 and decision on the guard (2026-11-18).",
   "breaks": "Without the guard, live_fundamental_false (#14).",
   "example": "loop_guarded.",
   "rocq": "static/LiveFundamental.v: live_fundamental"
  },
  "th.live-fundamental-typed": {
   "title": "live_fundamental_typed",
   "what": "The merged judgment with the guard implies ⊫ at erased types.",
   "why": "lf_p_term uses it at Some N.",
   "breaks": "Nothing. It is a definition.",
   "example": "P-Term of ⊩.",
   "rocq": "static/LiveFundamental.v: live_fundamental_typed"
  },
  "th.fundamental-proc": {
   "title": "fundamental_proc",
   "what": "Process typing implies ⊨_W.",
   "why": "One induction on ptyped using sem_p_term and sem_p_connect.",
   "breaks": "Nothing. It is a definition.",
   "example": "soundness.",
   "rocq": "static/FundamentalProc.v: fundamental_proc"
  },
  "th.live-fundamental-proc": {
   "title": "live_fundamental_proc",
   "what": "Process typing with ⊢▷ p implies ⊫_W.",
   "why": "A.3.",
   "breaks": "Nothing. It is a definition.",
   "example": "live_soundness.",
   "rocq": "static/FundamentalProc.v: live_fundamental_proc"
  },
  "th.lf-fundamental": {
   "title": "lf_fundamental",
   "what": "Lock-free process typing implies ⊪_W.",
   "why": "The proof reads fsem^N off the typing through fsem_of_cost and the live relation through live_fundamental_typed (comment in LFTyped.v).",
   "breaks": "Nothing. It is a definition.",
   "example": "lf_soundness.",
   "rocq": "soup/LFTyped.v: lf_fundamental"
  },
  "th.sem-p-term": {
   "title": "sem_p_term",
   "what": "A thread in E at the empty future with a well-formed split of its ends is a process in P.",
   "why": "Progress.md, S4.33. A spawn splits the environment by O-Spawn and P-Connect composes parent and child.",
   "breaks": "Nothing. It is a definition.",
   "example": "P-Term of ⊢ and ⊩.",
   "rocq": "compat/PTerm.v: sem_p_term"
  },
  "th.sth": {
   "title": "sth",
   "what": "The environment of a single thread. Θ = Σ ∪ Θ_B, Θ_B covers C, Σ apart from C, pfree Σ, and dpairs C Θ_B.",
   "why": "pfree is the decision of 2026-11-18.",
   "breaks": "Nothing. It is a definition.",
   "example": "Σ = ∅, C = ∅ for a source program.",
   "rocq": "compat/PTerm.v: sth"
  },
  "th.sem-p-connect": {
   "title": "sem_p_connect",
   "what": "Two components in P in their worlds compose in the join, given conn.",
   "why": "Two-world composition (W7).",
   "breaks": "Nothing. It is a definition.",
   "example": "LFClose composes two closes.",
   "rocq": "compat/ConnectP.v: sem_p_connect"
  },
  "th.lf-p-term": {
   "title": "lf_p_term",
   "what": "The premises of lf_term in a strict world give ⊪ for one thread.",
   "why": "A.4 names.",
   "breaks": "Nothing. It is a definition.",
   "example": "cl_term.",
   "rocq": "soup/LFCompose.v: lf_p_term"
  },
  "th.Erel-bind": {
   "title": "Erel_bind",
   "what": "E is closed under evaluation frames, for every κ, with the frame's heads in the hole's future.",
   "why": "Proposal §2.8 and progress.md S4 bind. No strictness and no bound on the frame's heads. The ends a hole acts on are its own (Erel_sends).",
   "breaks": "Nothing. It is a definition.",
   "example": "Every compatibility lemma with a subterm.",
   "rocq": "compat/Bind.v: Erel_bind"
  },
  "th.soundness": {
   "title": "soundness",
   "what": "A closed typed process in a strict world is deadlock free.",
   "why": "fundamental_proc then adequacy.",
   "breaks": "Nothing. It is a definition.",
   "example": "Through typed_dftyped and soundness_source, cy_typed gives Cycle deadlock free.",
   "rocq": "static/FundamentalProc.v: soundness"
  },
  "th.live-soundness": {
   "title": "live_soundness",
   "what": "With the guard, also no τ-divergence.",
   "why": "live_fundamental_proc then live_adequacy.",
   "breaks": "Nothing. It is a definition.",
   "example": "loop and stage are guarded.",
   "rocq": "static/FundamentalProc.v: live_soundness"
  },
  "th.soundness-source": {
   "title": "soundness_source",
   "what": "A closed source term of prim type typed in a strict world is deadlock free. No creation constraint.",
   "why": "A.5. Fresh roots replace the created hypotheses of inventory row S6 (proposal §1.3), so one theorem without a constraint remains.",
   "breaks": "Nothing. It is a definition.",
   "example": "Every DF example.",
   "rocq": "static/FundamentalProc.v: soundness_source"
  },
  "th.lf-soundness": {
   "title": "lf_soundness",
   "what": "A closed process typed by ⊩ in a lock-free world is lock free.",
   "why": "lf_fundamental then lf_adequacy.",
   "breaks": "Nothing. It is a definition.",
   "example": "cy_lock_free and the other LF examples.",
   "rocq": "soup/LFTyped.v: lf_soundness"
  },
  "th.lf-soundness-source": {
   "title": "lf_soundness_source",
   "what": "A guarded closed source term typed at Some N with a ticket count meeting ϑ is lock free.",
   "why": "A.3.",
   "breaks": "Nothing. It is a definition.",
   "example": "The six LF examples.",
   "rocq": "soup/LFCompose.v: lf_soundness_source"
  },
  "th.conservative": {
   "title": "conservative",
   "what": "The merged judgment at N = ∞ and the DF judgment type the same erased programs.",
   "why": "Q11. DF typing is the instance N = ∞.",
   "breaks": "Nothing. It is a definition.",
   "example": "cs_typed from cs_dftyped.",
   "rocq": "static/Conservativity.v: conservative"
  },
  "th.typed-dftyped": {
   "title": "typed_dftyped",
   "what": "Erasing annotations of a merged derivation at any N gives a DF derivation.",
   "why": "Proposal §2.17.",
   "breaks": "Nothing. It is a definition.",
   "example": "LF typings imply DF typings.",
   "rocq": "static/Conservativity.v: typed_dftyped"
  },
  "th.live-sub-df": {
   "title": "live_sub_df",
   "what": "At first-order result types, ⊫ implies ⊨.",
   "why": "Quirk G2. live ⊆ DF stays at box-free results (author, 2026-11-18).",
   "breaks": "Nothing. It is a definition.",
   "example": "Every example with result ∗.",
   "rocq": "compat/LiveDF.v: live_sub_df"
  },
  "th.tshape": {
   "title": "tshape",
   "what": "Built from ∗, S@x, ⊗, ⊕ and ∃. No arrow and no box.",
   "why": "For such T, V reads no E, so V is the same for both tables at every level (Vrel_shape).",
   "breaks": "Nothing. It is a definition.",
   "example": "tshape ∗.",
   "rocq": "compat/LiveDF.v: tshape"
  },
  "th.cost-fundamental": {
   "title": "cost_fundamental",
   "what": "The merged judgment implies the semantic cost judgment.",
   "why": "S7. E-Abs, E-Box and E-SpawnLam take the facts of their term from typed_tfacts.",
   "breaks": "Nothing. It is a definition.",
   "example": "fw_fsem.",
   "rocq": "cost/CostFund.v: cost_fundamental"
  },
  "th.fsem-of-cost": {
   "title": "fsem_of_cost",
   "what": "A closed typed thread with credits at most N and a ticket count meeting ϑ at reserve 0 has fsem with the session types of its ends.",
   "why": "Progress.md, S7. P-Term gives credit N to every end.",
   "breaks": "Before Q15, fw o was typed and had no fsem (fw_counterexample).",
   "example": "fw_fsem.",
   "rocq": "cost/CostFund.v: fsem_of_cost"
  }
 },
 "examples": [
  {
   "id": "ex-cs",
   "title": "Client and server cycle (ClientServer)",
   "modes": [
    "df",
    "live",
    "lf"
   ],
   "code": "main = let (a, a′) = new_0 in\n       let (a, ⟨b, b′⟩) = new_κ a in\n       let () = spawn (λu. let () = u in (force srv) ⟨a′, b′⟩) in\n       (force cli) ⟨a, b⟩\ncli  = !(f = λp. let (a, b) = p in let a = send ⟨∗, a⟩ in\n                let (u, b) = recv b in let () = u in (force f) ⟨a, b⟩)\nsrv  = !(g = λp. let (a, b) = p in let (u, a) = recv a in let () = u in\n                let b = send ⟨∗, b⟩ in (force g) ⟨a, b⟩)\n-- both boxes : □∀ι κ ζ. C. ∗ ⊸ (S1@ι ⊗ S2@κ ⊸^ζ ∗)\n-- C = {ι+k ≺ (κ+k)‾, κ+k ≺ (ι+k+1)‾, ι+k ≺ ζ, κ+k ≺ ζ | k}",
   "shows": "A cycle created by main types under family laws (Q2 (d)). a sits at a fresh root ρ, b at ρ·0 by anchoring, and Λ₀ states C at (ρ, ρ·0, ρ·1). The self call instantiates C at (ι⁺, κ⁺, ζ). Under ⊩ it types at N = 3 with credits 1 and 2 on the loop arguments, and the world is a lock-free world by a measure.",
   "rocq": "examples/ClientServer.v: cs_typed; examples/LFClientServer.v: cs_lftyped, cs_lock_free"
  },
  {
   "id": "ex-cycle",
   "title": "Cycle",
   "modes": [
    "df",
    "live",
    "lf"
   ],
   "code": "cycle = let (c, c′) = new_0 in\n        let (c, ⟨d, d′⟩) = new_0 c in\n        let () = spawn (λu. let () = u in let () = close c′ in close d′) in\n        let () = close c in close d\n-- Λ₀(r) = {r ≺ (r·0)‾, r‾ ≺ r·0}",
   "shows": "Main closes c while it holds d, so it needs ρ ≺ (ρ·0)‾. The thunk closes c′ while it holds d′, so it needs ρ̄ ≺ ρ·0. The laws of family 0 state exactly these facts. Under ⊩ it types at N = 2 with transformer offset 0.",
   "rocq": "examples/Cycle.v: cy_typed; examples/LFCycle.v: cy_lftyped, cy_lock_free"
  },
  {
   "id": "ex-between",
   "title": "A channel between two box arguments (FreshBetween)",
   "modes": [
    "df",
    "live",
    "lf"
   ],
   "code": "between : □(∀ι κ. C. ∗ ⊸ Close@ι ⊗ Close@κ ⊸^κ ∗)\nbetween = !(f = λp. let (c, e) = p in\n                    let (c, ⟨d, d′⟩) = new_0 c in\n                    let () = spawn (λu. let () = u in close d′) in\n                    let () = close c in let () = close d in close e)\n-- C = {ι ≺ κ, ι ≺ κ‾, ι ≺ δ‾, δ ≺ κ, δ ≺ κ‾},  δ = ι·0\nmain: c by new_0 at ρ, e by new_1 c at ρ·1, force between at (ρ, ρ·1)",
   "shows": "The box anchors the new channel at the end it receives at ι, so no point between two box points is needed (#52, fb_between_underivable). Lock free at N = 2.",
   "rocq": "examples/FreshBetween.v: fb_typed; examples/LFFreshBetween.v: fb_lftyped, fb_lock_free"
  },
  {
   "id": "ex-many",
   "title": "A channel that acts several times (FreshMany)",
   "modes": [
    "df",
    "live",
    "lf"
   ],
   "code": "many = !(f = λp. let (c, e) = p in\n                 let (c, ⟨d, d′⟩) = new_0 c in\n                 let () = spawn (λu. let () = u in\n                                     let (v, d′) = recv d′ in let () = v in\n                                     let (w, d′) = recv d′ in let () = w in close d′) in\n                 let () = close c in\n                 let () = close (send ⟨∗, send ⟨∗, d⟩⟩) in close e)\n-- C = {ι ≺ κ, ι ≺ κ‾, ι ≺ δ‾} ∪ {δ+k ≺ κ, δ+k ≺ κ‾ | k},  δ = ι·0",
   "shows": "An infinite box constraint. d acts at δ, δ+1 and δ+2 while e is held at κ. Lock free at N = 4, e loses 1 while c closes and 3 while d sends twice and closes.",
   "rocq": "examples/FreshMany.v: fm_typed; examples/LFFreshMany.v: fm_lftyped, fm_lock_free"
  },
  {
   "id": "ex-factory",
   "title": "The factory (FactoryEx)",
   "modes": [
    "df",
    "live",
    "lf"
   ],
   "code": "mk₀  = !(f = λu. let () = u in let (c, c′) = new_0 in\n                let () = spawn (λv. let () = v in close (send ⟨∗, c⟩)) in c′)\nmk₁  = !(f = λp. let (p, ⟨c, c′⟩) = new_0 p in\n                let () = spawn (λv. let () = v in close (send ⟨∗, c⟩)) in ⟨p, c′⟩)\nmain = let p = (force mk₀) ∗ in let ⟨p, q⟩ = (force mk₁) p in\n       let () = recvclose p in recvclose q\n-- Λ₀(r) = {r‾ ≺ r·0, r‾⁺ ≺ r·0}\n-- mk₀ : □(∗ ⊸ ∃^⊥ ι. Λ₀(ι). (?∗.Close)@ι‾)",
   "shows": "The first call creates at a fresh root and needs no point (#51, fx_no_first_call). The second anchors at the end it receives. Two variants of mk replace one term with two types. Lock free at N = 2.",
   "rocq": "examples/FactoryEx.v: fx_typed; examples/LFFactoryEx.v: fx_lftyped, fx_lock_free"
  },
  {
   "id": "ex-ring",
   "title": "The growing ring (GrowRing, Padovani 2014 Ex. III.7)",
   "modes": [
    "df",
    "live",
    "lf"
   ],
   "code": "Sch  = µα. ?(∃κ. α@κ).Close\nring : □(∀ι₁ ι₂. Cr. ∗ ⊸ (Sch@ι₁ ⊗ S̄ch@ι₂ ⊸^{ι₁+1} ∗))\nring = !(f = λp. let (x, y) = p in\n           let (y, ⟨a, a′⟩) = new_0 y in\n           let () = spawn (λw. let () = w in close (send ⟨a, y⟩)) in\n           let (x, ⟨b, b′⟩) = new_1 x in\n           let (z, x) = recv x in let () = close x in\n           let () = spawn (λw. let () = w in (force f) ⟨z, b′⟩) in\n           spawn (λw. let () = w in (force f) ⟨b, a′⟩))\nmain = let (e, e′) = new_0 in (force ring) ⟨e, e′⟩",
   "shows": "b is created by new_1 x before the receive on x, so it is anchored while x is held (the reordering of Appendix B.1). Cr holds five facts at every reachable pair. Lock free at N = 4 once the payload of Sch carries credit 2.",
   "rocq": "examples/GrowRing.v: rg_typed; examples/LFGrowRing.v: rg_lftyped, rg_lock_free"
  },
  {
   "id": "ex-close",
   "title": "Two threads closing one channel (LFClose)",
   "modes": [
    "lf"
   ],
   "code": "cl c⁺ ∥ cl c⁻,   cl o = close o\n-- each thread by lf_term over its end, cut c by lf_connect at exactly dual types",
   "shows": "The smallest use of P-Term and P-Connect of ⊩. The world has no facts and no families, which makes it a lock-free world (lfworld_bare).",
   "rocq": "examples/LFClose.v: cl_lftyped, cl_lock_free"
  },
  {
   "id": "ex-guard-neg",
   "title": "Guard rejections (GuardEx)",
   "modes": [
    "live",
    "lf"
   ],
   "code": "div_box     = !(f = force f)                         -- #14\npn_fix      = !(f = λx. (force f) x)                  -- PN's ⟨fix λx.x⟩, #13\ncx_box      = !(f = let ∗ = (force f) ∗ in λy. y)     -- GuardCex, #15\nspawn_loop  = !(f = λc. spawn (λ_. (force f) c))      -- KobForwarder shape, #12, #40",
   "shows": "Each box uses its self before any channel action, so ∅ ⊢▷ fails. The DF system keeps their typings, for instance PN's ⟨fix λx.x⟩.",
   "rocq": "examples/GuardEx.v: div_not_guarded, pn_fix_not_guarded, cx_not_guarded, spawn_loop_not_guarded"
  },
  {
   "id": "ex-guard-pos",
   "title": "Guard acceptances (GuardEx)",
   "modes": [
    "live",
    "lf"
   ],
   "code": "loop  = !(f = λx. let ⟨v, x′⟩ = recv x in (force f) x′)\nstage = !(f = λin. let ⟨v, in⟩ = recv in in let ∗ = close in in\n                  let ⟨a, b⟩ = new in let ∗ = spawn (λ_. (force f) b) in\n                  close (send ⟨v, a⟩))                  -- C2 pipeline, B.1 #4",
   "shows": "The receive ticks the context, so the self is unmarked when it is forced.",
   "rocq": "examples/GuardEx.v: loop_guarded, stage_guarded"
  },
  {
   "id": "ex-forwarder",
   "title": "The spawn forwarder (cost/Forwarder.v)",
   "modes": [
    "lf"
   ],
   "code": "fw o = let ⟨w, c⟩ = recv o in let ∗ = close c in spawn w\no : ?(∗ ⊸ ∗)^2.end\ndead_thunk q = λ_. let ∗ = Ω in close q",
   "shows": "Before Q15, dead_thunk q was in FV with no ends, and fw had no fsem after receiving it (fw_counterexample, S7.1). Q15 rejects dead_thunk, and fw gets its fsem from fsem_of_cost.",
   "rocq": "cost/Forwarder.v: dead_thunk_rejected, fw_ptyped; cost/CostFund.v: fw_fsem"
  },
  {
   "id": "ex-controller",
   "title": "The controller under ⊩ (LFController, being retyped)",
   "modes": [
    "lf"
   ],
   "code": "main = let (c, c′) = new_1 in\n       let (a, a′) = new_0 in let (a, ⟨b, b′⟩) = new_κ a in\n       let () = spawn (λu. let () = u in (force srv) ⟨⟨a′, b′⟩, c′⟩) in\n       (force cli) ⟨⟨a, b⟩, c⟩\ncli  = !(f = λp. let (q, k) = p in let (a, b) = q in\n                let a = send ⟨∗, a⟩ in let (u, b) = recv b in\n                let () = u in (force f) ⟨⟨a, b⟩, k⟩)\n-- c sits at Skip on each side, an idle end",
   "shows": "The controller (#20) is being retyped with age_idle. An idle end ages without the premise c ≤ a, and its credit falls to max(a − c, 0). With the old aging k lost credit at every step and reached the call below the parameter credit (C.6). The fuel layer already accepts idle ends, because their counters tick but skip the checks ≥ 1.",
   "rocq": "examples/LFController.v: sess_ages, idle_credit_falls, sess_sub_credit"
  }
 ]
};
