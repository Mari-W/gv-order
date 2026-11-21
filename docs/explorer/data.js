window.MAP = {
 "sections": [
  {
   "id": "syntax",
   "title": "Syntax",
   "intro": "Programs are terms of a call-by-value $\\lambda$-calculus with session-typed channels. Terms never mention points. Points appear in types and in the relation, where they order the waits of threads.",
   "blocks": [
    {
     "id": "syn-terms",
     "title": "Terms",
     "rocq": "lang/Syntax.v: expr",
     "tex": "\\begin{array}{rl}\ne ::= & \\htmlData{k=syn.var}{x} \\mid \\htmlData{k=syn.unit}{\\ast} \\mid \\htmlData{k=syn.end}{o} \\mid \\htmlData{k=syn.lam}{\\lambda e} \\mid \\htmlData{k=syn.app}{e_1\\,e_2} \\mid \\htmlData{k=syn.pair}{\\langle e_1, e_2\\rangle} \\\\\n\\mid & \\htmlData{k=syn.letu}{\\mathsf{let}\\ \\ast = e_1\\ \\mathsf{in}\\ e_2} \\mid \\htmlData{k=syn.letp}{\\mathsf{let}\\ \\langle a,b\\rangle = e_1\\ \\mathsf{in}\\ e_2} \\\\\n\\mid & \\htmlData{k=syn.inj}{\\mathsf{inj}_i\\,e} \\mid \\htmlData{k=syn.case}{\\mathsf{case}\\ e\\,(e_1)\\,(e_2)} \\\\\n\\mid & \\htmlData{k=syn.box}{!e} \\mid \\htmlData{k=syn.new}{\\mathsf{new}} \\mid \\htmlData{k=syn.op}{k}\n\\end{array}",
     "caption": "Thirteen term formers with de Bruijn variables. A box $!e$ binds itself in $e$, and $k$ ranges over the constants.",
     "modes": [
      "df",
      "lf"
     ],
     "about": {
      "why": "Typing has one rule per term former, and the semantics one head step per redex.",
      "used": [
       "sem-head",
       "r-base",
       "r-fun",
       "r-boxes"
      ]
     }
    },
    {
     "id": "syn-let",
     "title": "Derived let",
     "rocq": "lang/Syntax.v: ELet (notation)",
     "tex": "\\htmlData{k=syn.let}{\\mathsf{let}\\ a = e_1\\ \\mathsf{in}\\ e_2 \\ \\triangleq\\ \\mathsf{let}\\ \\langle a, u\\rangle = \\langle e_1, \\ast\\rangle\\ \\mathsf{in}\\ \\mathsf{let}\\ \\ast = u\\ \\mathsf{in}\\ e_2}",
     "caption": "The one-variable $\\mathsf{let}$ is notation for a pair followed by a unit elimination, with $u$ fresh.",
     "modes": [
      "df",
      "lf"
     ],
     "about": {
      "why": "Examples read better with a one-variable $\\mathsf{let}$. As notation it needs no typing rule of its own.",
      "used": [
       "r-data"
      ]
     }
    },
    {
     "id": "syn-prims",
     "title": "Constants",
     "rocq": "lang/Syntax.v: prim",
     "tex": "\\begin{array}{rl}\nk ::= & \\htmlData{k=prim.send}{\\mathsf{send}} \\mid \\htmlData{k=prim.recv}{\\mathsf{recv}} \\mid \\htmlData{k=prim.close}{\\mathsf{close}} \\mid \\htmlData{k=prim.select}{\\mathsf{select}_i} \\mid \\htmlData{k=prim.branch}{\\mathsf{branch}} \\\\\n\\mid & \\htmlData{k=prim.link}{\\mathsf{link}} \\mid \\htmlData{k=prim.spawn}{\\mathsf{spawn}} \\mid \\htmlData{k=prim.force}{\\mathsf{force}}\n\\end{array}",
     "caption": "The channel operations are constants. $\\mathsf{send}$ takes a pair $\\langle v, o\\rangle$, $\\mathsf{link}$ a pair of ends and $\\mathsf{spawn}$ a thunk.",
     "modes": [
      "df",
      "lf"
     ],
     "about": {
      "why": "As constants applied to values, the channel operations need no syntax of their own, and each has an ordinary function type.",
      "used": [
       "t-consts",
       "sem-head"
      ]
     }
    },
    {
     "id": "syn-values",
     "title": "Values",
     "rocq": "lang/Syntax.v: is_val",
     "tex": "\\htmlData{k=syn.values}{v ::= \\ast \\mid o \\mid k \\mid \\lambda e \\mid\\ !e \\mid \\langle v_1, v_2\\rangle \\mid \\mathsf{inj}_i\\,v}",
     "caption": "Unit, ends, constants, abstractions and boxes are values, and so are pairs and injections of values.",
     "modes": [
      "df",
      "lf"
     ],
     "about": {
      "why": "A thread that is a value has finished. The value relation $V$ is defined on values.",
      "used": [
       "v-rel",
       "e-rel"
      ]
     }
    },
    {
     "id": "syn-ends",
     "title": "Ends",
     "rocq": "lang/Syntax.v: cend, edual, ech",
     "tex": "\\htmlData{k=end.cend}{o ::= c^{+} \\mid c^{-}} \\qquad \\htmlData{k=end.dual}{\\overline{c^{+}} = c^{-}\\quad \\overline{c^{-}} = c^{+}} \\qquad \\htmlData{k=end.ech}{\\mathsf{ech}(c^{\\pm}) = c}",
     "caption": "An end $o$ belongs to the channel $\\mathsf{ech}\\,o$, and $\\overline{o}$ is the other end of that channel.",
     "modes": [
      "df",
      "lf"
     ],
     "about": {
      "why": "Two threads hold the two ends of a channel. Naming ends instead of channels gives each end its own type, point and counter.",
      "used": [
       "syn-fends",
       "syn-csub",
       "t-contexts"
      ]
     }
    },
    {
     "id": "syn-fends",
     "title": "Ends a term mentions",
     "rocq": "lang/Syntax.v: fends, fchans",
     "tex": "\\htmlData{k=syn.fends}{\\mathsf{fends}(e)} \\qquad \\htmlData{k=syn.fchans}{\\mathsf{fchans}(e) = \\mathsf{ech}[\\mathsf{fends}(e)]}",
     "caption": "$\\mathsf{fends}(e)$ is the set of ends in $e$, and $\\mathsf{fchans}(e)$ the set of their channels.",
     "modes": [
      "df",
      "lf"
     ],
     "about": {
      "why": "The relation reads ownership off terms. A closure or a payload owns exactly the ends in it, and the relation checks this when a value is spawned or sent.",
      "used": [
       "v-rel",
       "e-obl"
      ]
     }
    },
    {
     "id": "syn-procs",
     "title": "Processes and configurations",
     "rocq": "lang/Syntax.v: proc, lang/Process.v: config, erase",
     "tex": "\\begin{array}{l}\n\\htmlData{k=proc.proc}{p = (C, E)} \\qquad \\htmlData{k=proc.config}{q = (C, M),\\ M : \\mathbb{N} \\rightharpoonup \\mathsf{Expr}} \\\\\n\\htmlData{k=proc.erase}{\\mathsf{erase}(C, M) = (C, \\{\\!|\\, M(i) \\mid i \\,|\\!\\})}\n\\end{array}",
     "caption": "A process is a finite set $C$ of restricted channels and a finite multiset $E$ of threads. A configuration names its threads by $i \\in \\mathrm{dom}\\,M$.",
     "modes": [
      "df",
      "lf"
     ],
     "about": {
      "why": "A running program is a set of threads together with its private channels. A channel is restricted when both of its ends are inside the process.",
      "used": [
       "sem-proc",
       "p-typing",
       "p-rel"
      ]
     }
    },
    {
     "id": "syn-points",
     "title": "Points",
     "rocq": "types/Points.v: pname, point",
     "tex": "\\begin{array}{l}\nr ::= \\htmlData{k=pt.const}{a} \\mid \\htmlData{k=pt.var}{\\iota} \\qquad x ::= r \\mid \\htmlData{k=pt.shift}{x^{+}} \\mid \\htmlData{k=pt.field}{x\\cdot\\kappa} \\mid \\htmlData{k=pt.dual}{\\overline{x}} \\\\\n\\htmlData{k=pt.laws}{\\overline{\\overline{x}} = x \\quad \\overline{x}\\cdot\\kappa = x\\cdot\\kappa \\quad \\overline{x^{+}} = \\overline{x}^{+}}\n\\end{array}",
     "caption": "A point $x$ has a root, a constant $a$ or a variable $\\iota$. $\\overline{x}$ flips its polarity, $x^{+}$ raises its offset, and $x\\cdot\\kappa$ is one of its fields.",
     "modes": [
      "df",
      "lf"
     ],
     "about": {
      "why": "Points order the waits of threads. Each end has a point, and a thread may wait at a point only below the points of the ends it still holds.",
      "used": [
       "syn-moves",
       "w-world",
       "t-side"
      ]
     }
    },
    {
     "id": "syn-moves",
     "title": "Where an end moves",
     "rocq": "types/Points.v: sel_pt, bra_pt, payload_pts",
     "tex": "\\begin{array}{l}\nx \\;\\mapsto\\; \\htmlData{k=pt.shift}{x^{+}} \\qquad \\htmlData{k=sx.kappai}{\\kappa_{\\mathsf{false}} = 0 \\quad \\kappa_{\\mathsf{true}} = 1} \\\\\n\\htmlData{k=pt.sel}{\\mathsf{sel\\_pt}\\,x\\,i = \\overline{x\\cdot\\kappa_i}} \\qquad \\htmlData{k=pt.bra}{\\mathsf{bra\\_pt}\\,x\\,i = x\\cdot\\kappa_i} \\qquad \\htmlData{k=pt.payload}{\\mathsf{payload\\_pts}\\,x\\,m = (x\\cdot 0, \\dots, x\\cdot(m-1))}\n\\end{array}",
     "caption": "An action moves an end from $x$ to $x^{+}$, and a choice moves it to a field of $x$. The $j$-th payload end of a message at $x$ arrives at $x\\cdot j$.",
     "modes": [
      "df",
      "lf"
     ],
     "about": {
      "why": "The point of an end changes as its protocol advances. One point per end therefore describes a whole protocol, and no action needs a point of its own.",
      "example": "An end at $x$ that sends twice is at $x^{++}$ afterwards.",
      "used": [
       "r-act",
       "ty-payload"
      ]
     }
    },
    {
     "id": "syn-labels",
     "title": "Field labels",
     "rocq": "lang/Syntax.v: field",
     "tex": "\\htmlData{k=lbl.field}{\\kappa \\in \\mathbb{N}}",
     "caption": "Field labels $\\kappa$ are natural numbers, and $x\\cdot\\kappa$ is the field $\\kappa$ of the point $x$.",
     "modes": [
      "df",
      "lf"
     ],
     "about": {
      "why": "Fields give payload ends and the continuations of a choice points of their own, each related to the point of the carrier.",
      "used": [
       "syn-moves",
       "r-new"
      ]
     }
    },
    {
     "id": "syn-csub",
     "title": "Link substitution",
     "rocq": "lang/Syntax.v: csub",
     "tex": "\\htmlData{k=link.csub}{\\mathsf{csub}\\,o_1\\,o_2\\,(o) = \\begin{cases} o_2 & o = \\overline{o_1} \\\\ \\overline{o_2} & o = o_1 \\\\ o & o \\notin \\{o_1, \\overline{o_1}\\} \\end{cases}}",
     "caption": "A link of $o_1$ and $o_2$ renames $\\overline{o_1}$ to $o_2$ in the other threads, so that the two remaining ends form one channel.",
     "modes": [
      "df",
      "lf"
     ],
     "about": {
      "why": "After a link, the threads holding $\\overline{o_1}$ and $\\overline{o_2}$ communicate with each other directly.",
      "used": [
       "sem-proc",
       "r-act"
      ]
     }
    }
   ]
  },
  {
   "id": "semantics",
   "title": "Semantics",
   "intro": "A thread steps with a label, and a process steps by one or two thread steps. The section ends with the three properties the theorems establish, deadlock freedom, absence of internal divergence and lock freedom.",
   "blocks": [
    {
     "id": "sem-labels",
     "title": "Thread labels",
     "rocq": "lang/Semantics.v: tlabel, slabel",
     "tex": "\\begin{array}{rl}\n\\alpha ::= & \\htmlData{k=lbl.beta}{\\beta} \\mid \\htmlData{k=lbl.new}{\\mathsf{new}\\,c} \\mid \\htmlData{k=lbl.spawn}{\\mathsf{spawn}\\,v} \\mid \\htmlData{k=se.slabel}{\\sigma} \\\\\n\\sigma ::= & \\htmlData{k=lbl.send}{o!v} \\mid \\htmlData{k=lbl.recv}{o?v} \\mid \\htmlData{k=lbl.close}{o\\,\\mathsf{end}} \\mid \\htmlData{k=lbl.sel}{o \\lhd i} \\mid \\htmlData{k=lbl.bra}{o \\rhd i} \\mid \\htmlData{k=lbl.link}{\\leftrightarrow\\{o_1,o_2\\}}\n\\end{array}",
     "caption": "The label $\\beta$ stands for application, unit and pair elimination, case and force. A session label $\\sigma$ is an action offered on an end.",
     "modes": [
      "df",
      "lf"
     ],
     "about": {
      "why": "An internal step needs no other thread. A session label must be matched by the dual label of another thread.",
      "used": [
       "sem-head",
       "sem-proc",
       "ct-costs"
      ]
     }
    },
    {
     "id": "sem-head",
     "title": "Head steps (T-Act rules)",
     "rocq": "lang/Semantics.v: head_step",
     "tex": "\\begin{array}{l}\n\\htmlData{k=T-Act-App}{(\\lambda e)\\,v \\xrightarrow{\\beta} \\htmlData{k=se.subst}{e[v]}} \\\\\n\\htmlData{k=T-Act-Force}{\\mathsf{force}\\,(!e) \\xrightarrow{\\beta} e[!e]} \\qquad \\htmlData{k=T-Act-New}{\\mathsf{new} \\xrightarrow{\\mathsf{new}\\,c} \\langle c^{+}, c^{-}\\rangle} \\\\\n\\htmlData{k=T-Act-Spawn}{\\mathsf{spawn}\\,v \\xrightarrow{\\mathsf{spawn}\\,v} \\ast} \\\\\n\\htmlData{k=T-Act-Send}{\\mathsf{send}\\,\\langle v, o\\rangle \\xrightarrow{o!v} o} \\\\\n\\htmlData{k=T-Act-Recv}{\\mathsf{recv}\\,o \\xrightarrow{o?v} \\langle v, o\\rangle} \\qquad \\htmlData{k=T-Act-Close}{\\mathsf{close}\\,o \\xrightarrow{o\\,\\mathsf{end}} \\ast} \\\\\n\\htmlData{k=T-Act-Select}{\\mathsf{select}_i\\,o \\xrightarrow{o\\lhd i} o} \\qquad \\htmlData{k=T-Act-Branch}{\\mathsf{branch}\\,o \\xrightarrow{o\\rhd i} \\mathsf{inj}_i\\,o} \\\\\n\\htmlData{k=T-Act-Link}{\\mathsf{link}\\,\\langle o_1, o_2\\rangle \\xrightarrow{\\leftrightarrow\\{o_1,o_2\\}} \\ast}\n\\end{array}",
     "caption": "One head step per redex. $\\mathsf{recv}\\,o$ has a step for each value $v$ it may receive.",
     "modes": [
      "df",
      "lf"
     ],
     "about": {
      "why": "Because a receive steps for each possible value, the step of a thread is defined without the other thread of the channel.",
      "used": [
       "sem-ctx",
       "sem-proc"
      ]
     }
    },
    {
     "id": "sem-ctx",
     "title": "Evaluation frames (T-Act-Ctx)",
     "rocq": "lang/Semantics.v: tstep, frame_val",
     "tex": "\\dfrac{\\htmlData{k=T-Act-Ctx}{e \\xrightarrow{\\alpha} e'}\\quad \\htmlData{k=sem.frameval}{\\mathsf{frame\\_val}\\,f}}{\\htmlData{k=se.frame}{f[e]} \\xrightarrow{\\alpha} f[e']}\\;\\textsf{T-Act-Ctx}",
     "caption": "Steps lift through one evaluation frame $f$ at a time, never under $\\lambda$ or $!$.",
     "modes": [
      "df",
      "lf"
     ],
     "about": {
      "why": "Evaluation is call by value from left to right. A $\\lambda$ or a box delays its body until it is applied or forced.",
      "used": [
       "sem-head",
       "th-terms"
      ]
     }
    },
    {
     "id": "sem-proc",
     "title": "Process steps (P-Act rules)",
     "rocq": "lang/Process.v: istep",
     "tex": "\\begin{array}{l}\n\\htmlData{k=P-Act-Beta}{M(i) \\xrightarrow{\\beta} e'} \\\\ \\qquad \\Rightarrow\\ (C, \\htmlData{k=se.upd}{M[i \\mapsto e']}) \\\\[4pt]\n\\htmlData{k=P-Act-New}{M(i) \\xrightarrow{\\mathsf{new}\\,c} e',\\ \\htmlData{k=sem.fresh-global}{c \\notin C \\cup \\htmlData{k=se.echans}{\\mathsf{echans}(M)}}} \\\\ \\qquad \\Rightarrow\\ (C \\cup \\{c\\}, M[i\\mapsto e']) \\\\[4pt]\n\\htmlData{k=P-Act-Spawn}{M(i) \\xrightarrow{\\mathsf{spawn}\\,v} e',\\ j \\notin \\mathsf{dom}\\,M} \\\\ \\qquad \\Rightarrow\\ (C, M[i\\mapsto e'][j \\mapsto v\\,\\ast]) \\\\[4pt]\n\\htmlData{k=P-Act-Msg}{M(i) \\xrightarrow{o!v} e',\\ M(j) \\xrightarrow{\\overline{o}?v} f',\\ i \\neq j} \\\\ \\qquad \\Rightarrow\\ (C, M[i\\mapsto e'][j\\mapsto f']) \\\\[4pt]\n\\htmlData{k=P-Act-Close}{M(i) \\xrightarrow{o\\,\\mathsf{end}} e',\\ M(j) \\xrightarrow{\\overline{o}\\,\\mathsf{end}} f',\\ i \\neq j,\\ \\htmlData{k=end.ech}{\\mathsf{ech}}\\,o \\in C} \\\\ \\qquad \\Rightarrow\\ (C \\setminus \\{\\htmlData{k=end.ech}{\\mathsf{ech}}\\,o\\}, M[i\\mapsto e'][j\\mapsto f']) \\\\[4pt]\n\\htmlData{k=P-Act-Choice}{M(i) \\xrightarrow{o\\lhd b} e',\\ M(j) \\xrightarrow{\\overline{o}\\rhd b} f',\\ i \\neq j} \\\\ \\qquad \\Rightarrow\\ (C, M[i\\mapsto e'][j\\mapsto f']) \\\\[4pt]\n\\htmlData{k=P-Act-Link}{M(i) \\xrightarrow{\\leftrightarrow\\{o_1,o_2\\}} e',\\ \\htmlData{k=end.ech}{\\mathsf{ech}}\\,o_1 \\in C} \\\\ \\qquad \\Rightarrow\\ (C\\setminus\\{\\htmlData{k=end.ech}{\\mathsf{ech}}\\,o_1\\}, \\htmlData{k=link.csub}{\\mathsf{csub}\\,o_1\\,o_2} \\circ M[i\\mapsto e']) \\\\[4pt]\n\\htmlData{k=P-Act-Session}{M(i) \\xrightarrow{\\sigma} e',\\ \\htmlData{k=se.subj}{\\mathsf{subj}\\,\\sigma} \\cap C = \\varnothing} \\\\ \\qquad \\Rightarrow\\ (C \\setminus \\htmlData{k=sem.sentc}{\\mathsf{sentc}\\,\\sigma}, M[i\\mapsto e'])\n\\end{array}",
     "caption": "Each rule combines the steps of one or two threads into a step of the configuration $(C, M)$.",
     "modes": [
      "df",
      "lf"
     ],
     "about": {
      "why": "A message pairs a send and a receive on the two ends of one channel. Internal steps involve one thread.",
      "used": [
       "sem-events",
       "p-rel",
       "sem-props"
      ]
     }
    },
    {
     "id": "sem-events",
     "title": "Events",
     "rocq": "lang/Process.v: event, ev_parts, ev_admin, ev_tau",
     "tex": "\\begin{array}{l}\n\\htmlData{k=ev.event}{ev ::= \\mathsf{solo}_i\\,\\alpha\\,k \\mid \\mathsf{sync}_{i,j}\\,\\sigma \\mid \\mathsf{offer}_i\\,\\sigma} \\qquad \\htmlData{k=ev.pick}{k ::= \\cdot \\mid j \\mid (o_1, o_2)} \\\\\n\\htmlData{k=ev.admin}{\\mathsf{admin} = \\{\\mathsf{solo}_i\\,\\alpha\\,k\\}} \\qquad \\htmlData{k=ev.tau}{\\tau = \\mathsf{Event} \\setminus \\{\\mathsf{offer}_i\\,\\sigma\\}} \\qquad \\htmlData{k=se.parts}{\\mathsf{parts}(ev)}\n\\end{array}",
     "caption": "An event records the threads $\\mathsf{parts}(ev)$ that took part in a step, and the channel or ends of the step.",
     "modes": [
      "df",
      "lf"
     ],
     "about": {
      "why": "Lock freedom is stated in terms of the threads that take part in steps, which the event of each step records.",
      "used": [
       "sem-props",
       "th-adeq"
      ]
     }
    },
    {
     "id": "sem-props",
     "title": "Properties",
     "rocq": "lang/Safety.v: deadlock_free, lockfree/TauThread.v: no_tau_divergence, lockfree/Fair.v: lock_free",
     "tex": "\\begin{array}{l}\n\\htmlData{k=prop.terminated}{\\mathsf{terminated}\\,p \\iff p = (\\varnothing, \\{v\\} \\uplus E),\\ E \\subseteq \\{\\ast\\}} \\\\\n\\htmlData{k=prop.df}{\\mathsf{deadlock\\_free}\\,p \\iff \\forall p'.\\ p \\htmlData{k=se.reach}{\\to^{*}} p' \\Rightarrow \\mathsf{terminated}\\,p' \\lor \\exists p''.\\ p' \\to p''}\n\\annraw{ \\\\ }\\annot{\\htmlData{k=prop.notau}{\\mathsf{no\\_tau\\_divergence}\\,p \\iff \\forall q.\\ p \\to^{*} q \\Rightarrow \\htmlData{k=se.acc}{\\mathsf{Acc}}\\ \\htmlData{k=prop.padmin}{\\to_{\\mathsf{admin}}}\\ q}}\n\\annraw{ \\\\ }\\annot{\\htmlData{k=prop.lf}{\\begin{array}{l} \\mathsf{lock\\_free}\\,p \\iff \\forall \\htmlData{k=se.run}{(r, l) \\in \\mathsf{Run}}.\\ \\htmlData{k=se.r0}{\\htmlData{k=proc.erase}{\\mathsf{erase}}(r_0) = p} \\Rightarrow \\htmlData{k=prop.maximal}{\\mathsf{maximal}\\,r\\,l} \\Rightarrow \\htmlData{k=prop.wfair}{\\mathsf{wfair}\\,r\\,l} \\Rightarrow {} \\\\ \\qquad \\htmlData{k=prop.lfrun}{\\forall i\\,t.\\ \\htmlData{k=prop.pend}{\\mathsf{pend}(r_i, t)} \\Rightarrow \\exists j \\geq i.\\ t \\in \\htmlData{k=se.parts}{\\mathsf{parts}(l_j)}} \\end{array}}}\n\\end{array}",
     "caption": "A process is deadlock free when each reachable process has terminated or can step. \\annp{It has no internal divergence when no reachable process runs internal steps forever. It is lock free when, on each weakly fair maximal run, a waiting thread later takes part in a step.}",
     "modes": [
      "df",
      "lf"
     ],
     "about": {
      "why": "The theorems establish these properties for typed processes.",
      "used": [
       "th-adeq",
       "th-sound"
      ]
     }
    }
   ]
  },
  {
   "id": "types",
   "title": "Types and worlds",
   "intro": "Types give each end a session type and a point. Worlds order the points, and typing and the relation read the order of one world. \\annp{Lock-free types add credits to ends and closures, tickets to ends, and costs to arrows and judgments.}",
   "blocks": [
    {
     "id": "ty-grammar",
     "title": "Types",
     "rocq": "types/Types.v: ty",
     "tex": "\\begin{array}{rl}\nT, U ::= & \\htmlData{k=ty.unit}{\\ast} \\mid \\htmlData{k=ty.arrow}{(T \\multimap^{\\htmlData{k=ty.arrow.ub}{u}}_{\\htmlData{k=ty.arrow.lb}{l}}[\\annot{\\htmlData{k=ty.arrow.cost}{c}}]\\, U)\\annot{^{\\htmlData{k=ty.credit}{a}}}} \\mid \\htmlData{k=ty.prod}{T \\otimes U} \\mid \\htmlData{k=ty.sum}{T \\oplus U} \\mid \\htmlData{k=ty.sess}{(S@x)\\annot{^{\\htmlData{k=ty.credit}{a}}}_{\\annot{\\htmlData{k=ty.tickets}{m}}}} \\\\\n\\mid & \\htmlData{k=ty.box}{\\Box(\\forall \\htmlData{k=pt.var}{\\bar\\iota}\\, \\htmlData{k=ty.box.svars}{\\bar\\alpha}.\\ \\htmlData{k=ty.box.constraint}{C}.\\ \\ast \\multimap^{u}[c]\\, U)} \\mid \\htmlData{k=ty.ex}{\\exists^{\\htmlData{k=ty.ex.lb}{l}} \\bar\\iota.\\ C.\\ T}\n\\end{array}",
     "variants": {
      "df": "\\begin{array}{rl} T, U ::= & \\htmlData{k=ty.unit}{\\ast} \\mid \\htmlData{k=ty.arrow}{T \\multimap^{\\htmlData{k=ty.arrow.ub}{u}}_{\\htmlData{k=ty.arrow.lb}{l}} U} \\mid \\htmlData{k=ty.prod}{T \\otimes U} \\mid \\htmlData{k=ty.sum}{T \\oplus U} \\mid \\htmlData{k=ty.sess}{S@x} \\\\ \\mid & \\htmlData{k=ty.box}{\\Box(\\forall \\htmlData{k=pt.var}{\\bar\\iota}\\, \\htmlData{k=ty.box.svars}{\\bar\\alpha}.\\ \\htmlData{k=ty.box.constraint}{C}.\\ \\ast \\multimap^{u} U)} \\mid \\htmlData{k=ty.ex}{\\exists^{\\htmlData{k=ty.ex.lb}{l}} \\bar\\iota.\\ C.\\ T} \\end{array}"
     },
     "caption": "$S@x$ is an end with session type $S$ at the point $x$. An arrow has an upper point $u$ and a lower bound $l$, and a box quantifies over points and session types under a constraint $C$. \\annp{Credits $a$ appear on ends and on closures, the two kinds of value that hold ends themselves. \\annp{The credit of an end is a lower bound on its counter.} \\annp{The credit of a closure is a lower bound on its captured counters and bounds what they lose before a call.}}",
     "modes": [
      "df",
      "lf"
     ],
     "about": {
      "why": "A type says what a value is and, for an end, at which point it waits. \\annp{A credit bounds how long the thread holding an end may postpone it.}",
      "used": [
       "t-judgment",
       "v-rel"
      ]
     }
    },
    {
     "id": "ty-session",
     "title": "Session types",
     "rocq": "types/Types.v: sty, unfoldS",
     "tex": "\\begin{array}{rl}\nS ::= & \\htmlData{k=sty.skip}{\\mathsf{Skip}} \\mid \\htmlData{k=sty.seq}{S.S} \\mid \\htmlData{k=sty.recv}{?(\\bar\\iota.\\ T)} \\mid \\htmlData{k=sty.send}{!(\\bar\\iota.\\ T)} \\mid \\htmlData{k=sty.plus}{\\oplus(S_1, S_2)} \\\\\n\\mid & \\htmlData{k=sty.with}{\\&(S_1, S_2)} \\mid \\htmlData{k=sty.close}{\\mathsf{Close}} \\mid \\htmlData{k=sty.mu}{\\mu\\alpha.S} \\mid \\htmlData{k=sty.var}{\\alpha} \\mid \\htmlData{k=sty.vard}{\\overline{\\alpha}}  \\\\\n & \\htmlData{k=sty.unfold}{\\mathsf{unfold} : \\mathsf{STy} \\to \\mathsf{STy}}\n\\end{array}",
     "caption": "Session types with sequencing $S.S$ and recursion, read through $\\mathsf{unfold}(S)$. A payload binds point variables $\\bar\\iota$, which stand for the fields of the carrier.",
     "modes": [
      "df",
      "lf"
     ],
     "about": {
      "why": "A session type describes the protocol of one end. The typing rules read its first action after unfolding recursion and leading $\\mathsf{Skip}$.",
      "used": [
       "ty-dual",
       "r-act"
      ]
     }
    },
    {
     "id": "ty-dual",
     "title": "Duality",
     "rocq": "types/Types.v: dual, sflip",
     "tex": "\\htmlData{k=sty.dual}{\\begin{array}{l}\n\\mathsf{dual}(!P) = ?P \\qquad \\mathsf{dual}(?P) = !P \\qquad \\mathsf{dual}(\\alpha) = \\overline{\\alpha} \\\\\n\\mathsf{dual}(\\oplus(S_1,S_2)) = \\&(\\mathsf{dual}\\,S_1,\\mathsf{dual}\\,S_2) \\\\\n\\mathsf{dual}(S_1.S_2) = \\mathsf{dual}\\,S_1.\\mathsf{dual}\\,S_2 \\\\\n\\mathsf{dual}(\\mu\\alpha.S) = \\mu\\alpha.\\,\\htmlData{k=sty.flip}{\\mathsf{flip}_\\alpha}(\\mathsf{dual}\\,S)\n\\end{array}}",
     "caption": "$\\mathsf{dual}$ swaps sending and receiving and keeps payloads, $\\mathsf{Skip}$ and $\\mathsf{Close}$. We write $\\overline{S}$ for $\\mathsf{dual}\\,S$.",
     "modes": [
      "df",
      "lf"
     ],
     "about": {
      "why": "The two ends of a channel follow dual protocols. Creation, linking and composition check duality.",
      "used": [
       "r-new",
       "r-act",
       "p-typing"
      ]
     }
    },
    {
     "id": "ty-equiv",
     "title": "Session equivalence",
     "rocq": "types/Types.v: sequiv, relation/Relation.v: seqv, sdual",
     "tex": "\\begin{array}{l}\n\\htmlData{k=sty.sequiv}{S \\simeq S'} \\qquad \\htmlData{k=sty.seqv}{S \\approx S' \\iff \\htmlData{k=ty2.stydf}{\\mathsf{sty\\_df}}(S) \\simeq \\mathsf{sty\\_df}(S')} \\\\\n\\htmlData{k=sty.sdual}{\\mathsf{sdual}\\,S\\,S' \\iff S' \\approx \\mathsf{dual}\\,S}\n\\end{array}",
     "caption": "$S \\simeq S'$ when the two session types describe the same protocol. $\\approx$ is $\\simeq$ after erasing annotations, and $\\mathsf{sdual}$ is duality up to annotations.",
     "modes": [
      "df",
      "lf"
     ],
     "about": {
      "why": "With recursion and $\\mathsf{Skip}$ one protocol has many spellings, and the rules compare session types up to $\\simeq$.",
      "used": [
       "t-subs",
       "v-rel"
      ]
     }
    },
    {
     "id": "ty-heads",
     "title": "Active points and lower bounds",
     "rocq": "types/Types.v: heads, hbot, types/Points.v: lbound",
     "tex": "\\begin{array}{l}\n\\htmlData{k=ty.heads}{\\mathsf{ap}(S@x) = \\{\\overline{x}\\}} \\qquad \\htmlData{k=ty.heads}{\\mathsf{ap}(T \\multimap^{u}_{l} U) = \\mathsf{ap}(\\exists^{l}\\bar\\iota.\\ C.\\ T) = \\{l\\} \\setminus \\{\\cdot\\}} \\\\\n\\htmlData{k=ty.heads}{\\mathsf{ap}(T \\otimes U) = \\mathsf{ap}(T \\oplus U) = \\mathsf{ap}(T) \\cup \\mathsf{ap}(U)} \\qquad \\htmlData{k=ty.heads}{\\mathsf{ap}(\\ast) = \\mathsf{ap}(\\Box(\\forall\\bar\\iota\\,\\bar\\alpha.\\ C.\\ \\ast \\multimap^{u} U)) = \\varnothing} \\\\\n\\htmlData{k=ty.lbound}{l ::= \\cdot \\mid \\bot \\mid x} \\qquad \\htmlData{k=ty.ubound}{u ::= \\cdot \\mid x \\mid \\top} \\qquad \\htmlData{k=ty.botord}{\\Gamma \\nvdash x \\prec \\bot \\quad \\Gamma \\nvdash \\bot \\preccurlyeq y}\n\\end{array}",
     "caption": "$\\mathsf{ap}(T)$ is the set of dual points of the ends in a value of $T$. A thread holding such a value may wait only below these points. Hidden ends contribute $\\bot$, which no fact orders against a point, so a check against a value with hidden ends fails.",
     "modes": [
      "df",
      "lf"
     ],
     "about": {
      "why": "A thread that waits while it holds a value must wait below the dual points of the ends in that value, and $\\mathsf{ap}$ computes these points from the type.",
      "used": [
       "t-side",
       "t-judgment",
       "r-fun",
       "r-ex"
      ]
     }
    },
    {
     "id": "ty-payload",
     "title": "Payloads",
     "rocq": "types/Types.v: payload_at, pscoped",
     "tex": "\\begin{array}{l}\n\\htmlData{k=ty.payload-at}{\\mathsf{payload\\_at}\\,m\\,T\\,x = T[x\\cdot 0, \\ldots, x\\cdot(m{-}1) / \\iota_0, \\ldots, \\iota_{m-1}]} \\\\\n\\htmlData{k=ty.pscoped}{\\mathsf{pscoped}\\,\\bar\\iota\\,T}\n\\end{array}",
     "caption": "A payload $!(\\bar\\iota.\\,T)$ mentions only its own point variables $\\iota_0, \\ldots, \\iota_{m-1}$. A message at the carrier point $x$ places them at the fields $x\\cdot 0, \\ldots, x\\cdot(m{-}1)$.",
     "modes": [
      "df",
      "lf"
     ],
     "about": {
      "why": "A payload is described relative to the end that sends it, so one session type serves each point the end may have.",
      "used": [
       "r-act",
       "e-obl"
      ]
     }
    },
    {
     "id": "ty-ann",
     "title": "Annotations and tickets",
     "modes": [
      "lf"
     ],
     "rocq": "types/Costs.v: fuel; types/Types.v: TSess m; types/Costs.v: tsum_ok, lgt; types/Types.v: ty_df",
     "tex": "\\begin{array}{c}\\htmlData{k=ann.fuel}{a, c, m, N \\in \\mathbb{N} \\cup \\{\\infty\\} \\qquad \\infty - c = \\infty}\\\\[3ex]\\begin{array}{l}\n\\htmlData{k=ty.tickets}{(S@x)\\annot{^{a}}_{m} \\qquad a \\leq m \\qquad m \\in \\mathbb{N} \\cup \\{\\infty\\}} \\\\\n\\htmlData{k=ann.tsum}{\\mathsf{tk}(o) + \\mathsf{tk}(\\overline{o}) \\leq N}\n\\end{array}\\\\[3ex]\\htmlData{k=ann.tydf}{\\mathsf{ty\\_df}:\\quad a = c = m = N = \\infty}\\end{array}",
     "caption": "Credits $a$, costs $c$, tickets $m$ and the bound $N$ are numbers or $\\infty$. An end has $m$ tickets with $a \\leq m$, and the tickets of the two ends of a channel sum to at most $N$, so an end with $m$ tickets has a partner with at most $N - m$. With every annotation at $\\infty$, written $\\mathsf{ty\\_df}$, lock-free typing is deadlock-free typing.",
     "about": {
      "why": "These are the numbers lock-free typing adds to types and judgments. At $\\infty$ each premise about them holds.",
      "used": [
       "t-agecap",
       "r-act",
       "r-new",
       "p-typing",
       "th-conserv",
       "th-terms"
      ]
     }
    },
    {
     "id": "ty-kinds",
     "title": "Kinds of types",
     "rocq": "types/Types.v: unlimited, tfree",
     "tex": "\\begin{array}{l}\n\\htmlData{k=ty.tfree}{\\mathsf{tfree}\\,T \\iff T \\in \\mathcal{T}_{0}, \\qquad \\mathcal{T}_{0} ::= \\ast \\mid \\Box(\\forall\\bar\\iota\\,\\bar\\alpha.\\ C.\\ \\ast \\multimap^{u} U) \\mid \\mathcal{T}_{0} \\otimes \\mathcal{T}_{0} \\mid \\mathcal{T}_{0} \\oplus \\mathcal{T}_{0}} \\\\\n\\htmlData{k=ty.unlimited}{\\mathsf{unlimited}\\,T \\iff \\exists \\bar\\iota, \\bar\\alpha, C, u, U.\\ T = \\Box(\\forall\\bar\\iota\\,\\bar\\alpha.\\ C.\\ \\ast \\multimap^{u} U)}\n\\end{array}",
     "caption": "$\\mathsf{tfree}\\,T$ holds for the types whose values hold no end, and P-Term asks it of the result type of a process. $\\mathsf{unlimited}\\,T$ holds for the types that may be copied and dropped.",
     "modes": [
      "df",
      "lf"
     ],
     "about": {
      "why": "Process results hold no end, only unlimited types may be copied or dropped, and values without ends do not age.",
      "used": [
       "p-typing",
       "t-subs",
       "t-agecap"
      ]
     }
    },
    {
     "id": "w-world",
     "title": "Worlds",
     "rocq": "types/Worlds.v: sworld, world",
     "tex": "\\begin{array}{l}\n\\htmlData{k=w.world}{W = (\\htmlData{k=w.consts}{A}, \\htmlData{k=w.facts}{\\prec_A})} \\\\\n\\htmlData{k=w.rworld}{R = (A, \\varrho)},\\ \\htmlData{k=w.rank}{\\varrho_a : \\htmlData{k=w.tree}{\\mathsf{tree}(a)} \\to \\mathsf{Ord}}\\ \\text{for}\\ a \\in A \\\\\n\\htmlData{k=w.rank}{\\varrho_a(x) < \\varrho_a(x^{+}),\\ \\varrho_a(x) < \\varrho_a(\\overline{x}^{+})}\n\\end{array}",
     "caption": "A static world $W$ has a set of roots $A$ and facts $\\prec_A$ between points with roots in $A$. A ranked world $R$ has the same roots and gives the tree of each root ordinal ranks that rise along program order.",
     "modes": [
      "df",
      "lf"
     ],
     "about": {
      "why": "Typing reads the order of a static world, and the relation reads ranks. Each creation at a fresh root adds a root and ranks its tree.",
      "used": [
       "w-order",
       "w-ext",
       "p-typing"
      ]
     }
    },
    {
     "id": "w-order",
     "title": "The order of a world",
     "rocq": "types/Worlds.v: swstep, sw_lt, w_lt, wmodels",
     "tex": "\\begin{array}{l}\n\\htmlData{k=w.lt}{\\begin{array}{l} \\prec_W\\ =\\ \\mathsf{tc}\\big(\\htmlData{k=w.ws-fact}{\\prec_A} \\\\ \\qquad\\qquad \\cup\\; \\htmlData{k=w.ws-po}{\\{x \\prec x^{+}\\}} \\;\\cup\\; \\htmlData{k=w.ws-dpo}{\\{x \\prec \\overline{x}^{+}\\}}\\big) \\end{array}} \\\\\n\\htmlData{k=ty2.le}{x \\preceq y \\iff x = y \\lor x \\prec_W y} \\\\\n\\htmlData{k=w.rlt}{R \\vDash x \\prec y \\iff \\varrho(x) < \\varrho(y)} \\\\\n\\htmlData{k=w.sat}{R \\vDash W \\iff \\forall x \\prec_A y.\\ R \\vDash x \\prec y}\n\\end{array}",
     "caption": "$\\prec_W$ is the transitive closure $\\mathsf{tc}$ of the facts together with $x \\prec x^{+}$ and $x \\prec \\overline{x}^{+}$. A ranked world orders points by their ranks, and it satisfies $W$ when each fact of $W$ holds under these ranks.",
     "modes": [
      "df",
      "lf"
     ],
     "about": {
      "why": "Besides the stated facts, the order says that an end moves up as its protocol advances. The semantic judgments at $W$ read the relation at each ranked world that satisfies $W$.",
      "used": [
       "t-contexts",
       "rd"
      ]
     }
    },
    {
     "id": "w-wf",
     "title": "Well-formed and well-founded worlds",
     "rocq": "types/Worlds.v: sworld_wf, swf, wmodels_exists; static/Contexts.v: wf_new",
     "tex": "\\begin{array}{l}\n\\htmlData{k=w.wf}{\\mathsf{world\\_wf}\\,W} \\\\\n\\htmlData{k=w.lfworld}{\\mathsf{wf}\\,W \\iff \\prec_W \\text{ is well-founded}} \\\\\n\\htmlData{k=w.wfnew}{\\begin{array}{l} \\mathsf{wf\\_new}\\,\\rho\\,C \\iff (\\forall (x \\prec y) \\in C.\\ y \\in \\htmlData{k=w.tree}{\\mathsf{tree}(\\rho)}) \\\\ \\qquad \\land\\ (C \\cup \\htmlData{k=w.po}{\\mathsf{po}}) \\cap \\mathsf{tree}(\\rho)^{2} \\text{ is well-founded} \\end{array}}\n\\end{array}",
     "caption": "P-Term and P-Connect ask a well-founded static world, and E-New asks $\\mathsf{wf\\_new}$ of a creation at a fresh root. No theorem asks anything of the world.",
     "modes": [
      "df",
      "lf"
     ],
     "about": {
      "why": "A static world has a ranked world that satisfies it exactly when its order is well-founded. A creation at a fresh root needs ranks for the new tree in each ranked world that satisfies its context, which $\\mathsf{wf\\_new}$ guarantees.",
      "used": [
       "p-typing",
       "th-sound",
       "th-adeq"
      ]
     }
    },
    {
     "id": "w-ext",
     "title": "Extension, growth, join, restriction",
     "rocq": "types/Worlds.v: wext, wgrow, swjoin, swrestrict, wf_join_iff",
     "tex": "\\begin{array}{l}\n\\htmlData{k=w.ext}{W \\sqsubseteq W'} \\qquad \\htmlData{k=w.ext}{R \\sqsubseteq R'} \\qquad \\htmlData{k=w.grow}{R \\oplus (a, \\varrho_a) = (A \\cup \\{a\\},\\ \\varrho \\cup \\varrho_a)} \\qquad \\htmlData{k=w.join}{W_1 \\sqcup W_2} \\\\\n\\htmlData{k=w.R7}{\\begin{array}{l} \\htmlData{k=w.lfworld}{\\mathsf{wf}}(W_1 \\sqcup W_2) \\iff {} \\\\ \\qquad \\mathsf{wf}\\,W_1 \\land \\mathsf{wf}\\,W_2 \\land \\mathsf{wf}(\\htmlData{k=w.restrict}{W_1|_S} \\sqcup W_2|_S),\\ S = A_1 \\cap A_2 \\end{array}}\n\\end{array}",
     "caption": "Extension $\\sqsubseteq$, growth $R \\oplus (a, \\varrho_a)$ by the ranks of a fresh root, and the join $\\sqcup$. A join is well-founded when both worlds are and their restrictions to the shared roots $S = A_1 \\cap A_2$ join to a well-founded order.",
     "modes": [
      "df",
      "lf"
     ],
     "about": {
      "why": "Ranked worlds grow during a run and never change a rank, and the relation holds in each larger world. Composition joins two static worlds and checks only their shared roots.",
      "used": [
       "p-typing",
       "v-rel",
       "e-rel",
       "p-rel"
      ]
     }
    }
   ]
  },
  {
   "id": "typing",
   "title": "Typing",
   "intro": "The typing judgment assigns each term a type under a context of facts, ends and variables, and a future, the points at which the context acts after the term. Its rules check the order facts a thread needs when it waits. Process typing builds processes from typed threads. \\annp{Lock-free typing adds credits, tickets and costs at a finite bound $N$, and the guard.}",
   "blocks": [
    {
     "id": "t-lf-credits",
     "title": "Credits",
     "rocq": "types/Types.v: TSess, TLolli; static/Contexts.v: tage, lage, thage; static/Typing.v: e_abs, e_send, e_spawn; static/Weakening.v: e_spawn_lam",
     "modes": [
      "lf"
     ],
     "tex": "\\begin{array}{lll}\\htmlData{k=lfi.credit}{\\text{credit}} & \\htmlData{k=ty.credit}{(S@x)\\annot{^{a}},\\ (T \\mathrel{\\htmlData{k=ty.arrow}{\\multimap}} U)\\annot{^{a}}} & \\text{a lower bound on the counter of an end, or of the ends a closure captured} \\\\[3pt] \\htmlData{k=lfi.cost}{\\text{cost}} & \\htmlData{k=tj.eff}{e : T\\ !\\ c} & \\text{the term performs at most $c$ actions before it returns} \\\\[3pt]  & \\htmlData{k=age.ctx}{\\Delta - c} & \\text{what is held while $e$ runs loses $c$, and each credit must be at least $c$} \\\\[3pt]  & \\htmlData{k=age.idle}{(\\mathsf{Skip}@x)\\annot{^{a}} - c} & \\text{an idle end loses credit without the check} \\\\[3pt]  & \\htmlData{k=act.refill}{(S@x^{+})^{m}_{m}} & \\text{an action returns its end with credit $m$, its tickets} \\\\[3pt] \\htmlData{k=lfi.hop}{\\text{transfer}} & \\htmlData{k=E-Send.floor}{T' - 1 \\leq T[x\\cdot i]} & \\text{a sent end loses one} \\\\[3pt]  & \\htmlData{k=E-Abs.cap}{(T \\mathrel{\\htmlData{k=ty.arrow}{\\multimap}} U)\\annot{^{a}} : \\Delta - a} & \\text{the body of a closure sees each captured end at its credit minus $a$} \\\\[3pt]  & \\htmlData{k=E-Spawn.credit}{a \\geq 1} & \\text{a spawned closure has credit at least one, so the ends of the child lose one}\\end{array}",
     "caption": "Each end has a counter at run time, the number of actions the thread holding it may perform on other ends before it must act on this end. A credit is a lower bound on that counter, so the holding thread postpones an end only finitely often. Aging lowers the credits of held values by the cost of the code that runs. An action restores its own end to its tickets $m$, and transferring an end to another thread lowers its credit by one.",
     "about": {
      "why": "Credits rule out a holding thread that acts on other ends forever while a partner waits, and an end that is passed between threads forever.",
      "example": "Postponement and endless delegation in the Examples tab have no lock-free typing.",
      "used": [
       "t-agecap",
       "r-fun",
       "r-act",
       "r-threads",
       "fv"
      ]
     }
    },
    {
     "id": "t-lf-tickets",
     "title": "Tickets",
     "rocq": "static/Typing.v: e_link, e_send, p_term; types/Costs.v: lgt, tsum_ok",
     "modes": [
      "lf"
     ],
     "tex": "\\begin{array}{lll}\\htmlData{k=lfi.tickets}{\\text{tickets}} & \\htmlData{k=ty.tickets}{(S@x)\\annot{^{a}}_{m},\\ a \\leq m} & \\text{an upper bound on the counter of an end, at least its credit} \\\\[3pt]  & \\htmlData{k=ann.tsum}{\\mathsf{tk}(o) + \\mathsf{tk}(\\overline{o}) \\leq N} & \\text{the two ends of a channel have at most $N$ tickets together} \\\\[3pt]  & \\htmlData{k=act.refill}{(S@x^{+})^{m}_{m}} & \\text{an action sets the counter of its end back to $m$} \\\\[3pt]  & \\htmlData{k=E-Send.floor}{T' - 1 \\leq T[x\\cdot i]} & \\text{an end sent as payload loses one from its counter} \\\\[3pt]  & \\htmlData{k=E-Link.tickets}{a_1 + m_2 > N,\\ a_2 + m_1 > N} & \\text{a link asks the credit of each end to exceed the partner bound $N - m$ of the other}\\end{array}",
     "caption": "An end has $m$ tickets, an upper bound on its counter, and every action on the end sets its counter back to $m$. The two ends of a channel have at most $N$ tickets together, so an end with $m$ tickets has a partner with at most $N - m$. A link asks the credit of each linked end to exceed this bound of the other end, so the new partner of a waiting thread has a lower counter than the old one.",
     "about": {
      "why": "A link acts on no end, so no counter falls at a link, and it gives a waiting thread a new partner. Tickets make the counter of the new partner lower than the counter of the old one, so a thread that relinks a waiting end forever has no typing.",
      "example": "Link refresh in the Examples tab has no lock-free typing.",
      "used": [
       "r-act",
       "r-new",
       "p-typing",
       "ty-ann",
       "soup"
      ]
     }
    },
    {
     "id": "t-lf-guard",
     "title": "The guard",
     "rocq": "static/Guard.v: lguard, acts",
     "modes": [
      "lf"
     ],
     "tex": "\\begin{array}{lll}\\htmlData{k=lfi.guard}{\\text{guard}} & \\htmlData{k=guard.judg}{\\Lambda \\vdash\\!\\triangleright t} & \\text{$t$ uses the variable of a box only after a session action} \\\\[3pt]  & \\htmlData{k=guard.box}{\\Lambda \\mathrel{\\htmlData{k=guard.judg}{\\vdash\\!\\triangleright}}\\ !b \\iff \\htmlData{k=guard.marks}{\\mathsf{true}}.\\Lambda \\mathrel{\\htmlData{k=guard.judg}{\\vdash\\!\\triangleright}} b} & \\text{a box marks its own variable} \\\\[3pt]  & \\htmlData{k=guard.var}{\\Lambda(y) = \\htmlData{k=guard.marks}{\\mathsf{false}}} & \\text{a marked variable cannot be used} \\\\[3pt]  & \\htmlData{k=guard.acts}{\\mathsf{acts}\\,e} & \\text{each evaluation of $e$ to a value performs a session action, after which the marks are cleared} \\\\[3pt]  & \\htmlData{k=guard.proc}{\\vdash\\!\\triangleright p} & \\text{each thread of the process is guarded}\\end{array}",
     "caption": "Internal steps ($\\beta$, $\\mathsf{new}$, $\\mathsf{spawn}$, $\\mathsf{link}$) change no counter. The guard requires each recursive call to come after a session action, so a thread cannot take internal steps forever.",
     "about": {
      "why": "A loop made only of internal steps runs forever without acting with any other thread. Deadlock freedom allows such a loop and lock freedom does not.",
      "example": "Guard rejections in the Examples tab, such as $!(f = \\mathsf{force}\\,f)$.",
      "used": [
       "g-guard",
       "p-typing"
      ]
     }
    },
    {
     "id": "t-lf-wf",
     "title": "A well-founded world",
     "rocq": "types/Worlds.v: wchain_lt_wf; soup/LFAdequacy.v: lf_adequacy",
     "modes": [
      "lf"
     ],
     "tex": "\\begin{array}{lll}\\htmlData{k=lfi.wf}{\\text{ranks}} & \\htmlData{k=w.rank}{\\varrho_a : \\mathsf{tree}(a) \\to \\mathsf{Ord}} & \\text{a ranked world orders points by ordinals} \\\\[3pt]  & \\htmlData{k=w.wfnew}{\\mathsf{wf\\_new}\\,\\rho\\,C} & \\text{E-New at a fresh root asks a well-founded order on the new tree} \\\\[3pt]  & \\htmlData{k=w.lfworld}{\\mathsf{wf}\\,W} & \\text{P-Term and P-Connect ask a well-founded static world} \\\\[3pt]  & \\htmlData{k=lfi.measure}{\\varrho(\\mathsf{pt}\\,o)} & \\text{lock-free adequacy ranks a waiting thread by the end it waits on}\\end{array}",
     "caption": "A waiting thread waits on the thread holding its dual end, which may itself wait at a lower point. Points have ordinal ranks, so this chain of waits ends, and the thread at its bottom can act. Typing keeps ranks possible, and lock-free adequacy asks nothing of the world.",
     "about": {
      "why": "It rules out a chain of waiting threads that grows forever, each waiting below the previous one.",
      "example": "The growing waiting chain in the Examples tab has no typing, because E-New rejects its creation.",
      "used": [
       "th-sound",
       "th-adeq",
       "w-wf",
       "r-new",
       "p-typing"
      ]
     }
    },
    {
     "id": "t-judgment",
     "title": "The typing judgment",
     "rocq": "static/Typing.v: typed, dftyped",
     "tex": "\\begin{array}{l}\\htmlData{k=tj.Gamma}{\\Gamma} ; \\htmlData{k=tj.Delta}{\\Delta} \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{\\htmlData{k=tj.F}{F}}_{\\htmlData{k=tj.W}{W}\\annot{,\\htmlData{k=tj.N}{N}}} e : T\\annot{\\ \\htmlData{k=tj.eff}{!}\\ \\varepsilon} \\\\ \\htmlData{k=tj.held}{F \\triangleleft H = F \\cup \\htmlData{k=ty.heads}{\\mathsf{ap}}(H)}\\annot{\\ \\land\\ \\htmlData{k=tj.hage}{\\mathsf{def}(H - c)}}\\annraw{ \\\\ }\\annot{\\htmlData{k=tj.eff}{\\varepsilon = c \\in \\mathbb{N} \\cup \\{\\infty\\}} \\qquad \\htmlData{k=tj.seq}{\\varepsilon_1 \\cdot \\varepsilon_2 = c_1 + c_2}}\\annraw{ \\\\ }\\annot{\\htmlData{k=tj.zero}{0} \\qquad \\htmlData{k=tj.one}{1} \\qquad \\htmlData{k=tp.max}{\\max(\\varepsilon_1, \\varepsilon_2)} \\qquad \\htmlData{k=E-Sub.cost}{\\varepsilon \\leq \\varepsilon'}}\\end{array}",
     "caption": "$\\Gamma$ holds facts, $\\Delta$ the ends and variables, and $F$ is the future. $F \\triangleleft H$ adds to the future the active points of what the thread holds while $e$ runs. The world $W$ and the bound $N$ stay fixed for a whole derivation, and the rules leave them implicit. In the lock-free mode $\\varepsilon$ is the cost of $e$.",
     "modes": [
      "df",
      "lf"
     ],
     "about": {
      "why": "Several rules run one subterm while the thread holds the values of others. Writing the future as $F \\triangleleft H$ states once what these rules need, the future of the running subterm extended by the active points of the held values.",
      "example": "E-App runs $e_1$ while holding $\\Delta_2$, written $\\Gamma ; \\Delta_1 \\vdash^{F \\triangleleft \\Delta_2} e_1 : \\ldots$",
      "used": [
       "r-fun",
       "r-data"
      ]
     }
    },
    {
     "id": "t-contexts",
     "title": "Contexts and the fact theory",
     "rocq": "static/Contexts.v: tentry, tsplit, lenv_split, hctx, fl, sfuture",
     "tex": "\\begin{array}{l}\\htmlData{k=tj.Delta}{\\Delta : o \\mapsto (S@x)\\annot{\\annot{^{a}}},\\ i \\mapsto T} \\qquad \\htmlData{k=ctx.lsplit}{\\Delta = \\Delta_1, \\Delta_2} \\\\ \\htmlData{k=tj.Gamma}{\\Gamma = \\htmlData{k=ctx.hyps}{(C, \\bar x)^{*}}} \\qquad \\htmlData{k=ctx.slt}{\\Gamma \\vdash x \\prec y} \\\\ \\htmlData{k=tj.F}{F = (X, \\htmlData{k=ctx.fvarF}{{\\uparrow}u \\mid {\\uparrow}} \\mid \\htmlData{k=ctx.bot}{\\bot})}\\end{array}",
     "caption": "The rules read order facts only through $\\Gamma \\vdash x \\prec y$. It is the least transitive relation containing $\\prec_W$ and the facts $C[\\bar x]$ of the instances in $\\Gamma$.",
     "modes": [
      "df",
      "lf"
     ],
     "about": {
      "why": "The rules split $\\Delta$ between subterms and extend $\\Gamma$ under boxes and existentials. The block defines the two contexts and the order judgment $\\Gamma \\vdash x \\prec y$.",
      "used": [
       "t-side",
       "r-fun",
       "r-boxes",
       "r-ex"
      ]
     }
    },
    {
     "id": "t-side",
     "title": "Side conditions on points",
     "rocq": "static/Contexts.v: ub_below_s, rest_below, ub_below_u, lbx_below_h, hold_at",
     "tex": "\\begin{array}{l}\\htmlData{k=side.ub}{u \\prec F \\iff (\\forall y \\in X.\\ \\Gamma \\mathrel{\\htmlData{k=ctx.slt}{\\vdash}} u \\prec y) \\land (F = (X, {\\uparrow}v) \\Rightarrow \\Gamma \\mathrel{\\htmlData{k=ctx.slt}{\\vdash}} u \\preccurlyeq v) \\land F \\neq (X, {\\uparrow}) \\land F \\neq (X, \\bot)} \\\\ \\htmlData{k=side.top}{\\top \\prec F \\iff F = (\\varnothing, \\cdot)} \\qquad \\htmlData{k=E-Send.heads}{x \\prec T \\iff \\forall y \\in \\htmlData{k=ty.heads}{\\mathsf{ap}}(T).\\ \\Gamma \\mathrel{\\htmlData{k=ctx.slt}{\\vdash}} x \\prec y} \\qquad \\htmlData{k=side.lb}{l \\preccurlyeq \\Delta \\iff \\forall y \\in \\htmlData{k=ty.heads}{\\mathsf{ap}}(\\Delta).\\ \\Gamma \\mathrel{\\htmlData{k=ctx.slt}{\\vdash}} l \\preccurlyeq y} \\qquad \\htmlData{k=side.hold}{\\Gamma \\vdash C[\\bar x]}\\end{array}",
     "caption": "$u \\prec F$ says that $u$ lies below the points of $F$. $x \\prec T$ says that $x$ lies below the dual points of the ends in $T$. $l \\preccurlyeq \\Delta$ says that $l$ lies at or below the dual points of $\\Delta$, and $\\Gamma \\vdash C[\\bar x]$ that the facts of $C$ at $\\bar x$ are derivable.",
     "modes": [
      "df",
      "lf"
     ],
     "about": {
      "why": "These are the order checks of typing. A term never waits above a point at which its context acts later, and a thread waits only below the dual points of the values it holds.",
      "breaks": "Without them the type system is plain GV and the cycle of two threads closing two channels in opposite orders types.",
      "used": [
       "r-fun",
       "r-act",
       "r-boxes",
       "r-ex"
      ]
     }
    },
    {
     "id": "t-agecap",
     "title": "Aging",
     "modes": [
      "lf"
     ],
     "rocq": "static/Contexts.v: tage, lage, thage, types/Types.v: idle",
     "tex": "\\begin{array}{c}\\begin{array}{c}\\dfrac{\\begin{array}{c}\\htmlData{k=age.free}{\\htmlData{k=ty.tfree}{\\mathsf{tfree}}\\,T}\\end{array}}{T - c = T}\\;\\textsf{Age-Free} \\qquad \\dfrac{\\begin{array}{c}\\htmlData{k=age.credit}{c \\leq a}\\end{array}}{(S@x)\\annot{^{a}} - c = (S@x)^{a - c}}\\;\\textsf{Age-Credit} \\\\[2ex] \\dfrac{\\begin{array}{c}\\htmlData{k=age.idle}{\\htmlData{k=fu.idle}{\\mathsf{idle}}\\,S}\\end{array}}{(S@x)\\annot{^{a}} - c = (S@x)^{\\max(a - c, 0)}}\\;\\textsf{Age-Idle} \\qquad \\dfrac{\\begin{array}{c}\\htmlData{k=age.credit}{c \\leq a}\\end{array}}{(T \\mathrel{\\htmlData{k=ty.arrow}{\\multimap}} U)\\annot{^{a}} - c = (T \\mathrel{\\htmlData{k=ty.arrow}{\\multimap}} U)^{a - c}}\\;\\textsf{Age-Arr} \\\\[2ex] \\htmlData{k=age.agg}{(T_1 \\otimes T_2) - c = (T_1 - c) \\otimes (T_2 - c) \\qquad (T_1 \\oplus T_2) - c = (T_1 - c) \\oplus (T_2 - c) \\qquad (\\exists^{l}\\bar\\iota.\\,C.\\,T) - c = \\exists^{l}\\bar\\iota.\\,C.\\,(T - c)}\\end{array}\\end{array}",
     "caption": "$T - c$ lowers the credits of the ends and closures in $T$ by $c$. It requires $c \\leq a$ for ends that are not idle and for closures, and leaves $\\mathsf{tfree}$ types unchanged. A closure at credit $a$ captures its context aged by $a$, so its body sees each captured end at its own credit minus $a$.",
     "about": {
      "why": "An action of the thread postpones the ends the thread holds by one step. Aging records this on the types of held values, and capture records it for the ends a closure takes along.",
      "used": [
       "t-judgment",
       "r-fun",
       "r-data"
      ]
     }
    },
    {
     "id": "r-base",
     "title": "Unit, variables and ends",
     "modes": [
      "df",
      "lf"
     ],
     "rocq": "static/Typing.v: e_unit; static/Conservativity.v: d_unit; static/Typing.v: e_var; static/Conservativity.v: d_var; static/Typing.v: e_chan; static/Conservativity.v: d_chan",
     "tex": "\\begin{array}{c}\\dfrac{\\begin{array}{c}\\htmlData{k=ctx.empty}{\\Delta\\ \\text{unlimited}}\\end{array}}{\\Gamma ; \\Delta \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F} \\ast : \\ast\\annot{\\ \\htmlData{k=tj.eff}{!}\\ \\htmlData{k=tj.zero}{0}}}\\;\\textsf{E-Unit}\\\\[3ex]\\dfrac{\\begin{array}{c}\\htmlData{k=ctx.empty}{\\Delta\\ \\text{unlimited}}\\end{array}}{\\Gamma ; \\htmlData{k=ctx.only}{\\Delta, x : T} \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F} x : T\\annot{\\ \\htmlData{k=tj.eff}{!}\\ \\htmlData{k=tj.zero}{0}}}\\;\\textsf{E-Var}\\\\[3ex]\\dfrac{\\begin{array}{c}\\htmlData{k=ctx.empty}{\\Delta\\ \\text{unlimited}}\\end{array}}{\\Gamma ; \\htmlData{k=ctx.only}{\\Delta, o : (S@x)\\annot{\\annot{^{a}}}} \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F} o : (S@x)\\annot{\\annot{^{a}}}\\annot{\\ \\htmlData{k=tj.eff}{!}\\ \\htmlData{k=tj.zero}{0}}}\\;\\textsf{E-Chan}\\end{array}",
     "caption": "$\\ast$ uses no entry of $\\Delta$, and a variable or an end is typed by its own entry. The remaining entries must be unlimited.",
     "about": {
      "why": "Unused unlimited entries are dropped at the leaves of a derivation, so the rules need no weakening rule.",
      "used": [
       "r-data",
       "p-typing"
      ]
     }
    },
    {
     "id": "r-fun",
     "title": "Functions",
     "modes": [
      "df",
      "lf"
     ],
     "rocq": "static/Typing.v: e_abs; static/Conservativity.v: d_abs; static/Typing.v: e_app; static/Conservativity.v: d_app",
     "tex": "\\begin{array}{c}\\dfrac{\\begin{array}{c}\\htmlData{k=E-Abs.fut}{F_u = \\begin{cases} (\\varnothing, {\\uparrow}u) & u \\text{ a point} \\\\ (\\varnothing, {\\uparrow}) & u = \\cdot \\\\ (\\varnothing, \\cdot) & u = \\top \\end{cases}}\\quad \\htmlData{k=E-Abs.lb}{l \\neq \\bot \\Rightarrow l \\preccurlyeq \\Delta} \\\\ \\htmlData{k=E-Abs.body}{\\Gamma ; \\htmlData{k=E-Abs.cap}{\\Delta\\annot{ - a}}, T \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F_u} e : U\\annot{\\ \\htmlData{k=tj.eff}{!}\\ \\varepsilon}}\\end{array}}{\\Gamma ; \\Delta \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F} \\lambda e : (T \\mathrel{\\htmlData{k=ty.arrow}{\\multimap}}^{u}_{l}\\annot{[\\varepsilon]}\\, U)\\annot{\\annot{^{a}}}\\annot{\\ \\htmlData{k=tj.eff}{!}\\ \\htmlData{k=tj.zero}{0}}}\\;\\textsf{E-Abs}\\\\[3ex]\\dfrac{\\begin{array}{c}\\htmlData{k=E-App.fut1}{\\Gamma ; \\Delta_1 \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F \\htmlData{k=tj.held}{\\triangleleft} \\Delta_2} e_1 : (T \\mathrel{\\htmlData{k=ty.arrow}{\\multimap}}^{u}_{l}\\annot{[\\varepsilon]}\\, U)\\annot{\\annot{^{a}}}\\annot{\\ \\htmlData{k=tj.eff}{!}\\ \\varepsilon_1}} \\\\ \\htmlData{k=E-App.fut2}{\\Gamma ; \\Delta_2\\annot{ \\htmlData{k=age.ctx}{- \\varepsilon_1}} \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F \\htmlData{k=tj.held}{\\triangleleft} (T \\mathrel{\\htmlData{k=ty.arrow}{\\multimap}}^{u}_{l} U)\\annot{\\annot{^{a}}}} e_2 : T\\annot{\\ \\htmlData{k=tj.eff}{!}\\ \\varepsilon_2}}\\quad \\htmlData{k=E-App.ub}{u \\prec F}\\end{array}}{\\Gamma ; \\Delta_1, \\Delta_2 \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F} e_1\\,e_2 : U\\annot{\\ \\htmlData{k=tj.eff}{!}\\ \\varepsilon_1 \\htmlData{k=tj.seq}{\\cdot} \\varepsilon_2 \\htmlData{k=tj.seq}{\\cdot} \\varepsilon}}\\;\\textsf{E-App}\\end{array}",
     "caption": "E-Abs types the body under everything above the upper point $u$, under everything when there is no $u$, and under the empty future when $u = \\top$. It requires $l$ at or below the dual points of the captured entries unless $l = \\bot$. E-App holds $\\Delta_2$ while $e_1$ runs and the closure while $e_2$ runs, and the call requires $u \\prec F$. \\annp{The closure records the effect of its body. Holding it while $e_2$ runs ages it by the cost of $e_2$.}",
     "about": {
      "why": "A closure delays its body until a call. Its type records the bounds the body needs, and the call site checks them against its own future.",
      "used": [
       "r-threads",
       "v-rel",
       "th-terms"
      ]
     }
    },
    {
     "id": "r-data",
     "title": "Products, sums and let",
     "modes": [
      "df",
      "lf"
     ],
     "rocq": "static/Typing.v: e_pair; static/Conservativity.v: d_pair; static/Typing.v: e_letp, e_letu; static/Conservativity.v: d_letp, d_letu; static/Typing.v: e_inj, e_case; static/Conservativity.v: d_inj, d_case",
     "tex": "\\begin{array}{c}\\dfrac{\\begin{array}{c}\\htmlData{k=E-App.fut1}{\\Gamma ; \\Delta_1 \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F \\htmlData{k=tj.held}{\\triangleleft} \\Delta_2} e_1 : T_1\\annot{\\ \\htmlData{k=tj.eff}{!}\\ \\varepsilon_1}}\\quad \\htmlData{k=E-Pair.fut2}{\\Gamma ; \\Delta_2\\annot{ \\htmlData{k=age.ctx}{- \\varepsilon_1}} \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F \\htmlData{k=tj.held}{\\triangleleft} T_1} e_2 : T_2\\annot{\\ \\htmlData{k=tj.eff}{!}\\ \\varepsilon_2}}\\end{array}}{\\Gamma ; \\Delta_1, \\Delta_2 \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F} \\langle e_1, e_2\\rangle : \\annot{(}T_1\\annot{ \\htmlData{k=age.ctx}{- \\varepsilon_2}}\\annot{)} \\otimes T_2\\annot{\\ \\htmlData{k=tj.eff}{!}\\ \\varepsilon_1 \\htmlData{k=tj.seq}{\\cdot} \\varepsilon_2}}\\;\\textsf{E-Pair}\\\\[3ex]\\begin{array}{c}\\dfrac{\\begin{array}{c}\\htmlData{k=E-App.fut1}{\\Gamma ; \\Delta_1 \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F \\htmlData{k=tj.held}{\\triangleleft} \\Delta_2} e_1 : T_1 \\otimes T_2\\annot{\\ \\htmlData{k=tj.eff}{!}\\ \\varepsilon_1}}\\quad \\htmlData{k=tp.letp}{\\Gamma ; T_2, T_1, \\Delta_2\\annot{ \\htmlData{k=age.ctx}{- \\varepsilon_1}} \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F} e_2 : T\\annot{\\ \\htmlData{k=tj.eff}{!}\\ \\varepsilon_2}}\\end{array}}{\\Gamma ; \\Delta_1, \\Delta_2 \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F} \\htmlData{k=syn.letp}{\\mathsf{let}}\\ \\langle a, b\\rangle = e_1\\ \\htmlData{k=syn.letp}{\\mathsf{in}}\\ e_2 : T\\annot{\\ \\htmlData{k=tj.eff}{!}\\ \\varepsilon_1 \\htmlData{k=tj.seq}{\\cdot} \\varepsilon_2}}\\;\\textsf{E-LetP} \\\\[2ex] \\dfrac{\\begin{array}{c}\\htmlData{k=E-App.fut1}{\\Gamma ; \\Delta_1 \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F \\htmlData{k=tj.held}{\\triangleleft} \\Delta_2} e_1 : \\ast\\annot{\\ \\htmlData{k=tj.eff}{!}\\ \\varepsilon_1}}\\quad \\htmlData{k=tp.letu}{\\Gamma ; \\Delta_2\\annot{ \\htmlData{k=age.ctx}{- \\varepsilon_1}} \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F} e_2 : T\\annot{\\ \\htmlData{k=tj.eff}{!}\\ \\varepsilon_2}}\\end{array}}{\\Gamma ; \\Delta_1, \\Delta_2 \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F} \\htmlData{k=syn.letu}{\\mathsf{let}}\\ \\ast = e_1\\ \\htmlData{k=syn.letu}{\\mathsf{in}}\\ e_2 : T\\annot{\\ \\htmlData{k=tj.eff}{!}\\ \\varepsilon_1 \\htmlData{k=tj.seq}{\\cdot} \\varepsilon_2}}\\;\\textsf{E-LetU}\\end{array}\\\\[3ex]\\begin{array}{c}\\dfrac{\\begin{array}{c}\\Gamma ; \\Delta \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F} e : T_i\\annot{\\ \\htmlData{k=tj.eff}{!}\\ \\varepsilon}\\end{array}}{\\Gamma ; \\Delta \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F} \\htmlData{k=syn.inj}{\\mathsf{inj}_i\\,e} : T_1 \\oplus T_2\\annot{\\ \\htmlData{k=tj.eff}{!}\\ \\varepsilon}}\\;\\textsf{E-Inj} \\\\[2ex] \\dfrac{\\begin{array}{c}\\htmlData{k=E-App.fut1}{\\Gamma ; \\Delta_1 \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F \\htmlData{k=tj.held}{\\triangleleft} \\Delta_2} e : T_1 \\oplus T_2\\annot{\\ \\htmlData{k=tj.eff}{!}\\ \\varepsilon_0}}\\quad \\htmlData{k=E-Case.branches}{\\Gamma ; T_i, \\Delta_2\\annot{ \\htmlData{k=age.ctx}{- \\varepsilon_0}} \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F} e_i : T\\annot{\\ \\htmlData{k=tj.eff}{!}\\ \\varepsilon_i}}\\end{array}}{\\Gamma ; \\Delta_1, \\Delta_2 \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F} \\htmlData{k=syn.case}{\\mathsf{case}}\\ e\\,(e_1)\\,(e_2) : T\\annot{\\ \\htmlData{k=tj.eff}{!}\\ \\varepsilon_0 \\htmlData{k=tj.seq}{\\cdot} \\htmlData{k=tp.max}{\\max}(\\varepsilon_1,\\varepsilon_2)}}\\;\\textsf{E-Case}\\end{array}\\end{array}",
     "caption": "E-Pair holds the value of $e_1$ while $e_2$ runs. \\annp{The held value ages by the cost of $e_2$.} The derived $\\mathsf{let}$ is typed by E-Pair, E-LetP and E-LetU. Both branches of a case are typed under one context at one result type.",
     "about": {
      "why": "A pair is the simplest place where a thread holds a value while other code runs, and E-Pair checks the order this requires.",
      "used": [
       "r-act"
      ]
     }
    },
    {
     "id": "r-boxes",
     "title": "Boxes",
     "modes": [
      "df",
      "lf"
     ],
     "rocq": "static/Typing.v: e_box; static/Conservativity.v: d_box; static/Typing.v: e_force; static/Conservativity.v: d_force",
     "tex": "\\begin{array}{c}\\dfrac{\\begin{array}{c}\\htmlData{k=E-Box.self}{B = \\Box(\\forall \\bar\\iota\\,\\bar\\alpha.\\ C.\\ \\ast \\mathrel{\\htmlData{k=ty.arrow}{\\multimap}}^{u}\\annot{[\\varepsilon]}\\,U)}\\quad \\htmlData{k=E-Box.unl}{\\Delta\\ \\text{unlimited}}\\quad \\htmlData{k=E-Box.fresh}{\\bar\\iota\\ \\text{fresh}}\\quad \\htmlData{k=E-Box.inst}{\\forall \\bar s.\\ \\htmlData{k=tp.sinsts}{\\mathsf{sinsts}}\\,\\bar s} \\\\ \\htmlData{k=E-Box.body}{\\htmlData{k=E-Box.open}{\\Gamma, C(\\bar\\iota)} ; \\htmlData{k=E-Box.self}{\\Delta, f : B} \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{(\\varnothing,{\\uparrow}u)} e : \\htmlData{k=tp.sinst}{U[\\bar s]}\\annot{\\ \\htmlData{k=tj.eff}{!}\\ \\varepsilon}}\\end{array}}{\\Gamma ; \\Delta \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F} \\ !e : B\\annot{\\ \\htmlData{k=tj.eff}{!}\\ \\htmlData{k=tj.zero}{0}}}\\;\\textsf{E-Box}\\\\[3ex]\\dfrac{\\begin{array}{c}\\htmlData{k=E-Force.hold}{\\Gamma \\mathrel{\\htmlData{k=side.hold}{\\vdash}} C[\\bar x]}\\quad \\htmlData{k=E-Box.inst}{\\htmlData{k=tp.sinsts}{\\mathsf{sinsts}}\\,\\bar s}\\quad \\htmlData{k=E-Force.ub}{u[\\bar x] \\prec F} \\\\ \\Gamma ; \\Delta \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F} e : \\Box(\\forall\\bar\\iota\\,\\bar\\alpha.\\ C.\\ \\ast\\mathrel{\\htmlData{k=ty.arrow}{\\multimap}}^{u}\\annot{[\\varepsilon]}\\,U)\\annot{\\ \\htmlData{k=tj.eff}{!}\\ \\varepsilon_0}\\end{array}}{\\Gamma ; \\Delta \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F} \\htmlData{k=prim.force}{\\mathsf{force}}\\,e : \\htmlData{k=tp.sinst}{U[\\bar s]}\\htmlData{k=tp.pinst}{[\\bar x]}\\annot{\\ \\htmlData{k=tj.eff}{!}\\ \\varepsilon_0 \\htmlData{k=tj.seq}{\\cdot} \\varepsilon}}\\;\\textsf{E-Force}\\end{array}",
     "caption": "E-Box types the body once, with fresh point variables $\\bar\\iota$, the hypothesis $C(\\bar\\iota)$ and a fresh future variable above $u$, for each allowed session instance $\\bar s$. The context is unlimited, because a box may be copied. E-Force picks points $\\bar x$ and session types $\\bar s$, requires $C[\\bar x]$ and $u[\\bar x] \\prec F$, and gives the instantiated result type.",
     "about": {
      "why": "Boxes provide recursion and polymorphism over points and session types. Each force chooses an instance.",
      "used": [
       "v-rel",
       "g-guard"
      ]
     }
    },
    {
     "id": "r-ex",
     "title": "Existentials",
     "rocq": "static/Typing.v: e_pack, e_open; static/Conservativity.v: d_pack, d_open",
     "tex": "\\begin{array}{c}\\dfrac{\\begin{array}{c}\\htmlData{k=E-Force.hold}{\\Gamma \\mathrel{\\htmlData{k=side.hold}{\\vdash}} C[\\bar x]}\\quad \\htmlData{k=E-Pack.lb}{l \\preccurlyeq \\htmlData{k=tp.pinst}{T[\\bar x]}}\\quad \\htmlData{k=E-Pack.wf}{\\Gamma, C \\mathrel{\\htmlData{k=ctx.slt}{\\vdash}} l \\preccurlyeq T}\\quad \\Gamma ; \\Delta \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F} e : T[\\bar x]\\annot{\\ \\htmlData{k=tj.eff}{!}\\ \\varepsilon}\\end{array}}{\\Gamma ; \\Delta \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F} e : \\exists^{l}\\bar\\iota.\\,C.\\,T\\annot{\\ \\htmlData{k=tj.eff}{!}\\ \\varepsilon}}\\;\\textsf{E-Pack} \\\\[2ex] \\dfrac{\\begin{array}{c}\\htmlData{k=E-Open.entry}{\\Delta(i) = \\exists^{l}\\bar\\iota.\\,C.\\,T\\annot{,\\ \\neg\\htmlData{k=ty.unlimited}{\\mathsf{unlimited}}\\,T}}\\quad \\htmlData{k=E-Box.fresh}{\\bar\\iota\\ \\text{fresh}}\\quad \\htmlData{k=E-Open.cons}{\\mathsf{cons}\\,W\\,\\Gamma\\,m\\,C}\\quad \\htmlData{k=E-Open.body}{\\Gamma, C(\\bar\\iota) ; \\Delta[i \\mapsto T] \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F} e : U\\annot{\\ \\htmlData{k=tj.eff}{!}\\ \\varepsilon}}\\end{array}}{\\Gamma ; \\Delta \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F} e : U\\annot{\\ \\htmlData{k=tj.eff}{!}\\ \\varepsilon}}\\;\\textsf{E-Open} \\\\[2ex] \\htmlData{k=E-Open.cons}{\\mathsf{cons}\\,W\\,\\Gamma\\,m\\,C \\iff \\forall x, y \\in \\mathsf{Point}_{\\Gamma}.\\ (\\Gamma, C(\\bar\\iota) \\mathrel{\\htmlData{k=ctx.slt}{\\vdash}} x \\prec y \\Rightarrow \\Gamma \\mathrel{\\htmlData{k=ctx.slt}{\\vdash}} x \\prec y),\\ m = |\\bar\\iota|}\\end{array}",
     "caption": "E-Pack chooses witness points $\\bar x$ with $\\Gamma \\vdash C[\\bar x]$. E-Open names the witnesses by fresh point variables $\\bar\\iota$ with the hypothesis $C(\\bar\\iota)$, and asks that the hypothesis derive no new fact between points of $\\Gamma$.",
     "modes": [
      "df",
      "lf"
     ],
     "about": {
      "why": "An existential hides the points of a created channel behind the facts it states about these points. Conservativity keeps an opened binder that no value inhabits from ordering the points the code already holds.",
      "used": [
       "r-new",
       "v-rel"
      ]
     }
    },
    {
     "id": "t-consts",
     "title": "Types of constants",
     "rocq": "static/Constants.v: k_send_df, k_recv_df, k_close_df, k_select_df, k_branch_df, k_link_df, k_spawn_df, k_force_df, k_send, k_recv, k_close, k_select, k_branch, k_link, k_spawn, k_force",
     "tex": "\\begin{array}{lll}\n\\htmlData{k=prim.send}{\\mathsf{send}} & : T[x\\cdot i] \\otimes S_0@x \\mathrel{\\htmlData{k=ty.arrow}{\\multimap}}^{x} S@\\htmlData{k=pt.shift}{x^{+}} & \\htmlData{k=E-Send.unfold}{\\htmlData{k=sty.unfold}{\\mathsf{unfold}}(S_0) = {!}(\\bar\\iota.\\,T).S},\\ \\htmlData{k=ty.pscoped}{\\mathsf{pscoped}}\\,\\bar\\iota\\,T,\\ \\htmlData{k=E-Send.heads}{x \\prec T[x\\cdot i]} \\\\\n\\htmlData{k=prim.recv}{\\mathsf{recv}} & : S_0@x \\mathrel{\\htmlData{k=ty.arrow}{\\multimap}}^{x} T[x\\cdot i] \\otimes S@x^{+} & \\htmlData{k=E-Recv.unfold}{\\htmlData{k=sty.unfold}{\\mathsf{unfold}}(S_0) = {?}(\\bar\\iota.\\,T).S},\\ \\htmlData{k=ty.pscoped}{\\mathsf{pscoped}}\\,\\bar\\iota\\,T \\\\\n\\htmlData{k=prim.close}{\\mathsf{close}} & : S_0@x \\mathrel{\\htmlData{k=ty.arrow}{\\multimap}}^{x} \\ast & \\htmlData{k=E-Close.unfold}{\\htmlData{k=sty.unfold}{\\mathsf{unfold}}(S_0) = \\htmlData{k=sty.close}{\\mathsf{Close}}} \\\\\n\\htmlData{k=prim.select}{\\mathsf{select}}_i & : S_0@x \\mathrel{\\htmlData{k=ty.arrow}{\\multimap}}^{x} S_i@\\htmlData{k=pt.sel}{\\overline{x\\cdot\\kappa_i}} & \\htmlData{k=E-Select.unfold}{\\htmlData{k=sty.unfold}{\\mathsf{unfold}}(S_0) = \\oplus(S_1,S_2)} \\\\\n\\htmlData{k=prim.branch}{\\mathsf{branch}} & : S_0@x \\mathrel{\\htmlData{k=ty.arrow}{\\multimap}}^{x} S_1@\\htmlData{k=pt.bra}{x\\cdot\\kappa_1} \\oplus S_2@x\\cdot\\kappa_2 & \\htmlData{k=E-Branch.unfold}{\\htmlData{k=sty.unfold}{\\mathsf{unfold}}(S_0) = \\&(S_1,S_2)} \\\\\n\\htmlData{k=prim.link}{\\mathsf{link}} & : \\htmlData{k=E-Link.dual}{S@x \\otimes \\overline{S}@\\overline{x}} \\mathrel{\\htmlData{k=ty.arrow}{\\multimap}} \\ast & \\\\\n\\htmlData{k=prim.spawn}{\\mathsf{spawn}} & : (\\ast \\mathrel{\\htmlData{k=ty.arrow}{\\multimap}}^{u}_{l} \\ast) \\mathrel{\\htmlData{k=ty.arrow}{\\multimap}} \\ast & \\\\\n\\htmlData{k=prim.force}{\\mathsf{force}} & : \\Box(\\forall\\bar\\iota\\,\\bar\\alpha.\\ C.\\ \\ast\\mathrel{\\htmlData{k=ty.arrow}{\\multimap}}^{u} U) \\mathrel{\\htmlData{k=ty.arrow}{\\multimap}}^{u[\\bar x]} U[\\bar s][\\bar x] & \\htmlData{k=E-Force.hold}{\\Gamma \\mathrel{\\htmlData{k=side.hold}{\\vdash}} C[\\bar x]} \\\\\n\\htmlData{k=syn.new}{\\mathsf{new}} & : \\exists^{\\bot}\\bar\\iota.\\ \\htmlData{k=E-New.facts}{C}.\\ (S@\\pi \\otimes \\overline{S}@\\overline{\\pi}) & \\htmlData{k=E-New.pos}{(\\bar\\iota, \\pi) \\in \\{(\\rho, \\rho), (\\varnothing, x\\cdot\\kappa)\\}},\\ \\htmlData{k=E-New.wf}{\\pi = \\rho \\Rightarrow \\htmlData{k=w.wfnew}{\\mathsf{wf\\_new}}\\,\\rho\\,C},\\ \\htmlData{k=E-New.field}{\\pi = x\\cdot\\kappa \\Rightarrow \\Gamma \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}} C}\n\\end{array}",
     "caption": "Each constant has the type of its eta-expansion $\\lambda y.\\,k\\,y$, for each instance of its variables that meets the side conditions. An action on an end at $x$ has upper point $x$. $\\mathsf{new}$ is a term and is typed by E-New. \\annp{The types are shown without credits, tickets and cost.}",
     "modes": [
      "df",
      "lf"
     ],
     "about": {
      "why": "Constants are values and therefore need types. The upper point $x$ means that a caller may apply an action at $x$ only while its future lies above $x$.",
      "used": [
       "r-act",
       "r-threads",
       "r-boxes",
       "r-new"
      ]
     }
    },
    {
     "id": "r-act",
     "title": "Actions and link",
     "modes": [
      "df",
      "lf"
     ],
     "rocq": "static/Typing.v: e_send; static/Conservativity.v: d_send; static/Typing.v: e_recv; static/Conservativity.v: d_recv; static/Typing.v: e_close; static/Conservativity.v: d_close; static/Typing.v: e_select; static/Conservativity.v: d_select; static/Typing.v: e_branch; static/Conservativity.v: d_branch; static/Typing.v: e_link; static/Conservativity.v: d_link",
     "tex": "\\begin{array}{c}\\dfrac{\\begin{array}{c}\\htmlData{k=E-Send.unfold}{\\htmlData{k=sty.unfold}{\\mathsf{unfold}}(S_0) = {!}(\\bar\\iota.\\,T).S}\\quad \\htmlData{k=ty.pscoped}{\\mathsf{pscoped}\\,\\bar\\iota\\,T}\\quad \\htmlData{k=E-Send.heads}{x \\prec \\htmlData{k=ty.payload-at}{T[x\\cdot i]}}\\quad \\htmlData{k=side.act}{x \\prec F} \\\\ \\Gamma ; \\Delta \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F} e : T' \\otimes (S_0@x)\\annot{\\annot{^{a}}_{\\htmlData{k=ty.tickets}{m}}}\\annot{\\ \\htmlData{k=tj.eff}{!}\\ \\varepsilon}\\annraw{\\quad }\\annot{\\htmlData{k=E-Send.floor}{T' - 1 \\leq T[x\\cdot i]}}\\end{array}}{\\Gamma ; \\Delta \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F} \\htmlData{k=prim.send}{\\mathsf{send}}\\,e : (S@\\htmlData{k=pt.shift}{x^{+}})\\annot{^{\\htmlData{k=act.refill}{m}}_{m}}\\annot{\\ \\htmlData{k=tj.eff}{!}\\ \\varepsilon \\htmlData{k=tj.seq}{\\cdot} \\htmlData{k=tj.one}{1}}}\\;\\textsf{E-Send}\\\\[3ex]\\dfrac{\\begin{array}{c}\\htmlData{k=E-Recv.unfold}{\\htmlData{k=sty.unfold}{\\mathsf{unfold}}(S_0) = {?}(\\bar\\iota.\\,T).S}\\quad \\htmlData{k=ty.pscoped}{\\mathsf{pscoped}\\,\\bar\\iota\\,T}\\quad \\htmlData{k=side.act}{x \\prec F}\\quad \\Gamma ; \\Delta \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F} e : (S_0@x)\\annot{\\annot{^{a}}_{\\htmlData{k=ty.tickets}{m}}}\\annot{\\ \\htmlData{k=tj.eff}{!}\\ \\varepsilon}\\end{array}}{\\Gamma ; \\Delta \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F} \\htmlData{k=prim.recv}{\\mathsf{recv}}\\,e : T[x\\cdot i] \\otimes (S@\\htmlData{k=pt.shift}{x^{+}})\\annot{^{\\htmlData{k=act.refill}{m}}_{m}}\\annot{\\ \\htmlData{k=tj.eff}{!}\\ \\varepsilon \\htmlData{k=tj.seq}{\\cdot} \\htmlData{k=tj.one}{1}}}\\;\\textsf{E-Recv}\\\\[3ex]\\dfrac{\\begin{array}{c}\\htmlData{k=E-Close.unfold}{\\htmlData{k=sty.unfold}{\\mathsf{unfold}}(S_0) = \\htmlData{k=sty.close}{\\mathsf{Close}}}\\quad \\htmlData{k=side.act}{x \\prec F}\\quad \\Gamma ; \\Delta \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F} e : (S_0@x)\\annot{\\annot{^{a}}_{\\htmlData{k=ty.tickets}{m}}}\\annot{\\ \\htmlData{k=tj.eff}{!}\\ \\varepsilon}\\end{array}}{\\Gamma ; \\Delta \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F} \\htmlData{k=prim.close}{\\mathsf{close}}\\,e : \\ast\\annot{\\ \\htmlData{k=tj.eff}{!}\\ \\varepsilon \\htmlData{k=tj.seq}{\\cdot} \\htmlData{k=tj.one}{1}}}\\;\\textsf{E-Close}\\\\[3ex]\\dfrac{\\begin{array}{c}\\htmlData{k=E-Select.unfold}{\\htmlData{k=sty.unfold}{\\mathsf{unfold}}(S_0) = \\oplus(S_1,S_2)}\\quad \\htmlData{k=side.act}{x \\prec F}\\quad \\Gamma ; \\Delta \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F} e : (S_0@x)\\annot{\\annot{^{a}}_{\\htmlData{k=ty.tickets}{m}}}\\annot{\\ \\htmlData{k=tj.eff}{!}\\ \\varepsilon}\\end{array}}{\\Gamma ; \\Delta \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F} \\htmlData{k=prim.select}{\\mathsf{select}}_i\\,e : (S_i@\\htmlData{k=pt.sel}{\\overline{x\\cdot\\kappa_i}})\\annot{^{\\htmlData{k=act.refill}{m}}_{m}}\\annot{\\ \\htmlData{k=tj.eff}{!}\\ \\varepsilon \\htmlData{k=tj.seq}{\\cdot} \\htmlData{k=tj.one}{1}}}\\;\\textsf{E-Select}\\\\[3ex]\\dfrac{\\begin{array}{c}\\htmlData{k=E-Branch.unfold}{\\htmlData{k=sty.unfold}{\\mathsf{unfold}}(S_0) = \\&(S_1,S_2)}\\quad \\htmlData{k=side.act}{x \\prec F}\\quad \\Gamma ; \\Delta \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F} e : (S_0@x)\\annot{\\annot{^{a}}_{\\htmlData{k=ty.tickets}{m}}}\\annot{\\ \\htmlData{k=tj.eff}{!}\\ \\varepsilon}\\end{array}}{\\Gamma ; \\Delta \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F} \\htmlData{k=prim.branch}{\\mathsf{branch}}\\,e : (S_1@\\htmlData{k=pt.bra}{x\\cdot\\kappa_1})\\annot{^{\\htmlData{k=act.refill}{m}}_{m}} \\oplus (S_2@x\\cdot\\kappa_2)\\annot{^{\\htmlData{k=act.refill}{m}}_{m}}\\annot{\\ \\htmlData{k=tj.eff}{!}\\ \\varepsilon \\htmlData{k=tj.seq}{\\cdot} \\htmlData{k=tj.one}{1}}}\\;\\textsf{E-Branch}\\\\[3ex]\\dfrac{\\begin{array}{c}\\htmlData{k=E-Link.dual}{\\Gamma ; \\Delta \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F} e : (S@x)\\annot{\\annot{^{a_1}}_{m_1}} \\otimes (\\overline{S}@\\overline{x})\\annot{\\annot{^{a_2}}_{m_2}}\\annot{\\ \\htmlData{k=tj.eff}{!}\\ \\varepsilon}}\\annraw{\\quad }\\annot{\\htmlData{k=E-Link.tickets}{a_1 + m_2 > N,\\ a_2 + m_1 > N}}\\end{array}}{\\Gamma ; \\Delta \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F} \\htmlData{k=prim.link}{\\mathsf{link}}\\,e : \\ast\\annot{\\ \\htmlData{k=tj.eff}{!}\\ \\varepsilon}}\\;\\textsf{E-Link}\\end{array}",
     "caption": "An action on an end at $x$ waits at $x$ while the thread holds the rest of $\\Delta$. The rules therefore require $x$ below the future and below the dual points of the held values. Send and receive move the end to $x^{+}$ and the payload to the fields of $x$, a choice moves the end to the field of the branch, and a link requires no order fact. \\annp{An action costs one and returns the end\\annp{ with credit} $m$, its tickets. \\annp{A link asks the credit of each linked end to exceed the partner bound $N - m$ of the other.}}",
     "about": {
      "why": "A thread waits only at actions, so the order facts of the type system are required here.",
      "used": [
       "e-obl",
       "r-data",
       "syn-csub"
      ]
     }
    },
    {
     "id": "r-threads",
     "title": "Spawn",
     "modes": [
      "df",
      "lf"
     ],
     "rocq": "static/Typing.v: e_spawn; static/Conservativity.v: d_spawn",
     "tex": "\\begin{array}{c}\\dfrac{\\begin{array}{c}\\Gamma ; \\Delta \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F} e : (\\ast \\mathrel{\\htmlData{k=ty.arrow}{\\multimap}}^{u}_{l}\\annot{[c']}\\, \\ast)\\annot{\\annot{^{a}}}\\annot{\\ \\htmlData{k=tj.eff}{!}\\ \\varepsilon}\\annraw{\\quad }\\annot{\\htmlData{k=E-Spawn.credit}{a \\geq 1}}\\end{array}}{\\Gamma ; \\Delta \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F} \\htmlData{k=prim.spawn}{\\mathsf{spawn}}\\,e : \\ast\\annot{\\ \\htmlData{k=tj.eff}{!}\\ \\varepsilon}}\\;\\textsf{E-Spawn}\\end{array}",
     "caption": "E-Spawn spawns a closure value with the ends it captured. A written abstraction $\\mathsf{spawn}\\,(\\lambda e)$ types by E-Abs at upper point $\\top$ and lower point $\\bot$, so the child body runs under the empty future. \\annp{At credit $a = 1$ the transferred entries age by one.}",
     "about": {
      "why": "A spawned thread has no code after it, so the child body is typed at the empty future.",
      "used": [
       "v-rel",
       "e-obl"
      ]
     }
    },
    {
     "id": "r-new",
     "title": "Creation",
     "rocq": "static/Typing.v: e_new; static/Conservativity.v: d_new",
     "tex": "\\dfrac{\\begin{array}{c}\\htmlData{k=ctx.empty}{\\Delta\\ \\text{unlimited}}\\quad \\htmlData{k=E-New.pos}{(\\bar\\iota, \\pi) \\in \\{(\\rho, \\rho), (\\varnothing, x\\cdot\\kappa)\\}}\\quad \\htmlData{k=E-New.wf}{\\pi = \\rho \\Rightarrow \\htmlData{k=w.wfnew}{\\mathsf{wf\\_new}}\\,\\rho\\,C}\\quad \\htmlData{k=E-New.field}{\\pi = x\\cdot\\kappa \\Rightarrow \\Gamma \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}} C}\\annraw{\\quad }\\annot{\\htmlData{k=E-New.tickets}{m_1 + m_2 \\leq N}}\\end{array}}{\\Gamma ; \\Delta \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F} \\htmlData{k=syn.new}{\\mathsf{new}} : \\exists^{\\htmlData{k=E-New.bot}{\\bot}}\\bar\\iota.\\ \\htmlData{k=E-New.facts}{C}.\\ \\htmlData{k=E-New.dual}{(S@\\pi)\\annot{^{m_1}_{m_1}} \\otimes (\\htmlData{k=sty.dual}{\\overline{S}}@\\overline{\\pi})\\annot{^{m_2}_{m_2}}}\\annot{\\ \\htmlData{k=tj.eff}{!}\\ \\htmlData{k=tj.zero}{0}}}\\;\\textsf{E-New}",
     "caption": "The two ends of a new channel are at a fresh root $\\rho$ and its dual, or at a field $x\\cdot\\kappa$ and its dual. At a fresh root each fact of $C$ ends in the tree of $\\rho$, and $C$ with program order is well-founded on that tree. At a field $\\Gamma$ entails $C$. The lower bound is $\\bot$. \\annp{The creation picks tickets $m_1$ and $m_2$ with $m_1 + m_2 \\leq N$, and each end starts at credit equal to its tickets.}",
     "modes": [
      "df",
      "lf"
     ],
     "about": {
      "why": "Creation places a new channel in the order. Later rules may use the facts $C$ about the new points.",
      "used": [
       "e-obl",
       "w-ext"
      ]
     }
    },
    {
     "id": "t-subs",
     "title": "Subtyping and structural rules",
     "modes": [
      "df",
      "lf"
     ],
     "rocq": "static/Contexts.v: tsub, static/Typing.v: e_sub; static/Conservativity.v: d_conv; static/Typing.v: e_sub; static/Conservativity.v: d_conv; static/Weakening.v: e_weak, e_contract, d_weak, d_contract, typed_rename",
     "tex": "\\begin{array}{c}\\begin{array}{c}\\dfrac{\\begin{array}{c}\\htmlData{k=tp.sub-sess}{S \\htmlData{k=sty.sequiv}{\\simeq} S'}\\quad \\annot{\\htmlData{k=tp.sub-credit}{a' \\leq a}}\\end{array}}{\\htmlData{k=sub.tsub}{(S@x)\\annot{^{a}} \\leq (S'@x)\\annot{^{a'}}}}\\;\\textsf{Sub-Sess} \\\\[2ex] \\dfrac{\\begin{array}{c}\\htmlData{k=E-Sub.cost}{\\varepsilon \\leq \\varepsilon'}\\quad \\annot{\\htmlData{k=tp.sub-credit}{a' \\leq a}} \\\\ \\htmlData{k=tp.sub-var}{\\htmlData{k=sub.tsub}{T_1' \\leq T_1} \\quad \\htmlData{k=sub.tsub}{U \\leq U'}}\\end{array}}{(T_1 \\mathrel{\\htmlData{k=ty.arrow}{\\multimap}}^{u}_{l}[\\varepsilon]\\,U)\\annot{^{a}} \\leq (T_1' \\mathrel{\\htmlData{k=ty.arrow}{\\multimap}}^{u}_{l}[\\varepsilon']\\,U')\\annot{^{a'}}}\\;\\textsf{Sub-Arr} \\\\[2ex] \\dfrac{\\begin{array}{c}\\htmlData{k=E-Sub.cost}{\\varepsilon \\leq \\varepsilon'}\\quad \\htmlData{k=tp.sub-teq}{U \\equiv U'}\\end{array}}{\\Box(\\forall \\bar\\iota\\,\\bar\\alpha.\\ C.\\ \\ast \\mathrel{\\htmlData{k=ty.arrow}{\\multimap}}^{u}[\\varepsilon]\\,U) \\leq \\Box(\\ldots[\\varepsilon']\\,U')}\\;\\textsf{Sub-Box} \\qquad \\dfrac{\\begin{array}{c}\\htmlData{k=tp.sub-ex}{\\mathsf{facts}\\,C' \\subseteq \\mathsf{facts}\\,C}\\quad \\htmlData{k=tp.sub-teq}{T \\equiv T'}\\end{array}}{\\htmlData{k=sub.tsub}{\\exists^{l}\\bar\\iota.\\,C.\\,T \\leq \\exists^{l}\\bar\\iota.\\,C'.\\,T'}}\\;\\textsf{Sub-Ex} \\\\[2ex] \\dfrac{\\begin{array}{c}\\htmlData{k=tp.sub-agg}{\\htmlData{k=sub.tsub}{T_1 \\leq T_1'} \\quad \\htmlData{k=sub.tsub}{T_2 \\leq T_2'}}\\end{array}}{T_1 \\otimes T_2 \\leq T_1' \\otimes T_2' \\qquad T_1 \\oplus T_2 \\leq T_1' \\oplus T_2'}\\;\\textsf{Sub-Prod, Sub-Sum}\\end{array}\\\\[3ex]\\dfrac{\\begin{array}{c}\\Gamma ; \\Delta \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F} e : T\\annot{\\ \\htmlData{k=tj.eff}{!}\\ \\varepsilon}\\quad \\htmlData{k=sub.tsub}{T \\leq T'}\\annraw{\\quad }\\annot{\\htmlData{k=E-Sub.cost}{\\varepsilon \\leq \\varepsilon'}}\\end{array}}{\\Gamma ; \\Delta \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F} e : T'\\annot{\\ \\htmlData{k=tj.eff}{!}\\ \\varepsilon'}}\\;\\textsf{E-Sub}\\\\[3ex]\\begin{array}{c}\\dfrac{\\begin{array}{c}\\htmlData{k=E-Weak.drop}{\\Delta' \\preceq_{\\mathsf{wk}} \\Delta}\\quad \\Gamma ; \\Delta' \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F} e : T\\annot{\\ \\htmlData{k=tj.eff}{!}\\ \\varepsilon}\\end{array}}{\\Gamma ; \\Delta \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F} e : T\\annot{\\ \\htmlData{k=tj.eff}{!}\\ \\varepsilon}}\\;\\textsf{E-Weak} \\\\[2ex] \\dfrac{\\begin{array}{c}\\htmlData{k=ty.unlimited}{\\mathsf{unlimited}\\,U}\\quad \\Gamma ; \\Delta, U, U \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F} e : T\\annot{\\ \\htmlData{k=tj.eff}{!}\\ \\varepsilon}\\end{array}}{\\Gamma ; \\Delta, U \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F} e[1 \\mapsto 0] : T\\annot{\\ \\htmlData{k=tj.eff}{!}\\ \\varepsilon}}\\;\\textsf{E-Contract}\\end{array}\\end{array}",
     "caption": "Subtyping is $\\approx$ on session types, and an existential may drop facts. \\annp{Credits may decrease, and costs may increase.} Weakening and contraction are admissible, because they are renamings of variables.",
     "variants": {
      "df": "\\begin{array}{c}\\begin{array}{c}\\dfrac{\\begin{array}{c}\\htmlData{k=tp.sub-sess}{S \\htmlData{k=sty.seqv}{\\approx} S'}\\end{array}}{\\htmlData{k=sub.tsub}{S@x \\leq S'@x}}\\;\\textsf{Sub-Sess} \\qquad \\dfrac{\\begin{array}{c}\\htmlData{k=tp.sub-ex}{\\mathsf{facts}\\,C' \\subseteq \\mathsf{facts}\\,C}\\quad \\htmlData{k=tp.sub-teq}{T \\equiv T'}\\end{array}}{\\htmlData{k=sub.tsub}{\\exists^{l}\\bar\\iota.\\,C.\\,T \\leq \\exists^{l}\\bar\\iota.\\,C'.\\,T'}}\\;\\textsf{Sub-Ex} \\\\[2ex] \\dfrac{\\begin{array}{c}\\htmlData{k=tp.sub-agg}{\\htmlData{k=sub.tsub}{T_1 \\leq T_1'} \\quad \\htmlData{k=sub.tsub}{T_2 \\leq T_2'}}\\end{array}}{T_1 \\otimes T_2 \\leq T_1' \\otimes T_2' \\qquad T_1 \\oplus T_2 \\leq T_1' \\oplus T_2'}\\;\\textsf{Sub-Prod, Sub-Sum} \\qquad \\dfrac{\\begin{array}{c}\\htmlData{k=tp.sub-var}{\\htmlData{k=sub.tsub}{T_1' \\leq T_1} \\quad \\htmlData{k=sub.tsub}{U \\leq U'}}\\end{array}}{T_1 \\mathrel{\\htmlData{k=ty.arrow}{\\multimap}}^{u}_{l} U \\leq T_1' \\mathrel{\\htmlData{k=ty.arrow}{\\multimap}}^{u}_{l} U'}\\;\\textsf{Sub-Arr} \\\\[2ex] \\dfrac{\\begin{array}{c}\\htmlData{k=tp.sub-teq}{U \\equiv U'}\\end{array}}{\\Box(\\forall \\bar\\iota\\,\\bar\\alpha.\\ C.\\ \\ast \\mathrel{\\htmlData{k=ty.arrow}{\\multimap}}^{u} U) \\leq \\Box(\\forall \\bar\\iota\\,\\bar\\alpha.\\ C.\\ \\ast \\mathrel{\\htmlData{k=ty.arrow}{\\multimap}}^{u} U')}\\;\\textsf{Sub-Box}\\end{array}\\\\[3ex]\\dfrac{\\begin{array}{c}\\Gamma ; \\Delta \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F} e : T\\annot{\\ \\htmlData{k=tj.eff}{!}\\ \\varepsilon}\\quad \\htmlData{k=sub.tsub}{T \\leq T'}\\annraw{\\quad }\\annot{\\htmlData{k=E-Sub.cost}{\\varepsilon \\leq \\varepsilon'}}\\end{array}}{\\Gamma ; \\Delta \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F} e : T'\\annot{\\ \\htmlData{k=tj.eff}{!}\\ \\varepsilon'}}\\;\\textsf{E-Sub}\\\\[3ex]\\begin{array}{c}\\dfrac{\\begin{array}{c}\\htmlData{k=E-Weak.drop}{\\Delta' \\preceq_{\\mathsf{wk}} \\Delta}\\quad \\Gamma ; \\Delta' \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F} e : T\\annot{\\ \\htmlData{k=tj.eff}{!}\\ \\varepsilon}\\end{array}}{\\Gamma ; \\Delta \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F} e : T\\annot{\\ \\htmlData{k=tj.eff}{!}\\ \\varepsilon}}\\;\\textsf{E-Weak} \\\\[2ex] \\dfrac{\\begin{array}{c}\\htmlData{k=ty.unlimited}{\\mathsf{unlimited}\\,U}\\quad \\Gamma ; \\Delta, U, U \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F} e : T\\annot{\\ \\htmlData{k=tj.eff}{!}\\ \\varepsilon}\\end{array}}{\\Gamma ; \\Delta, U \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F} e[1 \\mapsto 0] : T\\annot{\\ \\htmlData{k=tj.eff}{!}\\ \\varepsilon}}\\;\\textsf{E-Contract}\\end{array}\\end{array}"
     },
     "about": {
      "why": "A value may forget facts it does not need. Admissible weakening and contraction keep the rule set free of structural rules.",
      "used": []
     }
    },
    {
     "id": "p-typing",
     "title": "Process typing",
     "modes": [
      "df",
      "lf"
     ],
     "rocq": "static/Typing.v: p_term; static/Typing.v: p_connect; static/Typing.v: ptyped, static/FundamentalProc.v: pguard",
     "tex": "\\begin{array}{c}\\dfrac{\\begin{array}{c}\\htmlData{k=ty.tfree}{\\mathsf{tfree}\\,T}\\quad \\htmlData{k=pfree}{\\mathsf{pfree}\\,\\Sigma}\\quad \\htmlData{k=P-Term.wf}{\\htmlData{k=w.lfworld}{\\mathsf{wf}}\\,W}\\\\ \\htmlData{k=P-Term.C0}{\\mathrm{dom}\\,\\Theta_B = \\htmlData{k=tp.ends}{\\mathsf{ends}}(C_0)}\\quad \\htmlData{k=P-Term.disj}{\\htmlData{k=tp.chans}{\\mathsf{chans}}\\,\\htmlData{k=tp.Sigma}{\\Sigma} \\cap C_0 = \\varnothing} \\\\ \\htmlData{k=P-Term.pairs}{\\forall c \\in C_0.\\ \\Theta_B(c^{+}) = (S@x)\\annot{^{m}_{m}},\\ \\Theta_B(c^{-}) = (\\overline{S}@\\overline{x})\\annot{^{m'}_{m'}}\\annot{,\\ m + m' \\leq N}} \\\\ \\htmlData{k=P-Term.typed}{\\varnothing ; \\htmlData{k=tp.lift}{\\Sigma\\annot{^{N/2}_{N/2}}}, \\Theta_B \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{\\htmlData{k=P-Term.future}{(\\varnothing,\\cdot)}} t : T\\annot{\\ !\\ c}}\\end{array}}{\\Sigma \\htmlData{k=tp.pjudg}{\\vdash\\annot{\\annot{^{N}}}_W} (C_0, \\{t\\}) : T}\\;\\textsf{P-Term}\\\\[3ex]\\dfrac{\\begin{array}{c}\\htmlData{k=P-Connect.left}{\\Sigma_1 \\cup \\Sigma_C \\mathrel{\\htmlData{k=tp.pjudg}{\\vdash}}\\annot{\\annot{^{N}}}_{W_1} (C_1, E_1) : T} \\\\ \\htmlData{k=P-Connect.right}{\\Sigma_2 \\cup \\htmlData{k=P-Connect.cut}{\\overline{\\Sigma_C}} \\mathrel{\\htmlData{k=tp.pjudg}{\\vdash}}\\annot{\\annot{^{N}}}_{W_2} (C_2, E_2) : \\ast} \\\\ \\htmlData{k=P-Connect.disj}{\\mathsf{disjoint}(\\htmlData{k=tp.chans}{\\mathsf{chans}}\\,\\Sigma_1, \\htmlData{k=tp.chans}{\\mathsf{chans}}\\,\\Sigma_2, \\htmlData{k=tp.chans}{\\mathsf{chans}}\\,\\Sigma_C, C_1, C_2)}\\quad \\htmlData{k=P-Connect.cutfree}{\\htmlData{k=pfree}{\\mathsf{pfree}}\\,\\Sigma_C} \\\\ \\htmlData{k=P-Connect.wf}{\\htmlData{k=w.lfworld}{\\mathsf{wf}}(\\htmlData{k=w.restrict}{W_1|_S} \\mathbin{\\htmlData{k=w.join}{\\sqcup}} W_2|_S),\\ S = \\htmlData{k=w.consts}{A_{W_1}} \\cap A_{W_2}}\\end{array}}{\\begin{array}{c}\\Sigma_1 \\cup \\Sigma_2 \\mathrel{\\htmlData{k=tp.pjudg}{\\vdash}}\\annot{\\annot{^{N}}}_{\\htmlData{k=P-Connect.join}{W_1 \\htmlData{k=w.join}{\\sqcup} W_2}} \\\\ (C_1 \\cup C_2 \\cup \\htmlData{k=tp.chans}{\\mathsf{chans}}\\,\\Sigma_C, E_1 \\mathbin{\\htmlData{k=tp.msunion}{\\uplus}} E_2) : T\\end{array}}\\;\\textsf{P-Connect}\\annraw{\\\\[3ex]}\\annot{\\htmlData{k=tp.lfjudg}{\\Sigma \\Vdash^{N}_W p : T \\iff \\htmlData{k=lf.N}{N \\in \\mathbb{N}} \\land \\Sigma \\mathrel{\\htmlData{k=tp.pjudg}{\\vdash}}\\annot{\\annot{^{N}}}_W p : T \\land \\htmlData{k=guard.proc}{\\vdash\\!\\triangleright p}}}\\end{array}",
     "caption": "P-Term types one thread $t$ that holds both ends of each channel in $C_0$, at dual types and points, over an interface $\\Sigma$ without partner pairs. P-Connect cuts two components at $\\Sigma_C$ against $\\overline{\\Sigma_C}$ and compares only the shared roots of the two worlds. \\annp{Lock-free process typing is process typing at a finite bound $N$ with each thread guarded. \\annp{The ends of a restricted channel have tickets of sum at most $N$, and each interface end has $N/2$.}}",
     "about": {
      "why": "Processes are built from single threads by P-Term and composed by P-Connect.",
      "used": [
       "g-guard"
      ]
     }
    },
    {
     "id": "g-guard",
     "title": "The guard",
     "modes": [
      "lf"
     ],
     "rocq": "static/Guard.v: sprim, acts; static/Guard.v: lguard; static/FundamentalProc.v: pguard",
     "tex": "\\begin{array}{c}\\htmlData{k=guard.acts}{\\begin{array}{l}\\mathsf{acts}\\,(k\\,e) \\iff k \\in K_{\\mathrm{act}} \\lor \\mathsf{acts}\\,e \\\\ K_{\\mathrm{act}} = \\{\\htmlData{k=prim.send}{\\mathsf{send}}, \\htmlData{k=prim.recv}{\\mathsf{recv}}, \\htmlData{k=prim.close}{\\mathsf{close}}, \\htmlData{k=prim.select}{\\mathsf{select}}_i, \\htmlData{k=prim.branch}{\\mathsf{branch}}\\} \\\\ \\mathsf{acts}\\,(e_1\\,e_2),\\ \\mathsf{acts}\\,\\langle e_1, e_2\\rangle \\iff \\mathsf{acts}\\,e_1 \\lor \\mathsf{acts}\\,e_2 \\\\ \\mathsf{acts}\\,(\\htmlData{k=syn.letp}{\\mathsf{let}}\\ p = e_1\\ \\htmlData{k=syn.letp}{\\mathsf{in}}\\ e_2) \\iff \\mathsf{acts}\\,e_1 \\lor \\mathsf{acts}\\,e_2 \\\\ \\mathsf{acts}\\,(\\htmlData{k=syn.case}{\\mathsf{case}}\\ e\\,(e_1)\\,(e_2)) \\iff \\mathsf{acts}\\,e \\lor (\\mathsf{acts}\\,e_1 \\land \\mathsf{acts}\\,e_2) \\\\ \\mathsf{acts}\\,(\\mathsf{inj}_i\\,e) \\iff \\mathsf{acts}\\,e \\qquad \\neg\\mathsf{acts}\\,v \\qquad \\neg\\mathsf{acts}\\,\\htmlData{k=syn.new}{\\mathsf{new}}\\end{array}}\\\\[3ex]\\begin{array}{c}\n\\dfrac{\\begin{array}{c}\\htmlData{k=guard.var}{\\Lambda(y) = \\htmlData{k=guard.marks}{\\mathsf{false}}}\\end{array}}{\\htmlData{k=guard.marks}{\\Lambda} \\mathrel{\\htmlData{k=guard.judg}{\\vdash\\!\\triangleright}} y}\\;\\textsf{gl\\_var} \\quad \\dfrac{\\begin{array}{c}\\htmlData{k=guard.lam}{\\htmlData{k=guard.marks}{\\mathsf{false}}.\\Lambda \\mathrel{\\htmlData{k=guard.judg}{\\vdash\\!\\triangleright}} b}\\end{array}}{\\Lambda \\mathrel{\\htmlData{k=guard.judg}{\\vdash\\!\\triangleright}} \\lambda b}\\;\\textsf{gl\\_lam} \\quad \\dfrac{\\begin{array}{c}\\htmlData{k=guard.box}{\\htmlData{k=guard.marks}{\\mathsf{true}}.\\Lambda \\mathrel{\\htmlData{k=guard.judg}{\\vdash\\!\\triangleright}} b}\\end{array}}{\\Lambda \\mathrel{\\htmlData{k=guard.judg}{\\vdash\\!\\triangleright}}\\ !b}\\;\\textsf{gl\\_box} \\\\[2ex]\n\\dfrac{\\begin{array}{c}\\htmlData{k=guard.cong}{\\Lambda \\mathrel{\\htmlData{k=guard.judg}{\\vdash\\!\\triangleright}} e_1}\\quad \\htmlData{k=guard.tick}{\\mathsf{kmarks}\\,\\Lambda\\,\\Lambda'\\,e_1}\\quad \\Lambda' \\mathrel{\\htmlData{k=guard.judg}{\\vdash\\!\\triangleright}} e_2\\end{array}}{\\Lambda \\mathrel{\\htmlData{k=guard.judg}{\\vdash\\!\\triangleright}} e_1\\,e_2}\\;\\textsf{gl\\_app} \\\\[2ex]\n\\dfrac{\\begin{array}{c}\\Lambda \\mathrel{\\htmlData{k=guard.judg}{\\vdash\\!\\triangleright}} e_1\\quad \\htmlData{k=guard.tick}{\\mathsf{kmarks}\\,\\Lambda\\,\\Lambda'\\,e_1}\\quad \\htmlData{k=guard.bind}{\\htmlData{k=guard.marks}{\\mathsf{false}}.\\htmlData{k=guard.marks}{\\mathsf{false}}.\\Lambda' \\mathrel{\\htmlData{k=guard.judg}{\\vdash\\!\\triangleright}} e_2}\\end{array}}{\\Lambda \\mathrel{\\htmlData{k=guard.judg}{\\vdash\\!\\triangleright}} \\htmlData{k=syn.letp}{\\mathsf{let}}\\ \\langle a, b\\rangle = e_1\\ \\htmlData{k=syn.letp}{\\mathsf{in}}\\ e_2}\\;\\textsf{gl\\_letp}\n\\end{array}\\\\[3ex]\\htmlData{k=guard.proc}{\\vdash\\!\\triangleright p \\iff \\forall t \\in p.\\ \\varnothing \\vdash\\!\\triangleright t}\\end{array}",
     "caption": "$\\mathsf{acts}\\,e$ holds when each evaluation of $e$ to a value performs a session action. The guard marks the variable of a box as unusable until the body has acted. A process is guarded when each of its threads is.",
     "about": {
      "why": "A thread that recurses without a session action makes internal steps forever. The guard rejects such recursion.",
      "used": [
       "p-typing"
      ]
     }
    }
   ]
  },
  {
   "id": "semantic",
   "title": "Semantic typing",
   "intro": "The logical relation defines when a value, a term and a process are safe, by induction on a step index. Typed programs are safe by the fundamental theorems, and safe closed processes are deadlock free by adequacy. \\annp{For lock freedom we read the same relation with other step costs, add fuel to each thread, and combine the two in the lock-free process relation.}",
   "blocks": [
    {
     "id": "sr-reading",
     "title": "Reading the relations",
     "rocq": "relation/Relation.v: Vrel, Erel, Prel, at_cost_E",
     "tex": "\\begin{array}{ll}\n\\htmlData{k=th.Vrel}{v \\in V^{W}_{\\alpha}\\llbracket \\Theta \\vdash T \\rrbracket} & \\text{the value } v \\text{ owns exactly the ends } \\Theta \\text{ and is safe at } T \\\\\n\\htmlData{k=th.Erel}{e \\in E^{W}_{\\alpha}\\llbracket \\Theta \\vdash T \\rrbracket^{F}} & \\text{the term } e \\text{, holding } \\Theta \\text{, is safe until it returns a value of } T \\text{, its context acting at } F \\text{ afterwards} \\\\\n\\htmlData{k=th.Prel}{p \\in P^{W}_{\\alpha}\\llbracket \\Sigma \\vdash T \\rrbracket} & \\text{the process } p \\text{ is safe with interface } \\Sigma \\\\\n\\htmlData{k=sr.obl}{\\mathsf{Obl}_\\ell(e')} & \\text{what a step } e \\xrightarrow{\\ell} e' \\text{ must preserve} \\\\\n\\htmlData{k=rel.atcost}{e'\\ \\mathsf{at}\\ \\Theta'} & e' \\text{ is safe holding } \\Theta' \\text{, at the same index after a free step and at every } \\beta \\text{ with } \\beta + c \\leq \\alpha \\text{ after a step of cost } c\n\\annraw{\\\\}\\annot{\\htmlData{k=sr.FE}{e \\in F^{N}_{\\alpha}\\llbracket \\Phi \\vdash \\sigma\\ !\\ d \\rrbracket}}\\annraw{&}\\annot{\\text{the thread } e \\text{, holding } \\Phi \\text{ with counters and tickets, has fuel at index } \\alpha}\n\\annraw{\\\\}\\annot{\\htmlData{k=th.soup}{a \\in S^{N,W}_{\\alpha}\\llbracket \\Sigma \\vdash T \\rrbracket}}\\annraw{&}\\annot{\\text{every thread of } a \\text{ is in } E[\\kappa_L] \\text{ and has fuel, under one ownership map}}\n\\end{array}",
     "caption": "The relations are indexed by a world $W$, whose order they read, and an ordinal index $\\alpha$. A term is safe when it is a safe value, or when it is ready and each of its steps leads to a safe term at every lower index the cost of the step allows. Readiness says that a stuck term waits below the dual points of the ends it holds. Processes are safe in the same way and remain safe when their ends are fused, so composing two safe processes needs no further proof. \\annp{Fuel is a second predicate on each thread, and the lock-free process relation requires both of every thread.}",
     "modes": [
      "df",
      "lf"
     ],
     "about": {
      "why": "Each row says in words what one judgment of this section means.",
      "used": [
       "v-rel",
       "e-rel",
       "p-rel"
      ]
     }
    },
    {
     "id": "ct-costs",
     "title": "Step costs",
     "modes": [
      "df",
      "lf"
     ],
     "rocq": "relation/CostTable.v: κ_DF, κ_L, ev_cost; relation/CostTable.v: ctable",
     "tex": "\\begin{array}{c}\\begin{array}{lcc}\n & \\htmlData{k=ct.DF}{\\kappa_{DF}} & \\annot{\\htmlData{k=ct.L}{\\kappa_L}} \\\\ \\hline\n\\htmlData{k=ct.beta}{\\beta} & 1 & 0 \\\\\n\\htmlData{k=ct.new}{\\mathsf{new}} & 1 & 0 \\\\\n\\htmlData{k=ct.spawn}{\\mathsf{spawn}} & 1 & 0 \\\\\n\\htmlData{k=ct.link}{\\mathsf{link}} & 0 & 0 \\\\\n\\htmlData{k=ct.give}{\\mathsf{send},\\ \\mathsf{select},\\ \\mathsf{close}} & 0 & 1 \\\\\n\\htmlData{k=ct.takek}{\\mathsf{recv},\\ \\mathsf{branch}} & 1 & 1 \\\\\n\\htmlData{k=ct.sync}{\\kappa_{give} + \\kappa_{take}} & 1 & 2\n\\end{array}\\annraw{\\\\[3ex]}\\annot{\\begin{array}{l}\n\\htmlData{k=ct.table}{\\kappa = (\\kappa_\\beta, \\kappa_{new}, \\kappa_{spawn}, \\kappa_{link}, \\kappa_{give}, \\kappa_{take}) \\in \\mathbb{N}^{6}} \\\\\n\\htmlData{k=ct.take-pos}{1 \\leq \\kappa_{take}} \\qquad \\htmlData{k=ct.give-pos}{\\kappa_\\beta = 0 \\Rightarrow 1 \\leq \\kappa_{give}} \\qquad \\htmlData{k=ct.give-take}{\\kappa_{give} \\leq \\kappa_{take}}\n\\end{array}}\\end{array}",
     "caption": "The number of levels each kind of step consumes in the deadlock-free relation. \\annp{A cost table $\\kappa$ assigns these numbers subject to three conditions. The lock-free relation uses $\\kappa_L$, in which internal steps are free.}",
     "variants": {
      "df": "\\begin{array}{c}\\begin{array}{lc}\n & \\htmlData{k=ct.DF}{\\kappa_{DF}} \\\\ \\hline\n\\htmlData{k=ct.beta}{\\beta} & 1 \\\\\n\\htmlData{k=ct.new}{\\mathsf{new}} & 1 \\\\\n\\htmlData{k=ct.spawn}{\\mathsf{spawn}} & 1 \\\\\n\\htmlData{k=ct.link}{\\mathsf{link}} & 0 \\\\\n\\htmlData{k=ct.give}{\\mathsf{send},\\ \\mathsf{select},\\ \\mathsf{close}} & 0 \\\\\n\\htmlData{k=ct.takek}{\\mathsf{recv},\\ \\mathsf{branch}} & 1 \\\\\n\\htmlData{k=ct.sync}{\\kappa_{give} + \\kappa_{take}} & 1\n\\end{array}\\end{array}"
     },
     "about": {
      "why": "The costs fix how far the level drops at a step. \\annp{A step of cost $0$ is read at the same level, so a thread cannot take infinitely many of them.}",
      "used": [
       "e-rel",
       "e-obl",
       "p-obls"
      ]
     }
    },
    {
     "id": "v-rel",
     "title": "The value relation",
     "modes": [
      "df",
      "lf"
     ],
     "rocq": "relation/Relation.v: Vbody; relation/Relation.v: Varr; relation/Relation.v: Vbody (TBox), Vrel_box_iff; relation/Relation.v: Vbody (TEx), Vrel_ex_iff; relation/Relation.v: tsize, Vtop, RelA; relation/Ord.v: osfix",
     "tex": "\\begin{array}{c}\\begin{array}{c}\n\\dfrac{\\begin{array}{c}\\phantom{x}\\end{array}}{\\htmlData{k=V-Unit}{\\ast \\in \\htmlData{k=th.Vrel}{V^{W}_{\\alpha}\\llbracket \\varnothing \\vdash \\ast \\rrbracket}}}\\;\\textsf{V-Unit} \\qquad \\dfrac{\\begin{array}{c}S' \\mathrel{\\htmlData{k=sty.seqv}{\\approx}} S\\end{array}}{\\htmlData{k=V-Sess}{o \\in \\htmlData{k=th.Vrel}{V^{W}_{\\alpha}\\llbracket \\htmlData{k=V-Sess.exact}{\\{o \\mapsto S'@x\\}} \\vdash S@x \\rrbracket}}}\\;\\textsf{V-Sess} \\\\[2ex]\n\\dfrac{\\begin{array}{c}v_1 \\in \\htmlData{k=th.Vrel}{V^{W}_{\\alpha}\\llbracket \\Theta_1 \\vdash T_1 \\rrbracket}\\quad v_2 \\in \\htmlData{k=th.Vrel}{V^{W}_{\\alpha}\\llbracket \\Theta_2 \\vdash T_2 \\rrbracket}\\end{array}}{\\htmlData{k=V-Prod}{\\langle v_1, v_2\\rangle \\in \\htmlData{k=th.Vrel}{V^{W}_{\\alpha}\\llbracket \\htmlData{k=V-Prod.split}{\\Theta_1 \\mathbin{\\htmlData{k=ctx.tsplit}{\\uplus}} \\Theta_2} \\vdash T_1 \\otimes T_2 \\rrbracket}}}\\;\\textsf{V-Prod} \\qquad \\dfrac{\\begin{array}{c}v \\in \\htmlData{k=th.Vrel}{V^{W}_{\\alpha}\\llbracket \\Theta \\vdash T_i \\rrbracket}\\end{array}}{\\htmlData{k=V-Sum}{\\htmlData{k=syn.inj}{\\mathsf{inj}_i}\\,v \\in \\htmlData{k=th.Vrel}{V^{W}_{\\alpha}\\llbracket \\Theta \\vdash T_1 \\oplus T_2 \\rrbracket}}}\\;\\textsf{V-Sum}\n\\end{array}\\\\[3ex]\\dfrac{\\begin{array}{c}\\htmlData{k=V-Arrow.exact}{\\mathrm{dom}\\,\\Theta = \\htmlData{k=syn.fends}{\\mathsf{fends}}(e)}\\quad \\htmlData{k=V-Arrow.lb}{l \\neq \\bot \\Rightarrow l \\mathrel{\\htmlData{k=ty2.le}{\\preccurlyeq}} \\htmlData{k=ty.heads}{\\mathsf{ap}}\\,\\Theta} \\\\ \\htmlData{k=V-Arrow.kripke}{\\forall W' \\mathrel{\\htmlData{k=w.ext}{\\sqsupseteq}} W},\\ \\htmlData{k=V-Arrow.level}{\\dfo{j < \\alpha}\\annot{j + \\kappa_{\\beta} \\leq \\alpha}},\\ \\Theta' \\mathbin{\\#} \\Theta,\\ \\htmlData{k=V-Arrow.ub}{F,\\ \\htmlData{k=w.lt}{W' \\vdash u \\prec F}}. \\\\ w \\in \\htmlData{k=th.Vrel}{V^{W'}_{j}\\llbracket \\Theta' \\vdash T \\rrbracket} \\ \\Longrightarrow\\ \\htmlData{k=V-Arrow.body}{e[w] \\in \\htmlData{k=th.Erel}{E^{W'}_{j}\\llbracket \\Theta \\cup \\Theta' \\vdash U \\rrbracket^{F}}}\\end{array}}{\\lambda e \\in \\htmlData{k=th.Vrel}{V^{W}_{\\alpha}\\llbracket \\Theta \\vdash T \\mathrel{\\htmlData{k=ty.arrow}{\\multimap}}^{u}_{l} U \\rrbracket}}\\;\\textsf{V-Arrow}\\\\[3ex]\\dfrac{\\begin{array}{c}\\htmlData{k=V-Box.empty}{\\Theta = \\varnothing}\\quad \\htmlData{k=V-Box.noends}{\\htmlData{k=syn.fends}{\\mathsf{fends}}(e) = \\varnothing} \\\\ \\htmlData{k=V-Box.kripke}{\\forall W' \\mathrel{\\htmlData{k=w.ext}{\\sqsupseteq}} W},\\ \\htmlData{k=V-Box.inst}{\\bar x,\\ W' \\vdash C[\\bar x]},\\ \\htmlData{k=V-Box.hc}{\\bar s,\\ \\mathsf{contractive}\\,\\bar s,\\ \\mathsf{scoped}\\,\\bar s}.\\quad \\htmlData{k=V-Box.thunk}{\\htmlData{k=sr.thunk}{\\mathsf{thunk}(e)} \\in \\htmlData{k=th.Vrel}{V^{W'}_{\\alpha}\\llbracket \\varnothing \\vdash \\ast \\mathrel{\\htmlData{k=ty.arrow}{\\multimap}}^{u[\\bar x]} U[\\bar s][\\bar x] \\rrbracket}}\\end{array}}{!e \\in \\htmlData{k=th.Vrel}{V^{W}_{\\alpha}\\llbracket \\varnothing \\vdash \\Box(\\forall\\bar\\iota\\,\\bar\\alpha.\\,C.\\ \\ast \\mathrel{\\htmlData{k=ty.arrow}{\\multimap}}^{u} U) \\rrbracket}}\\;\\textsf{V-Box}\\\\[3ex]\\dfrac{\\begin{array}{c}\\htmlData{k=V-Ex.lb}{l \\mathrel{\\htmlData{k=ty2.le}{\\preccurlyeq}} \\htmlData{k=ty.heads}{\\mathsf{ap}}\\,\\Theta}\\quad \\htmlData{k=V-Ex.witness}{W \\vdash C[\\bar x]}\\quad v \\in \\htmlData{k=th.Vrel}{V^{W}_{\\alpha}\\llbracket \\Theta \\vdash T[\\bar x] \\rrbracket}\\end{array}}{v \\in \\htmlData{k=th.Vrel}{V^{W}_{\\alpha}\\llbracket \\Theta \\vdash \\exists^{l}\\bar\\iota.\\,C.\\,T \\rrbracket}}\\;\\textsf{V-Ex}\\\\[3ex]\\begin{array}{l}\n\\htmlData{k=rel.vsize}{V_{\\alpha}\\llbracket\\Theta \\vdash T\\rrbracket \\ \\text{by recursion on}\\ (\\alpha, \\htmlData{k=sr.size}{\\mathsf{size}}\\,T) \\in (\\mathsf{Ord} \\times \\mathbb{N}, <_{\\mathrm{lex}})} \\\\\n\\htmlData{k=sr.size}{\\mathsf{size}(\\Box(\\forall\\bar\\iota\\,\\bar\\alpha.\\,C.\\ \\ast \\mathrel{\\htmlData{k=ty.arrow}{\\multimap}}^{u} U)) = 3 + \\mathsf{size}\\,U} \\qquad \\htmlData{k=sr.size}{\\mathsf{size}(\\ast \\mathrel{\\htmlData{k=ty.arrow}{\\multimap}}^{u} U) = 2 + \\mathsf{size}\\,U}\n\\end{array}\\end{array}",
     "caption": "Each rule is one clause of $V$, by recursion on the type within a level, and $\\Theta$ maps exactly the ends the value owns. A closure is safe when its body is safe in each larger world, at each lower level, for each argument and each future of the caller above $u$. A thunk, the closure that $\\mathsf{spawn}$ runs, is read at the empty future. A box owns no end, and it is safe when $\\mathsf{thunk}(e) = \\lambda\\_.\\,e[!e]$ is safe at each instance. An existential value is a value of the body at witness points whose facts hold.",
     "about": {
      "why": "The clauses for closures, thunks and boxes quantify over larger worlds and lower levels. This quantification makes the relation compositional.",
      "used": [
       "e-rel",
       "p-rel",
       "r-fun",
       "r-boxes",
       "r-ex"
      ]
     }
    },
    {
     "id": "e-rel",
     "title": "The term relation",
     "modes": [
      "df",
      "lf"
     ],
     "rocq": "relation/Relation.v: Ebody, Eind, Etop; relation/Relation.v: at_cost_E, at_cost_V, at_cost_P",
     "tex": "\\begin{array}{c}\\begin{array}{l}\n\\htmlData{k=E.zero}{\\forall e.\\ e \\in \\htmlData{k=th.Erel}{E^{W}_{0}\\llbracket \\Theta \\vdash T \\rrbracket^{F}}} \\\\\ne \\in \\htmlData{k=th.Erel}{E^{W}_{\\alpha}\\llbracket \\Theta \\vdash T \\rrbracket^{F}},\\ \\alpha > 0 \\iff \\htmlData{k=E.kripke}{\\forall W_1 \\mathrel{\\htmlData{k=w.ext}{\\sqsupseteq}} W}. \\\\\n\\quad \\htmlData{k=E.stop}{(\\mathsf{stop})\\ \\htmlData{k=sr.irred}{\\mathsf{irred}}\\,e \\Rightarrow e \\in \\htmlData{k=th.Vrel}{V^{W_1}_{\\alpha}\\llbracket \\Theta \\vdash T \\rrbracket}} \\\\\n\\quad \\htmlData{k=E.ready}{(\\mathsf{ready})\\ \\neg\\mathsf{irred}\\,e \\Rightarrow \\htmlData{k=sr.ready}{\\mathsf{ready}_{W_1}(\\Theta \\mid F, e)}} \\\\\n\\quad \\htmlData{k=E.step}{(\\mathsf{step})\\ \\forall \\ell, e'.\\ e \\xrightarrow{\\ell} e' \\Rightarrow \\htmlData{k=sr.obl}{\\mathsf{Obl}_\\ell(e')}} \\qquad \\htmlData{k=rel.lfp}{(\\mathsf{lfp})}\n\\end{array}\\\\[3ex]\\htmlData{k=rel.atcost}{e'\\ \\mathsf{at}}\\ \\Theta' \\iff \\begin{cases} \\htmlData{k=rel.lfp}{X(W, \\Theta', T, F, e')} & c = 0 \\\\ \\forall \\beta.\\ \\beta + c \\leq \\alpha \\Rightarrow e' \\in \\htmlData{k=th.Erel}{E^{W}_{\\beta}\\llbracket \\Theta' \\vdash T \\rrbracket^{F}} & c > 0 \\end{cases} \\qquad c = \\dfo{\\htmlData{k=ct.DF}{\\kappa_{DF}}(\\ell)}\\annot{\\htmlData{k=ct.table}{\\kappa}(\\ell)}\\end{array}",
     "caption": "A term in $E$ is a value in $V$ when it is irreducible and ready when it is reducible, and each of its steps meets its obligation. After a step of cost $c > 0$ at the ordinal index $\\alpha$ the successor is read at every $\\beta$ with $\\beta + c \\leq \\alpha$, and after a free step at $\\alpha$ itself. At a limit index this is every smaller index.",
     "about": {
      "why": "The term relation is the center of the logical relation. Values, obligations and readiness are its three clauses.",
      "used": [
       "rd",
       "e-obl",
       "sj-all",
       "p-obls"
      ]
     }
    },
    {
     "id": "e-obl",
     "title": "Obligations of term steps",
     "modes": [
      "df",
      "lf"
     ],
     "rocq": "relation/Relation.v: o_beta, o_new, o_spawn, new_env; relation/Relation.v: o_send, o_recv; relation/Relation.v: o_close, o_select, o_branch, o_link",
     "tex": "\\begin{array}{c}\\begin{array}{c}\n\\dfrac{\\begin{array}{c}\\htmlData{k=rel.atcost}{e'\\ \\mathsf{at}}\\ \\Theta\\end{array}}{\\htmlData{k=O-Beta}{\\htmlData{k=sr.obl}{\\mathsf{Obl}_{\\beta}(e')}}}\\;\\textsf{O-Beta} \\qquad \\dfrac{\\begin{array}{c}\\htmlData{k=O-Spawn.split}{\\Theta = \\Theta_M \\mathbin{\\htmlData{k=ctx.tsplit}{\\uplus}} \\Theta_r}\\quad \\htmlData{k=O-Spawn.thunk}{v \\in \\htmlData{k=th.Vrel}{V^{W}_{\\alpha}\\llbracket \\Theta_M \\vdash \\ast \\mathrel{\\htmlData{k=ty.arrow}{\\multimap}}^{\\htmlData{k=ty.ubound}{\\top}}_{\\bot} \\ast \\rrbracket}}\\quad \\htmlData{k=rel.atcost}{e'\\ \\mathsf{at}}\\ \\Theta_r\\end{array}}{\\htmlData{k=O-Spawn}{\\htmlData{k=sr.obl}{\\mathsf{Obl}_{\\mathsf{spawn}\\,v}(e')}}}\\;\\textsf{O-Spawn} \\\\[2ex]\n\\dfrac{\\begin{array}{c}\\htmlData{k=O-New.cfresh}{c^{\\pm} \\notin \\mathrm{dom}\\,\\Theta} \\\\ \\htmlData{k=O-New.grow}{\\exists S, \\pi, W'.\\ W \\htmlData{k=w.ext}{\\sqsubseteq} W'},\\ \\htmlData{k=rel.atcost}{e'\\ \\mathsf{at}}_{W'}\\ \\htmlData{k=O-New.dual}{\\Theta[c^{+} \\mapsto S@\\pi,\\ c^{-} \\mapsto \\overline{S}@\\overline{\\pi}]}\\end{array}}{\\htmlData{k=O-New}{\\htmlData{k=sr.obl}{\\mathsf{Obl}_{\\mathsf{new}\\,c}(e')}}}\\;\\textsf{O-New}\n\\end{array}\\\\[3ex]\\begin{array}{c}\n\\dfrac{\\begin{array}{c}\\htmlData{k=sr.head}{\\Theta(o) \\doteq \\htmlData{k=sty.send}{!(\\bar\\iota.\\ U)}.S@x}\\quad \\htmlData{k=O-Send.split}{\\Theta \\setminus o = \\Theta_M \\mathbin{\\htmlData{k=ctx.tsplit}{\\uplus}} \\Theta_r} \\\\ \\htmlData{k=O-Send.payload}{w \\in \\htmlData{k=th.Vrel}{V^{W}_{\\dfo{\\alpha}\\annot{\\beta}}\\llbracket \\Theta_M \\vdash \\htmlData{k=ty.payload-at}{U[x\\cdot\\bar\\imath]} \\rrbracket}}\\quad \\htmlData{k=rel.atcost}{e'\\ \\mathsf{at}}\\ \\htmlData{k=O-Send.shift}{\\Theta_r[o \\mapsto S@x^{+}]}\\end{array}}{\\htmlData{k=O-Send}{\\htmlData{k=sr.obl}{\\mathsf{Obl}_{\\mathsf{send}\\,o\\,w}(e')}}}\\;\\textsf{O-Send} \\\\[2ex]\n\\dfrac{\\begin{array}{c}\\htmlData{k=sr.head}{\\Theta(o) \\doteq \\htmlData{k=sty.recv}{?(\\bar\\iota.\\ U)}.S@x} \\\\ \\htmlData{k=O-Recv.forall}{\\forall \\beta, \\Theta_{in}.\\ \\dfo{\\beta < \\alpha}\\annot{\\beta + \\kappa_{take} \\leq \\alpha},\\ \\Theta_{in} \\mathbin{\\#} \\Theta,\\ w \\in \\htmlData{k=th.Vrel}{V^{W}_{j}\\llbracket \\Theta_{in} \\vdash \\htmlData{k=ty.payload-at}{U[x\\cdot\\bar\\imath]} \\rrbracket}} \\ \\Longrightarrow\\ \\htmlData{k=O-Recv.level}{e' \\in \\htmlData{k=th.Erel}{E^{W}_{j}\\llbracket \\Theta[o \\mapsto S@x^{+}] \\cup \\Theta_{in} \\vdash T \\rrbracket^{F}}}\\end{array}}{\\htmlData{k=O-Recv}{\\htmlData{k=sr.obl}{\\mathsf{Obl}_{\\mathsf{recv}\\,o\\,w}(e')}}}\\;\\textsf{O-Recv}\n\\end{array}\\\\[3ex]\\begin{array}{c}\n\\dfrac{\\begin{array}{c}\\htmlData{k=sr.head}{\\Theta(o) \\doteq \\htmlData{k=sty.close}{\\mathsf{Close}}@x}\\quad \\htmlData{k=rel.atcost}{e'\\ \\mathsf{at}}\\ \\Theta \\setminus o\\end{array}}{\\htmlData{k=O-Close}{\\htmlData{k=sr.obl}{\\mathsf{Obl}_{\\mathsf{close}\\,o}(e')}}}\\;\\textsf{O-Close} \\qquad \\dfrac{\\begin{array}{c}\\htmlData{k=O-Link.distinct}{o_1 \\neq o_2}\\quad \\htmlData{k=O-Link.dual}{\\Theta(o_1) = S_1@x,\\ \\Theta(o_2) = S_2@\\overline{x},\\ \\htmlData{k=sty.sdual}{\\mathsf{sdual}}\\,S_1\\,S_2}\\quad \\htmlData{k=rel.atcost}{e'\\ \\mathsf{at}}\\ \\Theta \\setminus \\{o_1, o_2\\}\\end{array}}{\\htmlData{k=O-Link}{\\htmlData{k=sr.obl}{\\mathsf{Obl}_{\\mathsf{link}\\,o_1\\,o_2}(e')}}}\\;\\textsf{O-Link} \\\\[2ex]\n\\dfrac{\\begin{array}{c}\\htmlData{k=sr.head}{\\Theta(o) \\doteq \\htmlData{k=sty.plus}{\\oplus(S_1,S_2)}@x}\\quad \\htmlData{k=rel.atcost}{e'\\ \\mathsf{at}}\\ \\Theta[o \\mapsto S_i@\\htmlData{k=pt.sel}{\\overline{x\\cdot\\kappa_i}}]\\end{array}}{\\htmlData{k=O-Select}{\\htmlData{k=sr.obl}{\\mathsf{Obl}_{\\mathsf{select}_i\\,o}(e')}}}\\;\\textsf{O-Select} \\qquad \\dfrac{\\begin{array}{c}\\htmlData{k=sr.head}{\\Theta(o) \\doteq \\htmlData{k=sty.with}{\\&(S_1,S_2)}@x}\\quad \\htmlData{k=rel.atcost}{e'\\ \\mathsf{at}}\\ \\Theta[o \\mapsto S_i@\\htmlData{k=pt.bra}{x\\cdot\\kappa_i}]\\end{array}}{\\htmlData{k=O-Branch}{\\htmlData{k=sr.obl}{\\mathsf{Obl}_{\\mathsf{branch}_i\\,o}(e')}}}\\;\\textsf{O-Branch}\n\\end{array}\\end{array}",
     "caption": "Each step $e \\xrightarrow{\\alpha} e'$ of a term holding $\\Theta$ must meet $\\mathsf{Obl}_\\alpha(e')$. A $\\beta$ step keeps the ends. A spawn gives the child exactly the ends of its thunk, and a creation adds two dual ends at a fresh root or at a field. A send gives away exactly the ends of its payload, and a receive is safe for each value that may arrive. A close removes the end, a choice moves it to the field of the branch, and a link removes two dual ends.",
     "about": {
      "why": "The obligations say how each step changes ownership and points. The relation reads step labels only here.",
      "used": [
       "e-rel"
      ]
     }
    },
    {
     "id": "rd",
     "title": "Readiness",
     "modes": [
      "df",
      "lf"
     ],
     "rocq": "relation/Readiness.v: ready_t, below_rest, offered_t, stable_t, link_t; relation/Readiness.v: ready_p, above_offered, stable_p, link_p, offered_p",
     "tex": "\\begin{array}{c}\\begin{array}{rcl}\n\\htmlData{k=sr.ready}{\\mathsf{ready}_W(\\Theta \\mid F, t)} & \\iff & \\htmlData{k=rd.stable}{\\mathsf{stable}\\,t} \\Longrightarrow \\htmlData{k=rd.value}{\\mathsf{done}} \\land \\htmlData{k=rd.below-rest}{\\mathsf{ordered}} \\\\[1ex]\n\\htmlData{k=rd.value}{\\mathsf{done}} & \\iff & \\htmlData{k=rd.value}{O = \\varnothing \\Rightarrow t \\in \\mathsf{Val}} \\\\\n\\htmlData{k=rd.below-rest}{\\mathsf{ordered}} & \\iff & \\htmlData{k=rd.link}{\\mathsf{link}\\,t} \\lor {} \\htmlData{k=rd.below-rest}{\\forall o \\in O.\\ \\htmlData{k=rd.below-held}{(\\forall o' \\in \\mathrm{dom}\\,\\Theta \\setminus O.\\ W \\vdash x_o \\prec \\overline{x_{o'}})} \\land \\htmlData{k=rd.below-future}{(\\forall y \\in F.\\ W \\vdash x_o \\prec y)}} \\\\[1ex]\n & & O = \\htmlData{k=rd.offered}{\\mathsf{offered}_\\Theta(t)} \\qquad \\Theta(o) = S@x_o\n\\end{array}\\\\[3ex]\\begin{array}{rcl}\n\\htmlData{k=sr.readyp}{\\mathsf{ready}_W(\\Sigma, p)} & \\iff & \\htmlData{k=rd.p-stable}{\\mathsf{stable}\\,p} \\Longrightarrow \\htmlData{k=rd.link}{\\mathsf{link}\\,p} \\lor (\\htmlData{k=rd.p-term}{\\mathsf{done}} \\land \\htmlData{k=rd.above-offered}{\\mathsf{covered}}) \\\\[1ex]\n\\htmlData{k=rd.p-term}{\\mathsf{done}} & \\iff & \\htmlData{k=rd.p-term}{O = \\varnothing \\Rightarrow \\htmlData{k=prop.terminated}{\\mathsf{terminated}}\\,p} \\\\\n\\htmlData{k=rd.above-offered}{\\mathsf{covered}} & \\iff & \\htmlData{k=rd.above-offered}{\\forall o \\in \\mathrm{dom}\\,\\Sigma \\setminus O.\\ \\exists o' \\in O.\\ W \\vdash x_{o'} \\prec \\overline{x_o}} \\\\[1ex]\n & & O = \\htmlData{k=rd.offered}{\\mathsf{offered}_\\Sigma(p)}\n\\end{array}\\end{array}",
     "caption": "Readiness constrains a stuck term, one that can only offer actions. A stuck term has finished when it offers nothing, and each end it offers lies below the dual points of the ends it keeps and below its future. A stuck process is at a link, or has finished when it offers nothing, and each interface end it keeps has an offered end below its dual point. Internal channels have no points.",
     "about": {
      "why": "In a strict order some stuck thread waits at a minimal point, and the thread holding the dual end can act with that thread. Adequacy uses this argument to derive deadlock freedom from readiness.",
      "used": [
       "e-rel",
       "p-rel",
       "th-adeq"
      ]
     }
    },
    {
     "id": "p-rel",
     "title": "The process relation",
     "modes": [
      "df",
      "lf"
     ],
     "rocq": "relation/Relation.v: Pbody, Pclauses, Pind, Ptop; relation/Relation.v: fuse_ok, pheld, pfuse, sdrop, dpairs, gch",
     "tex": "\\begin{array}{c}\\begin{array}{l}\np \\in \\htmlData{k=th.Prel}{P^{W}_{n{+}1}\\llbracket \\Sigma \\vdash T \\rrbracket} \\iff \\htmlData{k=P.strict}{\\forall W_1 \\mathrel{\\htmlData{k=w.ext}{\\sqsupseteq}} W}.\\ \\htmlData{k=P.fuse}{\\forall (h, D) \\in \\htmlData{k=sr.fuseok}{\\mathsf{Fus}}(\\Sigma, p)}.\\ \\htmlData{k=P.clauses}{\\mathsf{clauses}_{W_1}}(\\htmlData{k=sr.pfuse}{(h, D) \\cdot \\Sigma}, \\htmlData{k=sr.pfuse}{(h, D) \\cdot p}) \\\\[1ex]\n\\htmlData{k=P.clauses}{\\mathsf{clauses}_{W_1}(\\Sigma', p')} \\iff \\\\\n\\quad \\htmlData{k=P-Stop}{(\\mathsf{stop})\\ \\htmlData{k=sr.pirred}{\\mathsf{pirred}}\\,p' \\Rightarrow p' = (\\varnothing, \\{v\\} \\mathbin{\\htmlData{k=tp.msunion}{\\uplus}} E) \\land v \\in \\htmlData{k=th.Vrel}{V^{W_1}_{n{+}1}\\llbracket \\Sigma' \\vdash T \\rrbracket} \\land E \\subseteq \\{\\ast\\}} \\\\\n\\quad \\htmlData{k=P-Ready}{(\\mathsf{ready})\\ \\neg\\mathsf{pirred}\\,p' \\Rightarrow \\htmlData{k=sr.readyp}{\\mathsf{ready}_{W_1}(\\Sigma', p')}} \\\\\n\\quad \\htmlData{k=P-Step}{(\\mathsf{step})\\ p' \\xrightarrow{ev} p'' \\Rightarrow \\htmlData{k=sr.pobl}{\\mathsf{Pobl}_{ev}(p'')}} \\qquad \\htmlData{k=rel.lfp}{(\\mathsf{lfp})}\n\\end{array}\\\\[3ex]\\begin{array}{rcll}\n\\htmlData{k=sr.fuseok}{(h, D) \\in \\mathsf{Fus}(\\Sigma, (C, E))} & \\iff & \\htmlData{k=fuse.dcomm}{\\forall o.\\ h(\\overline{o}) = \\overline{h(o)}} \\\\\n & \\land & \\htmlData{k=fuse.inj}{\\forall o_1, o_2 \\in \\mathsf{held}.\\ h(o_1) = h(o_2) \\Rightarrow o_1 = o_2} \\\\\n & \\land & \\htmlData{k=fuse.partners}{\\forall o_1, o_2 \\in \\mathsf{held}.\\ h(o_2) = \\overline{h(o_1)} \\Rightarrow o_2 = \\overline{o_1} \\lor \\htmlData{k=end.ech}{\\mathsf{ech}}(h\\,o_1) \\in D} \\\\\n & \\land & \\htmlData{k=fuse.D}{D \\cap \\htmlData{k=sr.gch}{\\mathsf{gch}_h}[C] = \\varnothing} \\land \\htmlData{k=fuse.dpairs}{\\mathsf{dpairs}\\,D\\,(h\\,\\Sigma)} \\\\[1ex]\n\\htmlData{k=sr.held}{\\mathsf{held}} & = & \\htmlData{k=sr.held}{\\{o \\mid o \\in \\mathrm{dom}\\,\\Sigma \\lor \\htmlData{k=end.ech}{\\mathsf{ech}}\\,o \\in C\\}} \\\\\n\\htmlData{k=sr.gch}{\\mathsf{gch}_h(c)} & = & \\htmlData{k=sr.gch}{\\htmlData{k=end.ech}{\\mathsf{ech}}(h(c^{+}))} \\\\\n\\htmlData{k=sr.sdrop}{(h, D) \\cdot \\Sigma} & = & \\htmlData{k=sr.sdrop}{\\{h(o) \\mapsto y \\mid o \\mapsto y \\in \\Sigma,\\ \\htmlData{k=end.ech}{\\mathsf{ech}}(h\\,o) \\notin D\\}} \\\\\n\\htmlData{k=sr.pfuse}{(h, D) \\cdot (C, E)} & = & \\htmlData{k=sr.pfuse}{(\\mathsf{gch}_h[C] \\cup D,\\ h[E])} \\\\\n\\htmlData{k=fuse.dpairs}{\\mathsf{dpairs}\\,D\\,\\Sigma} & \\iff & \\htmlData{k=fuse.dpairs}{\\htmlData{k=end.ech}{\\mathsf{ech}}\\,o \\in D \\Rightarrow \\Sigma(o) = S@x \\land \\Sigma(\\overline{o}) = S'@\\overline{x} \\land \\htmlData{k=sty.sdual}{\\mathsf{sdual}}\\,S\\,S'}\n\\end{array}\\end{array}",
     "caption": "A process satisfies the three clauses of a term, stop, ready and step, in each larger ranked world and after each admissible fusion of its held ends. An admissible fusion $(h, D)$ renames held ends injectively, except for the new pairs it restricts in $D$.",
     "about": {
      "why": "Composition fuses ends of two processes. Building fusion into the relation lets the semantic P-Connect hold without further proof.",
      "used": [
       "p-obls",
       "sj-all",
       "th-compose"
      ]
     }
    },
    {
     "id": "p-obls",
     "title": "Obligations of process steps",
     "modes": [
      "df",
      "lf"
     ],
     "rocq": "relation/Relation.v: q_tau, q_send, q_recv, q_close, q_select, q_branch, q_link; relation/Relation.v: send_split, recv_ok, recv_back, recv_env",
     "tex": "\\begin{array}{c}\\begin{array}{c}\n\\dfrac{\\begin{array}{c}C' \\cap \\htmlData{k=tp.chans}{\\mathsf{chans}}\\,\\Sigma = \\varnothing\\quad p'\\ \\htmlData{k=rel.atcost}{\\mathsf{at}}_{\\htmlData{k=ct.sync}{\\dfo{\\htmlData{k=ct.DF}{\\kappa_{DF}}(ev)}\\annot{\\htmlData{k=ct.table}{\\kappa}(ev)}}}\\ \\Sigma\\end{array}}{\\htmlData{k=Q-Tau}{\\htmlData{k=sr.pobl}{\\mathsf{Pobl}_{ev}(p')}}}\\;\\textsf{Q-Tau} \\\\[2ex]\n\\dfrac{\\begin{array}{c}\\htmlData{k=sr.head}{\\Sigma(o) \\doteq \\htmlData{k=sty.send}{!(\\bar\\iota.\\ U)}.S@x}\\quad \\Sigma \\setminus o = \\Sigma_v \\mathbin{\\htmlData{k=ctx.tsplit}{\\uplus}} \\Sigma_r \\\\ \\htmlData{k=Q-Send.theta-e}{\\mathrm{dom}\\,\\Theta_e = \\{o' \\in \\htmlData{k=syn.fends}{\\mathsf{fends}}(w) \\mid \\htmlData{k=end.ech}{\\mathsf{ech}}(o') \\in C\\}}\\quad \\htmlData{k=Q-Send.split}{\\mathsf{send\\_split}\\,\\Sigma\\,\\Sigma_e\\,\\Theta_e} \\\\ w \\in \\htmlData{k=th.Vrel}{V^{W}_{\\dfo{\\alpha}\\annot{\\beta}}\\llbracket \\Sigma_v \\cup \\Theta_e \\vdash \\htmlData{k=ty.payload-at}{U[x\\cdot\\bar\\imath]} \\rrbracket}\\quad \\htmlData{k=rel.atcost}{p'\\ \\mathsf{at}}\\ (\\Sigma_r \\cup \\htmlData{k=Q-Send.sigma-e}{\\Sigma_e})[o \\mapsto S@x^{+}]\\end{array}}{\\htmlData{k=Q-Send}{\\htmlData{k=sr.pobl}{\\mathsf{Pobl}_{\\mathsf{send}\\,o\\,w}(p')}}}\\;\\textsf{Q-Send} \\\\[2ex]\n\\dfrac{\\begin{array}{c}\\htmlData{k=sr.head}{\\Sigma(o) \\doteq \\htmlData{k=sty.recv}{?(\\bar\\iota.\\ U)}.S@x} \\\\ \\forall j, \\Theta_2.\\ \\dfo{\\beta < \\alpha}\\annot{\\beta + \\kappa_{take} \\leq \\alpha},\\ \\htmlData{k=end.ech}{\\mathsf{ech}}[\\mathrm{dom}\\,\\Theta_2] \\cap C = \\varnothing,\\ \\htmlData{k=Q-Recv.ok}{\\mathsf{recv\\_ok}\\,\\Sigma'\\,\\Theta_2},\\ w \\in \\htmlData{k=th.Vrel}{V^{W}_{j}\\llbracket \\Theta_2 \\vdash \\htmlData{k=ty.payload-at}{U[x\\cdot\\bar\\imath]} \\rrbracket} \\\\ \\Longrightarrow\\ (C' \\cup \\htmlData{k=Q-Recv.back}{\\mathsf{recv\\_back}\\,\\Sigma'\\,\\Theta_2}, E') \\in \\htmlData{k=th.Prel}{P^{W}_{j}\\llbracket \\htmlData{k=Q-Recv.env}{\\mathsf{recv\\_env}\\,\\Sigma'\\,\\Theta_2} \\vdash T \\rrbracket}\\end{array}}{\\htmlData{k=Q-Recv}{\\htmlData{k=sr.pobl}{\\mathsf{Pobl}_{\\mathsf{recv}\\,o\\,w}(p')}}}\\;\\textsf{Q-Recv} \\\\[2ex]\n\\htmlData{k=Q-Link}{\\textsf{Q-Close, Q-Select, Q-Branch, Q-Link} = \\textsf{O-Close, O-Select, O-Branch, O-Link}\\,[\\Sigma/\\Theta,\\ P/E]} \\\\\np = (C, E),\\ p' = (C', E'),\\ \\Sigma' = \\Sigma[o \\mapsto S@x^{+}]\n\\end{array}\\\\[3ex]\\begin{array}{l}\n\\htmlData{k=Q-Send.split}{\\mathsf{send\\_split}\\,\\Sigma\\,\\Sigma_e\\,\\Theta_e} \\iff (\\forall o \\in \\mathrm{dom}\\,\\Theta_e.\\ o, \\overline{o} \\notin \\mathrm{dom}\\,\\Sigma) \\land {} \\\\\n\\quad (\\forall o.\\ o \\in \\mathrm{dom}\\,\\Sigma_e \\iff \\overline{o} \\in \\mathrm{dom}\\,\\Theta_e \\land o \\notin \\mathrm{dom}\\,\\Theta_e) \\land {} \\\\\n\\quad (\\forall o.\\ \\Theta_e(o) = S@y \\Rightarrow \\exists S'.\\ (\\Sigma_e \\cup \\Theta_e)(\\overline{o}) = S'@\\overline{y} \\land \\htmlData{k=sty.sdual}{\\mathsf{sdual}}\\,S\\,S') \\\\\n\\htmlData{k=Q-Recv.ok}{\\mathsf{recv\\_ok}\\,\\Sigma\\,\\Theta_2} \\iff (\\forall o \\in \\mathrm{dom}\\,\\Theta_2.\\ o \\notin \\mathrm{dom}\\,\\Sigma) \\land {} \\\\\n\\quad (\\forall o.\\ \\Theta_2(o) = S@y \\land (\\Sigma \\cup \\Theta_2)(\\overline{o}) = S'@y' \\Rightarrow y' = \\overline{y} \\land \\htmlData{k=sty.sdual}{\\mathsf{sdual}}\\,S\\,S') \\\\\n\\htmlData{k=Q-Recv.back}{\\mathsf{recv\\_back}\\,\\Sigma\\,\\Theta_2 = \\htmlData{k=end.ech}{\\mathsf{ech}}[\\{o \\in \\mathrm{dom}\\,\\Theta_2 \\mid \\overline{o} \\in \\mathrm{dom}\\,\\Sigma \\cup \\mathrm{dom}\\,\\Theta_2\\}]} \\\\\n\\htmlData{k=Q-Recv.env}{\\mathsf{recv\\_env}\\,\\Sigma\\,\\Theta_2 = \\{o \\mapsto y \\in \\Sigma \\mid \\overline{o} \\notin \\mathrm{dom}\\,\\Theta_2\\} \\cup {}} \\\\\n\\quad \\htmlData{k=Q-Recv.env}{\\{o \\mapsto y \\in \\Theta_2 \\mid \\overline{o} \\notin \\mathrm{dom}\\,\\Sigma \\cup \\mathrm{dom}\\,\\Theta_2\\}}\n\\end{array}\\end{array}",
     "caption": "Internal steps, including messages between two threads of $p$, keep the interface. A message with the outside moves ends across the interface. A send gives away its payload ends, including the ends $\\Theta_e$ of internal channels, and a receive must be safe for each value that may arrive at each lower level.",
     "about": {
      "why": "Each case says how the interface changes at a step and where the successor must be safe.",
      "used": [
       "p-rel"
      ]
     }
    },
    {
     "id": "fu-vs",
     "title": "Relation and fuel side by side",
     "rocq": "relation/Relation.v: Erel; fuel/Fuel.v: FuelE; soup/Soup.v: Soup",
     "modes": [
      "lf"
     ],
     "tex": "\\begin{array}{l|l|l}\n & \\text{the relation} & \\text{fuel} \\\\ \\hline\n\\text{a thread} & e \\in \\htmlData{k=th.Erel}{E^{W}_{\\alpha}\\llbracket \\Theta \\vdash T \\rrbracket^{F}} & e \\in \\htmlData{k=sr.FE}{F^{N}_{\\alpha}\\llbracket \\htmlData{k=fu.Phi}{\\Phi} \\vdash \\sigma\\ !\\ d \\rrbracket} \\\\\n\\text{an end} & o \\mapsto S@x \\text{ in } \\Theta & o \\mapsto S^{f}_{m} \\text{ in } \\Phi \\\\\n\\text{a value} & v \\in \\htmlData{k=th.Vrel}{V^{W}_{\\alpha}\\llbracket \\Theta \\vdash T \\rrbracket} & v \\in \\htmlData{k=sr.FV}{FV^{N}_{\\alpha}\\llbracket \\htmlData{k=fu.Phi}{\\Phi} \\vdash T\\annot{^{a}} \\rrbracket} \\\\\n\\text{a step } \\alpha & \\htmlData{k=sr.obl}{\\mathsf{Obl}_\\alpha(e')} & \\htmlData{k=sr.fobl}{\\mathsf{Fobl}_\\alpha(e')} \\\\\n\\text{rules out} & \\text{a stuck wait, and at } \\kappa_L \\text{ a loop of free steps} & \\text{a wait that never ends} \\\\\n\\text{used in} & \\htmlData{k=sj.term}{\\vDash} \\text{ and the lock-free process relation} & \\text{the lock-free process relation only}\n\\end{array}",
     "caption": "Fuel is a second predicate on a thread, separate from the relation and with the same shape, a value clause and one obligation per step. The relation gives each end a point, $S@x$, and fuel gives it a counter and tickets, $S^f_m$. The lock-free process relation requires both of each thread. The relation makes a stuck thread ready, and fuel bounds how often the thread holding a dual end acts on other ends first.",
     "about": {
      "why": "This table compares what the relation and fuel read and guarantee, and shows that the lock-free process relation is where they meet.",
      "used": [
       "fu",
       "soup",
       "th-chain"
      ]
     }
    },
    {
     "id": "fu",
     "title": "Fuel",
     "modes": [
      "lf"
     ],
     "rocq": "fuel/Fuel.v: Fdef, FuelE, FLev; fuel/Fuel.v: fsem; cost/CostSem.v: csem",
     "tex": "\\begin{array}{c}\\begin{array}{l}\n\\htmlData{k=fu.zero}{\\forall e.\\ e \\in \\htmlData{k=sr.FE}{F^{N}_{0}\\llbracket \\Phi \\vdash \\sigma\\ !\\ d \\rrbracket}} \\\\\ne \\in \\htmlData{k=sr.FE}{F^{N}_{\\alpha}\\llbracket \\htmlData{k=fu.Phi}{\\Phi} \\vdash \\htmlData{k=fu.rty}{\\sigma}\\ !\\ \\htmlData{k=fu.frame}{d} \\rrbracket},\\ \\alpha > 0 \\iff \\htmlData{k=fu.rename}{g,\\ \\mathsf{injective}(g|_{\\mathrm{dom}\\,\\Phi})}. \\\\\n\\quad \\htmlData{k=fu.val}{(\\mathsf{stop})\\ g(e) \\in \\mathsf{Val} \\Rightarrow g(e) \\in \\htmlData{k=sr.FV}{FV^{N}_{\\alpha}\\llbracket g\\Phi \\vdash \\sigma \\rrbracket}} \\\\\n\\quad \\htmlData{k=fu.step}{(\\mathsf{step})\\ g(e) \\xrightarrow{\\ell} e' \\Rightarrow \\forall \\beta < \\alpha.\\ \\htmlData{k=sr.fobl}{\\mathsf{Fobl}\\annot{^{N}}_{\\ell}(e')}} \\\\[6pt]\n\\htmlData{k=fu.Phi}{\\Phi : \\mathsf{End} \\rightharpoonup \\mathsf{STy} \\times \\mathbb{N} \\times \\mathbb{N},\\quad \\Phi(o) = S^{f}_{m},\\ f \\leq m}\n\\end{array}\\\\[3ex]\\begin{array}{l}\n\\htmlData{k=fu.fsem}{\\mathsf{fsem}\\,N\\,\\Phi\\,e \\iff \\forall \\alpha.\\ e \\in \\htmlData{k=sr.FE}{F^{N}_{\\alpha}\\llbracket \\Phi \\vdash \\htmlData{k=fu.rty}{\\mathsf{thread}}\\ !\\ \\infty \\rrbracket}} \\\\\n\\htmlData{k=cs.csem}{\\Delta \\vDash^{N} e : T\\ !\\ \\varepsilon}\n\\end{array}\\end{array}",
     "caption": "Fuel has the shape of the term relation $E$ without the ready clause. $e \\in F^N_n\\llbracket \\Phi \\vdash \\sigma\\ !\\ d\\rrbracket$ says that the thread $e$, which holds the ends $\\Phi$ with their counters and tickets, has fuel for $n$ more steps. When $e$ is a value it is in $FV$ at $\\sigma$. Otherwise each step meets its fuel obligation one level lower.",
     "about": {
      "why": "Fuel bounds how often a thread acts on other ends before it acts on an end it holds. Lock-free adequacy measures waits with these counters and tickets.",
      "used": [
       "fu-obls",
       "soup",
       "th-terms"
      ]
     }
    },
    {
     "id": "fu-obls",
     "title": "Fuel obligations",
     "modes": [
      "lf"
     ],
     "rocq": "fuel/Fuel.v: f_act, fspare, idle_at, refill, ftick, fhand; fuel/Fuel.v: f_beta, f_new, f_spawn, f_link, plink; fuel/Fuel.v: f_send, f_recv, f_close, f_select, f_branch",
     "tex": "\\begin{array}{c}\\begin{array}{rcll}\n\\htmlData{k=sr.act}{\\mathsf{act}}\\,o & \\iff & \\htmlData{k=F-Wait}{\\Phi(o) = S^{f}_{m} \\land \\neg \\htmlData{k=fu.idle}{\\mathsf{idle}}\\,S} & \\text{F-Wait} \\\\\n & \\land & \\htmlData{k=F-Tick}{\\htmlData{k=fu.fspare}{\\mathsf{positive}}(\\Phi \\setminus o)} \\land \\htmlData{k=F-Tick.frame}{1 \\leq d} & \\text{F-Count} \\\\[4pt]\n\\htmlData{k=fu.fspare}{\\mathsf{positive}}(\\Phi) & \\iff & \\htmlData{k=fu.fspare}{\\forall o \\mapsto S^{f}_{m} \\in \\Phi.\\ \\neg\\mathsf{idle}\\,S \\Rightarrow 1 \\leq f} \\\\\n\\htmlData{k=fu.tick}{\\Phi{\\downarrow}} & = & \\htmlData{k=fu.tick}{\\{o \\mapsto S^{f \\mathbin{\\dot-} 1}_{m} \\mid o \\mapsto S^{f}_{m} \\in \\Phi\\}} \\\\\n\\htmlData{k=fu.idle}{\\mathsf{idle}}\\,S & \\iff & \\htmlData{k=sty.unfold}{\\mathsf{unfold}}\\,S = \\htmlData{k=sty.skip}{\\mathsf{Skip}}\n\\end{array}\\\\[3ex]\\begin{array}{c}\n\\dfrac{\\begin{array}{c}e' \\in \\htmlData{k=sr.FE}{F^{N}_{\\beta}\\llbracket \\Phi \\vdash \\sigma\\ !\\ d \\rrbracket}\\end{array}}{\\htmlData{k=F-Beta}{\\mathsf{Fobl}_{\\beta}(e')}}\\;\\textsf{F-Beta} \\qquad\n\\dfrac{\\begin{array}{c}\\htmlData{k=F-New.fresh}{c^{\\pm} \\notin \\mathrm{dom}\\,\\Phi} \\Rightarrow \\exists S, m_1, m_2.\\ m_1 + m_2 \\leq N \\land e' \\in \\htmlData{k=sr.FE}{F^{N}_{\\beta}\\llbracket \\htmlData{k=F-New.cnew}{\\Phi[c^{+} \\mapsto S^{m_1}_{m_1}, c^{-} \\mapsto \\overline{S}^{m_2}_{m_2}]} \\vdash \\sigma\\ !\\ d \\rrbracket}\\end{array}}{\\htmlData{k=F-New}{\\mathsf{Fobl}_{\\mathsf{new}\\,c}(e')}}\\;\\textsf{F-New} \\\\[10pt]\n\\dfrac{\\begin{array}{c}M = \\htmlData{k=syn.fends}{\\mathsf{fends}}(v)\\quad \\htmlData{k=F-Spawn.held}{M \\subseteq \\mathrm{dom}\\,\\Phi}\\quad \\htmlData{k=fu.fspare}{\\mathsf{positive}}(\\Phi|_M) \\\\ \\htmlData{k=F-Spawn.child}{v\\,\\ast \\in \\htmlData{k=sr.FE}{F^{N}_{\\beta}\\llbracket \\htmlData{k=fu.tick}{\\Phi|_M{\\downarrow}} \\vdash \\htmlData{k=fu.rty}{\\mathsf{thread}}\\ !\\ \\infty \\rrbracket}} \\\\ e' \\in \\htmlData{k=sr.FE}{F^{N}_{\\beta}\\llbracket \\Phi \\setminus M \\vdash \\sigma\\ !\\ d \\rrbracket}\\end{array}}{\\htmlData{k=F-Spawn}{\\mathsf{Fobl}_{\\mathsf{spawn}\\,v}(e')}}\\;\\textsf{F-Spawn} \\\\[10pt]\n\\dfrac{\\begin{array}{c}\\htmlData{k=F-Link.plink}{\\Phi(o_1) = S^{f_1}_{m_1},\\ \\Phi(o_2) = S'^{f_2}_{m_2},\\ o_1 \\neq o_2,\\ S' \\mathrel{\\htmlData{k=sty.sequiv}{\\simeq}} \\overline{S}}\\quad \\htmlData{k=F-Link.ticket}{f_1 + m_2 > N,\\ f_2 + m_1 > N} \\\\ e' \\in \\htmlData{k=sr.FE}{F^{N}_{\\beta}\\llbracket \\Phi \\setminus \\{o_1,o_2\\} \\vdash \\sigma\\ !\\ d \\rrbracket}\\end{array}}{\\htmlData{k=F-Link}{\\mathsf{Fobl}_{\\mathsf{link}\\,o_1\\,o_2}(e')}}\\;\\textsf{F-Link}\n\\end{array}\\\\[3ex]\\begin{array}{c}\n\\dfrac{\\begin{array}{c}\\htmlData{k=sr.act}{\\mathsf{act}}\\,o\\quad \\Phi(o) = S_0{}^{f}_{m}\\quad \\htmlData{k=sty.unfold}{\\mathsf{unfold}}\\,S_0 = \\htmlData{k=sty.send}{!(\\bar\\iota.\\ T)}.S\\quad M = \\htmlData{k=syn.fends}{\\mathsf{fends}}(w)\\quad \\htmlData{k=F-Send.notsubj}{o \\notin M \\subseteq \\mathrm{dom}\\,\\Phi}\\quad \\htmlData{k=fu.fspare}{\\mathsf{positive}}(\\Phi|_M) \\\\ \\htmlData{k=F-Send.payload}{w \\in \\htmlData{k=sr.FV}{FV^{N}_{\\beta}\\llbracket \\htmlData{k=fu.tick}{\\Phi|_M{\\downarrow}} \\vdash T \\rrbracket}} \\\\ e' \\in \\htmlData{k=sr.FE}{F^{N}_{\\beta}\\llbracket \\htmlData{k=fu.tick}{(\\Phi \\setminus M){\\downarrow}}[o \\mapsto S^{m}_{m}] \\vdash \\sigma\\ !\\ d \\mathbin{\\dot-} 1 \\rrbracket}\\end{array}}{\\htmlData{k=F-Send}{\\mathsf{Fobl}_{\\mathsf{send}\\,o\\,w}(e')}}\\;\\textsf{F-Send} \\\\[10pt]\n\\dfrac{\\begin{array}{c}\\htmlData{k=sr.act}{\\mathsf{act}}\\,o\\quad \\Phi(o) = S_0{}^{f}_{m}\\quad \\htmlData{k=sty.unfold}{\\mathsf{unfold}}\\,S_0 = \\htmlData{k=sty.recv}{?(\\bar\\iota.\\ T)}.S \\\\ \\htmlData{k=F-Recv.forall}{\\forall \\gamma \\leq \\beta,\\ \\Phi_i \\mathbin{\\#} \\Phi.\\ w \\in \\htmlData{k=sr.FV}{FV^{N}_{\\gamma}\\llbracket \\Phi_i \\vdash T \\rrbracket}} \\Rightarrow e' \\in \\htmlData{k=sr.FE}{F^{N}_{\\gamma}\\llbracket \\htmlData{k=fu.tick}{\\Phi{\\downarrow}}[o \\mapsto S^{m}_{m}] \\cup \\Phi_i \\vdash \\sigma\\ !\\ d \\mathbin{\\dot-} 1 \\rrbracket}\\end{array}}{\\htmlData{k=F-Recv}{\\mathsf{Fobl}_{\\mathsf{recv}\\,o\\,w}(e')}}\\;\\textsf{F-Recv} \\\\[10pt]\n\\dfrac{\\begin{array}{c}\\htmlData{k=sr.act}{\\mathsf{act}}\\,o\\quad \\Phi(o) = S_0{}^{f}_{m}\\quad \\htmlData{k=sty.unfold}{\\mathsf{unfold}}\\,S_0 = \\htmlData{k=sty.close}{\\mathsf{Close}} \\\\ e' \\in \\htmlData{k=sr.FE}{F^{N}_{\\beta}\\llbracket \\htmlData{k=fu.tick}{(\\Phi \\setminus o){\\downarrow}} \\vdash \\sigma\\ !\\ d \\mathbin{\\dot-} 1 \\rrbracket}\\end{array}}{\\htmlData{k=F-Close}{\\mathsf{Fobl}_{\\mathsf{close}\\,o}(e')}}\\;\\textsf{F-Close} \\qquad\n\\dfrac{\\begin{array}{c}\\htmlData{k=sr.act}{\\mathsf{act}}\\,o\\quad \\Phi(o) = S_0{}^{f}_{m}\\quad \\htmlData{k=sty.unfold}{\\mathsf{unfold}}\\,S_0 \\in \\{\\oplus(S_1,S_2), \\&(S_1,S_2)\\} \\\\ e' \\in \\htmlData{k=sr.FE}{F^{N}_{\\beta}\\llbracket \\htmlData{k=fu.tick}{\\Phi{\\downarrow}}[o \\mapsto S_i{}^{m}_{m}] \\vdash \\sigma\\ !\\ d \\mathbin{\\dot-} 1 \\rrbracket}\\end{array}}{\\htmlData{k=F-Close}{\\mathsf{Fobl}_{\\mathsf{sel}_i\\,o}(e'),\\ \\mathsf{Fobl}_{\\mathsf{bra}_i\\,o}(e')}}\\;\\textsf{F-Choice}\n\\end{array}\\end{array}",
     "caption": "An action on $o$ requires $o$ held and not idle, and a positive counter on the other ends that are not idle and on the frame. It uses one unit of the frame, advances the protocol of $o$, resets the counter of $o$ to its tickets $m$ and decrements the other counters, written $\\Phi{\\downarrow}[o \\mapsto S^{m}_{m}]$. Internal steps decrement no counter. A new channel starts each end at its tickets. A send hands the ends of its payload on with their counters minus one. A link lowers no counter and asks the counter of each linked end to exceed the partner bound $N - m$ of the other.",
     "about": {
      "why": "Each kind of step changes the held ends, counters and tickets in one way, the same at each level.",
      "used": [
       "fu"
      ]
     }
    },
    {
     "id": "fv",
     "title": "Values with fuel",
     "rocq": "fuel/Fuel.v: Vty, Vres",
     "modes": [
      "lf"
     ],
     "tex": "\\begin{array}{c}\n\\dfrac{\\begin{array}{c}S' \\mathrel{\\htmlData{k=sty.sequiv}{\\simeq}} S\\quad \\htmlData{k=FV-Sess.counter}{a \\leq f}\\end{array}}{\\htmlData{k=FV-Sess}{o \\in \\htmlData{k=sr.FV}{FV^{N}_{\\alpha}\\llbracket \\{o \\mapsto S'^{f}_{m}\\} \\vdash (S@x)\\annot{^{a}}_{m} \\rrbracket}}}\\;\\textsf{FV-Sess} \\qquad\n\\dfrac{\\begin{array}{c}\\Phi = \\varnothing\\end{array}}{\\htmlData{k=FV-Thread}{v \\in \\htmlData{k=sr.FV}{FV^{N}_{\\alpha}\\llbracket \\Phi \\vdash \\htmlData{k=fu.rty}{\\mathsf{thread}} \\rrbracket}}}\\;\\textsf{FV-Thread} \\\\[10pt]\n\\dfrac{\\begin{array}{c}\\htmlData{k=FV-Arrow.exact}{\\htmlData{k=syn.fends}{\\mathsf{fends}}\\,e = \\mathrm{dom}\\,\\Phi}\\quad \\htmlData{k=FV-Arrow.floor}{\\Phi(o) = S^{f} \\land \\neg\\htmlData{k=fu.idle}{\\mathsf{idle}}\\,S \\Rightarrow a \\leq f} \\\\ \\forall \\beta < \\alpha,\\ \\htmlData{k=FV-Arrow.call}{\\Phi' \\geq \\Phi - a},\\ u \\in \\htmlData{k=sr.FV}{FV^{N}_{j}\\llbracket \\Phi_u \\vdash T \\rrbracket} \\\\ \\htmlData{k=FV-Arrow.body}{e[u] \\in \\htmlData{k=sr.FE}{F^{N}_{j}\\llbracket \\Phi' \\cup \\Phi_u \\vdash U\\ !\\ c \\rrbracket}}\\end{array}}{\\htmlData{k=FV-Arrow}{\\lambda e \\in \\htmlData{k=sr.FV}{FV^{N}_{\\alpha}\\llbracket \\Phi \\vdash (T \\mathrel{\\htmlData{k=ty.arrow}{\\multimap}}[c]\\, U)\\annot{^{a}} \\rrbracket}}}\\;\\textsf{FV-Arrow} \\\\[10pt]\n\\dfrac{\\begin{array}{c}\\htmlData{k=FV-Box.noends}{\\htmlData{k=syn.fends}{\\mathsf{fends}}\\,e = \\varnothing} \\\\ \\forall \\beta < \\alpha,\\ \\bar s \\in \\htmlData{k=tp.sinsts}{\\mathsf{sinsts}}\\,N \\\\ \\htmlData{k=FV-Box.body}{e[!e] \\in \\htmlData{k=sr.FE}{F^{N}_{j}\\llbracket \\varnothing \\vdash U[\\bar s]\\ !\\ c \\rrbracket}}\\end{array}}{\\htmlData{k=FV-Box}{!e \\in \\htmlData{k=sr.FV}{FV^{N}_{\\alpha}\\llbracket \\varnothing \\vdash \\Box(\\forall\\bar\\iota\\,\\bar\\alpha.\\ C.\\ \\ast \\mathrel{\\htmlData{k=ty.arrow}{\\multimap}}^{u}[c]\\, U) \\rrbracket}}}\\;\\textsf{FV-Box} \\\\[6pt]\n\\htmlData{k=sr.fvagg}{\\langle v_1, v_2\\rangle \\in \\htmlData{k=sr.FV}{FV^{N}_{\\alpha}\\llbracket \\Phi_1 \\uplus \\Phi_2 \\vdash T_1 \\otimes T_2 \\rrbracket} \\iff v_i \\in \\htmlData{k=sr.FV}{FV^{N}_{\\alpha}\\llbracket \\Phi_i \\vdash T_i \\rrbracket}}\n\\end{array}",
     "caption": "Values with fuel by recursion on the type. The counter of an end is at least its credit. A closure keeps the counters of its captured ends that are not idle at least at its credit $a$. Its body has fuel at each call whose counters are at least the counters at creation minus $a$. A box holds no end, and its body has fuel at each force.",
     "about": {
      "why": "Values with fuel connect credits in types with counters at run time.",
      "used": [
       "fu-obls",
       "th-terms"
      ]
     }
    },
    {
     "id": "soup",
     "title": "The lock-free process relation",
     "modes": [
      "lf"
     ],
     "rocq": "soup/State.v: hold, lfstate; soup/State.v: soup_gen, soup/Soup.v: soup_inv, Soup",
     "tex": "\\begin{array}{c}\\begin{array}{c}\n\\htmlData{k=sp.state}{a = (q, K)} \\qquad \\htmlData{k=sp.hold}{K : \\mathsf{End} \\rightharpoonup \\mathbb{N} \\times \\mathsf{Point} \\times \\mathbb{N} \\times \\mathbb{N}} \\\\\n\\htmlData{k=sp.next}{\\mathsf{lf\\_next}\\,N\\,(q, K)\\,ev\\,(q', K') \\iff K' \\in \\mathsf{own\\_next}\\,N\\,ev\\,K}\n\\end{array}\\\\[3ex]\\begin{array}{rcll}\na \\in \\htmlData{k=th.soup}{S^{N,W}_\\alpha\\llbracket\\Sigma \\vdash T\\rrbracket} & \\iff & \\htmlData{k=sp.exists}{\\exists A, \\Phi}.\\ \\htmlData{k=sp.tfree}{\\htmlData{k=ty.tfree}{\\mathsf{tfree}}\\,T} \\land \\text{for each thread } t \\text{ running } e\\text{,} & \\\\[1ex]\n & & \\quad \\htmlData{k=sp.rel}{e \\in \\htmlData{k=th.Erel}{E[\\kappa_L]^W_\\alpha\\llbracket A|_t \\vdash U_t\\rrbracket^{\\varnothing}}} & \\text{the relation} \\\\\n & & \\quad \\htmlData{k=sp.fuel}{e \\in \\htmlData{k=sr.FE}{F^{N}_{\\alpha}\\llbracket \\Phi|_t \\vdash \\htmlData{k=fu.rty}{\\mathsf{thread}}\\ !\\ \\infty \\rrbracket}} & \\text{fuel} \\\\\n & & \\land\\ \\htmlData{k=sp.own}{\\mathsf{consistent}}(a, A, \\Phi) & \\\\[2ex]\nA,\\ \\Phi & & \\text{the held ends as } o \\mapsto S@x \\text{ for the relation and as } o \\mapsto S^{f}_{m} \\text{ for fuel} & \\\\\nA|_t,\\ \\Phi|_t & & \\text{their restrictions to the ends } K \\text{ gives } t & \\htmlData{k=sp.ty}{U_t \\in \\{T, \\ast\\}} \\\\[2ex]\n\\htmlData{k=sp.own}{\\mathsf{consistent}}(a, A, \\Phi) & \\iff & \\htmlData{k=sp.dom}{\\mathrm{dom}\\,A = \\mathrm{dom}\\,\\Phi = \\mathrm{dom}\\,K} \\land \\htmlData{k=sp.owner}{K(o) = (t, x, f, m) \\Rightarrow t \\in \\mathrm{dom}\\,q} & \\text{owners} \\\\\n & \\land & \\htmlData{k=sp.pts}{K(o) = (t, x, f, m) \\Rightarrow A(o) = \\_@x \\land \\Phi(o) = \\_^{f}_{m}} \\land \\htmlData{k=sp.fin}{f \\in \\mathbb{N}} \\land \\htmlData{k=sp.cap}{f \\leq m} & \\\\\n & \\land & \\htmlData{k=sp.closed}{o \\in \\mathrm{dom}\\,K \\Rightarrow \\htmlData{k=end.ech}{\\mathsf{ech}}\\,o \\in C \\lor o \\in \\mathrm{dom}\\,\\Sigma} \\land \\htmlData{k=sp.pair}{o \\in \\mathrm{dom}\\,K \\land \\htmlData{k=end.ech}{\\mathsf{ech}}\\,o \\in C \\Rightarrow \\overline{o} \\in \\mathrm{dom}\\,K} & \\text{closed} \\\\\n & \\land & \\htmlData{k=sp.sdual}{\\htmlData{k=end.ech}{\\mathsf{ech}}\\,o \\in C \\land A(o) = S@x \\land A(\\overline{o}) = S'@x' \\Rightarrow x' = \\overline{x} \\land \\htmlData{k=sty.sdual}{\\mathsf{sdual}}\\,S\\,S'} & \\text{dual} \\\\\n & \\land & \\htmlData{k=sp.pdual}{\\htmlData{k=end.ech}{\\mathsf{ech}}\\,o \\in C \\land \\Phi(o) = P^{f}_{m} \\land \\Phi(\\overline{o}) = P'^{f'}_{m'} \\Rightarrow P' \\mathrel{\\htmlData{k=sty.sequiv}{\\simeq}} \\overline{P}} & \\\\\n & \\land & \\htmlData{k=sp.tsum}{\\htmlData{k=end.ech}{\\mathsf{ech}}\\,o \\in C \\land K(o) = (\\_, \\_, \\_, m) \\land K(\\overline{o}) = (\\_, \\_, \\_, m') \\Rightarrow m + m' \\leq N} & \\text{tickets} \\\\\n & \\land & \\htmlData{k=sp.sig}{\\Sigma(o) = S@x \\Rightarrow A(o) = S@x} \\land \\htmlData{k=sp.psig}{\\Phi(o) = S^{f}_{m}} & \\text{interface}\n\\end{array}\\end{array}",
     "caption": "An annotated configuration $a = (q, K)$ is a configuration $q$ with an ownership map $K$. $K$ gives each held end the thread that holds it, its point, its counter and its tickets. The configuration is in the lock-free process relation at the ordinal index $\\alpha$ when each thread is in $E[\\kappa_L]$ at the ends it owns and has fuel at their counters. $A$ and $\\Phi$ describe the held ends for the relation and for fuel, and $\\mathsf{consistent}$ requires $A$, $\\Phi$ and $K$ to agree. It also bounds each counter by its tickets and the tickets of the two ends of an internal channel by $N$. Fuel occurs only in this definition.",
     "about": {
      "why": "The lock-free process relation combines the relation and the fuel of each thread over one ownership map. Lock-free adequacy reads the points and counters that $K$ records, and the invariant on tickets makes the measure fall at a link.",
      "used": [
       "sj-all",
       "th-adeq"
      ]
     }
    },
    {
     "id": "sj-all",
     "title": "Semantic judgments",
     "modes": [
      "df",
      "lf"
     ],
     "rocq": "compat/SemTyped.v: Grel, sem_typed_at, sf_den, sem_typed; relation/Adequacy.v: sem_ptyped; soup/Soup.v: lf_sem, lf_next, own_next, world_next; soup/State.v: tchoice",
     "tex": "\\begin{array}{c}\\begin{array}{l}\n\\htmlData{k=sj.at}{\\Delta \\mathrel{\\htmlData{k=sj.term}{\\vDash[\\kappa]}}^{X}_W e : T \\iff \\forall n, W' \\mathrel{\\htmlData{k=w.ext}{\\sqsupseteq}} W, \\Theta', \\gamma.\\ \\htmlData{k=sr.tenv-erase}{|\\Delta|} \\mathbin{\\#} \\Theta' \\land {}} \\\\\n\\quad \\htmlData{k=sj.at}{\\htmlData{k=sj.grel}{\\gamma \\in G[\\kappa]^{W'}_{\\alpha}\\llbracket\\Theta' \\vdash \\Delta\\rrbracket} \\Rightarrow \\gamma(e) \\in \\htmlData{k=th.Erel}{E[\\kappa]^{W'}_{\\alpha}\\llbracket |\\Delta| \\cup \\Theta' \\vdash T\\rrbracket^{X}}} \\\\\n\\htmlData{k=sj.term}{\\Delta \\vDash[\\kappa]^{F}_W e : T \\iff \\forall R, B.\\ \\Delta \\vDash[\\kappa]^{\\htmlData{k=sj.den}{\\mathsf{den}_{R,B}(F)}}_W e : T} \\\\\n\\htmlData{k=sj.proc}{\\Sigma \\vDash[\\kappa]_W p : T \\iff \\forall \\alpha.\\ p \\in \\htmlData{k=th.Prel}{P[\\kappa]^{W}_{\\alpha}\\llbracket\\Sigma \\vdash T\\rrbracket}}\n\\end{array}\\annraw{\\\\[3ex]}\\annot{\\begin{array}{l}\n\\htmlData{k=sp.lfsem}{\\Sigma \\Vvdash_W p : T \\iff \\htmlData{k=sp.exists-before-forall}{\\exists N \\in \\mathbb{N}.\\ \\forall \\alpha.\\ \\exists a.\\ \\htmlData{k=proc.erase}{\\mathsf{erase}}(\\htmlData{k=th.qa}{q_a}) = p} \\land a \\in \\htmlData{k=th.soup}{S^{N,W}_\\alpha\\llbracket\\Sigma \\vdash T\\rrbracket}}\n\\end{array}}\\end{array}",
     "caption": "The semantic judgments quantify over ordinal indices, larger worlds and substitutions, and read the static future at each of its denotations. \\annp{The lock-free judgment fixes the bound $N$ once and chooses the annotated configuration at each index. The creation choice of each channel is an existential inside O-New.}",
     "variants": {
      "df": "\\begin{array}{c}\\begin{array}{l}\n\\htmlData{k=sj.at}{\\Delta \\mathrel{\\htmlData{k=sj.term}{\\vDash}}^{X}_W e : T \\iff \\forall n, W' \\mathrel{\\htmlData{k=w.ext}{\\sqsupseteq}} W, \\Theta', \\gamma.\\ \\htmlData{k=sr.tenv-erase}{|\\Delta|} \\mathbin{\\#} \\Theta' \\land {}} \\\\\n\\quad \\htmlData{k=sj.at}{\\htmlData{k=sj.grel}{\\gamma \\in G^{W'}_{\\alpha}\\llbracket\\Theta' \\vdash \\Delta\\rrbracket} \\Rightarrow \\gamma(e) \\in \\htmlData{k=th.Erel}{E^{W'}_{\\alpha}\\llbracket |\\Delta| \\cup \\Theta' \\vdash T\\rrbracket^{X}}} \\\\\n\\htmlData{k=sj.term}{\\Delta \\vDash^{F}_W e : T \\iff \\forall R, B.\\ \\Delta \\vDash^{\\htmlData{k=sj.den}{\\mathsf{den}_{R,B}(F)}}_W e : T} \\\\\n\\htmlData{k=sj.proc}{\\Sigma \\vDash_W p : T \\iff \\forall \\alpha.\\ p \\in \\htmlData{k=th.Prel}{P^{W}_{\\alpha}\\llbracket\\Sigma \\vdash T\\rrbracket}}\n\\end{array}\\end{array}"
     },
     "about": {
      "why": "The fundamental theorems conclude the semantic judgments, and adequacy takes a semantic judgment as its premise.",
      "used": [
       "th-terms",
       "th-fund-proc",
       "th-adeq"
      ]
     }
    }
   ]
  },
  {
   "id": "theorems",
   "title": "Theorems",
   "intro": "Typed closed processes are deadlock free, and the proof goes through the logical relation. The section opens with the chain of results and then states each of them for processes. The lemmas about terms come last. \\annp{The lock-free results sit next to their deadlock-free counterparts.}",
   "blocks": [
    {
     "id": "th-chain",
     "title": "How the results fit together",
     "rocq": "static/FundamentalProc.v: fundamental_proc, soundness; relation/Adequacy.v: adequacy; static/Fundamental.v: live_fundamental; cost/CostFund.v: fsem_of_cost; soup/LFTyped.v: lf_fundamental; soup/LFAdequacy.v: lf_adequacy",
     "modes": [
      "df",
      "lf"
     ],
     "tex": "\\begin{array}{rcl}\n\\Sigma \\htmlData{k=tp.pjudg}{\\vdash\\annot{^{\\infty}}_W} p : T & \\overset{\\htmlData{k=th.fundamental-proc}{\\textsf{fundamental\\_proc}}}{\\Longrightarrow} & \\Sigma \\htmlData{k=sj.proc}{\\vDash}_W p : T \\\\[1ex]\n\\varnothing \\htmlData{k=sj.proc}{\\vDash}_W p : T & \\overset{\\htmlData{k=th.adequacy}{\\textsf{adequacy}}}{\\Longrightarrow} & \\htmlData{k=prop.df}{\\mathsf{deadlock\\_free}}\\,p\n\\annraw{\\\\[3ex]}\\annot{\\varnothing ; \\Delta \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{\\varnothing}_{W\\annot{,N}} t : T\\ !\\ c \\land \\htmlData{k=guard.judg}{\\varnothing \\vdash\\!\\triangleright t}}\\annraw{&}\\annot{\\overset{\\htmlData{k=th.live-fundamental}{\\textsf{live\\_fundamental}}}{\\Longrightarrow}}\\annraw{&}\\annot{\\Delta \\htmlData{k=sj.term}{\\mathrel{\\htmlData{k=sj.proc}{\\mathrel{|\\!\\!\\vDash}}}}^{\\varnothing}_W t : T}\n\\annraw{\\\\[1ex]}\\annot{\\varnothing ; \\Delta \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{\\varnothing}_{W\\annot{,N}} t : T\\ !\\ c \\land \\htmlData{k=ty.tfree}{\\mathsf{tfree}}\\,T \\land \\htmlData{k=th.crle}{\\mathsf{cr}(\\Delta) \\leq N}}\\annraw{&}\\annot{\\overset{\\htmlData{k=th.fsem-of-cost}{\\textsf{fsem\\_of\\_cost}}}{\\Longrightarrow}}\\annraw{&}\\annot{\\htmlData{k=fu.fsem}{\\mathsf{fsem}\\,N\\,\\htmlData{k=th.styof}{\\Delta\\annot{^{N}}}\\,t}}\n\\annraw{\\\\[1ex]}\\annot{\\Sigma \\htmlData{k=tp.lfjudg}{\\Vdash^{N}_W} p : T}\\annraw{&}\\annot{\\overset{\\htmlData{k=th.lf-fundamental}{\\textsf{lf\\_fundamental}}}{\\Longrightarrow}}\\annraw{&}\\annot{\\Sigma \\htmlData{k=sp.lfsem}{\\Vvdash}_W p : T}\n\\annraw{\\\\[1ex]}\\annot{\\htmlData{k=th.em}{\\mathsf{EM}} \\land \\htmlData{k=th.ac}{\\mathsf{AC}} \\land \\varnothing \\htmlData{k=sp.lfsem}{\\Vvdash}_W p : T}\\annraw{&}\\annot{\\overset{\\htmlData{k=th.lf-adequacy}{\\textsf{lf\\_adequacy}}}{\\Longrightarrow}}\\annraw{&}\\annot{\\htmlData{k=prop.lf}{\\mathsf{lock\\_free}}\\,p}\n\\end{array}",
     "caption": "Typing implies the semantic judgment, and the semantic judgment implies deadlock freedom. Both steps use the relation $(V, E, P)$ at the step costs $\\kappa_{DF}$. \\annp{Lock freedom uses the same relation at $\\kappa_L$, which excludes internal divergence, together with fuel. The lock-free process relation combines both for each thread. Lock-free adequacy measures a wait on $o$ by $\\mu(t) = (\\varrho(\\mathsf{pt}\\,o), f)$, the ordinal rank of the point of $o$ and the counter $f$ of the dual end $\\overline{o}$. A step of the thread holding $\\overline{o}$ on another end decreases $f$, which F-Count keeps at $1$ or more. \\annp{A link gives the waiting thread a partner with a lower counter, by the premise of E-Link and the invariant on tickets.} Lock-free adequacy takes excluded middle and choice as hypotheses. The thread holding $\\overline{o}$ therefore acts on $\\overline{o}$ after finitely many steps.}",
     "about": {
      "why": "Each arrow is one theorem of this section. \\annp{The lock-free rows show what lock freedom adds to the deadlock-free proof.}",
      "used": []
     }
    },
    {
     "id": "th-sound",
     "title": "Soundness",
     "rocq": "static/FundamentalProc.v: soundness; soup/LFTyped.v: lf_soundness, lf_soundness_run, lf_soundness_padovani; lockfree/FairRun.v: fair_run_exists, lock_free_padovani",
     "modes": [
      "df",
      "lf"
     ],
     "tex": "\\begin{array}{l}\\htmlData{k=th.soundness}{\\begin{array}{l}\\varnothing \\htmlData{k=tp.pjudg}{\\vdash\\annot{^{\\infty}}_W} p : T \\\\ \\quad\\Longrightarrow\\ \\htmlData{k=prop.df}{\\mathsf{deadlock\\_free}}\\,p\\end{array}}\\annraw{ \\\\[1.5ex] }\\annot{\\htmlData{k=th.lf-soundness}{\\begin{array}{l}\\htmlData{k=th.em}{\\mathsf{EM}} \\land \\htmlData{k=th.ac}{\\mathsf{AC}} \\land \\varnothing \\htmlData{k=tp.lfjudg}{\\Vdash^{N}_W} p : T \\\\ \\quad\\Longrightarrow\\ \\htmlData{k=prop.lf}{\\mathsf{lock\\_free}}\\,p\\end{array}}} \\\\[1.5ex] \\htmlData{k=th.fair-run-exists}{\\begin{array}{l}\\mathsf{EM} \\land \\mathsf{DC} \\\\ \\quad\\Longrightarrow\\ \\exists (r, l).\\ \\htmlData{k=proc.erase}{\\mathsf{erase}}\\,(r\\,0) = p \\land \\htmlData{k=prop.maximal}{\\mathsf{maximal}}\\,(r, l) \\land \\htmlData{k=prop.wfair}{\\mathsf{wfair}}\\,(r, l)\\end{array}}\\annraw{ \\\\[1.5ex] }\\annot{\\htmlData{k=th.lf-padovani}{\\begin{array}{l}\\begin{array}{l}\\mathsf{EM} \\land \\mathsf{DC} \\land \\htmlData{k=prop.lf}{\\mathsf{lock\\_free}}\\,p \\land \\htmlData{k=proc.erase}{\\mathsf{erase}}\\,q_0 = p \\\\ \\land\\ q_0 \\to^{*} q \\land \\htmlData{k=prop.pend}{\\mathsf{pend}(q, t)}\\end{array} \\\\ \\quad\\Longrightarrow\\ \\exists q_1\\,ev\\,q_2.\\ q \\to^{*} q_1 \\xrightarrow{ev} q_2 \\land t \\in \\htmlData{k=se.parts}{\\mathsf{parts}(ev)}\\end{array}}}\\end{array}",
     "caption": "A closed typed process is deadlock free. \\annp{Under excluded middle and choice, a closed process typed at a finite bound $N$, with each thread guarded, is lock free.}",
     "about": {
      "why": "These are the main results."
     }
    },
    {
     "id": "th-compose",
     "title": "Semantic composition rules",
     "rocq": "compat/PTerm.v: sem_p_term; compat/ConnectP.v: sem_p_connect; soup/LFCompose.v: lf_p_term, lf_p_connect",
     "modes": [
      "df",
      "lf"
     ],
     "tex": "\\begin{array}{l}\\htmlData{k=th.sem-p-term}{\\begin{array}{l}\\begin{array}{l}\\htmlData{k=ty.tfree}{\\mathsf{tfree}}\\,T \\land \\htmlData{k=th.sth}{\\mathsf{sth}\\,\\Theta\\,\\Sigma\\,\\Theta_B\\,C} \\\\ \\land\\ t \\in \\htmlData{k=th.Erel}{E\\annot{[\\kappa]}^{W}_{\\alpha}\\llbracket \\Theta \\vdash T\\rrbracket^{\\varnothing}}\\end{array} \\\\ \\quad\\Longrightarrow\\ (C, \\{t\\}) \\in \\htmlData{k=th.Prel}{P\\annot{[\\kappa]}^{W}_{\\alpha}\\llbracket \\Sigma \\vdash T\\rrbracket}\\end{array}} \\\\[1.5ex] \\htmlData{k=th.sem-p-connect}{\\begin{array}{l}\\begin{array}{l}\\htmlData{k=ty.tfree}{\\mathsf{tfree}}\\,T \\land \\htmlData{k=th.conn}{\\mathsf{conn}} \\\\ \\land\\ p_1 \\in \\htmlData{k=th.Prel}{P^{W}_{\\alpha}\\llbracket \\Sigma_1 \\cup \\Sigma_C \\vdash T\\rrbracket} \\\\ \\land\\ p_2 \\in \\htmlData{k=th.Prel}{P^{W}_{\\alpha}\\llbracket \\Sigma_2 \\cup \\Sigma_D \\vdash \\ast\\rrbracket}\\end{array} \\\\ \\quad\\Longrightarrow\\ \\htmlData{k=th.par}{p_1 \\parallel_{\\Sigma_C} p_2} \\in \\htmlData{k=th.Prel}{P^{W}_{\\alpha}\\llbracket \\Sigma_1 \\cup \\Sigma_2 \\vdash T\\rrbracket}\\end{array}}\\annraw{ \\\\[1.5ex] }\\annot{\\htmlData{k=th.lf-p-term}{\\begin{array}{l}\\Sigma \\mathrel{\\htmlData{k=tp.lfjudg}{\\Vdash}}^{N}_{W} (C_0, \\{t\\}) : T \\\\ \\quad\\Longrightarrow\\ \\Sigma \\mathrel{\\htmlData{k=sp.lfsem}{\\Vvdash}}_W (C_0, \\{t\\}) : T\\end{array}}}\\end{array}",
     "caption": "A safe thread is a safe process, and two safe processes connected at dual interfaces form a safe process. A component proved safe without typing therefore composes with typed components. \\annp{The same holds for the lock-free process relation.}",
     "about": {
      "why": "P-Term and P-Connect hold in the relation, which makes the approach compositional.",
      "used": [
       "th-fund-proc"
      ]
     }
    },
    {
     "id": "th-fund-proc",
     "title": "Fundamental theorem",
     "rocq": "static/FundamentalProc.v: fundamental_proc, live_fundamental_proc; soup/LFTyped.v: lf_fundamental",
     "modes": [
      "df",
      "lf"
     ],
     "tex": "\\begin{array}{l}\\htmlData{k=th.fundamental-proc}{\\begin{array}{l}\\Sigma \\htmlData{k=tp.pjudg}{\\vdash\\annot{^{\\infty}}_W} p : T \\\\ \\quad\\Longrightarrow\\ \\Sigma \\htmlData{k=sj.proc}{\\vDash}_W p : T\\end{array}}\\annraw{ \\\\[1.5ex] }\\annot{\\htmlData{k=th.lf-fundamental}{\\begin{array}{l}\\Sigma \\htmlData{k=tp.lfjudg}{\\Vdash^{N}_W} p : T \\\\ \\quad\\Longrightarrow\\ \\Sigma \\htmlData{k=sp.lfsem}{\\Vvdash}_W p : T\\end{array}}}\\end{array}",
     "caption": "A typed process is in the semantic judgment. The proof is by induction over P-Term and P-Connect and uses the composition rules.",
     "about": {
      "why": "The fundamental theorem connects typing with the relation.",
      "used": [
       "th-sound"
      ]
     }
    },
    {
     "id": "th-adeq",
     "title": "Adequacy",
     "modes": [
      "df",
      "lf"
     ],
     "rocq": "relation/Adequacy.v: adequacy, live_adequacy, adequacy_gen; soup/LFAdequacy.v: lf_adequacy, lf_thread_progress; soup/SoupTau.v: soup_no_tau_divergence; soup/SoupRun.v: lfsoup_step",
     "tex": "\\begin{array}{c}\\begin{array}{l}\\htmlData{k=th.adequacy}{\\begin{array}{l}\\varnothing \\htmlData{k=sj.proc}{\\vDash}_W p : T \\\\ \\quad\\Longrightarrow\\ \\htmlData{k=prop.df}{\\mathsf{deadlock\\_free}}\\,p\\end{array}}\\end{array}\\annraw{\\\\[3ex]}\\annot{\\begin{array}{l}\\annot{\\htmlData{k=th.lf-adequacy}{\\begin{array}{l}\\htmlData{k=th.em}{\\mathsf{EM}} \\land \\htmlData{k=th.ac}{\\mathsf{AC}} \\land \\varnothing \\htmlData{k=sp.lfsem}{\\Vvdash}_W p : T \\\\ \\quad\\Longrightarrow\\ \\htmlData{k=prop.lf}{\\mathsf{lock\\_free}}\\,p\\end{array}}}\\annraw{ \\\\[1.5ex] }\\annot{\\htmlData{k=th.lf-thread-progress}{\\begin{array}{l}\\htmlData{k=th.em}{\\mathsf{EM}} \\land \\htmlData{k=th.ac}{\\mathsf{AC}} \\land \\varnothing \\mathrel{\\htmlData{k=sp.lfsem}{\\Vvdash}}_W p : T \\\\ \\quad\\Longrightarrow\\ \\begin{array}{l}\\forall (r, l).\\ \\htmlData{k=proc.erase}{\\mathsf{erase}}\\,(\\htmlData{k=se.run}{r\\,0}) = p \\land \\htmlData{k=prop.maximal}{\\mathsf{maximal}}\\,(r, l) \\land \\htmlData{k=prop.wfair}{\\mathsf{wfair}}\\,(r, l) \\\\ \\quad \\Longrightarrow\\ \\htmlData{k=th.tpr}{\\mathsf{thread\\_progress\\_run}}\\,(r, l)\\end{array}\\end{array}}}\\end{array}}\\end{array}",
     "caption": "A closed process in the semantic judgment is deadlock free. \\annp{Under excluded middle and choice, a closed process in the lock-free judgment is lock free, and each thread progresses on each weakly fair maximal run.}",
     "about": {
      "why": "Adequacy connects the relation with the safety property.",
      "used": [
       "th-sound"
      ]
     }
    },
    {
     "id": "th-conserv",
     "title": "Conservativity",
     "rocq": "static/Conservativity.v: conservative, typed_dftyped, dftyped_typed",
     "modes": [
      "lf"
     ],
     "tex": "\\begin{array}{l}\\annot{\\htmlData{k=th.conservative}{\\begin{array}{l}(\\exists \\varepsilon.\\ \\Gamma;\\htmlData{k=th.df}{\\Delta_{df}} \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F}_{W\\annot{,\\infty}} e : T_{df}\\ !\\ \\varepsilon) \\\\ \\quad\\iff\\ \\Gamma ; \\Delta_{df} \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F}_{W} e : T_{df}\\end{array}}}\\annraw{ \\\\[1.5ex] }\\annot{\\htmlData{k=th.typed-dftyped}{\\begin{array}{l}\\Gamma ; \\Delta \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F}_{W\\annot{,N}} e : T\\ !\\ \\varepsilon \\\\ \\quad\\Longrightarrow\\ \\Gamma ; \\Delta_{df} \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F}_W e : T_{df}\\end{array}}}\\end{array}",
     "caption": "The annotated judgment at $N = \\infty$ types the same terms as deadlock-free typing, and erasing the annotations of a lock-free typing gives a deadlock-free typing.",
     "about": {
      "why": "Lock-free typing therefore rejects no deadlock-free program."
     }
    },
    {
     "id": "th-terms",
     "title": "Lemmas about terms",
     "modes": [
      "df",
      "lf"
     ],
     "rocq": "static/FundamentalProc.v: soundness_source; soup/LFCompose.v: lf_soundness_source; static/Fundamental.v: typed_sem, fundamental, fundamental_typed, live_fundamental, live_fundamental_typed; compat/Bind.v: Erel_bind; cost/CostFund.v: cost_fundamental, fsem_of_cost",
     "tex": "\\begin{array}{c}\\begin{array}{l}\\htmlData{k=th.soundness-source}{\\begin{array}{l}\\htmlData{k=ty.tfree}{\\mathsf{tfree}}\\,T \\land \\varnothing ; \\varnothing \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{\\varnothing}_W t : T \\\\ \\quad\\Longrightarrow\\ \\htmlData{k=prop.df}{\\mathsf{deadlock\\_free}}(\\varnothing, \\{t\\})\\end{array}}\\annraw{ \\\\[1.5ex] }\\annot{\\htmlData{k=th.lf-soundness-source}{\\begin{array}{l}\\begin{array}{l}\\htmlData{k=th.em}{\\mathsf{EM}} \\land \\htmlData{k=th.ac}{\\mathsf{AC}} \\land N \\in \\mathbb{N} \\land \\htmlData{k=ty.tfree}{\\mathsf{tfree}}\\,T \\\\ \\land\\ \\varnothing ; \\varnothing \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{\\varnothing}_{W\\annot{,N}} t : T\\ !\\ c \\land \\htmlData{k=guard.judg}{\\varnothing \\vdash\\!\\triangleright t}\\end{array} \\\\ \\quad\\Longrightarrow\\ \\htmlData{k=prop.lf}{\\mathsf{lock\\_free}}(\\varnothing, \\{t\\})\\end{array}}}\\end{array}\\\\[3ex]\\begin{array}{l}\\htmlData{k=th.fundamental}{\\begin{array}{l}\\varnothing ; \\Delta \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F}_{W} t : T \\\\ \\quad\\Longrightarrow\\ \\Delta \\htmlData{k=sj.term}{\\mathrel{\\htmlData{k=sj.proc}{\\vDash}}}^{F}_W t : T\\end{array}}\\annraw{ \\\\[1.5ex] }\\annot{\\htmlData{k=th.fundamental-typed}{\\begin{array}{l}\\varnothing ; \\Delta \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F}_{W\\annot{,N}} t : T\\ !\\ \\varepsilon \\\\ \\quad\\Longrightarrow\\ \\htmlData{k=th.df}{\\Delta_{df}} \\mathrel{\\htmlData{k=sj.term}{\\vDash}}^{F}_W t : T_{df}\\end{array}}}\\annraw{ \\\\[1.5ex] }\\annot{\\htmlData{k=th.live-fundamental}{\\begin{array}{l}\\varnothing ; \\Delta \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F}_{W} t : T \\land \\htmlData{k=guard.judg}{\\varnothing \\vdash\\!\\triangleright t} \\\\ \\quad\\Longrightarrow\\ \\Delta \\htmlData{k=sj.term}{\\mathrel{\\htmlData{k=sj.proc}{\\mathrel{|\\!\\!\\vDash}}}}^{F}_W t : T\\end{array}}}\\annraw{ \\\\[1.5ex] }\\annot{\\htmlData{k=th.live-fundamental-typed}{\\begin{array}{l}\\begin{array}{l}\\varnothing ; \\Delta \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F}_{W\\annot{,N}} t : T\\ !\\ \\varepsilon \\\\ \\land\\ \\varnothing \\mathrel{\\htmlData{k=guard.judg}{\\vdash\\!\\triangleright}} t\\end{array} \\\\ \\quad\\Longrightarrow\\ \\Delta_{df} \\mathrel{\\htmlData{k=sj.term}{\\mathrel{|\\!\\!\\vDash}}}^{F}_W t : T_{df}\\end{array}}}\\end{array}\\\\[3ex]\\htmlData{k=th.Erel-bind}{\\begin{array}{l}\\begin{array}{l}e \\in \\htmlData{k=th.Erel}{E^{W}_{\\alpha}\\llbracket \\Theta_1 \\vdash T\\rrbracket^{F \\cup \\htmlData{k=ty.heads}{\\mathsf{ap}}\\,\\Theta_2}} \\\\ \\land\\ \\forall W' \\htmlData{k=w.ext}{\\sqsupseteq} W,\\ \\beta \\leq \\alpha,\\ v \\in \\htmlData{k=th.Vrel}{V^{W'}_{\\beta}\\llbracket\\Theta_v \\vdash T\\rrbracket}. \\\\ \\qquad \\htmlData{k=se.frame}{f[v]} \\in \\htmlData{k=th.Erel}{E^{W'}_{j}\\llbracket \\Theta_v \\cup \\Theta_2 \\vdash U\\rrbracket^{F}}\\end{array} \\\\ \\quad\\Longrightarrow\\ \\htmlData{k=se.frame}{f[e]} \\in \\htmlData{k=th.Erel}{E^{W}_{\\alpha}\\llbracket \\Theta_1 \\cup \\Theta_2 \\vdash U\\rrbracket^{F}}\\end{array}}\\annraw{\\\\[3ex]}\\annot{\\begin{array}{l}\\htmlData{k=th.cost-fundamental}{\\begin{array}{l}\\Gamma ; \\Delta \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{F}_{W\\annot{,N}} e : T\\ !\\ \\varepsilon \\\\ \\quad\\Longrightarrow\\ \\htmlData{k=cs.csem}{\\Delta \\mathrel{\\htmlData{k=sj.term}{\\vDash}}^{N} e : T\\ !\\ \\varepsilon}\\end{array}} \\\\[1.5ex] \\htmlData{k=th.fsem-of-cost}{\\begin{array}{l}\\varnothing ; \\Delta \\mathrel{\\htmlData{k=tp.vdash}{\\vdash}}^{\\varnothing}_{W\\annot{,N}} e : T\\ !\\ c \\land \\htmlData{k=ty.tfree}{\\mathsf{tfree}}\\,T \\land \\htmlData{k=th.crle}{\\mathsf{cr}(\\Delta) \\leq N} \\\\ \\quad\\Longrightarrow\\ \\htmlData{k=fu.fsem}{\\mathsf{fsem}\\,N\\,\\htmlData{k=th.styof}{\\Delta\\annot{^{N}}}\\,e}\\end{array}}\\end{array}}\\end{array}",
     "caption": "A closed program is sound as a one-thread process. Typing a term implies the semantic term judgment, and $E$ is closed under evaluation frames. \\annp{With the guard a typed term is in the relation at $\\kappa_L$, and a typed term at a finite bound $N$ has fuel.}",
     "about": {
      "why": "The proofs of the process results use these lemmas, each proved rule by rule.",
      "used": [
       "th-fund-proc",
       "th-adeq"
      ]
     }
    }
   ]
  }
 ],
 "notes": {
  "syn.var": {
   "title": "Variable",
   "what": "A de Bruijn index $x \\in \\mathbb{N}$, the number of binders between the occurrence and its binder.",
   "why": "A plain term former. With de Bruijn indices, substitution $e[v]$ and renaming need no side condition on fresh names.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\lambda x.\\,x$ is the identity, where $x$ is the index $0$.",
   "rocq": "lang/Syntax.v: Var",
   "sig": "x \\in \\mathsf{Expr}",
   "args": [
    {
     "name": "x",
     "meaning": "A de Bruijn index $x \\in \\mathbb{N}$, the number of binders between the occurrence and its binder."
    }
   ]
  },
  "syn.unit": {
   "title": "Unit value $\\ast$",
   "what": "The unit value $\\ast$, with $V\\llbracket\\Theta \\vdash \\ast\\rrbracket$ only at $\\Theta = \\varnothing$.",
   "why": "A plain term former. $\\mathsf{close}$, $\\mathsf{link}$ and $\\mathsf{spawn}$ return $\\ast$, and a terminated process has $\\ast$ in every thread except the main thread.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{close}\\,o \\xrightarrow{o\\,\\mathsf{end}} \\ast$.",
   "rocq": "lang/Syntax.v: EUnit",
   "sig": "\\ast \\in \\mathsf{Val}",
   "args": []
  },
  "syn.end": {
   "title": "End value $o$",
   "what": "The value $o$ names one end of a channel, the only channel name in terms.",
   "why": "Each end has its own name $c^{+}$ or $c^{-}$, and $\\mathsf{select}_i\\,o$ and $\\mathsf{branch}\\,o$ return the same name $o$. Hence no step of the semantics reads a point.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{new} \\xrightarrow{\\mathsf{new}\\,c} \\langle c^{+}, c^{-}\\rangle$ returns the two end values of $c$.",
   "rocq": "lang/Syntax.v: Chan",
   "sig": "o \\in \\mathsf{Val}",
   "args": [
    {
     "name": "o",
     "meaning": "An end $o \\in \\mathsf{End}$, one of $c^{+}, c^{-}$ for a channel $c$."
    }
   ]
  },
  "syn.lam": {
   "title": "$\\lambda$-abstraction",
   "what": "A one-argument closure $\\lambda e$, a value for every $e$ because no frame has its hole under $\\lambda$.",
   "why": "A plain term former and the value form of every user function.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\lambda x.\\,\\mathsf{send}\\,x$ is $\\mathsf{send}$ as a function value.",
   "rocq": "lang/Syntax.v: Lam",
   "sig": "\\lambda e \\in \\mathsf{Val}",
   "args": [
    {
     "name": "e",
     "meaning": "The body, $e \\in \\mathsf{Expr}$, with the argument as index $0$."
    }
   ]
  },
  "syn.app": {
   "title": "Application",
   "what": "Application, left to right, with $(\\lambda e)\\,v \\xrightarrow{\\beta} e[v]$.",
   "why": "A plain term former. It is the only way to run a closure, received or built.",
   "breaks": "Nothing. It is a definition.",
   "example": "$(\\lambda x.\\,\\mathsf{close}\\,x)\\,c^{+} \\xrightarrow{\\beta} \\mathsf{close}\\,c^{+}$.",
   "rocq": "lang/Syntax.v: App, lang/Semantics.v: t_act_app",
   "sig": "e_1\\,e_2 \\in \\mathsf{Expr}",
   "args": [
    {
     "name": "e_1",
     "meaning": "The function, evaluated first."
    },
    {
     "name": "e_2",
     "meaning": "The argument, evaluated once $e_1$ is a value."
    }
   ]
  },
  "syn.pair": {
   "title": "Pair",
   "what": "A pair $\\langle e_1, e_2\\rangle$, evaluated left to right, a value iff both components are values.",
   "why": "A plain term former. $\\mathsf{send}$ takes a pair $\\langle v, o\\rangle$ and $\\mathsf{recv}$ returns one.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{send}\\,\\langle \\ast, o\\rangle$.",
   "rocq": "lang/Syntax.v: Pair",
   "sig": "\\langle e_1, e_2\\rangle \\in \\mathsf{Expr}",
   "args": [
    {
     "name": "e_1, e_2",
     "meaning": "Subterms, $e_1, e_2 \\in \\mathsf{Expr}$."
    }
   ]
  },
  "syn.letu": {
   "title": "Unit elimination",
   "what": "$\\mathsf{let}\\ \\ast = e_1\\ \\mathsf{in}\\ e_2$ evaluates $e_1$ to $\\ast$ and then steps to $e_2$ by $\\beta$.",
   "why": "A plain term former. It sequences $e_1$ before $e_2$ when $e_1$ returns $\\ast$, and the derived $\\mathsf{let}$ uses it to discard its unit component.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{let}\\ \\ast = \\mathsf{close}\\,c^{+}\\ \\mathsf{in}\\ \\mathsf{close}\\,d^{+}$ closes $c^{+}$ and then $d^{+}$.",
   "rocq": "lang/Syntax.v: LetU",
   "sig": "\\mathsf{let}\\ \\ast = e_1\\ \\mathsf{in}\\ e_2 \\in \\mathsf{Expr}",
   "args": [
    {
     "name": "e_1",
     "meaning": "A term of type $\\ast$, evaluated first."
    },
    {
     "name": "e_2",
     "meaning": "The continuation, run after $e_1$ returns $\\ast$."
    }
   ]
  },
  "syn.letp": {
   "title": "Pair elimination",
   "what": "$\\mathsf{let}\\ \\langle a, b\\rangle = e_1\\ \\mathsf{in}\\ e_2$ evaluates $e_1$ to $\\langle v_1, v_2\\rangle$ and steps to $e_2[v_1, v_2]$ by $\\beta$.",
   "why": "A plain term former and the only eliminator of $\\otimes$. A $\\mathsf{recv}$ returns $\\langle v, o\\rangle$, and the continuation reads $v$ and $o$ through the pair elimination.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{let}\\ \\langle v, c\\rangle = \\mathsf{recv}\\,c\\ \\mathsf{in}\\ e$.",
   "rocq": "lang/Syntax.v: LetP",
   "sig": "\\mathsf{let}\\ \\langle a, b\\rangle = e_1\\ \\mathsf{in}\\ e_2 \\in \\mathsf{Expr}",
   "args": [
    {
     "name": "e_1",
     "meaning": "A term that returns a pair $\\langle v_1, v_2\\rangle$."
    },
    {
     "name": "a, b",
     "meaning": "The bound variables, $a$ at index $1$ for $v_1$ and $b$ at index $0$ for $v_2$."
    },
    {
     "name": "e_2",
     "meaning": "The body, in scope of $a$ and $b$."
    }
   ]
  },
  "syn.let": {
   "title": "Derived let",
   "what": "$\\mathsf{let}\\ a = e_1\\ \\mathsf{in}\\ e_2 := \\mathsf{let}\\ \\langle a, u\\rangle = \\langle e_1, \\ast\\rangle\\ \\mathsf{in}\\ \\mathsf{let}\\ \\ast = u\\ \\mathsf{in}\\ e_2$ with $u$ fresh.",
   "why": "The abbreviation binds one variable without a $\\lambda$, so its body keeps every end of the context and the typing needs no lower point $l$ for these ends. It uses only $\\otimes$ and $\\ast$, which every system already has.",
   "breaks": "Written as $(\\lambda a.\\,e_2)\\,e_1$ instead, the $\\lambda$ must bound the dual points of all ends it captures by one lower point $l$. After $\\mathsf{let}\\ \\langle a, a'\\rangle = \\mathsf{new}_\\ell$ the ends $a, a'$ are at $\\rho$ and $\\overline{\\rho}$, which have no common lower bound, and the body does not type.",
   "example": "$\\mathsf{let}\\ p = \\mathsf{force}\\,mk\\,\\ast\\ \\mathsf{in}\\ e$ keeps every end of the context in $e$.",
   "rocq": "lang/Syntax.v: ELet, lang/Semantics.v: t_act_let_unit, t_act_let_pair",
   "sig": "\\mathsf{let}\\ a = e_1\\ \\mathsf{in}\\ e_2 \\in \\mathsf{Expr}",
   "args": [
    {
     "name": "a",
     "meaning": "The bound variable, standing for the value of $e_1$."
    },
    {
     "name": "u",
     "meaning": "A variable not free in $e_2$, bound to the unit component."
    },
    {
     "name": "e_1, e_2",
     "meaning": "Subterms, $e_1, e_2 \\in \\mathsf{Expr}$."
    }
   ]
  },
  "syn.inj": {
   "title": "Injection",
   "what": "$\\mathsf{inj}_i\\,e$ for $i \\in \\{1, 2\\}$, a value when $e$ is a value.",
   "why": "A plain term former. $\\mathsf{branch}\\,o$ returns $\\mathsf{inj}_i\\,o$, and $i$ records which choice arrived.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{branch}\\,o \\xrightarrow{o \\rhd \\mathsf{true}} \\mathsf{inj}_2\\,o$.",
   "rocq": "lang/Syntax.v: Inj",
   "sig": "\\mathsf{inj}_i\\,e \\in \\mathsf{Expr}",
   "args": [
    {
     "name": "i",
     "meaning": "The side, $i \\in \\{1, 2\\}$."
    },
    {
     "name": "e",
     "meaning": "The injected term."
    }
   ]
  },
  "syn.case": {
   "title": "Case",
   "what": "$\\mathsf{case}\\ e\\,(a.e_1)\\,(a.e_2)$ evaluates $e$ to $\\mathsf{inj}_i\\,v$ and steps to $e_i[v]$ by $\\beta$.",
   "why": "A plain term former and the only eliminator of $\\oplus$. It consumes the result of $\\mathsf{branch}$.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{case}\\ (\\mathsf{branch}\\,o)\\,(a.\\,\\mathsf{close}\\,a)\\,(a.\\,\\mathsf{close}\\,a)$.",
   "rocq": "lang/Syntax.v: Case",
   "sig": "\\mathsf{case}\\ e\\,(a.e_1)\\,(a.e_2) \\in \\mathsf{Expr}",
   "args": [
    {
     "name": "e",
     "meaning": "The scrutinee, a term that returns $\\mathsf{inj}_i\\,v$."
    },
    {
     "name": "a",
     "meaning": "The variable bound to $v$ in each branch, index $0$."
    },
    {
     "name": "e_1, e_2",
     "meaning": "The branches, $e_i$ runs when $e$ returns $\\mathsf{inj}_i\\,v$."
    }
   ]
  },
  "syn.box": {
   "title": "Box $!e$",
   "what": "A recursive thunk value whose body binds the box at index $0$, $\\mathsf{force}\\,(!e) \\xrightarrow{\\beta} e[!e]$.",
   "why": "One former gives recursion and replication. The value relation asks $\\Theta = \\varnothing$ and $\\mathsf{fends}(e) = \\varnothing$ of a box, so copying a box duplicates no end.",
   "breaks": "Nothing. It is a definition.",
   "example": "$!(f = \\lambda x.\\,\\mathsf{let}\\ \\langle v, x'\\rangle = \\mathsf{recv}\\,x\\ \\mathsf{in}\\ \\mathsf{force}\\,f\\,x')$ is a server loop.",
   "rocq": "lang/Syntax.v: EBox",
   "sig": "!e \\in \\mathsf{Val}",
   "args": [
    {
     "name": "e",
     "meaning": "The body, with the box itself as index $0$."
    }
   ]
  },
  "syn.new": {
   "title": "$\\mathsf{new}$",
   "what": "$\\mathsf{new} \\xrightarrow{\\mathsf{new}\\,c} \\langle c^{+}, c^{-}\\rangle$ for a fresh channel $c$. The typing places $c^{+}$ at a position $\\pi$, a fresh root or a field $x\\cdot\\kappa$, places $c^{-}$ at $\\overline{\\pi}$, and states a constraint $C$ on both.",
   "why": "The term names no point. Position and constraint are part of the existential type of $\\mathsf{new}$, which the typing derivation chooses. Each ordering of a new channel is therefore available without program syntax.",
   "breaks": "With the position or the facts in the term, every held end that the facts mention is an argument that $\\mathsf{new}$ takes and returns, because ends are linear.",
   "example": "$\\mathsf{let}\\ \\langle a, a'\\rangle = \\mathsf{new}\\ \\mathsf{in}\\ e$.",
   "rocq": "lang/Syntax.v: ENew",
   "sig": "\\mathsf{new} : \\exists^{\\bot}\\bar\\iota.\\ C.\\ (S@\\pi \\otimes \\overline{S}@\\overline{\\pi})",
   "args": [
    {
     "name": "\\pi",
     "meaning": "The position of $c^{+}$, a fresh root $\\rho$ bound by the existential or a field $x\\cdot\\kappa$."
    },
    {
     "name": "C",
     "meaning": "The facts of the creation, with $\\mathsf{wf\\_new}\\,\\rho\\,C$ at a fresh root and $\\Gamma \\vdash C$ at a field."
    },
    {
     "name": "S",
     "meaning": "The session type of $c^{+}$."
    }
   ]
  },
  "syn.op": {
   "title": "Constant $k$",
   "what": "A constant $k$ is a value, and $k\\,v$ takes the head step of $k$ on the value $v$.",
   "why": "The constants are the operations on channels, boxes and threads. Application $k\\,e$ evaluates $e$ first, as each application does.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{send}\\,\\langle \\ast, o\\rangle$ applies $\\mathsf{send}$ to a pair.",
   "rocq": "lang/Syntax.v: Op (the value $k$ is $\\lambda x.\\,k\\,x$)",
   "sig": "k \\in \\mathsf{Val}",
   "args": [
    {
     "name": "k",
     "meaning": "A constant, $k \\in \\mathsf{Const}$."
    }
   ]
  },
  "prim.send": {
   "title": "$\\mathsf{send}$",
   "what": "$\\mathsf{send}\\,\\langle v, o\\rangle \\xrightarrow{o!v} o$.",
   "why": "The label contains the payload $v$. The value relation is exact, $\\mathrm{dom}\\,\\Theta = \\mathsf{fends}(v)$ for $v$ in $V$ at $\\Theta$, so the ends that leave the thread are determined by $v$.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{close}\\,(\\mathsf{send}\\,\\langle \\ast, c^{+}\\rangle)$ sends $\\ast$ and then closes.",
   "rocq": "lang/Syntax.v: PSend, lang/Semantics.v: t_act_send",
   "sig": "\\mathsf{send} : T[x\\cdot i] \\otimes S_0@x \\multimap^{x} S@x^{+}",
   "args": [
    {
     "name": "x",
     "meaning": "The point of the end acted on, also the upper point of the call."
    },
    {
     "name": "S_0",
     "meaning": "The session type of the end before the action."
    },
    {
     "name": "T, m",
     "meaning": "The payload type and the number $m$ of point variables it binds, instantiated at the fields $x\\cdot i$."
    },
    {
     "name": "S",
     "meaning": "The continuation after the action."
    }
   ]
  },
  "prim.recv": {
   "title": "$\\mathsf{recv}$",
   "what": "$\\mathsf{recv}\\,o \\xrightarrow{o?v} \\langle v, o\\rangle$ for every value $v$.",
   "why": "A receive has a step for each value, so it can match the send of the partner whatever value is sent. The session type of $o$ restricts the $v$ the relation considers.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{let}\\ \\langle u, b\\rangle = \\mathsf{recv}\\,b\\ \\mathsf{in}\\ e$.",
   "rocq": "lang/Syntax.v: PRecv",
   "sig": "\\mathsf{recv} : S_0@x \\multimap^{x} T[x\\cdot i] \\otimes S@x^{+}",
   "args": [
    {
     "name": "x",
     "meaning": "The point of the end acted on, also the upper point of the call."
    },
    {
     "name": "S_0",
     "meaning": "The session type of the end before the action."
    },
    {
     "name": "T, m",
     "meaning": "The payload type and the number $m$ of point variables it binds, instantiated at the fields $x\\cdot i$."
    },
    {
     "name": "S",
     "meaning": "The continuation after the action."
    }
   ]
  },
  "prim.close": {
   "title": "$\\mathsf{close}$",
   "what": "$\\mathsf{close}\\,o \\xrightarrow{o\\,\\mathsf{end}} \\ast$. The process step pairs it with $\\mathsf{close}\\,\\overline{o}$ and removes $\\mathsf{ech}\\,o$ from $C$.",
   "why": "A plain constant. A session type ends in $\\mathsf{Close}$, and after both closes no thread holds an end of the channel.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{close}\\,c^{+}$ in one thread and $\\mathsf{close}\\,c^{-}$ in another.",
   "rocq": "lang/Syntax.v: PClose",
   "sig": "\\mathsf{close} : S_0@x \\multimap^{x} \\ast",
   "args": [
    {
     "name": "x",
     "meaning": "The point of the end acted on, also the upper point of the call."
    },
    {
     "name": "S_0",
     "meaning": "The session type of the end before the action."
    }
   ]
  },
  "prim.select": {
   "title": "$\\mathsf{select}_i$",
   "what": "$\\mathsf{select}_i\\,o \\xrightarrow{o \\lhd i} o$ for $i \\in \\{\\mathsf{false}, \\mathsf{true}\\}$, where $\\mathsf{false}$ selects the first branch.",
   "why": "The end continues at $\\overline{x\\cdot\\kappa_i}$, a point that depends on $i$. Hence the two branches are ordered independently.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{select}_{\\mathsf{true}}\\,o$.",
   "rocq": "lang/Syntax.v: PSel",
   "sig": "\\mathsf{select}_i : S_0@x \\multimap^{x} S_i@\\overline{x\\cdot\\kappa_i}",
   "args": [
    {
     "name": "i",
     "meaning": "The chosen branch, $i \\in \\{\\mathsf{false}, \\mathsf{true}\\}$."
    },
    {
     "name": "x",
     "meaning": "The point of the end acted on, also the upper point of the call."
    },
    {
     "name": "S_0, S_i",
     "meaning": "The session type before the action and the chosen continuation."
    }
   ]
  },
  "prim.branch": {
   "title": "$\\mathsf{branch}$",
   "what": "$\\mathsf{branch}\\,o \\xrightarrow{o \\rhd i} \\mathsf{inj}_i\\,o$ for both $i$.",
   "why": "A plain constant, the partner of $\\mathsf{select}_i$. The injection $\\mathsf{inj}_i$ passes the chosen $i$ to the program.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{case}\\ (\\mathsf{branch}\\,o)\\,(a.\\,e_1)\\,(a.\\,e_2)$.",
   "rocq": "lang/Syntax.v: PBra",
   "sig": "\\mathsf{branch} : S_0@x \\multimap^{x} S_1@x\\cdot\\kappa_1 \\oplus S_2@x\\cdot\\kappa_2",
   "args": [
    {
     "name": "x",
     "meaning": "The point of the end acted on, also the upper point of the call."
    },
    {
     "name": "S_0, S_1, S_2",
     "meaning": "The session type before the action and the two continuations."
    }
   ]
  },
  "prim.link": {
   "title": "$\\mathsf{link}$",
   "what": "$\\mathsf{link}\\,\\langle o_1, o_2\\rangle \\xrightarrow{\\leftrightarrow\\{o_1, o_2\\}} \\ast$. The process step removes $\\mathsf{ech}\\,o_1$ and renames every thread by $\\mathsf{csub}\\,o_1\\,o_2$.",
   "why": "A link forwards a conversation without relaying messages. It acts on no protocol, so it costs $0$ in both cost tables, and in the fuel layer it lowers no counter.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{link}\\,\\langle c^{+}, d^{-}\\rangle$.",
   "rocq": "lang/Syntax.v: PLink",
   "sig": "\\mathsf{link} : S@x \\otimes \\overline{S}@\\overline{x} \\multimap \\ast",
   "args": [
    {
     "name": "S@x",
     "meaning": "The first linked end."
    },
    {
     "name": "\\overline{S}@\\overline{x}",
     "meaning": "The second, at the dual type and the dual point."
    }
   ]
  },
  "prim.spawn": {
   "title": "$\\mathsf{spawn}$",
   "what": "$\\mathsf{spawn}\\,v \\xrightarrow{\\mathsf{spawn}\\,v} \\ast$, and the process starts a thread running $v\\,\\ast$.",
   "why": "The label contains the thunk $v$. The value relation is exact, so the child holds exactly the ends $\\mathsf{fends}(v)$ and the parent keeps the rest.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{spawn}\\,(\\lambda u.\\,\\mathsf{let}\\ \\ast = u\\ \\mathsf{in}\\ \\mathsf{close}\\,d')$ transfers $d'$ to the child.",
   "rocq": "lang/Syntax.v: PSpawn",
   "sig": "\\mathsf{spawn} : (\\ast \\multimap^{u}_{l} \\ast) \\multimap \\ast",
   "args": [
    {
     "name": "u, l",
     "meaning": "The upper and lower point of the thunk, arbitrary."
    }
   ]
  },
  "prim.force": {
   "title": "$\\mathsf{force}$",
   "what": "$\\mathsf{force}\\,(!e) \\xrightarrow{\\beta} e[!e]$.",
   "why": "A plain constant. It is the only use of a box, and a loop calls itself by $\\mathsf{force}$ of its own self variable.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{force}\\,f\\,\\langle a, b\\rangle$ runs the loop $f$ again.",
   "rocq": "lang/Syntax.v: PForce",
   "sig": "\\mathsf{force} : \\Box(\\forall\\bar\\iota\\,\\bar\\alpha.\\ C.\\ \\ast\\multimap^{u} U) \\multimap^{u[\\bar x]} U[\\bar s][\\bar x]",
   "args": [
    {
     "name": "\\bar\\iota, \\bar\\alpha",
     "meaning": "The point and session variables of the box."
    },
    {
     "name": "\\bar x, \\bar s",
     "meaning": "Their instances, with $\\Gamma \\vdash C[\\bar x]$."
    },
    {
     "name": "u",
     "meaning": "The upper point of the body, instantiated as the upper point of the call."
    },
    {
     "name": "U",
     "meaning": "The result type of the body."
    }
   ]
  },
  "syn.values": {
   "title": "Values",
   "what": "$v ::= \\ast \\mid o \\mid k \\mid \\lambda e \\mid\\ !e \\mid \\langle v_1, v_2\\rangle \\mid \\mathsf{inj}_i\\,v$.",
   "why": "The results of evaluation. A thread that is a value has finished.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\langle \\ast, c^{+}\\rangle$ and $\\mathsf{send}$ are values.",
   "rocq": "lang/Syntax.v: is_val",
   "sig": "v \\in \\mathsf{Val} \\subseteq \\mathsf{Expr}",
   "args": [
    {
     "name": "v_1, v_2",
     "meaning": "Values."
    },
    {
     "name": "e",
     "meaning": "An arbitrary body."
    },
    {
     "name": "i",
     "meaning": "The side of an injection."
    }
   ]
  },
  "end.cend": {
   "title": "End",
   "what": "An end $o \\in \\{c^{+}, c^{-}\\}$ of a channel $c$, with one entry per end in every environment.",
   "why": "The two ends have independent names, and $\\mathsf{select}$ and $\\mathsf{branch}$ return the name they received. Hence an environment entry is determined by the end alone.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{new}$ returns $\\langle c^{+}, c^{-}\\rangle$.",
   "rocq": "lang/Syntax.v: cend",
   "sig": "o \\in \\mathsf{End} = \\{c^{+}, c^{-} \\mid c \\in \\mathsf{Chan}\\}",
   "args": [
    {
     "name": "c",
     "meaning": "A channel name."
    }
   ]
  },
  "end.dual": {
   "title": "Dual end $\\overline{o}$",
   "what": "$\\overline{c^{+}} = c^{-}$ and $\\overline{c^{-}} = c^{+}$, so $\\overline{\\overline{o}} = o$.",
   "why": "A message on $o$ synchronizes with an action on $\\overline{o}$. Every two-thread process step pairs an end with its partner.",
   "breaks": "Nothing. It is a definition.",
   "example": "A send on $c^{+}$ meets a receive on $c^{-}$.",
   "rocq": "lang/Syntax.v: edual",
   "sig": "\\overline{\\cdot} : \\mathsf{End} \\to \\mathsf{End}",
   "args": [
    {
     "name": "o",
     "meaning": "An end, $\\overline{o}$ is the other end of $\\mathsf{ech}\\,o$."
    }
   ]
  },
  "end.ech": {
   "title": "Channel of an end",
   "what": "$\\mathsf{ech}(c^{+}) = \\mathsf{ech}(c^{-}) = c$.",
   "why": "Restricted sets $C$ and the subjects of an offer are sets of channels, so the rules map ends to channels by $\\mathsf{ech}$.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{ech}(c^{-}) = c$.",
   "rocq": "lang/Syntax.v: ech",
   "sig": "\\mathsf{ech} : \\mathsf{End} \\to \\mathsf{Chan}",
   "args": [
    {
     "name": "o",
     "meaning": "An end, $\\mathsf{ech}\\,o$ is its channel."
    }
   ]
  },
  "syn.fends": {
   "title": "$\\mathsf{fends}$",
   "what": "$\\mathsf{fends}(e)$ is the finite set of ends that occur in $e$.",
   "why": "The value relation asks $\\mathrm{dom}\\,\\Theta = \\mathsf{fends}(\\lambda e)$ of a closure and $\\mathsf{fends}(e) = \\varnothing$ of a box. Hence for $v$ in $V$ at $\\Theta$ the ends a send or spawn of $v$ moves are $\\mathrm{dom}\\,\\Theta = \\mathsf{fends}(v)$, and ownership follows the syntax of values.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{fends}(\\lambda u.\\,\\mathsf{close}\\,a) = \\{a\\}$.",
   "rocq": "lang/Syntax.v: fends",
   "sig": "\\mathsf{fends} : \\mathsf{Expr} \\to \\mathcal{P}_{\\mathrm{fin}}(\\mathsf{End})",
   "args": [
    {
     "name": "e",
     "meaning": "A term, $\\mathsf{fends}(e)$ is the set of ends occurring in $e$."
    }
   ]
  },
  "syn.fchans": {
   "title": "$\\mathsf{fchans}$",
   "what": "$\\mathsf{fchans}(e) = \\{\\mathsf{ech}\\,o \\mid o \\in \\mathsf{fends}(e)\\}$.",
   "why": "A created channel $c$ must satisfy $c \\notin \\mathsf{fchans}(e)$ for every thread $e$, or two channels share a name.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{fchans}(\\langle c^{+}, d^{-}\\rangle) = \\{c, d\\}$.",
   "rocq": "lang/Syntax.v: fchans",
   "sig": "\\mathsf{fchans} : \\mathsf{Expr} \\to \\mathcal{P}_{\\mathrm{fin}}(\\mathsf{Chan})",
   "args": [
    {
     "name": "e",
     "meaning": "A term, $\\mathsf{fchans}(e) = \\mathsf{ech}[\\mathsf{fends}(e)]$."
    }
   ]
  },
  "proc.proc": {
   "title": "Process $(C, E)$",
   "what": "A process is a pair of a finite set $C$ of restricted channels and a finite multiset $E$ of threads.",
   "why": "A channel $c \\in C$ has both ends inside the process. An end $o$ with $\\mathsf{ech}\\,o \\notin C$ belongs to the interface with the environment.",
   "breaks": "Nothing. It is a definition.",
   "example": "$(\\{c\\}, \\{\\!|\\,\\mathsf{close}\\,c^{+}, \\mathsf{close}\\,c^{-}\\,|\\!\\})$.",
   "rocq": "lang/Syntax.v: proc",
   "sig": "p = (C, E) \\in \\mathsf{Proc} = \\mathcal{P}_{\\mathrm{fin}}(\\mathsf{Chan}) \\times \\mathcal{M}_{\\mathrm{fin}}(\\mathsf{Expr})",
   "args": [
    {
     "name": "C",
     "meaning": "The restricted channels."
    },
    {
     "name": "E",
     "meaning": "The threads, a finite multiset of terms."
    }
   ]
  },
  "proc.config": {
   "title": "Configuration",
   "what": "A configuration $q = (C, M)$ has a finite partial map $M : \\mathbb{N} \\rightharpoonup e$ from thread identifiers to terms.",
   "why": "Weak fairness and lock freedom speak about one thread $t$ across a run, so threads have identifiers.",
   "breaks": "Nothing. It is a definition.",
   "example": "$(\\varnothing, \\{0 \\mapsto main\\})$.",
   "rocq": "lang/Process.v: config",
   "sig": "q = (C, M) \\in \\mathsf{Config} = \\mathcal{P}_{\\mathrm{fin}}(\\mathsf{Chan}) \\times (\\mathbb{N} \\rightharpoonup_{\\mathrm{fin}} \\mathsf{Expr})",
   "args": [
    {
     "name": "C",
     "meaning": "The restricted channels."
    },
    {
     "name": "M",
     "meaning": "The thread map, $M(i)$ the term of thread $i \\in \\mathrm{dom}\\,M$."
    }
   ]
  },
  "proc.erase": {
   "title": "$\\mathsf{erase}$",
   "what": "$\\mathsf{erase}(C, M) = (C, \\{\\!|\\, M(i) \\mid i \\in \\mathrm{dom}\\,M \\,|\\!\\})$ forgets the identifiers.",
   "why": "Steps are defined once, on configurations. A process $p$ steps to $p'$ when some $q$ with $\\mathsf{erase}(q) = p$ steps to some $q'$ with $\\mathsf{erase}(q') = p'$.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{erase}(C, \\{0 \\mapsto e, 1 \\mapsto f\\}) = (C, \\{\\!|\\,e, f\\,|\\!\\})$.",
   "rocq": "lang/Process.v: erase",
   "sig": "\\mathsf{erase} : \\mathsf{Config} \\to \\mathsf{Proc}",
   "args": [
    {
     "name": "(C, M)",
     "meaning": "A configuration, $\\mathsf{erase}(C, M)$ keeps $C$ and the multiset of the terms $M(i)$."
    },
    {
     "name": "i",
     "meaning": "Ranges over $\\mathrm{dom}\\,M$."
    }
   ]
  },
  "pt.const": {
   "title": "Root $a$",
   "what": "A root $a \\in A$ of the world $W$, either shared with the environment or added to $W$ by the creation of a channel.",
   "why": "Every point of a held end has a root in $A$. The facts $\\prec_A$ mention only such points.",
   "breaks": "Nothing. It is a definition.",
   "example": "Roots $1, 2$ with the fact $1 \\prec \\overline{2}$.",
   "rocq": "types/Points.v: NConst",
   "sig": "a \\in \\mathsf{Root}",
   "args": [
    {
     "name": "a",
     "meaning": "A root, $a \\in A$ for the world $W$ in use."
    }
   ]
  },
  "pt.var": {
   "title": "Point variable $\\iota$",
   "what": "A de Bruijn point variable, bound by $\\Box\\forall\\bar\\iota$, by a payload $!(\\bar\\iota.\\,T)$ or by the existential of $\\mathsf{new}$, and absent from terms.",
   "why": "No term mentions a point. Types quantify over points instead.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\Box\\forall \\iota\\,\\kappa\\,\\zeta.\\ C.\\ \\ast \\multimap U$ binds three point variables.",
   "rocq": "types/Points.v: NVar",
   "sig": "\\iota \\in \\mathsf{Root}",
   "args": [
    {
     "name": "\\iota",
     "meaning": "A de Bruijn index over points, bound by $\\Box\\forall\\bar\\iota$, by a payload $!(\\bar\\iota.\\,T)$ or by the existential of $\\mathsf{new}$."
    }
   ]
  },
  "pt.shift": {
   "title": "Shift $x^{+}$",
   "what": "$x^{+}$ raises the offset of $x$ by $1$, so an action on an end at $x$ moves it to $x^{+}$.",
   "why": "For every $W$ and $x$, $x \\prec_W x^{+}$. Hence the actions of one end are ordered in program order.",
   "breaks": "Nothing. It is a definition.",
   "example": "After $\\mathsf{send}$ at $x$ the end is at $x^{+}$.",
   "rocq": "types/Points.v: pt_shift",
   "sig": "(\\cdot)^{+} : \\mathsf{Point} \\to \\mathsf{Point}",
   "args": [
    {
     "name": "x",
     "meaning": "A point, $x^{+}$ has the offset of $x$ plus $1$."
    }
   ]
  },
  "pt.field": {
   "title": "Field $x\\cdot\\kappa$",
   "what": "$x\\cdot\\kappa$ is a name below $x$ with offset $0$ and positive polarity, where payloads, branch continuations and channels created at a field are.",
   "why": "The $j$-th payload end of a message at $x$ is at $x\\cdot j$, and the continuation of choice $i$ at $x\\cdot\\kappa_i$. $\\mathsf{new}$ may place a channel at the same fields, so a channel created to be sent is at the field where the message delivers its payload.",
   "breaks": "With a separate sort of point for created channels, a reply channel created to be sent is away from the payload field, and request and reply programs do not type.",
   "example": "$\\mathsf{new}$ at the position $\\rho\\cdot 0$ places $d^{+}$ at $\\rho\\cdot 0$ and $d^{-}$ at $\\overline{\\rho\\cdot 0}$.",
   "rocq": "types/Points.v: pt_field",
   "sig": "(\\cdot)\\cdot\\kappa : \\mathsf{Point} \\times \\mathbb{N} \\to \\mathsf{Point}",
   "args": [
    {
     "name": "x",
     "meaning": "The parent point."
    },
    {
     "name": "\\kappa",
     "meaning": "The field label, $\\kappa \\in \\mathbb{N}$."
    }
   ]
  },
  "pt.dual": {
   "title": "Dual point $\\overline{x}$",
   "what": "$\\overline{x}$ flips the polarity of $x$, and the two ends of a channel are at $x$ and $\\overline{x}$.",
   "why": "A thread blocked at $u$ that holds an end at $v$ must satisfy $u \\prec \\overline{v}$, the point of the dual end.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{new}$ places $c^{+}$ at $\\rho$ and $c^{-}$ at $\\overline{\\rho}$.",
   "rocq": "types/Points.v: pt_dual",
   "sig": "\\overline{\\cdot} : \\mathsf{Point} \\to \\mathsf{Point}",
   "args": [
    {
     "name": "x",
     "meaning": "A point, $\\overline{x}$ has the opposite polarity."
    }
   ]
  },
  "pt.laws": {
   "title": "Point laws",
   "what": "For every $x$ and $\\kappa$, $\\overline{\\overline{x}} = x$, $\\overline{x}\\cdot\\kappa = x\\cdot\\kappa$ and $\\overline{x^{+}} = \\overline{x}^{+}$.",
   "why": "$\\overline{x}\\cdot\\kappa = x\\cdot\\kappa$ makes the payload points $x\\cdot j$ of sender and receiver equal, although the two ends are at $x$ and $\\overline{x}$.",
   "breaks": "If $\\overline{x}\\cdot\\kappa \\neq x\\cdot\\kappa$, the ends of a message are at different points for sender and receiver, and the received value is not in the value relation at its type.",
   "example": "$\\overline{\\rho}\\cdot 0 = \\rho\\cdot 0$.",
   "rocq": "types/Points.v: pt_dual_dual, pt_field_dual",
   "sig": "\\forall x \\in \\mathsf{Point}, \\kappa \\in \\mathbb{N}.\\ \\overline{\\overline{x}} = x \\land \\overline{x}\\cdot\\kappa = x\\cdot\\kappa \\land \\overline{x^{+}} = \\overline{x}^{+}",
   "args": [
    {
     "name": "x",
     "meaning": "An arbitrary point."
    },
    {
     "name": "\\kappa",
     "meaning": "An arbitrary field label."
    }
   ]
  },
  "sx.kappai": {
   "title": "Field of a choice $\\kappa_i$",
   "what": "$\\kappa_{\\mathsf{false}} = 0$ and $\\kappa_{\\mathsf{true}} = 1$.",
   "why": "The two continuations of a choice are at distinct fields $x\\cdot 0 \\neq x\\cdot 1$, so facts order them independently.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{branch}$ at $\\overline{x}$ continues at $x\\cdot 0$ or $x\\cdot 1$.",
   "rocq": "types/Points.v: bfield",
   "sig": "\\kappa_{(\\cdot)} : \\mathbb{B} \\to \\mathbb{N}",
   "args": [
    {
     "name": "i",
     "meaning": "A choice, $i \\in \\{\\mathsf{false}, \\mathsf{true}\\}$."
    }
   ]
  },
  "pt.sel": {
   "title": "Select continuation",
   "what": "$\\mathsf{sel\\_pt}\\,x\\,i = \\overline{x\\cdot\\kappa_i}$, the point of the end after $\\mathsf{select}_i$ at $x$.",
   "why": "Selecting end and branching end continue at the two sides $\\overline{x\\cdot\\kappa_i}$ and $x\\cdot\\kappa_i$ of one field.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{select}_{\\mathsf{false}}\\,o$ at $x$ continues at $\\overline{x\\cdot 0}$.",
   "rocq": "types/Points.v: sel_pt",
   "sig": "\\mathsf{sel\\_pt} : \\mathsf{Point} \\to \\mathbb{B} \\to \\mathsf{Point}",
   "args": [
    {
     "name": "x",
     "meaning": "The point of the selecting end before the step."
    },
    {
     "name": "i",
     "meaning": "The selected branch."
    }
   ]
  },
  "pt.bra": {
   "title": "Branch continuation",
   "what": "$\\mathsf{bra\\_pt}\\,x\\,i = x\\cdot\\kappa_i$, the point of the end after $\\mathsf{branch}$ at $\\overline{x}$ receives $i$.",
   "why": "It is $\\overline{\\mathsf{sel\\_pt}\\,x\\,i}$, the dual point of the selecting side.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{branch}$ at $\\overline{x}$ continues at $x\\cdot\\kappa_i$.",
   "rocq": "types/Points.v: bra_pt",
   "sig": "\\mathsf{bra\\_pt} : \\mathsf{Point} \\to \\mathbb{B} \\to \\mathsf{Point}",
   "args": [
    {
     "name": "x",
     "meaning": "The point of the selecting partner, the branching end is at $\\overline{x}$."
    },
    {
     "name": "i",
     "meaning": "The received choice."
    }
   ]
  },
  "pt.payload": {
   "title": "Payload fields",
   "what": "The $j$-th end of a message sent at $x$ is at $x\\cdot j$.",
   "why": "$\\overline{x}\\cdot j = x\\cdot j$, so sender at $x$ and receiver at $\\overline{x}$ compute the same points for the delivered ends.",
   "breaks": "Nothing. It is a definition.",
   "example": "A message on $y$ at $Y$ delivers its end at $Y\\cdot 0$.",
   "rocq": "types/Points.v: payload_pts",
   "sig": "\\mathsf{payload\\_pts} : \\mathsf{Point} \\to \\mathbb{N} \\to \\mathsf{Point}^{*}",
   "args": [
    {
     "name": "x",
     "meaning": "The point of the carrier end at the send."
    },
    {
     "name": "m",
     "meaning": "The number of point variables the payload binds."
    }
   ]
  },
  "lbl.field": {
   "title": "Field label $\\kappa$",
   "what": "$\\kappa \\in \\mathbb{N}$ selects the field $x\\cdot\\kappa$ of a point $x$.",
   "why": "Payloads, choices and the position of a new channel use fields. $x\\cdot\\kappa = x\\cdot\\kappa'$ iff $\\kappa = \\kappa'$.",
   "breaks": "Two channels created at one field $x\\cdot\\kappa$ are at the same points $x\\cdot\\kappa$ and $\\overline{x\\cdot\\kappa}$, so no fact orders one before the other.",
   "example": "$\\mathsf{bra\\_pt}\\,x\\,\\mathsf{true} = x\\cdot 1$.",
   "rocq": "lang/Syntax.v: field",
   "sig": "\\kappa \\in \\mathbb{N}",
   "args": [
    {
     "name": "\\kappa",
     "meaning": "A field label."
    }
   ]
  },
  "link.csub": {
   "title": "$\\mathsf{csub}$",
   "what": "$\\mathsf{csub}\\,o_1\\,o_2 = \\{\\overline{o_1} \\mapsto o_2,\\ o_1 \\mapsto \\overline{o_2}\\}$, the identity elsewhere, applied to every thread after a link.",
   "why": "After the link, the thread holding $\\overline{o_1}$ communicates with the thread holding $\\overline{o_2}$, so it holds $o_2$. The map identifies $\\overline{o_1}$ with $o_2$, so it is no bijection.",
   "breaks": "Nothing. It is a definition.",
   "example": "After $\\mathsf{link}\\,\\langle c^{+}, d^{-}\\rangle$ the thread holding $c^{-}$ holds $d^{-}$.",
   "rocq": "lang/Syntax.v: csub",
   "sig": "\\mathsf{csub} : \\mathsf{End} \\to \\mathsf{End} \\to \\mathsf{End} \\to \\mathsf{End}",
   "args": [
    {
     "name": "o_1, o_2",
     "meaning": "The linked ends, the channel of $o_1$ disappears."
    },
    {
     "name": "o",
     "meaning": "The end being renamed."
    }
   ]
  },
  "se.slabel": {
   "title": "Session label $\\sigma$",
   "what": "A label $\\sigma$ of a step that acts on an end and synchronizes with a partner thread or with the environment.",
   "why": "Session labels are exactly the steps a thread can wait on. Readiness and the obligations of the relation are stated over session labels.",
   "breaks": "Nothing. It is a definition.",
   "example": "$o?v$ and $o\\,\\mathsf{end}$ are session labels, $\\beta$ is none.",
   "rocq": "lang/Semantics.v: slabel",
   "sig": "\\sigma \\in \\mathsf{SLabel} \\subseteq \\mathsf{TLabel}",
   "args": [
    {
     "name": "o",
     "meaning": "The end the offer acts on, $o \\in \\mathsf{End}$."
    },
    {
     "name": "v",
     "meaning": "The value sent or received, where present."
    },
    {
     "name": "i",
     "meaning": "A choice, $i \\in \\{\\mathsf{false}, \\mathsf{true}\\}$."
    }
   ]
  },
  "se.subst": {
   "title": "Substitution $e[v]$",
   "what": "$e[v]$ is $e$ with the value $v$ for the variable of index $0$, and the other indices lowered by one.",
   "why": "A plain definition. Application, the two lets, case and force step by substitution.",
   "breaks": "Nothing. It is a definition.",
   "example": "$(\\mathsf{close}\\,x)[c^{+}] = \\mathsf{close}\\,c^{+}$.",
   "rocq": "lang/Syntax.v: subst1",
   "sig": "\\cdot[\\cdot] : \\mathsf{Expr} \\to \\mathsf{Val} \\to \\mathsf{Expr}",
   "args": [
    {
     "name": "e",
     "meaning": "The body, with a free index $0$."
    },
    {
     "name": "v",
     "meaning": "The value substituted for index $0$."
    }
   ]
  },
  "se.frame": {
   "title": "Frame filling $f[e]$",
   "what": "An evaluation frame $f$ is a term with one hole in evaluation position, and $f[e]$ fills the hole with $e$.",
   "why": "A plain definition. The frames fix where the next step of a term happens.",
   "breaks": "Nothing. It is a definition.",
   "example": "For $f = \\mathsf{let}\\ \\ast = \\square\\ \\mathsf{in}\\ e_2$, $f[\\mathsf{close}\\,c^{+}] = \\mathsf{let}\\ \\ast = \\mathsf{close}\\,c^{+}\\ \\mathsf{in}\\ e_2$.",
   "rocq": "lang/Semantics.v: frame, fill_frame",
   "sig": "\\cdot[\\cdot] : \\mathsf{Frame} \\to \\mathsf{Expr} \\to \\mathsf{Expr}",
   "args": [
    {
     "name": "f",
     "meaning": "An evaluation frame, a term with one hole $\\square$ in evaluation position."
    },
    {
     "name": "e",
     "meaning": "The term placed in the hole."
    }
   ]
  },
  "se.upd": {
   "title": "Map update $M[i \\mapsto e]$",
   "what": "$M[i \\mapsto e]$ maps $i$ to $e$ and every $j \\neq i$ to $M(j)$.",
   "why": "A plain definition.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\{0 \\mapsto e\\}[0 \\mapsto e'] = \\{0 \\mapsto e'\\}$.",
   "rocq": "lang/Process.v: istep",
   "sig": "\\cdot[\\cdot \\mapsto \\cdot] : (\\mathbb{N} \\rightharpoonup \\mathsf{Expr}) \\to \\mathbb{N} \\to \\mathsf{Expr} \\to (\\mathbb{N} \\rightharpoonup \\mathsf{Expr})",
   "args": [
    {
     "name": "M",
     "meaning": "The thread map."
    },
    {
     "name": "i",
     "meaning": "The updated identifier."
    },
    {
     "name": "e",
     "meaning": "The new term of thread $i$."
    }
   ]
  },
  "se.echans": {
   "title": "$\\mathsf{echans}(M)$",
   "what": "$\\mathsf{echans}(M) = \\bigcup_{i \\in \\mathrm{dom}\\,M} \\mathsf{fchans}(M(i))$, the channels some thread mentions.",
   "why": "A created channel $c$ satisfies $c \\notin \\mathsf{echans}(M)$, so it differs from every channel a thread mentions.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{echans}\\{0 \\mapsto \\mathsf{close}\\,c^{+}, 1 \\mapsto \\mathsf{close}\\,d^{-}\\} = \\{c, d\\}$.",
   "rocq": "lang/Syntax.v: echans",
   "sig": "\\mathsf{echans} : (\\mathbb{N} \\rightharpoonup \\mathsf{Expr}) \\to \\mathcal{P}_{\\mathrm{fin}}(\\mathsf{Chan})",
   "args": [
    {
     "name": "M",
     "meaning": "A thread map, $\\mathsf{echans}(M) = \\bigcup_{i \\in \\mathrm{dom}\\,M} \\mathsf{fchans}(M(i))$."
    }
   ]
  },
  "se.subj": {
   "title": "Subjects $\\mathsf{subj}\\,\\sigma$",
   "what": "$\\mathsf{subj}\\,\\sigma$ is the set of channels $\\sigma$ acts on, $\\{\\mathsf{ech}\\,o\\}$ for an action on $o$ and $\\{\\mathsf{ech}\\,o_1, \\mathsf{ech}\\,o_2\\}$ for a link.",
   "why": "An offer to the environment requires $\\mathsf{subj}\\,\\sigma \\cap C = \\varnothing$, so it uses only interface channels.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{subj}(o?v) = \\{\\mathsf{ech}\\,o\\}$.",
   "rocq": "lang/Semantics.v: subjs",
   "sig": "\\mathsf{subj} : \\mathsf{SLabel} \\to \\mathcal{P}_{\\mathrm{fin}}(\\mathsf{Chan})",
   "args": [
    {
     "name": "\\sigma",
     "meaning": "A session label."
    }
   ]
  },
  "se.parts": {
   "title": "Participants $\\mathsf{parts}(ev)$",
   "what": "$\\mathsf{parts}(\\mathsf{sync}_{i,j}\\,\\sigma) = \\{i, j\\}$, $\\mathsf{parts}(\\mathsf{solo}_i\\,\\alpha\\,k) = \\mathsf{parts}(\\mathsf{offer}_i\\,\\sigma) = \\{i\\}$, and $\\mathsf{parts}(\\bot) = \\varnothing$ for a stutter. A spawn names only the parent $i$.",
   "why": "A thread takes part in a step iff it is in $\\mathsf{parts}$ of its event. Weak fairness and lock freedom ask whether $t \\in \\mathsf{parts}(l_j)$ for some position $j$.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{parts}(\\mathsf{sync}_{0,1}\\,(a^{+}!\\ast)) = \\{0, 1\\}$.",
   "rocq": "lang/Process.v: ev_parts, lockfree/Fair.v: lparts",
   "sig": "\\mathsf{parts} : \\mathsf{Event} \\to \\mathcal{P}_{\\mathrm{fin}}(\\mathbb{N})",
   "args": [
    {
     "name": "ev",
     "meaning": "An event. $\\mathsf{parts}(ev)$ is the set of identifiers of the threads that take part in the step of $ev$."
    }
   ]
  },
  "se.reach": {
   "title": "Reachability $\\to^{*}$",
   "what": "$p \\to^{*} p'$ when $p$ reaches $p'$ in finitely many $\\tau$ steps.",
   "why": "A plain definition. Deadlock freedom and absence of internal divergence quantify over all $p'$ with $p \\to^{*} p'$.",
   "breaks": "Nothing. It is a definition.",
   "example": "$p \\to^{*} p$ for every $p$.",
   "rocq": "lang/Process.v: pred_star",
   "sig": "\\cdot \\to^{*} \\cdot \\subseteq \\mathsf{Proc} \\times \\mathsf{Proc}",
   "args": [
    {
     "name": "p, p'",
     "meaning": "Processes, $p \\to^{*} p'$ iff a finite sequence of $\\tau$ steps leads from $p$ to $p'$."
    }
   ]
  },
  "se.acc": {
   "title": "Accessibility $\\mathsf{Acc}$",
   "what": "$\\mathsf{Acc}\\,R\\,q$ holds when every $R$-chain $q = q_0\\,R\\,q_1\\,R \\cdots$ is finite, inductively, when $\\mathsf{Acc}\\,R\\,q'$ for every $q'$ with $q\\,R\\,q'$.",
   "why": "It states the absence of infinite $R$-chains from $q$ by induction, so proofs consume it by well-founded induction.",
   "breaks": "Nothing. It is a definition.",
   "example": "If every administrative chain from $q$ has length at most $2$, then $\\mathsf{Acc}\\ {\\to_{\\mathsf{admin}}}\\ q$.",
   "rocq": "Coq.Init.Wf: Acc",
   "sig": "\\mathsf{Acc} : (X \\to X \\to \\mathsf{Prop}) \\to X \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "R",
     "meaning": "A relation on $X$, instantiated with $\\to_{\\mathsf{admin}}$ on processes."
    },
    {
     "name": "q",
     "meaning": "The start element, instantiated with a process reachable from $p$."
    }
   ]
  },
  "se.r0": {
   "title": "The run starts at $p$",
   "what": "$r_0$ is the configuration at position $0$ of the run, and $\\mathsf{erase}(r_0) = p$ states that forgetting its thread names gives the process $p$.",
   "why": "Lock freedom is a property of a process, and runs are sequences of configurations, so the run must start at a configuration of $p$. Any naming of the threads of $p$ is allowed.",
   "breaks": "Nothing. It is a definition.",
   "example": "$r_0 = (\\{c\\}, \\{0 \\mapsto \\mathsf{close}\\,c^{+},\\ 1 \\mapsto \\mathsf{close}\\,c^{-}\\})$ for $p = (\\{c\\}, \\{\\!|\\mathsf{close}\\,c^{+}, \\mathsf{close}\\,c^{-}|\\!\\})$.",
   "rocq": "lockfree/Fair.v: lock_free",
   "sig": "\\mathsf{erase}(r_0) = p",
   "args": [
    {
     "name": "r_0",
     "meaning": "The first configuration of the run, $r$ applied to $0$."
    },
    {
     "name": "p",
     "meaning": "The process whose lock freedom is stated."
    }
   ]
  },
  "se.run": {
   "title": "Runs $r$ and $l$",
   "what": "A run is a pair of sequences, $r_i$ the configuration at position $i$ and $l_i$ the event of the step from $r_i$ to $r_{i+1}$, or none when $r_{i+1} = r_i$ stutters.",
   "why": "Lock freedom quantifies over infinite runs and speaks of positions $i \\leq j$ in a run.",
   "breaks": "Nothing. It is a definition.",
   "example": "$r_0 = (\\varnothing, \\{0 \\mapsto main\\})$.",
   "rocq": "lockfree/Fair.v: run_step",
   "sig": "(r, l) \\in \\mathsf{Run} = (\\mathbb{N} \\to \\mathsf{Config}) \\times (\\mathbb{N} \\to \\mathsf{Event}_{\\bot})",
   "args": [
    {
     "name": "r_i",
     "meaning": "The configuration at position $i$."
    },
    {
     "name": "l_i",
     "meaning": "The event of the step $r_i \\to r_{i+1}$, or $\\bot$ when $r_{i+1} = r_i$."
    }
   ]
  },
  "lbl.beta": {
   "title": "$\\beta$ label",
   "what": "The label of application, unit and pair elimination, case and force.",
   "why": "These steps have the same cost $\\kappa(\\beta)$ in each cost table, so one label covers these steps.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{force}\\,(!e) \\xrightarrow{\\beta} e[!e]$.",
   "rocq": "lang/Semantics.v: LBeta",
   "sig": "\\beta \\in \\mathsf{TLabel}",
   "args": []
  },
  "lbl.new": {
   "title": "Label $\\mathsf{new}\\,c$",
   "what": "It contains the name $c$ of the new channel.",
   "why": "The process rule reads $c$ to keep names fresh. Position and facts of $c$ are no part of the label, and the relation chooses position and facts.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{new} \\xrightarrow{\\mathsf{new}\\,c} \\langle c^{+}, c^{-}\\rangle$.",
   "rocq": "lang/Semantics.v: LNew",
   "sig": "\\mathsf{new}\\,c \\in \\mathsf{TLabel}",
   "args": [
    {
     "name": "c",
     "meaning": "The name of the new channel."
    }
   ]
  },
  "lbl.spawn": {
   "title": "Label $\\mathsf{spawn}\\,v$",
   "what": "It contains the thunk $v$ that starts the child thread $v\\,\\ast$.",
   "why": "The relation splits the environment of the parent as $\\Theta = \\Theta_c \\uplus \\Theta_r$ with $v$ in the thunk relation at $\\Theta_c$. Exactness of $V$ gives $\\mathrm{dom}\\,\\Theta_c = \\mathsf{fends}(v)$, so the split is determined by $v$.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{spawn}\\,(\\lambda u.\\,\\mathsf{close}\\,d')$ transfers $d'$ to the child.",
   "rocq": "lang/Semantics.v: LSpawn",
   "sig": "\\mathsf{spawn}\\,v \\in \\mathsf{TLabel}",
   "args": [
    {
     "name": "v",
     "meaning": "The thunk, the child thread is $v\\,\\ast$."
    }
   ]
  },
  "lbl.send": {
   "title": "Send label $o!v$",
   "what": "An offer to send the value $v$ on the end $o$.",
   "why": "The relation, the fuel layer and scope extrusion read the ends that leave as $\\mathsf{fends}(v)$. For $v$ in $V$ at $\\Theta_v$ this set is $\\mathrm{dom}\\,\\Theta_v$.",
   "breaks": "Nothing. It is a definition.",
   "example": "Sending the end $a$ on $o$ has the label $o!a$.",
   "rocq": "lang/Semantics.v: SSend",
   "sig": "o!v \\in \\mathsf{SLabel}",
   "args": [
    {
     "name": "o",
     "meaning": "The end the offer acts on, $o \\in \\mathsf{End}$."
    },
    {
     "name": "v",
     "meaning": "The payload."
    }
   ]
  },
  "lbl.recv": {
   "title": "Receive label $o?v$",
   "what": "An offer to receive $v$ on $o$, for every value $v$.",
   "why": "A receive must meet every send of a partner, so its labels range over all values.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{recv}\\,o \\xrightarrow{o?\\ast} \\langle \\ast, o\\rangle$.",
   "rocq": "lang/Semantics.v: SRecv",
   "sig": "o?v \\in \\mathsf{SLabel}",
   "args": [
    {
     "name": "o",
     "meaning": "The end the offer acts on, $o \\in \\mathsf{End}$."
    },
    {
     "name": "v",
     "meaning": "The received value, any value."
    }
   ]
  },
  "lbl.close": {
   "title": "Close label $o\\,\\mathsf{end}$",
   "what": "An offer to close $o$.",
   "why": "A plain label. Its obligation removes $o$ from the environment $\\Theta$, so after a close $o \\notin \\mathrm{dom}\\,\\Theta$.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{close}\\,c^{+} \\xrightarrow{c^{+}\\,\\mathsf{end}} \\ast$.",
   "rocq": "lang/Semantics.v: SClose",
   "sig": "o\\,\\mathsf{end} \\in \\mathsf{SLabel}",
   "args": [
    {
     "name": "o",
     "meaning": "The end the offer acts on, $o \\in \\mathsf{End}$."
    }
   ]
  },
  "lbl.sel": {
   "title": "Select label $o \\lhd i$",
   "what": "An offer to select branch $i$ on $o$.",
   "why": "A plain label. Its obligation moves $o$ from $x$ to $\\overline{x\\cdot\\kappa_i}$.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{select}_{\\mathsf{true}}\\,o \\xrightarrow{o \\lhd \\mathsf{true}} o$.",
   "rocq": "lang/Semantics.v: SSel",
   "sig": "o \\lhd i \\in \\mathsf{SLabel}",
   "args": [
    {
     "name": "o",
     "meaning": "The end the offer acts on, $o \\in \\mathsf{End}$."
    },
    {
     "name": "i",
     "meaning": "The selected branch."
    }
   ]
  },
  "lbl.bra": {
   "title": "Branch label $o \\rhd i$",
   "what": "An offer to receive the choice $i$ on $o$, for both $i$.",
   "why": "A plain label. $\\mathsf{branch}$ must meet either choice of the partner, so it has a step for each $i$, and the obligation moves $o$ to $x\\cdot\\kappa_i$.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{branch}\\,o$ has the labels $o \\rhd \\mathsf{false}$ and $o \\rhd \\mathsf{true}$.",
   "rocq": "lang/Semantics.v: SBra",
   "sig": "o \\rhd i \\in \\mathsf{SLabel}",
   "args": [
    {
     "name": "o",
     "meaning": "The end the offer acts on, $o \\in \\mathsf{End}$."
    },
    {
     "name": "i",
     "meaning": "The received choice."
    }
   ]
  },
  "lbl.link": {
   "title": "Link label $\\leftrightarrow\\{o_1, o_2\\}$",
   "what": "An unordered pair $\\{o_1, o_2\\}$ of ends, possibly with $o_1 = o_2$.",
   "why": "The label is a set, so one process rule removes the channel of either end.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\leftrightarrow\\{c^{+}, d^{-}\\}$.",
   "rocq": "lang/Semantics.v: SLink",
   "sig": "\\leftrightarrow\\{o_1, o_2\\} \\in \\mathsf{SLabel}",
   "args": [
    {
     "name": "o_1, o_2",
     "meaning": "The linked ends, an unordered pair."
    }
   ]
  },
  "T-Act-App": {
   "title": "T-Act-App",
   "what": "$(\\lambda e)\\,v \\xrightarrow{\\beta} e[v]$.",
   "why": "Call by value. The argument is a value before the body runs.",
   "breaks": "Nothing. It is a definition.",
   "example": "$(\\lambda x.\\,\\mathsf{close}\\,x)\\,c^{+} \\xrightarrow{\\beta} \\mathsf{close}\\,c^{+}$.",
   "rocq": "lang/Semantics.v: t_act_app",
   "sig": "\\cdot \\xrightarrow{\\cdot} \\cdot \\subseteq \\mathsf{Expr} \\times \\mathsf{TLabel} \\times \\mathsf{Expr}",
   "args": [
    {
     "name": "e",
     "meaning": "The body of the $\\lambda$."
    },
    {
     "name": "v",
     "meaning": "The argument, a value."
    }
   ]
  },
  "T-Act-Force": {
   "title": "T-Act-Force",
   "what": "$\\mathsf{force}\\,(!e) \\xrightarrow{\\beta} e[!e]$, so the body runs with the box for its self.",
   "why": "It is the only rule that unrolls a definition, so recursion and replication go through force steps.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{force}\\,!(f = \\mathsf{force}\\,f)$ steps to itself by $\\beta$ forever.",
   "rocq": "lang/Semantics.v: t_act_force",
   "sig": "\\cdot \\xrightarrow{\\cdot} \\cdot \\subseteq \\mathsf{Expr} \\times \\mathsf{TLabel} \\times \\mathsf{Expr}",
   "args": [
    {
     "name": "e",
     "meaning": "The body of the box, substituted with the box itself."
    }
   ]
  },
  "T-Act-New": {
   "title": "T-Act-New",
   "what": "$\\mathsf{new} \\xrightarrow{\\mathsf{new}\\,c} \\langle c^{+}, c^{-}\\rangle$ for every $c$, and the process rule picks $c$.",
   "why": "The step of a single thread cannot determine which channel names are in use. The process rule asks $c \\notin C \\cup \\mathsf{echans}(M)$.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{new} \\xrightarrow{\\mathsf{new}\\,c} \\langle c^{+}, c^{-}\\rangle$.",
   "rocq": "lang/Semantics.v: t_act_new",
   "sig": "\\cdot \\xrightarrow{\\cdot} \\cdot \\subseteq \\mathsf{Expr} \\times \\mathsf{TLabel} \\times \\mathsf{Expr}",
   "args": [
    {
     "name": "c",
     "meaning": "Any channel name, restricted by the process rule."
    }
   ]
  },
  "T-Act-Spawn": {
   "title": "T-Act-Spawn",
   "what": "$\\mathsf{spawn}\\,v \\xrightarrow{\\mathsf{spawn}\\,v} \\ast$.",
   "why": "The label contains $v$, so the process rule can start the thread $v\\,\\ast$.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{spawn}\\,(\\lambda u.\\,\\mathsf{close}\\,d') \\xrightarrow{\\mathsf{spawn}\\,(\\lambda u.\\,\\mathsf{close}\\,d')} \\ast$.",
   "rocq": "lang/Semantics.v: t_act_spawn",
   "sig": "\\cdot \\xrightarrow{\\cdot} \\cdot \\subseteq \\mathsf{Expr} \\times \\mathsf{TLabel} \\times \\mathsf{Expr}",
   "args": [
    {
     "name": "v",
     "meaning": "The thunk."
    }
   ]
  },
  "T-Act-Send": {
   "title": "T-Act-Send",
   "what": "$\\mathsf{send}\\,\\langle v, o\\rangle \\xrightarrow{o!v} o$.",
   "why": "The label contains the payload $v$, which the receiving thread obtains by the process rule.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{send}\\,\\langle \\ast, c^{+}\\rangle \\xrightarrow{c^{+}!\\ast} c^{+}$.",
   "rocq": "lang/Semantics.v: t_act_send",
   "sig": "\\cdot \\xrightarrow{\\cdot} \\cdot \\subseteq \\mathsf{Expr} \\times \\mathsf{TLabel} \\times \\mathsf{Expr}",
   "args": [
    {
     "name": "v",
     "meaning": "The payload."
    },
    {
     "name": "o",
     "meaning": "The end sent on, returned."
    }
   ]
  },
  "T-Act-Recv": {
   "title": "T-Act-Recv",
   "what": "$\\mathsf{recv}\\,o \\xrightarrow{o?v} \\langle v, o\\rangle$ for every value $v$.",
   "why": "The step of a single thread does not depend on what the partner sends, so it has a step for each $v$. The receive obligation quantifies only over $v$ in the value relation at the payload type.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{recv}\\,b \\xrightarrow{b?\\ast} \\langle \\ast, b\\rangle$.",
   "rocq": "lang/Semantics.v: t_act_recv",
   "sig": "\\cdot \\xrightarrow{\\cdot} \\cdot \\subseteq \\mathsf{Expr} \\times \\mathsf{TLabel} \\times \\mathsf{Expr}",
   "args": [
    {
     "name": "o",
     "meaning": "The end received on."
    },
    {
     "name": "v",
     "meaning": "Any value, one step for each."
    }
   ]
  },
  "T-Act-Close": {
   "title": "T-Act-Close",
   "what": "$\\mathsf{close}\\,o \\xrightarrow{o\\,\\mathsf{end}} \\ast$.",
   "why": "A plain rule. The process rule pairs it with $\\overline{o}\\,\\mathsf{end}$ in another thread.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{close}\\,c^{+} \\xrightarrow{c^{+}\\,\\mathsf{end}} \\ast$.",
   "rocq": "lang/Semantics.v: t_act_close",
   "sig": "\\cdot \\xrightarrow{\\cdot} \\cdot \\subseteq \\mathsf{Expr} \\times \\mathsf{TLabel} \\times \\mathsf{Expr}",
   "args": [
    {
     "name": "o",
     "meaning": "The closed end."
    }
   ]
  },
  "T-Act-Select": {
   "title": "T-Act-Select",
   "what": "$\\mathsf{select}_i\\,o \\xrightarrow{o \\lhd i} o$, returning the same end name.",
   "why": "The end keeps its name $o$, so no step reads a point.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{select}_{\\mathsf{true}}\\,o \\xrightarrow{o \\lhd \\mathsf{true}} o$.",
   "rocq": "lang/Semantics.v: t_act_select",
   "sig": "\\cdot \\xrightarrow{\\cdot} \\cdot \\subseteq \\mathsf{Expr} \\times \\mathsf{TLabel} \\times \\mathsf{Expr}",
   "args": [
    {
     "name": "i",
     "meaning": "The selected branch."
    },
    {
     "name": "o",
     "meaning": "The end, returned under the same name."
    }
   ]
  },
  "T-Act-Branch": {
   "title": "T-Act-Branch",
   "what": "$\\mathsf{branch}\\,o \\xrightarrow{o \\rhd i} \\mathsf{inj}_i\\,o$ for both $i$.",
   "why": "Either choice may arrive, so the thread has one step for each $i$.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{branch}\\,o \\xrightarrow{o \\rhd \\mathsf{true}} \\mathsf{inj}_2\\,o$.",
   "rocq": "lang/Semantics.v: t_act_branch",
   "sig": "\\cdot \\xrightarrow{\\cdot} \\cdot \\subseteq \\mathsf{Expr} \\times \\mathsf{TLabel} \\times \\mathsf{Expr}",
   "args": [
    {
     "name": "o",
     "meaning": "The end."
    },
    {
     "name": "i",
     "meaning": "The received choice, one step for each $i$."
    }
   ]
  },
  "T-Act-Link": {
   "title": "T-Act-Link",
   "what": "$\\mathsf{link}\\,\\langle o_1, o_2\\rangle \\xrightarrow{\\leftrightarrow\\{o_1, o_2\\}} \\ast$. The label is a set, so $\\langle o_1, o_2\\rangle$ and $\\langle o_2, o_1\\rangle$ give one label.",
   "why": "The renaming $\\mathsf{csub}\\,o_1\\,o_2$ concerns other threads, so the process rule performs the renaming.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{link}\\,\\langle c^{+}, d^{-}\\rangle \\xrightarrow{\\leftrightarrow\\{c^{+}, d^{-}\\}} \\ast$.",
   "rocq": "lang/Semantics.v: t_act_link",
   "sig": "\\cdot \\xrightarrow{\\cdot} \\cdot \\subseteq \\mathsf{Expr} \\times \\mathsf{TLabel} \\times \\mathsf{Expr}",
   "args": [
    {
     "name": "o_1, o_2",
     "meaning": "The linked ends."
    }
   ]
  },
  "T-Act-Ctx": {
   "title": "T-Act-Ctx",
   "what": "If $e \\xrightarrow{\\alpha} e'$ and $\\mathsf{frame\\_val}\\,f$, then $f[e] \\xrightarrow{\\alpha} f[e']$.",
   "why": "No frame has its hole under $\\lambda$ or $!$, so the bodies of closures and boxes take no step before they are called.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{let}\\ \\ast = \\mathsf{close}\\,c^{+}\\ \\mathsf{in}\\ e$ steps when $\\mathsf{close}\\,c^{+}$ does.",
   "rocq": "lang/Semantics.v: t_act_ctx",
   "sig": "\\dfrac{e \\xrightarrow{\\alpha} e' \\quad \\mathsf{frame\\_val}\\,f}{f[e] \\xrightarrow{\\alpha} f[e']}",
   "args": [
    {
     "name": "e, e'",
     "meaning": "The term in the hole before and after the step."
    },
    {
     "name": "\\alpha",
     "meaning": "The label, passed through unchanged."
    },
    {
     "name": "f",
     "meaning": "An evaluation frame whose subterms left of the hole are values."
    }
   ]
  },
  "sem.frameval": {
   "title": "$\\mathsf{frame\\_val}$",
   "what": "$\\mathsf{frame\\_val}\\,f$ holds when every subterm of $f$ left of the hole is a value.",
   "why": "It fixes left-to-right evaluation, so every term has at most one redex position.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{frame\\_val}(v_1\\,\\square)$ requires $v_1$ to be a value.",
   "rocq": "lang/Semantics.v: frame_val",
   "sig": "\\mathsf{frame\\_val} : \\mathsf{Frame} \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "f",
     "meaning": "A frame, $\\mathsf{frame\\_val}\\,f$ iff every subterm of $f$ left of the hole is a value."
    }
   ]
  },
  "P-Act-Beta": {
   "title": "P-Act-Beta",
   "what": "If $M(i) \\xrightarrow{\\beta} e'$, then $(C, M) \\to (C, M[i \\mapsto e'])$ with event $\\mathsf{solo}_i\\,\\beta\\,\\cdot$.",
   "why": "A plain rule. A $\\beta$ step changes only thread $i$.",
   "breaks": "Nothing. It is a definition.",
   "example": "A $\\beta$ step of thread $0$.",
   "rocq": "lang/Process.v: p_act_beta",
   "sig": "(C, M) \\xrightarrow{ev} (C', M') \\subseteq \\mathsf{Config} \\times \\mathsf{Event} \\times \\mathsf{Config}",
   "args": [
    {
     "name": "(C, M)",
     "meaning": "The configuration before the step, $C$ its restricted channels and $M$ its thread map."
    },
    {
     "name": "i",
     "meaning": "The identifier of the acting thread, $i \\in \\mathrm{dom}\\,M$."
    },
    {
     "name": "e'",
     "meaning": "The term of thread $i$ after its step."
    }
   ]
  },
  "P-Act-New": {
   "title": "P-Act-New",
   "what": "If $M(i) \\xrightarrow{\\mathsf{new}\\,c} e'$ and $c \\notin C \\cup \\mathsf{echans}(M)$, then $(C, M) \\to (C \\cup \\{c\\}, M[i \\mapsto e'])$.",
   "why": "Both ends of $c$ start in thread $i$, so $c$ is internal to the process and joins $C$.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{new}$ creates $c$ with $c \\notin C$.",
   "rocq": "lang/Process.v: p_act_new",
   "sig": "(C, M) \\xrightarrow{ev} (C', M') \\subseteq \\mathsf{Config} \\times \\mathsf{Event} \\times \\mathsf{Config}",
   "args": [
    {
     "name": "(C, M)",
     "meaning": "The configuration before the step, $C$ its restricted channels and $M$ its thread map."
    },
    {
     "name": "i",
     "meaning": "The identifier of the acting thread, $i \\in \\mathrm{dom}\\,M$."
    },
    {
     "name": "e'",
     "meaning": "The term of thread $i$ after its step."
    },
    {
     "name": "c",
     "meaning": "The new channel, with $c \\notin C \\cup \\mathsf{echans}(M)$."
    }
   ]
  },
  "sem.fresh-global": {
   "title": "Global freshness",
   "what": "$c \\notin C \\cup \\mathsf{echans}(M)$, so $c$ is neither restricted nor mentioned by any thread.",
   "why": "Channel names are global. If $c \\in \\mathsf{fchans}(M(j))$ for some $j$, the new channel would share its name with a channel thread $j$ uses.",
   "breaks": "Reusing a name some thread still mentions merges two channels into one, and an action on one channel synchronizes with an action on the other.",
   "example": "$c \\notin C \\cup \\mathsf{echans}(M)$.",
   "rocq": "lang/Process.v: p_act_new",
   "sig": "c \\notin C \\cup \\mathsf{echans}(M)",
   "args": [
    {
     "name": "c",
     "meaning": "The name of the channel being created."
    },
    {
     "name": "C",
     "meaning": "The restricted channels of the configuration."
    },
    {
     "name": "M",
     "meaning": "The thread map of the configuration."
    }
   ]
  },
  "P-Act-Spawn": {
   "title": "P-Act-Spawn",
   "what": "If $M(i) \\xrightarrow{\\mathsf{spawn}\\,v} e'$ and $j \\notin \\mathrm{dom}\\,M$, then $M$ becomes $M[i \\mapsto e'][j \\mapsto v\\,\\ast]$.",
   "why": "The event is $\\mathsf{solo}_i\\,(\\mathsf{spawn}\\,v)\\,j$, so only thread $i$ takes part.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{spawn}\\,(\\lambda u.\\,e)$ adds a thread $j$ running $(\\lambda u.\\,e)\\,\\ast$.",
   "rocq": "lang/Process.v: p_act_spawn",
   "sig": "(C, M) \\xrightarrow{ev} (C', M') \\subseteq \\mathsf{Config} \\times \\mathsf{Event} \\times \\mathsf{Config}",
   "args": [
    {
     "name": "(C, M)",
     "meaning": "The configuration before the step, $C$ its restricted channels and $M$ its thread map."
    },
    {
     "name": "i",
     "meaning": "The identifier of the acting thread, $i \\in \\mathrm{dom}\\,M$."
    },
    {
     "name": "e'",
     "meaning": "The term of thread $i$ after its step."
    },
    {
     "name": "v",
     "meaning": "The thunk."
    },
    {
     "name": "j",
     "meaning": "The identifier of the new thread, $j \\notin \\mathrm{dom}\\,M$."
    }
   ]
  },
  "P-Act-Msg": {
   "title": "P-Act-Msg",
   "what": "$M(i) \\xrightarrow{o!v} e'$, $M(j) \\xrightarrow{\\overline{o}?v} f'$, $i \\neq j$ give $M[i \\mapsto e'][j \\mapsto f']$, with no condition on $C$.",
   "why": "In a typed process both ends of $c$ are held inside only when $c \\in C$, so dropping the condition $\\mathsf{ech}\\,o \\in C$ adds no step to typed processes.",
   "breaks": "Nothing. It is a definition.",
   "example": "The client sends on $a$ and the server receives on $a'$.",
   "rocq": "lang/Process.v: p_act_msg",
   "sig": "(C, M) \\xrightarrow{ev} (C', M') \\subseteq \\mathsf{Config} \\times \\mathsf{Event} \\times \\mathsf{Config}",
   "args": [
    {
     "name": "(C, M)",
     "meaning": "The configuration before the step, $C$ its restricted channels and $M$ its thread map."
    },
    {
     "name": "i",
     "meaning": "The identifier of the acting thread, $i \\in \\mathrm{dom}\\,M$."
    },
    {
     "name": "j",
     "meaning": "The identifier of the partner thread, $j \\in \\mathrm{dom}\\,M$ with $j \\neq i$."
    },
    {
     "name": "o",
     "meaning": "The end of the sender, the receiver acts on $\\overline{o}$."
    },
    {
     "name": "v",
     "meaning": "The payload, the same value in both labels."
    },
    {
     "name": "e'",
     "meaning": "The term of thread $i$ after its step."
    },
    {
     "name": "f'",
     "meaning": "The term of thread $j$ after its step."
    }
   ]
  },
  "P-Act-Close": {
   "title": "P-Act-Close",
   "what": "If $M(i) \\xrightarrow{o\\,\\mathsf{end}} e'$, $M(j) \\xrightarrow{\\overline{o}\\,\\mathsf{end}} f'$ and $\\mathsf{ech}\\,o \\in C$, then $C$ becomes $C \\setminus \\{\\mathsf{ech}\\,o\\}$.",
   "why": "After both closes no thread holds an end of $\\mathsf{ech}\\,o$, so the channel leaves $C$.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{close}\\,c^{+}$ and $\\mathsf{close}\\,c^{-}$ in two threads remove $c$.",
   "rocq": "lang/Process.v: p_act_close",
   "sig": "(C, M) \\xrightarrow{ev} (C', M') \\subseteq \\mathsf{Config} \\times \\mathsf{Event} \\times \\mathsf{Config}",
   "args": [
    {
     "name": "(C, M)",
     "meaning": "The configuration before the step, $C$ its restricted channels and $M$ its thread map."
    },
    {
     "name": "i",
     "meaning": "The identifier of the acting thread, $i \\in \\mathrm{dom}\\,M$."
    },
    {
     "name": "j",
     "meaning": "The identifier of the partner thread, $j \\in \\mathrm{dom}\\,M$ with $j \\neq i$."
    },
    {
     "name": "o",
     "meaning": "The end closed by $i$, with $\\mathsf{ech}\\,o \\in C$."
    },
    {
     "name": "e'",
     "meaning": "The term of thread $i$ after its step."
    },
    {
     "name": "f'",
     "meaning": "The term of thread $j$ after its step."
    }
   ]
  },
  "P-Act-Choice": {
   "title": "P-Act-Choice",
   "what": "If $M(i) \\xrightarrow{o \\lhd b} e'$ and $M(j) \\xrightarrow{\\overline{o} \\rhd b} f'$ with the same $b$, then $M$ becomes $M[i \\mapsto e'][j \\mapsto f']$.",
   "why": "Requiring the same $b$ passes the choice of thread $i$ to thread $j$.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{select}_{\\mathsf{true}}\\,o$ meets $\\mathsf{branch}\\,\\overline{o}$, which steps to $\\mathsf{inj}_2\\,\\overline{o}$.",
   "rocq": "lang/Process.v: p_act_choice",
   "sig": "(C, M) \\xrightarrow{ev} (C', M') \\subseteq \\mathsf{Config} \\times \\mathsf{Event} \\times \\mathsf{Config}",
   "args": [
    {
     "name": "(C, M)",
     "meaning": "The configuration before the step, $C$ its restricted channels and $M$ its thread map."
    },
    {
     "name": "i",
     "meaning": "The identifier of the acting thread, $i \\in \\mathrm{dom}\\,M$."
    },
    {
     "name": "j",
     "meaning": "The identifier of the partner thread, $j \\in \\mathrm{dom}\\,M$ with $j \\neq i$."
    },
    {
     "name": "o",
     "meaning": "The selecting end, the partner branches on $\\overline{o}$."
    },
    {
     "name": "b",
     "meaning": "The choice, the same in both labels."
    },
    {
     "name": "e'",
     "meaning": "The term of thread $i$ after its step."
    },
    {
     "name": "f'",
     "meaning": "The term of thread $j$ after its step."
    }
   ]
  },
  "P-Act-Link": {
   "title": "P-Act-Link",
   "what": "If $M(i) \\xrightarrow{\\leftrightarrow\\{o_1, o_2\\}} e'$ and $\\mathsf{ech}\\,o_1 \\in C$, then $C$ loses $\\mathsf{ech}\\,o_1$ and every thread of $M[i \\mapsto e']$ is renamed by $\\mathsf{csub}\\,o_1\\,o_2$.",
   "why": "The label is unordered, so the rule applies with either end as $o_1$ and removes the channel of either end.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{link}\\,\\langle c^{+}, d^{-}\\rangle$ with $c \\in C$.",
   "rocq": "lang/Process.v: p_act_link",
   "sig": "(C, M) \\xrightarrow{ev} (C', M') \\subseteq \\mathsf{Config} \\times \\mathsf{Event} \\times \\mathsf{Config}",
   "args": [
    {
     "name": "(C, M)",
     "meaning": "The configuration before the step, $C$ its restricted channels and $M$ its thread map."
    },
    {
     "name": "i",
     "meaning": "The identifier of the acting thread, $i \\in \\mathrm{dom}\\,M$."
    },
    {
     "name": "o_1, o_2",
     "meaning": "The linked ends, with $\\mathsf{ech}\\,o_1 \\in C$."
    },
    {
     "name": "e'",
     "meaning": "The term of thread $i$ after its step."
    }
   ]
  },
  "P-Act-Session": {
   "title": "P-Act-Session",
   "what": "If $M(i) \\xrightarrow{\\sigma} e'$ and $\\mathsf{subj}\\,\\sigma \\cap C = \\varnothing$, then $(C, M) \\to (C \\setminus \\mathsf{sentc}\\,\\sigma, M[i \\mapsto e'])$, an offer to the environment.",
   "why": "A send of $v$ to the environment moves the ends $\\mathsf{fends}(v)$, so their channels leave $C$. The process and the relation compute the extruded channels from the same $v$.",
   "breaks": "Nothing. It is a definition.",
   "example": "An external send of a restricted $d^{+}$ removes $d$ from $C$.",
   "rocq": "lang/Process.v: p_act_session",
   "sig": "(C, M) \\xrightarrow{ev} (C', M') \\subseteq \\mathsf{Config} \\times \\mathsf{Event} \\times \\mathsf{Config}",
   "args": [
    {
     "name": "(C, M)",
     "meaning": "The configuration before the step, $C$ its restricted channels and $M$ its thread map."
    },
    {
     "name": "i",
     "meaning": "The identifier of the acting thread, $i \\in \\mathrm{dom}\\,M$."
    },
    {
     "name": "\\sigma",
     "meaning": "A session label with $\\mathsf{subj}\\,\\sigma \\cap C = \\varnothing$, an offer to the environment."
    },
    {
     "name": "e'",
     "meaning": "The term of thread $i$ after its step."
    }
   ]
  },
  "sem.sentc": {
   "title": "$\\mathsf{sentc}$",
   "what": "$\\mathsf{sentc}(o!v) = \\mathsf{fchans}(v) = \\{\\mathsf{ech}\\,o' \\mid o' \\in \\mathsf{fends}(v)\\}$, and $\\mathsf{sentc}\\,\\sigma = \\varnothing$ for every other $\\sigma$.",
   "why": "These are the channels a message to the environment moves out of the process.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{sentc}(o!d^{+}) = \\{d\\}$.",
   "rocq": "lang/Semantics.v: sentc",
   "sig": "\\mathsf{sentc} : \\mathsf{SLabel} \\to \\mathcal{P}_{\\mathrm{fin}}(\\mathsf{Chan})",
   "args": [
    {
     "name": "\\sigma",
     "meaning": "A session label, $\\mathsf{sentc}(o!v) = \\mathsf{fchans}(v)$ and $\\varnothing$ otherwise."
    }
   ]
  },
  "ev.event": {
   "title": "Event",
   "what": "$\\mathsf{solo}_i\\,\\alpha\\,k$ is a step of thread $i$ alone with thread label $\\alpha$. $\\mathsf{sync}_{i,j}\\,\\sigma$ is a step in which thread $i$ takes the send, close or select $\\sigma$ on an end $o$ and thread $j$ the matching receive, close or branch on $\\overline{o}$. $\\mathsf{offer}_i\\,\\sigma$ is an offer of thread $i$ to the environment.",
   "why": "Weak fairness asks of each thread $t$ that $t \\in \\mathsf{parts}(l_j)$ for some $j$, so every step names its threads.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{sync}_{0,1}\\,(a^{+}!\\ast)$.",
   "rocq": "lang/Process.v: event",
   "sig": "ev \\in \\mathsf{Event}",
   "args": [
    {
     "name": "i, j",
     "meaning": "Thread identifiers of the participants."
    },
    {
     "name": "\\alpha",
     "meaning": "The thread label of a solo step."
    },
    {
     "name": "k",
     "meaning": "The pick of a solo step."
    },
    {
     "name": "\\sigma",
     "meaning": "The session label of thread $i$, in a synchronization or an offer to the environment."
    }
   ]
  },
  "ev.pick": {
   "title": "Pick $k$",
   "what": "What a process rule chooses beyond the thread label. $k = j$ names the new thread of a spawn. $k = (o_1, o_2)$ orders the ends of a link, so the channel of $o_1$ goes and the thread with $\\overline{o_1}$ then holds $o_2$. Every other solo step has $k = \\cdot$.",
   "why": "The thread label of a link is the unordered set $\\{o_1, o_2\\}$, and the thread label of a spawn names no thread, so the event records the choice the rule makes.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{solo}_0\\,(\\leftrightarrow\\{c^{+}, d^{-}\\})\\,(c^{+}, d^{-})$ removes $c$.",
   "rocq": "lang/Process.v: pick",
   "sig": "k \\in \\mathbb{N}_{\\bot} \\cup \\mathsf{End} \\times \\mathsf{End}",
   "args": [
    {
     "name": "j",
     "meaning": "The identifier of a spawned thread."
    },
    {
     "name": "o_1, o_2",
     "meaning": "The ends of a link, the channel of $o_1$ goes."
    }
   ]
  },
  "ev.admin": {
   "title": "Administrative events",
   "what": "$\\mathsf{admin}$ is the set of solo events $\\mathsf{solo}_i\\,\\alpha\\,k$, the steps by $\\beta$, $\\mathsf{new}$, $\\mathsf{spawn}$ and $\\mathsf{link}$, each of cost $0$ in $\\kappa_L$.",
   "why": "They act on no protocol. Absence of internal divergence states that every chain of them is finite.",
   "breaks": "Nothing. It is a definition.",
   "example": "An unbounded chain of spawns takes only administrative steps.",
   "rocq": "lang/Process.v: ev_admin",
   "sig": "\\mathsf{admin} \\subseteq \\mathsf{Event}",
   "args": []
  },
  "ev.tau": {
   "title": "$\\tau$ events",
   "what": "Every event except $\\mathsf{offer}_i\\,\\sigma$, an offer to the environment.",
   "why": "A closed configuration has no environment, so all its steps are $\\tau$ steps.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{sync}_{0,1}\\,(a^{+}!\\ast)$ is a $\\tau$ event.",
   "rocq": "lang/Process.v: ev_tau, itstep",
   "sig": "\\tau \\subseteq \\mathsf{Event}",
   "args": []
  },
  "prop.terminated": {
   "title": "$\\mathsf{terminated}$",
   "what": "$\\mathsf{terminated}\\,p$ iff $p = (\\varnothing, \\{\\!|v|\\!\\} \\uplus E)$ with $v$ a value and $e = \\ast$ for every $e \\in E$.",
   "why": "At the end $C = \\varnothing$, so every channel is used up, and only the main thread returns a value.",
   "breaks": "Nothing. It is a definition.",
   "example": "$(\\varnothing, \\{\\!|\\ast, \\ast|\\!\\})$.",
   "rocq": "lang/Safety.v: terminated",
   "sig": "\\mathsf{terminated} : \\mathsf{Proc} \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "p",
     "meaning": "A process."
    },
    {
     "name": "v",
     "meaning": "The result of the main thread, a value."
    },
    {
     "name": "E",
     "meaning": "The multiset of the other threads, each equal to $\\ast$."
    }
   ]
  },
  "prop.df": {
   "title": "$\\mathsf{deadlock\\_free}$",
   "what": "$\\mathsf{deadlock\\_free}\\,p$ iff for every $p'$ with $p \\to^{*} p'$, $\\mathsf{terminated}\\,p'$ or $p' \\to p''$ for some $p''$.",
   "why": "It is the safety property the deadlock-freedom system proves of closed typed processes.",
   "breaks": "Nothing. It is a definition.",
   "example": "$(\\{c\\}, \\{\\!|\\mathsf{close}\\,c^{+}, \\mathsf{close}\\,c^{-}|\\!\\})$ is deadlock free.",
   "rocq": "lang/Safety.v: deadlock_free",
   "sig": "\\mathsf{deadlock\\_free} : \\mathsf{Proc} \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "p",
     "meaning": "The process."
    },
    {
     "name": "p'",
     "meaning": "Ranges over all processes with $p \\to^{*} p'$."
    },
    {
     "name": "p''",
     "meaning": "A successor of $p'$, existentially quantified."
    }
   ]
  },
  "prop.notau": {
   "title": "$\\mathsf{no\\_tau\\_divergence}$",
   "what": "For every $q$ with $p \\to^{*} q$, $\\mathsf{Acc}\\ {\\to_{\\mathsf{admin}}}\\ q$, so no infinite chain of administrative steps starts at $q$.",
   "why": "Lock freedom requires that a thread eventually performs its next action. An infinite chain of $\\beta$, spawn or link steps never performs one.",
   "breaks": "$\\mathsf{force}\\,!(f = \\mathsf{force}\\,f)$ takes $\\beta$ steps forever, and a forwarder that spawns a new forwarder at each round spawns forever.",
   "example": "$\\mathsf{force}\\,!(f = \\mathsf{force}\\,f)$ violates the property.",
   "rocq": "lockfree/TauThread.v: no_tau_divergence",
   "sig": "\\mathsf{no\\_tau\\_divergence} : \\mathsf{Proc} \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "p",
     "meaning": "The process."
    },
    {
     "name": "q",
     "meaning": "Ranges over all processes with $p \\to^{*} q$."
    }
   ]
  },
  "prop.padmin": {
   "title": "Administrative step",
   "what": "$q \\to_{\\mathsf{admin}} q'$ when $q \\to q'$ with an administrative event.",
   "why": "It is the relation that absence of internal divergence asks to be well-founded.",
   "breaks": "Nothing. It is a definition.",
   "example": "A $\\beta$ step of any thread.",
   "rocq": "lockfree/TauThread.v: padmin",
   "sig": "\\cdot \\to_{\\mathsf{admin}} \\cdot \\subseteq \\mathsf{Proc} \\times \\mathsf{Proc}",
   "args": [
    {
     "name": "q, q'",
     "meaning": "Processes with $q \\to q'$ by an event in $\\mathsf{admin}$."
    }
   ]
  },
  "prop.lf": {
   "title": "$\\mathsf{lock\\_free}$",
   "what": "For every run $(r, l)$ with $\\mathsf{erase}(r_0) = p$ that is maximal and weakly fair, every thread $t$ pending at a position $i$ has $t \\in \\mathsf{parts}(l_j)$ for some $j \\geq i$.",
   "why": "Deadlock freedom allows a thread to wait forever while other threads step. Lock freedom excludes it, and its definition mentions no type.",
   "breaks": "A server that serves one client forever while a second client waits is deadlock free and not lock free.",
   "example": "$(\\{c\\}, \\{\\!|\\mathsf{close}\\,c^{+}, \\mathsf{close}\\,c^{-}|\\!\\})$ is lock free.",
   "rocq": "lockfree/Fair.v: lock_free",
   "sig": "\\mathsf{lock\\_free} : \\mathsf{Proc} \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "p",
     "meaning": "The process."
    },
    {
     "name": "(r, l)",
     "meaning": "A run, $r_i \\in \\mathsf{Config}$ the configuration and $l_i$ the event or stutter at position $i \\in \\mathbb{N}$."
    },
    {
     "name": "i",
     "meaning": "A position of the run."
    },
    {
     "name": "t",
     "meaning": "A thread identifier."
    },
    {
     "name": "j",
     "meaning": "A position with $j \\ge i$, existentially quantified."
    }
   ]
  },
  "prop.maximal": {
   "title": "Maximal run",
   "what": "For every $i$, either $r_i \\to r_{i+1}$ by a $\\tau$ event $l_i$, or $r_i$ has no $\\tau$ step and $r_{i+1} = r_i$.",
   "why": "A run that stutters while a step is possible would satisfy lock freedom vacuously, so the definition quantifies over maximal runs only.",
   "breaks": "Nothing. It is a definition.",
   "example": "A run that stutters at $r_i$ while $r_i$ has a $\\tau$ step is not maximal.",
   "rocq": "lockfree/Fair.v: maximal",
   "sig": "\\mathsf{maximal} : \\mathsf{Run} \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "(r, l)",
     "meaning": "A run, $r_i \\in \\mathsf{Config}$ the configuration and $l_i$ the event or stutter at position $i \\in \\mathbb{N}$."
    },
    {
     "name": "i",
     "meaning": "Ranges over all positions."
    }
   ]
  },
  "prop.wfair": {
   "title": "Weak fairness",
   "what": "For every position $i$ and thread $t$, there is $j \\geq i$ with $t \\in \\mathsf{parts}(l_j)$ or $t$ disabled at $r_j$.",
   "why": "Without fairness a scheduler may never run an enabled thread $t$, and no program with two threads is lock free.",
   "breaks": "Nothing. It is a definition.",
   "example": "A run that never schedules an enabled thread is not weakly fair.",
   "rocq": "lockfree/Fair.v: wfair",
   "sig": "\\mathsf{wfair} : \\mathsf{Run} \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "(r, l)",
     "meaning": "A run, $r_i \\in \\mathsf{Config}$ the configuration and $l_i$ the event or stutter at position $i \\in \\mathbb{N}$."
    },
    {
     "name": "i",
     "meaning": "Ranges over all positions."
    },
    {
     "name": "t",
     "meaning": "Ranges over all thread identifiers."
    },
    {
     "name": "j",
     "meaning": "A position with $j \\ge i$, existentially quantified."
    }
   ]
  },
  "prop.pend": {
   "title": "Pending thread",
   "what": "$\\mathsf{pend}(q, t)$ holds when thread $t$ of $q$ has a session label as its next step.",
   "why": "Lock freedom guarantees progress exactly to the pending threads.",
   "breaks": "Nothing. It is a definition.",
   "example": "A thread at $\\mathsf{recv}\\,b$ is pending.",
   "rocq": "lockfree/Fair.v: pend",
   "sig": "\\mathsf{pend} : \\mathsf{Config} \\to \\mathbb{N} \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "q",
     "meaning": "A configuration, instantiated with $r_i$."
    },
    {
     "name": "t",
     "meaning": "A thread identifier of $q$."
    }
   ]
  },
  "prop.lfrun": {
   "title": "$\\mathsf{lf\\_run}$",
   "what": "For every $i$ and $t$, $\\mathsf{pend}(r_i, t)$ implies $t \\in \\mathsf{parts}(l_j)$ for some $j \\geq i$.",
   "why": "It is the condition on one run, and $\\mathsf{lock\\_free}\\,p$ asks it of every maximal weakly fair run from $p$.",
   "breaks": "Nothing. It is a definition.",
   "example": "Every message the client sends is received by the server at a later position.",
   "rocq": "lockfree/Fair.v: lf_run",
   "sig": "\\mathsf{lf\\_run} : \\mathsf{Run} \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "(r, l)",
     "meaning": "A run, $r_i \\in \\mathsf{Config}$ the configuration and $l_i$ the event or stutter at position $i \\in \\mathbb{N}$."
    },
    {
     "name": "i, t",
     "meaning": "Range over all positions and thread identifiers."
    },
    {
     "name": "j",
     "meaning": "A position with $j \\ge i$, existentially quantified."
    }
   ]
  },
  "ty.unit": {
   "title": "Unit type $\\ast$",
   "what": "The type of $\\ast$, with $V\\llbracket\\Theta \\vdash \\ast\\rrbracket = \\{\\ast\\}$ at $\\Theta = \\varnothing$ and empty otherwise.",
   "why": "A plain type. $\\mathsf{close}$, $\\mathsf{link}$ and $\\mathsf{spawn}$ return $\\ast$, and every spawned thread returns $\\ast$.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{close}\\,o : \\ast$.",
   "rocq": "types/Types.v: TUnit",
   "sig": "\\ast \\in \\mathsf{Ty}",
   "args": []
  },
  "ty.arrow": {
   "title": "Arrow",
   "what": "$(T \\multimap^{u}_{l}[c]\\,U)\\annot{^{a}}$ is a closure type with upper point $u$, lower point $l$, cost $c$\\annp{ and credit} $a$. \\annp{The body sees each captured end at its own credit minus $a$.}",
   "why": "A call runs code that may block and holds the ends of the closure. The type bounds where the call blocks by $u$ and where the held ends are by $l$.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\ast \\multimap \\ast$ is the type of a spawned thunk.",
   "rocq": "types/Types.v: TLolli",
   "sig": "(T \\multimap^{u}_{l}[c]\\,U)\\annot{^{a}} \\in \\mathsf{Ty}",
   "args": [
    {
     "name": "T",
     "meaning": "The argument type."
    },
    {
     "name": "U",
     "meaning": "The result type."
    },
    {
     "name": "a",
     "meaning": "The credit of the closure, a lower bound on its captured counters and what they lose before a call.",
     "ann": true
    },
    {
     "name": "u",
     "meaning": "The upper point, optional."
    },
    {
     "name": "l",
     "meaning": "The lower point, absent iff the closure holds no end."
    },
    {
     "name": "c",
     "meaning": "The cost of a call, $c \\in \\mathbb{N} \\cup \\{\\infty\\}$."
    }
   ]
  },
  "ty.ubound": {
   "title": "Upper point $u$",
   "what": "$u = x$ bounds the points where a call may block, $u = \\cdot$ (no end held, nothing to bound) asks nothing of the caller, and $u = \\top$ admits only the empty future, $\\top \\prec F \\iff F = (\\varnothing, \\cdot)$.",
   "why": "With $u = \\top$ the body runs as the last code of its thread. A spawned abstraction is such a closure, so E-Abs at $u = \\top$ and $l = \\bot$ followed by E-Spawn types it, and V-Arrow at $(\\top, \\bot)$ is the predicate of a spawned thunk.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{spawn}\\,(\\lambda e)$ uses $\\lambda e : \\ast \\multimap^{\\top}_{\\bot} \\ast$.",
   "rocq": "types/Points.v: ubound; static/Contexts.v: ub_below_u; relation/Readiness.v: ub_ltu",
   "sig": "u \\in \\mathsf{UBound} = \\{\\cdot, \\top\\} \\cup \\mathsf{Point}",
   "args": []
  },
  "ty.arrow.ub": {
   "title": "Upper point $u$",
   "what": "The body is in $E$ under every $F$ with $\\forall y \\in F.\\ u \\prec y$, which every caller must establish.",
   "why": "The type of a closure does not show its body. The condition $u \\prec F$ places the later actions of the caller above the points where the body may block.",
   "breaks": "Without $u$, a closure that blocks at $x$ with $y \\prec x$ for some later action $y$ of the caller could be called first, and the thread waits on its own later action.",
   "example": "A function that blocks on an end at $\\kappa$ has $u = \\kappa$.",
   "rocq": "types/Types.v: TLolli ub",
   "sig": "u \\in \\mathsf{Point}_{\\bot}",
   "args": [
    {
     "name": "u",
     "meaning": "A point or absent. The body is in $E$ under every future $F$ with $u \\prec y$ for all $y \\in F$."
    }
   ]
  },
  "ty.arrow.lb": {
   "title": "Lower point $l$",
   "what": "$\\forall y \\in \\mathsf{ap}(\\Theta).\\ l \\preceq y$ for the captured ends, with $l$ absent iff $\\Theta = \\varnothing$.",
   "why": "A closure is a held value. A thread blocked at $x$ while holding it needs $x \\prec y$ for every dual point $y$ of the captured ends, and $x \\prec l$ implies these facts.",
   "breaks": "Without $l$, a thread blocks at $x$ while it holds a closure with a captured end at $v$ and $x \\not\\prec \\overline{v}$, so the partner of that end may wait on the thread.",
   "example": "A closure capturing $a^{+}$ at $\\rho$ has $l = \\overline{\\rho}$.",
   "rocq": "types/Types.v: TLolli lb",
   "sig": "l \\in \\mathsf{Point} \\cup \\{\\cdot\\}",
   "args": [
    {
     "name": "l",
     "meaning": "A point with $l \\preceq y$ for every dual point $y$ of the captured ends, or $\\cdot$ iff the closure captures no end. Not $\\bot$, which marks hidden points at $\\exists^{\\bot}$."
    }
   ]
  },
  "ty.arrow.cost": {
   "title": "Arrow cost $c$",
   "what": "A call performs at most $c \\in \\mathbb{N} \\cup \\{\\infty\\}$ channel actions before it returns.",
   "why": "A thread that holds an end $o$ while a call runs delays $o$ by at most $c$ actions. Aging subtracts $c$ from the credit of $o$.",
   "breaks": "A thread that holds an end across a call that never returns waits forever the partner. With $c = \\infty$ the held end has credit $a - \\infty$, which fails $c \\leq a$ at finite counter bound.",
   "example": "A loop body that never returns has $c = \\infty$.",
   "rocq": "types/Types.v: TLolli c",
   "sig": "c \\in \\mathbb{N} \\cup \\{\\infty\\}",
   "args": [
    {
     "name": "c",
     "meaning": "An upper bound on the channel actions of one call before it returns."
    }
   ]
  },
  "ty.credit": {
   "title": "Credit $a$",
   "what": "$a \\in \\mathbb{N} \\cup \\{\\infty\\}$ on an end type $(S@x)\\annot{^{a}}_{m}$ is a lower bound on the counter of that end. On a closure type $(T \\multimap [c]\\, U)\\annot{^{a}}$ every captured end that is not idle has counter at least $a$.",
   "why": "A counter bounds how many actions of other ends an end may still wait through. Only ends and closures hold ends of their own. A pair, a sum or an existential holds the ends of its parts, and their types have the credits.",
   "breaks": "A send of an end whose counter may be $0$ lets the end be sent on forever while its partner waits.",
   "example": "A fresh end with $m$ tickets has type $(S@\\rho)^{m}_{m}$.",
   "rocq": "types/Types.v: TSess, TLolli",
   "sig": "a \\in \\mathbb{N} \\cup \\{\\infty\\}",
   "args": [
    {
     "name": "a",
     "meaning": "A lower bound on the counter of an end, or of the ends a closure captured."
    }
   ]
  },
  "ty.prod": {
   "title": "Product",
   "what": "$T \\otimes U$. Its value relation splits $\\Theta = \\Theta_1 \\uplus \\Theta_2$ between the components.",
   "why": "A plain type. $\\mathsf{send}$ takes a pair and $\\mathsf{recv}$ returns one.",
   "breaks": "Nothing. It is a definition.",
   "example": "$S_1@\\iota \\otimes S_2@\\kappa$ for two ends of a client.",
   "rocq": "types/Types.v: TProd",
   "sig": "T \\otimes U \\in \\mathsf{Ty}",
   "args": [
    {
     "name": "T, U",
     "meaning": "The component types."
    }
   ]
  },
  "ty.sum": {
   "title": "Sum",
   "what": "$T \\oplus U$, the type of $\\mathsf{inj}_1\\,v$ with $v : T$ and of $\\mathsf{inj}_2\\,v$ with $v : U$.",
   "why": "A plain type. $\\mathsf{branch}$ returns a sum whose injection records the choice.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{branch}$ at $x$ returns $S_1@x\\cdot\\kappa_{\\mathsf{false}} \\oplus S_2@x\\cdot\\kappa_{\\mathsf{true}}$.",
   "rocq": "types/Types.v: TSum",
   "sig": "T \\oplus U \\in \\mathsf{Ty}",
   "args": [
    {
     "name": "T, U",
     "meaning": "The types of the two injections."
    }
   ]
  },
  "ty.sess": {
   "title": "End type $S@x$",
   "what": "An end that runs the protocol $S$ and acts next at the point $x$.",
   "why": "The points order the next actions of all ends, and readiness compares them to exclude circular waiting.",
   "breaks": "Nothing. It is a definition.",
   "example": "$(!\\ast.\\mathsf{Close})@\\rho$.",
   "rocq": "types/Types.v: TSess",
   "sig": "(S@x)\\annot{^{a}}_{m} \\in \\mathsf{Ty}",
   "args": [
    {
     "name": "S",
     "meaning": "The protocol the end runs."
    },
    {
     "name": "x",
     "meaning": "The point of its next action."
    },
    {
     "name": "a",
     "meaning": "Its credit, a lower bound on its counter.",
     "ann": true
    },
    {
     "name": "m",
     "meaning": "\\annp{Its tickets, an upper bound on its counter, with $a \\leq m$.}"
    }
   ]
  },
  "ty.box": {
   "title": "Box type",
   "what": "$\\Box(\\forall\\bar\\iota\\,\\bar\\alpha.\\ C.\\ \\ast \\multimap^{u} U)$ is a replicable thunk, usable at every point instance $\\bar x$ with $C[\\bar x]$ and every session instance $\\bar s$.",
   "why": "A loop needs fresh points in each round. Quantifying over $\\bar\\iota$ under $\\Box$ gives every call its own instance.",
   "breaks": "Nothing. It is a definition.",
   "example": "A client loop has type $\\Box\\forall\\iota\\,\\kappa\\,\\zeta.\\ C.\\ \\ast \\multimap (S_1@\\iota \\otimes S_2@\\kappa \\multimap^{\\zeta} \\ast)$.",
   "rocq": "types/Types.v: TBox",
   "sig": "\\Box(\\forall\\bar\\iota\\,\\bar\\alpha.\\ C.\\ \\ast \\multimap^{u}[c]\\,U) \\in \\mathsf{Ty}",
   "args": [
    {
     "name": "\\bar\\iota",
     "meaning": "$m$ point variables, instantiated at each $\\mathsf{force}$ by points $\\bar x$ with $C[\\bar x]$."
    },
    {
     "name": "\\bar\\alpha",
     "meaning": "$k$ session variables, instantiated at each $\\mathsf{force}$."
    },
    {
     "name": "C",
     "meaning": "The constraint over $\\bar\\iota$ and outer points."
    },
    {
     "name": "u",
     "meaning": "The upper point of the thunk."
    },
    {
     "name": "c",
     "meaning": "The cost of one force."
    },
    {
     "name": "U",
     "meaning": "The result type."
    }
   ]
  },
  "ty.box.svars": {
   "title": "Session variables $\\bar\\alpha$",
   "what": "$k$ session variables, instantiated at every $\\mathsf{force}$ by session types whose recursion passes an action.",
   "why": "One box serves every protocol the caller substitutes for $\\bar\\alpha$.",
   "breaks": "Nothing. It is a definition.",
   "example": "A forwarder box for every protocol $\\alpha$.",
   "rocq": "types/Types.v: TBox k",
   "sig": "\\bar\\alpha = \\alpha_1, \\ldots, \\alpha_k",
   "args": [
    {
     "name": "k",
     "meaning": "The number of session variables."
    }
   ]
  },
  "ty.box.constraint": {
   "title": "Box constraint $C$",
   "what": "A set of facts $x \\prec y$ over $\\bar\\iota$ and outer points, possibly infinite.",
   "why": "A loop orders the points of all its rounds at once, and an infinite $C$ states the facts of every round.",
   "breaks": "Without $C$ a box cannot type a loop that waits on one end while it holds another across rounds.",
   "example": "$C$ states $\\iota \\prec \\overline{\\kappa}$ for the points of every round of a client loop.",
   "rocq": "types/Points.v: bcs",
   "sig": "C \\subseteq \\{x \\prec y \\mid x, y \\in \\mathsf{Point}\\}",
   "args": [
    {
     "name": "C",
     "meaning": "A set of facts over $\\bar\\iota$ and outer points, possibly infinite."
    }
   ]
  },
  "ty.ex": {
   "title": "Existential",
   "what": "$\\exists^{l}\\bar\\iota.\\ C.\\ T\\annot{^{a}}$ is $T[\\bar x]$ for some $\\bar x$ with $C[\\bar x]$, and $l$ bounds the dual points of its ends from below.",
   "why": "A fresh point is unknown outside the term that created the point. $\\mathsf{new}$ returns an existential over it, and payloads bind their points the same way.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{new} : \\exists^{\\bot}\\iota.\\ \\{\\overline{\\iota} \\prec \\iota\\cdot 0\\}.\\ (S@\\iota \\otimes \\overline{S}@\\overline{\\iota})$.",
   "rocq": "types/Types.v: TEx",
   "sig": "\\exists^{l}\\bar\\iota.\\ C.\\ T \\in \\mathsf{Ty}",
   "args": [
    {
     "name": "l",
     "meaning": "The lower bound, $\\cdot$, $\\bot$ or a point."
    },
    {
     "name": "\\bar\\iota",
     "meaning": "$m$ point variables, the witness $\\bar x$ is hidden."
    },
    {
     "name": "C",
     "meaning": "The facts the witness satisfies."
    },
    {
     "name": "T",
     "meaning": "The body type."
    }
   ]
  },
  "ty.ex.lb": {
   "title": "Lower bound $l$",
   "what": "$l = \\cdot$ when the value holds no end, $l = \\bot$ when its ends are at points unknown outside, and $l = x$ when $x \\preceq y$ for every dual point $y$ of its ends.",
   "why": "$\\bot$ stands for a fresh point that no fact of the context mentions, and $\\mathsf{hbot}$ propagates $\\bot$.",
   "breaks": "Without $\\bot$, a closure captures an unopened fresh pair and claims a lower point $l$ that no fact of $W$ supports.",
   "example": "$\\mathsf{new} : \\exists^{\\bot}\\ldots$",
   "rocq": "types/Points.v: lbound",
   "sig": "l \\in \\{\\cdot, \\bot\\} \\cup \\mathsf{Point}",
   "args": [
    {
     "name": "l",
     "meaning": "$\\cdot$ for no end, $\\bot$ for ends at unknown points, $x$ when $x \\preceq y$ for every dual point $y$ of the ends."
    }
   ]
  },
  "sty.skip": {
   "title": "$\\mathsf{Skip}$",
   "what": "The empty protocol, and an end at $S$ with $\\mathsf{unfold}(S) = \\mathsf{Skip}$ is idle.",
   "why": "No partner waits on an idle end. The fuel layer drops for idle ends the checks that counters are at least $1$, so they may be held indefinitely.",
   "breaks": "Nothing. It is a definition.",
   "example": "A control end that is passed around and never used is at $\\mathsf{Skip}$.",
   "rocq": "types/Types.v: SSkip, idle",
   "sig": "\\mathsf{Skip} \\in \\mathsf{STy}",
   "args": []
  },
  "sty.seq": {
   "title": "Sequencing",
   "what": "$S.S'$ runs $S$ and then $S'$, and $\\mathsf{unfold}$ normalizes it to its first action.",
   "why": "Sequencing composes protocols, so a recursion variable need not occur in tail position.",
   "breaks": "Nothing. It is a definition.",
   "example": "$(!\\ast).\\mathsf{Close}$.",
   "rocq": "types/Types.v: SSeq",
   "sig": "S.S' \\in \\mathsf{STy}",
   "args": [
    {
     "name": "S, S'",
     "meaning": "The first and the second protocol."
    }
   ]
  },
  "sty.recv": {
   "title": "Receive",
   "what": "$?(\\bar\\iota.\\ T)$ receives a value of $T[x\\cdot 0, \\ldots, x\\cdot(m{-}1)]$ for $\\bar\\iota = \\iota_0, \\ldots, \\iota_{m-1}$ when the end is at $x$.",
   "why": "A plain protocol action. The binder $\\bar\\iota$ is no existential, because the points of the payload are determined, the fields of $x$. It lets a message have ends whose points the receiver learns as fields of $x$.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mu\\alpha.\\,?(\\kappa.\\ \\alpha @\\kappa).\\mathsf{Close}$ receives an end of the same protocol at a field.",
   "rocq": "types/Types.v: SRcv",
   "sig": "?(\\bar\\iota.\\ T) \\in \\mathsf{STy}",
   "args": [
    {
     "name": "\\bar\\iota",
     "meaning": "The point variables of the payload, $\\iota_0, \\ldots, \\iota_{m-1}$, placed at $x\\cdot 0, \\ldots, x\\cdot(m{-}1)$ for the carrier point $x$."
    },
    {
     "name": "T",
     "meaning": "The payload type."
    }
   ]
  },
  "sty.send": {
   "title": "Send",
   "what": "$!(\\bar\\iota.\\ T)$ sends a value of $T[x\\cdot 0, \\ldots, x\\cdot(m{-}1)]$ for $\\bar\\iota = \\iota_0, \\ldots, \\iota_{m-1}$. \\annp{The ends of $T$ have their credits, and the sender ages the payload by one transfer.}",
   "why": "A plain protocol action, $\\mathsf{dual}$ of receive.",
   "breaks": "Nothing. It is a definition.",
   "example": "$!\\ast.\\mathsf{Close}$.",
   "rocq": "types/Types.v: SSnd",
   "sig": "!(\\bar\\iota.\\ T) \\in \\mathsf{STy}",
   "args": [
    {
     "name": "\\bar\\iota",
     "meaning": "The point variables of the payload, placed at the fields of the carrier point."
    },
    {
     "name": "T",
     "meaning": "The payload type."
    }
   ]
  },
  "sty.plus": {
   "title": "Internal choice",
   "what": "$\\oplus(S_1, S_2)$, where the selecting side chooses $i$ and continues with $S_1$ or $S_2$.",
   "why": "A plain protocol action. The holding thread decides the continuation.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\oplus(\\mathsf{Close}, !\\ast.\\mathsf{Close})$.",
   "rocq": "types/Types.v: SPlus",
   "sig": "\\oplus(S_1, S_2) \\in \\mathsf{STy}",
   "args": [
    {
     "name": "S_1, S_2",
     "meaning": "The continuations for $i = \\mathsf{false}$ and $i = \\mathsf{true}$."
    }
   ]
  },
  "sty.with": {
   "title": "External choice",
   "what": "$\\&(S_1, S_2)$, where the branching side receives $i$ and continues with $S_1$ or $S_2$.",
   "why": "A plain protocol action, $\\mathsf{dual}$ of internal choice.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\&(\\mathsf{Close}, ?\\ast.\\mathsf{Close})$.",
   "rocq": "types/Types.v: SWith",
   "sig": "\\&(S_1, S_2) \\in \\mathsf{STy}",
   "args": [
    {
     "name": "S_1, S_2",
     "meaning": "The continuations for the received $i = \\mathsf{false}$ and $i = \\mathsf{true}$."
    }
   ]
  },
  "sty.close": {
   "title": "$\\mathsf{Close}$",
   "what": "The next action of the end is $\\mathsf{close}$.",
   "why": "A plain protocol action. Every finite protocol ends with $\\mathsf{Close}$.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{Close}@x^{+}$ after one send at $x$.",
   "rocq": "types/Types.v: SEnd",
   "sig": "\\mathsf{Close} \\in \\mathsf{STy}",
   "args": []
  },
  "sty.mu": {
   "title": "Recursion $\\mu\\alpha.S$",
   "what": "A recursive protocol, equal to its unrolling $S[\\mu\\alpha.S/\\alpha]$ up to $\\simeq$.",
   "why": "A plain former. Loops run repeating protocols.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mu\\alpha.\\,!\\ast.\\alpha$ sends $\\ast$ forever.",
   "rocq": "types/Types.v: SMu",
   "sig": "\\mu\\alpha.S \\in \\mathsf{STy}",
   "args": [
    {
     "name": "\\alpha",
     "meaning": "The recursion variable, bound in $S$."
    },
    {
     "name": "S",
     "meaning": "The body."
    }
   ]
  },
  "sty.var": {
   "title": "Session variable $\\alpha$",
   "what": "A recursion variable bound by $\\mu$, or a session variable bound by a box.",
   "why": "A plain former. It refers to an enclosing $\\mu\\alpha$ or to a protocol substituted at $\\mathsf{force}$.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\alpha$ in $\\mu\\alpha.\\,!\\ast.\\alpha$.",
   "rocq": "types/Types.v: SVar",
   "sig": "\\alpha \\in \\mathsf{STy}",
   "args": [
    {
     "name": "\\alpha",
     "meaning": "A variable bound by an enclosing $\\mu$ or by a box."
    }
   ]
  },
  "sty.vard": {
   "title": "Dual variable $\\overline{\\alpha}$",
   "what": "$\\mathsf{dual}(\\alpha) = \\overline{\\alpha}$, and substituting $s$ for $\\alpha$ substitutes $\\mathsf{dual}\\,s$ for $\\overline{\\alpha}$.",
   "why": "The dual of a protocol substituted for $\\alpha$ is known only after substitution, so $\\overline{\\alpha}$ defers the dual.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{dual}\\,\\alpha = \\overline{\\alpha}$.",
   "rocq": "types/Types.v: SVarD",
   "sig": "\\overline{\\alpha} \\in \\mathsf{STy}",
   "args": [
    {
     "name": "\\alpha",
     "meaning": "A session variable, $\\overline{\\alpha}$ stands for $\\mathsf{dual}$ of its instance."
    }
   ]
  },
  "sty.unfold": {
   "title": "Head normal form",
   "what": "$\\mathsf{unfold}(S)$ unrolls $\\mu$ and reassociates sequencing until the first action is on top.",
   "why": "Every rule reads the first action of a session type, so rules match on $\\mathsf{unfold}(S)$ and need no separate rule for $\\mu$.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{unfold}(\\mu\\alpha.\\,!\\ast.\\alpha) = !\\ast.(\\mu\\alpha.\\,!\\ast.\\alpha)$.",
   "rocq": "types/Types.v: unfoldS",
   "sig": "\\mathsf{unfold} : \\mathsf{STy} \\to \\mathsf{STy}",
   "args": [
    {
     "name": "S",
     "meaning": "A contractive session type, $\\mathsf{unfold}(S)$ has its first action on top."
    }
   ]
  },
  "sty.dual": {
   "title": "Duality",
   "what": "$\\mathsf{dual}$ swaps $!$ with $?$ and $\\oplus$ with $\\&$, keeps payloads, $\\mathsf{Skip}$ and $\\mathsf{Close}$, and $\\overline{S} := \\mathsf{dual}\\,S$.",
   "why": "The two ends of a channel run $S$ and $\\mathsf{dual}\\,S$, so every send meets a receive.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{dual}(!\\ast.\\mathsf{Close}) = ?\\ast.\\mathsf{Close}$.",
   "rocq": "types/Types.v: dual",
   "sig": "\\mathsf{dual} : \\mathsf{STy} \\to \\mathsf{STy}",
   "args": [
    {
     "name": "S",
     "meaning": "A session type."
    },
    {
     "name": "P",
     "meaning": "A payload, kept unchanged."
    },
    {
     "name": "S_1, S_2",
     "meaning": "Continuations."
    }
   ]
  },
  "sty.flip": {
   "title": "$\\mathsf{flip}_\\alpha$",
   "what": "$\\mathsf{flip}_\\alpha$ swaps $\\alpha$ and $\\overline{\\alpha}$ for the variable bound by the enclosing $\\mu$.",
   "why": "In $\\mu\\alpha.S$ the variable $\\alpha$ names the whole protocol. After dualizing $S$, the occurrences $\\overline{\\alpha}$ must name $\\mathsf{dual}(\\mu\\alpha.S)$, which is $\\alpha$ again.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{dual}(\\mu\\alpha.\\,!\\ast.\\alpha) = \\mu\\alpha.\\,?\\ast.\\alpha$.",
   "rocq": "types/Types.v: sflip",
   "sig": "\\mathsf{flip}_\\alpha : \\mathsf{STy} \\to \\mathsf{STy}",
   "args": [
    {
     "name": "\\alpha",
     "meaning": "The variable of the enclosing $\\mu$, whose occurrences $\\alpha$ and $\\overline{\\alpha}$ are swapped."
    }
   ]
  },
  "sty.sequiv": {
   "title": "Session equivalence $\\simeq$",
   "what": "The greatest relation with $S \\simeq S'$ only if $\\mathsf{unfold}(S)$ and $\\mathsf{unfold}(S')$ have the same first action, with equal annotations, and equivalent continuations.",
   "why": "One protocol has many spellings, unrolled or not. Rules compare protocols up to $\\simeq$.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mu\\alpha.\\,!\\ast.\\alpha \\simeq !\\ast.\\mu\\alpha.\\,!\\ast.\\alpha$.",
   "rocq": "types/Types.v: sequiv",
   "sig": "\\cdot \\simeq \\cdot \\subseteq \\mathsf{STy} \\times \\mathsf{STy}",
   "args": [
    {
     "name": "S, S'",
     "meaning": "Session types, related iff their unfoldings agree on first action and annotations and have related continuations."
    }
   ]
  },
  "ty2.stydf": {
   "title": "$\\mathsf{sty\\_df}$",
   "what": "$\\mathsf{sty\\_df}(S)$ sets every annotation of $S$ to its value at $N = \\infty$.",
   "why": "\\annp{Deadlock freedom and liveness read no credit, so two protocols that differ only in annotations are equal for them.}",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{sty\\_df}(!(\\ast^{2}).\\mathsf{Close}) = !(\\ast^{\\infty}).\\mathsf{Close}$.",
   "rocq": "types/Types.v: sty_df",
   "sig": "\\mathsf{sty\\_df} : \\mathsf{STy} \\to \\mathsf{STy}",
   "args": [
    {
     "name": "S",
     "meaning": "A session type."
    }
   ]
  },
  "sty.seqv": {
   "title": "Up to annotations $\\approx$",
   "what": "$S \\approx S' \\iff \\mathsf{sty\\_df}(S) \\simeq \\mathsf{sty\\_df}(S')$.",
   "why": "\\annp{The relations of deadlock freedom and liveness ignore credits, so one relation serves every counter bound $N$.}",
   "breaks": "Nothing. It is a definition.",
   "example": "$!(\\ast^{2}).\\mathsf{Close} \\approx !(\\ast^{\\infty}).\\mathsf{Close}$.",
   "rocq": "relation/Relation.v: seqv",
   "sig": "\\cdot \\approx \\cdot \\subseteq \\mathsf{STy} \\times \\mathsf{STy}",
   "args": [
    {
     "name": "S, S'",
     "meaning": "Session types compared after $\\mathsf{sty\\_df}$."
    }
   ]
  },
  "sty.sdual": {
   "title": "Dual up to annotations",
   "what": "$\\mathsf{sdual}\\,S\\,S'$ iff $S' \\approx \\mathsf{dual}\\,S$.",
   "why": "The relation pairs the two ends of a channel by $\\mathsf{sdual}$, consistent with comparing by $\\approx$.",
   "breaks": "Nothing. It is a definition.",
   "example": "A link of ends at $S$ and $S'$ asks $\\mathsf{sdual}\\,S\\,S'$.",
   "rocq": "relation/Relation.v: sdual",
   "sig": "\\mathsf{sdual} : \\mathsf{STy} \\to \\mathsf{STy} \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "S",
     "meaning": "The protocol of one end."
    },
    {
     "name": "S'",
     "meaning": "The protocol of its partner, $S' \\approx \\mathsf{dual}\\,S$."
    }
   ]
  },
  "ty.heads": {
   "title": "$\\mathsf{ap}$",
   "what": "$\\mathsf{ap}(T)$ is the set of dual points of the ends a value of $T$ holds. It is $\\{\\overline{x}\\}$ for $S@x$, $\\{l\\}$ for an arrow or existential with bound $l$, and $\\varnothing$ for bound $\\cdot$. For $\\otimes$ and $\\oplus$ it is the union. An existential at $\\bot$ contributes $\\bot$.",
   "why": "A thread blocked at $u$ while holding a value of $T$ needs $u \\prec y$ for every $y \\in \\mathsf{ap}(T)$, or the partner of a held end may wait on the thread. With $\\bot$ in the set this fails, which is what hidden ends require.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{ap}(\\mathsf{Close}@\\rho \\otimes \\mathsf{Close}@\\rho\\cdot 0) = \\{\\overline{\\rho}, \\overline{\\rho\\cdot 0}\\}$ and $\\mathsf{ap}(\\exists^{\\bot}\\iota.\\,C.\\,T) = \\{\\bot\\}$.",
   "rocq": "types/Types.v: heads, hbot",
   "sig": "\\mathsf{ap} : \\mathsf{Ty} \\to \\mathcal{P}_{\\mathrm{fin}}(\\mathsf{Point} \\cup \\{\\bot\\})",
   "args": [
    {
     "name": "T",
     "meaning": "A type."
    }
   ]
  },
  "ty.botord": {
   "title": "$\\bot$ in the order",
   "what": "No fact relates $\\bot$ to a point, $\\Gamma \\nvdash x \\prec \\bot$ and $\\Gamma \\nvdash \\bot \\preccurlyeq y$.",
   "why": "Hidden ends are at points that no fact outside the existential mentions. A holding thread of such ends can be ordered against nothing, so it may not block.",
   "breaks": "Nothing. It is a definition.",
   "example": "$x \\prec \\{\\overline{\\rho}, \\bot\\}$ fails for every $x$.",
   "rocq": "types/Types.v: hbot; static/Contexts.v: sf_unionb, lbx_below_h",
   "sig": "\\Gamma \\nvdash x \\prec \\bot,\\ \\Gamma \\nvdash \\bot \\preccurlyeq y",
   "args": [
    {
     "name": "x, y",
     "meaning": "points"
    }
   ]
  },
  "ty.lbound": {
   "title": "Lower bounds $l$",
   "what": "$l ::= \\cdot \\mid \\bot \\mid x$, absent, unknown, or a point.",
   "why": "It records which facts about the points of the hidden ends are available to a holding thread.",
   "breaks": "Nothing. It is a definition.",
   "example": "$l = \\bot$ for $\\mathsf{new}_\\ell$.",
   "rocq": "types/Points.v: lbound",
   "sig": "l \\in \\mathsf{LBound} = \\{\\cdot, \\bot\\} \\cup \\mathsf{Point}",
   "args": []
  },
  "ty.payload-at": {
   "title": "$\\mathsf{payload\\_at}$",
   "what": "$\\mathsf{payload\\_at}\\,m\\,T\\,x = T[x\\cdot 0, \\ldots, x\\cdot(m{-}1) / \\iota_0, \\ldots, \\iota_{m-1}]$.",
   "why": "$\\overline{x}\\cdot j = x\\cdot j$, so sender at $x$ and receiver at $\\overline{x}$ compute the same payload type.",
   "breaks": "Nothing. It is a definition.",
   "example": "A payload $\\alpha @\\iota_0$ sent at $Y$ has type $\\alpha @Y\\cdot 0$.",
   "rocq": "types/Types.v: payload_at",
   "sig": "\\mathsf{payload\\_at} : \\mathbb{N} \\to \\mathsf{Ty} \\to \\mathsf{Point} \\to \\mathsf{Ty}",
   "args": [
    {
     "name": "m",
     "meaning": "The number of point variables of the payload."
    },
    {
     "name": "T",
     "meaning": "The payload type over $\\iota_0, \\ldots, \\iota_{m-1}$."
    },
    {
     "name": "x",
     "meaning": "The point of the carrier end."
    }
   ]
  },
  "ty.pscoped": {
   "title": "$\\mathsf{pscoped}$",
   "what": "$\\mathsf{pscoped}\\,\\bar\\iota\\,T$ iff every point variable of $T$ is among $\\bar\\iota$.",
   "why": "A payload mentions only its own point variables, so unrolling a $\\mu$ never captures an outer point.",
   "breaks": "A free outer point inside a $\\mu$-body is captured on unrolling, and point substitution changes its meaning.",
   "example": "$\\mathsf{pscoped}\\,\\iota_0\\,(S@\\iota_0)$.",
   "rocq": "types/Types.v: pscoped",
   "sig": "\\mathsf{pscoped} : \\mathsf{PVar}^{*} \\to \\mathsf{Ty} \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "\\bar\\iota",
     "meaning": "The point variables the payload binds."
    },
    {
     "name": "T",
     "meaning": "The payload type."
    }
   ]
  },
  "ann.fuel": {
   "title": "Numbers with $\\infty$",
   "what": "Credits, costs, counters, tickets and the bound $N$ range over $\\mathbb{N} \\cup \\{\\infty\\}$, where $\\infty$ means unbounded and $\\infty - c = \\infty$.",
   "why": "Deadlock-free typing sets every annotation to $\\infty$. Then a held end remains arbitrarily many actions, and the checks on credits hold.",
   "breaks": "Nothing. It is a definition.",
   "example": "A credit $\\infty$ aged by $3$ stays $\\infty$.",
   "rocq": "types/Costs.v: fuel",
   "sig": "\\mathbb{N} \\cup \\{\\infty\\}",
   "args": []
  },
  "ty.tickets": {
   "title": "Tickets $m$",
   "what": "$m \\in \\mathbb{N} \\cup \\{\\infty\\}$ on an end type $(S@x)\\annot{^{a}}_{m}$ bounds the counter of the end from above, and the credit satisfies $a \\leq m$. An action on the end sets its counter back to $m$, and the tickets stay with the end, also in a payload.",
   "why": "The thread holding the partner of an end acts on other ends at most as often as the counter of the partner allows, and the tickets of the partner bound that counter. A link compares the credit of one end with this bound, so the new partner of a waiting thread has a lower counter than the old one.",
   "breaks": "Without tickets a link can give a waiting thread a partner with a full counter in every round, and the wait never ends.",
   "example": "A new channel at $N = 4$ may give its ends $3$ and $1$ tickets.",
   "rocq": "types/Types.v: TSess",
   "sig": "m \\in \\mathbb{N} \\cup \\{\\infty\\}",
   "args": [
    {
     "name": "m",
     "meaning": "The tickets of an end, the value an action resets its counter to."
    },
    {
     "name": "a",
     "meaning": "The credit of the end, $a \\leq m$.",
     "ann": true
    }
   ]
  },
  "ann.tsum": {
   "title": "$\\mathsf{tk}(o) + \\mathsf{tk}(\\overline{o}) \\leq N$",
   "what": "The tickets of the two ends of a channel sum to at most $N$, the bound of the judgment. An end with $m$ tickets has a partner with at most $N - m$ tickets, a bound read off its own type.",
   "why": "E-Link compares the credit of each linked end with the partner bound of the other. Then the new partner of each waiting thread has a counter below the counter of the old one, and the measure of lock-free adequacy falls at every link.",
   "breaks": "Without the bound no premise of a link relates the counters of ends that other threads hold, and relinking a waiting end forever is accepted.",
   "example": "At $N = 4$ the two ends of a channel have $3$ and $1$ or $2$ and $2$ tickets.",
   "rocq": "types/Costs.v: tsum_ok",
   "sig": "\\mathsf{tk}(o) + \\mathsf{tk}(\\overline{o}) \\leq N : \\mathsf{Prop}",
   "args": [
    {
     "name": "o",
     "meaning": "An end of a channel and $\\overline{o}$ its partner."
    },
    {
     "name": "\\mathsf{tk}(o)",
     "meaning": "The tickets $m$ of $o$, read off its type $(S@x)\\annot{^{a}}_{m}$."
    },
    {
     "name": "N",
     "meaning": "The bound of the judgment."
    }
   ]
  },
  "ann.tydf": {
   "title": "$\\mathsf{ty\\_df}$",
   "what": "$\\mathsf{ty\\_df}(T)$ is $T$ with every annotation at its unbounded value. Credits, costs and tickets become $\\infty$.",
   "why": "Deadlock-free typing is the annotated typing at counter bound $N = \\infty$ with these annotations. One set of rules then serves both systems, and every premise about annotations holds at $\\infty$.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{ty\\_df}((S@x)^{3}) = (S@x)^{\\infty}$.",
   "rocq": "types/Types.v: ty_df",
   "sig": "\\mathsf{ty\\_df} : \\mathsf{Ty} \\to \\mathsf{Ty}",
   "args": [
    {
     "name": "T",
     "meaning": "A type."
    }
   ]
  },
  "ty.unlimited": {
   "title": "$\\mathsf{unlimited}$",
   "what": "$\\mathsf{unlimited}\\,T$ iff $T$ is a box type, so its variables admit weakening and contraction.",
   "why": "$V$ at a box type asks $\\Theta = \\varnothing$, so copying or dropping the value duplicates or loses no end.",
   "breaks": "Nothing. It is a definition.",
   "example": "The self of a box is unlimited.",
   "rocq": "types/Types.v: unlimited",
   "sig": "\\mathsf{unlimited} : \\mathsf{Ty} \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "T",
     "meaning": "A type."
    }
   ]
  },
  "ty.tfree": {
   "title": "$\\mathsf{tfree}$",
   "what": "$\\mathsf{tfree}\\,T$ iff $T$ is built from $\\ast$, boxes, $\\otimes$ and $\\oplus$. A value of such a type holds no end, because $V$ at a box asks $\\Theta = \\varnothing$.",
   "why": "Aging and capture leave an entry at a $\\mathsf{tfree}$ type unchanged. P-Term asks it of the result, so no partner waits on the result of a process.",
   "breaks": "A main thread that returns an end holds it forever, and its partner waits forever.",
   "example": "$\\mathsf{tfree}(\\ast \\otimes \\Box\\ldots)$.",
   "rocq": "types/Types.v: tfree",
   "sig": "\\mathsf{tfree} : \\mathsf{Ty} \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "T",
     "meaning": "A type."
    }
   ]
  },
  "w.world": {
   "title": "Static world",
   "what": "$W = (A, \\prec_A)$, roots and facts.",
   "why": "Typing reads the order $\\prec_W$ that $W$ generates. The relation reads ranked worlds $R$ with $R \\vDash W$, and a creation adds the ranks of its fresh root.",
   "breaks": "Nothing. It is a definition.",
   "example": "$W$ with $A = \\{1, 2\\}$ and the fact $1 \\prec \\overline{2}$.",
   "rocq": "types/Worlds.v: world",
   "sig": "W = (A, \\prec_A) \\in \\mathsf{World}",
   "args": [
    {
     "name": "A",
     "meaning": "The roots."
    },
    {
     "name": "\\prec_A",
     "meaning": "The facts."
    }
   ]
  },
  "w.rworld": {
   "title": "Ranked world",
   "what": "$R = (A, \\varrho)$, a finite set $A$ of roots and for each root $a$ a rank function $\\varrho_a$ on $\\mathsf{tree}(a)$.",
   "why": "The relation reads the order of points through ranks. Ranks are ordinals, so the order of a ranked world is well-founded and acyclic, and no premise on the world remains.",
   "breaks": "With a symbolic order the union of the worlds of a run may hold an infinite descending chain, and lock-free adequacy then needs a premise that no typing rule checks.",
   "example": "$R$ with $A = \\{\\rho\\}$ and $\\varrho(\\rho + k) = \\omega \\cdot k$.",
   "rocq": "types/Worlds.v: world",
   "sig": "R = (A, \\varrho) \\in \\mathsf{RWorld}",
   "args": [
    {
     "name": "A",
     "meaning": "The roots."
    },
    {
     "name": "\\varrho",
     "meaning": "A rank function for the tree of each root."
    }
   ]
  },
  "w.rank": {
   "title": "Rank function $\\varrho_a$",
   "what": "A map from $\\mathsf{tree}(a)$ to the ordinals with $\\varrho_a(x) < \\varrho_a(x^{+})$ and $\\varrho_a(x) < \\varrho_a(\\overline{x}^{+})$ for each $x$.",
   "why": "A creation at a fresh root ranks the whole tree of the root, fields included, so a later creation at a field finds its ranks fixed and picks nothing. Ordinals leave no room between $\\alpha$ and $\\alpha + 1$, so the room for later fields is fixed at the root.",
   "breaks": "If a root ranked only its own shifts, a field creation could need a rank strictly between $k + 1$ and $k + 2$, and no ordinal exists there.",
   "example": "Client and server rank $\\rho + k$ at $\\omega \\cdot k$ and $\\rho\\cdot 0 + k$ at $\\omega \\cdot k + 1$.",
   "rocq": "types/Worlds.v: w_rank, w_po",
   "sig": "\\varrho_a : \\mathsf{tree}(a) \\to \\mathsf{Ord}",
   "args": [
    {
     "name": "a",
     "meaning": "A root of $A$."
    },
    {
     "name": "x",
     "meaning": "A point of $\\mathsf{tree}(a)$."
    }
   ]
  },
  "w.tree": {
   "title": "Tree $\\mathsf{tree}(a)$",
   "what": "The points whose root is $a$, that is $a$, its shifts, its dual and its fields at each depth with their shifts and duals.",
   "why": "A rank function is chosen for the whole tree of a root at once.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\rho\\cdot 0^{+} \\in \\mathsf{tree}(\\rho)$.",
   "rocq": "static/Contexts.v: in_tree0; types/Points.v: pt_unroot",
   "sig": "\\mathsf{tree} : \\mathsf{Root} \\to \\mathcal{P}(\\mathsf{Point})",
   "args": [
    {
     "name": "a",
     "meaning": "A root."
    }
   ]
  },
  "w.rlt": {
   "title": "Order of a ranked world",
   "what": "$R \\vDash x \\prec y$ iff $\\varrho(x) < \\varrho(y)$.",
   "why": "Readiness and the obligations compare points in the ranked world. The order is transitive and well-founded because $<$ on ordinals is.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\varrho(\\rho) = 0 < \\omega = \\varrho(\\rho\\cdot 1)$ gives $R \\vDash \\rho \\prec \\rho\\cdot 1$.",
   "rocq": "types/Worlds.v: w_lt, w_lt_wf",
   "sig": "R \\vDash \\cdot \\prec \\cdot \\subseteq \\mathsf{Point} \\times \\mathsf{Point}",
   "args": [
    {
     "name": "R",
     "meaning": "A ranked world."
    },
    {
     "name": "x, y",
     "meaning": "Points."
    }
   ]
  },
  "w.sat": {
   "title": "Satisfaction $R \\vDash W$",
   "what": "Each fact of $W$ holds under the ranks of $R$.",
   "why": "The semantic judgments at a static world $W$ read the relation at each ranked world $R$ with $R \\vDash W$. Static entailment is sound in such $R$, so each fact a derivation uses holds in $R$.",
   "breaks": "Nothing. It is a definition.",
   "example": "A world with no facts is satisfied by each ranked world with its roots.",
   "rocq": "types/Worlds.v: wmodels",
   "sig": "\\cdot \\vDash \\cdot \\subseteq \\mathsf{RWorld} \\times \\mathsf{World}",
   "args": [
    {
     "name": "R",
     "meaning": "A ranked world."
    },
    {
     "name": "W",
     "meaning": "A world."
    }
   ]
  },
  "w.po": {
   "title": "Program order $\\mathsf{po}$",
   "what": "The facts $x \\prec x^{+}$ and $x \\prec \\overline{x}^{+}$ for each point $x$.",
   "why": "A rank function satisfies program order by definition, so a creation must rank program order together with its facts.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\rho \\prec \\rho^{+} \\in \\mathsf{po}$.",
   "rocq": "types/Worlds.v: po, w_po",
   "sig": "\\mathsf{po} \\subseteq \\mathsf{Point} \\times \\mathsf{Point}",
   "args": [
    {
     "name": "x",
     "meaning": "A point."
    }
   ]
  },
  "w.wfnew": {
   "title": "$\\mathsf{wf\\_new}\\,\\rho\\,C$",
   "what": "Each fact of $C$ ends in $\\mathsf{tree}(\\rho)$, and $C$ with program order is well-founded on $\\mathsf{tree}(\\rho)$.",
   "why": "A creation at a fresh root must find ranks for the new tree in each ranked world that satisfies its context. Facts from context points up into the new tree are met by ranks above the context points below the tree, and ranks inside the tree exist exactly when the order there is well-founded.",
   "breaks": "A fact from a new point down to a context point fails at a context point of rank $0$. A chain of creations each below the previous one would need an infinite descending chain of ordinals.",
   "example": "$\\{\\rho \\prec \\overline{\\rho\\cdot 0},\\ \\overline{\\rho} \\prec \\rho\\cdot 0\\}$ satisfies $\\mathsf{wf\\_new}\\,\\rho$.",
   "rocq": "static/Contexts.v: wf_new, new_step",
   "sig": "\\mathsf{wf\\_new} : \\mathsf{PVar} \\to \\mathcal{P}(\\mathsf{Point} \\times \\mathsf{Point}) \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "\\rho",
     "meaning": "The fresh root, a point variable bound by the existential of $\\mathsf{new}$."
    },
    {
     "name": "C",
     "meaning": "The facts of the creation."
    }
   ]
  },
  "w.consts": {
   "title": "Roots $A$",
   "what": "$A$ is the finite set of roots of $W$.",
   "why": "Facts mention only points with roots in $A$, and composition compares two worlds through $A_1 \\cap A_2$.",
   "breaks": "Nothing. It is a definition.",
   "example": "$A = \\{1, 2\\}$.",
   "rocq": "types/Worlds.v: w_consts",
   "sig": "A \\in \\mathcal{P}_{\\mathrm{fin}}(\\mathsf{Root})",
   "args": []
  },
  "w.facts": {
   "title": "Facts $\\prec_A$",
   "what": "A set of facts $x \\prec y$, possibly infinite, between points whose roots lie in $A$.",
   "why": "They order the channels a component shares with its environment and the channels created so far.",
   "breaks": "Nothing. It is a definition.",
   "example": "$1 \\prec \\overline{2}$.",
   "rocq": "types/Worlds.v: w_facts",
   "sig": "\\prec_A \\subseteq \\mathsf{Point} \\times \\mathsf{Point}",
   "args": []
  },
  "w.lt": {
   "title": "$\\prec_W$",
   "what": "$\\prec_W$ is the transitive closure of the three generators, and $W \\vdash x \\prec y$ means $x \\prec_W y$.",
   "why": "A waiting chain combines several facts, so the order is transitive.",
   "breaks": "Nothing. It is a definition.",
   "example": "$W \\vdash x \\prec x^{++}$.",
   "rocq": "types/Worlds.v: w_lt",
   "sig": "W \\vdash \\cdot \\prec \\cdot \\subseteq \\mathsf{Point} \\times \\mathsf{Point}",
   "args": [
    {
     "name": "W",
     "meaning": "A world."
    },
    {
     "name": "x, y",
     "meaning": "Points."
    }
   ]
  },
  "w.ws-fact": {
   "title": "Facts generator",
   "what": "$x \\prec_A y$ implies $x \\prec_W y$.",
   "why": "A plain generator. The facts of $W$ hold in $\\prec_W$.",
   "breaks": "Nothing. It is a definition.",
   "example": "$1 \\prec_W \\overline{2}$.",
   "rocq": "types/Worlds.v: ws_fact",
   "sig": "x \\prec_A y \\Rightarrow x \\prec_W y",
   "args": [
    {
     "name": "x, y",
     "meaning": "Points."
    }
   ]
  },
  "w.ws-po": {
   "title": "$x \\prec x^{+}$",
   "what": "For every $x$, $x \\prec_W x^{+}$.",
   "why": "An end acts at $x$ before it acts at $x^{+}$, so $\\prec_W$ contains the program order of each end.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\rho \\prec \\rho^{+}$.",
   "rocq": "types/Worlds.v: ws_po",
   "sig": "\\forall x.\\ x \\prec_W x^{+}",
   "args": [
    {
     "name": "x",
     "meaning": "Any point."
    }
   ]
  },
  "ty2.le": {
   "title": "Order or equal $\\preceq$",
   "what": "$x \\preceq y$ iff $x = y$ or $x \\prec_W y$.",
   "why": "Lower bounds compare by $\\preceq$, so a closure whose only captured end has dual point $l$ may have lower point $l$.",
   "breaks": "Nothing. It is a definition.",
   "example": "A closure capturing $a^{+}$ at $\\rho$ has $l = \\overline{\\rho}$ and $\\overline{\\rho} \\preceq \\overline{\\rho}$.",
   "rocq": "types/Worlds.v: w_le",
   "sig": "\\cdot \\preceq \\cdot \\subseteq \\mathsf{Point} \\times \\mathsf{Point}",
   "args": [
    {
     "name": "x, y",
     "meaning": "Points."
    }
   ]
  },
  "w.ws-dpo": {
   "title": "$x \\prec \\overline{x}^{+}$",
   "what": "For every $x$, $x \\prec_W \\overline{x}^{+}$.",
   "why": "The fact holds in every run. The action at $x$ synchronizes with the partner at $\\overline{x}$, and the partner acts at $\\overline{x}^{+}$ only afterwards, so $W$ may contain it for free.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\rho \\prec \\overline{\\rho}^{+}$.",
   "rocq": "types/Worlds.v: ws_dpo",
   "sig": "\\forall x.\\ x \\prec_W \\overline{x}^{+}",
   "args": [
    {
     "name": "x",
     "meaning": "Any point."
    }
   ]
  },
  "w.wf": {
   "title": "$\\mathsf{world\\_wf}$",
   "what": "$\\mathsf{world\\_wf}\\,W$ iff every fact of $\\prec_A$ relates points with roots in $A$.",
   "why": "A fact outside $A$ mentions a point no component owns.",
   "breaks": "Nothing. It is a definition.",
   "example": "A fact $1 \\prec 3$ with $3 \\notin A$ violates the property.",
   "rocq": "types/Worlds.v: world_wf",
   "sig": "\\mathsf{world\\_wf} : \\mathsf{World} \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "W",
     "meaning": "A world."
    }
   ]
  },
  "w.lfworld": {
   "title": "$\\mathsf{wf}$",
   "what": "$\\mathsf{wf}\\,W$ iff $\\prec_W$ is well-founded, so no infinite chain $\\cdots \\prec x_2 \\prec x_1 \\prec x_0$ exists.",
   "why": "A static world has a ranked world that satisfies it exactly when its order is well-founded, and the rank function of $\\prec_W$ is that ranked world. P-Term and P-Connect ask it, so the world of each process derivation is well-founded.",
   "breaks": "A cycle or an infinite descending chain in $\\prec_W$ admits no ranks, and the semantic judgment at $W$ would hold vacuously.",
   "example": "$W$ with no facts satisfies $\\mathsf{wf}\\,W$.",
   "rocq": "types/Worlds.v: swf, wmodels_exists",
   "sig": "\\mathsf{wf} : \\mathsf{World} \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "W",
     "meaning": "A world."
    }
   ]
  },
  "w.ext": {
   "title": "Extension $\\sqsubseteq$",
   "what": "$W \\sqsubseteq W'$ iff $A \\subseteq A'$ and each fact of $W$ is a fact of $W'$. For ranked worlds $R \\sqsubseteq R'$ iff $A \\subseteq A'$ and $\\varrho'$ agrees with $\\varrho$ on the trees of $A$.",
   "why": "No rank changes once chosen, so each fact true in $R$ stays true in each $R' \\sqsupseteq R$, and the relation is monotone in the world.",
   "breaks": "Nothing. It is a definition.",
   "example": "$R \\sqsubseteq R \\oplus (a, \\varrho_a)$ and $W \\sqsubseteq W \\sqcup W'$.",
   "rocq": "types/Worlds.v: swext, wext",
   "sig": "\\cdot \\sqsubseteq \\cdot \\subseteq \\mathsf{World}^{2} \\cup \\mathsf{RWorld}^{2}",
   "args": [
    {
     "name": "W, W'",
     "meaning": "The smaller and the larger static world."
    },
    {
     "name": "R, R'",
     "meaning": "The smaller and the larger ranked world."
    }
   ]
  },
  "w.grow": {
   "title": "Growth $R \\oplus (a, \\varrho_a)$",
   "what": "$R \\oplus (a, \\varrho_a)$ adds the fresh root $a$ to $A$ and its rank function $\\varrho_a$ to $\\varrho$.",
   "why": "A creation at a fresh root ranks the new tree, so the ranked world of a run grows with each root creation and never changes a rank. The union of the worlds of a run is one rank assignment, which lock-free adequacy uses as its measure.",
   "breaks": "If ranks could change along a run, the measure of a waiting thread could rise.",
   "example": "$R \\oplus (\\rho, \\varrho_\\rho)$ with $\\varrho_\\rho(x) = \\sigma + \\rho_C(x)$ for $\\sigma$ above each context point below the tree.",
   "rocq": "types/Worlds.v: wgrow; compat/Redex.v: Erel_new",
   "sig": "\\cdot \\oplus \\cdot : \\mathsf{RWorld} \\to \\mathsf{Root} \\times (\\mathsf{Point} \\to \\mathsf{Ord}) \\to \\mathsf{RWorld}",
   "args": [
    {
     "name": "R",
     "meaning": "A ranked world."
    },
    {
     "name": "a",
     "meaning": "The fresh root, $a \\notin A$."
    },
    {
     "name": "\\varrho_a",
     "meaning": "Its rank function on $\\mathsf{tree}(a)$."
    }
   ]
  },
  "w.join": {
   "title": "Join $\\sqcup$",
   "what": "$W_1 \\sqcup W_2$ takes the unions of roots and facts.",
   "why": "Two components typed in $W_1$ and $W_2$ compose in $W_1 \\sqcup W_2$.",
   "breaks": "Nothing. It is a definition.",
   "example": "$W \\sqsubseteq W \\sqcup W'$ and $W' \\sqsubseteq W \\sqcup W'$.",
   "rocq": "types/Worlds.v: wjoin",
   "sig": "\\cdot \\sqcup \\cdot : \\mathsf{World} \\to \\mathsf{World} \\to \\mathsf{World}",
   "args": [
    {
     "name": "W_1, W_2",
     "meaning": "The worlds of two components."
    }
   ]
  },
  "w.restrict": {
   "title": "Restriction $W|_S$",
   "what": "$W|_S$ has the facts $x \\prec_W y$ with roots of $x, y$ in $S$.",
   "why": "It is the derived order of $W$ on the points of the shared roots $S$, chains through private points included, and the only order a component exposes to another.",
   "breaks": "Nothing. It is a definition.",
   "example": "$W|_{A_1 \\cap A_2}$.",
   "rocq": "types/Worlds.v: wrestrict",
   "sig": "\\cdot|_{\\cdot} : \\mathsf{World} \\to \\mathcal{P}(\\mathsf{Root}) \\to \\mathsf{World}",
   "args": [
    {
     "name": "W",
     "meaning": "A world."
    },
    {
     "name": "S",
     "meaning": "A set of constants, instantiated with $A_1 \\cap A_2$."
    }
   ]
  },
  "w.R7": {
   "title": "Well-founded join",
   "what": "$\\mathsf{wf}(W_1 \\sqcup W_2)$ iff $\\mathsf{wf}\\,W_1$, $\\mathsf{wf}\\,W_2$ and $\\mathsf{wf}(W_1|_S \\sqcup W_2|_S)$ for $S = A_1 \\cap A_2$.",
   "why": "A descending chain of the join that meets shared points infinitely often gives a descending chain of the amalgam, and one that meets them finitely often ends in one private zone. So well-foundedness of the join is decided on the shared roots alone.",
   "breaks": "Nothing. It is a definition.",
   "example": "Two well-founded worlds with $A_1 \\cap A_2 = \\varnothing$ have a well-founded join.",
   "rocq": "types/Worlds.v: wf_join_iff",
   "sig": "\\mathsf{wf}(W_1 \\sqcup W_2) \\iff \\ldots",
   "args": [
    {
     "name": "W_1, W_2",
     "meaning": "Two well-formed worlds."
    },
    {
     "name": "S",
     "meaning": "The shared roots $A_1 \\cap A_2$."
    }
   ]
  },
  "tj.Gamma": {
   "title": "$\\Gamma$, facts",
   "what": "$\\Gamma$ is a list of constraint instances $(C, \\bar x)$.",
   "why": "Every order fact a rule may use beyond $\\prec_W$ is recorded in $\\Gamma$. The derivable facts are exactly the judgments $\\Gamma \\vdash x \\prec y$.",
   "breaks": "Nothing. It is a definition.",
   "example": "In the body of the client loop $\\Gamma$ holds $(C, [\\iota, \\kappa, \\zeta])$.",
   "rocq": "static/Contexts.v: hctx",
   "sig": "\\Gamma : (\\mathsf{Bcs} \\times \\mathsf{Pt}^{*})^{*}",
   "args": [
    {
     "name": "(C, \\bar x)",
     "meaning": "a constraint $C$ instantiated at the list of points $\\bar x$"
    }
   ]
  },
  "tj.hage": {
   "title": "$\\mathsf{def}(H - c)$, aging what is held",
   "what": "$H - c$ ages every entry of $H$ by the cost $c$ of $e$. It is defined when every end and closure in $H$ that is not idle has credit at least $c$.",
   "why": "The thread holds $H$ while $e$ runs, and each of the up to $c$ actions of $e$ lowers the counters of the held ends by $1$.",
   "breaks": "Without it a thread holds an end across unboundedly many actions on other ends, and the partner of that end waits without bound.",
   "example": "$(S@x)^{2} - 1 = (S@x)^{1}$ is defined, $(S@x)\\annot{^{0}} - 1$ is not.",
   "rocq": "static/Contexts.v: thage, lage",
   "sig": "H - c",
   "args": [
    {
     "name": "H",
     "meaning": "the entries the thread holds while $e$ runs, a context or a type"
    },
    {
     "name": "c",
     "meaning": "the cost of $e$"
    }
   ]
  },
  "lfi.credit": {
   "title": "Credits, a bound on postponement",
   "what": "Every end has a counter at run time, the number of actions the thread holding it may still perform on other ends before it must act on this one. The credit $a$ in $(S@x)\\annot{^{a}}$ is a lower bound on that counter, known statically. A closure has a credit too, because the ends it captured are invisible in its type.",
   "why": "A partner waiting on an end needs the holding thread to act on it eventually. If every action elsewhere lowers the counter and the counter must stay non-negative, the holding thread can only postpone the end finitely often.",
   "breaks": "Postponement in the Examples tab holds $b$ across a loop that never returns, so $\\mathsf{close}\\,b'$ waits forever. The loop has cost $\\infty$, and no credit is large enough.",
   "example": "$(S@x)^{3}$ may be held across three actions on other ends.",
   "rocq": "types/Types.v: TSess, TLolli; fuel/Fuel.v: f_act",
   "sig": "(S@x)\\annot{^{a}},\\ (T \\multimap U)\\annot{^{a}},\\ a \\in \\mathbb{N} \\cup \\{\\infty\\}",
   "args": [
    {
     "name": "a",
     "meaning": "a lower bound on the counter of the end, or of the ends a closure captured"
    }
   ]
  },
  "lfi.cost": {
   "title": "Cost, aging and tickets, the counting",
   "what": "The cost $c$ of a term bounds its actions before it returns. Every rule that runs a subterm while holding $\\Delta$ ages $\\Delta$ by that cost, $\\Delta - c$, which asks each credit to be at least the cost. An action on an end resets its counter to its tickets $m$, so the end returns as $(S@x^{+})^{m}_{m}$. Idle ends, $\\mathsf{Skip}$, age without the check, because no thread waits on an idle end.",
   "why": "Credits bound postponement only if the holding thread's actions lower the credits. The cost says how much, aging applies it to everything held, and the reset starts the count again after the holding thread acted on the end.",
   "breaks": "Without the reset a long-running protocol would run out of credit after $m$ actions.",
   "example": "$\\langle c, \\mathsf{send}\\,\\langle\\ast, d\\rangle\\rangle$ ages $c$ by $1$ while the send on $d$ runs.",
   "rocq": "static/Typing.v: typed; static/Contexts.v: tage, lage",
   "sig": "e : T\\ !\\ c,\\ \\Delta - c,\\ (S@x^{+})^{m}_{m}",
   "args": [
    {
     "name": "c",
     "meaning": "the cost, an upper bound on the actions of $e$"
    },
    {
     "name": "m",
     "meaning": "the tickets of the acted end"
    }
   ]
  },
  "lfi.hop": {
   "title": "Transfers, a passed end loses one",
   "what": "Every time an end is transferred to another thread, by a send or a spawn, its counter drops by $1$. A send asks $T' - 1 \\leq T[x\\cdot i]$ of the payload, a spawned body sees $\\Delta - 1$, and spawning a closure asks its credit $a \\geq 1$.",
   "why": "Transferring an end on is not an action on it, so it does not counter bound. Without the loss an end could be sent between threads forever and its partner would never be served.",
   "breaks": "Endless delegation in the Examples tab sends $e$ back and forth forever while $e'$ waits. After finitely many transfers no credit is left to send it again.",
   "example": "An end at credit $3$ can be passed on three times before a thread must act on the end.",
   "rocq": "static/Typing.v: e_send, e_spawn_lam, e_spawn",
   "sig": "T' - 1 \\leq T[x\\cdot i],\\ \\Delta - 1,\\ a \\geq 1",
   "args": [
    {
     "name": "T'",
     "meaning": "the type of a payload value"
    }
   ]
  },
  "lfi.tickets": {
   "title": "Tickets, one number per end",
   "what": "An end of type $(S@x)\\annot{^{a}}_{m}$ has tickets $m \\geq a$, an upper bound on its counter. An action on the end sets its counter back to $m$, and a send of the end as payload lowers its counter by one. The two ends of a channel have at most $N$ tickets together, so the partner of an end with $m$ tickets has at most $N - m$. E-Link asks $a_1 + m_2 > N$ and $a_2 + m_1 > N$.",
   "why": "A link acts on no end, so no counter falls at a link, and it gives the waiting thread a new partner. The premise of E-Link makes the counter of the new partner lower than the counter of the old one, so the measure of lock-free adequacy falls at every link.",
   "breaks": "Link refresh in the Examples tab relinks the partner of a waiting end to a new channel every round. The new end has a full counter, and no typing of the loop meets the premise of E-Link.",
   "example": "At $N = 4$ a link of ends with credits $3$ and $3$ and tickets $3$ and $3$ satisfies $3 + 3 > 4$ twice.",
   "rocq": "static/Typing.v: e_link, e_send; types/Costs.v: lgt",
   "sig": "(S@x)\\annot{^{a}}_{m},\\ a \\leq m,\\ \\mathsf{tk}(o) + \\mathsf{tk}(\\overline{o}) \\leq N",
   "args": [
    {
     "name": "m",
     "meaning": "the tickets of an end, an upper bound on its counter"
    },
    {
     "name": "N",
     "meaning": "the bound of the judgment"
    }
   ]
  },
  "lfi.guard": {
   "title": "The guard, no recursion before an action",
   "what": "$\\Lambda \\vdash\\!\\triangleright t$ asks that a box calls itself only after a session action. It is a syntactic check on terms.",
   "why": "Internal steps, $\\beta$, $\\mathsf{new}$ and $\\mathsf{spawn}$, cost no counter. A loop made only of them would step forever without ever serving anyone, which deadlock freedom allows and lock freedom does not.",
   "breaks": "Guard rejections in the Examples tab, e.g. $!(f = \\mathsf{force}\\,f)$ and a box that spawns itself forever.",
   "example": "$!(f = \\lambda x.\\, \\mathsf{let}\\ \\langle v, x\\rangle = \\mathsf{recv}\\,x\\ \\mathsf{in}\\ (\\mathsf{force}\\,f)\\,x)$ is guarded.",
   "rocq": "static/Guard.v: lguard",
   "sig": "\\Lambda \\vdash\\!\\triangleright t",
   "args": [
    {
     "name": "\\Lambda",
     "meaning": "the marks, which variables are boxes not yet allowed to recur"
    }
   ]
  },
  "lfi.wf": {
   "title": "A well-founded world, ranks",
   "what": "A ranked world gives each point an ordinal rank, and $x \\prec y$ holds iff the rank of $x$ is below the rank of $y$. E-New asks $\\mathsf{wf\\_new}$ at a fresh root, P-Term and P-Connect ask $\\mathsf{wf}$ of the static world, and lock-free adequacy has no premise on the world.",
   "why": "A waiting thread waits on a holding thread whose own waiting point lies lower. Ranks are ordinals, so this chain ends, and someone at the bottom can act.",
   "breaks": "A waiting chain that grows forever, in the Examples tab, creates each channel below the previous one, and E-New rejects that creation.",
   "example": "Client and server rank its points below $\\omega^{2} + 2$.",
   "rocq": "types/Worlds.v: world, w_lt; soup/LFAdequacy.v: lf_adequacy",
   "sig": "\\varrho_a : \\mathsf{tree}(a) \\to \\mathsf{Ord}",
   "args": [
    {
     "name": "a",
     "meaning": "a root of the ranked world"
    }
   ]
  },
  "lfi.measure": {
   "title": "The measure, rank of the awaited end",
   "what": "A pending thread $t$ waiting on the end $o$ is ranked by $\\varrho(\\mathsf{pt}\\,o)$, the ordinal of the point of $o$ in the ranked world of the run, and then by the counter of $\\overline{o}$.",
   "why": "The thread holding $\\overline{o}$ either acts or waits on an end whose point lies below, so the rank falls along each chain of waits. Within one rank the counter of $\\overline{o}$ falls at each step of that thread on other ends and at each link.",
   "breaks": "Without ranks a chain of waits could descend forever along an infinite chain of points.",
   "example": "A thread waiting on $c$ at $\\rho$ with $\\varrho(\\rho) = \\omega$.",
   "rocq": "soup/LFAdequacy.v: we, lf_rank, lf_adequacy",
   "sig": "\\varrho(\\mathsf{pt}\\,o) \\in \\mathsf{Ord}",
   "args": [
    {
     "name": "o",
     "meaning": "the end the pending thread waits on"
    },
    {
     "name": "\\mathsf{pt}\\,o",
     "meaning": "its point, recorded in the ownership map"
    }
   ]
  },
  "tj.held": {
   "title": "Holding $F \\triangleleft H$",
   "what": "$\\Delta \\vdash^{F \\triangleleft H} e$ types $e$ while the thread holds $H$. The future $F \\triangleleft H = F \\cup \\mathsf{ap}(H)$ adds the active points of $H$, \\annp{and in the lock-free mode the judgment also asks that $H - c$ is defined for the cost $c$ of $e$.}",
   "why": "Every rule that runs one part while it holds another states the same facts about the held part, and the notation states them once. $H$ is a context, as in E-App, or a type, as in E-Pair.",
   "breaks": "Without the future part a thread waits above an end it holds, and the partner of that end waits on the thread.",
   "example": "$\\Delta_1 \\vdash^{F \\triangleleft \\Delta_2} e_1$ in E-App.",
   "rocq": "static/Typing.v: e_app, e_pair, e_letp, e_letu, e_case",
   "sig": "F \\triangleleft H = F \\cup \\mathsf{ap}(H)",
   "args": [
    {
     "name": "F \\cup \\mathsf{ap}(H)",
     "meaning": "$F$ with the dual points of the ends in $H$ added, and the flag $\\bot$ added when $H$ holds an unopened existential at $\\bot$"
    },
    {
     "name": "H",
     "meaning": "the entries the thread holds while $e$ runs, a context or a type"
    },
    {
     "name": "c",
     "meaning": "the cost of $e$, lock-free mode only"
    }
   ]
  },
  "tj.eff": {
   "title": "Effect $\\varepsilon$",
   "what": "$\\varepsilon = c$ is the cost of a term, an upper bound on its channel actions before it returns.",
   "why": "Aging reads the cost. With tickets on ends the effect has no second component.",
   "breaks": "Nothing. It is a definition.",
   "example": "A send has effect $\\varepsilon \\cdot 1$, one more action than its argument.",
   "rocq": "static/Typing.v: typed",
   "sig": "\\varepsilon = c \\in \\mathsf{Eff} = \\mathbb{N} \\cup \\{\\infty\\}",
   "args": [
    {
     "name": "c",
     "meaning": "the cost"
    }
   ]
  },
  "tj.seq": {
   "title": "Sequencing $\\varepsilon_1 \\cdot \\varepsilon_2$",
   "what": "$\\varepsilon_1 \\cdot \\varepsilon_2 = c_1 + c_2$ in $\\mathbb{N} \\cup \\{\\infty\\}$.",
   "why": "A term that runs two parts in sequence adds their costs.",
   "breaks": "Nothing. It is a definition.",
   "example": "$1 \\cdot 1 = 2$.",
   "rocq": "static/Typing.v: typed",
   "sig": "\\cdot : \\mathsf{Eff} \\times \\mathsf{Eff} \\rightharpoonup \\mathsf{Eff}",
   "args": [
    {
     "name": "\\varepsilon_1, \\varepsilon_2",
     "meaning": "the effects of the first and the second part"
    }
   ]
  },
  "tj.zero": {
   "title": "No effect $0$",
   "what": "$0$, the effect of a value.",
   "why": "A value performs no action.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\lambda e$ has effect $0$.",
   "rocq": "static/Typing.v: e_abs, e_box, e_new",
   "sig": "0 \\in \\mathsf{Eff}",
   "args": []
  },
  "tj.one": {
   "title": "One action $1$",
   "what": "$1$, the effect of one channel action.",
   "why": "Every action adds one to the cost.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{close}\\,e$ has effect $\\varepsilon \\cdot 1$.",
   "rocq": "static/Typing.v: e_send, e_recv, e_close, e_select, e_branch",
   "sig": "1 \\in \\mathsf{Eff}",
   "args": []
  },
  "tj.Delta": {
   "title": "$\\Delta$, the linear context",
   "what": "$\\Delta$ maps ends $o$ to end types $(S@x)\\annot{^{a}}$ and de Bruijn indices $i$ to types $T$, with empty entries for indices another part owns.",
   "why": "Ends and variables split the same way between two subterms, so one context holds both. A split puts an empty entry at index $i$ in the half that does not own variable $i$, so no index shifts.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\Delta = a : (S_a@\\rho)\\annot{^{N}},\\ 0 : S_1@\\iota \\otimes S_2@\\kappa$.",
   "rocq": "static/Contexts.v: tenv, lenv",
   "sig": "\\Delta : (\\mathsf{End} \\rightharpoonup_{\\mathrm{fin}} \\mathsf{Ty}) \\times \\mathsf{Ty}_{\\bot}^{*}",
   "args": [
    {
     "name": "o",
     "meaning": "an end held by the term, with its end type $(S@x)\\annot{^{a}}$"
    },
    {
     "name": "\\Delta(i)",
     "meaning": "the entry of de Bruijn index $i$, empty or a type $T$"
    }
   ]
  },
  "tj.F": {
   "title": "The future $F$",
   "what": "$F = (X, {\\uparrow}u)$, $(X, {\\uparrow})$, $(X, \\bot)$ or $(X, \\cdot)$ with $X$ the points the context acts at after the term. ${\\uparrow}u$ is the unknown rest above a known point $u$, ${\\uparrow}$ an unknown rest with no bound, and $\\bot$ a rest at hidden points.",
   "why": "Every action at $x$ asks $x \\prec F$. Hence a term never waits at a point above a point at which its own context still acts.",
   "breaks": "Without $F$ the thread $\\mathsf{let}\\ \\ast = \\mathsf{close}\\,c\\ \\mathsf{in}\\ \\mathsf{close}\\,d$ types for every placement of $c$ and $d$, and beside a partner that closes $d$ before $c$ both threads wait forever.",
   "example": "$e_1$ of E-App runs under $F \\cup \\mathsf{ap}(\\Delta_2)$.",
   "rocq": "static/Contexts.v: sfuture, frest",
   "sig": "F : \\mathcal{P}_{\\mathrm{fin}}(\\mathsf{Pt}) \\times (\\{{\\uparrow}u \\mid u \\in \\mathsf{Pt}\\} + \\{{\\uparrow}, \\bot, \\cdot\\})",
   "args": [
    {
     "name": "X",
     "meaning": "the finite set of points the context acts at after the term"
    },
    {
     "name": "{\\uparrow}u",
     "meaning": "the unknown rest above the point $u$"
    },
    {
     "name": "\\bot",
     "meaning": "the flag that the context holds ends at points unknown to the term"
    }
   ]
  },
  "tj.W": {
   "title": "The world $W$",
   "what": "The static world whose order $\\prec_W$ the rules read.",
   "why": "Every point fact a rule uses comes from $\\prec_W$ or from $\\Gamma$. Typing is monotone in $W$, so a program typed in $W$ is typed in every $W' \\sqsupseteq W$.",
   "breaks": "Nothing. It is a definition.",
   "example": "E-Open asks $\\mathsf{cons}\\,W\\,\\Gamma\\,m\\,C$ over $\\prec_W$.",
   "rocq": "static/Typing.v: typed W",
   "sig": "W : \\mathsf{World}",
   "args": [
    {
     "name": "W",
     "meaning": "a world $(A, \\prec_A)$ of roots and facts"
    }
   ]
  },
  "tj.N": {
   "title": "The bound $N$",
   "what": "$N \\in \\mathbb{N} \\cup \\{\\infty\\}$ bounds the tickets of the two ends of each channel, $\\mathsf{tk}(o) + \\mathsf{tk}(\\overline{o}) \\leq N$.",
   "why": "A credit is a lower bound on a counter, the tickets of an end an upper bound, and each action of the thread holding an end on another end lowers its counter by $1$. A finite $N$ bounds the number of such actions between two actions on one end, which lock freedom needs, and $N = \\infty$ gives deadlock-free typing.",
   "breaks": "Nothing. It is a definition.",
   "example": "The client and server loop types at $N = 3$.",
   "rocq": "static/Typing.v: typed N",
   "sig": "N \\in \\mathbb{N} \\cup \\{\\infty\\}",
   "args": [
    {
     "name": "N",
     "meaning": "the bound on the tickets of the two ends of a channel, $\\infty$ for deadlock-free typing"
    }
   ]
  },
  "ctx.tsplit": {
   "title": "$\\Theta = \\Theta_1 \\uplus \\Theta_2$",
   "what": "$\\mathrm{dom}\\,\\Theta_1 \\cap \\mathrm{dom}\\,\\Theta_2 = \\varnothing$ and $\\Theta = \\Theta_1 \\cup \\Theta_2$.",
   "why": "Each end has exactly one owner. Two subterms therefore never act on the same end.",
   "breaks": "Nothing. It is a definition.",
   "example": "In E-App $\\Theta_1$ holds the ends of $e_1$ and $\\Theta_2$ those of $e_2$.",
   "rocq": "static/Contexts.v: tsplit",
   "sig": "\\Theta = \\Theta_1 \\uplus \\Theta_2 \\iff \\mathrm{dom}\\,\\Theta_1 \\cap \\mathrm{dom}\\,\\Theta_2 = \\varnothing \\land \\Theta = \\Theta_1 \\cup \\Theta_2",
   "args": [
    {
     "name": "\\Theta_1, \\Theta_2",
     "meaning": "the ends given to the first and to the second subterm"
    }
   ]
  },
  "ctx.lsplit": {
   "title": "$\\Delta = \\Delta_1, \\Delta_2$",
   "what": "Every end of $\\Delta$ goes to exactly one of $\\Delta_1$ and $\\Delta_2$. For every index $i$, a linear entry goes to one side and the other side has an empty entry, and an entry of unlimited type goes to both.",
   "why": "An end and a linear entry are used exactly once. An entry of unlimited type holds no end, so using it twice duplicates no end.",
   "breaks": "Nothing. It is a definition.",
   "example": "A box variable $f$ may be forced in both $e_1$ and $e_2$.",
   "rocq": "static/Contexts.v: tsplit, lenv_split",
   "sig": "\\Delta = \\Delta_1, \\Delta_2",
   "args": [
    {
     "name": "\\Delta",
     "meaning": "the linear context, ends $o$ with end types and de Bruijn indices with types"
    },
    {
     "name": "\\Delta_1, \\Delta_2",
     "meaning": "the contexts of the two subterms, the ends disjoint and the index lists of the same length as in $\\Delta$"
    },
    {
     "name": "i",
     "meaning": "a de Bruijn index, linear entries go to one side, unlimited entries to both"
    }
   ]
  },
  "ctx.hyps": {
   "title": "Constraint instances $(C, \\bar x)$",
   "what": "A constraint $C$ with the points $\\bar x$ it is instantiated at, added by E-Box and E-Open.",
   "why": "A box body and the scope of an opened existential refer to their points only through these instances. The facts $C[\\bar x]$ are the only hypotheses about these points.",
   "breaks": "Nothing. It is a definition.",
   "example": "$(C, [\\iota, \\kappa, \\zeta])$ in the body of the client loop.",
   "rocq": "static/Contexts.v: hyps, hc_open",
   "sig": "(C, \\bar x) \\in \\Gamma",
   "args": [
    {
     "name": "C",
     "meaning": "a box constraint, a set of facts over its bound point variables"
    },
    {
     "name": "\\bar x",
     "meaning": "the points $C$ is instantiated at, fresh point variables $\\bar\\iota$ inside a box or an opened existential"
    }
   ]
  },
  "ctx.fvarF": {
   "title": "The rest ${\\uparrow}u$ of $F$",
   "what": "The unknown part of a future, everything above $u$, or everything when there is no $u$. A term may wait at $x$ under ${\\uparrow}u$ when $\\Gamma \\vdash x \\preccurlyeq u$, and never under ${\\uparrow}$.",
   "why": "In the semantics ${\\uparrow}u$ denotes an arbitrary finite set of points above $u$. Readiness asks $x \\prec y$ of every point $y$ of the future, so a body typed under ${\\uparrow}u$ is correct for every caller future above $u$.",
   "breaks": "A future variable $\\varphi$ with the single fact $u \\prec \\varphi$ says the same, $\\Gamma \\vdash x \\prec \\varphi$ holds exactly when $\\Gamma \\vdash x \\preccurlyeq u$.",
   "example": "$F = (\\varnothing, {\\uparrow}u)$ for the body of a closure with upper point $u$.",
   "rocq": "static/Contexts.v: frest, rest_below",
   "sig": "F = (X, {\\uparrow}u)",
   "args": [
    {
     "name": "{\\uparrow}u",
     "meaning": "the rest, everything above $u$"
    },
    {
     "name": "X",
     "meaning": "the known points of the future"
    }
   ]
  },
  "ctx.bot": {
   "title": "The flag $\\bot$ in $F$",
   "what": "$\\bot$ states that the context holds ends at points unknown to the term, which then performs no session action.",
   "why": "Every action asks $u \\prec F$, which requires $F$ to have no $\\bot$. No point is known to lie below a hidden point, so an action under $\\bot$ could wait above the hidden point.",
   "breaks": "Nothing. It is a definition.",
   "example": "$e_1$ beside a context that holds an unopened $\\exists^{\\bot}$.",
   "rocq": "static/Contexts.v: FBot, fs_bot",
   "sig": "F = (X, \\bot)",
   "args": [
    {
     "name": "\\bot",
     "meaning": "the flag that some held end of the context has a point unknown to the term"
    },
    {
     "name": "X",
     "meaning": "the known points of the future"
    }
   ]
  },
  "ctx.slt": {
   "title": "$\\Gamma \\vdash x \\prec y$",
   "what": "The least transitive relation containing $\\prec_W$ and the facts $C[\\bar x]$ of the instances $(C, \\bar x)$ in $\\Gamma$.",
   "why": "Every order fact a typing rule reads is a judgment $\\Gamma \\vdash x \\prec y$.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\Gamma \\vdash x \\prec x^{+}$ for every $\\Gamma$ and $x$.",
   "rocq": "static/Contexts.v: fl, slt",
   "sig": "\\Gamma \\vdash x \\prec y \\subseteq \\mathsf{Hctx} \\times \\mathsf{Pt} \\times \\mathsf{Pt}",
   "args": [
    {
     "name": "\\Gamma",
     "meaning": "the facts, constraint instances $(C, \\bar x)$"
    },
    {
     "name": "x, y",
     "meaning": "points, the judgment states that $x$ lies strictly below $y$"
    }
   ]
  },
  "ctx.empty": {
   "title": "$\\Delta$ unlimited",
   "what": "Every non-empty entry of $\\Delta$ has unlimited type.",
   "why": "A value that mentions no variable uses no linear entry, and an unlimited entry may go unused.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\ast$ types under every $\\Delta$ whose entries are empty or unlimited.",
   "rocq": "static/Contexts.v: lenv_unl",
   "sig": "\\Delta\\ \\text{unlimited} \\iff \\Delta \\text{ holds no end} \\land \\forall i.\\ \\Delta(i) = \\bot \\lor \\mathsf{unlimited}\\,\\Delta(i)",
   "args": [
    {
     "name": "\\Delta",
     "meaning": "the linear context, ends $o$ with end types and de Bruijn indices with types"
    }
   ]
  },
  "ctx.only": {
   "title": "The only used entry",
   "what": "In $\\Delta, x : T$ the entry $x$ is used and every entry of $\\Delta$ has unlimited type.",
   "why": "Every linear entry is used exactly once, and an unlimited entry may go unused.",
   "breaks": "Nothing. It is a definition.",
   "example": "$x = 0$ types under $0 : T$.",
   "rocq": "static/Contexts.v: lenv_only",
   "sig": "\\Delta, x : T",
   "args": [
    {
     "name": "x",
     "meaning": "the variable or end used"
    },
    {
     "name": "T",
     "meaning": "its type"
    },
    {
     "name": "\\Delta",
     "meaning": "the rest of the context, unlimited"
    }
   ]
  },
  "side.act": {
   "title": "$x \\prec F$ at an action",
   "what": "For an action at $x$ under $F$, $\\Gamma \\vdash x \\prec y$ for every $y \\in X$, $\\Gamma \\vdash x \\preccurlyeq u$ when the rest of $F$ is ${\\uparrow}u$, and $F$ has neither the rest ${\\uparrow}$ nor $\\bot$.",
   "why": "While the term waits at $x$, every point at which its context acts later lies above $x$. This is readiness against the future.",
   "breaks": "Without it a term may wait at $x$ while its context must first act at a point below $x$, and the thread waits on itself through the dual end.",
   "example": "E-Close at $x$ asks $x \\prec F$.",
   "rocq": "static/Contexts.v: ub_below_s",
   "sig": "x \\prec F \\iff (\\forall y \\in X.\\ \\Gamma \\vdash x \\prec y) \\land (F = (X, {\\uparrow}u) \\Rightarrow \\Gamma \\vdash x \\preccurlyeq u) \\land F \\neq (X, {\\uparrow}) \\land F \\neq (X, \\bot)",
   "args": [
    {
     "name": "x",
     "meaning": "the point of the end the action is on"
    },
    {
     "name": "F",
     "meaning": "the future, the points at which the context acts after the term"
    },
    {
     "name": "\\Gamma",
     "meaning": "the facts, constraint instances $(C, \\bar x)$"
    }
   ]
  },
  "act.refill": {
   "title": "Credit $m$ after an action",
   "what": "An end returned by an action, or created fresh, has credit equal to its tickets $m$.",
   "why": "The fuel layer sets the counter of an end to its tickets at each action on the end, and the static credit is a lower bound on that counter.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{send}$ returns $(S@x^{+})^{m}_{m}$.",
   "rocq": "not yet in the Rocq (docs/redesign/check-links-without-tickets.md), today static/Typing.v: e_send, e_recv, e_select, e_branch, e_new",
   "sig": "(S@x)^{m}_{m}",
   "args": [
    {
     "name": "S@x",
     "meaning": "the end after the action, at its new point"
    },
    {
     "name": "m",
     "meaning": "the tickets of the end"
    }
   ]
  },
  "side.ub": {
   "title": "$u \\prec F$",
   "what": "$u \\prec F \\iff (\\forall y \\in X.\\ \\Gamma \\vdash u \\prec y) \\land (F = (X, {\\uparrow}v) \\Rightarrow \\Gamma \\vdash u \\preccurlyeq v)$, and $F$ has neither the rest ${\\uparrow}$ nor $\\bot$, true for absent $u$.",
   "why": "It is the condition $x \\prec F$ of an action, stated for the upper point $u$ up to which a callee may wait.",
   "breaks": "Nothing. It is a definition.",
   "example": "E-App asks $u \\prec F$ of the upper point $u$ of the closure.",
   "rocq": "static/Contexts.v: ub_below_s, ub_below_u",
   "sig": "u \\prec F \\iff (\\forall y \\in X.\\ \\Gamma \\vdash u \\prec y) \\land (F = (X, {\\uparrow}v) \\Rightarrow \\Gamma \\vdash u \\preccurlyeq v) \\land F \\neq (X, {\\uparrow}) \\land F \\neq (X, \\bot)",
   "args": [
    {
     "name": "u",
     "meaning": "the upper point of a closure or box, the highest point its body waits at"
    },
    {
     "name": "F",
     "meaning": "the future, the points at which the context acts after the term"
    },
    {
     "name": "\\Gamma",
     "meaning": "the facts, constraint instances $(C, \\bar x)$"
    }
   ]
  },
  "side.lb": {
   "title": "$l \\preccurlyeq H$",
   "what": "$l \\preccurlyeq H \\iff \\forall y \\in H.\\ l = y \\lor \\Gamma \\vdash l \\prec y$ for a point $l$, and $H = \\varnothing$ for absent $l$.",
   "why": "For a holding thread of a closure, the active points of its ends are bounded only through $l$. Hence $l$ must be a lower bound of those active points.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\overline{\\rho} \\preccurlyeq \\{\\overline{\\rho}\\}$.",
   "rocq": "static/Contexts.v: lbx_below_h, lbound_of",
   "sig": "l \\preccurlyeq H \\iff (l = \\cdot \\Rightarrow H = \\varnothing) \\land \\forall y \\in H.\\ l = y \\lor \\Gamma \\vdash l \\prec y",
   "args": [
    {
     "name": "l",
     "meaning": "a lower point, or $\\cdot$ when the value holds no end"
    },
    {
     "name": "H",
     "meaning": "a set of active points, dual points of held ends"
    }
   ]
  },
  "side.hold": {
   "title": "$\\Gamma \\vdash C[\\bar x]$",
   "what": "For every fact $y \\prec z$ of $C$ instantiated at $\\bar x$, $\\Gamma \\vdash y \\prec z$.",
   "why": "E-Force and E-Pack choose an instance $\\bar x$, and the box body or the packed value relies on $C[\\bar x]$.",
   "breaks": "Nothing. It is a definition.",
   "example": "The self call of the client loop instantiates $C$ at $(\\iota^{+}, \\kappa^{+}, \\zeta)$.",
   "rocq": "static/Contexts.v: hold_at",
   "sig": "\\Gamma \\vdash C[\\bar x] \\iff \\forall (y \\prec z) \\in C[\\bar x].\\ \\Gamma \\vdash y \\prec z",
   "args": [
    {
     "name": "C",
     "meaning": "a constraint over $m$ point variables"
    },
    {
     "name": "\\bar x",
     "meaning": "a list of $m$ points, the instance"
    },
    {
     "name": "\\Gamma",
     "meaning": "the facts, constraint instances $(C, \\bar x)$"
    }
   ]
  },
  "age.free": {
   "title": "Aging a type without ends",
   "what": "$T - c = T$ when $\\mathsf{tfree}\\,T$.",
   "why": "A type without ends has no counter that could fall, so aging changes nothing.",
   "breaks": "Nothing. It is a definition.",
   "example": "A box variable never ages.",
   "rocq": "static/Contexts.v: age_free",
   "sig": "\\mathsf{tfree}\\,T \\Rightarrow T - c = T",
   "args": [
    {
     "name": "T",
     "meaning": "a type holding no end"
    },
    {
     "name": "c",
     "meaning": "the cost of what runs meanwhile"
    }
   ]
  },
  "age.credit": {
   "title": "Aging an end or a closure",
   "what": "$(S@x)\\annot{^{a}} - c = (S@x)^{a - c}$ and $(T \\multimap U)\\annot{^{a}} - c = (T \\multimap U)^{a - c}$, defined when $c \\leq a$.",
   "why": "While a term of cost $c$ runs, the holding thread performs up to $c$ actions on other ends, and each lowers the counter of every held end by $1$. The premise $c \\leq a$ keeps the credit a lower bound on the counter.",
   "breaks": "Without $c \\leq a$ a server holds its client end while it runs a callback of cost $\\infty$ at finite $N$, and the client waits without bound.",
   "example": "$(S@x)^{3} - 1 = (S@x)^{2}$.",
   "rocq": "static/Contexts.v: age_sess, age_arr",
   "sig": "c \\leq a \\Rightarrow (S@x)\\annot{^{a}} - c = (S@x)^{a - c}",
   "args": [
    {
     "name": "a",
     "meaning": "the credit of the end or closure",
     "ann": true
    },
    {
     "name": "c",
     "meaning": "the cost of what runs while it is held"
    }
   ]
  },
  "age.idle": {
   "title": "Aging an idle end",
   "what": "$(S@x)\\annot{^{a}} - c = (S@x)^{\\max(a - c, 0)}$ when $\\mathsf{unfold}(S) = \\mathsf{Skip}$.",
   "why": "No thread acts on an idle end, so no action counter bounds an idle end. Truncation keeps its credit at or below its counter, which decrements and truncates at $0$ in the same way.",
   "breaks": "With $c \\leq a$ required an idle end held across a loop loses credit every round and no finite $N$ types the loop. Keeping the credit instead exceeds the counter after one decrement.",
   "example": "$(\\mathsf{Skip}@\\chi)\\annot{^{0}} - 1 = (\\mathsf{Skip}@\\chi)\\annot{^{0}}$.",
   "rocq": "static/Contexts.v: age_idle",
   "sig": "\\mathsf{idle}\\,S \\Rightarrow (S@x)\\annot{^{a}} - c = (S@x)^{\\max(a - c, 0)}",
   "args": [
    {
     "name": "S",
     "meaning": "a session type with $\\mathsf{unfold}(S) = \\mathsf{Skip}$"
    },
    {
     "name": "x",
     "meaning": "the point of the end"
    },
    {
     "name": "a",
     "meaning": "its credit",
     "ann": true
    },
    {
     "name": "c",
     "meaning": "the cost of what runs while the end is held"
    }
   ]
  },
  "age.agg": {
   "title": "Aging a product, sum or existential",
   "what": "Aging goes into the parts. $(T_1 \\otimes T_2) - c = (T_1 - c) \\otimes (T_2 - c)$, likewise for $\\oplus$, and $\\exists^{l}\\bar\\iota.\\,C.\\,T$ ages its body.",
   "why": "Only ends and closures have credits, so a compound type ages by aging the ends and closures it contains.",
   "breaks": "Nothing. It is a definition.",
   "example": "$((S@x)^{2} \\otimes \\ast) - 1 = (S@x)^{1} \\otimes \\ast$.",
   "rocq": "static/Contexts.v: age_prod, age_sum, age_ex",
   "sig": "(T_1 \\otimes T_2) - c = (T_1 - c) \\otimes (T_2 - c)",
   "args": [
    {
     "name": "T_1, T_2",
     "meaning": "the components"
    },
    {
     "name": "c",
     "meaning": "the cost of what runs while the value is held"
    }
   ]
  },
  "age.ctx": {
   "title": "Aging what is held",
   "what": "$\\Delta - \\varepsilon$ ages each entry of $\\Delta$ by the cost $\\varepsilon$.",
   "why": "The entries are held while the subterm with effect $\\varepsilon$ runs, and each of its actions lowers their counters by $1$.",
   "breaks": "Without aging a thread holds an end across unboundedly many actions on other ends, and the partner of that end waits without bound.",
   "example": "In the cycle example main loses $1$ of the credit of $d$ while it closes $c$.",
   "rocq": "static/Contexts.v: thage, lage",
   "sig": "\\Delta - \\varepsilon",
   "args": [
    {
     "name": "\\Delta",
     "meaning": "the entries held while a subterm runs"
    },
    {
     "name": "\\varepsilon",
     "meaning": "the effect of that subterm, its cost, which ages each entry"
    }
   ]
  },
  "sub.tsub": {
   "title": "Subtyping $T \\leq T'$",
   "what": "The least relation closed under Sub-Sess, Sub-Arr, Sub-Box, Sub-Ex and componentwise on $\\otimes$ and $\\oplus$, used by E-Sub.",
   "why": "The branches of $\\mathsf{case}$ and of a received choice need one common type. Every clause weakens what a value guarantees.",
   "breaks": "Without E-Sub two branches that create a channel with different facts have no common result type.",
   "example": "$\\exists^{\\bot}\\rho.\\,\\{\\rho \\prec \\overline{\\rho\\cdot 0}\\}.\\,T \\leq \\exists^{\\bot}\\rho.\\,\\varnothing.\\,T$, and $(S@x)^{3} \\leq (S@x)^{1}$ in the lock-free mode.",
   "rocq": "static/Contexts.v: tsub",
   "sig": "T \\leq T' \\subseteq \\mathsf{Ty} \\times \\mathsf{Ty}",
   "args": [
    {
     "name": "T",
     "meaning": "the type a value has"
    },
    {
     "name": "T'",
     "meaning": "the type it is used at"
    }
   ]
  },
  "tp.sub-credit": {
   "title": "Credits may fall",
   "what": "$a' \\leq a$ for the credits of an end.",
   "why": "A credit is a lower bound on the counter of an end, so a smaller credit guarantees less. $\\mathsf{new}$ and every action return credit $N$, and a parameter or a payload asks a fixed credit $b \\leq N$.",
   "breaks": "Without it a fresh end at credit $N$ fits only a parameter at credit exactly $N$, and no loop that ages an end before its self call types.",
   "example": "$(S@x)^{3} \\leq (S@x)^{2}$.",
   "rocq": "static/Contexts.v: tsub",
   "sig": "a' \\leq a",
   "args": [
    {
     "name": "a",
     "meaning": "the credit of the end in the subtype",
     "ann": true
    },
    {
     "name": "a'",
     "meaning": "the credit in the supertype",
     "ann": true
    }
   ]
  },
  "tp.sub-sess": {
   "title": "Session types up to equivalence",
   "what": "$S \\simeq S'$, bisimilar head normal forms with equal annotations, which is $S \\approx S'$ at annotations $\\infty$.",
   "why": "With $\\mathsf{Skip}$, sequencing and $\\mu$ one protocol has many spellings, e.g. $\\mathsf{Skip}.S \\simeq S$. Rules compare protocols by behaviour.",
   "breaks": "Without it an unfolded recursive protocol and its folded form would be different types, and no loop that acts once and recurses would type.",
   "example": "$\\mu\\alpha.\\,!\\ast.\\alpha \\leq\\ !\\ast.\\mu\\alpha.\\,!\\ast.\\alpha$ at the same point.",
   "rocq": "static/Contexts.v: sub_sess, types/Types.v: sequiv",
   "sig": "S \\simeq S'",
   "args": [
    {
     "name": "S, S'",
     "meaning": "session types at the same point $x$"
    }
   ]
  },
  "tp.sub-ex": {
   "title": "An existential may drop facts",
   "what": "$\\mathsf{facts}\\,C' \\subseteq \\mathsf{facts}\\,C$, the constraint $C'$ of the supertype states a subset of the facts of $C$ over the same variables.",
   "why": "E-New states the facts $C$ of a creation in its existential. Two branches of a $\\mathsf{case}$ or two creations that serve one type then agree on the facts both state, by dropping the rest.",
   "breaks": "Without it, two branches that create a channel with different facts have different result types, and the $\\mathsf{case}$ does not type.",
   "example": "$\\exists^{\\bot}\\rho.\\,\\{\\rho \\prec \\overline{\\rho\\cdot 0}\\}.\\,T \\leq \\exists^{\\bot}\\rho.\\,\\varnothing.\\,T$.",
   "rocq": "static/Contexts.v: sub_ex",
   "sig": "\\mathsf{facts}\\,C' \\subseteq \\mathsf{facts}\\,C",
   "args": [
    {
     "name": "C",
     "meaning": "the constraint of the subtype existential"
    },
    {
     "name": "C'",
     "meaning": "the constraint of the supertype existential, over the same variables"
    }
   ]
  },
  "tp.sub-var": {
   "title": "Variance",
   "what": "$\\leq$ is contravariant in the argument and covariant in the result of $\\multimap$, and covariant in the components of $\\otimes$ and $\\oplus$.",
   "why": "A closure that accepts more and returns less can stand for one that accepts less and returns more.",
   "breaks": "Nothing. It is a definition.",
   "example": "$((S@x)^{1} \\multimap (S@y)^{3}) \\leq ((S@x)^{2} \\multimap (S@y)^{1})$.",
   "rocq": "static/Contexts.v: sub_arr, sub_prod, sub_sum",
   "sig": "T_1' \\leq T_1 \\land U \\leq U'",
   "args": [
    {
     "name": "T_1, T_1'",
     "meaning": "the argument types, compared contravariantly"
    },
    {
     "name": "U, U'",
     "meaning": "the result types, compared covariantly"
    }
   ]
  },
  "tp.sub-agg": {
   "title": "Products and sums",
   "what": "$T_1 \\otimes T_2 \\leq T_1' \\otimes T_2'$ when $T_i \\leq T_i'$ for $i = 1, 2$, and likewise for $\\oplus$.",
   "why": "\\annp{A product or a sum has no credit of its own, so it compares part by part.}",
   "breaks": "Nothing. It is a definition.",
   "example": "$(S@x)^{2} \\otimes \\ast \\leq (S@x)^{1} \\otimes \\ast$.",
   "rocq": "static/Contexts.v: sub_prod, sub_sum",
   "sig": "T_1 \\leq T_1' \\land T_2 \\leq T_2'",
   "args": [
    {
     "name": "T_i, T_i'",
     "meaning": "the components of the two products or sums"
    }
   ]
  },
  "tp.sub-teq": {
   "title": "Equal up to $\\simeq$",
   "what": "$T \\equiv T'$, the two types have the same shape and their session types are pairwise $\\simeq$.",
   "why": "The body of a box and of an existential is compared exactly up to protocol spellings. \\annp{Credits inside it are not lowered, because a box is copied and an existential is opened at its own credit.}",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\Box(\\ldots\\,(\\mathsf{Skip}.S)@x) \\leq \\Box(\\ldots\\,S@x)$.",
   "rocq": "types/Types.v: teq",
   "sig": "T \\equiv T'",
   "args": [
    {
     "name": "T, T'",
     "meaning": "types of the same shape whose session types are pairwise $\\simeq$"
    }
   ]
  },
  "E-Abs.lb": {
   "title": "Lower point of a closure",
   "what": "$l \\neq \\bot \\Rightarrow l \\preccurlyeq \\Delta$. A point $l$ lies at or below every element of $\\mathsf{ap}(\\Delta)$, and $l = \\bot$ claims no bound.",
   "why": "A thread holding the closure reads the dual points of its ends only through $l$. A closure at $l = \\bot$ puts $\\bot$ into the future of the thread holding it, so that thread may not wait while it holds the closure, as for $\\exists^{\\bot}$.",
   "breaks": "A thread holding ends at the unrelated points $1$ and $2$ has no common lower point. A $\\lambda$ that captures both types at $l = \\bot$ and can then only be spawned or called in tail position.",
   "example": "Capturing $a^{+}$ at $\\rho$ gives $l = \\overline{\\rho}$.",
   "rocq": "static/Contexts.v: lbx_below_h, lbound_of",
   "sig": "l \\preccurlyeq \\Delta \\iff \\forall y \\in \\mathsf{ap}(\\Delta).\\ \\Gamma \\vdash l \\preccurlyeq y",
   "args": [
    {
     "name": "l",
     "meaning": "the lower point of the arrow"
    },
    {
     "name": "\\mathsf{ap}(\\Delta)",
     "meaning": "the dual points of every captured end, with $\\bot$ for hidden ends"
    }
   ]
  },
  "E-Abs.cap": {
   "title": "Capture as aging",
   "what": "\\annp{The body of a closure\\annp{ at credit $a$} sees $\\Delta - a$, each captured end and closure at its own credit minus $a$.}",
   "why": "The thread holding the closure performs up to $a$ actions before the call. \\annp{The body may therefore assume each captured credit minus $a$.} \\annp{Each end keeps its own credit, so an end at $N$ captured next to an end at $1$ stays at $N - a$.}",
   "breaks": "\\annp{A single shared credit puts an end at $N$ captured next to an end at $1$ at $0$, and a child that acts on the second end while it holds the first has no typing.}",
   "example": "$a^{+}$\\annp{ at credit $3$} in a closure\\annp{ at credit $1$} is seen\\annp{ at credit $2$}.",
   "rocq": "static/Typing.v: e_abs; static/Contexts.v: thage, lage",
   "sig": "\\Delta \\leadsto_{h,a} \\Delta^{h}",
   "args": [
    {
     "name": "h",
     "meaning": "the floor of the arrow",
     "ann": true
    },
    {
     "name": "a",
     "meaning": "the credit of the closure",
     "ann": true
    },
    {
     "name": "\\Delta^{h}",
     "meaning": "\\annp{the captured context restated at floor $h$}"
    }
   ]
  },
  "E-Abs.fut": {
   "title": "Future of the body",
   "what": "For a point $u$ the body runs under everything above $u$, with no upper point under everything, and for $u = \\top$ under the empty future $(\\varnothing, \\cdot)$.",
   "why": "A caller applies the closure only under a future $F$ with $u \\prec F$, and $\\top \\prec F$ holds only for the empty future, so a closure at $\\top$ is the last code of its thread.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\lambda e : \\ast \\multimap^{\\top}_{\\bot} \\ast$ for a thunk that is spawned.",
   "rocq": "static/Typing.v: e_abs; static/Contexts.v: abs_fut",
   "sig": "F_u",
   "args": [
    {
     "name": "u",
     "meaning": "the upper point of the arrow"
    }
   ]
  },
  "side.top": {
   "title": "$\\top \\prec F$",
   "what": "$\\top \\prec F$ holds exactly for the empty future $F = (\\varnothing, \\cdot)$.",
   "why": "The upper point $\\top$ lies above every point, so nothing may follow a call of such a closure. E-Spawn runs it as a new thread, where nothing follows.",
   "breaks": "Nothing. It is a definition.",
   "example": "E-App with $u = \\top$ needs $F = (\\varnothing, \\cdot)$, a call in tail position of a thread.",
   "rocq": "static/Contexts.v: ub_below_u",
   "sig": "\\top \\prec F \\iff F = (\\varnothing, \\cdot)",
   "args": [
    {
     "name": "F",
     "meaning": "the future of the caller"
    }
   ]
  },
  "E-Abs.body": {
   "title": "Body of a $\\lambda$",
   "what": "$e$ is typed under $\\Gamma$, the captured $\\Delta$ extended by the argument $T$, and the future $F_u$. \\annp{In the lock-free mode the captured entries are aged by the credit $a$.}",
   "why": "The body runs at a later call. It may rely only on its captured entries, its argument and the rest above $u$, and E-App establishes $u \\prec F$ at every call.",
   "breaks": "Nothing. It is a definition.",
   "example": "The body of the client loop with argument $S_1@\\iota \\otimes S_2@\\kappa$.",
   "rocq": "static/Typing.v: e_abs",
   "sig": "\\Gamma ; \\Delta\\annot{ - a}, T \\vdash^{F_u} e : U\\ !\\ \\varepsilon",
   "args": [
    {
     "name": "T",
     "meaning": "the argument at index $0$"
    },
    {
     "name": "U",
     "meaning": "the result of the body"
    },
    {
     "name": "\\varepsilon",
     "meaning": "the effect recorded on the arrow"
    }
   ]
  },
  "E-App.ub": {
   "title": "$u \\prec F$ at a call",
   "what": "The upper point $u$ of the closure satisfies $u \\prec F$.",
   "why": "The callee waits only at points up to $u$. Every point at which the caller acts afterwards lies above $u$.",
   "breaks": "A call of a closure that waits at $\\kappa$, while the caller must still act at a point below $\\kappa$, makes the caller wait on itself.",
   "example": "main forces $\\mathsf{between}$ last, so $F = \\varnothing$.",
   "rocq": "static/Typing.v: e_app",
   "sig": "u \\prec F",
   "args": [
    {
     "name": "u",
     "meaning": "the upper point of the arrow type of $e_1$"
    },
    {
     "name": "F",
     "meaning": "the future, the points at which the context acts after the term"
    }
   ]
  },
  "E-App.fut1": {
   "title": "The first subterm runs while the rest is held",
   "what": "$e_1$ is typed at the future $F \\triangleleft \\Delta_2$, which is $F \\cup \\mathsf{ap}(\\Delta_2)$, with $\\bot$ added when $\\Delta_2$ has $\\bot$.",
   "why": "The entries of the second subterm are held while $e_1$ runs. Hence $e_1$ must not wait above their dual points.",
   "breaks": "$\\mathsf{let}\\ \\ast = \\mathsf{close}\\,c\\ \\mathsf{in}\\ \\mathsf{close}\\,d$ beside a partner that closes $d$ before $c$ deadlocks. E-LetU rejects the first thread unless $x_c \\prec \\overline{x_d}$.",
   "example": "The cycle example needs $\\rho \\prec \\overline{\\rho\\cdot 0}$ for $\\mathsf{close}\\,c$ while $d$ is held.",
   "rocq": "static/Typing.v: e_app, e_pair, e_letp, e_letu, e_case",
   "sig": "\\Gamma ; \\Delta_1 \\vdash^{F \\triangleleft \\Delta_2} e_1 : \\ldots",
   "args": [
    {
     "name": "\\Delta_1",
     "meaning": "the part of the context given to $e_1$"
    },
    {
     "name": "\\Delta_2",
     "meaning": "the part held for the rest of the term"
    }
   ]
  },
  "E-App.fut2": {
   "title": "The argument runs while the closure is held",
   "what": "$e_2$ is typed while the thread holds the closure, so its future is $F \\cup \\{l\\}$ with $l$ the lower point of the closure. \\annp{In the lock-free mode the closure ages by the cost of $e_2$, which needs that much credit.}",
   "why": "The closure is held while $e_2$ runs, and $l$ bounds the dual points of its ends from below.",
   "breaks": "Nothing. It is a definition.",
   "example": "$f\\,(\\mathsf{close}\\,c)$ with $f$ capturing $d$.",
   "rocq": "static/Typing.v: e_app",
   "sig": "\\Gamma ; \\Delta_2 - \\varepsilon_1 \\vdash^{F \\triangleleft (T \\multimap^{u}_{l} U)\\annot{^{a}}} e_2 : T\\ !\\ \\varepsilon_2",
   "args": [
    {
     "name": "l",
     "meaning": "the lower point of the closure, held while $e_2$ runs"
    },
    {
     "name": "a",
     "meaning": "the credit of the closure, which bounds the cost of $e_2$",
     "ann": true
    }
   ]
  },
  "E-Pair.fut2": {
   "title": "The second component runs while the first is held",
   "what": "$e_2$ is typed while the thread holds the value of $e_1$, so its future is $F \\cup \\mathsf{ap}(T_1)$. In the lock-free mode $T_1$ ages by the cost of $e_2$.",
   "why": "The value of $e_1$ is held while $e_2$ runs.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\langle c, \\mathsf{close}\\,d\\rangle$ needs $x_d \\prec \\overline{x_c}$.",
   "rocq": "static/Typing.v: e_pair",
   "sig": "\\Gamma ; \\Delta_2 - \\varepsilon_1 \\vdash^{F \\triangleleft T_1} e_2 : T_2\\ !\\ \\varepsilon_2",
   "args": [
    {
     "name": "T_1",
     "meaning": "the type of the first component, held while $e_2$ runs"
    }
   ]
  },
  "tp.letp": {
   "title": "Body of a pair elimination",
   "what": "$e_2$ is typed under $\\Delta_2$, aged by $e_1$ in the lock-free mode, extended by $T_2$ at index $0$ and $T_1$ at index $1$, under $F$.",
   "why": "Both components become variables of $e_2$.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{let}\\ \\langle v, c\\rangle = \\mathsf{recv}\\,c\\ \\mathsf{in}\\ e$ binds the received value and the continuation end.",
   "rocq": "static/Typing.v: e_letp",
   "sig": "\\Gamma ; T_2, T_1, \\Delta_2 - \\varepsilon_1 \\vdash^{F} e_2 : T\\ !\\ \\varepsilon_2",
   "args": [
    {
     "name": "T_1 \\otimes T_2",
     "meaning": "the type of $e_1$"
    }
   ]
  },
  "tp.letu": {
   "title": "Body of a unit elimination",
   "what": "$e_2$ is typed under $\\Delta_2$, aged by $e_1$ in the lock-free mode, under $F$, after $e_1$ returned $\\ast$.",
   "why": "$\\ast$ holds no end, so nothing is bound. The rule sequences $e_1$ before $e_2$.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{let}\\ \\ast = \\mathsf{close}\\,c\\ \\mathsf{in}\\ \\mathsf{close}\\,d$.",
   "rocq": "static/Typing.v: e_letu",
   "sig": "\\Gamma ; \\Delta_2 - \\varepsilon_1 \\vdash^{F} e_2 : T\\ !\\ \\varepsilon_2",
   "args": [
    {
     "name": "\\Delta_2 - \\varepsilon_1",
     "meaning": "the context of $e_2$ aged by the cost of $e_1$"
    }
   ]
  },
  "E-Case.branches": {
   "title": "Branches",
   "what": "Each branch $e_i$ is typed under $T_i, \\Delta_2$ at the common result $T$.",
   "why": "Exactly one branch runs, and the choice is known only at run time. Both branches must fit the same continuation.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{case}\\,(\\mathsf{branch}\\,o)\\,(a.\\,\\mathsf{close}\\,a)\\,(a.\\,\\mathsf{close}\\,a)$.",
   "rocq": "static/Typing.v: e_case",
   "sig": "\\Gamma ; T_i, \\Delta_2 - \\varepsilon_0 \\vdash^{F} e_i : T\\ !\\ \\varepsilon_i",
   "args": [
    {
     "name": "i",
     "meaning": "$1$ or $2$, the branch"
    },
    {
     "name": "T_i",
     "meaning": "the payload of injection $i$ at index $0$"
    }
   ]
  },
  "E-Box.unl": {
   "title": "$\\Delta$ unlimited",
   "what": "Every entry of $\\Delta$ has unlimited type, so $\\Delta$ holds no end.",
   "why": "A box value is copied freely. If it held an end, a copy would duplicate that end.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{ring}$ captures no variable.",
   "rocq": "static/Contexts.v: lenv_unl",
   "sig": "\\Delta \\text{ holds no end} \\land \\forall i.\\ \\Delta(i) = T \\Rightarrow \\mathsf{unlimited}\\,T",
   "args": [
    {
     "name": "\\Delta",
     "meaning": "the linear context, ends $o$ with end types and de Bruijn indices with types"
    }
   ]
  },
  "E-Box.inst": {
   "title": "Typed for every instance",
   "what": "The premise has one derivation of the body for every list $\\bar s$ with $\\mathsf{sinsts}\\,\\bar s$, one session type per session variable $\\bar\\alpha$ of the box.",
   "why": "A force may pick any allowed $\\bar s$, and the derivation for that $\\bar s$ is the one that justifies the call. Checking every instance up front keeps E-Force a plain lookup.",
   "breaks": "Nothing. It is a definition.",
   "example": "A box with no session variable has exactly one instance, the empty list, so the premise is one derivation.",
   "rocq": "static/Typing.v: e_box",
   "sig": "\\forall \\bar s.\\ \\mathsf{sinsts}\\,\\bar s \\Rightarrow \\ldots",
   "args": [
    {
     "name": "\\bar s",
     "meaning": "a list of session types, one per session variable of the box"
    }
   ]
  },
  "E-Box.body": {
   "title": "Body of a box",
   "what": "The body is typed with no end, the fresh point variables $\\bar\\iota$, the hypothesis $C(\\bar\\iota)$, the box as $f$, and the future $(\\varnothing, {\\uparrow}u)$.",
   "why": "Each force instantiates $\\bar\\iota$ and the session variables anew. The body may assume only $C(\\bar\\iota)$ and the rest above $u$.",
   "breaks": "Nothing. It is a definition.",
   "example": "The body of the client loop.",
   "rocq": "static/Typing.v: e_box",
   "sig": "\\Gamma, C(\\bar\\iota) ; \\Delta, f \\vdash^{(\\varnothing, {\\uparrow}u)} e : U[\\bar s]\\ !\\ \\varepsilon",
   "args": [
    {
     "name": "\\bar\\iota",
     "meaning": "the fresh point variables of the box"
    },
    {
     "name": "f",
     "meaning": "the box itself at index $0$"
    },
    {
     "name": "{\\uparrow}u",
     "meaning": "the rest above the upper point of the box"
    }
   ]
  },
  "E-Box.open": {
   "title": "Opened constraint",
   "what": "$\\Gamma$ extended by the instance $C(\\bar\\iota)$ at the fresh variables.",
   "why": "The body relies on $C$ at its own point variables, and every force checks $C$ at the chosen instance.",
   "breaks": "Without $C$ the client loop cannot order the points of two consecutive rounds.",
   "example": "$\\Gamma, C(\\iota, \\kappa, \\zeta)$.",
   "rocq": "static/Contexts.v: hc_open",
   "sig": "\\Gamma, C(\\bar\\iota)",
   "args": [
    {
     "name": "C(\\bar\\iota)",
     "meaning": "the constraint at the fresh variables"
    }
   ]
  },
  "E-Box.self": {
   "title": "The self",
   "what": "The body binds the box as $f$ at index $0$, at its own type.",
   "why": "This is recursion. \\annp{A box holds no end, so it has no credit.}",
   "breaks": "Nothing. It is a definition.",
   "example": "$(\\mathsf{force}\\,f)\\,\\langle a, b\\rangle$ calls the self $f$.",
   "rocq": "static/Typing.v: e_box",
   "sig": "f : \\Box(\\forall \\bar\\iota\\,\\bar\\alpha.\\ C.\\ \\ast \\multimap^{u}[\\varepsilon]\\,U)",
   "args": [
    {
     "name": "f",
     "meaning": "the variable at index $0$ bound to the box itself"
    }
   ]
  },
  "E-Force.hold": {
   "title": "The instance meets $C$",
   "what": "$\\Gamma \\vdash C[\\bar x]$, for points $\\bar x$, one per variable of $\\bar\\iota$.",
   "why": "The body was typed under $C(\\bar\\iota)$. Running it at $\\bar x$ is correct only when $C[\\bar x]$ holds.",
   "breaks": "Nothing. It is a definition.",
   "example": "main forces $\\mathsf{between}$ at $(\\rho, \\rho\\cdot 1)$, where its creation of $\\rho$ states $C$.",
   "rocq": "static/Typing.v: e_force, e_pack",
   "sig": "\\Gamma \\vdash C[\\bar x]",
   "args": [
    {
     "name": "\\bar x",
     "meaning": "the points the force or pack instantiates $\\bar\\iota$ with, one per variable"
    }
   ]
  },
  "E-Force.ub": {
   "title": "$u[\\bar x] \\prec F$",
   "what": "The highest point the body waits at, $u$ with the chosen points put in, lies below every point of the future $F$.",
   "why": "After the force returns, the caller still acts at the points of $F$. If the body waited at a point above one of them, a partner could wait on the caller while the caller waits inside the body. This is the condition $u \\prec F$ of E-App for a box.",
   "breaks": "Nothing. It is a definition.",
   "example": "The self call of a loop at $\\zeta$ under $F = \\varnothing$.",
   "rocq": "static/Typing.v: e_force",
   "sig": "u[\\bar x] \\prec F",
   "args": [
    {
     "name": "u[\\bar x]",
     "meaning": "the upper point of the box at the instance $\\bar x$"
    },
    {
     "name": "F",
     "meaning": "the future, the points at which the context acts after the term"
    }
   ]
  },
  "E-Send.unfold": {
   "title": "Send head",
   "what": "$\\mathsf{unfold}(S_0) = {!}(\\bar\\iota.\\,T).S$.",
   "why": "Rules read the first action of $S_0$ after unfolding, so a recursive protocol $\\mu\\alpha.S$ needs no rule of its own.",
   "breaks": "Nothing. It is a definition.",
   "example": "$S_0 = \\mu\\alpha.\\,{!}\\ast.\\alpha$ unfolds to ${!}\\ast.(\\mu\\alpha.\\,{!}\\ast.\\alpha)$.",
   "rocq": "static/Typing.v: e_send",
   "sig": "\\mathsf{unfold}(S_0) = {!}(\\bar\\iota.\\,T).S",
   "args": [
    {
     "name": "S_0",
     "meaning": "the session type of the end before the action"
    },
    {
     "name": "\\mathsf{unfold}",
     "meaning": "the head normal form, which unfolds $\\mu$ and removes leading $\\mathsf{Skip}$"
    }
   ]
  },
  "E-Send.heads": {
   "title": "$x \\prec T$, the action point below a held value",
   "what": "$x \\prec T$ states $\\Gamma \\vdash x \\prec y$ for every $y \\in \\mathsf{ap}(T)$. If $T$ holds hidden ends, $\\bot \\in \\mathsf{ap}(T)$ and the check fails.",
   "why": "A thread waiting at $x$ while it holds a value of $T$ does not offer the ends in $T$, so readiness asks $x$ below the dual point of each. Hidden ends have no known dual point, so a thread holding them may not wait.",
   "breaks": "Without $\\bot$ in the active points, $\\mathsf{send}\\,\\langle p, o\\rangle$ with the unopened pair $p$ of a $\\mathsf{new}$ types, and the sender waits while holding ends at points nothing orders.",
   "example": "The growing ring needs $Y \\prec \\overline{Y\\cdot 0}$ for the payload $a$ of the send on $y$ at $Y$.",
   "rocq": "static/Typing.v: e_send; types/Types.v: heads, hbot",
   "sig": "x \\prec T \\iff \\forall y \\in \\mathsf{ap}(T).\\ \\Gamma \\vdash x \\prec y",
   "args": [
    {
     "name": "x",
     "meaning": "the point of the end the action is on"
    },
    {
     "name": "T",
     "meaning": "a held value, in E-Send the payload $T[x\\cdot i]$"
    },
    {
     "name": "y",
     "meaning": "a dual point of an end in $T$, or $\\bot$ for hidden ends, which no $x$ lies below"
    }
   ]
  },
  "E-Send.floor": {
   "title": "One transfer",
   "what": "$T' - 1 \\leq T[x\\cdot i]$, the payload value aged by one transfer still has the credits the protocol guarantees.",
   "why": "A transferred end loses $1$ of its counter at the send. Asking the promised credits after the loss bounds how often one end may be transferred.",
   "breaks": "Without the loss of $1$, an end is transferred forever, and its partner waits forever.",
   "example": "The growing ring sends $a'$ at credit $4$ against a promised $2$.",
   "rocq": "static/Typing.v: e_send",
   "sig": "T' - 1 \\leq T[x\\cdot i]",
   "args": [
    {
     "name": "T'",
     "meaning": "the type of the payload value"
    },
    {
     "name": "T[x\\cdot i]",
     "meaning": "the payload type of the protocol at the fields of $x$"
    }
   ]
  },
  "E-Recv.unfold": {
   "title": "Receive head",
   "what": "$\\mathsf{unfold}(S_0) = {?}(\\bar\\iota.\\,T).S$.",
   "why": "Rules read the first action of $S_0$ after unfolding, so recursive protocols need no rule of their own.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mu\\alpha.\\,{?}\\ast.\\alpha$ unfolds to ${?}\\ast.(\\mu\\alpha.\\,{?}\\ast.\\alpha)$.",
   "rocq": "static/Typing.v: e_recv",
   "sig": "\\mathsf{unfold}(S_0) = {?}(\\bar\\iota.\\,T).S",
   "args": [
    {
     "name": "S_0",
     "meaning": "the session type of the end before the action"
    },
    {
     "name": "\\mathsf{unfold}",
     "meaning": "the head normal form, which unfolds $\\mu$ and removes leading $\\mathsf{Skip}$"
    }
   ]
  },
  "E-Close.unfold": {
   "title": "Close head",
   "what": "$\\mathsf{unfold}(S_0) = \\mathsf{Close}$.",
   "why": "Rules read the first action of $S_0$ after unfolding.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{Close}@x$.",
   "rocq": "static/Typing.v: e_close",
   "sig": "\\mathsf{unfold}(S_0) = \\mathsf{Close}",
   "args": [
    {
     "name": "S_0",
     "meaning": "the session type of the end before the action"
    },
    {
     "name": "\\mathsf{unfold}",
     "meaning": "the head normal form, which unfolds $\\mu$ and removes leading $\\mathsf{Skip}$"
    }
   ]
  },
  "E-Select.unfold": {
   "title": "Select head",
   "what": "$\\mathsf{unfold}(S_0) = \\oplus(S_1, S_2)$.",
   "why": "Rules read the first action of $S_0$ after unfolding.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\oplus(\\mathsf{Close}, \\mathsf{Close})$.",
   "rocq": "static/Typing.v: e_select",
   "sig": "\\mathsf{unfold}(S_0) = \\oplus(S_1, S_2)",
   "args": [
    {
     "name": "S_0",
     "meaning": "the session type of the end before the action"
    },
    {
     "name": "\\mathsf{unfold}",
     "meaning": "the head normal form, which unfolds $\\mu$ and removes leading $\\mathsf{Skip}$"
    }
   ]
  },
  "E-Branch.unfold": {
   "title": "Branch head",
   "what": "$\\mathsf{unfold}(S_0) = \\&(S_1, S_2)$.",
   "why": "Rules read the first action of $S_0$ after unfolding.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\&(\\mathsf{Close}, \\mathsf{Close})$.",
   "rocq": "static/Typing.v: e_branch",
   "sig": "\\mathsf{unfold}(S_0) = \\&(S_1, S_2)",
   "args": [
    {
     "name": "S_0",
     "meaning": "the session type of the end before the action"
    },
    {
     "name": "\\mathsf{unfold}",
     "meaning": "the head normal form, which unfolds $\\mu$ and removes leading $\\mathsf{Skip}$"
    }
   ]
  },
  "E-Link.tickets": {
   "title": "$a_1 + m_2 > N$ and $a_2 + m_1 > N$",
   "what": "The credit of each linked end exceeds $N - m$ for the tickets $m$ of the other linked end, the bound on the tickets of the partner of that end.",
   "why": "After the link the partner of $o_1$ faces the partner of $o_2$, whose counter is at most $N - m_2 < a_1$, and $a_1$ bounds the counter of $o_1$ from below. The new partner of a waiting thread therefore has a lower counter than the old one, and the invariant on the tickets of a channel holds for the new pair.",
   "breaks": "Without the premise a thread relinks the partner of a waiting end to a new end with a full counter in every round, and the wait never ends.",
   "example": "At $N = 4$ ends at $(S@x)^{3}_{3}$ and $(\\overline{S}@\\overline{x})^{3}_{3}$ can be linked, and ends at credit $1$ cannot.",
   "rocq": "static/Typing.v: e_link; types/Costs.v: lgt",
   "sig": "a_1 + m_2 > N \\land a_2 + m_1 > N",
   "args": [
    {
     "name": "a_1, a_2",
     "meaning": "the credits of the two linked ends"
    },
    {
     "name": "m_1, m_2",
     "meaning": "their tickets"
    },
    {
     "name": "N",
     "meaning": "the bound on the tickets of a channel"
    }
   ]
  },
  "E-Link.dual": {
   "title": "Linked ends dual",
   "what": "$e$ returns $S@x \\otimes \\overline{S}@\\overline{x}$, two ends at dual types and dual points.",
   "why": "After the link the partners of the two ends form one channel. They are a well-typed pair only when the linked ends are exactly dual at dual points.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{link}\\,\\langle c^{+}, d^{-}\\rangle$ with $c^{+} : S@x$ and $d^{-} : \\overline{S}@\\overline{x}$.",
   "rocq": "static/Typing.v: e_link",
   "sig": "\\ldots \\vdash e : (S@x)\\annot{^{a_1}}_{m_1} \\otimes (\\overline{S}@\\overline{x})\\annot{^{a_2}}_{m_2}",
   "args": [
    {
     "name": "S@x",
     "meaning": "the first linked end"
    },
    {
     "name": "\\overline{S}@\\overline{x}",
     "meaning": "the second, at the dual type and dual point"
    }
   ]
  },
  "E-Spawn.credit": {
   "title": "Closure credit $a \\geq 1$",
   "what": "A spawned closure value has credit $a \\geq 1$.",
   "why": "Spawning passes on the captured ends with their counters minus $1$. The body was typed at each credit minus $a$, and $a \\geq 1$ covers that loss.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{spawn}\\,f$ with $f$ at credit $1$.",
   "rocq": "static/Typing.v: e_spawn",
   "sig": "a \\geq 1",
   "args": [
    {
     "name": "a",
     "meaning": "the credit of the closure value spawned",
     "ann": true
    }
   ]
  },
  "E-New.bot": {
   "title": "Lower bound $\\bot$",
   "what": "The pair is at a root $\\rho$ that no point of the context is related to.",
   "why": "$\\exists^{\\bot}$ records that the ends of the value are at points without a known lower bound, and $\\bot$ propagates into every future that holds the value.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{mk}_0$ returns $\\exists^{\\bot}\\iota.\\,C.\\,({?}\\ast.\\mathsf{Close})@\\overline{\\iota}$.",
   "rocq": "static/Typing.v: e_new",
   "sig": "\\exists^{\\bot}",
   "args": [
    {
     "name": "\\bot",
     "meaning": "the lower bound of the existential, no point of the context lies below its ends"
    }
   ]
  },
  "E-New.facts": {
   "title": "The constraint $C$",
   "what": "A set of facts, possibly infinite, over $\\pi$, its shifts and fields, and points of $\\Gamma$.",
   "why": "The derivation chooses the facts the new channel needs, and an interval $l \\prec \\pi \\prec u$ is the simplest case. Opening the existential adds $C$ to $\\Gamma$.",
   "breaks": "With facts limited to finitely many bounds by held ends, a client and server loop that orders the two channels at every round, $\\iota^{+k} \\prec \\overline{\\kappa^{+k}}$ for all $k$, does not type.",
   "example": "$C = \\{\\rho \\prec \\overline{\\rho\\cdot 0},\\ \\overline{\\rho} \\prec \\rho\\cdot 0\\}$ in the cycle example.",
   "rocq": "static/Typing.v: e_new",
   "sig": "C \\subseteq \\mathsf{Point} \\times \\mathsf{Point}",
   "args": [
    {
     "name": "C",
     "meaning": "the facts of the creation, chosen by the derivation"
    }
   ]
  },
  "E-New.pos": {
   "title": "Position $\\pi$",
   "what": "Either $\\pi = \\rho$, bound by the existential, or $\\pi = x\\cdot\\kappa$ for a point $x$ of the context.",
   "why": "A channel created to be sent on an end at $x$ lands at the field $x\\cdot j$ where the receiver expects its $j$-th payload end.",
   "breaks": "Nothing. It is a definition.",
   "example": "$d$ at $\\iota\\cdot 0$ in the example with a channel between two box arguments.",
   "rocq": "static/Typing.v: e_new",
   "sig": "\\pi \\in \\mathsf{Point}",
   "args": [
    {
     "name": "\\rho",
     "meaning": "the point variable bound by the existential"
    },
    {
     "name": "x, \\kappa",
     "meaning": "a point of the context and a field label"
    }
   ]
  },
  "E-New.wf": {
   "title": "$\\pi = \\rho \\Rightarrow \\mathsf{wf\\_new}\\,\\rho\\,C$",
   "what": "At a fresh root each fact of $C$ ends in $\\mathsf{tree}(\\rho)$, and $C$ with program order is well-founded on $\\mathsf{tree}(\\rho)$.",
   "why": "The fundamental theorem ranks the new tree at $\\sigma + \\rho_C$, with $\\sigma$ above each context point that a fact of $C$ puts below the tree and $\\rho_C$ the rank function of $C$ with program order. Facts from context points up into the tree then hold in each ranked world that satisfies $\\Gamma$.",
   "breaks": "A fact from a new point down to a context point fails when the context point has rank $0$, a rank that a box instance may choose. The growing waiting chain states such a fact in each round.",
   "example": "$\\{\\rho \\prec \\overline{\\rho\\cdot 0},\\ \\overline{\\rho} \\prec \\rho\\cdot 0\\}$ ends in $\\mathsf{tree}(\\rho)$ and is well-founded.",
   "rocq": "static/Contexts.v: wf_new; static/Typing.v: e_new",
   "sig": "\\pi = \\rho \\Rightarrow \\mathsf{wf\\_new}\\,\\rho\\,C : \\mathsf{Prop}",
   "args": [
    {
     "name": "\\rho",
     "meaning": "the fresh root"
    },
    {
     "name": "C",
     "meaning": "the facts of the creation"
    }
   ]
  },
  "E-New.field": {
   "title": "$\\pi = x\\cdot\\kappa \\Rightarrow \\Gamma \\vdash C$",
   "what": "At a field the context entails each fact of $C$.",
   "why": "The ranks of a field were fixed with its root, so a field creation picks no rank, and its facts must already hold.",
   "breaks": "A field creation that stated a new fact could ask a rank that the root left no room for.",
   "example": "A field creation with $C = \\varnothing$.",
   "rocq": "static/Typing.v: e_new_fld",
   "sig": "\\pi = x\\cdot\\kappa \\Rightarrow \\Gamma \\vdash C : \\mathsf{Prop}",
   "args": [
    {
     "name": "\\Gamma",
     "meaning": "the fact context"
    },
    {
     "name": "C",
     "meaning": "the facts of the creation"
    }
   ]
  },
  "E-New.dual": {
   "title": "Dual pair at its tickets",
   "what": "\\annp{$c^{+}$ has type $(S@\\pi)^{m_1}_{m_1}$ and $c^{-}$ type $(\\overline{S}@\\overline{\\pi})^{m_2}_{m_2}$, each at credit equal to its tickets.}",
   "why": "\\annp{Fuel starts each counter of a new channel at the tickets of its end\\annp{, and the credits} are lower bounds on these counters.}",
   "breaks": "Nothing. It is a definition.",
   "example": "$(S@\\pi)^{3}_{3} \\otimes (\\overline{S}@\\overline{\\pi})^{1}_{1}$ at $N = 4$.",
   "rocq": "not yet in the Rocq (docs/redesign/check-links-without-tickets.md, decided 2026-11-21)",
   "sig": "(S@\\pi)^{m_1}_{m_1} \\otimes (\\overline{S}@\\overline{\\pi})^{m_2}_{m_2}",
   "args": [
    {
     "name": "S",
     "meaning": "any session type, chosen by the derivation"
    },
    {
     "name": "m_1, m_2",
     "meaning": "\\annp{the tickets of the two ends, chosen by the derivation}"
    }
   ]
  },
  "E-New.tickets": {
   "title": "$m_1 + m_2 \\leq N$",
   "what": "The creation picks the tickets of the two new ends with sum at most $N$.",
   "why": "The invariant on the tickets of a channel holds for every new channel, so E-Link can read the partner bound of an end off its type.",
   "breaks": "Tickets above the bound break the premise of E-Link, which compares a credit with $N - m$.",
   "example": "$m_1 = m_2 = 2$ at $N = 4$.",
   "rocq": "not yet in the Rocq (docs/redesign/check-links-without-tickets.md, decided 2026-11-21)",
   "sig": "m_1 + m_2 \\leq N",
   "args": [
    {
     "name": "m_1, m_2",
     "meaning": "the tickets of the new ends"
    },
    {
     "name": "N",
     "meaning": "\\annp{the bound on the tickets of a channel, $N \\in \\mathbb{N} \\cup \\{\\infty\\}$}"
    }
   ]
  },
  "E-Sub.cost": {
   "title": "Effects may rise",
   "what": "$\\varepsilon \\leq \\varepsilon'$, so $c \\leq c'$ in $\\mathbb{N} \\cup \\{\\infty\\}$.",
   "why": "The cost is an upper bound, so a larger bound is also correct. The branches of a case and closures passed to one parameter have different effects, and the larger bound covers both.",
   "breaks": "Nothing. It is a definition.",
   "example": "Every cost may rise to $\\infty$.",
   "rocq": "static/Typing.v: e_sub, types/Costs.v: tle",
   "sig": "\\varepsilon \\leq \\varepsilon' \\iff c \\leq c'",
   "args": [
    {
     "name": "\\varepsilon = c",
     "meaning": "the effect derived"
    },
    {
     "name": "\\varepsilon' = c'",
     "meaning": "the weaker one concluded"
    }
   ]
  },
  "E-Weak.drop": {
   "title": "Weakening",
   "what": "$\\Delta'$ arises from $\\Delta$ by emptying entries of unlimited type only.",
   "why": "A linear entry may hold ends that must be used, so only entries of unlimited type are dropped.",
   "breaks": "Nothing. It is a definition.",
   "example": "Dropping an unused box variable.",
   "rocq": "static/Contexts.v: lenv_wk",
   "sig": "\\Delta' \\preceq_{\\mathsf{wk}} \\Delta",
   "args": [
    {
     "name": "\\Delta'",
     "meaning": "the context of the premise"
    },
    {
     "name": "\\Delta",
     "meaning": "the context of the conclusion, with additional unlimited entries"
    }
   ]
  },
  "E-Pack.lb": {
   "title": "Lower bound of a pack",
   "what": "$l = \\bot$, the ends become hidden, or $l \\preccurlyeq T[\\bar x]$, every head of the packed value lies at or above $l$, where $l = \\cdot$ asks that $T[\\bar x]$ holds no end.",
   "why": "After packing, a holding thread refers to the ends only through $l$, so $l$ must bound the active points of the packed value from below. The value relation at an existential states exactly this bound.",
   "breaks": "Nothing. It is a definition.",
   "example": "Packing a fresh pair at $\\bot$.",
   "rocq": "static/Contexts.v: lbx_below_h",
   "sig": "l = \\bot \\lor l \\preccurlyeq T[\\bar x]",
   "args": [
    {
     "name": "l",
     "meaning": "the lower bound of the existential"
    },
    {
     "name": "\\bar x",
     "meaning": "the witness points"
    }
   ]
  },
  "E-Pack.wf": {
   "title": "Well-formed existential",
   "what": "Under $\\Gamma$ and $C$ at the bound variables $\\bar\\iota$, $l \\preccurlyeq T$: each head of $T$ lies at or above $l$, and $l = \\cdot$ asks that $T$ holds no end.",
   "why": "The condition reads the type alone. It makes opening at the binder complete for each lower bound, so the algorithmic system can open eagerly.",
   "breaks": "Without it an existential at a point lower bound may be packed at one instance and need a later instance to be repacked, and no single place to open it is best.",
   "example": "$\\exists^{\\bot}\\iota.\\,C.\\,T$ is always well formed.",
   "rocq": "static/Contexts.v: ex_wf; static/Typing.v: e_pack",
   "sig": "\\Gamma, C \\vdash l \\preccurlyeq T",
   "args": [
    {
     "name": "l",
     "meaning": "the lower bound of the existential"
    },
    {
     "name": "C",
     "meaning": "the constraint at the bound variables"
    }
   ]
  },
  "E-Open.entry": {
   "title": "Opened entry",
   "what": "$\\Delta(i) = \\exists^{l}\\bar\\iota.\\,C.\\,T$ and $T$ is not unlimited.",
   "why": "Opening replaces entry $i$ in place. Variable renaming, used for contraction, maps distinct linear entries to distinct indices, and this needs the opened entry to be linear.",
   "breaks": "Nothing. It is a definition.",
   "example": "Opening the result of $\\mathsf{new}$.",
   "rocq": "static/Typing.v: e_open",
   "sig": "\\Delta(i) = \\exists^{l}\\bar\\iota.\\,C.\\,T \\land \\neg\\mathsf{unlimited}\\,T",
   "args": [
    {
     "name": "i",
     "meaning": "the de Bruijn index of the opened variable"
    }
   ]
  },
  "E-Open.body": {
   "title": "Body after opening",
   "what": "$e$ is typed with $C(\\bar\\iota)$ added to $\\Gamma$ and entry $i$ replaced by $T$, under the same future and result.",
   "why": "The fresh variables stand for the unknown witness, and $C$ is the only hypothesis about the witness in the scope. Freshness keeps them out of $F$ and $U$.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{let}\\ p = (\\mathsf{force}\\,\\mathsf{mk}_0)\\,\\ast\\ \\mathsf{in}\\ \\ldots$ opens the returned existential.",
   "rocq": "static/Typing.v: e_open",
   "sig": "\\Gamma, C(\\bar\\iota) ; \\Delta[i \\mapsto T] \\vdash^{F} e : U\\ !\\ \\varepsilon",
   "args": [
    {
     "name": "\\bar\\iota",
     "meaning": "the fresh point variables of the existential"
    },
    {
     "name": "U",
     "meaning": "the result type, which mentions no $\\bar\\iota$"
    }
   ]
  },
  "E-Open.cons": {
   "title": "Conservativity $\\mathsf{cons}\\,W\\,\\Gamma\\,m\\,C$",
   "what": "Each fact $x \\prec y$ between points of $\\Gamma$ that $\\Gamma, C(\\bar\\iota)$ derives, $\\Gamma$ derives already. Opening adds facts about the $m$ fresh points $\\bar\\iota$ and none between old points.",
   "why": "A dead arm or an uncalled abstraction receives no value, so the type of its binder may state arbitrary facts. Without the premise opening such a binder supplies the arm with an order fact that no world holds. The premise reads only the static order, and each existential that E-New creates satisfies the premise.",
   "breaks": "Without it the flag variant types. Its dead arm opens a binder whose constraint states $y \\prec \\overline{x}$, and the live arm asks only $x \\prec \\overline{y}$ of the world.",
   "example": "Opening $\\exists\\annot{^{0}}.\\,\\{y \\prec \\overline{x}\\}.\\,\\ast$ in a world with only $x \\prec \\overline{y}$ fails the premise.",
   "rocq": "static/Contexts.v: cons_open; static/PointSubst.v: cons_of_hold, cons_law; examples/SemBranch.v: Tbad_not_cons",
   "sig": "\\mathsf{cons} : \\mathsf{World} \\to \\mathsf{Hyps} \\to \\mathbb{N} \\to \\mathcal{P}(\\mathsf{Point} \\times \\mathsf{Point}) \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "W",
     "meaning": "the static world"
    },
    {
     "name": "\\Gamma",
     "meaning": "the fact context before the opening"
    },
    {
     "name": "m",
     "meaning": "the number of bound points, $m = |\\bar\\iota|$"
    },
    {
     "name": "C",
     "meaning": "the constraint of the opened existential"
    },
    {
     "name": "\\mathsf{Point}_{\\Gamma}",
     "meaning": "the points over the roots and variables of $\\Gamma$, which exclude the fresh $\\bar\\iota$"
    }
   ]
  },
  "pfree": {
   "title": "$\\mathsf{pfree}\\,\\Sigma$",
   "what": "For every $o \\in \\mathrm{dom}\\,\\Sigma$, $\\overline{o} \\notin \\mathrm{dom}\\,\\Sigma$.",
   "why": "P-Term puts every channel whose two ends the thread holds into $C_0$. Hence an interface never holds both ends of a channel, which the semantic P-Connect needs.",
   "breaks": "No program is lost, because such a channel always moves into $C_0$.",
   "example": "$\\Sigma = \\{c^{+}, c^{-}\\}$ is rejected, and $(\\{c\\}, \\ldots)$ with $\\Sigma = \\varnothing$ types instead.",
   "rocq": "static/Typing.v: pfree",
   "sig": "\\mathsf{pfree}\\,\\Sigma \\iff \\forall o \\in \\mathrm{dom}\\,\\Sigma.\\ \\overline{o} \\notin \\mathrm{dom}\\,\\Sigma",
   "args": [
    {
     "name": "\\Sigma",
     "meaning": "the interface, a finite map from the ends the process offers to its environment to $S@x$"
    }
   ]
  },
  "P-Term.C0": {
   "title": "$\\mathrm{dom}\\,\\Theta_B = \\mathsf{ends}(C_0)$",
   "what": "$o \\in \\mathrm{dom}\\,\\Theta_B$ iff the channel of $o$ is in $C_0$.",
   "why": "Every end of the thread is an interface end or an end of a restricted channel, and the second kind is exactly $\\Theta_B$.",
   "breaks": "Nothing. It is a definition.",
   "example": "$C_0 = \\varnothing$ and $\\Theta_B = \\varnothing$ for a source program.",
   "rocq": "static/Typing.v: p_term",
   "sig": "\\forall o.\\ o \\in \\mathrm{dom}\\,\\Theta_B \\iff \\mathsf{ech}(o) \\in C_0",
   "args": [
    {
     "name": "\\Theta_B",
     "meaning": "the entries of the restricted ends"
    },
    {
     "name": "C_0",
     "meaning": "the restricted channels of the thread"
    }
   ]
  },
  "P-Term.disj": {
   "title": "$\\mathsf{chans}\\,\\Sigma \\cap C_0 = \\varnothing$",
   "what": "No channel of the interface is restricted.",
   "why": "Then every end of $\\Sigma\\annot{^{N}} \\cup \\Theta_B$ lies in exactly one part, and the interface is the environment restricted to the channels outside $C_0$.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\Sigma = \\{c^{+} \\mapsto \\mathsf{Close}@x\\}$ with $C_0 = \\varnothing$.",
   "rocq": "static/Typing.v: p_term",
   "sig": "\\mathsf{chans}\\,\\Sigma \\cap C_0 = \\varnothing",
   "args": [
    {
     "name": "\\Sigma",
     "meaning": "the interface, a finite map from the ends the process offers to its environment to $S@x$"
    },
    {
     "name": "C_0",
     "meaning": "the restricted channels"
    }
   ]
  },
  "P-Term.pairs": {
   "title": "Restricted pairs dual",
   "what": "For every $c \\in C_0$ there are $S$, $x$, $m$ and $m'$ with $\\Theta_B(c^{+}) = (S@x)^{m}_{m}$, $\\Theta_B(c^{-}) = (\\overline{S}@\\overline{x})^{m'}_{m'}$ and $m + m' \\leq N$.",
   "why": "A restricted channel has both ends inside the process. \\annp{They synchronize with each other only, so they need dual types at dual points, and their tickets meet the bound of every channel.}",
   "breaks": "Nothing. It is a definition.",
   "example": "$c^{+} : S@x$ and $c^{-} : \\overline{S}@\\overline{x}$.",
   "rocq": "static/Typing.v: p_term",
   "sig": "\\forall c \\in C_0.\\ \\exists S\\,x\\,m\\,m'.\\ \\Theta_B(c^{+}) = (S@x)^{m}_{m} \\land \\Theta_B(c^{-}) = (\\overline{S}@\\overline{x})^{m'}_{m'} \\land m + m' \\leq N",
   "args": [
    {
     "name": "c",
     "meaning": "a restricted channel"
    },
    {
     "name": "S, x",
     "meaning": "the type and point of its positive end"
    },
    {
     "name": "m, m'",
     "meaning": "\\annp{the tickets of its two ends}"
    }
   ]
  },
  "P-Term.typed": {
   "title": "Thread typing",
   "what": "$t$ is typed under no facts, the interface ends and $\\Theta_B$, and the empty future.",
   "why": "The process judgment has static premises only. Its semantic content comes from the fundamental theorems.",
   "breaks": "Nothing. It is a definition.",
   "example": "The client and server main.",
   "rocq": "static/Typing.v: p_term",
   "sig": "\\varnothing ; \\Sigma^{N/2}_{N/2}, \\Theta_B \\vdash^{(\\varnothing,\\cdot)}_{W\\annot{,N}} t : T\\annot{\\ !\\ c}",
   "args": [
    {
     "name": "t",
     "meaning": "the thread"
    },
    {
     "name": "\\Sigma^{N/2}_{N/2}",
     "meaning": "\\annp{the interface at\\annp{ credit and }tickets $N/2$}"
    }
   ]
  },
  "P-Term.future": {
   "title": "Empty future",
   "what": "A thread at top level runs under $(\\varnothing, \\cdot)$.",
   "why": "A thread has no context, so no point lies in its future.",
   "breaks": "Nothing. It is a definition.",
   "example": "$(\\varnothing, \\cdot)$.",
   "rocq": "static/Typing.v: p_term",
   "sig": "F = (\\varnothing, \\cdot)",
   "args": [
    {
     "name": "F",
     "meaning": "the future of a top-level thread"
    }
   ]
  },
  "lf.N": {
   "title": "$N \\in \\mathbb{N}$",
   "what": "The bound of lock-free typing is a natural number.",
   "why": "Lock freedom ranks waiting threads by counters as natural numbers, and at $N = \\infty$ every counter is $\\infty$.",
   "breaks": "Nothing. It is a definition.",
   "example": "$N = 4$ for the growing ring.",
   "rocq": "static/Typing.v: ptyped",
   "sig": "N \\in \\mathbb{N}",
   "args": [
    {
     "name": "N",
     "meaning": "\\annp{the bound on the tickets of a channel, $N \\in \\mathbb{N} \\cup \\{\\infty\\}$}"
    }
   ]
  },
  "P-Connect.left": {
   "title": "Left component",
   "what": "$(C_1, E_1)$ is typed over $\\Sigma_1 \\cup \\Sigma_C$ in $W_1$ at result $T$.",
   "why": "The main thread lies on the left, so the left side has the result $T$ and the right side returns $\\ast$.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{close}\\,c^{+}$ at $T = \\ast$.",
   "rocq": "static/Typing.v: p_connect",
   "sig": "\\Sigma_1 \\cup \\Sigma_C \\vdash\\annot{\\annot{^{N}}}_{W_1} (C_1, E_1) : T",
   "args": [
    {
     "name": "\\Sigma_1",
     "meaning": "the interface kept outside"
    },
    {
     "name": "\\Sigma_C",
     "meaning": "the cut, the ends connected to the right component"
    }
   ]
  },
  "P-Connect.right": {
   "title": "Right component at $\\ast$",
   "what": "$(C_2, E_2)$ is typed over $\\Sigma_2 \\cup \\overline{\\Sigma_C}$ in $W_2$ at result $\\ast$.",
   "why": "Only the main thread returns a value, and every other thread returns $\\ast$.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{close}\\,c^{-}$.",
   "rocq": "static/Typing.v: p_connect",
   "sig": "\\Sigma_2 \\cup \\overline{\\Sigma_C} \\vdash\\annot{\\annot{^{N}}}_{W_2} (C_2, E_2) : \\ast",
   "args": [
    {
     "name": "\\Sigma_2",
     "meaning": "the interface kept outside"
    },
    {
     "name": "\\overline{\\Sigma_C}",
     "meaning": "the partners of the cut"
    }
   ]
  },
  "P-Connect.cut": {
   "title": "Exact dual cut $\\overline{\\Sigma_C}$",
   "what": "$\\overline{\\Sigma_C}$ maps $\\overline{o}$ to $\\overline{S}@\\overline{x}$ for every $o \\mapsto S@x$ in $\\Sigma_C$.",
   "why": "After composition the two ends of each cut channel are restricted, and lock freedom asks their protocols dual up to annotations. An exact dual gives this, a dual up to annotations does not.",
   "breaks": "\\annp{An annotation mismatch on a cut channel breaks the payload credit of a later message.}",
   "example": "$\\overline{\\{c^{+} \\mapsto \\mathsf{Close}@x\\}} = \\{c^{-} \\mapsto \\mathsf{Close}@\\overline{x}\\}$.",
   "rocq": "static/Typing.v: senv_dual",
   "sig": "\\overline{\\Sigma_C} = \\{\\overline{o} \\mapsto \\overline{S}@\\overline{x} \\mid (o \\mapsto S@x) \\in \\Sigma_C\\}",
   "args": [
    {
     "name": "\\Sigma_C",
     "meaning": "the cut"
    }
   ]
  },
  "P-Connect.disj": {
   "title": "Disjoint channels",
   "what": "$\\mathrm{dom}\\,\\Sigma_1 \\cap \\mathrm{dom}\\,\\Sigma_C = \\varnothing$, $\\mathrm{dom}\\,\\Sigma_2 \\cap \\mathrm{dom}\\,\\overline{\\Sigma_C} = \\varnothing$, the channel sets of $\\Sigma_1$, $\\Sigma_2$, $\\Sigma_C$ are pairwise disjoint, $C_1 \\cap C_2 = \\varnothing$, and each $C_i$ is disjoint from the channels of $\\Sigma_1$, $\\Sigma_2$, $\\Sigma_C$.",
   "why": "Every channel then belongs to one side. The cut $\\Sigma_C$ is the only channel set both sides use, so composition merges no two channels.",
   "breaks": "Nothing. It is a definition.",
   "example": "Two closes cut at $c$ with $\\Sigma_1 = \\Sigma_2 = \\varnothing$ and $C_1 = C_2 = \\varnothing$.",
   "rocq": "static/Typing.v: p_connect",
   "sig": "\\mathsf{chans}\\,\\Sigma_1, \\mathsf{chans}\\,\\Sigma_2, \\mathsf{chans}\\,\\Sigma_C, C_1, C_2\\ \\text{pairwise disjoint}",
   "args": [
    {
     "name": "C_1, C_2",
     "meaning": "the restricted channels of the components"
    }
   ]
  },
  "P-Connect.cutfree": {
   "title": "$\\mathsf{pfree}\\,\\Sigma_C$",
   "what": "The cut holds no partner pair.",
   "why": "The composite interface stays partner-free, which P-Term establishes for single threads.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\Sigma_C = \\{c^{+} \\mapsto \\mathsf{Close}@x\\}$.",
   "rocq": "static/Typing.v: p_connect",
   "sig": "\\mathsf{pfree}\\,\\Sigma_C",
   "args": [
    {
     "name": "\\Sigma_C",
     "meaning": "the cut"
    }
   ]
  },
  "P-Connect.wf": {
   "title": "Only the shared part is compared",
   "what": "$\\mathsf{wf}(W_1|_S \\sqcup W_2|_S)$ for $S = A_{W_1} \\cap A_{W_2}$, the roots of both worlds. $W|_S$ keeps the facts $x \\prec_W y$ derivable in $W$ whose roots lie in $S$.",
   "why": "Each side is well-founded by its own derivation, so each infinite descending chain of the join meets shared points infinitely often. Checking the orders the two sides induce on those roots is enough, and the join is then well-founded. A component exposes this order and no ranks, and the composite reads both sides at one ranked world.",
   "breaks": "If $W_1$ derives $\\rho \\prec \\overline{\\tau}$ and $W_2$ derives $\\overline{\\tau} \\prec \\rho$, the join has a cycle and two threads each wait on the other although each side alone is ready.",
   "example": "Two worlds without a common root need no check.",
   "rocq": "static/Typing.v: p_connect, ptyped_wf; types/Worlds.v: wf_join_iff",
   "sig": "\\mathsf{wf}(W_1|_S \\sqcup W_2|_S),\\ S = A_{W_1} \\cap A_{W_2}",
   "args": [
    {
     "name": "A_{W}",
     "meaning": "the roots of $W$"
    },
    {
     "name": "W|_S",
     "meaning": "the facts of $\\prec_W$ between points with roots in $S$"
    }
   ]
  },
  "P-Term.wf": {
   "title": "$\\mathsf{wf}\\,W$",
   "what": "The world of a single thread is well formed and well-founded.",
   "why": "The world of each process derivation is then well-founded and has a ranked world that satisfies it as a whole. P-Connect checks only the shared part, and the joined world is well-founded again.",
   "breaks": "Without it P-Connect would have to check the whole join.",
   "example": "The empty world.",
   "rocq": "static/Typing.v: p_term",
   "sig": "\\mathsf{wf}\\,W",
   "args": [
    {
     "name": "W",
     "meaning": "the world of the thread"
    }
   ]
  },
  "P-Connect.join": {
   "title": "Result in $W_1 \\sqcup W_2$",
   "what": "The composite is typed in the join of the two worlds.",
   "why": "Each component keeps its own facts, and the join contains the facts of both.",
   "breaks": "Nothing. It is a definition.",
   "example": "Two closes are typed in the join of their two worlds.",
   "rocq": "static/Typing.v: p_connect",
   "sig": "W_1 \\sqcup W_2",
   "args": [
    {
     "name": "W_1, W_2",
     "meaning": "the worlds of the components"
    }
   ]
  },
  "guard.judg": {
   "title": "The guard $\\varnothing \\vdash\\!\\triangleright t$",
   "what": "$\\Lambda \\vdash\\!\\triangleright t$ holds iff the self of every box in $t$ is used only after a session action of the body.",
   "why": "$\\kappa_L$ makes $\\beta$ free, so without the guard $!(f = \\mathsf{force}\\,f)$ types and diverges on free steps. Deadlock-free typing does not use the guard.",
   "breaks": "$!(f = \\mathsf{force}\\,f)$ types and is in no relation at $kappa_L$.",
   "example": "$!(f = \\lambda x.\\,\\mathsf{let}\\ \\langle v, x'\\rangle = \\mathsf{recv}\\,x\\ \\mathsf{in}\\ (\\mathsf{force}\\,f)\\,x')$ is guarded.",
   "rocq": "static/Guard.v: lguard",
   "sig": "\\Lambda \\vdash\\!\\triangleright t \\subseteq \\mathsf{bool}^{*} \\times \\mathsf{Expr}",
   "args": [
    {
     "name": "\\Lambda",
     "meaning": "the marks, a list mapping each variable to $\\mathsf{true}$ (unusable) or $\\mathsf{false}$"
    },
    {
     "name": "t",
     "meaning": "the term checked"
    }
   ]
  },
  "guard.marks": {
   "title": "Marks $\\Lambda$",
   "what": "$\\Lambda$ maps each variable to $\\mathsf{true}$, marked and not usable, or $\\mathsf{false}$.",
   "why": "A marked variable denotes a self that is available only one step later, as in guarded recursion.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{true}.\\varnothing$ marks the self of a box.",
   "rocq": "static/Guard.v: lguard",
   "sig": "\\Lambda : \\mathsf{bool}^{*}",
   "args": [
    {
     "name": "\\Lambda(y)",
     "meaning": "the mark of variable $y$, $\\mathsf{true}$ for the self of an enclosing box not yet passed by an action"
    }
   ]
  },
  "guard.var": {
   "title": "Marked variables unusable",
   "what": "$\\Lambda \\vdash\\!\\triangleright y$ requires $\\Lambda(y) = \\mathsf{false}$.",
   "why": "Using the self before an action would recurse with no step of positive cost in between.",
   "breaks": "$!(f = \\lambda x.\\,(\\mathsf{force}\\,f)\\,x)$ uses $f$ under a $\\lambda$ before any action and is rejected.",
   "example": "$y$ with $\\Lambda(y) = \\mathsf{false}$.",
   "rocq": "static/Guard.v: gl_var",
   "sig": "\\Lambda(y) = \\mathsf{false}",
   "args": [
    {
     "name": "y",
     "meaning": "the variable used"
    },
    {
     "name": "\\Lambda",
     "meaning": "the marks, a list mapping each variable to $\\mathsf{true}$ (unusable) or $\\mathsf{false}$"
    }
   ]
  },
  "guard.lam": {
   "title": "$\\lambda$ keeps the marks",
   "what": "$\\Lambda \\vdash\\!\\triangleright \\lambda b$ iff $\\mathsf{false}.\\Lambda \\vdash\\!\\triangleright b$.",
   "why": "The body of a $\\lambda$ runs at the level at which the $\\lambda$ is a value, so a self marked outside stays marked inside.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\lambda x.\\,(\\mathsf{force}\\,f)\\,x$ is not guarded under $\\Lambda(f) = \\mathsf{true}$.",
   "rocq": "static/Guard.v: gl_lam",
   "sig": "\\mathsf{false}.\\Lambda \\vdash\\!\\triangleright b",
   "args": [
    {
     "name": "b",
     "meaning": "the body of the $\\lambda$"
    },
    {
     "name": "\\mathsf{false}.\\Lambda",
     "meaning": "$\\Lambda$ with the unmarked argument at index $0$"
    }
   ]
  },
  "guard.box": {
   "title": "A box marks its self",
   "what": "$\\Lambda \\vdash\\!\\triangleright\\ !b$ iff $\\mathsf{true}.\\Lambda \\vdash\\!\\triangleright b$.",
   "why": "The self of a box is the recursive call, which must wait for an action.",
   "breaks": "Nothing. It is a definition.",
   "example": "$!b$ checks $b$ under $\\mathsf{true}.\\Lambda$.",
   "rocq": "static/Guard.v: gl_box",
   "sig": "\\mathsf{true}.\\Lambda \\vdash\\!\\triangleright b",
   "args": [
    {
     "name": "b",
     "meaning": "the body of the box"
    },
    {
     "name": "\\mathsf{true}.\\Lambda",
     "meaning": "$\\Lambda$ with the self at index $0$ marked"
    }
   ]
  },
  "guard.cong": {
   "title": "Frames",
   "what": "A frame checks its first subterm $e_1$ under $\\Lambda$ and the rest under the marks $\\Lambda'$ that $e_1$ leaves.",
   "why": "Without an action no step of positive cost happens, so every mark stays in force until $e_1$ acts.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\Lambda \\vdash\\!\\triangleright e_1\\,e_2$ from $\\Lambda \\vdash\\!\\triangleright e_1$ and $\\Lambda \\vdash\\!\\triangleright e_2$ with $\\Lambda' = \\Lambda$.",
   "rocq": "static/Guard.v: gl_app, gl_pair, gl_letu, gl_letp, gl_case",
   "sig": "\\Lambda \\vdash\\!\\triangleright e_1 \\land \\mathsf{kmarks}\\,\\Lambda\\,\\Lambda'\\,e_1 \\land \\Lambda' \\vdash\\!\\triangleright e_2",
   "args": [
    {
     "name": "e_1, e_2",
     "meaning": "the subterms of a frame"
    },
    {
     "name": "\\Lambda",
     "meaning": "the marks, a list mapping each variable to $\\mathsf{true}$ (unusable) or $\\mathsf{false}$"
    },
    {
     "name": "\\Lambda'",
     "meaning": "the marks after $e_1$"
    }
   ]
  },
  "guard.tick": {
   "title": "$\\mathsf{kmarks}\\,\\Lambda\\,\\Lambda'\\,e$",
   "what": "$\\Lambda' = \\Lambda$, or $\\Lambda' = \\varnothing$ and $\\mathsf{acts}\\,e$.",
   "why": "After a session action the rest runs one level lower, where every self is available.",
   "breaks": "Without the second case no loop that recurses after an action is guarded.",
   "example": "$\\mathsf{let}\\ \\langle v, x'\\rangle = \\mathsf{recv}\\,x\\ \\mathsf{in}\\ (\\mathsf{force}\\,f)\\,x'$ takes $\\Lambda' = \\varnothing$.",
   "rocq": "static/Guard.v: kmarks",
   "sig": "\\mathsf{kmarks}\\,\\Lambda\\,\\Lambda'\\,e \\iff \\Lambda' = \\Lambda \\lor (\\Lambda' = \\varnothing \\land \\mathsf{acts}\\,e)",
   "args": [
    {
     "name": "\\Lambda",
     "meaning": "the marks, a list mapping each variable to $\\mathsf{true}$ (unusable) or $\\mathsf{false}$"
    },
    {
     "name": "\\Lambda'",
     "meaning": "the marks for the rest"
    },
    {
     "name": "e",
     "meaning": "the term that runs first"
    }
   ]
  },
  "guard.bind": {
   "title": "Bound variables unmarked",
   "what": "Variables bound by a pair elimination or a case are marked $\\mathsf{false}$.",
   "why": "The bound value is computed by $e_1$ under $\\Lambda$. A value checked under $\\Lambda$ contains no variable marked in $\\Lambda$, so binding it unmarked lets no self escape.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{let}\\ \\langle a, b\\rangle = e_1\\ \\mathsf{in}\\ e_2$ checks $e_2$ under $\\mathsf{false}.\\mathsf{false}.\\Lambda$.",
   "rocq": "static/Guard.v: gl_letp, gl_case",
   "sig": "\\mathsf{false}.\\mathsf{false}.\\Lambda' \\vdash\\!\\triangleright e_2",
   "args": [
    {
     "name": "e_2",
     "meaning": "the body, with the two bound variables unmarked"
    },
    {
     "name": "\\Lambda'",
     "meaning": "the marks after the bound term"
    }
   ]
  },
  "guard.acts": {
   "title": "$\\mathsf{acts}\\,e$",
   "what": "$\\mathsf{acts}$ is the least predicate closed under the clauses shown, so every evaluation of $e$ to a value performs a step $k\\,v$ with $k \\in \\{\\mathsf{send}, \\mathsf{recv}, \\mathsf{close}, \\mathsf{select}_i, \\mathsf{branch}\\}$.",
   "why": "Each such step costs at least one level in the live cost table, so the rest after an acting $e_1$ runs one level lower, where the selves are in $V$.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{acts}\\,(\\mathsf{recv}\\,x)$.",
   "rocq": "static/Guard.v: acts, sprim",
   "sig": "\\mathsf{acts} : \\mathsf{Expr} \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "e",
     "meaning": "a term"
    },
    {
     "name": "k",
     "meaning": "an operator, acting when $k \\in \\{\\mathsf{send}, \\mathsf{recv}, \\mathsf{close}, \\mathsf{select}_i, \\mathsf{branch}\\}$"
    }
   ]
  },
  "guard.proc": {
   "title": "Guard of a process $\\vdash\\!\\triangleright p$",
   "what": "Every thread $t$ of $p$ satisfies $\\varnothing \\vdash\\!\\triangleright t$.",
   "why": "Live soundness and lock-free typing ask it beside process typing.",
   "breaks": "Nothing. It is a definition.",
   "example": "The client and server main is guarded.",
   "rocq": "static/FundamentalProc.v: pguard",
   "sig": "\\vdash\\!\\triangleright p \\iff \\forall t \\in E.\\ \\varnothing \\vdash\\!\\triangleright t",
   "args": [
    {
     "name": "p",
     "meaning": "the process $(C, E)$, restricted channels $C$ and a multiset $E$ of threads"
    },
    {
     "name": "t",
     "meaning": "a thread of $p = (C, E)$"
    }
   ]
  },
  "tp.Sigma": {
   "title": "The interface $\\Sigma$",
   "what": "$\\Sigma$ is a finite map from the ends a process offers to its environment to pairs $S@x$ of a session type and a point.",
   "why": "A process is typed against its interface, and composition cuts interface ends against each other.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\Sigma = \\{c^{+} \\mapsto \\mathsf{Close}@x\\}$.",
   "rocq": "static/Contexts.v: senv",
   "sig": "\\Sigma : \\mathsf{End} \\rightharpoonup_{\\mathrm{fin}} \\mathsf{Sty} \\times \\mathsf{Pt}",
   "args": [
    {
     "name": "o",
     "meaning": "an end offered to the environment"
    },
    {
     "name": "S@x",
     "meaning": "its session type and point"
    }
   ]
  },
  "tp.pjudg": {
   "title": "$\\Sigma \\vdash\\annot{\\annot{^{N}}}_{W} p : T$",
   "what": "The process $p$ is typed over $\\Sigma$ in $W$ at bound $N$ with result $T$, derived by P-Term and P-Connect.",
   "why": "One judgment serves deadlock freedom at $N = \\infty$ and lock freedom at finite $N$.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\varnothing \\vdash\\annot{^{\\infty}}_{W} (\\varnothing, \\{t\\}) : \\ast$.",
   "rocq": "static/Typing.v: ptyped",
   "sig": "\\Sigma \\vdash\\annot{\\annot{^{N}}}_{W} p : T",
   "args": [
    {
     "name": "\\Sigma",
     "meaning": "the interface, a finite map from the ends the process offers to its environment to $S@x$"
    },
    {
     "name": "W",
     "meaning": "the world whose order $\\prec_W$ the rule reads"
    },
    {
     "name": "N",
     "meaning": "\\annp{the bound on the tickets of a channel, $N \\in \\mathbb{N} \\cup \\{\\infty\\}$}"
    },
    {
     "name": "p",
     "meaning": "the process $(C, E)$, restricted channels $C$ and a multiset $E$ of threads"
    },
    {
     "name": "T",
     "meaning": "the result type of the main thread"
    }
   ]
  },
  "tp.lfjudg": {
   "title": "$\\Sigma \\Vdash^{N}_{W} p : T$",
   "what": "$\\Sigma \\Vdash^{N}_{W} p : T$ iff $N \\in \\mathbb{N}$, $\\Sigma \\vdash\\annot{\\annot{^{N}}}_{W} p : T$ and $\\vdash\\!\\triangleright p$.",
   "why": "Lock freedom needs finite counters and no infinite run of free steps, and the guard excludes the latter.",
   "breaks": "Nothing. It is a definition.",
   "example": "Two threads closing $c^{+}$ and $c^{-}$, at every $N \\in \\mathbb{N}$.",
   "rocq": "static/Typing.v: ptyped, static/FundamentalProc.v: pguard",
   "sig": "\\Sigma \\Vdash^{N}_{W} p : T \\iff N \\in \\mathbb{N} \\land \\Sigma \\vdash\\annot{\\annot{^{N}}}_{W} p : T \\land \\vdash\\!\\triangleright p",
   "args": [
    {
     "name": "\\Sigma",
     "meaning": "the interface, a finite map from the ends the process offers to its environment to $S@x$"
    },
    {
     "name": "W",
     "meaning": "the world whose order $\\prec_W$ the rule reads"
    },
    {
     "name": "N",
     "meaning": "\\annp{the bound on the tickets of a channel, $N \\in \\mathbb{N} \\cup \\{\\infty\\}$}"
    },
    {
     "name": "p",
     "meaning": "the process $(C, E)$, restricted channels $C$ and a multiset $E$ of threads"
    },
    {
     "name": "T",
     "meaning": "the result type of the main thread"
    }
   ]
  },
  "tp.chans": {
   "title": "$\\mathsf{chans}\\,\\Sigma$",
   "what": "The set of channels of the ends in $\\mathrm{dom}\\,\\Sigma$.",
   "why": "Restricted sets are sets of channels, so disjointness is stated on channels.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{chans}\\,\\{c^{+}, d^{-}\\} = \\{c, d\\}$.",
   "rocq": "static/Typing.v: chans_of",
   "sig": "\\mathsf{chans} : (\\mathsf{End} \\rightharpoonup X) \\to \\mathcal{P}(\\mathsf{Chan})",
   "args": [
    {
     "name": "\\Sigma",
     "meaning": "a finite map of ends"
    },
    {
     "name": "\\mathsf{chans}\\,\\Sigma",
     "meaning": "$\\{\\mathsf{ech}(o) \\mid o \\in \\mathrm{dom}\\,\\Sigma\\}$"
    }
   ]
  },
  "tp.ends": {
   "title": "$\\mathsf{ends}(C)$",
   "what": "The set $\\{c^{+}, c^{-} \\mid c \\in C\\}$.",
   "why": "A restricted channel contributes both its ends.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{ends}(\\{c\\}) = \\{c^{+}, c^{-}\\}$.",
   "rocq": "static/Typing.v: p_term",
   "sig": "\\mathsf{ends} : \\mathcal{P}(\\mathsf{Chan}) \\to \\mathcal{P}(\\mathsf{End})",
   "args": [
    {
     "name": "C",
     "meaning": "a set of channels"
    }
   ]
  },
  "tp.lift": {
   "title": "$\\Sigma^{N/2}_{N/2}$",
   "what": "\\annp{$\\Sigma$ with every entry at\\annp{ credit and }tickets $N/2$.}",
   "why": "The partner of an interface end belongs to another component. \\annp{Half of $N$ on each side keeps the bound on the tickets of a channel when P-Connect joins the two ends.}",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\{c^{+} \\mapsto \\mathsf{Close}@x\\}^{N/2}_{N/2} = \\{c^{+} \\mapsto (\\mathsf{Close}@x)^{N/2}_{N/2}\\}$.",
   "rocq": "static/Typing.v: p_term, tenv_of (fhalf N)",
   "sig": "\\Sigma^{N/2}_{N/2} : \\mathsf{End} \\rightharpoonup \\mathsf{Sty} \\times \\mathsf{Pt} \\times \\mathsf{Fuel} \\times \\mathsf{Fuel}",
   "args": [
    {
     "name": "\\Sigma",
     "meaning": "the interface, a finite map from the ends the process offers to its environment to $S@x$"
    },
    {
     "name": "N",
     "meaning": "\\annp{the bound on the tickets of a channel, $N \\in \\mathbb{N} \\cup \\{\\infty\\}$}"
    }
   ]
  },
  "E-Box.fresh": {
   "title": "$\\bar\\iota$ fresh",
   "what": "The bound point variables $\\bar\\iota$ occur nowhere in $\\Gamma$, $\\Delta$, $F$ or the result type.",
   "why": "They stand for points chosen later, at each force or for the unknown witness of an existential, so nothing in scope may mention these variables. The Rocq uses de Bruijn indices and shifts the context instead.",
   "breaks": "Nothing. It is a definition.",
   "example": "Opening $\\exists^{\\bot}\\iota.\\,C.\\,T$ under a context that mentions $\\rho$ picks $\\iota \\neq \\rho$.",
   "rocq": "types/Points.v: pshift; static/Typing.v: e_box, e_open",
   "sig": "\\bar\\iota \\cap \\mathsf{pvars}(\\Gamma, \\Delta, F, U) = \\varnothing",
   "args": [
    {
     "name": "\\bar\\iota",
     "meaning": "the bound point variables"
    }
   ]
  },
  "tp.pinst": {
   "title": "Point instance $T[\\bar x]$",
   "what": "Replaces the point variables $\\bar\\iota$ of $T$ by the points $\\bar x$.",
   "why": "Forcing and packing choose concrete points for the bound variables.",
   "breaks": "Nothing. It is a definition.",
   "example": "$(S@\\iota)[\\rho] = S@\\rho$.",
   "rocq": "types/Types.v: ty_inst",
   "sig": "T[\\bar x]",
   "args": [
    {
     "name": "T",
     "meaning": "a type over the bound point variables $\\bar\\iota$"
    },
    {
     "name": "\\bar x",
     "meaning": "the points substituted, $|\\bar x| = |\\bar\\iota|$"
    }
   ]
  },
  "tp.sinst": {
   "title": "Session instance $U[\\bar s]$",
   "what": "Replaces the session variables of $U$ by the session types $\\bar s$.",
   "why": "A box is polymorphic in its session variables, and each force chooses an instance.",
   "breaks": "Nothing. It is a definition.",
   "example": "$({\\alpha}@x)[\\mathsf{Close}] = \\mathsf{Close}@x$.",
   "rocq": "types/Types.v: sinst_ty",
   "sig": "U[\\bar s]",
   "args": [
    {
     "name": "U",
     "meaning": "a type over the session variables $\\bar\\alpha$"
    },
    {
     "name": "\\bar s",
     "meaning": "the session types substituted"
    }
   ]
  },
  "tp.sinsts": {
   "title": "Allowed session instances $\\mathsf{sinsts}\\,\\bar s$",
   "what": "The session types a session variable of a box may stand for. Every recursion $\\mu\\alpha.S$ inside each $s \\in \\bar s$, also inside payloads, passes an action before $\\alpha$ recurs, and no payload of $s$ mentions a point free below its binder. \\annp{At $N = \\infty$ each $s$ also has no finite credit.}",
   "why": "The rules read the first action of a protocol after unfolding. An instance such as $\\mu\\alpha.\\alpha$ has no first action, so substituting it would give an end no rule can type. \\annp{At $N = \\infty$ every annotation in a derivation is $\\infty$, and an instance with a finite credit inside its payloads would bring one in.}",
   "breaks": "Without the first condition a box with a variable $\\alpha$ could be forced at $\\mu\\alpha.\\alpha$, and an end of type $\\mu\\alpha.\\alpha$ would be stuck with no action to perform.",
   "example": "$\\mu\\alpha.\\,{!}\\ast.\\alpha$ and $\\mathsf{Close}$ are allowed, $\\mu\\alpha.\\alpha$ and $\\mu\\alpha.\\,\\mathsf{Skip}.\\alpha$ are not.",
   "rocq": "static/Contexts.v: sinsts; types/Types.v: hcontractive",
   "sig": "\\mathsf{sinsts} : \\mathsf{Fuel} \\to \\mathsf{Sty}^{*} \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "N",
     "meaning": "\\annp{the bound on the tickets of a channel, $N \\in \\mathbb{N} \\cup \\{\\infty\\}$}"
    },
    {
     "name": "\\bar s",
     "meaning": "a list of session types"
    }
   ]
  },
  "tp.max": {
   "title": "$\\max(\\varepsilon_1, \\varepsilon_2)$",
   "what": "The larger of two costs, $\\max(c_1, c_2)$.",
   "why": "Only one branch of a case runs, so its effect is bounded by the larger of the two.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\max(1, 2) = 2$.",
   "rocq": "types/Costs.v: fmax",
   "sig": "\\max : \\mathsf{Eff} \\times \\mathsf{Eff} \\to \\mathsf{Eff}",
   "args": [
    {
     "name": "\\varepsilon_1, \\varepsilon_2",
     "meaning": "the effects of the two branches"
    }
   ]
  },
  "tp.vdash": {
   "title": "The term turnstile $\\vdash$",
   "what": "The least relation closed under E-Unit to E-Open. The deadlock-free judgment $\\Gamma ; \\Delta \\vdash^{F} t : T$ is the instance $N = \\infty$ with every annotation $\\infty$.",
   "why": "One relation has the session type, the points and, in the lock-free mode, the\\annp{ credits and }the effect of $e$, so every mode reads its premises off one derivation.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\varnothing ; \\varnothing \\vdash^{(\\varnothing, \\cdot)} \\ast : \\ast$.",
   "rocq": "static/Typing.v: typed, dftyped",
   "sig": "\\Gamma ; \\Delta \\vdash^{F} e : T\\ !\\ \\varepsilon",
   "args": [
    {
     "name": "\\Gamma",
     "meaning": "the facts, constraint instances $(C, \\bar x)$"
    },
    {
     "name": "\\Delta",
     "meaning": "the linear context, ends $o$ with end types and de Bruijn indices with types"
    },
    {
     "name": "H",
     "meaning": "the entries the thread holds while $e$ runs, a context or a type"
    },
    {
     "name": "F",
     "meaning": "the future, the points at which the context acts after the term"
    },
    {
     "name": "e",
     "meaning": "the term"
    },
    {
     "name": "T",
     "meaning": "the result type"
    },
    {
     "name": "\\varepsilon",
     "meaning": "the effect of $e$, its cost, lock-free mode only"
    }
   ]
  },
  "tp.msunion": {
   "title": "Multiset union $E_1 \\uplus E_2$",
   "what": "$E_1 \\uplus E_2$, the multiset sum, counts every thread as often as $E_1$ and $E_2$ together.",
   "why": "A composite process runs the threads of both components side by side.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\{t_1\\} \\uplus \\{t_2\\} = \\{t_1, t_2\\}$.",
   "rocq": "lang/Syntax.v: proc",
   "sig": "\\uplus : \\mathcal{M}(\\mathsf{Expr}) \\times \\mathcal{M}(\\mathsf{Expr}) \\to \\mathcal{M}(\\mathsf{Expr})",
   "args": [
    {
     "name": "E_1, E_2",
     "meaning": "the thread multisets of the two components"
    }
   ]
  },
  "ct.table": {
   "title": "Cost table $\\kappa$",
   "what": "A sextuple $\\kappa \\in \\mathbb{N}^6$ of costs, one per kind of step.",
   "why": "One relation parametric in $\\kappa$ yields both the deadlock-freedom and the liveness relation, so each compatibility proof is done once for all $\\kappa$.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\kappa_{DF} = (1,1,1,0,0,1)$.",
   "rocq": "relation/CostTable.v: ctable",
   "sig": "\\kappa \\in \\mathsf{CTable} \\subseteq \\mathbb{N}^{6}",
   "args": [
    {
     "name": "\\kappa_\\beta, \\ldots, \\kappa_{take}",
     "meaning": "the costs of $\\beta$, creation, spawn, link, give and take"
    }
   ]
  },
  "ct.take-pos": {
   "title": "$1 \\leq \\kappa_{take}$",
   "what": "Receive and branch cost at least one level.",
   "why": "A receive reads $V$ of its payload negatively at the level of its continuation, so that level is $\\beta < \\alpha$ and $V_n$ is well defined.",
   "breaks": "With $\\kappa_{take} = 0$, $V_n$ would quantify negatively over $V_n$ and the fixpoint would not exist.",
   "example": "Both tables have $\\kappa_{take} = 1$.",
   "rocq": "relation/CostTable.v: c_take_pos",
   "sig": "1 \\leq \\kappa_{take} : \\mathsf{Prop}",
   "args": [
    {
     "name": "\\kappa",
     "meaning": "the cost table"
    }
   ]
  },
  "ct.give-pos": {
   "title": "$\\kappa_\\beta = 0 \\Rightarrow 1 \\leq \\kappa_{give}$",
   "what": "If $\\beta$ is free, a give costs at least one level.",
   "why": "For $\\kappa_\\beta = 0$, $V_n$ and $E_n$ are defined together by recursion on the size of the type, and a free send would read $V_n$ at a payload type of any size.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\kappa_L$ has $\\kappa_\\beta = 0$ and $\\kappa_{give} = 1$.",
   "rocq": "relation/CostTable.v: c_give_pos",
   "sig": "\\kappa_\\beta = 0 \\Rightarrow 1 \\leq \\kappa_{give} : \\mathsf{Prop}",
   "args": [
    {
     "name": "\\kappa",
     "meaning": "the cost table"
    }
   ]
  },
  "ct.give-take": {
   "title": "$\\kappa_{give} \\leq \\kappa_{take}$",
   "what": "A give costs at most a take.",
   "why": "A synchronization costs $\\kappa_{give} + \\kappa_{take}$, and composing two components counts a synchronization as two gives, which needs $2\\kappa_{give} \\leq \\kappa_{give} + \\kappa_{take}$.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\kappa_{DF}$ has $0 \\leq 1$ and $\\kappa_L$ has $1 \\leq 1$.",
   "rocq": "relation/CostTable.v: c_give_take",
   "sig": "\\kappa_{give} \\leq \\kappa_{take} : \\mathsf{Prop}",
   "args": [
    {
     "name": "\\kappa",
     "meaning": "the cost table"
    }
   ]
  },
  "ct.DF": {
   "title": "$\\kappa_{DF}$, the step index",
   "what": "The table $(1,1,1,0,0,1)$. It is the ordinary step index of a logical relation. Almost every step costs one level, and only a send, select, close or link costs none.",
   "why": "A step index lets $V$ and $E$ refer to themselves at lower levels, which recursion and received closures need. Each of the four free steps shrinks the term, so the successor is checked at the same level by recursion on the term. A send therefore passes its payload on at the level of the continuation.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\beta$ and $\\mathsf{recv}$ cost one level, $\\mathsf{send}$ costs none.",
   "rocq": "relation/CostTable.v: κ_DF",
   "sig": "\\kappa_{DF} = (1,1,1,0,0,1) \\in \\mathsf{CTable}",
   "args": []
  },
  "ct.L": {
   "title": "$\\kappa_L$, the live table",
   "what": "The table $(0,0,0,0,1,1)$. Internal steps, $\\beta$, $\\mathsf{new}$, $\\mathsf{spawn}$ and $\\mathsf{link}$, cost nothing, and only session actions cost a level.",
   "why": "A free step is checked inside the least fixpoint of the current level, and a least fixpoint admits only finitely many steps in a row. So a term in the relation at $\\kappa_L$ cannot take infinitely many internal steps without an action, which is absence of internal divergence. Lock freedom needs it, because a thread that loops internally never serves its partner. It is not about paying for messages.",
   "breaks": "$!(f = \\\\mathsf{force}\\\\,f)$ steps by $\\\\beta$ forever and is in no level at $\\\\kappa_L$, while it is in every level at $\\\\kappa_{DF}$.",
   "example": "Under $\\kappa_L$ a synchronization costs $2$, one level for each side.",
   "rocq": "relation/CostTable.v: κ_L",
   "sig": "\\kappa_L = (0,0,0,0,1,1) \\in \\mathsf{CTable}",
   "args": []
  },
  "ct.beta": {
   "title": "Cost $\\kappa_\\beta$",
   "what": "The cost of application, pair and unit elimination, case and force.",
   "why": "An arrow reads its body at every $\\beta < \\alpha$ under $\\kappa_{DF}$. \\annp{Under a general table it reads the levels $\\beta$ with $\\beta + \\kappa_\\beta \\leq \\alpha$, which for $\\kappa_L$ include $\\alpha$ itself.}",
   "breaks": "Nothing. It is a definition.",
   "example": "$(\\lambda e)\\,v \\xrightarrow{\\beta} e[v]$ costs $\\kappa_\\beta$.",
   "rocq": "relation/CostTable.v: c_beta",
   "sig": "\\kappa_\\beta \\in \\mathbb{N}",
   "args": [
    {
     "name": "\\kappa",
     "meaning": "the cost table"
    }
   ]
  },
  "ct.new": {
   "title": "Cost $\\kappa_{new}$",
   "what": "The cost of $\\mathsf{new}$.",
   "why": "Creation synchronizes with nobody, so $\\kappa_L$ counts it as an internal step.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\kappa_L(\\mathsf{new}) = 0$.",
   "rocq": "relation/CostTable.v: c_new",
   "sig": "\\kappa_{new} \\in \\mathbb{N}",
   "args": [
    {
     "name": "\\kappa",
     "meaning": "the cost table"
    }
   ]
  },
  "ct.spawn": {
   "title": "Cost $\\kappa_{spawn}$",
   "what": "The cost of $\\mathsf{spawn}$.",
   "why": "For $\\kappa_{spawn} = 0$ the child thunk is read inside the least fixpoint of the parent, so an infinite chain of spawns is in no $E_n$.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\kappa_L(\\mathsf{spawn}) = 0$.",
   "rocq": "relation/CostTable.v: c_spawn",
   "sig": "\\kappa_{spawn} \\in \\mathbb{N}",
   "args": [
    {
     "name": "\\kappa",
     "meaning": "the cost table"
    }
   ]
  },
  "ct.link": {
   "title": "Cost $\\kappa_{link}$",
   "what": "The cost of $\\mathsf{link}$, $0$ in both tables.",
   "why": "A link acts alone and synchronizes with nobody, so it is an internal step.",
   "breaks": "Under $\\kappa_L$ a loop that creates and links forever is an infinite sequence of internal steps and lies in no $E_n$.",
   "example": "$!(f = \\mathsf{let}\\ \\langle a, b\\rangle = \\mathsf{new}\\ \\mathsf{in}\\ \\mathsf{let}\\ \\ast = \\mathsf{link}\\,\\langle a, b\\rangle\\ \\mathsf{in}\\ \\mathsf{force}\\,f)$ diverges internally.",
   "rocq": "relation/CostTable.v: c_link",
   "sig": "\\kappa_{link} \\in \\mathbb{N}",
   "args": [
    {
     "name": "\\kappa",
     "meaning": "the cost table"
    }
   ]
  },
  "ct.give": {
   "title": "Cost $\\kappa_{give}$",
   "what": "The cost of $\\mathsf{send}$, $\\mathsf{select}$ and $\\mathsf{close}$.",
   "why": "The obligation of a give reads the continuation at the levels $\\beta$ with $\\beta + \\kappa_{give} \\leq \\alpha$.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\kappa_{DF}(\\mathsf{send}) = 0$.",
   "rocq": "relation/CostTable.v: c_give",
   "sig": "\\kappa_{give} \\in \\mathbb{N}",
   "args": [
    {
     "name": "\\kappa",
     "meaning": "the cost table"
    }
   ]
  },
  "ct.takek": {
   "title": "Cost $\\kappa_{take}$",
   "what": "The cost of $\\mathsf{recv}$ and $\\mathsf{branch}$, $1$ in both tables.",
   "why": "The obligation of a take reads every incoming value at the levels $\\beta$ with $\\beta + \\kappa_{take} \\leq \\alpha$, so $\\beta < \\alpha$.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\kappa(\\mathsf{recv}) = 1$.",
   "rocq": "relation/CostTable.v: c_take",
   "sig": "\\kappa_{take} \\in \\mathbb{N}",
   "args": [
    {
     "name": "\\kappa",
     "meaning": "the cost table"
    }
   ]
  },
  "ct.sync": {
   "title": "Cost of an event $\\kappa(ev)$",
   "what": "$\\kappa(ev)$ is the cost of the step kind of $ev$, and $\\kappa_{give} + \\kappa_{take}$ for a synchronization.",
   "why": "Both partners of a synchronization step at once, so the step of the process costs the sum of both costs.",
   "breaks": "Nothing. It is a definition.",
   "example": "A message costs $1$ under $\\kappa_{DF}$\\annp{ and $2$ under $\\kappa_L$}.",
   "rocq": "relation/CostTable.v: ev_cost",
   "sig": "\\kappa(\\cdot) : \\mathsf{Event} \\to \\mathbb{N}",
   "args": [
    {
     "name": "\\kappa",
     "meaning": "the cost table"
    },
    {
     "name": "ev",
     "meaning": "an event of the instrumented semantics"
    }
   ]
  },
  "rel.atcost": {
   "title": "$e'$ at $\\Theta'$",
   "what": "Take a step $\\ell$ of cost $c = \\kappa(\\ell)$ at the ordinal index $\\alpha$. Its successor is read in the fixpoint $X$ if $c = 0$, and in $E_\\beta$ for each ordinal $\\beta$ with $\\beta + c \\leq \\alpha$ if $c > 0$, with $\\beta + c$ the $c$-fold successor of $\\beta$.",
   "why": "Stated as two implications, $X$ occurs strictly positively and the inductive definition is admissible. At a successor $\\alpha = \\gamma + c$ the second case is the index $\\gamma$, and at a limit $\\lambda$ it is every $\\beta < \\lambda$, the later modality of transfinite step indexing.",
   "breaks": "Nothing. It is a definition.",
   "example": "Under $\\kappa_L$ a $\\beta$ step stays at index $\\alpha$, and at the limit $\\omega$ a step of cost $2$ obliges the successor at every finite index.",
   "rocq": "not yet in the Rocq (docs/redesign/check-transfinite.md)",
   "sig": "e' \\mathsf{at}\\ \\Theta' : \\mathsf{Prop}",
   "args": [
    {
     "name": "e'",
     "meaning": "the successor"
    },
    {
     "name": "\\Theta'",
     "meaning": "its environment"
    },
    {
     "name": "c = \\kappa(\\ell)",
     "meaning": "the cost of the step label $\\ell$"
    },
    {
     "name": "\\alpha, \\beta",
     "meaning": "ordinal indices"
    },
    {
     "name": "X",
     "meaning": "the least fixpoint under construction at index $\\alpha$"
    }
   ]
  },
  "rel.lfp": {
   "title": "Least fixpoint $X$",
   "what": "$E_n$ and $P_n$ are the least fixpoints of their clauses over steps of cost $0$.",
   "why": "A least fixpoint admits only finite sequences of cost-$0$ steps, so under $\\kappa_L$ no term in $E_n$ diverges internally.",
   "breaks": "A greatest fixpoint would admit $!(f = \\mathsf{force}\\,f)$, which takes only $\\beta$ steps.",
   "example": "Induction on $E_n$ is induction on cost-$0$ steps.",
   "rocq": "relation/Relation.v: Eind, Pind",
   "sig": "X : \\mathsf{World} \\to \\mathsf{Env} \\to \\mathsf{Ty} \\to \\mathcal{P}(\\mathsf{Point}) \\to \\mathsf{Expr} \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "X",
     "meaning": "the least relation closed under the clauses of level $n$"
    }
   ]
  },
  "V-Unit": {
   "title": "$V$ at $\\ast$",
   "what": "$v \\in V\\llbracket\\Theta \\vdash \\ast\\rrbracket \\iff \\Theta = \\varnothing \\land v = \\ast$.",
   "why": "A finished thread has result type $T$ or $\\ast$, and $\\Theta = \\varnothing$ shows that a thread holding a value of type $\\ast$ holds no end.",
   "breaks": "Without $\\Theta = \\varnothing$, a thread could end as $\\ast$ while owning an end that its partner waits on forever.",
   "example": "$\\ast \\in V\\llbracket\\varnothing \\vdash \\ast\\rrbracket$.",
   "rocq": "relation/Relation.v: Vbody TUnit",
   "sig": "v \\in V[\\kappa]^{W}_{\\alpha}\\llbracket \\Theta \\vdash T \\rrbracket",
   "args": [
    {
     "name": "\\kappa",
     "meaning": "the cost table"
    },
    {
     "name": "W",
     "meaning": "the world, $W \\in \\mathsf{World}$"
    },
    {
     "name": "\\alpha",
     "meaning": "the level, an ordinal"
    },
    {
     "name": "\\Theta",
     "meaning": "the environment, a finite map $\\mathsf{End} \\rightharpoonup \\mathsf{STy} \\times \\mathsf{Point}$"
    },
    {
     "name": "T",
     "meaning": "the type, $T \\in \\mathsf{Ty}$"
    },
    {
     "name": "v",
     "meaning": "the value"
    }
   ]
  },
  "V-Sess": {
   "title": "$V$ at $S@x$",
   "what": "$v \\in V\\llbracket\\Theta \\vdash S@x\\rrbracket \\iff \\exists o, S'.\\ v = o \\land \\Theta = \\{o \\mapsto S'@x\\} \\land S' \\approx S$.",
   "why": "$\\Theta$ keeps its annotations for the fuel layer, and $V$ compares session types erased.",
   "breaks": "Nothing. It is a definition.",
   "example": "$c^{+} \\in V\\llbracket\\{c^{+} \\mapsto S'@\\rho\\} \\vdash S@\\rho\\rrbracket$ for $S' \\approx S$.",
   "rocq": "relation/Relation.v: Vbody TSess",
   "sig": "v \\in V[\\kappa]^{W}_{\\alpha}\\llbracket \\Theta \\vdash T \\rrbracket",
   "args": [
    {
     "name": "\\kappa",
     "meaning": "the cost table"
    },
    {
     "name": "W",
     "meaning": "the world, $W \\in \\mathsf{World}$"
    },
    {
     "name": "\\alpha",
     "meaning": "the level, an ordinal"
    },
    {
     "name": "\\Theta",
     "meaning": "the environment, a finite map $\\mathsf{End} \\rightharpoonup \\mathsf{STy} \\times \\mathsf{Point}$"
    },
    {
     "name": "T",
     "meaning": "the type, $T \\in \\mathsf{Ty}$"
    },
    {
     "name": "v",
     "meaning": "the value"
    },
    {
     "name": "o",
     "meaning": "the end the value is"
    },
    {
     "name": "S'",
     "meaning": "the session type of $o$ in $\\Theta$, with annotations"
    }
   ]
  },
  "V-Sess.exact": {
   "title": "$\\Theta = \\{o \\mapsto S'@x\\}$",
   "what": "The environment of an end value is the singleton of its own entry at the point $x$ of the type.",
   "why": "Exact environments make $\\mathrm{dom}\\,\\Theta = \\mathsf{fends}(v)$ for every $v \\in V$, which fixes ownership at sends and spawns.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\Theta = \\{c^{+} \\mapsto S@\\rho\\}$.",
   "rocq": "relation/Relation.v: Vbody TSess",
   "sig": "\\Theta = \\{o \\mapsto S'@x\\} : \\mathsf{Prop}",
   "args": [
    {
     "name": "\\Theta",
     "meaning": "the environment, a finite map $\\mathsf{End} \\rightharpoonup \\mathsf{STy} \\times \\mathsf{Point}$"
    },
    {
     "name": "o",
     "meaning": "the subject end, $o \\in \\mathsf{End}$"
    },
    {
     "name": "S'@x",
     "meaning": "the entry of $o$, at the point $x$ of the type"
    }
   ]
  },
  "V-Prod": {
   "title": "$V$ at $\\otimes$",
   "what": "$\\langle v_1, v_2\\rangle \\in V\\llbracket\\Theta \\vdash T_1 \\otimes T_2\\rrbracket \\iff \\exists \\Theta_1, \\Theta_2.\\ \\Theta = \\Theta_1 \\uplus \\Theta_2 \\land \\forall i.\\ v_i \\in V\\llbracket\\Theta_i \\vdash T_i\\rrbracket$.",
   "why": "The clause mirrors E-Pair, and the disjoint split keeps environments exact through pairs.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\langle c^{+}, d^{-}\\rangle$ splits $\\{c^{+}, d^{-}\\}$ into $\\{c^{+}\\} \\uplus \\{d^{-}\\}$.",
   "rocq": "relation/Relation.v: Vbody TProd",
   "sig": "v \\in V[\\kappa]^{W}_{\\alpha}\\llbracket \\Theta \\vdash T \\rrbracket",
   "args": [
    {
     "name": "\\kappa",
     "meaning": "the cost table"
    },
    {
     "name": "W",
     "meaning": "the world, $W \\in \\mathsf{World}$"
    },
    {
     "name": "\\alpha",
     "meaning": "the level, an ordinal"
    },
    {
     "name": "\\Theta",
     "meaning": "the environment, a finite map $\\mathsf{End} \\rightharpoonup \\mathsf{STy} \\times \\mathsf{Point}$"
    },
    {
     "name": "T",
     "meaning": "the type, $T \\in \\mathsf{Ty}$"
    },
    {
     "name": "v",
     "meaning": "the value"
    },
    {
     "name": "\\Theta_1, \\Theta_2",
     "meaning": "the disjoint parts owned by $v_1$ and $v_2$"
    }
   ]
  },
  "V-Prod.split": {
   "title": "$\\Theta = \\Theta_1 \\uplus \\Theta_2$",
   "what": "The components own disjoint parts of $\\Theta$.",
   "why": "An end is owned by exactly one component, so no renaming can move a held end into a box inside a pair.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\{c^{+}\\} \\uplus \\{d^{-}\\}$.",
   "rocq": "relation/Relation.v: Vbody TProd",
   "sig": "\\Theta = \\Theta_1 \\uplus \\Theta_2 : \\mathsf{Prop}",
   "args": [
    {
     "name": "\\Theta",
     "meaning": "the environment, a finite map $\\mathsf{End} \\rightharpoonup \\mathsf{STy} \\times \\mathsf{Point}$"
    },
    {
     "name": "\\Theta_i",
     "meaning": "the part of component $i \\in \\{1,2\\}$"
    }
   ]
  },
  "V-Sum": {
   "title": "$V$ at $\\oplus$",
   "what": "$\\mathsf{inj}_i\\,v \\in V\\llbracket\\Theta \\vdash T_1 \\oplus T_2\\rrbracket \\iff v \\in V\\llbracket\\Theta \\vdash T_i\\rrbracket$.",
   "why": "The clause mirrors E-Inj and E-Case, and branch returns its end in an injection.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{inj}_1\\,c^{+} \\in V\\llbracket\\{c^{+} \\mapsto S_1@x\\cdot\\kappa_1\\} \\vdash S_1@x\\cdot\\kappa_1 \\oplus T\\rrbracket$.",
   "rocq": "relation/Relation.v: Vbody TSum",
   "sig": "v \\in V[\\kappa]^{W}_{\\alpha}\\llbracket \\Theta \\vdash T \\rrbracket",
   "args": [
    {
     "name": "\\kappa",
     "meaning": "the cost table"
    },
    {
     "name": "W",
     "meaning": "the world, $W \\in \\mathsf{World}$"
    },
    {
     "name": "\\alpha",
     "meaning": "the level, an ordinal"
    },
    {
     "name": "\\Theta",
     "meaning": "the environment, a finite map $\\mathsf{End} \\rightharpoonup \\mathsf{STy} \\times \\mathsf{Point}$"
    },
    {
     "name": "T",
     "meaning": "the type, $T \\in \\mathsf{Ty}$"
    },
    {
     "name": "v",
     "meaning": "the value"
    },
    {
     "name": "i",
     "meaning": "the side of the injection, $i \\in \\{1, 2\\}$"
    }
   ]
  },
  "V-Arrow.exact": {
   "title": "$\\mathrm{dom}\\,\\Theta = \\mathsf{fends}(e)$",
   "what": "A closure owns exactly the ends its body mentions.",
   "why": "With it, every $v \\in V$ satisfies $\\mathrm{dom}\\,\\Theta = \\mathsf{fends}(v)$, so the ends a send or spawn passes on are $\\mathsf{fends}$ of the value.",
   "breaks": "$\\lambda\\_.\\,\\mathsf{let}\\ \\ast = \\Omega\\ \\mathsf{in}\\ \\mathsf{close}\\,q^{+}$ owns nothing and is in $V$ at every level, and then a send of it next to $q^{+}$ fails E-Send.",
   "example": "$\\lambda\\_.\\,\\mathsf{close}\\,a$ owns $\\{a\\}$.",
   "rocq": "relation/Relation.v: Varr",
   "sig": "\\mathrm{dom}\\,\\Theta = \\mathsf{fends}(e) : \\mathsf{Prop}",
   "args": [
    {
     "name": "\\Theta",
     "meaning": "the environment, a finite map $\\mathsf{End} \\rightharpoonup \\mathsf{STy} \\times \\mathsf{Point}$"
    },
    {
     "name": "e",
     "meaning": "the body of the closure"
    }
   ]
  },
  "V-Arrow.lb": {
   "title": "$l \\preccurlyeq \\mathsf{ap}\\,\\Theta$",
   "what": "For $l = y$, $\\forall z \\in \\mathsf{ap}\\,\\Theta.\\ y \\preccurlyeq z$, and for $l$ absent, $\\mathsf{ap}\\,\\Theta = \\varnothing$.",
   "why": "The thread holding a closure reads its active points through $l$, which bounds the active points of the values it holds.",
   "breaks": "Nothing. It is a definition.",
   "example": "A closure over $a$ at $\\rho$ has $\\mathsf{ap}\\,\\Theta = \\{\\overline{\\rho}\\}$ and $l = \\overline{\\rho}$.",
   "rocq": "relation/Relation.v: Varr; relation/Readiness.v: lb_le",
   "sig": "l \\preccurlyeq \\mathsf{ap}\\,\\Theta : \\mathsf{Prop}",
   "args": [
    {
     "name": "l",
     "meaning": "the lower point of the arrow, a point or absent"
    },
    {
     "name": "\\Theta",
     "meaning": "the environment, a finite map $\\mathsf{End} \\rightharpoonup \\mathsf{STy} \\times \\mathsf{Point}$"
    }
   ]
  },
  "V-Arrow.kripke": {
   "title": "$\\forall W' \\sqsupseteq W$",
   "what": "The body is in $E$ in every extension $W'$ of $W$.",
   "why": "A closure may be called after composition has extended the world, so $V$ is monotone in $W$.",
   "breaks": "Nothing. It is a definition.",
   "example": "A received closure is called in $W \\sqcup W'$.",
   "rocq": "relation/Relation.v: Varr",
   "sig": "\\forall W' \\sqsupseteq W",
   "args": [
    {
     "name": "W",
     "meaning": "the world, $W \\in \\mathsf{World}$"
    },
    {
     "name": "W'",
     "meaning": "any extension of $W$"
    }
   ]
  },
  "V-Arrow.level": {
   "title": "Level of the body",
   "what": "The body is read at every level $\\beta < \\alpha$, \\annp{and under a general table at the levels $\\beta$ with $\\beta + \\kappa_\\beta \\leq \\alpha$.}",
   "why": "A $\\beta$-step costs one level in the deadlock-free relation. \\annp{Under $\\kappa_L$, where $\\beta$ is free, the body is read at the levels $\\beta \\leq \\alpha$.}",
   "breaks": "Nothing. It is a definition.",
   "example": "The body of a closure in $V_3$ is read at levels $0$ to $2$.",
   "rocq": "relation/Relation.v: Varr",
   "sig": "\\beta + \\kappa_\\beta \\leq \\alpha : \\mathsf{Prop}",
   "args": [
    {
     "name": "\\beta",
     "meaning": "the level at which the body is read"
    },
    {
     "name": "\\alpha",
     "meaning": "the level, an ordinal"
    }
   ]
  },
  "V-Arrow.ub": {
   "title": "$W' \\vdash u \\prec F$",
   "what": "The body is in $E$ under every future $F$ with $\\forall y \\in F.\\ W' \\vdash u \\prec y$.",
   "why": "A closure may block up to $u$, so its caller must still act only above $u$.",
   "breaks": "Nothing. It is a definition.",
   "example": "The body of $\\mathsf{between}$ runs under every $F$ above $\\kappa$.",
   "rocq": "relation/Readiness.v: ub_lt",
   "sig": "W' \\vdash u \\prec F : \\mathsf{Prop}",
   "args": [
    {
     "name": "u",
     "meaning": "the upper point of the arrow, a point or absent"
    },
    {
     "name": "F",
     "meaning": "the future of the call, any set of points above $u$"
    }
   ]
  },
  "V-Arrow.body": {
   "title": "Body in $E$",
   "what": "$e[w] \\in E^{W'}_{\\beta}\\llbracket\\Theta \\cup \\Theta' \\vdash U\\rrbracket^{F}$ for every argument $w \\in V^{W'}_{\\beta}\\llbracket\\Theta' \\vdash T\\rrbracket$ with $\\Theta' \\mathbin{\\#} \\Theta$.",
   "why": "The call owns the closure's ends and the argument's ends, which are disjoint, and the compatibility of E-App feeds exactly this union to the body.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{cli}$ applied to $\\langle a, b\\rangle$ runs at $\\{a, b\\}$.",
   "rocq": "relation/Relation.v: Varr",
   "sig": "e[w] \\in E^{W'}_{\\beta}\\llbracket \\Theta \\cup \\Theta' \\vdash U \\rrbracket^{F}",
   "args": [
    {
     "name": "w",
     "meaning": "the argument, in $V^{W'}_{\\beta}\\llbracket\\Theta' \\vdash T\\rrbracket$"
    },
    {
     "name": "\\Theta'",
     "meaning": "the ends of the argument, disjoint from $\\Theta$"
    },
    {
     "name": "U",
     "meaning": "the result type"
    }
   ]
  },
  "FV-Arrow.call": {
   "title": "$\\Phi' \\geq \\Phi - a$",
   "what": "At the call each captured end has the protocol it had at creation and a counter at least its counter at creation minus $a$.",
   "why": "Aging a closure by $c \\leq a$ lowers $a$ and the counters by $c$ together, so the difference stays, and the body was typed at each credit minus $a$.",
   "breaks": "Nothing. It is a definition.",
   "example": "A closure at credit $1$ created with counter $3$ on $o$ is called with counter $2$ or more on $o$.",
   "rocq": "fuel/Fuel.v: Vty TLolli; cost/CostRules.v: cle_fminus, cost_e_abs",
   "sig": "\\forall o.\\ \\Phi(o) = S^{f} \\Rightarrow \\Phi'(o) = S^{f'} \\land f' \\geq f - a",
   "args": [
    {
     "name": "\\Phi",
     "meaning": "the captured ends at creation"
    },
    {
     "name": "\\Phi'",
     "meaning": "the captured ends at the call"
    },
    {
     "name": "a",
     "meaning": "the credit of the closure",
     "ann": true
    }
   ]
  },
  "V-Box.empty": {
   "title": "$\\Theta = \\varnothing$",
   "what": "A box value owns no end.",
   "why": "Every value in $V$ satisfies $\\mathrm{dom}\\,\\Theta = \\mathsf{fends}(v)$, and at a box this is $\\Theta = \\varnothing$.",
   "breaks": "Without it, a box could be copied together with an end it owns.",
   "example": "$!(\\ldots) \\in V\\llbracket\\varnothing \\vdash \\Box(\\ldots)\\rrbracket$.",
   "rocq": "relation/Relation.v: Vbody TBox",
   "sig": "\\Theta = \\varnothing : \\mathsf{Prop}",
   "args": [
    {
     "name": "\\Theta",
     "meaning": "the environment, a finite map $\\mathsf{End} \\rightharpoonup \\mathsf{STy} \\times \\mathsf{Point}$"
    }
   ]
  },
  "V-Box.noends": {
   "title": "$\\mathsf{fends}(e) = \\varnothing$",
   "what": "The body of a box mentions no end.",
   "why": "A box is unlimited, so it must be copyable, and an end mentioned inside would be copied with the box.",
   "breaks": "A box hiding an end under an empty environment could be forced twice and act on the end twice.",
   "example": "$\\mathsf{ring}$ mentions no end.",
   "rocq": "relation/Relation.v: Vbody TBox",
   "sig": "\\mathsf{fends}(e) = \\varnothing : \\mathsf{Prop}",
   "args": [
    {
     "name": "e",
     "meaning": "the body of the box"
    }
   ]
  },
  "V-Box.kripke": {
   "title": "$\\forall W' \\sqsupseteq W$",
   "what": "The thunk is in $V$ in every extension $W'$ of $W$.",
   "why": "$V$ is monotone in $W$, and at a box the extension cannot be pushed into the thunk clause, because the instances $\\bar x$ range over points ordered only in $W'$.",
   "breaks": "Without it, a box received after composition could not be forced at an instance whose constraint holds only in the joined world.",
   "example": "Forcing a received box in $W \\sqcup W'$.",
   "rocq": "relation/Relation.v: Vbody TBox",
   "sig": "\\forall W' \\sqsupseteq W",
   "args": [
    {
     "name": "W",
     "meaning": "the world, $W \\in \\mathsf{World}$"
    },
    {
     "name": "W'",
     "meaning": "any extension of $W$"
    }
   ]
  },
  "V-Box.inst": {
   "title": "$W' \\vdash C[\\bar x]$",
   "what": "The thunk is in $V$ at every instance $\\bar x \\in \\mathsf{Point}^m$ with $\\forall (y \\prec z) \\in C.\\ W' \\vdash y[\\bar x] \\prec z[\\bar x]$.",
   "why": "E-Force asks $\\Gamma \\vdash C[\\bar x]$ at its instance, so the box must work at every instance meeting $C$ and at no other.",
   "breaks": "Nothing. It is a definition.",
   "example": "The self call of $\\mathsf{cli}$ at $(\\iota^{+}, \\kappa^{+}, \\zeta)$.",
   "rocq": "relation/Readiness.v: wholds",
   "sig": "W' \\vdash C[\\bar x] : \\mathsf{Prop}",
   "args": [
    {
     "name": "C",
     "meaning": "the box constraint over $m$ point variables"
    },
    {
     "name": "\\bar x",
     "meaning": "the point instance, $\\bar x \\in \\mathsf{Point}^m$"
    }
   ]
  },
  "V-Box.hc": {
   "title": "Contractive and scoped instances",
   "what": "The thunk is in $V$ at each list $\\bar s$ of $k$ session types that are hereditarily contractive and point-scoped.",
   "why": "Session instances must unfold to a head, which hereditary contractiveness guarantees. A payload of an instance must mention no point free below its binder, which scoping guarantees, as E-Send and E-Recv ask.",
   "breaks": "Nothing. It is a definition.",
   "example": "$k = 0$ in every example.",
   "rocq": "types/Types.v: hcontractive, sscoped; relation/Relation.v: Vbody",
   "sig": "\\forall s \\in \\bar s.\\ \\mathsf{hcontractive}\\,s \\land \\mathsf{sscoped}\\,s",
   "args": [
    {
     "name": "\\bar s",
     "meaning": "the session instance, $\\bar s \\in \\mathsf{STy}^k$"
    }
   ]
  },
  "V-Box.thunk": {
   "title": "The thunk at level $\\alpha$",
   "what": "$\\mathsf{thunk}(e) \\in V^{W'}_{\\alpha}\\llbracket\\varnothing \\vdash \\ast \\multimap^{u[\\bar x]} U[\\bar s][\\bar x]\\rrbracket$.",
   "why": "$\\mathsf{size}(\\Box\\ldots) > \\mathsf{size}(\\ast \\multimap U)$, so $V$ at the box reads $V$ at the thunk type inside level $\\alpha$.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{thunk}(e) = \\lambda.\\,e[!e]$.",
   "rocq": "relation/Relation.v: thunk, tthunk",
   "sig": "\\mathsf{thunk}(e) \\in V^{W'}_{\\alpha}\\llbracket \\varnothing \\vdash \\ast \\multimap^{u[\\bar x]} U[\\bar s][\\bar x] \\rrbracket",
   "args": [
    {
     "name": "u[\\bar x]",
     "meaning": "the upper point instantiated at $\\bar x$"
    },
    {
     "name": "U[\\bar s][\\bar x]",
     "meaning": "the result instantiated at $\\bar s$ and $\\bar x$"
    }
   ]
  },
  "V-Ex.lb": {
   "title": "$l \\preccurlyeq \\mathsf{ap}\\,\\Theta$",
   "what": "For $l = y$, $\\forall z \\in \\mathsf{ap}\\,\\Theta.\\ y \\preccurlyeq z$, for $l$ absent $\\mathsf{ap}\\,\\Theta = \\varnothing$, and for $l = \\bot$ nothing.",
   "why": "It lets a holding thread bound the actual active points of a packed value by its static active points, which the readiness of a send carrying a packed payload and the compatibility of E-Pack use.",
   "breaks": "Without it, a sender holding a packed payload could not show its offered end below the dual points of the payload ends.",
   "example": "$\\bot$ for $\\mathsf{new}_\\ell$.",
   "rocq": "relation/Readiness.v: lbx_le",
   "sig": "l \\preccurlyeq \\mathsf{ap}\\,\\Theta : \\mathsf{Prop}",
   "args": [
    {
     "name": "l",
     "meaning": "the lower bound, a point, absent or $\\bot$"
    },
    {
     "name": "\\Theta",
     "meaning": "the environment, a finite map $\\mathsf{End} \\rightharpoonup \\mathsf{STy} \\times \\mathsf{Point}$"
    }
   ]
  },
  "V-Ex.witness": {
   "title": "A witness in $W$",
   "what": "$\\exists \\bar x \\in \\mathsf{Point}^m.\\ W \\vdash C[\\bar x] \\land v \\in V\\llbracket\\Theta \\vdash T[\\bar x]\\rrbracket$.",
   "why": "Opening an existential substitutes fresh point variables and adds $C$ to $\\Gamma$, and the compatibility of E-Open instantiates them with this witness.",
   "breaks": "Nothing. It is a definition.",
   "example": "The fresh root $a$ with the facts $C$ of its creation.",
   "rocq": "relation/Relation.v: Vbody TEx",
   "sig": "\\exists \\bar x \\in \\mathsf{Point}^{m}.\\ W \\vdash C[\\bar x] \\land v \\in V^{W}_{\\alpha}\\llbracket \\Theta \\vdash T[\\bar x] \\rrbracket",
   "args": [
    {
     "name": "\\bar x",
     "meaning": "the witness points"
    },
    {
     "name": "C",
     "meaning": "the constraint of the existential"
    },
    {
     "name": "T[\\bar x]",
     "meaning": "the body type at the witness"
    }
   ]
  },
  "rel.vsize": {
   "title": "Recursion on $(\\alpha, \\mathsf{size}\\,T)$",
   "what": "$V_{\\alpha}$ is defined by well-founded recursion on the ordinal $\\alpha$ and, inside a level, on the size of the type, with all levels built by one fixpoint $\\mathsf{osfix}$.",
   "why": "Under $\\kappa_L$, $V_{\\alpha}$ reads $E_{\\beta}$ and $V_{\\beta}$ at the levels $\\beta \\leq \\alpha$ and at smaller types, and instantiation preserves size.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{size}(\\Box(\\ldots U)) = 3 + \\mathsf{size}\\,U$.",
   "rocq": "relation/Relation.v: tsize, Vtop, RelA; relation/Ord.v: osfix",
   "sig": "V : \\mathbb{N} \\to \\mathsf{World} \\to \\mathsf{Env} \\to \\mathsf{Ty} \\to \\mathsf{Expr} \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "\\alpha",
     "meaning": "the level, an ordinal"
    },
    {
     "name": "\\mathsf{size}\\,T",
     "meaning": "the inner recursion measure"
    }
   ]
  },
  "E.zero": {
   "title": "Level $0$",
   "what": "$E_0$ holds every term.",
   "why": "Step indexing starts from the trivial relation.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\forall e.\\ e \\in E_0\\llbracket\\Theta \\vdash T\\rrbracket^{F}$.",
   "rocq": "relation/Relation.v: Etop, Erel_0",
   "sig": "e \\in E^{W}_{0}\\llbracket \\Theta \\vdash T \\rrbracket^{F}",
   "args": [
    {
     "name": "\\kappa",
     "meaning": "the cost table"
    },
    {
     "name": "W",
     "meaning": "the world, $W \\in \\mathsf{World}$"
    },
    {
     "name": "\\alpha",
     "meaning": "the level, an ordinal"
    },
    {
     "name": "\\Theta",
     "meaning": "the environment, a finite map $\\mathsf{End} \\rightharpoonup \\mathsf{STy} \\times \\mathsf{Point}$"
    },
    {
     "name": "T",
     "meaning": "the type, $T \\in \\mathsf{Ty}$"
    },
    {
     "name": "F",
     "meaning": "the future, a finite set of points"
    },
    {
     "name": "e",
     "meaning": "the term"
    }
   ]
  },
  "E.kripke": {
   "title": "$\\forall W_1 \\sqsupseteq W$",
   "what": "Each unfolding of $E$ holds in every extension $W_1$ of $W$.",
   "why": "$E$ is monotone in $W$ by definition, so no clause needs its own world quantifier.",
   "breaks": "Nothing. It is a definition.",
   "example": "$e \\in E^{W}_n \\Rightarrow e \\in E^{W \\sqcup W'}_n$.",
   "rocq": "relation/Relation.v: Ebody",
   "sig": "\\forall W_1 \\sqsupseteq W",
   "args": [
    {
     "name": "W",
     "meaning": "the world, $W \\in \\mathsf{World}$"
    },
    {
     "name": "W_1",
     "meaning": "any extension of $W$, the world at which the clauses are read"
    }
   ]
  },
  "E.stop": {
   "title": "(stop)",
   "what": "$\\mathsf{irred}\\,e \\Rightarrow e \\in V^{W_1}_{\\alpha}\\llbracket\\Theta \\vdash T\\rrbracket$.",
   "why": "A term that takes no step must be a value in $V$, so a stuck term is in no $E_\\alpha$ for $\\alpha > 0$ and adequacy reads termination off $V$.",
   "breaks": "A stuck non-value would count as well typed, and adequacy would fail.",
   "example": "$\\ast \\in E_1\\llbracket\\varnothing \\vdash \\ast\\rrbracket^{\\varnothing}$.",
   "rocq": "relation/Relation.v: Ebody",
   "sig": "\\mathsf{irred}\\,e \\Rightarrow e \\in V^{W_1}_{\\alpha}\\llbracket \\Theta \\vdash T \\rrbracket",
   "args": [
    {
     "name": "e",
     "meaning": "the term"
    },
    {
     "name": "W_1",
     "meaning": "the extension of $W$"
    },
    {
     "name": "\\alpha",
     "meaning": "the ordinal index, $\\alpha > 0$"
    }
   ]
  },
  "E.ready": {
   "title": "(ready)",
   "what": "$\\neg\\mathsf{irred}\\,e \\Rightarrow \\mathsf{ready}_{W_1}(\\Theta \\mid F, e)$.",
   "why": "Readiness excludes circular waiting between threads.",
   "breaks": "Two threads each waiting on the partner of the other's second end deadlock.",
   "example": "$\\mathsf{ready}_W(\\Theta \\mid F, e)$.",
   "rocq": "relation/Relation.v: Ebody",
   "sig": "\\neg\\mathsf{irred}\\,e \\Rightarrow \\mathsf{ready}_{W_1}(\\Theta \\mid F, e)",
   "args": [
    {
     "name": "e",
     "meaning": "the term"
    },
    {
     "name": "W_1",
     "meaning": "the extension of $W$"
    }
   ]
  },
  "E.step": {
   "title": "(step)",
   "what": "$\\forall \\ell, e'.\\ e \\xrightarrow{\\ell} e' \\Rightarrow \\mathsf{Obl}_\\ell(e')$.",
   "why": "One conjunct per kind of label keeps $X$ strictly positive.",
   "breaks": "Nothing. It is a definition.",
   "example": "A send step meets O-Send.",
   "rocq": "relation/Relation.v: Esteps, Eobl",
   "sig": "\\forall \\ell, e'.\\ e \\xrightarrow{\\ell} e' \\Rightarrow \\mathsf{Obl}_\\ell(e')",
   "args": [
    {
     "name": "\\ell",
     "meaning": "a step label"
    },
    {
     "name": "e'",
     "meaning": "the successor"
    }
   ]
  },
  "O-Beta": {
   "title": "O-Beta",
   "what": "$e'$ at $\\Theta$.",
   "why": "A $\\beta$ step changes no end, and the compatibility of every elimination rule discharges it by reading the redex at the same environment.",
   "breaks": "Nothing. It is a definition.",
   "example": "Under $\\kappa_L$ a $\\beta$ step stays at level $n$.",
   "rocq": "relation/Relation.v: o_beta",
   "sig": "\\mathsf{o\\_beta} : \\mathsf{Expr} \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "W",
     "meaning": "the world, $W \\in \\mathsf{World}$"
    },
    {
     "name": "\\alpha",
     "meaning": "the level, an ordinal"
    },
    {
     "name": "\\Theta",
     "meaning": "the environment, a finite map $\\mathsf{End} \\rightharpoonup \\mathsf{STy} \\times \\mathsf{Point}$"
    },
    {
     "name": "T",
     "meaning": "the type, $T \\in \\mathsf{Ty}$"
    },
    {
     "name": "F",
     "meaning": "the future, a finite set of points"
    },
    {
     "name": "e, e'",
     "meaning": "a term and its successor, $e, e' \\in \\mathsf{Expr}$"
    }
   ]
  },
  "O-New": {
   "title": "O-New",
   "what": "For a fresh name $c$ some $S$, position $\\pi$ and world $W' \\sqsupseteq W$ place $c^{+}$ at $S@\\pi$ and $c^{-}$ at $\\overline{S}@\\overline{\\pi}$, and the successor runs in $W'$.",
   "why": "It is the semantic counterpart of E-New. The creation picks the point and grows the world by the roots it needs, ranking each new tree, and the existential property of ordinal indices fixes the choice once per creation. For a fresh root the fundamental theorem grows $W$ by that root and by the roots of the context points of $C$, with ranks above every context point below the tree.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{new}$ in the cycle.",
   "rocq": "relation/Relation.v: o_new; compat/Redex.v: Erel_new, Erel_new_fld",
   "sig": "\\mathsf{o\\_new} : \\mathsf{Chan} \\to \\mathsf{Expr} \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "W",
     "meaning": "the world, $W \\in \\mathsf{World}$"
    },
    {
     "name": "\\alpha",
     "meaning": "the level, an ordinal"
    },
    {
     "name": "\\Theta",
     "meaning": "the environment, a finite map $\\mathsf{End} \\rightharpoonup \\mathsf{STy} \\times \\mathsf{Point}$"
    },
    {
     "name": "T",
     "meaning": "the type, $T \\in \\mathsf{Ty}$"
    },
    {
     "name": "F",
     "meaning": "the future, a finite set of points"
    },
    {
     "name": "e, e'",
     "meaning": "a term and its successor, $e, e' \\in \\mathsf{Expr}$"
    },
    {
     "name": "c",
     "meaning": "the new channel name"
    },
    {
     "name": "S",
     "meaning": "the session type of $c^{+}$"
    },
    {
     "name": "\\pi",
     "meaning": "the position of $c^{+}$"
    },
    {
     "name": "W'",
     "meaning": "the grown world"
    }
   ]
  },
  "O-New.cfresh": {
   "title": "$c^{\\pm} \\notin \\mathrm{dom}\\,\\Theta$",
   "what": "The new name is no end of $\\Theta$.",
   "why": "The process rule picks $c$ globally fresh, so the term obligation may assume freshness.",
   "breaks": "Nothing. It is a definition.",
   "example": "$c^{+}, c^{-} \\notin \\mathrm{dom}\\,\\Theta$.",
   "rocq": "relation/Relation.v: cfresh",
   "sig": "c^{\\pm} \\notin \\mathrm{dom}\\,\\Theta : \\mathsf{Prop}",
   "args": [
    {
     "name": "c",
     "meaning": "the new channel name"
    },
    {
     "name": "\\Theta",
     "meaning": "the environment, a finite map $\\mathsf{End} \\rightharpoonup \\mathsf{STy} \\times \\mathsf{Point}$"
    }
   ]
  },
  "O-New.grow": {
   "title": "Position and world",
   "what": "$\\exists S, \\pi, W'.\\ W \\sqsubseteq W'$. The point $\\pi$ is any point, and $W'$ keeps every rank of $W$.",
   "why": "E-New at a fresh root picks a constant $a$ that $W$ does not rank and ranks its tree in $W'$ so that $C$ holds there. E-New at a field picks $x\\cdot\\kappa$ and keeps $W$. No rank changes, so the worlds of a run form a chain.",
   "breaks": "If a creation could change a rank, the measure of a waiting thread could rise.",
   "example": "At $\\pi = \\rho$ with $C = \\{\\rho \\prec \\overline{\\rho\\cdot 0},\\ \\overline{\\rho} \\prec \\rho\\cdot 0\\}$ the ranks $\\varrho(\\rho) = 0$ and $\\varrho(\\rho\\cdot 0) = 1$.",
   "rocq": "relation/Relation.v: o_new; types/Worlds.v: wgrow; compat/Redex.v: Erel_new",
   "sig": "\\exists S, \\pi, W'.\\ W \\sqsubseteq W'",
   "args": [
    {
     "name": "\\pi",
     "meaning": "the position"
    },
    {
     "name": "W'",
     "meaning": "a world that keeps every rank of $W$"
    }
   ]
  },
  "O-New.dual": {
   "title": "Dual placement",
   "what": "$\\Theta[c^{+} \\mapsto S@\\pi,\\ c^{-} \\mapsto \\overline{S}@\\overline{\\pi}]$.",
   "why": "It is the static result of E-New at the witness $\\pi$, and duality of the pair is what the lock-free process relation asks of restricted channels.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{new}$ gives $c^{+} : S@a$ and $c^{-} : \\overline{S}@\\overline{a}$.",
   "rocq": "relation/Relation.v: new_env",
   "sig": "\\Theta[c^{+} \\mapsto S@\\pi,\\ c^{-} \\mapsto \\overline{S}@\\overline{\\pi}] \\in \\mathsf{Env}",
   "args": [
    {
     "name": "c",
     "meaning": "the new channel"
    },
    {
     "name": "S",
     "meaning": "the chosen session type"
    },
    {
     "name": "\\pi",
     "meaning": "the position"
    }
   ]
  },
  "O-Spawn": {
   "title": "O-Spawn",
   "what": "$\\Theta$ splits into a part $\\Theta_M$ for the thunk, which is in $V^{W}_{\\alpha}\\llbracket\\Theta_M \\vdash \\ast \\multimap^{\\top}_{\\bot} \\ast\\rrbracket$, and a rest $\\Theta_r$ for the continuation.",
   "why": "Exactness of $V$ fixes $\\mathrm{dom}\\,\\Theta_M = \\mathsf{fends}(v)$, so the split is the same at every level.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{spawn}\\,(\\lambda\\_.\\,\\mathsf{close}\\,d')$ gives the child $\\{d'\\}$.",
   "rocq": "relation/Relation.v: o_spawn",
   "sig": "\\mathsf{o\\_spawn} : \\mathsf{Val} \\to \\mathsf{Expr} \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "W",
     "meaning": "the world, $W \\in \\mathsf{World}$"
    },
    {
     "name": "\\alpha",
     "meaning": "the level, an ordinal"
    },
    {
     "name": "\\Theta",
     "meaning": "the environment, a finite map $\\mathsf{End} \\rightharpoonup \\mathsf{STy} \\times \\mathsf{Point}$"
    },
    {
     "name": "T",
     "meaning": "the type, $T \\in \\mathsf{Ty}$"
    },
    {
     "name": "F",
     "meaning": "the future, a finite set of points"
    },
    {
     "name": "e, e'",
     "meaning": "a term and its successor, $e, e' \\in \\mathsf{Expr}$"
    },
    {
     "name": "v",
     "meaning": "the spawned thunk"
    },
    {
     "name": "\\Theta_M, \\Theta_r",
     "meaning": "the parts of the child and of the parent"
    }
   ]
  },
  "O-Spawn.split": {
   "title": "$\\Theta = \\Theta_M \\uplus \\Theta_r$",
   "what": "The child and the parent own disjoint parts of $\\Theta$.",
   "why": "The fundamental theorem builds the split from E-Spawn's split of the context, and the lock-free process relation moves exactly $\\Theta_M$ to the new thread.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\Theta_M = \\{d'\\}$.",
   "rocq": "relation/Relation.v: o_spawn",
   "sig": "\\exists \\Theta_M, \\Theta_r.\\ \\Theta = \\Theta_M \\uplus \\Theta_r",
   "args": [
    {
     "name": "\\Theta_M",
     "meaning": "the child's ends"
    },
    {
     "name": "\\Theta_r",
     "meaning": "the parent's ends"
    }
   ]
  },
  "O-Spawn.transfer": {
   "title": "$\\mathrm{dom}\\,\\Theta_M = \\mathsf{fends}(v)$",
   "what": "The part that leaves is exactly the set of ends of the value that leaves.",
   "why": "It follows from exactness of $V$, which makes ownership at a transfer independent of the level.",
   "breaks": "Without exactness, an end mentioned by neither side could go to either side at different levels.",
   "example": "$\\mathsf{fends}(\\lambda\\_.\\,\\mathsf{close}\\,d') = \\{d'\\}$.",
   "rocq": "relation/Relation.v: o_spawn, o_send",
   "sig": "\\mathrm{dom}\\,\\Theta_M = \\mathsf{fends}(v)",
   "args": [
    {
     "name": "\\Theta_M",
     "meaning": "the part that leaves"
    },
    {
     "name": "v",
     "meaning": "the value that leaves, the thunk or the payload"
    }
   ]
  },
  "O-Spawn.thunk": {
   "title": "$v \\in V^{W}_{\\alpha}\\llbracket\\Theta_M \\vdash \\ast \\multimap^{\\top}_{\\bot} \\ast\\rrbracket$",
   "what": "The thunk is a closure at upper point $\\top$ and lower point $\\bot$, in $V$ at the parent's level $n$. At $u = \\top$ its body is read at the empty future.",
   "why": "For $\\kappa_{spawn} = 0$ the child is read inside the parent's least fixpoint, so an infinite chain of spawns is in no $E_n$.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\lambda u.\\,\\mathsf{close}\\,d'$ at $\\Theta_M = \\{d'\\}$.",
   "rocq": "relation/Relation.v: o_spawn, Varr, Varr_top",
   "sig": "v \\in V^{W}_{\\alpha}\\llbracket\\Theta_M \\vdash \\ast \\multimap^{\\top}_{\\bot} \\ast\\rrbracket",
   "args": [
    {
     "name": "v",
     "meaning": "the thunk"
    },
    {
     "name": "\\Theta_M",
     "meaning": "its ends"
    }
   ]
  },
  "O-Send": {
   "title": "O-Send",
   "what": "The subject is at a send head, $\\Theta \\setminus o$ splits into the payload part $\\Theta_M$ and the rest, the payload is in $V$, and the continuation runs at the rest with $o$ at $S@x^{+}$.",
   "why": "Exactness of $V$ fixes $\\mathrm{dom}\\,\\Theta_M = \\mathsf{fends}(w)$.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{send}\\,\\langle a, y\\rangle$ in the growing ring.",
   "rocq": "relation/Relation.v: o_send",
   "sig": "\\mathsf{o\\_send} : \\mathsf{End} \\to \\mathsf{Val} \\to \\mathsf{Expr} \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "W",
     "meaning": "the world, $W \\in \\mathsf{World}$"
    },
    {
     "name": "\\alpha",
     "meaning": "the level, an ordinal"
    },
    {
     "name": "\\Theta",
     "meaning": "the environment, a finite map $\\mathsf{End} \\rightharpoonup \\mathsf{STy} \\times \\mathsf{Point}$"
    },
    {
     "name": "T",
     "meaning": "the type, $T \\in \\mathsf{Ty}$"
    },
    {
     "name": "F",
     "meaning": "the future, a finite set of points"
    },
    {
     "name": "e, e'",
     "meaning": "a term and its successor, $e, e' \\in \\mathsf{Expr}$"
    },
    {
     "name": "o",
     "meaning": "the subject end, $o \\in \\mathsf{End}$"
    },
    {
     "name": "w",
     "meaning": "the payload"
    },
    {
     "name": "x",
     "meaning": "the point of the subject, $x \\in \\mathsf{Point}$"
    },
    {
     "name": "S_0, S",
     "meaning": "the session type of the subject and its continuation after the head"
    },
    {
     "name": "m, U, b",
     "meaning": "the number of point variables, the type\\annp{ and the credit} of the payload"
    }
   ]
  },
  "O-Send.split": {
   "title": "$\\Theta \\setminus o = \\Theta_M \\uplus \\Theta_r$",
   "what": "The payload owns no copy of the subject $o$.",
   "why": "A send gives away held ends other than its subject.",
   "breaks": "A term that sends its own subject would leave the continuation acting on an end it gave away.",
   "example": "$\\Theta \\setminus o = \\Theta_M \\cup \\Theta_r$.",
   "rocq": "relation/Relation.v: o_send",
   "sig": "\\Theta \\setminus o = \\Theta_M \\uplus \\Theta_r",
   "args": [
    {
     "name": "\\Theta_M",
     "meaning": "the payload's ends"
    },
    {
     "name": "\\Theta_r",
     "meaning": "the remaining ends"
    }
   ]
  },
  "sr.head": {
   "title": "Head of an end $\\Theta(o) \\doteq S@x$",
   "what": "$\\Theta(o) \\doteq S@x$ states $\\Theta(o) = S_0@x$ for some $S_0$ with $\\mathsf{unfold}\\,S_0 = S$.",
   "why": "Every obligation reads the first action of the subject end after unfolding, so the notation states it once.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\Theta(o) \\doteq {!}(\\bar\\iota.\\,\\ast).\\mathsf{Close}@x$ for $\\Theta(o) = (\\mu\\alpha.\\,{!}\\ast.\\mathsf{Close})@x$.",
   "rocq": "relation/Relation.v: o_send, o_recv, o_close, o_select, o_branch",
   "sig": "\\Theta(o) \\doteq S@x \\iff \\exists S_0.\\ \\Theta(o) = S_0@x \\land \\mathsf{unfold}\\,S_0 = S",
   "args": [
    {
     "name": "\\Theta",
     "meaning": "the environment, a finite map $\\mathsf{End} \\rightharpoonup \\mathsf{STy} \\times \\mathsf{Point}$"
    },
    {
     "name": "o",
     "meaning": "the subject end"
    },
    {
     "name": "S",
     "meaning": "the head form of its protocol"
    }
   ]
  },
  "O-Send.payload": {
   "title": "Payload level",
   "what": "$w \\in V_{\\alpha}\\llbracket\\Theta_M \\vdash U[x\\cdot\\bar\\imath]\\rrbracket$, \\annp{and $V_{\\beta}$ for $\\beta + \\kappa_{give} \\leq \\alpha$ and for $\\beta = 0$ under a general table.}",
   "why": "The payload is read at the level of the continuation, because a send costs no level in the deadlock-free relation. \\annp{Under $\\kappa_L$ it costs one.}",
   "breaks": "Nothing. It is a definition.",
   "example": "The payload $a$ of $\\mathsf{send}\\,\\langle a, y\\rangle$ at $Y\\cdot 0$.",
   "rocq": "relation/Relation.v: o_send",
   "sig": "w \\in V^{W}_{\\beta}\\llbracket \\Theta_M \\vdash U[x\\cdot\\bar\\imath] \\rrbracket",
   "args": [
    {
     "name": "U[x\\cdot\\bar\\imath]",
     "meaning": "the payload type with its point variables at the fields $x\\cdot i$"
    }
   ]
  },
  "O-Send.shift": {
   "title": "$o : S@x^{+}$",
   "what": "The subject continues at $S$ and the next point $x^{+}$.",
   "why": "$x \\prec x^{+}$ holds in every world, so successive actions on one end are ordered.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\Theta_r[o \\mapsto S@x^{+}]$.",
   "rocq": "relation/Relation.v: o_send",
   "sig": "\\Theta_r[o \\mapsto S@x^{+}] \\in \\mathsf{Env}",
   "args": [
    {
     "name": "o",
     "meaning": "the subject end, $o \\in \\mathsf{End}$"
    },
    {
     "name": "x^{+}",
     "meaning": "the next point of $o$"
    }
   ]
  },
  "O-Recv": {
   "title": "O-Recv",
   "what": "For every $\\beta < \\alpha$ and every incoming $w \\in V_{\\beta}$ with ends disjoint from $\\Theta$, the continuation is in $E_{\\beta}$ with those ends added.",
   "why": "The value that arrives is unknown when the receiver is typed, so it continues for every value its type admits, and the compatibility of E-Recv pairs this with the sender's O-Send.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{let}\\ \\langle u, b\\rangle = \\mathsf{recv}\\,b\\ \\mathsf{in}\\ \\ldots$",
   "rocq": "relation/Relation.v: o_recv",
   "sig": "\\mathsf{o\\_recv} : \\mathsf{End} \\to \\mathsf{Val} \\to \\mathsf{Expr} \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "W",
     "meaning": "the world, $W \\in \\mathsf{World}$"
    },
    {
     "name": "\\alpha",
     "meaning": "the level, an ordinal"
    },
    {
     "name": "\\Theta",
     "meaning": "the environment, a finite map $\\mathsf{End} \\rightharpoonup \\mathsf{STy} \\times \\mathsf{Point}$"
    },
    {
     "name": "T",
     "meaning": "the type, $T \\in \\mathsf{Ty}$"
    },
    {
     "name": "F",
     "meaning": "the future, a finite set of points"
    },
    {
     "name": "e, e'",
     "meaning": "a term and its successor, $e, e' \\in \\mathsf{Expr}$"
    },
    {
     "name": "o",
     "meaning": "the subject end, $o \\in \\mathsf{End}$"
    },
    {
     "name": "w",
     "meaning": "the received value"
    },
    {
     "name": "x",
     "meaning": "the point of the subject, $x \\in \\mathsf{Point}$"
    },
    {
     "name": "S_0, S",
     "meaning": "the session type of the subject and its continuation after the head"
    }
   ]
  },
  "O-Recv.forall": {
   "title": "Every incoming value",
   "what": "$\\forall \\beta, \\Theta_{in}.\\ \\beta < \\alpha \\land \\Theta_{in} \\mathbin{\\#} \\Theta \\land w \\in V_{\\beta}\\llbracket\\Theta_{in} \\vdash U[x\\cdot\\bar\\imath]\\rrbracket$.",
   "why": "This negative occurrence of $V$ is at a lower level, so $V$ is well defined. \\annp{Under a general table the bound is $j + \\kappa_{take} \\leq n$, and $1 \\leq \\kappa_{take}$ keeps $\\beta < \\alpha$.}",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\forall j\\,\\Theta_{in}$.",
   "rocq": "relation/Relation.v: o_recv",
   "sig": "\\forall \\beta \\in \\mathsf{Ord}, \\Theta_{in}.\\ \\beta + \\kappa_{take} \\leq \\alpha \\land \\Theta_{in} \\mathbin{\\#} \\Theta \\land w \\in V_{\\beta}\\llbracket\\Theta_{in} \\vdash U[x\\cdot\\bar\\imath]\\rrbracket",
   "args": [
    {
     "name": "\\beta",
     "meaning": "the level of the incoming value"
    },
    {
     "name": "\\Theta_{in}",
     "meaning": "the ends it brings"
    }
   ]
  },
  "O-Recv.level": {
   "title": "Continuation at level $\\beta$",
   "what": "$e' \\in E_{\\beta}\\llbracket\\Theta[o \\mapsto S@x^{+}] \\cup \\Theta_{in} \\vdash T\\rrbracket^{F}$.",
   "why": "The continuation owns the old ends with $o$ advanced and the received ends, and is read at the level of the value it received.",
   "breaks": "Nothing. It is a definition.",
   "example": "$E_{\\beta}\\llbracket\\Theta[o \\mapsto S@x^{+}] \\cup \\Theta_{in} \\vdash T\\rrbracket^{F}$.",
   "rocq": "relation/Relation.v: o_recv",
   "sig": "e' \\in E^{W}_{\\beta}\\llbracket \\Theta[o \\mapsto S@x^{+}] \\cup \\Theta_{in} \\vdash T \\rrbracket^{F}",
   "args": [
    {
     "name": "\\beta",
     "meaning": "the level of the incoming value"
    },
    {
     "name": "\\Theta_{in}",
     "meaning": "the received ends"
    }
   ]
  },
  "O-Close": {
   "title": "O-Close",
   "what": "At a $\\mathsf{Close}$ head, $e'$ at $\\Theta \\setminus o$.",
   "why": "After the close nobody holds $o$, which matches the restriction removed by the process rule.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{close}\\,c^{+}$.",
   "rocq": "relation/Relation.v: o_close",
   "sig": "\\mathsf{o\\_close} : \\mathsf{End} \\to \\mathsf{Expr} \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "W",
     "meaning": "the world, $W \\in \\mathsf{World}$"
    },
    {
     "name": "\\alpha",
     "meaning": "the level, an ordinal"
    },
    {
     "name": "\\Theta",
     "meaning": "the environment, a finite map $\\mathsf{End} \\rightharpoonup \\mathsf{STy} \\times \\mathsf{Point}$"
    },
    {
     "name": "T",
     "meaning": "the type, $T \\in \\mathsf{Ty}$"
    },
    {
     "name": "F",
     "meaning": "the future, a finite set of points"
    },
    {
     "name": "e, e'",
     "meaning": "a term and its successor, $e, e' \\in \\mathsf{Expr}$"
    },
    {
     "name": "o",
     "meaning": "the subject end, $o \\in \\mathsf{End}$"
    }
   ]
  },
  "O-Select": {
   "title": "O-Select",
   "what": "At a head $\\oplus(S_1, S_2)$, $e'$ at $\\Theta[o \\mapsto S_i@\\overline{x\\cdot\\kappa_i}]$.",
   "why": "The selecting end keeps its name and moves to the dual side of the field of choice $i$, where E-Select places the end.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{select}_{\\mathsf{true}}\\,o$.",
   "rocq": "relation/Relation.v: o_select",
   "sig": "\\mathsf{o\\_select} : \\mathsf{End} \\to \\mathbb{B} \\to \\mathsf{Expr} \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "W",
     "meaning": "the world, $W \\in \\mathsf{World}$"
    },
    {
     "name": "\\alpha",
     "meaning": "the level, an ordinal"
    },
    {
     "name": "\\Theta",
     "meaning": "the environment, a finite map $\\mathsf{End} \\rightharpoonup \\mathsf{STy} \\times \\mathsf{Point}$"
    },
    {
     "name": "T",
     "meaning": "the type, $T \\in \\mathsf{Ty}$"
    },
    {
     "name": "F",
     "meaning": "the future, a finite set of points"
    },
    {
     "name": "e, e'",
     "meaning": "a term and its successor, $e, e' \\in \\mathsf{Expr}$"
    },
    {
     "name": "o",
     "meaning": "the subject end, $o \\in \\mathsf{End}$"
    },
    {
     "name": "i",
     "meaning": "the selected choice"
    }
   ]
  },
  "O-Branch": {
   "title": "O-Branch",
   "what": "For the choice $i$ the step took, $e'$ at $\\Theta[o \\mapsto S_i@x\\cdot\\kappa_i]$, one level later.",
   "why": "The branching end moves to the field of choice $i$, the dual point of the selecting side.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{branch}\\,o$.",
   "rocq": "relation/Relation.v: o_branch",
   "sig": "\\mathsf{o\\_branch} : \\mathsf{End} \\to \\mathbb{B} \\to \\mathsf{Expr} \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "W",
     "meaning": "the world, $W \\in \\mathsf{World}$"
    },
    {
     "name": "\\alpha",
     "meaning": "the level, an ordinal"
    },
    {
     "name": "\\Theta",
     "meaning": "the environment, a finite map $\\mathsf{End} \\rightharpoonup \\mathsf{STy} \\times \\mathsf{Point}$"
    },
    {
     "name": "T",
     "meaning": "the type, $T \\in \\mathsf{Ty}$"
    },
    {
     "name": "F",
     "meaning": "the future, a finite set of points"
    },
    {
     "name": "e, e'",
     "meaning": "a term and its successor, $e, e' \\in \\mathsf{Expr}$"
    },
    {
     "name": "o",
     "meaning": "the subject end, $o \\in \\mathsf{End}$"
    },
    {
     "name": "i",
     "meaning": "the received choice"
    }
   ]
  },
  "O-Link": {
   "title": "O-Link",
   "what": "Two distinct ends at $x$ and $\\overline{x}$ with dual types leave $\\Theta$.",
   "why": "After the link the partners of $o_1$ and $o_2$ form one channel, which is well typed only if $o_1$ and $o_2$ were dual.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{link}\\,\\langle c^{+}, d^{-}\\rangle$.",
   "rocq": "relation/Relation.v: o_link",
   "sig": "\\mathsf{o\\_link} : \\mathcal{P}_{\\mathrm{fin}}(\\mathsf{End}) \\to \\mathsf{Expr} \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "W",
     "meaning": "the world, $W \\in \\mathsf{World}$"
    },
    {
     "name": "\\alpha",
     "meaning": "the level, an ordinal"
    },
    {
     "name": "\\Theta",
     "meaning": "the environment, a finite map $\\mathsf{End} \\rightharpoonup \\mathsf{STy} \\times \\mathsf{Point}$"
    },
    {
     "name": "T",
     "meaning": "the type, $T \\in \\mathsf{Ty}$"
    },
    {
     "name": "F",
     "meaning": "the future, a finite set of points"
    },
    {
     "name": "e, e'",
     "meaning": "a term and its successor, $e, e' \\in \\mathsf{Expr}$"
    },
    {
     "name": "\\{o_1, o_2\\}",
     "meaning": "the linked ends"
    }
   ]
  },
  "O-Link.distinct": {
   "title": "$o_1 \\neq o_2$",
   "what": "A self link is rejected.",
   "why": "The link label is a set and may be degenerate.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{link}\\,\\langle c^{+}, c^{+}\\rangle$ is in no $E_n$.",
   "rocq": "relation/Relation.v: o_link",
   "sig": "o_1 \\neq o_2 : \\mathsf{Prop}",
   "args": [
    {
     "name": "o_1, o_2",
     "meaning": "the linked ends"
    }
   ]
  },
  "O-Link.dual": {
   "title": "Dual at dual points",
   "what": "$\\Theta(o_1) = S_1@x \\land \\Theta(o_2) = S_2@\\overline{x} \\land \\mathsf{sdual}\\,S_1\\,S_2$.",
   "why": "E-Link types the two ends exactly dual at dual points, and the lock-free process relation keeps restricted pairs dual, which the renaming of the link preserves only under this condition.",
   "breaks": "Nothing. It is a definition.",
   "example": "$c^{+} : S@x$ and $d^{-} : \\overline{S}@\\overline{x}$.",
   "rocq": "relation/Relation.v: o_link",
   "sig": "\\Theta(o_1) = S_1@x \\land \\Theta(o_2) = S_2@\\overline{x} \\land \\mathsf{sdual}\\,S_1\\,S_2",
   "args": [
    {
     "name": "S_1, S_2",
     "meaning": "the session types of the linked ends"
    },
    {
     "name": "x",
     "meaning": "the point of $o_1$"
    }
   ]
  },
  "rd.stable": {
   "title": "$\\mathsf{stable}\\,t$",
   "what": "$\\forall \\alpha, t'.\\ t \\xrightarrow{\\alpha} t' \\Rightarrow \\alpha \\text{ is a session label}$.",
   "why": "Readiness constrains only terms that wait for a partner.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{recv}\\,b$ is stable, $(\\lambda x.x)\\,\\ast$ is not.",
   "rocq": "relation/Readiness.v: stable_t",
   "sig": "\\mathsf{stable} : \\mathsf{Expr} \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "t",
     "meaning": "the term"
    }
   ]
  },
  "rd.offered": {
   "title": "$\\mathsf{offered}_\\Theta(t, o)$",
   "what": "$o \\in \\mathrm{dom}\\,\\Theta \\land \\exists \\sigma, t'.\\ t \\xrightarrow{\\sigma} t' \\land o \\in \\mathsf{subj}\\,\\sigma$.",
   "why": "Each end has its own entry, so the offered ends are read off the labels.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{recv}\\,b$ offers $b$.",
   "rocq": "relation/Readiness.v: offered_t",
   "sig": "\\mathsf{offered} : \\mathsf{Env} \\to \\mathsf{Expr} \\to \\mathsf{End} \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "\\Theta",
     "meaning": "the environment, a finite map $\\mathsf{End} \\rightharpoonup \\mathsf{STy} \\times \\mathsf{Point}$"
    },
    {
     "name": "t",
     "meaning": "the term"
    },
    {
     "name": "o",
     "meaning": "the end"
    }
   ]
  },
  "rd.value": {
   "title": "No offer means a value",
   "what": "$(\\forall o.\\ \\neg\\mathsf{offered}_\\Theta(t, o)) \\Rightarrow t \\in \\mathsf{Val}$.",
   "why": "A stable term offering only ends it does not hold would be stuck.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{close}\\,q$ with $q \\notin \\mathrm{dom}\\,\\Theta$ is not ready.",
   "rocq": "relation/Readiness.v: ready_t",
   "sig": "(\\forall o.\\ \\neg\\mathsf{offered}_\\Theta(t, o)) \\Rightarrow t \\in \\mathsf{Val}",
   "args": [
    {
     "name": "t",
     "meaning": "the term"
    }
   ]
  },
  "rd.link": {
   "title": "$\\mathsf{link}\\,t$",
   "what": "$\\exists os, t'.\\ t \\xrightarrow{\\leftrightarrow os} t'$, and a term at a link is ready.",
   "why": "A link step at process level needs no partner thread, so a link never waits and readiness need not order the link.",
   "breaks": "Asking the order of a link would reject every link next to an end held at an unrelated point, and E-Link has no order premise.",
   "example": "$\\mathsf{link}\\,\\langle c^{+}, d^{-}\\rangle$.",
   "rocq": "relation/Readiness.v: link_t",
   "sig": "\\mathsf{link} : \\mathsf{Expr} \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "t",
     "meaning": "the term"
    },
    {
     "name": "os",
     "meaning": "the linked ends of the step"
    }
   ]
  },
  "rd.below-rest": {
   "title": "$\\mathsf{below\\_rest}$",
   "what": "Every offered end at $x$ lies below the dual point of every held end it does not offer and below every point of $F$.",
   "why": "It excludes circular waiting, because a waiting thread's offer is minimal among what it holds and what its context still does.",
   "breaks": "Client and server each blocked on their second channel while holding the first, under a cyclic order.",
   "example": "Closing $c$ at $\\rho$ while $d$ is held at $\\rho\\cdot 0$ needs $\\rho \\prec \\overline{\\rho\\cdot 0}$.",
   "rocq": "relation/Readiness.v: below_rest",
   "sig": "\\mathsf{below\\_rest} : \\mathsf{World} \\to \\mathsf{Env} \\to (\\mathsf{End} \\to \\mathsf{Prop}) \\to \\mathcal{P}(\\mathsf{Point}) \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "W",
     "meaning": "the world, $W \\in \\mathsf{World}$"
    },
    {
     "name": "\\Theta",
     "meaning": "the environment, a finite map $\\mathsf{End} \\rightharpoonup \\mathsf{STy} \\times \\mathsf{Point}$"
    },
    {
     "name": "O",
     "meaning": "the offered ends"
    },
    {
     "name": "F",
     "meaning": "the future, a finite set of points"
    }
   ]
  },
  "rd.below-held": {
   "title": "Below held partners",
   "what": "$\\forall o' \\notin O.\\ \\Theta(o') = S'@x' \\Rightarrow W \\vdash x \\prec \\overline{x'}$.",
   "why": "The partner of a held end acts at $\\overline{x'}$, so the offered end is served before anyone waits on the held ends.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\rho \\prec \\overline{\\rho\\cdot 0}$.",
   "rocq": "relation/Readiness.v: below_rest",
   "sig": "\\forall o' \\notin O.\\ \\Theta(o') = S'@x' \\Rightarrow W \\vdash x \\prec \\overline{x'}",
   "args": [
    {
     "name": "x",
     "meaning": "the point of an offered end"
    },
    {
     "name": "o', x'",
     "meaning": "a held end that is not offered and its point"
    }
   ]
  },
  "rd.below-future": {
   "title": "Below the future",
   "what": "$\\forall y \\in F.\\ W \\vdash x \\prec y$.",
   "why": "The context acts at the points of $F$ after the term returns.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\kappa \\prec y$ for every $y$ above the upper point in $\\mathsf{between}$.",
   "rocq": "relation/Readiness.v: below_rest",
   "sig": "\\forall y \\in F.\\ W \\vdash x \\prec y",
   "args": [
    {
     "name": "x",
     "meaning": "the point of an offered end"
    },
    {
     "name": "y",
     "meaning": "a point of the future"
    }
   ]
  },
  "rd.p-stable": {
   "title": "$\\mathsf{stable}\\,p$",
   "what": "$p$ takes no internal step.",
   "why": "A process with an internal step is not waiting, and readiness speaks only of waiting processes.",
   "breaks": "Nothing. It is a definition.",
   "example": "A thread at an external $\\mathsf{recv}$.",
   "rocq": "relation/Readiness.v: stable_p",
   "sig": "\\mathsf{stable} : \\mathsf{Proc} \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "p",
     "meaning": "the process, $p = (C, E) \\in \\mathsf{Proc}$"
    }
   ]
  },
  "rd.p-term": {
   "title": "No offer means terminated",
   "what": "$(\\forall o.\\ \\neg\\mathsf{offered}_\\Sigma(p, o)) \\Rightarrow \\mathsf{terminated}\\,p$.",
   "why": "A stable process that offers nothing to its environment must be finished, which is the deadlock-freedom statement at the process level.",
   "breaks": "Without it, a stable process blocked on internal ends would satisfy P-Ready.",
   "example": "$(\\varnothing, \\{\\ast\\})$.",
   "rocq": "relation/Readiness.v: ready_p",
   "sig": "(\\forall o.\\ \\neg\\mathsf{offered}_\\Sigma(p, o)) \\Rightarrow \\mathsf{terminated}\\,p",
   "args": [
    {
     "name": "\\Sigma",
     "meaning": "the interface, a finite map $\\mathsf{End} \\rightharpoonup \\mathsf{STy} \\times \\mathsf{Point}$"
    },
    {
     "name": "p",
     "meaning": "the process, $p = (C, E) \\in \\mathsf{Proc}$"
    }
   ]
  },
  "rd.above-offered": {
   "title": "$\\mathsf{above\\_offered}$",
   "what": "Every interface end at $x$ that is not offered has an offered end at $x'$ with $W \\vdash x' \\prec \\overline{x}$.",
   "why": "The environment can always serve some offered end first, so composing two ready processes over a ranked world keeps one of them able to move.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{above\\_offered}\\,W\\,\\Sigma\\,O$.",
   "rocq": "relation/Readiness.v: above_offered",
   "sig": "\\mathsf{above\\_offered} : \\mathsf{World} \\to \\mathsf{Env} \\to (\\mathsf{End} \\to \\mathsf{Prop}) \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "W",
     "meaning": "the world, $W \\in \\mathsf{World}$"
    },
    {
     "name": "\\Sigma",
     "meaning": "the interface, a finite map $\\mathsf{End} \\rightharpoonup \\mathsf{STy} \\times \\mathsf{Point}$"
    },
    {
     "name": "o, x",
     "meaning": "an interface end that is not offered and its point"
    },
    {
     "name": "o', x'",
     "meaning": "an offered end and its point"
    }
   ]
  },
  "P.strict": {
   "title": "Later worlds",
   "what": "Each unfolding of $P$ holds in each ranked world $W_1 \\sqsupseteq W$.",
   "why": "Composition places a process into a larger world. A ranked world has no cycle, so no strictness premise remains.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\forall W_1 \\sqsupseteq W.\\ \\ldots$",
   "rocq": "relation/Relation.v: Pbody",
   "sig": "\\forall W_1 \\sqsupseteq W.\\ \\ldots",
   "args": [
    {
     "name": "W",
     "meaning": "the world, $W \\in \\mathsf{World}$"
    },
    {
     "name": "W_1",
     "meaning": "a ranked extension of $W$"
    }
   ]
  },
  "P.clauses": {
   "title": "$\\mathsf{clauses}_{W_1}(\\Sigma', p')$",
   "what": "The stop, ready and step clauses of $p'$ at the interface $\\Sigma'$ in the world $W_1$.",
   "why": "$P$ asks them after each fusion, and a term asks the same three of itself.",
   "breaks": "Nothing. It is a definition.",
   "example": "A finished process $(\\varnothing, \\{v\\})$ meets them when $v \\in V$.",
   "rocq": "relation/Relation.v: Pclauses",
   "sig": "\\mathsf{clauses}_{W_1} : \\mathsf{Env} \\to \\mathsf{Proc} \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "W_1",
     "meaning": "the later ranked world"
    },
    {
     "name": "\\Sigma'",
     "meaning": "the interface after the fusion"
    },
    {
     "name": "p'",
     "meaning": "the process after the fusion"
    }
   ]
  },
  "P.fuse": {
   "title": "Closed under fusions",
   "what": "Each unfolding holds at $(h, D)\\cdot\\Sigma$ and $(h, D)\\cdot p$ for every $(h, D) \\in \\mathsf{Fus}(\\Sigma, p)$.",
   "why": "Renaming, internalizing a pair of interface ends and the renaming done by a link are all fusions, and closure by definition makes each of them a projection.",
   "breaks": "With renamings alone, a link could join two unrelated interface ends into one channel and composition would fail.",
   "example": "$h = \\mathsf{id}$ internalizes pairs, $D = \\varnothing$ renames.",
   "rocq": "relation/Relation.v: Pbody",
   "sig": "\\forall (h, D) \\in \\mathsf{Fus}(\\Sigma, p).\\ \\ldots",
   "args": [
    {
     "name": "h",
     "meaning": "a map of ends"
    },
    {
     "name": "D",
     "meaning": "the channels the fusion restricts"
    }
   ]
  },
  "P-Stop": {
   "title": "P-Stop",
   "what": "$\\mathsf{pirred}\\,p' \\Rightarrow \\exists v, E.\\ p' = (\\varnothing, \\{v\\} \\uplus E) \\land v \\in V\\llbracket\\Sigma' \\vdash T\\rrbracket \\land \\forall e \\in E.\\ e = \\ast$.",
   "why": "An irreducible process in $P$ has no restricted channel left, its main thread returned a value in $V$ and every other thread returned $\\ast$, which is the definition of terminated.",
   "breaks": "Without it, a process stuck with restricted channels would be in $P$, and adequacy would fail.",
   "example": "$(\\varnothing, \\{\\ast, \\ast\\})$ at $T = \\ast$.",
   "rocq": "relation/Relation.v: Pclauses",
   "sig": "\\mathsf{pirred}\\,p' \\Rightarrow \\exists v, E.\\ p' = (\\varnothing, \\{v\\} \\uplus E) \\land \\ldots",
   "args": [
    {
     "name": "p'",
     "meaning": "the fused process"
    },
    {
     "name": "v",
     "meaning": "the main thread's value"
    },
    {
     "name": "E",
     "meaning": "the other threads, all $\\ast$"
    }
   ]
  },
  "P-Ready": {
   "title": "P-Ready",
   "what": "$\\neg\\mathsf{pirred}\\,p' \\Rightarrow \\mathsf{ready}_{W_1}(\\Sigma', p')$.",
   "why": "Readiness of processes excludes circular waiting across the interface.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{ready}_{W_1}(\\Sigma', p')$.",
   "rocq": "relation/Relation.v: Pclauses",
   "sig": "\\neg\\mathsf{pirred}\\,p' \\Rightarrow \\mathsf{ready}_{W_1}(\\Sigma', p')",
   "args": [
    {
     "name": "\\Sigma', p'",
     "meaning": "the fused interface and process"
    },
    {
     "name": "W_1",
     "meaning": "the strict extension"
    }
   ]
  },
  "P-Step": {
   "title": "P-Step",
   "what": "Every step $p' \\xrightarrow{ev} p''$ meets $\\mathsf{Pobl}_{ev}$. A process steps when some numbering of its threads steps, $p \\xrightarrow{ev} p' \\iff \\exists q, q'.\\ \\mathsf{erase}\\,q = p \\land q \\xrightarrow{ev} q' \\land \\mathsf{erase}\\,q' = p'$.",
   "why": "The obligations read the event and the result, and no thread number. Thread numbers matter only to the lock-free process relation, which records the thread holding each end.",
   "breaks": "Nothing. It is a definition.",
   "example": "A message between two threads meets Q-Tau.",
   "rocq": "relation/Relation.v: Psteps",
   "sig": "\\forall ev, p''.\\ p' \\xrightarrow{ev} p'' \\Rightarrow \\mathsf{Pobl}_{ev}(p'')",
   "args": [
    {
     "name": "p''",
     "meaning": "the process after the step"
    },
    {
     "name": "ev",
     "meaning": "the event"
    }
   ]
  },
  "fuse.dcomm": {
   "title": "$h$ commutes with duality",
   "what": "$\\forall o.\\ h(\\overline{o}) = \\overline{h(o)}$.",
   "why": "Restricted channels and the partners added by Q-Send and Q-Recv enter $P$ as pairs, which $h$ must map to pairs.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{csub}\\,o_1\\,o_2$ commutes with duality.",
   "rocq": "relation/Relation.v: dcomm",
   "sig": "\\forall o.\\ h(\\overline{o}) = \\overline{h(o)}",
   "args": [
    {
     "name": "h",
     "meaning": "the map of ends"
    }
   ]
  },
  "fuse.inj": {
   "title": "Injective on held ends",
   "what": "$\\forall o_1, o_2 \\in \\mathsf{held}.\\ h(o_1) = h(o_2) \\Rightarrow o_1 = o_2$.",
   "why": "$\\mathsf{csub}$ of a link identifies $\\overline{o_1}$ and $o_2$, so $h$ is no bijection, but it is injective on the held ends of the other component.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{csub}$ is injective on the other side's held ends.",
   "rocq": "relation/Relation.v: fuse_ok",
   "sig": "\\forall o_1, o_2 \\in \\mathsf{held}.\\ h(o_1) = h(o_2) \\Rightarrow o_1 = o_2",
   "args": [
    {
     "name": "o_1, o_2",
     "meaning": "held ends of $p$"
    }
   ]
  },
  "fuse.partners": {
   "title": "New partners only on $D$",
   "what": "$h(o_2) = \\overline{h(o_1)} \\Rightarrow o_2 = \\overline{o_1} \\lor \\mathsf{ech}(h\\,o_1) \\in D$.",
   "why": "Two held ends become partners only if they were or their channel is restricted by the fusion.",
   "breaks": "Without it, $h$ joins unrelated interface ends into one channel, and composition fails.",
   "example": "$D = \\varnothing$ creates no new pair.",
   "rocq": "relation/Relation.v: fuse_ok",
   "sig": "h(o_2) = \\overline{h(o_1)} \\Rightarrow o_2 = \\overline{o_1} \\lor \\mathsf{ech}(h\\,o_1) \\in D",
   "args": [
    {
     "name": "o_1, o_2",
     "meaning": "held ends of $p$"
    },
    {
     "name": "D",
     "meaning": "the channels the fusion restricts"
    }
   ]
  },
  "fuse.D": {
   "title": "$D \\cap \\mathsf{gch}_h[C] = \\varnothing$",
   "what": "The channels restricted by the fusion are not images of channels already restricted.",
   "why": "Composition splits a fused process into its two sides, and this condition keeps the two restricted sets $\\mathsf{gch}_h[C_i] \\cup D_i$ disjoint from each other and from the interface.",
   "breaks": "Without it, a restricted channel could be restricted again as a new pair, and the split of the fused composite fails.",
   "example": "$D \\mathbin{\\#} \\mathsf{gch}_h[C]$.",
   "rocq": "relation/Relation.v: fuse_ok",
   "sig": "D \\cap \\mathsf{gch}_h[C] = \\varnothing",
   "args": [
    {
     "name": "D",
     "meaning": "the channels the fusion restricts"
    },
    {
     "name": "C",
     "meaning": "the restricted channels of $p$"
    }
   ]
  },
  "fuse.dpairs": {
   "title": "$\\mathsf{dpairs}\\,D\\,\\Sigma$",
   "what": "Both ends of every channel of $D$ are in $\\Sigma$, at dual points and dual types.",
   "why": "They become restricted, and restricted channels are dual pairs.",
   "breaks": "Nothing. It is a definition.",
   "example": "Internalizing $c$ with $\\Sigma(c^{+}) = S@x$ and $\\Sigma(c^{-}) = \\overline{S}@\\overline{x}$.",
   "rocq": "relation/Relation.v: dpairs",
   "sig": "\\mathsf{dpairs} : \\mathcal{P}_{\\mathrm{fin}}(\\mathsf{Chan}) \\to \\mathsf{Env} \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "D",
     "meaning": "the channels"
    },
    {
     "name": "\\Sigma",
     "meaning": "the interface, a finite map $\\mathsf{End} \\rightharpoonup \\mathsf{STy} \\times \\mathsf{Point}$"
    }
   ]
  },
  "Q-Tau": {
   "title": "Q-Tau",
   "what": "An internal step that restricts no interface channel keeps $\\Sigma$, costs the levels of its kind of step and continues in some world $W' \\sqsupseteq W$.",
   "why": "Administrative steps and internal synchronizations are one clause. A creation among them may grow the world.",
   "breaks": "Nothing. It is a definition.",
   "example": "A message between two threads costs one level\\annp{, and $\\kappa_{give} + \\kappa_{take}$ under a general table}.",
   "rocq": "relation/Relation.v: q_tau",
   "sig": "\\mathsf{q\\_tau} : \\mathsf{Event} \\to \\mathsf{Proc} \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "W",
     "meaning": "the world, $W \\in \\mathsf{World}$"
    },
    {
     "name": "\\alpha",
     "meaning": "the level, an ordinal"
    },
    {
     "name": "\\Sigma",
     "meaning": "the interface, a finite map $\\mathsf{End} \\rightharpoonup \\mathsf{STy} \\times \\mathsf{Point}$"
    },
    {
     "name": "T",
     "meaning": "the type, $T \\in \\mathsf{Ty}$"
    },
    {
     "name": "p, p'",
     "meaning": "the process before and after the step, $p = (C, E)$ and $p' = (C', E')$"
    },
    {
     "name": "ev",
     "meaning": "the internal event"
    }
   ]
  },
  "Q-Send": {
   "title": "Q-Send",
   "what": "An external send. The interface part $\\Sigma_v$ and the restricted part $\\Theta_e$ of the payload leave, and the partners $\\Sigma_e$ left behind join the interface.",
   "why": "It is O-Send at the process level, and the compatibility of P-Term discharges it from O-Send of the thread.",
   "breaks": "Nothing. It is a definition.",
   "example": "Sending a restricted end $d^{+}$ puts $d^{-}$ into the interface.",
   "rocq": "relation/Relation.v: q_send",
   "sig": "\\mathsf{q\\_send} : \\mathsf{End} \\to \\mathsf{Val} \\to \\mathsf{Proc} \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "W",
     "meaning": "the world, $W \\in \\mathsf{World}$"
    },
    {
     "name": "\\alpha",
     "meaning": "the level, an ordinal"
    },
    {
     "name": "\\Sigma",
     "meaning": "the interface, a finite map $\\mathsf{End} \\rightharpoonup \\mathsf{STy} \\times \\mathsf{Point}$"
    },
    {
     "name": "T",
     "meaning": "the type, $T \\in \\mathsf{Ty}$"
    },
    {
     "name": "p, p'",
     "meaning": "the process before and after the step, $p = (C, E)$ and $p' = (C', E')$"
    },
    {
     "name": "o",
     "meaning": "the subject end, $o \\in \\mathsf{End}$"
    },
    {
     "name": "w",
     "meaning": "the payload"
    },
    {
     "name": "\\Sigma_v, \\Sigma_r",
     "meaning": "the interface ends of the payload and the rest"
    },
    {
     "name": "\\Theta_e, \\Sigma_e",
     "meaning": "the restricted ends that leave and their partners that stay"
    }
   ]
  },
  "Q-Send.theta-e": {
   "title": "Extruded ends $\\Theta_e$",
   "what": "$\\mathrm{dom}\\,\\Theta_e = \\{o' \\in \\mathsf{fends}(w) \\mid \\mathsf{ech}(o') \\in C\\}$.",
   "why": "$\\Theta_e$ is exactly the restricted part of the ends of $w$. Exactness of $V$ at the payload gives $\\mathsf{fends}(w) = \\mathrm{dom}\\,\\Sigma_v \\cup \\mathrm{dom}\\,\\Theta_e$, so the payload has $\\mathsf{fends}(w)$ and nothing else.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\Theta_e = \\{d^{+}\\}$.",
   "rocq": "relation/Relation.v: q_send, compat/Redex.v: Vrel_exact",
   "sig": "\\mathrm{dom}\\,\\Theta_e = \\{o' \\in \\mathsf{fends}(w) \\mid \\mathsf{ech}(o') \\in C\\}",
   "args": [
    {
     "name": "\\Theta_e",
     "meaning": "the restricted ends of the payload"
    },
    {
     "name": "w",
     "meaning": "the payload"
    },
    {
     "name": "C",
     "meaning": "the restricted channels"
    },
    {
     "name": "\\Sigma_v",
     "meaning": "the interface ends of the payload"
    }
   ]
  },
  "Q-Send.split": {
   "title": "$\\mathsf{send\\_split}$",
   "what": "The extruded ends are no interface ends, and $\\Sigma_e$ holds the partners of extruded ends that stay, at dual types and points.",
   "why": "The partner of an extruded end becomes an interface end, and the interface must record its type and point.",
   "breaks": "Without it, the process would keep an end its interface does not mention, and P-Stop could not hold.",
   "example": "$\\Sigma_e = \\{d^{-}\\}$.",
   "rocq": "relation/Relation.v: send_split",
   "sig": "\\mathsf{send\\_split} : \\mathsf{Env} \\to \\mathsf{Env} \\to \\mathsf{Env} \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "\\Sigma",
     "meaning": "the interface, a finite map $\\mathsf{End} \\rightharpoonup \\mathsf{STy} \\times \\mathsf{Point}$"
    },
    {
     "name": "\\Sigma_e",
     "meaning": "the partners that join the interface"
    },
    {
     "name": "\\Theta_e",
     "meaning": "the extruded ends"
    }
   ]
  },
  "Q-Send.sigma-e": {
   "title": "$\\Sigma_e$ joins the interface",
   "what": "Partners of extruded ends become interface ends.",
   "why": "Scope extrusion frees their channel.",
   "breaks": "Nothing. It is a definition.",
   "example": "$d^{-}$ joins $\\Sigma$.",
   "rocq": "relation/Relation.v: q_send",
   "sig": "\\Sigma_e \\in \\mathsf{Env}",
   "args": [
    {
     "name": "\\Sigma_e",
     "meaning": "the partners of extruded ends"
    }
   ]
  },
  "Q-Recv": {
   "title": "Q-Recv",
   "what": "For every incoming environment and value, the process continues with the received ends added and the channels both of whose ends it now holds restricted.",
   "why": "It is O-Recv at the process level, and composition feeds one component's Q-Send into the other's Q-Recv.",
   "breaks": "Nothing. It is a definition.",
   "example": "Receiving $d^{-}$ while holding $d^{+}$ restricts $d$.",
   "rocq": "relation/Relation.v: q_recv",
   "sig": "\\mathsf{q\\_recv} : \\mathsf{End} \\to \\mathsf{Val} \\to \\mathsf{Proc} \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "W",
     "meaning": "the world, $W \\in \\mathsf{World}$"
    },
    {
     "name": "\\alpha",
     "meaning": "the level, an ordinal"
    },
    {
     "name": "\\Sigma",
     "meaning": "the interface, a finite map $\\mathsf{End} \\rightharpoonup \\mathsf{STy} \\times \\mathsf{Point}$"
    },
    {
     "name": "T",
     "meaning": "the type, $T \\in \\mathsf{Ty}$"
    },
    {
     "name": "p, p'",
     "meaning": "the process before and after the step, $p = (C, E)$ and $p' = (C', E')$"
    },
    {
     "name": "o",
     "meaning": "the subject end, $o \\in \\mathsf{End}$"
    },
    {
     "name": "w",
     "meaning": "the received value"
    },
    {
     "name": "\\beta",
     "meaning": "the level of the value"
    },
    {
     "name": "\\Theta_2",
     "meaning": "the ends it brings"
    },
    {
     "name": "\\Sigma'",
     "meaning": "$\\Sigma[o \\mapsto S@x^{+}]$"
    }
   ]
  },
  "Q-Recv.ok": {
   "title": "$\\mathsf{recv\\_ok}$",
   "what": "Incoming ends are new to $\\Sigma$, and every incoming end whose partner is held or received is at the dual point with the dual type.",
   "why": "Composition delivers one component's payload only under this condition, and it is what makes a newly restricted pair dual.",
   "breaks": "Without the duality conjunct, receiving the partner of a held end at a mismatched type would restrict an ill-typed channel.",
   "example": "$\\mathsf{recv\\_ok}\\,\\Sigma\\,\\Theta_2$.",
   "rocq": "relation/Relation.v: recv_ok",
   "sig": "\\mathsf{recv\\_ok} : \\mathsf{Env} \\to \\mathsf{Env} \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "\\Sigma",
     "meaning": "the interface, a finite map $\\mathsf{End} \\rightharpoonup \\mathsf{STy} \\times \\mathsf{Point}$"
    },
    {
     "name": "\\Theta_2",
     "meaning": "the incoming ends"
    }
   ]
  },
  "Q-Recv.back": {
   "title": "$\\mathsf{recv\\_back}$",
   "what": "The channels of incoming ends whose partner is held or received along.",
   "why": "Both ends of such a channel are now in the process, so it is restricted, as the interface stays partner-free.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{recv\\_back}\\,\\Sigma\\,\\{d^{-}\\} = \\{d\\}$ for $d^{+} \\in \\mathrm{dom}\\,\\Sigma$.",
   "rocq": "relation/Relation.v: recv_back",
   "sig": "\\mathsf{recv\\_back} : \\mathsf{Env} \\to \\mathsf{Env} \\to \\mathcal{P}_{\\mathrm{fin}}(\\mathsf{Chan})",
   "args": [
    {
     "name": "\\Sigma",
     "meaning": "the interface, a finite map $\\mathsf{End} \\rightharpoonup \\mathsf{STy} \\times \\mathsf{Point}$"
    },
    {
     "name": "\\Theta_2",
     "meaning": "the incoming ends"
    }
   ]
  },
  "Q-Recv.env": {
   "title": "$\\mathsf{recv\\_env}$",
   "what": "The interface after the receive, without the ends that became internal.",
   "why": "Internal ends leave the interface, and the rest of $\\Theta_2$ joins the interface.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{recv\\_env}\\,\\Sigma\\,\\Theta_2$.",
   "rocq": "relation/Relation.v: recv_env",
   "sig": "\\mathsf{recv\\_env} : \\mathsf{Env} \\to \\mathsf{Env} \\to \\mathsf{Env}",
   "args": [
    {
     "name": "\\Sigma",
     "meaning": "the interface, a finite map $\\mathsf{End} \\rightharpoonup \\mathsf{STy} \\times \\mathsf{Point}$"
    },
    {
     "name": "\\Theta_2",
     "meaning": "the incoming ends"
    }
   ]
  },
  "Q-Link": {
   "title": "Q-Close, Q-Select, Q-Branch, Q-Link",
   "what": "The term obligations O-Close, O-Select, O-Branch and O-Link with $\\Sigma$ for $\\Theta$ and $P$ for $E$.",
   "why": "An external close, choice or link acts on interface ends exactly as a thread acts on its own ends.",
   "breaks": "Nothing. It is a definition.",
   "example": "Q-Link removes both linked ends from $\\Sigma$.",
   "rocq": "relation/Relation.v: q_close, q_select, q_branch, q_link",
   "sig": "\\mathsf{q\\_close}, \\mathsf{q\\_select}, \\mathsf{q\\_branch}, \\mathsf{q\\_link}",
   "args": [
    {
     "name": "W",
     "meaning": "the world, $W \\in \\mathsf{World}$"
    },
    {
     "name": "\\alpha",
     "meaning": "the level, an ordinal"
    },
    {
     "name": "\\Sigma",
     "meaning": "the interface, a finite map $\\mathsf{End} \\rightharpoonup \\mathsf{STy} \\times \\mathsf{Point}$"
    },
    {
     "name": "T",
     "meaning": "the type, $T \\in \\mathsf{Ty}$"
    },
    {
     "name": "p, p'",
     "meaning": "the process before and after the step, $p = (C, E)$ and $p' = (C', E')$"
    }
   ]
  },
  "sj.at": {
   "title": "Judgment at a set of points $X$",
   "what": "For every level, later world, environment $\\Theta'$ disjoint from the ends $|\\Delta|$ and grounding $\\gamma$ of the variables of $\\Delta$ in $\\Theta'$, $\\gamma(e) \\in E_\\alpha\\llbracket|\\Delta| \\cup \\Theta' \\vdash T\\rrbracket^{X}$, over every ordinal index $\\alpha$.",
   "why": "It quantifies over everything a context may supply, so it composes by the compatibility lemmas.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\Delta \\vDash^{X}_W e : T$.",
   "rocq": "compat/SemTyped.v: sem_typed_at",
   "sig": "\\Delta \\vDash^{X}_{W} e : T",
   "args": [
    {
     "name": "\\Delta",
     "meaning": "the linear context of the typing judgment, its ends erased to $|\\Delta|$"
    },
    {
     "name": "X",
     "meaning": "a set of points read as the future"
    },
    {
     "name": "n, W', \\Theta', \\gamma",
     "meaning": "every level, extension, environment of the grounding and grounding"
    }
   ]
  },
  "sj.grel": {
   "title": "Grounding $\\gamma \\in G\\llbracket\\Theta \\vdash \\Delta\\rrbracket$",
   "what": "$\\gamma$ substitutes for each entry $T^a$ of $\\Delta$ a value in $V\\llbracket\\Theta_i \\vdash T\\rrbracket$, with $\\Theta = \\biguplus_i \\Theta_i$.",
   "why": "Variables of $\\Delta$ stand for values, and the ends of those values split $\\Theta$ disjointly.",
   "breaks": "Nothing. It is a definition.",
   "example": "For $\\Delta = [T]$, $\\gamma(0) \\in V\\llbracket\\Theta \\vdash T\\rrbracket$.",
   "rocq": "compat/SemTyped.v: Grel",
   "sig": "\\gamma \\in G^{W}_{\\alpha}\\llbracket \\Theta \\vdash \\Delta \\rrbracket",
   "args": [
    {
     "name": "\\gamma",
     "meaning": "a substitution $\\mathbb{N} \\to \\mathsf{Expr}$ for the variables of $\\Delta$"
    },
    {
     "name": "\\Theta",
     "meaning": "the environment, a finite map $\\mathsf{End} \\rightharpoonup \\mathsf{STy} \\times \\mathsf{Point}$"
    },
    {
     "name": "\\Delta",
     "meaning": "the linear context"
    }
   ]
  },
  "sj.den": {
   "title": "$\\mathsf{den}_{R,B}(F)$",
   "what": "$\\mathsf{den}_{R,B}(F_1, f) = F_1 \\cup R \\cup B$, with $R$ only if $f$ has a rest and $B$ only if $f$ has the flag $\\bot$. For the rest $ {\\uparrow}u$ every point of $R$ lies above $u$.",
   "why": "The rest and the flag $\\bot$ stand for unknown sets of points, so the judgment holds at each choice of these sets.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{den}_{R,B}(\\varnothing, {\\uparrow}u) = R$.",
   "rocq": "compat/SemTyped.v: sf_den, rest_ok",
   "sig": "\\mathsf{den} : \\mathcal{P}(\\mathsf{Point}) \\to \\mathcal{P}(\\mathsf{Point}) \\to \\mathsf{SFuture} \\to \\mathcal{P}(\\mathsf{Point})",
   "args": [
    {
     "name": "R",
     "meaning": "the denotation of the rest"
    },
    {
     "name": "B",
     "meaning": "the denotation of the flag $\\bot$"
    },
    {
     "name": "F",
     "meaning": "the static future"
    }
   ]
  },
  "sj.term": {
   "title": "$\\Delta \\vDash^{F}_W e : T$",
   "what": "$\\forall \\rho, B.\\ \\Delta \\vDash^{\\mathsf{den}_{\\rho,B}(F)}_W e : T$, with the same context $\\Delta$ as the typing judgment.",
   "why": "It is the conclusion of the fundamental theorem for terms. \\annp{The lock-free reading $\\vDash[\\kappa_L]$ uses the table $\\kappa_L$.}",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\varnothing \\vDash^{\\varnothing}_W e : T$.",
   "rocq": "compat/SemTyped.v: sem_typed",
   "sig": "\\Delta \\vDash^{F}_{W} e : T",
   "args": [
    {
     "name": "\\Delta",
     "meaning": "the linear context"
    },
    {
     "name": "F",
     "meaning": "the static future"
    },
    {
     "name": "W",
     "meaning": "the world, $W \\in \\mathsf{World}$"
    },
    {
     "name": "e, T",
     "meaning": "the term and its type"
    }
   ]
  },
  "sj.proc": {
   "title": "$\\Sigma \\vDash_W p : T$",
   "what": "$\\forall \\alpha.\\ p \\in P^W_\\alpha\\llbracket\\Sigma \\vdash T\\rrbracket$, over every ordinal index $\\alpha$.",
   "why": "Adequacy turns it into deadlock freedom. \\annp{With $\\kappa_L$ it also gives absence of internal divergence.}",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\varnothing \\vDash_W p : \\ast$.",
   "rocq": "relation/Adequacy.v: sem_ptyped",
   "sig": "\\Sigma \\vDash_{W} p : T",
   "args": [
    {
     "name": "\\Sigma",
     "meaning": "the interface, a finite map $\\mathsf{End} \\rightharpoonup \\mathsf{STy} \\times \\mathsf{Point}$"
    },
    {
     "name": "W",
     "meaning": "the world, $W \\in \\mathsf{World}$"
    },
    {
     "name": "p",
     "meaning": "the process, $p = (C, E) \\in \\mathsf{Proc}$"
    },
    {
     "name": "T",
     "meaning": "the type, $T \\in \\mathsf{Ty}$"
    }
   ]
  },
  "fu.zero": {
   "title": "Index $0$",
   "what": "$F_0$ holds every term.",
   "why": "Step indexing starts from the trivial predicate.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\forall e.\\ e \\in F^N_0\\llbracket\\Phi \\vdash \\sigma\\ !\\ d\\rrbracket$.",
   "rocq": "fuel/Fuel.v: mk_flevel",
   "sig": "e \\in F^{N}_{\\alpha}\\llbracket \\Phi \\vdash \\sigma\\ !\\ d \\rrbracket",
   "args": [
    {
     "name": "N",
     "meaning": "the bound on the tickets of a channel, $N \\in \\mathbb{N} \\cup \\{\\infty\\}$"
    },
    {
     "name": "\\alpha",
     "meaning": "the ordinal index"
    },
    {
     "name": "\\Phi",
     "meaning": "the held ends, a finite map $o \\mapsto S^{f}_{m}$ from ends to a protocol, a counter $f$ and tickets $m \\geq f$"
    },
    {
     "name": "\\sigma",
     "meaning": "the result, a credited type or $\\mathsf{thread}$"
    },
    {
     "name": "d",
     "meaning": "the frame, the actions left before returning, $d \\in \\mathbb{N} \\cup \\{\\infty\\}$"
    },
    {
     "name": "e",
     "meaning": "the term"
    }
   ]
  },
  "fu.rty": {
   "title": "Result $\\sigma$",
   "what": "$\\sigma$ is a credited type $T^a$ of the returned value, or $\\mathsf{thread}$, whose value holds no end.",
   "why": "A spawned thread returns $\\ast$ and keeps no end, which $\\mathsf{thread}$ states without a type.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{thread}$ for a lock-free process relation thread.",
   "rocq": "fuel/Fuel.v: rty",
   "sig": "\\sigma \\in \\{T\\annot{^{a}}\\} \\cup \\{\\mathsf{thread}\\}",
   "args": [
    {
     "name": "T\\annot{^{a}}",
     "meaning": "a credited type"
    }
   ]
  },
  "fu.frame": {
   "title": "Frame $d$",
   "what": "$d \\in \\mathbb{N} \\cup \\{\\infty\\}$ bounds the channel actions the term performs before it returns.",
   "why": "Every action asks $1 \\leq d$ and lowers $d$ by one, so the frame bounds how often the context decrements its own ends during the term.",
   "breaks": "Nothing. It is a definition.",
   "example": "A thread has frame $\\infty$.",
   "rocq": "fuel/Fuel.v: Fdef",
   "sig": "d \\in \\mathbb{N} \\cup \\{\\infty\\}",
   "args": []
  },
  "fu.Phi": {
   "title": "Held ends $\\Phi$",
   "what": "$\\Phi$ maps each end the thread holds to its protocol $S$, a session type with annotations, its counter $f$ and its tickets $m \\geq f$, written $o \\mapsto S^{f}_{m}$.",
   "why": "The counter bounds how many actions of the thread holding it may pass before the end acts again, and an action sets it back to $m$. The protocol says when the end is idle and what it sends and receives. Where the relation gives an end a point, fuel gives it a counter and tickets.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\Phi = \\{a \\mapsto S^{3}_{3}\\}$.",
   "rocq": "fuel/Fuel.v: cenv",
   "sig": "\\Phi : \\mathsf{End} \\rightharpoonup \\mathsf{STy} \\times \\mathbb{N} \\times \\mathbb{N}",
   "args": [
    {
     "name": "S^{f}_{m}",
     "meaning": "the protocol $S$, counter $f$ and tickets $m$ of an end, $f \\leq m$"
    }
   ]
  },
  "fu.tick": {
   "title": "$\\Phi{\\downarrow}$",
   "what": "Every counter of $\\Phi$ lowered by one, truncated at $0$, with the tickets kept.",
   "why": "An action decrements the counters of the other ends of the thread holding it, and a transfer passes counters on one lower. Both use this operation.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\{a \\mapsto S^{3}_{3}, b \\mapsto S'^{1}_{2}\\}{\\downarrow} = \\{a \\mapsto S^{2}_{3}, b \\mapsto S'\\annot{^{0}}_{2}\\}$.",
   "rocq": "fuel/Fuel.v: ftick, fhand",
   "sig": "\\Phi{\\downarrow} = \\{o \\mapsto S^{f \\mathbin{\\dot-} 1}_{m} \\mid o \\mapsto S^{f}_{m} \\in \\Phi\\}",
   "args": [
    {
     "name": "\\Phi",
     "meaning": "the held ends, a finite map $o \\mapsto S^{f}_{m}$ from ends to a protocol, a counter $f$ and tickets $m \\geq f$"
    }
   ]
  },
  "fu.rename": {
   "title": "Injective renamings",
   "what": "Fuel holds for every renaming $g$ of ends injective on $\\mathrm{dom}\\,\\Phi$.",
   "why": "A link renames the partner of a removed end in another thread, so fuel must remain renaming.",
   "breaks": "A renaming that merges two held ends would merge their counters.",
   "example": "$g = \\{c^{+} \\mapsto d^{+}\\}$ on $\\Phi = \\{c^{+} \\mapsto S^{2}\\}$.",
   "rocq": "fuel/Fuel.v: kinj, renk",
   "sig": "g : \\mathsf{End} \\to \\mathsf{End} \\text{ injective on } \\mathrm{dom}\\,\\Phi",
   "args": [
    {
     "name": "g",
     "meaning": "the renaming"
    }
   ]
  },
  "fu.val": {
   "title": "(val)",
   "what": "$g(e) \\in \\mathsf{Val} \\Rightarrow g(e) \\in FV^{N}_{\\alpha}\\llbracket g\\Phi \\vdash \\sigma\\rrbracket$.",
   "why": "A returning term gives its context a value whose counters meet its credits, which the bind lemma of fuel consumes.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\ast$ returns at $\\Phi = \\varnothing$.",
   "rocq": "fuel/Fuel.v: Fdef",
   "sig": "g(e) \\in \\mathsf{Val} \\Rightarrow g(e) \\in FV^{N}_{\\alpha}\\llbracket g\\Phi \\vdash \\sigma \\rrbracket",
   "args": [
    {
     "name": "g",
     "meaning": "the renaming"
    }
   ]
  },
  "fu.step": {
   "title": "(step)",
   "what": "$\\forall \\ell, e'.\\ g(e) \\xrightarrow{\\ell} e' \\Rightarrow \\mathsf{Fobl}\\annot{^{N}}_\\ell(e')$ at every ordinal $\\beta < \\alpha$.",
   "why": "Each step updates the state by one index-free rule, which the lock-free process relation follows along a run. At a limit $\\alpha$ the obligation holds at every smaller index.",
   "breaks": "Nothing. It is a definition.",
   "example": "A send step meets F-Send.",
   "rocq": "not yet in the Rocq (docs/redesign/check-transfinite.md)",
   "sig": "\\forall \\ell, e'.\\ g(e) \\xrightarrow{\\ell} e' \\Rightarrow \\forall \\beta < \\alpha.\\ \\mathsf{Fobl}\\annot{^{N}}_{\\ell}(e')",
   "args": [
    {
     "name": "\\ell, e'",
     "meaning": "the step label and the successor"
    },
    {
     "name": "\\beta",
     "meaning": "the index of the successor"
    }
   ]
  },
  "fu.oneclock": {
   "title": "One level per step",
   "what": "Every step costs one level, $\\beta$, creation, spawn and link included.",
   "why": "A clock that let $\\beta$ be free would admit a box that only takes $\\beta$ steps at every level, so the cost fundamental theorem would need the guard as a premise.",
   "breaks": "Nothing. It is a definition.",
   "example": "F-Beta reads $e'$ at level $n$.",
   "rocq": "fuel/Fuel.v: Fdef",
   "sig": "\\text{cost}(\\alpha) = 1",
   "args": [
    {
     "name": "\\alpha",
     "meaning": "every step label"
    }
   ]
  },
  "F-Wait": {
   "title": "F-Wait",
   "what": "$\\Phi(o) = S^{f}$ with $S$ not idle, so the end is held and can act.",
   "why": "An idle end is exempt from the checks $\\geq 1$, so it must not act either.",
   "breaks": "Nothing. It is a definition.",
   "example": "An end at $\\mathsf{Skip}$ cannot act.",
   "rocq": "fuel/Fuel.v: f_act",
   "sig": "\\Phi(o) = S^{f}_{m} \\land \\neg\\mathsf{idle}\\,S",
   "args": [
    {
     "name": "\\Phi",
     "meaning": "the held ends, a finite map $o \\mapsto S^{f}_{m}$ from ends to a protocol, a counter $f$ and tickets $m \\geq f$"
    },
    {
     "name": "o",
     "meaning": "the subject end, $o \\in \\mathsf{End}$"
    }
   ]
  },
  "F-Tick": {
   "title": "F-Count",
   "what": "$\\mathsf{positive}(\\Phi \\setminus o)$, every other end that is not idle has counter at least $1$.",
   "why": "Each action decrements the counters of the other ends, so an end can wait only as many actions of the thread holding it as its counter allows.",
   "breaks": "A holding thread that loops on other ends forever while its partner waits on a held end.",
   "example": "At $\\Phi = \\{a \\mapsto S^{2}, b \\mapsto S'\\annot{^{0}}\\}$ no action on $a$ is allowed unless $b$ is idle.",
   "rocq": "fuel/Fuel.v: f_act, fspare",
   "sig": "\\mathsf{positive}(\\Phi \\setminus o)",
   "args": [
    {
     "name": "\\Phi",
     "meaning": "the held ends, a finite map $o \\mapsto S^{f}_{m}$ from ends to a protocol, a counter $f$ and tickets $m \\geq f$"
    },
    {
     "name": "o",
     "meaning": "the subject end, $o \\in \\mathsf{End}$"
    }
   ]
  },
  "F-Tick.frame": {
   "title": "$1 \\leq d$",
   "what": "The frame has a unit for the action.",
   "why": "The frame bounds the decrements of the context's ends during the term.",
   "breaks": "Nothing. It is a definition.",
   "example": "$1 \\leq d$.",
   "rocq": "fuel/Fuel.v: f_act",
   "sig": "1 \\leq d",
   "args": [
    {
     "name": "d",
     "meaning": "the frame"
    }
   ]
  },
  "fu.idle": {
   "title": "$\\mathsf{idle}$",
   "what": "$\\mathsf{idle}\\,S \\iff \\mathsf{unfold}\\,S = \\mathsf{Skip}$.",
   "why": "Idleness removes the checks $\\geq 1$ and never changes how a counter evolves, so counters stay index-free. The typing ages idle ends by truncation at $0$, matching counters that decrement down to $0$.",
   "breaks": "An idle end whose credit stayed fixed while its counter decrements would exceed its counter.",
   "example": "$\\mathsf{idle}\\,\\mathsf{Skip}$.",
   "rocq": "types/Types.v: idle; fuel/Fuel.v: idle_at",
   "sig": "\\mathsf{idle} : \\mathsf{STy} \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "S",
     "meaning": "a session type"
    }
   ]
  },
  "F-Beta": {
   "title": "F-Beta",
   "what": "$e'$ in $F_\\beta$ at the same state.",
   "why": "A $\\beta$ step changes no counter and costs one index.",
   "breaks": "Nothing. It is a definition.",
   "example": "$(\\lambda x.\\,x)\\,\\ast$.",
   "rocq": "fuel/Fuel.v: f_beta",
   "sig": "\\mathsf{f\\_beta} : \\mathsf{Expr} \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "N",
     "meaning": "the bound on the tickets of a channel, $N \\in \\mathbb{N} \\cup \\{\\infty\\}$"
    },
    {
     "name": "\\alpha",
     "meaning": "the ordinal index"
    },
    {
     "name": "\\Phi",
     "meaning": "the held ends, a finite map $o \\mapsto S^{f}_{m}$ from ends to a protocol, a counter $f$ and tickets $m \\geq f$"
    },
    {
     "name": "\\sigma",
     "meaning": "the result, a credited type or $\\mathsf{thread}$"
    },
    {
     "name": "d",
     "meaning": "the frame, the actions left before returning, $d \\in \\mathbb{N} \\cup \\{\\infty\\}$"
    },
    {
     "name": "e",
     "meaning": "the term"
    },
    {
     "name": "e'",
     "meaning": "the successor"
    }
   ]
  },
  "F-New": {
   "title": "F-New",
   "what": "For a fresh $c$, some $S$, $m_1$ and $m_2$ with $m_1 + m_2 \\leq N$ add $c^{+} \\mapsto S^{m_1}_{m_1}$ and $c^{-} \\mapsto \\overline{S}^{m_2}_{m_2}$ to $\\Phi$.",
   "why": "A new channel starts each end at its tickets, the credit E-New gives to the new ends.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{new}$ adds $c^{\\pm}$ at $2$ and $2$ for $N = 4$.",
   "rocq": "not yet in the Rocq (docs/redesign/check-links-without-tickets.md, decided 2026-11-21)",
   "sig": "\\mathsf{f\\_new} : \\mathsf{Chan} \\to \\mathsf{Expr} \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "c",
     "meaning": "the new channel"
    },
    {
     "name": "S",
     "meaning": "the protocol of $c^{+}$"
    },
    {
     "name": "m_1, m_2",
     "meaning": "the tickets of the two ends"
    },
    {
     "name": "e'",
     "meaning": "the successor"
    }
   ]
  },
  "F-New.fresh": {
   "title": "Fresh against the thread",
   "what": "$c^{\\pm} \\notin \\mathrm{dom}\\,\\Phi$.",
   "why": "Without it, a new channel could reuse a held name and overwrite its counter.",
   "breaks": "Nothing. It is a definition.",
   "example": "$c^{+} \\notin \\{a\\}$.",
   "rocq": "fuel/Fuel.v: ffresh",
   "sig": "c^{\\pm} \\notin \\mathrm{dom}\\,\\Phi",
   "args": [
    {
     "name": "c",
     "meaning": "the new channel"
    },
    {
     "name": "\\Phi",
     "meaning": "the held ends, a finite map $o \\mapsto S^{f}_{m}$ from ends to a protocol, a counter $f$ and tickets $m \\geq f$"
    }
   ]
  },
  "F-New.cnew": {
   "title": "New ends at their tickets",
   "what": "$\\Phi[c^{+} \\mapsto S^{m_1}_{m_1}, c^{-} \\mapsto \\overline{S}^{m_2}_{m_2}]$.",
   "why": "An action sets the counter of an end back to its tickets, and a new end starts there too.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\{c^{+} \\mapsto S^{3}_{3}, c^{-} \\mapsto \\overline{S}^{1}_{1}\\}$ at $N = 4$.",
   "rocq": "not yet in the Rocq (docs/redesign/check-links-without-tickets.md, decided 2026-11-21)",
   "sig": "\\Phi[c^{+} \\mapsto S^{m_1}_{m_1}, c^{-} \\mapsto \\overline{S}^{m_2}_{m_2}]",
   "args": [
    {
     "name": "m_1, m_2",
     "meaning": "the tickets of the new ends, $m_1 + m_2 \\leq N$"
    },
    {
     "name": "c",
     "meaning": "the new channel"
    },
    {
     "name": "S",
     "meaning": "the protocol of $c^{+}$"
    },
    {
     "name": "\\Phi",
     "meaning": "the held ends, a finite map $o \\mapsto S^{f}_{m}$ from ends to a protocol, a counter $f$ and tickets $m \\geq f$"
    }
   ]
  },
  "F-Spawn": {
   "title": "F-Spawn",
   "what": "The child takes $\\Phi|_M{\\downarrow}$ for $M = \\mathsf{fends}(v)$ and runs as a thread, the parent keeps $\\Phi \\setminus M$.",
   "why": "The split is a function of $v$, so it is the same at each index.",
   "breaks": "Nothing. It is a definition.",
   "example": "The thunk takes $d'$ at $1$ in the cycle.",
   "rocq": "fuel/Fuel.v: f_spawn",
   "sig": "\\mathsf{f\\_spawn} : \\mathsf{Val} \\to \\mathsf{Expr} \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "v",
     "meaning": "the thunk"
    },
    {
     "name": "M",
     "meaning": "$\\mathsf{fends}(v)$, the transferred ends"
    },
    {
     "name": "e'",
     "meaning": "the parent's successor"
    }
   ]
  },
  "F-Spawn.held": {
   "title": "$M \\subseteq \\mathrm{dom}\\,\\Phi$",
   "what": "Only held ends are transferred.",
   "why": "A child mentioning an end the parent does not hold would act on an end without a counter.",
   "breaks": "A box mentioning channel constants would pass on ends nobody holds.",
   "example": "$M = \\{d'\\}$.",
   "rocq": "fuel/Fuel.v: f_spawn",
   "sig": "M \\subseteq \\mathrm{dom}\\,\\Phi",
   "args": [
    {
     "name": "M",
     "meaning": "the transferred ends"
    }
   ]
  },
  "fu.fspare": {
   "title": "$\\mathsf{positive}$",
   "what": "$\\mathsf{positive}(\\Phi) \\iff$ every end of $\\Phi$ that is not idle has counter at least $1$.",
   "why": "A transfer passes the counter minus one, so a non-idle end must have a positive counter. A spawn is no action, so this is its only check.",
   "breaks": "A transfer at counter $0$ under truncation passes $0$ again and an end is passed on forever.",
   "example": "$\\mathsf{positive}(\\{d' \\mapsto S^{1}\\})$.",
   "rocq": "fuel/Fuel.v: fspare",
   "sig": "\\mathsf{positive}(\\Phi) \\iff \\forall o \\mapsto S^{f}_{m} \\in \\Phi.\\ \\neg\\mathsf{idle}\\,S \\Rightarrow 1 \\leq f",
   "args": [
    {
     "name": "\\Phi",
     "meaning": "the held ends, a finite map $o \\mapsto S^{f}_{m}$ from ends to a protocol, a counter $f$ and tickets $m \\geq f$"
    }
   ]
  },
  "F-Spawn.child": {
   "title": "The child",
   "what": "$v\\,\\ast \\in F^N_\\beta\\llbracket\\Phi|_M{\\downarrow} \\vdash \\mathsf{thread}\\ !\\ \\infty\\rrbracket$.",
   "why": "The child is a new thread of the lock-free process relation, so it must have thread fuel at exactly the ends and counters the lock-free process relation moves to the child.",
   "breaks": "Nothing. It is a definition.",
   "example": "$(\\lambda u.\\,\\mathsf{close}\\,d')\\,\\ast$.",
   "rocq": "fuel/Fuel.v: f_spawn",
   "sig": "v\\,\\ast \\in F^{N}_{\\beta}\\llbracket \\Phi|_M{\\downarrow} \\vdash \\mathsf{thread}\\ !\\ \\infty \\rrbracket",
   "args": [
    {
     "name": "v\\,\\ast",
     "meaning": "the child thread"
    },
    {
     "name": "M",
     "meaning": "the transferred ends"
    }
   ]
  },
  "F-Send": {
   "title": "F-Send",
   "what": "An action on $o$ that passes on $M = \\mathsf{fends}(w)$ one lower, the payload in $FV$, and the continuation with $o$ back at its tickets $m$.",
   "why": "A send is an action, so F-Count applies, and a transfer, so $\\mathsf{positive}$ applies.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{send}\\,\\langle a, y\\rangle$ in the growing ring.",
   "rocq": "fuel/Fuel.v: f_send",
   "sig": "\\mathsf{f\\_send} : \\mathsf{End} \\to \\mathsf{Val} \\to \\mathsf{Expr} \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "o",
     "meaning": "the subject end, $o \\in \\mathsf{End}$"
    },
    {
     "name": "w",
     "meaning": "the payload"
    },
    {
     "name": "M",
     "meaning": "$\\mathsf{fends}(w)$"
    },
    {
     "name": "T, b",
     "meaning": "the payload type and credit"
    },
    {
     "name": "S",
     "meaning": "the continuation protocol"
    }
   ]
  },
  "F-Send.notsubj": {
   "title": "$o \\notin M \\subseteq \\mathrm{dom}\\,\\Phi$",
   "what": "A send gives away held ends other than its subject.",
   "why": "The continuation keeps acting on $o$, so $o$ cannot leave.",
   "breaks": "A term that sends its own subject or an end its context holds.",
   "example": "$M = \\{a\\}$.",
   "rocq": "fuel/Fuel.v: f_send",
   "sig": "o \\notin M \\subseteq \\mathrm{dom}\\,\\Phi",
   "args": [
    {
     "name": "M",
     "meaning": "the transferred ends"
    },
    {
     "name": "o",
     "meaning": "the subject end, $o \\in \\mathsf{End}$"
    }
   ]
  },
  "F-Send.payload": {
   "title": "Payload in $FV$",
   "what": "$w \\in FV^N_{\\alpha}\\llbracket\\Phi|_M{\\downarrow} \\vdash T\\rrbracket$, with every transferred counter lowered by one transfer.",
   "why": "$FV$ reads no point, so the raw payload type and its placed form agree.",
   "breaks": "Nothing. It is a definition.",
   "example": "$FV^N_{\\alpha}\\llbracket \\{a \\mapsto S^{2}\\} \\vdash (S@x)^{2}\\rrbracket$ for a payload end promised at credit $2$.",
   "rocq": "fuel/Fuel.v: f_send",
   "sig": "w \\in FV^{N}_{\\alpha}\\llbracket \\Phi|_M{\\downarrow} \\vdash T \\rrbracket",
   "args": [
    {
     "name": "w",
     "meaning": "the payload"
    },
    {
     "name": "T",
     "meaning": "the payload type"
    }
   ]
  },
  "F-Recv": {
   "title": "F-Recv",
   "what": "An action on $o$ that continues for every incoming value in $FV$ at every index $\\gamma \\leq \\beta$ with ends disjoint from $\\Phi$.",
   "why": "The receiver continues for every value its type admits, and the lock-free process relation supplies the sender's transferred ends.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{recv}\\,b$ in the client loop.",
   "rocq": "fuel/Fuel.v: f_recv",
   "sig": "\\mathsf{f\\_recv} : \\mathsf{End} \\to \\mathsf{Val} \\to \\mathsf{Expr} \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "o",
     "meaning": "the subject end, $o \\in \\mathsf{End}$"
    },
    {
     "name": "w",
     "meaning": "the received value"
    },
    {
     "name": "\\beta, \\Phi_i",
     "meaning": "its level and the ends it brings"
    }
   ]
  },
  "F-Recv.forall": {
   "title": "Every incoming value",
   "what": "$\\forall \\gamma \\leq \\beta, \\Phi_i.\\ w \\in FV^N_\\gamma\\llbracket\\Phi_i \\vdash T\\rrbracket$.",
   "why": "Every value in $FV$ is exact, so incoming closures hold exactly what they mention.",
   "breaks": "Without exactness, a received closure owning nothing but mentioning an end could not be spawned.",
   "example": "$\\Phi_i = \\{e \\mapsto S^{2}_{2}\\}$.",
   "rocq": "fuel/Fuel.v: f_recv",
   "sig": "\\forall \\gamma \\leq \\beta, \\Phi_i \\mathbin{\\#} \\Phi.\\ w \\in FV^{N}_{\\gamma}\\llbracket \\Phi_i \\vdash T \\rrbracket \\Rightarrow \\ldots",
   "args": [
    {
     "name": "\\Phi_i",
     "meaning": "the ends of the received value, disjoint from $\\Phi$"
    },
    {
     "name": "\\gamma",
     "meaning": "an ordinal index at most $\\beta$"
    }
   ]
  },
  "F-Close": {
   "title": "F-Close, F-Select, F-Branch",
   "what": "Actions that drop $o$ and decrement the rest at a close, or advance the protocol of $o$ to $S_i$ and set it back to its tickets $m$ at a choice.",
   "why": "They are the fuel forms of O-Close, O-Select and O-Branch, and each is an action, so F-Count applies.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{close}\\,c^{+}$.",
   "rocq": "fuel/Fuel.v: f_close, f_select, f_branch",
   "sig": "\\mathsf{f\\_close}, \\mathsf{f\\_select}, \\mathsf{f\\_branch} : \\mathsf{End} \\to \\ldots \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "o",
     "meaning": "the subject end, $o \\in \\mathsf{End}$"
    },
    {
     "name": "i",
     "meaning": "the choice, for select and branch"
    }
   ]
  },
  "F-Link": {
   "title": "F-Link",
   "what": "Two distinct held ends at dual protocols leave, and the counter of each exceeds the partner bound $N - m$ of the other.",
   "why": "The link lowers no counter. Its premise makes the partner of a waiting thread after the link have a lower counter than before.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{link}\\,\\langle c^{+}, d^{-}\\rangle$ with counters $3$ and $3$ and tickets $3$ and $3$ at $N = 4$.",
   "rocq": "fuel/Fuel.v: f_link",
   "sig": "\\mathsf{f\\_link} : \\mathcal{P}_{\\mathrm{fin}}(\\mathsf{End}) \\to \\mathsf{Expr} \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "\\{o_1, o_2\\}",
     "meaning": "the linked ends"
    }
   ]
  },
  "F-Link.plink": {
   "title": "Dual held ends",
   "what": "$o_1 \\neq o_2$, both held, at protocols $S$ and $S' \\simeq \\overline{S}$, with annotations.",
   "why": "After the link the partners form one channel, whose protocols are dual only if the two linked protocols were, and annotations must match for later payload credits.",
   "breaks": "A credit mismatch at a link breaks the payload credit of a later message.",
   "example": "$c^{+} \\mapsto S^{2}_{3}$ and $d^{-} \\mapsto \\overline{S}^{1}_{3}$.",
   "rocq": "fuel/Fuel.v: plink",
   "sig": "\\Phi(o_1) = S^{f_1}_{m_1},\\ \\Phi(o_2) = S'^{f_2}_{m_2},\\ o_1 \\neq o_2,\\ S' \\simeq \\overline{S}",
   "args": [
    {
     "name": "\\Phi",
     "meaning": "the held ends, a finite map $o \\mapsto S^{f}_{m}$ from ends to a protocol, a counter $f$ and tickets $m \\geq f$"
    },
    {
     "name": "o_1, o_2",
     "meaning": "the linked ends"
    }
   ]
  },
  "F-Link.ticket": {
   "title": "$f_1 + m_2 > N$ and $f_2 + m_1 > N$",
   "what": "The counter of each linked end exceeds $N - m$ for the tickets $m$ of the other linked end.",
   "why": "The partner of $o_2$ has at most $N - m_2$ tickets, so its counter is below $f_1$. The thread waiting on the partner of $o_1$ then faces a lower counter after the link, and the measure of lock-free adequacy falls.",
   "breaks": "Without it a link can give a waiting thread a partner with a full counter in every round.",
   "example": "$3 + 3 > 4$.",
   "rocq": "fuel/Fuel.v: lok",
   "sig": "f_1 + m_2 > N \\land f_2 + m_1 > N",
   "args": [
    {
     "name": "f_1, f_2",
     "meaning": "the counters of the linked ends"
    },
    {
     "name": "m_1, m_2",
     "meaning": "their tickets"
    },
    {
     "name": "N",
     "meaning": "the bound on the tickets of a channel, $N \\in \\mathbb{N} \\cup \\{\\infty\\}$"
    }
   ]
  },
  "FV-Sess": {
   "title": "$FV$ at $S@x$",
   "what": "An end with protocol $S' \\simeq S$, counter $f \\geq a$ and the tickets $m$ of its type.",
   "why": "Credits are lower bounds on counters, and the tickets of the type are those fuel resets the counter to.",
   "breaks": "Nothing. It is a definition.",
   "example": "$o \\mapsto S^{3}_{3}$ at $(S@x)^2_3$.",
   "rocq": "fuel/Fuel.v: Vty TSess",
   "sig": "o \\in FV^{N}_{\\alpha}\\llbracket \\{o \\mapsto S'^{f}_{m}\\} \\vdash (S@x)\\annot{^{a}}_{m} \\rrbracket",
   "args": [
    {
     "name": "o",
     "meaning": "the subject end, $o \\in \\mathsf{End}$"
    },
    {
     "name": "S@x, a, m",
     "meaning": "the end type, its credit and its tickets"
    },
    {
     "name": "S', f",
     "meaning": "the protocol and counter of $o$"
    }
   ]
  },
  "FV-Sess.counter": {
   "title": "$a \\leq f$",
   "what": "The counter meets the credit.",
   "why": "Typing reasons with credits and the lock-free process relation with counters, and this inequality transfers every credit bound of typing to the counters.",
   "breaks": "Without it, a context could age an end below its actual counter and F-Count would fail on an end whose credit typing treats as positive.",
   "example": "$2 \\leq 3$.",
   "rocq": "fuel/Fuel.v: Vty TSess",
   "sig": "a \\leq f",
   "args": [
    {
     "name": "a",
     "meaning": "the credit",
     "ann": true
    },
    {
     "name": "f",
     "meaning": "the counter"
    }
   ]
  },
  "FV-Arrow": {
   "title": "$FV$ at an arrow",
   "what": "A closure whose body has fuel at every lower level, counters at or above the counters at creation minus its credit and argument in $FV$.",
   "why": "The clause reads costs and credits, the data typing attaches to arrows.",
   "breaks": "Nothing. It is a definition.",
   "example": "A loop body at cost $\\infty$.",
   "rocq": "fuel/Fuel.v: Vty TLolli",
   "sig": "\\lambda e \\in FV^{N}_{\\alpha}\\llbracket \\Phi \\vdash (T \\multimap\\annot{[c; h]}\\, U)\\annot{^{a}} \\rrbracket",
   "args": [
    {
     "name": "c, h",
     "meaning": "the cost and floor of the arrow"
    },
    {
     "name": "a",
     "meaning": "the credit of the closure",
     "ann": true
    }
   ]
  },
  "FV-Arrow.exact": {
   "title": "$\\mathsf{fends}\\,e = \\mathrm{dom}\\,\\Phi$",
   "what": "The closure holds exactly the ends it mentions.",
   "why": "It mirrors exactness of $V$, and the cost fundamental theorem needs it to read fuel off typing.",
   "breaks": "A closure mentioning an end it does not hold would be in $FV$, and a forwarder receiving that closure could not spawn the closure.",
   "example": "$\\lambda\\_.\\,\\mathsf{close}\\,a$ holds $\\{a\\}$.",
   "rocq": "fuel/Fuel.v: Vty TLolli",
   "sig": "\\mathsf{fends}\\,e = \\mathrm{dom}\\,\\Phi",
   "args": [
    {
     "name": "e",
     "meaning": "the body"
    }
   ]
  },
  "FV-Arrow.floor": {
   "title": "Counters $\\geq a$",
   "what": "Every captured counter $f$ of an end that is not idle has $a \\leq f$.",
   "why": "The closure's credit $a$ is a lower bound on each captured counter, as the credit of an end is on its own counter.",
   "breaks": "Nothing. It is a definition.",
   "example": "$a = 1$ needs counters $\\geq 1$.",
   "rocq": "fuel/Fuel.v: Vty TLolli",
   "sig": "\\Phi(o) = S^{f} \\Rightarrow h + a \\leq f",
   "args": [
    {
     "name": "h",
     "meaning": "the floor"
    },
    {
     "name": "a",
     "meaning": "the closure's credit",
     "ann": true
    }
   ]
  },
  "FV-Arrow.body": {
   "title": "Body fuel",
   "what": "$e[u] \\in F^{N}_{\\beta}\\llbracket\\Phi' \\cup \\Phi_u \\vdash U\\ !\\ c\\rrbracket$.",
   "why": "The caller supplies an argument and counters lowered by at most $a$ by its own actions, and the body guarantees fuel with frame $c$.",
   "breaks": "Nothing. It is a definition.",
   "example": "A call of a closure of cost $1$.",
   "rocq": "fuel/Fuel.v: Vty TLolli",
   "sig": "e[u] \\in F^{N}_{\\beta}\\llbracket \\Phi' \\cup \\Phi_u \\vdash U\\ !\\ c \\rrbracket",
   "args": [
    {
     "name": "\\beta",
     "meaning": "a lower level"
    },
    {
     "name": "\\Phi'",
     "meaning": "the captured ends with counters at the call, at least $h$"
    },
    {
     "name": "\\Phi_u",
     "meaning": "the ends of the argument"
    },
    {
     "name": "c",
     "meaning": "the frame, the cost of the arrow"
    }
   ]
  },
  "FV-Box": {
   "title": "$FV$ at a box",
   "what": "A box with no ends whose body has fuel per force at every lower level and session instance in $\\mathsf{sinsts}\\,N$.",
   "why": "A box is unlimited, so it holds no counters and works at every use.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{ring}$ at $N = 4$.",
   "rocq": "fuel/Fuel.v: Vty TBox",
   "sig": "!e \\in FV^{N}_{\\alpha}\\llbracket \\varnothing \\vdash \\Box(\\ldots) \\rrbracket",
   "args": [
    {
     "name": "e",
     "meaning": "the body"
    }
   ]
  },
  "FV-Box.noends": {
   "title": "$\\mathsf{fends}\\,e = \\varnothing$",
   "what": "A box mentions no end and holds no protocol or counter.",
   "why": "A copied box would otherwise copy ends.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{ring}$.",
   "rocq": "fuel/Fuel.v: Vty TBox",
   "sig": "\\mathsf{fends}\\,e = \\varnothing",
   "args": [
    {
     "name": "e",
     "meaning": "the body"
    }
   ]
  },
  "FV-Box.body": {
   "title": "Body per force",
   "what": "$e[!e] \\in F^{N}_{\\beta}\\llbracket\\varnothing \\vdash U[\\bar s]\\ !\\ c\\rrbracket$ for every $\\beta < \\alpha$ and $\\bar s \\in \\mathsf{sinsts}\\,N$.",
   "why": "Each force unrolls the box once, at an instance the forcing context chooses.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\bar s \\in \\mathsf{sinsts}\\,N$.",
   "rocq": "fuel/Fuel.v: Vty TBox",
   "sig": "e[!e] \\in F^{N}_{\\beta}\\llbracket \\varnothing \\vdash U[\\bar s]\\ !\\ c \\rrbracket",
   "args": [
    {
     "name": "\\beta",
     "meaning": "a lower level"
    },
    {
     "name": "\\bar s",
     "meaning": "a session instance in $\\mathsf{sinsts}\\,N$"
    },
    {
     "name": "c",
     "meaning": "the frame, the cost of one force"
    }
   ]
  },
  "FV-Thread": {
   "title": "Thread result",
   "what": "$v \\in FV\\llbracket\\Phi \\vdash \\mathsf{thread}\\rrbracket \\iff \\Phi = \\varnothing$.",
   "why": "A finished thread holds no end.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\Phi = \\varnothing$.",
   "rocq": "fuel/Fuel.v: Vres",
   "sig": "v \\in FV^{N}_{\\alpha}\\llbracket \\Phi \\vdash \\mathsf{thread} \\rrbracket",
   "args": [
    {
     "name": "v",
     "meaning": "the returned value"
    }
   ]
  },
  "fu.fsem": {
   "title": "$\\mathsf{fsem}$",
   "what": "$\\mathsf{fsem}\\,N\\,\\Phi\\,e$ iff $e \\in F^N_\\alpha\\llbracket\\Phi \\vdash \\mathsf{thread}\\ !\\ \\infty\\rrbracket$ for every ordinal $\\alpha$.",
   "why": "It is the fuel of a thread that the lock-free process relation requires, and the cost fundamental theorem derives it from typing. It is the one fuel statement that holds at every index.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{fsem}\\,N\\,\\{c^{+} \\mapsto \\mathsf{Close}^{2}_{2}\\}\\,(\\mathsf{close}\\,c^{+})$.",
   "rocq": "not yet in the Rocq (docs/redesign/check-links-without-tickets.md and check-transfinite.md)",
   "sig": "\\mathsf{fsem} : (\\mathbb{N} \\cup \\{\\infty\\}) \\to (\\mathsf{End} \\rightharpoonup \\mathsf{STy} \\times \\mathbb{N} \\times \\mathbb{N}) \\to \\mathsf{Expr} \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "N",
     "meaning": "the bound on the tickets of a channel, $N \\in \\mathbb{N} \\cup \\{\\infty\\}$"
    },
    {
     "name": "\\Phi",
     "meaning": "the held ends, a finite map $o \\mapsto S^{f}_{m}$ from ends to a protocol, a counter $f$ and tickets $m \\geq f$"
    },
    {
     "name": "e",
     "meaning": "the thread"
    },
    {
     "name": "\\alpha",
     "meaning": "every ordinal index"
    }
   ]
  },
  "cs.csem": {
   "title": "$\\Delta \\vDash^{N} e : T\\ !\\ \\varepsilon$",
   "what": "For every larger counter bound, level, injective renaming of the ends of $\\Delta$, grounding in $FV$, the instance has fuel at $T$ with frame $c$, for $\\varepsilon = c$.",
   "why": "It reads no $\\Gamma$, world or future, because fuel reads none of these.",
   "breaks": "Nothing. It is a definition.",
   "example": "The cost fundamental theorem concludes this judgment.",
   "rocq": "cost/CostSem.v: csem",
   "sig": "\\Delta \\vDash^{N} e : T\\ !\\ \\varepsilon",
   "args": [
    {
     "name": "\\Delta",
     "meaning": "the linear context"
    },
    {
     "name": "N",
     "meaning": "the bound on the tickets of a channel, $N \\in \\mathbb{N} \\cup \\{\\infty\\}$"
    },
    {
     "name": "T",
     "meaning": "the type"
    },
    {
     "name": "\\varepsilon",
     "meaning": "the effect, the cost $c$"
    }
   ]
  },
  "sp.state": {
   "title": "Annotated configuration $a = (q, K)$",
   "what": "A configuration $q$ and an ownership map $K$.",
   "why": "Ranks and counters of the termination measure are read off $K$.",
   "breaks": "Nothing. It is a definition.",
   "example": "$(q, K)$.",
   "rocq": "soup/State.v: lfstate",
   "sig": "a = (q, K) \\in \\mathsf{Config} \\times \\mathsf{Own}",
   "args": [
    {
     "name": "q",
     "meaning": "the configuration"
    },
    {
     "name": "K",
     "meaning": "the ownership map of the annotated configuration"
    }
   ]
  },
  "sp.hold": {
   "title": "$K(o) = (t, x, f, m)$",
   "what": "The holding thread $t$, point $x$, counter $f$ and tickets $m$ of a held end $o$.",
   "why": "One map records all data the measure and the invariant on tickets read.",
   "breaks": "Nothing. It is a definition.",
   "example": "$K(a) = (0, \\rho, 2, 3)$.",
   "rocq": "soup/State.v: hold",
   "sig": "K : \\mathsf{End} \\rightharpoonup \\mathbb{N} \\times \\mathsf{Point} \\times \\mathbb{N} \\times \\mathbb{N}",
   "args": [
    {
     "name": "t, x, f, m",
     "meaning": "holding thread, point, counter and tickets"
    }
   ]
  },
  "sp.exists": {
   "title": "Chosen per level",
   "what": "$\\exists A, \\Phi, U$, the held ends for the relation and for fuel, and the result type of each thread, chosen at each level.",
   "why": "O-New and F-New choose the session type of a new channel in separate existentials, so the protocols in $\\Phi$ are not determined by $A$.",
   "breaks": "Nothing. It is a definition.",
   "example": "$A = \\{c^{+} \\mapsto \\mathsf{Close}@x\\}$ and $\\Phi = \\{c^{+} \\mapsto \\mathsf{Close}^{2}\\}$.",
   "rocq": "soup/Soup.v: Soup",
   "sig": "\\exists A \\in \\mathsf{Env}, \\Phi, U : \\mathbb{N} \\to \\mathsf{Ty}",
   "args": [
    {
     "name": "A",
     "meaning": "the held ends for the relation, $o \\mapsto S@x$"
    },
    {
     "name": "\\Phi",
     "meaning": "the held ends for fuel, $o \\mapsto S^{f}$"
    },
    {
     "name": "U",
     "meaning": "the result type of each thread"
    }
   ]
  },
  "sp.tfree": {
   "title": "$\\mathsf{tfree}\\,T$",
   "what": "The result type holds no end.",
   "why": "A main thread returning an end would leave that end's partner waiting.",
   "breaks": "$\\mathsf{main}$ returning an end.",
   "example": "$\\mathsf{tfree}\\,\\ast$.",
   "rocq": "soup/State.v: sp_tfree",
   "sig": "\\mathsf{tfree}\\,T",
   "args": [
    {
     "name": "T",
     "meaning": "the type, $T \\in \\mathsf{Ty}$"
    }
   ]
  },
  "sp.rel": {
   "title": "Every thread live",
   "what": "$\\forall t.\\ q(t) \\in E[\\kappa_L]^W_\\alpha\\llbracket K_t(A) \\vdash U_t\\rrbracket^{\\varnothing}$, where $K_t(A)$ restricts $A$ to the ends held by $t$.",
   "why": "The per-thread relation at $\\kappa_L$ excludes internal divergence and infinite chains of spawns.",
   "breaks": "Nothing. It is a definition.",
   "example": "$q(0) \\in E[\\kappa_L]\\llbracket K_0(A) \\vdash T\\rrbracket^{\\varnothing}$.",
   "rocq": "soup/State.v: sp_rel",
   "sig": "\\forall t, e.\\ q(t) = e \\Rightarrow e \\in E[\\kappa_L]^{W}_{\\alpha}\\llbracket K_t(A) \\vdash U_t \\rrbracket^{\\varnothing}",
   "args": [
    {
     "name": "t",
     "meaning": "a thread"
    },
    {
     "name": "K_t(A)",
     "meaning": "$A$ restricted to the ends held by $t$"
    }
   ]
  },
  "sp.ty": {
   "title": "$U_t \\in \\{T, \\ast\\}$",
   "what": "Each thread returns at $T$ or at $\\ast$.",
   "why": "A thread that returns has a value in $V$ at $U_t$, and for $U_t \\in \\{T, \\ast\\}$ with $\\mathsf{tfree}\\,T$ that value holds no end, which the termination argument uses.",
   "breaks": "Without it, a finished thread could still hold an end.",
   "example": "$\\mathsf{main}$ at $T$, spawned threads at $\\ast$.",
   "rocq": "soup/State.v: sp_ty",
   "sig": "U_t \\in \\{T, \\ast\\}",
   "args": [
    {
     "name": "t",
     "meaning": "a thread"
    }
   ]
  },
  "sp.fuel": {
   "title": "Each thread has fuel",
   "what": "$\\forall t.\\ q(t) \\in F^N_\\alpha\\llbracket\\Phi|_t \\vdash \\mathsf{thread}\\ !\\ \\infty\\rrbracket$, where $\\Phi|_t$ is $\\Phi$ on the ends that $K$ gives to $t$.",
   "why": "The counters and tickets of $\\Phi$ are those recorded in $K$.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\Phi|_0 = \\{a \\mapsto S^{2}_{3}\\}$.",
   "rocq": "soup/State.v: sp_fuel",
   "sig": "e \\in F^{N}_{\\alpha}\\llbracket \\Phi|_t \\vdash \\mathsf{thread}\\ !\\ \\infty \\rrbracket",
   "args": [
    {
     "name": "t",
     "meaning": "a thread"
    },
    {
     "name": "\\Phi|_t",
     "meaning": "$\\Phi$ on the ends that $K$ gives to $t$"
    }
   ]
  },
  "sp.pts": {
   "title": "Points, counters and tickets from $K$",
   "what": "$K(o) = (t, x, f, m)$ implies that $o$ is at $x$ in $A$ and has counter $f$ and tickets $m$ in $\\Phi$.",
   "why": "The relation and fuel read the data that $K$ records.",
   "breaks": "Nothing. It is a definition.",
   "example": "$A(a) = S@\\rho$, $\\Phi(a) = S^{2}_{3}$ and $K(a) = (0, \\rho, 2, 3)$.",
   "rocq": "soup/State.v: sp_pts, ctrs",
   "sig": "K(o) = (t, x, f, m) \\Rightarrow A(o) = \\_@x \\land \\Phi(o) = \\_^{f}_{m}",
   "args": [
    {
     "name": "o",
     "meaning": "an end"
    }
   ]
  },
  "sp.dom": {
   "title": "$\\mathrm{dom}\\,A = \\mathrm{dom}\\,\\Phi = \\mathrm{dom}\\,K$",
   "what": "$A$, $\\Phi$ and $K$ describe the same held ends.",
   "why": "Lock-free adequacy reads the protocol of an end of $K$, and of its dual end, to decide idleness, and a synchronization updates $\\Phi$ and $K$ together.",
   "breaks": "Without it, a held end could lack a protocol, and idleness of a waiting end would be undefined.",
   "example": "$\\mathrm{dom}\\,\\Phi = \\{c^{+}, c^{-}\\} = \\mathrm{dom}\\,K$.",
   "rocq": "soup/State.v: sp_dom, sp_pts",
   "sig": "\\mathrm{dom}\\,A = \\mathrm{dom}\\,\\Phi = \\mathrm{dom}\\,K",
   "args": [
    {
     "name": "\\Phi",
     "meaning": "the held ends, a finite map $o \\mapsto S^{f}_{m}$ from ends to a protocol, a counter $f$ and tickets $m \\geq f$"
    },
    {
     "name": "K",
     "meaning": "the ownership map of the annotated configuration"
    }
   ]
  },
  "sp.owner": {
   "title": "Holding threads exist",
   "what": "$\\forall o.\\ K(o) = (t, \\_, \\_) \\Rightarrow t \\in \\mathrm{dom}\\,q$.",
   "why": "A thread waiting on an end needs its partner's holding thread to be a thread of $q$, so the dependency of waiting threads is a relation on threads.",
   "breaks": "Without it, an end could be held by a thread that no longer exists, and its partner would wait forever.",
   "example": "$K(a) = (0, \\rho, 2)$ with $q(0)$ defined.",
   "rocq": "soup/State.v: sp_owner",
   "sig": "\\forall o.\\ K(o) = (t, \\_, \\_, \\_) \\Rightarrow t \\in \\mathrm{dom}\\,q",
   "args": [
    {
     "name": "o, t",
     "meaning": "a held end and the thread holding it"
    }
   ]
  },
  "sp.closed": {
   "title": "Held ends restricted or interface",
   "what": "$\\forall o \\in \\mathrm{dom}\\,K.\\ \\mathsf{ech}\\,o \\in C \\lor o \\in \\mathrm{dom}\\,\\Sigma$.",
   "why": "For $\\Sigma = \\varnothing$ each held end is restricted, so the lock-free process relation holds both ends of each channel it acts on. Composition splits held ends along this condition.",
   "breaks": "Without it, a closed process could hold an end whose partner nobody holds, and the thread holding it would wait forever.",
   "example": "For $\\Sigma = \\varnothing$, $\\mathsf{ech}\\,o \\in C$.",
   "rocq": "soup/State.v: sp_closed",
   "sig": "\\forall o \\in \\mathrm{dom}\\,K.\\ \\mathsf{ech}\\,o \\in C \\lor o \\in \\mathrm{dom}\\,\\Sigma",
   "args": [
    {
     "name": "C",
     "meaning": "the restricted channels of $q$"
    },
    {
     "name": "\\Sigma",
     "meaning": "the interface, a finite map $\\mathsf{End} \\rightharpoonup \\mathsf{STy} \\times \\mathsf{Point}$"
    }
   ]
  },
  "sp.pair": {
   "title": "Restricted partners held",
   "what": "$\\forall o \\in \\mathrm{dom}\\,K.\\ \\mathsf{ech}\\,o \\in C \\Rightarrow \\overline{o} \\in \\mathrm{dom}\\,K$.",
   "why": "The partner of an internal end is held by some thread.",
   "breaks": "Nothing. It is a definition.",
   "example": "Both ends of $c$ in the pair of closes.",
   "rocq": "soup/State.v: sp_pair",
   "sig": "\\forall o \\in \\mathrm{dom}\\,K.\\ \\mathsf{ech}\\,o \\in C \\Rightarrow \\overline{o} \\in \\mathrm{dom}\\,K",
   "args": [
    {
     "name": "o",
     "meaning": "a held end"
    }
   ]
  },
  "sp.sdual": {
   "title": "Restricted pairs dual",
   "what": "$A(o) = S@x \\land A(\\overline{o}) = S'@x' \\land \\mathsf{ech}\\,o \\in C \\Rightarrow x' = \\overline{x} \\land \\mathsf{sdual}\\,S\\,S'$.",
   "why": "Internal partners are at dual points with dual session types.",
   "breaks": "Nothing. It is a definition.",
   "example": "$x' = \\overline{x}$.",
   "rocq": "soup/State.v: sp_sdual",
   "sig": "A(o) = S@x \\land A(\\overline{o}) = S'@x' \\land \\mathsf{ech}\\,o \\in C \\Rightarrow x' = \\overline{x} \\land \\mathsf{sdual}\\,S\\,S'",
   "args": [
    {
     "name": "o",
     "meaning": "an end of a restricted channel"
    }
   ]
  },
  "sp.pdual": {
   "title": "Restricted protocols dual",
   "what": "$\\mathsf{ech}\\,o \\in C$, $\\Phi(o) = P^{f}$ and $\\Phi(\\overline{o}) = P'^{f'}$ imply $P' \\simeq \\overline{P}$.",
   "why": "Lock-free adequacy reads idleness from $\\Phi$, and duality transfers idleness from an end to its dual end.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\Phi(c^{+}) = \\mathsf{Close}^{2}$ and $\\Phi(c^{-}) = \\mathsf{Close}^{1}$.",
   "rocq": "soup/State.v: sp_pdual",
   "sig": "\\mathsf{ech}\\,o \\in C \\land \\Phi(o) = P^{f}_{m} \\land \\Phi(\\overline{o}) = P'^{f'}_{m'} \\Rightarrow P' \\simeq \\overline{P}",
   "args": [
    {
     "name": "P, P'",
     "meaning": "the protocols of the two ends"
    }
   ]
  },
  "sp.sig": {
   "title": "Interface entries in $A$",
   "what": "$\\Sigma(o) = y \\Rightarrow A(o) = y$.",
   "why": "Restricting a cut makes its channels internal, and their dual entries in $A$ come from $\\Sigma$ through this condition.",
   "breaks": "Without it, a channel restricted at composition could have non-dual entries in $A$.",
   "example": "$A(c^{+}) = \\Sigma(c^{+})$.",
   "rocq": "soup/State.v: sp_sig",
   "sig": "\\Sigma(o) = y \\Rightarrow A(o) = y",
   "args": [
    {
     "name": "y",
     "meaning": "an entry $S@x$"
    }
   ]
  },
  "sp.psig": {
   "title": "Interface protocols in $\\Phi$",
   "what": "$\\Sigma(o) = S@x$ implies $\\Phi(o) = S^{f}$ for some counter $f$.",
   "why": "At composition the protocols of the cut come from $\\Sigma$, which typing makes dual.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\Sigma(o) = \\mathsf{Close}@x$ and $\\Phi(o) = \\mathsf{Close}^{2}$.",
   "rocq": "soup/State.v: sp_psig",
   "sig": "\\Sigma(o) = S@x \\Rightarrow \\Phi(o) = S^{f}_{m}",
   "args": [
    {
     "name": "o",
     "meaning": "the subject end, $o \\in \\mathsf{End}$"
    }
   ]
  },
  "sp.fin": {
   "title": "Finite counters",
   "what": "$\\forall o.\\ K(o) = (\\_, \\_, f) \\Rightarrow f \\in \\mathbb{N}$.",
   "why": "The termination measure reads every counter as a natural number.",
   "breaks": "Nothing. It is a definition.",
   "example": "$K(a) = (0, \\rho, 2)$.",
   "rocq": "soup/State.v: sp_fin",
   "sig": "\\forall o.\\ K(o) = (\\_, \\_, f) \\Rightarrow f \\in \\mathbb{N}",
   "args": [
    {
     "name": "f",
     "meaning": "the counter of $o$"
    }
   ]
  },
  "sp.lfsem": {
   "title": "$\\Sigma \\Vvdash_W p : T$",
   "what": "$\\exists N \\in \\mathbb{N}.\\ \\forall \\alpha.\\ \\exists a.\\ \\mathsf{erase}(q_a) = p \\land a \\in S^{N,W}_\\alpha\\llbracket\\Sigma \\vdash T\\rrbracket$, over every ordinal index $\\alpha$.",
   "why": "The lock-free process relation alone suffices, and absence of internal divergence of the lock-free process relation gives what a process conjunct would.",
   "breaks": "Nothing. It is a definition.",
   "example": "The lock-free fundamental theorem concludes this judgment.",
   "rocq": "not yet in the Rocq (docs/redesign/check-transfinite.md)",
   "sig": "\\Sigma \\Vvdash_{W} p : T",
   "args": [
    {
     "name": "\\Sigma",
     "meaning": "the interface, a finite map $\\mathsf{End} \\rightharpoonup \\mathsf{STy} \\times \\mathsf{Point}$"
    },
    {
     "name": "W",
     "meaning": "the world, $W \\in \\mathsf{World}$"
    },
    {
     "name": "p",
     "meaning": "the process, $p = (C, E) \\in \\mathsf{Proc}$"
    },
    {
     "name": "T",
     "meaning": "the type, $T \\in \\mathsf{Ty}$"
    },
    {
     "name": "N",
     "meaning": "the bound, fixed before $\\alpha$"
    },
    {
     "name": "a",
     "meaning": "the annotated configuration, chosen at each index $\\alpha$"
    }
   ]
  },
  "sp.exists-before-forall": {
   "title": "$\\forall \\alpha$ before $\\exists a$",
   "what": "$N$ is fixed before the index, and the annotated configuration $a$ is an ordinary existential at each ordinal index $\\alpha$. The creation of a channel chooses its position, facts and tickets inside O-New.",
   "why": "The relation holds at every ordinal of a universe above the space of creation choices. The existential property, proved from excluded middle and choice, turns $\\forall \\alpha.\\ \\exists a$ into $\\exists a.\\ \\forall \\alpha$, so along a run every choice holds at every index.",
   "breaks": "At the finite indices alone the existential property fails for an infinite space of choices, the example $\\exists n.\\ \\triangleright^{n}\\bot$ of transfinite step indexing.",
   "example": "$\\exists N.\\ \\forall \\alpha.\\ \\exists a.\\ \\ldots$",
   "rocq": "not yet in the Rocq (docs/redesign/check-transfinite.md)",
   "sig": "\\exists N \\in \\mathbb{N}.\\ \\forall \\alpha.\\ \\exists a.\\ \\mathsf{erase}(q_a) = p \\land \\ldots",
   "args": [
    {
     "name": "N",
     "meaning": "the bound on the tickets of a channel, $N \\in \\mathbb{N} \\cup \\{\\infty\\}$"
    },
    {
     "name": "\\alpha",
     "meaning": "an ordinal index"
    },
    {
     "name": "a",
     "meaning": "the annotated configuration"
    }
   ]
  },
  "sp.next": {
   "title": "$\\mathsf{lf\\_next}$",
   "what": "$\\mathsf{lf\\_next}\\,N\\,(q, K)\\,ev\\,(q', K')$ holds when $K'$ is one of the ownership maps $\\mathsf{own\\_next}\\,N\\,ev\\,K$ allows.",
   "why": "A creation places the new ends at a position, with facts and with tickets of sum at most $N$, each counter at its tickets. An action moves its end to the next point and resets its counter to its tickets. A transfer moves the ends to the receiving thread and decrements their counters. A link renames. None of these depends on the index, and the choices of a creation come from O-New and F-New.",
   "breaks": "Nothing. It is a definition.",
   "example": "One step of the lock-free process relation along an event.",
   "rocq": "not yet in the Rocq (docs/redesign/check-links-without-tickets.md and check-transfinite.md)",
   "sig": "\\mathsf{lf\\_next} : \\mathbb{N} \\to \\mathsf{LFState} \\to \\mathsf{Event} \\to \\mathsf{LFState} \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "N",
     "meaning": "the bound on the tickets of a channel, $N \\in \\mathbb{N} \\cup \\{\\infty\\}$"
    },
    {
     "name": "(q, K)",
     "meaning": "the state"
    },
    {
     "name": "ev",
     "meaning": "the event"
    },
    {
     "name": "(q', K')",
     "meaning": "the state after the event"
    }
   ]
  },
  "sp.cap": {
   "title": "$f \\leq m$",
   "what": "Each counter recorded in $K$ is at most the tickets of its end.",
   "why": "The partner bound $N - m$ of an end bounds the counter of its partner only through this inequality, which E-Link and F-Link use.",
   "breaks": "A counter above its tickets would let the new partner after a link have a counter above the bound the link premise checks.",
   "example": "$K(a) = (0, \\rho, 2, 3)$ with $2 \\leq 3$.",
   "rocq": "soup/State.v: sp_cap",
   "sig": "K(o) = (\\_, \\_, f, m) \\Rightarrow f \\leq m",
   "args": [
    {
     "name": "f, m",
     "meaning": "the counter and the tickets of $o$"
    }
   ]
  },
  "sp.tsum": {
   "title": "$m + m' \\leq N$ on internal channels",
   "what": "For an internal channel the tickets of its two ends, read from $K$, sum to at most $N$.",
   "why": "It is the invariant $\\mathsf{tk}(o) + \\mathsf{tk}(\\overline{o}) \\leq N$ of typing, kept along a run. A creation chooses tickets with that sum, an action keeps the tickets, and a link joins two ends whose tickets meet it by the premise of F-Link. Lock-free adequacy measures a wait by the counter of the dual end, and this invariant bounds the counter of a new partner after a link.",
   "breaks": "Without it the measure need not fall at a link.",
   "example": "$K(c^{+}) = (0, x, 3, 3)$ and $K(c^{-}) = (1, \\overline{x}, 1, 1)$ at $N = 4$.",
   "rocq": "soup/State.v: sp_tsum",
   "sig": "\\mathsf{ech}\\,o \\in C \\land K(o) = (\\_, \\_, \\_, m) \\land K(\\overline{o}) = (\\_, \\_, \\_, m') \\Rightarrow m + m' \\leq N",
   "args": [
    {
     "name": "m, m'",
     "meaning": "the tickets of the two ends of an internal channel"
    },
    {
     "name": "N",
     "meaning": "the bound on the tickets of a channel, $N \\in \\mathbb{N} \\cup \\{\\infty\\}$"
    }
   ]
  },
  "sp.own": {
   "title": "$\\mathsf{consistent}(a, A, \\Phi)$",
   "what": "The ownership map $K$ of the annotated configuration agrees with $A$ and $\\Phi$. Each held end is held by one thread of the configuration and is internal or in the interface. Both ends of an internal channel are held, at dual types, points and protocols. Interface entries come from $\\Sigma$, counters are finite and at most the tickets, and the tickets of the two ends of an internal channel sum to at most $N$.",
   "why": "Lock-free adequacy reads the thread holding an end, its point and its counter from $K$, and concludes that the dual end of an internal end is held by some thread at the dual protocol.",
   "breaks": "Without it a thread could wait on an end whose dual end no thread holds, and the chain of waits in the proof of adequacy would break off.",
   "example": "Two threads closing $c^{+}$ and $c^{-}$, each holding one end, with $C = \\{c\\}$.",
   "rocq": "soup/State.v: soup_gen",
   "sig": "\\mathsf{consistent} : \\mathsf{LFState} \\to \\mathsf{Env} \\to (\\mathsf{End} \\rightharpoonup \\mathsf{STy} \\times \\mathbb{N} \\times \\mathbb{N}) \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "a",
     "meaning": "the annotated configuration $(q, K)$"
    },
    {
     "name": "A",
     "meaning": "the held ends for the relation"
    },
    {
     "name": "\\Phi",
     "meaning": "the held ends for fuel"
    }
   ]
  },
  "sr.FE": {
   "title": "Fuel $F^N_\\alpha\\llbracket\\Phi \\vdash \\sigma\\ !\\ d\\rrbracket$",
   "what": "The thread holds the ends $\\Phi$, each with counter and tickets, and has fuel at the ordinal index $\\alpha$ to return at $\\sigma$ within $d$ actions.",
   "why": "It bounds postponement per thread, independent of points. It is indexed by $\\alpha$, as $E$ is, so it is written as membership and not as a judgment.",
   "breaks": "Nothing. It is a definition.",
   "example": "$F^{4}_\\alpha\\llbracket\\{a \\mapsto S^{3}_{3}\\} \\vdash \\mathsf{thread}\\ !\\ \\infty\\rrbracket$.",
   "rocq": "not yet in the Rocq (docs/redesign/check-links-without-tickets.md and check-transfinite.md)",
   "sig": "e \\in F^{N}_{\\alpha}\\llbracket \\Phi \\vdash \\sigma\\ !\\ d \\rrbracket",
   "args": [
    {
     "name": "N",
     "meaning": "the bound on the tickets of a channel, $N \\in \\mathbb{N} \\cup \\{\\infty\\}$"
    },
    {
     "name": "\\alpha",
     "meaning": "the ordinal index"
    },
    {
     "name": "\\Phi",
     "meaning": "the held ends, a finite map $o \\mapsto S^{f}_{m}$ from ends to a protocol, a counter $f$ and tickets $m \\geq f$"
    },
    {
     "name": "\\sigma",
     "meaning": "the result, a credited type or $\\mathsf{thread}$"
    },
    {
     "name": "d",
     "meaning": "the frame, the actions left before returning, $d \\in \\mathbb{N} \\cup \\{\\infty\\}$"
    },
    {
     "name": "e",
     "meaning": "the term"
    }
   ]
  },
  "sr.FV": {
   "title": "Values with fuel, $FV^N_{\\alpha}\\llbracket\\Phi \\vdash \\sigma\\rrbracket$",
   "what": "The value holds exactly the ends $\\Phi$, and their counters meet the credits of $\\sigma$.",
   "why": "Values have the protocols and counters of their ends.",
   "breaks": "Nothing. It is a definition.",
   "example": "$o \\in FV\\llbracket\\{o \\mapsto S^{3}\\} \\vdash (S@x)^2\\rrbracket$.",
   "rocq": "fuel/Fuel.v: Vfuel, Vty",
   "sig": "v \\in FV^{N}_{\\alpha}\\llbracket \\Phi \\vdash \\sigma \\rrbracket",
   "args": [
    {
     "name": "N",
     "meaning": "the bound on the tickets of a channel, $N \\in \\mathbb{N} \\cup \\{\\infty\\}$"
    },
    {
     "name": "\\alpha",
     "meaning": "the level, an ordinal"
    },
    {
     "name": "\\Phi",
     "meaning": "the held ends, a finite map $o \\mapsto S^{f}_{m}$ from ends to a protocol, a counter $f$ and tickets $m \\geq f$"
    },
    {
     "name": "\\sigma",
     "meaning": "the result"
    },
    {
     "name": "v",
     "meaning": "the value"
    }
   ]
  },
  "sr.act": {
   "title": "$\\mathsf{act}\\,o$",
   "what": "The common premise of every action on $o$, F-Wait and F-Count.",
   "why": "Send, receive, close, select and branch share this premise.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{act}\\,a$ at $\\Phi = \\{a \\mapsto S\\annot{^{0}}, b \\mapsto S'^{1}\\}$ holds.",
   "rocq": "fuel/Fuel.v: f_act",
   "sig": "\\mathsf{act} : \\mathsf{End} \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "o",
     "meaning": "the subject end, $o \\in \\mathsf{End}$"
    },
    {
     "name": "\\Phi",
     "meaning": "the held ends, a finite map $o \\mapsto S^{f}_{m}$ from ends to a protocol, a counter $f$ and tickets $m \\geq f$"
    },
    {
     "name": "d",
     "meaning": "the frame"
    }
   ]
  },
  "sr.thunk": {
   "title": "$\\mathsf{thunk}(e)$",
   "what": "$\\mathsf{thunk}(e) = \\lambda\\_.\\,e[!e]$.",
   "why": "Forcing $!e$ steps to $e[!e]$, which the thunk delays by one $\\lambda$.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{thunk}(\\mathsf{force}\\,f) = \\lambda\\_.\\,\\mathsf{force}\\,(!\\mathsf{force}\\,f)$.",
   "rocq": "relation/Relation.v: thunk",
   "sig": "\\mathsf{thunk} : \\mathsf{Expr} \\to \\mathsf{Val}",
   "args": [
    {
     "name": "e",
     "meaning": "the body of a box"
    }
   ]
  },
  "sr.size": {
   "title": "$\\mathsf{size}\\,T$",
   "what": "The size of a type, with a box counting $3 + \\mathsf{size}\\,U$.",
   "why": "It makes $V$ at a box read $V$ at the smaller thunk type.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{size}\\,\\ast = 1$.",
   "rocq": "relation/Relation.v: tsize",
   "sig": "\\mathsf{size} : \\mathsf{Ty} \\to \\mathbb{N}",
   "args": [
    {
     "name": "T",
     "meaning": "the type, $T \\in \\mathsf{Ty}$"
    }
   ]
  },
  "sr.irred": {
   "title": "$\\mathsf{irred}\\,e$",
   "what": "$e$ takes no step, $\\neg\\exists \\alpha, e'.\\ e \\xrightarrow{\\alpha} e'$.",
   "why": "Values and stuck terms are irreducible.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{irred}\\,\\ast$.",
   "rocq": "lang/Semantics.v: irred",
   "sig": "\\mathsf{irred} : \\mathsf{Expr} \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "e",
     "meaning": "the term"
    }
   ]
  },
  "sr.ready": {
   "title": "$\\mathsf{ready}_W(\\Theta \\mid F, t)$",
   "what": "Readiness of a term with environment $\\Theta$ and future $F$ in world $W$.",
   "why": "It excludes circular waiting.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{ready}_W(\\{c^{+} \\mapsto \\mathsf{Close}@\\rho\\} \\mid \\varnothing, \\mathsf{close}\\,c^{+})$.",
   "rocq": "relation/Readiness.v: ready_t",
   "sig": "\\mathsf{ready} : \\mathsf{World} \\to \\mathsf{Env} \\to \\mathcal{P}(\\mathsf{Point}) \\to \\mathsf{Expr} \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "W",
     "meaning": "the world, $W \\in \\mathsf{World}$"
    },
    {
     "name": "\\Theta",
     "meaning": "the environment, a finite map $\\mathsf{End} \\rightharpoonup \\mathsf{STy} \\times \\mathsf{Point}$"
    },
    {
     "name": "F",
     "meaning": "the future, a finite set of points"
    },
    {
     "name": "t",
     "meaning": "the term"
    }
   ]
  },
  "sr.readyp": {
   "title": "$\\mathsf{ready}_W(\\Sigma, p)$",
   "what": "Readiness of a process with interface $\\Sigma$ in world $W$.",
   "why": "It excludes circular waiting across the interface.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{ready}_W(\\varnothing, (\\varnothing, \\{\\ast\\}))$.",
   "rocq": "relation/Readiness.v: ready_p",
   "sig": "\\mathsf{ready} : \\mathsf{World} \\to \\mathsf{Env} \\to \\mathsf{Proc} \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "W",
     "meaning": "the world, $W \\in \\mathsf{World}$"
    },
    {
     "name": "\\Sigma",
     "meaning": "the interface, a finite map $\\mathsf{End} \\rightharpoonup \\mathsf{STy} \\times \\mathsf{Point}$"
    },
    {
     "name": "p",
     "meaning": "the process, $p = (C, E) \\in \\mathsf{Proc}$"
    }
   ]
  },
  "sr.obl": {
   "title": "$\\mathsf{Obl}_\\ell(e')$",
   "what": "The obligation of the step label $\\ell$, one of O-Beta to O-Link.",
   "why": "Each label has its own obligation, read off the label.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{Obl}_{\\beta}(e') = $ O-Beta.",
   "rocq": "relation/Relation.v: Eobl",
   "sig": "\\mathsf{Obl} : \\mathsf{TLabel} \\to \\mathsf{Expr} \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "\\ell",
     "meaning": "the step label"
    },
    {
     "name": "e'",
     "meaning": "the successor"
    }
   ]
  },
  "sr.pobl": {
   "title": "$\\mathsf{Pobl}_{ev}(p')$",
   "what": "The obligation of the event $ev$, one of Q-Tau to Q-Link.",
   "why": "Each event has its own obligation, read off the event.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{Pobl}_{ev}$ is Q-Tau for an internal event.",
   "rocq": "relation/Relation.v: Pobl",
   "sig": "\\mathsf{Pobl} : \\mathsf{Event} \\to \\mathsf{Proc} \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "ev",
     "meaning": "the event"
    },
    {
     "name": "p'",
     "meaning": "the process after the step"
    }
   ]
  },
  "sr.fobl": {
   "title": "$\\mathsf{Fobl}^N_\\ell(e')$",
   "what": "The fuel obligation of the step label $\\ell$, one of F-Beta to F-Link, read at an index $\\beta$.",
   "why": "Each label has its own fuel update.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{Fobl}$ of a send is F-Send.",
   "rocq": "fuel/Fuel.v: Fobl",
   "sig": "\\mathsf{Fobl}\\annot{^{N}} : \\mathsf{TLabel} \\to \\mathsf{Expr} \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "N",
     "meaning": "the bound on the tickets of a channel, $N \\in \\mathbb{N} \\cup \\{\\infty\\}$"
    },
    {
     "name": "\\ell",
     "meaning": "the step label"
    },
    {
     "name": "e'",
     "meaning": "the successor"
    }
   ]
  },
  "sr.fuseok": {
   "title": "$(h, D) \\in \\mathsf{Fus}(\\Sigma, p)$",
   "what": "$(h, D)$ is an admissible fusion of the held ends of $p$ with interface $\\Sigma$.",
   "why": "One notion covers renaming, internalizing pairs and the renaming of a link.",
   "breaks": "Nothing. It is a definition.",
   "example": "$(\\mathsf{id}, \\varnothing) \\in \\mathsf{Fus}(\\Sigma, p)$.",
   "rocq": "relation/Relation.v: fuse_ok",
   "sig": "\\mathsf{Fus}(\\Sigma, p) \\subseteq (\\mathsf{End} \\to \\mathsf{End}) \\times \\mathcal{P}_{\\mathrm{fin}}(\\mathsf{Chan})",
   "args": [
    {
     "name": "h",
     "meaning": "the map of ends"
    },
    {
     "name": "D",
     "meaning": "the channels restricted by the fusion"
    },
    {
     "name": "\\Sigma",
     "meaning": "the interface, a finite map $\\mathsf{End} \\rightharpoonup \\mathsf{STy} \\times \\mathsf{Point}$"
    },
    {
     "name": "p",
     "meaning": "the process, $p = (C, E) \\in \\mathsf{Proc}$"
    }
   ]
  },
  "sr.sdrop": {
   "title": "$(h, D)\\cdot\\Sigma$",
   "what": "$\\Sigma$ renamed by $h$, without the ends of the channels $D$, in the Rocq $\\mathsf{sdrop}\\,D\\,(h\\,\\Sigma)$.",
   "why": "The channels of $D$ become restricted and leave the interface.",
   "breaks": "Nothing. It is a definition.",
   "example": "$(\\mathsf{id}, \\{c\\})\\cdot\\{c^{+}, c^{-}, d^{+}\\} = \\{d^{+}\\}$.",
   "rocq": "relation/Relation.v: sdrop, kren",
   "sig": "(h, D)\\cdot\\Sigma : \\mathsf{Env}",
   "args": [
    {
     "name": "h",
     "meaning": "the map of ends"
    },
    {
     "name": "D",
     "meaning": "the channels"
    },
    {
     "name": "\\Sigma",
     "meaning": "the interface, a finite map $\\mathsf{End} \\rightharpoonup \\mathsf{STy} \\times \\mathsf{Point}$"
    }
   ]
  },
  "sr.pfuse": {
   "title": "$(h, D)\\cdot p$",
   "what": "$p$ renamed by $h$ with the channels $D$ added to the restricted set, in the Rocq $\\mathsf{pfuse}\\,h\\,D\\,p$.",
   "why": "It is the process after the fusion.",
   "breaks": "Nothing. It is a definition.",
   "example": "$(\\mathsf{id}, \\{c\\})\\cdot(C, E) = (C \\cup \\{c\\}, E)$.",
   "rocq": "relation/Relation.v: pfuse",
   "sig": "(h, D)\\cdot p : \\mathsf{Proc}",
   "args": [
    {
     "name": "h",
     "meaning": "the map of ends"
    },
    {
     "name": "D",
     "meaning": "the new restricted channels"
    },
    {
     "name": "p",
     "meaning": "the process, $p = (C, E) \\in \\mathsf{Proc}$"
    }
   ]
  },
  "sr.pirred": {
   "title": "$\\mathsf{pirred}\\,p$",
   "what": "$p$ takes no process step.",
   "why": "P-Stop applies exactly to irreducible processes.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{pirred}\\,(\\varnothing, \\{\\ast\\})$.",
   "rocq": "lang/Process.v: pirred",
   "sig": "\\mathsf{pirred} : \\mathsf{Proc} \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "p",
     "meaning": "the process, $p = (C, E) \\in \\mathsf{Proc}$"
    }
   ]
  },
  "sr.held": {
   "title": "Held ends",
   "what": "$\\mathsf{held} = \\{o \\mid o \\in \\mathrm{dom}\\,\\Sigma \\lor \\mathsf{ech}\\,o \\in C\\}$.",
   "why": "A process holds its interface ends and both ends of every restricted channel.",
   "breaks": "Nothing. It is a definition.",
   "example": "For $\\Sigma = \\{d^{+}\\}$ and $C = \\{c\\}$, $\\mathsf{held} = \\{d^{+}, c^{+}, c^{-}\\}$.",
   "rocq": "relation/Relation.v: pheld",
   "sig": "\\mathsf{held} \\subseteq \\mathsf{End}",
   "args": [
    {
     "name": "\\Sigma",
     "meaning": "the interface, a finite map $\\mathsf{End} \\rightharpoonup \\mathsf{STy} \\times \\mathsf{Point}$"
    },
    {
     "name": "C",
     "meaning": "the restricted channels"
    }
   ]
  },
  "sr.gch": {
   "title": "$\\mathsf{gch}_h$",
   "what": "$\\mathsf{gch}_h(c) = \\mathsf{ech}(h(c^{+}))$, the channel map induced by $h$.",
   "why": "Restricted sets are sets of channels, so $h$ acts on them through its action on $c^{+}$.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{gch}_{\\mathsf{id}}(c) = c$.",
   "rocq": "relation/Relation.v: gch",
   "sig": "\\mathsf{gch}_h : \\mathsf{Chan} \\to \\mathsf{Chan}",
   "args": [
    {
     "name": "h",
     "meaning": "the map of ends"
    },
    {
     "name": "c",
     "meaning": "a channel"
    }
   ]
  },
  "sr.tenv-erase": {
   "title": "$|\\Delta|$",
   "what": "The ends of $\\Delta$ with their session types and points, each entry $(S@x)\\annot{^{a}}$ becoming $S@x$.",
   "why": "\\annp{$E$ reads ends only, and no credit.}",
   "breaks": "Nothing. It is a definition.",
   "example": "$|c^{+} : (S@\\rho)^{3},\\ 0 : T| = \\{c^{+} \\mapsto S@\\rho\\}$.",
   "rocq": "relation/Relation.v: tenv_erase",
   "sig": "|\\cdot| : \\mathsf{Ctx} \\to \\mathsf{Env}",
   "args": [
    {
     "name": "\\Delta",
     "meaning": "a linear context"
    }
   ]
  },
  "sr.fvagg": {
   "title": "Products, sums and existentials in $FV$",
   "what": "$\\otimes$ splits $\\Phi$ disjointly between its parts, $\\oplus$ checks the injected part, and $\\exists$ checks its body.",
   "why": "Only ends and closures have credits, so these types only pass $\\Phi$ on.",
   "breaks": "Nothing. It is a definition.",
   "example": "$(S@x)^{2} \\otimes \\ast$ gives $o$ to the first part.",
   "rocq": "fuel/Fuel.v: Vty",
   "sig": "FV \\text{ at } \\otimes, \\oplus, \\exists",
   "args": [
    {
     "name": "\\Phi",
     "meaning": "the held ends, split among the parts"
    }
   ]
  },
  "th.adequacy": {
   "title": "Adequacy",
   "what": "If $\\varnothing \\vDash_W p : T$ then $p$ is deadlock free.",
   "why": "It turns the semantic judgment into the safety property. The relation reads ranked worlds, whose order has no cycle, so readiness of threads waiting round a cycle never holds and no strictness premise remains.",
   "breaks": "With a cyclic order the premise would hold for two threads that wait on each other.",
   "example": "Two threads closing the two ends of $c$ are deadlock free.",
   "rocq": "relation/Adequacy.v: adequacy",
   "sig": "\\varnothing \\vDash_W p : T \\Rightarrow \\mathsf{deadlock\\_free}\\,p",
   "args": [
    {
     "name": "W",
     "meaning": "a static world, the semantic judgments read the relation at the ranked worlds that satisfy $W$"
    },
    {
     "name": "p",
     "meaning": "a closed process $(C, E)$"
    },
    {
     "name": "T",
     "meaning": "the result type of the main thread"
    }
   ]
  },
  "th.lf-adequacy": {
   "title": "Lock-free adequacy",
   "what": "Under excluded middle and choice, if $\\varnothing \\Vvdash_W p : T$ then $p$ is lock free.",
   "why": "A pending thread waits for the thread holding the partner of its end. The proof follows this chain of waiting threads and shows it is finite. Its measure ranks a waiting thread by the ordinal $\\varrho(\\mathsf{pt}\\,o)$ of the end $o$ it waits on and then by the counter of the dual end. Ranks are ordinals, so the chain is finite, and a link moves a waiting thread to a partner with a lower counter. The existential property turns the annotated configuration chosen at each ordinal index into one that holds at every index, and the run is then a sequence of such configurations.",
   "breaks": "Without ranks an infinite descending chain of points lets a thread wait forever along an infinite chain of holding threads.",
   "example": "Two threads closing the two ends of $c$ are lock free.",
   "rocq": "soup/LFAdequacy.v: lf_adequacy; types/Worlds.v: wchain_lt_wf",
   "sig": "\\mathsf{EM} \\land \\mathsf{AC} \\land \\varnothing \\Vvdash_W p : T \\Rightarrow \\mathsf{lock\\_free}\\,p",
   "args": [
    {
     "name": "W",
     "meaning": "a static world, the semantic judgments read the relation at the ranked worlds that satisfy $W$"
    },
    {
     "name": "p",
     "meaning": "a closed process $(C, E)$"
    },
    {
     "name": "T",
     "meaning": "the result type of the main thread"
    }
   ]
  },
  "th.lf-thread-progress": {
   "title": "Thread progress",
   "what": "Under the premises of lock-free adequacy, excluded middle and choice included, every run $(r, l)$ with $\\mathsf{erase}(r\\,0) = p$, $\\mathsf{maximal}\\,(r, l)$ and $\\mathsf{wfair}\\,(r, l)$ satisfies $\\mathsf{thread\\_progress\\_run}\\,(r, l)$.",
   "why": "Every thread eventually returns a value or takes part in a session step, so no thread, pending or not, is postponed forever.",
   "breaks": "Nothing. It is a definition.",
   "example": "Every lock-free example.",
   "rocq": "soup/LFAdequacy.v: lf_thread_progress",
   "sig": "\\ldots \\Rightarrow \\forall (r, l).\\ \\mathsf{erase}(r\\,0) = p \\land \\mathsf{maximal}\\,(r, l) \\land \\mathsf{wfair}\\,(r, l) \\Rightarrow \\mathsf{thread\\_progress\\_run}\\,(r, l)",
   "args": [
    {
     "name": "W",
     "meaning": "a static world, the semantic judgments read the relation at the ranked worlds that satisfy $W$"
    },
    {
     "name": "p",
     "meaning": "a closed process $(C, E)$"
    },
    {
     "name": "(r, l)",
     "meaning": "a run, $r\\,i$ the configuration and $l\\,i$ the event at position $i$"
    }
   ]
  },
  "th.fundamental": {
   "title": "Fundamental theorem",
   "what": "$\\varnothing ; \\Delta \\vdash^{F}_{W} t : T$ implies $\\Delta \\vDash^{F}_{W} t : T$.",
   "why": "Each typing rule has a semantic counterpart that holds at every level, and the theorem is the induction on the derivation.",
   "breaks": "Nothing. It is a definition.",
   "example": "The main thread of the cycle example satisfies the semantic judgment.",
   "rocq": "static/Fundamental.v: fundamental",
   "sig": "\\mathsf{strict}\\,W \\land \\varnothing ; \\Delta \\vdash^{F}_{W} t : T \\Rightarrow \\Delta \\vDash^{F}_{W} t : T",
   "args": [
    {
     "name": "W",
     "meaning": "a static world, the semantic judgments read the relation at the ranked worlds that satisfy $W$"
    },
    {
     "name": "\\Delta",
     "meaning": "the linear context of ends and variables"
    },
    {
     "name": "F",
     "meaning": "the future"
    },
    {
     "name": "t",
     "meaning": "the term"
    },
    {
     "name": "T",
     "meaning": "its type"
    }
   ]
  },
  "th.fundamental-typed": {
   "title": "Fundamental theorem for annotated typing",
   "what": "For each $N$, the annotated typing judgment implies the semantic judgment at $\\Delta_{df}$ and $T_{df}$.",
   "why": "Erasing the annotations of an annotated derivation gives a deadlock-free derivation, to which the fundamental theorem applies.",
   "breaks": "Nothing. It is a definition.",
   "example": "The client and server main at $N = \\infty$.",
   "rocq": "static/Fundamental.v: fundamental_typed",
   "sig": "\\mathsf{strict}\\,W \\land \\varnothing ; \\Delta \\vdash^{F}_{W\\annot{,N}} t : T\\ !\\ \\varepsilon \\Rightarrow \\Delta_{df} \\vDash^{F}_{W} t : T_{df}",
   "args": [
    {
     "name": "W",
     "meaning": "a static world, the semantic judgments read the relation at the ranked worlds that satisfy $W$"
    },
    {
     "name": "\\Delta",
     "meaning": "the linear context of ends and variables"
    },
    {
     "name": "N",
     "meaning": "any bound on tickets"
    }
   ]
  },
  "th.live-fundamental": {
   "title": "Live fundamental theorem",
   "what": "$\\varnothing ; \\Delta \\vdash^{F}_{W} t : T$ and $\\varnothing \\vdash\\!\\triangleright t$ imply $\\Delta \\mathrel{|\\!\\!\\vDash}^{F}_{W} t : T$.",
   "why": "The guard lets a box recurse only after an action, so every recursive call is read at a lower level, as the least fixpoint of the relation at $kappa_L$ requires.",
   "breaks": "Without the guard the statement is false, $!(f = \\mathsf{force}\\,f)$ types and satisfies no live judgment.",
   "example": "The guarded receive loop.",
   "rocq": "static/Fundamental.v: live_fundamental",
   "sig": "\\mathsf{strict}\\,W \\land \\varnothing ; \\Delta \\vdash^{F}_{W} t : T \\land \\varnothing \\vdash\\!\\triangleright t \\Rightarrow \\Delta \\mathrel{|\\!\\!\\vDash}^{F}_{W} t : T",
   "args": [
    {
     "name": "W",
     "meaning": "a static world, the semantic judgments read the relation at the ranked worlds that satisfy $W$"
    },
    {
     "name": "\\Delta",
     "meaning": "the linear context of ends and variables"
    },
    {
     "name": "F",
     "meaning": "the future"
    },
    {
     "name": "t",
     "meaning": "the guarded term"
    }
   ]
  },
  "th.live-fundamental-typed": {
   "title": "Live fundamental theorem for annotated typing",
   "what": "The annotated typing judgment with $\\varnothing \\vdash\\!\\triangleright t$ implies the live judgment at erased environments and type.",
   "why": "Lock-free soundness obtains the relation at $kappa_L$ of each thread from this theorem.",
   "breaks": "Nothing. It is a definition.",
   "example": "A thread typed by P-Term at finite $N$.",
   "rocq": "static/Fundamental.v: live_fundamental_typed",
   "sig": "\\mathsf{strict}\\,W \\land \\ldots \\vdash^{F}_{W\\annot{,N}} t : T\\ !\\ \\varepsilon \\land \\varnothing \\vdash\\!\\triangleright t \\Rightarrow \\Delta_{df} \\mathrel{|\\!\\!\\vDash}^{F}_{W} t : T_{df}",
   "args": [
    {
     "name": "W",
     "meaning": "a static world, the semantic judgments read the relation at the ranked worlds that satisfy $W$"
    },
    {
     "name": "N",
     "meaning": "any bound on tickets"
    },
    {
     "name": "t",
     "meaning": "the guarded term"
    }
   ]
  },
  "th.fundamental-proc": {
   "title": "Fundamental theorem for processes",
   "what": "$\\Sigma \\vdash\\annot{^{\\infty}}_{W} p : T$ implies $\\Sigma \\vDash_W p : T$. P-Term asks a well-founded world, and P-Connect keeps the join well-founded, so the derivation gives $\\mathsf{wf}\\,W$ and the theorem reads the relation at the ranked worlds that satisfy $W$.",
   "why": "It is an induction on the process derivation with the semantic P-Term and P-Connect as cases.",
   "breaks": "Nothing. It is a definition.",
   "example": "Two threads closing the two ends of $c$.",
   "rocq": "static/FundamentalProc.v: fundamental_proc",
   "sig": "\\Sigma \\vdash\\annot{^{\\infty}}_{W} p : T \\Rightarrow \\Sigma \\vDash_W p : T",
   "args": [
    {
     "name": "W",
     "meaning": "a static world, the semantic judgments read the relation at the ranked worlds that satisfy $W$"
    },
    {
     "name": "\\Sigma",
     "meaning": "the interface of the process"
    },
    {
     "name": "p",
     "meaning": "a closed process $(C, E)$"
    },
    {
     "name": "T",
     "meaning": "the result type of the main thread"
    }
   ]
  },
  "th.lf-fundamental": {
   "title": "Lock-free fundamental theorem",
   "what": "$\\Sigma \\Vdash^{N}_{W} p : T$ implies $\\Sigma \\Vvdash_W p : T$.",
   "why": "The fuel of each thread comes from its cost typing at finite $N$, and its relation at $kappa_L$ from its guarded typing.",
   "breaks": "Nothing. It is a definition.",
   "example": "The cycle example.",
   "rocq": "soup/LFTyped.v: lf_fundamental",
   "sig": "\\Sigma \\Vdash^{N}_{W} p : T \\Rightarrow \\Sigma \\Vvdash_W p : T",
   "args": [
    {
     "name": "W",
     "meaning": "a static world, the semantic judgments read the relation at the ranked worlds that satisfy $W$"
    },
    {
     "name": "\\Sigma",
     "meaning": "the interface of the process"
    },
    {
     "name": "N",
     "meaning": "the bound on the tickets of a channel, a natural number for lock freedom"
    },
    {
     "name": "p",
     "meaning": "a closed process $(C, E)$"
    },
    {
     "name": "T",
     "meaning": "the result type of the main thread"
    }
   ]
  },
  "th.sem-p-term": {
   "title": "Semantic P-Term",
   "what": "If $\\mathsf{tfree}\\,T$, $\\mathsf{sth}\\,\\Theta\\,\\Sigma\\,\\Theta_B\\,C$ and $t \\in E[\\kappa]^{W}_{\\alpha}\\llbracket\\Theta \\vdash T\\rrbracket^{\\varnothing}$, then $(C, \\{t\\}) \\in P[\\kappa]^{W}_{\\alpha}\\llbracket\\Sigma \\vdash T\\rrbracket$.",
   "why": "It is P-Term in the relation. When $t$ spawns $v$, the child receives exactly the ends $\\mathsf{fends}(v)$, which $V$ fixes by $\\mathrm{dom}\\,\\Theta = \\mathsf{fends}(v)$, and the proof composes parent and child as P-Connect does.",
   "breaks": "Nothing. It is a definition.",
   "example": "A single thread with $\\Sigma = \\varnothing$ and $C = \\varnothing$.",
   "rocq": "compat/PTerm.v: sem_p_term",
   "sig": "\\mathsf{tfree}\\,T \\land \\mathsf{sth}\\,\\Theta\\,\\Sigma\\,\\Theta_B\\,C \\land t \\in E[\\kappa]^{W}_{\\alpha}\\llbracket\\Theta \\vdash T\\rrbracket^{\\varnothing} \\Rightarrow (C, \\{t\\}) \\in P[\\kappa]^{W}_{\\alpha}\\llbracket\\Sigma \\vdash T\\rrbracket",
   "args": [
    {
     "name": "\\kappa",
     "meaning": "a cost table, $\\kappa_{DF}$ for deadlock freedom and $\\kappa_L$ for liveness"
    },
    {
     "name": "\\alpha",
     "meaning": "the level, an ordinal"
    },
    {
     "name": "\\Sigma",
     "meaning": "the interface of the process"
    },
    {
     "name": "\\Theta_B",
     "meaning": "the entries of the restricted ends"
    },
    {
     "name": "C",
     "meaning": "the restricted channels"
    },
    {
     "name": "t",
     "meaning": "the thread"
    }
   ]
  },
  "th.sth": {
   "title": "$\\mathsf{sth}\\,\\Theta\\,\\Sigma\\,\\Theta_B\\,C$",
   "what": "$\\Theta = \\Sigma \\cup \\Theta_B$, $\\mathrm{dom}\\,\\Theta_B = \\mathsf{ends}(C)$, $\\mathsf{chans}\\,\\Sigma \\cap C = \\varnothing$, $\\mathsf{pfree}\\,\\Sigma$, and for every $c \\in C$ the two entries of $\\Theta_B$ are dual at dual points.",
   "why": "These are the environment premises of P-Term, as the semantic proof uses these premises.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\Sigma = \\varnothing$ and $C = \\varnothing$ for a source program.",
   "rocq": "compat/PTerm.v: sth",
   "sig": "\\mathsf{sth} : \\mathsf{Env} \\to \\mathsf{Env} \\to \\mathsf{Env} \\to \\mathcal{P}(\\mathsf{Chan}) \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "\\Theta",
     "meaning": "the ends held by the term"
    },
    {
     "name": "\\Sigma",
     "meaning": "the interface of the process"
    },
    {
     "name": "\\Theta_B",
     "meaning": "the entries of the ends of restricted channels"
    },
    {
     "name": "C",
     "meaning": "the restricted channels"
    }
   ]
  },
  "th.sem-p-connect": {
   "title": "Semantic P-Connect",
   "what": "If $\\mathsf{tfree}\\,T$, $\\mathsf{conn}$, $p_1 \\in P^{W}_{\\alpha}\\llbracket\\Sigma_1 \\cup \\Sigma_C \\vdash T\\rrbracket$ and $p_2 \\in P^{W}_{\\alpha}\\llbracket\\Sigma_2 \\cup \\Sigma_D \\vdash \\ast\\rrbracket$, then $p_1 \\parallel_{\\Sigma_C} p_2 \\in P^{W}_{\\alpha}\\llbracket\\Sigma_1 \\cup \\Sigma_2 \\vdash T\\rrbracket$, with both components at one ranked world $W$.",
   "why": "It is P-Connect in the relation, for each level $n$ and each cost table. The composite reads both components at one ranked world that satisfies both static worlds, so two rankings are never reconciled, and a fresh root of either side is fresh for that world.",
   "breaks": "Nothing. It is a definition.",
   "example": "Two threads closing $c^{+}$ and $c^{-}$, cut at $c$.",
   "rocq": "compat/ConnectP.v: sem_p_connect",
   "sig": "\\mathsf{tfree}\\,T \\land \\mathsf{conn} \\land p_1 \\in P^{W}_{\\alpha}\\llbracket\\Sigma_1 \\cup \\Sigma_C \\vdash T\\rrbracket \\land p_2 \\in P^{W}_{\\alpha}\\llbracket\\Sigma_2 \\cup \\Sigma_D \\vdash \\ast\\rrbracket \\Rightarrow p_1 \\parallel_{\\Sigma_C} p_2 \\in P^{W}_{\\alpha}\\llbracket\\Sigma_1 \\cup \\Sigma_2 \\vdash T\\rrbracket",
   "args": [
    {
     "name": "\\alpha",
     "meaning": "the level, an ordinal"
    },
    {
     "name": "W",
     "meaning": "one ranked world for both components"
    },
    {
     "name": "\\Sigma_C, \\Sigma_D",
     "meaning": "the cut and its partners"
    },
    {
     "name": "p_1, p_2",
     "meaning": "the two components"
    }
   ]
  },
  "th.lf-p-term": {
   "title": "P-Term in the lock-free process relation",
   "what": "A thread with $\\Sigma \\Vdash^{N}_{W} (C_0, \\{t\\}) : T$ derived by P-Term satisfies $\\Sigma \\Vvdash_W (C_0, \\{t\\}) : T$.",
   "why": "It is P-Term read in the lock-free process relation.",
   "breaks": "Nothing. It is a definition.",
   "example": "One thread closing its end $c^{+}$.",
   "rocq": "soup/LFCompose.v: lf_p_term",
   "sig": "\\Sigma \\Vdash^{N}_{W} (C_0, \\{t\\}) : T \\Rightarrow \\Sigma \\Vvdash_W (C_0, \\{t\\}) : T",
   "args": [
    {
     "name": "W",
     "meaning": "a static world, the semantic judgments read the relation at the ranked worlds that satisfy $W$"
    },
    {
     "name": "\\Sigma",
     "meaning": "the interface of the process"
    },
    {
     "name": "t",
     "meaning": "the single thread"
    },
    {
     "name": "C_0",
     "meaning": "its restricted channels"
    }
   ]
  },
  "th.Erel-bind": {
   "title": "Bind",
   "what": "For every cost table, if $e \\in E^{W}_{\\alpha}\\llbracket\\Theta_1 \\vdash T\\rrbracket^{F \\cup \\mathsf{ap}\\,\\Theta_2}$ and $f[v] \\in E^{W'}_{\\beta}\\llbracket\\Theta_v \\cup \\Theta_2 \\vdash U\\rrbracket^{F}$ for all $W' \\sqsupseteq W$, $j \\leq n$ and $v \\in V^{W'}_{\\beta}\\llbracket\\Theta_v \\vdash T\\rrbracket$, then $f[e] \\in E^{W}_{\\alpha}\\llbracket\\Theta_1 \\cup \\Theta_2 \\vdash U\\rrbracket^{F}$.",
   "why": "Every rule with a subterm runs the subterm first. The frame holds $\\Theta_2$ while the hole runs, so the hole must not wait above $\\mathsf{ap}\\,\\Theta_2$.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{let}\\ \\ast = \\mathsf{close}\\,c\\ \\mathsf{in}\\ \\mathsf{close}\\,d$ runs $\\mathsf{close}\\,c$ with $\\overline{x_d}$ in its future.",
   "rocq": "compat/Bind.v: Erel_bind",
   "sig": "e \\in E^{W}_{\\alpha}\\llbracket\\Theta_1 \\vdash T\\rrbracket^{F \\cup \\mathsf{ap}\\,\\Theta_2} \\land (\\forall W' \\sqsupseteq W, \\beta \\leq \\alpha, v.\\ \\ldots) \\Rightarrow f[e] \\in E^{W}_{\\alpha}\\llbracket\\Theta_1 \\cup \\Theta_2 \\vdash U\\rrbracket^{F}",
   "args": [
    {
     "name": "f",
     "meaning": "an evaluation frame"
    },
    {
     "name": "\\Theta_2",
     "meaning": "the ends the frame holds while $e$ runs"
    },
    {
     "name": "W', j, v",
     "meaning": "every later world, every level $\\beta \\leq \\alpha$ and every value $v$ in $V^{W'}_{\\beta}$ that $e$ may return"
    }
   ]
  },
  "th.soundness": {
   "title": "Soundness",
   "what": "$\\varnothing \\vdash\\annot{^{\\infty}}_{W} p : T$ implies that $p$ is deadlock free.",
   "why": "The fundamental theorem for processes followed by adequacy.",
   "breaks": "Nothing. It is a definition.",
   "example": "The cycle example is deadlock free.",
   "rocq": "static/FundamentalProc.v: soundness",
   "sig": "\\varnothing \\vdash\\annot{^{\\infty}}_{W} p : T \\Rightarrow \\mathsf{deadlock\\_free}\\,p",
   "args": [
    {
     "name": "W",
     "meaning": "a static world, the semantic judgments read the relation at the ranked worlds that satisfy $W$"
    },
    {
     "name": "p",
     "meaning": "a closed process $(C, E)$"
    },
    {
     "name": "T",
     "meaning": "the result type of the main thread"
    }
   ]
  },
  "th.soundness-source": {
   "title": "Soundness for source terms",
   "what": "For strict $W$, $\\mathsf{tfree}\\,T$ and $\\varnothing ; \\varnothing \\vdash^{\\varnothing}_{W} t : T$, the process $(\\varnothing, \\{t\\})$ is deadlock free.",
   "why": "A source term creates channels only at fresh roots and at fields of held ends, so it is P-Term with $\\Sigma = \\varnothing$ and $C_0 = \\varnothing$.",
   "breaks": "Nothing. It is a definition.",
   "example": "Every deadlock-free example.",
   "rocq": "static/FundamentalProc.v: soundness_source",
   "sig": "\\mathsf{tfree}\\,T \\land \\varnothing ; \\varnothing \\vdash^{\\varnothing}_{W} t : T \\Rightarrow \\mathsf{deadlock\\_free}(\\varnothing, \\{t\\})",
   "args": [
    {
     "name": "W",
     "meaning": "a static world, the semantic judgments read the relation at the ranked worlds that satisfy $W$"
    },
    {
     "name": "t",
     "meaning": "a source term, the main thread"
    },
    {
     "name": "T",
     "meaning": "the result type of the main thread"
    }
   ]
  },
  "th.lf-soundness": {
   "title": "Lock-free soundness",
   "what": "Under excluded middle and choice, $\\varnothing \\Vdash^{N}_{W} p : T$ implies that $p$ is lock free.",
   "why": "The lock-free fundamental theorem followed by lock-free adequacy.",
   "breaks": "Nothing. It is a definition.",
   "example": "The cycle example is lock free.",
   "rocq": "soup/LFTyped.v: lf_soundness",
   "sig": "\\mathsf{EM} \\land \\mathsf{AC} \\land \\varnothing \\Vdash^{N}_{W} p : T \\Rightarrow \\mathsf{lock\\_free}\\,p",
   "args": [
    {
     "name": "W",
     "meaning": "a static world, the semantic judgments read the relation at the ranked worlds that satisfy $W$"
    },
    {
     "name": "N",
     "meaning": "the bound on the tickets of a channel, a natural number for lock freedom"
    },
    {
     "name": "p",
     "meaning": "a closed process $(C, E)$"
    },
    {
     "name": "T",
     "meaning": "the result type of the main thread"
    }
   ]
  },
  "th.lf-soundness-source": {
   "title": "Lock-free soundness for source terms",
   "what": "For $W$ with $\\mathsf{wf}\\,W$, $N \\in \\mathbb{N}$, $\\mathsf{tfree}\\,T$, a typing $\\varnothing ; \\varnothing \\vdash^{\\varnothing}_{W\\annot{,N}} t : T\\ !\\ c$ and $\\varnothing \\vdash\\!\\triangleright t$, the process $(\\varnothing, \\{t\\})$ is lock free.",
   "why": "The premises are those of P-Term at finite $N$ with $\\Sigma = \\varnothing$ and $C_0 = \\varnothing$, plus the guard. Lock-free soundness then applies.",
   "breaks": "Nothing. It is a definition.",
   "example": "Every lock-free example.",
   "rocq": "soup/LFCompose.v: lf_soundness_source",
   "sig": "\\mathsf{wf}\\,W \\land N \\in \\mathbb{N} \\land \\ldots \\Rightarrow \\mathsf{lock\\_free}(\\varnothing, \\{t\\})",
   "args": [
    {
     "name": "W",
     "meaning": "a static world, the semantic judgments read the relation at the ranked worlds that satisfy $W$"
    },
    {
     "name": "N",
     "meaning": "the bound on the tickets of a channel, a natural number for lock freedom"
    },
    {
     "name": "t",
     "meaning": "the source term"
    }
   ]
  },
  "th.fair-run-exists": {
   "title": "A maximal weakly fair run exists",
   "what": "Assume excluded middle and dependent choice. For every configuration $q$ there is a run $(r, l)$ with $r\\,0 = q$, $\\mathsf{maximal}\\,(r, l)$ and $\\mathsf{wfair}\\,(r, l)$. Hence every process $p$ has such a run with $\\mathsf{erase}(r\\,0) = p$, and lock-free soundness also gives one for every typed $p$.",
   "why": "The scheduler goes round robin over thread numbers and at each position takes a step of the targeted thread when that thread is enabled. Dependent choice picks the steps and excluded middle decides enabledness. Lock freedom still quantifies over every such run.",
   "breaks": "Nothing. It is a definition.",
   "example": "Two threads $\\ast$ and $\\ast$ start a maximal weakly fair run.",
   "rocq": "lockfree/FairRun.v: fair_run_exists, fair_run_exists_proc; soup/LFTyped.v: lf_soundness_run",
   "sig": "\\mathsf{EM} \\land \\mathsf{DC} \\Rightarrow \\exists (r, l).\\ r\\,0 = q \\land \\mathsf{maximal}\\,(r, l) \\land \\mathsf{wfair}\\,(r, l)",
   "args": [
    {
     "name": "\\mathsf{EM}",
     "meaning": "excluded middle, $P \\lor \\lnot P$ for every proposition $P$, a hypothesis and no axiom"
    },
    {
     "name": "\\mathsf{DC}",
     "meaning": "dependent choice, a total relation on a type has an infinite chain from every element, a hypothesis and no axiom"
    },
    {
     "name": "q",
     "meaning": "a configuration, a lifting of $p$ for the process form"
    },
    {
     "name": "(r, l)",
     "meaning": "a run, $r\\,i$ the configuration and $l\\,i$ the event at position $i$"
    }
   ]
  },
  "th.lf-padovani": {
   "title": "Lock freedom in reachability form",
   "what": "Assume excluded middle and dependent choice. If $p$ is lock free, $\\mathsf{erase}\\,q_0 = p$, $q_0 \\to^{*} q$ and thread $t$ is pending in $q$, then there are $q_1$ and a step $q_1 \\to q_2$ with event $ev$ such that $q \\to^{*} q_1$ and $t \\in \\mathsf{parts}(ev)$.",
   "why": "It is the reachability form of lock freedom, stated per thread. A maximal weakly fair run from $q$, prefixed with the steps from $q_0$, is a run from $p$, and lock freedom of that run makes $t$ take part in a later step.",
   "breaks": "Nothing. It is a definition.",
   "example": "Every lock-free example.",
   "rocq": "lockfree/FairRun.v: lock_free_padovani; soup/LFTyped.v: lf_soundness_padovani",
   "sig": "\\mathsf{EM} \\land \\mathsf{DC} \\land \\mathsf{lock\\_free}\\,p \\land \\mathsf{erase}\\,q_0 = p \\land q_0 \\to^{*} q \\land \\mathsf{pend}(q, t) \\Rightarrow \\exists q_1\\,ev\\,q_2.\\ q \\to^{*} q_1 \\xrightarrow{ev} q_2 \\land t \\in \\mathsf{parts}(ev)",
   "args": [
    {
     "name": "\\mathsf{EM}",
     "meaning": "excluded middle, $P \\lor \\lnot P$ for every proposition $P$, a hypothesis and no axiom"
    },
    {
     "name": "\\mathsf{DC}",
     "meaning": "dependent choice, a total relation on a type has an infinite chain from every element, a hypothesis and no axiom"
    },
    {
     "name": "p",
     "meaning": "a closed process $(C, E)$"
    },
    {
     "name": "t",
     "meaning": "a thread pending in the reachable configuration $q$"
    }
   ]
  },
  "th.conservative": {
   "title": "Conservativity",
   "what": "The annotated typing judgment at $N = \\infty$ derives some $T_{df}\\ !\\ \\varepsilon$ iff the deadlock-free judgment derives $T_{df}$, at erased contexts.",
   "why": "Deadlock-free typing is the annotated typing judgment with credits, costs and tickets ignored, so one set of rules serves both.",
   "breaks": "Nothing. It is a definition.",
   "example": "The client and server main.",
   "rocq": "static/Conservativity.v: conservative",
   "sig": "(\\exists \\varepsilon.\\ \\ldots \\vdash^{F}_{W\\annot{,\\infty}} e : T_{df}\\ !\\ \\varepsilon) \\iff \\ldots \\vdash^{F}_{W} e : T_{df}",
   "args": [
    {
     "name": "\\varepsilon",
     "meaning": "some cost"
    },
    {
     "name": "e",
     "meaning": "the term"
    }
   ]
  },
  "th.typed-dftyped": {
   "title": "Erasure to deadlock-free typing",
   "what": "For every $N$, erasing the annotations of an annotated derivation gives a deadlock-free derivation.",
   "why": "Hence every lock-free typing is also a deadlock-free typing.",
   "breaks": "Nothing. It is a definition.",
   "example": "The cycle at $N = 2$ erases to its deadlock-free typing.",
   "rocq": "static/Conservativity.v: typed_dftyped",
   "sig": "\\Gamma ; \\Delta \\vdash^{F}_{W\\annot{,N}} e : T\\ !\\ \\varepsilon \\Rightarrow \\Gamma ; \\Delta_{df} \\vdash^{F}_{W} e : T_{df}",
   "args": [
    {
     "name": "N",
     "meaning": "any bound on tickets"
    }
   ]
  },
  "th.cost-fundamental": {
   "title": "Cost fundamental theorem",
   "what": "The annotated typing judgment implies the semantic cost judgment $\\Delta \\vDash^{N} e : T\\ !\\ \\varepsilon$.",
   "why": "It is the cost half of the annotated typing judgment, proved rule by rule.",
   "breaks": "Nothing. It is a definition.",
   "example": "The forwarder $\\mathsf{fw}$.",
   "rocq": "cost/CostFund.v: cost_fundamental",
   "sig": "\\Gamma ; \\Delta \\vdash^{F}_{W\\annot{,N}} e : T\\ !\\ \\varepsilon \\Rightarrow \\Delta \\vDash^{N} e : T\\ !\\ \\varepsilon",
   "args": [
    {
     "name": "N",
     "meaning": "the bound on the tickets of a channel"
    },
    {
     "name": "e",
     "meaning": "the term"
    }
   ]
  },
  "th.fsem-of-cost": {
   "title": "Fuel from cost typing",
   "what": "If $\\varnothing ; \\Delta \\vdash^{\\varnothing}_{W\\annot{,N}} e : T\\ !\\ c$, $\\mathsf{tfree}\\,T$ and $\\mathsf{cr}(\\Delta) \\leq N$, then $\\mathsf{fsem}\\,N\\,\\Delta\\annot{^{N}}\\,e$.",
   "why": "P-Term gives every end credit equal to its tickets, so the cost judgment yields the per-thread fuel that lock freedom needs.",
   "breaks": "If a closure could mention an end it does not own, the forwarder could receive a closure that owns nothing and would have no fuel after spawning the closure.",
   "example": "The forwarder $\\mathsf{fw}$.",
   "rocq": "cost/CostFund.v: fsem_of_cost",
   "sig": "\\varnothing ; \\Delta \\vdash^{\\varnothing}_{W\\annot{,N}} e : T\\ !\\ c \\land \\mathsf{tfree}\\,T \\land \\mathsf{cr}(\\Delta) \\leq N \\Rightarrow \\mathsf{fsem}\\,N\\,\\Delta\\annot{^{N}}\\,e",
   "args": [
    {
     "name": "\\Delta",
     "meaning": "the ends of the thread with their credits and tickets"
    }
   ]
  },
  "th.crle": {
   "title": "$\\mathsf{cr}(\\Delta) \\leq N$",
   "what": "Every credit in $\\Delta$ is at most the bound $N$, that is $a \\leq N$ for every entry $(S@x)\\annot{^{a}}_{m}$ or $(T \\multimap U)\\annot{^{a}}$ of $\\Delta$.",
   "why": "A thread starts with every counter at its tickets, which are at most $N$, so its credits may guarantee no more than $N$.",
   "breaks": "A credit above $N$ would allow more postponement than a fresh counter allows.",
   "example": "$\\mathsf{cr}(\\{o \\mapsto (S@x)^{2}_{3}\\}) \\leq 4$.",
   "rocq": "cost/CostFund.v: fsem_of_cost",
   "sig": "\\mathsf{cr} : \\mathsf{TEnv} \\to \\mathbb{N} \\cup \\{\\infty\\}",
   "args": [
    {
     "name": "\\Delta",
     "meaning": "a context"
    },
    {
     "name": "N",
     "meaning": "the bound on the tickets of a channel"
    }
   ]
  },
  "th.Prel": {
   "title": "The process relation $P$",
   "what": "$P[\\kappa]^{W}_{\\alpha}\\llbracket\\Sigma \\vdash T\\rrbracket$, the processes in the relation at table $\\kappa$, world $W$, level $n$, interface $\\Sigma$ and result $T$.",
   "why": "The semantic process judgment asks membership at every level $n$.",
   "breaks": "Nothing. It is a definition.",
   "example": "Two threads closing $c^{+}$ and $c^{-}$ lie in $P^{W}_{\\alpha}\\llbracket\\varnothing \\vdash \\ast\\rrbracket$ for every $n$.",
   "rocq": "relation/Relation.v: Prel",
   "sig": "P[\\kappa]^{W}_{\\alpha}\\llbracket\\Sigma \\vdash T\\rrbracket \\subseteq \\mathsf{Proc}",
   "args": [
    {
     "name": "\\kappa",
     "meaning": "a cost table, $\\kappa_{DF}$ for deadlock freedom and $\\kappa_L$ for liveness"
    },
    {
     "name": "W",
     "meaning": "a static world, the semantic judgments read the relation at the ranked worlds that satisfy $W$"
    },
    {
     "name": "\\alpha",
     "meaning": "the level, an ordinal"
    },
    {
     "name": "\\Sigma",
     "meaning": "the interface of the process"
    },
    {
     "name": "T",
     "meaning": "the result type of the main thread"
    }
   ]
  },
  "th.Erel": {
   "title": "The term relation $E$",
   "what": "$E[\\kappa]^{W}_{\\alpha}\\llbracket\\Theta \\vdash T\\rrbracket^{F}$ is the set of terms in the relation at cost table $\\kappa$, world $W$ and level $n$, for ends $\\Theta$, result $T$ and future $F$.",
   "why": "The semantic term judgment asks membership at each level and for each grounding of the variables.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{close}\\,c^{+} \\in E^{W}_{\\alpha}\\llbracket\\{c^{+} \\mapsto \\mathsf{Close}@x\\} \\vdash \\ast\\rrbracket^{\\varnothing}$.",
   "rocq": "relation/Relation.v: Erel",
   "sig": "E[\\kappa]^{W}_{\\alpha}\\llbracket\\Theta \\vdash T\\rrbracket^{F} \\subseteq \\mathsf{Expr}",
   "args": [
    {
     "name": "\\kappa",
     "meaning": "a cost table, $\\kappa_{DF}$ for deadlock freedom and $\\kappa_L$ for liveness"
    },
    {
     "name": "W",
     "meaning": "a static world, the semantic judgments read the relation at the ranked worlds that satisfy $W$"
    },
    {
     "name": "\\alpha",
     "meaning": "the level, an ordinal"
    },
    {
     "name": "\\Theta",
     "meaning": "the ends held by the term"
    },
    {
     "name": "T",
     "meaning": "the result type"
    },
    {
     "name": "F",
     "meaning": "the future"
    }
   ]
  },
  "th.Vrel": {
   "title": "The value relation $V$",
   "what": "$V^{W}_{\\beta}\\llbracket\\Theta \\vdash T\\rrbracket$ is the set of values in the relation at world $W$ and level $j$, for ends $\\Theta$ and type $T$.",
   "why": "A term in $E$ that is irreducible is a value in $V$.",
   "breaks": "Nothing. It is a definition.",
   "example": "$c^{+} \\in V^{W}_{\\beta}\\llbracket\\{c^{+} \\mapsto \\mathsf{Close}@x\\} \\vdash \\mathsf{Close}@x\\rrbracket$.",
   "rocq": "relation/Relation.v: Vrel",
   "sig": "V^{W}_{\\beta}\\llbracket\\Theta \\vdash T\\rrbracket \\subseteq \\mathsf{Val}",
   "args": [
    {
     "name": "W",
     "meaning": "a static world, the semantic judgments read the relation at the ranked worlds that satisfy $W$"
    },
    {
     "name": "\\beta",
     "meaning": "the level"
    },
    {
     "name": "\\Theta",
     "meaning": "the ends held by the term"
    },
    {
     "name": "T",
     "meaning": "the type"
    }
   ]
  },
  "th.soup": {
   "title": "The lock-free process relation $S^{N,W}_{\\alpha}$",
   "what": "$a \\in S^{N,W}_{\\alpha}\\llbracket\\Sigma \\vdash T\\rrbracket$ holds of an annotated configuration $a$ when each thread of $a$ is in the relation at $\\kappa_L$ and has fuel at the ordinal index $\\alpha$. Ownership, points, counters and tickets are those that $a$ records.",
   "why": "The lock-free judgment chooses $a$ at each index, and the existential property gives one $a$ for every index.",
   "breaks": "Nothing. It is a definition.",
   "example": "The state of two threads closing $c^{+}$ and $c^{-}$.",
   "rocq": "soup/Soup.v: Soup, lf_sem; soup/SoupRun.v: lfsoup_step, lfsoup_step_all, lfsoup_run",
   "sig": "S^{N,W}_{\\alpha}\\llbracket\\Sigma \\vdash T\\rrbracket \\subseteq \\mathsf{LFState}",
   "args": [
    {
     "name": "N",
     "meaning": "the bound on the tickets of a channel, a natural number for lock freedom"
    },
    {
     "name": "W",
     "meaning": "a static world, the semantic judgments read the relation at the ranked worlds that satisfy $W$"
    },
    {
     "name": "\\alpha",
     "meaning": "the ordinal index"
    },
    {
     "name": "\\Sigma",
     "meaning": "the interface of the process"
    },
    {
     "name": "T",
     "meaning": "the result type of the main thread"
    }
   ]
  },
  "th.qa": {
   "title": "$q_a$",
   "what": "The configuration of the annotated configuration $a$.",
   "why": "An annotated configuration is a configuration together with ownership, counters and tickets.",
   "breaks": "Nothing. It is a definition.",
   "example": "$q_a = (C, M)$.",
   "rocq": "soup/State.v: s_q",
   "sig": "q_a : \\mathsf{Config}",
   "args": [
    {
     "name": "a",
     "meaning": "an annotated configuration"
    }
   ]
  },
  "th.em": {
   "title": "Excluded middle $\\mathsf{EM}$",
   "what": "Each proposition holds or fails, $\\forall P.\\ P \\lor \\neg P$, as an explicit hypothesis.",
   "why": "The existential property of ordinal indices, $\\forall \\alpha.\\ \\exists a$ to $\\exists a.\\ \\forall \\alpha$, is proved by contradiction.",
   "breaks": "Without it the creation choice cannot be fixed once along a run, and the lock-free judgment needs the choice $\\chi$ before the index again.",
   "example": "Transfinite Iris assumes it in its model.",
   "rocq": "lockfree/FairRun.v: excluded_middle; relation/ExProp.v: exist_prop",
   "sig": "\\mathsf{EM} := \\forall P : \\mathsf{Prop}.\\ P \\lor \\neg P",
   "args": [
    {
     "name": "P",
     "meaning": "a proposition"
    }
   ]
  },
  "th.ac": {
   "title": "Choice $\\mathsf{AC}$",
   "what": "A total relation contains a function, as an explicit hypothesis.",
   "why": "The existential property picks one failing index per witness, and the run picks one choice of tickets per state and position, from which a recursion builds the states of the run.",
   "breaks": "Without it the states chosen per index do not form one sequence along the run.",
   "example": "One choice of tickets per position of a run of the lock-free process relation.",
   "rocq": "lockfree/FairRun.v: functional_choice; relation/ExProp.v: exist_prop; soup/SoupRun.v: lfsoup_run",
   "sig": "\\mathsf{AC} := \\forall R : X \\to Y \\to \\mathsf{Prop}.\\ (\\forall x.\\ \\exists y.\\ R\\,x\\,y) \\Rightarrow \\exists f.\\ \\forall x.\\ R\\,x\\,(f\\,x)",
   "args": [
    {
     "name": "R",
     "meaning": "a total relation"
    },
    {
     "name": "f",
     "meaning": "a choice function"
    },
    {
     "name": "X, Y",
     "meaning": "two types"
    }
   ]
  },
  "th.conn": {
   "title": "$\\mathsf{conn}$",
   "what": "The side conditions of P-Connect, with $\\Sigma_D$ the partners of $\\Sigma_C$ dual up to $\\approx$ at dual points.",
   "why": "They make the composite a process in which every channel belongs to one side.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\Sigma_C = \\{c^{+} \\mapsto \\mathsf{Close}@x\\}$ and $\\Sigma_D = \\{c^{-} \\mapsto \\mathsf{Close}@\\overline{x}\\}$.",
   "rocq": "compat/Connect.v: conn, cut_dual",
   "sig": "\\mathsf{conn}\\,\\Sigma_1\\,\\Sigma_C\\,C_1\\,\\Sigma_2\\,\\Sigma_D\\,C_2",
   "args": [
    {
     "name": "\\Sigma_1, \\Sigma_2",
     "meaning": "the outer interfaces"
    },
    {
     "name": "\\Sigma_C, \\Sigma_D",
     "meaning": "the cut and its partners"
    },
    {
     "name": "C_1, C_2",
     "meaning": "the restricted channels of the two sides"
    }
   ]
  },
  "th.par": {
   "title": "$p_1 \\parallel_{\\Sigma_C} p_2$",
   "what": "The composite $(C_1 \\cup C_2 \\cup \\mathsf{chans}\\,\\Sigma_C, E_1 \\uplus E_2)$ of $p_1 = (C_1, E_1)$ and $p_2 = (C_2, E_2)$.",
   "why": "After composition the two sides communicate on the cut, which no outside process holds.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\mathsf{close}\\,c^{+} \\parallel \\mathsf{close}\\,c^{-}$ restricts $c$.",
   "rocq": "compat/Connect.v: pconn",
   "sig": "p_1 \\parallel_{\\Sigma_C} p_2 = (C_1 \\cup C_2 \\cup \\mathsf{chans}\\,\\Sigma_C, E_1 \\uplus E_2)",
   "args": [
    {
     "name": "p_i = (C_i, E_i)",
     "meaning": "the two components"
    },
    {
     "name": "\\Sigma_C",
     "meaning": "the cut"
    }
   ]
  },
  "th.df": {
   "title": "Erasure $X_{df}$",
   "what": "$\\Delta_{df}$ and $T_{df}$ drop every credit, ticket and cost and keep session types, points and facts.",
   "why": "Deadlock-free typing and the relations read no annotation.",
   "breaks": "Nothing. It is a definition.",
   "example": "$(S@x)^{3}$ erases to $S@x$.",
   "rocq": "types/Types.v: ty_df, static/Contexts.v: tenv_df, lenv_df",
   "sig": "X \\mapsto X_{df}",
   "args": [
    {
     "name": "X",
     "meaning": "an end environment, a variable context or a type"
    }
   ]
  },
  "th.styof": {
   "title": "$\\Delta\\annot{^{N}}$",
   "what": "The held ends of $\\Delta$ for fuel, each counter at its tickets. An entry $o \\mapsto (S@x)\\annot{^{a}}_{m}$ of $\\Delta$ becomes $o \\mapsto S^{m}_{m}$.",
   "why": "Fuel reads protocols, counters and tickets and ignores points and credits. A thread starts with each counter at its tickets.",
   "breaks": "Nothing. It is a definition.",
   "example": "$\\{a \\mapsto (S@x)^{2}_{3}\\}\\annot{^{N}} = \\{a \\mapsto S^{3}_{3}\\}$.",
   "rocq": "cost/CostFund.v: fsem_of_cost",
   "sig": "\\Delta\\annot{^{N}} : \\mathsf{End} \\rightharpoonup \\mathsf{STy} \\times \\mathbb{N} \\times \\mathbb{N}",
   "args": [
    {
     "name": "\\Delta",
     "meaning": "the linear context of ends and variables"
    }
   ]
  },
  "th.tpr": {
   "title": "$\\mathsf{thread\\_progress\\_run}$",
   "what": "For a run $(r, l)$, $\\mathsf{thread\\_progress\\_run}\\,(r, l)$ holds iff each thread $t$ of each position $i$ later stops or acts. That is, some $j \\geq i$ exists at which $t$ is a value in $r\\,j$ or takes part in the step $l\\,j$ by a session action.",
   "why": "It states lock freedom per run for each thread, including the threads that are not pending. A thread that is neither stopped nor acting forever would be postponed without end.",
   "breaks": "Nothing. It is a definition.",
   "example": "In a run of two threads closing $c^{+}$ and $c^{-}$, both threads take part in the close step.",
   "rocq": "lockfree/ThreadProgress.v: thread_progress_run",
   "sig": "\\mathsf{thread\\_progress\\_run} : (\\mathbb{N} \\to \\mathsf{Config}) \\to (\\mathbb{N} \\to \\mathsf{Event}_{\\bot}) \\to \\mathsf{Prop}",
   "args": [
    {
     "name": "(r, l)",
     "meaning": "a run, $r\\,i$ the configuration and $l\\,i$ the event at position $i$"
    },
    {
     "name": "i, j",
     "meaning": "positions with $i \\leq j$"
    },
    {
     "name": "t",
     "meaning": "a thread identifier"
    }
   ]
  }
 },
 "examples": [
  {
   "id": "ex-cs",
   "title": "Client and server cycle",
   "modes": [
    "df",
    "lf"
   ],
   "code": "main = let ⟨a, a′⟩ = new in                    -- a at ρ\n       let ⟨b, b′⟩ = new in                    -- b at ρ·0, facts C at (ρ, ρ·0, ρ·1)\n       let ∗ = spawn (λu. let ∗ = u in (force srv) ⟨a′, b′⟩) in\n       (force cli) ⟨a, b⟩\ncli  = !(f = λp. let ⟨a, b⟩ = p in let a = send ⟨∗, a⟩ in\n                let ⟨u, b⟩ = recv b in let ∗ = u in (force f) ⟨a, b⟩)\nsrv  = !(g = λp. let ⟨a, b⟩ = p in let ⟨u, a⟩ = recv a in let ∗ = u in\n                let b = send ⟨∗, b⟩ in (force g) ⟨a, b⟩)\n-- both boxes : □∀ι κ ζ. C. ∗ ⊸ (S1@ι ⊗ S2@κ ⊸^ζ ∗)\n-- C = {ι+k ≺ (κ+k)‾, κ+k ≺ (ι+k+1)‾, ι+k ≺ ζ, κ+k ≺ ζ | k}",
   "shows": "A client sends on $a$ and then receives on $b$, and a server receives on $a$ and then sends on $b$, both forever. The second $\\mathsf{new}$ places $b$ at the field $\\rho\\cdot 0$ of the root of $a$ and states the facts $C$ at $(\\rho, \\rho\\cdot 0, \\rho\\cdot 1)$. Each recursive call is at the next points $(\\iota^{+}, \\kappa^{+}, \\zeta)$, where $C$ states the same facts again.",
   "rocq": "examples/ClientServer.v: cs_typed; examples/LFClientServer.v: cs_lftyped, cs_lock_free",
   "accepts": {
    "df": {
     "ok": true,
     "rocq": "cs_dftyped, cs_typed"
    },
    "live": {
     "ok": true,
     "rocq": "cs_dftyped, cs_guarded"
    },
    "lf": {
     "ok": true,
     "N": 3,
     "rocq": "cs_lftyped, cs_lock_free"
    }
   },
   "lead": "Two loops that call themselves forever over the same two channels are deadlock free, because one constraint orders the points of all their rounds at once."
  },
  {
   "id": "ex-cycle",
   "title": "Cycle",
   "modes": [
    "df",
    "lf"
   ],
   "code": "cycle = let ⟨c, c′⟩ = new in          -- c at ρ\n        let ⟨d, d′⟩ = new in          -- d at ρ·0, C = {ρ ≺ (ρ·0)‾, ρ‾ ≺ ρ·0}\n        let ∗ = spawn (λu. let ∗ = u in let ∗ = close c′ in close d′) in\n        let ∗ = close c in close d",
   "shows": "Main closes $c$ and then $d$, and the spawned thread closes $c'$ and then $d'$. Each thread waits on one channel while it holds an end of the other. The second $\\mathsf{new}$ states exactly the two facts this requires, $\\rho \\prec \\overline{\\rho\\cdot 0}$ for main and $\\overline{\\rho} \\prec \\rho\\cdot 0$ for the spawned thread.",
   "rocq": "examples/Cycle.v: cy_typed; examples/LFCycle.v: cy_lftyped, cy_lock_free",
   "accepts": {
    "df": {
     "ok": true,
     "rocq": "cy_dftyped, cy_typed"
    },
    "live": {
     "ok": true,
     "rocq": "cy_dftyped, cy_guarded"
    },
    "lf": {
     "ok": true,
     "N": 2,
     "rocq": "cy_lftyped, cy_lock_free"
    }
   },
   "lead": "Two threads that use two channels in the same order type, because creating the second channel states the two order facts the threads need."
  },
  {
   "id": "ex-between",
   "title": "A channel between two box arguments",
   "modes": [
    "df",
    "lf"
   ],
   "code": "between : □(∀ι κ. C. ∗ ⊸ Close@ι ⊗ Close@κ ⊸^κ ∗)\nbetween = !(f = λp. let ⟨c, e⟩ = p in\n                    let ⟨d, d′⟩ = new in        -- d at ι·0\n                    let ∗ = spawn (λu. let ∗ = u in close d′) in\n                    let ∗ = close c in let ∗ = close d in close e)\n-- C = {ι ≺ κ, ι ≺ κ‾, ι ≺ δ‾, δ ≺ κ, δ ≺ κ‾},  δ = ι·0\nmain: c by new at ρ, e by new at ρ·1, force between at (ρ, ρ·1)",
   "shows": "The box creates a channel $d$ while it holds two arguments $c$ and $e$, and closes $c$, $d$ and $e$ in this order. E-New places $d$ at the field $\\iota\\cdot 0$ of the point of $c$. The facts of the box constraint then order $d$ between $c$ and $e$, and no point between two box points is needed.",
   "rocq": "examples/FreshBetween.v: fb_typed; examples/LFFreshBetween.v: fb_lftyped, fb_lock_free",
   "accepts": {
    "df": {
     "ok": true,
     "rocq": "fb_dftyped, fb_typed"
    },
    "live": {
     "ok": true,
     "rocq": "fb_dftyped, fb_guarded"
    },
    "lf": {
     "ok": true,
     "N": 2,
     "rocq": "fb_lftyped, fb_lock_free"
    }
   },
   "lead": "A procedure can create a channel whose point lies between the points of two channels it receives as arguments."
  },
  {
   "id": "ex-many",
   "title": "A channel that acts several times",
   "modes": [
    "df",
    "lf"
   ],
   "code": "many = !(f = λp. let ⟨c, e⟩ = p in\n                 let ⟨d, d′⟩ = new in         -- d at δ\n                 let ∗ = spawn (λu. let ∗ = u in\n                                     let ⟨v, d′⟩ = recv d′ in let ∗ = v in\n                                     let ⟨w, d′⟩ = recv d′ in let ∗ = w in close d′) in\n                 let ∗ = close c in\n                 let ∗ = close (send ⟨∗, send ⟨∗, d⟩⟩) in close e)\n-- C = {ι ≺ κ, ι ≺ κ‾, ι ≺ δ‾} ∪ {δ+k ≺ κ, δ+k ≺ κ‾ | k},  δ = ι·0",
   "shows": "The new end $d$ sends twice and closes while the box holds $e$. The constraint of the box is infinite, one pair of facts for each offset of $\\delta$, so $d$ may act at $\\delta$, $\\delta^{+}$ and $\\delta^{++}$ below the point $\\kappa$ of $e$.",
   "rocq": "examples/FreshMany.v: fm_typed; examples/LFFreshMany.v: fm_lftyped, fm_lock_free",
   "accepts": {
    "df": {
     "ok": true,
     "rocq": "fm_dftyped, fm_typed"
    },
    "live": {
     "ok": true,
     "rocq": "fm_dftyped, fm_guarded"
    },
    "lf": {
     "ok": true,
     "N": 4,
     "rocq": "fm_lftyped, fm_lock_free"
    }
   },
   "lead": "A new channel can act several times while an older end is held, because a box constraint may state infinitely many facts."
  },
  {
   "id": "ex-factory",
   "title": "The factory",
   "modes": [
    "df",
    "lf"
   ],
   "code": "mk₀  = !(f = λu. let ∗ = u in let ⟨c, c′⟩ = new in\n                let ∗ = spawn (λv. let ∗ = v in close (send ⟨∗, c⟩)) in c′)\nmk₁  = !(f = λp. let ⟨c, c′⟩ = new in\n                let ∗ = spawn (λv. let ∗ = v in close (send ⟨∗, c⟩)) in ⟨p, c′⟩)\nmain = let p = (force mk₀) ∗ in let ⟨p, q⟩ = (force mk₁) p in\n       let ∗ = recvclose p in recvclose q\n-- mk₀ places c at a fresh ρ with C(ρ) = {ρ‾ ≺ ρ·0, ρ‾⁺ ≺ ρ·0}, mk₁ at ι·0 for p at ι\n-- mk₀ : □(∗ ⊸ ∃^⊥ ι. C(ι). (?∗.Close)@ι‾)",
   "shows": "Each box creates a channel, spawns a sender on one end and returns the other end. $\\mathsf{mk}_0$ places the channel at a fresh root and returns it packed in an existential. $\\mathsf{mk}_1$ places it at a field of the end it receives. The two boxes type one creation in the two ways E-New allows.",
   "rocq": "examples/FactoryEx.v: fx_typed; examples/LFFactoryEx.v: fx_lftyped, fx_lock_free",
   "accepts": {
    "df": {
     "ok": true,
     "rocq": "fx_dftyped, fx_typed"
    },
    "live": {
     "ok": true,
     "rocq": "fx_dftyped, fx_guarded"
    },
    "lf": {
     "ok": true,
     "N": 2,
     "rocq": "fx_lftyped, fx_lock_free"
    }
   },
   "lead": "One way of creating a channel admits two typings, at a fresh root hidden in an existential or at a field of an end the creator holds."
  },
  {
   "id": "ex-ring",
   "title": "The growing ring",
   "modes": [
    "df",
    "lf"
   ],
   "code": "Sch  = µα. ?(κ. α@κ).Close\nring : □(∀ι₁ ι₂. Cr. ∗ ⊸ (Sch@ι₁ ⊗ S̄ch@ι₂ ⊸^{ι₁+1} ∗))\nring = !(f = λp. let ⟨x, y⟩ = p in\n           let ⟨a, a′⟩ = new in                -- a at ι₂·0\n           let ∗ = spawn (λw. let ∗ = w in close (send ⟨a, y⟩)) in\n           let ⟨b, b′⟩ = new in                -- b at ι₁·1\n           let ⟨z, x⟩ = recv x in let ∗ = close x in\n           let ∗ = spawn (λw. let ∗ = w in (force f) ⟨z, b′⟩) in\n           spawn (λw. let ∗ = w in (force f) ⟨b, a′⟩))\nmain = let ⟨e, e′⟩ = new in (force ring) ⟨e, e′⟩",
   "shows": "Each round of the ring receives an end $z$ on $x$, spawns two copies of itself, and so the ring grows forever. E-New places $b$ at $\\iota_1\\cdot 1$ while $x$ is held at $\\iota_1$, before the receive on $x$. The ring is lock free, with lock-free typing at $N = 4$.",
   "rocq": "examples/GrowRing.v: rg_typed; examples/LFGrowRing.v: rg_lftyped, rg_lock_free",
   "accepts": {
    "df": {
     "ok": true,
     "rocq": "rg_dftyped, rg_typed"
    },
    "live": {
     "ok": true,
     "rocq": "rg_dftyped, rg_guarded"
    },
    "lf": {
     "ok": true,
     "N": 4,
     "rocq": "rg_lftyped, rg_lock_free"
    }
   },
   "lead": "A ring of threads that grows forever is lock free."
  },
  {
   "id": "ex-close",
   "title": "Two threads closing one channel",
   "modes": [
    "lf"
   ],
   "code": "cl c⁺ ∥ cl c⁻,   cl o = close o\n-- each thread by P-Term at every finite N over its end, cut c by P-Connect at exactly dual types",
   "shows": "Two threads each close one end of $c$. P-Term types each thread over its end, and P-Connect cuts $c$ at dual types in a world without facts. It is the smallest use of the two process rules.",
   "rocq": "examples/LFClose.v: cl_lftyped, cl_lock_free",
   "accepts": {
    "lf": {
     "ok": true,
     "N": "every",
     "rocq": "cl_lftyped, cl_lock_free"
    }
   },
   "lead": "The smallest process built from two typed threads by the process rules."
  },
  {
   "id": "ex-guard-neg",
   "title": "Guard rejections",
   "modes": [
    "lf"
   ],
   "code": "div_box     = !(f = force f)                         -- loops on β steps\npn_fix      = !(f = λx. (force f) x)                  -- fix λx.x\ncx_box      = !(f = let ∗ = (force f) ∗ in λy. y)     -- recurses before returning\nspawn_loop  = !(f = λc. spawn (λ_. (force f) c))      -- spawns forever",
   "shows": "Each box uses its own variable before its first session action. The first loops on $\\beta$ steps, the second is $\\mathsf{fix}\\,\\lambda x.\\,x$, the third recurses before it returns, and the fourth spawns forever. The guard rejects all four, so they are outside lock-free typing.",
   "rocq": "examples/GuardEx.v: div_not_guarded, pn_fix_not_guarded, cx_not_guarded, spawn_loop_not_guarded",
   "accepts": {
    "live": {
     "ok": false,
     "part": "guard",
     "rocq": "div_not_guarded, pn_fix_not_guarded, cx_not_guarded, spawn_loop_not_guarded"
    },
    "lf": {
     "ok": false,
     "part": "guard",
     "rocq": "div_not_guarded, pn_fix_not_guarded, cx_not_guarded, spawn_loop_not_guarded"
    }
   },
   "lead": "Recursion that can run forever without a session action is outside lock-free typing."
  },
  {
   "id": "ex-guard-pos",
   "title": "Guard acceptances",
   "modes": [
    "lf"
   ],
   "code": "loop  = !(f = λx. let ⟨v, x′⟩ = recv x in (force f) x′)\nstage = !(f = λin. let ⟨v, in⟩ = recv in in let ∗ = close in in\n                  let ⟨a, b⟩ = new in let ∗ = spawn (λ_. (force f) b) in\n                  close (send ⟨v, a⟩))                  -- a pipeline stage",
   "shows": "In both boxes a $\\mathsf{recv}$ comes before the recursive call. A receive is a session action, so the guard checks the rest of the body under $\\varnothing$, where the variable of the box is usable again.",
   "rocq": "examples/GuardEx.v: loop_guarded, stage_guarded",
   "accepts": {
    "live": {
     "ok": true,
     "part": "guard",
     "rocq": "loop_guarded, stage_guarded"
    },
    "lf": {
     "ok": true,
     "part": "guard",
     "rocq": "loop_guarded, stage_guarded"
    }
   },
   "lead": "Recursion that performs a session action before each recursive call passes the guard."
  },
  {
   "id": "ex-forwarder",
   "title": "The spawn forwarder",
   "modes": [
    "lf"
   ],
   "code": "fw o = let ⟨w, c⟩ = recv o in let ∗ = close c in spawn w\no : ?((∗ ⊸ ∗)^2).Close\ndead_thunk q = λ_. let ∗ = Ω in close q",
   "shows": "The forwarder receives a closure on $o$ and spawns the closure as a new thread. $\\mathsf{dead\\_thunk}\\,q$ mentions the end $q$ without owning it, so it is not a value in $FV$ and cannot arrive on $o$. Each closure the forwarder receives therefore owns its ends, and $\\mathsf{fw}$ has fuel at each counter bound.",
   "rocq": "cost/Forwarder.v: dead_thunk_rejected, fw_ptyped; cost/CostFund.v: fw_fsem",
   "accepts": {
    "lf": {
     "ok": true,
     "N": "every",
     "part": "typing and fuel",
     "rocq": "fw_ptyped, fw_fsem, dead_thunk_rejected"
    }
   },
   "lead": "A thread that receives closures and spawns them is lock free, because a received closure owns the ends it mentions."
  },
  {
   "id": "ex-controller",
   "title": "The controller",
   "modes": [
    "lf"
   ],
   "code": "main = let ⟨a, a′⟩ = new in let ⟨b, b′⟩ = new in   -- a at ρ, b at ρ·0\n       let ⟨c, c′⟩ = new in                              -- c at ρ·2\n       let ∗ = spawn (λu. let ∗ = u in (force srv) ⟨⟨a′, b′⟩, c′⟩) in\n       (force cli) ⟨⟨a, b⟩, c⟩\ncli  = !(f = λp. let ⟨q, k⟩ = p in let ⟨a, b⟩ = q in\n                let a = send ⟨∗, a⟩ in let ⟨u, b⟩ = recv b in\n                let ∗ = u in (force f) ⟨⟨a, b⟩, k⟩)\n-- c sits at Skip on each side, an idle end",
   "shows": "The client sends on $a$ and receives on $b$ in each round, and holds the end $k$ at $\\mathsf{Skip}@\\chi$ throughout. Aging requires $c \\leq a$ only of ends that are not idle. The idle end $k$ therefore has credit $0$ across rounds of unbounded cost.",
   "rocq": "examples/LFController.v: ctl_typedN, ctl_guarded, ctl_lftyped, ctl_lock_free",
   "accepts": {
    "lf": {
     "ok": true,
     "N": 3,
     "rocq": "ctl_lftyped"
    }
   },
   "lead": "An end that no thread ever acts on may be held across a loop of unbounded length."
  },
  {
   "id": "ex-flag",
   "title": "Self-computed flag",
   "modes": [
    "df",
    "lf"
   ],
   "code": "not     = λz. case z of inl w ⇒ inj₂ w | inr w ⇒ inj₁ w\nthread  = case not (inj₂ ∗) of\n            inl w ⇒ let ∗ = w in let ∗ = close c in close d      -- runs\n          | inr w ⇒ let ∗ = w in let ∗ = close d in close c      -- never runs\npartner = let ∗ = close c̄ in close d̄\n-- the process ({c, d}, {thread, partner}), c at x, d at y",
   "rocq": "examples/SemBranch.v: sbv_thread_E, sbv_deadlock_free, sbv_rejected, Tbad_not_cons",
   "accepts": {
    "df": {
     "ok": false,
     "part": "P-Connect",
     "rocq": "sbv_rejected, for every world and every bound. E-Open asks cons, so the dead arm needs y ≺ x̄ from its own world, and the joined world has the cycle y ≺ x̄ ≺ y"
    },
    "sem": {
     "ok": true,
     "rocq": "sbv_thread_E and sbv_deadlock_free"
    }
   },
   "shows": "The flag is always $\\mathsf{inj}_1\\,\\ast$, so the thread closes $c$ before $d$. E-Case types both arms in one world. The live arm asks $x \\prec \\overline{y}$ and the partner asks $\\overline{x} \\prec y$. The dead arm asks $y \\prec \\overline{x}$. E-Open adds no fact between points of the old context, so no binder type supplies that fact, and the world of the thread must hold $y \\prec \\overline{x}$. The joined world has the cycle $y \\prec \\overline{x} \\prec y$, and P-Connect asks a strict join. The relation reads only the steps the thread takes. After the $\\beta$ steps the thread is in the live arm, which the fundamental theorem places in $E$ in a world with $x \\prec \\overline{y}$ alone. Semantic P-Connect joins it with the partner, and adequacy gives deadlock freedom.",
   "lead": "Only semantic typing shows that a thread branching on a flag it computes itself is deadlock free. Static typing checks the arm that never runs, and that arm closes the two channels in the other order."
  },
  {
   "id": "ex-flagpair",
   "title": "Two threads on one received flag",
   "modes": [
    "df",
    "lf"
   ],
   "code": "A = case z of inl _ ⇒ let ∗ = close a in close b\n             | inr _ ⇒ let ∗ = close b in close a\nB = case z of inl _ ⇒ let ∗ = close ā in close b̄\n             | inr _ ⇒ let ∗ = close b̄ in close ā\n-- a at x, b at y, both threads receive the same flag z",
   "rocq": "examples/FlagPair.v: fp_gate, fp_unrealizable",
   "accepts": {
    "df": {
     "ok": false,
     "part": "P-Connect"
    },
    "sem": {
     "ok": true,
     "part": "the whole process, by its reductions",
     "rocq": "argued, no Rocq proof. Thread by thread it fails: fp_unrealizable"
    }
   },
   "shows": "Both threads get the same flag, so they close $a$ and $b$ in the same order in every run. A received flag is any value of $V$ at $\\ast \\oplus \\ast$, so each thread has to be in $E$ for both flags. With $\\mathsf{inl}$ thread A closes $a$ while it holds $b$ and asks $x \\prec \\overline{y}$. With $\\mathsf{inr}$ thread B closes $\\overline{b}$ while it holds $\\overline{a}$ and asks $\\overline{y} \\prec x$. The join of the two worlds then has a cycle, and P-Connect asks a well-founded join. One such thread alone fits in a well-founded world, the pair does not. The flag travels on an internal channel, so the process relation of the closed process reads only its actual reductions, in which both threads take the same branch. Following them puts the process in $P$ directly.",
   "lead": "Two threads that branch on one flag sent by a third thread are deadlock free. A proof that follows the reductions of the whole process shows it, and a proof that puts each thread into the relation on its own fails."
  },
  {
   "id": "rx-postpone",
   "title": "Postponement, a holding thread that never serves",
   "modes": [
    "lf"
   ],
   "code": "chat = !(f = λa. let a = send ⟨∗, a⟩ in (force f) a)\nloop = !(f = λ⟨a, b⟩. let ⟨u, a⟩ = recv a in let ∗ = u in (force f) ⟨a, b⟩)\nmain = let ⟨a, a′⟩ = new in let ⟨b, b′⟩ = new in\n       let ∗ = spawn (λ_. (force chat) a′) in\n       let ∗ = spawn (λ_. close b′) in\n       (force loop) ⟨a, b⟩            -- holds b forever, close b′ waits forever",
   "shows": "Main holds $b$ while it runs a loop that never returns, and the thread with $b'$ waits forever while other threads step. Aging requires $c \\leq a$ of each held end that is not idle. The loop has cost $\\infty$, and $b$ has a finite credit, so the program has no lock-free typing.",
   "rocq": "to be mechanized",
   "accepts": {
    "lf": {
     "ok": false,
     "part": "aging"
    }
   },
   "lead": "A deadlock-free program in which one thread waits forever, because the thread holding its dual end never acts on that end."
  },
  {
   "id": "rx-delegate",
   "title": "Endless delegation, an end that travels forever",
   "modes": [
    "lf"
   ],
   "code": "pass = !(f = λ⟨e, x, y⟩. let x = send ⟨e, x⟩ in let ⟨e, y⟩ = recv y in (force f) ⟨e, x, y⟩)\nback = !(f = λ⟨x, y⟩. let ⟨e, x⟩ = recv x in let y = send ⟨e, y⟩ in (force f) ⟨x, y⟩)\nmain = let ⟨e, e′⟩ = new in let ⟨x, x′⟩ = new in let ⟨y, y′⟩ = new in\n       let ∗ = spawn (λ_. close e′) in       -- waits for e forever\n       let ∗ = spawn (λ_. (force back) ⟨x′, y′⟩) in\n       (force pass) ⟨e, x, y⟩                -- e goes back and forth forever",
   "shows": "Two threads send the end $e$ back and forth forever, and the thread with $e'$ waits. Each send passes $e$ on with its counter one lower. After finitely many sends no credit remains to send $e$ again, so the program has no lock-free typing.",
   "rocq": "to be mechanized",
   "accepts": {
    "lf": {
     "ok": false,
     "part": "payload credit"
    }
   },
   "lead": "A deadlock-free program in which an end is sent back and forth forever while its partner waits."
  },
  {
   "id": "rx-relink",
   "title": "Link refresh, a waiting thread that always faces a fresh end",
   "modes": [
    "lf"
   ],
   "code": "refresh = !(f = λ⟨w, k⟩. let ⟨c, c′⟩ = new in\n                     let ∗ = link ⟨w, c⟩ in          -- the waiting thread now talks to c′\n                     let k = send ⟨∗, k⟩ in           -- one step on another channel\n                     (force f) ⟨c′, k⟩)\nsink    = !(f = λk. let ⟨u, k⟩ = recv k in let ∗ = u in (force f) k)\nmain = let ⟨w, w′⟩ = new in let ⟨k, k′⟩ = new in\n       let ∗ = spawn (λ_. close w′) in              -- waits forever\n       let ∗ = spawn (λ_. (force sink) k′) in\n       (force refresh) ⟨w, k⟩",
   "shows": "Each round links the partner of the waiting end to a new channel. The waiting thread then faces a new end with a full counter, and no counter decreases to $0$. E-Link asks the credit of the linked end to exceed the partner bound of the new end. After the send that credit is too low for the recursive call, so the program has no lock-free typing.",
   "rocq": "to be mechanized",
   "accepts": {
    "lf": {
     "ok": false,
     "part": "tickets"
    }
   },
   "lead": "A deadlock-free program in which links keep replacing the end a thread waits on."
  },
  {
   "id": "rx-chain",
   "title": "A waiting chain that grows forever",
   "modes": [
    "lf"
   ],
   "code": "grow = !(f = λw. let ⟨c, c′⟩ = new in                 -- c below the point of w\n                 let ⟨d, d′⟩ = new in let ∗ = spawn (λ_. recvclose d′) in\n                 let ∗ = close (send ⟨∗, d⟩) in              -- one session action\n                 let ∗ = spawn (λ_. (force f) c′) in\n                 let ∗ = close c in close w)                 -- waits on its child\nmain = let ⟨w, w′⟩ = new in let ∗ = spawn (λ_. close w′) in (force grow) w\n-- every thread waits on the one it spawned, close w′ never proceeds",
   "shows": "Each thread spawns a child, waits on it, and the child does the same. Each wait is at a point below the point of the previous one, and the chain grows forever. A well-founded world has no infinite descending chain, and lock-free soundness assumes a well-founded world.",
   "rocq": "argued in docs/redesign/check-layers.md, E-New asks wf_new (static/Contexts.v), not mechanized as a rejection",
   "accepts": {
    "lf": {
     "ok": false,
     "part": "E-New"
    }
   },
   "lead": "A deadlock-free program in which a chain of waiting threads grows forever."
  }
 ]
};
