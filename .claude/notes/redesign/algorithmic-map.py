"""Write the section "Algorithmic typing" of docs/explorer/map.json.

    python3 .claude/notes/redesign/algorithmic-map.py docs/explorer/map.json

Replaces the section with id algorithmic and its alg.* notes, then
docs/explorer/check.sh and paper/tools/map2tex.py run as usual.
"""
import json, sys
p = sys.argv[1]
with open(p, encoding='utf-8') as fh:
    m = json.load(fh)
m['sections'] = [s for s in m['sections'] if s['id'] != 'algorithmic']

V = r'\mathrel{\sym{tp.vdash}{\vdash}}'
SYN = r'\mathrel{\sym{alg.syn}{\Rightarrow}}'
CHK = r'\mathrel{\sym{alg.chk}{\Leftarrow}}'
MODE = r'\mathrel{\sym{alg.mode}{d}}'
def EFF(e): return r'\inmode{lf}{\ \sym{tj.eff}{!}\ ' + e + '}'
def J(G, D, F, t, arr, T, e): return G + ' ; ' + D + ' ' + V + '^{' + F + '} ' + t + ' ' + arr + ' ' + T + EFF(e)
D1 = r'\sym{alg.split}{\Delta{\restriction}t_1}'
D2 = r'\sym{alg.split}{\Delta{\setminus}t_1}'
D2a = r'\sym{alg.split}{\Delta{\setminus}t_1}\inmode{lf}{ \sym{age.ctx}{- \varepsilon_1}}'
HELD = r'\sym{tj.held}{\triangleleft}'
ARR = r'(T \mathrel{\sym{ty.arrow}{\multimap}}^{u}_{l}\inmode{lf}{[\varepsilon]}\, U)\inmode{lf}{^{a}}'
SEQ = r'\sym{tj.seq}{\cdot}'
def rule(prems, concl, name):
    return r'\dfrac{\begin{array}{c}' + prems + r'\end{array}}{' + concl + r'}\;\textsf{' + name + '}'
def stack(*rs): return r'\begin{array}{c}' + r'\\[3ex]'.join(rs) + r'\end{array}'
UNL = r'\sym{ctx.empty}{\sym{ty.unlimited}{\mathsf{unlimited}}\,\Delta}'
CONTR = r'\sym{sty.contr}{\mathsf{contr}}'

annot = (r'\begin{array}{c}\begin{array}{rl}'
  r't ::= & i \mid \ast \mid o \mid \lambda t \mid t_1\,t_2 \mid \langle t_1, t_2\rangle \mid \sym{syn.letu}{\mathsf{let}\ \ast = t_1\ \mathsf{in}\ t_2} \mid \sym{syn.letp}{\mathsf{let}\ \langle a,b\rangle = t_1\ \mathsf{in}\ t_2} \\'
  r'\mid & \sym{syn.inj}{\mathsf{inj}_i\,t} \mid \sym{syn.case}{\mathsf{case}\ t\,(t_1)\,(t_2)} \mid\ \sym{syn.box}{!t} \mid \sym{syn.op}{k\,t} \\'
  r'\mid & \sym{alg.new}{\mathsf{new}[C, S\inmode{lf}{, m_1, m_2}]} \mid \sym{alg.newf}{\mathsf{new}[x\cdot\kappa, S\inmode{lf}{, m_1, m_2}]} \mid \sym{alg.force}{\mathsf{force}[\bar x, \bar s]\,t} \\'
  r'\mid & \sym{alg.asc}{(t : T\inmode{lf}{\ !\ \varepsilon})} \mid \sym{alg.pack}{\mathsf{pack}[\bar x]\,t : \exists^{l}\bar\iota.\,C.\,T} \mid \sym{alg.open}{\mathsf{open}\ i : U\ \mathsf{in}\ t}'
  r'\end{array} \\[2ex]'
  r'\sym{alg.erase}{|\mathsf{new}[\ldots]| = \mathsf{new} \qquad |\mathsf{force}[\bar x, \bar s]\,t| = \mathsf{force}\,|t| \qquad |(t : T)| = |\mathsf{pack}[\bar x]\,t : T| = |\mathsf{open}\ i : U\ \mathsf{in}\ t| = |t|}'
  r'\end{array}')

judg = (r'\begin{array}{c}'
  + J(r'\Gamma', r'\Delta', 'F', 't', SYN, 'T', r'\varepsilon') + r'\qquad '
  + J(r'\Gamma', r'\Delta', 'F', 't', CHK, 'T', r'\varepsilon') + r' \\[2ex]'
  r'\sym{alg.split}{\Delta{\restriction}t = \{\, z : T \in \Delta \mid z \in |t| \lor \sym{ty.unlimited}{\mathsf{unlimited}}\,T \,\}} \qquad '
  r'\sym{alg.split}{\Delta{\setminus}t = \{\, z : T \in \Delta \mid z \notin |t| \lor \sym{ty.unlimited}{\mathsf{unlimited}}\,T \,\}}'
  r'\end{array}')

r_unit = rule(UNL, J(r'\Gamma', r'\Delta', 'F', r'\ast', SYN, r'\ast', r'\sym{tj.zero}{0}'), 'Syn-Unit')
r_var = rule(UNL, J(r'\Gamma', r'\sym{ctx.only}{\Delta, i : T}', 'F', 'i', SYN, 'T', r'\sym{tj.zero}{0}'), 'Syn-Var')
r_chan = rule(UNL + r'\inmodeplain{lf}{\quad }\inmode{lf}{\sym{E-Chan.crtk}{a \leq m}}',
              J(r'\Gamma', r'\sym{ctx.only}{\Delta, o : \sym{ty.sess}{S_x\inmode{lf}{^{a,m}}}}', 'F', 'o', SYN, r'\sym{ty.sess}{S_x\inmode{lf}{^{a,m}}}', r'\sym{tj.zero}{0}'), 'Syn-Chan')
NEWWF = r'\sym{E-New.wf}{\inmodeplain{df}{\sym{new.acyc}{\mathsf{acyc\_new}}}\inmode{lf}{\sym{new.ok}{\mathsf{new\_ok}_N}}\,\Gamma\,\rho\,C}'
TK = r'\inmodeplain{lf}{\quad }\inmode{lf}{\sym{E-New.tickets}{m_1 + m_2 \leq N}}'
r_new = rule(UNL + r'\quad ' + NEWWF + r'\quad ' + CONTR + r'\,S' + TK,
             J(r'\Gamma', r'\Delta', 'F', r'\sym{alg.new}{\mathsf{new}[C, S\inmode{lf}{, m_1, m_2}]}', SYN,
               r'\exists^{\bot}\rho.\ C.\ \sym{ty.sess}{S_{\rho}\inmode{lf}{^{m_1,m_1}}} \otimes \sym{sty.dual}{\overline{S}}_{\overline{\rho}}\inmode{lf}{^{m_2,m_2}}', r'\sym{tj.zero}{0}'), 'Syn-New')
r_newf = rule(UNL + r'\quad ' + CONTR + r'\,S' + TK,
             J(r'\Gamma', r'\Delta', 'F', r'\sym{alg.newf}{\mathsf{new}[x\cdot\kappa, S\inmode{lf}{, m_1, m_2}]}', SYN,
               r'\sym{ty.sess}{S_{x\cdot\kappa}\inmode{lf}{^{m_1,m_1}}} \otimes \sym{sty.dual}{\overline{S}}_{\overline{x\cdot\kappa}}\inmode{lf}{^{m_2,m_2}}', r'\sym{tj.zero}{0}'), 'Syn-New-Field')
leaves = stack(r_unit, r_var, r_chan, r_new, r_newf)

r_app = rule(J(r'\Gamma', D1, 'F ' + HELD + ' ' + D2, 't_1', SYN, ARR, r'\varepsilon_1') + r'\quad \sym{E-App.ub}{u \prec F} \\ '
             + J(r'\Gamma', D2a, 'F ' + HELD + r' (T \mathrel{\sym{ty.arrow}{\multimap}}^{u}_{l} U)\inmode{lf}{^{a}}', 't_2', CHK, 'T', r'\varepsilon_2')
             + r'\inmodeplain{lf}{\quad }\inmode{lf}{\varepsilon_2 \leq a}',
             J(r'\Gamma', r'\Delta', 'F', r't_1\,t_2', SYN, 'U', r'\varepsilon_1 ' + SEQ + r' \varepsilon_2 ' + SEQ + r' \varepsilon'), 'Syn-App')
r_pair = rule(J(r'\Gamma', D1, 'F ' + HELD + ' ' + D2, 't_1', SYN, 'T_1', r'\varepsilon_1') + r'\quad '
              + J(r'\Gamma', D2a, 'F ' + HELD + ' T_1', 't_2', SYN, 'T_2', r'\varepsilon_2'),
              J(r'\Gamma', r'\Delta', 'F', r'\langle t_1, t_2\rangle', SYN, r'\inmode{lf}{(}T_1\inmode{lf}{ \sym{age.ctx}{- \varepsilon_2}}\inmode{lf}{)} \otimes T_2', r'\varepsilon_1 ' + SEQ + r' \varepsilon_2'), 'Syn-Pair')
r_letu = rule(J(r'\Gamma', D1, 'F ' + HELD + ' ' + D2, 't_1', CHK, r'\ast', r'\varepsilon_1') + r'\quad '
              + J(r'\Gamma', D2a, 'F', 't_2', MODE, 'T', r'\varepsilon_2'),
              J(r'\Gamma', r'\Delta', 'F', r'\sym{syn.letu}{\mathsf{let}}\ \ast = t_1\ \sym{syn.letu}{\mathsf{in}}\ t_2', MODE, 'T', r'\varepsilon_1 ' + SEQ + r' \varepsilon_2'), 'Alg-LetU')
r_letp = rule(J(r'\Gamma', D1, 'F ' + HELD + ' ' + D2, 't_1', SYN, r'T_1 \otimes T_2', r'\varepsilon_1') + r'\quad '
              + J(r'\Gamma', r'T_2, T_1, ' + D2a, 'F', 't_2', MODE, 'T', r'\varepsilon_2'),
              J(r'\Gamma', r'\Delta', 'F', r'\sym{syn.letp}{\mathsf{let}}\ \langle a, b\rangle = t_1\ \sym{syn.letp}{\mathsf{in}}\ t_2', MODE, 'T', r'\varepsilon_1 ' + SEQ + r' \varepsilon_2'), 'Alg-LetP')
elims = stack(r_app, r_pair, r_letu, r_letp)

r_lam = rule(r'\sym{E-Abs.lb}{l \preccurlyeq \Delta}\quad \sym{E-Abs.contr}{' + CONTR + r'\,T} \\ '
             + J(r'\Gamma', r'\Delta\inmode{lf}{ \sym{E-Abs.cap}{- a}}, T', r'\sym{ty.up}{{\vartriangle}u}', 't', CHK, 'U', r'\varepsilon_0')
             + r'\inmodeplain{lf}{\quad }\inmode{lf}{\varepsilon_0 \leq \varepsilon}',
             J(r'\Gamma', r'\Delta', 'F', r'\lambda t', CHK, ARR, r'\sym{tj.zero}{0}'), 'Chk-Lam')
r_inj = rule(J(r'\Gamma', r'\Delta', 'F', 't', CHK, 'T_i', r'\varepsilon') + r'\quad \sym{E-Inj.contr}{' + CONTR + r'\,(T_1 \oplus T_2)}',
             J(r'\Gamma', r'\Delta', 'F', r'\sym{syn.inj}{\mathsf{inj}_i\,t}', CHK, r'T_1 \oplus T_2', r'\varepsilon'), 'Chk-Inj')
r_case = rule(J(r'\Gamma', r'\sym{alg.split}{\Delta{\restriction}t}', 'F ' + HELD + r' \sym{alg.split}{\Delta{\setminus}t}', 't', SYN, r'T_1 \oplus T_2', r'\varepsilon_0') + r' \\ '
              + J(r'\Gamma', r'T_j, \sym{alg.split}{\Delta{\setminus}t}\inmode{lf}{ \sym{age.ctx}{- \varepsilon_0}}', 'F', 't_j', CHK, 'T', r'\varepsilon_j') + r'\quad (j = 1, 2)',
              J(r'\Gamma', r'\Delta', 'F', r'\sym{syn.case}{\mathsf{case}\ t\,(t_1)\,(t_2)}', CHK, 'T', r'\varepsilon_0 ' + SEQ + r' \sym{tp.max}{\max(\varepsilon_1, \varepsilon_2)}'), 'Chk-Case')
BOX = r'\Box(\forall \bar\iota\,\bar Z.\ C.\ \ast \mathrel{\sym{ty.arrow}{\multimap}}^{u}\inmode{lf}{[\varepsilon]}\,U)'
r_box = rule(r'\sym{E-Box.self}{B = ' + BOX + r'}\quad \sym{E-Box.unl}{\sym{ty.unlimited}{\mathsf{unlimited}}\,\Delta}\quad \sym{alg.boxcontr}{' + CONTR + r'\,U, \Delta}\quad \sym{alg.boxfresh}{\bar\zeta \mathrel{\#} \Delta, B} \\ '
             + J(r'\sym{E-Box.open}{\Gamma, C(\bar\iota)}', r'\sym{E-Box.self}{\Delta, f : B}', r'\sym{ty.up}{{\vartriangle}u}', 't', CHK, r'\sym{alg.boxinst}{U[\bar Z \mapsto \bar\zeta]}', r'\varepsilon_0')
             + r'\inmodeplain{lf}{\quad }\inmode{lf}{\varepsilon_0 \leq \varepsilon}',
             J(r'\Gamma', r'\Delta', 'F', r'!t', CHK, 'B', r'\sym{tj.zero}{0}'), 'Chk-Box')
r_sub = rule(r"\sym{alg.bysub}{t \neq \lambda t', \mathsf{inj}_i\,t', \mathsf{case}\ldots, !t', \mathsf{let}\ldots}\quad "
             + J(r'\Gamma', r'\Delta', 'F', 't', SYN, 'T_0', r'\varepsilon') + r' \\ \sym{sub.tsub}{\Gamma \vdash T_0 \leq T}\quad \sym{E-Sub.contr}{' + CONTR + r'\,T_0 \Rightarrow \mathsf{contr}\,T}',
             J(r'\Gamma', r'\Delta', 'F', 't', CHK, 'T', r'\varepsilon'), 'Chk-Sub')
intros = stack(r_lam, r_inj, r_case, r_box, r_sub)

r_op = rule(J(r'\Gamma', r'\Delta', 'F', 't', SYN, 'T_0', r'\varepsilon') + r'\quad \sym{alg.prem}{\mathsf{prem}_k(\Gamma, F, T_0)}',
            J(r'\Gamma', r'\Delta', 'F', r'k\,t', SYN, r'\sym{alg.prem}{\mathsf{res}_k(T_0)}', r'\varepsilon ' + SEQ + r' \varepsilon_k'), 'Syn-Op')
r_force = rule(J(r'\Gamma', r'\Delta', 'F', 't', SYN, BOX, r'\varepsilon_0') + r' \\ \sym{E-Force.hold}{\Gamma \mathrel{\sym{side.hold}{\vdash}} C[\bar x]}\quad \sym{E-Box.inst}{\sym{tp.sinsts}{\mathsf{sinsts}}\,\bar s}\quad \sym{E-Force.ub}{u[\bar x] \prec F}',
               J(r'\Gamma', r'\Delta', 'F', r'\sym{alg.force}{\mathsf{force}[\bar x, \bar s]\,t}', SYN, r'\sym{tp.sinst}{U[\bar s]}\sym{tp.pinst}{[\bar x]}', r'\varepsilon_0 ' + SEQ + r' \sym{E-Force.one}{1} ' + SEQ + r' \varepsilon'), 'Syn-Force')
r_asc = rule(J(r'\Gamma', r'\Delta', 'F', 't', CHK, 'T', r'\varepsilon') + r'\inmodeplain{lf}{\quad }\inmode{lf}{\sym{E-Sub.cost}{\varepsilon \leq \varepsilon'"'"'}}',
             J(r'\Gamma', r'\Delta', 'F', r'\sym{alg.asc}{(t : T\inmode{lf}{\ !\ \varepsilon'"'"'})}', SYN, 'T', r"\varepsilon'"), 'Syn-Asc')
r_pack = rule(r'\sym{E-Force.hold}{\Gamma \mathrel{\sym{side.hold}{\vdash}} C[\bar x]}\quad \sym{E-Pack.lb}{l \preccurlyeq \sym{tp.pinst}{T[\bar x]}}\quad \sym{E-Pack.wf}{\Gamma, C \mathrel{\sym{ctx.slt}{\vdash}} l \preccurlyeq T}\quad '
              + J(r'\Gamma', r'\Delta', 'F', 't', CHK, r'T[\bar x]', r'\varepsilon'),
              J(r'\Gamma', r'\Delta', 'F', r'\sym{alg.pack}{\mathsf{pack}[\bar x]\,t : \exists^{l}\bar\iota.\,C.\,T}', SYN, r'\exists^{l}\bar\iota.\,C.\,T', r'\varepsilon'), 'Syn-Pack')
r_open = rule(r'\sym{E-Open.entry}{\Delta(i) = \exists^{l}\bar\iota.\,C.\,T,\ \neg\sym{ty.unlimited}{\mathsf{unlimited}}\,T}\quad \sym{E-Box.fresh}{\bar\iota \mathrel{\#} \Gamma, \Delta, F, U}\quad \sym{E-Open.cons}{\mathsf{conserv}_{\Gamma}(\bar\iota, C)} \\ '
              + J(r'\Gamma, C(\bar\iota)', r'\Delta[i \mapsto T]', 'F', 't', CHK, 'U', r'\varepsilon'),
              J(r'\Gamma', r'\Delta', 'F', r'\sym{alg.open}{\mathsf{open}\ i : U\ \mathsf{in}\ t}', SYN, 'U', r'\varepsilon'), 'Syn-Open')
structs = stack(r_op, r_force, r_asc, r_pack, r_open)

thms = (r'\begin{array}{l}'
  + J(r'\Gamma', r'\Delta', 'F', 't', SYN, 'T', r'\varepsilon') + r' \implies ' + r'\Gamma ; \Delta ' + V + r'^{F} |t| : T' + EFF(r'\varepsilon') + r' \\[1ex]'
  + r'\sym{ctx.contr}{' + CONTR + r'\,\Delta} \land \Gamma ; \Delta ' + V + r'^{F} e : T' + EFF(r'\varepsilon') + r' \implies \exists t.\ |t| = e \land ' + J(r'\Gamma', r'\Delta', 'F', 't', SYN, 'T', r'\varepsilon') + r' \\[1ex]'
  + r'\sym{alg.dec}{\mathsf{alg}(t)(\Gamma, \Delta, F) = (T\inmode{lf}{, \varepsilon}) \iff ' + J(r'\Gamma', r'\Delta', 'F', 't', SYN, 'T', r'\varepsilon') + r'}'
  + r'\end{array}')

def src(file, names): return {'file': file, 'names': names}
blocks = [
 {'id': 'alg-annot', 'title': 'Annotated terms',
  'formula': annot,
  'caption': r"An annotated term $t$ is a [[syn-terms|term]] with five more forms, each of which records a choice that the declarative rules make and the term does not show. $\mathsf{new}[C, S]$ creates at a fresh base with the constraint $C$ of [[r-new|E-New]], and $\mathsf{new}[x\cdot\kappa, S]$ creates at a field. $\mathsf{force}[\bar x, \bar s]$ fixes the instance of [[r-boxes|E-Force]]. The ascription $(t : T)$ is one use of E-Sub of [[t-subs]], $\mathsf{pack}$ one use of E-Pack and $\mathsf{open}$ one use of E-Open of [[r-ex]]. Inside $\mathsf{open}\ i : U\ \mathsf{in}\ t$ the annotations of $t$ name the opened points $\bar\iota$. The erasure $|t|$ deletes the annotations and gives the term that the declarative judgment types.",
  'why': r"No program mentions a point, so the term alone does not fix where E-Open applies, which points it introduces, or at which position and constraint $\mathsf{new}$ creates. The annotations record these choices and the erasure removes them before the declarative judgment, which therefore stays as it is.",
  'source': [src('algorithmic/Annot.v', ['aexpr', 'erase'])],
  'deviations': [{'kind': 'notation', 'reason': r"The Rocq names the opened variable by its index, `AOpen i U t`. The annotations inside $t$ use de Bruijn point variables as the premise of `e_open` does, the opened ones at $0, \ldots, m - 1$ and the others shifted by $m$. `AAsc T c t` has the cost $c$ in both modes, at $\infty$ in the deadlock-free one.", 'names': ['aexpr']}]},
 {'id': 'alg-judgment', 'title': 'Algorithmic judgments',
  'formula': judg,
  'caption': r"Synthesis $\Rightarrow$ computes the type\inmode{lf}{ and the cost} from $\Gamma$, $\Delta$, $F$ and $t$. Checking $\Leftarrow$ takes the type as input\inmode{lf}{ and computes the cost}. A binary rule splits $\Delta$ by occurrence. The first premise receives the entries that its term mentions, the second the rest, and both receive the [[ty-kinds|unlimited]] entries. The future of the first premise is then known before it runs, as in [[t-judgment]].",
  'why': r"The declarative split of [[t-contexts]] is a choice, and the future of the first premise reads its second half. A linear entry occurs in exactly the subterm that uses it, so the occurrences fix the split. An unlimited entry is a box, which has no active point and ages to itself, so handing it to both sides changes neither future nor aging.",
  'source': [src('algorithmic/Algo.v', ['syn', 'chk', 'fut1']), src('algorithmic/Annot.v', ['tpart', 'lpart', 'lpart_wk'])],
  'deviations': [{'kind': 'notation', 'reason': r"The Rocq keeps the ends in their own context $\Theta$, as [[t-contexts]] records, and splits it by the ends of the erased first subterm (`tpart`), and the variables by `lpart`. The map writes both as one split of $\Delta$.", 'names': ['tpart', 'lpart']}]},
 {'id': 'alg-leaves', 'title': 'Leaves and creation',
  'formula': leaves,
  'caption': r"The leaves synthesize the types of [[r-base]] with the same premises. $\mathsf{new}$ synthesizes the type of [[r-new|E-New]] at the base or field and the constraint\inmode{lf}{ and tickets} that its annotation names.",
  'why': r"Each premise is a declarative premise, so the rule decides it by an oracle or by computation.",
  'source': [src('algorithmic/Algo.v', ['a_unit', 'a_var', 'a_chan', 'a_new', 'a_new_fld'])]},
 {'id': 'alg-elim', 'title': 'Application, pairs and let',
  'formula': elims,
  'caption': r"The function of an application synthesizes its arrow, which gives the argument type to check against. A pair synthesizes both components. A let checks or synthesizes its body in the mode $d \in \{\Rightarrow, \Leftarrow\}$ of the conclusion. The futures and the aging are those of [[r-fun]] and [[r-data]], with the split of [[alg-judgment]].",
  'why': r"The arrow has the upper point $u$ and the lower point $l$. Once synthesized, it fixes the premise $u \prec F$ and the future of the argument.",
  'source': [src('algorithmic/Algo.v', ['a_app', 'a_pair', 'a_letu', 'a_letp', 'c_letu', 'c_letp'])]},
 {'id': 'alg-intro', 'title': 'Checked forms',
  'formula': intros, 'introduces': [r'\zeta'],
  'caption': r"A $\lambda$, an injection, a case and a box are only checked, against an expected type that fixes their points\inmode{lf}{, credit and cost}. Chk-Box checks the body once, at fresh session variables $\bar\zeta$ for the $\bar Z$ of the box, and asks the box context contractive. The other forms are checked by synthesis followed by [[t-subs|subtyping]].",
  'why': r"E-Box quantifies over the session instances. A derivation over contractive contexts at fresh variables gives one at each contractive instance (`typed_sinst`), so one check suffices. A $\lambda$ has no best upper point, which is why it needs its arrow from outside.",
  'source': [src('algorithmic/Algo.v', ['c_lam', 'c_inj', 'c_case', 'c_box', 'c_sub', 'by_sub']), src('algorithmic/Annot.v', ['box_inst', 'box_base']), src('algorithmic/Sound.v', ['box_body_all']), src('static/Sinst.v', ['typed_sinst'])],
  'deviations': [{'kind': 'notation', 'reason': r"The fresh variables $\bar\zeta$ are `box_inst M k` with `M = box_base k U Δ`, the session variables $M, \ldots, M + k - 1$ above the free session variables of the box context. Checking returns the cost of the body, and Chk-Lam and Chk-Box ask it at most the cost in the type, which E-Sub then raises.", 'names': ['box_inst', 'box_base']}]},
 {'id': 'alg-struct', 'title': 'Constants, force and the annotation rules',
  'formula': structs,
  'caption': r"Syn-Op stands for one rule per constant $k$ of [[r-act]] and [[r-threads]]. $\mathsf{prem}_k$ and $\mathsf{res}_k$ are the premises and the result of the rule of $k$, one of E-Send, E-Recv, E-Close, E-Select, E-Branch, E-Link and E-Spawn. They are read on the synthesized type of the argument.\inmode{lf}{ The cost $\varepsilon_k$ is $1$ for the actions and $0$ for link and spawn.} Syn-Asc, Syn-Pack and Syn-Open are E-Sub, E-Pack and E-Open at the place that the annotation marks.",
  'why': r"A constant reads the session type of its argument, so the argument synthesizes. The three annotation rules are the only places, besides Chk-Sub, where a type changes without a change of term.",
  'source': [src('algorithmic/Algo.v', ['a_send', 'a_recv', 'a_close', 'a_select', 'a_branch', 'a_link', 'a_spawn', 'a_force', 'a_asc', 'a_pack', 'a_open'])]},
 {'id': 'alg-oracles', 'title': 'Oracles',
  'table': {'align': 'l', 'header': ['oracle', 'decides'],
    'rows': [
      {'label': 'entailment', 'cells': [{'formula': r'\sym{ctx.slt}{\Gamma \vdash_W x \prec y}'}]},
      {'label': 'instance of a constraint', 'cells': [{'formula': r'\Gamma \mathrel{\sym{side.hold}{\vdash_W}} C[\bar x]'}]},
      {'label': 'conservativity', 'cells': [{'formula': r'\sym{E-Open.cons}{\mathsf{conserv}_{\Gamma}(\bar\iota, C)}'}]},
      {'label': 'creation', 'cells': [{'formula': NEWWF}]},
      {'label': 'equality of constraints', 'cells': [{'formula': r'C = C'"'"''}]},
      {'label': 'session types', 'cells': [{'formula': r"S \sym{sty.seqv}{\approx} S'\inmode{lf}{ \qquad S \mathrel{\sym{sty.ssub}{\sqsubseteq}} S'}"}]}]},
  'caption': r"The algorithm is decidable relative to these six oracles. From them it decides equality of types, the side conditions of [[t-side]], the scope of payloads and [[t-subs|subtyping]], each by recursion on the types. For finite constraints the first five reduce to finite searches over the facts.",
  'why': r"A constraint is a set of facts, and the client and server example uses an infinite one. The rules read it only through these questions, so the algorithm is as decidable as the theory of the constraints it meets and the equivalence of context-free session types.",
  'source': [src('algorithmic/Oracles.v', ['SltOracle', 'HoldOracle', 'ConsOracle', 'NewOracle', 'BcsOracle', 'SequivOracle', 'SsubOracle', 'tsub_dec', 'ty_eq_dec'])]},
 {'id': 'alg-thms', 'title': 'Soundness, completeness and decidability',
  'formula': thms,
  'caption': r"Soundness. A synthesized type is a declarative type of the erasure, at the same contexts\inmode{lf}{ and cost}. Completeness. Over a contractive context a declarative derivation for $e$ gives an annotation of $e$ that synthesizes the same type\inmode{lf}{ and cost}. Decidability. The function $\mathsf{alg}$ computes synthesis and checking by recursion on $t$ and returns exactly the derivable results, so each judgment is decidable relative to the [[alg-oracles|oracles]] and has at most one result. The three theorems hold at each bound $N$, so for both instances.",
  'why': r"Together they make the algorithmic system an implementation of the declarative one for annotated programs. A program typed by P-Term starts from contractive ends and no variables, so completeness covers the programs that P-Term types.",
  'source': [src('algorithmic/Sound.v', ['algo_sound']), src('algorithmic/Complete.v', ['algo_complete', 'algo_iff']), src('algorithmic/Decide.v', ['alg', 'alg_sound', 'alg_complete', 'syn_dec', 'chk_dec', 'syn_det', 'chk_det', 'typed_annot_dec'])],
  'deviations': [{'kind': 'notation', 'reason': r"Completeness is stated for each weakening of $\Delta$ by unlimited entries (`algo_complete`), and `algo_complete_at` is the form shown. The contractive context is `tenv_contr Θ` and `lenv_contr Δ`.", 'names': ['algo_complete']}]},
]

sec = {'id': 'algorithmic', 'title': 'Algorithmic typing',
       'intro': r"The algorithmic system types annotated terms by two syntax-directed judgments, synthesis and checking. It is sound and complete for the declarative judgment of [[t-judgment]] and decidable relative to oracles for the order facts and for session types.\inmode{lf}{ Costs, credits and tickets are literals of the annotations or computed from them.}",
       'blocks': blocks}
m['sections'].append(sec)

def note(title, meaning, why, example, sig=None, source=None):
    n = {'title': title, 'meaning': meaning, 'why': why, 'breaks': 'Nothing. It is a definition.', 'example': example}
    if sig: n['signature'] = sig
    if source: n['source'] = source
    return n
N = m['notes']
N['alg.syn'] = note(r'Synthesis $\Rightarrow$', r"$\Gamma ; \Delta \vdash^{F} t \Rightarrow T$ computes $T$\inmode{lf}{ and the cost} from the inputs and $t$.", r"The type of an elimination form or an annotation follows from its parts.", r"$\Gamma ; \Delta \vdash^{F} \ast \Rightarrow \ast$.", r'\Gamma ; \Delta \vdash^{F} t \Rightarrow T\inmode{lf}{\ !\ \varepsilon}', [src('algorithmic/Algo.v', ['syn'])])
N['alg.chk'] = note(r'Checking $\Leftarrow$', r"$\Gamma ; \Delta \vdash^{F} t \Leftarrow T$ takes $T$ as input\inmode{lf}{ and computes the cost}.", r"A $\lambda$, an injection, a case and a box read their points from the expected type.", r"$\Gamma ; \Delta \vdash^{F} \lambda t \Leftarrow \ast \multimap^{\top}_{\bot} \ast$ when the body checks.", r'\Gamma ; \Delta \vdash^{F} t \Leftarrow T\inmode{lf}{\ !\ \varepsilon}', [src('algorithmic/Algo.v', ['chk'])])
N['alg.mode'] = note(r'Mode $d$', r"$d$ is $\Rightarrow$ or $\Leftarrow$, the mode of the conclusion, passed to the body of a let.", r"A let returns what its body returns.", r"A let in checking position checks its body.")
N['alg.split'] = note(r'Split by occurrence', r"$\Delta{\restriction}t$ holds the entries of $\Delta$ that $|t|$ mentions and the unlimited ones, $\Delta{\setminus}t$ the others and the unlimited ones.", r"Linear entries occur exactly in the subterm that uses them, so the split needs no choice.", r"With $\Delta = c : S_x, d : S'_y$ and $t = \mathsf{close}\,c$, $\Delta{\restriction}t = c : S_x$.", None, [src('algorithmic/Annot.v', ['tpart', 'lpart'])])
N['alg.erase'] = note(r'Erasure $|t|$', r"The term left when the annotations of $t$ are deleted.", r"The declarative judgment types terms without annotations.", r"$|(\mathsf{open}\ 0 : \ast\ \mathsf{in}\ \ast : \ast)| = \ast$.", None, [src('algorithmic/Annot.v', ['erase'])])
N['alg.new'] = note(r'$\mathsf{new}[C, S]$', r"Creation at a fresh base with constraint $C$ and protocol $S$\inmode{lf}{ at tickets $m_1$ and $m_2$}.", r"E-New picks $C$, $S$\inmode{lf}{ and the tickets}, and the term shows none of these choices.", r"$\mathsf{new}[\varnothing, \mathsf{Close}]$.", None, [src('algorithmic/Annot.v', ['aexpr'])])
N['alg.newf'] = note(r'$\mathsf{new}[x\cdot\kappa, S]$', r"Creation at the field $\kappa$ of the point $x$.", r"E-New picks the position, which the term does not show.", r"$\mathsf{new}[\rho\cdot 0, \mathsf{Close}]$.", None, [src('algorithmic/Annot.v', ['aexpr'])])
N['alg.force'] = note(r'$\mathsf{force}[\bar x, \bar s]$', r"A force at the point instance $\bar x$ and the session instance $\bar s$.", r"E-Force picks both instances, and matching against the expected type does not always find the session instance.", r"$\mathsf{force}[\rho^{+}, \cdot]\,f$.", None, [src('algorithmic/Annot.v', ['aexpr'])])
N['alg.asc'] = note(r'Ascription $(t : T)$', r"$t$ at the type $T$\inmode{lf}{ and the cost $\varepsilon$}, one use of E-Sub.", r"E-Sub has no term former. The annotation marks the node where a derivation applies E-Sub.", r"$(\lambda t : \ast \multimap^{\top}_{\bot} \ast)$.", None, [src('algorithmic/Annot.v', ['aexpr'])])
N['alg.pack'] = note(r'$\mathsf{pack}[\bar x]$', r"One use of E-Pack at the witness $\bar x$ and the existential type that follows.", r"A witness that occurs only in the constraint or the lower bound is found by no match on the type.", r"$\mathsf{pack}[\rho]\,t : \exists^{\bot}\iota.\,\varnothing.\,\mathsf{Close}_{\iota}$.", None, [src('algorithmic/Annot.v', ['aexpr'])])
N['alg.open'] = note(r'$\mathsf{open}\ i : U\ \mathsf{in}\ t$', r"One use of E-Open on the existential of the variable $i$, around $t$, with result type $U$.", r"E-Open has no term former, and the points it introduces have no name in the term. The node fixes the place and names the points.", r"$\mathsf{open}\ 0 : \ast\ \mathsf{in}\ t$.", None, [src('algorithmic/Annot.v', ['aexpr'])])
N['alg.boxcontr'] = note(r'Contractive box context', r"$U$ and the types of $\Delta$ are contractive.", r"Instantiating a derivation at a session instance needs contractive contexts (`typed_sinst`).", r"A box whose context holds only contractive boxes.", None, [src('static/Sinst.v', ['lenv_contr'])])
N['alg.boxfresh'] = note(r'Fresh session variables $\bar\zeta$', r"Session variables above the free session variables of $\Delta$ and $B$.", r"The body is checked once at them and instantiated afterwards, which leaves the context unchanged.", r"For a closed $\Delta$, $\bar\zeta = 0, \ldots, k - 1$ above the box variables of $B$.", None, [src('algorithmic/Annot.v', ['box_inst', 'box_base'])])
N['alg.boxinst'] = note(r'$U[\bar Z \mapsto \bar\zeta]$', r"The result of the box with its session variables replaced by the fresh ones.", r"It is one instance of E-Box, and `box_body_all` derives the other instances from this one.", r"$\mathsf{Close}_{x}[\cdot] = \mathsf{Close}_{x}$.", None, [src('algorithmic/Sound.v', ['box_body_all'])])
N['alg.bysub'] = note(r'Forms checked by subtyping', r"The forms other than a $\lambda$, an injection, a case, a box and a let.", r"These forms synthesize, so checking them is synthesis followed by subtyping.", r"An application in checking position.", None, [src('algorithmic/Algo.v', ['by_sub'])])
N['alg.prem'] = note(r'$\mathsf{prem}_k$ and $\mathsf{res}_k$', r"The premises and the result type of the rule of the constant $k$, read on the type of its argument.", r"Each constant has one rule, so the type of the argument fixes premises and result.", r"For $k = \mathsf{close}$, $\mathsf{prem}_k$ asks $\mathsf{unfold}(S) = \mathsf{Close}$ and $x \prec F$, and $\mathsf{res}_k$ is $\ast$.")
N['alg.dec'] = note(r'The algorithm $\mathsf{alg}$', r"A function from an annotated term to a synthesis function and a checking function, each returning a result or none.", r"It decides the algorithmic judgments relative to the oracles.", r"$\mathsf{alg}(\ast)(\Gamma, \Delta, F) = \ast$ when $\Delta$ is unlimited.", None, [src('algorithmic/Decide.v', ['alg'])])
DEVA = [{'kind': 'notation', 'reason': 'The Rocq writes this form as a constructor of `aexpr`.', 'names': ['aexpr']}]
for k in ['alg.new', 'alg.newf', 'alg.force', 'alg.pack', 'alg.open']:
    N[k]['deviations'] = DEVA
N['alg.erase']['deviations'] = [{'kind': 'notation', 'reason': 'The Rocq function `erase` maps each annotation constructor of `aexpr` to the term former it marks or to its subterm.', 'names': ['erase']}]
N['alg.bysub']['deviations'] = [{'kind': 'notation', 'reason': 'The Rocq tests the head constructor with the boolean function `by_sub`.', 'names': ['by_sub']}]
N['alg.boxfresh']['signature'] = r'\bar\zeta \mathrel{\#} \Delta, B'
N['alg.boxfresh']['args'] = [{'name': r'\bar\zeta', 'meaning': 'the fresh session variables, one for each session variable of the box'}]
if 'ctx.contr' not in N:
    N['ctx.contr'] = note(r'Contractive context', r"The session types in $\Delta$ are contractive.", r"Completeness needs contractive contexts at boxes. P-Term gives its thread a contractive context.", r"$c : \mathsf{Close}_{x}$.", None, [src('static/Sinst.v', ['lenv_contr', 'tenv_contr'])])

with open(p, 'w', encoding='utf-8') as fh:
    fh.write(json.dumps(m, ensure_ascii=False, indent=1) + '\n')
