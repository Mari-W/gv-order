# Map audit, 2026-11-22

Branch redesign-map, from redesign at 1401e2d. The audit checks every block,
caption, note and example of docs/explorer against the Rocq of v2/ on this
branch, against the map deltas of the reports in docs/redesign/pending.md,
and against the proof-map checker of branch mapkit. Measured boxes are left
out (branch redesign-mbox).

Each entry gives the block or note id, the old and new text or formula, the
reason, and the Rocq name it was checked against. Sections follow page order.

## Syntax

- Section order (layout.js). Old: terms, let, constants, values, ends, fends,
  processes, points, moves, labels, link substitution. New: ends, constants,
  terms, let, values, fends, processes, labels, points, moves, link
  substitution. Why: checker (var-before-intro of $o$, $k$, $\kappa$), each
  block now uses only what earlier blocks define.
- `syn-terms`. Old: variable $x$ and the former $k$. New: variable $i$ and the
  former $k\,e$. Caption old "Thirteen term formers with de Bruijn variables.
  A box $!e$ binds itself in $e$, and $k$ ranges over the constants." New
  names the binders of λ, case and the pair let, and says that a constant
  always comes with its argument. Why: Rocq change and faithfulness, `Op (k :
  prim) (e : expr)` is a saturated constant, and $x$ clashed with points in
  E-Var next to E-Chan. Checked against `expr`, `Op`, `Var`.
- `syn-values`. Old: $v ::= \ast \mid o \mid k \mid \lambda e \mid \ldots$. New:
  $k$ removed, caption adds "A constant applied to a value is a redex, never
  a value". Why: faithfulness, `is_val` has no case for `Op`. Checked against
  `is_val`.
- `syn-prims`. Caption and title note rewritten: the constants cover channels,
  threads and boxes, one former $k\,e$, one typing rule per constant. Old why
  text claimed "each has an ordinary function type". Checked against `prim`,
  static/Constants.v `k_send`.
- `syn-ends`, `syn-procs`. Captions introduce $c$, $p$ and $q$ before use.
  Why: checker (var-before-intro).
- Notes `syn.var`, `syn.op`, `syn.values` and their signatures follow the
  three changes above. `syn.op` old "A constant $k$ is a value", new "The
  term $k\,e$ applies the constant $k$ to its argument $e$ ... never a value",
  cites `Op` and `k_send` in place of the citation text "(the value $k$ is
  $\lambda x.\,k\,x$)".

- Cross-links (all sections). The page now renders `[[block-id]]` and
  `[[block-id|label]]` in prose as links to blocks (index.html, `blink`), and
  gen.js fails on a dead link. Links added: E-New to O-New and growth of
  worlds, the actions to obligations and readiness, process typing to the
  composition rules and to models of worlds, Sub-Ex to the value clause,
  E-Open to the flag example, the theorem captions to the blocks they
  combine, and the new examples to the rules and theorems they use. This is
  the same link syntax as proof-map, so the converter passes it through.

## Semantics

- `sem-head`. New rows T-Act-Let (unit and pair elimination) and T-Act-Case,
  with notes `T-Act-Let` and `T-Act-Case`. Old: only application and force
  among the β steps, the caption said β covers the rest. Why: instructiveness
  and checker (uncovered `t_act_case_inl`, `t_act_case_inr`). Checked against
  `head_step` constructors `t_act_let_unit`, `t_act_let_pair`,
  `t_act_case_inl`, `t_act_case_inr`.
- `sem-events`. Caption adds what $\tau$ and administrative events are, so
  $\tau$ is defined before the block uses it. Checked against `ev_tau`,
  `ev_admin`.
- `sem-props`. Lock-free caption names the run $r$, its events $l$ and the
  pending thread $t$. Old "a waiting thread later takes part in a step". Why:
  checker (var-before-intro), and the old text said "waiting" where
  `lock_free` says pending. Checked against `lock_free`, `lf_run`.

## Types and worlds

- `ty-grammar`, `ty-dual`, `ty-heads`. Captions introduce the cost $c$, the
  tickets $m$, the payload $P$, and the shapes of $l$ and $u$ before the
  formulas use them. The ⊥ row of `ty-heads` drops $\Gamma$, old
  $\Gamma \nvdash x \prec \bot \quad \Gamma \nvdash \bot \preccurlyeq y$, new
  $x \not\prec \bot \quad \bot \not\preccurlyeq x$, because $\Gamma$ is defined
  only in the typing section. Why: checker (var-before-intro). Note
  `ty.botord` follows.
- `w-world`. Old: $W = (A, \prec_A)$ and a ranked world $R = (A, \varrho)$ with
  one rank function per root. New: the static world $W = (A, \prec_A)$ and the
  world of the relation $R = (B, <_R, k)$, a strict partial order on the
  points $\mathsf{Point}_B$ with roots in $B$ that contains program order. In
  the lock-free view the kind $k ::= \mathsf{strict} \mid \mathsf{ranked}\
  \varrho$, with $x <_R y \iff \varrho(x) < \varrho(y)$ at a ranked world.
  The deadlock-free view hides the kind. Caption and title note explain why
  there are two kinds (one stuck configuration needs a strict order, one wait
  across a run needs ranks fixed once chosen). Why: Rocq change (worlds are
  strict partial orders with a kind field). Checked against `world`,
  `w_ord`, `w_ord_trans`, `w_ord_irrefl`, `w_ord_po`, `w_rk`, `w_rk_ord`,
  `wstrict`, `wranked`, `sworld`, `sworld_wf`.
- `w-order`. Old: $R \vDash x \prec y \iff \varrho(x) < \varrho(y)$ and
  $R \vDash W \iff \forall x \prec_A y.\ R \vDash x \prec y$. New:
  $R \vdash x \prec y \iff \mathsf{po}(x, y) \lor (x, y \in \mathsf{Point}_B
  \land x <_R y)$, $\mathsf{po}$ as its own formula, and $R \vDash W \iff A
  \subseteq B \land \forall (x \prec y) \in {\prec_A}.\ R \vdash x \prec y$.
  Why: Rocq change and faithfulness (`wmodels` also asks the constants as
  roots). Checked against `w_lt`, `po`, `w_le`, `wmodels`, `sw_lt`.
- `w-wf`. Old title "Well-formed and well-founded worlds", formulas
  `world_wf`, `wf`, `wf_new`, `gen_new` (with single partners). New title
  "Acyclic and well-founded worlds": `world_wf`, $\mathsf{acyc}\,W$, the strict
  model of an acyclic world, and in the lock-free view $\mathsf{wf}\,W$ (now
  written as the absence of a descending sequence, without `\text`), the
  ranked model, and $\mathsf{ok}_N$. The creation conditions moved to the
  E-New block, which uses $\Gamma$ (defined later). Old caption "No theorem
  asks anything of the world" was false (the LF results ask a ranked world).
  Checked against `sacyc`, `swf`, `wok`, `dmodels_exists`, `wmodels_exists`,
  `swf_sacyc`.
- `w-ext`. Old: extension of ranked worlds by roots and ranks, growth
  $R \oplus (a, \varrho_a)$, and the well-founded join. New: extension keeps
  roots and order (and in the lock-free view kind and ranks, $k \sqsubseteq
  k'$), strict growth $R \oplus_a C = (B \cup \{a\}, \mathsf{tc}({<_R} \cup
  C[a] \cup \mathsf{po}))$, ranked growth in the lock-free view, and the join
  rule for $\mathsf{acyc}$ with the $\mathsf{wf}$ rule in the lock-free view.
  Checked against `wext`, `wk_ext`, `aw_W`, `wgrow`, `acyc_join_iff`,
  `wf_join_iff`, `wok_join_iff`.
- Notes. Rewritten `w.world`, `w.rworld`, `w.rank` (one rank function
  $\varrho : \mathsf{Point} \to \mathsf{Ord}$, not one per root), `w.rlt`,
  `w.sat`, `w.po`, `w.consts`, `w.facts`, `w.lt`, `w.wf`, `w.lfworld`,
  `w.ext`, `w.grow`, `w.join`, `w.R7`. New `w.rord`, `w.kind`, `w.acyc`,
  `w.models`, `w.wok`. Deleted `w.wfnew` and `w.gennew` (replaced in the
  typing section). Checker findings fixed here: `w_po`, `w_consts`,
  `w_facts`, `world_wf` did not exist (now `po`, `sw_consts`, `sw_facts`,
  `sworld_wf`), `wjoin` was cited in the wrong file (now `swjoin`).
- Syntax caption `syn-points` now introduces $y$ and $z$ as points, which the
  world formulas use.

## Typing

- Section order (layout.js, BLOCKS.md). Old: the lock-free device blocks
  first, then the judgment. New: judgment, contexts, side conditions, then
  the lock-free device blocks. Why: checker (var-before-intro of $\Delta$,
  $\Lambda$, $t$, $\rho$), the device blocks use the notation of the
  judgment. This changes rule 4 of BLOCKS.md, see the questions.
- `t-lf-counters` (new, lock-free only) replaces `t-lf-credits` and
  `t-lf-tickets`. Rows: the counter $a \leq f(o) \leq m$ of an end
  $o : (S@x)^{a}_{m}$, credit, cost, aging, idle ends, tickets, reset by an
  action, $\mathsf{tk}(o) + \mathsf{tk}(\overline{o}) \leq N$, transfer,
  capture, spawn, link. Caption explains why there are two numbers (the
  credit a lower bound the holding thread needs, the tickets an upper bound
  the waiting thread needs) and derives "at most $N$ links per wait" from
  E-Link. Worked example at $N = 4$ in the title note. New notes
  `lfi.counter`, `lfi.link`. Rewritten `lfi.credit`, `lfi.tickets`.
  Why: brief (merge Credits and Tickets into one Counters block),
  instructiveness. Checked against `TSess`, `lgt`, `tsum_ok`, `e_link`,
  `sp_cap`, `sp_tsum` (soup/State.v).
- `t-lf-wf`. Old title "A well-founded world", rows $\varrho_a :
  \mathsf{tree}(a) \to \mathsf{Ord}$ and $\mathsf{wf\_new}\,\rho\,C$, caption
  "lock-free adequacy asks nothing of the world". New title "Ranked worlds",
  rows $\varrho : \mathsf{Point} \to \mathsf{Ord}$, $\mathsf{gen\_new}$,
  $\mathsf{wf}\,W$ at a finite bound, the measure. Caption says that ranks
  fixed once chosen keep the union of the worlds of a run well-founded and
  that lock-free adequacy asks a ranked world. Note `lfi.wf` follows. Why:
  Rocq change (`lf_adequacy` takes `wranked W`). Checked against `wranked`,
  `wchain_lt_wf`, `lf_adequacy`.
- `t-judgment`, `t-contexts`, `r-boxes`, `g-guard`, `t-lf-guard`. Captions
  introduce $H$, $X$, $u$, $f$, $B$, $s$, $\Lambda$, $b$, $p$, $t$ before
  use. The guard formulas write the variable $i$ (old $y$), matching the
  syntax. $K_{\mathrm{act}}$ became $\mathsf{Act}$. Why: checker
  (var-before-intro).
- `r-new`. Old: one rule E-New with the position premise $(\bar\iota, \pi) \in
  \{(\rho, \rho), (\varnothing, x\cdot\kappa)\}$, $\pi = \rho \Rightarrow
  \mathsf{gen\_new}\,\Gamma\,\rho\,C$ and $\pi = x\cdot\kappa \Rightarrow
  \Gamma \vdash C$. New: two rules. E-New at a fresh root asks
  $\mathsf{acyc\_new}\,\Gamma\,\rho\,C$ in the deadlock-free view and
  $\mathsf{new\_ok}_N\,\Gamma\,\rho\,C$ in the lock-free view, and returns
  $\exists^{\bot}\rho.\,C.\,(S@\rho \otimes \overline{S}@\overline{\rho})$.
  E-New-Field returns the plain pair at $x\cdot\kappa$, with no constraint and
  no existential. Below the rules: $\prec^{\rho}_{C}$ (new step),
  $\mathsf{bridge}_C$, $\mathsf{acyc\_new}$, and in the lock-free view
  $\mathsf{gen\_new}$ with finite nonempty sets $Y$ of context points,
  $\mathsf{new\_ok}_N$ and Lemma C ($\mathsf{gen\_new} \Rightarrow
  \mathsf{acyc\_new}$). Caption explains why plain new has two rules, title
  note example from the two-channel cycle. New notes `new.step`,
  `new.bridge`, `new.acyc`, `new.gen`, `new.ok`, `new.lemmaC`. Rewritten
  `E-New.wf`, `E-New.field`, `E-New.facts`, `E-New.dual`, `E-New.tickets`
  (the last two cited "not yet in the Rocq"). Deleted `E-New.pos`. Why: Rocq
  change (`e_new` asks `new_ok N`, `e_new_fld` has no constraint, the old map
  showed (gen-new₁) with single partners). Checked against `e_new`,
  `e_new_fld`, `new_ok`, `acyc_new`, `cbridge`, `new_step`, `gen_new`,
  `gen_new_rel`, `gen_new_acyc`.
- `t-consts`. The row for $\mathsf{new}$ is removed. $\mathsf{new}$ is a term
  former with its own two rules, and the row repeated the old one-rule form.
- `t-subs`. Sub-Ex old: premises $\Gamma, C(\bar\iota) \vdash C'(\bar\iota)$
  and the body, conclusion $\exists^{l} \leq \exists^{l}$. New: added premise
  $l' = l \lor \Gamma, C(\bar\iota) \vdash l' \preccurlyeq T$, conclusion
  $\exists^{l} \leq \exists^{l'}$, in both views. Lock-free Sub-Sess now
  shows the tickets, $(S@x)^{a}_{m} \leq (S'@x)^{a'}_{m}$. New note
  `tp.sub-exlb`, `tp.sub-ex` cites `tsub_open_pack` and drops the claim
  about the same lower bound. Why: Rocq change (sixth run), `sub_ex` takes
  `lb_lower`, `sub_sess` keeps the tickets. Checked against `sub_ex`,
  `lb_lower`, `sub_sess`, `Vrel_heads`, `Vrel_tsub`, `tsub_open_pack`.
- `r-ex`. E-Open showed $\neg\mathsf{unlimited}\,T$ only in the lock-free
  view. It is a premise at every $N$ and is now plain. Note `E-Open.cons`
  cites `cons_gen`, `cons_tree`, `sbv_rejected` in place of the deleted
  `cons_law`. Note `E-Pack.wf` loses its colon. Checked against `e_open`,
  `cons_open`.
- `p-typing`. P-Term old premise $\mathsf{wf}\,W$, new $\mathsf{acyc}\,W$
  (deadlock-free view) and $\mathsf{ok}_N\,W$ (lock-free view). P-Connect old
  $\mathsf{wf}(W_1 \sqcup W_2)$, new $\mathsf{acyc}$ and $\mathsf{ok}_N$ of
  the join. P-Connectⁿ likewise, and its conclusion old $W \sqsubseteq
  (W_1 \sqcup \cdots \sqcup W_n)|_{\mathsf{I}(\Sigma, T)}$, new
  $\mathsf{facts}\,W \subseteq \mathsf{facts}(\ldots)$, because
  `p_connect_n` states inclusion of facts only. Caption old "compares only
  the shared roots of the two worlds", new names the hidden world
  $W|_{\mathsf{I}(\Sigma, T)}$, the join of the interface worlds, and the one
  sentence on Milner's ring (acyclic in pairs, cyclic together, rejected).
  Notes `P-Term.wf`, `P-Connect.wf`, `P-Connect.n`, `tp.pjudg` follow, the
  title note of P-Connect says "check on the joined order" for "strictness
  check". Why: Rocq change (`wok N` in `p_term`, `p_connect`,
  `p_connect_n`). Checked against `p_term`, `p_connect`, `wok`, `ptyped_wf`,
  `p_connect_n`, `ring_rejected`.
- Wording. "self" of a box became "box variable" or "recursive call" in
  typing, syntax, semantics, types, the relation and theorem notes, as the
  paper dropped self.
- Citations fixed: `lbound_of` (deleted) in `side.lb`, `E-Abs.lb`; `tle`
  (now `fle`) in `E-Sub.cost`; `tenv_of` and `e_spawn_lam` cited in the right
  files; `act.refill` no longer says "not yet in the Rocq".

## Semantic typing

- Whole section, notation. Old: the relation, its notes and signatures wrote
  the world of the relation as $W$, $W'$, $W_1$, the same letter as the static
  world. New: $R$, $R'$, $R_1$, as in the types section. The static world $W$
  stays only where a judgment is read at a static world (`sp-lf`, `sp.allR`).
  The rest denotation $\mathsf{den}_{R,B}$ became $\mathsf{den}_{Y,Z}$ to free
  $R$. The order inside the relation hovers to `w.rlt`, not to the static
  order `w.lt`. Why: rigour (one letter, one meaning) and the Rocq change that
  splits static worlds from worlds of the relation.
- `e-rel` (`e-body`). Old: $\forall e.\ e \in E_0$ and the clauses only at
  $\alpha > 0$. New: the clauses at every index. Note `E.zero` deleted. Why:
  faithfulness, `Etop n = Eind n`, and a term at index $0$ still meets its
  stop and ready clauses and its free steps ("A level with nothing below it
  obliges no step of positive cost"). The old note also cited the missing
  `Erel_0`. Checked against `Ebody`, `Eind`, `Etop`, `at_cost_E`.
- `p-rel` (`p-body`). Old: $p \in P_{n+1}$ with a finite level. New: row
  $\forall p.\ p \in P^{R}_0$ and the clauses at $\alpha > 0$, new note
  `P.zero`. Caption says so. Checked against `Ptop`, `Pind`, `Pbody`.
- `fu` (`fu-def`). Old: $\forall e.\ e \in F^N_0$ and clauses at $\alpha >
  0$. New: clauses at every index, note `fu.zero` deleted (it cited the
  missing `mk_flevel`). Checked against `FLevA`, `mk_flarg`, `Fdef`.
- `sj-all` (`sp-lf`). Old: $\Sigma \Vvdash_W p : T \iff \exists N \in
  \mathbb{N}.\ \forall R \vDash W.\ \forall \alpha.\ \exists a.\ \ldots$. New:
  $\Sigma \Vvdash^{N}_W p : T \iff \forall R \vDash W.\ \mathsf{ranked}\,R
  \Rightarrow \forall \alpha.\ \exists a.\ \ldots$, the bound a parameter.
  Caption adds that the deadlock-free judgment at a static world reads strict
  models. Notes `sp.lfsem`, `sp.allR`, `sp.exists-before-forall` follow.
  Checked against `lf_sems`, `lf_sem`, `sem_ptyped_sw`.
- O-New notes `O-New`, `O-New.grow`. Old: the creation ranks each new tree,
  and "$R'$ keeps every rank". New: in a strict world the creation adds the
  facts of $C$ and closes transitively, in a ranked world it ranks the tree.
  Cites `Erel_new_acyc`, `Erel_new_any`. Notes `P.strict`, `P.clauses`,
  `rd.above-offered` drop "ranked" where the world is of either kind.
- Citations that said "not yet in the Rocq" now name the Rocq: `fu.step`
  (`Fdef`, `Fobl`), `F-New` and `F-New.cnew` (`f_new`, `cnew`), `fu.fsem`
  (`fsem`), `sp.exists-before-forall` (`exist_prop`, `lf_sem`), `sp.next`
  (`lf_next`, `own_next`, `world_next`), `sr.FE` (`FuelE`, `FLevA`),
  `rel.atcost` (`oadd`). Missing names fixed: `FLev` (now `FLevA`), `lb_le`
  (now `lbx_le`).
- Captions `sr-reading`, `v-rel`, `e-obl`, `rd`, `p-rel`, `sj-all`, `fu-vs`,
  `fu`, `fu-obls` introduce $V$, $\Theta$, $w$, $\pi$, $O$, $h$, $\gamma$,
  $G$, $Y$, $Z$, $\Phi$, $d$, $g$. `sr-reading` says that the deadlock-free
  relation reads strict worlds and the lock-free threads ranked ones. Why:
  checker (var-before-intro) and the Rocq change on worlds.

- `sr-ord` (new block, after the reading guide). Ordinals as Brouwer trees,
  their order and its well-foundedness, $\beta + c$, $\mathsf{osfix}$, and in
  the lock-free view the existential property with its EM and FC hypotheses.
  New notes `ord.ord`, `ord.lt`, `ord.wf`, `ord.add`, `ord.fix`,
  `ord.exprop`. Why: brief (transfinite indices `ord`, `olt_wf`, `osfix`,
  `exist_prop` were cited only in passing, `olt_wf` nowhere). Checked against
  relation/Ord.v and relation/ExProp.v.
- Notes `O-Spawn.transfer` and `fu.oneclock` deleted. No formula used them
  (gen.js and the checker reported them unused).

## Theorems

All theorem blocks were rewritten against the statements on this branch. The
common changes: the deadlock-free, live, hidden and n-ary results lost their
excluded-middle hypothesis (DF over acyclic worlds), the lock-free results
take excluded middle and functional choice (old display "EM ∧ AC", now
"EM ∧ FC", note `th.ac` retitled), semantic judgments name their world ($R$
for a world of the relation, $W$ for a static world), and the hidden forms
are the headline.

- New semantic notations used here, defined in the semantic block `sj` and
  `sp-lf`: $\Sigma \vDash_W p : T$ (all strict models, `sem_ptyped_sw`),
  $\Sigma \vDash^{h}_W p : T$ (some acyclic whole world hides to $W$,
  `sem_ptyped_h`), hiding $W' \rightsquigarrow_I W$ (`hides`), and
  $\Sigma \Vvdash^{N,h}_W p : T$ (`lf_sems_h`). New notes `sj.sw`, `sj.h`,
  `sj.hides`, `sp.lfsemh`.
- `th-chain`. Old rows: `fundamental_proc` to $\Sigma \vDash_W$, `adequacy`,
  `live_fundamental`, `lf_fundamental`, and `EM ∧ AC ∧ ∅ ⊪_W p ⇒ lock_free`
  by `lf_adequacy`. New rows: `fundamental_proc_h` to $\vDash^{h}_W$,
  `adequacy_h`, `live_fundamental_ranked` (EM, any model), `fsem_of_cost`,
  `lf_fundamental_h` (EM, guard) to $\Vvdash^{N,h}_W$, and `lf_adequacy` at a
  ranked $R$ with no classical hypothesis. Caption says where excluded middle
  enters. Checked against those names.
- `th-adeq`. Rows `adequacy` (at $R$), new `adequacy_h`, `lf_adequacy` and
  `lf_thread_progress` (old premise EM ∧ AC, now $\mathsf{ranked}\,R$, as the
  Rocq states), new `lf_sems_adequacy` (EM, FC, a well-formed well-founded
  static world). New notes `th.adequacy-h`, `th.lf-sems-adequacy`.
- `th-fund-proc`. Rows `fundamental_proc_h`, new `live_fundamental_proc_h`,
  `lf_fundamental_h` with EM, finite $N$ and the guard (old row
  $\Sigma \Vdash^{N}_W p : T \Rightarrow \Sigma \Vvdash_W p : T$ without EM).
  New note `th.live-fundamental-proc`.
- `th-compose`. Rows over $R$, new `sem_p_connect_sw` at static worlds,
  `lf_p_term` with EM and the premises $\mathsf{pterm}_N$ (new note
  `th.ptermprem`), `lf_p_connect` with the bound $N$. New note
  `th.sem-p-connect-sw`. `th.sem-p-connect` drops "ranked".
- `th-sound`. Rows `soundness_h`, new `connect_n_soundness` (acyclic join),
  new `live_soundness_h`, `lf_soundness_h` (EM, FC, finite $N$, guard), new
  `connect_n_lf_soundness`, `fair_run_exists` (now lock-free only, with
  $\mathsf{DC}$ hovered to the new note `th.dc`), `lock_free_padovani`. New
  notes `th.connect-n`, `th.lf-connect-n`, `th.live-soundness`, `th.pcomps`.
  Old caption "deadlock free in every strict world" and "lock free in every
  strict and well-founded world" replaced.
- `th-terms`. `soundness_source` asks a well-formed acyclic world (old: no
  world premise, and the note said "strict $W$"); `lf_soundness_source` asks
  EM, FC and a well-founded world. The four term fundamental theorems read
  each strict $R \vDash W$; new row `live_fundamental_ranked`. Bind over $R$.
  New note `th.live-fundamental-ranked`.
- Notes rewritten: `th.adequacy`, `th.lf-adequacy`, `th.lf-thread-progress`,
  `th.fundamental`, `th.fundamental-typed`, `th.live-fundamental`,
  `th.live-fundamental-typed`, `th.fundamental-proc`, `th.lf-fundamental`,
  `th.sem-p-connect`, `th.lf-p-term`, `th.soundness`, `th.soundness-source`,
  `th.lf-soundness`, `th.lf-soundness-source`, `th.em`, `th.ac`, `th.Prel`,
  `th.Erel`, `th.Vrel`, and their signatures. `th.em` old "Without it ... the
  lock-free judgment needs the choice $\chi$ before the index again" (χ is
  gone), new names the two uses of excluded middle.

## Examples

- New `ex-copycat` (Copycat, a forwarder at independent points). The five
  facts, P-Term, identity expansion (with its condition on the root of $y$),
  partner ∥ fwd ∥ partner deadlock free, the η-expanded payload at $y\cdot 0$,
  the schema over protocols of unit messages, and the rejected forwarder
  ring. Checked against `fwd_term`, `fwd_expand`, `fwd_config_deadlock_free`,
  `fwdh_term`, `fwdp_term`, `ring_rejected`, `ring_rejected_full`.
- New `ex-milner` (Milner's ring). Hidden worlds acyclic in pairs
  (`ring_pairs`), cyclic together (`ring_cyclic`, now stated as
  ¬ `sacyc`), rejected (`ring_rejected`), the acyclic variant typed by the
  n-ary connect and deadlock free (`ring_typed`, `ring_df`), the two-channel
  cycle (`cyc2_rejected`, `cyc2_rejected_h`).
- New `ex-forkjoin` (recursive fork-join with replies). Typed at $N = \infty$
  under `acyc_new` and deadlock free with no classical hypothesis
  (`fjr_acyc`, `fjr_dftyped`, `fjr_deadlock_free`). One round, factorial and
  Fibonacci named. The finite-bound rejection is not claimed as a theorem,
  only that `gen_new` asks a well-founded order on the tree.
- New `ex-shared` (private constants and hiding). `opposite_clash`
  (¬ `sacyc` of the whole worlds), `opposite_compose`, `opposite_df`,
  `shared_hidden`, `shared_not_cut`, `fact_needs_zero`.
- New `ex-gennew` (creations with exits). The two-entry program with the set
  $\{\rho\cdot 2, \rho\cdot 3\}$ (`te_gen`), the two-upper-bound program
  (`tu_gen1`), both typed and deadlock free, both rejected after the
  creation under each `wf_new` constraint (`te_rejected_wf_new`,
  `tu_rejected_wf_new`).
- New `ex-sinst` (why session types are contractive), no verdict badge.
  `typed_sinst_false`, `ss_var_guard`, `typed_sinst`, `inv_chan_sty`.
- `ex-flag`, `ex-flagpair`. "P-Connect asks a strict join" and "a
  well-founded join" became "an acyclic join". Checked against `p_connect`,
  `sbv_rejected`.
- `rx-chain`. Old: "$\mathsf{wf\_new}$ forbids it ... lock-free soundness
  assumes a well-founded world", citation text "argued in
  docs/redesign/check-layers.md ...". New: at a finite bound E-New asks
  `gen_new`, the rejection is argued and not mechanized (said in the text),
  citation `gen_new`, `new_ok`, `fj_wait_needs`. Why: Rocq change and the
  checker (three reason-missing errors came from the old citation text).

## Questions for the author

Author's answers, 2026-11-22. Keep $R$ for relation worlds and $i$ for term variables. State the lock-free rejection of recursive fork-join as argued. Whitelist "cost" in lint-map.py and the mapkit checker (done, mapkit 4694de6). Leave the three overview tables for Phase C.

1. Device blocks after the judgment? Recommended: yes, as done. The
   lock-free blocks (counters, guard, ranked worlds) used $\Delta$,
   $\Lambda$, $t$ and $\rho$ before the judgment defined them. Rule 4 of
   BLOCKS.md is changed to match. The alternative keeps them first and
   defines the notation in their captions.
2. Worlds of the relation written $R$ throughout? Recommended: yes, as done.
   The Rocq uses one letter for both kinds, the map now uses $W$ for static
   worlds and $R$ for worlds of the relation, and the rest denotation moved
   from $\mathsf{den}_{R,B}$ to $\mathsf{den}_{Y,Z}$.
3. Term variables written $i$? Recommended: yes, as done. $x$ clashed with
   points in E-Var next to E-Chan. $i$ also names injections and threads,
   where it is a subscript or a thread name.
4. Numeric payload binders? Recommended: keep them. The brief lists "numeric
   payload indices" as removed, but `SSnd (m : nat) (T : ty)` and
   `payload_at` still place payload variables at $x\cdot 0, \ldots,
   x\cdot(m{-}1)$ on this branch. The map follows the Rocq. The fields
   $\sigma.\kappa$ of the paper would be a planned deviation.
5. Full judgment as a block? Recommended: no. The hidden judgment is the
   headline, and the full one appears in notes (`tp.pjudg`,
   `th.fundamental-proc`) and in the definition of $\vDash^{h}_W$.
6. Lock-free rejection of recursive fork-join? Recommended: state it as
   argued, as done. The map says only that `gen_new` asks a well-founded
   order on the tree. Proposition 7 is on paper.
7. Overview tables with words (`sr-reading`, `fu-vs`, `soup`)? Recommended:
   leave them. They cause 40 of the 53 prose-in-formula warnings. Turning
   them into proof-map tables needs a converter change on mapkit.
8. "cost" as metaphor? Recommended: whitelist it in lint-map and the private
   checker. It is the Rocq term for step costs and arrow costs, and it
   accounts for about 40 of the metaphor hits.

## Things the map still forgets

- The process-level erasure $\mathsf{fptyped}\,(\mathsf{Some}\,N)
  \Rightarrow \mathsf{fptyped}\,\mathsf{None}$, which the Rocq does not have
  either (report of 2026-11-22). `cons_acyc` is likewise open.
- `live_sub_df` (the live judgment implies the deadlock-free one under EM
  and FC) is cited nowhere.
- `wfit`, the world condition of `typed_sem`, appears only in citations.
- `typed_ren`, `fptyped_ren` and the renaming of private constants have no
  formula, only the prose of the hiding notes.
- `fj_wait_needs` and `cl2_needs` (every typing of close a; close b asks the
  point of a below the head of b) would make a good lemma block for the
  rejection arguments.
- Measured boxes (branch redesign-mbox) are left out, as instructed.
- Rocq comments that are stale, noted and not changed. relation/Ord.v says
  "The relation and fuel still use the natural-number fixpoint of
  relation/Sfix.v", but Sfix.v is gone. The report of 2026-11-22 lists
  comments in relation/Readiness.v, relation/Relation.v and compat/*.v that
  say "ranked world" where the world has either kind.
- Checker false positives that remain: subscripts such as $\kappa_{DF}$,
  $\kappa_L$ and $\Theta_B$ count as the variables $D$, $L$, $B$, the rule
  name P-Connect$^{n}$ counts as the bare word Connect, and notational
  renames (51 rename-undeclared) need `renamed` deviations in the overlay,
  which lives on mapkit.

## Checker counts before and after

Before, at 1401e2d. `node check.js` on the converted map with the overlay and
extension of demo/, `--root v2`.

| Category | Before | After |
|---|---|---|
| errors | 19 | 0 |
| name-missing | 13 | 0 |
| name-elsewhere | 3 | 0 |
| reason-missing | 3 | 0 |
| warnings | 729 | 595 |
| var-before-intro | 106 | 6 |
| prose-in-formula | 66 | 53 |
| rename-undeclared | 45 | 51 |
| bare-word | 10 | 10 |
| prose:every/any/all | 319 | 305 |
| prose:metaphor | 175 | 164 |
| prose:hedge | 6 | 0 |
| prose:colon | 1 | 0 |
| prose:pronoun ending | 1 | 1 |
| prose:sentence > 35 words | 0 | 5 |
| info | 11 | 8 |

gen.js before: 0 errors, no DF-LEAK, unused notes `O-Spawn.transfer` and
`fu.oneclock`. lint-map.py before: 163 metaphor, 319 every/any/all, 1 pronoun
ending, 0 elsewhere.

After, at the last commit of this branch. The six remaining var-before-intro
are the subscript false positives ($D$, $L$ from $\kappa_{DF}$, $\kappa_L$).
rename-undeclared rose by six because the new notes show $\mathsf{tc}$,
$\mathsf{po}$ and $\mathsf{Point}$ next to the Rocq names they cite. The five
long sentences are counted across a `\annp{...}` boundary, where the
checker does not split. The map grew from 70 blocks, 525 notes and 17
examples to 70 blocks, 556 notes and 23 examples (two blocks merged into
the counters block, one ordinal block added).

gen.js after: 0 errors, no DF-LEAK, no unused note, no dead link. lint-map.py
after: 164 metaphor, 305 every/any/all, 1 pronoun ending, 5 sentences over
35 words, 0 semicolons, 0 coined words. MathJax was not run (the checker
needs `--mathjax` with `mathjax-full`, which is not installed), KaTeX in
gen.js renders every block, note and caption.

## Notation change, end types

The author decided on 2026-11-22 to write the end type $(S@x)^{a}_{m}$ as
$S_x^{a,m}$. The point goes in the subscript, and the credit and then the
tickets go in the superscript. The deadlock-free view writes $S_x$. A point
with a decoration reads $S_{x^{+}}$ or $S_{\overline{x}}$, using the
$\overline{x}$ of the rest of the map. A protocol that is not one letter is
parenthesized, as in $(!\ast.\mathsf{Close})_{\rho}$. Closures keep
$(T \multimap [c]\,U)^{a}$.

- All `@` occurrences in gen/*.js are gone: formulas, captions, notes,
  signatures, semrel (V-Sess is now $o \in V\llbracket\{o \mapsto
  S'_x\} \vdash S_x\rrbracket$), and the code of the examples
  (`Close_ι`, `(?∗.Close)_ι‾`, `Sch_ι₁`). A script rewrote the plain
  cases. The cases below were renamed by hand. A primed protocol is written
  $\{S'\}_x$ in the TeX, so that a superscript after it is not a second
  superscript.
- Notes `ty.sess`, `ty.credit`, `ty.tickets` and the counter row of
  `t-lf-counters` describe the notation once.
- gen.js. The superscript $^{a,m}$ after a point subscript is coloured as a
  lock-free annotation (`ENDSUP`), and the DF-LEAK check also rejects an
  uncoloured $_x^{\ldots,\ldots}$.

Clashes, where a subscript on the protocol would stack on the point:

1. Actions (E-Send, E-Recv, E-Close, the constants table, the signatures of
   the constants, the unfold notes). The type before the action, old $S_0$,
   is now $S$. Its continuation, old $S$, is now $S'$.
2. Choices (E-Select, E-Branch, O-Select, O-Branch, the constants). The
   branches, old $S_1, S_2$, are now $S', S''$. The chosen continuation, old
   $S_i$, is now $(\mathsf{if}\ i\ \mathsf{then}\ S''\ \mathsf{else}\ S')$,
   as in the Rocq, with a new note `sty.choice`. The branch points, old
   $x\cdot\kappa_1$ and $x\cdot\kappa_2$, are now $x\cdot\kappa_{\mathsf{false}}$
   and $x\cdot\kappa_{\mathsf{true}}$, as `bra_pt` and the syntax block state.
3. O-Link and its note: old $S_1, S_2$, now $S, S'$.
4. The head notation `sr.head`: old $\Theta(o) \doteq S@x$ with $\Theta(o) =
   S_0@x$, now $\Theta(o) \doteq H_x$ with $\Theta(o) = S_x$ and
   $\mathsf{unfold}\,S = H$.
5. Example types in notes: $S_1@\iota \otimes S_2@\kappa$ became $S_{\iota}
   \otimes S'_{\kappa}$ (`ty.prod`, `ty.box`, typing notes), $S_a@\rho$
   became $S''_{\rho}$ (`tj.Delta`), $S_1@x\cdot\kappa_1$ in a V-Sum note
   became $S_{x\cdot\kappa_{\mathsf{false}}}$.
6. Example code: `S1@ι ⊗ S2@κ` became `S_ι ⊗ S′_κ` (client and server), and
   in the contractivity example `s₀`, `s₁` became `s`, `s′` in code and
   prose.

Left unchanged, because they are no end types: the session-type grammar
$\oplus(S_1, S_2)$, and fuel entries $S^{f}_{m}$, whose subscript is the
tickets. Question for the author: write fuel entries as $S^{f,m}$ too?
Recommended yes, because a subscript now reads as a point.

Checks: gen.js 0 errors, no DF-LEAK, no unhovered symbol. lint-map.py 9
metaphor, 305 every/any/all, 1 pronoun ending, 5 sentences over 35 words, 0
elsewhere. Screenshots of types, typing and semantic typing in both modes
render every changed formula.

Follow-up, same day. Fuel entries are written $S^{f,m}$ (counter, then
tickets), as end types carry credit and tickets, and so are the examples
$S^{3,3}$, $\overline{S}^{m_2,m_2}$, $P^{f,m}$, $\mathsf{Close}^{2,2}$ and the
interface lift $\Sigma^{N/2,N/2}$. The session-type grammar, duality and the
choice notes write $\oplus(S', S'')$, $\&(S', S'')$ and $S'.S''$ for the old
$S_1, S_2$. The fuel rules F-Send, F-Recv, F-Close and F-Choice rename their
$S_0$ to $S$, its continuation to $S'$, and the chosen branch to
$(\mathsf{if}\ i\ \mathsf{then}\ S''\ \mathsf{else}\ S')$, and the remaining
$S_0$, $S_i$, $S_1$, $S_2$ in notes and signatures are gone. A grep for
`S_<digit>`, `S_0` and `S_i` in gen/*.js finds nothing, so a subscript on a
protocol always names a point. gen.js 0 errors, no DF-LEAK. lint-map
unchanged.

## Coverage sweep

Branch redesign-map after the fast-forward to 6688230. Swept every file of
v2/examples and every Theorem and Corollary of static/, soup/, lockfree/,
relation/Adequacy.v, cost/CostFund.v and compat/LiveDF.v (150 results; there
is no soundness/ directory). After the sweep each of the 150 is cited by the
map. Measured boxes are left out.

Added, theorems section:
- `th-adeq`: rows `live_sub_df` (EM, FC, a result type with no end and no
  box, with the new note `th.boxfree`), `lf_sems_h_adequacy`, and
  `thread_progress` (lock freedom, no internal divergence and
  `links_restricted` give progress of each thread, note `th.linksr`).
- `th-terms` (fundamental theorems for terms): a first row defining
  $\mathsf{fit}_N\,R$ (`wfit`), strict, or ranked at a finite bound under
  EM in the lock-free view, with the note saying that `typed_sem` reads
  every model that fits.
- `th-fund-proc`: rows `ptyped_full`, `fptyped_ptyped` and
  `typed_ren`/`fptyped_ren`, with a note `tp.fpjudg` for the full judgment
  $\Sigma \vdash^{N,\mathsf{full}}_W p : T$.
- `th-compose`: row `lf_soup_term`, semantic P-Term in the lock-free
  judgment from relation and fuel, with the channel premises
  $\mathsf{chan}_N$ (note `th.chprem`). `soup_connect` cited in its note.
- New block `th-inv` "What two closes ask", merged into the lemmas about
  terms: `cl2_needs` and `fj_wait_needs`.

Added, examples:
- `ex-cs-split` (LFClientServerSplit: `cs_split_lock_free`,
  `cs_split_typed`, `cs_split_lock_free_h`).
- `ex-tree` (TreeTopo: `tt_deadlock_free`, `tt_dead_world_wf`; the static
  derivation is stated as not mechanized).
- `ex-link` (LFLink: `lk_new`, `lk_typed`, `lk_ok`).
- `ex-forkjoin` now says why the recursive program has no lock-free typing
  by this route: each typing of close c; close w asks the point of c below
  the dual point of w at every bound (`fj_wait_needs`), the child forces the
  same box at that dual point, so the box hypothesis must descend in each
  round, and `gen_new` admits no infinite descent. The last step is marked
  argued and not mechanized. Cites `fj_term`, `fct_term`, `fib_term`.
- `ex-flag` cites the plain program (`sb_thread_E`, `sb_deadlock_free`),
  `sbv_rejected_h` and `cl2_needs`. `ex-ring3` cites `ring_not_df` and
  `cyc2_not_df`. `ex-copycat` cites `fwd_config_typed`, `fwdh_config_typed`,
  `fwdh_config_deadlock_free`, `fwdp_sem`, `fwd_needs`.

Checked and already present: `sbv_thread_E`, `sbv_deadlock_free`,
`sbv_rejected`, `Tbad_not_cons` (ex-flag and E-Open), `opposite_df`
(ex-shared), `fp_unrealizable` and `fp_gate` (ex-flagpair), GenNew
(ex-gennew), SinstStuck (ex-sinst).

Cited only, on purpose:
- `typed_weaken_head`, `dftyped_rename`, `dftyped_weaken_head` (structural
  lemmas behind the admissible E-Weak, in the r-admis citation).
- `idle_dual` (in the note of $\mathsf{Skip}$).
- `lfsoup_isteps` (run construction, in the note of the lock-free process
  relation), `thread_acc` (in the thread-progress note).

Skipped on purpose: examples/Tools.v, Tools2.v and LFTools.v, which are
libraries of tactics and helper lemmas with no result of their own.

Checks: gen.js 0 errors, no DF-LEAK. Checker 0 errors, 448 warnings (the
seven var-before-intro are the subscript false positives of κ_DF and κ_L).
lint-map 9 metaphor, 308 every/any/all, 1 pronoun ending, 5 long sentences.
Screenshots of the theorems in both views and of the examples render.

## Classification

Every result, block, note and example is now classified as deadlock freedom
or lock freedom, and the guarded results at $\kappa_L$ (Rocq `live_*`) count
as lock freedom.

- **Mode `live` removed.** Source mode lists, the `live` variant of the type
  grammar, the `live` verdicts of examples and the "typed and guarded, live"
  badge of the page are gone. gen.js no longer maps `live` to `lf`, and it
  now fails on any mode other than `df` and `lf` (BAD-MODE).
- **Examples.**
  - `ex-ring` (GrowRing). Old lead "A ring of threads that grows forever is
    lock free" under a deadlock-free badge in the DF view. New: deadlock free
    in DF, and the lock-free claim only in the LF view. GrowRing proves
    `rg_dftyped`/`rg_typed` (DF, deadlock freedom through soundness for a
    single program) and `rg_lftyped`, `rg_lock_free` (LF).
  - `ex-forkjoin`. The sentences on the missing lock-free typing are
    lock-free-only.
  - `ex-sinst`. "A session variable does not guard" became "does not make a
    recursion contractive", so the word guard means only the lock-free guard.
  - LF badges showed half the bound. The Rocq types the processes at
    `exists 6` (client and server), 4 (cycle, channel between box
    arguments, factory), 8 (channel acting several times, growing ring) and
    6 (controller). The badges now show these values.
  - Checked and unchanged: examples proved only deadlock free (copycat,
    three-thread ring, fork-join, private constants, creations with exits,
    flag, two flags, tree) say lock free nowhere in the DF view. LF-only
    examples (two closes, guard, forwarder, controller, split client and
    server, link, the four rejections) stay out of the DF view.
- **Theorems and notes.**
  - The guarded results (`live_soundness_h`, `live_fundamental*`,
    `live_sub_df`) sit in lock-free rows only, as before.
  - Reader prose no longer says "live" or "liveness": "the live judgment"
    became "the semantic judgment at $\kappa_L$", "Live soundness" became
    "Soundness without internal divergence", "Live fundamental theorem"
    became "Fundamental theorem at $\kappa_L$", "live arm" became "running
    arm", "the live table" became "the lock-free table", and the remaining
    mentions in `ct.table`, `sty.seqv`, `ty2.stydf`, `w.kind`, `w-world`,
    `guard.proc`, `th.boxfree`, `th.em`, `aK` and the fuel action were
    reworded.
  - The full judgment and $\mathsf{fit}$ no longer show the bound $N$ in the
    DF view (`\vdash^{\mathsf{full}}_W`, $\mathsf{fit}\,R$).
- **The opposite direction.**
  - gen.js treats sentences about lock freedom, $\kappa_L$, ranked worlds,
    fuel, the guard, excluded middle, functional choice, counters and
    internal divergence as lock-free prose in DF-reachable notes, captions
    and block title notes. The DF-LEAK check fails on such words left
    uncoloured.
  - New note `w.strict` for the strict worlds of the DF view. The DF
    formulas hovered `strict` to the note on kinds, which explains ranks.
  - $\kappa_{\mathsf{false}}$, $\kappa_{\mathsf{true}}$ hovered to the guard
    note through the automatic hover of `\mathsf{true}` and `\mathsf{false}`.
    The automatic hover is removed and the labels hover to `sx.kappai`.
  - `syn-ends`, `ty.arrow`, `ct.link`, `ct.takek` keep their lock-free part
    (counter, cost and credit, the table $\kappa_L$) in lock-free sentences.
  - Signatures write $\mathbb{N} \cup \{\infty\}$ for the Rocq sort `fuel`,
    which read as the lock-free fuel.

Checks: gen.js 0 errors, no DF-LEAK, no BAD-MODE. lint-map: 9 metaphor, 308
every/any/all, 1 pronoun ending, 17 sentences over 35 words. The rise from 6
is an artifact of lint-map, which removes `\annp{` but keeps the closing
brace, so it no longer splits sentences at a lock-free sentence boundary.
Screenshots of theorems and examples in both views checked.
