# Paper audit against Rocq (phase 5)

Every definition, rule, theorem, lemma and example claim of `paper/*.tex`
checked against the Rocq statement it cites or describes, on branch
`paper-phases`. Line numbers are approximate (taken during the audit).
"Fixed" means the paper was changed in commit "paper: phase 5 audit
fixes against the Rocq statements". No Rocq file changed in this phase.

## 2-calculus.tex

| # | claim | Rocq | verdict |
|---|-------|------|---------|
| 1 | Fig. 1 syntax of constants, values, terms | `konst`, `expr`, `is_val` | matches (choice constants belong to §4) |
| 2 | Fig. 2 labels and evaluation contexts | `slabel`, `tlabel`, `tstep` | matches |
| 3 | T-Act-App … T-Act-Link, T-Act-Ctx | `head_step`, `tstep` | matches |
| 4 | fc, sent, unordered link label | `subjs`, `sentc`, `upair_comm`, `HeadLink` | matches |
| 5 | process = finite set and multiset of closed terms | `proc` | mismatch, not fixed: `proc` does not require closed terms. Harmless, every reachable process from a closed program is closed |
| 6 | P-Act-Session/Beta/New/Spawn/Msg/Close/Link | `proc_step` | matches |
| 7 | Harmony | `harmony` | matches |
| 8 | irred, terminated, safe, deadlock free | `irred`, `pirred`, `terminated`, `safe`, `deadlock_free` | matches |
| 9 | sync has exactly one reduction sequence, ends terminated | `sync_deadlock_free` | mismatch: false (two independent steps interleave) and not proved. Fixed: now only "deadlock free" |
| 10 | cycle has exactly one reduction sequence | `cycle_deadlock_free` | mismatch as #9. Fixed |
| 11 | blocked reaches an irreducible non-terminated process, not deadlock free | `blocked_main` (definition only) | mismatch: no theorem. Fixed: the pure steps are mentioned and the text says the deadlock is not mechanized |
| 12 | points, facts, constraints, roots | `pname`, `point`, `fact`, `bcs`, `pn_root` | matches |
| 13 | types and session types | `ty`, `sty`, `lbound` | presentation: Rocq writes `!T.S` as `SSeq (SSnd m T) S`; §4 introduces `;` |
| 14 | duality | `dual` | matches |
| 15 | point substitution, payload substitution | `pt_inst`, `pinst_ty`, `pup`, `payload_at` | matches |
| 16 | arrow ℓ absent or point, ∃ also ⊥ | `TLolli`, `TEx` | matches |
| 17 | Def. payload mentions only self[j] | `payload_at`, `pscoped` | minor: `pscoped` also admits constants; source programs have none. Not changed |
| 18 | Remark: no rule enforces Def. payload, `payload_pinst` unconditional | `kscoped`, `t_const`, `payload_pinst` | mismatch: E-Const checks `kscoped`, the lemma assumes `pscoped`. Fixed |
| 19 | future is a finite set of nodes | `sfuture` | mismatch: at most one future variable. Fixed |
| 20 | source program Θ = ∅, Γ without constants | `styped` | matches |
| 21 | A-rules (aliasing) | `seqs` | matches |
| 22 | O-rules (order) | `fl` | matches |
| 23 | heads, ℓ ≤ N, u ≺ F | `heads`, `lb_below_hb`, `ub_below_s` | matches |
| 24 | structural rules not mentioned in the body | `t_weak`, `t_contract` | omission. Fixed: pointer to the appendix |
| 25 | E-Unit, E-Var | `t_unit`, `t_var` | matches |
| 26 | E-Const asks p⃗ known | `t_const`, `konst_ty` | mismatch: only force asks it. Fixed |
| 27 | E-Abs | `t_abs` | matches |
| 28 | E-App, E-Pair, E-LetPair, E-Let*, E-Inj, E-Case | `t_app` … `t_case` | matches |
| 29 | E-Conv | `t_conv`, `steq` | matches |
| 30 | E-Exp | `t_exp` | matches for points; session instances are §4 |
| 31 | E-Pack | `t_pack` | mismatch: missing `skn` premise. Fixed ("p⃗ known") |
| 32 | E-Open | `t_open` | mismatch: missing `¬ unlimited T`. Fixed |
| 33 | known points | `skn` | matches |
| 34 | bounds of send/recv/close/link/spawn | `konst_sig` | matches |
| 35 | signatures figure | `konst_sig`, `KTNewEx` | matches |
| 36 | creation constraint acyclic: Γ,C ⊬ p ≺ p | `cc_ok`, `cc_acyclic_at` | mismatch: Rocq asks acyclicity relative to Γ. Fixed |
| 37 | placement between u and v needs Γ ⊢ u ≺ v | `t_newfresh_lh_open` | matches |
| 38 | `let ⟨c,d⟩ = new` unfolds through six rules | `t_new_open`, `let_new` | matches |
| 39 | C₀ against ∅ is acyclicity of C₀ | `c0_creation_ok`, `c0_acyclic` | mismatch: also no outer point. Fixed |
| 40 | delegation example | `deleg_typed`, `deleg_deadlock_free`, `dl_C`, `dl_rank` | matches |
| 41 | delegation priority gap `!⁰.?¹⁰` | `Sdel` | mismatch: the carrier is send then close. Fixed: send at 0, close at 10, delegated send and close at 1 and 2, any finite delegated session of at most nine actions fits, unbounded ones fit no gap |
| 42 | optional channel example | `some_deadlock_free`, `none_deadlock_free`, `some_swapped_deadlock_free` | matches |
| 43 | request/reply example | `rr_typed`, `rr_deadlock_free`, `rq_C` | matches |

## 3-logical-rel.tex

| # | claim | Rocq | verdict |
|---|-------|------|---------|
| 1 | Def. world | `world`, `world_wf` | matches |
| 2 | strict = < irreflexive | `strict` | mismatch: also well formed. Fixed |
| 3 | extension, fresh extension | `wext`, `wext_fresh` | matches |
| 4 | creation constraint realized by fresh extension | `wext_cc` | matches |
| 5 | join, restriction | `wjoin`, `wrestrict` | matches |
| 6 | quantifiers "∀ W′ ⊑ W" in V-Abs, V-Box, O-Recv, Q-Recv, semantic judgment | `wext W W'` | mismatch: direction reversed against Def. extension. Fixed to W′ ⊒ W |
| 7 | amalgamation | `amalgamation` | matches |
| 8 | fresh extension theorem | `fresh_extension` | matches |
| 9 | readiness | `ready_t`, `ready_p`, `below_rest`, `offered_t` | matches |
| 10 | environments, split | `senv`, `tenv`, `tenv_comp` | matches |
| 11 | V rules | `Vdef`, `Vfun` | matches (session instances of V-Box are §4) |
| 12 | V-Const at any T | `Vfun` | minor: Rocq only at arrows; every signature is an arrow. Not changed |
| 13 | E-Zero, E-Intro | `Edef`, `Efuel` | matches |
| 14 | O-New freshness | `Eobl` | mismatch in scope of σ. Fixed |
| 15 | O-Beta … O-Link | `Eobl` | matches |
| 16 | cost function | `tcost`, `scost` | matches for core labels |
| 17 | P-Zero, P-Intro | `Pdef`, `Pfuel` | matches |
| 18 | Q-Tau | `Pobl`, `Ptau_case` | matches |
| 19 | Q-Recv | `Pobl`, `recv_ok` | mismatch: `recv_ok` premise missing. Fixed (premise and one defining sentence) |
| 20 | Q-Send | `Psend_case`, `send_split` | mismatch: disjointness premise missing. Fixed |
| 21 | Q-Close, Q-Link | `Pclos_case`, `Plink_case` | matches |
| 22 | V-Abs/V-Box side conditions are the only syntactic ones | `Psend_case` | mismatch: Q-Send has one too. Fixed |
| 23 | grounding substitutions, semantic judgments | `grounding`, `sem_typed`, `sem_ptyped` | matches |
| 24 | wf is two syntactic conditions | `term_wf` | incomplete. Fixed: all three conditions |
| 25 | `Prel_steps`, `Prel_safe`, adequacy | same | matches |
| 26 | compositionality table, 18 rules | `sem_typed_*`, `Prel_term`, `Prel_connect` | matches |
| 27 | comp. E-Abs hypothesis | `sem_typed_lam` | mismatch: Rocq quantifies over W′ and F′. Fixed |
| 28 | comp. E-Exp hypothesis | `sem_typed_box` | mismatch as #27 plus instances. Fixed |
| 29 | comp. P-Connect in one world | `conn_all`, `Prel_connect` | mismatch: one-world version is `conn_all`. Fixed, both cited |
| 30 | fundamental property | `fundamental`, `fundamental_proc` | matches |
| 31 | `soundness` before `soundness_source` | `soundness`, `soundness_source` | matches, order correct |
| 32 | every example goes through the fundamental property | examples | matches |

## 1-intro.tex, 5-formalization.tex

| # | claim | Rocq | verdict |
|---|-------|------|---------|
| 1 | every result carries a Rocq reference | all theorem environments | matches |
| 2 | 114 files | `_CoqProject` | matches |
| 3 | 46,633 lines | comment-stripped count | matches |
| 4 | 1,541 definitions | Definition+Fixpoint+Inductive+Record | matches |
| 5 | 3,519 lemmas and theorems | Lemma+Theorem+Corollary = 3,541 | mismatch: `Local Lemma` was left out. Fixed, method in a TeX comment |
| 6 | per-directory line table, 23,698 lines, 51% | wc | matches |
| 7 | one term judgment, `styped` its instance | `typed`, `styped` | matches |
| 8 | MP translation mechanized, treated informally | `mp3_deadlock_free_source` | matches |
| 9 | no axiom | `CheckAll.v` | matches (Print Assumptions, see CLOUD-REPORT) |

## 4-extensions.tex

| # | claim | Rocq | verdict |
|---|-------|------|---------|
| 1 | every program of the section has a deadlock freedom proof | — | mismatch: the rejections do not. Fixed ("every typed program") |
| 2 | received chain | `ch_typed`, `ch_deadlock_free`, `ch_sub` | matches |
| 3 | forwarder | `fw_sub`, `fw_typed`, `fw_deadlock_free` | matches |
| 4 | Kobayashi forwarder rank in ℤ | `KobForwarder.fw_ok` | mismatch: lexicographic order. Fixed |
| 5 | Kobayashi forwarder typing | `KobForwarder.fw_typed`, `fw_deadlock_free_kob` | matches |
| 6 | factorial server | `fc_deadlock_free` | matches |
| 7 | Milner's scheduler | `ms_typed`, `ms_deadlock_free`, `sched_deadlock_free` | matches |
| 8 | every Γ of a closed typable program is acyclic | `slt_acyclic_nil` | mismatch: lemma covers a strict world without hypotheses. Fixed |
| 9 | one round is not enough | `rr_call_underivable` | matches |
| 10 | a box needs its constraint | `ord_no_constraint`, `ordered_typed` | mismatch: Rocq proves only ¬(ι ≺ ι′). Fixed |
| 11 | a reversed agent | `sched_rev_underivable`, `ms_rev_underivable` | matches |
| 12 | cyclic forwarding, and it deadlocks | `badlink_underivable` | facts match; the deadlock is only a comment. Fixed: text says so |
| 13 | choice signatures | `konst_sig` | matches; constants renamed select₀/select₁ to agree with i ∈ {0,1}, sum written ⊕{S₀,S₁} |
| 14 | P-Act-Choice, O/Q clauses | `PStepChoice`, `Eobl`, `Pobl` | matches |
| 15 | branch ordering, choice encoding | `bo_deadlock_free`, `ChoiceEnc` theorems | matches; encoding injects inj_{i+1} (fixed indexing) |
| 16 | CFST boxes, walks, ceilings | `TBox`, `t_exp`, `sendTree_ty` | matches |
| 17 | CFST programs | `tree_*`, `sch_*`, `ts_*`, `as_*`, `dl_untypable`, `dlfix_deadlock_free`, `si_*`, `sd_deadlock_free` | matches |
| 18 | dropping at Skip is not deadlock free | `sd_not_deadlock_free` | matches |
| 19 | ceiling is coarse (K8) | — | informal, no Rocq claim |
| 20 | translation covers every closed program of the source | — | mismatch: mechanized fragments at unit type. Fixed |
| 21 | PGV theorem statement | `pgv_deadlock_free_source` | mismatch: unit type, o < pr(T) also at recv. Fixed |
| 22 | PGV proof steps | `pgv_translate`, `PGVSimulation.sim_step` | mismatch: bound becomes a point below the future, matching sequence may be empty. Fixed |
| 23 | PGV world, eta, relation | `Wpgv`, `pgv_eta`, `rel` | matches |
| 24 | fragment adds o < pr(T) at send | `pk_send`, `pk_recv` | mismatch: also at recv. Fixed |
| 25 | both counterexamples rejected here | `cx1_rejected`, `cx2_rejected` | mismatch: lemmas are about PGV with the premises. Fixed |
| 26 | falling sessions outside the theorem | `fall2_typed`, `S1_not_mono` | matches; `% TODO(author): falling sessions open` present |
| 27 | their delegation and forwarding examples | `pgv_deleg_deadlock_free`, `pgv_link_deadlock_free` | mismatch: not attributed in Rocq. Fixed ("of our own") |
| 28 | PN theorem | `pn_deadlock_free_source` | mismatch: fragment limits hidden. Fixed |
| 29 | PN proof names | `pn_translate_source`, `Crel_acyclic`, `trel*` | matches; ambiguous names qualified |
| 30 | PN examples | `*_deadlock_free_src` | matches |
| 31 | Mordido–Pérez informal | — | matches (no formal theorem); citations to the cfst examples added |

## 7-appendix.tex

| # | claim | Rocq | verdict |
|---|-------|------|---------|
| 1 | Γ is a triple, `styped` at `wnil` | `fctx`, `styped`, `wnil` | matches |
| 2 | world irrelevant for Θ = ∅ | `typed_world_transfer` | mismatch: source world well formed with empty support. Fixed |
| 3 | E-Ch, E-Weak, E-Contract | `t_ch`, `t_weak`, `t_contract` | matches |
| 4 | primitive types | `prim` | matches |
| 5 | P-Term | `pt_term` | matches |
| 6 | P-Connect with literal dual | `pt_connect` | mismatch: separate Σ′_C dual at aliased points. Fixed |
| 7 | delegation table | `deleg_typed`, `dl_C` | matches |
| 8 | duality figure, relational duality | `dual`, `sdual_seq_dual` | matches; added that ≈ compares points by equality under □ and ∃ (`steq`) |
| 9 | reduction semantics has six rules | `red` | mismatch: choice rule missing. Fixed (R-Choice, harmony pairing) |
| 10 | pure reduction, harmony lemmas | `vred_reduction`, `harmony_forward`, `harmony_backward` | matches |

## Not mechanized, stated as such

- `blocked` deadlocks (2-calculus, example blocked).
- `badlink` deadlocks after the forwarding (4-extensions).
- No P-Connect derivation for the scheduler ring (4-extensions, scheduler): argued in prose only.
- `fallxy` defeats every translation reading points off session types: Rocq comment only.

## Claims about other papers (for a local check)

| file | claim | key |
|------|-------|-----|
| 2 | calculus based on Lindley and Morris's GV | `conf/esop/LindleyM15` |
| 2 | P-Act-Session in the spirit of the π-calculus Open rule | `lts-pi` |
| 2 | forked threads return unit, main returns the value | `conf/esop/LindleyM15` |
| 3 | n is a step index | `Ahmed06` |
| 4 | replicated forwarder needs the fresh channel below | `Kobayashi06` |
| 4 | factorial server is Kobayashi's running example and P14 example (3) | `Kobayashi06`, `Padovani14` |
| 4 | Milner's scheduler is their Example 1, untypable in CP/Wadler; Wadler ≡ GV | `DardhaG18`, `conf/esop/LindleyM15` |
| 4 | sendTree, treeSum, arithmetic server | `ThiemannV16` |
| 4 | MP allow dropping at Skip; MP do not type the ceiling program | `MordidoP` |
| 4 | PGV has 0 and absurd; send puts no payload condition; pair rule ignores left type; Example 2.1 | `KokkeD23` |
| 4 | Table 2, T-App-Poly, fix; fibo and pipe; levels, two-level arrow, shift at ⊤ | `PadovaniN15` |
| 4 | MP priorities on CFST actions, priority sequences, top effect, their examples | `MordidoP` |
| 5 | MP translation | `MordidoP` |
| 6 | first logical relations for session types | `DBLP:journals/iandc/PerezCPT14`, `DBLP:conf/concur/CairesP10` |
| 6 | SN and safety via second-order LL | `conf/esop/RochaC23`, `DBLP:journals/tcs/Girard87` |
| 6 | adequacy for CLL | `conf/esop/Atkey17`, `conf/icfp/Wadler12` |
| 6 | noninterference, cyclic extension | `DBLP:conf/lics/DerakhshanBJ21`, `DBLP:conf/ecoop/0001DB24` |
| 6 | timed IoT logical relation | `DBLP:journals/pacmpl/YaoICBZ25` |
| 6 | Actris/Multris prove safety, not DF | `HinrichsenBK22`, `HinrichsenLKB21`, `HinrichsenBK20`, `HinrichsenJK24` |
| 6 | LinearActris connectivity graphs | `JacobsHK24`, `JacobsBK22`, `JacobsB23` |
| 6 | comparison table rows (time tags, levels, priorities, APCP, worlds, events, lock types, Lam extraction) | `Kobayashi97`, `Kobayashi06`, `Padovani14`, `PadovaniN15`, `DardhaG18`, `KokkeD23`, `APCP`, `BalzerTP19`, `VieiraV13`, `FlanaganA99`, `KobayashiL17` |
| 6 | single-channel composition rejects Milner's scheduler | `DBLP:conf/concur/CairesP10`, `DBLP:journals/jfp/Wadler14`, `DardhaG18` |
| 6 | acyclic thread/channel graph invariant | `DBLP:journals/pacmpl/JacobsBK22` |
| 6 | future-work references | `conf/esop/Atkey17`, `Kobayashi02`, `Padovani13`, `DOsualdoSFG21`, `LiangF18`, `LeeLYCKH25`, `JacobsHK24`, `DardhaP22`, `Jaramillo025`, `HondaYC16` |
| 6 | their cyclic pair deadlocks synchronously | `DBLP:conf/ecoop/0001DB24` |
| 7 | duality as a function | `LindleyM16` |
| 7 | relational and functional duality agree | `DBLP:journals/corr/abs-2004-01322` |
