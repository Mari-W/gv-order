# Pending changes: the map leads, the Rocq follows

## Report, 2026-11-22, deadlock freedom over acyclic worlds

Branch redesign-df in .claude/worktrees/redesign-df, from redesign at
ea7f8b2, nothing pushed. Commits 3044719 (design copied from
redesign-fj), 78bc1ce, c9d6103, 29ddb10, d729cec, 5c5075b, 3ea8e07,
c959378 and the commit of this report. The design is
docs/redesign/check-df-acyclic.md. No Admitted, no Axiom, no new
Parameter. No syntactic clause in a relation, no semantic premise in a
typing rule.

- Worlds (types/Worlds.v). One record `world` with roots, a strict
  order `w_ord` on the rooted points that contains program order, and a
  kind `w_rk : option (point → rank_ord)`. A strict world
  (`wstrict`, `w_rk = None`) is an arbitrary strict partial order. A
  ranked world (`wranked`) carries ranks that give its order. Extension
  `⊑` asks inclusion of roots and order and keeps the kind, and at a
  ranked world every rank. So a world and its extensions have one kind,
  and the relation, which quantifies over extensions only, is the
  relation of that kind. This is the `WorldKind` parameter of the
  design as a field of the world instead of a type class. It needs no
  `Context` line in the 40 files that read worlds, and no proof of
  relation/, compat/ (but Redex.v), cost/ or fuel/ changed. The three
  instances are κ_DF and κ_L at strict worlds and κ_L at ranked worlds.
  `w_lt_wf` and `wchain_lt_wf` take a ranked world. `wstrict_of` and
  `dmodels_exists` model an acyclic static world by itself, with no
  rank. `wmodels_exists` now also says the model is ranked.
- Static side.
  - static/Contexts.v. `cbridge`, `acyc_new` (section 2.2 of the
    design), `new_ok N` and `wok N` switched on N, Lemma C
    (`gen_new_acyc`, constructive), `wf_new_acyc`, `new_ok_acyc`,
    `wok_acyc`, `swf_wok`, the wrapper `swf_ok_wok` and `sw_empty_wok`.
  - types/Worlds.v. `sacyc`, `swf_sacyc`, `sacyc_mono` and
    `acyc_join_iff` (with `join_split`, about 50 lines, constructive).
  - static/Typing.v. E-New asks `new_ok N`, P-Term and both P-Connects
    ask `wok N`. `fptyped_wf` and `ptyped_wf` return `wok N`
    (`wok_join_iff`, `swrestrict_wok`).
  - Followers. static/Consts.v (`acyc_new_ren`, `new_ok_ren`,
    `sacyc_ren`, `wok_ren`), static/Hiding.v (`wok_sub`,
    `connect_hidden` takes N), static/Inversion.v,
    static/Conservativity.v (`d_new_acyc`, `d_new` through Lemma C,
    the E-New case of `typed_dftyped` through `new_ok_acyc`),
    static/ConnectN.v, static/PointSubst.v (`tree_ends`,
    `slt_open_out_te`, `cons_tree`, the opening of an existential whose
    facts end in the new tree is conservative without (wf-new)).
- Soundness.
  - compat/Redex.v. `Erel_new_acyc` is Proposition A, constructive. The
    world of a creation is the transitive closure of the old order, the
    facts of C at the fresh root and program order (`aw_W`).
    Irreflexivity goes through the invariant `aw_inv`, which records a
    chain by where its ends lie and collapses every bridge with
    (acyc-new)(ii). `Erel_new` keeps its proof at ranked worlds.
    `Erel_new_any` dispatches on the kind and takes excluded middle only
    at a ranked world.
  - compat/LiveRules.v. `later_new` asks `new_sem` and
    `wranked W → excluded_middle`.
  - static/Fundamental.v. `typed_sem` loses its EM hypothesis and reads
    worlds with `wfit N W`, a strict world, or a ranked one at a finite N
    under excluded middle. `acyc_new_sem_of`, `new_sem_of`.
    `fundamental`, `fundamental_typed`, `live_fundamental`,
    `live_fundamental_typed` take `wstrict R` and no EM. New
    `live_fundamental_ranked` (EM) reads a derivation at `Some N` at any
    world, and `sem_later_df`.
  - static/FundamentalProc.v. `fundamental_proc`,
    `live_fundamental_proc`, `soundness`, `live_soundness`,
    `soundness_source` (now `sacyc W`), `fundamental_proc_h`,
    `live_fundamental_proc_h`, `soundness_h`, `live_soundness_h`,
    `adequacy_h`, `live_adequacy_h` take no EM. `sem_ptyped_sw` reads
    strict worlds, `sem_ptyped_h` an acyclic whole world.
    static/ConnectN.v. `connect_n_soundness` and
    `connect_n_live_soundness` take `sacyc` and no EM.
  - Lock-free side. `lf_sems` reads ranked worlds. `typed_live` and
    `lf_p_term` call `live_fundamental_ranked` on the derivation at
    `Some N`, no erasure. soup/LFAdequacy.v threads `wranked W`
    (`wk_ranked`), `lf_adequacy` and `lf_thread_progress` take it. The
    LF results keep EM and functional choice as before.
  - `live_sub_df` compiled unchanged. The universe question of section
    2.3 does not arise.
- Examples.
  - Recursive fork-join with replies (examples/ForkJoin.v, `fjr_acyc`,
    `fjr_dftyped`, `fjr_term`, `fjr_deadlock_free`). The worker is a box
    that forces itself through its box variable at (ι·0)‾ and (ι·1)‾.
    The box hypothesis is F(ι) with F((ι·w)‾) for every nonempty word w
    (`fjH`), closed under the descent (`fjH_desc`). main creates w with
    the laws H(ρ‾), which hold the infinite chain ρ ≻ ρ·0 ≻ …. (acyc-new)
    holds by the order offset, then polarity, then depth reversed. The
    language has no numbers, so the worker has no base case and never
    replies. The derivation reads no data, so a base case by a case
    split would not change it.
  - Padovani's fact (`fa_acyc`, `fct_dftyped`, `fct_deadlock_free`) and
    fibo (`fb_acyc`, `fib_dftyped`, `fib_deadlock_free`), with unit
    payloads and no case split, for the same reason. fibo forces one box
    at two instances. fact orders by depth reversed, then offset, fibo
    by depth reversed, then the last field, then offset.
  - The rejections stay. `ring_rejected` and `ring_rejected_full` of
    Ring.v and of Copycat.v, `sbv_rejected`, and the new `cyc2_rejected`
    and `cyc2_rejected_h` (the two-channel cycle, examples/Ring.v,
    through soundness). `opposite_clash` and `ring_cyclic` now state
    `¬ sacyc`, a stronger rejection.
  - Every DF example theorem lost its EM hypothesis: `fj_deadlock_free`,
    `opposite_df`, `ring_df`, `ring_rejected`, `ring_rejected_full`,
    `sb_deadlock_free`, `sbv_deadlock_free`, `tt_deadlock_free`,
    `tu_deadlock_free`, `te_deadlock_free`,
    `fwd_config_deadlock_free`, `fwdh_config_deadlock_free`, `fwdp_sem`
    (now with `wstrict R`). The others build through `swf_ok_wok`,
    `swf_wok`, `swf_sacyc` and `sw_empty_wok`. Copycat's
    `cut_W_f_swf` and `cut_W_p_swf` became `cut_W_f_wok` and
    `cut_W_p_wok`.
  - test/GuardNotations.expected and test/SoupNotations.expected are
    regenerated, for the new statements of `live_fundamental`,
    `live_soundness_h`, `lf_adequacy` and `lf_thread_progress`.
- Not done.
  - The process-level erasure `fptyped (Some N) → fptyped None`. It
    needs the ticket bookkeeping of `tenv_of (fhalf N)` against
    `tenv_df`. No result uses it. Lemma C and `swf_wok` give the two
    premise cases.
  - `cons_acyc`, conservativity of the opening of an arbitrary
    (acyc-new) existential with exits, the analogue of `cons_gen`. The
    examples need only `cons_tree`.
  - Comments in relation/Readiness.v, relation/Relation.v and
    compat/*.v that say "ranked world" where the world is now of either
    kind.
- Laptop, build of c959378 from a clean tree. `make` exit 0,
  `make test` passes, `make check` 210 of 210 (198 before, plus four
  for fork-join, three for fact, three for fibo, two for the cycle).
- Map changes for the audit (docs/explorer not edited). Worlds are
  strict partial orders with a kind, ranked only for the lock-free
  threads. E-New at N = ∞ asks (acyc-new), with bridges, at a finite N
  (gen-new). P-Term and P-Connect ask acyclic worlds at N = ∞. Lemma C.
  Proposition A as `Erel_new_acyc`. DF soundness, live soundness,
  hidden and n-ary soundness without excluded middle. `lf_p_term`
  through `live_fundamental_ranked`. `soundness_source` asks `sacyc`.
  New examples fork-join, fact, fibo, two-channel cycle.
  `opposite_clash` and `ring_cyclic` state `¬ sacyc`.

## Report, 2026-11-22, merge of redesign-clean3, redesign-fwd and redesign-fj

Branch redesign, from 3b237a1, nothing pushed. Commits 0f9f260 (merge of
redesign-clean3), f24bf4f (static/Consts.v), 18d65cb (expected
notations), a529af9 (merge of redesign-fwd), a5e99e2 (merge of
redesign-fj) and the commit of this report.

- Merge of redesign-clean3 (0f9f260, f24bf4f, 18d65cb). Git conflicted in
  CheckAll.v, _CoqProject, pending.md, soup/LFCompose.v, soup/LFTyped.v,
  static/FundamentalProc.v and the two expected files.
  - CheckAll.v and _CoqProject keep both sides.
  - FundamentalProc.v keeps the full judgment `fptyped None` from hiding
    and adds the EM hypothesis from the sixth run. LFCompose.v and
    LFTyped.v keep the hiding form of `lf_p_term` and `lf_fundamental`
    (conclusion `lf_sems N W`, every ranked world) and add EM.
  - static/Consts.v. `tsub_ren` proves the new Sub-Ex premise `lb_lower`.
    The case lb′ = lb is direct. The other case is `ex_wf_ren`, because
    `lb_lower` unfolds to `ex_wf`. `gen_new_ren` renames the partner sets
    pointwise. S′ s T′ holds when T′ = π <$> T for some T with S s T.
  - The expected outputs of `live_soundness_h` and `lf_fundamental` are
    regenerated from the laptop.
  - pending.md. The sixth-run report is restored from redesign-clean3.
- Merge of redesign-fwd (a529af9). Git conflicted in CheckAll.v,
  _CoqProject and pending.md.
  - Copycat.v was written against the judgment from before hiding. It now
    types on the full judgment. The merge renames `ptyped` to `fptyped`,
    `p_term` to `fp_term` and `p_connect` to `fp_connect`, and the lemmas
    to `fptyped_wf`, `fptyped_chans` and `fptyped_two`. The structural
    ring proof is now `ring_rejected_full` (full judgment, every bound).
    A new corollary `ring_rejected` rejects the ring with hiding through
    `ptyped_full`, so the name keeps its old statement.
  - CheckAll.v qualifies the four clashing names
    `examples.FreshBetween.fb_dftyped`, `examples.Copycat.fb_dftyped`,
    `examples.Ring.ring_rejected` and `examples.Copycat.ring_rejected`.
    On redesign-fwd, `Print Assumptions fb_dftyped` in the FreshBetween
    block printed the Copycat lemma. CheckAll.v also lists
    `examples.Copycat.ring_rejected_full`.
- Merge of redesign-fj (a5e99e2). Git conflicted in CheckAll.v only.
  ForkJoin.v moves to `fptyped` and `fp_term` like Copycat.v.
- Theorems that gain excluded middle as a hypothesis here, in addition
  to those of the sixth run. `soundness_h`, `live_soundness_h`,
  `fundamental_proc_h`, `live_fundamental_proc_h`, `lf_fundamental_h`,
  the hiding forms of `lf_p_term` and `lf_fundamental`,
  `connect_n_soundness`, `connect_n_live_soundness`, `opposite_df`,
  `ring_rejected`, `ring_rejected_full` and `ring_df` of Ring.v,
  `cli_term` and `srv_term` of LFClientServerSplit.v,
  `fwd_config_deadlock_free`, `fwdh_config_deadlock_free` and `fwdp_sem`
  of Copycat.v, and `fj_deadlock_free`. `connect_n_lf_soundness`,
  `lf_soundness` and `lf_soundness_h` took EM already.
- Map. No edits. `node docs/explorer/gen/gen.js` reports 0 errors and
  leaves data.js unchanged.
- Laptop. After f24bf4f and 18d65cb, `make` exit 0, `make test` passes,
  `make check` 184 of 184. After a529af9, `make` exit 0, `make check`
  194 of 194. Final build of a5e99e2 from a clean tree. `make` exit 0,
  `make test` passes, `make check` 198 of 198.
- No Admitted, no Axiom, no new Parameter.

## Report, 2026-11-22, fork-join with replies

Branch redesign-fj in .claude/worktrees/redesign-fj, from redesign-fwd at
8ba07c4, Rocq in c399554, nothing pushed. One new file,
v2/examples/ForkJoin.v, plus one line in v2/_CoqProject and four
`Print Assumptions` lines in v2/CheckAll.v. No rule changed. `make check`
gives 138 of 138 closed.

Recursive fork-join with replies does not type, in the DF judgment or at
any finite N. One round types, and so does any fixed depth with one box per
level.

- One round, binary (`fj_dftyped`, `fj_term`, `fj_deadlock_free`). main
  creates w at a fresh root ρ, keeps the end at ρ and spawns the worker on
  ρ‾. The worker is a box `□∀ι. H. (End@ι ⊸^⊤ ∗)`. It creates both child
  channels by E-New-Field at ι·0 and ι·1, spawns the two leaves on the
  duals, closes c1, then c2, then w. Readiness asks ι·0 ≺ (ι·1)‾ and
  ι·0 ≺ ῑ for the first close and ι·1 ≺ ῑ for the second. These three facts
  are H. The laws of ρ state H at ρ‾ (a field is the same from both ends),
  they meet (wf-new) by the measure (depth = 0, field sum, offset), and
  main forces the box at ρ‾. P-Term types the closed program over the empty
  world, and `soundness` gives deadlock freedom. The unary round is the
  same derivation with one child.
- The blocking premise is readiness of the wait, together with E-Force at
  the child. After the spawn the parent runs close c; close w.
  `fj_wait_needs` (an instance of `cl2_needs` from SemBranch) shows that
  every typing of that term, at any N, world and context, asks
  `slt W Γ p ῑ` for the point p of c and the point ι of w. The child holds
  c at p‾ and forces the same box there, so it needs `hold_at H` at
  ι′ = p‾ with ῑ′ = p ≺ ῑ. This is the hypothesis of Proposition 7 of
  check-general-new.md with f(ι) = ῑ. W, Γ and H then have no common model,
  so main cannot force the box. Every round must lower ῑ, and one H states
  the same facts for every call.
- The field route fails for the same reason as the fresh-root route. A
  field creation adds no fact, so the facts about ι·κ·κ′ that the child
  needs come from H or from the laws of ρ, and either would have to hold an
  infinite descent ῑ ≻ ι·κ ≻ ι·κ·κ′ ≻ … . Proposition 7 says that a field
  creation needs no extension and the proof applies unchanged. A box that
  may answer at once does not help, because a case split adds no fact.
- Not mechanized. The rejection of the recursive program as a whole rests
  on Proposition 7, which is on paper. The depth-d version with d + 1 boxes
  is not in Rocq. The LF judgment was not tried for the round. Its premises
  of readiness and E-Force are the same, and `fj_wait_needs` is stated at
  every N, so the recursion fails there too.
- Question 3 (binary) is answered by the round above. The recursive binary
  version fails at the first close, as the unary one does.

## Report, 2026-11-22, a derived forwarder at independent points (design B)

Branch redesign-fwd in .claude/worktrees/redesign-fwd, from redesign at
46276d6, commits ae8f5fc to b550ebb, nothing pushed. One new file,
v2/examples/Copycat.v, plus one line in v2/_CoqProject and nine
`Print Assumptions` lines in v2/CheckAll.v. No rule changed and no rule
blocked a derivation. All results are closed under the global context.

- Item 1, the copycat. Done for ?∗.!∗.Close, for a higher-order payload
  and as a schema over every first-order protocol.
  - Concrete (ae8f5fc, 39c5070). `fwd_t o1 o2` holds o1 : S@x and
    o2 : S‾@y and types under exactly the facts of the design, x ≺ y‾,
    y ≺ (x⁺)‾, y⁺ ≺ (x⁺)‾, x⁺ ≺ (y⁺⁺)‾ and x⁺⁺ ≺ (y⁺⁺)‾ (`fwd_dftyped`).
    Each action asks its point below the heads of the ends still held,
    and the head of an end at y is y‾. The last fact comes from Close.
    `fwd_term` types the thread by P-Term over the world `W_f` with the
    two constant roots and these five facts. `W_f` is well-founded by the
    potential 2·offset + (root + offset mod 2), because the end that acts
    first alternates with the offset.
  - Higher-order payload (f0dcccb, b0361b1), Sh = ?(Close@ι₀).Close. The
    received end sits at x·0 and a payload sent on y must sit at y·0. An
    end keeps its point and E-Sub keeps points, so the forwarder cannot
    pass the end on. It η-expands it. It creates a channel at the field
    y·0 by E-New-Field, sends that end on y, and forwards the received end
    to the kept end at (y·0)‾, which for Close closes both. The facts sit
    at the fields, eleven of them, among them y ≺ (y·0)‾ for the payload
    of the send and x·0 ≺ y·0 for the inner forwarder (`fwdh_dftyped`,
    `fwdh_term`). This is what "payload ends pass on with facts at their
    fields" amounts to in Rocq.
  - Schema (4953768, ed132d9). Protocols p ::= end | ?p | !p with unit
    payloads. `fb p` keeps the two ends in the de Bruijn shape [o2; o1]
    after every step, so it is defined and typed by induction on p
    (`fb_dftyped`). The facts `ffp p x y` are generated by p. A receive
    on the first end gives x ≺ y‾ and y ≺ (x⁺)‾, a send gives y ≺ x‾ and
    x ≺ (y⁺)‾, Close gives x ≺ y‾. `W_p p` holds them and is well-founded
    by the same potential, with the order inside an offset read off p
    (`pfirst`). `fwdp_term` types the thread at every p, and
    `pS (PRcv (PSnd PEnd)) = S1` relates it to the concrete forwarder.
    Choice and recursion are not covered. Recursion needs the forwarder
    as a box with an upper point, as in ClientServer.
- Item 2, identity expansion. Done for the concrete type and for every
  first-order protocol (50416d7, ed132d9). `fwd_expand` and
  `fwdp_expand` state that a process P with o1‾ : S‾@x‾ in its interface
  types with the forwarder behind it. P ∥ fwd then holds o2 : S‾@y in
  place of o1‾, at the same type. The one condition on the world W of P
  is that W does not know the root of y. Between two points on the root of
  x the forwarder's world then derives only program order
  (`W_f_lt_root0`, `W_p_lt_root0`), so the cut of P-Connect is
  well-founded because W is. The partner of P now has to hold o2‾ at y‾.
  No renaming lemma moves a typed partner from o1 at x to o2‾ at y‾, so
  the two-sided form is not stated.
- Item 3, the forwarder ring (3f08cf2). `ring_rejected` shows that
  fwd(o1, o2) ∥ fwd(o2‾, o1‾) cut on {a, b} types at no bound N, no world
  and no type. `fwd_needs` inverts any typing of `fwd_t a b` down to its
  first receive and gives the point of a below the head of b. The first
  forwarder gives x ≺ y‾, the second y‾ ≺ x, and the joined world, which
  is well-founded by `ptyped_wf`, would hold x ≺ x. `inv_recv` is new and
  local to the file, the rest reuses static/Inversion.v and the helpers
  of SemBranch.
- Item 4, soundness for free. `fwd_config_deadlock_free`: partner ∥ fwd ∥
  partner over ?∗.!∗.Close types by `fwd_expand` and P-Connect and is
  deadlock free by `soundness`. `fwdh_config_deadlock_free` does the same
  for the higher-order forwarder, with partners whose worlds hold facts at
  their own fields. Every world of that run raises one potential, so every
  cut is well-founded. `fwdp_sem` puts the schema forwarder in the
  relation at every ranked world that models `W_p p`, and such a world
  exists (`W_p_models`).
- Builds. Local single-file builds throughout. Laptop at 3f08cf2: `make`
  exit 0, `make check` 129 of 129. Laptop at b550ebb: `make` exit 0,
  `make test` passes, `make check` 134 of 134.
- Map changes, not made (docs/explorer untouched).
  - A new example node for examples/Copycat.v with the five facts, the
    ring and the η-expansion of a payload end.
  - The parked item "Link as a primitive, identity expansion" below: design
    B is now mechanized. Identity expansion holds for `fwd` at
    first-order protocols and at the Close payload, link keeps fusion and
    tickets.
  - SHARP-EDGES entry 37 and the link pages can say that a sequential
    copycat at independent points types, while one at dual points stays
    untyped.
  - The CheckAll count rises from 125 to 134.

## Report, sixth run of 2026-11-22 on Sub-Ex lowering l, (gen-new) with sets and its examples

Branch redesign-clean3 in .claude/worktrees/redesign-s4, nothing pushed,
commits 09fd0b9 to the head. docs/explorer untouched, the map changes are
listed at the end.

- Item 1, the heads lemma and Sub-Ex with a lower l. Done (09fd0b9).
  - The heads lemma existed already. `Vrel_heads` (compat/Redex.v, since
    S4.4) says that every end o : S@x of a value of T with `hbot T = false`
    has a head h ∈ `heads T` with `w_le W h x‾`. The fifth run missed it.
    What was missing is its use in Sub-Ex.
  - Rule. `sub_ex` takes `lb_lower W Γ n C lb lb' T`, which is `lb' = lb`
    or `lbx_below_h W (hc_open n C Γ) lb'↑ (heads T) (hbot T)`, the
    premise E-Pack asks after an opening at the identity instance. ⊥ is
    always allowed, `LNone` needs no heads and no ⊥ flag, `LPt x'` needs
    Γ, C ⊢ x' ≼ h for each head h of the body.
  - `Vrel_tsub` (static/Fundamental.v) reads the heads of the ends off
    `Vrel_heads` at the witnesses and the facts through `sle_sem` under
    `hsat_open`. `tsub_df`, `tsub_sinst`, `tsub_refl` and `Vty_sub`
    (fuel/FuelSub.v) follow.
  - `tsub_open_pack` (static/Conservativity.v). Opening x : ∃^l ιs. C. T
    and packing at ιs with C' and l' that Γ and C entail is one step of
    Sub-Ex. Not done, the theorem about the two programs `e` and
    `let x = e in x`. Its hard half inverts a derivation of the let
    through E-Open, E-Pack and E-Sub, and Inversion.v has no lemma for
    Var or Let with an existential. A pack at points other than ιs is
    also outside Sub-Ex, which compares bodies at the same instance.
- Item 2, (gen-new) with finite sets. Done (5ffaf18, 2f5c6e6), with
  excluded middle as a hypothesis.
  - Rule. `gen_new_rel` (static/Contexts.v) relates points of the new tree
    to lists of points of Γ. Every list is nonempty, each exit u ≺ y has a
    list below y, each point of the list of a step below lies below some
    point of the list above, each entry z ≺ s lies below some point of
    the list of s. The old relation is `gen_new1`, and `gen_new1_gen`,
    `wf_new_plus_gen` (through `wf_new_plus_gen1`) and `wf_new_gen` derive
    the old premises. The examples keep proving `wf_new`.
  - `cons_gen` (static/PointSubst.v) carries the sets through `cinv`.
    Constructive.
  - `Erel_new` (compat/Redex.v) keeps the construction and proves
    `Sr s T → ∃ t ∈ T, rank_base s ≤ rk0 t` by well-founded induction,
    with the t of largest rank from `list_max_rank`.
  - No constructive proof exists. `two_below_gd` (relation/Ranks.v) shows
    that a rank r with a, b ≤ r < c for any a, b < c gives
    (P → Q) ∨ (Q → P) for all P, Q. Take a and b the suprema of 1 over P
    and over Q, c the supremum of a + 1 and b + 1. The creation of the
    two-entry example needs exactly such an r at a model where the two
    entries have ranks a and b and ρ̄ has rank c, so Brouwer suprema do
    not help. `ole_total` (constructive from excluded middle) gives the
    largest member of a finite family.
  - Theorems that gain `excluded_middle` as a hypothesis, none as an
    axiom. compat/Redex.v `Erel_new`. compat/LiveRules.v `later_new`.
    static/Fundamental.v `typed_sem`, `typed_sem_df`, `typed_sem_live`,
    `fundamental`, `fundamental_typed`, `live_fundamental`,
    `live_fundamental_typed`. static/FundamentalProc.v
    `fundamental_proc`, `live_fundamental_proc`, `soundness`,
    `live_soundness`, `soundness_source`. soup/LFCompose.v `typed_live`,
    `lf_p_term`. soup/LFTyped.v `lf_fundamental`. examples/SemBranch.v
    `typed_E_df`, `arm_E`, `sb_thread_E`, `partner_E`, `arm_v_E`,
    `sbv_thread_E`, `sb_deadlock_free(_R)`, `sbv_deadlock_free(_R)`.
    examples/TreeTopo.v the section lemmas from `leaf_E` on and
    `tt_deadlock_free`. `lf_soundness`, `lf_soundness_run`,
    `lf_soundness_padovani` and `lf_soundness_source` had it already.
    `cost_fundamental`, `fsem_of_cost`, `adequacy` and the typing
    results stay free of it. The abbreviation `excluded_middle` in
    compat/Redex.v points to lockfree/FairRun.v, which Redex only
    Requires, because importing it reopens the scope of ‾ on ends.
  - test/GuardNotations.expected and test/SoupNotations.expected print
    the new hypothesis.
- Item 3, examples/GenNew.v. Done (4667961).
  - Two upper bounds. `tu_main` creates a at ρ, b at ρ·0, spawns
    close a′; close b′, creates d at a fresh root π with
    C = {π ≺ ρ̄, π ≺ (ρ·0)‾}, spawns close d′, closes d, a and b. Γ has
    ρ·1 ≺ ρ̄ and ρ ≺ (ρ·0)‾, and no point below both. `tu_gen1` proves
    (gen-new₁) with S = {(π, ρ·1), (π, ρ)}, and `tu_gen` lifts it.
  - Two entries. `te_main` creates a at ρ, e1 at ρ·0, e2 at ρ·1, spawns
    the three partners, creates d at π with
    C = {ρ·0 ≺ π, ρ·1 ≺ π, π ≺ ρ̄}, spawns close e1; close e2; close d′
    and closes d and a. Γ has ρ·0 ≺ ρ·2 ≺ ρ̄, ρ·1 ≺ ρ·3 ≺ ρ̄ and
    ρ·0 ≺ (ρ·1)‾. `te_gen` proves (gen-new) with S = {(π, {ρ·2, ρ·3})}.
  - Both are typed end to end in the DF projection (`tu_dftyped`,
    `te_dftyped`) at the empty world, and deadlock free by
    `soundness_source` under excluded middle (`tu_deadlock_free`,
    `te_deadlock_free`). This is P-Term with Σ = ∅ and C₀ = ∅.
  - Rejection under (wf-new). `tu_not_wf_new` and `te_not_wf_new`, the
    constraints of d are not (wf-new). `tu_rejected_wf_new` and
    `te_rejected_wf_new`, under every constraint C′ with `wf_new C′`, the
    thread `close d; close a` with d at π and a at ρ has no derivation in
    `hc_open 1 C′ Γ`, by `cl2_needs` (SemBranch.v) and `slt_open_out`.
    This is the thread after the creation has reduced, with channel ends
    in Θ. Not mechanized, that no derivation of `tu_main` exists with
    every E-New under (wf-new). It needs inversion lemmas for Var, Let,
    New and Spawn through E-Open and E-Sub, which Inversion.v lacks. I did
    not prove either constraint outside (wf-new⁺) or (gen-new₁) by a lemma.
- Laptop at 2f5c6e6: `make` exit 0, `make test` passes, `make check` 142 of
  142.

Plausibility. No Admitted, no Axiom, no new Parameter. CheckAll lists 142
results, 17 of them new. The examples build. `soundness` and
`lf_soundness` print no axiom, `soundness` now takes excluded middle as
an argument. rx-chain stays excluded by Proposition 7 of
check-general-new.md, which holds for every sound E-New, (gen-new) with
sets included. Not mechanized.

Map changes for the audit (docs/explorer/gen).

- typing.js, both Sub-Ex rules (the lines with `rule('Sub-Ex'`). The
  conclusion reads ∃^{l} ≤ ∃^{l'}, and a new premise
  `h('tp.sub-exlb', l' = l \vee \Gamma, C(\bar\iota) \vdash l' \preceq \mathsf{heads}\,T)`.
  New note `tp.sub-exlb`, citing static/Contexts.v `lb_lower`, `sub_ex`,
  compat/Redex.v `Vrel_heads`, static/Fundamental.v `Vrel_tsub`,
  static/Conservativity.v `tsub_open_pack`. Note `tp.sub-ex` drops "with
  the same lower bound".
- types.js, block `w-wf`, formula `w.gennew` and note `w.gennew` and its
  signature `sa('w.gennew', …)`. S ⊆ tree(ρ) × P_fin⁺(Point_Γ), the three
  clauses over sets as in section 4 of check-general-new.md. Example
  becomes the two-entry example with S = {(π, {ρ·2, ρ·3})}. Citation adds
  `gen_new1`, `gen_new1_gen`, `wf_new_plus_gen1`, relation/Ranks.v
  `list_max_rank`, `two_below_gd` and examples/GenNew.v `tu_gen1`,
  `te_gen`.
- typing.js, note `E-New.wf`. Partners are sets, the proof takes the
  partner of largest rank under excluded middle. Citation adds
  `gen_new1_gen`.
- theorems.js, `th.soundness`, `th.soundness-source`, the live soundness
  and fundamental entries (`th.live-fundamental-typed` and the DF
  fundamental theorem), `th.lf-fundamental` and their `sa(…)` signatures
  gain EM as a premise, as `th.lf-soundness` shows it. Block `th-chain`
  and `th-sound` say that DF soundness needs excluded middle since
  E-New takes partner sets.
- A new note for the classical step, relation/Ranks.v `ole_total`,
  `list_max_rank`, `two_below_gd`, linked from `w.gennew`.
- Examples. examples/GenNew.v with `tu_main` (two upper bounds, needs a
  relation) and `te_main` (two entries, needs sets), each typed and
  deadlock free, each rejected after the creation under every (wf-new)
  constraint.
- prose.js and rejects.js need no change. rx-chain stays argued.

## Report, run of 2026-11-22 on the merge of redesign-comp and the n-ary connect

Branch redesign, from 314ddc3, commits e074d5b (merge), 2cb0286 (n-ary
connect), 12e32ba (map) and the commits of this report, nothing pushed.

- Step 1, the merge (e074d5b). `git merge redesign-comp` conflicted in
  seven files. CheckAll.v keeps both import lines and both lists of
  results. LFTools.v and SemBranch.v take the clean3 premise patterns
  under the new names `fp_term` and `fptyped_one`. LFTyped.v takes the
  clean3 pattern with HΣc, the `revert Hg` of redesign-comp and the
  current argument list of `lf_p_term`. pending.md keeps the hiding report
  first, then the fifth-run report, then the older reports of both sides.
  typing.js keeps the hiding forms of P-Term and P-Connect and adds the
  premise `P-Term.contr`. data.js is regenerated (`gen.js`, 0 errors).
  - Git applied the contractivity premises of clean3 to `fp_term`. The
    merge adds the same two premises to `p_term` (contractive interface,
    contractive restricted ends), so the hidden and the full judgment ask
    the same of a thread.
  - static/Consts.v. `sk_ren`, `ugv_ren`, `tcontr_ren`, `scontr_ren`
    (renaming constants keeps contractivity), `sinsts_ren` over
    `Forall contractive`, `tsub_ren` restated for `tsub W Γ` (Sub-Ex goes
    through `hold_at_ren`, `bcs_inst_pshift_ren` and `ids_ren`, Sub-Box
    through `teq_ren` and `tcontr_ren`), and `gen_new_ren`. The facts of a
    creation constraint speak of variables only, so a context point
    renames with the environment (`ctx_pt_ren`) and the partner relation
    renames on its second component.
  - static/Hiding.v. `typed_ren` covers the premises of E-Abs, E-Inj,
    E-Box, E-New, E-New-Field and E-Sub. `fptyped_ren`, `ptyped_full` and
    `fptyped_ptyped` read the contractivity premises of P-Term.
  - examples/SharedRoots.v (`senv2_contr`) and LFClientServerSplit.v prove
    the new premises, the latter by `contr_tac`.
  - Laptop on the merged tree before the merge commit. `make` exit 0,
    `make test` passes, `make check` 156 of 156. All named results
    survive. These are the `_h` theorems, `typed_sinst`, `cons_gen` (with
    `gen_new` in E-New), `cs_split_typed`, `shared_hidden`, `opposite_df`
    and `sbv_rejected_h`.
- Step 2, the n-ary connect (2cb0286). static/ConnectN.v.
  - `pcomps N Ws Σ p T` collects n component derivations at their hidden
    worlds Ws. Component i ≥ 2 connects over a cut Σ_{C,i} to the
    composite of the components before it, with the side conditions of
    P-Connect and no condition on worlds. The cut may hold ends of several
    earlier components, so a ring closes at its last component.
  - `p_connect_n`. From `pcomps N Ws Σ p T` and `swf (sw_joins Ws)`, the
    one interface check on the join of the n hidden worlds, a derivation
    `ptyped N W Σ p T` exists at a world W whose facts are facts of
    `swrestrict (sw_joins Ws) (iface Σ T)`. The rule is admissible, no new
    constructor of `ptyped`. The proof folds `p_connect`
    (`pcomps_fold`). The world of each partial composite derives only
    facts of the join of its component worlds, so the n-ary premise gives
    each binary premise by `swf_sub`.
  - Amalgamation. The fold needs no n-ary amalgamation lemma, so it is not
    proved. The hidden worlds already live on their interface constants.
    The result world can derive fewer facts than the restricted join,
    because a constant the composite hides at an earlier step drops out of
    the later checks. The rule states the inclusion and not equality.
  - Soundness through the binary results. `connect_n_soundness`
    (deadlock freedom) and `connect_n_live_soundness` in
    static/ConnectN.v, `connect_n_lf_soundness` (lock freedom at Some N
    with guards, EM and FC as hypotheses) in soup/LFConnectN.v. Each one
    applies `p_connect_n` and the `_h` soundness theorem.
  - examples/Ring.v, Milner's ring. A = cl c⁻; cl a⁺, B = cl a⁻; cl b⁺,
    C = cl b⁻; cl c⁺, with a, b, c at the constants 0, 1, 2. The thread
    worlds hold c̄ ≺ ā, ā ≺ b̄ and b̄ ≺ c̄. By `ring_comps` the ring meets
    every condition of the n-ary rule but the world check. By
    `ring_pairs` the hidden worlds are well-founded two at a time. By
    `ring_cyclic` the join of the three holds c̄ ≺ ā ≺ b̄ ≺ c̄. By
    `ring_rejected` no world types the ring in `ptyped None`, because the
    ring is stuck (`ring_stuck`, read off `pstep_iff` and the first action
    of each thread) and so not deadlock free. `ring_rejected_full` is the
    same for `fptyped`.
  - The acyclic ring. C' = cl c⁺; cl b⁻ asks c ≺ b. The join of the three
    hidden worlds is well-founded (`ring'_wf`, a rank on points),
    `ring_typed` types the ring by `p_connect_n`, and `ring_df` gives
    deadlock freedom through `connect_n_soundness`. The example types at
    N = ∞ only, so it has no lock-free instance.
  - CheckAll lists the 11 new results.
- Laptop, clean build at 12e32ba (`git archive HEAD v2`). `make -j8`
  exit 0, `make test` passes, `make check` 167 of 167 results closed under
  the global context.
- Map (12e32ba). The P-Connect block gets a second row, P-Connectⁿ, with
  the note `P-Connect.n` and its signature. The block cites
  static/ConnectN.v. `gen.js` reports 0 errors.
- Map changes for the audit. Merge (e074d5b). typing.js P-Term carries
  both the hiding conclusion and `P-Term.contr`, the rest of the map is
  the union of the two sides, data.js regenerated. Step 2 (12e32ba). Row
  and note `P-Connect.n`. Not on the map. `pcomps` as its own note,
  `ring_rejected`, `ring_typed` and the other Ring results as examples,
  and the soundness corollaries in th-sound. The sentence on Milner's ring
  in `P-Connect.wf` can now cite examples/Ring.v.
- No Admitted, no Axiom, no new Parameter. No typing rule changed beyond
  the two P-Term premises the merge copies from `fp_term`.
- The open item "The n-ary connect" got a three-line update.

## Report, run of 2026-11-22 on hiding (repair (b))

Branch redesign-comp, from 0647d1e, commits a1c2c71, 85ee183, 504a06c,
caea47f and f1e7116, nothing pushed. Only the process-typing part of
static/Typing.v changed. The expression rules are untouched. 504a06c does
not build on its own (LFClientServerSplit), caea47f repairs it.

Hiding is sound for both relations, in the restated form.

- The judgment (static/Typing.v). `ptyped` is the process judgment with
  hiding. P-Term concludes at `swrestrict W (iface Σ T)`. P-Connect asks
  `swf (W1 ⊔ W2)` of the two component worlds and concludes at
  `swrestrict (W1 ⊔ W2) (iface (Σ1 ∪ Σ2) T)`. Each component world lives
  on its interface constants (`ptyped_consts`), so the premise is
  `swf (W1|I1 ⊔ W2|I2)`. The old judgment is kept as `fptyped`, with
  `fp_term`, `fp_connect` and the old lemmas renamed. It is the target of
  the soundness proof. The notation Σ ⊢_W p : T now means `ptyped`.
- The interface constants (static/Consts.v). `iface Σ T` holds every
  constant of the points and session types of Σ and of T, a superset of
  the roots of the points of Σ. A payload type or a box type can name a
  constant, and the renaming below must fix Σ and T.
- Item 1. `swrestrict W S` already keeps the derived order between points
  with roots in S, so a chain through private constants becomes a fact
  (`swrestrict_iff`, static/Hiding.v). No new definition was needed.
- Item 2, soundness. The direct semantic form fails to prove. A ranked
  world R that models W|I may rank interface points a and b at 0 and 1
  while W puts a private point between them, and no extension of R ranks
  it, because an extension keeps every rank. So hiding is proved through
  derivations. `typed_ren` renames the constants of a term derivation by
  a bijection, `fptyped_ren` a full process derivation. `ptyped_full`
  turns every hidden derivation into a full one at a world W' that hides
  to the hidden world (`hides`, the facts W' derives between interface
  points lie in it). At P-Connect the first component is renamed to keep
  its private constants off the interface of the second, the second off
  the whole world of the first (`cb_avoid`, `rename_side`). Then the two
  worlds share only constants of both interfaces, and `connect_hidden`
  gives the premise of `fp_connect` and the hiding of the join. Its core
  is `join_vis`, which shows that a chain of the join changes sides only
  at shared constants. This covers case 3 of the SharedRoots report,
  roots the two outer interfaces share. `fptyped_ptyped` is the converse,
  so hiding loses no program.
- Both relations. `soundness_h`, `live_soundness_h` and `lf_soundness_h`
  conclude deadlock freedom and lock freedom from the hidden judgment.
  `fundamental_proc_h`, `live_fundamental_proc_h` and `lf_fundamental_h`
  give the semantic judgment at a hidden world (`sem_ptyped_h`,
  `lf_sems_h`, a well-founded whole world that hides to it).
- Item 3, semantic P-Connect. `sem_p_connect_h` and `lf_p_connect_h`
  compose at the interface orders, `swf (W1 ⊔ W2)` of the hidden worlds,
  given whole worlds whose private constants are apart. That apartness is
  a hypothesis because the relation has no renaming lemma for constants.
  The static renaming supplies it inside `ptyped_full`. `sem_p_connect_sw`
  and `lf_p_connect` are unchanged and still serve the full judgment.
- Item 4 (examples/SharedRoots.v). `shared_hidden` types P(c, d) ∥ P(e, f)
  with hiding. Each component sits at a world with no constant and no fact
  (`hcomp_typed`), so the two compose by their interface worlds.
  `opposite_compose` is case 2. P'(e, f) closes f first and orders 0
  oppositely, the whole worlds clash (`opposite_clash`, a cycle at 0), and
  the hidden composition types and is deadlock free (`opposite_df`).
  `shared_not_cut` and `fact_needs_zero` stay, stated for `fptyped`.
  examples/LFClientServerSplit.v adds `cs_split_typed`, the split program
  in the hidden judgment, and `cs_split_lock_free_h`.
  `sbv_rejected_h` rejects the flag variant with hiding.
- Other examples, Inversion.v, Forwarder.v and LFTools.v use `fptyped`,
  by renaming only.
- Checks on the laptop, at f1e7116. `make -j8` builds with no error,
  `make test` passes after test/GuardNotations prints `live_soundness_h`,
  and `make check` reports 147 of 147 results closed under the global
  context. No Admitted, no Axiom, no new Parameter.
- Map (f1e7116). P-Term concludes at W|_{I(Σ, T)}, P-Connect asks
  wf(W1 ⊔ W2) and concludes at (W1 ⊔ W2)|_{I(Σ1 ∪ Σ2, T)}. New notes
  `P-Term.hide` (the component type is Σ with its interface world) and
  `tp.iface`. `P-Connect.wf` explains the interface orders, the renaming
  and the sentence on Milner's ring. The fundamental theorems and
  soundness cite the hidden forms. `node docs/explorer/gen/gen.js` reports
  0 errors.
- Map changes for the audit (made in f1e7116, no later edits). Typing
  block, rule P-Term (conclusion world `P-Term.hide`, new notes
  `P-Term.hide` and `tp.iface`, `P-Term.wf` text). Rule P-Connect (premise
  `P-Connect.wf` now wf(W1 ⊔ W2) with the interface orders, the renaming
  and Milner's ring, conclusion `P-Connect.join` at the hidden join), the
  `p-term` and `p-connect` why texts, note `tp.pjudg` (component type,
  `fptyped`). Types block, note `w.restrict` and its signature. Theorems
  blocks th-fund-proc, th-compose and th-sound (rocq references to the
  `_h` forms, `ptyped_full`, `connect_hidden`), notes
  `th.fundamental-proc`, `th.lf-fundamental` and their signatures,
  `th.lf-p-connect`, `th.soundness`, `th.lf-soundness`. Not yet on the
  map. `fptyped_ptyped` (hiding loses no program), `sem_p_connect_h` as
  its own row, the examples `shared_hidden`, `opposite_compose`,
  `opposite_df`, `cs_split_typed`, `sbv_rejected_h`, and the note
  `w.R7`, which still states the join at the shared constants and is
  now used only by the full judgment.

## Report, fifth run of 2026-11-22 on contractivity, Sub-Ex and (gen-new₁)

Branch redesign-clean3 in .claude/worktrees/redesign-s4, nothing pushed,
commits a136833 to the head.

- Item 1, contractive session types and `typed_sinst`. Done.
  - Predicate (types/Contractive.v, a136833). `scontr` and `tcontr` are
    boolean, mutual over session types and types, and go into payloads. A
    recursion variable must be reached only through an action, a choice or
    Close. A session variable does not guard, because an instance may set it
    to Skip (`ss_var_guard`). µ-variables inside payloads, as in GrowRing's
    `µα. ?(1, α@ι₀). Close`, sit behind an action and are fine. Closure under
    renaming, flipping, duality, `sinst` (contractive instances), `pinst`
    and `ty_df`.
  - Fuel (5981333). `unrN_sfuel : scontr s → ∃ h, unrN (sfuel s) s = Some h`,
    with `unrN_mono` and `unrN_unfoldS` (any fuel above `sfuel s` gives
    `unfoldS s`). `scontr_hcontractive` relates the new predicate to the old
    one.
  - ≈ under instances (006c5ce to e1d1f10). A bisimulation up to ≈
    (`sequiv_upto`), the head of a sequence (`hd_seq`), the laws Skip;S ≈ S,
    S;Skip ≈ S, associativity, congruence, unfolding of µ, Close and choice
    distribution, then `sinst_unrN` (an instance commutes with unfolding up
    to ≈), `unrN_var_uc` (each variable head lowers the count of unguarded
    variables) and `sequiv_sinst` and `teq_sinst` for contractive types and
    instances. `unfoldS_sinst_act` gives the payload of an action head of an
    instance exactly and its continuation up to ≈.
  - Rules (3d3883e). Contractivity enters at E-New and E-New-Field (the
    protocol), E-Abs (the argument), E-Inj (the sum), E-Box (the result U,
    which the body cannot establish because it refers to the box through f),
    P-Term (Σ and the restricted ends) and E-Sub. E-Sub asks
    `tcontr T → tcontr T'`. Asking `tcontr T'` outright breaks
    `typed_to_inf`, which lifts any DF derivation to cost ∞ by E-Sub at the
    same type and underlies every `d_*` rule. Over contractive contexts the
    two forms agree (`typed_scontr`). `sinsts` and the instance quantifier
    of the box clause of the relation (Relation.v, LiveRules.v, Redex.v,
    Fundamental.v) read `Forall contractive` in place of
    `Forall hcontractive`. This restricts the instances the relation
    quantifies over, a type-level condition like the old one, no syntactic
    clause on terms.
  - `typed_sinst` (f8d3be6, static/Sinst.v). Over contexts with contractive
    session types, at contractive, scoped instances (df at N = ∞), a
    derivation is a derivation of the instantiated judgment.
    `typed_sinst_slist` is the box form. The box case shifts the instance of
    the instantiated box past the free session variables of the box and its
    context (`tfv`, `lfv`, `sinst_above`). The actions use
    `unfoldS_sinst_*` and close the continuation by E-Sub.
  - SinstStuck.v keeps `typed_sinst_false` (its context holds the
    non-contractive s0, so it shows the premise on the context is needed)
    and adds `ss_var_guard`. Every example builds. The examples prove
    contractivity by `vm_compute` (`contr_tac`). LFLink takes `scontr S` as a
    section hypothesis.
  - Laptop at 186308e: `make` exit 0, `make test` passes, `make check` 121 of
    121.
- Item 2, Sub-Ex by entailment. Done for the constraint, the lower bound
  stays.
  - `tsub W Γ T T'` (ece7bea). Sub-Ex asks
    `hold_at W (hc_open n C Γ) (bcs_inst (pshift n) C') (ids n)` and compares
    the bodies under `hc_open n C Γ`. The old subset rule is the case where
    each fact of C' is a fact of C (`hold_open_self`). Semantically
    `Vrel_tsub` (Fundamental.v) reads the facts of C' off C and Γ at the
    witnesses through `hsat_open` and `hold_sem`. `later_conv` (LiveRules.v)
    now takes a value-level conversion. `tsub_pinst` is gone, the fuel and
    cost relations ignore W and Γ.
  - Relation to `let x = e in x`. Opening x and packing at the opened points
    gives exactly the constraints C' with
    `hold_at W (hc_open n C Γ) C'[shifted] (ids n)`, so with the same lower
    bound e now types wherever `let x = e in x` does. Not mechanized as a
    theorem about the two programs. Open with pack can also change the
    lower bound l to one that E-Pack accepts. Sub-Ex keeps l, because the
    relation reads l against the heads of the ends of the value
    (`lbx_le W lb (senv_heads Θ)`), and lowering it soundly needs a lemma
    relating those heads to `heads T`, which does not exist.
  - Sub-Box (5a0f9f4). For k > 0 the results may differ up to ≡ when both
    are contractive (`U = U' ∨ (teq U U' ∧ tcontr U ∧ tcontr U')`). The
    relation case uses `teq_sinst` at the contractive instances the box
    clause quantifies over. The equality disjunct keeps `tsub_refl` free of
    contractivity.
  - Laptop at 5a0f9f4: `make` exit 0, `make test` passes, `make check` 121 of
    121.
- Item 3, (wf-new⁺) and (gen-new₁). Done in one step (48aef68). E-New at a
  fresh root asks `gen_new W Γ C` (static/Contexts.v), the (gen-new₁) of
  check-general-new.md with a relation S between points of the new tree and
  points of Γ. Its clauses are well-foundedness of C with program order on
  the tree, Γ ⊢ z ≺ y for facts between context points, a partner below y
  for each exit u ≺ y, descent of partners along `new_step`, and each entry
  z ≺ s below the partner of s. A context point of C is `ctx_pt C x`, the
  variable 1 + j read as the j-th point of `bc_env C`.
  - (wf-new⁺) is `wf_new_plus` (a map h on a downward closed D) and
    `wf_new_plus_gen` turns it into (gen-new₁). (wf-new) is
    `wf_new_gen`. The examples keep proving `wf_new` and pass it through
    `wf_new_gen` in `d_new'`, `e_new'`, `e_new_tk`.
  - `cons_gen : facts_const W → gen_new W Γ C → cons_open W Γ 1 C`
    (static/PointSubst.v) by the invariant `cinv`, which follows a
    derivation in `hc_open 1 C Γ` through the partners, in four cases by
    where its two ends lie. `cons_new` stays for the E-Open sites of the
    examples.
  - `Erel_new` (compat/Redex.v) takes `gen_new_sem W C`, the same clauses
    with the order of the ranked world. The construction is that of the
    third run, `rank_base (new_step C) b0`. The new part is the invariant
    `Sr s t → rank_base s ≤ rk0 t` by well-founded induction
    (`rank_base_le`, constructive). Exits then hold by `rk0` rising along
    W1. `gen_new_sem_of` (Fundamental.v) gives the semantic form from
    `wmodels W1 W`, `hsat W1 σ Γ` and `slt_sem`, as the E-New case of
    `typed_sem` has them. O-New and the relation clauses did not change.
  - Not done. The finite-set version (gen-new), as instructed. A mechanized
    rejection of rx-chain under (gen-new₁), which check-general-new.md
    argues by its Proposition 7. No example uses an exit yet, and the
    two-upper-bound example is not written as a program.
  - Map (48aef68). New note `w.gennew` in the worlds block, E-New.wf reads
    `π = ρ ⇒ gen_new Γ ρ C`. Lint counts unchanged.
  - Laptop at 48aef68: `make` exit 0, `make test` passes, `make check` 125 of
    125.

Plausibility. No Admitted, no Axiom, no new Parameter. The examples build.
rx-relink, rx-postpone and rx-delegate rest on tickets, aging and payload
credit, which this run did not touch. S4.18 concerns (fuse), kept. rx-chain
stays excluded, argued by Proposition 7 of check-general-new.md, not
mechanized. One edit outside static/ that touches the area of the other
agent, soup/LFTyped.v (the P-Term premise pattern, three lines).
- Map (186308e, 28aa5a5). New note `sty.contr` and premises E-New.contr,
  E-Sub.contr, E-Abs.contr, E-Inj.contr, E-Box.contr, P-Term.contr. E-Box.inst
  cites `typed_sinst`. Sub-Ex shows `Γ, C(ῑ) ⊢ C'(ῑ)` and
  `Γ, C(ῑ) ⊢ T ≤ T'`, Sub-Box the contractive alternative (`tp.sub-boxc`).
  gen.js 0 errors, check.js 0, lint-map 161 metaphor and 316 every/any/all
  (323 before), 0 elsewhere.

## Report, run of 2026-11-22 on the overlap of P-Connect

Branch redesign-comp, from 97a7a3e, commits 059d27c and 32ee457,
nothing pushed. static/Typing.v and the typing rules are untouched.

Repair (a) of the open item "P-Connect's overlap is the shared constants"
is false, and no normalization that only drops unused constants saves it.
examples/SharedRoots.v proves `shared_not_cut`. Each component
P(c, d) = (cl c⁺; cl d⁺) ∥ (cl c⁻; cl d⁻) puts c at the constant 0 and d at
0·0, and its first closes ask 0 ≺ (0·0)‾ and 0‾ ≺ 0·0. Both components type
over the empty interface at the world W0 with the one constant 0 and these
two facts (`comp_typed`). P(c, d) ∥ P(e, f) then types by P-Connect over
the empty cut, and 0 ∈ `swshared` although Σ_C has no point.
`fact_needs_zero` shows that every well-formed world deriving the first
fact holds 0, so each side uses its 0. Both results are closed under the
global context.

Three things put a constant into S outside the roots of Σ_C.

- P-Term asks nothing of the constants of W beyond well-formedness and
  well-foundedness, so a world may hold constants no end mentions. Typing
  reads W only through ≺_W, never through `sw_consts`, so these could be
  dropped, but `sw_facts` is a predicate and the constants its facts use
  are not computable without classical logic.
- Two components may pick the same private constant, as above. Nothing in
  `ptyped` keeps them apart, and E-New picks fresh roots only under ∃ in
  the type, so the static world never records a creation. Renaming apart
  would need a lemma that renames constants through `typed` and `ptyped`,
  which the development does not have. The coincidence also costs
  completeness. If P(e, f) closed d first, its world would order
  0·0 ≺ 0‾ and (0·0)‾ ≺ 0, the join with W0 would hold the cycle
  0 ≺ (0·0)‾ ≺ 0, and P-Connect would refuse a composition that renaming
  0 to 1 in one component accepts (argued, not mechanized).
- Two outer interfaces may share a root. A thread that receives a pair at
  x·0 and x·1 and spawns one half leaves ends at a·0 and a·1 in two
  components, and the cut need not mention a. This sharing is genuine,
  and P-Connect must compare the facts at a.

Repair (b) is therefore needed, in the form the open item states it. With
hiding, a component's world lives on the roots of its own interface, so S
lies in roots(Σ1 ∪ Σ_C) ∩ roots(Σ2 ∪ Σ̄_C), which is the roots of Σ_C
together with the roots both outer interfaces share. The claim "S ⊆ roots
of Σ_C" holds after neither repair, because of the third case. The right
target is "P-Connect compares the two interface orders". Soundness of
hiding is not checked here. The map cites `shared_not_cut` at P-Connect.wf
(`node docs/explorer/gen/gen.js`, 0 errors).

## Report, run of 2026-11-21 on compositional lock-free semantics

Branch redesign-comp in .claude/worktrees/redesign-comp, from bb04f3e,
commits d4858e4 to 6b0995e, nothing pushed. static/Typing.v and the typing
rules are untouched.

- `lf_sem` (soup/Soup.v, d4858e4) no longer asks `s_W a = W`. It reads
  `∀ n, ∃ a, erase (s_q a) = p ∧ a ∈ S^{N,W}_n⟦Σ ⊢ T⟧`, and `Soup` keeps
  `W ⊑ s_W a`, so a state may start at any extension of the ranked world.
  New `soup_inv_mono`: the soup at one index is monotone in the world it
  reads its threads at.
- The judgment at a static world (soup/LFCompose.v). `lf_sems N W Σ p T :=
  ∀ R, wmodels R W → Σ ⊪^N _R p : T`. `lf_p_term` and `lf_fundamental`
  conclude `lf_sems`, the latter by an induction with no world argument.
- Semantic P-Connect. `lf_p_connect : lf_sems N W1 (Σ1 ∪ ΣC) p1 T →
  lf_sems N W2 (Σ2 ∪ Σ̄C) p2 ∗ → (channel premises) → lf_sems N (W1 ⊔ W2) …`.
  At a ranked world R of the join, R models W1 and W2. The first component
  gives a state at some R1 ⊒ R. The second is read at R1, which models W2,
  and gives a state at R2 ⊒ R1. The soup of the first moves up to R2 by
  `soup_inv_mono` (`lf_soup_connect`). Reading the second component at R1
  keeps the fresh roots of the two from colliding, so no renaming of roots
  is needed.
- The composite world. `join_models : sworld_wf W1 → sworld_wf W2 → swf W1
  → swf W2 → swf (W1|S ⊔ W2|S) → ∃ R, wmodels R (W1 ⊔ W2)`, by
  `wf_join_iff` and `wmodels_exists`. The ranks of R are the rank function
  of the joined order (check-layers-open.md §2), never the ranks of a
  component. `lf_sems_adequacy` and `lf_connect_adequacy` (two closed
  components over a cut, at their own static worlds, with the condition on
  the shared constants) conclude lock freedom under EM and FC.
- Why the components are read at every ranked world of their static world,
  and not at one fixed R1 and R2 each. A ranked world orders two ranked
  points whenever their ranks differ. So R1 ⊨ W1 may put y ≺ x̄ and
  R2 ⊨ W2 put x̄ ≺ y for shared points that no fact relates. A thread that
  holds c⁺ at x and waits on d⁺ at y is ready in R1, its partner that holds
  d⁻ at ȳ and waits on c⁻ at x̄ is ready in R2, and the composite deadlocks,
  with W1 = W2 free of facts and `swf (W1|S ⊔ W2|S)` true. A semantic
  P-Connect from fixed R1 and R2 is therefore unsound, whatever re-ranking
  of the join is chosen (argued, not mechanized). The universal reading
  compares the components only through their static worlds, at the shared
  roots, as the static P-Connect does.
- Deadlock-free side. It already composes this way. `proc_gen` proves
  `∀ R, wmodels R W → sem_ptyped κ R Σ p T`, and P holds a process itself at
  a ranked world with no starting state, so both components are read at one
  R that models the join. `sem_p_connect_sw` (static/FundamentalProc.v,
  6b0995e) states it at static worlds, with `sem_ptyped_sw`.
- Test (5fd3db7). examples/LFClientServerSplit.v splits the client-server
  program into two components over the cut {a⁺ at ρ, b⁺ at ρ·0}. The client
  lives in W_cli, the laws `cs_L` at the constant 0 and polarity true, the
  server in W_srv at polarity false. Each thread is `App (EForce box)
  (Pair ends)`, typed by P-Term at N = 6, and the box constraint holds by
  the facts of its own world. The join is well-founded by the measure
  (field sum, offset, depth) (`swf_lex3`), which gives the condition on
  the shared constant through `wf_join_iff`. `cs_split_lock_free` follows
  from `lf_p_term` on each side and `lf_connect_adequacy`.
- Checks on the laptop. `make -j8` builds with no error, `make test` passes
  after SoupNotations.expected was regenerated for the new
  `lf_fundamental`, and `make check` reports 122 of 122 results closed
  under the global context (new: `lf_soup_connect`, `join_models`,
  `lf_sems_adequacy`, `lf_connect_adequacy`, `cs_split_lock_free`,
  `sem_p_connect_sw`). No Admitted, no Axiom, no new Parameter. EM and FC
  stay hypotheses. Every LF example and `lf_soundness` build unchanged.
- Map (b0040f4, 6b0995e). The annotated configuration carries its ranked
  world R_a, the lock-free process relation reads threads at R_a with
  R ⊑ R_a, the lock-free judgment reads `∀ R ⊨ W`, and the composition
  block has a row for P-Connect in the lock-free judgment with the note
  `th.lf-p-connect`. New notes `sp.world` and `sp.allR`. gen.js reports 0
  errors, check.js 0 mathjax errors, lint-map 0 semicolons, 0 coined words,
  0 sentences over 35 words, 161 metaphor and 322 every/any/all against 323
  before.

## Report, fourth run of 2026-11-21 on typed_sinst and rx-chain

Branch redesign-clean3 in .claude/worktrees/redesign-s4, nothing pushed,
commits 1a0a873 to the head.

- Item 1, `typed_sinst`. The lemma as stated is false, and the run proves the
  negation instead (`typed_sinst_false`, v2/examples/SinstStuck.v).
  - Counterexample. With X = µβ.β, s0 = α ; X and s1 = (α ; Skip) ; X unfold
    to the same head α with tail X, so s0 ≈ s1 and
    c : s0@x ⊢ c : s1@x by E-Chan and E-Sub. The instance
    α := ?(∗) ; (Skip ; Skip) satisfies `sinsts N`. Under it both heads are the
    same receive, with tails (Skip ; Skip) ; X and ((Skip ; Skip) ; Skip) ; X.
    Both tails are stuck, because X never reaches a head, and `sequiv`
    compares stuck terms on the nose. So the two instances are not
    equivalent (`ss_inst_not_sequiv`, by computation at depth 2), and no
    derivation types c at the instance of s1.
  - New inversion lemma `inv_chan_sty` (static/Inversion.v). A channel typed
    at an end type has in Θ a session type ≈ to the one of that type.
  - Consequence for the algorithm (finding 6.1, corrected there). Checking a
    box body once at the identity instance accepts boxes that E-Box rejects,
    whenever the body uses a session type that is not contractive. A box
    whose body creates a channel at s0 and returns its ends at s1 and
    dual s0 is such a box (argued, not mechanized). Two ways out, both decisions for the author. One
    is a contractivity premise wherever a session type enters a derivation
    (E-New, the ends of P-Term, the target of E-Sub). The proof of
    `typed_sinst` then also needs that `sfuel s` is enough fuel for `unrN` on
    every contractive s, and that `sequiv` is closed under `sinst` for
    contractive types. Neither lemma exists. The other is a `sequiv` that
    does not compare stuck terms syntactically.
  - CheckAll.v prints the assumptions of `inv_chan_sty` and
    `typed_sinst_false`. The map cites `typed_sinst_false` at the note
    E-Box.inst.
- Item 2, rx-chain. Not started, because item 1 did not land as a theorem.
  The proof also needs more than inversion through the rules of the
  program. Inversion.v has no lemma for Lam, App, Box, Force, Spawn, New,
  Send or Var. More importantly, the box `grow` may carry any constraint C,
  and `bc_facts` is a predicate, so C may be infinite and closed under the
  shift of one round. Rejecting the field case needs an induction over the
  rounds. C at the point of w entails C one level lower, so Γ of main
  entails an infinite descending chain in the tree of the root of w. That
  contradicts `wf_new` of the creation in main only through a lemma that
  `slt` under `hc_open` of a `wf_new` constraint, restricted to the new
  tree, lies in the transitive closure of C and program order. The fresh
  root case needs that the point of w lies outside the tree of the new root.
  rejects.js still says the rejection is argued.

## Report, third run of 2026-11-21 on layers, plain new and well-formed existentials

Branch redesign-clean3 in .claude/worktrees/redesign-s4, nothing pushed. The
session crashed three times. Every sub-step that built was committed, from
4066cf1 to the head. redesign did not move and needed no merge.

- Stage 3, layers together with plain `new`. Done.
  - Syntax (4066cf1). `ENew` carries no label, `new_κ` and `LNewAt` are gone,
    and `LNew c` names only the channel. A creation at a field is written
    `⟨y, new⟩` in the examples.
  - Worlds (1bd3062, types/Worlds.v). A static world `sworld` has constants
    and facts, no families and no laws. A ranked world `world` has a finite
    set of roots `w_roots`, a rank `w_rank : point → ord@{Set}` and program
    order on its roots (`w_po`). `W ⊢ x ≺ y` is program order or a rise of
    rank between ranked points, so it is transitive, irreflexive
    (`w_lt_irrefl`) and well-founded (`w_lt_wf`) in every world. An extension
    keeps the roots and their ranks. `wmodels R W` says that R ranks every
    fact of W, `wmodels_exists : sworld_wf W → swf W → ∃ R, wmodels R W`.
    `swf W := wf (sw_lt W)` with `wf` of relation/Ranks.v.
    `wf_join_iff : swf (W1 ⊔ W2) ↔ swf W1 ∧ swf W2 ∧ swf (W1|S ⊔ W2|S)` is
    constructive, by nested accessibility on the amalgam and on each side.
    `strict`, `wfworld`, families, laws, generated roots, `wfrename` and
    static/Renaming.v are gone.
  - Typing (b64f02e). E-New at a fresh root asks `wf_new C` (static/Contexts.v):
    every fact of C ends in the tree of the variable 0, and C with program
    order is well-founded on that tree. E-New-Field (`e_new_fld`) creates at
    any `x·κ` and returns the pair, its constraint would be entailed. P-Term
    asks `sworld_wf W ∧ swf W`, P-Connect asks `swf (W1|S ⊔ W2|S)`,
    `ptyped_wf` replaces `ptyped_strict`. (wf-new⁺) is not implemented.
  - `cons_new : facts_const W → wf_new C → cons_open W Γ 1 C`
    (static/PointSubst.v) replaces `cons_law` at every E-Open site.
  - Relation (55626a6). O-New is `cfresh c Θ → ∃ S π W', W ⊑ W' ∧ e' at W'`,
    and `q_tau` lets a τ step of P continue at some `W' ⊒ W`. `Pbody` lost
    `strict W1`. DF adequacy follows the worlds of a run.
  - `Erel_new` (6585afc, compat/Redex.v). Under (wf-new) the creation picks a
    constant a that the world and the context points do not use, grows the
    world by a and the roots of the context points (`wgrow`), and ranks the
    tree of a by `rank_base` (relation/Ranks.v) through `pt_unroot`
    (types/Points.v), above each context point below the tree.
  - Fundamental theorem (e194e57, 14d166c). `typed_sem` reads every ranked
    `W1` with `wmodels W1 W`, and `ent_sound` is `slt_sem` through
    `wmodels_lt`. `fundamental_proc W R`, `soundness` builds R by
    `wmodels_exists`. `live_sub_df` takes `excluded_middle` and
    `functional_choice` to fix one world for every level after a creation.
  - P-Connect composes at one ranked world (`sem_p_connect`, `soup_connect`).
    The composition context `cctx` carries `G1W`, `G2W` and `LW` for the
    worlds a τ step grows to.
  - Soup (bb89e8c to de0aa79). A state carries its world `s_W`, and
    `Soup N W n Σ T a := W ⊑ s_W a ∧ soup_inv at s_W a`. A creation choice
    `tchoice` holds the tickets, the point and the grown world, and
    `lf_next` takes them. `lfsoup_run` gives one choice per position and the
    chain `s_W (a k) ⊑ s_W (a (k+1))`. `lf_sem` starts at the world itself,
    so two components meet at one world.
  - Criterion (67a20ac). The order of the run is `wchain_lt`, a fact in some
    world of the chain, well-founded by `wchain_lt_wf`. A waiting thread is
    ranked by the point of the end it waits on. `lf_adequacy`,
    `lf_thread_progress` and `lf_soundness` have no premise on the world.
  - Examples (55d1616 to d61152d). All eighteen move. Each creation at a
    fresh root states its old family laws as C and proves `wf_new` by a
    lexicographic measure (`wf_new_lex3`), the measures of the old
    `W_*_wfworld` lemmas. Static worlds of the examples are `sw_empty`, or
    the constant worlds of SemBranch and TreeTopo. The semantic parts of
    SemBranch, TreeTopo and FlagPair read one ranked world.
    LFClientServer uses the measure (field sum, offset, depth), whose ranks
    lie below ω³.
  - Checks. rx-chain is excluded by `wf_new` (a fact down to a context point
    fails its first clause), argued, not mechanized. `sbv_rejected` holds,
    now from `swf_irrefl` of the joined world. `lk_typed` holds.
    `fp_unrealizable` holds at one ranked world. Every LF and DF example
    builds.
- Stage 4, `typed_sinst`. Not started. The run spent its time on stage 3.
- Stage 5, well-formed existential types (c7a7e60). `ex_wf W Γ lb m C T :=
  lbx_below_h W (hc_open m C Γ) (lb_map (pt_inst (pshift m)) lb) (heads T) (hbot T)`
  (static/Contexts.v) is a premise of E-Pack and of `d_pack`. The two pack
  sites of the examples (FactoryEx, LFFactoryEx) pack at ⊥ and discharge it
  by `I`. The fundamental theorem ignores it. The map shows it as the
  premise `Γ, C ⊢ l ≼ T` of E-Pack (`E-Pack.wf`).

Plausibility. No Admitted, no Axiom, no new Parameter. rx-relink,
rx-postpone and rx-delegate rest on tickets, aging and payload credit, which
this run did not touch. S4.18 concerns (fuse), kept. rx-chain is now
rejected by (wf-new) instead of `wfworld`.

Final state. On the laptop `make -j8` builds with no error, `make test`
passes after the .expected files of TypeNotations, RelationNotations,
CostNotations, GuardNotations and SoupNotations were regenerated for the new
signatures, and `make check` reports 114 of 114 results closed under the
global context.

Map (80a5e13, bc4f947). The LAYERS and NEW2 tags are gone, and the rocq
references of worlds, O-New, E-New, P-Term, P-Connect, the soup and the
theorems name the new definitions. O-New and Q-Tau read `∃ S, π, W' ⊒ W`.
gen.js reports 0 errors, check.js 0 mathjax errors, lint-map the counts of
before (323 every/any/all, 161 metaphor, 0 elsewhere).

## Report, second run of 2026-11-21 on transfinite indices and layers

Branch redesign-clean3 in .claude/worktrees/redesign-s4, nothing pushed.
redesign was merged once (de69df2) and did not move afterwards.

- Stage 2, transfinite step indices. Done.
  - The port (3b1297f, after the WIP commits 5448493 to 6f1eec9). V, E
    and P, FuelE and Vfuel and the soup are indexed by `Ix := ord`
    (relation/Ord.v). `at_cost_E n c` reads the continuation at every `j`
    with `ole (oadd j c) n`. The fixpoints are `osfix` over one argument sum
    (`RelA`, `FLevA`), and relation/Sfix.v is gone. The arrow reads its body
    at every `j` with `j + κ(β) ≤ n` through the readers below n and, when β
    is free, by unfolding V and E at `j ≤ n` from those readers, so no case
    split `j < n ∨ j = n` is needed. E is the least fixpoint at every level.
    P holds every process at a level with nothing below it (`Ptop`), and a
    payload is also read at level 0 (`at_cost_V`), the truncated level of
    finite indices. Without these two, composition at level 0 lacks the
    exactness of payloads. The limit cases of the `induction n` and
    `destruct n` sites became well-founded induction (`oind`). The joint
    inductions of renaming and conversion now prove V at every `j ≤ n` by
    induction on the type. `child` in compat/PTerm.v proves level n and
    goes down. Deadlock-freedom adequacy reads the finite levels `onat k`.
  - Scoped instances (2154509). `sinsts` and the V-box ask
    `Forall hcontractive ss ∧ Forall sscoped ss` (finding 6.1).
    `typed_sinst` is not proved, see below.
  - The existential property (c34125c). relation/ExProp.v proves
    `exist_prop : excluded_middle → functional_choice → ∀ X P, (P down-closed)
    → (∀ α, ∃ x, P x α) → ∃ x, ∀ α, P x α`, by the limit of one failing
    level per witness. `functional_choice` is a new definition next to
    `excluded_middle` and `dependent_choice` in lockfree/FairRun.v, an
    argument, never an axiom.
  - Creation tickets. E-New and E-NewAt take tickets `m1 m2` with
    `tsum_ok N m1 m2`, F-New asks `∃ S m1 m2, tsum_ok N m1 m2 ∧ …`, and the
    soup update takes the choice (`lf_next tc`, `lf_run_state tcs`).
    `lfsoup_step : a ∈ S_n → itstep → ∀ lv < n, ∃ tc, tsum_ok ∧ lf_next tc a ev q' ∈ S_lv`.
    `lfsoup_step_all` picks one tc for every level by `exist_prop`, and
    `lfsoup_run` builds the run from one choice per state and position by
    functional choice and recursion, so dependent choice is not needed.
  - The soup's `∃ a` before `∀`. `lf_sem N W Σ p T := ∀ n, ∃ a, erase (s_q a) = p ∧ a ∈ S_n`.
    `lf_sem_state` recovers one state for every index under EM and FC.
    `lf_adequacy`, `lf_thread_progress`, `lf_soundness` and the LF example
    theorems take `excluded_middle` and `functional_choice`.
    `soup_no_tau_divergence` stays constructive by a per-level reachability
    lemma (`lfsoup_isteps`).
  - Link example (dcd1dd6). examples/LFLink.v proves `lk_typed`, a thread
    holding c⁺ at x and d⁻ at x‾ at N tickets types `ELink ⟨c⁺, d⁻⟩` for
    every N ≥ 1, and `lk_new`, E-New gives ends at N and 0 tickets. Under the
    fixed split this link typed for no even N (finding 6.12). A full closed
    program with a link was not built.
  - Not done in stage 2. The interface ends of P-Term keep N/2 tickets
    (`tenv_of (fhalf N)`, `sp_sigcap`). E-NewAt in the examples keeps the old
    instance through the wrapper `e_new_at'`.
- Stage 3, layers. Groundwork only (26f8b7f). relation/Ranks.v defines
  `rank_ord := ord@{Set}`, `ranked R ρ`, `wf R`, and proves
  `wf_iff_wellfounded`, constructively, with the rank of a point the limit of
  the successors of the ranks below it over the subtype of points below it.
  The obstacle is size, not design. Ranked worlds replace `world` in the
  relation, every E-New site moves from families to plain `new` with C, and
  `wfworld`, `strict`, families, laws and generated roots leave Worlds.v, the
  typing rules, the soup and all eighteen examples. That did not fit after
  stage 2. Still open are ranked worlds, (wf-new) at E-New, O-New picking ranks
  through `exist_prop`, `wf (W1|S ⊔ W2|S)` at P-Connect and `wf W` at P-Term,
  `wf_join_iff`, `ent_sound`, `cons_open` under ranks, the criterion ranking
  by the end a thread waits on, and the checks of rx-chain, LFClientServer
  and `sbv_rejected`.
- Coordinator additions. Finding 6.1 premise landed, `typed_sinst` not
  proved. It is an induction over every rule of `typed` with session
  substitution through contexts, aging, subtyping, `unfoldS`, `dual` and the
  binders of nested boxes. Finding 6.3, well-formed existentials, waits for
  layers and was not started.

Plausibility. Every LF and DF example builds. `soundness` is closed under the
global context, and `lf_soundness` takes EM and FC as arguments and is closed
too. The rejects.js programs and S4.18 rest on mechanisms that stage 2 keeps
(aging, payload credit, E-Link's `lgt`, `wfworld`, the clause (fuse)).
rx-relink, rx-chain, rx-postpone and rx-delegate are unchanged in kind,
because no world or ordering premise changed. Chosen tickets only add
derivations.

Final state. `make -j2` builds with no error. `make test` passes after the
.expected files of RelationNotations, FuelNotations, CompatNotations and
SoupNotations were regenerated. `make check` reports 110 of 110 results
closed under the global context. No Admitted, no Axiom, no new Parameter.

Map (243c6b2). The TRANSFINITE planned tags are gone. The relation and fuel
blocks and the theorems use α and β as levels, the soup and the classical
hypotheses cite the Rocq, the V-box asks scoped instances, and NEW2 no
longer claims fixed creation tickets. The LAYERS tag stays and mentions
relation/Ranks.v. gen.js reports 0 errors, check.js 0 mathjax errors,
lint-map 0 coined words, 0 semicolons, 0 sentences over 35 words, and 323
every/any/all against 326 before.

## Report, run of 2026-11-21 on tickets, transfinite indices, layers and E-Open

Branch redesign-clean3 in .claude/worktrees/redesign-s4, nothing pushed.
Step 0 merged redesign. Later merges of redesign are 829beea and 933ca2e.

- Stage 1, tickets as one cap per end. Done (22d7a0a). `TSess S x a m`,
  `lgt N a m := a + m > N`, `tsum_ok N m1 m2 := m1 + m2 ≤ N`. E-Link asks
  `lgt N a1 m2` and `lgt N a2 m1`. P-Term asks `tsum_ok` of each restricted
  channel. The soup keeps `sp_cap`, `sp_tsum` and `sp_sigcap`, and adequacy
  measures on ℕ with `<`. ϑ, `tix`, the refill monotonicity in N and
  cost/Transformers.v are gone. Creation tickets are fixed: new_ℓ starts at
  N/2 and N − N/2, new_κ o at m and N − m, interface ends at N/2, until the
  existential property gives a free choice. `lf_sem` is parametric in N, so the
  sides of P-Connect share N. The LF examples type at twice their old bound.
- Stage 2, transfinite step indices. Groundwork only (8769bc2).
  relation/Ord.v proves `olt_wf`, `oadd_lt` and `osfix_unfold` (well-founded
  recursion, unfolding up to pointwise ↔, no funext, no axiom). The port of the
  relation, fuel and the soup to α is not done. It is the 43-file change of
  check-transfinite.md and no design obstacle was found.
- Stage 3, layers. Not started. O-New picks ranks through the existential
  property of stage 2, and the removal of families, laws and generated roots
  rewrites every world and E-New site. `wf_join_iff` and `ent_sound` are open.
- Stage 4, E-Open conservativity and the flag variant. Done on the pre-layer
  worlds (3381fd4). `cons_open W Γ m C := ∀ x y, slt W (hc_open m C Γ)
  (pt_inst (pshift m) x) (pt_inst (pshift m) y) → slt W Γ x y` is a premise of
  E-Open (Rocq name `cons_open`, because `cons` is the list constructor).
  `cons_law` discharges the 15 example sites. It asks only that the facts of W
  sit at constant roots (`facts_const`). `opened_cons` and `inv_chan` are in
  static/Inversion.v. SemBranch proves `Tbad_not_cons`, `sbv_thread_E`,
  `sbv_deadlock_free` and `sbv_rejected : ∀ N W, ¬ ptyped N W ∅ sbv_config TUnit`.
  `sb_dead_arm_typed` is gone.

Plausibility. All LF and DF examples build, `lf_soundness` and `soundness`
are closed under the global context, and stage 4 only removes derivations.
The rejects.js programs are argued, not mechanized, and their mechanisms
(aging, payload credit, E-Link's `lgt`, wfworld) are as before. S4.18 concerns
(fuse), which no stage touched.

Final state. `make -j2` builds with no error. `make test` passes after the
.expected files of TypeNotations, FuelNotations, CostNotations and
SoupNotations were regenerated for the stage 1 judgments. `make check`
reports 106 of 106 results closed under the global context. No Admitted, no
Axiom, no new Parameter.

Map. Stage 1 removed the TICKETS tags. Stage 4 removed the planned tags of
E-Open and the flag example, and the flag example now cites `sbv_rejected`.
The TRANSFINITE note says that relation/Ord.v exists. The LAYERS and NEW2
tags stay. gen.js reports 0 errors, check.js 0 mathjax errors, lint-map 0
coined words, 0 semicolons, 0 sentences over 35 words.

## Report, earlier next run of 2026-11-21 (stages 1 to 4)

Branch redesign-clean3 in .claude/worktrees/redesign-s4, nothing pushed.
Step 0 merged redesign by fast forward (78db2c2). The coordinator
limited the run to stages 1 to 4. Stages 5 and 6 (fair runs, the
Padovani corollary) run on branch redesign-fair. No lemma in this run
builds on ϑ, χ, families or wfworld beyond what the stages touched.

- Stage 1, entry 12, per-end capture. Done (4d71675). `TLolli` lost the
  floor h, capture is aging by a (`thage`, `lage` at E-Abs), FV-Arrow
  asks the captured counters of the ends that are not idle at least a
  and accepts any call counters f′ ≥ f − a, Sub-Arr asks a′ ≤ a.
  `tcap`, `lcap`, `thcap` and their lemmas are gone.
- Stage 2, entry 12, generalized arrows. Done (f30a0ed). Upper point
  `ubound` (none, a point, ⊤), lower point `lbound` (none, a point, ⊥).
  E-SpawnLam and `Vthunk` are gone, `e_spawn_lam` and `d_spawn_lam`
  are lemmas (E-Abs at (⊤, ⊥) and credit 1, then E-Spawn), and O-Spawn
  reads `Varr` at `∗ ⊸^⊤_⊥ ∗`.
- Stage 3, entry 14b, no future variables. Done (7545c89). Γ holds only
  constraint instances, the rest of a future is everything above u or
  everything, and the semantic reading quantifies one set R above u
  (`rest_ok`). The relation keeps finite futures.
- Stage 4, entry 7, inversion and static rejections. Partly done (08bc06b).
  Inversion lemmas for E-Close, E-Case, E-LetU, E-LetP, E-Pair, E-Let,
  P-Term and P-Connect in v2/static/Inversion.v. Stopped:
  `sb_untypable`, the static half of FlagPair and rejects.js. E-Open in
  a dead arm can add facts from an existential that no value inhabits,
  so facts of an opened Γ do not transfer to W. `sb_dead_arm_typed`
  shows it on the flag program. A variant of the flag program whose
  arms read their binder is, on paper, statically typable, against
  docs/redesign/semantic-example.md (entry 7). The programs of
  rejects.js need the cost and ticket judgments, not an inversion.
- Stages 5 and 6. Not reached, moved to redesign-fair by the
  coordinator.

Plausibility, each stage. The lock-free and deadlock-free examples
build, `lf_soundness` and `soundness` build with no new axiom, so the
four programs of rejects.js stay excluded. The S4.18 counterexample
concerns (fuse), which no stage touched. SemBranch, TreeTopo and
FlagPair build. The details sit under entries 12, 14 and 7.

Final state at the commit of this report. `make -j2` builds with no
error. `make test` passes after test/FuelNotations.expected was updated
to `Vfuel_age`. `make check` reports 93 of 93 results closed under the
global context. No Admitted, no new axiom.

Map. After stage 1 the floor h, the capture block t-cap and its notes
are gone, FV-Arrow and E-Abs.cap cite the Rocq, and the capture blocks
lost their planned tags. After stage 2 the planned tags of entry 12 are
gone, the blocks E-SpawnLam and V-Thunk and their notes are gone, and ⊤
and ⊥ cite `ubound`, `ub_below_u`, `abs_fut` and `Varr_top`. After stage
3 Γ is a list of constraint instances, F has the rests ↑u and ↑, and
E-Abs, E-Box, u ≺ F and the semantic reading den_{R,B} follow the Rocq.
After stage 4 the static rejection of the flag program is marked
doubtful. The plain-new planned
tags and χ are untouched. gen.js, check.js and lint-map report 0
errors, 0 coined words, 0 sentences over 35 words.

## Report, entries 4 and 5, branch redesign-fair, 2026-11-21

Both entries landed, on top of 4d71675 (redesign-clean3).

- Entry 4 (6e9bcde). New file v2/lockfree/FairRun.v. The hypotheses are
  two definitions, `excluded_middle := ∀ P : Prop, P ∨ ¬ P` and
  `dependent_choice := ∀ A (R : A → A → Prop), (∀ x, ∃ y, R x y) →
  ∀ x0, ∃ f : nat → A, f 0 = x0 ∧ ∀ n, R (f n) (f (S n))`. Both are
  arguments of the lemmas, no axiom and no Parameter.
  `fair_run_exists : excluded_middle → dependent_choice → ∀ q : config,
  ∃ r l, r 0 = q ∧ maximal r l ∧ wfair r l`.
  `fair_run_exists_proc` gives the same with `erase (r 0) = p`, through
  `erase_surj`. The scheduler targets thread `rr n = n - ⌊√n⌋²` at
  position n, which goes round robin over 0, then 0..2, then 0..4, and so
  on. It steps the target when the target is enabled, any thread
  otherwise, and repeats a stuck end. Dependent choice picks the steps
  from `istep`, and excluded middle decides enabledness and stuckness. No
  step function and no redex finder. The lemma reads only the
  operational semantics (`itstep`, `tenabled`, `stuck`), no ticket, world,
  point or step index.
  `lf_soundness_run N W p T : excluded_middle → dependent_choice →
  wfworld W → ∅ ⊩^N _ W p : T → lock_free p ∧ ∃ r l, erase (r 0) = p ∧
  maximal r l ∧ wfair r l` in soup/LFTyped.v. It uses `lf_soundness` only
  through its conclusion, so it survives the planned change of tickets,
  χ and wfworld once `lf_soundness` is restated. `lock_free` is unchanged
  and still quantifies over every maximal weakly fair run.
- Entry 5 (5bd777a). `lf_padovani p := ∀ q0 q t, erase q0 = p →
  itsteps q0 q → pend q t → ∃ q1 ev q2, itsteps q q1 ∧ itstep q1 ev q2 ∧
  t ∈ ev_parts ev`.
  `lock_free_padovani : excluded_middle → dependent_choice → ∀ p,
  lock_free p → lf_padovani p`. The proof starts a fair run at q and
  prefixes it with the path from q0 (`run_prefix`, `run_cons`,
  `run_itsteps`). `lf_soundness_padovani` states it for typed p, again
  through `lock_free` only. Checked against Padovani 2014, Def. II.1
  (pdf p4). Padovani's form is per channel, wait(a, Q) and a reachable
  R with sync(a, R), a synchronization that is possible and need not be
  taken. Ours is per thread and asks the step itself, so it is the
  stronger reading. The fact is in the paper store.
- Plausibility. `fair_run_two_threads` applies the lemma to
  `(∅, {[0 := EUnit; 1 := EUnit]})`. `Print lock_free` still shows the
  universal over runs.
- Map. Notes `th.fair-run-exists` and `th.lf-padovani` with signatures,
  both as rows of the soundness block. `gen.js` reports 0 errors.
- make check: 98 of 98 results closed under the global context (the five
  new ones included). The first run segfaulted, the retry passed.
- make test: fails on test/FuelNotations only. The base commit 4d71675
  renamed `Vfuel_recount` to `Vfuel_age` and left FuelNotations.expected
  stale. This branch touches neither fuel/ nor test/. Every other
  notation test passes.
- Nothing failed in the two entries.

## Morning report, overnight run of 2026-11-20

Branch redesign-clean3 in .claude/worktrees/redesign-s4, nothing pushed.
Step 0 merged redesign (0c7756e). The explorer sources conflicted where
one side had removed `prim` and the other `hbot`, and the merge removes
both. One note of the merged map (ev.pick) used the word "holder" and a
sentence of 37 words, and the merge rewords it.

- Stage 1, entry 6, credits only on ends and closures. Done (61ad17b,
  dccb8a4). E-Send ages its payload operand by one and subtypes it to the
  declared payload. Sub-Ex now compares bodies by `tsub`, so V's
  monotonicity along subtyping is proved under every point instantiation.
- Stage 2, entry 13, P-Connect over the shared roots. Done (69526fa,
  f0f9344). `ptyped_strict`, `p_connect_join`, `strict_bare`. p_join is
  gone and the process theorems lost their `strict W` premise.
- Stage 3, entry 14, ⊥ folded into heads. Left out by the rule "only if it
  shortens proofs" (d5ff8e6), with the counts in entry 14.
- Stage 4, entry 2, one plain new. Stopped at the feasibility check of
  risk (a) (d5ff8e6). The soup fixes its state for every index and
  updates it from the event, which names neither the point nor the
  constraint of a plain new, so a choice per level cannot be fixed. Three
  repairs and a note on risk (b) are in entry 2. No Rocq change.
- Stage 5, entry 7. Partly done (f756da5, 86c4991). `fp_unrealizable`
  (v2/examples/FlagPair.v) shows two threads that branch on one received
  flag are in E together in no pair of worlds with a strict join. The four
  programs of rejects.js are not mechanized, v2 can neither build an
  infinite run nor invert `typed`.
- Stage 6, entry 4, a weakly fair run exists. Not done (4d37d51). A run is
  a function, and building it from Prop-level steps needs dependent choice
  or a step function that v2 lacks.
- Stage 7, entry 5. Not reached, it needs stage 6.
- Stage 8, the map's notation in the Rocq. Partly done (96d5f7e, 4d2ec2b).
  `tfin` is ϑ(0) ∈ ℕ, `cr_le` is cr(Θ) ≤ N, `soup_gen_iff` reads the soup
  as relation, fuel and `soup_consistent`. Not done: one map Φ in the
  fuel layer, and Pbody over pstep. The open question is written up
  under entry 8 and nothing is decided.
- Stage 9, remove the clause (fuse) of P. Not done (dca9d20, entry 15).
  A probe that dropped the clause fails first in Relation.v
  (`Pbody_mapX`), and the clause has uses in 14 files. Entry 15 lists
  what the work needs. The probe was reverted.
- Stage 10, entry 11, faithfulness audit. Done for the cited Rocq names and
  the theorem statements (ca7c7a7). Six dangling names, names cited in
  the wrong file, and four theorems on the map that still ask `strict W`.
- Design checks (c258c50, 8823fb2), write-ups only. No future variables
  holds, checked by two lemmas in a scratch file
  (docs/redesign/check-future-variables.md). Per-end capture holds on
  paper and removes the floor h (docs/redesign/check-per-end-capture.md).
  The type-directed ticket split does not go through as stated
  (docs/redesign/check-ticket-split.md).

Final state of v2 at e64095d. `make -j2` builds with no error.
`make test` passes, after the expected outputs of CostNotations,
FuelNotations, GuardNotations and SoupNotations were updated to the new
signatures (e64095d). `make check` reports 93 of 93 results closed under
the global context. No Admitted, no new axiom. Map. No edit after the
merge. check.js reports 0 mathjax errors and lint-map reports 0 coined
words and 0 sentences over 35 words.

Since 2026-11-19 the author reviews the explorer map (docs/explorer) and
asks for changes. Each change goes into the map at once and into this list.
One proof-repair agent later implements the whole list in the Rocq in a
single run. Where a change turns out implausible in the Rocq, the agent
reports and the author decides.

Each entry: what changes, where the map already shows it, what the Rocq
must do, open questions.

## Decisions of the author on the overnight report, 2026-11-20

- **Entry 2, plain `new`.** Families stay in the Rocq for now. The author
  does not want families, facts fixed in the world instead of in the type
  of `new`. Proposal of 2026-11-20, on the map as planned: a creation
  choice χ, fixed before the level as A and Φ are. The lock-free semantic
  judgment reads `∃ N, a, χ. erase(q_a) = p ∧ ∀ n. a ∈ S^{N,W,χ}_n`, the
  thread relation is `E[κ_L, χ]`, O-New under lock freedom asks
  `(π, C) = χ(e, Θ)(a)` for the fresh root a, and `lf_next^χ` places the
  new ends at π and grows the world by C. Under deadlock freedom O-New
  keeps its existential. For a typed thread χ is the choice of its E-New
  step. Open: whether χ applied to the creating term counts as reading
  syntax (it is an existential function the relation applies, no clause
  inspects the term), and what χ is keyed on if not (e, Θ). A write-up
  checks the proposal on O-New and the fundamental theorem. The same
  write-up checks a condition on C that keeps the union of
  the worlds of a run well-founded. Test it against the client-server
  constraint `ι+k ≺ (κ+k)‾` and against the growing chain `rx-chain`. A
  criterion that compares ranks within one position only is unsound,
  because it accepts `rx-chain`, which is not lock free. Decide after the
  write-up.
- **Entry 15, the clause (fuse).** Kept. The map writes it readably as
  `(h, D)·p` for `pfuse h D p` and `(h, D) ∈ Fus(Σ, p)` for
  `fuse_ok h D Σ p`. No removal attempt.
- **Entries 4, 5 and 7.** Build inversion lemmas for `typed` through
  E-Case, E-Close, E-Let and P-Connect, then mechanize the static
  rejections (the flag example `sb_untypable`, `FlagPair`, the programs of
  `rejects.js`). State "a weakly fair run exists" with dependent choice as
  an explicit hypothesis of the lemma, no axiom. Entry 5 follows from it.
- **Entry 14b, no future variables.** Adopt in the Rocq.
- **Entry 12, per-end capture.** Adopt in the Rocq.
- **Classical hypotheses (2026-11-21).** The lock-free adequacy theorem may take
  excluded middle and choice as explicit hypotheses. This admits transfinite
  step indices (check-transfinite.md) in place of χ.
  Rocq, stage 2 of the run of 2026-11-21 (redesign-clean3): groundwork only.
  relation/Ord.v has universe-polymorphic cumulative Brouwer trees `ord@{u}`,
  the order `ole`/`olt` by structural recursion (no inversion of a limit, so no
  dependent-equality axiom), `olt_wf`, `oadd β c` with `oadd_lt`, and `osfix`
  by well-founded recursion with `osfix_unfold` up to pointwise ↔, no funext.
  Not done: the port of Rrel, FuelE, the soup relations and the 28 `induction n`
  and 46 `destruct n` sites to α. Nothing in it is a design obstacle. The port
  is the 43-file change of check-transfinite.md section 4 and did not fit the run
  after stages 1 and 4. The existential property, χ removal and the EM ∧ AC
  hypotheses of lock-free adequacy wait for it.
  Rocq, stage 2 of the second run of 2026-11-21: landed (3b1297f port, c34125c
  existential property). Every relation, fuel and the soup are indexed by `Ix`,
  E-New and E-NewAt choose their tickets, and lock-free adequacy takes
  `excluded_middle` and `functional_choice` as hypotheses.
- **Tickets are caps, one number per end (2026-11-21).** The old tickets ϑ go.
  An end type `(S@x)^a_m` carries m tickets, `tk(o) + tk(ō) ≤ K` holds for
  every channel, and E-Link asks `a1 + m2 > K` and `a2 + m1 > K`
  (check-links-without-tickets.md, last section).
  Rocq, stage 1 of the run of 2026-11-21 (redesign-clean3): landed. `TSess S x a m`,
  `lgt`, `tsum_ok`, `sp_cap`, `sp_tsum`, `sp_sigcap`, measure `fu` on ℕ with `<`.
  The bound keeps the name N. new_ℓ starts its ends at N/2 and N − N/2, new_κ o at m
  and N − m, interface ends at N/2, because the caps of a creation need an index-free
  source until the existential property lands.
- **Layers and fuel extension (write-up A3, 2026-11-21, decided).**
  check-layers.md. Points as ordinal ranks hold with a well-founded C per fresh
  root and fields ranked in advance. Client-server and every lock-free example
  type. Fuel extension removes N and does not remove K. The author adopts
  layers for the next Rocq run, together with tickets and transfinite indices.
  Tickets stay finite with N and K for now. Ordinal tickets may come later.
  Confirmed after explanation (2026-11-21). Ranks are ordinals, not naturals,
  because the server end of LFClientServer sits above an unbounded ascending
  chain of client points (rank ω, ranks up to ω²+1). Ranks reuse the
  Brouwer-tree type of the step indices.
  Rocq, stage 3 of the run of 2026-11-21 (redesign-clean3): not started.
  O-New picks the ranks inside the relation, which needs the existential
  property of stage 2, and the removal of families, laws and generated roots
  rewrites every world and every E-New site of the examples. `wf_join_iff`,
  `ent_sound`, (wf-new) at E-New and the wf premises of P-Connect and P-Term
  are open. Ranks can reuse `ord@{Set}` of relation/Ord.v. Stage 4 ran on the
  pre-layer worlds as the coordinator allowed.
  Rocq, stage 3 of the second run of 2026-11-21: groundwork only (26f8b7f).
  relation/Ranks.v proves `wf_iff_wellfounded` for rank functions into
  `ord@{Set}`, constructively. Worlds, (wf-new), `wf_join_iff` and `ent_sound`
  are open, see the report at the top.
  Rocq, stage 3 of the third run of 2026-11-21: landed with plain `new`
  (4066cf1 to d61152d). Ranked worlds, (wf-new), `wf_join_iff`, growing
  worlds in O-New, the soup and the criterion, no premise on the world in
  adequacy. See the report at the top.
- **Algorithmic typing (author, 2026-11-21).** A bidirectional system, sound
  and complete for the declarative one, decidable when the constraint theory
  is. Type annotations are allowed where needed, for functions and the like.
  Equivalence of context-free session types is a postulated oracle, decided by
  Almeida et al. 2020, and its cost does not matter. The decidable fragment has
  no schematic constraints, so C is finite and (wf-new) is a cycle check. A plan
  starts now (algorithmic-plan.md). The full draft waits until the declarative
  system is final.
- **Decisions on the algorithmic plan (author, 2026-11-21).**
  - E-Box. `sinsts` gains `Forall sscoped ss` and `typed_sinst` is proved
    (plan 6.1). Fixed now in the Rocq run.
  - Opened points are named by an erased `unpack x as ῑ` (plan 6.2).
  - Existential types are well formed, `l ≼ ap(T)` under C (plan 6.3). Rocq
    after layers. Rocq, third run: `ex_wf`, a premise of E-Pack (c7a7e60).
    `typed_sinst` (plan 6.1) is still open.
  - The decidable fragment admits facts schematic in one offset k, with
    entailment by one-counter reachability (plan 6.4). GrowRing stays outside.
  - Plain `new` stays. Where its position is not fixed by the expected type,
    a type annotation names it, `(new : (S@x·κ) ⊗ …)` for a field or a fresh
    point for a root. No `new_κ` surface syntax (author, replacing plan 6.3).
  - Numbers inside payload types of session types are written in annotations,
    never unknowns of the solver, because the equivalence oracle only decides
    finished types (plan 6.6, explained to the author).
- **Open points of A3 (2026-11-21, awaiting decision).** check-layers-open.md.
  The restriction on plain `new` is real, O-New needs no change, P-Connect asks
  `wf (W1|S ⊔ W2|S)`, the other cases change only through `ent_sound`, and
  ranks are `Ord@{Set}` below step indices `Ord@{s}` from one polymorphic tree.
- **E-Open asks conservativity (author, 2026-11-21).** check-flag-rejection.md.
  E-Open gains `cons W Γ m C`. Opening adds no fact between points of the old
  context. The running example becomes the flag variant whose arms read their
  binder, statically rejected by ordering, not linearity.
  Rocq, stage 4 of the run of 2026-11-21 (redesign-clean3): landed on the
  pre-layer worlds. E-Open, `op_step` and `d_open` ask `cons_open W Γ m C`
  (static/Contexts.v), the 15 example sites discharge it by `cons_law`
  (static/PointSubst.v), `opened_cons` and `inv_chan` are in
  static/Inversion.v, and examples/SemBranch.v proves `Tbad_not_cons`,
  `sbv_thread_E`, `sbv_deadlock_free` and `sbv_rejected` (no world and no
  bound type the variant). `sb_dead_arm_typed` is gone.

## Open

1. **Events folded into labels (N.2).** Three cases `solo i α`,
   `sync i j o σ`, `offer i σ`. Started on branch redesign-clean3 in the
   worktree .claude/worktrees/redesign-s4: N.1 (P-Term asks `tfree`,
   `prim` gone) is committed there (6986a1c), N.2 is uncommitted and
   built, without make test, make check or the map. The agent stopped when
   the session ended. Map: not yet. Rocq: finish N.2 on that branch.
   Status 2026-11-20: done in the Rocq (fc8a020, EvSolo, EvSync, EvOffer
   in lang/Process.v) and on the map (56e4eb4), merged into redesign.

2. **One plain `new`; position and facts live in the type.** Decided
   2026-11-19. The term is `new`, label `new c`, event `new_i c`. E-New
   types it at `∃^⊥ ῑ. C. ((S@π)^N ⊗ (S̄@π̄)^N)` with
   `(ῑ, π) ∈ {(ρ, ρ)} ∪ {(ε, x·κ)}` (a fresh root, or a field of a point
   of the context) and premise `strict(Γ ∪ C)`. C is any constraint in the
   existing constraint language (possibly infinite) over π, its shifts and
   fields, and context points. An interval per end is the special case
   `L⁺ ≺ π ≺ U⁺, L⁻ ≺ π̄ ≺ U⁻`. Finite intervals of held ends do not
   suffice: the client-server example needs `ι+k ≺ (κ+k)‾` for all k.
   Worlds become `W = (A, ≺_A)` with growth `W ⊕ C`; families L, laws Λ_ℓ,
   generated roots g_ℓ, `new_ℓ`, `new_κ o`, E-NewAt, O-NewAt, T-Act-NewAt,
   the labels LNew ℓ / LNewAt and P-Connect's disjoint-families premise go.
   O-New: `c fresh ⇒ ∀ a ∉ A_W ⇒ ∃ S π C. π ∈ {a} ∪ {x·κ} ∧
   strict(W ⊕ C) ∧ e' at_{W⊕C} Θ[c⁺ ↦ S@π, c⁻ ↦ S̄@π̄]`. The examples are
   translated one to one: new_ℓ becomes new with C = Λ_ℓ(ρ) stated on the
   new that needs it, new_κ o becomes new at x·κ. Map: done.
   Rocq: E, V, P and the soup become Kripke in W along creations (W grows
   along a run), world growth lemmas (strict and well-founded preserved by
   one strict growth), every theorem over the grown world.
   Risks to report back on, not to paper over:
   (a) O-New chooses C by an existential at each level. The lock-free
       argument needs ownership the same at every level, and the root is
       universal for that reason. C chosen per level may break it. Possible
       fix: the soup fixes the world of a run once, as it fixes ownership.
   (b) Each grown world is well-founded, but a run may grow the world
       forever (a loop that creates below the previous channel). Check that
       lock freedom only needs the world at each position, not the limit.
   (c) Two creations at one field x·κ share a point. Allowed (loose), the
       strictness check decides.
   Overnight stage 4, 2026-11-20: stopped at the feasibility check of (a),
   no Rocq change. Verdict on (a): the plan fails as stated. The soup
   fixes the state `a` once for every index (`lf_sem := ∃ N a, ∀ n, a ∈
   S^{N,W}_n⟦Σ ⊢ T⟧`, soup/Soup.v), and a run computes the next state by
   the index-free update `own_next` from the event alone. The event of a
   plain `new c` names neither the point π nor the constraint C. If O-New
   picks `∃ S π C` at each level, the state after the creation needs the
   point of the new ends in K to equal π_n for every n, and the world to
   grow by one C for every n. Nothing forces π_n and C_n to agree across
   levels. Downward closure of E does not rescue it, because the choices
   form an infinite set (every field κ, every constraint C), so no
   pigeonhole argument finds one choice valid at every level. Repairs to
   decide on: (i) a finite menu of (π, C) per creation, determined by Θ,
   with downward closure and pigeonhole giving one choice for all levels
   (the client-server constraint `ι+k ≺ (κ+k)‾` for all k must then be one
   entry of the menu); (ii) the soup carries its own world and points,
   and O-New in the lock-free relation is stated at the world and point
   the soup offers, quantified universally over the offers that keep the
   world strict, which turns the thread's choice into the environment's
   and loses the creations that need a particular C; (iii) per-level
   worlds and points in the soup, which breaks the rank argument, because
   the rank of a pending thread is the point of its end in K at that
   position and the criterion compares it across positions. Note on (b)
   from the same reading: lockfree/Criterion.v asks one well-founded order
   on ranks for the whole run, so with growing worlds the order would be
   the union of the worlds along the run, which a loop that creates below
   its previous channel makes non-well-founded although every single
   world is well founded. A criterion that compares ranks only within one
   position would be needed. (c) needs nothing beyond strictness.

3. **No GV constants in the Rocq; constants are values on the map.**
   `k_send`, `k_new`, `k_new_at` are unused. Rocq: delete them and the
   sentence about constants in the header of lang/Syntax.v. The map shows
   constants `k` as values with `k v` stepping by the head step of `k`.
   The Rocq keeps saturated `Op k e`, and the value `k` is `λx. k x`.
   The map shows a block "Types of constants" (typing section, DF form):
   send : T[x·i] ⊗ S₀@x ⊸^x S@x⁺ (conditions of E-Send), recv, close,
   select_i, branch at upper point x, link : S@x ⊗ S̄@x̄ ⊸ ∗,
   spawn : (∗ ⊸^u_l ∗) ⊸ ∗, force : □(∀ῑᾱ.C. ∗ ⊸^u U) ⊸^{u[x̄]} U[s̄][x̄]
   under Γ ⊢ C[x̄]. Rocq: prove each as a derived rule, λy. k y typed at
   that schema (dftyped, and the merged typing with the annotations of
   the rule of k), or report which schema needs changing.

4. **Lock freedom is not vacuous (low priority, queued 2026-11-19).**
   `lock_free p` quantifies over every maximal weakly fair run from p. Keep
   that universal (an existential would let a good scheduler hide a lock).
   Add a semantics lemma, independent of typing: every configuration has a
   maximal weakly fair run (round-robin over its finitely many threads;
   the constructive form needs a choice of step at each position). State
   the main result with it, e.g. `lf_soundness` also concludes
   `∃ r l. erase (r 0) = p ∧ maximal r l ∧ wfair r l`, or package both in
   the definition. Map: add the existence lemma to the theorems section
   once proven.
   Overnight stage 6, 2026-11-20: not done. A run is a function
   `nat → config`, so building one picks a step at every position. The
   semantics gives steps only as propositions (`istep`, with the received
   value, the fresh channel and the new thread number chosen inside), and
   a Prop existential does not yield a function without the axiom of
   dependent choice, which the rules forbid. The lemma needs a function
   that computes a step of a given thread when it has one: a redex finder
   for one thread, a partner search for synchronisations, fresh names,
   and a decision whether the thread is enabled, for the round robin.
   v2 has none of these, and I did not write them in this run.

5. **Padovani-style lock freedom as a corollary (low priority, queued
   2026-11-19).** From `lock_free p` and item 4: for every q reachable
   from p and every thread pending in q, some q' reachable from q has a
   step in which that thread takes part (Padovani 2014, Def. II.1, in our
   per-thread form). Map: one line in the theorems section once proven.
   Overnight stage 7, 2026-11-20: not reached. The corollary starts a
   maximal weakly fair run from the reachable q, which is entry 4.

6. **Decided 2026-11-19 (author): credits only where ends sit.**
   Today every slot of a type carries a credit: components of ⊗ and ⊕,
   the body of ∃, the argument and result of ⊸, the result of a box, the
   payload (b), and every Δ entry (static/Contexts.v: `ty` in
   types/Types.v; `TSess` itself has none). The aggregate cases of aging
   and capture (`age_prod`, `age_sum`, `age_ex`, `cap_prod`, `cap_sum`,
   `cap_ex`) push the outer credit into the parts (a + aᵢ) and reset it to
   0, so an outer credit on ⊗, ⊕, ∃ is only a shared offset. Only two kinds
   of position need a credit of their own: an end `S@x` (its counter) and a
   closure `T ⊸ U` (its captured ends are invisible in its type, Cap-Arr).
   Proposal: credits as part of exactly these two type formers,
   `(S@x)^a` and `(T ⊸ U)^a`; drop the credits of ⊗, ⊕, ∃, box results,
   arrow argument and result, and payloads (the payload's own leaves carry
   them, E-Send's floor becomes aging the payload by 1). Aging and capture
   then recurse structurally and the summing rules go. Open: whether any
   proof uses the outer offset to age an aggregate in one step
   (`age_credit` on an aggregate) in a way the leaf form cannot match, and
   whether subtyping of aggregates (Sub-Prod with a + aᵢ) loses anything.
   Map: Types section done (grammar `(S@x)^a`, `(T ⊸ U)^a`, no credits on
   ⊗ ⊕ ∃ box results or payloads; the map calls ϑ a "ticket need"). The
   typing, semantic-typing, fuel and theorem blocks still show the old
   credits and must follow the Rocq once this is implemented.
   Rocq status: the repair agent was stopped by the author on 2026-11-19
   during stage C. Branch redesign-clean3 (worktree redesign-s4) holds
   entry 3 done (5907cd0), a merge of redesign (f0b97af) and two WIP
   commits for this entry (2c2168a, b9d0c05) that do not build. Resume
   from b9d0c05: the credits section of the types was next.
   Done in the Rocq 2026-11-20 (61ad17b, overnight stage 1). Credits sit
   on `TSess S x a` and `TLolli … a` only, aging and capture recurse
   structurally, E-Send types its operand at `Tp ⊗ S₀@x^a`, asks
   `tage 1 Tp Tp'` and `tsub Tp' (payload_at m T x)`, and payloads carry
   no credit. No proof used the outer offset of an aggregate. Sub-Ex now
   compares the bodies by `tsub` instead of `teq`, so the lemma that V is
   monotone along subtyping is proved under every point instantiation
   (`Vrel_tsub_pinst`). The cost fundamental theorem, both fundamental
   theorems and every example build unchanged in shape. In the lock-free
   examples a box result is now the closure `(T ⊸ U)^∞`, and the credits
   of its argument sit on the ends of `T`.

7. **One rejected example per lock-freedom mechanism (2026-11-19).** The
   map's examples page shows four programs that step forever without a
   deadlock while a thread waits forever: postponement (rx-postpone, aging),
   endless delegation (rx-delegate, payload credit / one hop), link refresh
   (rx-relink, tickets), a growing waiting chain (rx-chain, well-founded
   world); τ-divergence is covered by the guard rejections. Rocq: for each,
   the process, a proof that it is not lock free, and a proof that it is
   not lock-free typable at any N (or that the named premise fails for
   every derivation); then fill the badges' Rocq names. rx-chain depends on
   entry 2's risk (b) once worlds grow. Map: done (badges say "to be
   mechanized").
   Overnight stage 5, 2026-11-20 (f756da5). Done: v2/examples/FlagPair.v.
   Two threads branch on one flag that a third party sends, the first on
   a at x and b at y, the second on ā and b̄. `fp_unrealizable` shows that
   no pair of worlds with a strict join has both threads in E for both
   flags. The first thread with inl asks x ≺ ȳ (`fp_gate`), the second
   with inr asks ȳ ≺ x, a cycle. One thread alone is not rejected, its
   arms ask x ≺ ȳ and y ≺ x̄. Closed under the global context.
   Stopped: the four programs of rejects.js. Each needs two proofs that
   v2 has no tools for. Not lock free needs an explicit infinite maximal
   weakly fair run with a thread pending at every position, and v2 builds
   no run, it only reasons about given ones (lockfree/Fair.v). Not typable
   needs inversion of `typed` through E-Sub, E-Open, E-Pack, E-Box and
   E-Force, and v2 has no inversion lemma for `typed`. The badges stay
   "to be mechanized".
   Next run, stage 4 (2026-11-21). Inversion lemmas done in
   v2/static/Inversion.v: `inv_close`, `inv_case`, `inv_letu`,
   `inv_letp`, `inv_pair`, `inv_let` (the derived E-Let), and
   `ptyped_one`, `ptyped_two` for P-Term and P-Connect over one thread
   on each side. E-Sub and E-Pack change only the type, so the lemmas
   forget it. E-Open changes the context, so each lemma states the
   premises of its rule in a context `opened` from the given one.
   Stopped: `sb_untypable`, the static half of FlagPair and the programs
   of rejects.js. The ordering argument does not go through. An arm of
   E-Case may open an existential entry of Δ, and its constraint may
   state any fact over outer points through its environment. Nothing
   asks that a value inhabits the type of a λ argument or of a dead arm,
   so no fact derived in an opened Γ transfers to W. Concretely,
   `sb_dead_arm_typed` (v2/examples/SemBranch.v) types the dead arm,
   with its binder read by let ∗ = w, in the world Wa that holds only
   x ≺ ȳ: the binder has the type ∃⁰. y ≺ x̄. ∗, and E-Open gives the arm
   y ≺ x̄. On paper this extends to the whole variant of the thread
   (sb_not at the argument type (∃⁰. y ≺ x̄. ∗) ⊕ ∗, partner in Wb), so
   the claim of semantic-example.md that the static system rejects the
   flag program fails for that variant. The program as written binds a
   unit it never reads, and a unit is linear, so it is rejected for that
   reason, which needs inversion through E-App and E-Abs as well. The
   programs of rejects.js need the cost and ticket judgments through
   boxes, more than an inversion. The map marks the static rejection of
   the flag program as doubtful.

8. **Readable typing notation (draft, under review).** Map: draft blocks at
   the end of the typing section (Draft notation, Draft E-App, E-Send,
   E-Abs): one linear context Δ for ends and variables, W and N implicit,
   held entries `∥ H` (future ∪ heads(H), and in LF the aging H − c), and
   one effect ε = (c, ϑ) with sequencing ε₁·ε₂ (defined iff tok). Pure
   notation over the current rules. If the author approves: convert every
   rule on the map. Rocq: optional definitions and unfolding lemmas.
   Approved by the author 2026-11-19: convert all rules after the repair
   run. Also replace heads(H) by a lighter notation (proposal: H̄, the
   points the partners of H wait at, with S@x ↦ x̄, closures and ∃ ↦ their
   lower point l, boxes ↦ ∅).
   Map done 2026-11-19: every typing rule uses the notation, one form per
   rule with the lock-free parts marked (no separate D- rules on the map),
   and the draft blocks are gone. Heads: no H̄, because an overline on a
   context already means the dual interface (P-Connect). Instead heads
   hide inside `∥ H`, and the two places that still need them lift the
   order to types and contexts, `x ≺ T` (E-Send) and `l ≼ Δ` (E-Abs,
   E-Pack). The typing rules also follow entry 6 (credits only on ends and
   closures, aging and capture structural, E-Send asks `T' − 1 ≤ T[x·i]`,
   no outer credits on results). Process rules and the semantic-typing and
   theorem sections still use the old judgment (entry 9).

   Overnight stage 8, 2026-11-20 (96d5f7e), the Rocq side of the map's
   notation. Done: `tfin ϑ` is ϑ(0) ∈ ℕ (types/Costs.v) and replaces
   `∃ tk, meets ϑ 0 tk` in p_term, fsem_of_cost, lf_p_term and
   lf_soundness_source. `cr_le Θ N` is cr(Θ) ≤ N (static/Contexts.v) in
   fsem_of_cost and thfuel_id. `meets ϑ r tk` carries the comment
   ϑ(r) ≤ tk. `soup_consistent` and `soup_gen_iff` (soup/State.v) read the
   soup as relation, fuel and consistency. Names and comments only, no
   Rocq notation, because a notation that starts with ϑ( or cr( clashes
   with application. Not done: one map Φ for Π and φ in FuelE and FV,
   with Φ↓ and spare Φ (FuelE and Vfuel occur in 20 files, and fuel/*.v
   and cost/*.v hold 302 lemmas that pass the two maps), and the step
   clause of Pbody over
   pstep (it changes the definition of P that stage 9 also changes, so
   it belongs to that work).
   Open question for the author, facts only. O-New picks the session
   type of a new channel by `∃ S` in relation/Relation.v (o_new) and F-New
   by its own `∃ S` in fuel/Fuel.v (f_new). The two obligations live in
   two step-indexed predicates that the soup combines only at the end,
   so a shared existential needs FuelE to take the relation's choice as
   a parameter, or one predicate for both. Then the soup could ask
   `Π = sty ∘ A` and drop Π. Nothing decided.

9. **Readable semantic typing (to design).** Same treatment as entry 8 for
   V, E, P, the obligations, readiness, fuel and the soup: show the relation
   at κ_DF in DF mode, the general κ form with the differences coloured in
   LF, and lighter notation where one idea is written out several times.
   Map only. Draft after entry 8 is converted.
   Map done 2026-11-19: a new marker `\dfo{…}` shows the deadlock-free
   reading of a part whose lock-free reading is an `\annot`, so DF shows
   `j < n`, level `n` for a send payload and `κ_DF(α)` where LF shows the
   general table. The general cost table is LF only, the DF table labels
   its last row as a message. The obligations write the head of the
   subject end once, `Θ(o) ≐ S@x` (Θ(o) = S₀@x with unfold S₀ = S). The
   semantic judgment takes the typing context, `Δ ⊨^F_W e : T`, with
   `|Δ|` its ends. Payloads lose `^b` and FV follows entry 6.

10. **Readability pass over every section (map only, after the repair
    run).** Syntax, semantics, types, typing, semantic typing, theorems,
    examples: lighter notation where one idea repeats, explanations and
    examples a newcomer can follow, every symbol defined and hoverable,
    hover texts proofread (also the DF texts the annotation filter cut).
    Entries 8 and 9 are part of it.
    Scope narrowed by the author 2026-11-19: theorems and examples only,
    the other sections are fine. Map done 2026-11-19: theorem statements
    use the new judgments (`∅ ; Δ ⊢^F_W t : T`, `T ! ε` for the annotated
    one, `Δ ⊨^F_W t : T`, erasure `Δ_df`), "merged judgment" became
    "annotated typing judgment", general-κ rows and `[κ]` show only in LF,
    and the captions state the DF result first. Examples use the source
    syntax of the syntax section (`let ∗ =`, `let ⟨a, b⟩ =`), the
    forwarder protocol reads `?((∗ ⊸ ∗)^2).Close`, and the controller
    states idle aging in the entry-6 form.

11. **Faithfulness audit of the map against the Rocq (after the repair
    run is merged).** Check every block, rule, signature and theorem on the
    map against the definitions in v2/, list every difference that is not a
    queued entry, and fix the map or queue the Rocq change.
    Overnight stage 10, 2026-11-20, against redesign-clean3 after stages
    1, 2, 5 and 8. Scope: every Rocq name the map cites (601 references in
    data.js, checked by a script against the definitions in v2/) and the
    statements of the theorems section. The formulas of the other blocks
    were not compared symbol by symbol. No map edit, none of the
    differences is a statement the Rocq proves false. Differences that no
    entry queues:
    (1) Names that no longer exist. ty-ann cites `cr_df` (gone with entry
    6). age.credit cites `age_credit` (now `age_sess` and `age_arr`).
    P-Connect.strict cites `p_join_iff_connect` (gone with entry 13, the
    rule now rests on `strict_join_iff` and `ptyped_strict`).
    th.live-fundamental and th.live-fundamental-typed cite
    static/LiveFundamental.v, which does not exist (both theorems are in
    static/Fundamental.v). ctx.only cites `tenv_only` (the Rocq name is
    `lenv_only`). syn.let cites `t_act_let` (the steps are
    `t_act_let_unit` and `t_act_let_pair`).
    (2) Names in the wrong file. The blocks r-base, r-fun, r-data,
    r-boxes, r-ex, r-act, r-threads, r-new and t-subs cite the rules
    `d_*` and `d_conv` in static/Typing.v, they are in
    static/Conservativity.v. V-Arrow.lb cites `lb_le` in
    relation/Relation.v, it is in relation/Readiness.v. fu.idle and
    sty.skip cite `idle` in fuel/Fuel.v, it is in types/Types.v.
    (3) Premises the Rocq dropped. th.fundamental-proc, th.lf-fundamental,
    th.soundness and th.lf-soundness, with their notes and signatures,
    ask `strict W`. Since stage 2 the Rocq theorems ask none
    (`ptyped_strict`), so the map states a weaker theorem. Entry 13 names
    the Rocq change and marks its map side done, but the theorems section
    still shows the premise.
    (4) Rocq results without a map entry: `fp_unrealizable`
    (examples/FlagPair.v), `soup_gen_iff` (the soup as relation, fuel and
    consistency, soup/State.v), `strict_bare` (types/Worlds.v),
    `p_connect_join` (static/Typing.v).

12. **Generalized arrows, E-SpawnLam derived (decided 2026-11-19 by the
    author, design to confirm).** Today E-SpawnLam exists beside E-Spawn
    because E-Abs asks a common lower point `l ≼ Δ` and types the body
    under a fresh future above `u`, and a λ spawned in place needs neither.
    Generalize the two points of an arrow instead.
    (a) Lower point `l = ⊥` allowed (`lbound` already has `LBot`, used by
    `∃^⊥`). E-Abs drops `l ≼ Δ` when `l = ⊥`, `hbot` reports such arrows,
    and holding the closure puts `⊥` into the future, which forbids
    blocking while it is held, as for `∃^⊥`.
    (b) Upper point `u = ⊤`. E-Abs types the body under the empty future
    `(∅, ·)`, and E-App needs `⊤ ≺ F`, which holds only for the empty
    future, so such a closure is applied only in tail position of a thread.
    E-Spawn asks nothing of `u`.
    Then `spawn (λe)` types by E-Abs at `l = ⊥, u = ⊤` plus E-Spawn, and
    E-SpawnLam goes. The value clause at `u = ⊤` is exactly `Vthunk` (body
    at the empty future), so V-Arrow absorbs V-Thunk and one value clause
    goes too. Check: E-SpawnLam ages the handed context by one hop while
    E-Spawn asks closure credit `a ≥ 1`, so capture at `h, a = 1` must give
    the same credits as `Δ − 1`, and the ticket need of E-SpawnLam
    (`tspawn` of the body at reserve 0) must match E-Spawn on the arrow.
    Tickets match (both write tspawn(ϑ'(0))). Credits do not: capture
    restates every captured end at one floor h, with h + a ≤ a₀, while
    E-SpawnLam keeps each end at its own credit minus one. Lost example:
    A at N and B at 1 handed to a child that acts on B while holding A.
    E-SpawnLam gives A at N − 1, capture at a = 1 forces h = 0 and A at 0.
    Proposed fix, to check first: per-end capture, the body sees Δ − a
    instead of the floor h, and FV-Arrow asks counters at call time to be
    at least the counters at creation minus a (FV knows the creation
    counters). Then the derivation loses nothing, ordinary closures get
    more precise, and the floor h (and Cap-Arr's h − h₀) may go. Touches
    FV-Arrow, capture, Sub-Arr. Fallback if it fails: generalized arrows
    with the loss, after checking every lock-free example still types.
    Order: check per-end capture, then generalize arrows. Author
    (2026-11-19): per-end capture is important.
    Rocq: after the repair run (entry 6) is merged. Map: after the design
    is confirmed.
    Design check 2026-11-20 (docs/redesign/check-per-end-capture.md, on
    paper). Per-end capture holds and removes the floor h. Capture becomes
    aging by a, FV-Arrow asks `φ′ ≥ φ − a`, Sub-Arr asks `a' ≤ a`. E-SpawnLam
    then differs from E-Abs plus E-Spawn only in the arrow points.
    Done in the Rocq 2026-11-21 (next run, stage 1). `TLolli` lost the
    floor h, and `tcap`, `lcap`, `thcap` with their lemmas are gone. E-Abs
    asks `thage a Θ Θh` and `lage a Δ Δh`. FV-Arrow (fuel/Fuel.v, `Vty`)
    asks the captured counters of the ends that are not idle at least a,
    and at a call accepts any counters `f′ ≥ f − a`. Sub-Arr asks
    `fle a' a`. `Vty_age` carries the call bound through aging by
    `fsub_age` (types/Costs.v), and `cost_e_abs` builds the body
    environment from `envf_age` and `envf_mono` over `cle_fminus`. The
    capture of a closure inside a closure is aging the inner closure, so
    Cap-Arr went with the rest. Plausibility. Every lock-free and
    deadlock-free example builds unchanged in shape, the box results of
    the lock-free examples are closures at credit ∞, which ages a box by
    `age_free` as before. The forwarder thunk `T_thk` at credit 2 still
    types. The four programs of rejects.js stay excluded, because
    `lf_soundness` still builds with no new axiom and these programs are
    not lock free. The S4.18 counterexample concerns the clause (fuse) of
    P, which this stage leaves alone, and `fuse_ok` still forbids new
    pairs of partners outside D. SemBranch, TreeTopo and FlagPair read
    no arrow credit and build unchanged. The loss
    example of this entry (A at N and B at 1 captured at a = 1) now keeps
    A at N − 1, which is `lage 1` on the two entries.
    Generalized arrows done in the Rocq 2026-11-21 (next run, stage 2).
    `TLolli` carries an upper point `ubound` (none, a point, or ⊤,
    types/Points.v) and a lower point `lbound` (none, a point, or ⊥).
    E-App asks `ub_below_u`, which at ⊤ is the empty future, and holds
    the closure under `lb_heads lb` with the ⊥ flag `lb_bot lb`. E-Abs
    asks `lbx_below_h` of the lower point, which asks nothing at ⊥, and
    types the body under `abs_hc φ ub Γ` and `abs_fut φ ub`, the empty
    future at ⊤. `hbot` reports an arrow at ⊥. The rule E-SpawnLam is
    gone, and `e_spawn_lam` (static/Weakening.v) and `d_spawn_lam`
    (static/Conservativity.v) are lemmas, E-Abs at (⊤, ⊥) and credit 1
    followed by E-Spawn. `Vthunk` is gone. O-Spawn reads `Varr` at
    `∗ ⊸^⊤_⊥ ∗` (relation/Relation.v), and `Varr_top` turns any arrow
    value at `∗ ⊸ ∗` into one. The semantic side reads ⊤ by `ub_ltu`
    (relation/Readiness.v), and the fundamental theorem builds the body
    hypotheses by `hsat_abs`. `lb_le`, `lbound_of`, `lb_sem`,
    `later_spawn_lam` and `cost_e_spawn_lam` went with the rule.
    Plausibility. Every deadlock-free and lock-free example builds, the
    spawned abstractions through the derived lemmas with unchanged
    calls. A closure at ⊥ cannot be sent, because E-Send asks
    `hbot T = false` of the payload. A closure at ⊤ is applied only under
    the empty future, so it runs as the last code of its thread. The
    programs of rejects.js stay excluded by `lf_soundness`, and the
    S4.18 counterexample concerns (fuse), which this stage leaves alone.
    SemBranch, TreeTopo and FlagPair build unchanged.

13. **P-Connect compares only the shared roots (2026-11-19, author).**
    Today p_connect asks world_wf W1, world_wf W2, disjoint families and
    strict (W1 ⊔ W2), and the lemma p_join states the overlap form, strict
    W1, strict W2, strict (W1|_S ⊔ W2|_S) for the shared constants S,
    equivalent by p_join_iff_connect (strict_join_iff). world_wf is not
    trivially true, because p_term asks nothing of its world. New form:
    p_term asks strict W, and p_connect asks disjoint families and only
    strict (W1|_S ⊔ W2|_S). By induction every process derivation sits over
    a strict world (strict_join_iff for the connect case), so the old rule
    is derivable, p_join disappears, and the `strict W` premise of the
    process soundness theorems follows from the derivation. The map writes
    S = A_{W1} ∩ A_{W2} and no families premise, because entry 2 removes
    families. Map done. Rocq: after the repair run is merged.
    Done in the Rocq 2026-11-20 (overnight stage 2, 69526fa). p_term
    asks `strict W`, p_connect asks disjoint families and
    `strict (W1|_S ⊔ W2|_S)` with `S = wshared W1 W2`, and
    `ptyped_strict` shows every derivation sits over a strict world. The
    earlier rule is the lemma `p_connect_join`, and p_join and
    p_join_iff_connect are gone. fundamental_proc,
    live_fundamental_proc, soundness, live_soundness, lf_fundamental and
    lf_soundness lost their `strict W` premise. The source theorems keep
    it, because P-Term asks it. A world without facts and families is
    strict (`strict_bare`), which the forwarder uses.

14. **Typing QA against static/Typing.v (2026-11-19).** Beyond entries 2,
    6, 8, 12, 13 the map differed in three places, all fixed on the map:
    `¬hbot T` at E-Send is gone: the map lets heads return ⊥ for hidden
    ends (heads(∃^⊥) = {⊥}, no fact relates ⊥ to a point), so `x ≺ T`,
    `l ≼ Δ` and held futures need no separate hbot or ⊥_Δ (Rocq: heads
    with ∅ plus the flag hbot, sf_unionb, lbx_below_h; optional Rocq
    cleanup, heads into Point ∪ {⊥}); the arrow lower bound "absent"
    (`LNone`, no end) is written `·`, not `⊥`, which is the hidden bound
    `LBot` of `∃^⊥`; held futures add the flag ⊥ when H holds an `∃^⊥`
    (`sf_unionb … (lenv_bot Δ2)`). Entry 12 must keep the two apart: the
    new arrow bound there is `LBot`, and hbot must report such arrows, so
    a spawn-only closure cannot be sent (no loss, it cannot exist today).
    Overnight stage 3, 2026-11-20: not done, by the rule "only if it
    shortens proofs". The flag is threaded beside the head sets through
    hbot (41 uses in 20 files), lenv_bot (56 in 17), sf_unionb (47 in 18)
    and fs_bot (12 in 10), and the semantic reading `sf_den` interprets it
    by the arbitrary set B. Folding ⊥ into the sets replaces each case
    split on the flag by a membership test of ⊥ and changes every one of
    these sites, with no proof that gets shorter in sight. `LNone` and
    `LBot` stay apart as they are.
    Open questions from the author, to discuss:
    (a) Named variables on the map instead of de Bruijn indices in Δ, as
        for points (the Rocq keeps indices). Author: cosmetic, map only,
        low priority.
    (b) Future variables: Γ holds φ ↦ u (the fact u ≺ φ) and F names φ as
        the unknown rest. Each φ has exactly one fact, so Γ ⊢ x ≺ φ iff
        Γ ⊢ x ≼ u. Candidate: F = (X, above u) and no future variables in
        Γ. To check against fl and the semantic den_{ρ,B}. Author
        (2026-11-19): wanted if it holds.
        Checked 2026-11-20 (docs/redesign/check-future-variables.md). It
        holds, `fl_to_var` and `fl_from_var` compiled in a scratch file.
        The relation's future needs the rest "above u" beside its points.
        Done in the Rocq 2026-11-21 (next run, stage 3). Γ holds only the
        constraint instances (`hctx` lost `hc_fv`), `fl` relates points
        only, and `node`, `fl_v`, `hc_fvar` and `fhyps` are gone. The rest
        of a static future is `RAbove u` (everything above u) or `RAll`
        (everything), with the ⊥ flag beside it (static/Contexts.v,
        `frest`, `futrest`). `ub_below_s` asks `sle W Γ x u` against the
        rest `RAbove u` (`rest_below`), and nothing against `RAll`.
        E-Abs types the body under `abs_fut ub` and E-Box under
        `rest_of ub`, both with Γ unchanged, and neither rule picks a
        fresh variable. `sf_pinst` instantiates the point of the rest.
        The relation keeps its futures as finite sets. Instead the
        semantic reading quantifies over one set R for the rest with
        `rest_ok` (R above u, compat/SemTyped.v), and the fundamental
        theorem carries `rest_ok` beside `hsat`. This is shorter than a
        predicate future in the relation, which the check note proposed,
        and reads the same, because a singleton above u already forces
        `x ≺ y` for every y above u. Plausibility. Every example builds.
        The body futures of the example boxes changed from a variable φ
        with `u ≺ φ` to the rest above u, and each `φ_hyp` lemma went.
        The rejected programs of rejects.js stay excluded by
        `lf_soundness`. The S4.18 counterexample concerns (fuse), which
        this stage leaves alone. SemBranch, TreeTopo and FlagPair build
        unchanged.

15. **Remove the clause (fuse) of P (author 2026-11-19, overnight stage
    9).** Not done in the overnight run of 2026-11-20, no Rocq change.
    A probe dropped the clause from `Pbody` (relation/Relation.v:505) and
    built. The first failure is inside Relation.v (`Pbody_mapX`, which
    maps the clauses under the fusion), and everything that reads P
    waits behind it. The clause is used in 14 files (counts of
    `fuse_ok` or `pfuse`): compat/ConnectLink.v 27, ConnectCtx.v 22,
    Rename.v 17, ConnectP.v 17, Relation.v 14, ConnectSteps.v,
    ConnectFuse.v, ConnectExt.v, ConnectExtMsg.v 7 each, Connect.v 6,
    PTerm.v 4, Conv.v 4, ConnectRen.v 2, LiveDF.v 1. `Prel_rename`
    (compat/Rename.v:915) is the projection `Prel_fuse` at D = ∅ and
    becomes an induction on the level, as `Erel_rename` is. The link case
    of P-Connect (compat/ConnectLink.v, 585 lines) reaches the fusion
    when `csub o1 o2` gives the other component a dual pair, so it needs
    a second theorem beside renaming, that P at Σ ∪ {c⁺, c⁻} with the two
    ends dual at dual points gives P at Σ with c restricted. That theorem
    changes the readiness of the interface (two interface ends become
    internal, so `above_offered` stops reading them) and turns interface
    actions on c into internal synchronizations, so its proof has the
    shape of P-Connect itself. compat/ConnectFuse.v (396 lines), which
    shows the composite closed under fusions, would go. The question of
    bound restricted channels (quotient or binder) was not reached. The
    first test, the counterexample of S4.18, was not run.

## Done in the Rocq

(entries move here once the repair agent has implemented and merged them)

## Open discussion (not scheduled)

- **P-Connect's overlap is the shared constants, not the interface (2026-11-21,
  from the Curry-Howard session).** P-Connect asks `swf (W1|S ⊔ W2|S)` with
  `S = swshared W1 W2 = sw_consts W1 ∩ sw_consts W2` (static/Typing.v,
  types/Worlds.v). S is the set of constants both worlds know, not the roots
  of the cut interface Σ_C. The rule composes by the interface only if the
  two coincide. Two repairs. (a) A lemma that in every derivation S ⊆ the
  roots of the points of Σ_C. Private constants are fresh and families are
  gone, so it may hold already, but nothing states it. (b) A hiding step, so a
  judgment's world lives on its interface only, W restricted to the roots of
  Σ, sound by transitivity as amalgamation is. With either, the type of a
  component reads (Σ, W|roots Σ), and P-Connect checks duality and
  well-foundedness of the two interface orders. Needs the author's go.
  Update 2026-11-22. Repair (a) is false (examples/SharedRoots.v on
  redesign-comp, `shared_not_cut`). The author chose repair (b), hiding.
  P-Connect compares the two interface orders, including roots the two outer
  interfaces share.
- **The n-ary connect (2026-11-21, from the Curry-Howard session).** (1) On
  main, `Prel_connect_n` (theories/composition/PConnectN.v:378) asks
  strictness of the full amalgam W1 ⊔ … ⊔ Wn, and v2 has no n-ary connect.
  Amalgamation extends to n components. With S_i the roots W_i shares with
  any other world, wf (⊔ W_i) holds iff wf (⊔ W_i|S_i). A cycle in the union
  passes through private stretches of single worlds, and transitivity of W_i
  collapses each stretch into a fact of W_i|S_i. Not proved in Rocq. With it
  the n-ary premise is an interface check, as the binary one is. (2) The
  n-ary condition is no conjunction of pairwise conditions. Milner's ring is
  pairwise consistent and cyclic as a whole. Every system that admits cycles
  has this, and priority systems only look pairwise because integer
  priorities fix one global order in advance. The map should say this in one
  sentence where it explains why P-Connect checks the overlap.
  Update 2026-11-22. Ported as an admissible rule over hiding
  (static/ConnectN.v, `p_connect_n`) with examples/Ring.v. The fold needs
  no amalgamation, which stays unproved. See the report at the top.
- **Tickets as a bounce bound (2026-11-22, from the Curry-Howard session,
  an analogy).** Read as infinitary proof theory, counters are the progress
  condition on infinite branches and links are bounces through axioms
  (baelde2022bouncing, where a bound k on bounce height gives a decidable
  hierarchy). The note warns against merging the bounce bound into the
  action counters, which is what the failed A1 candidate did. The decided
  tickets do not merge them. A ticket bounds a counter from above, and
  E-Link asks `a1 + m2 > N`, so each bounce strictly lowers the tickets of
  the partner a wait moves to, and a chain of bounces along one wait has at
  most N links. The three devices are order (rank), counters (credit, fuel)
  and tickets (bounce bound). The map can say this where it explains links.
- **Link as a primitive, identity expansion (2026-11-22, from the Curry-Howard
  session, parked by the author for later).** Link fuses at dual points x and
  x̄. With synchronous semantics and one point per end, the two forwarded ends
  then act at the same instant, which no single thread does. Every sequential
  copycat fails readiness whichever end it acts on first, because it would
  need x ≺ x or x̄ ≺ x̄ (SHARP-EDGES entry 37). Consequences. (1) Link is a
  primitive no program implements, like the axiom at atomic types in CP.
  (2) Identity expansion fails, which matters for a logic and not for the
  relation. (3) Tickets are the price of fusion, because fusion moves a wait
  without an action. Hand-written forwarders at link's type stay untyped.
  Three designs.
  - A. Keep fusion. No Rocq cost, no identity expansion.
  - B. Keep fusion and add a derived forwarder `fwd` at independent points x
    and y, with facts generated by the session type and no new rule. The
    copycat alternates. Where it receives on the first end and sends on the
    second, x_k ≺ ȳ_k and then y_k ≺ x̄_{k+1}, symmetric for the other
    polarity, and payload ends pass on with facts at their fields. Identity
    expansion holds for `fwd`, tickets stay for link, and the forwarder ring
    fwd(a1,b1) ∥ fwd(b2,a2) cut on {a,b} gives the cycle x ≺ ȳ ≺ x, which the
    well-foundedness check rejects.
  - C. Replace fusion by forwarders. Identity expansion holds and tickets
    likely go, because bounces become actions and growing forwarder chains go
    to rank. PGV subsumption of link breaks, because PGV gives both link ends
    the same priorities and a copycat needs strict alternation. It reverses
    the decision of 2026-10-29 and touches every link lemma.
  The session recommends B. All on paper, nothing in Rocq, higher-order
  payloads untested. No change without the author's go.
  Update 2026-11-22 (author). Try B, never C. An agent derives `fwd` with the
  existing rules on branch redesign-fwd. The n-ary connect is to be ported
  once hiding lands.
- **Cross-references everywhere on the map (author 2026-11-19, another
  day).** Every symbol in every formula should be hoverable and lead to
  its definition, which needs a restructure of the generator (one
  definition site per symbol, references by key). Today only the parts
  wrapped by hand or by the automatic word list are hoverable.

- **Link budgets per end.** Per-thread link tickets reject a box that links
  once per round forever (e.g. a server linking each new client to a
  worker) and received closures that link. A budget per end in the session
  type, like payload credits for hops, might accept the server. The plan
  (docs/extensions/lock-freedom-plan.md §18) rules out per-end tickets only
  together with replacement. The author judged it not the cleanest move for
  now (2026-11-19). No Rocq work.
- **Points on actions instead of one point per end.** Kobayashi and
  Padovani annotate every action with its priority. We keep one point per
  end, S@x, and compute later points (x⁺, fields x·κ). Equal
  expressiveness for finite protocols, finite types for recursive ones,
  point-free session types. Written points would only read better. Author
  (2026-11-19): queue it as a discussion item. No Rocq work. Author later
  the same day: not wanted for now, also not as a display on the map.
- **Type-directed ticket split at spawn.** Today a spawn halves the
  tickets (child ⌈tk/2⌉, parent ⌊tk/2⌋), which forces the doubling form
  ϑ(r) = 2^s r + b and the side condition tok. If the child got exactly
  its need b_c, needs would just add up. That needs the split to be fixed
  outside the step index without the relation reading types. Discuss
  together with per-end link budgets. No Rocq work. Author (2026-11-19):
  probably good, worth designing.
  Design check 2026-11-20 (docs/redesign/check-ticket-split.md). Not as
  stated. The soup needs the split fixed for every index, and a split by
  the child's need either reads its type or needs a classical pigeonhole
  over the finitely many splits. With exact splits needs become offsets
  `r + b` and `tok` goes.
- **Programs the topological relation accepts and ours rejects.** The
  earlier relation (D'Osualdo, van den Heuvel, Thiemann, Weidner) needs no
  order, only a per-extruded-channel split at the interface. Candidate:
  thread A sends a flag to thread B, then both close a and b in the order
  the flag picks. Deadlock free. Ours rejects it: A needs x_a ≺ x̄_b and
  x_b ≺ x̄_a, B needs x̄_a ≺ x_b and x̄_b ≺ x_a, a cycle, and the points
  are fixed before the flag exists. Check the earlier relation accepts it
  (internal channels only, so the interface split is not involved).
  Later: a hybrid that cuts along one channel without order facts
  (Wadler-style) and uses points only for cycles.
  **Important, to discuss (author 2026-11-19).** The author wants the
  relation to admit, inside a component, whatever can be proved by hand.
  Correction of an earlier claim: it already does at the process level.
  ready_p (relation/Readiness.v) reads points only of interface ends, and
  internal channels carry none, so P⟦∅ ⊢ T⟧ asks exactly deadlock
  freedom of every reachable stuck state, and the flag program is in it by
  a direct proof. What rejects it is the route through typing: P-Term asks
  each thread to be in E, and E orders every end the thread holds.
  sem_p_connect composes any two members of P, so a hand-proved component
  composes with typed ones, provided it is ready at its interface (offered
  ends below the partner points of the ends it does not offer). Both
  points are obvious, no mechanization wanted. Options discussed:
  (a) one-end lemma: a process with one free end, in either relation,
      offers that end when stuck; this would allow a mixed P-Connect along
      a single channel (cut of one channel, payload condition as in
      docs/extensions/regions.md §3, cut points stay on our side); needs
      their definitions (dosualdo2026logical is metadata only in the
      store, read and record facts first);
  (b) a single-channel cut rule in our own relation that needs no world
      agreement, orders only inside cycles (the hybrid);
  (c) world growth at a decision with an owner token (data-dependent
      constraints, regions.md §1 pending choices, BranchWorlds.v), and
      facts guarded by shared values (regions.md §6);
  (d) state and check that we subsume their static system, which types
      trees (one point per end may already suffice). Semantic inclusion of
      their relation in ours is false in general.
  (e) Author: embed the topological relation in ours by one generic proof.
      Inside a component nothing is to show, internal channels carry no
      points. At the external channels replay the topological argument
      once, generically: their tree-shaped interface should let us choose
      points for the interface ends so that ready_p holds. Then every
      process in their relation is in our P, and composes with typed code
      by sem_p_connect. Open: which points the tree induces, and whether
      their interface readiness implies above_offered.
