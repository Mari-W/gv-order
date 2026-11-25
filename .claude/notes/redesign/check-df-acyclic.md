# Design check, deadlock freedom over acyclic worlds

2026-11-22, branch redesign-fj. Write-up only, no change to v2/. Every
argument is on paper. I read the Rocq on redesign at a5e99e2, namely
types/Worlds.v, relation/Ranks.v, relation/Readiness.v, relation/Relation.v,
relation/Adequacy.v, relation/ExProp.v, static/Contexts.v (`gen_new`),
static/Typing.v (`e_new`, `fp_term`, `fp_connect`, `p_term`, `p_connect`),
static/Conservativity.v, static/Fundamental.v, static/FundamentalProc.v,
compat/Redex.v (`Erel_new`), compat/LiveDF.v, compat/Connect.v
(`finite_lt_acc`), soup/LFTyped.v, soup/LFAdequacy.v and the examples
ForkJoin, Ring, Copycat, SharedRoots, SemBranch and Cycle. The notation is
that of check-general-new.md. tree(ρ) is the tree of the new root, a context
point is a point outside tree(ρ), an entry is a fact `z ≺ v` of C with z a
context point and v in tree(ρ), and an exit is a fact `u ≺ y` of C with u in
tree(ρ) and y a context point. Padovani's programs are quoted from the facts
of `padovani2014deadlock` in the papers store (p2, p8, p10). I read no page
of the paper in this run and recorded no new fact.

## Verdicts

1. The design works. The deadlock-free relation reads worlds whose order is
   an arbitrary strict partial order on points, with no ranks. I recommend
   strict relational worlds over integer ranks, because integer and rational
   ranks are not exact for the new E-New premise (section 2.3). On the DF
   side E-New asks (acyc-new) of section 2.2, P-Term and P-Connect ask
   acyclicity in place of `swf`, readiness is unchanged, O-New is unchanged,
   and adequacy keeps its proof, which uses only irreflexivity and
   transitivity (`finite_lt_acc`). DF soundness no longer needs excluded
   middle. The only use of EM on the DF path is `list_max_rank` inside
   `Erel_new`, and the new creation lemma builds the extended world as a
   transitive closure, constructively.
2. One static judgment with a mode switch on N. At N = ∞ (`None`, the DF and
   live judgment) E-New asks (acyc-new) and the process rules ask
   acyclicity. At a finite N (the lock-free judgment) they keep (gen-new)
   and `swf`. (gen-new) implies (acyc-new) statically and constructively
   (section 3.1), and `swf` implies acyclicity, so the erasure
   `typed_dftyped` keeps working and every LF-typed term stays DF-typed.
   The relation becomes parametric in the kind of world. κ_DF and the live
   relation for `live_soundness` sit over strict worlds, the lock-free
   development keeps ranked worlds for its threads. `live_sub_df` keeps its
   statement, because both of its sides sit over strict worlds.
3. Recursive fork-join with replies, Padovani's `fact` and `fibo` type as
   deadlock free under the new design (section 4). Each needs a box
   hypothesis H with infinitely many facts, closed under the descent to a
   child, and laws of the root of the first channel that hold an infinite
   descending chain in tree(ρ). (acyc-new) accepts them, (gen-new) rejects
   them. Proposition 7 of check-general-new.md does not apply, because it
   takes a model with the least rank, and strict worlds have none. All
   three stay rejected by the LF judgment, as Padovani's stay outside his
   lock-free system.
4. Nothing deadlocking becomes typable (section 5). Milner's ring, the
   forwarder ring, SharedRoots' `opposite_clash`, the two-channel cycle and
   `sbv_rejected` are rejected by a cycle in the joined world or in the laws
   of one creation. Every one of these proofs uses irreflexivity
   (`swf_irrefl`) or soundness, never well-foundedness. Acyclicity rejects
   each of them.
5. Rocq cost (section 6). The proofs of the relation, the compatibility
   lemmas and the fundamental theorem read worlds only through 15 lemmas of
   types/Worlds.v. The internals of a ranked world appear in 3 files,
   types/Worlds.v, compat/Redex.v (`Erel_new`) and soup/LFAdequacy.v
   (`w_lt_wf`, `wchain_lt_wf`). The work is one interface for worlds with
   two instances, one new creation lemma, a mode switch in 3 typing rules,
   an acyclic join lemma, and a mechanical parametrization of the 46 files
   outside examples/ that mention `world`. The DF and LF developments share
   every proof but the creation lemma and LF adequacy.

## 1. Where well-foundedness is used today

`grep` over v2/ for every lemma that reads well-foundedness of a world
(`w_lt_wf`, `wchain_lt_wf`, `oind` on ranks, `wf_join_iff`, `swf_irrefl`,
`list_max_rank`) gives this picture.

- DF adequacy (relation/Adequacy.v, compat/Connect.v) uses
  `w_lt_irrefl` and `w_lt_trans` only. `finite_lt_acc` shows that ≺
  restricted to a finite list of points is well-founded because the world
  is irreflexive, and that is the argument that a stable state with pending
  actions has an offered end. Its comment says so ("No decision of ≺ is
  needed").
- `live_adequacy` adds `Prel_acc_live`, an induction on the least fixpoint
  of administrative steps. It reads no world order.
- Lock-free adequacy (soup/LFAdequacy.v) uses `w_lt_wf (wk k)` for local
  progress and `wchain_lt_wf` for the run. The second is the place where
  lock freedom needs ranks. The point a thread waits on may not descend
  forever along the run, and the ranks of a chain of ranked worlds are
  fixed once chosen.
- The static side asks `swf` at P-Term, at both forms of P-Connect, in the
  hidden semantic judgment `sem_ptyped_h`, in `soundness_source` and in the
  n-ary rule (static/ConnectN.v). It asks `well_founded (new_step C)` in
  (gen-new). The world built at a creation needs ranks, which is why
  (gen-new) asks C ∪ po well-founded and why `Erel_new` needs the largest
  rank of a partner set.

So deadlock freedom asks well-foundedness only because the relation's
worlds are ranked. The ranks enter through `wmodels_exists` and
`Erel_new`, and both can be replaced by transitive closures.

## 2. The design

### 2.1 Strict worlds

A strict world is a set of roots and an order on points.

    D = (roots(D), ≺_D)
      ≺_D transitive and irreflexive
      po ⊆ ≺_D
      x ≺_D y ⇒ po x y ∨ (rin D x ∧ rin D y)
    D ⊑ D'  ⇔  roots(D) ⊆ roots(D') ∧ ≺_D ⊆ ≺_D'

The last clause of the first block mirrors `w_lt` of ranked worlds, where a
fact between unranked points is program order. Extension asks inclusion
only. The creation of section 2.4 never adds a fact between two existing
points (it is conservative), so a stricter ⊑ that also reflects the old
order is available if some proof needs it. No proof I read does. Readiness,
`wholds`, `ub_lt`, `lbx_le` and `wmodels` read the world through `W ⊢ x ≺ y`
and keep their definitions. `w_lt_trans`, `w_lt_irrefl`, `po_lt`,
`w_lt_mono`, `w_le_mono`, `wext_refl`, `wext_trans`, `rin_mono`, `rin_po`,
`wmodels_lt`, `wmodels_mono` and `wmodels_ext` hold by definition.

A static world W with `sacyc W := ∀ x, ¬ W ⊢ₛ x ≺ x` is modelled by the
strict world (consts W, ⊢ₛ) itself. `lt_zone` gives the root clause. This
replaces `wmodels_exists` and needs no rank function, so `rank_of` and the
Brouwer trees leave the DF path.

### 2.2 E-New on the DF side, (acyc-new)

A bridge of C from z to y is a fact `z ≺ y` of C between context points,
or an entry `z ≺ v`, a path of C ∪ po inside tree(ρ) from v to u, and an
exit `u ≺ y`.

    π = ρ  ⇒  (i)  C ∪ po is acyclic on tree(ρ)
              (ii) Γ ⊢ z ≺ y for every bridge of C from z to y   (acyc-new)

In Rocq terms, (i) is `∀ x, in_tree0 x → ¬ tc (new_step C) x x`, and (ii)
reads `slt W Γ (ctx_pt C z) (ctx_pt C y)`. Like (gen-new), the premise reads
`slt`, the facts of C and program order. It names no rank and no world of
the relation, so it is a static premise. It has no partner relation and no
finite sets. For finite C, W and Γ it is decidable by reachability, a cycle
test on the finite graph of section 5 of check-general-new.md plus one `slt`
question per pair of context points joined through tree(ρ).

Proposition A, soundness. Let R be a strict world and σ an instance with
`wmodels R W` and `hsat R σ Γ`, and let (acyc-new) hold. Pick a fresh root π
outside roots(R) and outside the roots of the points of `bc_env C` under σ.
Let R′ have the roots of R, the root of π and the roots of the context
points of Cσ, and let ≺_R′ be the transitive closure of ≺_R, of Cσ at π and
of program order. Then R′ is a strict world, R ⊑ R′, and
`wholds R′ C (π :: env σ)`.

Proof. Transitivity, `po ⊆ ≺_R′`, the root clause, R ⊑ R′ and `wholds` hold
by construction. Irreflexivity. No step of ≺_R and no program-order step
leaves tree(π) or enters it, because π is fresh. Take a cycle and cut it
into maximal segments inside tree(π) and steps outside. A cycle with no
point outside tree(π) is a cycle of C ∪ po on the tree, which (i) excludes.
Otherwise each maximal segment inside the tree is entered by an entry and
left by an exit, so it is a bridge from z to y, and a fact of C between two
context points is a bridge too. By (ii) and `ent_sound` each bridge gives
`R ⊢ zσ ≺ yσ`. Replacing every bridge gives a cycle of ≺_R, which is
irreflexive. The same replacement turns every R′-path between two points of
R into an R-path, so R′ adds no fact between old points. The decomposition
decides membership in tree(π) by comparing roots, which is decidable, so
the proof is constructive. ∎

Proposition B, exactness. If Γ has a strict model and every strict model of
W and Γ has an extension that satisfies C at some point, then (acyc-new)
holds.

Proof. As in check-general-new.md, section 1, a fresh root suffices. (i) is
needed, because an extension restricted to tree(π) is acyclic and contains
C ∪ po. For (ii), instantiate the point variables of Γ by fresh constants
and let R0 be the closure of W, the hypotheses of Γ and program order. R0
orders two points exactly when Γ derives the fact, and it is irreflexive
because Γ has a model. Let a bridge run from z to y. If z and y are the
same point, every extension holds a cycle through the bridge, against the
assumption. Otherwise suppose ¬ Γ ⊢ z ≺ y. Then `R1 = tc(R0 ∪ {y ≺ z})` is
strict, because a cycle would need `R0 ⊢ z ≺ y`. R1 models W and Γ, and
every extension of R1 that satisfies C holds `y ≺ z ≺ … ≺ y`. ∎

So (acyc-new) is exact for every C, finite or infinite, up to contexts with
no model. Proposition 4 of check-general-new.md needed finitely many sources
and Proposition 6 left infinite C open. Over strict worlds both caveats
vanish, because no supremum of ranks is taken.

### 2.3 Why not integer or rational ranks

Integer ranks are the reading Padovani uses, and they fail exactness in two
ways. First, `Γ ⊢ x⁽ⁿ⁾ ≺ y` for every n (a hypothesis with infinitely many
facts, as the client-server constraint has) is acyclic and has no integer
model, because the ranks of x, x⁺, x⁺⁺, … rise without bound. Second, take
entries z_k ≺ v for every k, an exit v ≺ y and `Γ ⊢ z_k ≺ y`. A model with
ϱ(z_k) = −1/k and ϱ(y) = 0 leaves no rational rank for v, while the strict
closure orders v between all z_k and y. A rank codomain thus needs extra
static conditions of the kind (gen-new) has, with a maximum over finite
sets, and the maximum brings back excluded middle on any codomain where ≤ is
not decidable. Strict relational worlds avoid all three. The universe level
does not change, because `point → point → Prop` lives in Type@{Set+1} like
`rank_ord`, so a strict world can still be a creation choice of
`exist_prop`. This should be confirmed by Rocq at the use in `live_sub_df`.

### 2.4 P-Term, P-Connect and the relation

- P-Term (`fp_term`, `p_term`). `sworld_wf W ∧ swf W` becomes
  `sworld_wf W ∧ sacyc W` at N = ∞.
- P-Connect, full form (`fp_connect`). `swf (W1|S ⊔ W2|S)` becomes
  `sacyc (W1|S ⊔ W2|S)`. The analogue of `wf_join_iff` is
  `sacyc (W1 ⊔ W2) ↔ sacyc W1 ∧ sacyc W2 ∧ sacyc (W1|S ⊔ W2|S)`. A cycle of
  the join that meets a shared point rotates to start there, and
  `join_shared` turns it into a cycle of the amalgam. A cycle that meets no
  shared point stays in one zone, because a fact of Wi relates points of
  its zone, program order keeps the root, and passing from one zone to the
  other needs a point in both. So it is a cycle of W1 or W2. Both cases are
  constructive with `zone_dec`. This is about 40 lines against 120 for
  `wf_join_iff`.
- P-Connect, hidden form (`p_connect`). `swf (W1 ⊔ W2)` becomes
  `sacyc (W1 ⊔ W2)`. `swrestrict_swf`, `swf_sub` and `swf_ren` have
  one-line acyclic versions.
- The ranked worlds of the DF relation become strict worlds. No clause of
  E, V or P changes. O-New keeps `∃ S π W′, W ⊑ W′ ∧ …`, now over strict
  worlds. The comment of `Pbody` ("Every ranked world is acyclic, so the
  strictness premise of S4.15 is gone") stays true word for word.
- Readiness (relation/Readiness.v) is unchanged. `below_rest` and
  `above_offered` read `W ⊢ x ≺ y`.
- Adequacy. `adequacy_gen`, `adequacy`, `live_adequacy` keep their proofs.
  `soundness`, `live_soundness`, `soundness_h`, `live_soundness_h`,
  `soundness_source`, `connect_n_soundness` and `connect_n_live_soundness`
  take `sacyc` where they took `swf`, and use the model of section 2.1 in
  place of `wmodels_exists`.
- The E-New case of `typed_sem` calls the creation lemma of Proposition A
  through `acyc_new_sem_of`, the analogue of `gen_new_sem_of`, which reads
  (ii) through `slt_sem`.

### 2.5 Excluded middle

On the DF path EM enters only through `Erel_new` (`list_max_rank`), then
`later_new`, `typed_sem`, `fundamental`, `fundamental_proc` and every
soundness corollary. Proposition A is constructive, so `later_new` over
strict worlds takes no EM and neither does `typed_sem` at strict worlds.
`soundness`, `soundness_h`, the n-ary corollaries, `live_soundness`,
`ring_rejected` and the `*_deadlock_free` theorems of the examples drop
their `excluded_middle` hypothesis. `live_sub_df` keeps EM and functional
choice, which it needs for `exist_prop`, not for a maximum. The lock-free
side keeps EM where it has it today (`lf_soundness`, fair runs, and the
maximum in its own creation lemma).

With integer ranks the maximum would be decidable and EM would also drop,
but section 2.3 rules integer ranks out on exactness grounds.

## 3. One judgment or two

### 3.1 The static judgment

One judgment, with the mode read off N.

    new_ok N W Γ C := match N with None ⇒ acyc_new W Γ C | Some _ ⇒ gen_new W Γ C end
    wok N W        := match N with None ⇒ sacyc W       | Some _ ⇒ swf W       end

E-New asks `new_ok N W Γ C`, P-Term asks `sworld_wf W ∧ wok N W`, both
P-Connects ask `wok N` of their join. The DF judgment ⊢ and the live
judgment ⊢ with ⊢▷ are the instance N = ∞. The lock-free judgment ⊩^N is
the instance `Some N` and is unchanged.

Lemma C. `gen_new W Γ C → acyc_new W Γ C`, constructively. (i) holds
because a well-founded relation has no cycle. For (ii), take a bridge
`z ≺ s_0 ⇝ … ⇝ s_k = u ≺ y`. The exit clause gives `(u, T_k) ∈ S` with every
t ∈ T_k below y. Walking the path down, the step clause gives
`(s_j, T_j) ∈ S` with every point of T_j below some point of T_{j+1}. The
entry clause gives t_0 ∈ T_0 with `Γ ⊢ z ≺ t_0`. Then
`z ≺ t_0 ≺ t_1 ≺ … ≺ t_k ≺ y` in Γ. A fact between context points is clause
two of (gen-new). ∎

With Lemma C and `swf → sacyc`, the E-New case and the process cases of the
erasure go through. `typed_dftyped` lifts a derivation at any N to N = ∞,
so every LF-typed term is DF-typed. A process-level erasure from
`fptyped (Some N)` to `fptyped None` does not exist today. It would be one
induction with the same two lemmas plus the ticket bookkeeping of
`tenv_of (fhalf N)`, which the term-level erasure already handles.

A separate mode flag is the alternative to switching on N. It would allow a
finite ticket bound with only acyclic worlds, which no current result uses.
I recommend switching on N.

### 3.2 The relation

The world kind is a parameter of the relation, independent of the cost
table κ. Three instances are in use.

    κ_DF over strict worlds   deadlock freedom, soundness, soundness_h
    κ_L  over strict worlds   live_soundness, live_soundness_h, live_sub_df
    κ_L  over ranked worlds   the threads of the lock-free development

The last instance must take its threads from a derivation at `Some N`, which
carries (gen-new). Today `live_fundamental_typed` erases to N = ∞ first and
then calls `typed_sem`. After the change, `lf_p_term` calls `typed_sem` at
ranked worlds on the derivation at `Some N` directly. Its E-New case asks
`N = Some _` and uses the present `Erel_new`. Everything else in
`typed_sem` reads worlds through the interface and is shared.

`live_sub_df` compares κ_L and κ_DF at the same strict world, as now. Its
proof reads no rank. The LF chain argument stays where it is, in
soup/LFAdequacy.v, over the ranked instance.

## 4. Fork-join, fact and fibo

Notation of ForkJoin.v. `□∀ι. H. U` is a box over the point variable ι with
hypothesis H, `new_{x·κ}` is E-New-Field, `force f` inside a box body is the
recursive call through the box variable f, and End channels are closed at
both ends. n ranges over a data type. Every case split on n adds no fact, so
the derivations read only that both arms type. For a point x, `x·w` with w a
word over fields is the iterated field, and `(x‾)·κ = x·κ`.

### 4.1 Recursive binary fork-join with replies

    wk   = □∀ι. H. (ℕ ⊗ End@ι ⊸^⊤ ∗)
           λ(n, w). case n of
             0     ⇒ close w
             n′+1  ⇒ let (c1, c1′) = new_{ι·0} in let (c2, c2′) = new_{ι·1} in
                      spawn (λ_. force f (n′, c1′)); spawn (λ_. force f (n′, c2′));
                      close c1; close c2; close w
    main = let (w, w′) = new in spawn (λ_. force wk (k, w′)); close w

Readiness of the worker. `close c1` at ι·0 holds c2 at ι·1 and w at ι, so it
asks `ι·0 ≺ (ι·1)‾` and `ι·0 ≺ ῑ`. `close c2` asks `ι·1 ≺ ῑ`. `close w` holds
nothing. Write

    F(x) = { x·0 ≺ (x·1)‾,  x·0 ≺ x‾,  x·1 ≺ x‾ }
    H(ι) = F(ι) ∪ ⋃ { F((ι·w)‾) | w ∈ {0,1}⁺ }

The child of c1 forces the box at ι′ = (ι·0)‾. There `ι′·w = ι·0·w` and
`ι′‾ = ι·0`, so `H(ι′) ⊆ H(ι)`, and `hold_at Γ_b H(ι′)` holds by the
hypothesis of the box. The same holds for c2. E-Force asks nothing else,
and the spawned closures type at (⊤, ⊥) as in ForkJoin.v.

main creates w at a fresh root ρ with the laws `C = H(ρ‾)`, which unfold to

    ρ·0 ≺ (ρ·1)‾,  ρ·0 ≺ ρ,  ρ·1 ≺ ρ,
    ρ·w·0 ≺ (ρ·w·1)‾,  ρ·w·0 ≺ ρ·w,  ρ·w·1 ≺ ρ·w      for w ∈ {0,1}⁺

All facts lie inside tree(ρ), so there are no bridges and (ii) holds. For
(i), every fact starts at a positive point at offset 0, no fact starts at a
negative point, and program order only raises the offset. A cycle therefore
uses facts only, and only facts between positive points, which all go from
depth d + 1 to depth d. So C ∪ po is acyclic, witnessed by the potential
(−depth, offset) ordered lexicographically into ℤ × ℕ. main forces the box at
ρ‾, where the laws give H(ρ‾) on the nose, and closes w holding nothing.
P-Term types the closed program over the empty world, which is acyclic, and
DF soundness gives deadlock freedom.

(gen-new) rejects C, because `ρ ≻ ρ·0 ≻ ρ·0·0 ≻ …` descends forever. That is
Proposition 7 at work. The LF judgment keeps (gen-new) and rejects the
program, and so does any finite family of boxes for unbounded depth.

The proof of soundness over strict worlds needs no infinite descent inside
one world. The semantic box clause asks the body at every world that holds
H at ι, and the recursive force needs H at ι′, which the same world holds.
The infinite chain lives in the laws of ρ, and Proposition A builds a strict
world that holds them.

### 4.2 Padovani's fact

Padovani's process (p2) is

    *fact?(x, y). if x = 0 then y!<1> else (νa)(fact!<x−1, a> | a?(z).y!<x·z>)

In our syntax y is a reply end `!ℕ.End`.

    fact = □∀ι. H. (ℕ ⊗ !ℕ.End@ι ⊸^⊤ ∗)
           λ(x, y). case x of
             0     ⇒ send y 1; close y
             x′+1  ⇒ let (a, a′) = new_{ι·0} in
                      spawn (λ_. force f (x′, a′));
                      let z = recv a in close a; send y (x·z); close y
    main = let (y, y′) = new in spawn (λ_. force fact (k, y′)); let r = recv y in close y

a has type `?ℕ.End@ι·0`, a′ has `!ℕ.End@(ι·0)‾`. `recv a` at ι·0 and
`close a` at (ι·0)⁺ hold y at ι, so they ask `ι·0 ≺ ῑ` and `(ι·0)⁺ ≺ ῑ`, and
the first follows from the second by program order. `send y` and `close y`
hold nothing.

    F(x) = { (x·0)⁺ ≺ x‾ }
    H(ι) = F(ι) ∪ ⋃ { F((ι·0ᵏ)‾) | k ≥ 1 }
         = { (ι·0)⁺ ≺ ῑ } ∪ { (ι·0ᵏ⁺¹)⁺ ≺ ι·0ᵏ | k ≥ 1 }

The child forces at (ι·0)‾ and `H((ι·0)‾) ⊆ H(ι)`. main uses the laws
`C = H(ρ‾) = { (ρ·0ᵏ⁺¹)⁺ ≺ ρ·0ᵏ | k ≥ 0 }`. Each fact lowers the depth by one,
program order keeps the depth and raises the offset, so (−depth, offset)
rises along C ∪ po and (i) holds. There are no bridges. main receives on y
at ρ and closes at ρ⁺ holding nothing. This is Padovani's negative priority
for a (p2, p8) in the form of an infinite descending chain of points.

### 4.3 Padovani's fibo

Padovani's process (p8, Example III.6) is

    *fibo?(x, y). if x ≤ 1 then y!<x>
                  else (νa)(νb)(fibo!<x−1, a> | fibo!<x−2, b> | b?(z2).a?(z1).y!<z1+z2>)

In our syntax

    fibo = □∀ι. H. (ℕ ⊗ !ℕ.End@ι ⊸^⊤ ∗)
           λ(x, y). case x ≤ 1 of
             tt ⇒ send y x; close y
             ff ⇒ let (a, a′) = new_{ι·0} in let (b, b′) = new_{ι·1} in
                  spawn (λ_. force f (x−1, a′)); spawn (λ_. force f (x−2, b′));
                  let z2 = recv b in close b; let z1 = recv a in close a;
                  send y (z1+z2); close y

`recv b` and `close b` hold a at ι·0 and y at ι, so they ask
`(ι·1)⁺ ≺ (ι·0)‾` and `(ι·1)⁺ ≺ ῑ`, from which the facts at ι·1 follow by
program order. `recv a` and `close a` ask `(ι·0)⁺ ≺ ῑ`.

    F(x) = { (x·1)⁺ ≺ (x·0)‾,  (x·1)⁺ ≺ x‾,  (x·0)⁺ ≺ x‾ }
    H(ι) = F(ι) ∪ ⋃ { F((ι·w)‾) | w ∈ {0,1}⁺ }

The two recursive calls force at (ι·0)‾ and (ι·1)‾, two different instances,
and both satisfy `H(ι′) ⊆ H(ι)`. This is Padovani's polymorphic recursion
(p8) as two instances of one box. main uses `C = H(ρ‾)`, which unfolds to
`(ρ·w·1)⁺ ≺ (ρ·w·0)‾`, `(ρ·w·1)⁺ ≺ ρ·w` and `(ρ·w·0)⁺ ≺ ρ·w` for every word w,
the empty one included. A fact either lowers the depth or stays at one depth
and goes from a name ending in 1 to a name ending in 0. Program order keeps
the name. So the potential (−depth, 0 if the last field is 1 and 1
otherwise, offset), lexicographic, rises along C ∪ po, and (i) holds. There
are no bridges.

## 5. Cycles stay rejected

Every rejection in v2/examples rests on irreflexivity of a world or on
soundness, and each survives with acyclicity in place of well-foundedness.

- Milner's ring (examples/Ring.v). `ring_cyclic` derives `pc‾ ≺ pc‾` in the
  join of the three hidden thread worlds through `pc‾ ≺ pa‾ ≺ pb‾ ≺ pc‾`, so
  `sacyc` of the join fails and the n-ary rule rejects it.
  `ring_rejected` goes through soundness and `ring_not_df`. It stays valid
  and loses its EM hypothesis.
- The forwarder ring (`ring_rejected_full` in examples/Copycat.v). The two
  forwarders give `x ≺ y‾` and `y‾ ≺ x` (`fwd_needs`), so the joined world
  holds `x ≺ x`. The proof reads `swf_irrefl` of the joined world, which
  becomes the definition of `sacyc`.
- SharedRoots (`opposite_clash`). The whole worlds of P(c, d) and P′(e, f)
  hold a cycle at the constant 0, so they are not acyclic together. With
  hiding they compose (`opposite_compose`) and are deadlock free, as now.
- The classic two-channel cycle, `close c; close d ∥ close d‾; close c‾`
  with c at x and d at y. The first thread asks `x ≺ y‾`, the second
  `y‾ ≺ x`. Typed as two components, the join holds `x ≺ x` and P-Connect
  rejects it. Typed as one creation whose laws state both facts, the laws
  hold a cycle in tree(ρ) and (acyc-new)(i) rejects it. If the second fact
  comes from Γ and the first from an exit, the bridge asks `Γ ⊢ x ≺ y‾`
  against `Γ ⊢ y‾ ≺ x`, which makes Γ cyclic, so no model and no closed
  program reaches it.
- `sbv_rejected` (examples/SemBranch.v), the variant whose dead arm asks
  `y ≺ x‾`. The join holds `x‾ ≺ y ≺ x‾`, and the proof uses `swf_irrefl`.

Proposition A gives the general reason. A typed closed program has an
acyclic world at every step, so the finite set of waiting threads of a
reachable state has a least offered end (`finite_lt_acc`). Removing
well-foundedness only admits infinite descending chains spread over
infinitely many points, which no single reachable state contains.

## 6. Rocq cost

At a5e99e2 the files outside examples/ that mention `world` are, by
directory, compat 16, soup 11, static 8, relation 6, cost 2, test 2, types 2, fuel 1.
Their proofs read worlds through the lemmas of section 2.1, except in three
places.

1. types/Worlds.v. A class `WorldKind` with the carrier, `rin`, `w_lt`, `⊑`,
   and the 15 lemmas of section 2.1 as fields. Instance `RWorld` is the
   present record. Instance `DWorld` is the strict record of section 2.1.
   New static lemmas `sacyc`, `acyc_join_iff`, `swrestrict_sacyc`,
   `sacyc_sub`, `sacyc_ren` and `dmodels_exists`. About 150 lines.
2. static/Contexts.v. `bridge`, `acyc_new`, `new_ok`, `wok` and Lemma C.
   About 60 lines.
3. static/Typing.v. `e_new`, `fp_term`, `fp_connect`, `p_term`, `p_connect`
   take `new_ok N` and `wok N`. `fptyped_wf` and `ptyped_wf` return
   `wok N`. static/Inversion.v (2 lemmas), static/Hiding.v (5 uses),
   static/ConnectN.v (6 uses), static/Consts.v (`swf_ren`) follow.
4. static/Conservativity.v. The E-New case of `typed_dftyped` uses Lemma C.
5. compat/Redex.v. A new `Erel_new_acyc` over `DWorld`, constructive, by
   Proposition A, about 120 lines. The present `Erel_new` stays for
   `RWorld`. compat/LiveRules.v gets `later_new_acyc` without EM.
6. static/Fundamental.v. The E-New case of `typed_sem` dispatches on the
   world kind. At `DWorld` it uses `acyc_new_sem_of` for any N. At `RWorld`
   it takes `N = Some _` and uses `gen_new_sem_of`. `fundamental`,
   `live_fundamental` lose EM. A new `live_fundamental_ranked` replaces the
   erasure route in `live_fundamental_typed` for the lock-free threads.
7. static/FundamentalProc.v. The soundness theorems over `DWorld`, without
   EM, with `sacyc` premises.
8. soup/*. Fix the instance `RWorld`. soup/LFTyped.v and LFCompose.v keep
   `swf`, because the LF judgment is the instance `Some N`.
9. relation/*, compat/*, cost/*, fuel/*. A `Context` line per section and
   no change to proof bodies, except where a proof unfolds `w_lt` of a
   ranked world. `rk0_lt` and `rank_base_le` in compat/Redex.v are such
   places and stay with the `RWorld` creation lemma.
10. examples/. The DF examples prove `swf` of concrete worlds by measures
   (`swf_meas`, `wf_new_lex3`). Acyclicity follows from each, so a one-line
   wrapper `swf_sacyc` keeps every example. Rejections need `sacyc` in
   place of `swf_irrefl`. ForkJoin gains the recursive programs of section
   4, which need a potential into ℤ × ℕ for (i).

Divergence. The DF and LF developments share the relation, every
compatibility lemma, `typed_sem` but its E-New case, the static judgment and
its erasure. They differ in the world instance, the creation lemma, the
mode premises of 3 rules and adequacy, which already differs today. My
estimate is 400 to 600 new lines and a mechanical edit of about 40 files.
The parametrization is the largest part. A cheaper route that keeps one
world type cannot work. The lock-free run needs ranks fixed across a chain
of worlds, and a relation over strict worlds lets O-New pick extensions that
no rank function fits.

## What was checked and what was not

Checked on paper.

- That DF adequacy, live adequacy and every DF rejection use irreflexivity
  and transitivity of worlds only, against the sources listed above.
- Propositions A and B, Lemma C, the acyclic join lemma.
- The insufficiency of integer and rational ranks for exactness.
- The derivations of section 4 for recursive fork-join, fact and fibo, the
  closure of each H under the descent, and acyclicity of each set of laws.
- The rejections of section 5.

Not checked.

- Anything in Rocq. No statement here is mechanized.
- The universe level of the strict world record at its use in
  `exist_prop`.
- The process-level erasure from `fptyped (Some N)` to `fptyped None`,
  which does not exist today.
- The lock-free creation lemma at `RWorld` reached directly from a
  derivation at `Some N`, beyond reading that `typed_sem` already takes any
  N.
- Cost and fuel relations, which I read only as far as their use of
  worlds.
