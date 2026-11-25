# Design check, per-branch orders on old points (fx-orders)

2026-11-23, branch fx-orders from redesign 80aaef1. Write-up only, no Rocq
change. Approved by the author on 2026-11-23 ("is good i kind of want it.
draft it"). The argument is on paper. The facts of the derivation of R in
section 2 were checked by a throwaway script outside the repository
(acyclicity per slice, the bridges of E-New per slice, and the cycle of
the unsliced union). Nothing else was run.

Reading order of the sources. pending.md (the reports "slice in the
world, stage 1 stopped" and "C1 stopped at the crux"),
check-transfinite-branches.md, v2/examples/BranchExt.v,
v2/examples/PointReuse.v, cll-insights.md, proposal.md §2.3.

## Verdict

The design works for deadlock freedom and for lock freedom, with one
change of architecture. Deadlock freedom moves from the process relation
P to the state judgment of soup/ that lock freedom already uses.

1. Design. Decision points are the root points ρ, ρ⁺, ρ‾, … of a decision
   root ρ, a root that O-New picks fresh and marks. A world carries its
   decision roots D, a knowledge set K of literals s:i (the choice at the
   site s took label i), and one order per slice λ, a total map from
   sites to labels. The relation reads x ≺ y when every slice that
   extends K orders x below y. Select and branch at a decision point add
   their literal to K. Typing gains guarded facts in constraints, a
   literal set in Γ, a decision flag on constraints and one rule E-Offer.
   E-New-Field, P-Term and P-Connect do not change.
2. R. It types at N = ∞ and lies in the relation (section 2). The two
   orders x⁺ ≺ y·0 and y⁺ ≺ x·0 sit in the constraint of the creation of f
   as facts guarded by z:l and z:r. Each slice is acyclic, the union is
   not, and today's E-New rejects the same constraint without guards.
3. Lost programs. None. Every derivation of today is a derivation of the
   new system with empty guards and empty literal sets. All 36 files of
   v2/examples and all 24 ex-* entries of the map type as before,
   including the field creations inside boxes and the "x·0 twice" thread.
4. Circularity. Removed. No slice sits in the world, so a creation reads
   only K, the decisions made so far. The orders of the new root are a
   family over slices, which is the order ∃ π, ∀ λ, ∃ W′. With root-only
   decision points every run makes at most one exchange per decision
   site, so λ_r is a function and extends every K of the run.
5. P-Connect. Knowledge K works. Through P it fails, by the fx-slice
   vacuity example recast for K (section 5.1). Through the state judgment
   it works, because that judgment keeps every channel with its point and
   composes initial states only. `lf_p_connect` keeps its statement. DF
   gets the same rule, and `fundamental_proc_h`, `adequacy_h`,
   `sem_p_connect_h` and the live pair change form. `soundness_h` and
   every `*_deadlock_free` keep their statements.
6. LF. In scope, without option B. Ranks become a family over slices,
   fixed per slice at the creation of their root. Lemma F holds per slice,
   and `lf_adequacy` reads the chain of worlds at λ_r.
7. Cost. About 60 files, 18 of them in substance, in six stages. The first
   stage to mechanize is S0, deadlock freedom through the state judgment
   for today's system, with no change to worlds or typing.

## 0. The design in brief

    decision root    ρ ∈ D(W), picked fresh by O-New
    decision point   a point whose name is a decision root (any offset, either polarity)
    site             s(x) = (name of x, offset of x), polarity dropped, so s(x) = s(x‾)
    literal          s:i with i ∈ {l, r}
    knowledge        K(W), a finite consistent set of literals on decision sites of W
    slice            λ : site → {l, r}, and λ ⊨ K when λ agrees with K
    world            roots, D, K, and an order ≺_λ per slice (ranks ρ_λ when ranked)
    reading          W ⊢ x ≺ y  :=  po x y ∨ ∀ λ ⊨ K(W). x ≺_λ y

A select or branch with label i on an end at a decision point x moves the
world to W ⊕ s(x):i. Static worlds keep their form. Guards live in the
constraints of E-New, of boxes and of existentials, and a literal enters Γ
only through E-Offer.

## 1. The design of (a) and (b)

### 1.1 Decision points

A decision point is a point x with pt_name x = ρ for a decision root ρ.
Its site is (ρ, pt_off x). The fields ρ·κ, ρ⁺·κ, … are not decision
points, whatever κ is.

Claim. In every run, a decision site hosts the ends of one channel, and
that channel makes one exchange there.

Argument. O-New may place a channel at a decision point only when its
root is fresh (section 1.3). No other step moves an end to a root point.
Shift keeps the name and raises the offset, select and branch move to a
field, a payload sits at a field of the carrier (`payload_at`), spawn and
the handoff of a closure keep points. A link of o1 at x and o2 at x‾ with
x a decision point joins two ends of the one channel at that name, so it
leaves no channel behind. P-Term and P-Connect place channels at constants
and their fields, and no constant of a static world is a decision root of
a world that models it (section 1.2). Each end acts once at each point it
occupies, so each site sees one exchange.

Consequence. A guard exists at the first choice of each channel created at
a decision root, after any number of sends and receives. Later choices of
the same channel happen at fields and cannot be decisions. Lifting this is
open question Q2 (section 10).

This is route (a) of pending.md with today's point algebra. It asks
nothing of E-New-Field, because fields are never decision points.

### 1.2 Worlds

The world record of types/Worlds.v gains three components and indexes its
order by slices.

    w_dec  : gset pname                          decision roots, ⊆ w_roots
    w_kn   : gset lit                            consistent, sites of w_dec
    w_ord  : slice → point → point → Prop        a strict order per slice
    w_rk   : option (slice → point → rank_ord)   ranks per slice, when ranked

`w_ord_trans`, `w_ord_irrefl`, `w_ord_po` and `w_rk_ord` hold per slice.
The reading is the one of section 0.

    W ⊢ x ≺ y  :=  po x y ∨ (rin W x ∧ rin W y ∧ ∀ λ ⊨ w_kn W. w_ord W λ x y)

K is consistent, so some λ satisfies it, and the reading is irreflexive
and transitive (`w_lt_irrefl`, `w_lt_trans` keep their proofs). It grows
with K, because fewer slices remain.

Extension W ⊑ W′ asks

- `w_roots W ⊆ w_roots W′`
- `w_dec W′ ∩ w_roots W = w_dec W`, so only fresh roots become decision roots
- `w_kn W ⊆ w_kn W′`
- for every λ ⊨ w_kn W′, the facts of W at λ between old points hold in W′ at λ
- for every λ ⊨ w_kn W′, the ranks of W′ at λ on old points are those of W at λ.

Lemma F per slice. If W is ranked, W ⊑ W′, x and y are old points and
λ ⊨ K(W′), then w_ord W′ λ x y ↔ w_ord W λ x y. The proof of
check-transfinite-branches.md §1 runs inside one slice.

A slice lists a label for every site, so a family over slices fixes the
order of every possible future at the creation of a root, and K selects
the futures that remain.

`wmodels R W` for a static world W keeps its two clauses, read with the
new reading, and adds that no constant of W is a decision root of R. That
clause is monotone along ⊑ by the clause on `w_dec`. A world models a
context Γ when it models W, holds every hypothesis of Γ, holds every
literal of Γ in K, and holds every decision point of Γ in D. A guarded
hypothesis g ⇒ u ≺ v holds in R when every λ ⊨ K(R) ∪ g orders u below v.

The constructors `wstrict_of`, `wrank`, `wranked_of` and `wgrow` take the
constant family, D = ∅ and K = ∅. That makes every world built today a
world of the new kind with the same reading.

### 1.3 The relation

Readiness (relation/Readiness.v) keeps its text. `below_rest` and
`above_offered` read W ⊢ x ≺ y, now at K. `wholds W C xs` reads a guarded
fact g ⇒ u ≺ v of C at xs as "every λ ⊨ K(W) ∪ g orders u below v", and
asks the first instance to be a decision root when C carries the decision
flag.

Four obligations change in relation/Relation.v.

    o_new c e'        cfresh c Θ → ∃ S π W', W ⊑ W' ∧
                        (pt_name π ∈ w_dec W' → pt_root π ∉ w_roots W ∧ no literal of W' on the root of π) ∧
                        at_cost_E … W' (new_env c S π Θ) T F e'
    o_select o i e'   ∃ S0 x S1 S2, Θ !! o = Some (S0, x) ∧ unfoldS S0 = SPlus S1 S2 ∧
                        ∀ W', learn W x i W' → at_cost_E … W' (<[o := (…, sel_pt x i)]> Θ) T F e'
    o_branch o i e'   the same with SWith and bra_pt x i, at cost c_take
    q_select, q_branch   the same change in P

`learn W x i W′` holds when W′ = W and x is not a decision point of W, or
when W′ adds s(x):i to K(W) and K(W) holds no s(x):¬i. When K(W) already
holds s(x):¬i, no W′ exists and the obligation holds vacuously. Sender and
receiver compute the same literal, because their ends sit at x‾ and x and
s(x‾) = s(x).

V at an existential and at a box reads `wholds` with guards and the
decision flag. Nothing else in E, V or P reads K. Ebody and Pbody keep
their quantification over every W1 ⊒ W, which now includes growth of K.

Vacuity is harmless for E. No E-level lemma joins the obligations of two
threads (`Erel_bind`, `o_spawn`, the compat rules of terms), and the
fundamental theorem only gets easier. The only consumer that joins two
obligations into one step is a synchronization, in P (`sem_p_connect`) or
in the state judgment (`step_choice`). Section 5 shows that P cannot
excuse a vacuous pair and the state judgment never meets one.

### 1.4 The state judgment

The invariant `soup_gen` (soup/State.v) gains one clause.

    sp_dec   for every decision root ρ of s_W a, the ends of A at points named ρ
             belong to one channel, and when K(s_W a) decides a site of ρ,
             no end of A sits at a point named ρ

It is preserved step by step. A creation at a decision point picks a fresh
root by O-New and K has no literal on it. A choice at a decision site s of
ρ moves the state to s_W ⊕ s:i, and both ends, the only ones named ρ, leave
for fields, where nothing brings them back to the name ρ. Every
other step changes no point to a root point (section 1.1). So a choice at
a decision site of a reachable state finds s undecided, `learn` has its
witness, and `step_choice` (soup/SoupSync.v) gets the continuations of
both threads at the one world s_W ⊕ s:i. Every other thread holds no end
at s and moves to that world by `Erel_mono`.

`lf_sem` (soup/Soup.v) asks its state to hold no end at a decision point.
P-Term gives such a state, because the thread starts with ends at
constants. A union of two such states again has none, which is all
`soup_connect` needs of `sp_dec`.

Deadlock freedom at a reachable state. Pick any λ ⊨ K(s_W). Every thread
is ready at the reading, hence at ≺_λ. ≺_λ is a strict order on finitely
many points, so the chain argument of `pc_ready` (compat/Connect.v,
`finite_lt_acc`) finds an offered end with no partner waiting below it.

### 1.5 Typing

| Rule or definition | Change |
|---|---|
| bcs (types/Points.v) | facts carry a guard, a finite set of literals over points of the constraint, and the record gains a decision flag for its first bound variable. An unguarded fact is today's `FLt` |
| hctx (static/Contexts.v) | gains a literal set `hc_lits`. `slt W Γ` uses a hypothesis g ⇒ u ≺ v when g ⊆ hc_lits Γ. Static worlds stay unguarded |
| `hold_at` | a guarded fact g ⇒ u ≺ v of C at xs holds when `slt W (Γ + g) u v`. The flag asks xs₀ to be a decision point of Γ at offset 0 |
| `new_ok`, `acyc_new`, `gen_new`, `cons_open` | read per assignment L of the guard literals of C, today's condition for the facts of C whose guard lies in L, under Γ + L |
| E-New | its constraint may carry guards and the flag. The premise is `new_ok` per assignment. No other change |
| E-New-Field | none |
| E-Offer | new, below |
| e_branch, e_select, e_case | none |
| E-Pack, E-Force, E-Open | read guards through `hold_at` and `cons_open`. No new premise |
| P-Term, P-Connect | none. Their worlds have no guards, and `wok` is today's |

    e_offer Θ Θ1 Θ2 Θ2' Γ Δ Δ1 Δ2 Δ2' F e e1 e2 S0 x S1 S2 a mS T c0 c1 c2 :
      tsplit Θ Θ1 Θ2 → lenv_split Δ Δ1 Δ2 → unfoldS S0 = SWith S1 S2 → dec_pt Γ x →
      ub_below_s W Γ (Some x) F1 →
      typed W N Θ1 Γ Δ1 F1 e (TSess S0 x a mS) c0 →
      thage c0 Θ2 Θ2' → lage c0 Δ2 Δ2' →
      typed W N Θ2' (hc_lit x l Γ) (Some (TSess S1 (bra_pt x l) mS mS) :: Δ2') F e1 T c1 →
      typed W N Θ2' (hc_lit x r Γ) (Some (TSess S2 (bra_pt x r) mS mS) :: Δ2') F e2 T c2 →
      typed W N Θ Γ Δ F (Case (EBra e) e1 e2) T (fadd c0 (fadd (Some 1) (fmax c1 c2)))

    with F1 = sf_unionb F (tenv_heads Θ2 ∪ lenv_heads Δ2) (lenv_bot Δ2)

`dec_pt Γ x` says that x is a root point of a point variable that Γ
records as a decision root, through the flag of the constraint that bound
it. E-Offer is e_case over e_branch with the literal added to each arm. Its
semantic proof follows the two. The branch step meets O-Branch, whose
continuation runs at W ⊕ s(x):i, a world that models Γ + s(x):i, and the
case reduces by a β step at that world. When K(W) holds the other label,
O-Branch is vacuous.

Why one new rule and not fewer. A literal must come from the event that
decides it. Reading it off the point of an end (an end at bra_pt x i
proves s(x):i) would need a clause of the relation that ties the points of
an environment to K, and E-New-Field may put an unrelated channel at
bra_pt x i. That is open question Q3, not adopted. The selector needs no
rule for R. E-SelectIn, the analogue on the selecting side, adds
expressiveness and is left out by the rule of fewest rules.

Guards need no premise on their sites. A guard on a site that is no
decision site never fires, because only E-Offer adds literals and it asks
`dec_pt`.

## 2. The program R

### 2.1 Source

R is D23 of CLL≺ (check-transfinite-branches.md §2) closed by a selector,
with e, c and f created by main. z, x and y are the fresh roots of e, c and
f. The payload field of a point p is p·0.

    T a b = let ⟨p′, p⟩ = new in let a = send ⟨p′, a⟩ in close p;
            let ⟨q′, q⟩ = new in let b = send ⟨q′, b⟩ in close a; close q; close b
    U a   = let ⟨r, a⟩ = recv a in close r; close a

    main  = let ⟨e, ē⟩ = new in                  E-New, decision root z, C_e = ∅
            let ⟨c, c̄⟩ = new in                  E-New, root x, C_c
            let ⟨f, f̄⟩ = new in                  E-New, root y, C_f
            spawn (λu. u; close (select l ē));
            spawn (λu. u; U c̄);
            spawn (λu. u; U f̄);
            case branch e of inl w ⇒ close w; T c f
                           | inr w ⇒ close w; T f c

c and f carry one end of protocol end and then close, `!end.end` on the
side of T. The new channels p and q of T are field creations at x·0 and
y·0 (E-New-Field), with p′ at x·0 and p at (x·0)‾. Arm l acts on x before
y, arm r on y before x. Every run terminates.

### 2.2 The facts each thread needs

A blocking action on an end at u while an end at v is held needs u ≺ v‾
(readiness). A send at u also needs u ≺ v‾ for the carried end at v.

    main before the case   z ≺ x̄, z ≺ ȳ
    arm l (T c f)          z·0 ≺ x̄, z·0 ≺ ȳ, x ≺ (x·0)‾, x ≺ x·0, x ≺ ȳ,
                           (x·0)‾ ≺ x̄⁺, (x·0)‾ ≺ ȳ, y ≺ (y·0)‾, y ≺ y·0, y ≺ x̄⁺,
                           x⁺ ≺ y·0, x⁺ ≺ ȳ⁺, (y·0)‾ ≺ ȳ⁺
    arm r (T f c)          the same with x and y exchanged and z·1 for z·0
    U c̄, U f̄               x·0 ≺ x⁺, y·0 ≺ y⁺
    selector               none

Arm l and U f̄ give x⁺ ≺ y·0 ≺ y⁺, arm r and U c̄ give y⁺ ≺ x·0 ≺ x⁺, so
the union of all facts has the cycle x⁺ ≺ y·0 ≺ y⁺ ≺ x·0 ≺ x⁺. Each arm with
both copies of U is acyclic.

### 2.3 The derivation at N = ∞

The constraints, with x, y the bound variable of each creation and earlier
roots in its environment.

    C_e = ∅, decision flag set
    C_c = z ≺ x̄, z ≺ x·0, z·0 ≺ x̄, z·1 ≺ x̄, z·0 ≺ x·0, z·1 ≺ x·0,
          x·0 ≺ x⁺, x ≺ (x·0)‾, x ≺ x·0, (x·0)‾ ≺ x̄⁺                    all unguarded
    C_f = z ≺ ȳ, z·0 ≺ ȳ, z·1 ≺ ȳ, y·0 ≺ y⁺, y ≺ (y·0)‾, y ≺ y·0, (y·0)‾ ≺ ȳ⁺
          [z:l]  x ≺ ȳ, (x·0)‾ ≺ ȳ, y ≺ x̄⁺, x⁺ ≺ y·0, x⁺ ≺ ȳ⁺
          [z:r]  y ≺ x̄, (y·0)‾ ≺ x̄, x ≺ ȳ⁺, y⁺ ≺ x·0, y⁺ ≺ x̄⁺

- E-New for e with the flag, E-Open. Γ records z as a decision root.
- E-New for c, E-Open. C_c has entries from the tree of z and facts inside
  the tree of x, no exit, so `acyc_new` holds with no bridge.
- E-New for f, E-Open. The guard literals of C_f are z:l and z:r, so
  `new_ok` is read twice. Under z:l the only exit is y ≺ x̄⁺ and no entry
  reaches y through the tree of y, so there is no bridge. Under z:r the
  entries z ≺ ȳ, z·0 ≺ ȳ and z·1 ≺ ȳ reach the exits y⁺ ≺ x·0 and
  y⁺ ≺ x̄⁺ through ȳ ≺ y⁺, and C_c derives the bridges z ≺ x·0,
  z·i ≺ x·0, z ≺ x̄⁺ and z·i ≺ x̄⁺. The tree of y is acyclic under each
  assignment.
- The three spawns by `e_spawn_lam`. Each spawned body needs only its own
  facts, which are unguarded and in C_c or C_f.
- E-Offer at z, which is a decision point of Γ. The premise
  ub_below_s z F1 asks z ≺ x̄ and z ≺ ȳ. Arm i is typed under Γ + z:i, so
  the facts of C_f guarded by z:i are available. Every fact that arm i
  needs is in C_c, in the unguarded part of C_f, or in the part guarded by
  z:i. The script confirmed that nothing is missing.

So main types by `dftyped` at the empty world, and P-Term types the closed
program.

Today's rules reject this derivation. Drop the guards of C_f. Then the
entry x⁺ ≺ y·0 [l], the tree fact y·0 ≺ y⁺ and the exit y⁺ ≺ x·0 [r] form
a bridge x⁺ ≺ x·0 that Γ does not derive. Adding it to C_c closes the
cycle x·0 ≺ x⁺ ≺ x·0 with the fact of U. Whether every derivation of R
fails today is not proved. check-transfinite-branches.md §2 argues it
through the relation.

### 2.4 R in the relation

The fundamental theorem gives main in E at every world that models the
empty world, and the state judgment carries it along every run.

- The creation of e picks a fresh root z, puts it into D and leaves K
  empty. The creations of c and f pick fresh roots x and y. For each slice
  λ the new order is ≺_λ closed under C_c, and under the part of C_f whose
  guard λ satisfies. Each slice stays strict by the proof of `Erel_new`
  applied inside that slice, because `acyc_new` holds under the
  assignment that λ induces on the guard literals.
- No other thread can fix the opposite of a guarded fact. An extension
  must keep every slice strict, and the slices with z:l already hold
  x⁺ ≺ y·0. This is the difference from C1, where the arm added its fact
  at the branch, after a partner could have fixed the opposite
  (`bx_not_E`).
- The selector and main meet at z. z is undecided, because e is the only
  channel at z. The state moves to K = {z:l}. Main continues in arm l and
  reads the slices with z:l, U and V read every slice and need only
  unguarded facts.
- At any reachable state, pick λ ⊨ K. All readiness facts hold at ≺_λ,
  which is strict, so no state is a deadlock.

### 2.5 R in the lock-free relation

R also has a lock-free typing at a finite N, argued and not checked for
tickets. The ranks of a slice are fixed when their root is created,
for every slice at once. Under z:r the new points ȳ and y⁺ must sit
between z and x·0, so the context needs a chain of that length below x·0.
(gen-new) asks for it through partner sets. Add z ≺ x, z·i ≺ x, x ≺ x̄ and
(x·0)‾ ≺ x·0 to C_c, which keeps both slices acyclic (checked). Under z:r
the partner map y ↦ z, (y·0)‾ ↦ x, ȳ ↦ x, y·0 ↦ x, y⁺ ↦ (x·0)‾ meets the
three conditions of `gen_new_rel`. Under z:l the only exit is y ≺ x̄⁺, met
by y ↦ z.

## 3. Lost programs

None.

Embedding. A derivation of today is a derivation of the new system with
every guard empty, every flag unset and every literal set empty. Every
changed definition reduces to today's on such data.

- `slt` with hc_lits = ∅ uses exactly the unguarded hypotheses, which are
  all of them.
- `new_ok` per assignment has one assignment, the empty one, and reads
  today's condition.
- `hold_at`, `cons_open` and `wholds` without guards and flags are
  today's.
- E-Offer adds derivations and removes none. e_case, e_branch, e_select,
  E-New-Field, P-Term and P-Connect are unchanged.
- The new clause of O-New constrains only creations at decision points.
  The semantic E-New picks a fresh root and E-New-Field a field, so the
  fundamental theorem keeps every case.

Statements that read the relation by hand keep their truth.

- `bx_not_E` speaks of `bx_R`, which becomes the world with the constant
  family, D = ∅ and K = ∅. Its proof reads the same steps.
  `bx_rejected` goes through the fundamental theorem and stays true. The
  point z of bx_thread is a constant, which is never a decision point, so
  E-Offer does not apply.
- `fp_unrealizable` uses only irreflexivity and transitivity of the
  reading, which hold.
- The rejections `rx_chain_rejected`, `fjr_lf_rejected` (Descent.v),
  `rx_relink_rejected`, `rx_postpone_rejected`, `rx_delegate_rejected`
  (Rejects.v) and `sbv_rejected` (SemBranch.v) quantify over all
  derivations. None of these terms contains `Case (EBra _) _ _`, so no
  derivation of them uses E-Offer, Γ never holds a literal, and every
  guarded fact is dead. Erasing the guarded facts maps such a derivation
  to one of today, because each per-assignment premise implies today's
  premise on the unguarded part. The proofs gain this erasure lemma and
  the E-Offer case of the skeleton and inversion lemmas.

Per example.

| File | Map entry | What it uses | Verdict |
|---|---|---|---|
| BranchExt.v | ex-branch-ext | semantic world by hand, case on a branch at a constant | unchanged, see above |
| ClientServer.v, LFClientServer.v | ex-cs | E-New, boxes | types |
| LFClientServerSplit.v | ex-cs-split | two components, `lf_p_connect` | types |
| Copycat.v, CopycatTwo.v, CopycatTwoN.v | ex-copycat, ex-forwarder | E-New-Field at independent points, P route by hand | types, the hand proof ports to the state judgment (S0) |
| Cycle.v, LFCycle.v | ex-cycle | E-New | types |
| Descent.v | ex-forkjoin | prop7, rejections | types, rejections need the erasure lemma |
| FactoryEx.v, LFFactoryEx.v | ex-factory | boxes, E-New | types |
| FlagPair.v | ex-flagpair | case on a received flag | unchanged, a case on data gets no literal |
| ForkJoin.v | ex-forkjoin | 7 field creations, 4 boxes | types |
| FreshBetween.v, LFFreshBetween.v | ex-between | E-New inside a box | types |
| FreshMany.v, LFFreshMany.v | ex-many | E-New inside a box | types |
| GenNew.v | ex-gennew | (gen-new) with exits | types, one assignment |
| GrowRing.v, LFGrowRing.v | ex-ring | boxes | types |
| GuardEx.v | ex-guard-neg, ex-guard-pos | boxes | types |
| LetVarCounter.v | none | existential under a box | types |
| LFClose.v, LFController.v, LFLink.v | ex-close, ex-controller, ex-link | soup judgment | types |
| PointReuse.v | ex-point-reuse | E-New-Field at x·0 twice | types, x·0 is a field and no decision point |
| Rejects.v | (rejections of the explorer) | skeletons | unchanged, erasure lemma |
| Ring.v | ex-ring3 | n-ary P-Connect | types |
| SemBranch.v | ex-flag | case on data, P route by hand | types, the hand proof ports to the state judgment (S0) |
| SharedRoots.v | ex-shared | hiding | types |
| SinstStuck.v | ex-sinst | contractivity | unchanged |
| TreeTopo.v | ex-tree | P route by hand | types, the hand proof ports (S0) |
| Tools.v, Tools2.v, LFTools.v | none | derivation helpers | unchanged |

The two programs of the fx-slice report. Field creations inside boxes
type, because E-New-Field has no new premise. The thread that twice
creates at x·0 and closes the new end while it holds y types, because x·0
is a field and needs no freshness.

SemFlag.v and SemRounds.v live on fx-branch and later branches, not on
redesign 80aaef1. Neither uses EBra or ESel (checked on aec0b4b for
SemFlag), so the erasure argument covers them.

## 4. The circularity of obstruction 3

Removed, under two conditions that the design meets.

1. A creation reads only K. The world holds no slice, only the family of
   orders over slices and the decided literals. O-New picks S, π and W′
   from the current world, so the point π depends on decisions made
   before the creation and on nothing later. W′ fixes an order for every
   slice at once, which is ∃ π, ∀ λ, ∃ order, the order of quantifiers of
   pending.md route (c).
2. Decision sites are root points. Section 1.1 gives one exchange per
   site and run, so λ_r, the label exchanged at each site in the run r
   (an arbitrary label where r exchanges nothing), is a function. Every
   K_k along r is a set of literals of exchanges of r, so λ_r ⊨ K_k.

λ_r is defined after `lfsoup_run` has fixed every creation choice of r, by
excluded middle (does an exchange occur at s) and functional choice, both
hypotheses of `lf_adequacy` already. Nothing reads λ_r back, so there is
no circle.

The fx-slice example of obstruction 3 is excluded twice. Its proof of
O-New placed a channel at z1 or z0 according to λ(z0), a label not yet
decided. With K, an undecided z0 offers nothing to read. And z0 and z1
host one channel each when they are decision points.

A slice in the world (option A of check-transfinite-branches.md) stays
circular, even with λ_new restricted to the new points. W then carries λ
on old undecided sites, and the choice of π may read them. That route is
stopped.

## 5. P-Connect and the vacuity of obstruction 2

### 5.1 Knowledge through P fails

Counterexample, R of section 2 with the selector. Run until main, the
selector, U and V are four threads and e is still at z. At that state the
process relation P must hold at every W1 ⊒ W (Pbody), and W1 may hold
z:r in K. The selector's select l and main's branch l are both vacuous at
W1, because `learn W1 z l` has no witness. Their synchronization is an
internal step of the composite of the two components that hold ē and e.
Q-Admin asks some W′ ⊒ W1 with the composite after the step in P. Every
such W′ holds z:r, and main in arm l is not ready there, because the slices
with z:r order y·0 ≺ y⁺ ≺ x·0 ≺ x⁺ and arm l closes c at x⁺ while it holds
q at (y·0)‾. So no W′ exists, and `sem_p_connect` fails at W1.

`q_tau` cannot excuse the step, because the event of an internal
synchronization names ends and a label but no point. The same failure
occurs one level down, inside a component whose hidden channels were cut
channels of an earlier P-Connect, and through the larger cut that a
delegated closure creates.

Framing the extension (no W1 that decides a site of Σ) does not help. The
composite would have to know that the hidden sites of one component are
not interface sites of the other, which P cannot state.

### 5.2 A ghost environment

A P that carries the ends of its hidden channels with their points can
state one channel per decision site, excuse a disagreeing internal
synchronization, and promise that its steps keep the property. That is
the environment A and the ownership map K of `soup_gen` rebuilt inside P,
with the fusion renamings of `Pbody` applied to the ghost. Not pursued.

### 5.3 Knowledge through the state judgment works

The state judgment avoids both failures.

- It keeps every channel with its point (A), so `sp_dec` is statable and
  `step_choice` knows the site of every synchronization.
- It is existential in its world. `lf_sem` asks for some state at each
  index, and a state follows a run, so its K is the K of real decisions.
  The vacuous case of `learn` never fires along a state.
- It composes initial states only. `lf_soup_connect` joins two states that
  hold no end at a decision point (section 1.4), so their union satisfies
  `sp_dec` with no premise about hidden channels.

`lf_p_connect` (soup/LFCompose.v) keeps its statement. Its proof is
today's plus the `sp_dec` clause of the union. The second component is
still read at the world of the first, and both have no ends at decision
points, so a fake literal in that world concerns no channel of either.

DF through the state judgment. `soup_gen` is generic in the relation of
its threads. The DF instance takes `Erel κ_DF` and the trivial fuel part,
at N = None. Its composition rule `df_p_connect` is `lf_soup_connect` at
that instance, and its adequacy is the finite chain argument of section
1.4.

DF results that change form.

- `fundamental_proc_h` concludes the DF state judgment through
  `ptyped_sem`, in place of `sem_ptyped_h κ_DF`.
- `sem_p_connect_h` and `sem_p_connect_sw` give way to `df_p_connect`.
- `adequacy_h` reads the state judgment.
- `live_fundamental_proc_h`, `live_adequacy_h` and `live_soundness_h`
  move the same way at κ_L, with `soup_no_tau_divergence` for divergence.
- `soundness_h` and every `*_deadlock_free` of the examples keep their
  statements.
- The P relation, `sem_p_connect` (compat/ConnectP.v) and `adequacy`
  (relation/Adequacy.v) stay true where they hold, but they leave the
  soundness path. `sem_p_connect` as stated becomes false (5.1), so it
  needs a premise that no decision point is ever reached, or retirement.
  The three examples that use the P route by hand (SemBranch, TreeTopo
  and Copycat through `sem_p_term_sw`) port to the state judgment.

## 6. Lock freedom

In scope, without option B.

- Ranked worlds carry ranks per slice,
  `w_rk : option (slice → point → rank_ord)`. A creation chooses the ranks of its root for every slice.
  Lemma F per slice says they never change. Ordinals of relation/Ord.v
  suffice, no new index is needed.
- The semantic E-New of soup/LFTyped.v runs `gen_new_ext` per slice. A
  family of rank functions over slices needs either a construction that is
  uniform in λ or functional choice. Functional choice is already a
  hypothesis of `lf_adequacy`. Whether `gen_new_ext` is uniform is the
  first thing to check in S5.
- `lf_adequacy_soup` instantiates the criterion with `wchain_lt` at λ_r,
  the order of the ranks at λ_r along the chain of worlds of the run.
  These ranks are fixed once chosen, so `wchain_lt_wf` applies at λ_r.
  Readiness at each state holds at every λ ⊨ K_k, in particular at λ_r.
- `exist_prop` needs the choice type in the universe of the limits of Ix.
  A family over slices adds a function from a type in Set to `tchoice`,
  which leaves its universe unchanged.

Option B stays unnecessary. Its only gain over this design was deciding
points created after the ordered points, and section 9 shows that no sound
rule can order old points under a younger decision.

## 7. Cost

Stages, each with its own build and `make check`.

| Stage | Content | Files in substance | Mechanical |
|---|---|---|---|
| S0 | DF and live through the state judgment for today's system. Generalize `soup_inv` over the thread relation and the fuel part, DF instance, `df_p_connect`, DF adequacy by the finite chain, restate `fundamental_proc_h` and `adequacy_h` | soup/State.v, Soup.v, SoupCompose.v, new soup/DFAdequacy.v, static/FundamentalProc.v | soup/SoupStep.v, SoupSync.v, SoupLink.v, SoupTau.v, SoupRun.v, LFCompose.v, LFTyped.v, three examples |
| S1 | Worlds with D, K and slice families. Every constructor takes the constant family, D = ∅, K = ∅ | types/Worlds.v, relation/Ranks.v | about 14 files that build worlds, compat/*, soup/* rebuild |
| S2 | The four obligations, `learn`, guarded `wholds`, V at TEx and TBox | relation/Relation.v, relation/Readiness.v, compat/Redex.v | relation/Closure.v, compat/Rename.v, RenameInd.v, LiveRules.v, Bind.v |
| S3 | Guarded constraints, flag, literals, per-assignment `new_ok`, E-Offer, fundamental cases, erasure lemma | types/Points.v, static/Contexts.v, static/Typing.v, static/Fundamental.v, static/Conservativity.v | static/PointSubst.v, PointSubstTyped.v, Inversion.v, Skeleton.v, Weakening.v, Sinst.v, ChanRen.v, LetVar.v, Consts.v, Constants.v, ConnectN.v, ConnectNExact.v, cost/CostFund.v, CostRules.v, examples/Descent.v, Rejects.v |
| S4 | `sp_dec`, `step_choice` with learning, `step_new` at a fresh decision root, `lf_sem` clause, DF adequacy at λ ⊨ K | soup/State.v, SoupSync.v, SoupStep.v, Soup.v | soup/SoupRun.v, LFEvents.v, LFLocal.v |
| S5 | LF. Ranks per slice in E-New, λ_r in adequacy | soup/LFTyped.v, soup/LFAdequacy.v | types/Worlds.v (`wchain_lt` at a slice), lockfree/Criterion.v untouched |
| S6 | examples/OfferOrder.v with R at N = ∞, then its LF typing, map entry, explorer | new example | docs/explorer |

About 60 files change, 18 in substance. The 15 files that build `BCs`
directly and the 32 that write `FLt` need no edit when `FLt` and the
two-argument `BCs` stay as notations for the unguarded, unflagged case.
The four notation tests need regenerated .expected files after S1 and S3.

Lemmas that change in substance. `wext`, `w_lt`, `w_ord_rank`,
`wext_rank`, `w_lt_wf`, `wchain_lt`, `wchain_lt_wf`, `wmodels`,
`wmodels_exists`, `dmodels_exists`, `join_models`, `wstrict_of`, `wrank`,
`wranked_of`, `wgrow`, `o_new`, `o_select`, `o_branch`, `q_select`,
`q_branch`, `Vbody` at TEx and TBox, `wholds`, `slt`, `hold_at`,
`new_ok`, `acyc_new`, `gen_new`, `cons_open`, `hc_open`, `Erel_new`,
`gen_new_ext`, `fundamental_typed`, `soup_gen`, `world_next`,
`step_choice`, `step_new`, `lfsoup_step`, `lf_sem`, `lf_soup_connect`,
`lf_adequacy_soup`, `fundamental_proc_h`, `adequacy_h`, and the live
pair.

First stage to mechanize. S0. It is the change of architecture that
section 5 rests on, it needs no new world and no new rule, and its
acceptance test is sharp. `soundness_h` proved through the state
judgment with an unchanged statement and `make check` at today's count.
If S0 fails, the design falls back to the ghost environment of 5.2. The
first lemma of S4, `sp_dec` preserved by every step, is the second risk
and can be prototyped right after S0.

## 8. Known counterexamples

| Counterexample | Under this design |
|---|---|
| BranchExt, `bx_not_E` | Still true, unchanged world. A per-arm order needs guarded facts present from the creation of the younger point, so no partner can fix the opposite. bx_thread offers at a constant, which is no decision point, so `bx_rejected` stands |
| D23 composition of C1 (two threads, each with per-branch facts, deadlock under mixed labels) | Rejected. The facts of both offers guard one constraint, and `new_ok` is read under every assignment, so the mixed assignment (e1:l, e2:r) closes the cycle. Correlated choices are rejected as in CLL≺ (D23, O9) |
| PointReuse | Types. Its two exchanges sit at the field x·0, which is no decision point, so no literal arises |
| R of check-transfinite-branches.md | Types (section 2), in DF and LF |
| R′ (the decision created after c and f) | Rejected. A guarded fact between old points in the constraint of the younger decision root is a fact between two context points, which `cons_open` asks Γ to derive under the assignment. Semantically it is unsound by the Kripke argument of BranchExt |
| R with e at a field of x (check-transfinite §4.3) | Rejected, fields are no decision points. No program of today is lost |
| Descent rx-chain | Still rejected. No offer, so every derivation erases to one of today, and `prop7` applies |
| fx-slice vacuity (obstruction 2) | Breaks P (5.1). Never arises in the state judgment, because a state's K is real and `sp_dec` keeps decided sites empty |
| fx-slice placement by λ(z0) (obstruction 3) | Impossible, a creation reads K only and an undecided z0 offers nothing |
| fx-slice "x·0 twice" thread | Types, fields need no freshness |

## 9. Routes stopped

- Slice in the world (option A). Circular by obstruction 3, also with λ_new
  on new points only (section 4).
- Knowledge through P. Counterexample in 5.1.
- Knowledge at every point, fields included. PointReuse exchanges l and
  then r at x·0, so K would become inconsistent, `learn` would have no
  witness for the second exchange, and the state judgment could not follow
  the run. Decision points must be root points.
- Decision constants, sites at constants of the static world. A component
  that declares the interface constant a a decision root with e at a, and
  a second component whose world contains a and that holds a restricted
  channel d at a, compose by P-Connect, which cannot see d. A run in which
  d exchanges r at a first and e then receives l at a meets an
  inconsistent K. The open component of D23, with e free, needs this, see
  Q1.
- Guards on old points under a younger decision root (R′). Unsound by the
  Kripke argument of BranchExt, so no rule may add them, and option B
  brings nothing beyond this design.

## 10. Open questions for the author

- Q1. Decision constants. The open D23, with e an interface end, needs
  constants as decision roots. That needs the hidden world of `ptyped` to
  record which interface constants host hidden channels, and P-Connect to
  check it. A new component of the static judgment, not adopted.
- Q2. Later choices on one channel. Making the continuation fields of a
  choice at a decision site decision points again needs E-New-Field
  forbidden at exactly those names. That loses nothing of today, because
  no decision root exists today, and costs anchored creation at that one
  name, where no message lands. The alternative, branch points apart from
  payload fields, contradicts K11 of proposal §2.3. Not adopted.
- Q3. Literals from the points of ends. Holding an end at bra_pt x i would
  prove s(x):i if E-New-Field were forbidden at the branch fields of
  decision points and the relation tied the points of an environment to K.
  The second part is a clause of the relation about environments. Not
  adopted, E-Offer is used instead.
- Q4. The P route. Keep P with a premise that no decision point is
  reached, or retire `sem_p_connect` and compat/Connect*.v from the
  soundness path after S0.
- Q5. Value literals. A case on received data (FlagPair, SemBranch) stays
  outside. Covering it needs literals for values at decision sites, a send
  at the decision site, and a rule like E-Offer for E-Recv followed by a
  case. Not part of this design.
