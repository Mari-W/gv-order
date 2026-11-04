# B. Context-free session types

Goal. Deadlock freedom for context-free session types by orders, with the
compositional logical relation unchanged in shape.

## Background

Thiemann and Vasconcelos (ICFP 2016) add Skip and sequential composition S;S.
Equivalence holds up to the monoid laws and the distribution of choice over ;
(Lemma 3.4). Tree serialization needs polymorphism over the continuation,
sendTree : ∀α. Tree → TreeC;α → α, and polymorphic recursion, which the paper
calls essential (pp. 2–3).

Mordido and Pérez (2026) make context-free session types deadlock free with
priorities. Each channel carries a priority sequence, which new fixes as
n₁ + k·n₂. Priority polymorphism ranges over intervals, and fix is a constant.
Our counterpart replaces the fixed sequences by a world. It admits cycles and
partial orders.

## Outline

1. Session syntax. S ::= Skip | S;S | !T | ?T | ⊕{…} | &{…} | μX.S | X, with
   duality pointwise. The relation needs only the head normal form of a
   contractive type (unr, Lemma 3.8 of Thiemann and Vasconcelos). A
   synchronization obligation reads the first action, so E and P keep their
   clauses.
2. Points after a segment. An instant still counts actions, so points stay
   (c, k). After sendTree the continuation sits at ι + n, and n depends on the
   tree. The type quantifies over the offset.

   ```
   sendTree : □(∀ι ζ α. C. Tree → (TreeC;α)@ι ⊸^ζ ∃n. α@(ι+n))
   C = {ι+k ≺ ζ ∣ k ∈ ℕ}
   ```

   This was the sketch. The mechanized type (sharp edges 73) has no Tree
   argument and returns ∃ι′≽ι. C′. α@ι′ with C′ = {ι ≺ ι′} ∪ {ι′+k ≺ ζ ∣ k}.
   The existential binds a point with a lower point, not an offset.

   The ceiling ζ is the one of the tail-call example. The recursive calls stay
   inside C for every offset, because C[ι+1+n/ι] ⊆ C. This coarse version needs
   offset variables in points (ι+n with n bound by ∃) and nothing new in the
   constraint language.

   The coarse ceiling also bounds the continuation, and that fails as soon as
   another channel acts between the segment and the continuation.

   ```
   sendTree t c ; close d ; send v c
   ```

   The world needs (c,k) ≺ (d,0) for k < n and (d,0) ≺ (c,n), with n the size of
   t. Two additions can express it.
   - Facts that depend on data. C = {ι+k ≺ ζ ∣ k < n} ∪ {ζ ≺ ι+n} with n a term
     over the tree (direction C, offsets as terms). The world of a closed program
     then contains facts at the concrete n.
   - Segment ends as names. A new root names "the instant where the segment that
     starts at x ends", like a carried root names a message position. ζ below
     the end is then a plain fact. Every point of the segment below ζ becomes
     the conditional fact x+k ≺ end ⇒ x+k ≺ ζ, which is not positive.
     The run fixes the alias between the end and a concrete instant, so the world
     must learn an alias between existing points while the program runs
     (direction C, worlds that grow).
3. Polymorphism over session types. ∀α under □, next to ∀ιs. α occurs only in
   session positions S@x, and V reads those only through V-Chan. If V recurses on
   the value structure of a type and treats session subterms as opaque, T[S/α]
   has the structure of T and V stays well founded without an index cost.
4. Static rules. Skip, sequencing, conversion up to the CFST equivalence and
   Γ ⊢ ≡, and instantiation of α at force. Recursion stays an ordinary force.
5. Composition. P-Connect, P-Term and the bind lemma read labels only. They carry
   over without change.

## Target examples

- sendTree and recvTree (Thiemann and Vasconcelos 2016).
- Stream, the binary tree with polymorphism per node, and the
  scheduler A.5 (Mordido and Pérez 2026). Every example of Mordido and Pérez
  should type here, which feeds direction D.

## Decisions for the mechanization (2026-10-30, overnight, to be confirmed)

The author asked for full context-free session types on the logical relation.
The decisions below follow the philosophy of the core. They keep the relation
and the composition lemmas free of syntactic premises, stay close to Thiemann
and Vasconcelos, and leave PGV and Padovani–Novara alone. Each is provisional
and logged in SHARP-EDGES.

- K1. Session syntax. S ::= Skip | S;S | !P | ?P | ⊕(S, S) | &(S, S) | Close |
  μX.S | X | X̄. Send and receive lose their continuation, as in Thiemann and
  Vasconcelos. Choice is binary, and n-ary choice nests. The existing session
  type variables X and their duals X̄ serve as continuation variables.
- K2. Close needs no position rule. After a close the entry leaves the
  environment, so the rest of Close;S is never read. No well-formedness
  condition forbids it.
- K3. Equivalence is bisimilarity on the LTS of Thiemann and Vasconcelos over
  contractive types, with the monoid laws of Skip and ;, the distribution of
  choice over ;, and equirecursive μ. The relation reads only the head normal
  form unr(S), whose cases are Skip, !P;S′, ?P;S′, ⊕(S₁,S₂), &(S₁,S₂), Close and
  a variable. Duality is pointwise and maps X to X̄.
- K4. Choice in the calculus. Two new constants select₁, select₂ and one new
  constant branch with labels c◁i and c▷i. Selecting gives a step like send and
  costs 0. Branching waits like receive and costs 1. branch returns a sum, so
  case does the dispatch. Readiness treats a selection like a send and a branch
  like a receive.
- K5. Points. Every action, choices included, moves the instant by one. Skip
  and ; move nothing. For choices K10 replaces it.
- K6. Polymorphism over the continuation. A box binds session type variables
  next to its point variables, □(∀ιs αs. C. ∗ ⊸^u_⊤ T). V-Box quantifies over
  all closed session types for αs. V reads a session type only through V-Chan,
  so instantiating α keeps the recursion of V well founded.
  As built, V-Box quantifies over hereditarily contractive session types
  (sharp edges 73).
- K7. Existential points. A new type former ∃ι. C. T with a positive
  constraint C, the dual of the box binder. V⟦∃ι. C. T⟧ holds when some point x
  satisfies C[x/ι] and the value lies in V⟦T[x/ι]⟧. sendTree returns
  ∃ι′. C. α@ι′ for the instant after its segment.
- K8. Facts about segments use the coarse ceiling, a point ζ with ι+k ≺ ζ for
  every k. Facts that depend on the length of the segment wait for direction C.
  The example sendTree t c ; close d ; send v c stays outside.
- K9. Branch layout. The work happens on a branch cfst from orders-lr. PGV and
  Padovani–Novara (theories/pgv, theories/pn) leave that branch's build and are
  not ported.
- K10. Branch roots (2026-10-31, approved by the author, replaces K5 for
  choices). selectᵢ and branch move the entry of c from x to the branch root
  x◁i, a new point name like the carried root x.i. The world laws gain
  congruence x ≡ y ⇒ x◁i ≡ y◁i and program order x ≺ x◁i. Send, receive and
  close still move by one. Ceilings over ι+k become ceilings over the walks
  from ι, the points reached by successors and branch roots. The program T2 of
  data-dependent.md types in BranchOrder.v and did not under K5. SHARP-EDGES 76
  has the details.
- K11. A choice continues at the point of a payload (2026-11-04, decided by
  the author, replaces K10). selectᵢ moves the entry of c from x to x[i],
  the same point the i-th channel of a message sent at x gets, with
  x[0] for the first branch and x[1] for the second. branch returns
  S₁@x[0] + S₂@x[1]. The name x◁i is gone, with its congruence and its
  program-order law. x[i] already has congruence. Program order does not
  relate x and x[i], so selectᵢ owes x ≺ x[i] and branch owes x ≺ x[0] and
  x ≺ x[1] in their signatures, the way send owes x ≺ heads(P[x]). The
  programs state these facts in creation constraints or box constraints.
  Walks for ceilings go through x+1 and x[i]. Choice stays primitive. On
  branch `exists`, docs/extensions/choice-encoding.md derives it from sums
  and delegation with the arms at self[0] and self[1].
- K12. K7 is replaced by the existential of branch `exists` (2026-11-04).
  ∃^ℓ ιs. C. T has a lower bound ℓ that is ⊤, ⊥ or a point, E-Pack asks
  the ⊥ flag of the packed type to be off unless ℓ = ⊥, and new has the one
  signature ∗ ⊸ ∃^⊥ ι. C. (S@ι ⊗ S̄@ι) with C a creation constraint. A
  segment function returns ∃^ℓ ι′. C′. α@ι′ with ℓ = ι and the ceiling facts
  in C′.
- K13. V-Box keeps the reading of K6 (2026-11-04). The thunk lies in the
  arrow relation at the instance sinst(ss, T[xs/ιs]). Branch `exists` reads
  the thunk through V at the body under a point substitution, so that V
  stays structural. A session instance is no point substitution, so that
  reading would need a second substitution argument in V and its
  composition laws for session types. K6 already shows that the arrow
  reading is sound with existentials, because `Vrel_box_iff` states it with
  `Vlam` and no proof needs a λ in V at a type other than an arrow.
- K9 no longer holds. theories/pgv and theories/pn are in the build again.

## Order of work

1. Stage A. Session syntax K1, head normal form, contractiveness, bisimilarity
   and duality K3, choice constants and labels K4 in the LTS.
2. Stage B. The relation for the new labels and the head normal form, readiness,
   costs, and the composition lemmas P-Connect, P-Term, internalizing a link and
   the bind lemma.
3. Stage C. Boxes over session variables K6 and existential points K7 in the
   relation and in the static system, then the fundamental theorem.
4. Stage D. Examples from the literature, each with a closed deadlock_free
   proof, or a precise reason why it falls outside.
   - sendTree and recvTree (Thiemann and Vasconcelos 2016, pp. 2–3).
   - The binary tree channel with polymorphism per node, the stream of
     Listing 1.1, the classic deadlock scenario (rejected), and Milner's
     scheduler A.5 (Mordido and Pérez 2026, pp. 3–5, 37–38).
   - Further CFST examples from the papers store ([EXAMPLE] facts) and from
     FreeST, for instance an arithmetic expression server.
   - A tree server that recurses on both subtrees.

Stages A and B cost the most. Each stage ends with a full build, closed Print
Assumptions and a report.

## Stage D results (2026-10-31)

Every target example types or is rejected as the literature expects, with
the core unchanged. The files are in theories/examples/cfst/, and SHARP-EDGES
74 has the details.

| Example | Source | Result | File |
|---|---|---|---|
| recvTree as drain, the tree channel with one point per node | Thiemann and Vasconcelos pp. 2–3, Mordido and Pérez p. 5 | typed | TreeCopy.v |
| recvTree then sendTree as copy, polymorphic recursion in both continuations | Thiemann and Vasconcelos pp. 2–3 | typed | TreeCopy.v |
| two streams in a cycle | Mordido and Pérez Listings 1.1, 1.2 | typed | Stream.v |
| the classic deadlock | Mordido and Pérez p. 3 | rejected, no strict world types it | CfstDeadlock.v |
| its repair, one thread sends first | Mordido and Pérez p. 3 | typed | CfstDeadlock.v |
| Milner's scheduler, k = 3 | Mordido and Pérez A.5 | typed | CfstScheduler.v |
| treeSum serving transform on Node 3 Leaf (Node 4 Leaf Leaf) | Thiemann and Vasconcelos Listing 2 | typed | TreeSum.v |
| the arithmetic server with the client Add (Const 5) (Mult (Const 7) (Const 9)) | Thiemann and Vasconcelos Listing 3 | typed | ArithServer.v |

Simplifications. The calculus keeps no recursive data types and no
integers. Int and () become ∗. A tree travels on a channel or comes from
the program's own selections, so drain and copy stand in for recvTree and
sendTree on tree values, and the main program sends the fixed tree
Node(Leaf, Leaf). A unary choice becomes a send of ∗ and its branch a
receive, which K4 treats alike. Both semantics are synchronous (Mordido and
Pérez, Fig. 15, p. 30). Only the scheduler of van den Heuvel and Pérez that A.5
starts from is asynchronous.

Findings.
- The coarse ceiling of K8 suffices for every example. copy acts on two
  channels inside the segment, but both advance by the size of the tree, so
  its zigzag κ+k ≺ ι+k ≺ κ+k+1 is stable under the shift and needs no fact
  that depends on data. The case sendTree t c; close d; send v c stays
  outside, as K8 says.
- Existential points need one open and one pack per recursive call whose
  result is passed on, because the lower point of the result is the point of
  the call. copy and drain wrap the second call in λr. r for this.
- The scheduler needs the parity of the instant. Its follower admits no
  rank linear in the instant, and the closed program gets the rank
  9⌊k/2⌋ + b(X, k mod 2).
- The classic deadlock is rejected through soundness. The program reaches a
  state where both threads wait on a receive, so it is not deadlock free and
  no strict world types it. No inversion of derivations is needed.
- A reply after the subtrees needs no new fact. treeSum opens the result of
  its right call at κ″, sends, and packs at κ with the witness κ″+1, under
  the coarse ceiling. The arithmetic server is drain with two branches in
  place of a branch and a receive. Both return the channel without the
  integer, and Int becomes ∗ (SHARP-EDGES 75).

## Ported to the exists core (2026-11-04)

Branch `cfst` now runs on the core of branch `exists` (merge commit
b88b23b), with the context-free additions on top. The source judgment
`styped`, `soundness_source`, existential points with a lower bound,
creation constraints and the empty world come from `exists`. Session
syntax K1, head normal forms and bisimilarity K3, choice K4, boxes over
session variables K6 and the coarse ceiling K8 come from `cfst`. K10 gave
way to K11 and K7 to K12. `soundness`, `soundness_source`, `fundamental`
and `fundamental_proc` have closed `Print Assumptions`.

### What changed

- `ty` has `TBox n k C T` with k session variables and `TEx lb n C T` with
  `lb : lbound`. `ty_ind_ex` gives the body of ∃ at every instance and the
  body of □ directly, as K13 needs.
- `konst_ty` has ten signatures. KTNew is gone, KTNewEx is the existential
  new, and KTSel1, KTSel2 and KTBra owe x ≺ x[i] (K11).
- Program order `ppo` moved to types/Types.v, and `ple p v` reads
  p = v ∨ ppo p v. Betweenness for a fresh channel compares points along
  program order.
- The rules E-Pack and E-Open are those of `exists` in rules/ExRules.v.
  `Erel_Vsub` there has the cases of the choice labels.
- `styped` has `st_box` over session instances and `hsteq` compares boxes
  by ≈ on the nose, as `steq` does.
- Every example of examples/cfst/ states a whole-program `styped`
  derivation, creates its channels with `let_new_pair` under a creation
  constraint, and proves deadlock freedom with `soundness_source` or with
  `soundness (Wpo [])` and `ptyped_closed_s`. A ceiling that no channel
  occupies is the top-level variable of C₀ = ∅.
- PGV and Padovani–Novara build again. Their translations write S;S for
  send and receive, and their simulations gained the choice labels and the
  choice communication. No statement changed.

### What broke and how it was fixed

- Creation.v, written for program order of one name, had to accept the
  laws of K10 during the merge. K11 removed them again, and the file is the
  one of `exists` with two lemmas `ppo_pofs` and `pofs_ppo` that move between
  `ppo` and offsets of one name.
- The ⊥ flag reached cfst's tools. `tv_case` asks the flag of the shared
  context to be off, and the frames of the examples are `Some (FVar φ)`.
- Conservativity makes an earlier channel state facts in advance. In
  BranchOrder.v the constraint of d derives c[1] ≺ c[0], so c is created
  with {ι ≺ ι[0], ι ≺ ι[1], ι[1] ≺ ι[0]}. T2 still types under K11. In
  TreeCopy.v channel a states α·w ≺ (α·w)[i] along every walk w, because
  the zigzag of b derives these facts between points of a.
- The facts of the scheduler's world do not split into conservative
  creation constraints, because the constraint of C1 derives facts between
  A1 and A2 that no earlier constraint states. Each channel is created with
  a rank constraint that orders its instants against every instant of each
  earlier channel. It states more facts than the world did, and two
  instants of equal rank on different channels stay unrelated.
- Under K11 a branch owes κ ≺ κ[i], so the box constraints of drain,
  treeSum and receiveEval contain κ·w ≺ (κ·w)[i] along every walk. The
  zigzag of copy derives these facts, so its constraint did not change.
- A box typed under Ψ = [] has to type under the hypothesis of C₀.
  `typed_hyps_wk` in CfstTools.v does it with `typed_pinst` at the identity.
- The classic deadlock had to switch to `let_new_pair`. The old let on new
  does not type, because new returns an existential. `dl_untypable` now says
  that no `styped` derivation exists in the empty world, and
  `dl_untypable_source` says the same under every acyclic C₀.

SHARP-EDGES 137 to 141 have the details.

