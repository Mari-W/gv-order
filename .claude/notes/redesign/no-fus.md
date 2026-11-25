# Removing fusion from P (branch no-fus), 2026-11-25

Status: done on branch no-fus-port. P has no fusion quantifier, the
closure is the theorem `Prel_gfuse`, and the whole build is green (section
"Downstream adaptation" at the end).

## The link case is not blocked

The renaming lemma for the new P (clauses of p at Σ, no fusion quantifier)
fails as a forward simulation only when the simulation is stated with one
function on ends. Two goals fail.

1. A thread runs `link(a1, a2)` with `ech a1 ∈ p.1` and a2 held by nobody
   (a2 ∉ dom Σ, ech a2 ∉ p.1). h may send a2 onto any end. If h a2 = h a1,
   the image step is a self link. After it the image holds h a1 where p'
   holds a2 (the former a1‾ occurrences) and h a1‾ where p' also holds a2
   (the former a2 occurrences). No function g' on the ends of p' gives the
   image as `emapE g' p'.2`.
2. If h a2 = h(d±) for a restricted d ≠ ech a1, the image can also take the
   step `PickLink (h a2) (h a1)`, which removes the channel h d. p has no
   step that removes d.

Both close once the simulation relates occurrences, not names.

- Relation. q is related to p under h when q.1 = gch h p.1 ∪ D and the
  threads of q are those of p with every occurrence of an end o replaced by
  h o if o is held, and by an arbitrary end otherwise (an inductive
  structural relation on terms, lifted to multisets). Goal 1 disappears,
  because the two kinds of a2 occurrences may have different images.
- Goal 2 is simulated by the same step of p, `PickLink a1 a2`, with a new
  map h' = h except h' d⁺ = h a1‾ and h' d⁻ = h a1. The channel of a1 is gone
  from p', which frees its image name. h' commutes with duality, stays
  injective on the held ends of p', creates no dual pair, and gch h'
  (p.1 ∖ {ech a1}) = gch h p.1 ∖ {gch h d}. This needs p.1 ## chans Σ, so that
  kren h' Σ = kren h Σ. P does not force that, so it becomes a premise. It is
  preserved by every step and holds at every use (conn gives it).
- Every other action of p on an unheld end is an offer, because unheld means
  ech ∉ p.1. Its obligation reads Σ !! o and gives False. So unheld ends never
  act, except as the second end of a τ link, which the two cases above cover.

## What a fusion-free P still needs: internalizing

P-Connect needs a fusion with D ≠ ∅ in one case. A component links two cut
ends o1, o2. The other component then holds o2 and o2‾ (o1‾ became o2 by
csub o1 o2), and the channel of o2 must become restricted in it
(`fuse_ok_csub_cut`, compat/ConnectLink.v). This is a join of two interface
ends of different channels, not only an existing pair.

As a theorem this requires a single-process version of the cross
synchronization of P-Connect. A τ message on a D channel in the fused process
is two offers of p, a send (q_send, cost κ(give)) and then a receive of the
result (q_recv, cost κ(take)). The sum is positive, so the result lands below
the level and the outer level induction applies. Close and choice are the same.
P-Stop and P-Ready of the fused process need the descent argument of
`comp_ready` and `finite_lt_acc`: an offer on a D end whose partner does not
offer has, by above_offered, an offer strictly below the partner's point, and
the chain stops in a finite environment. Two facts restrict the theorem.

- tfree T when D ≠ ∅. Without fusion in the definition P contains a process
  whose final value carries both ends of a channel. Restricting that channel
  breaks P-Stop. The current P excludes this process only through the fusion
  clause. Every use of a D fusion (P-Connect) is at a primitive type.
- pfree Σ when D ≠ ∅. A τ message on a free channel keeps the interface, so a
  received end whose dual is in Σ would be restricted in p and not in the
  fused process. conn gives pfree for both components.

The clause transfer must also be closed under composition, because ConnectP
reads the induction hypothesis Φ1 at fusions of fusions (G1, G2 with csub on a
step result). The occurrence relation composes by relational composition,
which a representation with one name map would not.

## Proposed statement

```
Theorem Prel_gfuse κ n W Σ T p q h D :
  p ∈ P[κ]^W _ n⟦Σ ⊢ T⟧ → p.1 ## chans_of Σ →
  (D ≠ ∅ → tfree T ∧ pfree Σ) →
  gfuse h D Σ p q →            (* fuse_ok h D Σ p, q.1 = set_map (gch h) p.1 ∪ D,
                                  occurrence relation on threads *)
  q ∈ P[κ]^W _ n⟦sdrop D (kren h Σ) ⊢ T⟧.
```

D = ∅ with q = pmap h p is renaming, h = id is internalizing, and h = csub o1 o2
with D = {ech o2} is the P-Connect case. The proof is a well-founded induction
on the level with a Pind induction inside, through a clause-level transfer
lemma with separate source and target predicates.

## Plan and size

1. Occurrence relation on terms and soups: values, substitution, `act`,
   continuation of a step, re-indexing of soups (about 400 lines).
2. Clause transfer and Prel_gfuse: one case per image event, a backward
   value pull for Q-Recv (reuses `pull_value`), the send split with D ends
   in the payload, self synchronizations, P-Stop and P-Ready (about 2000 to
   2500 lines). The old development needed ChannelRenaming, JunkRenaming and
   Internalize, about 5200 lines, for the same content.
3. Relation.v: drop the quantifier. Pbody_id, Prel_conv, PTerm (sth_fuse
   goes), LiveDF, Closure and Adequacy shrink.
4. ConnectP: the composite needs its clauses at Σ only, so ConnectFuse.v
   goes. Φfuse ranges over gfuse, and Prel_ind_fuse and Pbody_fuse become
   theorems through the transfer lemma. cctx keeps its fields, with HP1 and
   HP2 given by Prel_gfuse from conn.
5. FuelE keeps its kinj quantifier.

## Implementation state, 2026-11-25 (after the go)

P has no fusion quantifier (relation/Relation.v, `Pbody` reads the clauses
at Σ and p in every later world). The closure theorem is proved and closed
under the global context.

```
Prel_gfuse : p ∈ P[κ]^W _ n⟦Σ ⊢ T⟧ → fside D Σ T p → gfuse h D Σ p q →
             q ∈ P[κ]^W _ n⟦sdrop D (kren h Σ) ⊢ T⟧
fside D Σ T p   := p.1 ## chans_of Σ ∧ tfree T ∧ pfree Σ
gfuse h D Σ p q := fuse_ok h D Σ p ∧ q.1 = set_map (gch h) p.1 ∪ D ∧
                   mcrel (hrel h Σ p.1) p.2 q.2
```

`mcrel` (compat/Occ.v) relates threads occurrence by occurrence. An
occurrence of an end o stands opposite h o when o or its dual end is held
(the dual matters because a map that commutes with duality fixes it), and
opposite any end otherwise. Instances: `Prel_fuse` (pfuse), `Prel_rename`
(pmap, D = ∅). `Prel_ind_fuse`, `Pbody_gfuse`, `Φfuse` (all in
compat/Fusion.v) are the induction principle P-Connect uses.

Premises. tfree T and pfree Σ are now asked always, not only for D ≠ ∅. A
received end whose dual end q holds becomes a channel of D on the side of
p, so D grows from ∅ during the simulation. Every use of fusion is inside
P-Connect, at a primitive type and at pfree interfaces, so no theorem
loses generality. A consequence: internalizing an existing pair (u and ū
both in Σ, h = id) is no instance, because Σ must be free of pairs.
Joining two ends of different channels is an instance, and that is what
P-Connect needs (`fuse_ok_csub_cut`).

The proof (Fusion.v 3000 lines, Occ.v 265 lines). Strong induction on the
level, Pind induction inside, through `clauses_q`, the clauses of q from
those of p.

- τ steps of q: `tau_beta`, `tau_new`, `tau_spawn`; links by `tau_link_p`
  (map csub y1 y2 ∘ h, which also covers the link onto a restricted channel
  that p performs with an end nobody holds) and `tau_link_off` (a link on a
  channel of D that p offers, D shrinks or moves); messages, closes and
  choices on held channels; the self synchronizations on a channel of D
  (`self_msg`, `self_close`, `self_choice`): an offer of p and then the
  dual offer of its successor at level j + κ(take). The sync costs
  κ(give) + κ(take) > 0, so the result lies below n and the outer
  induction applies.
- offers of q: `off_send` (ends of D in the payload are extruded, their
  partners join the interface), `off_recv` (the value is pulled back by
  `pull_value`, which now also exports freshness and closure under duals;
  received ends whose dual q holds become channels of D), `off_close`,
  `off_sel`, `off_bra`, `off_link`.
- P-Stop and P-Ready: τ steps and offers of p are steps of q (`fwd_tau`,
  `fwd_off`, `fwd_link`); offers on the two ends of a channel of D meet
  (`fwd_sync`, by `hd_ok_sync`); `chain` descends along `above_offered` to
  an offered end outside D, which stops on the finite set of points.

## Downstream adaptation, 2026-11-25 (branch no-fus-port)

The branch builds. No admit and no axiom are left.

- cctx (compat/ConnectCtx.v). `G1W0` and `G2W0` take the renaming form,
  `fuse_ok h ∅` with `sdrop ∅` and `pfuse h ∅`. All 12 call sites passed
  D = ∅ and only drop that argument. The fusion `h1 D1` of the other
  component in `G2W0` stays general, because ConnectLink passes
  `{[ech o2]}` there. `HP1` and `HP2` stay general and follow from
  `Prel_fuse`.
- Side conditions. `conn_fside1` and `conn_fside2` read fside of a
  component from conn. `ren_fside1` and `ren_fside2` read fside of the
  source of a renaming from conn of the renamed composite (`pfree_kren`
  reflects pfree through h). `fside_sub` passes fside to a smaller
  interface. `conn_conv` reads conn up to ≈.
- ConnectP. The composite's own fusion is gone, `step` gives the clauses
  of the composite at Σ1 ∪ Σ2 by `pc_clauses` over the original cut.
  `ind1` and `ind2` use `Prel_ind_fuse`. Φ1 and Φ2 keep the equation on
  the interface, and `Φ1_conv`, `Φ2_conv` show them closed under ≈ by
  `senv_eqv_split`, `conn_conv` and `Prel_conv`.
- ConnectLink. The six renamings take fside from conn, the two in
  `ren_comp1` and `ren_comp2` from the conn of the stepped component and
  the four in the link cases from the conn of the cut through
  `fside_sub`.
- ConnectFuse.v and PTerm's section `fuse` (`sth_fuse`, `fs_res`,
  `pfuse_single`) are deleted. `node_gen` calls `core` at Θ and e
  themselves.
- `Pclauses_id_fuse` (relation/Relation.v) is now unused. It stays,
  because deleting it recompiles Fusion.v.

Statements. No theorem of the soundness chain changed. `Prel_fuse` and
`Prel_rename` gained the premise `fside`. Both are used only inside
P-Connect (ConnectP.v, ConnectLink.v), where conn gives it.

Map. The author's no-fus-map.py applied. The captions of the relations
section and of p-rel now say renaming keeps processes safe and name the
side conditions of `Prel_gfuse`. check.sh has 0 errors, the page test
passes 15 of 15.

Lines: Relation.v −42/+29 (net), Occ.v +265, Fusion.v +3000, small edits in
Rename.v, Conv.v, Connect.v, LiveDF.v, Closure.v, PTerm.v.
