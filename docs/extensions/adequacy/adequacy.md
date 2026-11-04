# D. Adequacy for related systems

Goal. Every program that a related deadlock-free system types is deadlock free
by our relation. The paper can then say that orders generalize priorities, trees
and acyclic worlds.

## Two routes

1. Translation into the static system. Map each source derivation to a
   derivation of spec §9 at a world built from the source annotations. Soundness
   then follows from ours.
2. Direct fundamental theorem. Interpret the source judgment in our relation and
   prove each source rule as a compatibility lemma. This is adequacy in the sense
   of the paper. It needs no detour through spec §9 and states the result in the
   source system's own terms.

The study on branch orders-old-backup (docs/DESIGN-pgv-fundamental.md) chose
route 2 for PGV. Route 1 is cheaper where spec §9 already has matching rules.

## Targets

Tier 1 are functional systems with a direct translation. Tier 2 reach us through
translations that already exist. Tier 3 need an extension of the core first.

| Tier | System | Calculus | Translation idea | Needs |
|---|---|---|---|---|
| 1 | GV♯ (the paper), GV (Lindley and Morris 2015) | GV, tree topology | trees give a world without cross facts | core |
| 1 | PGV (Kokke and Dardha 2021), its Linear Haskell embedding | GV with priorities | priority of an action becomes the rank of its instant | core |
| 1 | Padovani and Novara (FORTE 2015) | higher-order functional, linear channels with levels, effects | levels as ranks, polymorphic recursion as boxes | linear channels as one-shot sessions |
| 1 | Mordido and Pérez (2026) | GV with context-free sessions | priority sequences n₁ + k·n₂ as infinite constraints | B |
| 2 | CP (Wadler), HCP | classical linear logic processes | through the CP to GV translation of Lindley and Morris 2015 | tier 1 for GV |
| 2 | PCP (Dardha and Gay 2018) | CP with priorities and a cycle rule | through the PCP to PGV encoding of Kokke and Dardha, which preserves typing | tier 1 for PGV |
| 2 | Kobayashi (2006), class K | π with usages, obligation and capability levels | the pair of levels to ranks | encoding of π into GV |
| 2 | Padovani (CSL-LICS 2014) | linear π | priorities as ranks, shifting z ↦ z+n as box instances | encoding of π into GV |
| 2 | Vieira and Vasconcelos (2013) | binary sessions on π, events | their strict partial order on events is a world, their partial union is ⊔ | encoding of π into GV |
| 3 | APCP, CGV (van den Heuvel and Pérez 2021, 2022) | asynchronous, cyclic | APCP priorities as ranks | asynchronous communication |
| 3 | Balzer, Toninho and Pfenning (ESOP 2019) | shared sessions | their acyclic order on worlds as facts | shared channels |
| 3 | λ-lock++ (Jacobs and Balzer 2023) | locks with local lock orders | one world per lock group | locks |
| 3 | MPGV (Jacobs, Balzer and Krebbers 2022) | multiparty GV, no priorities | n-ary fork as a tree of binary channels | multiparty sessions |

## Using the comparison results

Two papers compare whole classes. Dardha and Pérez (2022) show that the
processes typable from classical linear logic, class L, are strictly included in
those of Kobayashi's system, class K. Jaramillo and Pérez (ECOOP 2025) relate HCP
to Padovani's asynchronous priority system. A translation of K into our system
therefore covers L through the first result, modulo the encoding of π into GV.
Kobayashi's obligation and capability levels are the strongest target among the
π systems.

## Outline for PGV

Status 2026-10-30. Route 1 is done in Rocq for the monotone fragment of
repaired PGV with link (theories/pgv/, `pgv_deadlock_free`). Step 1 uses
the protocol-point world, step 4 holds with that one world for every program.
pgv-adequacy.md §7 has the details.

Status 2026-10-30 for Padovani and Novara. Fragment v1 with repair R2 is done in
Rocq (theories/pn/, `pn_deadlock_free`), with fibo and the signal pipe.
padovani-novara.md §7 has the details and every discrepancy.

Status 2026-10-31 for Mordido and Pérez. Stage 1 is done on paper
(mordido-perez.md, mordido-perez-counterexamples.txt). Five closed programs type
and get stuck, each with a local repair, and one deadlock-free program types
there and not here (mordido-perez.md 9.5). Stage 2 is mechanized for fragment v1 in
theories/mp/ (mordido-perez.md 12 and 13). Every closed program of v1 with
repairs R1 to R6 translates to a deadlock-free program (`mp_deadlock_free`),
and the two streams go through the translation (`st_mp_deadlock_free`). A sixth
defect came up, a branching that ignores the channels it holds (R6).

1. Points from priorities. A PGV session type writes a priority o on every action,
   !^o T.S. The instant of that action gets rank o, and the world orders instants
   by rank. Every PGV side condition has to become a strict fact. Where PGV
   compares with ≤, the translation needs a tie-breaking rule.
2. Arrows. PGV writes T ⊸^{p,q} U with a lower bound p and an upper bound q on
   the effect. They map to the lower point ℓ and the upper point u of T ⊸^u_ℓ U.
3. Derivations. Translate each PGV rule into a derivation of spec §9 at the
   world of step 1. Fork in PGV is derived from new and spawn, as here.
4. Statement. If ⊢_PGV p, then ⊢_W p for the world W of its priorities, and W is
   strict.

## What the earlier PGV study found

The study on orders-old-backup designed route 2 on the channel-named priority
relation that the current design replaced. Its findings that carry over follow.

- PGV has no recursion and no recursive types, so its value relation is a
  structural recursion on the PGV type.
- The arrow bounds split cleanly. p is read off the closure, because T-Lam sets
  it to the minimum priority of the captured environment. q is quantified over
  frames, because PGV only uses it as "everything I do stays below what you still
  hold". This is exactly our lower point ℓ and our frame F.
- T-App is the hardest rule. It needs an expression relation with frames and a
  bind lemma for it. The current design has both (E with F, Erel_bind).
- Branching (T-CaseSum) causes no trouble under the direct route.

Its walls came from the old design. The current design should remove them, which
has to be checked.

- W-A. A carrier and the channel it delegates could not lie in one cut interface,
  because the old composition demanded injective priorities per region. Worlds
  now speak about points, nothing asks distinct instants to differ (spec §15),
  and P-Connect cuts any set of channels.
- W-B. A channel captured in a sent closure was invisible, because the old
  annotation map was blind under arrows. Arrows now carry ℓ and u, so a sent
  closure exposes its bounds through V-Abs.
- D6. Global distinctness of priorities. The study already showed it liftable by
  a normalization at the front end.

The study estimated 3850 lines on the old base. Its stages 1 and 2 (the layer and
the bind lemma) exist in the current core, which should cut the estimate roughly
in half. docs/LITERATURE.md on the same branch holds a rule-by-rule comparison of
PGV and a mapping plan for MPGV. Its PGV theorem numbers are off by one in
several places.

## Outline for GV♯

The tree topology of the paper induces an order in which no two components share
a cross fact. Each GV♯ derivation translates to one here, and the extrusion split
becomes an instance of P-Connect. This makes the order system a conservative
extension of the paper's.

## Open questions

- Padovani and Kobayashi type π-calculi. Subsumption there needs an encoding of
  processes into GV, and the result is weaker than a direct translation.
- PGV and Mordido and Pérez use numeric priorities with arithmetic on them. Our
  worlds are partial orders. Every assignment into ℕ gives a world. The converse
  fails for worlds. The tail-call world puts infinitely many instants below
  (z,0) and has no rank into ℕ (tc_deadlock_free uses a pair rank). Whether some
  program types here and not in PGV is a separate question.
- Whether the translations go in Rocq. PGV and GV♯ are small enough. The others
  stay on paper.
