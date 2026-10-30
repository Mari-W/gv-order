# Design review after sharp edges 1 to 61 (2026-10-30)

Historical. This review covered the order design as of sharp edges 61. Its items are resolved or superseded (sharp edges 62 to 67), and C2, one world per component, stays deferred. The current design is ORDERS-SPEC.md.

Status. The author approved every item of A and B on 2026-10-30, and agreed with
C. Slots stay, boxes keep both jobs, and one world per component stays deferred.

Each item says what it buys and what it costs. Group A changes no definition.
Group B changes definitions and means re-proving. Group C records root causes
we work around today without changing them.

## A. Clean-ups with no change of definition

A1. **SHARP-EDGES carries a dead middle.** Entries 18 to 36 are superseded by 37
and still take a third of the file. Move them into one "History of the
channel-named worlds" appendix with one paragraph each. Keep the numbers so that
references in commits stay valid.

A2. **ORDERS-SPEC reads as a diff.** It mixes `[changed]` tags, notes like
"before decision N", and rationale. Split it into the current design with no
history, and a rationale column that points to sharp-edge numbers. The lagda
then follows the current design one to one.

A3. **Two typing layers without names.** Static.v holds the finite system
`typed` and the infinitary `ityped`, which is the list of semantic rules in
derivation form. Rename `ityped` to `sem_rules` and move it next to
TermRules2.v. Then Static.v holds only the checker side and one lemma
(`typed_ityped`) that connects the two. About 100 lines of duplicated
`term_wf` proofs disappear once `ityped_term_wf` is read off `typed`.

A4. **Typing.v is the paper's Fig. 4 system.** Relation.v imports it for the
linear environments `lenv`. Move `lenv` and its splitting lemmas into their own
file and drop the paper judgment, if nothing else uses it. A grep confirms.
DropCounter.v goes into a `counterexamples/` directory next to future refuted
statements.

A5. **One move lemma instead of three in Junk.v.** Junk collapse, renaming and
fusion are three instances of `tenv_move` along a partial map that respects ≡.
Junk.v proves each at V, E and P. A single lemma over the move, with the three
as corollaries, would shrink the largest file (2690 lines) and makes the
argument one sentence in the paper.

A6. **The spec still speaks of G where the system uses W.** After 53, 57 and 58
the static system is indexed by the world and reads facts from W plus
hypotheses. G and W_G belong only to the decidability question. Say so in §9
and keep schemas in docs/DECIDABILITY.md.

## B. Changes of definition

B1. **One fact theory for everything that orders points.** Today five things
supply facts. The world W gives ground facts. C gives box hypotheses. Ψ
collects the enclosing boxes' C. Φ gives frame-variable hypotheses u ≺ φ. G
gives schemas. Static.v reads them through `slt W Ψ`, `ub_below_s` and
`ub_below_h`. Define one judgment Γ ⊢ x ≺ y over a context Γ of facts with point
and frame variables, closed under the world laws, with one substitution lemma.
The world is then the ground case, and force checks Γ[xs] ⊆ W. The step
invariance of 61 becomes Γ closed under the steps. This costs the static half of
Static.v (about 800 lines) and nothing in the semantic relation. It is the
change I would make first, because 54 to 61 each added another fact source.

B2. **The upper point lives only on arrows.** A box is a polymorphic thunk
whose only eliminator is force, and force has type ⊸^u. Write the box as
□(∀ιs. C. ∗ ⊸^u_⊤ T) and drop u from the box former. V-Box becomes V of a thunk
at every admissible instance, and 52 becomes a consequence of the arrow rule
instead of a separate design. Types, V-Box, KTForce and E-Exp change. The proofs
of 52 mostly carry over, because they already go through E-App.

B3. **Readiness and frames are one condition.** ready says offered heads lie
below the heads the thread holds and does not offer. frame says offered heads
lie below F. F is the set of heads the context holds. Define
ready_W(Θ ∣ F, t): every offered head lies below every head of Θ ∖ offered and
every point of F. E-Step then has one premise instead of two, and the bind lemma
(48) reads as moving heads from Θ₂ into F. Ready.v, E-Step and the lemmas that
split ready and frame change. P is untouched, because processes have no frame.

B4. **A cost function on labels.** Sharp edge 45 split each obligation into a
free clause and a costly clause, written out case by case (Esend_case,
Eclos_case, Elink_case and so on). Define cost(λ) ∈ {0, 1} once, with send,
close and link at 0, and state every obligation at index n − cost(λ). The
relation's text shrinks by half, and a future change of the cost model touches
one function. Relation.v changes, and the downstream proofs change by name only.

B5. **One measure for the inner inductions.** Inside one index level, P-Connect
inducts on the soup size (46), P-Term on the thread size (47) and Internalize on
the giving-step fixpoint. Define E and P by well-founded recursion on (n, size)
in lexicographic order, where size is the number of send, close and link redexes
outside λ plus |C ∪ dom Σ|. Every free step then lowers the size, and all three
proofs use the same induction. Relation.v changes. Connect, PTerm and
Internalize get simpler but must be redone. Do this only together with B4.

## C. Root causes we work around

C1. **Slots put message structure into point names.** A point p[b][i] says "the
i-th point carried at (p, b)". This is why delegation produces aliases between
shapes of different depth, which no decidability theorem covers, and why slot
nesting is unbounded in programs. The receiver needs a name before the channel
exists (sharp edge 5), and no alternative has come up that avoids this. I
recommend keeping slots and stating decidability for the classes the doc covers.

C2. **One world per component (sharp edge 4, deferred by the author).** It stays
the only known source of incompleteness for run-dependent orders.

C3. **Boxes are the only polymorphism and the only recursion.** Constraints (58),
steps (61) and the 59 fix all exist because one construct does both jobs. Making
recursion a separate construct with its own invariant, and boxes plain
polymorphic thunks, would split the design along the two jobs. It changes the
syntax, and the paper keeps □ with fix. I would not do it now.

## Recommended order

A1 to A6 first, because they cost little and change no statement. Then B1,
because the open work on 59 to 61 adds to the fact sources. B2 and B3 together
after that, if the paper presentation should be shorter. B4 and B5 only if the
relation is reworked anyway.
