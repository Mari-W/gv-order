# Design check, deciding session equivalence

2026-11-21, branch redesign. Write-up only, no change to v2/. I read the Rocq
on redesign-clean3 at bb04f3e, namely types/Types.v (syntax, `sinst`,
`unroll`, `unfoldS`, `hcontractive`, `eqT`, `eq_step`, `sequiv`) and the uses
of `hcontractive` and `sscoped` in static/Contexts.v and relation/Relation.v.
The literature is almeida2020deciding and costa2023system from the papers
store. The last section lists what was checked and what was not.

## Verdicts

1. Payload types in v2 can contain free session variables of an enclosing µ.
   Nothing forbids it. `sinst` substitutes into payloads, `unroll` is `sinst`,
   so unrolling `µα. !(…α…). S` puts the recursive type into the payload.
   `sscoped` and `pscoped` restrict point variables only, `hcontractive` never
   looks into a payload, and the typing rules check no session variable.
   The example GrowRing uses a µ variable in a payload,
   `Sch = µα. ?(1, α@ι₀). Close`. Variables bound by an enclosing box can
   occur in payloads as well.
2. So the simple argument (decide payloads first, then use their classes as
   labels in Almeida et al.) does not apply to v2 as it stands. With µ-bound
   variables in payloads the comparison of a payload can depend on the
   comparison it is part of, and payload depth is unbounded after unrolling.
3. The case is covered by Theorem 3 of costa2023system, decidability of type
   equivalence for Fωµ∗;. Its LTS has a transition from a message into its
   payload, its message constructor takes payloads of kind ∗, and v2 has only
   session recursion, which is of kind s. v2 maps into Fωµ∗; with every
   annotated constructor as a record with one label that carries the
   annotations.
4. The simple argument goes through under the restriction that no payload
   mentions a variable bound by a µ outside it. Then it reduces directly to
   Theorems 1, 3 and 4 of almeida2020deciding by induction on payload depth.
   GrowRing violates the restriction, so the paper should cite Costa et al.
5. Both results need two side conditions that v2 does not state yet. Every
   session type inside a payload must be contractive too, and the constraints
   of existentials and boxes need a syntax with decidable equality, because
   `bc_facts` is a `Prop` and `eqT` compares constraints by Leibniz equality.

## 1. Session variables in payloads

The syntax (types/Types.v) is

    T ::= Unit | T ⊸^{ub,lb,c,a} T | T ⊗ T | T ⊕ T | □^{n,k,C,ub,c} T
        | S@x^a;m | ∃^{lb} n. C. T
    S ::= ?(m, T) | !(m, T) | Close | µ.S | α | α‾ | Skip | S;S | S ⊕ S | S & S

with de Bruijn session variables. `□^{n,k,…}` binds k session variables
(`sinst_ty` lifts the substitution k times under `TBox`), µ binds one. The
substitution enters payloads,

    sinst σ (SRcv m T) = SRcv m (sinst_ty σ T)
    sinst_ty σ (TSess s x a mt) = TSess (sinst σ s) x a mt

and `unroll s = sinst (SMu s .: SVar) s`. So the term

    µα. !(0, α@x^a;m). Skip        SMu (SSeq (SSnd 0 (TSess (SVar 0) x a m)) SSkip)

is a session type of v2, and one unrolling gives `!(0, (µα. …)@x^a;m). Skip`.
It is point-scoped (`pscoped 0` asks only that x has no point variable), and
no rule of static/Typing.v rejects it. The only place that checks session
types is `sinsts` (static/Contexts.v), which asks `hcontractive` and
`sscoped` of the instances of box variables, and `sscoped` is about points.

Equivalence compares payloads with the same coinductive relation. In
`eq_step`, two receives compare `m = m′ ∧ eqT τ T U ∧ τ s′ r′`, and `eqT τ`
uses τ at every `TSess` inside the payload. Annotations compare by equality.
A box with session binders (`k > 0`) compares its body syntactically.

## 2. Why the simple argument needs a restriction

The simple argument computes the classes of the payloads of S and R first,
by induction on depth, and then runs Almeida et al. with each class as a
message label. This needs a fixed finite set of payloads whose comparison does
not refer to the outer comparison.

Both fail with µ-bound variables in payloads. Compare

    S = µα. !(0, α@x^a;m). Skip        R = µβ. !(0, β@x^a;m). Skip

After one step each, the payload pair is `(S@x^a;m, R@x^a;m)`, so the payload
question is the outer question itself. The payloads reached also change with
each unrolling, and their depth grows without bound. Here S ≈ R holds
coinductively, but no induction on depth reaches it.

## 3. The general case, by Costa et al.

costa2023system define type equivalence as bisimilarity over an LTS on types
(p. 16). The message constructor ♯ ∈ {?, !} has kind ∗ ⇒ s, so a payload is
any proper type, a session type included, and records and variants take
components of kind ∗ (Fig. 4, p. 9). The LTS sends `♯T;U` by ♯1 to the
payload T and by ♯2 to U (L-MsgSeq1, L-MsgSeq2, Fig. 9, p. 15). A recursion
variable of kind s may therefore occur in a payload, and the bisimulation runs
through it. Theorem 3 (p. 23) decides equivalence for Fωµ∗;, the types whose
recursion has kind t or s (p. 6), by translating each type into a simple
grammar (Lemma 5, p. 21) and deciding bisimilarity of simple grammars with the
algorithm of Almeida et al. or Burkart et al., in doubly exponential time.

The encoding of v2 into Fωµ∗;, written ⟦·⟧.

| v2 | Fωµ∗; |
|---|---|
| Skip, Close, S;S′ | Skip, End, ⟦S⟧;⟦S′⟧ |
| S ⊕ S′, S & S′ | ⊕{l: ⟦S⟧, r: ⟦S′⟧}, &{l: ⟦S⟧, r: ⟦S′⟧} |
| µ.S, α bound by µ | µ α:s. ⟦S⟧, α |
| α bound by a box, α‾ | a free variable α : s, Dual α |
| ?(m, T), !(m, T) | ?{ℓ_m : ⟦T⟧}, !{ℓ_m : ⟦T⟧} |
| Unit, T ⊗ U, T ⊕ U | Unit, {fst: ⟦T⟧, snd: ⟦U⟧}, ⟨inl: ⟦T⟧, inr: ⟦U⟧⟩ |
| T ⊸^{ub,lb,c,a} U | {ℓ_{ub,lb,c,a} : ⟦T⟧ → ⟦U⟧} |
| S@x^a;m | {ℓ_{x,a,m} : ⟦S⟧} |
| ∃^{lb} n. C. T | {ℓ_{lb,n,C} : ⟦T⟧} |
| □^{n,0,C,ub,c} U | {ℓ_{n,C,ub,c} : ⟦U⟧} |
| □^{n,k,C,ub,c} U, k > 0 | {ℓ_{□ n k C ub c U} : Unit}, the whole term in the label |

Each `eq_step` case matches one rule of Fig. 9. A receive matches L-MsgSeq1
and L-MsgSeq2, with m in the label of the record. `HVar a s′` matches
L-VarSeq1 with m = 0 type arguments. `HPlus` and `HWith` match L-ChoiceSeq and
L-ConstApp. `HEnd` matches L-EndSeq, and `hseq` makes Close absorb its
continuation as End does. `HSkip` matches the lone Skip, which has no
transition. An annotation compared by equality in `eqT` sits in a record
label, and L-ConstApp compares labels. A box with `k > 0` compares by syntax in
v2 and by its label here. v2 stores duals already pushed through (`dual`,
`sflip`), so `Dual` occurs only at variables, as in L-DualSeq1 and L-DualSeq2.
Both LTSs are deterministic for each label, so the limit of the approximants
`aeq n` is bisimilarity, although `aeq` counts a step per message and Fig. 9
also counts the record steps inside a payload.

v2 has no type-level λ and no application, and its recursion has kind s, so
⟦S⟧ lies in Fωµ∗;. Contractivity gives the normalisation that their type
formation asks in K-TApp (Theorem 2, p. 14).

## 4. The restricted case, by Almeida et al.

Restriction (closed payloads). No payload of S or R contains a free
occurrence of a session variable bound by a µ outside that payload. Variables
bound by an enclosing box may occur.

Under the restriction, unrolling changes a payload only by renumbering box
variables, because `unroll` substitutes for the µ variable alone. Name the box
variables (levels in place of indices), and the payloads reachable from S and
R are the finitely many payload subterms of S and R.

The argument, by induction on the payload depth d, the nesting of messages
inside payloads.

- Collect the payloads `(m, T)` of S and R. Their session types have depth
  below d. By induction ≈ is decidable on them, so `m = m′ ∧ eqT sequiv T U`
  is decidable, and it is an equivalence (`eqT_refl`, `eqT_sym`, `eqT_trans`).
  Annotations are compared by equality.
- Replace each message `♯(m, T)` by `♯B` with B the class of `(m, T)`, each
  box variable α and α‾ by a message `!B_α`, `!B_{α‾}` with fresh labels,
  Close by `µX. !B_end; X` with a fresh label, and ⊕, & by labelled choices
  with labels l and r. A free variable at the head of v2 is one step with a
  continuation (`HVar a s′`), as a message is. The loop for Close is unnormed,
  so it absorbs any continuation, as Close does, and only another Close
  encodes to a type bisimilar to it.
- The result lies in the language of almeida2020deciding,
  `skip | #B | ⋆{lᵢ : Tᵢ} | S;T | µX.T | X` (p. 41), where a message `#B` is one
  action label. Contractivity in v2 gives their formation premise ¬T✓ under
  µ. S ≈ R iff the two encodings are bisimilar, by coinduction
  (`sequiv_coind`) against their LTS.
- Decide that with `bisimT`. Theorem 1 (full abstraction into simple
  grammars) and Theorems 3 and 4 (soundness and completeness of the
  expansion-tree algorithm) give the decision (pp. 49 to 51).

The restriction fails for an example of v2. GrowRing and LFGrowRing use

    Sch = µα. ?(1, α@ι₀). Close        SMu (SSeq (SRcv 1 (TSess (SVar 0) (pvar 0) …)) SEnd)

a channel that receives a channel of its own type (examples/GrowRing.v,
examples/LFGrowRing.v). The other recursive types in v2/examples (`Sa`, `Sb`
of ClientServer) carry Unit. So the restricted argument does not cover the
examples, and the paper needs Costa et al.

## 5. The statement

As the paper would cite it.

> Proposition (decidability of ≈). Let S and R be session types in which
> every session type, including those inside payloads, is contractive, and
> whose points, credits and constraints come from a syntax with decidable
> equality. Then S ≈ R is decidable. The encoding ⟦·⟧ maps S and R into the
> fragment Fωµ∗; of Costa et al. [costa2023system], with S ≈ R iff
> ⟦S⟧ ∼ ⟦R⟧, and their Theorem 3 decides ⟦S⟧ ∼ ⟦R⟧ by reduction to
> bisimilarity of simple grammars, which the algorithm of Almeida et al.
> [almeida2020deciding] decides. If no payload mentions a variable of an
> enclosing µ, the reduction goes directly to Almeida et al., by induction on
> the nesting of payloads, with the classes of the payloads as message labels.

Contractivity of payloads matters. `hcontractive` follows the continuation of
a message and never enters its payload (`hc_step` on `HRcv _ _ s′` asks only
`τ s′`). A contractive type can carry a payload `(µα.α)@x^a;m`, whose `hd` is
`HStuck`, and then `eq_step` compares the stuck terms by syntax. The author's
decision that all session types are contractive should be stated for payloads
as well, for example by a predicate that recurses into payload types.

Decidable annotations matter. `eqT` asks `C = C′` for the constraints of
existentials and boxes, and `bcs` holds its facts as `fact → Prop`. An
algorithm needs constraints as finite syntax, or as names compared by
equality.

## What was checked and what was not

Checked.

- In the Rocq, that `sinst`, `sinst_ty` and `unroll` enter payloads, that
  `sscoped` and `pscoped` restrict points only, that `hcontractive` does not
  enter payloads, and that only `sinsts` checks session types.
- In costa2023system, the kinds of Fig. 4 (p. 9), the LTS of Fig. 9 (p. 15),
  the definition of equivalence (p. 16), Theorem 2 (p. 14), the construction
  and Lemma 5 (pp. 20 and 21), and Theorem 3 (p. 23).
- In almeida2020deciding, from the facts recorded in the store, the syntax
  with basic messages (p. 41), Theorems 1, 3 and 4 (pp. 49 to 51), and that
  higher-order session types are left as an extension (Section 6). I reread
  the syntax and the higher-order remark in the extracted text.
- On paper, the case-by-case match of `eq_step` with Fig. 9, and the
  restricted argument.

Not checked.

- Anything mechanized. Neither the encoding nor the restricted argument is
  in Rocq.
- That the approximants `aeq n` and bisimilarity coincide in v2 in detail. I
  argued it from determinism of both LTSs.
- That the labels carrying whole box terms (`k > 0`) stay finitely many along
  the construction of Lemma 5. They are subterms of finitely many unrollings,
  so I expect it, as for the syntactically identical types that Lemma 5
  reuses.
- The polymorphic system of almeida2022polymorphic, whose PDF is not in the
  store.
