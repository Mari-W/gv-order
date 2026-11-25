# Design check, the static rejection of the flag program

2026-11-21, branch redesign. Write-up only, no change to v2/. The program
and the rules are those of branch redesign-clean3 at 1cabad4
(.claude/worktrees/redesign-s4). Two statements were checked in a throwaway
Rocq file against the built v2 of that commit, and the file is deleted. Every
other argument is on paper. The last section lists which is which.

Notation. x is the point of c and y the point of d, as in
docs/redesign/semantic-example.md. `Tbad = ∃⁰. (y ≺ x̄). ∗` is an existential
with no bound point whose constraint states `y ≺ x̄` over two outer points
(`Tbad` and `Cbad` in v2/examples/SemBranch.v). Wa holds only `x ≺ ȳ`, Wb
holds only `x̄ ≺ y`.

## Verdicts

1. The variant whose arms read their binder is statically typable, as a
   closed process at the world `Wa ⊔ Wb`. Checked in Rocq, closed under the
   global context. The program as written is rejected, but its live arm
   already fails. Its binder has type ∗ in every derivation, ∗ is linear,
   and the arm never reads it. The claim of semantic-example.md therefore
   holds for the program as written, for a reason unrelated to the order,
   and fails for the variant.
2. Fixes.
   - (a) A consistency check at E-Open or E-Pack does not restore the
     rejection. `Wa` plus `y ≺ x̄` is strict. The cycle needs the partner's
     world, which the thread's derivation never sees.
   - (b) An inhabitation premise where existentials are introduced is
     vacuous. E-Pack already asks `hold_at`, and E-New's constraint is the
     laws of W. `Tbad` never passes through either rule. It enters as the
     free summand of E-Inj and as the argument type of a λ. A premise at
     every binder needs a context-dependent well-formedness judgment for
     every type, nested ones included.
   - (c) Conservativity at E-Open. E-Open asks that the opened context
     derive no new fact between points of the old context. The premise
     reads only `slt`. It restores the rejection of every variant, keeps
     every example typing with a one-line discharge, leaves the fundamental
     theorem as it is, and follows from (wf-new) and (wf-new⁺) of the layers
     design. Recommended.
3. Not needed if (c) is adopted. Without a rule change, the flag program
   with a box payload in place of ∗ is semantically typed and statically
   rejected by today's rules. Section 5 sketches the proof. It shows less
   than (c), because the rejection then rests on the binders being unread.

## 1. The variant

```
not      = λz. case z of inl w ⇒ inj₂ w | inr w ⇒ inj₁ w
thread′  = case not (inj₂ ∗) of inl w ⇒ let ∗ = w in close c; close d
                              | inr w ⇒ let ∗ = w in close d; close c
partner  = close c̄; close d̄
```

The derivation types `not` at `(Tbad ⊕ ∗) ⊸ (∗ ⊕ Tbad)`, with no upper and no
lower point. The argument `inj₂ ∗` has type `Tbad ⊕ ∗`, and E-Inj asks nothing
of the summand `Tbad`. The flag then has type `∗ ⊕ Tbad`. The live arm binds
w at ∗ and closes c while holding d, under `x ≺ ȳ` from Wa. The dead arm binds
w at `Tbad`, opens it with E-Open, which adds `y ≺ x̄` to Γ, consumes w by
`let ∗ = w` and closes d while holding c. `sb_dead_arm_typed` of SemBranch.v
is this dead arm. The partner types in Wb, and P-Connect joins at `Wa ⊔ Wb`,
which `Wab_strict` shows strict.

The probe proved the following, against the definitions of SemBranch.v.

```
Definition sbv_thread : expr :=
  Case sb_flag (LetU (Var 0) (cl2 oc od)) (LetU (Var 0) (cl2 od oc)).
Definition Tnot : ty :=
  TLolli UNone LNone None tinf (TSum Tbad TUnit) (TSum TUnit Tbad) None.

Lemma not_typed W Γ F : dftyped W ∅ Γ [] F sb_not Tnot.
Lemma flag_typed W Γ F : dftyped W ∅ Γ [] F sb_flag (TSum TUnit Tbad).
Lemma sbv_thread_typed : dftyped Wa Θa hc_empty [] (∅, None) sbv_thread TUnit.

Definition sbv_config : proc :=
  (({["c"]} ∪ {["d"]}), {[+ sbv_thread +]} ⊎ {[+ sb_partner +]}).
Theorem sbv_typed : ptyped None (Wa ⊔ Wb) ∅ sbv_config TUnit.
(* Print Assumptions sbv_typed: Closed under the global context *)
```

`sbv_typed` uses `p_connect_join` with `Wab_strict`, and `p_term` on each side
with no restricted channel.

The program as written. Its scrutinee is `not (inj₂ ∗)`, and the payload ∗
has type ∗ up to E-Sub and E-Pack. `tsub` relates `TUnit` only to itself
(`sub_unit`), and E-Pack can only wrap ∗ into an existential with body ∗. So
the live arm's binder has type ∗ or an existential over ∗, and neither is
unlimited (`unlimited` holds of boxes only). An entry that is not unlimited
must occur in the term (`typed_tfacts`, cost/Exact.v), and `close c; close d`
has no variable. The dead arm fails for the same reason. Both failures are
about linearity.

## 2. Where the argument of semantic-example.md breaks

The argument says that Γ is empty at P-Term, that E-Abs adds nothing, and
that only W1 can derive `y ≺ x̄`. Two rules add facts to Γ. E-Box adds its
constraint inside the box body, and E-Force pays for it with `hold_at` at the
caller. E-Open adds the constraint of an existential entry of Δ, and nothing
pays for it. The fundamental theorem is sound because a value of the
existential carries a witness in the semantic world. A dead arm and an
uncalled λ receive no value, so their binder types may state any fact.

## 3. The fixes

### (a) Consistency of the opened constraint

E-Open asks `strict (W ∪ facts of hc_open m C Γ)`, or E-Pack asks the same of
its constraint. For the variant this is `strict (Wa ∪ {y ≺ x̄})`. It holds.
Offsets never decrease along a step of the order, facts sit only at offset 0,
and the only facts are `x ≺ ȳ` and `y ≺ x̄`. From ȳ or x̄ every step leads to
offset 1 or more, so neither x nor y is reachable again, and there is no
cycle. The check therefore passes and the variant still types. A global
version at P-Connect would need the facts of every E-Open in the world, and
asking `W ⊢` of those facts is the premise of (c). E-Pack is irrelevant here,
because `Tbad` is never packed.

### (b) Inhabitation where existentials are introduced

Existentials are introduced by E-Pack and E-New. E-Pack asks
`hold_at W Γ C xs`, a witness, and E-New's constraint is `bcs_of (w_laws W ℓ)`,
which every generated root of ℓ satisfies by `ws_law`. Both already have
inhabited constraints. `Tbad` reaches the dead arm through the summand that
E-Inj leaves free and through the argument type of `not`. A premise that
catches it must sit at E-Inj, E-Abs, E-Case and E-LetP, and at every type
inside a payload, an arrow or a box. Its context differs per position. An
arrow argument is inhabited at the call, in the caller's context, not at the
λ. This is a well-formedness judgment for types with one context per
position, more machinery than the problem warrants. Not recommended.

### (c) Conservativity at E-Open (recommended)

```
cons W Γ m C  :=  ∀ x y, slt W (hc_open m C Γ) (pshift m x) (pshift m y)
                         → slt W Γ x y

  Δ(i) = ∃^lb ῑ_m. C. T    ¬ unlimited T    cons W Γ m C
  Θ↑ ; hc_open m C Γ ; Δ↑[i ↦ T] ⊢^{F↑}_{W,N} e : U↑ ▷ c ; ϑ
  ─────────────────────────────────────────────────────────── E-Open
  Θ ; Γ ; Δ ⊢^F_{W,N} e : U ▷ c ; ϑ
```

In words, opening adds facts about the new points and none between old
points. The premise reads `slt` only, so it is static. It is not a syntactic
clause in the relation, because the relation does not change.

Restores the rejection. Probe lemma `Tbad_not_cons : ¬ cons Wa hc_empty 0 Cbad`
holds in Rocq. Opening `Tbad` in Wa would derive `y ≺ x̄`, and
`Wa_not_yx : ¬ Wa ⊢ py ≺ px‾` holds by a rank argument (facts raise the
constant root, program order keeps it). For the general case one lemma
suffices.

```
opened_cons : opened Θ Γ Δ F Θ' Γ' Δ' F' →
  ∃ σ, Θ' = tenv_pinst σ Θ ∧ F' = sf_pinst σ F ∧
       ∀ x y, slt W Γ' (pt_inst σ x) (pt_inst σ y) → slt W Γ x y
```

σ is the composite shift of the steps, and the proof is an induction on
`opened` with `cons` at each step. From `Γ = hc_empty` it gives `W ⊢ x ≺ y`
for any fact the opened context derives between shifted outer points. The
dead arm's gate `y ≺ x̄` is such a fact whatever the arm opens. Section 4
uses this lemma.

Keeps the examples. Every E-Open in v2/examples opens an existential
`TEx _ 1 (bcs_of (w_laws W ℓ)) _` with `ℓ ∈ w_fams W`, from E-New or, in
FactoryEx and LFFactoryEx, from `Tres` over the same laws. There are 15
sites in Cycle, FactoryEx (2), FreshBetween, FreshMany, ClientServer,
GrowRing, LFCycle, LFFactoryEx (2), LFFreshBetween, LFFreshMany,
LFClientServer, LFController and LFGrowRing. Each discharges `cons` by two
lemmas.

```
cons_of_hold : world_wf W → length xs = m → hold_at W Γ C xs → cons W Γ m C
law_hold     : ℓ ∈ w_fams W → hold_at W Γ (bcs_of (w_laws W ℓ)) [pgen ℓ 0]
```

`law_hold` is one `ws_law` step. `cons_of_hold` instantiates the bound points
by xs (`plist xs` after the shift is the identity on outer points), maps a
derivation through `w_lt_pinst` (PointSubst.v) and replaces each hypothesis
of C by its `hold_at` derivation. TreeTopo, FlagPair and the semantic proofs
of SemBranch use no E-Open. `sb_dead_arm_typed` stops holding, and
`Tbad_not_cons` takes its place as the record of the mechanism.

Keeps the fundamental theorem. A new premise on a rule only removes
derivations. The E-Open case of Fundamental.v (line 557), cost/CostFund.v and
the occurrence lemma of cost/Exact.v consume derivations and ignore it. Only
two lemmas build an E-Open, the renaming lemma (Weakening.v line 533) and
`conservative` (Conservativity.v line 531). Both keep W, Γ, m and C, so the
premise passes through unchanged. `d_open` and `opened` gain the premise.
No lemma substitutes points into a whole derivation or weakens its Γ, so
stability of `cons` under those operations is not needed today. On paper it
holds under both, because every path between outer points that passes
through the bound points enters and leaves by facts of C, and conservativity
already covers that pair.

Under the layers design. E-New at a fresh root ρ asks (wf-new) of
check-layers.md, every fact between `tree(ρ)` and a context point goes from
the context point up. No path then leaves `tree(ρ)` towards the context, so
the opened constraint derives no fact between context points, and `cons`
holds. (wf-new⁺) of check-layers-open.md allows facts `u ≺ y` down to the
context for u in the set D, which is closed downwards. A path that enters
`tree(ρ)` at `z ≺ u₀` and leaves at `u ≺ y` stays below u, so it stays in D,
and the map h turns it into `Γ ⊢ z ≺ h(u₀) ≺ … ≺ h(u) ≺ y`. A field creation
asks `Γ ⊢ C`, which gives `cons` at once. So E-New's existentials satisfy the
premise by construction in both designs, and the soundness of entailment
(`ent_sound`) is untouched.

A witness premise in place of `cons`, E-Open asks `∃ xs, hold_at W Γ C xs`,
is simpler in today's Rocq and also restores the rejection. It breaks under
layers. The client-server constraint has `ι+k ≺ ζ` for every k, and the
context has no instance of it in general. Conservativity is the form that
survives the planned change.

## 4. The static rejection with (c), sketch

Claim. For every W, `¬ ptyped None W ∅ sbv_config TUnit`, and the same for
`sb_config`.

1. `ptyped_two` gives P-Connect over one thread on each side, worlds W1 and
   W2, a cut ΣC, and `strict (W1 ⊔ W2)` by `ptyped_strict`. The interface is
   ∅, so Σ1 and Σ2 are empty.
2. `ptyped_one` gives P-Term on each side. A thread mentions exactly the ends
   of its Θ (`typed_tfacts`). The thread mentions c⁺ and d⁺ only, the
   partner c⁻ and d⁻ only, so no side restricts a channel and ΣC holds the
   two ends of one side, at points x and y. By symmetry the thread is on the
   left, with c⁺ at x and d⁺ at y, and the partner holds c⁻ at x̄ and d⁻ at
   ȳ. The case with the thread on the right is the same with the roles of
   the worlds swapped.
3. Thread. `inv_case` at Γ = hc_empty, Δ = [] gives an opened context, which
   is the start itself because Δ has no entry. The scrutinee has no end, so
   by `typed_tfacts` its Θ1 is ∅ and the arms receive c at x and d at y
   (aging changes credits, not points). The dead arm is typed under
   `Some T2 :: []`. `inv_letu` twice and `inv_close` reach
   `close d` in an opened context Γ' with future F' that contains the head
   x̄ of c (`tenv_heads`). An inversion lemma for E-Chan, `inv_chan`, still
   to write, places d at the shifted y. `ub_below_s` gives
   `slt W1 Γ' (σ y) (σ x̄)`, and `opened_cons` gives `W1 ⊢ y ≺ x̄`.
4. Partner. The same steps without a case give `W2 ⊢ x̄ ≺ y`. The partner has
   no binder, so its context is never opened.
5. `W1 ⊔ W2 ⊢ y ≺ x̄ ≺ y` contradicts `strict (W1 ⊔ W2)`.

Missing pieces in Rocq. `inv_chan` (E-Chan under E-Sub, E-Pack and E-Open,
with `tsub` keeping the point of a session type), `opened_cons`,
`cons_of_hold`, `law_hold`, and the bookkeeping of step 2 on `ptyped_two`.
The lemmas of Inversion.v cover E-Case, E-LetU, E-Close, P-Term and P-Connect
already.

## 5. Fallback without a rule change

```
b        = box ∗
thread″  = case not (inj₂ b) of inl _ ⇒ close c; close d
                              | inr _ ⇒ close d; close c
partner  = close c̄; close d̄
```

Semantic typing. Exactly `sb_thread_E`, with `b` for ∗. The three β steps
need `is_val b`, and the live arm is the same `cl2 oc od`.

Static rejection, by today's rules. The arms never read their binder, so by
`typed_tfacts` its type is unlimited, a box. E-Open opens only existential
entries, so it never opens the binder. A binder of existential type over a
box is not unlimited and cannot be opened (`¬ unlimited T`), so it is
excluded too. The thread's Δ is [] at P-Term, so no open ever happens at or
above the dead arm, and Γ there is hc_empty. The gate of `close d` gives
`W1 ⊢ y ≺ x̄` directly, and steps 1, 2, 4 and 5 of section 4 finish the
proof. `opened_cons` is not needed, only `inv_chan` and the bookkeeping.

This example carries less. The variant of section 1 still types, so the
example shows that the relation ignores an unread binder, which a reader
can dismiss as a technicality. With (c) the rejection holds for every arm
shape, and the running example can be the variant itself, written with the
pattern `inl ∗ ⇒`.

## What was checked

In Rocq, in a throwaway file `v2/examples/ZZProbeFlag.v` of redesign-s4,
compiled with `rocq c -R . GV` against the .vo files of 1cabad4 and deleted
afterwards. `not_typed`, `flag_typed`, `sbv_thread_typed`, `sbv_typed`
(closed under the global context), `cons_open` as defined in section 3,
`slt_empty_w`, `Wa_not_yx` and `Tbad_not_cons` (closed under the global
context). During the probe the active run of that worktree rewrote the
file's `TLolli` to the new signature without the ticket argument. The probe
was restored and checked against the old .vo files, so these results speak
for 1cabad4, not for the ticket redesign in progress.

On paper. That the original program fails by linearity (section 1), the
strictness of `Wa ∪ {y ≺ x̄}` in (a), the analysis of (b), `opened_cons`,
`cons_of_hold`, `law_hold`, the count of 15 E-Open sites (grep), the
pass-through of the two constructing lemmas (read, not compiled), the
stability of `cons` under substitution and weakening, the layers argument,
the rejection sketch of section 4 and the whole of section 5.
