# Design check, no future variables (entry 14b)

Overnight run of 2026-11-20, branch redesign-clean3. Write-up only, no Rocq
change.

## Verdict

The equivalence holds. `Γ ⊢ x ≺ φ` holds exactly when Γ has the hypothesis
`φ ↦ u` and `Γ ⊢ x ≼ u`. A future variable is never the source of a fact, so
no fact between two points passes through one. The future F can become "the
points X and everything above u", and Γ keeps only the constraint instances.

## The check

The fact theory is `fl W Γ` of static/Contexts.v. Its only rule with a
variable on the right is `fl_v`, which gives `u ≺ φ` from `hc_fv Γ !! φ =
Some (Some u)`. Transitivity passes through a point. Two lemmas, compiled
against redesign-clean3 in a scratch file and then deleted, state it.

```
Lemma fl_from_var W Γ φ b : ¬ fl W Γ (NV φ) b.
Lemma fl_to_var W Γ x φ :
  fl W Γ (NP x) (NV φ) ↔ ∃ u, hc_fv Γ !! φ = Some (Some u) ∧ sle W Γ x u.
```

The proofs are an induction on `fl` each, about ten lines in total. A variable
with the entry `φ ↦ None` (an arrow or box without upper point) has no fact
below it, so nothing may block under it.

The semantic reading `sf_den ρ B F` (compat/SemTyped.v) replaces φ by an
arbitrary finite set ρ φ, and the instance hypothesis `hsat` (static/
Fundamental.v) asks every point of ρ φ above u. Readiness asks `x ≺ y` for
every y of the future, and E is antitone in the future (`ready_t_future`). So
quantifying over every finite set above u asks the same as `x ≺ y` for every
y above u, which a singleton already forces.

## What changes if the author takes it

- The future of the static judgment becomes the pair of X and a rest, where
  the rest is absent, "above u", or "everything" (the old `φ ↦ None`).
  The ⊥ flag stays beside it.
- `ub_below_s` asks `sle W Γ x u` where it asked `fl W Γ (NP x) (NV φ)`.
- E-Abs and E-Box type the body under the rest "above ub" and leave Γ alone.
  `hc_fvar`, `hc_fv` and the side condition `φ ∉ dom (hc_fv Γ)` go.
- The relation's future, today a `gset point`, needs the rest "above u" as
  well, a finite set plus an optional upper point, or a predicate. Readiness
  reads it as `∀ y, u ≺ y → x ≺ y`.
- In static/Fundamental.v the second conjunct of `hsat` and the lemmas
  `den_fresh`, `hsat_fvar` go, and `sf_den` loses ρ.
