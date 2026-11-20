# A thread that branches on its own flag (semantic typing only)

File: `v2/examples/SemBranch.v`, logical names under `GV.examples.SemBranch`.
Idea and shape from `theories/examples/SemFlag.v` of the old library. Nothing
else is reused from there.

## The program

```
not      = λz. case z of inl w ⇒ inj₂ w | inr w ⇒ inj₁ w
thread   = case not (inj₂ ()) of inl _ ⇒ let () = close c in close d
                               | inr _ ⇒ let () = close d in close c
partner  = let () = close c̄ in close d̄
```

The process is `({c, d}, {thread, partner})`. The thread holds the ends c at x
and d at y. The partner holds c̄ at x̄ and d̄ at ȳ. The points are the constants
x = (0, +, 0) and y = (1, +, 0). The flag always evaluates to `inj₁ ()`, so the
thread takes the first arm and closes c first. The second arm never runs.

The gates of the three closes are:

| close | holds | gate |
|---|---|---|
| first arm, `close c` | d at y | x ≺ ȳ |
| second arm, `close d` (dead) | c at x | y ≺ x̄ |
| partner, `close c̄` | d̄ at ȳ | x̄ ≺ y |

The process is deadlock free. The live arm and the partner agree on the
order x ≺ ȳ and x̄ ≺ y, which is acyclic.

## What the theorems state

```
Theorem sb_thread_E n :
  Erel κ_DF n Wa (tenv_erase Θa) TUnit ∅ sb_thread.

Theorem sb_deadlock_free : deadlock_free sb_config.
```

`sb_thread_E` puts the thread in E at every level n, in the world `Wa` whose
only fact is x ≺ ȳ, over the environment c : Close@x, d : Close@y. `sb_config` is
`({c, d}, {[+ sb_thread +]} ⊎ {[+ sb_partner +]})`. `Print Assumptions` reports
both closed under the global context, and the file has no `Admitted`.

`sb_untypable` is not proved. The argument is in the last section.

## How the proof goes

1. `sb_thread_E`. Three deterministic β steps take the thread to the live arm.
   The lemma `Erel_det` wraps `Erel_beta` (compat/Redex.v) and the lemmas
   `det_beta_case`, `det_beta_app`, `det_beta_inr`, `det_beta_inl` supply the
   determinism side condition. The steps are the application of `not`, the
   inner case on `inj₂ ()`, and the outer case on `inj₁ ()`.
2. The live arm `cl2 oc od` is typed in `dftyped` (lemma `cl2_typed`, with
   `d_letu`, `d_close`, `d_chan` of static/Conservativity.v) in the world `Wa`.
   `typed_E` (static/FundamentalProc.v) and `fundamental` (static/Fundamental.v)
   turn the derivation into membership in E (lemma `typed_E_df`).
3. The partner is typed the same way in the world `Wb` whose only fact is
   x̄ ≺ y (lemma `partner_E`).
4. `sem_p_term` (compat/PTerm.v) makes each side a process. The side condition
   `sth` is `sth_a` and `sth_b`. The cut is ΣC = {c⁺ : (End, x), d⁺ : (End, y)}
   and the partner interface is `senv_dual ΣC`.
5. `sem_p_connect` (compat/ConnectP.v) composes the two at `Wa ⊔ Wb`. The side
   condition `conn` is `sb_conn`, from `senv_dual_cut` of FundamentalProc.v.
6. `adequacy` (relation/Adequacy.v) needs `strict (Wa ⊔ Wb)`. The lemma
   `strict_rank` proves it by a lexicographic order on (constant, offset). Every
   fact raises the constant from 0 to 1, and the steps x ↦ x⁺ and x ↦ x̄⁺ raise
   the offset. `Wa_strict` and `Wb_strict` follow by `strict_mono`.

The thread never mentions y ≺ x̄. No world in the proof holds it.

## What was hard

- The old proof ran the β steps on an open term and grounded it afterwards. The
  v2 thread is closed and holds channel constants, so the steps run on the
  closed term and the final step uses `typed_E` at the empty grounding.
- v2 has no `Wfacts` helper and no strictness lemma for small constant worlds.
  `strict_rank` fills this gap and is the only new world lemma.
- `;` is a term token under the typing notations, so a set literal `{[a; b]}`
  does not parse in this file. It is written as a union of singletons.
- `sem_p_connect` takes the two sides over `Σ1 ∪ ΣC` and `Σ2 ∪ ΣD`. With
  Σ1 = Σ2 = ∅ the unions reduce by `left_id_L`, and `chans_ΣC` equates the
  restricted set of the composite with the two channel names.
- Building `Rocq` for this file from a cold tree rebuilds about 20 files.
  The file itself checks in a few seconds.

## Why the static system rejects it

A static derivation of `sb_config` ends in `p_connect` over the two threads.
The thread side contains the derivation of `sb_thread`. E-Case types both arms
under one Γ and one world W1. The dead arm `close d; close c` needs
y ≺ x̄ by E-Close at d's point, so `slt W1 Γ y x̄` holds. The hypotheses Γ are
empty at the top of P-Term and E-Abs adds none, so only the order of W1 can
derive it, and W1 ⊢ y ≺ x̄. The partner needs W2 ⊢ x̄ ≺ y. The side condition
of `p_connect` is `strict (W1 ⊔ W2)`, and the join holds both facts, a cycle.
The two orientations of the cut (thread holds c⁺ or c⁻) and the two orders of
the components give the same cycle.

This is an argument and not a Rocq proof. A proof needs inversion of `typed`
through E-Case, E-LetU, E-Close and E-Chan with the aging and splitting
premises, and through `p_connect` with its choice of cut. I did not attempt it.

The open term is another matter. In context c : Close@x, d : Close@y the thread
is semantically typed in any strict world with x ≺ ȳ, and the static system
types the dead arm only when it also has y ≺ x̄. The static rejection needs
the partner, which is why the closed process is the right statement.

## Proposed entry for the Examples tab

Title: Self-computed flag

Summary: A thread branches on a flag it computes itself, orders two channels
differently in the two arms, and is deadlock free because only one arm can run.

Explanation: The thread negates `inj₂ ()` and closes c then d on `inl`, or d
then c on `inr`. The flag is always `inj₁ ()`, so it closes c first. A partner
closes c̄ then d̄. E-Case types both arms under one world. The live arm asks
x ≺ ȳ, the dead arm asks y ≺ x̄, and the partner asks x̄ ≺ y, so the joint world
has a cycle and P-Connect rejects the process. The relation never reads the
dead arm. It runs three β steps, ends in the live arm, which the fundamental
theorem types under x ≺ ȳ, and composes with the partner under x̄ ≺ y. The two
worlds join without a cycle, so adequacy applies.

Code:

```
thread  = case (λz. case z of inl w ⇒ inj₂ w | inr w ⇒ inj₁ w) (inj₂ ()) of
            inl _ ⇒ let () = close c in close d
          | inr _ ⇒ let () = close d in close c
partner = let () = close c̄ in close d̄
```

Rocq names: `sb_thread`, `sb_partner`, `sb_config` (program), `sb_thread_E`
(thread in E), `sb_deadlock_free` (main theorem), `strict_rank`, `Wab_strict`
(worlds), `cl2_typed` (static arm), `Erel_det`, `det_beta_case` (β steps),
`sb_conn`, `sth_a`, `sth_b` (side conditions). All in `v2/examples/SemBranch.v`.
