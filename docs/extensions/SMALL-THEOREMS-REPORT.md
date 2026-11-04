# Three small theorems, report

Branch `claude/small-theorems-3rew5v`, started from `main` at b621661. The
head is the commit that adds this report. Four new Rocq files, all registered in
_CoqProject. No existing Rocq file changed, and no statement of an existing
theorem changed. Docs changed by targeted edits in
docs/extensions/choice-encoding.md, and docs/extensions/existential-payloads.md
is new.

Every theorem below was checked with `Print Assumptions`, and each answered
"Closed under the global context".

## 1. Primitive choice translates into the encoding

theories/examples/ChoiceTranslate.v and theories/examples/ChoiceTranslateEx.v.

The translation of types `tr_ty`/`tr_sty` replaces ⊕(S₁, S₂) by Sch S₁ S₂ and
&(T₁, T₂) by Sbr T₁ T₂ of ChoiceEnc.v. The translation of terms `tr_e` replaces
select₁, select₂ and branch by closed λ-terms.

```
selᵢ = λc. let (k, k′) = new ∗ at x[i] in
           let (c, ()) = ⟨send ⟨injᵢ k′, c⟩, ∗⟩ in
           let () = spawn (λu. let () = u in close c) in k
bra  = λc. let (p, c) = recv c in let () = spawn (λu. let () = u in close c) in p
```

| Theorem | Statement |
|---|---|
| `tr_dual` | tr (dual S) = dual (tr S) |
| `tr_pinst` | tr commutes with point instantiation |
| `selE_typed` | selᵢ : Sch S₁ S₂@x ⊸^x Sᵢ@x[i] if x known, x ≺ x[0], x ≺ x[1] (in `typed`, any strict world) |
| `braE_typed` | bra : Sbr T₁ T₂@x ⊸^x T₁@x[0] + T₂@x[1], no fact |
| `fstyped_styped` | the fragment `fstyped` lies in `styped` |
| `choice_translate` | fstyped Φ Ψ Δ F e T → styped Φ Ψ (tr Δ) F (tr e) (tr T) |
| `choice_translate_df` | creation_ok C₀, prim T and fstyped ∅ [(C₀, ιs)] [] (∅, None) t T give deadlock freedom of tr t |
| `tr_breaks_seq` | ⊕(Skip, Skip);!∗.Close ≈ ⊕(Skip;!∗.Close, Skip;!∗.Close), and their translations are not ≈ |
| `native_fstyped` | T1 ∥ T2 ∥ T3 written with select₁ and branch lies in the fragment under {a ≺ a[1], a[1] ≺ δ, δ ≺ a[0], δ ≺ a[1]+1} |
| `native_deadlock_free` | that program is deadlock free |
| `translated_deadlock_free` | its translation is deadlock free under the same constraint |

The fragment is `styped` with three restrictions.
- E-Conv compares session types syntactically and points by ≡ (`hsteq0`).
  `tr_breaks_seq` shows that the translation does not preserve ≈.
- □ and force bind no session variable. A box is typed at every instance of its
  session variables, and most instances are no translation of a source type.
- selectᵢ at x asks x known and both x ≺ x[0] and x ≺ x[1]. The native constant
  asks x ≺ x[i] only. selᵢ creates k at x[i], which needs x known, and its send
  carries a sum whose heads are x[0] and x[1].

Every other rule is in the fragment, among them E-Open, E-Pack, E-Weak,
E-Contract, new with any creation constraint, and boxes without session
variables. The translation keeps Ψ, so the translated creation constraint is the
source constraint. For a native derivation whose selects have only x ≺ x[i],
the constraint has to state x ≺ x[1-i] as well before the fragment applies. I
did not prove that a native derivation transfers to the larger constraint.

## 2. The negative control is underivable

theories/examples/ChoiceNegative.v.

| Theorem | Statement |
|---|---|
| `sd_of` | in a plain context every derivation ends in a syntax-directed rule followed by E-Conv and E-Pack |
| `t2_underivable` | ¬ styped Φ Ψ Δ F T2 T for every Ψ with irreflexive hlt and every plain Δ whose binding 2, if present, is (dual Sch₀)@a |
| `body0_underivable` | the same for spawn T1, spawn T3 and T2 |
| `body0_underivable_top` | the same with Ψ = [(C₀, ιs)] for every C₀ that `c0_acyclic` accepts |
| `c0_irrefl` | c0_acyclic C₀ makes hlt [(C₀, ιs)] irreflexive |
| `negative_new_at` | with Sch₀ in place of Sch, the premise of `t_new_at` at a and δ (the route of `choice_typed`) has no derivation under any acyclic C₀ |
| `t2i_underivable`, `bodyg_underivable` | the same results for c′ at any variable i and any spawned thunks |

Plain means that no binding is unlimited or existential, so E-Weak, E-Contract
and E-Open cannot fire. The proof inverts the receive on c′, reads the payload
type of Sch₀ off the session equivalence (both arms at x[0]), inverts the case,
and reads δ ≺ x[0] from the first arm and x[0] ≺ δ from the second off the upper
point of each application and the heads of its future, up to ≡.

## 3. Existential payloads are a derived form

theories/examples/ExPayload.v and docs/extensions/existential-payloads.md.

| Theorem | Statement |
|---|---|
| `ex_rank_ok` | the top-level constraint {a+1 ≺ a[0]} is acyclic |
| `ex_typed` | styped of the server and client program under it |
| `ex_deadlock_free` | the program is deadlock free, by `soundness_source` |

The server creates k₁ at a[0] and k₂ at a fresh v with {a[0] ≺ v}, and sends
⟨k₁′, pack k₂′⟩ with the payload ∃κ₀. Close@κ₀ ⊗ ∃^{κ₀} ι. {κ₀ ≺ ι}. (!∗.Close)@ι.
The client opens the existential and uses the opened fact a[0] ≺ v′ to close k₁′
while it holds k₂′. The doc gives the derived rules Send-∃ (E-Pack plus the send
signature, asking x ≺ ℓ) and Recv-∃ (the receive signature, E-LetPair and
E-Open). The answer is a derived form. The boundary is the type language. A payload
type mentions only payload binders, so no message carries a fact about the
carrier point or about channels outside the message, derived or primitive.

## Build

A clean `make -j4` of the branch in a fresh checkout is running. This section is
filled in when it ends.

## Not done

- The negative control is stated after the two news. The closed term of the
  negative control is the term of `choice_main`, which `choice_typed` types with
  Sch, so no statement about the closed term can express it. The type Sch₀
  enters at the instance of new. `negative_new_at` covers the route through
  `t_new_at`, which keeps the top-level hypothesis. A derivation that opens the
  existential of a new elsewhere in the term is not covered, because E-Open may
  sit anywhere in the derivation and the context then holds an existential
  binding, which the inversion excludes.
- The translation covers the fragment above. Recursive session types that need
  E-Conv up to unfolding, and boxes with session variables, are outside. The
  recursive server of choice-encoding.md is outside.
- The derived rules Send-∃ and Recv-∃ are written in the doc and used in the
  example. They are not stated as general Rocq lemmas.
