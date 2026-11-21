# Design check, links without tickets (Phase A1)

2026-11-21, branch redesign. Write-up only, no Rocq change. The argument is
on paper and was not checked in Rocq.

## Verdict

The candidate fails as stated. Carrying `min(k(o2‾), k(o1) − 1)` onto the new
partner lowers a counter that another thread owns, and no premise of E-Link
can pay for it. The nearest alternative holds. It lowers no counter at all.
Each end type carries a cap, an upper bound on the counter of the end, and a
bound on the cap of its partner. E-Link asks the credit of each linked end to
exceed the partner bound of the other linked end. Then the new partner of a
waiting end already has a counter below the counter of the old partner, the
measure drops at every link, and tickets, `ϑ`, `tlink`, `tspawn`, `tseq`, `tok`,
the reserve r and the ticket premise of P-Term all go. Spawn needs no split.
Relink is rejected, every lock-free example keeps its typing, and the other
three programs of rejects.js are rejected by the same premises as today. The
caps are a creation choice, so they inherit the open question of entry 2 (risk
(a)) and are settled by whatever settles it (families today, χ or the
existential property of check-transfinite.md later).

## The setting

- A link of thread L on `{o1, o2}` with pick `PickLink o1 o2` removes the
  channel of o1 and renames `o1‾` to o2 (`csub`, lang/Syntax.v). In K the entry
  of `o1‾` moves to the key o2 and keeps its holder, point and counter, and the
  entry of `o2‾` stays (`own_next`, soup/Soup.v). Write k1, k2 for the counters
  of o1, o2 (held by L), k1′ for `o1‾` (held by B) and k2′ for `o2‾` (held by
  H2).
- After the link B and H2 are partners. If B waits, its partner counter goes
  from k1 to k2′. If H2 waits, its partner counter goes from k2 to k1′.
- The measure of a pending thread t is today the pair (sum of tickets, counter
  of the partner end), ordered lexicographically (`fu`, soup/LFAdequacy.v). A
  link lowers the first component (`tk_next`). Without tickets the second
  component alone must drop at the link, so we need `k2′ < k1` and `k1′ < k2`.
- In rx-relink B is the thread of `close w′`, L and H2 are both `refresh`, and
  `o2‾ = c′` was created by `new` with counter N. Today k2′ = N each round.

## Why the candidate fails

The candidate sets the counter of `o2‾` to `min(k2′, k1 − 1)` and that of
`o1‾` to `min(k1′, k2 − 1)`. The measure then drops at every link. The lock-free process relation
must still hold after the link, and `sp_fuel` asks H2 to be in FuelE at its
counters in K (soup/State.v). FuelE is monotone upward in the counters and not
downward.

1. No premise of E-Link pays. Every counter is at most N (a new end and an
   acted end start at N, every other update lowers). Take H2 that has just
   acted on `o2‾`, so k2′ = N, and then performs N actions on other ends before
   it acts on `o2‾` again. F-Tick asks `k(o2‾) ≥ 1` before each of those N
   actions, so H2 is in FuelE at counter N and in no FuelE at N − 1. H2 is
   typable on its own at credit N. Let L link o1 with o2 right after H2's
   action. Whatever E-Link asks of L, k1 ≤ N, so the new counter of `o2‾` is at
   most N − 1, and H2's last action fails F-Tick. The program L ∥ B ∥ H2 is
   typable by P-Connect and the lock-free process relation fails at the state after the link. Asking
   credit of the linked ends cannot help, because they are L's ends, they vanish
   in the link, and their credit bounds k1 from below, not k2′ from above.
2. A carried bound that H2 does not see is unsound. Keep H2's counter and
   record `v(o2‾) = min(k2′, v(o1) − 1)` beside it, only for the measure. Then
   `v ≤ k` holds always, but v can reach 0 while L's real counter on its end is
   still N. L may link again, and v cannot drop below 0. rx-relink is typable in
   this variant (refresh keeps real counters N and N − 1), and it is not lock
   free.
3. Lantana makes the target consent. OBLS-OFFLOAD (`obl_move`) needs the
   children token `parP_kids p2` of the new parent beside one unit of the moved
   obligation's fuel (lantana2027, lantana/program_logic/obl_forest.v). The
   mover owns the new parent's permission. In our setting the new parent is H2,
   and nothing that L holds speaks for H2. The alternative below puts that
   permission into the type of the end that L does hold, o2.

## The nearest alternative, caps

### The idea

o1 and `o2‾` have the same session type, so a bound shared by a protocol never
separates them. The bound that separates them is a number that the creator of
the channel of o2 fixed for `o2‾`, and that o2's type reports to whoever holds
o2. A cap m on an end promises that its counter never exceeds m. A partner
bound m̄ on an end promises that the cap of its partner is at most m̄. E-Link
asks `a1 > m̄2` and `a2 > m̄1`. Then

    k2′ ≤ cap(o2‾) ≤ m̄2 < a1 ≤ k1      and      k1′ ≤ cap(o1‾) ≤ m̄1 < a2 ≤ k2.

No counter changes at the link. H2 and B keep their counters and their FuelE.
Only their partners change.

### Rule changes

- Types. `TSess S x a` becomes `TSess S x a (m, m̄)`, written
  `(S@x)^a_{m,m̄}` with `a ≤ m ≤ N` and `m̄ ≤ N`. TLolli and TBox lose the field
  `t : tix`. `tix`, `tapp`, `meets`, `tfin`, `tid`, `tinf`, `tle`, `tspawn`,
  `tlink`, `tseq`, `tmax`, `tok` and `link_split` go (types/Costs.v). Duality of
  end types swaps the caps of the two ends of a channel. No subtyping on m. The
  partner bound may grow, `(m, m̄) ≤ (m, m̄′)` for `m̄ ≤ m̄′`.
- Judgment. `Θ ; Γ ; Δ ⊢^F_{W,N} e : T ▷ c`, the effect is the cost alone.
  Every `tok` premise and every `tseq` in a conclusion goes (E-App, E-Pair,
  E-LetU, E-LetP, E-Case, E-Force, E-Link, E-Spawn).
- E-Link.

      Θ ; Γ ; Δ ⊢ e : (S@x)^{a1}_{m1,m̄1} ⊗ (S̄@x̄)^{a2}_{m2,m̄2} ▷ c0
      a1 > m̄2      a2 > m̄1
      ──────────────────────────────────────────────── E-Link
      Θ ; Γ ; Δ ⊢ link e : ∗ ▷ c0

- E-New. `new` returns `(S@π)^{m}_{m,m̄} ⊗ (S̄@π̄)^{m̄}_{m̄,m}` with
  `m, m̄ ≤ N` fixed with the point of the channel (see the last section).
- Actions. E-Send, E-Recv, E-Select and E-Branch return the end at credit m,
  its own cap, where they return N today. The caps travel unchanged with the
  end, also as a payload.
- E-Spawn, E-SpawnLam. No `tspawn`, the conclusion has no effect beyond the
  cost.
- P-Term. The premise `N = None ∨ tfin ϑ` goes. The ends of ΘB sit at
  `(S@x)^{m}_{m,m̄}` and `(S̄@x̄)^{m̄}_{m̄,m}`. The interface entries of
  `tenv_of N Σ` get caps (N, N), so an interface end serves as a link target
  only through a partner bound that the other component reports.

### Fuel and process relation changes

- FuelE loses tk and the reserve r. φ maps an end to its counter, its cap
  and its partner bound. `refill` sets o to its cap instead of N. F-Link reads

      plink Π os ∧ os ⊆ dom φ ∧ φ(o1) > m̄(o2) ∧ φ(o2) > m̄(o1) ∧ El n′ … (mrem os Π) (mrem os φ) e′

  and F-Spawn keeps the ends split and drops `Nat.div2`. The closure and box
  clauses of `Vty` lose `meets t r tk`.
- The lock-free process relation. `hold` gets the cap of the end, `s_tk` and `tk_next` go, and
  `knew` starts the two ends at their caps. Two clauses join `soup_gen`, both
  index-free on K except the bound read in Π.
  - `sp_cap`. Every counter in K is at most the cap of its end.
  - `sp_pbound`. For an internal channel, the partner bound of each end is at
    least the cap of the other end.

  `sp_pdual` compares protocols up to the caps.
- The link preserves both clauses. After `PickLink o1 o2` the new pair is
  `(o1‾, o2‾)`. The partner bound of `o1‾` is at least the cap of o1, which is
  at least a1, and the cap of `o2‾` is at most `m̄2 < a1`. Symmetrically the
  partner bound of `o2‾` is at least `a2 > m̄1`, and m̄1 bounds the cap of `o1‾`. Every other update keeps
  counters at most caps (refill to the cap, tick, hand-over minus one).
- The measure. `fu k t` becomes the counter of the partner of the end t
  waits on, ordered by `<` on ℕ. In the proof of `Hfuel` (soup/LFAdequacy.v) the
  link case uses F-Link at level 1 for k1 and `sp_cap` with `sp_pbound` for k2′,
  which gives `k2′ < k1`. The spawn case loses its ticket part (`ksum_spawn`
  goes), every other case is as today without the first component.
  `lf_run_criterion` keeps its statement with `M = nat` and `Rm = lt`.

### Lemmas to change

`cost/Transformers.v` goes. `link_split` and the ticket parts of
`fsem_of_cost`, `thfuel_id`, `lf_p_term` and `lf_soundness_source` go. The cost
compatibility lemmas of E-Link and E-Spawn (cost/CostRules.v) prove F-Link from
the two new premises and credit at most counter (`Vty` at TSess, `fle a f`).
`soup/SoupLink.v` proves `sp_cap` and `sp_pbound` after the link. FuelMono,
FuelBind and FuelSub lose their tk and r arguments.

## The four checks

1. Paying for the link. Nothing to pay, because the link lowers no counter.
   The price moves to the type, a cap and a partner bound per end, chosen at the
   creation of the channel. The credits that E-Link asks of o1 and o2 are the
   credit asked of the linked ends that the plan named, measured against the
   partner bounds.
2. Spawn. No split, no `Nat.div2`, no doubling. check-ticket-split.md has
   nothing left to decide.
3. The examples and the measure.
   - rx-relink. `link ⟨w, c⟩` asks `a_w > m̄(c) ≥ cap(c′)`. After `send k`
     the credit of c′ is at most `cap(c′) − 1 < a_w − 1`, and the recursive call
     asks c′ at the parameter type of w with credit a_w. No typing exists, for
     any choice of caps.
   - The lock-free examples. No `v2/examples/LF*.v` uses `link`
     (`grep -il link v2/examples/LF*.v` finds nothing). Their tickets appear
     only as the transformer `tid` and its compositions. Each keeps its typing
     with caps (N, N) on every end and the ticket arguments deleted.
   - The measure drops at every step of the partner holder on another end (F-Tick
     as today), at a hand-over (minus one as today) and at a link (above).
4. The rest of rejects.js. rx-postpone is rejected by aging, rx-delegate by
   the payload credit, rx-chain by `wfworld`. None of them links or spends a
   ticket, and the alternative changes none of these premises.

## What the alternative also accepts

A box that links once per round forever, such as a server that links each new
client to a worker, is rejected today by the ticket need ∞. With caps it types
when the protocol of the received ends gives the client end a credit above the
partner bound of the worker end. This is the case "link budgets per end" of the
open discussion in pending.md, reached through counters instead of a separate
budget.

## Open, the creation choice of the caps

The lock-free process relation fixes the counter of a new end index-free (`knew`), so the caps of a
new channel must be the same at every level. Today the creation label names a
family ℓ or an anchor o and a field κ, so the caps can sit in the world with
the laws, a pair `(m_ℓ, m̄_ℓ)` per family and one per field. With one plain
`new` (entry 2) the caps join the point π and the constraint C in the creation
choice. They then need exactly what π and C need, the choice χ of the current
proposal, or the existential property of transfinite indices
(check-transfinite.md). Caps range over a finite set, so a classical pigeonhole
over `{0..N}²` would also fix them, which v2 rules out together with excluded
middle (check-ticket-split.md).
