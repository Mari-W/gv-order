# GV≺

GV≺ is a functional language with session-typed channels in the style of GV.
Every end of a channel acts at a point, and programs state facts `x ≺ y`
between points. Two logical relations over worlds of points and facts give
the guarantees. A typed closed program is deadlock free. Typed at a finite
bound, it is also lock free.

This repository holds the Rocq mechanization, a map of its definitions and
theorems, and the paper draft.

- The map, a browsable page of every rule, relation and theorem with links
  into the Rocq, is at <https://mariusweidner.de/gv-order/>.
- The development has no axioms and no admitted proofs. Lock freedom assumes
  excluded middle and functional choice, and the theorems state these as
  hypotheses.

## Main results

| Theorem | File | Statement |
|---|---|---|
| `soundness` | `theories/static/FundamentalProc.v` | `∅ ⊢_W p : T → deadlock_free p` |
| `lf_soundness` | `theories/soup/LFTyped.v` | `EM → FC → ∅ ⊩^N_W p : T → lock_free p` |
| `fundamental_proc` | `theories/static/FundamentalProc.v` | a typed process is in the deadlock-free relation |
| `lf_fundamental` | `theories/soup/LFTyped.v` | a typed process at a finite bound is in the lock-free relation |
| `adequacy` | `theories/relation/Adequacy.v` | a closed process in the relation is deadlock free |
| `fundamental` | `theories/static/Fundamental.v` | a typed term is in the term relation |

`theories/CheckAll.v` prints the assumptions of 287 results, the examples
included. `make check` fails unless each of them is closed under the global
context.

## Building

The development needs OCaml, Rocq 9.2, rocq-stdlib 9.2 and rocq-stdpp 1.13.
`gv-order.opam.locked` pins the versions that CI uses.

```
opam switch create gv-order ocaml-base-compiler.5.3.0
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install --deps-only --locked .
eval $(opam env)
ulimit -s 1000000
make -j$(nproc)
make test     # the notations print as written
make check    # every result of CheckAll.v is closed
```

Some files need a large stack. If `make` stops with error 139, raise the
stack limit as above and run it again.

With Docker, `docker build -t gv-order .` builds the development and runs
`make check` in a clean Ubuntu image.

## Layout

| Directory | Content |
|---|---|
| `theories/lang` | syntax, thread and process semantics, deadlock freedom and progress |
| `theories/lockfree` | runs, weak fairness and lock freedom |
| `theories/types` | types, session types, duality, points and worlds |
| `theories/static` | the typing judgments, their fundamental theorems and soundness |
| `theories/relation` | worlds, readiness, the value, term and process relations, adequacy |
| `theories/compat` | the compatibility lemma of each typing rule |
| `theories/fuel`, `theories/cost` | fuel, the second predicate of the lock-free relation |
| `theories/soup` | the lock-free process relation and its adequacy |
| `theories/examples` | typed and rejected programs, each with its theorem |
| `theories/test` | notation tests |
| `docs/explorer` | the map, `map.json`, served as the website |
| `tools/proof-map` | the page that renders the map and the checker that compares it with the Rocq |
| `paper` | the paper draft |

The logical root of `theories/` is `GV`, so `theories/lang/Syntax.v` is the
module `GV.lang.Syntax`.

## The map

`docs/explorer/map.json` lists each definition, rule and theorem with its
formula, a note on each symbol and the Rocq names it stands for.
`make map` checks that each cited name exists in `theories/` and that each
formula renders. CI runs this check and publishes the page on every push to
`main`.

To view the page locally, run `docs/explorer/serve.sh` and open the address
it prints.
