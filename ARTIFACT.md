# Artifact: deadlock freedom by strict partial orders and a logical relation

This artifact is the Rocq development in `theories/` that accompanies the
paper draft in `paper/`. It mechanizes GV♯, its static type system with
points, futures and constrained boxes, a step-indexed logical relation
indexed by worlds of points, and the proof that every typed closed program
is deadlock free. It also embeds three priority-based systems (PGV,
Padovani and Novara, Mordido and Pérez) and proves their programs deadlock
free through the embedding.

The development has no axioms and no admitted proofs. `make check` verifies
this for 452 declarations by `Print Assumptions` (section 3).

## 1. Requirements

Software (pinned in `spo-lr-df.opam.locked`)

| Package | Version |
|---|---|
| OCaml (`ocaml-base-compiler`) | 5.3.0 |
| `rocq-core`, `rocq-runtime` | 9.2.0 |
| `rocq-stdlib` | 9.2.0 |
| `rocq-stdpp` | 1.13.0 |
| `dune`, `zarith`, `ocamlfind` | 3.23.1, 1.14, 1.9.8 |
| `python3` (for `make check`) | any 3.x |

Hardware and time, measured on 4 cores of an Intel Xeon at 2.10 GHz with
15 GB of memory (Ubuntu 24.04)

| Step | Wall clock | Peak memory |
|---|---|---|
| opam switch with OCaml and the dependencies | BUILD_DEPS | |
| `make -j4` from a clean tree | BUILD_TIME | BUILD_MEM |
| `make check` after the build | CHECK_TIME | CHECK_MEM |
| `docker build .` from scratch (all of the above) | DOCKER_TIME | |

Peak memory is the largest resident set of one `rocq` process. With `-jN`
up to N processes run at once. 8 GB of memory and 10 GB of disk suffice
for the Docker build. The longest files compile sequentially, so more than
4 cores barely shortens the build.

## 2. Getting started

Either route builds the whole development and runs the assumption check.
The kick-the-tires phase is the same command as the full evaluation.

### 2.1 With Docker (recommended)

```
docker build -t spo-lr-df .
```

The image starts from `ubuntu:24.04`, installs opam, creates an OCaml 5.3.0
switch, installs the locked dependencies, runs `make` and then `make check`.
The build fails if any step fails. If Docker Hub rate limits the pull of the
base image, use a mirror

```
docker build --build-arg BASE=public.ecr.aws/docker/library/ubuntu:24.04 -t spo-lr-df .
```

To inspect the built tree afterwards, run `docker run --rm -it spo-lr-df`,
which opens a shell in `/home/rocq/spo-lr-df` with the switch active.

### 2.2 With opam

```
opam init --bare --disable-sandboxing        # skip if opam is set up
opam switch create spo-lr-df ocaml-base-compiler.5.3.0
eval $(opam env --switch spo-lr-df)
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install --deps-only --locked .
ulimit -s 1000000
make -j$(nproc)
make check
```

`--locked` installs the exact versions of `spo-lr-df.opam.locked`.
Without it, opam solves the constraints of `spo-lr-df.opam`, which fix
rocq-core 9.2.0, rocq-stdlib 9.2.0 and rocq-stdpp 1.13.0 and leave the
rest free. The lockfile takes rocq-stdpp from the upstream GitLab archive
of tag `stdpp-1.13.0` (`pin-depends`).

Two notes on the build. The large stack (`ulimit -s 1000000`, about 1 GB)
is needed by a few deep proof terms. Do not use `ulimit -s unlimited`. If
`rocq` still dies with a segmentation fault from the stack, run `make`
again, which resumes. If `Makefile.conf` is missing, `make` regenerates it
with `rocq makefile -f _CoqProject -o Makefile`.

### 2.3 Expected output

`make` prints one `ROCQ compile theories/....v` line per file, 114 in all,
and no errors. Warnings are expected. `make check` ends with

```
452 names checked, 452 closed, 0 open; report in _build/check/report.txt
OK: every checked name is closed under the global context
```

and prints 5 warnings for references in `paper/4-extensions.tex` that name
no declaration (section 4.3).

## 3. Step-by-step instructions: checking the claims

### 3.1 What `make check` checks

`make check` builds everything and then runs `artifact/check.py`, which

1. collects the names below from the sources,
2. writes `_build/check/Check.v` with `Redirect "…" Print Assumptions N.`
   for each fully qualified name N,
3. compiles it against the built theories, and
4. fails unless the output for every name is exactly
   `Closed under the global context`.

It also fails if `theories/` contains `Admitted.`, `admit.` or a top-level
`Axiom`, `Parameter` or `Conjecture`, or if a name of the core list does
not exist. The checked names are

- the core results by name: `soundness`, `soundness_source`,
  `fundamental`, `fundamental_proc`, `sem_rules_fundamental`, `adequacy`,
  `styped_typed`, `typed_styped`, `styped_iff`, `harmony`, the process
  composition lemmas `Prel_term`, `Prel_indep`, `Prel_connect`,
  `Prel_connect_n`, `Prel_internalize`, `Erel_bind`, and the embedding
  theorems `pgv_translate`, `pgv_deadlock_free`,
  `pgv_deadlock_free_source`, `pn_translate`, `pn_translate_source`,
  `pn_deadlock_free`, `pn_deadlock_free_source`, `mp_translate`,
  `mp_deadlock_free`, `mp2_translate`, `mp2_deadlock_free`,
  `mp2_deadlock_free_source`, `mp3_translate`, `mp3_deadlock_free`,
  `mp3_deadlock_free_source`,
- every `Theorem` of the development,
- every `Lemma`, `Theorem`, `Corollary` or `Example` whose name contains
  `deadlock_free`, `untypable`, `underivable` or `_translate`,
- the same kinds in `theories/pgv`, `theories/pn` and `theories/mp` whose
  name contains `deadlock`, `translate`, `simulat` or ends in `_typed`,
- every declaration cited by `\rocq{…}` in `paper/*.tex` (section 4).

The list is recomputed on every run, so new and renamed theorems are
picked up. `python3 artifact/check.py --list` prints it with the reason
each name is included. `_build/check/report.txt` lists every name with
`closed` or `OPEN`.

### 3.2 The main claims

| Claim | Rocq name | File |
|---|---|---|
| A typed closed process at a strict world is deadlock free | `soundness` | `theories/static/Fundamental.v` |
| A closed source program under an acyclic top-level constraint is deadlock free | `soundness_source` | `theories/static/Fundamental.v` |
| Fundamental property, terms and processes | `fundamental`, `fundamental_proc` | `theories/static/Fundamental.v` |
| Fundamental property of the semantic rules | `sem_rules_fundamental` | `theories/rules/SemanticRules.v` |
| Adequacy: a semantically typed closed process is deadlock free | `adequacy` | `theories/relation/LogicalRelation.v` |
| The source judgment and the world-carrying judgment agree | `styped_typed`, `typed_styped`, `styped_iff` | `theories/static/Source.v` |
| Reduction semantics and LTS agree | `harmony` | `theories/lang/Harmony.v` |
| PGV programs are deadlock free | `pgv_translate`, `pgv_deadlock_free`, `pgv_deadlock_free_source` | `theories/pgv/PGVTranslate.v`, `theories/pgv/PGVSimulation.v` |
| Padovani and Novara programs are deadlock free | `pn_translate`, `pn_deadlock_free`, `pn_deadlock_free_source` | `theories/pn/PNTranslate.v`, `theories/pn/PNSimulation.v` |
| Mordido and Pérez programs are deadlock free | `mp_deadlock_free`, `mp2_deadlock_free_source`, `mp3_deadlock_free_source` | `theories/mp/` |

To inspect a single claim interactively, open a file that imports it, or run

```
eval $(opam env)
rocq repl -R theories LRGV
Require Import LRGV.static.Fundamental.
Check soundness_source.
Print Assumptions soundness_source.
```

### 3.3 Reading a statement against the paper

Section 4 maps every `\rocq{…}` reference of the paper to a file, line and
fully qualified name (`theories/a/B.v` is the module `LRGV.a.B`). The
module map of `theories/` is in `README.md`, the design decisions referred
to as "sharp edges N" in comments are in `docs/SHARP-EDGES.md`, and the
declarative system is specified in `docs/ORDERS-SPEC.md`.

## 4. Paper claims and their Rocq declarations

### 4.1 How the table is made

The paper links each claim to the mechanization with `\rocq{name}`.
`artifact/claims.py` resolves every reference as `paper/rocqrefs.py`
resolves it (the first declaration of the name in `theories/`, constructors
of inductive definitions included) and writes the table below. Rerun

```
python3 artifact/claims.py --update
```

after a change to `paper/` or `theories/`. Line numbers refer to the commit
of this file. "Element" is the theorem-like environment around the
reference, else the figure caption or rule section on its line, else the
enclosing section.

### 4.2 Names that occur in more than one file

The table follows the paper's links, which take the first file in sorted
path order. 18 names cited by the paper are declared in more than one
file, and for these the link can point at a file other than the one the
text means. Read the "Element" column to pick the intended file.

| Name | Declared in (the table shows the first) |
|---|---|
| `Crel` | `mp/MP2World.v`, `mp/MP3World.v`, `mp/MPWorld.v`, `pn/PNWorld.v` |
| `crel_hold` | `mp/MP2Translate.v`, `mp/MP3Translate.v`, `mp/MPWorld.v`, `pn/PNWorld.v` |
| `deleg_main`, `deleg_typed` | `examples/Delegation.v`, `pgv/PGVExamples.v` |
| `ends` | `composition/PConnectN.v`, `types/Types.v` |
| `ext_close`, `ext_recv`, `ext_send` | `composition/ConnectCut.v`, `composition/Internalize.v` |
| `ext_link`, `link_give` | `composition/ConnectSteps.v`, `composition/Internalize.v` |
| `final`, `sim_star`, `sim_step` | `mp/MP2Simulation.v`, `mp/MP3Simulation.v`, `pgv/PGVSimulation.v`, `pn/PNSimulation.v` |
| `fwd_rt` | `mp/MP2Simulation.v`, `mp/MP3Simulation.v`, `pn/PNSimulation.v` |
| `fw_main`, `fw_sub`, `fw_typed` | `examples/Forwarder.v`, `examples/KobForwarder.v` |
| `proot` | `mp/MP2World.v`, `mp/MP3World.v`, `mp/MPWorld.v`, `pgv/PGVWorld.v`, `pn/PNWorld.v` |

Paths are relative to `theories/`. `make check` checks every declaration
of these names.

### 4.3 References without a declaration

Five references of `paper/4-extensions.tex` name no declaration of this
commit. `python3 paper/rocqrefs.py check` reports them too.

| Paper | Reference | Declaration meant |
|---|---|---|
| 4-extensions.tex:160 | `kfw_ok` | `fw_ok` in `theories/examples/KobForwarder.v` |
| 4-extensions.tex:163 | `kfw_sub` | `fw_sub` in `theories/examples/KobForwarder.v` |
| 4-extensions.tex:164 | `kfw_typed` | `fw_typed` in `theories/examples/KobForwarder.v` |
| 4-extensions.tex:165 | `kfw_deadlock_free` | `fw_deadlock_free_kob` in `theories/examples/KobForwarder.v` |
| 4-extensions.tex:442 | `fixlam` | none. Commit 7f61a5c removed the lemma when `fix` became general |

Commit 38dc79c renamed the KobForwarder declarations to a `kfw_` prefix,
and a later change on `main` restored the `fw_` names. `make check` checks
the four declarations of the third column under their current names.

### 4.4 The table

<!-- claims:begin (generated by artifact/claims.py) -->
<!-- claims:end -->
