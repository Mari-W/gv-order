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
| opam switch with OCaml and the dependencies | 10 min (3 min OCaml, 7 min Rocq and stdpp) | |
| `make -j4` from a clean tree | 13 min (16 min CPU time) | 1.0 GB per process, 2.6 GB in all |
| `make check` after the build | 7.5 min | 1.9 GB |
| `docker build .` from scratch (all of the above) | 33 min (10.5 min opam, 21.5 min `make` and `make check`) | |
| GitHub Actions, `ubuntu-24.04` runner, no cache | 36 min (17.5 min opam switch, 10 min `make`, CHECK_CI) | |
| GitHub Actions with the cached opam switch | CI_CACHED | |

Peak memory per process is the largest resident set of one `rocq`
process. With `-jN` up to N processes run at once, and the whole machine
used at most 2.6 GB during `make -j4`. The build used 16 min of CPU time
in 13 min of wall clock, so 4 cores ran 1.2 processes on average and the
long files on the dependency chain set the wall clock. The Docker image takes 2.3 GB of disk.

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

Two notes on the build. The development asks for a large stack
(`ulimit -s 1000000`, about 1 GB). Do not use `ulimit -s unlimited`. If
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

### 2.4 Continuous integration

`.github/workflows/build.yml` runs on every push and pull request. It
installs opam from Ubuntu 24.04, restores the opam switch from the Actions
cache, keyed by the hash of `spo-lr-df.opam` and `spo-lr-df.opam.locked`,
creates and saves it on a miss, runs `make` and `make check`, and uploads
`_build/check/report.txt`. A manual run (`workflow_dispatch`) with the
input `docker` also runs the Docker build. The workflow needs no secrets.

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

- the core results `soundness`, `soundness_source`,
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
| Adequacy, a semantically typed closed process is deadlock free | `adequacy` | `theories/relation/LogicalRelation.v` |
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
| Paper | Element | Rocq name | Kind | Location |
|---|---|---|---|---|
| 2-calculus.tex:23 | Constants, values, terms | `expr` | Inductive | `theories/lang/Syntax.v:20` |
| 2-calculus.tex:51 | Figure (Syntax of GV♯) | `expr` | Inductive | `theories/lang/Syntax.v:20` |
| 2-calculus.tex:59 | Session labels, term labels, evaluation contexts | `slabel` | Inductive | `theories/lang/Semantics.v:15` |
| 2-calculus.tex:59 | Session labels, term labels, evaluation contexts | `tlabel` | Inductive | `theories/lang/Semantics.v:35` |
| 2-calculus.tex:88 | Labelled reductions for terms | `tstep` | Inductive | `theories/lang/Semantics.v:112` |
| 2-calculus.tex:190 | Theorem (Harmony) | `harmony` | Theorem | `theories/lang/Harmony.v:303` |
| 2-calculus.tex:209 | Labelled reductions for processes | `plabel` | Inductive | `theories/lang/Semantics.v:426` |
| 2-calculus.tex:280 | Definition (Irreducible terms and processes) | `irred` | Definition | `theories/lang/Semantics.v:499` |
| 2-calculus.tex:286 | Definition (Terminated process) | `terminated` | Definition | `theories/lang/Safety.v:14` |
| 2-calculus.tex:293 | Definition (Safe process) | `safe` | Definition | `theories/lang/Safety.v:17` |
| 2-calculus.tex:299 | Definition (Deadlock freedom) | `deadlock_free` | Definition | `theories/lang/Safety.v:20` |
| 2-calculus.tex:305 | Example (An exchange between two threads) | `sync_main` | Definition | `theories/examples/Sync.v:23` |
| 2-calculus.tex:318 | Example (An exchange between two threads) | `sync_deadlock_free` | Lemma | `theories/examples/Sync.v:57` |
| 2-calculus.tex:321 | Example (A cyclic topology) | `cycle_main` | Definition | `theories/examples/Cycle.v:24` |
| 2-calculus.tex:334 | Example (A cyclic topology) | `cycle_deadlock_free` | Lemma | `theories/examples/Cycle.v:63` |
| 2-calculus.tex:337 | Example (A deadlocked process) | `blocked_main` | Definition | `theories/examples/Rejected.v:147` |
| 2-calculus.tex:367 | Names, points, facts, constraints | `point` | Record | `theories/types/Types.v:35` |
| 2-calculus.tex:367 | Names, points, facts, constraints | `fact` | Inductive | `theories/types/Types.v:106` |
| 2-calculus.tex:367 | Names, points, facts, constraints | `bcs` | Record | `theories/types/Types.v:140` |
| 2-calculus.tex:405 | Types, session types, bounds | `ty` | Inductive | `theories/types/Types.v:175` |
| 2-calculus.tex:417 | Session duality | `dual` | Fixpoint | `theories/types/Types.v:626` |
| 2-calculus.tex:431 | Point substitution | `pt_inst` | Definition | `theories/types/Types.v:88` |
| 2-calculus.tex:431 | Point substitution | `pinst_ty` | Fixpoint | `theories/types/Types.v:326` |
| 2-calculus.tex:446 | § The Static System | `pup` | Definition | `theories/types/Types.v:92` |
| 2-calculus.tex:447 | Payloads | `payload_at` | Definition | `theories/types/Types.v:346` |
| 2-calculus.tex:469 | Definition (Payload) | `payload_at` | Definition | `theories/types/Types.v:346` |
| 2-calculus.tex:486 | Remark | `pinst_ty` | Fixpoint | `theories/types/Types.v:326` |
| 2-calculus.tex:492 | Remark | `sinst_ty` | Fixpoint | `theories/types/Types.v:645` |
| 2-calculus.tex:492 | Remark | `sren_ty` | Fixpoint | `theories/types/Types.v:552` |
| 2-calculus.tex:493 | Remark | `sflip_ty` | Fixpoint | `theories/types/Types.v:584` |
| 2-calculus.tex:497 | Remark | `payload_pinst` | Lemma | `theories/static/PointSubst.v:384` |
| 2-calculus.tex:519 | § Contexts and the judgment | `styped` | Inductive | `theories/static/Source.v:152` |
| 2-calculus.tex:528 | Aliasing | `seqs` | Inductive | `theories/static/FactTheory.v:106` |
| 2-calculus.tex:565 | Precedence | `fl` | Inductive | `theories/static/FactTheory.v:115` |
| 2-calculus.tex:598 | Heads, lower bounds, precedence of a frame | `heads` | Fixpoint | `theories/types/Types.v:519` |
| 2-calculus.tex:655 | Typing rules for terms | `styped` | Inductive | `theories/static/Source.v:152` |
| 2-calculus.tex:732 | Structural rules and rules for points | `styped` | Inductive | `theories/static/Source.v:152` |
| 2-calculus.tex:807 | Type-indexed families of type signatures for constants | `konst_ty` | Inductive | `theories/types/Types.v:1739` |
| 2-calculus.tex:842 | Definition (Creation constraint) | `cc_ok` | Definition | `theories/types/Types.v:1593` |
| 2-calculus.tex:874 | § Signatures | `t_new_open` | Lemma | `theories/static/Typing.v:203` |
| 2-calculus.tex:878 | § Processes | `prim` | Inductive | `theories/types/Types.v:1205` |
| 2-calculus.tex:886 | § Processes | `typed` | Inductive | `theories/static/Typing.v:18` |
| 2-calculus.tex:890 | § Processes | `styped_typed` | Theorem | `theories/static/Source.v:302` |
| 2-calculus.tex:899 | Primitive types | `prim` | Inductive | `theories/types/Types.v:1205` |
| 2-calculus.tex:923 | Typing rules for processes | `ptyped` | Inductive | `theories/static/Typing.v:150` |
| 2-calculus.tex:958 | § Soundness | `c0_consts` | Definition | `theories/static/Fundamental.v:957` |
| 2-calculus.tex:960 | § Soundness | `proot` | Definition | `theories/mp/MP2World.v:59` |
| 2-calculus.tex:962 | Theorem (Soundness for source programs) | `soundness_source` | Theorem | `theories/static/Fundamental.v:1184` |
| 2-calculus.tex:973 | § Soundness | `wnil` | Definition | `theories/static/Fundamental.v:902` |
| 2-calculus.tex:973 | § Soundness | `wnil_strict` | Lemma | `theories/static/Fundamental.v:904` |
| 2-calculus.tex:973 | § Soundness | `styped_typed` | Theorem | `theories/static/Source.v:302` |
| 2-calculus.tex:976 | § Soundness | `wc0` | Definition | `theories/static/Fundamental.v:1013` |
| 2-calculus.tex:977 | § Soundness | `wc0_strict` | Lemma | `theories/static/Fundamental.v:1025` |
| 2-calculus.tex:977 | § Soundness | `wc0_ext` | Lemma | `theories/static/Fundamental.v:1047` |
| 2-calculus.tex:979 | § Soundness | `wc0_holds` | Lemma | `theories/static/Fundamental.v:1056` |
| 2-calculus.tex:981 | § Soundness | `typed_sem_rules` | Lemma | `theories/static/Fundamental.v:373` |
| 2-calculus.tex:982 | § Soundness | `sem_rules_fundamental` | Theorem | `theories/rules/SemanticRules.v:114` |
| 2-calculus.tex:983 | § Soundness | `Prel_term` | Theorem | `theories/composition/PTerm.v:989` |
| 2-calculus.tex:985 | § Soundness | `prim_pinst` | Lemma | `theories/static/Fundamental.v:1173` |
| 2-calculus.tex:995 | § Soundness | `typed_styped` | Theorem | `theories/static/Source.v:438` |
| 2-calculus.tex:998 | Example (Delegation) | `deleg_main` | Definition | `theories/examples/Delegation.v:35` |
| 2-calculus.tex:1046 | Example (Delegation) | `deleg_typed` | Lemma | `theories/examples/Delegation.v:67` |
| 2-calculus.tex:1047 | Example (Delegation) | `deleg_deadlock_free` | Lemma | `theories/examples/Delegation.v:121` |
| 3-logical-rel.tex:33 | Definition (World) | `world` | Record | `theories/relation/Worlds.v:24` |
| 3-logical-rel.tex:33 | Definition (World) | `world_wf` | Record | `theories/relation/Worlds.v:92` |
| 3-logical-rel.tex:33 | Definition (World) | `strict` | Definition | `theories/relation/Worlds.v:110` |
| 3-logical-rel.tex:44 | Definition (World) | `pt_known` | Definition | `theories/relation/Worlds.v:117` |
| 3-logical-rel.tex:47 | Definition (Extension) | `wext` | Definition | `theories/relation/Worlds.v:219` |
| 3-logical-rel.tex:47 | Definition (Extension) | `wext_fresh` | Definition | `theories/relation/Worlds.v:228` |
| 3-logical-rel.tex:62 | § Worlds and Readiness | `wjoin` | Definition | `theories/relation/Worlds.v:234` |
| 3-logical-rel.tex:64 | § Worlds and Readiness | `wrestrict` | Definition | `theories/relation/Worlds.v:240` |
| 3-logical-rel.tex:66 | Theorem (Amalgamation) | `amalgamation` | Theorem | `theories/relation/Worlds.v:647` |
| 3-logical-rel.tex:79 | § Worlds and Readiness | `wjoin_wf` | Lemma | `theories/relation/Worlds.v:255` |
| 3-logical-rel.tex:79 | § Worlds and Readiness | `wrestrict_wf` | Lemma | `theories/relation/Worlds.v:285` |
| 3-logical-rel.tex:81 | § Worlds and Readiness | `wjoin_restrict_incl` | Lemma | `theories/relation/Worlds.v:636` |
| 3-logical-rel.tex:85 | § Worlds and Readiness | `jpath` | Inductive | `theories/relation/Worlds.v:448` |
| 3-logical-rel.tex:85 | § Worlds and Readiness | `join_jpath` | Lemma | `theories/relation/Worlds.v:495` |
| 3-logical-rel.tex:88 | § Worlds and Readiness | `jpath_decomp` | Lemma | `theories/relation/Worlds.v:556` |
| 3-logical-rel.tex:90 | § Worlds and Readiness | `join_cycle` | Lemma | `theories/relation/Worlds.v:609` |
| 3-logical-rel.tex:94 | Theorem (Fresh extension) | `fresh_extension` | Theorem | `theories/relation/Worlds.v:667` |
| 3-logical-rel.tex:109 | § Worlds and Readiness | `wext_fresh` | Definition | `theories/relation/Worlds.v:228` |
| 3-logical-rel.tex:111 | § Worlds and Readiness | `wgen_incl` | Lemma | `theories/relation/Worlds.v:426` |
| 3-logical-rel.tex:123 | Definition (Readiness) | `ready_t` | Definition | `theories/relation/Readiness.v:91` |
| 3-logical-rel.tex:123 | Definition (Readiness) | `ready_p` | Definition | `theories/relation/Readiness.v:96` |
| 3-logical-rel.tex:126 | Definition (Readiness) | `entry_head` | Definition | `theories/types/Types.v:1283` |
| 3-logical-rel.tex:146 | Definition (Readiness) | `below_rest` | Definition | `theories/relation/Readiness.v:77` |
| 3-logical-rel.tex:146 | Definition (Readiness) | `above_offered` | Definition | `theories/relation/Readiness.v:70` |
| 3-logical-rel.tex:148 | Definition (Readiness) | `offered_t` | Definition | `theories/relation/Readiness.v:52` |
| 3-logical-rel.tex:148 | Definition (Readiness) | `offered_p` | Definition | `theories/relation/Readiness.v:55` |
| 3-logical-rel.tex:191 | § A Logical Relation for GV♯ | `senv` | Notation | `theories/types/Types.v:1231` |
| 3-logical-rel.tex:191 | § A Logical Relation for GV♯ | `tenv` | Notation | `theories/types/Types.v:1265` |
| 3-logical-rel.tex:191 | § A Logical Relation for GV♯ | `ends` | Definition | `theories/composition/PConnectN.v:37` |
| 3-logical-rel.tex:191 | § A Logical Relation for GV♯ | `tenv_of` | Definition | `theories/types/Types.v:1267` |
| 3-logical-rel.tex:198 | § A Logical Relation for GV♯ | `tenv_comp` | Definition | `theories/types/SessionEquiv.v:729` |
| 3-logical-rel.tex:202 | Value logical relation | `Vdef` | Fixpoint | `theories/relation/LogicalRelation.v:132` |
| 3-logical-rel.tex:278 | Term logical relation | `Edef` | Definition | `theories/relation/LogicalRelation.v:312` |
| 3-logical-rel.tex:295 | Obligations of a term transition | `Eobl` | Definition | `theories/relation/LogicalRelation.v:245` |
| 3-logical-rel.tex:360 | § A Logical Relation for GV♯ | `tcost` | Definition | `theories/relation/LogicalRelation.v:172` |
| 3-logical-rel.tex:362 | § A Logical Relation for GV♯ | `Efuel` | Fixpoint | `theories/relation/LogicalRelation.v:302` |
| 3-logical-rel.tex:380 | Process logical relation | `Pdef` | Definition | `theories/relation/LogicalRelation.v:488` |
| 3-logical-rel.tex:398 | Obligations of a process transition | `Pobl` | Definition | `theories/relation/LogicalRelation.v:427` |
| 3-logical-rel.tex:464 | § A Logical Relation for GV♯ | `recv_back` | Definition | `theories/relation/LogicalRelation.v:332` |
| 3-logical-rel.tex:464 | § A Logical Relation for GV♯ | `recv_env` | Definition | `theories/relation/LogicalRelation.v:339` |
| 3-logical-rel.tex:470 | § A Logical Relation for GV♯ | `send_split` | Definition | `theories/relation/LogicalRelation.v:345` |
| 3-logical-rel.tex:485 | Definition (Grounding substitutions) | `grounding` | Fixpoint | `theories/relation/LogicalRelation.v:1031` |
| 3-logical-rel.tex:501 | Definition (Semantic judgments) | `sem_typed` | Definition | `theories/relation/LogicalRelation.v:1098` |
| 3-logical-rel.tex:501 | Definition (Semantic judgments) | `sem_ptyped` | Definition | `theories/relation/LogicalRelation.v:1104` |
| 3-logical-rel.tex:521 | § Fundamental Property | `term_wf` | Definition | `theories/relation/LogicalRelation.v:1070` |
| 3-logical-rel.tex:522 | § Fundamental Property | `typed_term_wf_s` | Lemma | `theories/static/Fundamental.v:214` |
| 3-logical-rel.tex:526 | Lemma | `Prel_steps` | Lemma | `theories/relation/LogicalRelation.v:1111` |
| 3-logical-rel.tex:538 | § Fundamental Property | `Prel_S_tau` | Lemma | `theories/relation/LogicalRelation.v:996` |
| 3-logical-rel.tex:545 | Lemma | `Prel_safe` | Lemma | `theories/relation/LogicalRelation.v:1124` |
| 3-logical-rel.tex:552 | § Fundamental Property | `proc_progress` | Lemma | `theories/lang/Safety.v:459` |
| 3-logical-rel.tex:554 | § Fundamental Property | `Prel_S_irred` | Lemma | `theories/relation/LogicalRelation.v:988` |
| 3-logical-rel.tex:558 | § Fundamental Property | `Prel_S_empty_no_sess` | Lemma | `theories/relation/LogicalRelation.v:1006` |
| 3-logical-rel.tex:562 | Theorem (Adequacy) | `adequacy` | Theorem | `theories/relation/LogicalRelation.v:1135` |
| 3-logical-rel.tex:581 | § Fundamental Property | `typed` | Inductive | `theories/static/Typing.v:18` |
| 3-logical-rel.tex:581 | § Fundamental Property | `styped_typed` | Theorem | `theories/static/Source.v:302` |
| 3-logical-rel.tex:595 | § Fundamental Property | `sem_typed_unit` | Lemma | `theories/rules/TermRules.v:256` |
| 3-logical-rel.tex:596 | § Fundamental Property | `sem_typed_konst` | Lemma | `theories/rules/TermRules.v:265` |
| 3-logical-rel.tex:597 | § Fundamental Property | `sem_typed_var` | Lemma | `theories/rules/TermRules.v:279` |
| 3-logical-rel.tex:598 | § Fundamental Property | `sem_typed_lam` | Lemma | `theories/rules/TermRules.v:561` |
| 3-logical-rel.tex:599 | § Fundamental Property | `sem_typed_app` | Lemma | `theories/rules/BoxRules.v:57` |
| 3-logical-rel.tex:600 | § Fundamental Property | `sem_typed_pair` | Lemma | `theories/rules/TermRules.v:496` |
| 3-logical-rel.tex:601 | § Fundamental Property | `sem_typed_letp` | Lemma | `theories/rules/TermRules.v:418` |
| 3-logical-rel.tex:602 | § Fundamental Property | `sem_typed_letu` | Lemma | `theories/rules/TermRules.v:380` |
| 3-logical-rel.tex:603 | § Fundamental Property | `sem_typed_inj1` | Lemma | `theories/rules/TermRules.v:340` |
| 3-logical-rel.tex:604 | § Fundamental Property | `sem_typed_case` | Lemma | `theories/rules/TermRules.v:451` |
| 3-logical-rel.tex:605 | § Fundamental Property | `sem_typed_wk` | Lemma | `theories/rules/TermRules.v:1127` |
| 3-logical-rel.tex:606 | § Fundamental Property | `sem_typed_contract` | Lemma | `theories/rules/BoxRules.v:109` |
| 3-logical-rel.tex:607 | § Fundamental Property | `sem_typed_teq` | Lemma | `theories/invariance/EquivInvariance.v:155` |
| 3-logical-rel.tex:608 | § Fundamental Property | `sem_typed_box` | Lemma | `theories/rules/BoxRules.v:140` |
| 3-logical-rel.tex:609 | § Fundamental Property | `sem_typed_pack` | Lemma | `theories/rules/ExRules.v:68` |
| 3-logical-rel.tex:610 | § Fundamental Property | `sem_typed_open` | Lemma | `theories/rules/ExRules.v:113` |
| 3-logical-rel.tex:611 | § Fundamental Property | `Prel_term` | Theorem | `theories/composition/PTerm.v:989` |
| 3-logical-rel.tex:612 | § Fundamental Property | `Prel_connect` | Theorem | `theories/composition/PConnect.v:199` |
| 3-logical-rel.tex:618 | § Fundamental Property | `sem_typed_chan` | Lemma | `theories/rules/TermRules.v:287` |
| 3-logical-rel.tex:620 | § Fundamental Property | `sem_typed_force` | Lemma | `theories/rules/BoxRules.v:77` |
| 3-logical-rel.tex:621 | § Fundamental Property | `Prel_indep` | Theorem | `theories/composition/PTerm.v:1003` |
| 3-logical-rel.tex:623 | Lemma (Compositionality: E-Abs) | `sem_typed_lam` | Lemma | `theories/rules/TermRules.v:561` |
| 3-logical-rel.tex:634 | § Fundamental Property | `Vrel_Erel` | Lemma | `theories/relation/LogicalRelation.v:977` |
| 3-logical-rel.tex:641 | § Fundamental Property | `fchans_subst` | Lemma | `theories/lang/Syntax.v:482` |
| 3-logical-rel.tex:646 | § Fundamental Property | `grounding_heads` | Lemma | `theories/rules/TermRules.v:105` |
| 3-logical-rel.tex:653 | Lemma (Compositionality: E-Exp) | `sem_typed_box` | Lemma | `theories/rules/BoxRules.v:140` |
| 3-logical-rel.tex:669 | § Fundamental Property | `grounding_unl` | Lemma | `theories/rules/BoxRules.v:128` |
| 3-logical-rel.tex:678 | § Fundamental Property | `Vrel_box_thunk_iff` | Lemma | `theories/relation/LogicalRelation.v:1256` |
| 3-logical-rel.tex:687 | Lemma (Compositionality: P-Connect) | `Prel_connect` | Theorem | `theories/composition/PConnect.v:199` |
| 3-logical-rel.tex:709 | § Fundamental Property | `Prel_mono` | Lemma | `theories/invariance/Monotonicity.v:263` |
| 3-logical-rel.tex:709 | § Fundamental Property | `wext_join_l` | Lemma | `theories/invariance/Monotonicity.v:60` |
| 3-logical-rel.tex:711 | § Fundamental Property | `wext_fresh_join` | Lemma | `theories/relation/Worlds.v:727` |
| 3-logical-rel.tex:714 | § Fundamental Property | `cut_ok` | Record | `theories/composition/ConnectCut.v:28` |
| 3-logical-rel.tex:715 | § Fundamental Property | `ctys` | Definition | `theories/composition/ConnectCut.v:17` |
| 3-logical-rel.tex:717 | § Fundamental Property | `ctys_sym` | Lemma | `theories/composition/ConnectCut.v:19` |
| 3-logical-rel.tex:717 | § Fundamental Property | `cut_ok_sym` | Lemma | `theories/composition/ConnectCut.v:46` |
| 3-logical-rel.tex:720 | § Fundamental Property | `conn_at` | Definition | `theories/composition/ConnectCut.v:72` |
| 3-logical-rel.tex:723 | § Fundamental Property | `conn_lt` | Definition | `theories/composition/ConnectCut.v:79` |
| 3-logical-rel.tex:723 | § Fundamental Property | `msize` | Definition | `theories/relation/LogicalRelation.v:197` |
| 3-logical-rel.tex:726 | § Fundamental Property | `pcost_giving` | Lemma | `theories/relation/LogicalRelation.v:411` |
| 3-logical-rel.tex:728 | § Fundamental Property | `conn_level` | Lemma | `theories/composition/PConnect.v:31` |
| 3-logical-rel.tex:728 | § Fundamental Property | `Prel_S_intro` | Lemma | `theories/relation/LogicalRelation.v:958` |
| 3-logical-rel.tex:733 | § Fundamental Property | `Prel_S_stop_prim` | Lemma | `theories/composition/ConnectCut.v:138` |
| 3-logical-rel.tex:735 | § Fundamental Property | `Vrel_prim_empty` | Lemma | `theories/relation/LogicalRelation.v:592` |
| 3-logical-rel.tex:738 | § Fundamental Property | `conn_stop` | Lemma | `theories/composition/ConnectCut.v:179` |
| 3-logical-rel.tex:744 | § Fundamental Property | `link_l` | Lemma | `theories/composition/ReadyChain.v:477` |
| 3-logical-rel.tex:744 | § Fundamental Property | `link_r` | Lemma | `theories/composition/ReadyChain.v:487` |
| 3-logical-rel.tex:745 | § Fundamental Property | `stable_l` | Lemma | `theories/composition/ReadyChain.v:287` |
| 3-logical-rel.tex:745 | § Fundamental Property | `stable_r` | Lemma | `theories/composition/ReadyChain.v:293` |
| 3-logical-rel.tex:747 | § Fundamental Property | `ready_core` | Definition | `theories/composition/ReadyChain.v:255` |
| 3-logical-rel.tex:747 | § Fundamental Property | `Prel_S_ready` | Lemma | `theories/composition/ConnectCut.v:148` |
| 3-logical-rel.tex:750 | § Fundamental Property | `cut_not_both` | Lemma | `theories/composition/ReadyChain.v:433` |
| 3-logical-rel.tex:752 | § Fundamental Property | `sdual_snd` | Lemma | `theories/composition/ReadyChain.v:132` |
| 3-logical-rel.tex:752 | § Fundamental Property | `sdual_rcv` | Lemma | `theories/composition/ReadyChain.v:140` |
| 3-logical-rel.tex:752 | § Fundamental Property | `sdual_end` | Lemma | `theories/composition/ReadyChain.v:148` |
| 3-logical-rel.tex:754 | § Fundamental Property | `msg_tau` | Lemma | `theories/composition/ReadyChain.v:86` |
| 3-logical-rel.tex:754 | § Fundamental Property | `close_tau` | Lemma | `theories/composition/ReadyChain.v:101` |
| 3-logical-rel.tex:759 | § Fundamental Property | `ext_l` | Lemma | `theories/composition/ReadyChain.v:331` |
| 3-logical-rel.tex:762 | § Fundamental Property | `step_l` | Lemma | `theories/composition/ReadyChain.v:524` |
| 3-logical-rel.tex:762 | § Fundamental Property | `step_r` | Lemma | `theories/composition/ReadyChain.v:553` |
| 3-logical-rel.tex:766 | § Fundamental Property | `descent` | Lemma | `theories/composition/ReadyChain.v:585` |
| 3-logical-rel.tex:775 | § Fundamental Property | `no_offers_l` | Lemma | `theories/composition/ReadyChain.v:637` |
| 3-logical-rel.tex:775 | § Fundamental Property | `no_offers_r` | Lemma | `theories/composition/ReadyChain.v:654` |
| 3-logical-rel.tex:777 | § Fundamental Property | `empty_of_no_offers` | Lemma | `theories/composition/ReadyChain.v:673` |
| 3-logical-rel.tex:778 | § Fundamental Property | `ready_connect` | Theorem | `theories/composition/ReadyChain.v:731` |
| 3-logical-rel.tex:781 | § Fundamental Property | `ptau_inv` | Lemma | `theories/invariance/JunkRenaming.v:682` |
| 3-logical-rel.tex:781 | § Fundamental Property | `proc_step_sess_inv` | Lemma | `theories/lang/Semantics.v:508` |
| 3-logical-rel.tex:785 | § Fundamental Property | `own_tau` | Lemma | `theories/composition/ConnectSteps.v:123` |
| 3-logical-rel.tex:788 | § Fundamental Property | `Prel_tau_rename` | Lemma | `theories/invariance/PointRenaming.v:1758` |
| 3-logical-rel.tex:789 | § Fundamental Property | `tau_beta` | Lemma | `theories/composition/ConnectSteps.v:862` |
| 3-logical-rel.tex:789 | § Fundamental Property | `tau_new` | Lemma | `theories/composition/ConnectSteps.v:881` |
| 3-logical-rel.tex:789 | § Fundamental Property | `tau_spawn` | Lemma | `theories/composition/ConnectSteps.v:871` |
| 3-logical-rel.tex:790 | § Fundamental Property | `tau_msg` | Lemma | `theories/composition/ConnectSteps.v:894` |
| 3-logical-rel.tex:790 | § Fundamental Property | `tau_close` | Lemma | `theories/composition/ConnectSteps.v:905` |
| 3-logical-rel.tex:795 | § Fundamental Property | `cross_msg` | Lemma | `theories/composition/ConnectSteps.v:334` |
| 3-logical-rel.tex:797 | § Fundamental Property | `cross_close` | Lemma | `theories/composition/ConnectSteps.v:171` |
| 3-logical-rel.tex:800 | § Fundamental Property | `cross_subj` | Lemma | `theories/composition/ConnectSteps.v:149` |
| 3-logical-rel.tex:803 | § Fundamental Property | `ext_recv` | Lemma | `theories/composition/ConnectCut.v:433` |
| 3-logical-rel.tex:803 | § Fundamental Property | `ext_send` | Lemma | `theories/composition/ConnectCut.v:292` |
| 3-logical-rel.tex:803 | § Fundamental Property | `ext_close` | Lemma | `theories/composition/ConnectCut.v:594` |
| 3-logical-rel.tex:804 | § Fundamental Property | `ext_link` | Lemma | `theories/composition/ConnectSteps.v:56` |
| 3-logical-rel.tex:809 | § Fundamental Property | `link_give` | Lemma | `theories/composition/ConnectSteps.v:822` |
| 3-logical-rel.tex:810 | § Fundamental Property | `link_own` | Lemma | `theories/composition/ConnectSteps.v:577` |
| 3-logical-rel.tex:810 | § Fundamental Property | `ext_link_norm` | Lemma | `theories/composition/ConnectSteps.v:625` |
| 3-logical-rel.tex:814 | § Fundamental Property | `Prel_connect_list` | Lemma | `theories/composition/PConnectN.v:311` |
| 3-logical-rel.tex:815 | § Fundamental Property | `Prel_connect_n` | Theorem | `theories/composition/PConnectN.v:374` |
| 3-logical-rel.tex:825 | Theorem (Fundamental property) | `fundamental` | Theorem | `theories/static/Fundamental.v:854` |
| 3-logical-rel.tex:825 | Theorem (Fundamental property) | `fundamental_proc` | Theorem | `theories/static/Fundamental.v:868` |
| 3-logical-rel.tex:852 | § Fundamental Property | `typed_sem_rules` | Lemma | `theories/static/Fundamental.v:373` |
| 3-logical-rel.tex:852 | § Fundamental Property | `sem_rules` | Inductive | `theories/rules/SemanticRules.v:20` |
| 3-logical-rel.tex:858 | § Fundamental Property | `sem_rules_fundamental` | Theorem | `theories/rules/SemanticRules.v:114` |
| 3-logical-rel.tex:860 | § Fundamental Property | `typed_sem_rules_closed` | Lemma | `theories/static/Fundamental.v:840` |
| 3-logical-rel.tex:867 | § Fundamental Property | `wext_join_self` | Lemma | `theories/static/Fundamental.v:859` |
| 3-logical-rel.tex:870 | Theorem (Soundness) | `soundness` | Theorem | `theories/static/Fundamental.v:888` |
| 3-logical-rel.tex:885 | § Fundamental Property | `soundness_source` | Theorem | `theories/static/Fundamental.v:1184` |
| 4-extensions.tex:13 | Example (The received chain) | `ch_main` | Definition | `theories/examples/ReceivedChain.v:52` |
| 4-extensions.tex:64 | Example (The received chain) | `ch_sub` | Lemma | `theories/examples/ReceivedChain.v:62` |
| 4-extensions.tex:68 | Example (The received chain) | `ch_typed` | Lemma | `theories/examples/ReceivedChain.v:172` |
| 4-extensions.tex:69 | Example (The received chain) | `ch_deadlock_free` | Lemma | `theories/examples/ReceivedChain.v:205` |
| 4-extensions.tex:83 | Example (The forwarder) | `fw_main` | Definition | `theories/examples/Forwarder.v:72` |
| 4-extensions.tex:126 | Example (The forwarder) | `fw_sub` | Lemma | `theories/examples/Forwarder.v:80` |
| 4-extensions.tex:127 | Example (The forwarder) | `fprod_typed` | Lemma | `theories/examples/Forwarder.v:147` |
| 4-extensions.tex:127 | Example (The forwarder) | `fcons_typed` | Lemma | `theories/examples/Forwarder.v:182` |
| 4-extensions.tex:129 | Example (The forwarder) | `fw_typed` | Lemma | `theories/examples/Forwarder.v:346` |
| 4-extensions.tex:130 | Example (The forwarder) | `fw_deadlock_free` | Lemma | `theories/examples/Forwarder.v:425` |
| 4-extensions.tex:136 | Example (Kobayashi's forwarder server) | `fwsrv` | Definition | `theories/examples/KobForwarder.v:69` |
| 4-extensions.tex:160 | Example (Kobayashi's forwarder server) | `kfw_ok` | unresolved | **(no declaration)** |
| 4-extensions.tex:163 | Example (Kobayashi's forwarder server) | `kfw_sub` | unresolved | **(no declaration)** |
| 4-extensions.tex:164 | Example (Kobayashi's forwarder server) | `kfw_typed` | unresolved | **(no declaration)** |
| 4-extensions.tex:165 | Example (Kobayashi's forwarder server) | `kfw_deadlock_free` | unresolved | **(no declaration)** |
| 4-extensions.tex:168 | Example (The factorial server) | `fcsrv` | Definition | `theories/examples/FactServer.v:69` |
| 4-extensions.tex:187 | Example (The factorial server) | `fc_deadlock_free` | Theorem | `theories/examples/FactServer.v:203` |
| 4-extensions.tex:193 | Example (Milner's cyclic scheduler) | `ms_main` | Definition | `theories/examples/MilnerSched.v:87` |
| 4-extensions.tex:224 | Example (Milner's cyclic scheduler) | `ms_typed` | Lemma | `theories/examples/MilnerSched.v:112` |
| 4-extensions.tex:224 | Example (Milner's cyclic scheduler) | `ms_deadlock_free` | Theorem | `theories/examples/MilnerSched.v:179` |
| 4-extensions.tex:226 | Example (Milner's cyclic scheduler) | `sched_deadlock_free` | Lemma | `theories/examples/Scheduler.v:119` |
| 4-extensions.tex:237 | § Programs the System Rejects | `slt_acyclic_nil` | Lemma | `theories/examples/Rejected.v:175` |
| 4-extensions.tex:239 | Theorem (One round is not enough) | `rr_call_underivable` | Lemma | `theories/examples/Rejected.v:58` |
| 4-extensions.tex:256 | § Programs the System Rejects | `rr_R` | Definition | `theories/examples/Rejected.v:41` |
| 4-extensions.tex:257 | § Programs the System Rejects | `rr_rank` | Definition | `theories/examples/Rejected.v:34` |
| 4-extensions.tex:258 | § Programs the System Rejects | `fl_map` | Lemma | `theories/static/FactTheory.v:126` |
| 4-extensions.tex:261 | § Programs the System Rejects | `isvar_const` | Lemma | `theories/examples/Rejected.v:47` |
| 4-extensions.tex:262 | § Programs the System Rejects | `world_wf` | Record | `theories/relation/Worlds.v:92` |
| 4-extensions.tex:263 | § Programs the System Rejects | `rr_R_po` | Lemma | `theories/examples/Rejected.v:51` |
| 4-extensions.tex:274 | Theorem (A box needs its constraint) | `ord_no_constraint` | Lemma | `theories/examples/Rejected.v:244` |
| 4-extensions.tex:290 | Theorem (A box needs its constraint) | `ordered_typed` | Lemma | `theories/examples/Ordered.v:29` |
| 4-extensions.tex:294 | § Programs the System Rejects | `ord_R` | Definition | `theories/examples/Rejected.v:230` |
| 4-extensions.tex:300 | § Programs the System Rejects | `ord_R_po` | Lemma | `theories/examples/Rejected.v:238` |
| 4-extensions.tex:302 | § Programs the System Rejects | `bcs_open_nil` | Lemma | `theories/static/PointSubst.v:176` |
| 4-extensions.tex:307 | Theorem (A reversed agent) | `sched_rev_underivable` | Lemma | `theories/examples/Rejected.v:182` |
| 4-extensions.tex:307 | Theorem (A reversed agent) | `ms_rev_underivable` | Lemma | `theories/examples/Rejected.v:193` |
| 4-extensions.tex:325 | § Programs the System Rejects | `sl_trans` | Lemma | `theories/static/FactTheory.v:165` |
| 4-extensions.tex:325 | § Programs the System Rejects | `sl_eqr` | Lemma | `theories/static/FactTheory.v:163` |
| 4-extensions.tex:325 | § Programs the System Rejects | `se_sym` | Constructor | `theories/static/FactTheory.v:110` |
| 4-extensions.tex:332 | Theorem (A cyclic forwarding) | `badlink_underivable` | Lemma | `theories/examples/Rejected.v:204` |
| 4-extensions.tex:334 | Theorem (A cyclic forwarding) | `badlink_main` | Definition | `theories/examples/Rejected.v:152` |
| 4-extensions.tex:349 | § Programs the System Rejects | `blocked_main` | Definition | `theories/examples/Rejected.v:147` |
| 4-extensions.tex:362 | Theorem (A fragment of PGV) | `pgv_deadlock_free_source` | Theorem | `theories/pgv/PGVSimulation.v:873` |
| 4-extensions.tex:365 | Theorem (A fragment of PGV) | `pgv_mono` | Fixpoint | `theories/pgv/PGVTypes.v:109` |
| 4-extensions.tex:365 | Theorem (A fragment of PGV) | `pgv_typed` | Inductive | `theories/pgv/PGVTyping.v:81` |
| 4-extensions.tex:374 | § Priority Systems Embedded | `Wpgv` | Definition | `theories/pgv/PGVWorld.v:166` |
| 4-extensions.tex:375 | § Priority Systems Embedded | `Wpgv_strict` | Lemma | `theories/pgv/PGVWorld.v:174` |
| 4-extensions.tex:376 | § Priority Systems Embedded | `pgv_translate` | Theorem | `theories/pgv/PGVTranslate.v:276` |
| 4-extensions.tex:379 | § Priority Systems Embedded | `ptyped_closed` | Lemma | `theories/examples/ExampleTools.v:511` |
| 4-extensions.tex:379 | § Priority Systems Embedded | `pgv_deadlock_free` | Theorem | `theories/pgv/PGVTranslate.v:390` |
| 4-extensions.tex:383 | § Priority Systems Embedded | `pgv_eta` | Fixpoint | `theories/pgv/PGVTranslate.v:46` |
| 4-extensions.tex:385 | § Priority Systems Embedded | `rel` | Inductive | `theories/pgv/PGVSimulation.v:30` |
| 4-extensions.tex:385 | § Priority Systems Embedded | `rel_eta` | Lemma | `theories/pgv/PGVSimulation.v:50` |
| 4-extensions.tex:387 | § Priority Systems Embedded | `sim_step` | Lemma | `theories/mp/MP2Simulation.v:980` |
| 4-extensions.tex:387 | § Priority Systems Embedded | `sim_star` | Lemma | `theories/mp/MP2Simulation.v:1036` |
| 4-extensions.tex:389 | § Priority Systems Embedded | `norm` | Lemma | `theories/pgv/PGVSimulation.v:635` |
| 4-extensions.tex:391 | § Priority Systems Embedded | `final` | Lemma | `theories/mp/MP2Simulation.v:1150` |
| 4-extensions.tex:396 | § Priority Systems Embedded | `pgv_typed` | Inductive | `theories/pgv/PGVTyping.v:81` |
| 4-extensions.tex:410 | § Priority Systems Embedded | `cx1_rejected` | Lemma | `theories/pgv/PGVExamples.v:286` |
| 4-extensions.tex:410 | § Priority Systems Embedded | `cx2_rejected` | Lemma | `theories/pgv/PGVExamples.v:275` |
| 4-extensions.tex:413 | § Priority Systems Embedded | `pgv_ex21_deadlock_free` | Theorem | `theories/pgv/PGVExamples.v:181` |
| 4-extensions.tex:414 | § Priority Systems Embedded | `pgv_deleg_deadlock_free` | Theorem | `theories/pgv/PGVExamples.v:214` |
| 4-extensions.tex:415 | § Priority Systems Embedded | `pgv_link_deadlock_free` | Theorem | `theories/pgv/PGVExamples.v:241` |
| 4-extensions.tex:417 | Theorem (Padovani and Novara) | `pn_deadlock_free_source` | Theorem | `theories/pn/PNSimulation.v:1245` |
| 4-extensions.tex:426 | § Priority Systems Embedded | `pn_translate_source` | Theorem | `theories/pn/PNTranslate.v:1017` |
| 4-extensions.tex:427 | § Priority Systems Embedded | `Crel` | Definition | `theories/mp/MP2World.v:391` |
| 4-extensions.tex:427 | § Priority Systems Embedded | `Crel_acyclic` | Lemma | `theories/pn/PNWorld.v:246` |
| 4-extensions.tex:429 | § Priority Systems Embedded | `pn_deadlock_free` | Theorem | `theories/pn/PNTranslate.v:1027` |
| 4-extensions.tex:434 | § Priority Systems Embedded | `trel` | Inductive | `theories/pn/PNSimulation.v:104` |
| 4-extensions.tex:434 | § Priority Systems Embedded | `trel_of_typed` | Lemma | `theories/pn/PNSimulation.v:433` |
| 4-extensions.tex:435 | § Priority Systems Embedded | `trel_subst` | Lemma | `theories/pn/PNSimulation.v:294` |
| 4-extensions.tex:436 | § Priority Systems Embedded | `fwd_rt` | Lemma | `theories/mp/MP2Simulation.v:868` |
| 4-extensions.tex:437 | § Priority Systems Embedded | `src_progress` | Lemma | `theories/pn/PNSimulation.v:598` |
| 4-extensions.tex:440 | § Priority Systems Embedded | `pn_deadlock_free_src` | Definition | `theories/pn/PNSemantics.v:135` |
| 4-extensions.tex:442 | § Priority Systems Embedded | `fixlam` | unresolved | **(no declaration)** |
| 4-extensions.tex:446 | § Priority Systems Embedded | `fibo_deadlock_free_src` | Theorem | `theories/pn/PNSimulation.v:1265` |
| 4-extensions.tex:446 | § Priority Systems Embedded | `pipe_deadlock_free_src` | Theorem | `theories/pn/PNSimulation.v:1270` |
| 4-extensions.tex:464 | § Priority Systems Embedded | `crel_hold` | Lemma | `theories/mp/MP2Translate.v:1163` |
| 7-appendix.tex:285 | § Duality and Equivalence of Recursive Session Types | `dual` | Fixpoint | `theories/types/Types.v:626` |
| 7-appendix.tex:299 | § Duality and Equivalence of Recursive Session Types | `SVarD` | Constructor | `theories/types/Types.v:207` |
| 7-appendix.tex:300 | § Duality and Equivalence of Recursive Session Types | `sflip_ty` | Fixpoint | `theories/types/Types.v:584` |
| 7-appendix.tex:308 | § Duality and Equivalence of Recursive Session Types | `sdual_seq_dual` | Lemma | `theories/types/SessionEquiv.v:399` |
| 7-appendix.tex:335 | Lemma | `vred_reduction` | Lemma | `theories/lang/Harmony.v:176` |
| 7-appendix.tex:345 | § Pure reduction | `head_red_head_step` | Lemma | `theories/lang/Harmony.v:170` |
| 7-appendix.tex:345 | § Pure reduction | `head_step_beta_head_red` | Lemma | `theories/lang/Harmony.v:173` |
| 7-appendix.tex:347 | § Pure reduction | `fill_tstep` | Lemma | `theories/lang/Harmony.v:132` |
| 7-appendix.tex:349 | § Pure reduction | `tstep_fill_decomp` | Lemma | `theories/lang/Harmony.v:141` |
| 7-appendix.tex:366 | Reduction semantics | `red` | Inductive | `theories/lang/Harmony.v:61` |
| 7-appendix.tex:416 | § Harmony | `fill_tstep` | Lemma | `theories/lang/Harmony.v:132` |
| 7-appendix.tex:418 | § Harmony | `tstep_fill_decomp` | Lemma | `theories/lang/Harmony.v:141` |
| 7-appendix.tex:420 | § Harmony | `harmony_forward` | Theorem | `theories/lang/Harmony.v:190` |
| 7-appendix.tex:432 | § Harmony | `harmony_backward` | Theorem | `theories/lang/Harmony.v:230` |
| 7-appendix.tex:438 | § Harmony | `head_step_link_inv` | Lemma | `theories/lang/Harmony.v:224` |
| 7-appendix.tex:440 | § Harmony | `upair_eq_inv` | Lemma | `theories/lang/Semantics.v:148` |
<!-- claims:end -->
