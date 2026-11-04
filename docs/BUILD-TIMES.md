# Build times

Clean build wall-clock dropped from 741 s to 631 s (minus 15%) on a 4-core cloud container, `make -j4`, Rocq 9.2.0, stdpp 1.13.0, OCaml 5.3.0. The critical path dropped from 716 s to 605 s. Total CPU dropped from 946 s to 847 s.

The build is serial in practice. The critical path is 97% of the wall-clock before and 96% after, so `-j` beyond 2 or 3 buys almost nothing. Only proof time on the chain Syntax → … → JunkRenaming → Internalize → ConnectCut → ConnectSteps → PConnect → PTerm → … → MP3Simulation shortens the build.

Measured with `make -j4 TIMED=1 TIMING=1` (per-file real time, per-sentence `.v.timing` files). Unchanged files vary by up to 9% between the two runs (JunkRenaming 119 s and 129 s), so differences below that are noise.

## Changes

All edits sit inside proof bodies, except one new tactic `mtrim` in ConnectSteps.v. No statement, definition, notation or name changed.

| file | lemma | before (s) | after (s) | change |
|---|---|---:|---:|---|
| lang/Syntax.v | `fchans_subst` | 23.8 | 2.6 | per-constructor goal selectors replace `try (...; set_solver); try set_solver`, whose failing branches cost 20 s |
| invariance/PointRenaming.v | `heads_sw`, `roots_sw_mut` | 24.0 | 2.2 | per-constructor goal selectors replace failing `try set_solver` passes |
| composition/ConnectSteps.v | `cross_msg` | 111.5 | 62.3 | new tactic `mtrim` clears hypotheses that `mpoint` never uses before the three `mpoint` calls, so `rewrite ... in *` runs over 30 hypotheses instead of 90 |
| composition/PConnect.v | `conn_level` | 58.7 | 2.9 | `clear -HΣs` before each `multiset_solver`, which otherwise processes the whole context |

## Per file, before and after

| file | before (s) | after (s) |
|---|---:|---:|
| composition/ConnectSteps.v | 143.9 | 97.5 |
| invariance/JunkRenaming.v | 118.8 | 129.1 |
| composition/ConnectCut.v | 105.7 | 115.0 |
| composition/PTerm.v | 77.5 | 80.4 |
| composition/PConnect.v | 59.9 | 4.3 |
| invariance/PointRenaming.v | 37.8 | 16.4 |
| composition/Internalize.v | 34.8 | 38.1 |
| lang/Syntax.v | 29.2 | 8.7 |
| mp/MP3Translate.v | 19.7 | 21.4 |
| examples/cfst/CfstScheduler.v | 13.8 | 14.1 |
| invariance/PointConversion.v | 12.5 | 13.6 |
| mp/MP2Translate.v | 12.2 | 12.7 |
| rules/Bind.v | 12.1 | 12.2 |
| composition/ReadyChain.v | 11.8 | 12.4 |
| pgv/PGVSimulation.v | 10.0 | 10.2 |
| mp/MP3Simulation.v | 9.1 | 9.3 |
| mp/MP2Simulation.v | 9.1 | 9.8 |
| pn/PNSimulation.v | 8.6 | 9.1 |
| pgv/PGVFalling.v | 8.6 | 9.1 |
| lang/Safety.v | 6.9 | 7.6 |
| mp/MPTranslate.v | 6.5 | 6.7 |
| examples/cfst/CfstDeadlock.v | 6.4 | 6.5 |
| examples/cfst/TreeCopy.v | 5.9 | 6.1 |
| mp/MPRounds.v | 5.9 | 6.0 |
| composition/PConnectN.v | 5.7 | 6.2 |
| all 114 files, CPU sum | 946 | 847 |

Critical path before (file, seconds, cumulative):
```
  lang/Syntax                                  29.2  (cum    29.2)
  lang/Semantics                                3.0  (cum    32.2)
  lang/Safety                                   6.9  (cum    39.1)
  relation/Readiness                            0.9  (cum    40.0)
  relation/LogicalRelation                      2.9  (cum    42.9)
  invariance/PointRenaming                     37.8  (cum    80.7)
  invariance/EquivInvariance                    2.8  (cum    83.5)
  invariance/Monotonicity                       3.0  (cum    86.4)
  invariance/PointConversion                   12.5  (cum    98.9)
  invariance/ChannelRenaming                    2.3  (cum   101.2)
  invariance/JunkRenaming                     118.8  (cum   220.1)
  composition/Internalize                      34.8  (cum   254.8)
  composition/ConnectCut                      105.7  (cum   360.5)
  composition/ConnectSteps                    143.9  (cum   504.4)
  composition/PConnect                         59.9  (cum   564.4)
  composition/PTerm                            77.5  (cum   641.8)
  rules/Bind                                   12.1  (cum   653.9)
  rules/TermRules                               4.7  (cum   658.5)
  rules/BoxRules                                1.3  (cum   659.8)
  rules/ExRules                                 2.1  (cum   661.9)
  rules/SemanticRules                           1.3  (cum   663.2)
  static/FactTheory                             1.4  (cum   664.6)
  static/PointSubst                             2.7  (cum   667.3)
  static/Typing                                 3.3  (cum   670.6)
  static/Source                                 1.6  (cum   672.2)
  static/Fundamental                            4.1  (cum   676.3)
  examples/ExampleTools                         3.8  (cum   680.1)
  examples/cfst/CfstTools                       1.6  (cum   681.7)
  mp/MP3World                                   1.7  (cum   683.4)
  mp/MP3Typing                                  1.1  (cum   684.5)
  mp/MP3Translate                              19.7  (cum   704.2)
  mp/MP3Examples                                2.8  (cum   707.0)
  mp/MP3Simulation                              9.1  (cum   716.1)
```

Critical path after (file, seconds, cumulative):
```
  lang/Syntax                                   8.7  (cum     8.7)
  lang/Semantics                                3.4  (cum    12.1)
  lang/Safety                                   7.6  (cum    19.7)
  relation/Readiness                            1.0  (cum    20.7)
  relation/LogicalRelation                      3.1  (cum    23.8)
  invariance/PointRenaming                     16.4  (cum    40.2)
  invariance/EquivInvariance                    3.2  (cum    43.4)
  invariance/Monotonicity                       3.4  (cum    46.8)
  invariance/PointConversion                   13.6  (cum    60.4)
  invariance/ChannelRenaming                    2.5  (cum    62.9)
  invariance/JunkRenaming                     129.1  (cum   192.0)
  composition/Internalize                      38.1  (cum   230.1)
  composition/ConnectCut                      115.0  (cum   345.1)
  composition/ConnectSteps                     97.5  (cum   442.7)
  composition/PConnect                          4.3  (cum   446.9)
  composition/PTerm                            80.4  (cum   527.3)
  rules/Bind                                   12.2  (cum   539.5)
  rules/TermRules                               4.8  (cum   544.3)
  rules/BoxRules                                1.4  (cum   545.7)
  rules/ExRules                                 2.2  (cum   547.9)
  rules/SemanticRules                           1.3  (cum   549.2)
  static/FactTheory                             1.4  (cum   550.6)
  static/PointSubst                             2.9  (cum   553.5)
  static/Typing                                 3.4  (cum   556.8)
  static/Source                                 1.6  (cum   558.5)
  static/Fundamental                            4.0  (cum   562.5)
  examples/ExampleTools                         4.0  (cum   566.5)
  examples/cfst/CfstTools                       1.7  (cum   568.2)
  mp/MP3World                                   1.6  (cum   569.8)
  mp/MP3Typing                                  1.1  (cum   570.9)
  mp/MP3Translate                              21.4  (cum   592.4)
  mp/MP3Examples                                3.1  (cum   595.5)
  mp/MP3Simulation                              9.3  (cum   604.8)
```

## Remaining hot spots (not done)

Per-lemma times after this branch, from the `.v.timing` files. These are the next candidates, all on the critical path.

| file | lemma | s | cause |
|---|---|---:|---|
| invariance/JunkRenaming.v | `Prel_junk` | 75 | about 200 `set_solver`/`naive_solver` calls of 1 to 5 s each over a large context, no single hot spot |
| composition/ConnectCut.v | `ext_recv`, `ext_send` | 49, 35 | `mpoint` calls of 2 to 8 s each, same cause as `cross_msg`. `mtrim; mpoint` applies but each call needs a test |
| composition/PTerm.v | `link_env` | 44 | many `tlk` calls of 2 to 4 s |
| composition/ConnectSteps.v | `cross_msg` | 62 | two 8-way `destruct (decide ...); set_solver` blocks at 11 s each, one 8.7 s `multiset_solver` |
| invariance/JunkRenaming.v | `rel_fuse` | 14 | |

## Checks

Full clean build green after the changes. `Print Assumptions` on `soundness`, `soundness_source` and all 91 `*_deadlock_free*` theorems (93 in total, including the `*_not_deadlock_free` counterexamples) prints "Closed under the global context" for each.
