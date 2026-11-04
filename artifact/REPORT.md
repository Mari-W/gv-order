# Artifact report, 2026-11-04

What was added, all outside `theories/` and `paper/`

- `spo-lr-df.opam` (rocq-core 9.2.0, rocq-stdlib 9.2.0, rocq-stdpp 1.13.0)
  and `spo-lr-df.opam.locked` (every dependency pinned, OCaml 5.3.0).
- `Dockerfile` and `.dockerignore`, building from `ubuntu:24.04`.
- `Makefile.local` with the target `make check`, read by the generated
  `Makefile`.
- `artifact/check.py`, the assumption check behind `make check`.
- `artifact/claims.py`, the generator of the paper-to-Rocq table.
- `.github/workflows/build.yml`, the CI workflow.
- `ARTIFACT.md`, the artifact README.

What was tested

| Test | Result |
|---|---|
| opam switch from scratch (opam 2.1.5, OCaml 5.3.0, locked dependencies) | passed, 10 min |
| `make -j4` in a fresh clone | passed, 114 files, 13 min wall, 1.0 GB per process |
| `make check` | passed, 452 of 452 names closed, 7.5 min |
| `make check` on a copy with one `Admitted` theorem and one theorem using an `Axiom` | failed as intended, both reported `OPEN`, exit 1 |
| `docker build` from scratch | passed, 33 min, image 2.3 GB |
| `docker run` of the image | shell in the built tree, Rocq 9.2 |
| `actionlint` 1.7.7 on the workflow | no findings |
| GitHub Actions run 9, no cache | passed, 34 min |
| GitHub Actions run 10, cached switch | CI_RESULT |

Two deviations from the plain setup in this sandbox. Docker Hub
rate limited the pull of `ubuntu:24.04`, so the Docker test used the same
image from `public.ecr.aws` with the sandbox proxy's CA added
(`--build-arg BASE=...`). The sandbox proxy blocks GitHub release archives,
so the lockfile takes rocq-stdpp 1.13.0 from the upstream GitLab archive of
tag `stdpp-1.13.0` (`pin-depends`). GitHub Actions used the same lockfile.

Found in the paper, not changed

- Five `\rocq{...}` references name no declaration: `kfw_ok`, `kfw_sub`,
  `kfw_typed`, `kfw_deadlock_free` (4-extensions.tex:160 to 165, the
  KobForwarder declarations are named `fw_*` again on `main`) and `fixlam`
  (4-extensions.tex:442, removed by commit 7f61a5c).
- 18 cited names are declared in more than one file, so their permalinks
  can point at the wrong file (ARTIFACT.md, section 4.2). `fw_main`,
  `fw_sub` and `fw_typed` resolve to `Forwarder.v` where the text about
  Kobayashi's forwarder means `KobForwarder.v`.
