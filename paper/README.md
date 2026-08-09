# Paper sources

The LaTeX sources live here; the mechanization lives in `theories/`.

```sh
make -C paper          # build main.pdf (generates rocqrefs.tex first)
make -C paper check    # fail on citations to declarations that no longer exist
make -C paper clean
```

The logo in `rocq-logo.pdf` is the Rocq icon from
[rocq-prover/rocq-prover.org](https://github.com/rocq-prover/rocq-prover.org)
(`asset/logos/icon-rocq-orange.svg`), converted to PDF. Delete it and
the citations fall back to a typeset badge.

## Citing the mechanization

Write `\rocq{fundamental_proc}` in the text. It renders as

> [logo] `Compositionality.v:fundamental_proc`

hyperlinked to that declaration. For different link text use
`\rocqas{Theorem 3.13}{fundamental_proc}`.

The logo comes from `paper/rocq-logo.pdf` (or `.png`) if you drop one
there, and otherwise falls back to a small typeset badge — so the paper
builds with no external assets and no licensing question. Redefine
`\rocqlogo` to override.

References resolve **by name**, through `rocqrefs.tex`:

```sh
python3 paper/rocqrefs.py gen      # regenerate after editing theories/
python3 paper/rocqrefs.py check    # fail on references that no longer exist
```

`gen` records the current file and line of every top-level declaration
**and pins the base URL to the HEAD commit**, so links are permalinks:
they keep pointing at the code the paper described even after the branch
moves on. A lemma may move within its file without rotting the link. Renaming
or deleting one makes `check` fail and, if `rocqrefs.tex` is stale, makes
the LaTeX build fail — which is the point: a paper claim that cites a
lemma that no longer exists should not compile.

Run `check` in CI alongside `make`.

## Anonymity

The base URL is the only place the artifact's location appears.
Regenerate against an [Anonymous GitHub](https://anonymous.4open.science/)
mirror for submission and nothing else in the paper changes:

```sh
python3 paper/rocqrefs.py gen --base https://anonymous.4open.science/r/XXXX/
```

Anonymous GitHub serves `.../r/<id>/theories/Junk.v#L816`, the same anchor
shape as GitHub, so the links work unchanged. With no base at all the
names typeset inert.
