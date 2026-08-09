# Paper sources

The LaTeX sources live here; the mechanization lives in `theories/`.

## Citing the mechanization

Write `\rocq{fundamental_proc}` in the text. It typesets the name and
links to the declaration. For a different link text use
`\rocqas{Theorem 3.13}{fundamental_proc}`.

References resolve **by name**, through `rocqrefs.tex`:

```sh
python3 paper/rocqrefs.py gen      # regenerate after editing theories/
python3 paper/rocqrefs.py check    # fail on references that no longer exist
```

`gen` records the current file and line of every top-level declaration,
so a lemma may move within its file without rotting the link. Renaming
or deleting one makes `check` fail and, if `rocqrefs.tex` is stale, makes
the LaTeX build fail — which is the point: a paper claim that cites a
lemma that no longer exists should not compile.

Run `check` in CI alongside `make`.

## Anonymity

`\rocqbase` in `rocqrefs.sty` is the only place the artifact's location
appears. Leave it empty and the names typeset as inert `\texttt`; set it
to an [Anonymous GitHub](https://anonymous.4open.science/) mirror for
submission, and to the real repository for the camera-ready. Nothing
else in the paper changes between the two builds.

```latex
\renewcommand{\rocqbase}{https://anonymous.4open.science/r/XXXXXX/}
```

Anonymous GitHub serves `.../r/<id>/theories/Junk.v#L816`, which is the
shape `rocqdef` emits, so the anchors work unchanged.
