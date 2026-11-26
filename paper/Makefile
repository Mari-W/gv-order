# Build the paper and keep its links to the mechanization honest.
.PHONY: all gen refs anon check clean

all: main.pdf

# The citation table must exist before LaTeX runs.
main.pdf: rocqrefs.tex gen/defs.tex $(wildcard *.tex) $(wildcard *.sty) main.bib
	latexmk -pdf -interaction=nonstopmode main.tex

# The figures, rules, examples and the appendix come from the proof map.
gen/defs.tex: tools/map2tex.py ../docs/explorer/map.json
	python3 tools/map2tex.py

gen:
	python3 tools/map2tex.py

rocqrefs.tex:
	python3 rocqrefs.py gen

# Regenerate after any change to theories/ -- the permalinks pin HEAD.
refs:
	python3 rocqrefs.py gen

# Submission build: anonymous artifact links (set ANON to the real mirror).
ANON ?= https://anonymous.4open.science/r/XXXX/
anon:
	python3 rocqrefs.py gen --base $(ANON)
	latexmk -pdf -interaction=nonstopmode main.tex

# Fail if any \rocq{...} names a declaration that no longer exists.
check:
	python3 rocqrefs.py check

clean:
	latexmk -C
	rm -f rocqrefs.tex
