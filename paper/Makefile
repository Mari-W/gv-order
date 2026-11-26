# Build the paper and keep its links to the mechanization honest.
# The generators live outside paper/, in .claude/notes/paper.
.PHONY: all gen refs anon check clean

NOTES := ../.claude/notes/paper
MAP2TEX := $(NOTES)/tools/map2tex.py
ROCQREFS := $(NOTES)/rocqrefs.py

all: main.pdf supplement.pdf

# The citation table must exist before LaTeX runs.
main.pdf: rocqrefs.tex gen/defs.tex $(wildcard *.tex) $(wildcard figures/*.tex) $(wildcard *.sty) main.bib
	latexmk -pdf -interaction=nonstopmode main.tex

# The supplement: the example programs and the map blocks the paper does not need.
supplement.pdf: rocqrefs.tex gen/defs.tex supplement.tex mapmacros.tex notation.tex preamble.tex $(wildcard gen/examples/*.tex)
	latexmk -pdf -interaction=nonstopmode supplement.tex

# The figures, rules, examples and the appendix come from the proof map.
gen/defs.tex: $(MAP2TEX) ../docs/explorer/map.json
	python3 $(MAP2TEX)

gen:
	python3 $(MAP2TEX)

rocqrefs.tex:
	python3 $(ROCQREFS) gen

# Regenerate after any change to theories/ -- the permalinks pin HEAD.
refs:
	python3 $(ROCQREFS) gen

# Submission build: anonymous artifact links (set ANON to the real mirror).
ANON ?= https://anonymous.4open.science/r/XXXX/
anon:
	python3 $(ROCQREFS) gen --base $(ANON)
	latexmk -pdf -interaction=nonstopmode main.tex

# Fail if any \rocq{...} names a declaration that no longer exists.
check:
	python3 $(ROCQREFS) check

clean:
	latexmk -C
	rm -f rocqrefs.tex
