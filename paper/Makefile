# Build the paper and keep its links to the mechanization honest.
.PHONY: all refs check clean

all: main.pdf

# The citation table must exist before LaTeX runs.
main.pdf: rocqrefs.tex $(wildcard *.tex) $(wildcard *.sty) main.bib
	latexmk -pdf -interaction=nonstopmode main.tex

rocqrefs.tex:
	python3 rocqrefs.py gen

# Regenerate after any change to theories/ -- the permalinks pin HEAD.
refs:
	python3 rocqrefs.py gen

# Fail if any \rocq{...} names a declaration that no longer exists.
check:
	python3 rocqrefs.py check

clean:
	latexmk -C
	rm -f rocqrefs.tex
