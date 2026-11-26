# Frozen copy of the paper before the end-points change (commit 2b31d8b).
# rocqrefs.tex is kept as is, so the links stay pinned to that commit.
.PHONY: all clean
all: main.pdf
main.pdf: $(wildcard *.tex) $(wildcard *.sty) main.bib
	latexmk -pdf -interaction=nonstopmode main.tex
clean:
	latexmk -C
