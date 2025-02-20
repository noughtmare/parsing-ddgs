SRC := src
SCT := $(SRC)/sections

PDFLATEX = lualatex -output-directory build/ -interaction=nonstopmode -file-line-error
LATEXMK  = latexmk -r $(SRC)/latexmkrc

SOURCES := $(patsubst %.lagda,%.tex,$(wildcard src/sections/*.lagda))

all: document.pdf 

document.pdf: build build/document.tex $(SOURCES) src/references.bib src/unicode.tex
	$(LATEXMK) build/document.tex
	cp build/document.pdf document.pdf

#	 $(PDFLATEX) build/document.tex
#	 bibtex build/document
#	 $(PDFLATEX) build/document.tex
#	 $(PDFLATEX) build/document.tex

# Quick 'n dirty build, intended for use with watch script
quick: build build/document.tex $(SOURCES) src/references.bib src/unicode.tex
	$(PDFLATEX) build/document.tex
	cp build/document.pdf document.pdf

build/document.tex: $(SRC)/document.tex
	cp $(SRC)/document.tex build/document.tex

%.tex: %.lagda
	agda --latex --latex-dir=$(SCT) $<

build:
	mkdir $@

clean:
	$(LATEXMK) -C src/document
	rm -f document.pdf
	rm -rf build
	rm -r $(SCT)/*.tex
.PHONY: all clean
