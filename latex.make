include .rc.make

subdirs := src/ src/Examples/
sources := $(wildcard $(addsuffix *.lagda.tex,$(subdirs)))
renamed := $(sources:%.lagda.tex=%.tex)
moved   := $(renamed:src/%=$(LATEX-OUTPUT-DIR)%)

$(moved): $(LATEX-OUTPUT-DIR)%.tex: src/%.lagda.tex
	stack exec agda -- --latex-dir=$(LATEX-OUTPUT-DIR) --latex $<

.PHONY: all clean
all: $(moved)
clean: rm -rf $(LATEX-OUTPUT-DIR)