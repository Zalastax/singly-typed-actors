include .rc.make

subdirs := src/ src/Examples/ src/Selective/ src/Selective/Examples/
sources := $(wildcard $(subdirs:%=%*.lagda.tex))
renamed := $(sources:%.lagda.tex=%.tex)
moved   := $(renamed:src/%=$(LATEX-OUTPUT-DIR)%)
out-subdirs := $(subdirs:src/%=$(LATEX-OUTPUT-DIR)%)
generated   :=  $(wildcard $(out-subdirs:%=%*.tex))

$(moved): $(LATEX-OUTPUT-DIR)%.tex: src/%.lagda.tex
	stack exec agda -- --latex-dir=$(LATEX-OUTPUT-DIR) --latex $<
	perl postprocess-latex.pl $@ > $(LATEX-OUTPUT-DIR)$*.processed
	mv $(LATEX-OUTPUT-DIR)$*.processed $@

.PHONY: all clean
all: $(moved)
clean:
	rm $(wildcard $(wildcard $(generated)))