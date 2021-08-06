TOOL = ../_build/default/src/pomsets.exe
OPTIONS ?= --tex --complete
TEX_OPTIONS = --interaction=batchmode
export TEXINPUTS := $(abspath ./latex-template/):${TEXINPUTS}
PREAMBLE = ./latex-template/preamble.tex

PROGRAMS = $(wildcard tests/*.lit) \
	$(wildcard tests/jctc/*.lit) 

TEX_SOURCES = $(shell echo $(patsubst %.lit,diagrams/%.tex,$(PROGRAMS)) | tr ' ' '\n' | sort -V)
DIAGRAMS = $(shell echo $(patsubst %.lit,diagrams/%.pdf,$(PROGRAMS)) | tr ' ' '\n' | sort -V)

.PRECIOUS: $(TOOL)

all: $(TEMPLATE) tool $(TEX_SOURCES) 

tool:
	make -C ..

diagrams/%.tex: %.lit $(TOOL) $(PREAMBLE)
	@mkdir -p $(dir $@)
	@cat $(PREAMBLE) > $@
	$(TOOL) $(OPTIONS) $< >> $@

diagrams/%.pdf: diagrams/%.tex
	@cd $(dir $@); lualatex $(TEX_OPTIONS) $(notdir $<)

clean:
	rm -rf diagrams/
