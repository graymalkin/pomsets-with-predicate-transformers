TOOL = ../_build/default/src/pomsets.exe
OPTIONS ?= --tex --complete
TEX_OPTIONS = --interaction=batchmode
export TEXINPUTS := $(abspath ./latex-template/):${TEXINPUTS}
PREAMBLE = ./latex-template/preamble.tex

PROGRAMS = $(wildcard tests/jctc/*.lit)

TEX_SOURCES = $(shell echo $(patsubst %.lit,diagrams/%.tex,$(PROGRAMS)) | tr ' ' '\n' | sort -V)
DIAGRAMS = $(shell echo $(patsubst %.lit,diagrams/%.pdf,$(PROGRAMS)) | tr ' ' '\n' | sort -V)
DERIVATIONS = $(shell echo $(patsubst %.lit,diagrams/%-pwt.deriv,$(PROGRAMS)) | tr ' ' '\n' | sort -V)) \
	$(shell echo $(patsubst %.lit,diagrams/%-pwtc.deriv,$(PROGRAMS)) | tr ' ' '\n' | sort -V))

.PRECIOUS: $(TOOL)

all: $(TEMPLATE) tool $(TEX_SOURCES) 

tool:
	make -C ..

check: $(DERIVATIONS)

diagrams/%-pwt.deriv : %.lit $(TOOL)
	@mkdir -p $(dir $@)
	$(TOOL) --model pwt --time --check --complete $< > $@
	@cat $@

diagrams/%-pwtc.deriv : %.lit $(TOOL)
	@mkdir -p $(dir $@)
	$(TOOL) --model pwtc --time --check --complete $< > $@
	@cat $@

diagrams/%.tex: %.lit $(TOOL) $(PREAMBLE)
	@mkdir -p $(dir $@)
	@cat $(PREAMBLE) > $@
	$(TOOL) $(OPTIONS) $< >> $@

diagrams/%.pdf: diagrams/%.tex
	@cd $(dir $@); lualatex $(TEX_OPTIONS) $(notdir $<)

clean:
	rm -rf diagrams/
