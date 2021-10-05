TOOL = ../_build/default/src/pomsets.exe
OPTIONS ?= --tex --complete
TEX_OPTIONS = --interaction=batchmode
export TEXINPUTS := $(abspath ./latex-template/):${TEXINPUTS}
PREAMBLE = ./latex-template/preamble.tex

PROGRAMS = \
	$(wildcard tests/test6/*.lit) #\
#	$(wildcard tests/jctc/*.lit) 
# $(wildcard tests/*.lit) 

TEX_SOURCES = $(shell echo $(patsubst %.lit,diagrams/%.tex,$(PROGRAMS)) | tr ' ' '\n' | sort -V)
DIAGRAMS = $(shell echo $(patsubst %.lit,diagrams/%.pdf,$(PROGRAMS)) | tr ' ' '\n' | sort -V)
DERIVATIONS = $(shell echo $(patsubst %.lit,diagrams/%.deriv,$(PROGRAMS)) | tr ' ' '\n' | sort -V))

.PRECIOUS: $(TOOL)

all: $(TEMPLATE) tool $(TEX_SOURCES) 

tool:
	make -C ..

check: $(DERIVATIONS)

diagrams/%.deriv : %.lit $(TOOL)
	$(TOOL) --check --complete $< > $@
	@cat $@

diagrams/%.tex: %.lit $(TOOL) $(PREAMBLE)
	@mkdir -p $(dir $@)
	@cat $(PREAMBLE) > $@
	$(TOOL) $(OPTIONS) $< >> $@

diagrams/%.pdf: diagrams/%.tex
	@cd $(dir $@); lualatex $(TEX_OPTIONS) $(notdir $<)

clean:
	rm -rf diagrams/
