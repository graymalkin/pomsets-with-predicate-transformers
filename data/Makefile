TOOL = ../pomsets.native
OPTIONS = --tex
TEX_OPTIONS = --interaction=batchmode
PREAMBLE = ./latex-template/preamble.tex

PROGRAMS = $(wildcard tests/paper-examples/*.lit)
TEX_SOURCES = $(shell echo $(patsubst %.lit,diagrams/%.tex,$(PROGRAMS)) | tr ' ' '\n' | sort -V)
DIAGRAMS = $(shell echo $(patsubst %.lit,diagrams/%.pdf,$(PROGRAMS)) | tr ' ' '\n' | sort -V)

.PRECIOUS: $(TOOL)

all: $(TEMPLATE) tool $(TEX_SOURCES) 

tool:
	make -C ..

diagrams/%.tex: %.lit $(TOOL) $(PREAMBLE)
	@mkdir -p $(dir $@)
	@cat $(PREAMBLE) > $@
	$(OCAMLRUNPARAM) $(TOOL) $(OPTIONS) $< >> $@
	@cd $(dir $@); lualatex $(TEX_OPTIONS) $(notdir $@)

clean:
	rm -rf diagrams/
