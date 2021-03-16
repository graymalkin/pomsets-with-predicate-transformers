TOOL = ../pomsets.native
OPTIONS = --tex
TEX_OPTIONS = --interaction=batchmode
TEMPLATE = ./latex-template/template.tex

PROGRAMS = $(wildcard tests/paper-examples/*.lit)
TEX_SOURCES = $(shell echo $(patsubst %.lit,diagrams/%.tex,$(PROGRAMS)) | tr ' ' '\n' | sort -V)

.PRECIOUS: $(TOOL)

all: $(TEMPLATE) $(TOOL) $(TEX_SOURCES) 

$(TOOL):
	make -C ..

diagrams/%.tex: %.lit $(TOOL)
	@mkdir -p $(dir $@)
	$(OCAMLRUNPARAM) $(TOOL) $(OPTIONS) $< > $@

clean:
	rm -rf $(TEX_SOURCES)
