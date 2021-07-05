TOOL = ../_build/default/src/pomsets.exe
OPTIONS = --tex --complete
TEX_OPTIONS = --interaction=batchmode
PREAMBLE = ./latex-template/preamble.tex

PROGRAMS = $(wildcard tests/*.lit)
	# $(wildcard tests/paper-examples/*.lit) \
	# $(wildcard tests/jctc/*.lit) 

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
	@cd $(dir $@); lualatex $(TEX_OPTIONS) $(notdir $@) > /dev/null

clean:
	rm -rf diagrams/
