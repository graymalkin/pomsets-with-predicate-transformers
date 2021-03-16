SOURCE_FILES = src/*.ml src/*.mli \
  src/parse/*.ml src/parse/*.mll src/parse/*.mly \
	src/latex/*.ml

%.byte: $(SOURCE_FILES)
	ocamlbuild -use-ocamlfind $@

%.native: $(SOURCE_FILES)
	ocamlbuild -use-ocamlfind $@

all: pomsets.byte pomsets.native

clean:
	ocamlbuild -clean
