SOURCE_FILES = src/*.ml src/*.mli \
  src/parse/*.ml src/parse/*.mll src/parse/*.mly \
	src/latex/*.ml \
	test/*.ml

%.byte: $(SOURCE_FILES)
	ocamlbuild -use-ocamlfind $@

%.native: $(SOURCE_FILES)
	ocamlbuild -use-ocamlfind $@

all: test pomsets.byte pomsets.native

test: test.byte
	./test.byte

clean:
	ocamlbuild -clean
