%.byte:
	ocamlbuild -use-ocamlfind $@

%.native:
	ocamlbuild -use-ocamlfind $@

all: pomsets.byte pomsets.native

clean:
	ocamlbuild -clean
