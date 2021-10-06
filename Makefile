all: build

build:
	dune build
	@echo ""

test:
	dune runtest
	@echo ""

clean:
	dune clean
