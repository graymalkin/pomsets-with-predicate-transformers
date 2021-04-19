all:
	dune build
	@echo ""
	dune runtest
	@echo ""

clean:
	dune clean