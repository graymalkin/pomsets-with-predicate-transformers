# Predicate Transformers for Relaxed Memory
OCaml implementation of Predicate Transformers for Relaxed Memory.

## Build this tool

This tool has been built against OCaml 4.10.0, other versions of OCaml will probably work.

You will need some libraries:

```bash
opam install dune batteries fmt menhir ocamlgraph ounit2 ppx_deriving
opam install merlin utop ocp-indent # nice to have
```

Then you can build this tool using `dune`.

```bash
dune build
dune runtest
```

The build can be cleaned using `dune clean`.

The dune commands are aliased in a Makefile, under `make all`, `make build`, `make test` and `make clean`, and behave as expected.

## Running the tool

Dune builds the executable at `./_build/default/src/pomsets.exe`.

## Options

```
./_build/default/src/pomsets.exe [OPTIONS] <FILENAME>
  --log        Set the log level as one of {all, debug, warn, error, none} [default: none]
  --log-time   Include time stamps in log output [default: false]
  --program    Interpret a program from the command line.
  --size       Print the number of completed pomsets [default: false]
  --tex        Use LaTeX output [default: false]
  --time       Show execution time [default: false]
  -help        Display this list of options
  --help       Display this list of options
```
