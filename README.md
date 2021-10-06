# Predicate Transformers for Relaxed Memory
OCaml implementation of Predicate Transformers for Relaxed Memory.

## Build this tool

This tool has been built against OCaml 4.10.0, other versions of OCaml will probably work.

You will need some libraries:

```bash
opam install dune batteries fmt menhir ocamlgraph ounit2 z3
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

Dune builds the executable at `./_build/default/src/pomsets.exe`, you will need to pass in a litmus test file. A sample is provided in `demo.lit`.

Litmus tests have 3 sections. 
  1. First an optional configuration section which contains the name of the test, a value set, and optionally a comment.
  2. Second, the program itself written in a simple syntax. Grammar is in `src/parse/Parser.mly`.
  3. Finally, an optional set of assertions in the format `{allow|forbid} (<boolean expression>) [] "<comment>"`. Multiple assertions can be listed, with `;` as a separator.

```
name="Demo"
values={0,1}
comment "Demonstrates simple calculation of dependency"
%%
x := 0;
r1 := x;
if (r1 = 0) {
  y := 1
}
%%
allow (r1 = 0) [] ""
```


## Options

```
./_build/default/src/pomsets.exe [OPTIONS] <FILENAME>
  --check              Check that pomsets generated satisfy the litmus assertion
  --complete           Print only completed pomsets
  --log <level>        Set the log level as one of {all, info, debug, warn, error, none} [default: none]
  --log-time           Include time stamps in log output
  --model <model>      Select a version of the model from {PwT, RC11, MCA1} [default: PwT]
  --program <program>  Interpret a program from the command line.
  --print              Pretty print pomsets
  --size               Print the number of completed pomsets
  --tex                Use LaTeX output
  --time               Show execution time
  -help                Display this list of options
  --help               Display this list of options
```
