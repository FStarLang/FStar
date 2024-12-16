FSTAR_EXE ?= ../../bin/fstar.exe

.PHONY: all
all: run

Hello.ml: Hello.fst
	$(FSTAR_EXE) --codegen OCaml Hello.fst --extract Hello --z3version 4.13.3

bin/hello.exe: Hello.ml
	$(FSTAR_EXE) --ocamlenv dune build @install --profile=release
	$(FSTAR_EXE) --ocamlenv dune install --prefix=.

.PHONY: run
run: bin/hello.exe
	./bin/hello.exe | grep "Hi!"
	# Find a way to install this? dune install skips the bytecode
	$(FSTAR_EXE) --ocamlenv dune exec ./hello.bc | grep "Hi!"

clean:
	dune clean
