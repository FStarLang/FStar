FSTAR_EXE ?= ../../bin/fstar.exe

.PHONY: all
all: run

Hello.ml: Hello.fst
	$(FSTAR_EXE) --codegen OCaml Hello.fst --extract Hello

bin/hello.exe: Hello.ml
	$(FSTAR_EXE) --ocamlenv dune build @install --profile=release
	$(FSTAR_EXE) --ocamlenv dune install --prefix=.

.PHONY: run
run: bin/hello.exe
	./bin/hello.exe | grep "Hi!"
