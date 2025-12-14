# In this repository, we inherit this variable. Externally we
# just take fstar.exe from the PATH.
FSTAR_EXE ?= fstar.exe

.PHONY: all
all: run
ifneq ($(OS),Windows_NT) # See comment in ../simple_hello/Makefile
all: run.bc
endif

%.checked: %
	$(FSTAR_EXE) $< --cache_checked_modules --ext optimize_let_vc --ext fly_deps

%.ml: %.fst.checked
	$(FSTAR_EXE) --codegen OCaml $<

bin/hello.exe: Hello.ml
	$(FSTAR_EXE) --ocamlenv dune build @install --profile=release
	$(FSTAR_EXE) --ocamlenv dune install --prefix=.

.PHONY: run
run: bin/hello.exe
	./bin/hello.exe | grep "Hi!"

run.bc: bin/hello.exe
	# Find a way to install this? dune install skips the bytecode
	$(FSTAR_EXE) --ocamlenv dune exec ./hello.bc | grep "Hi!"

clean:
	dune clean

# Keep intermediate files
.SECONDARY:
