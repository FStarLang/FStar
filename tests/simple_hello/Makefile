# This is probably the simplest makefile to build an F* application, and can be adapted easily.
# We should not need to include any other internal makefiles.
# Dune also works fine under the --ocamlenv.

FSTAR ?= ../../bin/fstar.exe

all: Hello.test

Hello.test: Hello.exe
	./Hello.exe | grep "Hello F\*!"

%.ml: %.fst
	$(FSTAR) --codegen OCaml $< --extract $*

%.exe: %.ml
	$(FSTAR) --ocamlenv ocamlfind ocamlopt -package fstar.lib -linkpkg $< -o $@
