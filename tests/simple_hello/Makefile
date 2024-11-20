# This is probably the simplest makefile to build an F* application, and can be adapted easily.
# We should not need to include any other internal makefiles.
# Dune also works fine under the --ocamlenv.

FSTAR ?= ../../bin/fstar.exe

all: Hello.test

Hello.test: Hello.exe Hello.byte
	./Hello.exe  | grep "Hello F\*!"
	./Hello.byte | grep "Hello F\*!"

%.ml: %.fst
	$(FSTAR) --codegen OCaml $< --extract $*

%.exe: %.ml
	$(FSTAR) --ocamlopt $< -o $@

%.byte: %.ml
	$(FSTAR) --ocamlc $< -o $@

clean:
	rm -f *.ml *.exe *.byte *.cm* *.o
