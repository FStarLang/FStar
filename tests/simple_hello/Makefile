# This is probably the simplest makefile to build an F* application, and can be adapted easily.
# We should not need to include any other internal makefiles.
# Dune also works fine under the --ocamlenv.

# In this repository, we inherit this variable. Externally we
# just take fstar.exe from the PATH.
FSTAR_EXE ?= fstar.exe

all: Hello.test

Hello.test: Hello.exe Hello.byte
	./Hello.exe  | grep "Hello F\*!"
	./Hello.byte | grep "Hello F\*!"

%.ml: %.fst
	$(FSTAR_EXE) --codegen OCaml $< --extract $* --z3version 4.13.3

%.exe: %.ml
	$(FSTAR_EXE) --ocamlopt $< -o $@

%.byte: %.ml
	$(FSTAR_EXE) --ocamlc $< -o $@

clean:
	rm -f *.ml *.exe *.byte *.cm* *.o
