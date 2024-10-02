
# ifdef FSTAR_HOME
#   ifeq ($(OS),Windows_NT)
#     OCAMLPATH := $(shell cygpath -m $(FSTAR_HOME)/lib);$(OCAMLPATH)
#   else
#     OCAMLPATH := $(FSTAR_HOME)/stage2/lib:$(OCAMLPATH)
#   endif
# endif

FSTAR_OCAML := $(shell $(FSTAR_HOME)/bin/fstar.exe --locate_ocaml)
OCAMLPATH := $(FSTAR_OCAML):$(OCAMLPATH)
# with dune
Main.exe: $(wildcard *.ml)
	OCAMLPATH="$(OCAMLPATH)" dune build
	cp _build/default/Main.exe .

#with ocamlbuild
Main.native: $(wildcard *.ml)
	OCAMLPATH="$(OCAMLPATH)" ocamlbuild -tag thread -use-ocamlfind -quiet -pkg batteries -pkg fstar.lib -cflags -w,-8 Main.native

clean:
	rm -rf _build Main.native Main.exe
