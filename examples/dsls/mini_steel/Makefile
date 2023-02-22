include ../Makefile.include

ifeq ($(OS),Windows_NT)
  OCAMLPATH := $(shell cygpath -m $(FSTAR_HOME)/bin);$(OCAMLPATH)
else
  OCAMLPATH := $(FSTAR_HOME)/lib:$(OCAMLPATH)
endif

plugin: verify_all _build/Pulse_Main.cmxs

_build/Pulse_Main.cmxs: extract_all
	(OCAMLPATH="$(OCAMLPATH)" ocamlbuild -I ml -I _output -use-ocamlfind -pkg fstar.lib -use-menhir Pulse_Main.cmxs -cflags -w,-8)

.PHONY: plugin
