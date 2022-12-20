include ../Makefile.include

ifeq ($(OS),Windows_NT)
  OCAMLPATH := $(shell cygpath -m $(FSTAR_HOME)/bin);$(OCAMLPATH)
else
  OCAMLPATH := $(FSTAR_HOME)/bin:$(OCAMLPATH)
endif

plugin: _output/_build/Pulse_Main.cmxs

_output/_build/Pulse_Main.cmxs: extract_all
	(cd _output; OCAMLPATH="$(OCAMLPATH)" ocamlbuild -use-ocamlfind -pkg fstar-tactics-lib Pulse_Main.cmxs -cflags -w,-8)

.PHONY: plugin
