include ../../Makefile.common
include ../Makefile.include

include $(FSTAR_HOME)/.common.mk

FSTAR_LIB_OCAMLPATH := $(call maybe_cygwin_path,$(FSTAR_HOME)/lib)

ifeq ($(OS),Windows_NT)
  OCAMLPATH := $(FSTAR_LIB_OCAMLPATH);$(OCAMLPATH)
else
  OCAMLPATH := $(FSTAR_LIB_OCAMLPATH):$(OCAMLPATH)
endif

all:
	$(MAKE) all-common
	$(MAKE) plugin
	$(MAKE) -C tests/

plugin: verify_all _build/Pulse_Main.cmxs

_build/Pulse_Main.cmxs: extract_all
	(OCAMLPATH="$(OCAMLPATH)" ocamlbuild -I ml -I _output -use-ocamlfind -pkg fstar.lib -use-menhir Pulse_Main.cmxs -cflags -w,-8)

.PHONY: plugin
