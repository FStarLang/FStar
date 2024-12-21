FSTAR_DEFAULT_ARGS=
ifdef FSTAR_HOME
  ULIB_ML=$(FSTAR_HOME)/ulib/ml
  FSTARLIB_DIR=$(FSTAR_HOME)/lib/fstar/lib
else
  FSTAR_PREFIX=$(dir $(shell which fstar.exe))/..
  ULIB_ML=$(FSTAR_PREFIX)/lib/fstar/ml
  FSTARLIB_DIR=$(FSTAR_PREFIX)/lib/fstar/lib
endif
FSTARLIB=$(FSTARLIB_DIR)/fstar_lib.cmxa

# Left as an example if we were to add multiple versions of fstar ulib
# ifeq ($(MEM),HST)
#	OCAML_DEFAULT_FLAGS=-predicates hyperstack
# endif

ifdef FSTAR_HOME
  WITH_OCAMLPATH=OCAMLPATH=$(FSTAR_HOME)/lib
else
  WITH_OCAMLPATH=
endif
OCAMLOPT_BARE=$(WITH_OCAMLPATH) ocamlfind opt
OCAMLOPT_=$(OCAMLOPT_BARE) -package fstar.lib -linkpkg -g
OCAMLOPT=$(OCAMLOPT_) $(OCAML_DEFAULT_FLAGS)
OCAMLC_=$(WITH_OCAMLPATH) ocamlfind c -package fstar.lib -linkpkg -g
OCAMLC=$(OCAMLC_) $(OCAML_DEFAULT_FLAGS)
