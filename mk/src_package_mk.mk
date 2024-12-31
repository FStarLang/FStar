# This makefile is for OCaml source distributions and is
# modeled after stage{1,2}/Makefile, but
# 1- is standalone, does use common.mk or others
# 2- does not install the library as it will not be there on
#    OCaml source distributions
#
# FSTAR_DUNE_OPTIONS += --no-print-directory
# FSTAR_DUNE_OPTIONS += --display=quiet

FSTAR_DUNE_BUILD_OPTIONS := $(FSTAR_DUNE_OPTIONS)

.NOTPARALLEL:
# Sorry, but dune seems to get confused when its OCAMLPATH is changing

.DEFAULT_GOAL:= all

.PHONY: _force
_force:

build:
	dune build --root=dune $(FSTAR_DUNE_BUILD_OPTIONS)

install_bin: build
	dune install --root=dune --prefix=$(CURDIR)/out

install_lib:
	# Install library (cp -u: don't copy unless newer)
	mkdir -p out/ulib
	cp -t out/lib/fstar ulib/*.fst
	cp -t out/lib/fstar ulib/*.fsti
	cp -t out/lib/fstar ulib/fstar.include
	cp -r -t out/lib/fstar ulib/experimental
	cp -r -t out/lib/fstar ulib/legacy

check_lib: install_bin install_lib
	mkdir -p out/lib/fstar/.checked
	env \
	  SRC=ulib/ \
	  FSTAR_EXE=out/bin/fstar.exe \
	  CACHE_DIR=out/lib/fstar/.checked \
	  TAG=lib \
	  CODEGEN=none \
	  OUTPUT_DIR=none \
	  $(MAKE) -f mk/lib.mk verify
	# No need for the depend file
	rm -f out/lib/fstar/.checked/.dependlib

clean: _force
	dune clean $(FSTAR_DUNE_OPTIONS) --root=dune
	rm -rf $(CURDIR)/out

all: check_lib
