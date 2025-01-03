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

check_lib: install_bin
	env \
	  SRC=ulib/ \
	  FSTAR_EXE=out/bin/fstar.exe \
	  CACHE_DIR=ulib.checked \
	  TAG=lib \
	  CODEGEN=none \
	  OUTPUT_DIR=none \
	  $(MAKE) -f mk/lib.mk verify

install_lib: check_lib
	@# Install get_fstar_z3 script
	cp get_fstar_z3.sh $(CURDIR)/out/bin
	@# Install library
	cp -H -p -r ulib out/lib/fstar/ulib
	echo 'ulib' >> out/lib/fstar/fstar.include
	rm -f out/lib/fstar/ulib/*.config.json
	@# Install checked files for the library
	mkdir -p out/lib/fstar/ulib/.checked
	cp -p ulib.checked/* out/lib/fstar/ulib/.checked/
	echo '.checked' >> out/lib/fstar/ulib/fstar.include

clean: _force
	dune clean $(FSTAR_DUNE_OPTIONS) --root=dune
	rm -rf $(CURDIR)/out

all: install_lib
