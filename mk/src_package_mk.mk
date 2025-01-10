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
	@# Install library and its checked files
	cp -H -p -r ulib out/lib/fstar/ulib
	cp -H -p -r ulib.checked out/lib/fstar/ulib.checked
	echo 'ulib'          > out/lib/fstar/fstar.include
	echo 'ulib.checked' >> out/lib/fstar/fstar.include

check_fstarc: install_bin
	env \
	  SRC=src/ \
	  FSTAR_EXE=out/bin/fstar.exe \
	  CACHE_DIR=fstarc.checked/ \
	  CODEGEN=None \
	  OUTPUT_DIR=None \
	  TAG=fstarc \
	  FSTAR_LIB=$(abspath ulib) \
	  FSTAR_ROOT=$(CURDIR) \
	  $(MAKE) -f mk/fstar-12.mk all-checked

install_fstarc: check_fstarc
	@# Install checked files for FStarC
	mkdir -p out/lib/fstar/fstarc/
	cp -H -p -r src               out/lib/fstar/fstarc/src
	cp -H -p -r fstarc.checked    out/lib/fstar/fstarc/src.checked
	echo 'src'          > out/lib/fstar/fstarc/fstar.include
	echo 'src.checked' >> out/lib/fstar/fstarc/fstar.include

trim: _force
	dune clean $(FSTAR_DUNE_OPTIONS) --root=dune

clean: trim
	rm -rf $(CURDIR)/out

all: install_lib install_fstarc

# Needed for 'opam install'
PREFIX ?= /usr/local
install: install_lib install_fstarc
	cp -r out/* $(PREFIX)
