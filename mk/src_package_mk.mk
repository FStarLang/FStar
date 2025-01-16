# This makefile is for OCaml source distributions.
#
# Also note: this Makefile should run in Windows too. Some of the $(call
# cygpath, ..) below are in support of this. Example windows error:
#
# ...
# dune install --root=dune --prefix=/cygdrive/d/a/FStar/FStar/fstar/out
# env \
#   SRC=ulib/ \
#   FSTAR_EXE=out/bin/fstar.exe \
#   CACHE_DIR=ulib.checked \
#   TAG=lib \
#   CODEGEN=none \
#   OUTPUT_DIR=none \
#   make -f mk/lib.mk verify
# mk/lib.mk:3: *** FSTAR_EXE ("out/bin/fstar.exe") does not exist (cwd = /cygdrive/d/a/FStar/FStar/fstar).  Stop.
# ...
#
# I think this is probably a dune bug.

# NOTE: (Guido 2025-01-13) For whatever undebuggable reason, Cygwin make
# (version 4.4.1-1 at least) to (sometimes) freeze , and halt the build.
# Not running this makefile (and sub-makes) in parallel *seems* to help,
# though obviously makes this significantly slower in Windows.
ifeq ($(OS),Windows_NT)
.NOTPARALLEL:
MAYBEJ1=-j1
else
MAYBEJ1=
endif

include mk/common.mk

FSTAR_DUNE_OPTIONS += --no-print-directory
FSTAR_DUNE_OPTIONS += --display=quiet

FSTAR_DUNE_BUILD_OPTIONS := $(FSTAR_DUNE_OPTIONS)
.DEFAULT_GOAL:= all

.PHONY: .force
.force:

# In some places, we need to compute absolute paths, and in a Cygwin
# enviroment we need Windows-style paths (forward slashes ok, but no
# /cygdrive/).
ifeq ($(OS),Windows_NT)
cygpath=$(shell cygpath -m "$(abspath $(1))")
else
cygpath=$(abspath "$(1)")
endif

build:
	$(call msg, "DUNE BUILD")
	dune build --root=dune $(FSTAR_DUNE_BUILD_OPTIONS)

install_bin: build
	$(call msg, "DUNE INSTALL")
	dune install --root=dune --prefix=$(call cygpath,out)

check_lib: install_bin
	$(call msg, "CHECK LIB")
	env \
	  SRC=ulib/ \
	  FSTAR_EXE=$(call cygpath,out/bin/fstar.exe) \
	  CACHE_DIR=ulib.checked \
	  TAG=lib \
	  CODEGEN=none \
	  OUTPUT_DIR=none \
	  FSTAR_ROOT=$(CURDIR) \
	  $(MAKE) -f mk/lib.mk verify $(MAYBEJ1)

install_lib: check_lib
	$(call msg, "INSTALL LIB")
	@# Install library and its checked files
	cp -T -H -p -r ulib out/lib/fstar/ulib
	cp -T -H -p -r ulib.checked out/lib/fstar/ulib.checked
	echo 'ulib'          > out/lib/fstar/fstar.include
	echo 'ulib.checked' >> out/lib/fstar/fstar.include

check_fstarc: install_bin
	$(call msg, "CHECK FSTARC")
	env \
	  SRC=src/ \
	  FSTAR_EXE=$(call cygpath,out/bin/fstar.exe) \
	  CACHE_DIR=fstarc.checked/ \
	  CODEGEN=None \
	  OUTPUT_DIR=None \
	  TAG=fstarc \
	  FSTAR_LIB=$(call cygpath,ulib) \
	  FSTAR_ROOT=$(CURDIR) \
	  $(MAKE) -f mk/fstar-12.mk verify $(MAYBEJ1)
	$(call msg, "DONE CHECK FSTARC")

install_fstarc: check_fstarc
	$(call msg, "INSTALL FSTARC")
	@# Install checked files for FStarC
	mkdir -p out/lib/fstar/fstarc/
	cp -T -H -p -r src               out/lib/fstar/fstarc/src
	cp -T -H -p -r fstarc.checked    out/lib/fstar/fstarc/src.checked
	echo 'src'          > out/lib/fstar/fstarc/fstar.include
	echo 'src.checked' >> out/lib/fstar/fstarc/fstar.include

trim: .force
	$(call msg, "DUNE CLEAN")
	dune clean $(FSTAR_DUNE_OPTIONS) --root=dune

clean: trim
	rm -rf $(CURDIR)/out
	rm -rf ulib.checked
	rm -rf fstarc.checked

all: install_lib install_fstarc

install_fstarc: install_lib
# ^ The windows build in Github actions seems to sporadically
# hang for over an hour, but sometimes works fine. I suspect
# some kind of stupid race, so sequentialize these two install
# phases.

# Needed for 'opam install'
PREFIX ?= /usr/local
install: install_lib install_fstarc
	mkdir -p $(PREFIX)
	cp -r out/* $(PREFIX)

package:
	rm -rf pkgtmp
	mkdir -p pkgtmp
	$(MAKE) install PREFIX=pkgtmp/fstar
	.scripts/bin-install.sh pkgtmp/fstar
	.scripts/mk-package.sh pkgtmp fstar$(FSTAR_TAG)
