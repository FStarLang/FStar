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

include mk/common.mk

FSTAR_DUNE_OPTIONS += --no-print-directory
FSTAR_DUNE_OPTIONS += --display=quiet

FSTAR_DUNE_BUILD_OPTIONS := $(FSTAR_DUNE_OPTIONS)
.DEFAULT_GOAL:= all

.PHONY: .force
.force:

build:
	$(call msg, "DUNE BUILD")
	dune build --root=dune $(FSTAR_DUNE_BUILD_OPTIONS)

install_bin: build
	$(call msg, "DUNE INSTALL")
	dune install --root=dune --prefix=$(call cygpath,out)

minimal: install_bin install_lib_src

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
	  $(MAKE) -f mk/lib.mk verify

install_lib_src:
	$(call msg, "INSTALL LIB SRC")
	@# Install library sources, set up fstar.include
	rm -rf out/lib/fstar/ulib
	mkdir -p out/lib/fstar
	cp -H -p -r ulib out/lib/fstar/ulib
	echo 'ulib'          > out/lib/fstar/fstar.include
	echo 'ulib.checked' >> out/lib/fstar/fstar.include

install_lib: check_lib install_lib_src
	$(call msg, "INSTALL LIB")
	@# Install library checked files. NOTE: We use /. at the end of the
	@# src so that, if the target already exists as a directory, we copy
	@# the *contents* of ulib.checked into it, instead of creating another
	@# ulib.checked under it. In Linux, this can be avoided with the -T
	@# flag, but MacOS does not have it.
	cp -H -p -r ulib.checked/. out/lib/fstar/ulib.checked

check_fstarc: install_bin
	$(call msg, "CHECK FSTARC")
	env \
	  SRC=src/ \
	  FSTAR_EXE=$(call cygpath,out/bin/fstar.exe) \
	  CACHE_DIR=fstarc.checked/ \
	  CODEGEN=none \
	  OUTPUT_DIR=none \
	  TAG=fstarc \
	  FSTAR_LIB=$(call cygpath,ulib) \
	  FSTAR_ROOT=$(CURDIR) \
	  $(MAKE) -f mk/fstar-12.mk verify
	$(call msg, "DONE CHECK FSTARC")

install_fstarc: check_fstarc
	$(call msg, "INSTALL FSTARC")
	@# Install checked files for FStarC
	mkdir -p out/lib/fstar/fstarc/
	@# See note about /. above
	cp -H -p -r src/.               out/lib/fstar/fstarc/src
	cp -H -p -r fstarc.checked/.    out/lib/fstar/fstarc/src.checked
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
## LINES BELOW ADDED BY src-install.sh
export FSTAR_COMMITDATE=2025-12-15 10:20:20 -0800
export FSTAR_COMMIT=2ce4ca2d71973a9f96c84de114fa28e4302ccb74
