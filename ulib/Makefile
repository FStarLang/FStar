.PHONY: all benchmark extra install-fstarlib install-fstar-tactics rebuild clean_checked clean_ocaml clean fstardoc

FSTAR_HOME=..

# Makefile.verify has been split off because it is the actual
# Makefile that is distributed in the binary package. This
# Makefile here is not.

all: .cache
	+$(MAKE) FSTAR_HOME=$(FSTAR_HOME) -f Makefile.verify verify-core

benchmark: .cache
	+$(MAKE) FSTAR_HOME=$(FSTAR_HOME) -f Makefile.verify verify-benchmark

extra: .cache
	+$(MAKE) FSTAR_HOME=$(FSTAR_HOME) -f Makefile.verify verify-extra

.cache:
	mkdir -p .cache

include $(FSTAR_HOME)/ulib/ml/Makefile.include
include $(FSTAR_HOME)/.common.mk

# GM: These dependencies suck, but are needed.
fstarlib.mgen: *.fst *.fsti experimental/*.fst experimental/*.fsti legacy/*.fst legacy/*.fsti
	mkdir -p ml/extracted
	rm -f .depend.extract
	+OUTPUT_DIRECTORY=ml/extracted \
	    EXTRACT_MODULES="--extract '-Prims +FStar +LowStar -FStar.Tactics -FStar.Reflection -FStar.InteractiveHelpers $(NOEXTRACT_MODULES)'" \
	    $(MAKE) -f Makefile.extract all-ml
	# the next cp is done because FStar_Pervasives.ml is needed to bootstrap the compiler
	# we could follow this style for other files too, e.g., FStar_Option.ml
	cp ../src/ocaml-output/FStar_Pervasives.ml ml/extracted
	touch fstarlib.mgen

# NOTE: fstarlib_leftovers.ml takes directories that MUST NOT end with /
FSTARLIB_LEFTOVERS=$(shell ocaml fstarlib_leftovers.ml +ml +ml/extracted -../bin/fstar-compiler-lib)
fstartaclib.mgen: fstarlib.mgen
	mkdir -p tactics_ml/extracted
	rm -f .depend.extract
	+OUTPUT_DIRECTORY=tactics_ml/extracted \
	    CODEGEN=Plugin \
	    EXTRACT_MODULES="--extract '+FStar.Tactics +FStar.Reflection $(NOEXTRACT_MODULES) +Steel.Effect.Common +FStar.InteractiveHelpers'" \
	    $(MAKE) -f Makefile.extract all-ml
	mkdir -p tactics_ml/fstarlib_leftovers
	cp $(FSTARLIB_LEFTOVERS) tactics_ml/fstarlib_leftovers
	touch fstartaclib.mgen

######################################################
# OCaml extraction of fstarlib and fstar-tactics-lib #
######################################################

FSTAR_BIN := $(realpath $(FSTAR_HOME)/bin)
ifeq ($(OS),Windows_NT)
  OCAMLPATH_SEP=;
  FSTAR_BIN := $(shell cygpath -m $(FSTAR_BIN))
else
  OCAMLPATH_SEP=:
endif

OCAMLPATH:=$(FSTAR_BIN)$(OCAMLPATH_SEP)$(OCAMLPATH)

FSTAR_OCAMLBUILD_EXTRAS ?= -cflag -g
OCAMLBUILD=cd ../ && OCAMLPATH="$(OCAMLPATH)" ocamlbuild $(FSTAR_OCAMLBUILD_EXTRAS) -use-ocamlfind

# relative to ulib
DIRS_WITH_FSTARLIB_ML_FILES = ml experimental/ml ml/extracted
DIRS_WITH_TACLIB_ML_FILES = tactics_ml tactics_ml/extracted tactics_ml/fstarlib_leftovers

FSTARLIB_OCAMLBUILD=$(OCAMLBUILD) -build-dir ulib/ml/_build \
  $(addprefix -I ulib/,$(DIRS_WITH_FSTARLIB_ML_FILES))

TACLIB_OCAMLBUILD=$(OCAMLBUILD) -build-dir ulib/tactics_ml/_build \
  $(addprefix -I ulib/,$(DIRS_WITH_TACLIB_ML_FILES))

ml/fstarlib.mllib: fstarlib.mgen $(wildcard $(addsuffix /*.ml,$(DIRS_WITH_FSTARLIB_ML_FILES)))
	./gen_mllib.sh $(DIRS_WITH_FSTARLIB_ML_FILES) > $@

# Please don't create an empty fstartactics.ml: ocamlbuild < 0.11 gives higher
# priority to its cmx -> cmxs rule than to the cmxa -> cmx one, so an empty
# fstartactics.ml will yield an empty fstarlib.cmxs (unless you add a .mldylib).
# (see `https://github.com/ocaml/ocamlbuild/releases/tag/0.11.0')
# ---
# Having to isolate fstarlib_leftovers is unpleasant.  Ideally, we'd much rather
# dynlink fstarlib into the compiler before dynlinking fstartaclib.  But doing
# this naively is causes random segfaults, bus errors, and OOM errors coming
# from the GC.  We (CPC, VD) surmise the issue stems from loading the same
# modules twice, once from the compiler and once from fstarlib (the compiler
# relies on some realized files from ulib/ml).  Our workaround is to include in
# fstartaclib all fstarlib modules not already in the compiler.
TACLIB_ML=$(wildcard $(addsuffix /*.ml,$(DIRS_WITH_TACLIB_ML_FILES)))
tactics_ml/fstartaclib.mllib: fstartaclib.mgen $(TACLIB_ML)
	./gen_mllib.sh $(DIRS_WITH_TACLIB_ML_FILES) > $@

FSTARLIB_OBJECTS=fstarlib.a fstarlib.cma fstarlib.cmxs fstarlib.cmxa
TACLIB_OBJECTS=fstartaclib.cma fstartaclib.cmxs fstartaclib.cmxa

_fstarlib: ml/fstarlib.mllib
	+$(MAKE) -C ml/ intfiles
	$(FSTARLIB_OCAMLBUILD) $(FSTARLIB_OBJECTS)
_fstartaclib: tactics_ml/fstartaclib.mllib
	+$(MAKE) -C ml/ intfiles
	$(TACLIB_OCAMLBUILD) $(TACLIB_OBJECTS)

$(FSTARLIB_OBJECTS): _fstarlib
$(TACLIB_OBJECTS): _fstartaclib

# No trailing slash please
FSTARLIB_DIR=../bin/fstarlib
TACLIB_DIR=../bin/fstar-tactics-lib

FSTARLIB_OUTPUTS=$(addprefix ml/_build/ulib/, \
        $(addsuffix /*.cmi,$(DIRS_WITH_FSTARLIB_ML_FILES)) \
        $(addsuffix /*.cmx,$(DIRS_WITH_FSTARLIB_ML_FILES)) \
        $(addprefix ml/,$(FSTARLIB_OBJECTS)))

TACLIB_OUTPUTS=$(addprefix tactics_ml/_build/ulib/, \
        $(addsuffix /*.cmi,$(DIRS_WITH_TACLIB_ML_FILES)) \
        $(addsuffix /*.cmx,$(DIRS_WITH_TACLIB_ML_FILES)) \
        $(addprefix tactics_ml/,$(TACLIB_OBJECTS)))

install-fstarlib: $(FSTARLIB_DIR)/META
install-fstar-tactics: $(TACLIB_DIR)/META

# This rule is doing an atomic copy into FSTARLIB_DIR,
# so we never see a partial file in bin/
$(FSTARLIB_DIR)/META: $(FSTARLIB_OBJECTS)
	@echo '[INSTALL   fstarlib]'
	$(Q)rm -rf $(FSTARLIB_DIR)_new
	$(Q)mkdir -p $(FSTARLIB_DIR)_new
	$(Q)cp $(FSTARLIB_OUTPUTS) $(FSTARLIB_DIR)_new
	$(Q)sed "s/__FSTAR_VERSION__/$$(cat ../version.txt)/" <ml/fstarlib-META >$(FSTARLIB_DIR)_new/META
	$(Q)rm -rf $(FSTARLIB_DIR)
	$(Q)mv $(FSTARLIB_DIR)_new $(FSTARLIB_DIR)

# See comment for $(FSTARLIB_DIR)/META
$(TACLIB_DIR)/META: $(TACLIB_OBJECTS)
	@echo '[INSTALL   fstartaclib]'
	$(Q)rm -rf $(TACLIB_DIR)_new
	$(Q)mkdir -p $(TACLIB_DIR)_new
	$(Q)cp $(TACLIB_OUTPUTS) $(TACLIB_DIR)_new
	$(Q)sed "s/__FSTAR_VERSION__/$$(cat ../version.txt)/" <ml/fstar-tactics-lib-META >$(TACLIB_DIR)_new/META
	$(Q)rm -rf $(TACLIB_DIR)
	$(Q)mv $(TACLIB_DIR)_new $(TACLIB_DIR)

clean_checked:
	$(Q)rm -f *.checked .cache/*.checked .depend

clean: clean_checked clean_ocaml
	@echo "[CLEAN     ulib/]"
	$(Q)rm -f .depend.extract
	$(Q)rm -f *.mgen
	$(Q)rm -f *.checked.lax .cache/*.checked.lax
	$(Q)rm -fr ml/extracted tactics_ml/extracted tactics_ml/fstarlib_leftovers

clean_ocaml:
	rm -f ml/*.mllib tactics_ml/*.mllib tactics_ml/*.mldylib *~
	rm -rf $(FSTARLIB_DIR)
	rm -rf $(TACLIB_DIR)
	rm -rf ml/_build tactics_ml/_build # ← ocamlbuild -clean does not work on Cygwin

rebuild: clean_ocaml
	+$(MAKE) install-fstarlib
	+$(MAKE) install-fstar-tactics

DOC_FILES=prims.fst FStar.Pervasives.Native.fst FStar.Pervasives.fst \
	  FStar.Squash.fsti FStar.Classical.fsti FStar.BigOps.fsti \
	  FStar.BaseTypes.fsti FStar.BitVector.fst FStar.BV.fsti \
	  FStar.Char.fsti FStar.Date.fsti FStar.DependentMap.fsti \
	  FStar.Dyn.fsti FStar.Exn.fst FStar.Fin.fst FStar.Float.fsti \
	  FStar.FunctionalExtensionality.fsti FStar.Float.fsti \
	  FStar.Ghost.fsti FStar.IFC.fsti FStar.IndefiniteDescription.fst \
	  FStar.UInt8.fst FStar.UInt16.fst FStar.UInt32.fst FStar.UInt64.fst

DOC_DIR=./doc

fstardoc: $(DOC_DIR) $(addprefix $(DOC_DIR)/, $(addsuffix .md, $(DOC_FILES)))

$(DOC_DIR):
	mkdir -p $@

$(DOC_DIR)/%.md: %
	../bin/fstar --print_in_place $^
	python3 ../.scripts/fstardoc/fstardoc.py $^ > $@
