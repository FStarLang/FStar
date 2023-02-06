.PHONY: all benchmark extra clean_checked clean_ocaml clean fstardoc ulib-in-fsharp

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



include $(FSTAR_HOME)/ulib/ml/Makefile.realized
include $(FSTAR_HOME)/ulib/ml/Makefile.include
include $(FSTAR_HOME)/.common.mk

ulib-in-fsharp:
	+$(MAKE) -f Makefile.extract.fsharp all-fs

clean_checked:
	$(Q)rm -f *.checked .cache/*.checked .depend

clean: clean_checked clean_ocaml
	@echo "[CLEAN     ulib/]"
	$(Q)rm -f .depend.extract.rsp
	$(Q)rm -f .depend.extract
	$(Q)rm -f *.checked.lax .cache/*.checked.lax

clean_ocaml:
	@echo "[CLEAN OCAML LIBS]"
	$(Q)+$(MAKE) -C ulib/ml clean

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

INSTALL_EXEC ?= install

install: all
	+./install-ulib.sh
