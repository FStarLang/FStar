all: verify

FSTAR_HOME ?= $(realpath $(dir $(shell which fstar.exe))/..)
export FSTAR_HOME
FSTAR_EXE = $(FSTAR_HOME)/bin/fstar.exe

INCLUDE_PATH := $(FSTAR_HOME)/ulib/.cache $(FSTAR_HOME)/ulib/experimental

FSTAR_OPTIONS = --cache_checked_modules \
		--cmi \
		--compat_pre_typed_indexed_effects \
	        --already_cached '*,-Steel.C.Array,-Steel.ST.C.Types' \
		$(addprefix --include ,$(INCLUDE_PATH)) \
		$(OTHERFLAGS)

FSTAR = $(FSTAR_EXE) $(FSTAR_OPTIONS)

ALL_SOURCE_FILES = $(wildcard *.fst *.fsti)

.depend: $(ALL_SOURCE_FILES) Makefile
	$(FSTAR) --dep full $(ALL_SOURCE_FILES) > $@.tmp
	mv $@.tmp $@

depend: .depend

-include .depend

$(ALL_CHECKED_FILES): %.checked:
	$(FSTAR) $<
	@touch -c $@

verify: $(ALL_CHECKED_FILES)
	echo $*

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS)

clean:
	-rm -rf *.checked .depend .depend.tmp

.PHONY: all verify clean depend
