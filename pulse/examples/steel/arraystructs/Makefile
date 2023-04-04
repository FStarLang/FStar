all: world

FSTAR_HOME ?= $(realpath $(dir $(shell which fstar.exe))/..)
export FSTAR_HOME
FSTAR_EXE = $(FSTAR_HOME)/bin/fstar.exe

INCLUDE_PATH := $(FSTAR_HOME)/ulib/.cache $(FSTAR_HOME)/ulib/experimental

ifdef KRML_HOME
KRML_EXE = $(KRML_HOME)/krml
MY_FSTAR_PATH=$(CURDIR)/my_fstar
INCLUDE_PATH += $(KRML_HOME)/krmllib $(KRML_HOME)/krmllib/obj $(MY_FSTAR_PATH)/lib/steel_c
endif

world: verify test fstlib

fstlib:
	+$(MAKE) -C $@

FSTAR_OPTIONS := --cache_checked_modules \
		--cmi \
		--compat_pre_typed_indexed_effects \
	        --already_cached 'Prims,FStar,LowStar,Steel' \
		$(addprefix --include ,$(INCLUDE_PATH)) \
		$(OTHERFLAGS)

ifdef KRML_HOME
FSTAR_OPTIONS += --load ExtractSteelC
endif

FSTAR = $(FSTAR_EXE) $(FSTAR_OPTIONS)

ALL_SOURCE_FILES = $(wildcard *.fst *.fsti)
NO_EXTRACT_MODULES=PointStruct HaclExample ScalarUnion
EXTRACT_SOURCE_FILES = $(filter-out $(addsuffix .fst,$(NO_EXTRACT_MODULES)),$(ALL_SOURCE_FILES))

comma=,

ifdef KRML_HOME # FIXME: should be HAS_OCAML
# We need to add some Low* files to the dependency roots, because F* extracts Steel.C null to LowStar null
# since the KaRaMeL AST does not have a node for null
# TODO: This should be removed, and support for Steel.C null should be directly added to KaRaMeL instead
SOME_LOWSTAR_FILES = $(FSTAR_HOME)/ulib/LowStar.Monotonic.Buffer.fst $(FSTAR_HOME)/ulib/LowStar.Buffer.fst $(KRML_HOME)/krmllib/C.fst
MY_FSTAR=$(MY_FSTAR_PATH)/lib/steel_c/ExtractSteelC.cmxs
$(MY_FSTAR):
	+$(MAKE) -C $(MY_FSTAR_PATH)
endif

.depend: $(ALL_SOURCE_FILES) Makefile $(MY_FSTAR)
	$(FSTAR) --dep full $(ALL_SOURCE_FILES) $(SOME_LOWSTAR_FILES) --extract 'krml:* -FStar $(addprefix -,$(NO_EXTRACT_MODULES))'  > $@.tmp
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

.PRECIOUS: %.ml
%.ml:
	$(FSTAR) $(notdir $(subst .checked,,$<)) --codegen OCaml \
	--extract_module $(basename $(notdir $(subst .checked,,$<)))

clean:
	-rm -rf *.checked *.krml .depend .depend.tmp *.c *.h *.o compile_flags.txt extract

ifdef KRML_HOME

.PRECIOUS: %.krml
%.krml:
	$(FSTAR) $(notdir $(subst .checked,,$<)) --codegen krml \
	--extract_module $(basename $(notdir $(subst .checked,,$<)))

ALL_MODULE_NAMES=$(basename $(EXTRACT_SOURCE_FILES))
FILTERED_KRML_FILES=$(filter-out FStar_NMST.krml Steel_%.krml,$(ALL_KRML_FILES))

extract: $(FILTERED_KRML_FILES)
	$(KRML_EXE) -skip-compilation -skip-makefiles -bundle 'FStar.\*,Steel.\*,C' -add-include '"steel_c.h"' $^
	touch $@

ALL_C_FILES=$(addsuffix .c,$(ALL_MODULE_NAMES))

$(ALL_C_FILES): %.c: extract
	test -f $@
	touch $@

ALL_O_FILES=$(subst .c,.o,$(ALL_C_FILES))

$(ALL_O_FILES): %.o: %.c
	$(CC) $(CFLAGS) -DKRML_VERIFIED_UINT128 -I $(KRML_HOME)/include -I $(KRML_HOME)/krmllib/dist/minimal -I lib -o $@ -c $<

test: $(ALL_O_FILES)

else # no KRML_HOME

test:
	echo KaRaMeL is not installed, skipping test

endif # KRML_HOME

.PHONY: all world verify clean depend test fstlib
