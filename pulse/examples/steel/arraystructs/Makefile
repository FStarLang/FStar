all: world

FSTAR_HOME ?= $(realpath $(dir $(shell which fstar.exe))/..)
FSTAR_EXE = $(FSTAR_HOME)/bin/fstar.exe

INCLUDE_PATH = $(FSTAR_HOME)/ulib/.cache $(FSTAR_HOME)/ulib/experimental $(KRML_HOME)/krmllib $(KRML_HOME)/krmllib/obj

ifdef KRML_HOME
KRML_EXE = $(KRML_HOME)/krml
endif

world: verify test

FSTAR_OPTIONS = --cache_checked_modules \
		--cmi \
	        --already_cached 'Prims,FStar,LowStar,Steel' \
		$(addprefix --include ,$(INCLUDE_PATH)) \
		$(OTHERFLAGS)

FSTAR = $(FSTAR_EXE) $(FSTAR_OPTIONS)

ALL_SOURCE_FILES = $(wildcard *.fst *.fsti)

# We need to add some Low* files to the dependency roots, because F* extracts Steel.C null to LowStar null
# since the KaRaMeL AST does not have a node for null
# TODO: This should be removed, and support for Steel.C null should be directly added to KaRaMeL instead
SOME_LOWSTAR_FILES = $(FSTAR_HOME)/ulib/LowStar.Monotonic.Buffer.fst $(FSTAR_HOME)/ulib/LowStar.Buffer.fst

.depend: $(ALL_SOURCE_FILES) Makefile
	$(FSTAR) --dep full $(ALL_SOURCE_FILES) $(SOME_LOWSTAR_FILES) --extract 'krml:*,-Prims,-FStar.MSTTotal,-FStar.NMSTTotal,-FStar.MST,-FStar.NMST' > $@.tmp
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

ALL_MODULE_NAMES=$(basename $(ALL_SOURCE_FILES))
FILTERED_KRML_FILES=$(filter-out FStar_NMST.krml Steel_%.krml,$(ALL_KRML_FILES))

extract: $(FILTERED_KRML_FILES)
	$(KRML_EXE) -skip-compilation -skip-makefiles -bundle 'FStar.\*,Steel.\*,C' $^
	touch $@

ALL_C_FILES=$(addsuffix .c,$(ALL_MODULE_NAMES))

$(ALL_C_FILES): %.c: extract
	test -f $@
	touch $@

ALL_O_FILES=$(subst .c,.o,$(ALL_C_FILES))

$(ALL_O_FILES): %.o: %.c
	$(CC) $(CFLAGS) -DKRML_VERIFIED_UINT128 -I $(KRML_HOME)/include -I $(KRML_HOME)/krmllib/dist/minimal -o $@ -c $<

test: $(ALL_O_FILES)

else # no KRML_HOME

test:
	echo KaRaMeL is not installed, skipping test

endif # KRML_HOME

.PHONY: all world verify clean depend test
