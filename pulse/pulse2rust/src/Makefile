all: extract

FSTAR_HOME ?= $(realpath $(dir $(shell which fstar.exe))/..)
FSTAR_EXE = $(FSTAR_HOME)/bin/fstar.exe

# Assume FSTAR_HOME points to the F* source tree
include $(FSTAR_HOME)/.common.mk
include $(FSTAR_HOME)/ulib/gmake/z3.mk    # This pins $(Z3) ...
include $(FSTAR_HOME)/ulib/gmake/fstar.mk # and $(FSTAR) for all sub-make calls
include $(FSTAR_HOME)/src/Makefile.boot.common

CACHE_DIR = $(CURDIR)
OUTPUT_DIRECTORY = $(CURDIR)/ocaml/generated
FSTAR_BOOT_OPTIONS += --MLish_effect FStarC.Compiler.Effect
FSTAR_C=$(RUNLIM) $(FSTAR_EXE) $(SIL) $(FSTAR_BOOT_OPTIONS) --include $(FSTAR_HOME)/src/.cache.boot --cache_checked_modules

# Would be nice to add --already_cached 'Prims FStar'
# but it currently fails
# --warn_error -321 is suppressing related warnings on unexpected checked files

.depend:
	$(call msg, "DEPEND")
	$(Q)$(FSTAR_C) --dep full --warn_error -321  \
		Pulse2Rust.fst                   \
		--odir $(OUTPUT_DIRECTORY)	     \
		--extract_namespace 'Pulse2Rust' \
		--output_deps_to .depend

depend: .depend

include .depend

%.checked.lax:
	$(call msg, "LAXCHECK", $(basename $(basename $(notdir $@))))
	$(Q)$(BENCHMARK_PRE) $(FSTAR_C) $< --already_cached '*,'-$(basename $(notdir $<)) \
	  $(if $(findstring /ulib/,$<),,--MLish) \
		$<
	$(Q)@touch -c $@

%.ml:
	$(call msg, "EXTRACT", $(notdir $@))
	$(Q)$(BENCHMARK_PRE) $(FSTAR_C) $(notdir $(subst .checked.lax,,$<)) \
	--odir $(OUTPUT_DIRECTORY) \
	--codegen OCaml \
	--extract_module $(basename $(notdir $(subst .checked.lax,,$<)))

extract: $(ALL_ML_FILES)
