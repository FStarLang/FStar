all: extract

FSTAR_HOME ?= $(realpath $(dir $(shell which fstar.exe))/..)
FSTAR_EXE = $(FSTAR_HOME)/bin/fstar.exe

# Assume FSTAR_HOME points to the F* source tree
include $(FSTAR_HOME)/.common.mk
include $(FSTAR_HOME)/ulib/gmake/z3.mk    # This pins $(Z3) ...
include $(FSTAR_HOME)/ulib/gmake/fstar.mk # and $(FSTAR) for all sub-make calls
include $(FSTAR_HOME)/src/Makefile.boot.common

OUTPUT_DIRECTORY = $(CURDIR)/../ocaml/plugin/generated
ADDITIONAL_INCLUDES=$(FSTAR_HOME)/src/.cache.boot

FSTAR_OPTIONS= \
	$(OTHERFLAGS) --lax --MLish --MLish_effect FStarC.Compiler.Effect \
	--no_location_info --warn_error -271-272-241-319-274 \
	$(addprefix --include , $(addprefix $(FSTAR_HOME)/src/,$(INCLUDE_PATHS))) \
	$(addprefix --include , $(ADDITIONAL_INCLUDES)) \
	--include . \
	--odir "$(OUTPUT_DIRECTORY)" \
	--cache_checked_modules

FSTAR_C=$(RUNLIM) $(FSTAR_EXE) $(SIL) $(FSTAR_OPTIONS)

FSTAR_FILES=$(wildcard *.fst)

all: extract

.depend: $(FSTAR_FILES)
	$(FSTAR_C) --warn_error -321 --dep full --extract PulseSyntaxExtension --output_deps_to $@ $^

depend: .depend
include .depend


%.checked.lax:
	$(call msg, "CHECK", $(notdir $@))
	$(Q)$(BENCHMARK_PRE) $(FSTAR_C) $< --already_cached 'Prims,FStar'
	$(Q)touch $@

# And then, in a separate invocation, from each .checked.lax we
# extract an .ml file
$(OUTPUT_DIRECTORY)/%.ml: 
	mkdir -p $(OUTPUT_DIRECTORY)
	$(call msg, "EXTRACT", $(notdir $@))
	$(Q)$(BENCHMARK_PRE) $(FSTAR_C) $(notdir $(subst .checked.lax,, $<)) \
		--extract $(basename $(notdir $(subst .checked.lax,, $<))) \
		--already_cached '*' \
		--codegen OCaml
	chmod -x $@

extract: $(ALL_ML_FILES)

clean:
	rm -rf $(addprefix $(OUTPUT_DIRECTORY)/, $(ALL_ML_FILES))
	rm *.checked.lax
	rm -f .depend

.PHONY: all extract clean depend
