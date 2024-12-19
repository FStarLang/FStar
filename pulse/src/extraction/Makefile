FSTAR_EXE   ?= $(shell which fstar.exe)
FSTAR_STAGE ?= $(abspath $(shell $(FSTAR_EXE) --locate)/../..)
FSTAR_HOME  ?= $(abspath $(shell $(FSTAR_EXE) --locate)/../../..)
include $(FSTAR_HOME)/mk/common.mk
.DEFAULT_GOAL := all

all: extract

# Assume FSTAR_HOME points to the F* source tree
include $(FSTAR_HOME)/gmake/fstar.mk # and $(FSTAR) for all sub-make calls

OUTPUT_DIRECTORY = $(CURDIR)/../ocaml/plugin/generated
ADDITIONAL_INCLUDES=$(FSTAR_STAGE)/fstarc.checked $(FSTAR_HOME)/src

FSTAR_OPTIONS= \
	$(OTHERFLAGS) --lax --MLish --MLish_effect FStarC.Compiler.Effect \
	--no_location_info --warn_error -271-272-241-319-274 \
	$(addprefix --include , $(ADDITIONAL_INCLUDES)) \
	--include . \
	--odir "$(OUTPUT_DIRECTORY)" \
	--cache_checked_modules

FSTAR_C=$(RUNLIM) $(FSTAR_EXE) $(SIL) $(FSTAR_OPTIONS)

FSTAR_FILES=$(wildcard *.fst *.fsti)

all: extract

.depend: $(FSTAR_FILES)
	$(FSTAR_C) --warn_error -321 \
	  --dep full --extract ExtractPulse,ExtractPulseC,ExtractPulseOCaml --output_deps_to $@ $^

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
		--codegen PluginNoLib
	chmod -x $@

extract: $(ALL_ML_FILES)

clean:
	rm -rf $(addprefix $(OUTPUT_DIRECTORY)/, $(ALL_ML_FILES))
	rm *.checked.lax
	rm -f .depend

.PHONY: all extract clean depend
