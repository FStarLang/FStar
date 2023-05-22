all: extract

LIB_STEEL=$(CURDIR)/../../../lib/steel
LIB_PULSE=$(LIB_STEEL)/pulse
OUTPUT_DIRECTORY=generated

CODEGEN = Plugin

ifneq (,$(FSTAR_HOME))
	FSTAR=$(FSTAR_HOME)/bin/fstar.exe
else
	FSTAR=fstar.exe
endif

FSTAR_FILES:=$(wildcard $(LIB_PULSE)/*.fst $(LIB_PULSE)/*.fsti)

MY_FSTAR=$(RUNLIM) $(FSTAR) $(SIL) $(OTHERFLAGS) --include $(LIB_STEEL) --include $(LIB_PULSE) --cache_checked_modules --odir $(OUTPUT_DIRECTORY) --warn_error @241 --already_cached '*,' --load_cmxs steel
EXTRACT_MODULES=--extract '+Pulse,-Pulse.Steel'

COMPAT_INDEXED_EFFECTS=--compat_pre_typed_indexed_effects

%.checked:
	$(call msg, "CHECK", $(basename $(notdir $@)))
	@# You can debug with --debug $(basename $(notdir $<))
	$(Q)$(RUNLIM) $(MY_FSTAR) $(SIL) $(COMPAT_INDEXED_EFFECTS) $<

# And then, in a separate invocation, from each .checked we
# extract an .ml file
$(OUTPUT_DIRECTORY)/%.ml:
	$(call msg, "EXTRACT", $(basename $(notdir $@)))
	$(Q)$(MY_FSTAR) $(subst .checked,,$(notdir $<)) --codegen $(CODEGEN) --extract_module $(basename $(notdir $(subst .checked,,$<)))
	chmod -x $@

.depend: $(FSTAR_FILES)
	$(call msg, "DEPEND")
	$(Q)true $(shell rm -f .depend.rsp) $(foreach f,$(FSTAR_FILES),$(shell echo $(f) >> $@.rsp))
	$(Q)$(MY_FSTAR) --dep full $(EXTRACT_MODULES) $(addprefix --include , $(INCLUDE_PATHS)) @$@.rsp > $@.tmp
	mv $@.tmp $@

include .depend

FStar_Parser_Parse.mly: $(FSTAR_HOME)/ocaml/fstar-lib/FStar_Parser_Parse.mly
	cp $^ $@

extract: $(ALL_ML_FILES) FStar_Parser_Parse.mly

.PHONY: all extract
