all: pulse

PULSE_HOME ?= ../..
OUTPUT_DIRECTORY=$(PULSE_HOME)/src/ocaml/plugin/generated
CODEGEN = Plugin

ifneq (,$(FSTAR_HOME))
  FSTAR=$(FSTAR_HOME)/bin/fstar.exe
else
  FSTAR=fstar.exe
endif

FSTAR_FILES:=$(wildcard *.fst *.fsti)

FSTAR_OPTIONS=$(OTHERFLAGS) --cache_checked_modules --warn_error @241 --already_cached '*,-Pulse,-PulseSyntaxExtension' --include $(PULSE_HOME)/lib/steel/pulse --odir $(OUTPUT_DIRECTORY)
EXTRACT_MODULES=--extract '+Pulse,-Pulse.Steel'

include $(PULSE_HOME)/lib/steel/runlim.mk

MY_FSTAR=$(RUNLIM) $(FSTAR) $(SIL) $(FSTAR_OPTIONS)

%.checked:
	$(call msg, "CHECK", $(basename $(notdir $@)))
	@# You can debug with --debug $(basename $(notdir $<))
	$(Q)$(RUNLIM) $(MY_FSTAR) $(SIL) $(COMPAT_INDEXED_EFFECTS) $<
	touch -c $@

.depend: $(FSTAR_FILES)
	$(call msg, "DEPEND")
	$(Q)true $(shell rm -f .depend.rsp) $(foreach f,$(FSTAR_FILES),$(shell echo $(f) >> $@.rsp))
	$(Q)$(MY_FSTAR) $(EXTRACT_MODULES) --dep full @$@.rsp > $@.tmp
	mv $@.tmp $@

include .depend

# And then, in a separate invocation, from each .checked we
# extract an .ml file
$(OUTPUT_DIRECTORY)/%.ml:
	$(call msg, "EXTRACT", $(basename $(notdir $@)))
	$(Q)$(MY_FSTAR) $(subst .checked,,$(notdir $<)) --codegen $(CODEGEN) --extract_module $(basename $(notdir $(subst .checked,,$<)))
	chmod -x $@

fstar_parser_parse=$(OUTPUT_DIRECTORY)/../FStar_Parser_Parse.mly

$(fstar_parser_parse): $(FSTAR_HOME)/ocaml/fstar-lib/FStar_Parser_Parse.mly
	cp $^ $@

extract: pulse $(ALL_ML_FILES) $(fstar_parser_parse)

.PHONY: extract

pulse: $(ALL_CHECKED_FILES)

clean:
	rm -f .depend* *.checked

.PHONY: all pulse clean %.fst-in %.fsti-in

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS)
