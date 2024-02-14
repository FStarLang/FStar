PULSE_HOME ?= ../..

all: verify extract

OUTPUT_DIRECTORY=$(PULSE_HOME)/src/ocaml/plugin/generated
CODEGEN = Plugin

INCLUDE_PATHS += $(PULSE_HOME)/lib/pulse

FSTAR_OPTIONS += --already_cached '*,-Pulse,-PulseSyntaxExtension' --odir $(OUTPUT_DIRECTORY)
FSTAR_DEP_OPTIONS +=--extract '+Pulse,-Pulse.Steel'

include $(PULSE_HOME)/share/pulse/Makefile.include-base

# And then, in a separate invocation, from each .checked we
# extract an .ml file
$(OUTPUT_DIRECTORY)/%.ml:
	$(call msg, "EXTRACT", $(basename $(notdir $@)))
	$(Q)$(FSTAR) $(subst .checked,,$(notdir $<)) --codegen $(CODEGEN) --extract_module $(basename $(notdir $(subst .checked,,$<)))
	chmod -x $@

extract: $(ALL_ML_FILES)

.PHONY: clean extract

clean:
	rm -f .depend* *.checked
