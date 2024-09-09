PULSE_HOME ?= ../..

all: verify extract

OUTPUT_DIRECTORY=$(PULSE_HOME)/src/ocaml/plugin/generated
FSTAR_ML_CODEGEN = Plugin

INCLUDE_PATHS += $(PULSE_HOME)/lib/pulse

FSTAR_OPTIONS += --already_cached '*,-Pulse,-PulseSyntaxExtension'
FSTAR_DEP_OPTIONS +=--extract '+Pulse,-Pulse.Steel'

include $(PULSE_HOME)/share/pulse/Makefile.include-base

extract: $(ALL_ML_FILES)

.PHONY: clean extract

clean:
	rm -f .depend* *.checked
