# This Makefile only tests extraction of CBOR parsing and serialization.
# It is not intended to be used with `emacs`. Instead, please use VSCode, with
# a workspace starting from the Steel root directory.

PULSE_HOME ?= ../../../../../../
PULSE_EXAMPLES_ROOT = $(PULSE_HOME)/share/steel/examples/pulse
OUTPUT_DIRECTORY=_output
CACHE_DIRECTORY=$(OUTPUT_DIRECTORY)/cache
SRC_DIRS := extern
INCLUDE_PATHS := ../_output/cache
OTHERFLAGS += --cmi --already_cached '*,-CBOR.Pulse.Type,-CDDLExtractionTest'

FSTAR_DEP_OPTIONS=--extract '* -FStar.Tactics -FStar.Reflection -Steel -Pulse +Pulse.Class +Pulse.Lib -Pulse.Lib.Core'
KRML=$(KRML_HOME)/krml $(KRML_OPTS)
all: verify test

include $(PULSE_HOME)/share/steel/Makefile.include

FILTERED_KRML_FILES := $(filter-out %/prims.krml,$(ALL_KRML_FILES))

.PHONY: extract_all
extract_all: $(FILTERED_KRML_FILES)

extract_all_ml: $(ALL_ML_FILES)

.PHONY: extract_c
extract_c: $(OUTPUT_DIRECTORY)/CBOR.h

$(OUTPUT_DIRECTORY)/CBOR.h: $(FILTERED_KRML_FILES)
	$(KRML) -bundle C -bundle CBOR.Spec.Constants+CBOR.Pulse.Type+CBOR.Pulse.Extern=[rename=CBOR] -no-prefix CBOR.Spec.Constants,CBOR.Pulse.Type,CBOR.Pulse.Extern -bundle CBOR.Pulse= -bundle CDDLExtractionTest.Assume+CDDLExtractionTest.Bytes+CDDLExtractionTest.BytesUnwrapped+CDDLExtractionTest.Choice=*[rename=CDDLExtractionTest] -skip-linking $^ -tmpdir $(OUTPUT_DIRECTORY)

$(OUTPUT_DIRECTORY)/%.krml:
	$(FSTAR) --codegen krml $(subst .checked,, $(notdir $<)) --extract_module $(basename $(subst .checked,, $(notdir $<)))

$(OUTPUT_DIRECTORY)/%.ml:
	$(FSTAR) --codegen OCaml $(subst .checked,, $(notdir $<)) --extract_module $(basename $(subst .checked,, $(notdir $<)))

.PHONY: extern

extern/CBOR.o: extern/CBOR.h extern/CBOR.c
	+$(MAKE) -C extern

extern: extern/CBOR.o

test: extern extract_c
	+$(MAKE) -C test
