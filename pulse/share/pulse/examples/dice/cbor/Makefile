# This Makefile only tests extraction of CBOR parsing and serialization.
# It is not intended to be used with `emacs`. Instead, please use VSCode, with
# a workspace starting from the Steel root directory.

PULSE_ROOT ?= ../../../../..
SRC=.
CACHE_DIR=_cache
OTHERFLAGS += --include $(PULSE_ROOT)/out/lib/pulse
OTHERFLAGS += --include extern
OTHERFLAGS += --include ../_cache
# Note: ^ a bit of a hack. This directory can work independently of the
# DPE directory above, but in a test we first run verify on DPE which
# involves verifying everything here already, so this saves some time.
OTHERFLAGS += --warn_error -342
OUTPUT_DIR=_output
TAG=cbor
ROOTS=$(shell find $(SRC) -type f -name '*.fst' -o -name '*.fsti')
OTHERFLAGS += --already_cached '*,-CBOR.Pulse.Type,-CDDLExtractionTest'
include $(PULSE_ROOT)/mk/boot.mk

.DEFAULT_GOAL := myall

KRML=$(KRML_EXE) $(KRML_OPTS)
myall: verify test

# The modules whose definitions are extracted. Custard compiles the whole
# program reachable from them in one run; --custard_split keeps each F*
# module a separate karamel module, so that the bundles below can name them.
CUSTARD_ENTRY_MODULES := CBOR.Pulse CBOR.Pulse.Extern \
  CDDLExtractionTest.Assume CDDLExtractionTest.Bytes \
  CDDLExtractionTest.BytesUnwrapped CDDLExtractionTest.Choice

.PHONY: extract_all
extract_all: $(OUTPUT_DIR)/Custard.krml

$(OUTPUT_DIR)/Custard.krml: verify
	$(call msg, "CUSTARD", "CBOR")
	$(Q)mkdir -p $(OUTPUT_DIR)
	$(Q)$(FSTAR) --codegen KrmlC --custard_split --odir $(OUTPUT_DIR) \
	  $(addprefix --custard_entry_module ,$(CUSTARD_ENTRY_MODULES)) \
	  CBOR.Pulse.fst

.PHONY: extract_c
extract_c: $(OUTPUT_DIR)/CBOR.h

$(OUTPUT_DIR)/CBOR.h: $(OUTPUT_DIR)/Custard.krml
	$(KRML) -bundle C -bundle CBOR.Spec.Const+CBOR.Pulse.Type+CBOR.Pulse.Extern=[rename=CBOR] -no-prefix CBOR.Spec.Const,CBOR.Pulse.Type,CBOR.Pulse.Extern -bundle CBOR.Pulse= -bundle CDDLExtractionTest.Assume+CDDLExtractionTest.Bytes+CDDLExtractionTest.BytesUnwrapped+CDDLExtractionTest.Choice=*[rename=CDDLExtractionTest] -skip-linking $^ -tmpdir $(OUTPUT_DIR)

.PHONY: extern

extern/CBOR.o: extern/CBOR.h extern/CBOR.c
	+$(MAKE) -C extern

extern: extern/CBOR.o

test: extern extract_c
	+$(MAKE) -C test
