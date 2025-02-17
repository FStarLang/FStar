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
OTHERFLAGS += --warn_error -342 --cmi
OUTPUT_DIR=_output
CODEGEN=krml
TAG=cbor
ROOTS=$(shell find $(SRC) -type f -name '*.fst' -o -name '*.fsti')
DEPFLAGS=--extract '* -FStar -Pulse -PulseCore'
OTHERFLAGS += --cmi --already_cached '*,-CBOR.Pulse.Type,-CDDLExtractionTest'
include $(PULSE_ROOT)/mk/boot.mk

.DEFAULT_GOAL := myall

KRML=$(KRML_HOME)/krml $(KRML_OPTS)
myall: verify test

.PHONY: extract_all
extract_all: $(ALL_KRML_FILES)

extract_all_ml: $(ALL_ML_FILES)

.PHONY: extract_c
extract_c: $(OUTPUT_DIR)/CBOR.h

$(OUTPUT_DIR)/CBOR.h: $(ALL_KRML_FILES)
	$(KRML) -bundle C -bundle CBOR.Spec.Constants+CBOR.Pulse.Type+CBOR.Pulse.Extern=[rename=CBOR] -no-prefix CBOR.Spec.Constants,CBOR.Pulse.Type,CBOR.Pulse.Extern -bundle CBOR.Pulse= -bundle CDDLExtractionTest.Assume+CDDLExtractionTest.Bytes+CDDLExtractionTest.BytesUnwrapped+CDDLExtractionTest.Choice=*[rename=CDDLExtractionTest] -skip-linking $^ -tmpdir $(OUTPUT_DIR)

.PHONY: extern

extern/CBOR.o: extern/CBOR.h extern/CBOR.c
	+$(MAKE) -C extern

extern: extern/CBOR.o

test: extern extract_c
	+$(MAKE) -C test
