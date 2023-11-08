# This Makefile only tests (verification and) extraction of DPE message parsing.
# It is not intended to be used with `emacs`. Instead, please use VSCode, with
# a workspace starting from the Steel root directory.

PULSE_EXAMPLES_ROOT = ../..
STEEL_HOME = $(PULSE_EXAMPLES_ROOT)/../../../../

INCLUDE_DIRS=lib dice/common dice/dpe dice/engine dice/l0 dice/cbor .
SRC_DIRS=$(addprefix $(PULSE_EXAMPLES_ROOT)/, $(INCLUDE_DIRS))
FSTAR_FILES=$(wildcard CDDLExtractionTest.*.fst) # but I still need to enumerate them in the Karamel bundle

FSTAR_DEP_OPTIONS=--extract '* -FStar.Tactics -FStar.Reflection -Steel -Pulse +Pulse.Class +Pulse.Lib -Pulse.Lib.Core'
KRML=$(KRML_HOME)/krml
all: verify test

include $(PULSE_EXAMPLES_ROOT)/Makefile.pulse.common

extract_all: $(ALL_KRML_FILES)

extract_all_ml: $(ALL_ML_FILES)

$(OUTPUT_DIRECTORY)/CDDLExtractionTest.c: extract_all
	$(KRML) -bundle CBOR.Spec.Constants+CBOR.Pulse.Type+CBOR.Pulse.Extern+CBOR.Pulse=CBOR.*[rename=CBOR,rename-prefix] -bundle CDDLExtractionTest.Assume+CDDLExtractionTest.Bytes+CDDLExtractionTest.BytesUnwrapped+CDDLExtractionTest.Choice=*[rename=CDDLExtractionTest] -skip-compilation $(wildcard _output/*.krml) -tmpdir $(OUTPUT_DIRECTORY)

$(OUTPUT_DIRECTORY)/%.krml:
	$(FSTAR) --codegen krml $(subst .checked,, $(notdir $<)) --extract_module $(basename $(subst .checked,, $(notdir $<)))

$(OUTPUT_DIRECTORY)/%.ml:
	$(FSTAR) --codegen OCaml $(subst .checked,, $(notdir $<)) --extract_module $(basename $(subst .checked,, $(notdir $<)))

test: $(OUTPUT_DIRECTORY)/CDDLExtractionTest.c
