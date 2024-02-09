PULSE_HOME ?= ../../../../..
PULSE_EXAMPLES_ROOT = $(PULSE_HOME)/share/steel/examples/pulse
OUTPUT_DIRECTORY=_output
CACHE_DIRECTORY=$(OUTPUT_DIRECTORY)/cache
SRC_DIRS = common dpe engine l0
INCLUDE_PATHS += cbor
#/Pulse.Lib.HashTable.fst
FSTAR_DEP_OPTIONS=--extract '* -FStar.Tactics -FStar.Reflection -Steel -Pulse +Pulse.Class +Pulse.Lib -Pulse.Lib.Core'
all: verify

include $(PULSE_HOME)/share/steel/Makefile.include

ifeq (,$(KRML_HOME))
KRML_HOME=$(FSTAR_HOME)/../karamel
endif
KRML=$(KRML_HOME)/krml

extract:
#	$(FSTAR) --codegen OCaml CustomSyntax.fst --extract CustomSyntax
	$(FSTAR) --codegen OCaml ExtractionTest.fst --extract ExtractionTest

extract_c:
	$(FSTAR) --codegen krml Demo.MultiplyByRepeatedAddition.fst --extract '* -Pulse.Lib.Core'
	$(FSTAR_HOME)/../karamel/krml -bundle Demo.MultiplyByRepeatedAddition=* -skip-compilation $(OUTPUT_DIRECTORY)/out.krml

extract_all: $(ALL_KRML_FILES)

$(OUTPUT_DIRECTORY)/DPE.c:
	$(KRML) -bundle DPE=* -skip-compilation $(wildcard $(OUTPUT_DIRECTORY)/*.krml) -tmpdir $(OUTPUT_DIRECTORY)

$(OUTPUT_DIRECTORY)/Pulse_Lib_HashTable.c:
	$(KRML) -bundle Pulse.Lib.HashTable=* -skip-compilation $(wildcard $(OUTPUT_DIRECTORY)/*.krml) -tmpdir $(OUTPUT_DIRECTORY)

$(OUTPUT_DIRECTORY)/%.krml:
	$(FSTAR) --codegen krml $(subst .checked,, $(notdir $<)) --extract_module $(basename $(subst .checked,, $(notdir $<)))
