PULSE_EXAMPLES_ROOT = ..
PULSE_HOME = ../../../../..

INCLUDE_DIRS=dice/common dice/dpe dice/engine dice/l0 dice/cbor .
SRC_DIRS=$(addprefix $(PULSE_EXAMPLES_ROOT)/, $(INCLUDE_DIRS))
FSTAR_FILES=../dice/dpe/DPE.fst
#/Pulse.Lib.HashTable.fst
FSTAR_DEP_OPTIONS=--extract '* -FStar.Tactics -FStar.Reflection -Steel -Pulse +Pulse.Class +Pulse.Lib -Pulse.Lib.Core'
KRML=$(FSTAR_HOME)/../karamel/krml
all: verify extract_all

extract:
#	$(FSTAR) --odir _output --codegen OCaml CustomSyntax.fst --extract CustomSyntax
	$(FSTAR) --odir _output --codegen OCaml ExtractionTest.fst --extract ExtractionTest

extract_c:
	$(FSTAR) --codegen krml Demo.MultiplyByRepeatedAddition.fst --extract '* -Pulse.Lib.Core'
	$(FSTAR_HOME)/../karamel/krml -bundle Demo.MultiplyByRepeatedAddition=* -skip-compilation _output/out.krml

include $(PULSE_EXAMPLES_ROOT)/Makefile.pulse.common

extract_all: $(ALL_KRML_FILES)

$(OUTPUT_DIRECTORY)/Pulse_Lib_HashTable.ml:
	$(FSTAR) --codegen OCaml $(subst .checked,, $(notdir $<)) --extract_module $(basename $(subst .checked,, $(notdir $<)))

$(OUTPUT_DIRECTORY)/Pulse_Lib_HashTable_Spec.ml:
	$(FSTAR) --codegen OCaml $(subst .checked,, $(notdir $<)) --extract_module $(basename $(subst .checked,, $(notdir $<)))

$(OUTPUT_DIRECTORY)/DPE.c:
	$(KRML) -bundle DPE=* -skip-compilation $(wildcard _output/*.krml) -tmpdir $(OUTPUT_DIRECTORY)

$(OUTPUT_DIRECTORY)/Pulse_Lib_HashTable.c:
	$(KRML) -bundle Pulse.Lib.HashTable=* -skip-compilation $(wildcard _output/*.krml) -tmpdir $(OUTPUT_DIRECTORY)

$(OUTPUT_DIRECTORY)/%.krml:
	$(FSTAR) --codegen krml $(subst .checked,, $(notdir $<)) --extract_module $(basename $(subst .checked,, $(notdir $<)))

