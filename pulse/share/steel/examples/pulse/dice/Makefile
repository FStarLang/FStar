## Modeled on dice/cbor/Makefile

PULSE_EXAMPLES_ROOT = ..
STEEL_HOME = $(PULSE_EXAMPLES_ROOT)/../../../../

INCLUDE_DIRS=lib lib/pledge _output/cache dice/common dice/dpe dice/engine dice/l0
SRC_DIRS=$(addprefix $(PULSE_EXAMPLES_ROOT)/, $(INCLUDE_DIRS))
FSTAR_FILES=$(wildcard $(addsuffix /*.fst, $(SRC_DIRS))) $(wildcard $(addsuffix /*.fsti, $(SRC_DIRS)))
OUTPUT_DIRECTORY=../_output

include $(PULSE_EXAMPLES_ROOT)/Makefile.pulse.common

FSTAR_DEP_OPTIONS=--extract '* -FStar.Tactics -FStar.Reflection -Steel -Pulse +Pulse.Class +Pulse.Lib -Pulse.Lib.Core'

%.ast:
	$(FSTAR) --admit_smt_queries true --codegen Extension $(subst .ast,, $(notdir $@)) --extract_module $(basename $(subst .ast,, $(notdir $@)))

DPE_FILES = EngineTypes.fst \
  EngineCore.fst \
	L0Types.fst \
	L0Crypto.fst \
	L0Core.fst \
	Pulse.Lib.HashTable.Type.fst \
	Pulse.Lib.HashTable.Spec.fst \
	Pulse.Lib.HashTable.fst \
	DPETypes.fst \
	DPE.fst

dpe-ast: $(addsuffix .ast, $(DPE_FILES))
