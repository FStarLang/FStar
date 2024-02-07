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

dpe-ast: EngineTypes.fst.ast EngineCore.fst.ast L0Types.fst.ast L0Crypto.fst.ast L0Core.fst.ast Pulse.Lib.HashTable.Type.fst.ast Pulse.Lib.HashTable.Spec.fst.ast Pulse.Lib.HashTable.fst.ast DPE.fst.ast