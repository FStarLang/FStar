SUBDIRS += bug-reports
SUBDIRS += nolib
SUBDIRS += pool

PULSE_ROOT ?= ..
include $(PULSE_ROOT)/mk/test.mk

KRML_FLAGS = -ccopt -Wno-error=unused-but-set-variable

# FIXME: these extra karamel dependencies should be somehow
# automatically computed. I am just retaining them from the previous
# Makefile.

$(OUTPUT_DIR)/VecAlloc.c: KRML_FLAGS=-faggressive-inlining

$(OUTPUT_DIR)/Example_Hashtable.c: $(addprefix $(OUTPUT_DIR)/,\
	FStar_Pervasives.krml \
	FStar_Pervasives_Native.krml \
	Pulse_Lib_Vec.krml \
	Pulse_Lib_HashTable_Type.krml \
	Pulse_Lib_HashTable_Spec.krml \
	Pulse_Lib_HashTable.krml)

$(OUTPUT_DIR)/Example_Slice.c: $(addprefix $(OUTPUT_DIR)/,\
	Pulse_Lib_Slice.krml)

$(OUTPUT_DIR)/Example_Unreachable.c: $(addprefix $(OUTPUT_DIR)/,\
	FStar_Pervasives.krml \
	FStar_Pervasives_Native.krml)
