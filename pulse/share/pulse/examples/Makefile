PULSE_HOME ?= ../../..
PULSE_SHARE = $(PULSE_HOME)/share/pulse

SRC_DIRS = bug-reports by-example parallel parix c .
INCLUDE_PATHS += $(PULSE_HOME)/lib/pulse/c
OUTPUT_DIRECTORY=_output
CACHE_DIRECTORY=$(OUTPUT_DIRECTORY)/cache

.PHONY: all
all: verify test dice

include $(PULSE_SHARE)/Makefile.include

.PHONY: dice
dice:
	+$(MAKE) -C dice

$(OUTPUT_DIRECTORY)/Example_Hashtable.c: $(addprefix $(OUTPUT_DIRECTORY)/,\
	FStar_Pervasives.krml FStar_Pervasives_Native.krml \
	Pulse_Lib_Vec.krml \
	Pulse_Lib_HashTable_Type.krml Pulse_Lib_HashTable_Spec.krml Pulse_Lib_HashTable.krml)

$(OUTPUT_DIRECTORY)/Example_Slice.c: $(addprefix $(OUTPUT_DIRECTORY)/,\
	Pulse_Lib_Slice.krml)

$(OUTPUT_DIRECTORY)/Example_Unreachable.c: $(addprefix $(OUTPUT_DIRECTORY)/,FStar_Pervasives.krml FStar_Pervasives_Native.krml)

$(OUTPUT_DIRECTORY)/%.c: $(EXTRA_KRML_DEPS) $(OUTPUT_DIRECTORY)/%.krml
	$(KRML_HOME)/krml -bundle $*=* $(EXTRA_KRML_OPTS) -skip-linking $+ -tmpdir $(OUTPUT_DIRECTORY)

.PHONY: extract
extract: $(OUTPUT_DIRECTORY)/ExtractionTest.ml

.PHONY: extract_unreachable
extract_unreachable: $(OUTPUT_DIRECTORY)/Example_Unreachable.ml

EXTRACT_C_FILES = $(addprefix $(OUTPUT_DIRECTORY)/,ExtractionTest.c PulsePointStruct.c Bug166.c Example_Unreachable.c Example_Hashtable.c Example_Slice.c)

ifneq (,$(KRML_HOME))
test-dpe-c: dice
	+$(MAKE) -C dice test-c

test-cbor: dice
	+$(MAKE) -C dice/cbor

else
test-dpe-c:

test-cbor:

EXTRACT_C_FILES =

endif

extract_c: $(EXTRACT_C_FILES)

test: test-cbor extract extract_pulse_c extract_c extract_c_bug166 test-dpe-c test-error-messages extract_c_unreachable extract_c_hashtable

test-error-messages:
	+$(MAKE) -C bug-reports/error-messages

.PHONY: test-dpe-c test-error-messages

.PHONY: extract_pulse_c extract_c

.PHONY: test test-cbor test-cbor-raw
