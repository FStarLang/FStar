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

$(OUTPUT_DIRECTORY)/%.c: $(OUTPUT_DIRECTORY)/%.krml
	$(KRML_HOME)/krml -bundle $*=* $(EXTRA_KRML_OPTS) -skip-linking $< -tmpdir $(OUTPUT_DIRECTORY)

.PHONY: extract
extract: $(OUTPUT_DIRECTORY)/ExtractionTest.ml

ifneq (,$(KRML_HOME))
test-dpe-c: dice
	+$(MAKE) -C dice test-c

test-cbor: dice
	+$(MAKE) -C dice/cbor

extract_c: $(OUTPUT_DIRECTORY)/ExtractionTest.c

extract_pulse_c: $(OUTPUT_DIRECTORY)/PulsePointStruct.c

else
test-dpe-c:

test-cbor:

extract_c:

extract_pulse_c:

endif

test: test-cbor extract extract_pulse_c extract_c test-dpe-c test-error-messages

test-error-messages:
	+$(MAKE) -C bug-reports/error-messages

.PHONY: test-dpe-c test-error-messages

.PHONY: extract_pulse_c extract_c

.PHONY: test test-cbor test-cbor-raw
