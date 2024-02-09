PULSE_HOME ?= ../../../..
PULSE_SHARE = $(PULSE_HOME)/share/steel
# ^ This must point to /steel/share. But we cannot rely on going via
# the root (../../../..) since the OPAM package will detach the share
# directory from the rest of the repo.

SRC_DIRS = bug-reports by-example parallel parix c .
INCLUDE_PATHS += $(PULSE_HOME)/lib/pulse/c
OUTPUT_DIRECTORY=_output
CACHE_DIRECTORY=$(OUTPUT_DIRECTORY)/cache

all: verify test dice

include $(PULSE_SHARE)/Makefile.include

.PHONY: dice
dice:
	+$(MAKE) -C dice

extract:
#	$(FSTAR) --odir $(OUTPUT_DIRECTORY) --codegen OCaml CustomSyntax.fst --extract CustomSyntax
	$(FSTAR) --codegen OCaml ExtractionTest.fst --extract ExtractionTest

extract_c: $(CACHE_DIRECTORY)/ExtractionTest.fst.checked
	$(FSTAR) --codegen krml ExtractionTest.fst --extract ExtractionTest
	$(KRML_HOME)/krml -bundle ExtractionTest=* -skip-compilation $(OUTPUT_DIRECTORY)/ExtractionTest.krml -tmpdir $(OUTPUT_DIRECTORY)

#	$(FSTAR) --codegen krml Demo.MultiplyByRepeatedAddition.fst --extract '* -Pulse.Lib.Core'
#	$(FSTAR_HOME)/../karamel/krml -bundle Demo.MultiplyByRepeatedAddition=* -skip-compilation $(OUTPUT_DIRECTORY)/out.krml

ifneq (,$(KRML_HOME))
test-cbor: dice
	+$(MAKE) -C dice/cbor

extract_pulse_c: $(CACHE_DIRECTORY)/PulsePointStruct.fst.checked
	$(FSTAR) --odir $(OUTPUT_DIRECTORY) --codegen krml PulsePointStruct.fst --extract PulsePointStruct
	$(KRML_HOME)/krml -bundle PulsePointStruct=* -skip-linking $(OUTPUT_DIRECTORY)/PulsePointStruct.krml -tmpdir $(OUTPUT_DIRECTORY)

else
test-cbor:

extract_pulse_c:

endif

test: test-cbor extract_pulse_c

.PHONY: extract_pulse_c

.PHONY: test test-cbor test-cbor-raw

PREFIX ?= /usr/local
ifeq ($(OS),Windows_NT)
  PULSE_INSTALL_PREFIX=$(shell cygpath -m $(PREFIX))
else
  PULSE_INSTALL_PREFIX=$(PREFIX)
endif
export PULSE_INSTALL_PREFIX

ifeq (,$(INSTALL))
  INSTALL := $(shell ginstall --version 2>/dev/null | cut -c -8 | head -n 1)
  ifdef INSTALL
     INSTALL := ginstall
  else
     INSTALL := install
  endif
  export INSTALL
endif
