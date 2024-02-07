PULSE_SHARE = ../../
# ^ This must point to /steel/share. But we cannot rely on going via
# the root (../../../..) since the OPAM package will detach the share
# directory from the rest of the repo.

INCLUDE_DIRS=bug-reports by-example lib lib/c class lib/pledge dice/cbor dice/common dice/dpe dice/engine dice/l0 parallel parix c .
CACHE_DIR=.cache
SRC_DIRS=$(addprefix $(PULSE_SHARE)/examples/pulse/, $(INCLUDE_DIRS))
FSTAR_FILES=$(wildcard $(addsuffix /*.fst, $(SRC_DIRS))) $(wildcard $(addsuffix /*.fsti, $(SRC_DIRS)))

all: verify test

extract:
#	$(FSTAR) --odir _output --codegen OCaml CustomSyntax.fst --extract CustomSyntax
	$(FSTAR) --odir _output --codegen OCaml ExtractionTest.fst --extract ExtractionTest

extract_c: _output/cache/ExtractionTest.fst.checked
	$(FSTAR) --odir _output --codegen krml ExtractionTest.fst --extract ExtractionTest
	$(KRML_HOME)/krml -bundle ExtractionTest=* -skip-compilation _output/ExtractionTest.krml -tmpdir _output

#	$(FSTAR) --codegen krml Demo.MultiplyByRepeatedAddition.fst --extract '* -Pulse.Lib.Core'
#	$(FSTAR_HOME)/../karamel/krml -bundle Demo.MultiplyByRepeatedAddition=* -skip-compilation _output/out.krml

ifneq (,$(KRML_HOME))
test-cbor: cbor
	+$(MAKE) -C dice/cbor

extract_pulse_c: _output/cache/PulsePointStruct.fst.checked
	$(FSTAR) --odir _output --codegen krml PulsePointStruct.fst --extract PulsePointStruct
	$(KRML_HOME)/krml -bundle PulsePointStruct=* -skip-linking _output/PulsePointStruct.krml -tmpdir _output

else
test-cbor:

extract_pulse_c:

endif

test: test-cbor extract_pulse_c

.PHONY: extract_pulse_c

.PHONY: test test-cbor test-cbor-raw

include Makefile.pulse.common

PULSE_LIB_CHECKED_FILES=$(filter $(CACHE_DIRECTORY)/Pulse.Lib.%,$(ALL_CHECKED_FILES))

.PHONY: lib
lib: $(PULSE_LIB_CHECKED_FILES)

PULSE_C_CHECKED_FILES=$(filter $(CACHE_DIRECTORY)/Pulse.C.%,$(ALL_CHECKED_FILES))

.PHONY: c
c: $(PULSE_C_CHECKED_FILES)

CBOR_CHECKED_FILES=$(filter $(CACHE_DIRECTORY)/CBOR.% $(CACHE_DIRECTORY)/CDDL.% $(CACHE_DIRECTORY)/CDDLExtractionTest.%,$(ALL_CHECKED_FILES))

.PHONY: cbor
cbor: lib $(CBOR_CHECKED_FILES)

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

.PHONY: install-lib %.install

%.install: %
	$(INSTALL) -m 644 -D $< $(PULSE_INSTALL_PREFIX)/share/steel/examples/pulse/$<

install-lib: $(addsuffix .install,$(PULSE_LIB_CHECKED_FILES) $(wildcard lib/*.fst lib/*.fsti))
