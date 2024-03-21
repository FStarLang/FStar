# This Makefile is only for extraction to C. It assumes everything
# already verified. This separate Makefile is needed because the
# extraction root list needed to compute ALL_KRML_FILES is smaller
# than the verification root list.

PULSE_HOME ?= ../../../..
PULSE_EXAMPLES_ROOT = $(PULSE_HOME)/share/pulse/examples
OUTPUT_DIRECTORY_BASE=_output
CACHE_DIRECTORY=$(OUTPUT_DIRECTORY_BASE)/cache
OUTPUT_DIRECTORY=$(OUTPUT_DIRECTORY_BASE)/c
INCLUDE_PATHS += common dpe engine l0 cbor common/hacl-c
FSTAR_FILES := dpe/DPE.fst
ALREADY_CACHED_LIST = *,-HACL,-EverCrypt,-Spec.Hash.Definitions
FSTAR_DEP_FILE=.depend-c
FSTAR_OPTIONS += --warn_error -342 --cmi
FSTAR_DEP_OPTIONS=--extract '* -FStar.Tactics -FStar.Reflection -Pulse -PulseCore +Pulse.Lib -Pulse.Lib.Array.Core -Pulse.Lib.Core -Pulse.Lib.HigherReference'
all: test

include $(PULSE_HOME)/share/pulse/Makefile.include

KRML ?= $(KRML_HOME)/krml

.PHONY: extract
extract: $(ALL_KRML_FILES)
	$(KRML) -skip-compilation -ccopt -Wno-unused-variable -bundle 'HACL=EverCrypt.\*,Spec.Hash.Definitions' -bundle 'DPE=*' -add-include '"EverCrypt_Hash.h"' -add-include '"EverCrypt_HMAC.h"' -add-include '"EverCrypt_Ed25519.h"' -warn-error @4+9 -tmpdir $(OUTPUT_DIRECTORY) $^

.PHONY: test
test: extract
	+$(MAKE) -C common/hacl-c
	+$(MAKE) -C $(OUTPUT_DIRECTORY) -f Makefile.basic USER_CFLAGS='-I $(CURDIR)/common/hacl-c/_output -I $(CURDIR)/common/hacl-c' DPE.o HACL.o
ifneq (,$(HACL_HOME))
	+$(MAKE) -C $(OUTPUT_DIRECTORY) -f Makefile.basic clean
	+$(MAKE) -C $(HACL_HOME)/dist/gcc-compatible Makefile.config
	+$(MAKE) -C $(OUTPUT_DIRECTORY) -f Makefile.basic USER_CFLAGS='-I $(HACL_HOME)/dist/gcc-compatible -mavx' DPE.o HACL.o
	+$(MAKE) -C $(OUTPUT_DIRECTORY) -f Makefile.basic clean
	+$(MAKE) -C $(OUTPUT_DIRECTORY) -f Makefile.basic USER_CFLAGS='-I $(HACL_HOME)/dist/gcc-compatible -mavx -mavx2' DPE.o HACL.o
endif
