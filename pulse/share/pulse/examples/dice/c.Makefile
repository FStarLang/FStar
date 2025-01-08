# This Makefile is only for extraction to C. It assumes everything
# already verified. This separate Makefile is needed because the
# extraction root list needed to compute ALL_KRML_FILES is smaller
# than the verification root list.

PULSE_ROOT ?= ../../../..
SRC=.
CACHE_DIR=_cache
OTHERFLAGS += --include $(PULSE_ROOT)/out/lib/pulse
OTHERFLAGS += --warn_error -342 --cmi
OUTPUT_DIR=_output
CODEGEN=krml
TAG=dicec
ROOTS=dpe/DPE.fst
DEPFLAGS=--extract '* -FStar.Tactics -FStar.Reflection -Pulse -PulseCore +Pulse.Lib -Pulse.Lib.Array.Core -Pulse.Lib.Core -Pulse.Lib.HigherReference'
include $(PULSE_ROOT)/mk/boot.mk

.DEFAULT_GOAL := myall

KRML ?= $(KRML_HOME)/krml

myall: verify test

extract: $(ALL_KRML_FILES)
	$(call msg, "KRML")
	$(KRML) -skip-compilation -ccopt -Wno-unused-variable -bundle 'HACL=EverCrypt.\*,Spec.Hash.Definitions' -bundle 'DPE=*' -library Pulse.Lib.Primitives,Pulse.Lib.SpinLock,L0Core -add-include '"Pulse_Lib_SpinLock.h"' -add-include '"EverCrypt_Base.h"' -warn-error @4+9 -tmpdir $(OUTPUT_DIR) $^

# Note: the Karamel-generated makefiles require running with
# default rules enabled, but they are disabled here (from common.mk).
# We set MAKEFLAGS to empty to not have any of our local
# configuration inherited. Ideally we would just remove the 'r'
# flag from the relevant component in MAKEFLAGS.
test: MAKEFLAGS=
test: extract
	cp $(CURDIR)/external/c/hacl/* $(OUTPUT_DIR)
	+$(MAKE) -C $(OUTPUT_DIR) -f Makefile.basic Pulse_Lib_SpinLock.o DPE.o HACL.o
ifneq (,$(HACL_HOME))
ifneq (,$(wildcard $(HACL_HOME)/dist/gcc-compatible/Makefile.basic))
	# ^ This makefile is removed routinely by the everest script (unsure why)
	# and having it missing would make all this fail mysteriously. Skip
	# this chunk if it's missing and add a warning.
	+$(MAKE) -C $(OUTPUT_DIR) -f Makefile.basic clean
	+$(MAKE) -C $(HACL_HOME)/dist/gcc-compatible Makefile.config
	+$(MAKE) -C $(OUTPUT_DIR) -f Makefile.basic USER_CFLAGS='-I $(HACL_HOME)/dist/gcc-compatible -mavx' Pulse_Lib_SpinLock.o DPE.o HACL.o
	+$(MAKE) -C $(OUTPUT_DIR) -f Makefile.basic clean
	+$(MAKE) -C $(OUTPUT_DIR) -f Makefile.basic USER_CFLAGS='-I $(HACL_HOME)/dist/gcc-compatible -mavx -mavx2' Pulse_Lib_SpinLock.o DPE.o HACL.o
else
	$(warning WARNING: skipping HACL tests even if HACL_HOME is set since state looks dirty)
endif
endif
