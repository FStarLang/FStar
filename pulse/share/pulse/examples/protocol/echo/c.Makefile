# Extraction of the echo servers to C. Expects everything to be already verified
# (see Makefile). Uses a separate makefile since the extraction roots differ
# from the verification roots.

PULSE_ROOT ?= ../../../../..
SRC=.
CACHE_DIR=_cache
OTHERFLAGS += --include spec --include impl
OUTPUT_DIR=_output
CODEGEN=krml
TAG=echoc
ROOTS=impl/Echo.Server.fst
DEPFLAGS=--extract '* -FStar.Tactics -FStar.Reflection -Pulse -PulseCore +Pulse.Lib.Protocol +Pulse.Lib.TCP +Pulse.Lib.BufferedTCP +Pulse.Lib.BufferedStream +Pulse.Lib.Memmove +Pulse.Lib.Array'
include $(PULSE_ROOT)/mk/boot.mk

.DEFAULT_GOAL := myall

KRML ?= $(KRML_EXE)
RUNTIME = $(PULSE_ROOT)/share/pulse/runtime
KRML_HOME = $(dir $(KRML_EXE))../..
# -Wno-dangling-else: KaRaMeL prints the [match outcome] in serve_endpoint as
# an unbraced `else if (...) if (...) {...} else ...`, which is correct C.
CFLAGS = -std=c11 -D_DEFAULT_SOURCE -Wall -Wno-unused-variable \
  -Wno-unused-function -Wno-unused-but-set-variable -Wno-dangling-else \
  -I$(KRML_HOME)/include -I$(KRML_HOME)/krmllib/dist/minimal \
  -I$(OUTPUT_DIR) -I$(RUNTIME)

RUNTIME_C = $(RUNTIME)/Pulse_Lib_TCP_runtime.c $(RUNTIME)/pulse_tcp_sockets.c \
  $(RUNTIME)/Pulse_Lib_Memmove_runtime.c

myall: test

extract: $(OUTPUT_DIR)/.extract.touch

$(OUTPUT_DIR)/.extract.touch: $(ALL_KRML_FILES)
	$(call msg, "KRML")
	$(KRML) -skip-compilation -warn-error @4+9 -tmpdir $(OUTPUT_DIR) \
	  -library Pulse.Lib.TCP,Pulse.Lib.Memmove \
	  -add-include '"Pulse_Lib_TCP_runtime.h"' \
	  -bundle 'Echo.Server=Echo.*,Pulse.Lib.Protocol.*,Pulse.Lib.BufferedTCP,Pulse.Lib.BufferedTCP.*,Pulse.Lib.BufferedStream,Pulse.Lib.BufferedStream.*,Pulse.Lib.Array[rename=Echo_Verified]' \
	  -bundle 'FStar.*,Pulse.*,PulseCore.*,Prims' \
	  -no-prefix Echo.Server \
	  -no-prefix Echo.Report \
	  $^
	touch $@

$(OUTPUT_DIR)/echo_test.exe: $(OUTPUT_DIR)/.extract.touch test_main.c $(RUNTIME_C)
	$(call msg, "CC", $@)
	$(CC) $(CFLAGS) -o $@ $(OUTPUT_DIR)/Echo_Verified.c test_main.c \
	  $(RUNTIME_C) -pthread

test: $(OUTPUT_DIR)/echo_test.exe
	$(call msg, "RUN", $<)
	$<
