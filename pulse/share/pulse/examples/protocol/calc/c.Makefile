# Extraction of the calc server to C. Assumes everything is already verified
# (see Makefile). Uses a separate makefile since the extraction roots differ
# from the verification roots.

PULSE_ROOT ?= ../../../../..
SRC=.
CACHE_DIR=_cache
OTHERFLAGS += --include spec --include impl
OUTPUT_DIR=_output
CODEGEN=krml
TAG=calcc
ROOTS=impl/Calc.Server.EndpointRunner.fst
DEPFLAGS=--extract '* -FStar.Tactics -FStar.Reflection -Pulse -PulseCore +Pulse.Lib.Protocol +Pulse.Lib.TCP'
include $(PULSE_ROOT)/mk/boot.mk

.DEFAULT_GOAL := myall

KRML ?= $(KRML_EXE)
RUNTIME = $(PULSE_ROOT)/share/pulse/runtime
KRML_HOME = $(dir $(KRML_EXE))../..
CFLAGS = -std=c11 -D_DEFAULT_SOURCE -Wall -Wno-unused-variable \
  -I$(KRML_HOME)/include -I$(KRML_HOME)/krmllib/dist/minimal \
  -I$(OUTPUT_DIR) -I$(RUNTIME)

myall: test

extract: $(OUTPUT_DIR)/.extract.touch

$(OUTPUT_DIR)/.extract.touch: $(ALL_KRML_FILES)
	$(call msg, "KRML")
	$(KRML) -skip-compilation -warn-error @4+9 -tmpdir $(OUTPUT_DIR) \
	  -library Pulse.Lib.TCP \
	  -add-include '"Pulse_Lib_TCP_runtime.h"' \
	  -bundle 'Calc.Server.EndpointRunner=Calc.*[rename=Calc_Server]' \
	  -bundle 'FStar.*,Pulse.*,PulseCore.*,Prims' \
	  -no-prefix Calc.Server.EndpointRunner \
	  $^
	touch $@

$(OUTPUT_DIR)/calc_test.exe: $(OUTPUT_DIR)/.extract.touch test_main.c \
    $(RUNTIME)/Pulse_Lib_TCP_runtime.c $(RUNTIME)/pulse_tcp_sockets.c
	$(call msg, "CC", $@)
	$(CC) $(CFLAGS) -o $@ $(OUTPUT_DIR)/Calc_Server.c test_main.c \
	  $(RUNTIME)/Pulse_Lib_TCP_runtime.c $(RUNTIME)/pulse_tcp_sockets.c -pthread

test: $(OUTPUT_DIR)/calc_test.exe
	$(call msg, "RUN", $<)
	$<
