# Custard extraction of the calc server to C. Assumes everything is already verified
# (see Makefile). Uses a separate makefile since the extraction roots differ
# from the verification roots.

PULSE_ROOT ?= ../../../../..
SRC=.
CACHE_DIR=_cache
OTHERFLAGS += --include spec --include impl
OUTPUT_DIR=_output
TAG=calcc
ROOTS=impl/Calc.Server.EndpointRunner.fst
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

# Custard (F*'s whole-program extractor) reads the checked files and extracts
# the functions test_main.c call, plus everything they reach.  --custard_split
# keeps one karamel module per F* module so that the bundles below can name
# them.  Pulse.Lib.TCP's abstract types are defined by the C runtime
# (Pulse_Lib_TCP_runtime.h), so no declaration is emitted for them.
CUSTARD_ENTRIES = \
  Calc.Server.EndpointRunner.run_channel_endpoint
CUSTARD_EXTERN_TYPES = Pulse.Lib.TCP.channel Pulse.Lib.TCP.listener

$(OUTPUT_DIR)/Custard.krml: $(ALL_CHECKED_FILES)
	$(call msg, "CUSTARD", "calc")
	mkdir -p $(OUTPUT_DIR)
	$(FSTAR) --already_cached ',*' --codegen KrmlC --custard_split \
	  $(addprefix --custard_entry ,$(CUSTARD_ENTRIES)) \
	  $(addprefix --custard_extern_type ,$(CUSTARD_EXTERN_TYPES)) \
	  impl/Calc.Server.EndpointRunner.fst

$(OUTPUT_DIR)/.extract.touch: $(OUTPUT_DIR)/Custard.krml
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
