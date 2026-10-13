# Custard extraction of the echo servers to C. Expects everything to be already verified
# (see Makefile). Uses a separate makefile since the extraction roots differ
# from the verification roots.

PULSE_ROOT ?= ../../../../..
SRC=.
CACHE_DIR=_cache
OTHERFLAGS += --include spec --include impl
OUTPUT_DIR=_output
TAG=echoc
ROOTS=impl/Echo.Server.fst
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

# Custard (F*'s whole-program extractor) reads the checked files and extracts
# the functions test_main.c call, plus everything they reach.  --custard_split
# keeps one karamel module per F* module so that the bundles below can name
# them.  Pulse.Lib.TCP's abstract types are defined by the C runtime
# (Pulse_Lib_TCP_runtime.h), so no declaration is emitted for them.
CUSTARD_ENTRIES = \
  Echo.Server.echo_session_direct \
  Echo.Server.echo_session_endpoint
CUSTARD_EXTERN_TYPES = Pulse.Lib.TCP.channel Pulse.Lib.TCP.listener

$(OUTPUT_DIR)/Custard.krml: $(ALL_CHECKED_FILES)
	$(call msg, "CUSTARD", "echo")
	mkdir -p $(OUTPUT_DIR)
	$(FSTAR) --already_cached ',*' --codegen KrmlC --custard_split \
	  $(addprefix --custard_entry ,$(CUSTARD_ENTRIES)) \
	  $(addprefix --custard_extern_type ,$(CUSTARD_EXTERN_TYPES)) \
	  impl/Echo.Server.fst

$(OUTPUT_DIR)/.extract.touch: $(OUTPUT_DIR)/Custard.krml
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
