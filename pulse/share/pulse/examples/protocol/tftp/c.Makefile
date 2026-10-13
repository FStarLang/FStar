# Custard extraction of the verified TFTP loops to C. Assumes everything is already
# verified (see Makefile). Uses a separate makefile since the extraction roots
# differ from the verification roots.

PULSE_ROOT ?= ../../../../..
SRC=.
CACHE_DIR=_cache
OTHERFLAGS += --include spec --include impl
OUTPUT_DIR=_output
TAG=tftpc
ROOTS=impl/TFTP.Impl.Client.Loop.fst impl/TFTP.Impl.Server.Loop.fst
include $(PULSE_ROOT)/mk/boot.mk

.DEFAULT_GOAL := myall

KRML ?= $(KRML_EXE)
RUNTIME = $(PULSE_ROOT)/share/pulse/runtime
KRML_HOME = $(dir $(KRML_EXE))../..
CFLAGS = -std=c11 -D_DEFAULT_SOURCE -Wall -Wno-unused-variable \
  -Wno-unused-function -Wno-unused-but-set-variable \
  -I$(KRML_HOME)/include -I$(KRML_HOME)/krmllib/dist/minimal \
  -I$(OUTPUT_DIR) -I$(RUNTIME)

myall: test

extract: $(OUTPUT_DIR)/.extract.touch

# Custard (F*'s whole-program extractor) reads the checked files and extracts
# the functions vloop_test.c and interop/ call, plus everything they reach.
# --custard_split keeps one karamel module per F* module so that the bundles
# below can name them.  Pulse.Lib.TCP's abstract types are defined by the C runtime
# (Pulse_Lib_TCP_runtime.h), so no declaration is emitted for them.
CUSTARD_ENTRIES = \
  TFTP.Impl.Client.CanonicalProtocol.new_tftp_client \
  TFTP.Impl.Client.Loop.tftp_client_start \
  TFTP.Impl.Client.Loop.tftp_client_run \
  TFTP.Impl.Server.CanonicalProtocol.new_tftp_server \
  TFTP.Impl.Server.Loop.tftp_server_run
CUSTARD_EXTERN_TYPES = Pulse.Lib.TCP.channel Pulse.Lib.TCP.listener

$(OUTPUT_DIR)/Custard.krml: $(ALL_CHECKED_FILES)
	$(call msg, "CUSTARD", "tftp")
	mkdir -p $(OUTPUT_DIR)
	$(FSTAR) --already_cached ',*' --codegen KrmlC --custard_split \
	  $(addprefix --custard_entry ,$(CUSTARD_ENTRIES)) \
	  $(addprefix --custard_extern_type ,$(CUSTARD_EXTERN_TYPES)) \
	  impl/TFTP.Impl.Client.Loop.fst

$(OUTPUT_DIR)/.extract.touch: $(OUTPUT_DIR)/Custard.krml
	$(call msg, "KRML")
	$(KRML) -skip-compilation -warn-error @4+9 -tmpdir $(OUTPUT_DIR) \
	  -library Pulse.Lib.TCP \
	  -add-include '"Pulse_Lib_TCP_runtime.h"' \
	  -bundle 'TFTP.Impl.Client.Loop+TFTP.Impl.Client.CanonicalProtocol+TFTP.Impl.Server.Loop+TFTP.Impl.Server.CanonicalProtocol=TFTP.*,Pulse.Lib.Protocol.*,Pulse.Lib.Array[rename=TFTP_Verified]' \
	  -bundle 'FStar.*,Pulse.*,PulseCore.*,Prims' \
	  -no-prefix TFTP.Impl.Client.Loop \
	  -no-prefix TFTP.Impl.Server.Loop \
	  -no-prefix TFTP.Impl.Client.CanonicalProtocol \
	  -no-prefix TFTP.Impl.Server.CanonicalProtocol \
	  $^
	touch $@

$(OUTPUT_DIR)/vloop_test.exe: $(OUTPUT_DIR)/.extract.touch vloop_test.c \
    $(RUNTIME)/Pulse_Lib_TCP_runtime.c $(RUNTIME)/pulse_tcp_sockets.c
	$(call msg, "CC", $@)
	$(CC) $(CFLAGS) -o $@ $(OUTPUT_DIR)/TFTP_Verified.c vloop_test.c \
	  $(RUNTIME)/Pulse_Lib_TCP_runtime.c $(RUNTIME)/pulse_tcp_sockets.c

test: $(OUTPUT_DIR)/vloop_test.exe
	$(call msg, "RUN", $<)
	$< dummy.txt
