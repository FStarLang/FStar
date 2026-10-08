# ═══════════════════════════════════════════════════════════════════
# TFTP interoperability tests against the tftp-hpa reference (tftp / in.tftpd)
# ═══════════════════════════════════════════════════════════════════
# Two black-box interop tests transfer a file between one of our *extracted*
# verified-loop TFTP programs and the matching tftp-hpa reference program, then
# check that the received copy is byte-for-byte identical to the original:
#
#   test-server : our extracted `tftp_server` (sender)   <->  tftp-hpa `tftp` (get)
#   test-client : tftp-hpa `in.tftpd` (server)            <->  our extracted `tftp_client`
#
# TFTP runs over UDP with a transfer-ID (TID) discipline: the client sends a Read
# Request (RRQ) to the server port; the server replies with DATA from a fresh
# ephemeral port (its TID); thereafter packets flow between the two TIDs.  Our
# programs' data loops are the VERIFIED, extracted Pulse loops (tftp_server_run /
# tftp_client_run in TFTP_Verified.c); the RRQ + TID handshake is thin unverified
# glue (tftp_server.c / tftp_client.c).  We use octet mode (byte-exact) on an
# unprivileged port so no root is needed.
#
# A test PASSES only if the transfer terminates cleanly within the timeout AND
# the received file is byte-identical to the original.  A stalled/timed-out
# session is a FAIL.  These are UNVERIFIED interop drivers exercised end-to-end.
#
# The extracted verified-loop bundle is built by the parent directory's
# `make test-c` (into ../_output).  tftp-hpa's `tftp` and tftpd-hpa's
# `in.tftpd` must be on PATH (Debian/Ubuntu packages `tftp-hpa` / `tftpd-hpa`);
# a test that cannot find them reports SKIP.  This directory is not part of the
# default Pulse example build: it binds UDP ports and needs external programs.

PARENT      := ..
PULSE_ROOT  ?= ../../../../../..
include $(PULSE_ROOT)/mk/fstar-tree.mk
OUTPUT_DIR  := $(abspath $(PARENT)/_output)
RUNTIME     := $(abspath $(PULSE_ROOT)/share/pulse/runtime)
KRML_HOME   := $(abspath $(dir $(KRML_EXE))../..)

SRV_OUR := $(OUTPUT_DIR)/tftp_server
CLI_OUR := $(OUTPUT_DIR)/tftp_client

DUMMY   := $(abspath $(PARENT)/dummy.txt)
# Distinct default ports so the two tests can run concurrently
# (`make -jN test-server test-client`) without a UDP bind collision.  Override
# either independently (e.g. SRV_PORT=7000).
SRV_PORT ?= 6969
CLI_PORT ?= 6970
TIMEOUT ?= 30
CC      ?= gcc
CFLAGS_INTEROP = -std=c11 -D_DEFAULT_SOURCE -Wall -Wno-unused-function \
  -I$(KRML_HOME)/include -I$(KRML_HOME)/krmllib/dist/minimal \
  -I$(OUTPUT_DIR) -I$(RUNTIME)

SRV_DIR := _run_server
CLI_DIR := _run_client
SRV_DIR_ABS := $(abspath $(SRV_DIR))
CLI_DIR_ABS := $(abspath $(CLI_DIR))

.PHONY: all test test-server test-client build-progs clean help

all: test

# Build the extracted verified-loop bundle (via the parent) then our two interop
# programs against it.
build-progs:
	@$(MAKE) --no-print-directory -C $(PARENT) test-c
	@echo "Compiling TFTP interop drivers over the VERIFIED loops..."
	$(CC) $(CFLAGS_INTEROP) -o $(SRV_OUR) tftp_server.c \
	  $(OUTPUT_DIR)/TFTP_Verified.c \
	  $(RUNTIME)/Pulse_Lib_TCP_runtime.c $(RUNTIME)/pulse_tcp_sockets.c
	$(CC) $(CFLAGS_INTEROP) -o $(CLI_OUR) tftp_client.c \
	  $(OUTPUT_DIR)/TFTP_Verified.c \
	  $(RUNTIME)/Pulse_Lib_TCP_runtime.c $(RUNTIME)/pulse_tcp_sockets.c
	@echo "Interop drivers tftp_server / tftp_client (verified loops) compiled to $(OUTPUT_DIR)/."

# ── Server test: our extracted sender  <->  tftp-hpa `tftp -c get` (receiver) ──
test-server: build-progs
	@echo "═══════════════════════════════════════════════════════════════════"
	@echo " SERVER interop test:  extracted tftp_server (sender)  ->  tftp-hpa tftp (get)"
	@echo "═══════════════════════════════════════════════════════════════════"
	@command -v tftp >/dev/null 2>&1 || { echo "  SKIP: tftp-hpa 'tftp' not found on PATH (install the 'tftp-hpa' package)"; exit 3; }
	@rm -rf $(SRV_DIR); mkdir -p $(SRV_DIR)/root $(SRV_DIR)/recv
	@cp $(DUMMY) $(SRV_DIR)/root/payload.bin
	@echo "  serving payload.bin ($$(wc -c < $(DUMMY)) bytes) with our sender; receiving with tftp-hpa ..."
	@cd $(SRV_DIR)/recv && \
	  timeout -k 3 $(TIMEOUT) bash -c 'srv=""; cleanup(){ [ -n "$$srv" ] && kill "$$srv" 2>/dev/null; }; trap cleanup EXIT INT TERM; \
	    $(SRV_OUR) $(SRV_PORT) ../root & srv=$$!; sleep 0.4; \
	    tftp 127.0.0.1 $(SRV_PORT) -m octet -c get payload.bin; rc=$$?; wait $$srv 2>/dev/null; exit $$rc' \
	    > ../run.log 2>&1; \
	  st=$$?; \
	  if cmp -s payload.bin $(DUMMY); then content=match; else content=differ; fi; \
	  if [ $$st -eq 0 ] && [ "$$content" = match ]; then \
	    echo "  RESULT: PASS - clean transfer; tftp-hpa received an identical copy"; \
	    rm -rf $(SRV_DIR_ABS); \
	  else \
	    if [ $$st -eq 124 ]; then echo "  RESULT: FAIL - session did not terminate cleanly: stalled, killed after $(TIMEOUT)s (content: $$content)"; \
	    elif [ $$st -ne 0 ]; then echo "  RESULT: FAIL - a transfer program exited non-zero: exit=$$st (content: $$content)"; \
	    else echo "  RESULT: FAIL - received file missing or differs"; fi; \
	    echo "  --- recv dir ---"; ls -la . 2>/dev/null; \
	    echo "  --- run.log (tail) ---"; tail -20 ../run.log 2>/dev/null; \
	    echo "  (run dir kept at $(SRV_DIR_ABS) for inspection)"; \
	    exit 1; \
	  fi

# ── Client test: tftp-hpa `in.tftpd` (server)  <->  our extracted receiver ────
test-client: build-progs
	@echo "═══════════════════════════════════════════════════════════════════"
	@echo " CLIENT interop test:  tftp-hpa in.tftpd (server)  ->  extracted tftp_client"
	@echo "═══════════════════════════════════════════════════════════════════"
	@command -v in.tftpd >/dev/null 2>&1 || { echo "  SKIP: tftpd-hpa 'in.tftpd' not found on PATH (install the 'tftpd-hpa' package)"; exit 3; }
	@rm -rf $(CLI_DIR); mkdir -p $(CLI_DIR)/root $(CLI_DIR)/recv
	@cp $(DUMMY) $(CLI_DIR)/root/payload.bin
	@chmod -R a+rX $(CLI_DIR)/root
	@echo "  serving payload.bin ($$(wc -c < $(DUMMY)) bytes) with in.tftpd; receiving with our client ..."
	@cd $(CLI_DIR) && \
	  timeout -k 3 $(TIMEOUT) bash -c 'srv=""; cleanup(){ [ -n "$$srv" ] && { kill -- -$$srv 2>/dev/null; kill $$srv 2>/dev/null; }; }; trap cleanup EXIT INT TERM; \
	    setsid in.tftpd -L --secure --address 127.0.0.1:$(CLI_PORT) --user $$(id -un) $(CLI_DIR_ABS)/root & srv=$$!; sleep 0.4; \
	    $(CLI_OUR) 127.0.0.1 $(CLI_PORT) payload.bin recv/payload.bin; rc=$$?; exit $$rc' \
	    > run.log 2>&1; \
	  st=$$?; \
	  if cmp -s recv/payload.bin root/payload.bin; then content=match; else content=differ; fi; \
	  if [ $$st -eq 0 ] && [ "$$content" = match ]; then \
	    echo "  RESULT: PASS - clean transfer; our client reconstructed an identical copy"; \
	    rm -rf $(CLI_DIR_ABS); \
	  else \
	    if [ $$st -eq 124 ]; then echo "  RESULT: FAIL - session did not terminate cleanly: stalled, killed after $(TIMEOUT)s (content: $$content)"; \
	    elif [ $$st -ne 0 ]; then echo "  RESULT: FAIL - a transfer program exited non-zero: exit=$$st (content: $$content)"; \
	    else echo "  RESULT: FAIL - received file missing or differs"; fi; \
	    echo "  --- run dir ---"; ls -la recv 2>/dev/null; \
	    echo "  --- run.log (tail) ---"; tail -20 run.log 2>/dev/null; \
	    echo "  (run dir kept at $(CLI_DIR_ABS) for inspection)"; \
	    exit 1; \
	  fi

# ── Run both, aggregate, and report ────────────────────────────────────────
test:
	@rc=0; \
	 $(MAKE) --no-print-directory test-server || rc=1; \
	 echo; \
	 $(MAKE) --no-print-directory test-client || rc=1; \
	 echo; \
	 if [ $$rc -eq 0 ]; then echo "OVERALL: all interop tests PASSED"; \
	 else echo "OVERALL: some interop tests FAILED (see above)"; fi; \
	 exit $$rc

clean:
	rm -rf $(SRV_DIR) $(CLI_DIR)

help:
	@echo "TFTP interop tests (vs tftp-hpa):"
	@echo "  make test-server  - our tftp_server (sender) vs tftp-hpa tftp (get)"
	@echo "  make test-client  - tftp-hpa in.tftpd (server) vs our tftp_client (receiver)"
	@echo "  make test         - run both sequentially and report an aggregate result"
	@echo "  make clean        - remove interop run directories"
	@echo "  Parallel:  make -j2 test-server test-client  (distinct default ports"
	@echo "             SRV_PORT=$(SRV_PORT) / CLI_PORT=$(CLI_PORT), so no bind collision)."
	@echo "  Each target self-cleans: background peers are trap-killed on exit/timeout,"
	@echo "  and the run dir is removed on PASS (kept on FAIL for inspection)."
	@echo "  Overrides: SRV_PORT=<n> CLI_PORT=<n> TIMEOUT=<seconds> (default $(TIMEOUT))."
