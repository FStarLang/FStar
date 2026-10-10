FSTAR_FILES := $(wildcard spec/*.fst impl/*.fst)
OTHERFLAGS += --include spec --include impl

PULSE_ROOT ?= ../../../../..
include $(PULSE_ROOT)/mk/test.mk

# Extract the verified TFTP sender and receiver loops to C and run a file
# transfer between them over a SOCK_DGRAM socketpair (see vloop_test.c).
# interop/ holds optional wrappers for testing against tftp-hpa; it is not
# built by default.
.PHONY: test-c
test-c: verify # reuses cache, needs to run after verify
	+$(MAKE) -f c.Makefile

all: test-c
