FSTAR_FILES := $(wildcard spec/*.fst impl/*.fst)
OTHERFLAGS += --include spec --include impl

PULSE_ROOT ?= ../../../../..
include $(PULSE_ROOT)/mk/test.mk

# Extract the two verified echo servers to C and run them against a client
# over a socketpair (see test_main.c).
.PHONY: test-c
test-c: verify # reuses cache, needs to run after verify
	+$(MAKE) -f c.Makefile

all: test-c
