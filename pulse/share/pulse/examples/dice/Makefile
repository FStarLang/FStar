FSTAR_FILES != find . -name '*.fst' -o -name '*.fsti'

PULSE_ROOT ?= ../../../..
include $(PULSE_ROOT)/mk/test.mk

# Extra tests
.PHONY: test-c
test-c: verify # reuses cache, needs to run after verify
	+$(MAKE) -f c.Makefile

.PHONY: test-cbor
test-cbor:
	+$(MAKE) -C cbor

# Add a dependency for 'all'
all: test-c test-cbor
