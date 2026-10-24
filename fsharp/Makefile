FSTAR_ROOT ?= ..
include $(FSTAR_ROOT)/mk/common.mk

.PHONY: all test clean

all: test

test:
	+$(MAKE) -C tests all

clean:
	+$(MAKE) -C tests clean
