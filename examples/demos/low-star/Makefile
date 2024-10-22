FSTAR_ROOT ?= ../../..
include $(FSTAR_ROOT)/mk/test.mk

extract:
	krml -skip-compilation Demo.fst -tmpdir out | grep "wrote out"

extract-tailcalls:
	krml -skip-compilation -ftail-calls Demo.fst -tmpdir out | grep "wrote out"
