################################################################################
### This examples tests inline_for_extraction across interface boundaries.
### The test target extraction B.fst to B.ml and checks that no references to
### A.id remains, since it should have been inlined
###
### Relative to example 0, this one also includes a case of interfaces that
### lack implementations
################################################################################

FSTAR_ROOT ?= ../../../..
OTHERFLAGS += --cmi
include $(FSTAR_ROOT)/mk/test.mk

all: test

$(OUTPUT_DIR)/%.ml: %.fst.checked
	$(FSTAR) --codegen OCaml --extract $* $*.fst

test: $(OUTPUT_DIR)/B.ml
	egrep test_function $< | egrep -q -v A.id #test that A.id is inlined
