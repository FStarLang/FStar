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

# Test.ml.expected should not contain a magic.
