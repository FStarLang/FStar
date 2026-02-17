################################################################################
### This examples tests inline_for_extraction across interface boundaries.
### The test target extraction B.fst to B.ml and checks that no references to
### A.id remains, since it should have been inlined
################################################################################

FSTAR_ROOT ?= ../../../..
include $(FSTAR_ROOT)/mk/test.mk

# There should not be a call to A.id in B.ml.expected.
