################################################################################
### This examples tests inline_for_extraction across interface boundaries.
### The test target extraction B.fst to B.ml and checks that no references to
### A.id remains, since it should have been inlined
###
### Relative to example 0, this one also includes a case of interfaces that
### lack implementations
################################################################################

# This is needed because ../Makefile.common includes
# ../../../Makefile.common, but GNU Make does not support chained
# includes with relative paths
FSTAR_EXAMPLES = $(realpath ../../../../examples)

ROOTS=B.fst
EXTRACT=A B

all: test

include ../Makefile.common

test: B.ml
	egrep test_function B.ml | egrep -q -v A.id #test that A.id is inlined
