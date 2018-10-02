################################################################################
### This examples tests inline_for_extraction across interface boundaries.
### The test target extraction B.fst to B.ml and checks that no references to
### A.id remains, since it should have been inlined
################################################################################

FSTAR_HOME=../../../..
ROOTS=B.fst
EXTRACT=A B

all: test

include ../Makefile.common

test: B.ml
	egrep test_function B.ml | egrep -q -v A.id #test that A.id is inlined
