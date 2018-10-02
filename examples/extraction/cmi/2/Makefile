################################################################################
### This examples tests erasure of non-informative types across interface boundaries.
###
### The test target extraction B.fst to B.ml and checks that no references to
### test_function remains, since it is a `int -> unit` function and should
### have been erased.
###
### In contrast with example ../1, this interface A.fsti is decorated with a
### must_erase_for_extraction attribute, which means that --cmi is not necessary
### for type-correct extraction
################################################################################

FSTAR_HOME=../../../..
ROOTS=B.fst
EXTRACT=A B

all: test

include ../Makefile.common

test: B.must_erase.ml
	egrep -q -v test_function B.ml
	diff B.ml B.must_erase.ml

# To observe the difference, see that without --cmi, B.fst extracts
# to B.ml while still containing a dangling reference to the erased
# A.f
B.must_erase.ml: A.ml B.ml
	cp B.ml B.ml.sav
	$(FSTAR) B.fst --codegen OCaml --extract B
	cp B.ml $@
	cp B.ml.sav B.ml
	diff B.ml B.broken.ml
