################################################################################
### This examples tests erasure of non-informative types across interface boundaries.
### The test target extraction B.fst to B.ml and checks that no references to
### test_function remains, since it is a `int -> unit` function and should
### have been erased
################################################################################

FSTAR_HOME=../../../..
ROOTS=B.fst
EXTRACT=A B

all: test

include ../Makefile.common

test: A.ml B.ml
	egrep -q -v test_function B.ml

# To observe the difference, see that without --cmi, B.fst extracts
# to B.ml while still containing a dangling reference to the erased
# A.f
B.broken.ml: B.ml
	mv B.ml B.ml.sav
	$(FSTAR) B.fst --codegen OCaml --extract B
	cp B.ml B.broken.ml
	mv B.ml.sav B.ml
	diff B.ml B.broken.ml
