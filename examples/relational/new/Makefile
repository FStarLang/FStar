FLAGS=--z3timeout 30
#LIB=

OTHERFLAGS+=$(FLAGS) $(LIB)
FSTAR_HOME=../../..
include ../../Makefile.include

uall: all
sall:

all: ifc\
		 random_tapes\
		 recursive

ifc:
	$(FSTAR) ifc.fst

random_tapes:
	$(FSTAR) random_tapes.fst

recursive:
	$(FSTAR) recursive.fst
