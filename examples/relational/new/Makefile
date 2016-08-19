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
	$(FSTAR) whilelanguage.fst ifc.fst ifcExample.fst

random_tapes:
	$(FSTAR) random_tapes.fst

recursive:
	$(FSTAR) recursive.fst
