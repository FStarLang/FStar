#FLAGS=
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
	$(FSTAR) rel.fst whilelanguage.fst ifc.fst ifcExample.fst

random_tapes:
	$(FSTAR) bijection.fst random_tapes.fst

recursive:
	$(FSTAR) recursive.fst

WhileReify:
	$(FSTAR) --include ../../dm4free WhileReify.fst
