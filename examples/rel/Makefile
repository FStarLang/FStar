#FLAGS=
#LIB=

OTHERFLAGS+=$(FLAGS) $(LIB)
FSTAR_HOME=../..
include ../Makefile.include

uall: all

all: ifc\
		 random_tapes\
		 delimited_release\
		 recursive \
		 WhileReify.dm4f \
		 IfcReify.dm4f

ifc:
	$(FSTAR) rel.fst whilelanguage.fst ifc.fst ifcExample.fst

random_tapes:
	$(FSTAR) bijection.fst random_tapes.fst

recursive:
	$(FSTAR) recursive.fst

delimited_release:
	$(FSTAR) delimited_release.fst

%.dm4f: %.fst
	$(FSTAR) --include ../dm4free $^

blowup:
	$(FSTAR) --include ../dm4free/ --debug Ifc_Recursive_Heap_Reify --debug_level SMTEncodingReify --trace_error ifc_recursive_heap_reify.fst
# Failure("Bound term variable not found (after unmangling): hi#647")
