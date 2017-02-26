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
		 WhileReify \
		 delimitedReleaseReify \
		 ifc_reify_examples \
		 IfcExampleReify \
		 IfcExampleReify2 \
		 IfcReify \
		 IfcTypechecker.dm4f

%.dm4f: %.fst
	$(FSTAR) --include ../dm4free $^

ifc:
	$(FSTAR) rel.fst whilelanguage.fst ifc.fst ifcExample.fst

random_tapes:
	$(FSTAR) bijection.fst random_tapes.fst

recursive:
	$(FSTAR) recursive.fst

delimited_release:
	$(FSTAR) delimited_release.fst

WhileReify:
	$(FSTAR) --include ../dm4free WhileReify.fst

IfcReify:
	$(FSTAR) --include ../dm4free IfcReify.fst

IfcExampleReify:
	$(FSTAR) --include ../dm4free ifcExampleReify.fst
	
IfcExampleReify2:
	$(FSTAR) --include ../dm4free ifcExampleReify2.fst

ifc_reify_examples:
	$(FSTAR) --include ../dm4free ifc_compose_reify.fst ifc_recursive_heap_reify.fst ifc_recursive_reify.fst ifc_reify.fst ifc_reify_long.fst simple_ifc_reify.fst

delimitedReleaseReify:
	$(FSTAR) --include ../dm4free delimitedReleaseReify.fst


blowup:
	$(FSTAR) --include ../dm4free/ --debug Ifc_Recursive_Heap_Reify --debug_level SMTEncodingReify --trace_error ifc_recursive_heap_reify.fst
# Failure("Bound term variable not found (after unmangling): hi#647")
