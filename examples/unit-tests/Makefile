VERFILES=unit1.fst testset.fst 
include ../Makefile.include
NEGFILES=negative-tests.fst

all: .all.ver all-neg

all-neg: $(NEGFILES)
	-$(FSTAR) $(STDLIB) $^
	echo "EXPECT 25 FAILURES<------------------------------------"

rel2: 
	$(FSTAR) --rel2 ../../lib/list.fst

#DO WE REALLY NEED THESE TARGETS HERE?
utils:
	$(FSTAR) --codegen OCaml --prims prims.fst utils.fst

stdlib:
	$(FSTAR) --codegen OCaml $(STDLIB)

