VERFILES=unit1.fst unit2.fst testset.fst 
include ../Makefile.include
NEGFILES=negative-tests.fst

all: .all.ver all-neg

all-neg: $(NEGFILES)
	-$(FSTAR) $(STDLIB) $^
	echo "EXPECT 27 FAILURES<------------------------------------"

test: 
	$(FSTAR) --fs_typ_app --admit_fsi Microsoft.FStar.Util ../../lib/list.fst ../../lib/partialmap.fst ../../lib/st.fst ../../src/basic/util.fsi test.fst

#DO WE REALLY NEED THESE TARGETS HERE?
utils:
	$(FSTAR) --codegen OCaml --prims prims.fst utils.fst

stdlib:
	$(FSTAR) --codegen OCaml $(STDLIB)

