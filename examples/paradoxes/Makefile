include ../Makefile.include
all:

russell:
	$(FSTAR) russell.fst

berardi:
	$(FSTAR) constr.fst berardi.fst

value-restriction: value-restriction.fst
	$(FSTAR) FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst list.fst --admit_fsi FStar.Set $^
