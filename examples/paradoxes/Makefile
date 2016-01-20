include ../Makefile.include
all:

russell:
	$(FSTAR) russell.fst

berardi:
	$(FSTAR) FStar.Constructive.fst berardi.fst

value-restriction: value-restriction.fst
	$(FSTAR) FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.List.fst --admit_fsi FStar.Set $^
