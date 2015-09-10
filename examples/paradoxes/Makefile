include ../Makefile.include
all:

berardi:
	$(FSTAR) constr.fst berardi.fst

value-restriction: value-restriction.fst
	$(FSTAR) set.fsi heap.fst st.fst all.fst list.fst --admit_fsi FStar.Set $^
