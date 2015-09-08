include ../Makefile.include
all: berardi

berardi:
	$(FSTAR) ../../lib/constr.fst berardi.fst

value-restriction: value-restriction.fst
	$(FSTAR) $(addprefix $(FSTAR_HOME)/lib/, set.fsi heap.fst st.fst all.fst list.fst) --admit_fsi FStar.Set $^
