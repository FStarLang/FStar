VERFILES=counters.fst intsort.fst insertionsort.fst mergesort.fst 
OTHERFLAGS=
include ../Makefile.include
all: .all.ver downgrade binary_search qsc gc unification

ARR_LIB=$(addprefix $(FSTAR_HOME)/lib/, FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Set.fst FStar.Heap.fst stperm.fst seq.fsi FStar.Seq.fst FStar.SeqProperties.fst FStar.Array.fst)

qs_seq: $(ARR_LIB) qs_seq.fst
	$(FSTAR) --z3timeout 20 $^

qsort_arr: $(ARR_LIB) qsort_arr.fst
	$(FSTAR) --z3timeout 20 $^

downgrade: $(ARR_LIB) qs_seq.fst qsort_arr.fst downgrade.fst
	$(FSTAR) --z3timeout 20 $^

binary_search: $(FSTAR_HOME)/lib/seq.fsi binary_search.fst
	$(FSTAR) --admit_fsi FStar.Seq $^

qsc:
	$(FSTAR) qsc.fst

gc: gc.fst
	$(FSTAR) $^

unification: unification.fst
	$(FSTAR) $^
