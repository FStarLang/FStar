VERFILES=counters.fst intsort.fst insertionsort.fst mergesort.fst 
OTHERFLAGS=
include ../Makefile.include
all: .all.ver downgrade binary_search qsc gc unification

ARR_LIB=$(addprefix $(FSTAR_HOME)/lib/, FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fst FStar.Heap.fst stperm.fst FStar.Seq.fst FStar.SeqProperties.fst FStar.Array.fst)

qs_seq: $(ARR_LIB) qs_seq.fst
	$(FSTAR) --explicit_deps --z3timeout 20 $^

qsort_arr: $(ARR_LIB) qsort_arr.fst
	$(FSTAR) --explicit_deps --z3timeout 20 $^

downgrade: $(ARR_LIB) qs_seq.fst qsort_arr.fst downgrade.fst
	$(FSTAR) --explicit_deps --z3timeout 20 $^

binary_search: $(FSTAR_HOME)/lib/FStar.Seq.fst binary_search.fst
	$(FSTAR) --explicit_deps $^

qsc:
	$(FSTAR) qsc.fst

gc: gc.fst
	$(FSTAR) $^

unification: unification.fst
	$(FSTAR) --explicit_deps $(addprefix --admit_fsi , FStar.Set FStar.OrdSet FStar.OrdSetProps) \
	 $(addprefix $(FSTAR_HOME)/lib/, FStar.FunctionalExtensionality.fst FStar.Set.fst FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.List.Tot.fst ordset.fsi FStar.OrdSetProps.fst) $^
