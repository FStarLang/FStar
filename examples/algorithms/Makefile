VERFILES=counters.fst intsort.fst insertionsort.fst mergesort.fst qsc.fst
OTHERFLAGS=
include ../Makefile.include
all: .all.ver downgrade qs_seq qsort_arr

qs_seq: $(addprefix ../../lib/, classical.fst ext.fst seq.fsi seq.fst seqproperties.fst) qs_seq.fst
	$(FSTAR) $^ 

ARR_LIB=$(addprefix ../../lib/, classical.fst ext.fst set.fsi set.fst heap.fst stperm.fst seq.fsi seq.fst seqproperties.fst arr.fst) 

downgrade: $(ARR_LIB) qsort_arr.fst downgrade.fst
	$(FSTAR) $^ 

qsort_arr: $(ARR_LIB) qsort_arr.fst
	$(FSTAR) $^ 

binary_search: binary_search.fst
	$(FSTAR) ../../lib/seq.fsi --admit_fsi Seq $^
