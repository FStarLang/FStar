VERFILES=counters.fst intsort.fst insertionsort.fst mergesort.fst
OTHERFLAGS=
include ../Makefile.include
all: .all.ver downgrade binary_search qsc gc

ARR_LIB=$(addprefix $(FSTAR_HOME)/lib/, classical.fst ext.fst set.fsi set.fst heap.fst stperm.fst seq.fsi seq.fst seqproperties.fst arr.fst)

qs_seq: $(ARR_LIB) qs_seq.fst
	$(FSTAR) --z3timeout 20 $^

qsort_arr: $(ARR_LIB) qsort_arr.fst
	$(FSTAR) --z3timeout 20 $^

downgrade: $(ARR_LIB) qs_seq.fst qsort_arr.fst downgrade.fst
	$(FSTAR) --z3timeout 20 $^

binary_search: $(FSTAR_HOME)/lib/seq.fsi binary_search.fst
	$(FSTAR) --admit_fsi Seq $^

qsc: $(FSTAR_HOME)/lib/list.fst qsc.fst
	$(FSTAR) $^

gc: gc.fst
	$(FSTAR) $^
