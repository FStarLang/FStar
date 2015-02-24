VERFILES=counters.fst insertionsort-lemma.fst insertionsort.fst intlist-insertionsort.fst mergesort.fst
OTHERFLAGS=
include ../Makefile.include
all: .all.ver 

qsort_seq: qsort_seq.fst
	$(FSTAR) ../../lib/seq.fst qsort_seq.fst --max_ifuel 1  --max_fuel 4
