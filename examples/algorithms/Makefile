VERFILES=counters.fst intsort.fst insertionsort.fst mergesort.fst qsc.fst
OTHERFLAGS=
include ../Makefile.include
all: .all.ver #downgrade qs_seq

qs_seq: $(addprefix ../../lib/, classical.fst ext.fst seq.fsi seq.fst seqproperties.fst) qs_seq.fst
	$(FSTAR) $^ 


qsort_arr: $(addprefix ../../lib/, set.fst heap.fst stperm.fst seq.fst  seqproperties.fsi seqpermutation.fsi arr.fst) qsort_arr.fst
	$(FSTAR) --admit_fsi SeqProperties --admit_fsi SeqPermutation $^ 

downgrade: $(addprefix ../../lib/, classical.fst ext.fst set.fsi set.fst seq.fsi seq.fst seqproperties.fst)# heap.fst stperm.fst arr.fst) downgrade.fst
	$(FSTAR) $^ --z3timeout 10

# qsort_arr: $(addprefix ../../lib/, classical.fst seq.fstarr.fst) qsort_arr.fst
# 	$(FSTAR) --admit_fsi SeqProperties --admit_fsi SeqPermutation $^  --z3timeout 20


binary_search: binary_search.fst
	$(FSTAR) ../../lib/seq.fsi --admit_fsi Seq $^
