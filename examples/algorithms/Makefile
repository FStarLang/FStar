VERFILES=counters.fst intsort.fst insertionsort.fst mergesort.fst qsc.fst
OTHERFLAGS=
include ../Makefile.include
all: .all.ver #downgrade

qsort_seq_libs: qsort_seq_props qsort_seq_perm
	$(FSTAR) 

qsort_seq_props: $(addprefix ../../lib/, classical.fst seq.fst seqproperties.fsi seqproperties.fst)
	$(FSTAR) $^

qsort_seq_perm: $(addprefix ../../lib/, classical.fst seq.fst seqproperties.fsi seqpermutation.fsi seqpermutation.fst)
	$(FSTAR) --admit_fsi SeqProperties $^ --initial_fuel 0 --max_fuel 0 --max_ifuel 0 --z3timeout 60

qsort_seq: $(addprefix ../../lib/, classical.fst seq.fst seqproperties.fsi seqpermutation.fsi) qs_seq2.fst
	$(FSTAR) --admit_fsi SeqProperties --admit_fsi SeqPermutation $^  --z3timeout 20

qsort_seq_full: qsort_seq_libs qsort_seq

qsort_arr: $(addprefix ../../lib/, set.fst heap.fst stperm.fst seq.fst  seqproperties.fsi seqpermutation.fsi arr.fst) qsort_arr.fst
	$(FSTAR) --admit_fsi SeqProperties --admit_fsi SeqPermutation $^ 

downgrade: $(addprefix ../../lib/, set.fst heap.fst stperm.fst seq.fst seqproperties.fsi seqpermutation.fsi arr.fst) downgrade.fst
	$(FSTAR) --admit_fsi SeqProperties --admit_fsi SeqPermutation $^ 

# qsort_arr: $(addprefix ../../lib/, classical.fst seq.fstarr.fst) qsort_arr.fst
# 	$(FSTAR) --admit_fsi SeqProperties --admit_fsi SeqPermutation $^  --z3timeout 20

qs_seq2: qs_seq2.fst
	$(FSTAR) ../../lib/classical.fst ../../lib/seq.fst $^  --max_ifuel 1  --max_fuel 2

# qsort_seq: qsort_seq.fst
# 	$(FSTAR) ../../lib/seq.fst qsort_seq.fst --max_ifuel 1  --max_fuel 4
